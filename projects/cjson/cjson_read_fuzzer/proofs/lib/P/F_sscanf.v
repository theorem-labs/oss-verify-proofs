(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SFModel.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SysStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Image.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require FP.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require PropExec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Prelim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require SoftFloat.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require StrFun.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require FloatScan.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require FloatScanProps.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require FloatScan_nn.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require FloatScan_split2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require SFW1_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_scan_calls.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Shgetc_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require FmtFp_facts3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_memcpy.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_strnlen.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_fmt_fp_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_divtf3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_floatscan_common.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_subtf3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_letf2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_getf2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_floatsitf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_floatunsitf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_pop_arg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_scalbn.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Scan_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_rscan_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_scalbnl.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_rscan_model.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require PImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require StoreCache.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc Require RStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I Require IImgP.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_floatscan_A0.
Module F_floatscan_A0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.StrFun OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan.DoubleOps OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScanProps OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan_nn.FloatScan_split OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan_split2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls.F_fmt_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Shgetc_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_facts3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_strnlen.F_memchr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_multf3_tail OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_multf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_divtf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.F_divtf3_main OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3.F_addtf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_letf2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_getf2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatsitf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatunsitf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_pop_arg.F_extenddftf2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbn OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_rscan_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_rfile OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbnl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.F_fmodl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_scanexp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_rscan_model.F_rscan_facts.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.


#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_memcpy.P_memcpy_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_strnlen.F_memchr.P_memchr_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_multf3.P_multf3_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.F_divtf3_main.P_divtf3_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3.F_addtf3_E.P_addtf3_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3.P_subtf3_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_letf2.P_letf2_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_getf2.P_getf2_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatsitf.P_floatsitf_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatunsitf.P_floatunsitf_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_pop_arg.F_extenddftf2.P_extenddftf2_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbn.P_scalbn_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_letf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_letf2_callv0_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_fixunstfsi_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatsitf_callp_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatunsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatunsitf_callfix_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_extenddftf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_multf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_divtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_addtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_subtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_frexpl_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_signbitl_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_fpclassifyl_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_A.P_shlim_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_A.P_toread_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_B.P_sread_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc.P_uflow_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc.P_shgetc_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_rfile.P_shgetc_callJ_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbnl.P_scalbnl_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbnl.P_fabsl_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbnl.P_copysignl_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.F_fmodl.P_rfmodl_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_scanexp.P_scanexp_rspec_c.
(* [comment removed for export] *)
#[local] Existing Instance OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgP.P_img.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAtT _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAt _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RoB _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelCode _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelSym _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelNear _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 2 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.ZFact _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
(* [comment removed for export] *)
Local Ltac gonly_lia := let HI := fresh "HI" in pose proof I as HI; clear - HI; Zify.zify; xlia zchecker.
Local Ltac gonly_refute := lazymatch goal with |- ?G => assert (~ G) by gonly_lia end.
(* [comment removed for export] *)
Local Ltac flia ::= first [ assumption | slim; lia ].


(* [comment removed for export] *)
Local Strategy 1000 [FUEL_RING FUEL_SCALE df_dnk_loop df_dn_loop df_dni_loop df_upk_loop df_up_loop df_tz_loop df_al_loop df_pad_loop df_asm_loop df_dig_loop df_rz_loop df_lz_loop].
End F_floatscan_A0.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_floatscan_A1.
Module F_floatscan_A1.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.StrFun OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan.DoubleOps OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScanProps OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan_nn.FloatScan_split OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan_split2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls.F_fmt_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Shgetc_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_facts3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_strnlen.F_memchr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_multf3_tail OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_multf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_divtf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.F_divtf3_main OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3.F_addtf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_letf2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_getf2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatsitf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatunsitf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_pop_arg.F_extenddftf2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbn OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_rscan_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_rfile OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbnl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.F_fmodl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_scanexp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_rscan_model.F_rscan_facts.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.


#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_memcpy.P_memcpy_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_strnlen.F_memchr.P_memchr_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_multf3.P_multf3_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.F_divtf3_main.P_divtf3_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3.F_addtf3_E.P_addtf3_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3.P_subtf3_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_letf2.P_letf2_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_getf2.P_getf2_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatsitf.P_floatsitf_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatunsitf.P_floatunsitf_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_pop_arg.F_extenddftf2.P_extenddftf2_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbn.P_scalbn_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_letf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_letf2_callv0_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_fixunstfsi_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatsitf_callp_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatunsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatunsitf_callfix_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_extenddftf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_multf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_divtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_addtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_subtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_frexpl_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_signbitl_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_fpclassifyl_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_A.P_shlim_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_A.P_toread_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_B.P_sread_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc.P_uflow_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc.P_shgetc_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_rfile.P_shgetc_callJ_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbnl.P_scalbnl_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbnl.P_fabsl_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbnl.P_copysignl_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.F_fmodl.P_rfmodl_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_scanexp.P_scanexp_rspec_c.
(* [comment removed for export] *)
#[local] Existing Instance OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgP.P_img.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAtT _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAt _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RoB _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelCode _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelSym _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelNear _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 2 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.ZFact _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
(* [comment removed for export] *)
Local Ltac gonly_lia := let HI := fresh "HI" in pose proof I as HI; clear - HI; Zify.zify; xlia zchecker.
Local Ltac gonly_refute := lazymatch goal with |- ?G => assert (~ G) by gonly_lia end.
(* [comment removed for export] *)
Local Ltac flia ::= first [ assumption | slim; lia ].


(* [comment removed for export] *)
Local Strategy 1000 [FUEL_RING FUEL_SCALE df_dnk_loop df_dn_loop df_dni_loop df_upk_loop df_up_loop df_tz_loop df_al_loop df_pad_loop df_asm_loop df_dig_loop df_rz_loop df_lz_loop].
End F_floatscan_A1.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_floatscan_A2.
Module F_floatscan_A2.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.StrFun OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan.DoubleOps OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScanProps OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan_nn.FloatScan_split OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan_split2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls.F_fmt_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Shgetc_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_facts3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_strnlen.F_memchr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_multf3_tail OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_multf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_divtf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.F_divtf3_main OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3.F_addtf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_letf2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_getf2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatsitf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatunsitf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_pop_arg.F_extenddftf2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbn OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_rscan_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_rfile OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbnl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.F_fmodl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_scanexp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_rscan_model.F_rscan_facts.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.


#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_memcpy.P_memcpy_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_strnlen.F_memchr.P_memchr_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_multf3.P_multf3_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.F_divtf3_main.P_divtf3_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3.F_addtf3_E.P_addtf3_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3.P_subtf3_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_letf2.P_letf2_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_getf2.P_getf2_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatsitf.P_floatsitf_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatunsitf.P_floatunsitf_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_pop_arg.F_extenddftf2.P_extenddftf2_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbn.P_scalbn_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_letf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_letf2_callv0_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_fixunstfsi_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatsitf_callp_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatunsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatunsitf_callfix_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_extenddftf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_multf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_divtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_addtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_subtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_frexpl_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_signbitl_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_fpclassifyl_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_A.P_shlim_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_A.P_toread_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_B.P_sread_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc.P_uflow_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc.P_shgetc_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_rfile.P_shgetc_callJ_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbnl.P_scalbnl_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbnl.P_fabsl_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbnl.P_copysignl_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.F_fmodl.P_rfmodl_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_scanexp.P_scanexp_rspec_c.
(* [comment removed for export] *)
#[local] Existing Instance OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgP.P_img.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAtT _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAt _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RoB _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelCode _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelSym _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelNear _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 2 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.ZFact _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
(* [comment removed for export] *)
Local Ltac gonly_lia := let HI := fresh "HI" in pose proof I as HI; clear - HI; Zify.zify; xlia zchecker.
Local Ltac gonly_refute := lazymatch goal with |- ?G => assert (~ G) by gonly_lia end.
(* [comment removed for export] *)
Local Ltac flia ::= first [ assumption | slim; lia ].


(* [comment removed for export] *)
Local Strategy 1000 [FUEL_RING FUEL_SCALE df_dnk_loop df_dn_loop df_dni_loop df_upk_loop df_up_loop df_tz_loop df_al_loop df_pad_loop df_asm_loop df_dig_loop df_rz_loop df_lz_loop].
End F_floatscan_A2.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_floatscan_A3.
Module F_floatscan_A3.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.StrFun OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan.DoubleOps OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScanProps OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan_nn.FloatScan_split OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan_split2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls.F_fmt_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Shgetc_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_facts3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_strnlen.F_memchr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_multf3_tail OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_multf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_divtf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.F_divtf3_main OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3.F_addtf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_letf2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_getf2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatsitf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatunsitf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_pop_arg.F_extenddftf2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbn OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_rscan_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_rfile OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbnl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.F_fmodl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_scanexp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_rscan_model.F_rscan_facts.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.


#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_memcpy.P_memcpy_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_strnlen.F_memchr.P_memchr_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_multf3.P_multf3_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.F_divtf3_main.P_divtf3_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3.F_addtf3_E.P_addtf3_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3.P_subtf3_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_letf2.P_letf2_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_getf2.P_getf2_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatsitf.P_floatsitf_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatunsitf.P_floatunsitf_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_pop_arg.F_extenddftf2.P_extenddftf2_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbn.P_scalbn_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_letf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_letf2_callv0_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_fixunstfsi_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatsitf_callp_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatunsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatunsitf_callfix_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_extenddftf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_multf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_divtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_addtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_subtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_frexpl_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_signbitl_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_fpclassifyl_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_A.P_shlim_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_A.P_toread_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_B.P_sread_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc.P_uflow_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc.P_shgetc_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_rfile.P_shgetc_callJ_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbnl.P_scalbnl_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbnl.P_fabsl_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbnl.P_copysignl_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.F_fmodl.P_rfmodl_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_scanexp.P_scanexp_rspec_c.
(* [comment removed for export] *)
#[local] Existing Instance OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgP.P_img.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAtT _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAt _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RoB _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelCode _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelSym _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelNear _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 2 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.ZFact _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
(* [comment removed for export] *)
Local Ltac gonly_lia := let HI := fresh "HI" in pose proof I as HI; clear - HI; Zify.zify; xlia zchecker.
Local Ltac gonly_refute := lazymatch goal with |- ?G => assert (~ G) by gonly_lia end.
(* [comment removed for export] *)
Local Ltac flia ::= first [ assumption | slim; lia ].


(* [comment removed for export] *)
Local Strategy 1000 [FUEL_RING FUEL_SCALE df_dnk_loop df_dn_loop df_dni_loop df_upk_loop df_up_loop df_tz_loop df_al_loop df_pad_loop df_asm_loop df_dig_loop df_rz_loop df_lz_loop].
End F_floatscan_A3.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require NElim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_floatscan_D.
Module F_floatscan_D.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.StrFun OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan.DoubleOps OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScanProps OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan_nn.FloatScan_split OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan_split2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls.F_fmt_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Shgetc_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_facts3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_strnlen.F_memchr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_multf3_tail OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_multf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_divtf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.F_divtf3_main OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3.F_addtf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_letf2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_getf2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatsitf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatunsitf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_pop_arg.F_extenddftf2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbn OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_rscan_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_rfile OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbnl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.F_fmodl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_scanexp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_rscan_model.F_rscan_facts.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.


#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_memcpy.P_memcpy_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_strnlen.F_memchr.P_memchr_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_multf3.P_multf3_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.F_divtf3_main.P_divtf3_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3.F_addtf3_E.P_addtf3_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3.P_subtf3_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_letf2.P_letf2_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_getf2.P_getf2_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatsitf.P_floatsitf_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatunsitf.P_floatunsitf_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_pop_arg.F_extenddftf2.P_extenddftf2_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbn.P_scalbn_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_letf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_letf2_callv0_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_fixunstfsi_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatsitf_callp_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatunsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatunsitf_callfix_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_extenddftf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_multf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_divtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_addtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_subtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_frexpl_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_signbitl_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_fpclassifyl_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_A.P_shlim_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_A.P_toread_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_B.P_sread_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc.P_uflow_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc.P_shgetc_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_rfile.P_shgetc_callJ_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbnl.P_scalbnl_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbnl.P_fabsl_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbnl.P_copysignl_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.F_fmodl.P_rfmodl_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_scanexp.P_scanexp_rspec_c.
(* [comment removed for export] *)
#[local] Existing Instance OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgP.P_img.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAtT _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAt _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RoB _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelCode _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelSym _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelNear _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 2 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.ZFact _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.

(* [comment removed for export] *)
Local Ltac flia ::= first [ assumption | slim; lia ].


(* [comment removed for export] *)
Local Strategy 1000 [FUEL_RING FUEL_SCALE df_dnk_loop df_dn_loop df_dni_loop df_upk_loop df_up_loop df_tz_loop df_al_loop df_pad_loop df_asm_loop df_dig_loop df_rz_loop df_lz_loop].

(* [comment removed for export] *)
Local Ltac nat_diet ::= repeat nat_diet_step;
  lazymatch goal with _ : Z.of_nat (natZ _) = _ |- _ => idtac | _ =>
    repeat match goal with H : context [natZ (Zpos ?p)] |- _ =>
      lazymatch goal with _ : Z.of_nat (natZ (Zpos p)) = _ |- _ => fail | _ => pose proof (natZ_pos p) end end end.
End F_floatscan_D.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_floatscan_E.
Module F_floatscan_E.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.StrFun OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan.DoubleOps OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScanProps OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan_nn.FloatScan_split OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan_split2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls.F_fmt_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Shgetc_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_facts3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_strnlen.F_memchr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_multf3_tail OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_multf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_divtf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.F_divtf3_main OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3.F_addtf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_letf2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_getf2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatsitf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatunsitf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_pop_arg.F_extenddftf2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbn OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_rscan_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_rfile OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbnl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.F_fmodl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_scanexp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_rscan_model.F_rscan_facts.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.


#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_memcpy.P_memcpy_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_strnlen.F_memchr.P_memchr_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_multf3.P_multf3_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.F_divtf3_main.P_divtf3_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3.F_addtf3_E.P_addtf3_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3.P_subtf3_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_letf2.P_letf2_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_getf2.P_getf2_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatsitf.P_floatsitf_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatunsitf.P_floatunsitf_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_pop_arg.F_extenddftf2.P_extenddftf2_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbn.P_scalbn_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_letf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_letf2_callv0_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_fixunstfsi_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatsitf_callp_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatunsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatunsitf_callfix_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_extenddftf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_multf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_divtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_addtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_subtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_frexpl_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_signbitl_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_fpclassifyl_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_A.P_shlim_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_A.P_toread_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_B.P_sread_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc.P_uflow_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc.P_shgetc_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_rfile.P_shgetc_callJ_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbnl.P_scalbnl_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbnl.P_fabsl_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbnl.P_copysignl_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.F_fmodl.P_rfmodl_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_scanexp.P_scanexp_rspec_c.
(* [comment removed for export] *)
#[local] Existing Instance OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgP.P_img.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAtT _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAt _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RoB _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelCode _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelSym _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelNear _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 2 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.ZFact _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
(* [comment removed for export] *)
Local Ltac gonly_lia := let HI := fresh "HI" in pose proof I as HI; clear - HI; Zify.zify; xlia zchecker.
Local Ltac gonly_refute := lazymatch goal with |- ?G => assert (~ G) by gonly_lia end.
(* [comment removed for export] *)
Local Ltac flia ::= first [ assumption | slim; lia ].


(* [comment removed for export] *)
Local Strategy 1000 [FUEL_RING FUEL_SCALE df_dnk_loop df_dn_loop df_dni_loop df_upk_loop df_up_loop df_tz_loop df_al_loop df_pad_loop df_asm_loop df_dig_loop df_rz_loop df_lz_loop].

(* [comment removed for export] *)
Local Ltac nat_diet ::= repeat nat_diet_step;
  lazymatch goal with _ : Z.of_nat (natZ _) = _ |- _ => idtac | _ =>
    repeat match goal with H : context [natZ (Zpos ?p)] |- _ =>
      lazymatch goal with _ : Z.of_nat (natZ (Zpos p)) = _ |- _ => fail | _ => pose proof (natZ_pos p) end end end.
End F_floatscan_E.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_floatscan_F1.
Module F_floatscan_F1.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.StrFun OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan.DoubleOps OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScanProps OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan_nn.FloatScan_split OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan_split2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls.F_fmt_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Shgetc_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_facts3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_strnlen.F_memchr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_multf3_tail OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_multf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_divtf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.F_divtf3_main OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3.F_addtf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_letf2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_getf2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatsitf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatunsitf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_pop_arg.F_extenddftf2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbn OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_rscan_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_rfile OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbnl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.F_fmodl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_scanexp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_rscan_model.F_rscan_facts.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.


#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_memcpy.P_memcpy_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_strnlen.F_memchr.P_memchr_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_multf3.P_multf3_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.F_divtf3_main.P_divtf3_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3.F_addtf3_E.P_addtf3_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3.P_subtf3_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_letf2.P_letf2_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_getf2.P_getf2_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatsitf.P_floatsitf_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatunsitf.P_floatunsitf_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_pop_arg.F_extenddftf2.P_extenddftf2_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbn.P_scalbn_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_letf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_letf2_callv0_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_fixunstfsi_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatsitf_callp_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatunsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatunsitf_callfix_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_extenddftf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_multf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_divtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_addtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_subtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_frexpl_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_signbitl_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_fpclassifyl_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_A.P_shlim_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_A.P_toread_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_B.P_sread_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc.P_uflow_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc.P_shgetc_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_rfile.P_shgetc_callJ_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbnl.P_scalbnl_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbnl.P_fabsl_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbnl.P_copysignl_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.F_fmodl.P_rfmodl_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_scanexp.P_scanexp_rspec_c.
(* [comment removed for export] *)
#[local] Existing Instance OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgP.P_img.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAtT _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAt _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RoB _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelCode _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelSym _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelNear _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 2 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.ZFact _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
(* [comment removed for export] *)
Local Ltac mem_after_store ::= mem_after_store_cached.
Local Ltac addr_eq_tac ::= addr_eq_tac_cached.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_cached segs m m' MU WM.
Local Ltac sc_clear := repeat match goal with H : sc_dj _ _ _ _ |- _ => clear H | H : sc_in _ _ _ |- _ => clear H
  | H : sc_no _ _ _ _ |- _ => clear H | H : sc_noin _ _ _ |- _ => clear H end.
(* [comment removed for export] *)
Local Ltac gonly_lia := let HI := fresh "HI" in pose proof I as HI; clear - HI; Zify.zify; xlia zchecker.
Local Ltac gonly_refute := lazymatch goal with |- ?G => assert (~ G) by gonly_lia end.
(* [comment removed for export] *)
Local Ltac flia ::= first [ assumption | slim; lia ].


(* [comment removed for export] *)
Local Strategy 1000 [FUEL_RING FUEL_SCALE df_dnk_loop df_dn_loop df_dni_loop df_upk_loop df_up_loop df_tz_loop df_al_loop df_pad_loop df_asm_loop df_dig_loop df_rz_loop df_lz_loop].
End F_floatscan_F1.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_floatscan_F2.
Module F_floatscan_F2.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.StrFun OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan.DoubleOps OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScanProps OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan_nn.FloatScan_split OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan_split2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls.F_fmt_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Shgetc_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_facts3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_strnlen.F_memchr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_multf3_tail OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_multf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_divtf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.F_divtf3_main OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3.F_addtf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_letf2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_getf2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatsitf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatunsitf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_pop_arg.F_extenddftf2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbn OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_rscan_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_rfile OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbnl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.F_fmodl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_scanexp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_rscan_model.F_rscan_facts.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.


#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_memcpy.P_memcpy_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_strnlen.F_memchr.P_memchr_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_multf3.P_multf3_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.F_divtf3_main.P_divtf3_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3.F_addtf3_E.P_addtf3_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3.P_subtf3_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_letf2.P_letf2_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_getf2.P_getf2_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatsitf.P_floatsitf_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatunsitf.P_floatunsitf_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_pop_arg.F_extenddftf2.P_extenddftf2_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbn.P_scalbn_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_letf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_letf2_callv0_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_fixunstfsi_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatsitf_callp_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatunsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatunsitf_callfix_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_extenddftf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_multf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_divtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_addtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_subtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_frexpl_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_signbitl_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_fpclassifyl_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_A.P_shlim_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_A.P_toread_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_B.P_sread_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc.P_uflow_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc.P_shgetc_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_rfile.P_shgetc_callJ_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbnl.P_scalbnl_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbnl.P_fabsl_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbnl.P_copysignl_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.F_fmodl.P_rfmodl_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_scanexp.P_scanexp_rspec_c.
(* [comment removed for export] *)
#[local] Existing Instance OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgP.P_img.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAtT _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAt _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RoB _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelCode _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelSym _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelNear _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 2 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.ZFact _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
(* [comment removed for export] *)
Local Ltac gonly_lia := let HI := fresh "HI" in pose proof I as HI; clear - HI; Zify.zify; xlia zchecker.
Local Ltac gonly_refute := lazymatch goal with |- ?G => assert (~ G) by gonly_lia end.
(* [comment removed for export] *)
Local Ltac flia ::= first [ assumption | slim; lia ].


(* [comment removed for export] *)
Local Strategy 1000 [FUEL_RING FUEL_SCALE df_dnk_loop df_dn_loop df_dni_loop df_upk_loop df_up_loop df_tz_loop df_al_loop df_pad_loop df_asm_loop df_dig_loop df_rz_loop df_lz_loop].
End F_floatscan_F2.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_floatscan_F3.
Module F_floatscan_F3.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.StrFun OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan.DoubleOps OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScanProps OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan_nn.FloatScan_split OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan_split2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls.F_fmt_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Shgetc_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_facts3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_strnlen.F_memchr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_multf3_tail OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_multf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_divtf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.F_divtf3_main OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3.F_addtf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_letf2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_getf2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatsitf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatunsitf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_pop_arg.F_extenddftf2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbn OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_rscan_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_rfile OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbnl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.F_fmodl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_scanexp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_rscan_model.F_rscan_facts.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.


#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_memcpy.P_memcpy_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_strnlen.F_memchr.P_memchr_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_multf3.P_multf3_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.F_divtf3_main.P_divtf3_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3.F_addtf3_E.P_addtf3_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3.P_subtf3_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_letf2.P_letf2_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_getf2.P_getf2_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatsitf.P_floatsitf_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatunsitf.P_floatunsitf_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_pop_arg.F_extenddftf2.P_extenddftf2_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbn.P_scalbn_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_letf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_letf2_callv0_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_fixunstfsi_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatsitf_callp_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatunsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatunsitf_callfix_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_extenddftf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_multf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_divtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_addtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_subtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_frexpl_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_signbitl_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_fpclassifyl_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_A.P_shlim_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_A.P_toread_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_B.P_sread_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc.P_uflow_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc.P_shgetc_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_rfile.P_shgetc_callJ_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbnl.P_scalbnl_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbnl.P_fabsl_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbnl.P_copysignl_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.F_fmodl.P_rfmodl_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_scanexp.P_scanexp_rspec_c.
(* [comment removed for export] *)
#[local] Existing Instance OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgP.P_img.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAtT _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAt _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RoB _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelCode _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelSym _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelNear _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 2 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.ZFact _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
(* [comment removed for export] *)
Local Ltac gonly_lia := let HI := fresh "HI" in pose proof I as HI; clear - HI; Zify.zify; xlia zchecker.
Local Ltac gonly_refute := lazymatch goal with |- ?G => assert (~ G) by gonly_lia end.
(* [comment removed for export] *)
Local Ltac flia ::= first [ assumption | slim; lia ].


(* [comment removed for export] *)
Local Strategy 1000 [FUEL_RING FUEL_SCALE df_dnk_loop df_dn_loop df_dni_loop df_upk_loop df_up_loop df_tz_loop df_al_loop df_pad_loop df_asm_loop df_dig_loop df_rz_loop df_lz_loop].
End F_floatscan_F3.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_floatscan_M.
Module F_floatscan_M.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.StrFun OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan.DoubleOps OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScanProps OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan_nn.FloatScan_split OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan_split2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls.F_fmt_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Shgetc_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_facts3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_strnlen.F_memchr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_multf3_tail OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_multf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_divtf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.F_divtf3_main OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3.F_addtf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_letf2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_getf2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatsitf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatunsitf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_pop_arg.F_extenddftf2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbn OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_rscan_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_rfile OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbnl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.F_fmodl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_scanexp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_rscan_model.F_rscan_facts.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.


#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_memcpy.P_memcpy_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_strnlen.F_memchr.P_memchr_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_multf3.P_multf3_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.F_divtf3_main.P_divtf3_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3.F_addtf3_E.P_addtf3_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3.P_subtf3_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_letf2.P_letf2_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_getf2.P_getf2_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatsitf.P_floatsitf_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatunsitf.P_floatunsitf_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_pop_arg.F_extenddftf2.P_extenddftf2_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbn.P_scalbn_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_letf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_letf2_callv0_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_fixunstfsi_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatsitf_callp_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatunsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatunsitf_callfix_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_extenddftf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_multf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_divtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_addtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_subtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_frexpl_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_signbitl_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_fpclassifyl_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_A.P_shlim_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_A.P_toread_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_B.P_sread_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc.P_uflow_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc.P_shgetc_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_rfile.P_shgetc_callJ_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbnl.P_scalbnl_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbnl.P_fabsl_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbnl.P_copysignl_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.F_fmodl.P_rfmodl_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_scanexp.P_scanexp_rspec_c.
(* [comment removed for export] *)
#[local] Existing Instance OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgP.P_img.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAtT _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAt _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RoB _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelCode _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelSym _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelNear _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 2 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.ZFact _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
(* [comment removed for export] *)
Local Ltac gonly_lia := let HI := fresh "HI" in pose proof I as HI; clear - HI; Zify.zify; xlia zchecker.
Local Ltac gonly_refute := lazymatch goal with |- ?G => assert (~ G) by gonly_lia end.


(* [comment removed for export] *)
Local Strategy 1000 [FUEL_RING FUEL_SCALE df_dnk_loop df_dn_loop df_dni_loop df_upk_loop df_up_loop df_tz_loop df_al_loop df_pad_loop df_asm_loop df_dig_loop df_rz_loop df_lz_loop].

(* [comment removed for export] *)
Local Ltac nat_diet ::= repeat nat_diet_step;
  lazymatch goal with _ : Z.of_nat (natZ _) = _ |- _ => idtac | _ =>
    repeat match goal with H : context [natZ (Zpos ?p)] |- _ =>
      lazymatch goal with _ : Z.of_nat (natZ (Zpos p)) = _ |- _ => fail | _ => pose proof (natZ_pos p) end end end.
End F_floatscan_M.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_floatscan_N.
Module F_floatscan_N.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.StrFun OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan.DoubleOps OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScanProps OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan_nn.FloatScan_split OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan_split2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls.F_fmt_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Shgetc_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_facts3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_strnlen.F_memchr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_multf3_tail OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_multf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_divtf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.F_divtf3_main OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3.F_addtf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_letf2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_getf2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatsitf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatunsitf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_pop_arg.F_extenddftf2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbn OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_rscan_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_rfile OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbnl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.F_fmodl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_scanexp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_rscan_model.F_rscan_facts.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.


#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_memcpy.P_memcpy_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_strnlen.F_memchr.P_memchr_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_multf3.P_multf3_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.F_divtf3_main.P_divtf3_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3.F_addtf3_E.P_addtf3_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3.P_subtf3_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_letf2.P_letf2_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_getf2.P_getf2_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatsitf.P_floatsitf_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatunsitf.P_floatunsitf_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_pop_arg.F_extenddftf2.P_extenddftf2_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbn.P_scalbn_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_letf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_letf2_callv0_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_fixunstfsi_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatsitf_callp_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatunsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatunsitf_callfix_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_extenddftf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_multf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_divtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_addtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_subtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_frexpl_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_signbitl_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_fpclassifyl_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_A.P_shlim_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_A.P_toread_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_B.P_sread_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc.P_uflow_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc.P_shgetc_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_rfile.P_shgetc_callJ_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbnl.P_scalbnl_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbnl.P_fabsl_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbnl.P_copysignl_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.F_fmodl.P_rfmodl_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_scanexp.P_scanexp_rspec_c.
(* [comment removed for export] *)
#[local] Existing Instance OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgP.P_img.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAtT _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAt _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RoB _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelCode _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelSym _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelNear _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 2 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.ZFact _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.

(* [comment removed for export] *)
Local Ltac flia ::= first [ assumption | slim; lia ].


(* [comment removed for export] *)
Local Strategy 1000 [FUEL_RING FUEL_SCALE df_dnk_loop df_dn_loop df_dni_loop df_upk_loop df_up_loop df_tz_loop df_al_loop df_pad_loop df_asm_loop df_dig_loop df_rz_loop df_lz_loop].
End F_floatscan_N.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_floatscan_N0.
Module F_floatscan_N0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.StrFun OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan.DoubleOps OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScanProps OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan_nn.FloatScan_split OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan_split2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls.F_fmt_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Shgetc_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_facts3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_strnlen.F_memchr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_multf3_tail OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_multf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_divtf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.F_divtf3_main OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3.F_addtf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_letf2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_getf2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatsitf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatunsitf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_pop_arg.F_extenddftf2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbn OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_rscan_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_rfile OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbnl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.F_fmodl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_scanexp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_rscan_model.F_rscan_facts.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.


#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_memcpy.P_memcpy_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_strnlen.F_memchr.P_memchr_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_multf3.P_multf3_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.F_divtf3_main.P_divtf3_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3.F_addtf3_E.P_addtf3_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3.P_subtf3_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_letf2.P_letf2_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_getf2.P_getf2_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatsitf.P_floatsitf_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatunsitf.P_floatunsitf_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_pop_arg.F_extenddftf2.P_extenddftf2_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbn.P_scalbn_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_letf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_letf2_callv0_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_fixunstfsi_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatsitf_callp_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatunsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatunsitf_callfix_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_extenddftf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_multf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_divtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_addtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_subtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_frexpl_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_signbitl_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_fpclassifyl_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_A.P_shlim_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_A.P_toread_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_B.P_sread_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc.P_uflow_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc.P_shgetc_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_rfile.P_shgetc_callJ_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbnl.P_scalbnl_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbnl.P_fabsl_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbnl.P_copysignl_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.F_fmodl.P_rfmodl_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_scanexp.P_scanexp_rspec_c.
(* [comment removed for export] *)
#[local] Existing Instance OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgP.P_img.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAtT _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAt _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RoB _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelCode _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelSym _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelNear _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 2 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.ZFact _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.

(* [comment removed for export] *)
Local Ltac flia ::= first [ assumption | slim; lia ].


(* [comment removed for export] *)
Local Strategy 1000 [FUEL_RING FUEL_SCALE df_dnk_loop df_dn_loop df_dni_loop df_upk_loop df_up_loop df_tz_loop df_al_loop df_pad_loop df_asm_loop df_dig_loop df_rz_loop df_lz_loop].
End F_floatscan_N0.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_floatscan_N3E8.
Module F_floatscan_N3E8.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.StrFun OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan.DoubleOps OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScanProps OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan_nn.FloatScan_split OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan_split2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls.F_fmt_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Shgetc_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_facts3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_strnlen.F_memchr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_multf3_tail OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_multf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_divtf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.F_divtf3_main OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3.F_addtf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_letf2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_getf2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatsitf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatunsitf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_pop_arg.F_extenddftf2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbn OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_rscan_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_rfile OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbnl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.F_fmodl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_scanexp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_rscan_model.F_rscan_facts.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.


#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_memcpy.P_memcpy_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_strnlen.F_memchr.P_memchr_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_multf3.P_multf3_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.F_divtf3_main.P_divtf3_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3.F_addtf3_E.P_addtf3_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3.P_subtf3_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_letf2.P_letf2_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_getf2.P_getf2_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatsitf.P_floatsitf_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatunsitf.P_floatunsitf_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_pop_arg.F_extenddftf2.P_extenddftf2_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbn.P_scalbn_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_letf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_letf2_callv0_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_fixunstfsi_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatsitf_callp_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatunsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatunsitf_callfix_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_extenddftf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_multf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_divtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_addtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_subtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_frexpl_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_signbitl_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_fpclassifyl_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_A.P_shlim_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_A.P_toread_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_B.P_sread_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc.P_uflow_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc.P_shgetc_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_rfile.P_shgetc_callJ_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbnl.P_scalbnl_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbnl.P_fabsl_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbnl.P_copysignl_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.F_fmodl.P_rfmodl_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_scanexp.P_scanexp_rspec_c.
(* [comment removed for export] *)
#[local] Existing Instance OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgP.P_img.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAtT _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAt _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RoB _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelCode _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelSym _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelNear _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 2 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.ZFact _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
(* [comment removed for export] *)
Local Ltac gonly_lia := let HI := fresh "HI" in pose proof I as HI; clear - HI; Zify.zify; xlia zchecker.
Local Ltac gonly_refute := lazymatch goal with |- ?G => assert (~ G) by gonly_lia end.
(* [comment removed for export] *)
Local Ltac flia ::= first [ assumption | slim; lia ].


(* [comment removed for export] *)
Local Strategy 1000 [FUEL_RING FUEL_SCALE df_dnk_loop df_dn_loop df_dni_loop df_upk_loop df_up_loop df_tz_loop df_al_loop df_pad_loop df_asm_loop df_dig_loop df_rz_loop df_lz_loop].
End F_floatscan_N3E8.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_floatscan_N484.
Module F_floatscan_N484.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.StrFun OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan.DoubleOps OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScanProps OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan_nn.FloatScan_split OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan_split2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls.F_fmt_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Shgetc_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_facts3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_strnlen.F_memchr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_multf3_tail OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_multf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_divtf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.F_divtf3_main OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3.F_addtf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_letf2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_getf2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatsitf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatunsitf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_pop_arg.F_extenddftf2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbn OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_rscan_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_rfile OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbnl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.F_fmodl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_scanexp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_rscan_model.F_rscan_facts.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.


#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_memcpy.P_memcpy_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_strnlen.F_memchr.P_memchr_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_multf3.P_multf3_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.F_divtf3_main.P_divtf3_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3.F_addtf3_E.P_addtf3_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3.P_subtf3_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_letf2.P_letf2_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_getf2.P_getf2_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatsitf.P_floatsitf_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatunsitf.P_floatunsitf_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_pop_arg.F_extenddftf2.P_extenddftf2_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbn.P_scalbn_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_letf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_letf2_callv0_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_fixunstfsi_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatsitf_callp_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatunsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatunsitf_callfix_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_extenddftf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_multf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_divtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_addtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_subtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_frexpl_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_signbitl_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_fpclassifyl_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_A.P_shlim_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_A.P_toread_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_B.P_sread_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc.P_uflow_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc.P_shgetc_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_rfile.P_shgetc_callJ_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbnl.P_scalbnl_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbnl.P_fabsl_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbnl.P_copysignl_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.F_fmodl.P_rfmodl_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_scanexp.P_scanexp_rspec_c.
(* [comment removed for export] *)
#[local] Existing Instance OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgP.P_img.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAtT _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAt _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RoB _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelCode _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelSym _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelNear _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 2 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.ZFact _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.

(* [comment removed for export] *)
Local Ltac flia ::= first [ assumption | slim; lia ].


(* [comment removed for export] *)
Local Strategy 1000 [FUEL_RING FUEL_SCALE df_dnk_loop df_dn_loop df_dni_loop df_upk_loop df_up_loop df_tz_loop df_al_loop df_pad_loop df_asm_loop df_dig_loop df_rz_loop df_lz_loop].
End F_floatscan_N484.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_floatscan_NK.
Module F_floatscan_NK.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.StrFun OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan.DoubleOps OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScanProps OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan_nn.FloatScan_split OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan_split2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls.F_fmt_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Shgetc_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_facts3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_strnlen.F_memchr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_multf3_tail OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_multf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_divtf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.F_divtf3_main OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3.F_addtf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_letf2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_getf2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatsitf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatunsitf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_pop_arg.F_extenddftf2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbn OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_rscan_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_rfile OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbnl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.F_fmodl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_scanexp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_rscan_model.F_rscan_facts.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.


#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_memcpy.P_memcpy_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_strnlen.F_memchr.P_memchr_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_multf3.P_multf3_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.F_divtf3_main.P_divtf3_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3.F_addtf3_E.P_addtf3_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3.P_subtf3_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_letf2.P_letf2_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_getf2.P_getf2_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatsitf.P_floatsitf_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatunsitf.P_floatunsitf_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_pop_arg.F_extenddftf2.P_extenddftf2_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbn.P_scalbn_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_letf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_letf2_callv0_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_fixunstfsi_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatsitf_callp_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatunsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatunsitf_callfix_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_extenddftf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_multf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_divtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_addtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_subtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_frexpl_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_signbitl_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_fpclassifyl_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_A.P_shlim_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_A.P_toread_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_B.P_sread_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc.P_uflow_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc.P_shgetc_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_rfile.P_shgetc_callJ_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbnl.P_scalbnl_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbnl.P_fabsl_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbnl.P_copysignl_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.F_fmodl.P_rfmodl_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_scanexp.P_scanexp_rspec_c.
(* [comment removed for export] *)
#[local] Existing Instance OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgP.P_img.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAtT _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAt _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RoB _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelCode _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelSym _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelNear _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 2 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.ZFact _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.

(* [comment removed for export] *)
Local Ltac flia ::= first [ assumption | slim; lia ].


(* [comment removed for export] *)
Local Strategy 1000 [FUEL_RING FUEL_SCALE df_dnk_loop df_dn_loop df_dni_loop df_upk_loop df_up_loop df_tz_loop df_al_loop df_pad_loop df_asm_loop df_dig_loop df_rz_loop df_lz_loop].
End F_floatscan_NK.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_floatscan_P.
Module F_floatscan_P.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.StrFun OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan.DoubleOps OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScanProps OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan_nn.FloatScan_split OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan_split2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls.F_fmt_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Shgetc_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_facts3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_strnlen.F_memchr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_multf3_tail OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_multf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_divtf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.F_divtf3_main OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3.F_addtf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_letf2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_getf2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatsitf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatunsitf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_pop_arg.F_extenddftf2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbn OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_rscan_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_rfile OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbnl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.F_fmodl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_scanexp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_rscan_model.F_rscan_facts.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.


#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_memcpy.P_memcpy_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_strnlen.F_memchr.P_memchr_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_multf3.P_multf3_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.F_divtf3_main.P_divtf3_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3.F_addtf3_E.P_addtf3_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3.P_subtf3_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_letf2.P_letf2_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_getf2.P_getf2_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatsitf.P_floatsitf_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatunsitf.P_floatunsitf_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_pop_arg.F_extenddftf2.P_extenddftf2_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbn.P_scalbn_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_letf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_letf2_callv0_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_fixunstfsi_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatsitf_callp_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatunsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatunsitf_callfix_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_extenddftf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_multf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_divtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_addtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_subtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_frexpl_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_signbitl_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_fpclassifyl_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_A.P_shlim_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_A.P_toread_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_B.P_sread_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc.P_uflow_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc.P_shgetc_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_rfile.P_shgetc_callJ_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbnl.P_scalbnl_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbnl.P_fabsl_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbnl.P_copysignl_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.F_fmodl.P_rfmodl_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_scanexp.P_scanexp_rspec_c.
(* [comment removed for export] *)
#[local] Existing Instance OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgP.P_img.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAtT _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAt _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RoB _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelCode _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelSym _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelNear _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 2 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.ZFact _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.

(* [comment removed for export] *)
Local Ltac flia ::= first [ assumption | slim; lia ].


(* [comment removed for export] *)
Local Strategy 1000 [FUEL_RING FUEL_SCALE df_dnk_loop df_dn_loop df_dni_loop df_upk_loop df_up_loop df_tz_loop df_al_loop df_pad_loop df_asm_loop df_dig_loop df_rz_loop df_lz_loop].
End F_floatscan_P.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_floatscan_R.
Module F_floatscan_R.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.StrFun OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan.DoubleOps OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScanProps OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan_nn.FloatScan_split OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan_split2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls.F_fmt_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Shgetc_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_facts3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_strnlen.F_memchr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_multf3_tail OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_multf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_divtf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.F_divtf3_main OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3.F_addtf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_letf2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_getf2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatsitf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatunsitf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_pop_arg.F_extenddftf2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbn OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_rscan_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_rfile OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbnl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.F_fmodl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_scanexp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_rscan_model.F_rscan_facts.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.


#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_memcpy.P_memcpy_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_strnlen.F_memchr.P_memchr_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_multf3.P_multf3_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.F_divtf3_main.P_divtf3_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3.F_addtf3_E.P_addtf3_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3.P_subtf3_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_letf2.P_letf2_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_getf2.P_getf2_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatsitf.P_floatsitf_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatunsitf.P_floatunsitf_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_pop_arg.F_extenddftf2.P_extenddftf2_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbn.P_scalbn_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_letf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_letf2_callv0_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_fixunstfsi_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatsitf_callp_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatunsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatunsitf_callfix_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_extenddftf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_multf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_divtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_addtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_subtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_frexpl_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_signbitl_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_fpclassifyl_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_A.P_shlim_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_A.P_toread_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_B.P_sread_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc.P_uflow_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc.P_shgetc_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_rfile.P_shgetc_callJ_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbnl.P_scalbnl_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbnl.P_fabsl_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbnl.P_copysignl_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.F_fmodl.P_rfmodl_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_scanexp.P_scanexp_rspec_c.
(* [comment removed for export] *)
#[local] Existing Instance OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgP.P_img.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAtT _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAt _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RoB _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelCode _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelSym _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelNear _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 2 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.ZFact _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
(* [comment removed for export] *)
Local Ltac gonly_lia := let HI := fresh "HI" in pose proof I as HI; clear - HI; Zify.zify; xlia zchecker.
Local Ltac gonly_refute := lazymatch goal with |- ?G => assert (~ G) by gonly_lia end.
(* [comment removed for export] *)
Local Ltac flia ::= first [ assumption | slim; lia ].


(* [comment removed for export] *)
Local Strategy 1000 [FUEL_RING FUEL_SCALE df_dnk_loop df_dn_loop df_dni_loop df_upk_loop df_up_loop df_tz_loop df_al_loop df_pad_loop df_asm_loop df_dig_loop df_rz_loop df_lz_loop].

(* [comment removed for export] *)
Local Ltac nat_diet ::= repeat nat_diet_step;
  lazymatch goal with _ : Z.of_nat (natZ _) = _ |- _ => idtac | _ =>
    repeat match goal with H : context [natZ (Zpos ?p)] |- _ =>
      lazymatch goal with _ : Z.of_nat (natZ (Zpos p)) = _ |- _ => fail | _ => pose proof (natZ_pos p) end end end.
End F_floatscan_R.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_floatscan_T.
Module F_floatscan_T.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.StrFun OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan.DoubleOps OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScanProps OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan_nn.FloatScan_split OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan_split2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls.F_fmt_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Shgetc_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_facts3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_strnlen.F_memchr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_multf3_tail OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_multf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_divtf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.F_divtf3_main OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3.F_addtf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_letf2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_getf2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatsitf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatunsitf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_pop_arg.F_extenddftf2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbn OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_rscan_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_rfile OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbnl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.F_fmodl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_scanexp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_rscan_model.F_rscan_facts.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.


#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_memcpy.P_memcpy_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_strnlen.F_memchr.P_memchr_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_multf3.P_multf3_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.F_divtf3_main.P_divtf3_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3.F_addtf3_E.P_addtf3_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3.P_subtf3_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_letf2.P_letf2_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_getf2.P_getf2_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatsitf.P_floatsitf_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatunsitf.P_floatunsitf_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_pop_arg.F_extenddftf2.P_extenddftf2_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbn.P_scalbn_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_letf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_letf2_callv0_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_fixunstfsi_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatsitf_callp_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatunsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatunsitf_callfix_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_extenddftf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_multf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_divtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_addtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_subtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_frexpl_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_signbitl_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_fpclassifyl_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_A.P_shlim_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_A.P_toread_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_B.P_sread_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc.P_uflow_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc.P_shgetc_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_rfile.P_shgetc_callJ_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbnl.P_scalbnl_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbnl.P_fabsl_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbnl.P_copysignl_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.F_fmodl.P_rfmodl_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_scanexp.P_scanexp_rspec_c.
(* [comment removed for export] *)
#[local] Existing Instance OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgP.P_img.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAtT _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAt _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RoB _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelCode _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelSym _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelNear _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 2 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.ZFact _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.

(* [comment removed for export] *)
Local Ltac flia ::= first [ assumption | slim; lia ].


(* [comment removed for export] *)
Local Strategy 1000 [FUEL_RING FUEL_SCALE df_dnk_loop df_dn_loop df_dni_loop df_upk_loop df_up_loop df_tz_loop df_al_loop df_pad_loop df_asm_loop df_dig_loop df_rz_loop df_lz_loop].

(* [comment removed for export] *)
Local Ltac nat_diet ::= repeat nat_diet_step;
  lazymatch goal with _ : Z.of_nat (natZ _) = _ |- _ => idtac | _ =>
    repeat match goal with H : context [natZ (Zpos ?p)] |- _ =>
      lazymatch goal with _ : Z.of_nat (natZ (Zpos p)) = _ |- _ => fail | _ => pose proof (natZ_pos p) end end end.
End F_floatscan_T.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_floatscan_U.
Module F_floatscan_U.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.StrFun OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan.DoubleOps OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScanProps OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan_nn.FloatScan_split OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan_split2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls.F_fmt_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Shgetc_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_facts3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_strnlen.F_memchr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_multf3_tail OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_multf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_divtf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.F_divtf3_main OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3.F_addtf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_letf2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_getf2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatsitf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatunsitf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_pop_arg.F_extenddftf2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbn OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_rscan_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_rfile OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbnl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.F_fmodl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_scanexp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_rscan_model.F_rscan_facts.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.


#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_memcpy.P_memcpy_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_strnlen.F_memchr.P_memchr_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_multf3.P_multf3_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.F_divtf3_main.P_divtf3_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3.F_addtf3_E.P_addtf3_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3.P_subtf3_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_letf2.P_letf2_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_getf2.P_getf2_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatsitf.P_floatsitf_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatunsitf.P_floatunsitf_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_pop_arg.F_extenddftf2.P_extenddftf2_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbn.P_scalbn_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_letf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_letf2_callv0_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_fixunstfsi_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatsitf_callp_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatunsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatunsitf_callfix_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_extenddftf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_multf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_divtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_addtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_subtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_frexpl_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_signbitl_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_fpclassifyl_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_A.P_shlim_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_A.P_toread_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_B.P_sread_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc.P_uflow_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc.P_shgetc_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_rfile.P_shgetc_callJ_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbnl.P_scalbnl_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbnl.P_fabsl_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbnl.P_copysignl_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.F_fmodl.P_rfmodl_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_scanexp.P_scanexp_rspec_c.
(* [comment removed for export] *)
#[local] Existing Instance OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgP.P_img.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAtT _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAt _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RoB _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelCode _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelSym _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelNear _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 2 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.ZFact _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.

(* [comment removed for export] *)
Local Ltac flia ::= first [ assumption | slim; lia ].


(* [comment removed for export] *)
Local Strategy 1000 [FUEL_RING FUEL_SCALE df_dnk_loop df_dn_loop df_dni_loop df_upk_loop df_up_loop df_tz_loop df_al_loop df_pad_loop df_asm_loop df_dig_loop df_rz_loop df_lz_loop].
End F_floatscan_U.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_floatscan_UK.
Module F_floatscan_UK.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.StrFun OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan.DoubleOps OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScanProps OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan_nn.FloatScan_split OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan_split2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls.F_fmt_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Shgetc_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_facts3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_strnlen.F_memchr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_multf3_tail OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_multf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_divtf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.F_divtf3_main OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3.F_addtf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_letf2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_getf2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatsitf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatunsitf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_pop_arg.F_extenddftf2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbn OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_rscan_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_rfile OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbnl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.F_fmodl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_scanexp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_rscan_model.F_rscan_facts.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.


#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_memcpy.P_memcpy_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_strnlen.F_memchr.P_memchr_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_multf3.P_multf3_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.F_divtf3_main.P_divtf3_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3.F_addtf3_E.P_addtf3_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3.P_subtf3_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_letf2.P_letf2_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_getf2.P_getf2_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatsitf.P_floatsitf_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatunsitf.P_floatunsitf_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_pop_arg.F_extenddftf2.P_extenddftf2_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbn.P_scalbn_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_letf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_letf2_callv0_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_fixunstfsi_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatsitf_callp_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatunsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatunsitf_callfix_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_extenddftf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_multf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_divtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_addtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_subtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_frexpl_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_signbitl_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_fpclassifyl_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_A.P_shlim_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_A.P_toread_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_B.P_sread_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc.P_uflow_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc.P_shgetc_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_rfile.P_shgetc_callJ_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbnl.P_scalbnl_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbnl.P_fabsl_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbnl.P_copysignl_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.F_fmodl.P_rfmodl_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_scanexp.P_scanexp_rspec_c.
(* [comment removed for export] *)
#[local] Existing Instance OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgP.P_img.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAtT _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAt _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RoB _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelCode _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelSym _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelNear _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 2 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.ZFact _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.

(* [comment removed for export] *)
Local Ltac flia ::= first [ assumption | slim; lia ].


(* [comment removed for export] *)
Local Strategy 1000 [FUEL_RING FUEL_SCALE df_dnk_loop df_dn_loop df_dni_loop df_upk_loop df_up_loop df_tz_loop df_al_loop df_pad_loop df_asm_loop df_dig_loop df_rz_loop df_lz_loop].
End F_floatscan_UK.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_floatscan_W1.
Module F_floatscan_W1.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.StrFun OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan.DoubleOps OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScanProps OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan_nn.FloatScan_split OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan_split2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls.F_fmt_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Shgetc_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_facts3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_strnlen.F_memchr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_multf3_tail OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_multf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_divtf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.F_divtf3_main OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3.F_addtf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_letf2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_getf2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatsitf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatunsitf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_pop_arg.F_extenddftf2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbn OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_rscan_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_rfile OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbnl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.F_fmodl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_scanexp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_rscan_model.F_rscan_facts.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.


#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_memcpy.P_memcpy_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_strnlen.F_memchr.P_memchr_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_multf3.P_multf3_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.F_divtf3_main.P_divtf3_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3.F_addtf3_E.P_addtf3_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3.P_subtf3_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_letf2.P_letf2_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_getf2.P_getf2_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatsitf.P_floatsitf_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatunsitf.P_floatunsitf_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_pop_arg.F_extenddftf2.P_extenddftf2_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbn.P_scalbn_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_letf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_letf2_callv0_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_fixunstfsi_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatsitf_callp_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatunsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatunsitf_callfix_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_extenddftf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_multf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_divtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_addtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_subtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_frexpl_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_signbitl_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_fpclassifyl_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_A.P_shlim_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_A.P_toread_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_B.P_sread_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc.P_uflow_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc.P_shgetc_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_rfile.P_shgetc_callJ_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbnl.P_scalbnl_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbnl.P_fabsl_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbnl.P_copysignl_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.F_fmodl.P_rfmodl_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_scanexp.P_scanexp_rspec_c.
(* [comment removed for export] *)
#[local] Existing Instance OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgP.P_img.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAtT _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAt _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RoB _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelCode _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelSym _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelNear _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 2 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.ZFact _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
(* [comment removed for export] *)
Local Ltac mem_after_store ::= mem_after_store_cached.
Local Ltac addr_eq_tac ::= addr_eq_tac_cached.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_cached segs m m' MU WM.
Local Ltac sc_clear := repeat match goal with H : sc_dj _ _ _ _ |- _ => clear H | H : sc_in _ _ _ |- _ => clear H
  | H : sc_no _ _ _ _ |- _ => clear H | H : sc_noin _ _ _ |- _ => clear H end.
(* [comment removed for export] *)
Local Ltac gonly_lia := let HI := fresh "HI" in pose proof I as HI; clear - HI; Zify.zify; xlia zchecker.
Local Ltac gonly_refute := lazymatch goal with |- ?G => assert (~ G) by gonly_lia end.
(* [comment removed for export] *)
Local Ltac flia ::= first [ assumption | slim; lia ].


(* [comment removed for export] *)
Local Strategy 1000 [FUEL_RING FUEL_SCALE df_dnk_loop df_dn_loop df_dni_loop df_upk_loop df_up_loop df_tz_loop df_al_loop df_pad_loop df_asm_loop df_dig_loop df_rz_loop df_lz_loop].

(* [comment removed for export] *)
Local Ltac nat_diet ::= repeat nat_diet_step;
  lazymatch goal with _ : Z.of_nat (natZ _) = _ |- _ => idtac | _ =>
    repeat match goal with H : context [natZ (Zpos ?p)] |- _ =>
      lazymatch goal with _ : Z.of_nat (natZ (Zpos p)) = _ |- _ => fail | _ => pose proof (natZ_pos p) end end end.
End F_floatscan_W1.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_floatscan_W2.
Module F_floatscan_W2.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.StrFun OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan.DoubleOps OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScanProps OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan_nn.FloatScan_split OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan_split2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls.F_fmt_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Shgetc_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_facts3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_strnlen.F_memchr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_multf3_tail OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_multf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_divtf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.F_divtf3_main OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3.F_addtf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_letf2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_getf2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatsitf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatunsitf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_pop_arg.F_extenddftf2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbn OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_rscan_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_rfile OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbnl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.F_fmodl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_scanexp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_rscan_model.F_rscan_facts.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.


#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_memcpy.P_memcpy_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_strnlen.F_memchr.P_memchr_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_multf3.P_multf3_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.F_divtf3_main.P_divtf3_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3.F_addtf3_E.P_addtf3_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3.P_subtf3_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_letf2.P_letf2_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_getf2.P_getf2_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatsitf.P_floatsitf_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatunsitf.P_floatunsitf_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_pop_arg.F_extenddftf2.P_extenddftf2_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbn.P_scalbn_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_letf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_letf2_callv0_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_fixunstfsi_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatsitf_callp_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatunsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatunsitf_callfix_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_extenddftf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_multf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_divtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_addtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_subtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_frexpl_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_signbitl_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_fpclassifyl_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_A.P_shlim_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_A.P_toread_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_B.P_sread_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc.P_uflow_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc.P_shgetc_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_rfile.P_shgetc_callJ_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbnl.P_scalbnl_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbnl.P_fabsl_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbnl.P_copysignl_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.F_fmodl.P_rfmodl_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_scanexp.P_scanexp_rspec_c.
(* [comment removed for export] *)
#[local] Existing Instance OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgP.P_img.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAtT _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAt _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RoB _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelCode _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelSym _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelNear _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 2 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.ZFact _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
(* [comment removed for export] *)
Local Ltac mem_after_store ::= mem_after_store_cached.
Local Ltac addr_eq_tac ::= addr_eq_tac_cached.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_cached segs m m' MU WM.
Local Ltac sc_clear := repeat match goal with H : sc_dj _ _ _ _ |- _ => clear H | H : sc_in _ _ _ |- _ => clear H
  | H : sc_no _ _ _ _ |- _ => clear H | H : sc_noin _ _ _ |- _ => clear H end.
(* [comment removed for export] *)
Local Ltac gonly_lia := let HI := fresh "HI" in pose proof I as HI; clear - HI; Zify.zify; xlia zchecker.
Local Ltac gonly_refute := lazymatch goal with |- ?G => assert (~ G) by gonly_lia end.
(* [comment removed for export] *)
Local Ltac flia ::= first [ assumption | slim; lia ].


(* [comment removed for export] *)
Local Strategy 1000 [FUEL_RING FUEL_SCALE df_dnk_loop df_dn_loop df_dni_loop df_upk_loop df_up_loop df_tz_loop df_al_loop df_pad_loop df_asm_loop df_dig_loop df_rz_loop df_lz_loop].

(* [comment removed for export] *)
Local Ltac nat_diet ::= repeat nat_diet_step;
  lazymatch goal with _ : Z.of_nat (natZ _) = _ |- _ => idtac | _ =>
    repeat match goal with H : context [natZ (Zpos ?p)] |- _ =>
      lazymatch goal with _ : Z.of_nat (natZ (Zpos p)) = _ |- _ => fail | _ => pose proof (natZ_pos p) end end end.
End F_floatscan_W2.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_floatscan_W3.
Module F_floatscan_W3.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.StrFun OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan.DoubleOps OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScanProps OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan_nn.FloatScan_split OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan_split2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls.F_fmt_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Shgetc_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_facts3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_strnlen.F_memchr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_multf3_tail OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_multf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_divtf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.F_divtf3_main OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3.F_addtf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_letf2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_getf2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatsitf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatunsitf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_pop_arg.F_extenddftf2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbn OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_rscan_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_rfile OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbnl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.F_fmodl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_scanexp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_rscan_model.F_rscan_facts.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.


#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_memcpy.P_memcpy_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_strnlen.F_memchr.P_memchr_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_multf3.P_multf3_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.F_divtf3_main.P_divtf3_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3.F_addtf3_E.P_addtf3_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3.P_subtf3_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_letf2.P_letf2_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_getf2.P_getf2_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatsitf.P_floatsitf_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatunsitf.P_floatunsitf_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_pop_arg.F_extenddftf2.P_extenddftf2_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbn.P_scalbn_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_letf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_letf2_callv0_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_fixunstfsi_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatsitf_callp_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatunsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatunsitf_callfix_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_extenddftf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_multf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_divtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_addtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_subtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_frexpl_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_signbitl_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_fpclassifyl_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_A.P_shlim_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_A.P_toread_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_B.P_sread_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc.P_uflow_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc.P_shgetc_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_rfile.P_shgetc_callJ_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbnl.P_scalbnl_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbnl.P_fabsl_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbnl.P_copysignl_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.F_fmodl.P_rfmodl_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_scanexp.P_scanexp_rspec_c.
(* [comment removed for export] *)
#[local] Existing Instance OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgP.P_img.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAtT _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAt _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RoB _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelCode _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelSym _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelNear _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 2 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.ZFact _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
(* [comment removed for export] *)
Local Ltac mem_after_store ::= mem_after_store_cached.
Local Ltac addr_eq_tac ::= addr_eq_tac_cached.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_cached segs m m' MU WM.
Local Ltac sc_clear := repeat match goal with H : sc_dj _ _ _ _ |- _ => clear H | H : sc_in _ _ _ |- _ => clear H
  | H : sc_no _ _ _ _ |- _ => clear H | H : sc_noin _ _ _ |- _ => clear H end.
(* [comment removed for export] *)
Local Ltac gonly_lia := let HI := fresh "HI" in pose proof I as HI; clear - HI; Zify.zify; xlia zchecker.
Local Ltac gonly_refute := lazymatch goal with |- ?G => assert (~ G) by gonly_lia end.
(* [comment removed for export] *)
Local Ltac flia ::= first [ assumption | slim; lia ].


(* [comment removed for export] *)
Local Strategy 1000 [FUEL_RING FUEL_SCALE df_dnk_loop df_dn_loop df_dni_loop df_upk_loop df_up_loop df_tz_loop df_al_loop df_pad_loop df_asm_loop df_dig_loop df_rz_loop df_lz_loop].

(* [comment removed for export] *)
Local Ltac nat_diet ::= repeat nat_diet_step;
  lazymatch goal with _ : Z.of_nat (natZ _) = _ |- _ => idtac | _ =>
    repeat match goal with H : context [natZ (Zpos ?p)] |- _ =>
      lazymatch goal with _ : Z.of_nat (natZ (Zpos p)) = _ |- _ => fail | _ => pose proof (natZ_pos p) end end end.
End F_floatscan_W3.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_floatscan_W4.
Module F_floatscan_W4.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.StrFun OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan.DoubleOps OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScanProps OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan_nn.FloatScan_split OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan_split2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls.F_fmt_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Shgetc_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_facts3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_strnlen.F_memchr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_multf3_tail OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_multf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_divtf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.F_divtf3_main OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3.F_addtf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_letf2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_getf2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatsitf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatunsitf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_pop_arg.F_extenddftf2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbn OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_rscan_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_rfile OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbnl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.F_fmodl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_scanexp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_rscan_model.F_rscan_facts.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.


#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_memcpy.P_memcpy_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_strnlen.F_memchr.P_memchr_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_multf3.P_multf3_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.F_divtf3_main.P_divtf3_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3.F_addtf3_E.P_addtf3_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3.P_subtf3_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_letf2.P_letf2_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_getf2.P_getf2_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatsitf.P_floatsitf_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatunsitf.P_floatunsitf_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_pop_arg.F_extenddftf2.P_extenddftf2_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbn.P_scalbn_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_letf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_letf2_callv0_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_fixunstfsi_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatsitf_callp_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatunsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatunsitf_callfix_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_extenddftf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_multf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_divtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_addtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_subtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_frexpl_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_signbitl_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_fpclassifyl_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_A.P_shlim_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_A.P_toread_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_B.P_sread_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc.P_uflow_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc.P_shgetc_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_rfile.P_shgetc_callJ_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbnl.P_scalbnl_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbnl.P_fabsl_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbnl.P_copysignl_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.F_fmodl.P_rfmodl_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_scanexp.P_scanexp_rspec_c.
(* [comment removed for export] *)
#[local] Existing Instance OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgP.P_img.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAtT _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAt _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RoB _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelCode _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelSym _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelNear _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 2 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.ZFact _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
(* [comment removed for export] *)
Local Ltac mem_after_store ::= mem_after_store_cached.
Local Ltac addr_eq_tac ::= addr_eq_tac_cached.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_cached segs m m' MU WM.
Local Ltac sc_clear := repeat match goal with H : sc_dj _ _ _ _ |- _ => clear H | H : sc_in _ _ _ |- _ => clear H
  | H : sc_no _ _ _ _ |- _ => clear H | H : sc_noin _ _ _ |- _ => clear H end.
(* [comment removed for export] *)
Local Ltac gonly_lia := let HI := fresh "HI" in pose proof I as HI; clear - HI; Zify.zify; xlia zchecker.
Local Ltac gonly_refute := lazymatch goal with |- ?G => assert (~ G) by gonly_lia end.
(* [comment removed for export] *)
Local Ltac flia ::= first [ assumption | slim; lia ].


(* [comment removed for export] *)
Local Strategy 1000 [FUEL_RING FUEL_SCALE df_dnk_loop df_dn_loop df_dni_loop df_upk_loop df_up_loop df_tz_loop df_al_loop df_pad_loop df_asm_loop df_dig_loop df_rz_loop df_lz_loop].
End F_floatscan_W4.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_floatscan.
Module F_floatscan.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.StrFun OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan.DoubleOps OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScanProps OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan_nn.FloatScan_split OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan_split2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls.F_fmt_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Shgetc_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_facts3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_strnlen.F_memchr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_multf3_tail OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_multf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_divtf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.F_divtf3_main OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3.F_addtf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_letf2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_getf2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatsitf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatunsitf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_pop_arg.F_extenddftf2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbn OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_rscan_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_rfile OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbnl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.F_fmodl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_scanexp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_rscan_model.F_rscan_facts.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg.
Export OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.


#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_memcpy.P_memcpy_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_strnlen.F_memchr.P_memchr_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_multf3.P_multf3_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.F_divtf3_main.P_divtf3_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3.F_addtf3_E.P_addtf3_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3.P_subtf3_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_letf2.P_letf2_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_getf2.P_getf2_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatsitf.P_floatsitf_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatunsitf.P_floatunsitf_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_pop_arg.F_extenddftf2.P_extenddftf2_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbn.P_scalbn_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_letf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_letf2_callv0_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_fixunstfsi_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatsitf_callp_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatunsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatunsitf_callfix_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_extenddftf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_multf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_divtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_addtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_subtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_frexpl_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_signbitl_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_fpclassifyl_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_A.P_shlim_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_A.P_toread_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_B.P_sread_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc.P_uflow_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc.P_shgetc_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_rfile.P_shgetc_callJ_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbnl.P_scalbnl_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbnl.P_fabsl_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbnl.P_copysignl_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.F_fmodl.P_rfmodl_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_scanexp.P_scanexp_rspec_c.
(* [comment removed for export] *)
#[local] Existing Instance OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgP.P_img.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAtT _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAt _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RoB _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelCode _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelSym _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelNear _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 2 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.ZFact _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.

(* [comment removed for export] *)


(* [comment removed for export] *)
Local Strategy 1000 [FUEL_RING FUEL_SCALE df_dnk_loop df_dn_loop df_dni_loop df_upk_loop df_up_loop df_tz_loop df_al_loop df_pad_loop df_asm_loop df_dig_loop df_rz_loop df_lz_loop].
#[export] Instance P_L_ENTRY_c : OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_floatscan.L_ENTRY_c := OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_floatscan.L_ENTRY_c_ok.
End F_floatscan.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_trunctfdf2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_rscan_shape.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_vfscanf_A.
Module F_vfscanf_A.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.StrFun OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan.DoubleOps OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScanProps OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan_nn.FloatScan_split OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan_split2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls.F_fmt_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Shgetc_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_facts3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_strnlen.F_memchr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_multf3_tail OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_multf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_divtf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.F_divtf3_main OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3.F_addtf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_letf2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_getf2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatsitf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatunsitf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_pop_arg.F_extenddftf2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbn OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_trunctfdf2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_rscan_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_rfile OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_rscan_model.F_rscan_facts OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_rscan_model OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_rscan_shape.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg.
Import ListNotations.
Open Scope bv_scope.
(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.


#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_memcpy.P_memcpy_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_strnlen.F_memchr.P_memchr_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_multf3.P_multf3_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.F_divtf3_main.P_divtf3_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3.F_addtf3_E.P_addtf3_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3.P_subtf3_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_letf2.P_letf2_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_getf2.P_getf2_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatsitf.P_floatsitf_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatunsitf.P_floatunsitf_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_pop_arg.F_extenddftf2.P_extenddftf2_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbn.P_scalbn_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_trunctfdf2.P_trunctfdf2_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_letf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_letf2_callv0_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_fixunstfsi_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatsitf_callp_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatunsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatunsitf_callfix_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_extenddftf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_multf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_divtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_addtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_subtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_frexpl_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_signbitl_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_fpclassifyl_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_A.P_shlim_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_A.P_toread_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_B.P_sread_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc.P_uflow_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc.P_shgetc_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_rfile.P_shgetc_callJ_c F_floatscan.P_L_ENTRY_c.
(* [comment removed for export] *)
#[local] Existing Instance OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgP.P_img.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAtT _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAt _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RoB _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelCode _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelSym _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelNear _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 2 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.ZFact _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
(* [comment removed for export] *)
Local Ltac mem_after_store ::= mem_after_store_cached.
Local Ltac addr_eq_tac ::= addr_eq_tac_cached.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_cached segs m m' MU WM.
Local Ltac sc_clear := repeat match goal with H : sc_dj _ _ _ _ |- _ => clear H | H : sc_in _ _ _ |- _ => clear H
  | H : sc_no _ _ _ _ |- _ => clear H | H : sc_noin _ _ _ |- _ => clear H end.
(* [comment removed for export] *)
Local Ltac gonly_lia := let HI := fresh "HI" in pose proof I as HI; clear - HI; Zify.zify; xlia zchecker.
Local Ltac gonly_refute := lazymatch goal with |- ?G => assert (~ G) by gonly_lia end.
Local Ltac tslia ::= first [ exact I | gonly_lia | gonly_refute; fail 1 | tlia | split; [ tlia | exact I ] ].
(* [comment removed for export] *)
Local Ltac flia ::= first [ assumption | slim; lia ].

(* [comment removed for export] *)

Ltac showt := let x28 := getreg 28%Z in let x29 := getreg 29%Z in let x30 := getreg 30%Z in let x31 := getreg 31%Z in
  idtac "t3=" x28; idtac "t4=" x29; idtac "t5=" x30; idtac "t6=" x31.
Ltac showall := let x10 := getreg 10%Z in let x11 := getreg 11%Z in let x12 := getreg 12%Z in let x13 := getreg 13%Z in let x14 := getreg 14%Z in let x15 := getreg 15%Z in let x16 := getreg 16%Z in let x17 := getreg 17%Z in let x5 := getreg 5%Z in let x6 := getreg 6%Z in let x7 := getreg 7%Z in let x8 := getreg 8%Z in let x9 := getreg 9%Z in let x18 := getreg 18%Z in let x19 := getreg 19%Z in let x20 := getreg 20%Z in let x21 := getreg 21%Z in let x22 := getreg 22%Z in let x23 := getreg 23%Z in let x24 := getreg 24%Z in let x25 := getreg 25%Z in let x26 := getreg 26%Z in let x27 := getreg 27%Z in let x28 := getreg 28%Z in let x29 := getreg 29%Z in let x30 := getreg 30%Z in let x31 := getreg 31%Z in let x2 := getreg 2%Z in let x1 := getreg 1%Z in
    idtac "a0=" x10; idtac "a1=" x11; idtac "a2=" x12; idtac "a3=" x13; idtac "a4=" x14; idtac "a5=" x15; idtac "a6=" x16; idtac "a7=" x17; idtac "t0=" x5; idtac "t1=" x6; idtac "t2=" x7; idtac "s0=" x8; idtac "s1=" x9; idtac "s2=" x18; idtac "s3=" x19; idtac "s4=" x20; idtac "s5=" x21; idtac "s6=" x22; idtac "s7=" x23; idtac "s8=" x24; idtac "s9=" x25; idtac "s10=" x26; idtac "s11=" x27; idtac "t3=" x28; idtac "t4=" x29; idtac "t5=" x30; idtac "t6=" x31; idtac "sp=" x2; idtac "ra=" x1.
Ltac show_hyp H := let T := type of H in idtac H ":" T.
Ltac dlia := first [lia | match goal with |- ?g => idtac "LIA FAILED:"; idtac g; fail 1 end].
Ltac plia := unfold zlength, got_ssp, ssp_guard in *; lia.
(* [comment removed for export] *)
Ltac hyp_cells :=
  lazymatch goal with |- rw_cells _ ?m ?A ?cs =>
    match goal with H : rw_cells _ m A ?cs' |- _ =>
      replace cs with cs' by (repeat (reflexivity || lazymatch goal with |- @eq Z _ _ => fail | _ => f_equal end); lia); exact H end
  end.
(* [comment removed for export] *)
Ltac fix_stk := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) =>
  match goal with H : stk _ m _ _ |- _ => let n := fresh "ST" in rename H into n end end.
Tactic Notation "callx" tactic3(tac) := callw tac; try fix_stk.

(* [comment removed for export] *)
Ltac fix_idx := repeat match goal with
  | |- context [Z_to_bv 64 (?A + Z.shiftl ?k 2)] =>
    replace (Z_to_bv 64 (A + Z.shiftl k 2)%Z) with (Z_to_bv 64 (A + 4 * k)%Z) by (rewrite (Z.shiftl_mul_pow2 k 2) by lia; f_equal; lia)
  | |- context [Z_to_bv 64 (Z.shiftl ?k 2 + ?A)] =>
    replace (Z_to_bv 64 (Z.shiftl k 2 + A)%Z) with (Z_to_bv 64 (A + 4 * k)%Z) by (rewrite (Z.shiftl_mul_pow2 k 2) by lia; f_equal; lia) end.

(* [comment removed for export] *)
Ltac eval_swraps := repeat match goal with |- context [bv_swrap 32 ?e] =>
  let v := eval vm_compute in (bv_swrap 32 e) in lazymatch isZcst v with true => change (bv_swrap 32 e) with v end end.


Definition VF_DEPTH : Z := 9136.    (* [comment removed for export] *)
Definition VFSCANF : Z := 0x1ca20.
Definition RFMT : Z := 0x102a8.      (* [comment removed for export] *)
Notation RATP := F_floatscan_common.RATP.
Notation RERRNO := F_floatscan_common.RERRNO.
End F_vfscanf_A.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_vfscanf_B.
Module F_vfscanf_B.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.StrFun OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan.DoubleOps OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScanProps OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan_nn.FloatScan_split OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan_split2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls.F_fmt_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Shgetc_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_facts3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_strnlen.F_memchr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_multf3_tail OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_multf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_divtf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.F_divtf3_main OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3.F_addtf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_letf2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_getf2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatsitf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatunsitf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_pop_arg.F_extenddftf2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbn OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_trunctfdf2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_rscan_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_rfile OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_rscan_model.F_rscan_facts OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_rscan_model OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_rscan_shape.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg.
Import ListNotations.
Open Scope bv_scope.
(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.


#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_memcpy.P_memcpy_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_strnlen.F_memchr.P_memchr_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_multf3.P_multf3_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.F_divtf3_main.P_divtf3_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3.F_addtf3_E.P_addtf3_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3.P_subtf3_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_letf2.P_letf2_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_getf2.P_getf2_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatsitf.P_floatsitf_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatunsitf.P_floatunsitf_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_pop_arg.F_extenddftf2.P_extenddftf2_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbn.P_scalbn_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_trunctfdf2.P_trunctfdf2_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_letf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_letf2_callv0_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_fixunstfsi_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatsitf_callp_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatunsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatunsitf_callfix_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_extenddftf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_multf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_divtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_addtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_subtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_frexpl_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_signbitl_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_fpclassifyl_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_A.P_shlim_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_A.P_toread_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_B.P_sread_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc.P_uflow_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc.P_shgetc_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_rfile.P_shgetc_callJ_c F_floatscan.P_L_ENTRY_c.
(* [comment removed for export] *)
#[local] Existing Instance OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgP.P_img.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAtT _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAt _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RoB _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelCode _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelSym _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelNear _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 2 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.ZFact _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
(* [comment removed for export] *)
Local Ltac mem_after_store ::= mem_after_store_cached.
Local Ltac addr_eq_tac ::= addr_eq_tac_cached.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_cached segs m m' MU WM.
Local Ltac sc_clear := repeat match goal with H : sc_dj _ _ _ _ |- _ => clear H | H : sc_in _ _ _ |- _ => clear H
  | H : sc_no _ _ _ _ |- _ => clear H | H : sc_noin _ _ _ |- _ => clear H end.
(* [comment removed for export] *)
Local Ltac gonly_lia := let HI := fresh "HI" in pose proof I as HI; clear - HI; Zify.zify; xlia zchecker.
Local Ltac gonly_refute := lazymatch goal with |- ?G => assert (~ G) by gonly_lia end.
Local Ltac tslia ::= first [ exact I | gonly_lia | gonly_refute; fail 1 | tlia | split; [ tlia | exact I ] ].
(* [comment removed for export] *)
Local Ltac flia ::= first [ assumption | slim; lia ].

(* [comment removed for export] *)

Ltac showt := let x28 := getreg 28%Z in let x29 := getreg 29%Z in let x30 := getreg 30%Z in let x31 := getreg 31%Z in
  idtac "t3=" x28; idtac "t4=" x29; idtac "t5=" x30; idtac "t6=" x31.
Ltac showall := let x10 := getreg 10%Z in let x11 := getreg 11%Z in let x12 := getreg 12%Z in let x13 := getreg 13%Z in let x14 := getreg 14%Z in let x15 := getreg 15%Z in let x16 := getreg 16%Z in let x17 := getreg 17%Z in let x5 := getreg 5%Z in let x6 := getreg 6%Z in let x7 := getreg 7%Z in let x8 := getreg 8%Z in let x9 := getreg 9%Z in let x18 := getreg 18%Z in let x19 := getreg 19%Z in let x20 := getreg 20%Z in let x21 := getreg 21%Z in let x22 := getreg 22%Z in let x23 := getreg 23%Z in let x24 := getreg 24%Z in let x25 := getreg 25%Z in let x26 := getreg 26%Z in let x27 := getreg 27%Z in let x28 := getreg 28%Z in let x29 := getreg 29%Z in let x30 := getreg 30%Z in let x31 := getreg 31%Z in let x2 := getreg 2%Z in let x1 := getreg 1%Z in
    idtac "a0=" x10; idtac "a1=" x11; idtac "a2=" x12; idtac "a3=" x13; idtac "a4=" x14; idtac "a5=" x15; idtac "a6=" x16; idtac "a7=" x17; idtac "t0=" x5; idtac "t1=" x6; idtac "t2=" x7; idtac "s0=" x8; idtac "s1=" x9; idtac "s2=" x18; idtac "s3=" x19; idtac "s4=" x20; idtac "s5=" x21; idtac "s6=" x22; idtac "s7=" x23; idtac "s8=" x24; idtac "s9=" x25; idtac "s10=" x26; idtac "s11=" x27; idtac "t3=" x28; idtac "t4=" x29; idtac "t5=" x30; idtac "t6=" x31; idtac "sp=" x2; idtac "ra=" x1.
Ltac show_hyp H := let T := type of H in idtac H ":" T.
Ltac dlia := first [lia | match goal with |- ?g => idtac "LIA FAILED:"; idtac g; fail 1 end].
Ltac plia := unfold zlength, got_ssp, ssp_guard in *; lia.
(* [comment removed for export] *)
Ltac hyp_cells :=
  lazymatch goal with |- rw_cells _ ?m ?A ?cs =>
    match goal with H : rw_cells _ m A ?cs' |- _ =>
      replace cs with cs' by (repeat (reflexivity || lazymatch goal with |- @eq Z _ _ => fail | _ => f_equal end); lia); exact H end
  end.
(* [comment removed for export] *)
Ltac fix_stk := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) =>
  match goal with H : stk _ m _ _ |- _ => let n := fresh "ST" in rename H into n end end.
Tactic Notation "callx" tactic3(tac) := callw tac; try fix_stk.

(* [comment removed for export] *)
Ltac fix_idx := repeat match goal with
  | |- context [Z_to_bv 64 (?A + Z.shiftl ?k 2)] =>
    replace (Z_to_bv 64 (A + Z.shiftl k 2)%Z) with (Z_to_bv 64 (A + 4 * k)%Z) by (rewrite (Z.shiftl_mul_pow2 k 2) by lia; f_equal; lia)
  | |- context [Z_to_bv 64 (Z.shiftl ?k 2 + ?A)] =>
    replace (Z_to_bv 64 (Z.shiftl k 2 + A)%Z) with (Z_to_bv 64 (A + 4 * k)%Z) by (rewrite (Z.shiftl_mul_pow2 k 2) by lia; f_equal; lia) end.

(* [comment removed for export] *)
Ltac eval_swraps := repeat match goal with |- context [bv_swrap 32 ?e] =>
  let v := eval vm_compute in (bv_swrap 32 e) in lazymatch isZcst v with true => change (bv_swrap 32 e) with v end end.


Definition VF_DEPTH : Z := 9136.    (* [comment removed for export] *)
Definition VFSCANF : Z := 0x1ca20.
Definition RFMT : Z := 0x102a8.      (* [comment removed for export] *)
Notation RATP := F_floatscan_common.RATP.
Notation RERRNO := F_floatscan_common.RERRNO.
End F_vfscanf_B.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_strtod.
Module F_strtod.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.StrFun OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan.DoubleOps OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScanProps OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan_nn.FloatScan_split.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls.F_fmt_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Shgetc_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_facts3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_strnlen.F_memchr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_trunctfdf2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_rscan_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_rfile OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_rscan_model.F_rscan_facts OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_rscan_model OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_rscan_shape.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg.
Import ListNotations.
Open Scope bv_scope.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.


#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_memcpy.P_memcpy_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_strnlen.F_memchr.P_memchr_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_trunctfdf2.P_trunctfdf2_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_letf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_letf2_callv0_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_fixunstfsi_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatsitf_callp_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatunsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatunsitf_callfix_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_extenddftf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_multf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_divtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_addtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_subtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_frexpl_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_signbitl_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_fpclassifyl_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_A.P_shlim_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_A.P_toread_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_B.P_sread_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc.P_uflow_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc.P_shgetc_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_rfile.P_shgetc_callJ_c F_floatscan.P_L_ENTRY_c.
(* [comment removed for export] *)
#[local] Existing Instance OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgP.P_img.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAtT _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAt _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RoB _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelCode _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelSym _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelNear _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 2 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.ZFact _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
(* [comment removed for export] *)
Local Ltac mem_after_store ::= mem_after_store_cached.
Local Ltac addr_eq_tac ::= addr_eq_tac_cached.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_cached segs m m' MU WM.
Local Ltac sc_clear := repeat match goal with H : sc_dj _ _ _ _ |- _ => clear H | H : sc_in _ _ _ |- _ => clear H
  | H : sc_no _ _ _ _ |- _ => clear H | H : sc_noin _ _ _ |- _ => clear H end.
(* [comment removed for export] *)
Local Ltac gonly_lia := let HI := fresh "HI" in pose proof I as HI; clear - HI; Zify.zify; xlia zchecker.
Local Ltac gonly_refute := lazymatch goal with |- ?G => assert (~ G) by gonly_lia end.
Local Ltac tslia ::= first [ exact I | gonly_lia | gonly_refute; fail 1 | tlia | split; [ tlia | exact I ] ].

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)

Ltac hush := idtac.
Ltac zs := zstep; try (fix_litstore; mem_after_store_opt).
Ltac br K := if_cases K; zify_cond K; try (rewrite ?signed_of_Z in K by lia); try (exfalso; lia).
Tactic Notation "callx" tactic3(tac) := callw tac; try (lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) => match goal with H : stk _ m _ _ |- _ => let n := fresh "ST" in rename H into n end end).

Theorem rstrtod_proof : rstrtod_stmt.
Proof. first [ exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_strtod.rstrtod_proof | (pose proof OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_strtod.rstrtod_proof as T_; exact T_) | exact @OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_strtod.rstrtod_proof | apply OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_strtod.rstrtod_proof | (apply (@OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_strtod.rstrtod_proof OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgP.P_img); typeclasses eauto) ]. Qed.
#[export] Instance P_rstrtod_proof_c : OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_strtod.rstrtod_proof_c := OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_strtod.rstrtod_proof_c_ok.
End F_strtod.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_vfscanf.
Module F_vfscanf.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.StrFun OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan.DoubleOps OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScanProps OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan_nn.FloatScan_split OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan_split2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls.F_fmt_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Shgetc_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_facts3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_strnlen.F_memchr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_multf3_tail OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_multf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_divtf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.F_divtf3_main OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3.F_addtf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_letf2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_getf2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatsitf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatunsitf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_pop_arg.F_extenddftf2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbn OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_trunctfdf2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_rscan_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_rfile OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_rscan_model.F_rscan_facts OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_rscan_model OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_rscan_shape.


Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg.
Import ListNotations.
Open Scope bv_scope.
(* [comment removed for export] *)
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.


#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_memcpy.P_memcpy_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_strnlen.F_memchr.P_memchr_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_multf3.P_multf3_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatscan_common.F_divtf3_main.P_divtf3_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3.F_addtf3_E.P_addtf3_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3.P_subtf3_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_letf2.P_letf2_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_getf2.P_getf2_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatsitf.P_floatsitf_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatunsitf.P_floatunsitf_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_pop_arg.F_extenddftf2.P_extenddftf2_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbn.P_scalbn_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_trunctfdf2.P_trunctfdf2_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_letf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_letf2_callv0_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_fixunstfsi_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatsitf_callp_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatunsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatunsitf_callfix_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_extenddftf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_multf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_divtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_addtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_subtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_frexpl_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_signbitl_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_fpclassifyl_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_A.P_shlim_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_A.P_toread_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_B.P_sread_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc.P_uflow_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc.P_shgetc_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_rfile.P_shgetc_callJ_c F_floatscan.P_L_ENTRY_c.
(* [comment removed for export] *)
#[local] Existing Instance OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgP.P_img.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAtT _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAt _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RoB _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelCode _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelSym _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelNear _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 2 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.ZFact _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.

(* [comment removed for export] *)

Ltac showt := let x28 := getreg 28%Z in let x29 := getreg 29%Z in let x30 := getreg 30%Z in let x31 := getreg 31%Z in
  idtac "t3=" x28; idtac "t4=" x29; idtac "t5=" x30; idtac "t6=" x31.
Ltac showall := let x10 := getreg 10%Z in let x11 := getreg 11%Z in let x12 := getreg 12%Z in let x13 := getreg 13%Z in let x14 := getreg 14%Z in let x15 := getreg 15%Z in let x16 := getreg 16%Z in let x17 := getreg 17%Z in let x5 := getreg 5%Z in let x6 := getreg 6%Z in let x7 := getreg 7%Z in let x8 := getreg 8%Z in let x9 := getreg 9%Z in let x18 := getreg 18%Z in let x19 := getreg 19%Z in let x20 := getreg 20%Z in let x21 := getreg 21%Z in let x22 := getreg 22%Z in let x23 := getreg 23%Z in let x24 := getreg 24%Z in let x25 := getreg 25%Z in let x26 := getreg 26%Z in let x27 := getreg 27%Z in let x28 := getreg 28%Z in let x29 := getreg 29%Z in let x30 := getreg 30%Z in let x31 := getreg 31%Z in let x2 := getreg 2%Z in let x1 := getreg 1%Z in
    idtac "a0=" x10; idtac "a1=" x11; idtac "a2=" x12; idtac "a3=" x13; idtac "a4=" x14; idtac "a5=" x15; idtac "a6=" x16; idtac "a7=" x17; idtac "t0=" x5; idtac "t1=" x6; idtac "t2=" x7; idtac "s0=" x8; idtac "s1=" x9; idtac "s2=" x18; idtac "s3=" x19; idtac "s4=" x20; idtac "s5=" x21; idtac "s6=" x22; idtac "s7=" x23; idtac "s8=" x24; idtac "s9=" x25; idtac "s10=" x26; idtac "s11=" x27; idtac "t3=" x28; idtac "t4=" x29; idtac "t5=" x30; idtac "t6=" x31; idtac "sp=" x2; idtac "ra=" x1.
Ltac show_hyp H := let T := type of H in idtac H ":" T.
Ltac dlia := first [lia | match goal with |- ?g => idtac "LIA FAILED:"; idtac g; fail 1 end].
Ltac plia := unfold zlength, got_ssp, ssp_guard in *; lia.
(* [comment removed for export] *)
Ltac hyp_cells :=
  lazymatch goal with |- rw_cells _ ?m ?A ?cs =>
    match goal with H : rw_cells _ m A ?cs' |- _ =>
      replace cs with cs' by (repeat (reflexivity || lazymatch goal with |- @eq Z _ _ => fail | _ => f_equal end); lia); exact H end
  end.
(* [comment removed for export] *)
Ltac fix_stk := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) =>
  match goal with H : stk _ m _ _ |- _ => let n := fresh "ST" in rename H into n end end.
Tactic Notation "callx" tactic3(tac) := callw tac; try fix_stk.

(* [comment removed for export] *)
Ltac fix_idx := repeat match goal with
  | |- context [Z_to_bv 64 (?A + Z.shiftl ?k 2)] =>
    replace (Z_to_bv 64 (A + Z.shiftl k 2)%Z) with (Z_to_bv 64 (A + 4 * k)%Z) by (rewrite (Z.shiftl_mul_pow2 k 2) by lia; f_equal; lia)
  | |- context [Z_to_bv 64 (Z.shiftl ?k 2 + ?A)] =>
    replace (Z_to_bv 64 (Z.shiftl k 2 + A)%Z) with (Z_to_bv 64 (A + 4 * k)%Z) by (rewrite (Z.shiftl_mul_pow2 k 2) by lia; f_equal; lia) end.

(* [comment removed for export] *)
Ltac eval_swraps := repeat match goal with |- context [bv_swrap 32 ?e] =>
  let v := eval vm_compute in (bv_swrap 32 e) in lazymatch isZcst v with true => change (bv_swrap 32 e) with v end end.


Definition VF_DEPTH : Z := 9136.    (* [comment removed for export] *)
Definition VFSCANF : Z := 0x1ca20.
Definition RFMT : Z := 0x102a8.      (* [comment removed for export] *)
Notation RATP := F_floatscan_common.RATP.
Notation RERRNO := F_floatscan_common.RERRNO.
#[export] Instance P_L_VA_c : OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_vfscanf.L_VA_c := OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_vfscanf.L_VA_c_ok.
End F_vfscanf.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import SFModel Arr SysStep Image FP.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Bytes PropExec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import Prelim SoftFloat StrFun.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require FloatScan.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan.DoubleOps.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import FloatScan FloatScanProps.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require FloatScan_nn.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan_nn.FloatScan_split.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import SFW1_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_scan_calls.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls.F_fmt_calls.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import F_scan_calls Shgetc_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import Scan_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import FmtFp_facts3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Exit.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit.F_memset.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import F_memcpy.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_strnlen.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_strnlen.F_memchr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import F_fmt_fp_lib F_trunctfdf2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_fmt_fp_lib.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Scan_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_A.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Scan_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_B.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Scan_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import F_rscan_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Scan_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_rfile.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_rscan_model.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_rscan_model.F_rscan_facts.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import F_rscan_model F_rscan_shape.

From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import PImg.
(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require StoreCache.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import StoreCache.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgP OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_sscanf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_fmt_fp_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_strnlen.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_memcpy.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Exit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Scan_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Scan_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Scan_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Scan_iface.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_trunctfdf2.
#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit.F_memset.P_memset_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_memcpy.P_memcpy_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_strnlen.F_memchr.P_memchr_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_trunctfdf2.P_trunctfdf2_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_letf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_letf2_callv0_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_fixunstfsi_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatsitf_callp_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatunsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatunsitf_callfix_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_extenddftf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_multf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_divtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_addtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_subtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_frexpl_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_signbitl_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_fpclassifyl_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_A.P_shlim_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_A.P_toread_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_B.P_sread_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc.P_uflow_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc.P_shgetc_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_rfile.P_shgetc_callJ_c F_floatscan.P_L_ENTRY_c F_vfscanf.P_L_VA_c.
(* [comment removed for export] *)
#[local] Existing Instance OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgP.P_img.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAtT _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAt _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RoB _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelCode _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelSym _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelNear _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 2 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.ZFact _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
(* [comment removed for export] *)
Local Ltac mem_after_store ::= mem_after_store_cached.
Local Ltac addr_eq_tac ::= addr_eq_tac_cached.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_cached segs m m' MU WM.
Local Ltac sc_clear := repeat match goal with H : sc_dj _ _ _ _ |- _ => clear H | H : sc_in _ _ _ |- _ => clear H
  | H : sc_no _ _ _ _ |- _ => clear H | H : sc_noin _ _ _ |- _ => clear H end.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)

Ltac zs := zstep; try (fix_litstore; mem_after_store_opt).
Ltac br K := if_cases K; zify_cond K; try (rewrite ?signed_of_Z in K by lia); try (exfalso; lia).
Tactic Notation "callx" tactic3(tac) := callw tac; try (lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) => match goal with H : stk _ m _ _ |- _ => let n := fresh "ST" in rename H into n end end).

(* [comment removed for export] *)
  (* [comment removed for export] *)
Local Ltac brf K := if_cases K; zify_cond K; try (rewrite ?signed_of_Z in K by lia).
Local Ltac br10 K := brf K; [ exfalso; lia | ].

Lemma find_segment_none_of_bounds : forall (segs : list Segment) (l : list (Z * Z)) z n,
  map (fun s => (Z.of_N (seg_base s), Z.of_N (seg_base s) + Z.of_N (seg_size s)))%Z segs = l ->
  Forall (fun bt => ~ (fst bt <= z /\ z + n <= snd bt)%Z) l ->
  find_segment segs z n = None.
Proof. first [ exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_sscanf.find_segment_none_of_bounds | (pose proof OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_sscanf.find_segment_none_of_bounds as T_; exact T_) | exact @OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_sscanf.find_segment_none_of_bounds | apply OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_sscanf.find_segment_none_of_bounds | (apply (@OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_sscanf.find_segment_none_of_bounds OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgP.P_img); typeclasses eauto) ]. Qed.

(* [comment removed for export] *)
Lemma ref_find_segment_none : forall z n, (1 <= n)%Z -> (z + n <= 0x10000 \/ 0x55000 <= z)%Z ->
  find_segment psegs z n = None.
Proof.
  intros z n Hn Hz.
  eapply find_segment_none_of_bounds.
  { vm_compute. reflexivity. }
  repeat constructor; cbn [fst snd]; lia.
Qed.
#[local] Hint Extern 0 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.ZFact _) => exact ref_find_segment_none : typeclass_instances.

Definition hideP (P : Prop) := P.

Theorem rsscanf_lg_proof : rsscanf_lg_stmt.
Proof. first [ exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_sscanf.rsscanf_lg_proof | (pose proof OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_sscanf.rsscanf_lg_proof as T_; exact T_) | exact @OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_sscanf.rsscanf_lg_proof | apply OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_sscanf.rsscanf_lg_proof | (apply (@OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_sscanf.rsscanf_lg_proof OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgP.P_img); typeclasses eauto) ]. Qed.
#[export] Instance P_rsscanf_lg_proof_c : OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_sscanf.rsscanf_lg_proof_c := OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_sscanf.rsscanf_lg_proof_c_ok.
