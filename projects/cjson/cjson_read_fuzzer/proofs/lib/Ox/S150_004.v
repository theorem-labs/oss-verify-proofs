(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RelSpec.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Mem.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Exec.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.RegsEquiv.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SCPS.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NodesSound.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.RzNodesImpl.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Stdio.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Driver.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LRz.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSO_rz.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_iface.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_poison8.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_memset.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_fmt_fp_lib.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_pad.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Exit.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.SO_base.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_printf_iface.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Stdio_iface.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_base.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Exit_pre2.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.SO_piface.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SO_model.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SO_rz.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.SO_stdio_exit.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_trunA.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeSpec.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_data.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_art.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AShadow.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcsdefs.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_musl.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_poison.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_poison2.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FmtFp.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_memcpy.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_fwritex.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_pop_arg.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_vsnprintf.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Printf_model.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Printf_mlib.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Printf_pieces.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_str3.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcleaf.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcdefs.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcommon_x.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcommon_tb.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcommon_su.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcommon_sco.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcommon_sre.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_fmt_iface.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_vfprintf.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_fprintf.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.SO_fprintf.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_icpt_defs.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_icpt_fwrite.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_vprintf.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SCPS.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LRz.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_tree.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AShadow.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_conv.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcsdefs.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Exit.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.SO_base.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Stdio_iface.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_trunA.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_base.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_iface2.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_traces.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_fuzz_iface.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_stmt.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.DrvTop.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.DrvTop.
From Corelib Require Import PrimInt63 PrimString.
Fixpoint flush_loop (n : nat) (acc : int) : int :=
  match n with
  | O => acc
  | S k => flush_loop k (PrimString.length (PrimString.make 16777211%uint63 acc))
  end.
Lemma gc_flush : flush_loop 150 0%uint63 = 16777211%uint63.
Proof. vm_cast_no_check (@eq_refl int 16777211%uint63). Qed.
