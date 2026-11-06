(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Mem.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Cells.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Frame.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Exec.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SCPS.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.Spin.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.SRealizes.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LRz.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_data.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_rep.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_art.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_artF.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_cost.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_quarantine_iface.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_sec_dstateP.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_kit.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_nn_specs.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_p_abs.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_tpz.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_apz.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_pop.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_q_wf2.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_q_zone.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_q_wf3.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_sec.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaOn.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_iface.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_lib4.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_q_drain.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_secz.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_poison8.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_spz.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_sec_dstate.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_fz.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_bandtac4.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LMeasure.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_front.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_sec_hz.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_sec_fpU.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_sec_lib.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_cd_stmt.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_specs.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_quarantine_iface2.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_q_lock.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_q_ms.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_q_rec2.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AShadow.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_poison8.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_poison8.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_cd_stmt.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_cd_main.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_sec.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_sec_gbb.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_sec.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_p_nn.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_quarantine_iface2.
From Corelib Require Import PrimInt63 PrimString.
Fixpoint flush_loop (n : nat) (acc : int) : int :=
  match n with
  | O => acc
  | S k => flush_loop k (PrimString.length (PrimString.make 16777211%uint63 acc))
  end.
Lemma gc_flush : flush_loop 150 0%uint63 = 16777211%uint63.
Proof. vm_cast_no_check (@eq_refl int 16777211%uint63). Qed.
