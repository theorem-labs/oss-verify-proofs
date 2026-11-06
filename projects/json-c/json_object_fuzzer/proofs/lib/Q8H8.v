(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup Lib.GwApply QWxq_c1 QRjH QHnV QCcH QfLs Q0Ek Qtgi QjDH Qsw7 QJjn QRUw QkMG Qu4M QG8z Qdyh QLbz Q2Sr Qa8x Q7UD Qhd4 Qwm6 QlKV QsKa Qiiq Q4v2 Qoif Q1Ey Ql4f Q1Y6 QrQv QEUF QW22 QnDr Qmgs QdGy QWrz QV7s QQ2r QtyQ Q63E Q6oO Qvmy Q9yh Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QJjn QRUw.Mq0 QRUw QkMG. Import Qu4M.Mq0 QG8z Qdyh.Mq0 Qdyh.Mq2 QLbz Q2Sr Qdyh.Mq3 Qa8x.Mq3.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa QsKa.Mq4 Qiiq.Mq0 QsKa.Mq6 Q4v2.Mq0 QlKV.Mq5 QlKV.Mq7 QsKa.Mq5 Qoif.Mq0 Q1Ey Ql4f.Mq1 Q1Y6.Mq2 QrQv.Mq2 QEUF QW22.Mq3 QnDr.Mq2 Qmgs QdGy.Mq5 QWrz.Mq1 QV7s QQ2r.Mq2 QtyQ.Mq2 QtyQ.Mq3 QsKa.Mq0 Q63E.Mq6 Q6oO.Mq0 Q63E.Mq7 Qvmy.Mq0 QW22.Mq0 QV7s.Mq1 Q9yh.Mq0.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import QnDr.Mq3.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section PeSTop1.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_outside : forall m m' W, GA m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= hl_img_lo A4H \/ hl_img_hi A4H <= fst iv) W -> GA m'.
Hypothesis GA_pres : forall LB SP m m', heap_pres A4H LB SP m m' -> GA m -> GA m'.
Hypothesis GA_presx : forall LB SP m m', heap_presx A4H a4_volatile LB SP m m' -> lh_globA m' -> GA m -> GA m'.
Hypothesis GA_lh : forall m, GA m -> lh_globA m.

Hypothesis MAPP : memappend_A_stmt2 HIx.
Hypothesis SHRINK : jo_array_shrink_A2J HIx.
Hypothesis AADD : jo_array_add_A2J HIx.
Hypothesis PUT : put_stmt_A HIx.
Hypothesis NEWARR : jo_new_array_A3 HIx.
Hypothesis NEWOBJ : jo_new_object_A3_stmt HIx.
Variable HD : Z.
Hypothesis HD_le : 64 + 96 + 4096 + 128 + HD <= 12288.
Hypothesis OADD : jo_object_add_A HIx HD.
Hypothesis ISTRNCMP : istrncmp_spec_U.
Hypothesis ISTRNCASECMP : istrncasecmp_spec_U.
Hypothesis NEWDBL : jo_new_double_A_stmt HIx.
Hypothesis NEWBOOL : jo_new_boolean_A_stmt HIx.
Hypothesis NEWSTR : jo_new_string_len_A_stmt HIx.
Hypothesis PARSEI : parse_i64_A_stmt HIx 0xa39f8.
Hypothesis PARSEU : parse_i64_A_stmt HIx 0xa3c68.
Hypothesis STRTOD : strtod_A_stmt HIx.
Hypothesis NEWINT : jo_new_int_A_stmt HIx 0x9c330.
Hypothesis NEWUINT : jo_new_int_A_stmt HIx 0x9c9d4.
Hypothesis NEWDBLS : new_double_s_A_stmt HIx.

Variables (pf : pe_fix) (pa : pe_fixA) (q : Z) (LBc LM : list blk) (FRS : list frame) (payload : list byte)
(me : word -> option byte) (lo : Z) (sv : pe_saved) (T : TSet) (F0 : bvmap 5 word).
Hypothesis FRN : Z.of_nat (length FRS) + 2 < 4096.
Hypothesis STC : PE_STATIC_A HIx pf pa lo.
Hypothesis CSTR : CSTR_OK pf payload.
Hypothesis UTF : bytes_at asegs me UTF8REP_ADDR_A Qa8x.Mq3.utf8rep.
Hypothesis BSL : 0 <= pa_bslack pa.
Hypothesis DSL : 0 <= pa_dslack pa.
Hypothesis FL0 : pf_fl pf = 0.
Variables (v2 ra2 : Z).
Hypothesis S0V : pe_s0 sv = Z_to_bv 64 v2.
Hypothesis RAV : pe_ra sv = Z_to_bv 64 ra2.
Hypothesis HV : (v2 < alloc_ceiling \/ v2 mod 8 <> 0 \/ v2 <= pa_sp0 pa \/ hiA_top A4L HIx - 16 <= v2) /\ 0 <= v2 < 2^64.
Hypothesis UWK_arr : uw_ok A4L (hl_malloc A4H) (Z_to_bv 64 0x9eb50) (UWfp ra2 v2).
Hypothesis UWK_obj : uw_ok A4L (hl_malloc A4H) (Z_to_bv 64 0x9bbfc) (UWfp ra2 v2).
Hypothesis UWK_free : uw_ok A4L (hl_free A4H) (Z_to_bv 64 0x94360) (UWfp ra2 v2).
Hypothesis UWK_dbl : uw_ok A4L (hl_malloc A4H) (Z_to_bv 64 0x9d9cc) (UWfp ra2 v2).
Hypothesis UWK_str : uw_ok A4L (hl_malloc A4H) (Z_to_bv 64 0x9e570) (UWfp ra2 v2).
Hypothesis UWK_dup : uw_ok A4L (hl_strdup A4L) (Z_to_bv 64 0x95f88) (UWfp ra2 v2).
Hypothesis UWK_dbls : uw_ok A4L (hl_malloc A4H) (Z_to_bv 64 0x9daec) (UWfp ra2 v2).

Notation CASEx := (CASE_S HIx GA pf pa q LBc LM FRS payload me lo sv T F0 Qa8x.Mq3.utf8rep).
Notation KOUTx := (KOUT_S HIx GA pf pa q LBc LM FRS payload me lo sv T F0).
Hypothesis KO : KOUTx.

Lemma all_cases_S : forall st, 0 <= st <= 26 -> CASEx st.
Proof.
intros st R. enum_z R st.
- apply (case_eatws HIx GA GA_outside GA_pres MAPP); assumption.
- apply (case_start HIx GA GA_outside GA_pres GA_lh NEWARR NEWOBJ pf pa q LBc LM FRS payload me lo sv T F0 Qa8x.Mq3.utf8rep BSL FL0 v2 ra2); assumption.
- apply (case_finish HIx GA GA_outside GA_pres PUT); assumption.
- apply (case_null HIx GA GA_outside GA_pres MAPP ISTRNCMP ISTRNCASECMP NEWDBL pf pa q LBc LM FRS payload me lo sv T F0 Qa8x.Mq3.utf8rep BSL FL0 v2 ra2); assumption.
- apply (case_cstart HIx GA GA_outside GA_pres MAPP); assumption.
- apply (case_comment HIx GA GA_outside GA_pres MAPP); assumption.
- apply (case_ceol HIx GA GA_outside GA_pres MAPP); assumption.
- apply (case_cend HIx GA GA_outside GA_pres MAPP); assumption.
- apply (case_string HIx GA GA_outside GA_pres MAPP NEWSTR pf pa q LBc LM FRS payload me lo sv T F0 Qa8x.Mq3.utf8rep BSL FL0 v2 ra2); assumption.
- apply (case_sesc HIx GA GA_outside GA_pres MAPP); assumption.
- apply (case_euni HIx GA GA_outside GA_pres MAPP); first [assumption | reflexivity].
- apply (case_needesc HIx GA GA_outside GA_pres MAPP); first [assumption | reflexivity].
- apply (case_needu HIx GA GA_outside GA_pres MAPP); first [assumption | reflexivity].
- apply (case_bool HIx GA GA_outside GA_pres MAPP ISTRNCMP ISTRNCASECMP NEWBOOL pf pa q LBc LM FRS payload me lo sv T F0 Qa8x.Mq3.utf8rep BSL FL0); assumption.
- apply (case_number HIx GA GA_outside GA_pres MAPP pf pa q LBc LM FRS payload me lo sv T F0 Qa8x.Mq3.utf8rep BSL FL0 v2 ra2); assumption.
- apply (case_array HIx GA GA_outside GA_pres SHRINK PUT); assumption.
- apply (case_aadd HIx GA GA_outside GA_pres AADD); assumption.
- apply (case_asep HIx GA GA_outside GA_pres SHRINK); assumption.
- apply (case_ofs HIx GA GA_outside GA_pres); assumption.
- apply (case_ofield HIx GA GA_outside GA_pres MAPP pf pa q LBc LM FRS payload me lo sv T F0 Qa8x.Mq3.utf8rep BSL FL0 v2 ra2); assumption.
- apply (case_ofend HIx GA GA_outside).
- apply (case_oval HIx GA GA_outside GA_pres PUT); assumption.
- apply (case_ovadd HIx GA GA_outside GA_pres GA_presx GA_lh HD HD_le OADD pf pa q LBc LM FRS payload me lo sv T F0 Qa8x.Mq3.utf8rep FRN BSL v2 ra2); assumption.
- apply (case_osep HIx GA GA_outside).
- apply (case_array2 HIx GA GA_outside GA_pres SHRINK PUT); assumption.
- apply (case_ofs2 HIx GA GA_outside GA_pres); assumption.
- apply (case_inf HIx GA GA_outside GA_pres NEWDBL pf pa q LBc LM FRS payload me lo sv T F0 Qa8x.Mq3.utf8rep BSL FL0 v2 ra2); assumption.
Qed.

Theorem pe_kall_S : forall n, KALL_S HIx GA pf pa q LBc LM FRS payload me lo sv T F0 n.
Proof.
apply (pe_master_S HIx GA GA_outside pf pa q LBc LM FRS payload me lo sv T F0 Qa8x.Mq3.utf8rep STC CSTR UTF KO).
- exact (kerr2_of_kout HIx GA GA_outside pf pa q LBc LM FRS payload me lo sv T F0 STC KO).
- exact all_cases_S.
Qed.
End PeSTop1.
End RC__1.
End Mq0.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qtgi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qtgi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QjDH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QjDH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDH.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QkMG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkMG. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QG8z.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QG8z. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qdyh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qdyh.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qdyh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qdyh.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLbz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLbz. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2Sr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2Sr. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qa8x.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qa8x.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qdyh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qdyh.Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbFI. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qhd4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qhd4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mqd. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qiiq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qiiq. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSHS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSHS. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Ql4f.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql4f.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1Y6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1Y6.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QrQv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QrQv.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEUF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEUF.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqf. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QW22.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QW22.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnDr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnDr.Mq6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mqe. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qoif.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qoif.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnDr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnDr.Mq5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qmgs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qmgs.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdGy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdGy.Mqc. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWrz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWrz.Mq5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QV7s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QV7s.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQ2r.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQ2r.Mq7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QtyQ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QtyQ.Mq9. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QILa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QILa. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QtyQ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QtyQ.Mqa. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9yh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9yh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mq9. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q63E.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q63E.Mqg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6oO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6oO.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q63E.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q63E.Mqh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qvmy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qvmy. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QW22.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QW22.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QV7s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QV7s.Mq5.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section PeSTop1B.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_outside : forall m m' W, GA m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= hl_img_lo A4H \/ hl_img_hi A4H <= fst iv) W -> GA m'.
Hypothesis GA_pres : forall LB SP m m', heap_pres A4H LB SP m m' -> GA m -> GA m'.
Hypothesis GA_presx : forall LB SP m m', heap_presx A4H a4_volatile LB SP m m' -> lh_globA m' -> GA m -> GA m'.
Hypothesis GA_lh : forall m, GA m -> lh_globA m.

Hypothesis MAPP : memappend_A_stmt2 HIx.
Hypothesis SHRINK : jo_array_shrink_A2J HIx.
Hypothesis AADD : jo_array_add_A2J HIx.
Hypothesis PUT : put_stmt_A HIx.
Hypothesis NEWARR : jo_new_array_A3 HIx.
Hypothesis NEWOBJ : jo_new_object_A3_stmt HIx.
Variable HD : Z.
Hypothesis HD_le : 80 + 96 + 4096 + 144 + HD <= 12288.
Hypothesis OADD : jo_object_add_A HIx HD.
Hypothesis ISTRNCMP : istrncmp_spec_U.
Hypothesis ISTRNCASECMP : istrncasecmp_spec_U.
Hypothesis NEWDBL : jo_new_double_A_stmt HIx.
Hypothesis NEWBOOL : jo_new_boolean_A_stmt HIx.
Hypothesis NEWSTR : jo_new_string_len_A_stmt HIx.
Hypothesis PARSEI : parse_i64_A_stmt HIx 0xa6060.
Hypothesis PARSEU : parse_i64_A_stmt HIx 0xa62ec.
Hypothesis STRTOD : strtod_A_stmt HIx.
Hypothesis NEWINT : jo_new_int_A_stmt HIx 0x9dbdc.
Hypothesis NEWUINT : jo_new_int_A_stmt HIx 0x9e328.
Hypothesis NEWDBLS : new_double_s_A_stmt HIx.

Variables (pf : pe_fix) (pa : pe_fixA) (q : Z) (LBc LM : list blk) (FRS : list frame) (payload : list byte)
(me : word -> option byte) (lo : Z) (sv : pe_saved) (T : TSet) (F0 : bvmap 5 word).
Hypothesis FRN : Z.of_nat (length FRS) + 2 < 4096.
Hypothesis STC : PE_STATIC_A HIx pf pa lo.
Hypothesis CSTR : CSTR_OK pf payload.
Hypothesis UTF : bytes_at asegs me UTF8REP_ADDR_A Qa8x.Mq3.utf8rep.
Hypothesis BSL : 0 <= pa_bslack pa.
Hypothesis DSL : 0 <= pa_dslack pa.
Hypothesis FL0 : pf_fl pf = 0.
Variables (v2 ra2 : Z).
Hypothesis S0V : pe_s0 sv = Z_to_bv 64 v2.
Hypothesis RAV : pe_ra sv = Z_to_bv 64 ra2.
Hypothesis HV : (v2 < alloc_ceiling \/ v2 mod 8 <> 0 \/ v2 <= pa_sp0 pa \/ hiA_top A4L HIx - 16 <= v2) /\ 0 <= v2 < 2^64.

Hypothesis UWK_arr : uw_ok A4L (hl_malloc A4H) (Z_to_bv 64 0xa0770) (UWfp ra2 v2).
Hypothesis UWK_obj : uw_ok A4L (hl_malloc A4H) (Z_to_bv 64 0x9d38c) (UWfp ra2 v2).
Hypothesis UWK_free : uw_ok A4L (hl_free A4H) (Z_to_bv 64 0x94e48) (UWfp ra2 v2).
Hypothesis UWK_dbl : uw_ok A4L (hl_malloc A4H) (Z_to_bv 64 0x9f3fc) (UWfp ra2 v2).
Hypothesis UWK_str : uw_ok A4L (hl_malloc A4H) (Z_to_bv 64 0xa00d4) (UWfp ra2 v2).
Hypothesis UWK_dup : uw_ok A4L (hl_strdup A4L) (Z_to_bv 64 0x975cc) (UWfp ra2 v2).
Hypothesis UWK_dbls : uw_ok A4L (hl_malloc A4H) (Z_to_bv 64 0x9f57c) (UWfp ra2 v2).

Notation CASEx := (CASE_S HIx GA pf pa q LBc LM FRS payload me lo sv T F0 Qa8x.Mq3.utf8rep).
Notation KOUTx := (KOUT_S HIx GA pf pa q LBc LM FRS payload me lo sv T F0).
Hypothesis KO : KOUTx.

Lemma all_cases_S : forall st, 0 <= st <= 26 -> CASEx st.
Proof.
intros st R. enum_z R st.
- apply (case_eatws HIx GA GA_outside GA_pres MAPP); assumption.
- apply (case_start HIx GA GA_outside GA_pres GA_lh NEWARR NEWOBJ pf pa q LBc LM FRS payload me lo sv T F0 Qa8x.Mq3.utf8rep BSL FL0 v2 ra2); assumption.
- apply (case_finish HIx GA GA_outside GA_pres PUT); assumption.
- apply (case_null HIx GA GA_outside GA_pres MAPP ISTRNCMP ISTRNCASECMP NEWDBL pf pa q LBc LM FRS payload me lo sv T F0 Qa8x.Mq3.utf8rep BSL FL0 v2 ra2); assumption.
- apply (case_cstart HIx GA GA_outside GA_pres MAPP); assumption.
- apply (case_comment HIx GA GA_outside GA_pres MAPP); assumption.
- apply (case_ceol HIx GA GA_outside GA_pres MAPP); assumption.
- apply (case_cend HIx GA GA_outside GA_pres MAPP); assumption.
- apply (case_string HIx GA GA_outside GA_pres MAPP NEWSTR pf pa q LBc LM FRS payload me lo sv T F0 Qa8x.Mq3.utf8rep BSL FL0 v2 ra2); assumption.
- apply (case_sesc HIx GA GA_outside GA_pres MAPP); assumption.
- apply (case_euni HIx GA GA_outside GA_pres MAPP); first [assumption | reflexivity].
- apply (case_needesc HIx GA GA_outside GA_pres MAPP); first [assumption | reflexivity].
- apply (case_needu HIx GA GA_outside GA_pres MAPP); first [assumption | reflexivity].
- apply (case_bool HIx GA GA_outside GA_pres MAPP ISTRNCMP ISTRNCASECMP NEWBOOL pf pa q LBc LM FRS payload me lo sv T F0 Qa8x.Mq3.utf8rep BSL FL0); assumption.
- apply (case_number HIx GA GA_outside GA_pres MAPP pf pa q LBc LM FRS payload me lo sv T F0 Qa8x.Mq3.utf8rep BSL FL0 v2 ra2); assumption.
- apply (case_array HIx GA GA_outside GA_pres SHRINK PUT); assumption.
- apply (case_aadd HIx GA GA_outside GA_pres AADD); assumption.
- apply (case_asep HIx GA GA_outside GA_pres SHRINK); assumption.
- apply (case_ofs HIx GA GA_outside GA_pres); assumption.
- apply (case_ofield HIx GA GA_outside GA_pres MAPP pf pa q LBc LM FRS payload me lo sv T F0 Qa8x.Mq3.utf8rep BSL FL0 v2 ra2); assumption.
- apply (case_ofend HIx GA GA_outside).
- apply (case_oval HIx GA GA_outside GA_pres PUT); assumption.
- apply (case_ovadd HIx GA GA_outside GA_pres GA_presx GA_lh HD HD_le OADD pf pa q LBc LM FRS payload me lo sv T F0 Qa8x.Mq3.utf8rep FRN BSL v2 ra2); assumption.
- apply (case_osep HIx GA GA_outside).
- apply (case_array2 HIx GA GA_outside GA_pres SHRINK PUT); assumption.
- apply (case_ofs2 HIx GA GA_outside GA_pres); assumption.
- apply (case_inf HIx GA GA_outside GA_pres NEWDBL pf pa q LBc LM FRS payload me lo sv T F0 Qa8x.Mq3.utf8rep BSL FL0 v2 ra2); assumption.
Qed.

Theorem pe_kall_S : forall n, KALL_S HIx GA pf pa q LBc LM FRS payload me lo sv T F0 n.
Proof.
apply (pe_master_S HIx GA GA_outside pf pa q LBc LM FRS payload me lo sv T F0 Qa8x.Mq3.utf8rep STC CSTR UTF KO).
- exact (kerr2_of_kout HIx GA GA_outside pf pa q LBc LM FRS payload me lo sv T F0 STC KO).
- exact all_cases_S.
- exact FL0.
Qed.
End PeSTop1B.
End RC__1.
