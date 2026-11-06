(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qdyh.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qdyh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qdyh.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QIsM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QIsM.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qa8x.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qa8x.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLbz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLbz. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QMdR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QMdR.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qa8x.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qa8x. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXfU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXfU.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qa8x.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qa8x.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXfU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXfU.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXfU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXfU.Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7UD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7UD. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qhd4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qhd4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqa. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qiiq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qiiq.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mq6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4v2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4v2.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mq5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1Ey.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1Ey. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Ql4f.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql4f.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1Y6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1Y6.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QrQv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QrQv.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEUF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEUF. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QW22.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QW22.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdGy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdGy.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYZ0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYZ0.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mq7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdGy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdGy.Mq6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q63E.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q63E.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QVob.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QVob.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q228.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q228.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QMmN.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QMmN. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QMgr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QMgr. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qw5U.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qw5U.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qeia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qeia.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWrz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWrz.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qvmy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qvmy.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYZ0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYZ0.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJZd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJZd.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QW22.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QW22.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QV7s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QV7s.Mq1.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac QlEo_c1.solve_load ::= QXup.mkr__solve_load_3. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEUF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEUF.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QMgr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QMgr.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section PeSNumA.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_outside : forall m m' W, GA m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= hl_img_lo A4H \/ hl_img_hi A4H <= fst iv) W -> GA m'.
Hypothesis GA_pres : forall LB SP m m', heap_pres A4H LB SP m m' -> GA m -> GA m'.
Hypothesis MAPP : memappend_A_stmt2 HIx.
Hypothesis PARSEI : parse_i64_A_stmt HIx 0xa39f8.
Hypothesis PARSEU : parse_i64_A_stmt HIx 0xa3c68.
Hypothesis STRTOD : strtod_A_stmt HIx.
Hypothesis NEWINT : jo_new_int_A_stmt HIx 0x9c330.
Hypothesis NEWUINT : jo_new_int_A_stmt HIx 0x9c9d4.
Hypothesis NEWDBLS : new_double_s_A_stmt HIx.

Ltac pe_openA STC INV :=
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR); pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk);
destruct INV as [CORE REST];
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR);
pose proof REST as (HP & LV & OBJ & ST & ERR & STR & PLEN & SBin & HPR & MDV & G & BUD).

Ltac shq_facts HP INq INtk q mxd tk dz j SH SEPc SEPq SEPt :=
pose proof (stack_shadowA HIx _ _ _ _ _ _ _ q mxd dz j HP INq ltac:(lia) ltac:(lia)) as SH;
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ q (32 * mxd) (4 * dz + j) q (32 * mxd) HP INq ltac:(lia) (in_or_app _ _ _ (or_introl INq))) as (SEPc & SEPq & _);
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ q (32 * mxd) (4 * dz + j) tk 72 HP INq ltac:(lia) (in_or_app _ _ _ (or_introl INtk))) as (_ & SEPt & _);
cbn [hl_sb A4L] in SEPc, SEPq, SEPt.

Lemma num_adv_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel) (co0 bnd : Z)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet)
(gp t1 t2 a1 a2 a3 a4 a5 a6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> pf_fl pf = 0 ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
PBOKat m ts bnd -> CSTR_OK pf payload ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_number ->
0 <= co0 <= t_co ts -> t_co ts < pf_len pf -> nth_error payload (Z.to_nat (t_co ts)) = Some cb -> bv_unsigned cb <> 0 ->

(forall m' cb' a5',
t_co ts + 1 < pf_len pf -> nth_error payload (Z.to_nat (t_co ts + 1)) = Some cb' -> bv_unsigned cb' <> 0 ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md A B (ts_set_co ts (t_co ts + 1)) cb' nb pj sv errv ->
PBOKat m' (ts_set_co ts (t_co ts + 1)) bnd ->
AJ5 A4L HIx A T md
(Q1Y6.Mq2.pe_msE pf pa 0x94954 (Z_to_bv 64 (pf_tk pf / 8 + 2147450884)) gp (Z_to_bv 64 (pf_tk pf / 8 + 3)) t1 t2 (Z_to_bv 64 (pf_sb pf + (t_co ts + 1) + 1)) a1 a2 a3 (Z_to_bv 64 (bv_unsigned cb')) a5' a6 (Z_to_bv 64 (t_pb ts))
(Z_to_bv 64 (t_co ts + 1 - co0)) a3 (Z_to_bv 64 (Z.of_nat (t_depth ts))) (Z_to_bv 64 (pf_sb pf + (t_co ts + 1))) (Z_to_bv 64 (pf_tk pf + 32)) (Z_to_bv 64 (pa_F pa)) (Z_to_bv 64 q)
(Z_to_bv 64 (pf_sb pf + co0)) (Z_to_bv 64 (pf_tk pf + 64)) (Z_to_bv 64 (pa_F pa + 64)) (Z_to_bv 64 (pf_tk pf / 8 + 2147450888)) (Z_to_bv 64 (pf_lenr pf)) F fc m')) ->

(forall m' cb' a0' a5',
t_co ts + 1 < pf_len pf -> nth_error payload (Z.to_nat (t_co ts + 1)) = Some cb' -> bv_unsigned cb' = 0 ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md A B (ts_set_co ts (t_co ts + 1)) cb' nb pj sv errv ->
PBOKat m' (ts_set_co ts (t_co ts + 1)) bnd ->
AJ5 A4L HIx A T md
(Q1Y6.Mq2.pe_msE pf pa 0x94b20 (Z_to_bv 64 (pf_tk pf / 8 + 2147450884)) gp (Z_to_bv 64 (pf_tk pf / 8 + 3)) t1 t2 a0' a1 a2 a3 (Z_to_bv 64 (bv_unsigned cb')) a5' a6 (Z_to_bv 64 (t_pb ts))
(Z_to_bv 64 (t_co ts + 1 - co0)) (Z_to_bv 64 (pf_tk pf + 20)) (Z_to_bv 64 (Z.of_nat (t_depth ts))) (Z_to_bv 64 (pf_sb pf + (t_co ts + 1))) (Z_to_bv 64 (pf_tk pf + 32)) (Z_to_bv 64 (pa_F pa)) (Z_to_bv 64 q)
(Z_to_bv 64 (pf_sb pf + co0)) (Z_to_bv 64 (pf_tk pf + 64)) (Z_to_bv 64 (pa_F pa + 64)) (Z_to_bv 64 (pf_tk pf / 8 + 2147450888)) (Z_to_bv 64 (pf_lenr pf)) F fc m')) ->

(forall m' a4',
t_co ts + 1 = pf_len pf -> pf_lenr pf = pf_len pf ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md A B (ts_set_co ts (pf_len pf)) cb nb pj sv errv ->
PBOKat m' (ts_set_co ts (pf_len pf)) bnd ->
AJ5 A4L HIx A T md
(Q1Y6.Mq2.pe_msE pf pa 0x97da8 (Z_to_bv 64 (pf_tk pf / 8 + 2147450884)) gp (Z_to_bv 64 (pf_tk pf / 8 + 3)) t1 t2 (Z_to_bv 64 (pf_sb pf + t_co ts + 1)) a1 a2 a3 a4' a5 a6 (Z_to_bv 64 (t_pb ts))
(Z_to_bv 64 (t_co ts - co0)) (Z_to_bv 64 (pf_tk pf + 20)) (Z_to_bv 64 (Z.of_nat (t_depth ts))) (Z_to_bv 64 (pf_sb pf + t_co ts)) (Z_to_bv 64 (pf_tk pf + 32)) (Z_to_bv 64 (pa_F pa)) (Z_to_bv 64 q)
(Z_to_bv 64 (pf_sb pf + co0)) (Z_to_bv 64 (pf_tk pf + 64)) (Z_to_bv 64 (pa_F pa + 64)) (Z_to_bv 64 (pf_tk pf / 8 + 2147450888)) (Z_to_bv 64 (pf_lenr pf)) F fc m')) ->
AJ5 A4L HIx A T md
(Q1Y6.Mq2.pe_msE pf pa 0x949ec (Z_to_bv 64 (pf_tk pf / 8 + 2147450884)) gp (Z_to_bv 64 (pf_tk pf / 8 + 3)) t1 t2 (Z_to_bv 64 (pf_sb pf + t_co ts + 1)) a1 a2 a3 a4 a5 a6 (Z_to_bv 64 (t_pb ts))
(Z_to_bv 64 (t_co ts - co0)) (Z_to_bv 64 (pf_tk pf + 20)) (Z_to_bv 64 (Z.of_nat (t_depth ts))) (Z_to_bv 64 (pf_sb pf + t_co ts)) (Z_to_bv 64 (pf_tk pf + 32)) (Z_to_bv 64 (pa_F pa)) (Z_to_bv 64 q)
(Z_to_bv 64 (pf_sb pf + co0)) (Z_to_bv 64 (pf_tk pf + 64)) (Z_to_bv 64 (pa_F pa + 64)) (Z_to_bv 64 (pf_tk pf / 8 + 2147450888)) (Z_to_bv 64 (pf_lenr pf)) F fc m).
Proof.
intros until fc. intros STC FL0 INV PBK CSTR Hl Hst Hco0 Hco Hc Hnz Kloop Kexit Keof.
pose proof INV as INV0.
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
destruct INV as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof REST as (HP & LV & OBJ & ST & ERR & STR & PLEN & SBin & HPR & MDV & G & BUD).
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *. subst fl.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
unfold ts_set_co in Kloop, Kexit, Keof.
cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in Kloop, Kexit, Keof.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
pose proof FR as FR0. unfold pe_frameA in FR. destruct FR as (SLOTS & GAP & SAVED & FF & FSH). unfold Q1Y6.Mq2.pe_msE in *.
unfold pe_slotsA in SLOTS. cbn zeta in SLOTS. unfold pe_savedA_cells in SAVED. unfold ff_cellsA in FF. unfold ffsh_cells, FSH0 in FSH. cbn [map] in FSH.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd 0) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 4 HP INtk ltac:(lia)) as SHT4.
replace (tk / 8 + 4 + A_SB) with (tk / 8 + 2147450884) in SHT4 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 4 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT4t & _).
cbn [hl_sb A4L] in SEPT4t. assert (EQx : tk / 8 + A_SB + 4 = tk / 8 + 2147450884) by (unfold A_SB; lia). rewrite EQx in SEPT4t. clear EQx.
assert (cs_T4_T : csep (tk / 8 + 2147450884) 1 tk (Z.of_nat 72)) by (unfold csep; clear - SEPT4t; lia). clear SEPT4t.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 8 HP INtk ltac:(lia)) as SHT8.
replace (tk / 8 + 8 + A_SB) with (tk / 8 + 2147450888) in SHT8 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 8 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT8t & _).
cbn [hl_sb A4L] in SEPT8t. assert (EQx : tk / 8 + A_SB + 8 = tk / 8 + 2147450888) by (unfold A_SB; lia). rewrite EQx in SEPT8t. clear EQx.
assert (cs_T8_T : csep (tk / 8 + 2147450888) 1 tk (Z.of_nat 72)) by (unfold csep; clear - SEPT8t; lia). clear SEPT8t.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs m) as WM.
pose proof (bytes_at_bound _ _ _ _ STR) as SBB.
pose proof alloc_ceiling_range as ACR.
pose proof (bv_unsigned_in_range 8 cb) as CBR; unfold bv_modulus in CBR; cbn in CBR.
assert (INF : In (Ff, 2) ((Ff, 2) :: FRS)) by (left; reflexivity).
assert (INtk' : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd 0) q LB0 ts0 ++ LM)) by (apply in_or_app; left; exact INtk).
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP INF INtk') as DFt. rewrite fr_size_2 in DFt.
assert (GF0' : 0 <= Ff) by lia. assert (GFc' : Ff < alloc_ceiling) by lia.
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP INF) as DSF. rewrite fr_size_2 in DSF. cbn [hl_sb A4L] in DSF.
destruct SBin as [L00 | PL]; [exfalso; lia|].
assert (SBc : sb + len <= alloc_ceiling).
{ destruct PL as [([b0 n0] & Hb0 & Hb1 & Hb2) | (Fh & kh & HFh & HF1 & HF2 & _)]; cbn [pf_sb pf_len pa_sp0 blk_addr blk_size fst snd] in *.
- pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ b0 n0 HP ltac:(apply in_or_app; left; unfold pe_blocksA; apply in_or_app; right; right; right; exact Hb0)) as (_ & _ & _ & Hbhi & _). lia.
- pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP (or_intror HFh)) as (_ & _ & _ & HFhc & _). lia. }
assert (SBhi : sb + len <= 2^47) by lia.
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8, A_SB in *.
pose proof (munch_refl [(tk, tk + 72); (Ff + 64, Ff + 65)] m) as MU.
assert (HW : Forall (pe_wtfA (PEF tk oldl newl len lenr sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl)) [(tk, tk + 72); (Ff + 64, Ff + 65)]).
{ apply Forall_cons; [left; cbn [fst snd pf_tk]; lia |]. apply Forall_cons; [| apply Forall_nil]. right; right; left. cbn [fst snd pa_F]. lia. }
assert (cs_FF_T : csep Ff 248 tk (Z.of_nat 72)) by (unfold csep; clear - DFt; lia).
assert (cs_T_FF : csep tk 72 Ff (Z.of_nat 248)) by (unfold csep; clear - DFt; lia).
clear LV OBJ HPR.
stash PB. stash TSK. stash GAP. stash SAVED. stash FSH. stash DSF. stash DFt.
stash Kloop. stash Kexit. stash Keof. stash INV0. stash REST. stash FR0. stash PBK. stash SBc. stash SBhi. stash Hc. stash STR. stash HW. stash Himg_t.
reenterA asegs A4L HIx asegs_wx HP.
step.
norm_sx32.
step.
norm_w32.
step.
step.
unstash INV0. unstash REST. unstash FR0. unstash HW. unstash PBK. unstash Hc.
destruct (peek_cases (PEF tk oldl newl len lenr sb spf pmd mxd 0) payload co cb LENR CSTR (proj1 RR) ltac:(cbn [pf_len pf_mxd]; lia) ltac:(cbn [pf_len pf_mxd]; lia) Hc Hnz)
as [[Elenr Heof] | [Hne Hmore]]; cbn [pf_len pf_lenr pf_mxd] in *.
{
subst lenr. rewrite Heof. if_false.
step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, FFc : rw_cells asegs mc Ff _ |- _ =>
assert (FRc : pe_frameA asegs mc (PEF tk oldl newl len len sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) cb nb pj sv)
by (eapply (pe_frameA_scan HIx) with (ts := ts0); [exact STC | exact (proj1 REST) | exact FR0 | exact MUc | exact WMc | exact FFc]);
evt_done5;
destruct (PE_INV_A_tokw HIx GA GA_outside (PEF tk oldl newl len len sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m mc md A B ts0
cb nb pj sv errv _ (co + 1) (TS isd stpos (Z_to_bv 64 (co + 1)) err ucs high quote) cb nb STC INV0 MUc WMc MIc HW TOKc FRc
ltac:(cbn [pf_len]; lia) eq_refl) as [INV1 PBK1]
end end.
unstash Keof. replace (co + 1) with len in INV1, PBK1 by lia.
eapply (Keof _ _); [lia | reflexivity | exact INV1 | exact (PBK1 _ PBK)]. }
if_truex.

destruct (nth_error payload (Z.to_nat (co + 1))) as [c'|] eqn:Hc'; [| apply nth_error_None in Hc'; lia].
pose proof (bv_unsigned_in_range 8 c') as CBR'; unfold bv_modulus in CBR'; cbn in CBR'.
pose proof (payload_shadow_pe HIx (PEF tk oldl newl len lenr sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) LB0 FRS _ _ _ _ _ _ _ (co + 1) HP
ltac:(intros bb Hbb; unfold pe_blocksA; apply in_or_app; right; right; right; exact Hbb) PL ltac:(cbn [pf_len]; lia)) as (v1 & SHP1 & Hv1).
cbn [pf_sb] in SHP1, Hv1. unfold A_SB in SHP1. replace (sb + (co + 1)) with (sb + co + 1) in SHP1, Hv1 by lia.
unstash SBhi. unstash DSF. unstash SBc.
pose proof (shadow_blk_apart HIx _ _ _ _ _ _ _ _ _ (sb + co + 1) 1 HP INtk' ltac:(lia) ltac:(lia) ltac:(lia)) as DSPt. unfold shA, A_SB in DSPt.
assert (SHPF : (sb + co + 1) / 8 + 2147450880 + 1 <= Ff \/ Ff + 256 <= (sb + co + 1) / 8 + 2147450880) by (clear - DSF SBhi SB0 CO Hmore; Z.div_mod_to_equations; lia).
lazymatch goal with MUc : munch _ m ?mc |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
apply (fun H => ro_cells_transport asegs _ m mc _ _ H MUc) in SHP1; [| cbn [disjoint_from fst snd cells_size csize Z.of_nat]; clear - DSPt SHPF; lia] end.
assert (LE1 : le1 (zxb c') = [c']).
{ unfold le1, zxb. cbn [Z_to_le_bytes pf_mxd]. f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 8) with 256%Z. change (bv_modulus 64) with 18446744073709551616%Z. Z.div_mod_to_equations. nia. }
stash DSF. stash SBc. stash DSPt. stash SHPF. stash Hv1. stash LE1. stash INV0. stash REST. stash FR0. stash HW. stash Hc. stash Hc'. stash PBK.
asan_rechkA.
lazymatch goal with TOKc : rw_cells asegs ?mc tk _ |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (tok_flags_byteA mxd 0 mc tk pb (Z.of_nat depth) q (TS isd stpos (Z_to_bv 64 (co + 1)) err ucs high quote) TOKc) as RDF end.
step.
rewrite ?zxb_zero. clear RDF.
step.
step.
step.
step.
if_true.
step.
sh_norm.

lazymatch goal with |- evt _ _ (MS ?R ?FF _ ?fcc None ?mm ?rom) =>
assert (JOIN : forall a4y a5y, evt asegs (AJ5e A4L HIx A T md) (MS (bvmap_set 14 a4y (bvmap_set 15 a5y R)) FF (Z_to_bv 64 0x94a58) fcc None mm rom)) end.
2:{ unstash Hv1. destruct Hv1 as [-> | [Hv8 Hvlt]].
- step. rewrite ?sxb_zero. step. if_false. apply JOIN.
- step. rewrite (sxb_small v1) by lia. step. if_truex.
step.
rewrite (unsigned_lit (sb + co + 1)) by lia. rewrite (land7_mod8 (sb + co + 1)) by lia.
pose proof (Z.mod_pos_bound (sb + co + 1) 8 ltac:(lia)) as R8. remember ((sb + co + 1) mod 8) as r8 eqn:Er8 in *.
step.
if_truex. apply JOIN. }
intros a4y a5y. clear SHP1.
unstash REST. unstash STR. unstash HW. unstash Hc'.
lazymatch goal with MUc : munch _ m ?mc |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (payload_privateA HIx _ _ _ _ _ _ _ ts0 _ _ _ _ _ _ _ STC (proj1 REST) STR PLEN (or_intror PL) MUc (pe_wtfA_private _ _ q pbs _ HW)) as STRc end.
cbn [pf_sb] in STRc.
pose proof (payload_byteA _ _ _ _ _ STRc Hc' ltac:(lia)) as RDC. replace (sb + (co + 1)) with (sb + co + 1) in RDC by lia.
stash REST. stash STR. stash HW. clear STRc.
step.
change (zxb c') with (Z_to_bv 64 (bv_unsigned c')). clear RDC.
clear SHT4 SHT8.
unstash LE1.
step.
replace (le1 (Z_to_bv 64 (bv_unsigned c'))) with [c'] by (rewrite <- LE1; reflexivity). mem_after_store.
step.
step.
norm_w32.
step.
step.
unstash REST. unstash HW. unstash INV0. unstash FR0. unstash PBK. unstash Hc'.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, FFc : rw_cells asegs mc Ff _ |- _ =>
assert (FRc : pe_frameA asegs mc (PEF tk oldl newl len lenr sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) c' nb pj sv)
by (eapply (pe_frameA_scan HIx) with (ts := ts0); [exact STC | exact (proj1 REST) | exact FR0 | exact MUc | exact WMc | exact FFc]);
destruct (PE_INV_A_tokw HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m mc md A B ts0
cb nb pj sv errv _ (co + 1) (TS isd stpos (Z_to_bv 64 (co + 1)) err ucs high quote) c' nb STC INV0 MUc WMc MIc HW TOKc FRc
ltac:(cbn [pf_len]; lia) eq_refl) as [INV1 PBK1]
end end.
replace (sb + co + 2) with (sb + (co + 1) + 1) by lia. replace (sb + co + 1) with (sb + (co + 1)) by lia.
replace (co - co0 + 1) with (co + 1 - co0) by lia.
destruct (Z.eq_dec (bv_unsigned c') 0) as [E0 | N0].
-
if_falsex. step.
step.
evt_done5. unstash Kexit.
eapply (Kexit _ c'); [cbn [pf_len]; lia | first [exact Hc' | reflexivity] | exact E0 | exact INV1 | exact (PBK1 _ PBK)].
- if_truex. evt_done5. unstash Kloop.
eapply (Kloop _ c'); [cbn [pf_len]; lia | first [exact Hc' | reflexivity] | exact N0 | exact INV1 | exact (PBK1 _ PBK)].
Qed.

Lemma num_loop_A :
forall (n : nat) (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel) (co0 bnd : Z)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet)
(gp t1 t2 a1 a2 a3 a5 a6 s4 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> pf_fl pf = 0 ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
PBOKat m ts bnd -> CSTR_OK pf payload ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_number ->
0 <= co0 <= t_co ts -> t_co ts < pf_len pf -> nth_error payload (Z.to_nat (t_co ts)) = Some cb -> bv_unsigned cb <> 0 ->
(pf_len pf - t_co ts <= Z.of_nat n) ->

(forall m' co' cb' (isdq : word) a0' a1' a2' a3' a5' a6',
t_co ts <= co' < pf_len pf -> nth_error payload (Z.to_nat co') = Some cb' ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md A B (ts_set_x ts co' (TS isdq (ts_stpos (t_x ts)) (Z_to_bv 64 co') (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))) cb' nb pj sv errv ->
PBOKat m' (ts_set_x ts co' (TS isdq (ts_stpos (t_x ts)) (Z_to_bv 64 co') (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))) bnd ->
AJ5 A4L HIx A T md
(Q1Y6.Mq2.pe_msE pf pa 0x94b20 (Z_to_bv 64 (pf_tk pf / 8 + 2147450884)) gp (Z_to_bv 64 (pf_tk pf / 8 + 3)) t1 t2 a0' a1' a2' a3' (Z_to_bv 64 (bv_unsigned cb')) a5' a6' (Z_to_bv 64 (t_pb ts))
(Z_to_bv 64 (co' - co0)) (Z_to_bv 64 (pf_tk pf + 20)) (Z_to_bv 64 (Z.of_nat (t_depth ts))) (Z_to_bv 64 (pf_sb pf + co')) (Z_to_bv 64 (pf_tk pf + 32)) (Z_to_bv 64 (pa_F pa)) (Z_to_bv 64 q)
(Z_to_bv 64 (pf_sb pf + co0)) (Z_to_bv 64 (pf_tk pf + 64)) (Z_to_bv 64 (pa_F pa + 64)) (Z_to_bv 64 (pf_tk pf / 8 + 2147450888)) (Z_to_bv 64 (pf_lenr pf)) F fc m')) ->

(forall m' co' cb' (isdq : word) a1' a2' a3' a4' a5' a6',
t_co ts <= co' -> co' + 1 = pf_len pf -> pf_lenr pf = pf_len pf ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md A B (ts_set_x ts (pf_len pf) (TS isdq (ts_stpos (t_x ts)) (Z_to_bv 64 (pf_len pf)) (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))) cb' nb pj sv errv ->
PBOKat m' (ts_set_x ts (pf_len pf) (TS isdq (ts_stpos (t_x ts)) (Z_to_bv 64 (pf_len pf)) (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))) bnd ->
AJ5 A4L HIx A T md
(Q1Y6.Mq2.pe_msE pf pa 0x97da8 (Z_to_bv 64 (pf_tk pf / 8 + 2147450884)) gp (Z_to_bv 64 (pf_tk pf / 8 + 3)) t1 t2 (Z_to_bv 64 (pf_sb pf + co' + 1)) a1' a2' a3' a4' a5' a6' (Z_to_bv 64 (t_pb ts))
(Z_to_bv 64 (co' - co0)) (Z_to_bv 64 (pf_tk pf + 20)) (Z_to_bv 64 (Z.of_nat (t_depth ts))) (Z_to_bv 64 (pf_sb pf + co')) (Z_to_bv 64 (pf_tk pf + 32)) (Z_to_bv 64 (pa_F pa)) (Z_to_bv 64 q)
(Z_to_bv 64 (pf_sb pf + co0)) (Z_to_bv 64 (pf_tk pf + 64)) (Z_to_bv 64 (pa_F pa + 64)) (Z_to_bv 64 (pf_tk pf / 8 + 2147450888)) (Z_to_bv 64 (pf_lenr pf)) F fc m')) ->
AJ5 A4L HIx A T md
(Q1Y6.Mq2.pe_msE pf pa 0x94954 (Z_to_bv 64 (pf_tk pf / 8 + 2147450884)) gp (Z_to_bv 64 (pf_tk pf / 8 + 3)) t1 t2 (Z_to_bv 64 (pf_sb pf + t_co ts + 1)) a1 a2 a3 (Z_to_bv 64 (bv_unsigned cb)) a5 a6 (Z_to_bv 64 (t_pb ts))
(Z_to_bv 64 (t_co ts - co0)) s4 (Z_to_bv 64 (Z.of_nat (t_depth ts))) (Z_to_bv 64 (pf_sb pf + t_co ts)) (Z_to_bv 64 (pf_tk pf + 32)) (Z_to_bv 64 (pa_F pa)) (Z_to_bv 64 q)
(Z_to_bv 64 (pf_sb pf + co0)) (Z_to_bv 64 (pf_tk pf + 64)) (Z_to_bv 64 (pa_F pa + 64)) (Z_to_bv 64 (pf_tk pf / 8 + 2147450888)) (Z_to_bv 64 (pf_lenr pf)) F fc m).
Proof.
induction n as [|n IH]; intros until fc; intros STC FL0 INV PBK CSTR Hl Hst Hco0 Hco Hc Hnz Hn Kexit Keof.
{ exfalso. cbn in Hn. lia. }
pose proof INV as INV0.
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
destruct INV as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof REST as (HP & _).
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *. subst fl.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
unfold ts_set_x in Kexit, Keof.
cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in Kexit, Keof.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
unfold pe_frameA in FR. destruct FR as (SLOTS & _). unfold Q1Y6.Mq2.pe_msE in *.
unfold pe_slotsA in SLOTS. cbn zeta in SLOTS.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd 0) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 3 HP INtk ltac:(lia)) as SHT3.
replace (tk / 8 + 3 + A_SB) with (tk / 8 + 2147450883) in SHT3 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 3 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT3t & _).
cbn [hl_sb A4L] in SEPT3t. assert (EQx : tk / 8 + A_SB + 3 = tk / 8 + 2147450883) by (unfold A_SB; lia). rewrite EQx in SEPT3t. clear EQx.
assert (cs_T3_T : csep (tk / 8 + 2147450883) 1 tk (Z.of_nat 72)) by (unfold csep; clear - SEPT3t; lia). clear SEPT3t.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 4 HP INtk ltac:(lia)) as SHT4.
replace (tk / 8 + 4 + A_SB) with (tk / 8 + 2147450884) in SHT4 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 4 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT4t & _).
cbn [hl_sb A4L] in SEPT4t. assert (EQx : tk / 8 + A_SB + 4 = tk / 8 + 2147450884) by (unfold A_SB; lia). rewrite EQx in SEPT4t. clear EQx.
assert (cs_T4_T : csep (tk / 8 + 2147450884) 1 tk (Z.of_nat 72)) by (unfold csep; clear - SEPT4t; lia). clear SEPT4t.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs m) as WM.
pose proof (bv_unsigned_in_range 8 cb) as CBR; unfold bv_modulus in CBR; cbn in CBR.
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8, A_SB in *.
pose proof (munch_refl [(tk, tk + 72)] m) as MU.

assert (ADVK : forall mX (isdX : word) gpX a1X a2X a3X a4X a5X a6X,
PE_INV_A HIx GA (PEF tk oldl newl len lenr sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo mX md A B (TST depth levels co pb pbs (TS isdX stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) cb nb pj sv errv ->
PBOKat mX (TST depth levels co pb pbs (TS isdX stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) bnd ->
gpX = gp ->
AJ5 A4L HIx A T md
(Q1Y6.Mq2.pe_msE (PEF tk oldl newl len lenr sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) 0x949ec (Z_to_bv 64 (tk / 8 + 2147450884)) gpX (Z_to_bv 64 (tk / 8 + 3)) t1 t2 (Z_to_bv 64 (sb + co + 1)) a1X a2X a3X a4X a5X a6X (Z_to_bv 64 pb)
(Z_to_bv 64 (co - co0)) (Z_to_bv 64 (tk + 20)) (Z_to_bv 64 (Z.of_nat depth)) (Z_to_bv 64 (sb + co)) (Z_to_bv 64 (tk + 32)) (Z_to_bv 64 Ff) (Z_to_bv 64 q)
(Z_to_bv 64 (sb + co0)) (Z_to_bv 64 (tk + 64)) (Z_to_bv 64 (Ff + 64)) (Z_to_bv 64 (tk / 8 + 2147450888)) (Z_to_bv 64 lenr) F fc mX)).
{ intros mX isdX gpX a1X a2X a3X a4X a5X a6X INVX PBKX ->.
set (tsX := TST depth levels co pb pbs (TS isdX stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
eapply (num_adv_A (PEF tk oldl newl len lenr sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo mX md A B tsX l co0 bnd cb nb pj sv errv T);
[exact STC | reflexivity | exact INVX | exact PBKX | exact CSTR | exact Hl | exact Hst | cbn [t_co tsX]; lia | exact Hco | exact Hc | exact Hnz | | |].
-
intros m' cb' a5' Hco' Hcb' Hnz' INV' PBK'.
eapply (IH (PEF tk oldl newl len lenr sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m' md A B (ts_set_co tsX (co + 1)) l co0 bnd cb' nb pj sv errv T);
[exact STC | reflexivity | exact INV' | exact PBK' | exact CSTR | exact Hl | exact Hst | cbn [t_co ts_set_co]; lia | exact Hco' | exact Hcb' | exact Hnz' | cbn [t_co ts_set_co pf_len]; lia | |];
cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote ts_set_co ts_set_x tsX].
+ intros m'' co'' cb'' isdq a0' a1' a2' a3' a5'' a6' Hco'' Hcb'' INV'' PBK''.
eapply (Kexit m'' co'' cb'' isdq); [cbn [pf_len] in *; lia | exact Hcb'' | exact INV'' | exact PBK''].
+ intros m'' co'' cb'' isdq a1' a2' a3' a4' a5'' a6' Hco'' Eco'' Elr INV'' PBK''.
eapply (Keof m'' co'' cb'' isdq); [cbn [pf_len] in *; lia | exact Eco'' | exact Elr | exact INV'' | exact PBK''].
-
intros m' cb' a0' a5' Hco' Hcb' Ez INV' PBK'.
cbn [t_co tsX pf_len] in Hco'.
eapply (Kexit m' (co + 1) cb' isdX); [lia | exact Hcb' | exact INV' | exact PBK'].
-
intros m' a4' Eco' Elr INV' PBK'. cbn [t_co tsX pf_len pf_lenr] in Eco', Elr.
eapply (Keof m' co cb isdX); [lia | exact Eco' | exact Elr | exact INV' | exact PBK']. }
stash Himg_t. stash IH. stash Kexit. stash Keof.
reenterA asegs A4L HIx asegs_wx HP.

assert (ACCK : forall a1X a2X a3X a4X a5X a6X s4X,
evt asegs (AJ5e A4L HIx A T md)
(Q1Y6.Mq2.pe_msE (PEF tk oldl newl len lenr sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) 0x9497c (Z_to_bv 64 (tk / 8 + 2147450884)) gp (Z_to_bv 64 (tk / 8 + 3)) t1 t2 (Z_to_bv 64 (sb + co + 1)) a1X a2X a3X a4X a5X a6X (Z_to_bv 64 pb)
(Z_to_bv 64 (co - co0)) s4X (Z_to_bv 64 (Z.of_nat depth)) (Z_to_bv 64 (sb + co)) (Z_to_bv 64 (tk + 32)) (Z_to_bv 64 Ff) (Z_to_bv 64 q)
(Z_to_bv 64 (sb + co0)) (Z_to_bv 64 (tk + 64)) (Z_to_bv 64 (Ff + 64)) (Z_to_bv 64 (tk / 8 + 2147450888)) (Z_to_bv 64 lenr) F fc m)).
{ intros a1X a2X a3X a4X a5X a6X s4X. unfold Q1Y6.Mq2.pe_msE. cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pa_sp0 pa_F]. unfold shA. a4l. unfold A_SB.
step.
step.
asan_rechkA.
evt_done5.
eapply (ADVK m isd gp); [exact INV0 | exact PBK | reflexivity]. }

assert (ISDK : forall a1X a2X a3X a4X a5X a6X,
evt asegs (AJ5e A4L HIx A T md)
(Q1Y6.Mq2.pe_msE (PEF tk oldl newl len lenr sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) 0x949cc (Z_to_bv 64 (tk / 8 + 2147450884)) gp (Z_to_bv 64 (tk / 8 + 3)) t1 t2 (Z_to_bv 64 (sb + co + 1)) a1X a2X a3X a4X a5X a6X (Z_to_bv 64 pb)
(Z_to_bv 64 (co - co0)) (Z_to_bv 64 (tk + 20)) (Z_to_bv 64 (Z.of_nat depth)) (Z_to_bv 64 (sb + co)) (Z_to_bv 64 (tk + 32)) (Z_to_bv 64 Ff) (Z_to_bv 64 q)
(Z_to_bv 64 (sb + co0)) (Z_to_bv 64 (tk + 64)) (Z_to_bv 64 (Ff + 64)) (Z_to_bv 64 (tk / 8 + 2147450888)) (Z_to_bv 64 lenr) F fc m)).
{ intros a1X a2X a3X a4X a5X a6X. unfold Q1Y6.Mq2.pe_msE. cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pa_sp0 pa_F]. unfold shA. a4l. unfold A_SB.
step.
step.
rewrite ?sxb_zero, ?zxb_zero.
step.
if_false.
step.
step.
stepz.
asan_rechkA.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _ |- _ =>
evt_done5;
destruct (PE_INV_A_tokw1 HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m mc md A B ts0
cb nb pj sv errv co (TS (Z_to_bv 64 1) stpos (Z_to_bv 64 co) err ucs high quote) STC INV0 MUc WMc MIc TOKc ltac:(cbn [pf_len]; lia) eq_refl) as [INV1 PBT1]
end end.
eapply (ADVK _ (Z_to_bv 64 1) gp); [exact INV1 | exact (PBT1 _ PBK) | reflexivity]. }

assert (DOTK : forall a1X a2X a3X a5X a6X s4X,
evt asegs (AJ5e A4L HIx A T md)
(Q1Y6.Mq2.pe_msE (PEF tk oldl newl len lenr sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) 0x949a8 (Z_to_bv 64 (tk / 8 + 2147450884)) gp (Z_to_bv 64 (tk / 8 + 3)) t1 t2 (Z_to_bv 64 (sb + co + 1)) a1X a2X a3X (Z_to_bv 64 (bv_unsigned cb)) a5X a6X (Z_to_bv 64 pb)
(Z_to_bv 64 (co - co0)) s4X (Z_to_bv 64 (Z.of_nat depth)) (Z_to_bv 64 (sb + co)) (Z_to_bv 64 (tk + 32)) (Z_to_bv 64 Ff) (Z_to_bv 64 q)
(Z_to_bv 64 (sb + co0)) (Z_to_bv 64 (tk + 64)) (Z_to_bv 64 (Ff + 64)) (Z_to_bv 64 (tk / 8 + 2147450888)) (Z_to_bv 64 lenr) F fc m)).
{ intros a1X a2X a3X a5X a6X s4X. unfold Q1Y6.Mq2.pe_msE. cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pa_sp0 pa_F]. unfold shA. a4l. unfold A_SB.
step.
step.
rewrite ?sxb_zero, ?zxb_zero.
step.
step.
if_false.
step.
step.
destruct (Z.eq_dec (bv_unsigned cb) 46) as [E46 | N46].
2:{ if_truex. evt_done5. unstash Kexit. eapply (Kexit m co cb isd); [lia | exact Hc | exact INV0 | exact PBK]. }
if_falsex.
step.
step.
step.
destruct (Z.eq_dec (bv_unsigned (sx32 isd)) 0) as [EI0 | NI0].
2:{ if_truex. evt_done5. unstash Kexit. eapply (Kexit m co cb isd); [lia | exact Hc | exact INV0 | exact PBK]. }
if_falsex.
apply ISDK. }

assert (SIGNK : forall a1X a2X a3X a5X a6X s4X,
evt asegs (AJ5e A4L HIx A T md)
(Q1Y6.Mq2.pe_msE (PEF tk oldl newl len lenr sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) 0x94964 (Z_to_bv 64 (tk / 8 + 2147450884)) gp (Z_to_bv 64 (tk / 8 + 3)) t1 t2 (Z_to_bv 64 (sb + co + 1)) a1X a2X a3X (Z_to_bv 64 (bv_unsigned cb)) a5X a6X (Z_to_bv 64 pb)
(Z_to_bv 64 (co - co0)) s4X (Z_to_bv 64 (Z.of_nat depth)) (Z_to_bv 64 (sb + co)) (Z_to_bv 64 (tk + 32)) (Z_to_bv 64 Ff) (Z_to_bv 64 q)
(Z_to_bv 64 (sb + co0)) (Z_to_bv 64 (tk + 64)) (Z_to_bv 64 (Ff + 64)) (Z_to_bv 64 (tk / 8 + 2147450888)) (Z_to_bv 64 lenr) F fc m)).
{ intros a1X a2X a3X a5X a6X s4X. unfold Q1Y6.Mq2.pe_msE. cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pa_sp0 pa_F]. unfold shA. a4l. unfold A_SB.
step.
step.
destruct (Z.eq_dec (bv_unsigned cb) 45) as [E45 | N45].
{ if_falsex.
step.
destruct (Z.eq_dec (bv_unsigned s4X) 0) as [ES0 | NS0].
2:{ if_truex. apply ACCK. }
if_falsex.
step.
step.
if_truex. apply DOTK. }
if_truex.
step.
step.
destruct (Z.eq_dec (bv_unsigned cb) 43) as [E43 | N43].
2:{ if_truex. apply DOTK. }
if_falsex.
step.
destruct (Z.eq_dec (bv_unsigned a3X) 0) as [EA0 | NA0].
{ if_truex. apply DOTK. }
if_falsex. apply ACCK. }

assert (NDIGK : forall a1X a2X a3X a5X a6X s4X,
evt asegs (AJ5e A4L HIx A T md)
(Q1Y6.Mq2.pe_msE (PEF tk oldl newl len lenr sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) 0x94960 (Z_to_bv 64 (tk / 8 + 2147450884)) gp (Z_to_bv 64 (tk / 8 + 3)) t1 t2 (Z_to_bv 64 (sb + co + 1)) a1X a2X a3X (Z_to_bv 64 (bv_unsigned cb)) a5X a6X (Z_to_bv 64 pb)
(Z_to_bv 64 (co - co0)) s4X (Z_to_bv 64 (Z.of_nat depth)) (Z_to_bv 64 (sb + co)) (Z_to_bv 64 (tk + 32)) (Z_to_bv 64 Ff) (Z_to_bv 64 q)
(Z_to_bv 64 (sb + co0)) (Z_to_bv 64 (tk + 64)) (Z_to_bv 64 (Ff + 64)) (Z_to_bv 64 (tk / 8 + 2147450888)) (Z_to_bv 64 lenr) F fc m)).
{ intros a1X a2X a3X a5X a6X s4X. unfold Q1Y6.Mq2.pe_msE. cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pa_sp0 pa_F]. unfold shA. a4l. unfold A_SB.
step.
destruct (Z.eq_dec (bv_unsigned a1X) 0) as [EA1 | NA1].
2:{ if_falsex. apply SIGNK. }
if_truex.
step.
step.
step.
rewrite (unsigned_lit (bv_unsigned cb)) by lia.
pose proof (OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.Bytes.lor_lt_pow2 (bv_unsigned cb) 32 8 ltac:(lia) ltac:(lia)) as X32.
destruct (Z.eq_dec (Z.lor (bv_unsigned cb) 32) 101) as [E101 | N101].
2:{ if_truex. apply SIGNK. }
if_falsex.
step.
step.
step.
apply ISDK. }
step. step.
step.
destruct (Z_le_dec 48 (bv_unsigned cb)) as [G48 | L48]; [destruct (Z_le_dec (bv_unsigned cb) 57) as [L57 | G57] |].
-
if_truex. apply ACCK.
- if_falsex. apply NDIGK.
- replace (Z_to_bv 64 (bv_unsigned cb + -48)) with (Z_to_bv 64 (bv_unsigned cb + -48 + 2^64)).
2:{ apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
rewrite <- (Z_mod_plus_full (bv_unsigned cb + -48) 1 (2^64)). f_equal. }
if_falsex. apply NDIGK.
Qed.

Lemma num_eof_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel) (co0 k0 : Z)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kB : nat)
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 s6 s7 t4 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
PBOKat m ts (co0 + k0) -> k0 <= 0 -> BOK pf pa ts B kB ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_number ->
t_co ts = pf_len pf -> 0 <= co0 < pf_len pf ->
(forall m' md' A' B' pbs' errv' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' s11' t4' t6' F' fc',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' (ts_pbs (ts_set_x ts (t_co ts) (tx_err (t_x ts) (Z_to_bv 64 1))) pbs') cb nb pj sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msO asegs pf pa APE_OUT x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' (Z_to_bv 64 (pf_tk pf + 56)) s11' t4' t6' F' fc' m')) ->
(forall m' md' A' B' pbs' errv' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' s11' t4' t6' F' fc',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' (ts_pbs (ts_set_x ts (t_co ts) (tx_err (t_x ts) (Z_to_bv 64 1))) pbs') cb nb pj sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msO asegs pf pa APE_ERRMEM x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' (Z_to_bv 64 (pf_tk pf + 56)) s11' t4' t6' F' fc' m')) ->
AJ5 A4L HIx A T md
(Q1Y6.Mq2.pe_msE pf pa 0x97da8 x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 (Z_to_bv 64 (t_pb ts)) (Z_to_bv 64 (pf_len pf - 1 - co0)) (Z_to_bv 64 (pf_tk pf + 20)) (Z_to_bv 64 (Z.of_nat (t_depth ts)))
s6 s7 (Z_to_bv 64 (pa_F pa)) (Z_to_bv 64 q) (Z_to_bv 64 (pf_sb pf + co0)) (Z_to_bv 64 (pf_tk pf + 64)) t4 (Z_to_bv 64 (pf_tk pf / 8 + 2147450888)) t6 F fc m).
Proof.
intros until fc. intros STC BSL INV PBK K0 BK Hl Hst Heof Hco0 Kout Kerr16. pose proof INV as INV0.
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
destruct INV as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof REST as (HP & LV & _).
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
unfold pe_frameA in FR. destruct FR as (SLOTS & _). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS.
unfold Q1Y6.Mq2.pe_msE, pe_msA, pe_msO in *.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * mxd) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t.
blk_factsA A4L HIx HP q (32 * mxd) Hqal Hqlo Hqhi Himg_q.
subst co.
pose proof (q_ne_tkA HIx _ _ _ _ _ _ _ _ _ _ HP) as Hqtk. cbn [pf_tk] in Hqtk.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ tk 72 q (32 * mxd) HP (in_or_app _ LM _ (or_introl INtk)) (in_or_app _ LM _ (or_introl INq)) ltac:(congruence)) as Hdtq.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 4 HP INtk ltac:(lia)) as SHT4.
replace (tk / 8 + 4 + A_SB) with (tk / 8 + 2147450884) in SHT4 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 4 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT4c & SEPT4q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 4 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT4t & _).
cbn [hl_sb A4L] in SEPT4c, SEPT4q, SEPT4t. assert (EQx : tk / 8 + A_SB + 4 = tk / 8 + 2147450884) by (unfold A_SB; lia). rewrite EQx in SEPT4c, SEPT4q, SEPT4t. clear EQx.
pose proof (stack_shadowA HIx _ _ _ _ _ _ _ q mxd 0 0 HP INq ltac:(lia) ltac:(lia)) as SHQ0.
replace (q / 8 + 4 * 0 + 0 + A_SB) with (q / 8 + 2147450880) in SHQ0 by (unfold A_SB; lia).
pose proof (TSK depth l Hl) as Ld. unfold srec_cells in Ld. rewrite Hst in Ld.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(tk, tk + 72)] m) as MU.
unfold APE_OUT, APE_ERRMEM in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
stash Himg_t. stash Himg_q. clear PB TSK REST LV SEPT4c SEPT4q SEPT4t.
reenterA asegs A4L HIx asegs_wx HP.
step.

lazymatch goal with |- evt _ _ (MS ?R ?FF _ ?fcc None ?mm ?rom) =>
assert (TAILE : evt asegs (AJ5e A4L HIx A T md) (MS (bvmap_set 10 (Z_to_bv 64 1) R) FF (Z_to_bv 64 0x97eb4) fcc None mm rom)) end.
{ step.
asan_rechkM 1.
step.
norm_w32. replace (len - 1 - co0 + 1) with (len - co0) by lia.
stepz.
step. step. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _ |- _ =>
evt_done5;
destruct (PE_INV_A_tokw1 HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m mc md A B ts0
cb nb pj sv errv len (tx_err (t_x ts0) (Z_to_bv 64 1)) STC INV0 MUc WMc MIc TOKc ltac:(cbn [pf_len]; lia) eq_refl) as [INVe PBKe]
end end.
set (tsE := ts_set_x ts0 len (tx_err (t_x ts0) (Z_to_bv 64 1))) in *.
eapply (pe_memappend_pk HIx GA GA_pres MAPP (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo _ md A B tsE cb nb pj sv errv T co0 k0 (len - co0));
[exact STC | exact BSL | exact INVe | exact (PBKe _ PBK) | exact K0 | lia | lia | cbn [t_co tsE ts_set_x]; lia | cbn [pf_len]; lia | cbn [pf_len]; lia
| exact (BOK_set_x _ _ ts0 B kB len _ ltac:(cbn [t_co ts0]; lia) BK) | rewrite unsigned_lit by lia; reflexivity |].
intros m2 md2 A2 B2 pbs2 errv2 r w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 F2 fc2 INV2 OUT2 FS2 FRM2.
cbn [pf_spf] in *. unfold A_TP in *.
clear Htal Htlo Hthi Hqal Hqlo Hqhi INV0 PBK BK INVe PBKe Hdtq. try clear SHQ0. try clear Ld. clear TOK SLOTS SHT4 INtk INq HP.
pose proof INV2 as [CORE2 REST2]. destruct CORE2 as (_ & _ & _ & _ & _ & _ & _ & _ & FR2). pose proof (proj1 REST2) as HP.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 (ts_pbs tsE pbs2))) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 4 HP INtk ltac:(lia)) as SHT4.
replace (tk / 8 + 4 + A_SB) with (tk / 8 + 2147450884) in SHT4 by (unfold A_SB; lia).
pose proof FR2 as (SLOTS & _). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS. cbn [pf_tk pf_spf pf_lenr pa_F pa_sp0 pa_oldloc pa_newloc] in SLOTS. unfold shA in SLOTS. a4l. unfold SB2, SB4, SB7, SB8 in SLOTS.
clear REST2 FR2.
reenterA asegs A4L HIx asegs_wx HP.
destruct OUT2 as [(-> & _ & _) | [-> Epbs2]].
- do 4 step.
if_truex.
evt_done5.
eapply (Kout m2 md2 A2 B2 pbs2 errv2); [exact INV2 | exact FS2 | exact FRM2].
- replace (Z_to_bv 64 (2^64 - 1)) with (Z_to_bv 64 (-1)) by (apply bv_eq; vm_compute; reflexivity).
do 4 step.
if_false.
step.
step.
rewrite ?sxb_zero, ?zxb_zero.
step.
if_true.
evt_done5.
eapply (Kerr16 m2 md2 A2 B2 pbs2 errv2); [exact INV2 | exact FS2 | exact FRM2]. }
step.
destruct depth as [|dp].
- if_false.
asan_chkA.
replace (q + 32 * Z.of_nat 0) with q in Ld by lia.
step.
norm_sx32.
step.
if_truex.
step. step.
apply TAILE.
- if_truex.
step. step.
apply TAILE.
Qed.

Definition pe_jtabNA : list byte := Eval vm_compute in match image_bytes asegs 0x22ca4 260 with Some bs => bs | None => [] end.
Lemma pe_jtabNA_ro : forall m, mem_inv asegs m -> ro_cells asegs m 0x22ca4 [CB 260 pe_jtabNA].
Proof.
intros m MI. change 260%nat with (length pe_jtabNA).
apply ro_cells_image; [exact MI | vm_compute; reflexivity | lia | ].
change (Z.of_nat (length pe_jtabNA)) with 260%Z. lia.
Qed.
Definition num_jtA (c : Z) : Z := if zin c [9; 10; 13; 32; 44; 47; 73] then 0x94d60 else 0x987c0.

Lemma num_chk_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet)
(x1 gp t0 t1 t2 a0 a1 a2 a3 a5 a6 a7 s3 s6 s7 s10 s11 t4 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
(forall a0' a1',
AJ5 A4L HIx A T md
(Q1Y6.Mq2.pe_msE pf pa 0x94d60 x1 gp t0 t1 t2 a0' a1' a2 a3 (Z_to_bv 64 (bv_unsigned cb)) a5 a6 a7 s3 (Z_to_bv 64 (pf_tk pf + 20)) (Z_to_bv 64 (Z.of_nat (t_depth ts)))
s6 s7 (Z_to_bv 64 (pa_F pa)) (Z_to_bv 64 (pf_tk pf + 56)) s11 (Z_to_bv 64 (pf_tk pf + 64)) t4 (Z_to_bv 64 (pf_tk pf / 8 + 2147450888)) t6 F fc m)) ->
(forall m' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' s11' t4' t6',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md A B (ts_set_x ts (t_co ts) (tx_err (t_x ts) (Z_to_bv 64 7))) cb nb pj sv errv ->
AJ5 A4L HIx A T md
(pe_msO asegs pf pa APE_OUT x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' (Z_to_bv 64 (pf_tk pf + 56)) s11' t4' t6' F fc m')) ->
AJ5 A4L HIx A T md
(Q1Y6.Mq2.pe_msE pf pa 0x94b20 x1 gp t0 t1 t2 a0 a1 a2 a3 (Z_to_bv 64 (bv_unsigned cb)) a5 a6 a7 s3 (Z_to_bv 64 (pf_tk pf + 20)) (Z_to_bv 64 (Z.of_nat (t_depth ts)))
s6 s7 (Z_to_bv 64 (pa_F pa)) s10 s11 (Z_to_bv 64 (pf_tk pf + 64)) t4 (Z_to_bv 64 (pf_tk pf / 8 + 2147450888)) t6 F fc m).
Proof.
intros until fc. intros STC INV Kok Kout. pose proof INV as INV0.
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
destruct INV as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof REST as (HP & _).
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
unfold pe_frameA in FR. destruct FR as (SLOTS & _). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS.
unfold Q1Y6.Mq2.pe_msE, pe_msA, pe_msO in *.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 4 HP INtk ltac:(lia)) as SHT4.
replace (tk / 8 + 4 + A_SB) with (tk / 8 + 2147450884) in SHT4 by (unfold A_SB; lia).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (pe_jtabNA_ro m MI) as JT.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(tk, tk + 72)] m) as MU.
pose proof (bv_unsigned_in_range 8 cb) as CBR; unfold bv_modulus in CBR; cbn in CBR.
unfold APE_OUT in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
stash Himg_t. clear PB TSK REST.
reenterA asegs A4L HIx asegs_wx HP.
step.

lazymatch goal with |- evt _ _ (MS ?R ?FF _ ?fcc None ?mm ?rom) =>
assert (ERR7 : forall a0v a1v, evt asegs (AJ5e A4L HIx A T md) (MS (bvmap_set 10 a0v (bvmap_set 11 a1v R)) FF (Z_to_bv 64 0x987c0) fcc None mm rom)) end.
{ intros a0v a1v.
step.
asan_rechkA.
step. step.
step.
stepz.
step. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _ |- _ =>
evt_done5;
destruct (PE_INV_A_tokw1 HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m mc md A B ts0
cb nb pj sv errv co (tx_err (t_x ts0) (Z_to_bv 64 7)) STC INV0 MUc WMc MIc TOKc ltac:(cbn [pf_len]; lia) eq_refl) as [INVe _]
end end.
eapply Kout. exact INVe. }

lazymatch goal with |- evt _ _ (MS ?R ?FF _ ?fcc None ?mm ?rom) =>
assert (OKJ : forall a0v a1v, evt asegs (AJ5e A4L HIx A T md) (MS (bvmap_set 10 a0v (bvmap_set 11 a1v R)) FF (Z_to_bv 64 0x94d60) fcc None mm rom)) end.
{ intros a0v a1v. evt_done5. apply Kok. }
step.
destruct depth as [|dp].
{ if_true. apply OKJ. }
if_falsex.
step. step.
step.
assert (JTK : forall a0v a1v, evt asegs (AJ5e A4L HIx A T md)
(MS (bvmap_set 10 a0v (bvmap_set 11 a1v
(mkR x1 (Z_to_bv 64 spf) gp (Z_to_bv 64 6434400) t0 t1 t2 (Z_to_bv 64 sp0) (Z_to_bv 64 spf) a0 a1 a2 a3 (Z_to_bv 64 (bv_unsigned cb)) a5 a6 a7
(Z_to_bv 64 (Ff / 8 + 2147450880)) s3 (Z_to_bv 64 (tk + 20)) (Z_to_bv 64 (Z.of_nat (S dp))) s6 s7 (Z_to_bv 64 Ff) (Z_to_bv 64 2147450880) (Z_to_bv 64 (tk + 56)) s11
(Z_to_bv 64 (tk + 64)) t4 (Z_to_bv 64 (tk / 8 + 2147450888)) t6)))
F (Z_to_bv 64 (num_jtA (bv_unsigned cb))) fc None m (seg_rom asegs))).
{ intros a0v a1v. unfold num_jtA. destruct (zin (bv_unsigned cb) [9; 10; 13; 32; 44; 47; 73]); [apply OKJ | apply ERR7]. }
destruct (Z_lt_dec (bv_unsigned cb) 9) as [LT9 | GE9].
-
replace (Z_to_bv 64 (bv_unsigned cb + -9)) with (Z_to_bv 64 (bv_unsigned cb + -9 + 2^64)).
2:{ apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
rewrite <- (Z_mod_plus_full (bv_unsigned cb + -9) 1 (2^64)). f_equal. }
if_truex.
step. step.
step.
replace (Z_to_bv 64 (bv_unsigned cb + -93)) with (Z_to_bv 64 (bv_unsigned cb + -93 + 2^64)).
2:{ apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
rewrite <- (Z_mod_plus_full (bv_unsigned cb + -93) 1 (2^64)). f_equal. }
if_falsex.
step.
apply ERR7.
- destruct (Z_lt_dec 73 (bv_unsigned cb)) as [GT73 | LE73].
+ if_truex.
step. step.
step.
destruct (Z_lt_dec (bv_unsigned cb) 93) as [LT93 | GE93].
* replace (Z_to_bv 64 (bv_unsigned cb + -93)) with (Z_to_bv 64 (bv_unsigned cb + -93 + 2^64)).
2:{ apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
rewrite <- (Z_mod_plus_full (bv_unsigned cb + -93) 1 (2^64)). f_equal. }
if_falsex. step.
apply ERR7.
* destruct (Z_lt_dec 125 (bv_unsigned cb)) as [GT125 | LE125].
{ if_falsex. step.
apply ERR7. }
if_truex.
do 6 step.
step.
assert (MSK : forall c, 93 <= c <= 125 ->
negb (bv_eqb (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (4294971393 ≫ (bv_unsigned (Z_to_bv 64 (c + -93)) mod 64)))) 1)) (Z_to_bv 64 0)) = zin c [93; 105; 125]).
{ intros c Rc. enum_from c 93%Z 33%nat; vm_compute; reflexivity. }
rewrite (MSK (bv_unsigned cb) ltac:(lia)). clear MSK.
destruct (zin (bv_unsigned cb) [93; 105; 125]); cbv iota.
{ apply OKJ. }
step.
apply ERR7.
+ if_falsex.
step.
rewrite (unsigned_lit (bv_unsigned cb + -9)) by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
step. step. step.
pose proof (bytes_at_read asegs m 0x22ca4 pe_jtabNA ((bv_unsigned cb + -9) * 4) 4 (ro_cells_bytes_atA _ _ _ _ JT) ltac:(lia)
ltac:(change (length pe_jtabNA) with 260%nat; lia)) as RD.
unfold wa in RD. replace (0x22ca4 + (bv_unsigned cb + -9) * 4) with ((bv_unsigned cb + -9) * 4 + 142500) in RD by lia.
step. step. step.
assert (R9 : 9 <= bv_unsigned cb <= 73) by lia.
match goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) =>
replace pc with (Z_to_bv 64 (num_jtA (bv_unsigned cb))); [apply JTK |] end.
clear - R9. enum_from (bv_unsigned cb) 9%Z 65%nat; apply bv_eq; vm_compute; reflexivity.
Qed.

Lemma num_app_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (co0 k0 : Z)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kB : nat)
(gp t1 t2 a0 a1 a2 a3 a4 a5 a6 s5 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
PBOKat m ts (co0 + k0) -> k0 <= 0 -> BOK pf pa ts B kB -> 0 <= co0 <= t_co ts -> t_co ts < pf_len pf ->
(forall m' md' A' B' pbs' errv' gp' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' F' fc',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' (ts_pbs ts pbs') cb nb pj sv errv' ->
PBOKat m' (ts_pbs ts pbs') (t_co ts + k0) -> BOK pf pa (ts_pbs ts pbs') B' kB ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(Q1Y6.Mq2.pe_msE pf pa 0x94d98 (Z_to_bv 64 (pf_tk pf / 8 + 2147450884)) gp' (Z_to_bv 64 (pf_tk pf / 8 + 3)) t1' t2' a0' a1' a2' a3' a4' a5' a6' a7'
(Z_to_bv 64 (t_co ts - co0)) (Z_to_bv 64 (pf_tk pf + 20)) s5' (Z_to_bv 64 (pf_sb pf + t_co ts)) (Z_to_bv 64 (pf_tk pf + 32)) (Z_to_bv 64 (pa_F pa)) (Z_to_bv 64 (pf_tk pf + 56))
(Z_to_bv 64 (pf_sb pf + co0)) (Z_to_bv 64 (pf_tk pf + 64)) (Z_to_bv 64 (pa_F pa + 64)) (Z_to_bv 64 (pf_tk pf / 8 + 2147450888)) (Z_to_bv 64 (pf_lenr pf)) F' fc' m')) ->
(forall m' md' A' B' pbs' errv' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' s11' t4' t6' F' fc',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' (ts_set_x (ts_pbs ts pbs') (t_co ts) (tx_err (t_x ts) (Z_to_bv 64 16))) cb nb pj sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msO asegs pf pa APE_OUT x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' (Z_to_bv 64 (pf_tk pf + 56)) s11' t4' t6' F' fc' m')) ->
AJ5 A4L HIx A T md
(Q1Y6.Mq2.pe_msE pf pa 0x94d60 (Z_to_bv 64 (pf_tk pf / 8 + 2147450884)) gp (Z_to_bv 64 (pf_tk pf / 8 + 3)) t1 t2 a0 a1 a2 a3 a4 a5 a6 (Z_to_bv 64 (t_pb ts))
(Z_to_bv 64 (t_co ts - co0)) (Z_to_bv 64 (pf_tk pf + 20)) s5 (Z_to_bv 64 (pf_sb pf + t_co ts)) (Z_to_bv 64 (pf_tk pf + 32)) (Z_to_bv 64 (pa_F pa)) (Z_to_bv 64 (pf_tk pf + 56))
(Z_to_bv 64 (pf_sb pf + co0)) (Z_to_bv 64 (pf_tk pf + 64)) (Z_to_bv 64 (pa_F pa + 64)) (Z_to_bv 64 (pf_tk pf / 8 + 2147450888)) (Z_to_bv 64 (pf_lenr pf)) F fc m).
Proof.
intros until fc. intros STC BSL INV PBK K0 BK Hco0 Hco Kapp Kout. pose proof INV as INV0.
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
destruct INV as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof REST as (HP & LV & _).
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
unfold Q1Y6.Mq2.pe_msE, pe_msA, pe_msO in *.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
unfold APE_OUT in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
clear PB TSK REST LV TOK FR.
reenterA asegs A4L HIx asegs_wx HP.
step.
destruct (Z.eq_dec (co - co0) 0) as [E0 | N0].
{ rewrite E0. if_true. evt_done5.
replace (Z_to_bv 64 0) with (Z_to_bv 64 (co - co0)) by (rewrite E0; reflexivity).
eapply (Kapp m md A B pbs errv); [exact INV0 | eapply PBOKat_weaken; [| exact PBK]; lia | exact BK | apply fsaved_refl | intros X; exact X]. }
if_falsex.
step. step. step. step.
step.
evt_done5.
eapply (pe_memappend_pk HIx GA GA_pres MAPP (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m md A B ts0 cb nb pj sv errv T co0 k0 (co - co0));
[exact STC | exact BSL | exact INV0 | exact PBK | exact K0 | lia | lia | cbn [t_co ts0]; lia | cbn [pf_len]; lia | cbn [pf_len]; lia | exact BK | rewrite unsigned_lit by lia; reflexivity |].
intros m2 md2 A2 B2 pbs2 errv2 r w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 F2 fc2 INV2 OUT2 FS2 FRM2.
cbn [pf_spf] in *. unfold A_TP in *.
clear HP INV0 PBK BK MI.
pose proof INV2 as [CORE2 REST2]. destruct CORE2 as (_ & _ & _ & _ & TOK & _ & _ & _ & FR2). pose proof (proj1 REST2) as HP.
unfold ts_pbs, ts0 in TOK. cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_tk pf_mxd pf_fl] in TOK.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 (ts_pbs ts0 pbs2))) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 4 HP INtk ltac:(lia)) as SHT4.
replace (tk / 8 + 4 + A_SB) with (tk / 8 + 2147450884) in SHT4 by (unfold A_SB; lia).
pose proof FR2 as (SLOTS & _). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS. cbn [pf_tk pf_spf pf_lenr pa_F pa_sp0 pa_oldloc pa_newloc] in SLOTS. unfold shA in SLOTS. a4l. unfold SB2, SB4, SB7, SB8 in SLOTS.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. a4l.
pose proof (wmono_refl asegs m2) as WM.
pose proof (munch_refl [(tk, tk + 72)] m2) as MU.
stash Himg_t. clear REST2 FR2.
reenterA asegs A4L HIx asegs_wx HP.
destruct OUT2 as [(-> & PBK2 & BK2) | [-> Epbs2]].
- do 7 step.
if_truex.
evt_done5.
eapply (Kapp m2 md2 A2 B2 pbs2 errv2); [exact INV2 | eapply PBOKat_weaken; [| exact PBK2]; lia | exact BK2 | exact FS2 | exact FRM2].
- replace (Z_to_bv 64 (2^64 - 1)) with (Z_to_bv 64 (-1)) by (apply bv_eq; vm_compute; reflexivity).
do 7 step.
if_false.
step.
step.
asan_rechkA.
step.
step.
stepz.
step. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m2 mc, WMc : wmono asegs m2 mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _ |- _ =>
evt_done5;
destruct (PE_INV_A_tokw1 HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m2 mc md2 A2 B2 (ts_pbs ts0 pbs2)
cb nb pj sv errv2 co (tx_err (t_x ts0) (Z_to_bv 64 16)) STC INV2 MUc WMc MIc TOKc ltac:(cbn [pf_len]; lia) eq_refl) as [INVe _]
end end.
eapply (Kout _ md2 A2 B2 pbs2 errv2); [exact INVe | exact FS2 | exact FRM2].
Qed.

Lemma number_mode_ss : forall ss c hn, 0 <= ss <= 26 -> lvl_mode ST_number ss = Some (c, hn) -> c = CNone /\ hn = false /\ ss = ST_start.
Proof. intros ss c hn R Hm. enum_z R ss; vm_compute in Hm; first [discriminate Hm | injection Hm as <- <-; repeat split; reflexivity]. Qed.

Lemma num_minf_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel) (co0 : Z)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP : Z) (kB : nat)
(gp t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
PBOKat m ts kP -> kP <= t_co ts -> BOK pf pa ts B kB ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_number ->
pj_16 pj = Z_to_bv 64 (pf_tk pf / 8 + 2147450881) ->
0 <= co0 <= t_co ts -> t_co ts < pf_len pf ->

(forall a0' a1' a2' a3',
AJ5 A4L HIx A T md
(Q1Y6.Mq2.pe_msE pf pa 0x94e5c (Z_to_bv 64 (pf_tk pf / 8 + 2147450884)) gp (Z_to_bv 64 (pf_tk pf / 8 + 3)) t1 t2 a0' a1' a2' a3' (Z_to_bv 64 (pf_tk pf + 8)) a5 a6 a7
(Z_to_bv 64 (t_co ts - co0)) (Z_to_bv 64 (pf_tk pf + 20)) (Z_to_bv 64 (pf_tk pf / 8 + 2147450887)) (Z_to_bv 64 (pf_sb pf + t_co ts)) (Z_to_bv 64 (pf_tk pf + 32)) (Z_to_bv 64 (pa_F pa)) (Z_to_bv 64 (pf_tk pf + 56))
(Z_to_bv 64 (pf_tk pf / 8 + 2147450881)) (Z_to_bv 64 (pf_tk pf + 64)) (Z_to_bv 64 (pa_F pa + 64)) (Z_to_bv 64 (pf_tk pf / 8 + 2147450888)) (Z_to_bv 64 (pf_lenr pf)) F fc m)) ->

(forall m' t0' a0' a1' a2' a3' a4' s5',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md A B
(ts_set_x (ts_lvl ts (TL ST_inf (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) (t_co ts)
(TS (ts_isd (t_x ts)) (Z_to_bv 64 0) (ts_choff (t_x ts)) (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))) cb nb pj sv errv ->
PBOKat m' (ts_set_x (ts_lvl ts (TL ST_inf (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) (t_co ts)
(TS (ts_isd (t_x ts)) (Z_to_bv 64 0) (ts_choff (t_x ts)) (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))) kP ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa APE_REDO (t_co ts) gp t0' t1 t2 a0' a1' a2' a3' a4' a5 a6 a7 s5' (Z_to_bv 64 (pf_tk pf + 56)) (Z_to_bv 64 (pa_F pa + 64)) F fc m')) ->
AJ5 A4L HIx A T md
(Q1Y6.Mq2.pe_msE pf pa 0x94d98 (Z_to_bv 64 (pf_tk pf / 8 + 2147450884)) gp (Z_to_bv 64 (pf_tk pf / 8 + 3)) t1 t2 a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (t_co ts - co0)) (Z_to_bv 64 (pf_tk pf + 20)) s5 (Z_to_bv 64 (pf_sb pf + t_co ts)) (Z_to_bv 64 (pf_tk pf + 32)) (Z_to_bv 64 (pa_F pa)) (Z_to_bv 64 (pf_tk pf + 56))
(Z_to_bv 64 (pf_sb pf + co0)) (Z_to_bv 64 (pf_tk pf + 64)) (Z_to_bv 64 (pa_F pa + 64)) (Z_to_bv 64 (pf_tk pf / 8 + 2147450888)) (Z_to_bv 64 (pf_lenr pf)) F fc m).
Proof.
intros until fc. intros STC INV PBK HkPc BK Hl Hst P16 Hco0 Hco Knext Kredo. pose proof INV as INV0. pe_openA STC INV.
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
pose proof FR as FR0. unfold pe_frameA in FR. destruct FR as (SLOTS & GAP & SAVED & FF & FSH).
unfold pe_slotsA in SLOTS. cbn zeta in SLOTS. unfold ff_cellsA in FF. rewrite P16 in SLOTS.
unfold Q1Y6.Mq2.pe_msE, pe_msA in *.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * mxd) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t.
blk_factsA A4L HIx HP q (32 * mxd) Hqal Hqlo Hqhi Himg_q.
pose proof (q_ne_tkA HIx _ _ _ _ _ _ _ _ _ _ HP) as Hqtk. cbn [pf_tk] in Hqtk.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ tk 72 q (32 * mxd) HP (in_or_app _ LM _ (or_introl INtk)) (in_or_app _ LM _ (or_introl INq)) ltac:(congruence)) as Hdtq.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs m) as WM.
pose proof (LV depth l Hl) as LVd. pose proof LVd as (ST26 & SS26 & _ & Md).
rewrite Nat.ltb_irrefl, Nat.eqb_refl in Md. destruct Md as (c0 & hn0 & Hmode & CLS0 & NM0).
destruct (number_mode_ss _ _ _ SS26 ltac:(rewrite <- Hst; exact Hmode)) as (Ec0 & Ehn0 & Ess). subst c0 hn0.
pose proof (TSK depth l Hl) as Ld. remember (q + 32 * Z.of_nat depth) as bse eqn:Hbse in Ld. unfold srec_cells in Ld.
assert (HbseR : q <= bse /\ bse + 32 <= q + (32 * mxd)) by (subst bse; lia).
assert (Hb8 : bse mod 8 = 0) by (subst bse; clear - Hqal; Z.div_mod_to_equations; lia).
pose proof (bv_unsigned_in_range 8 cb) as CBR; unfold bv_modulus in CBR; cbn in CBR.
shq_facts HP INq INtk q mxd tk (Z.of_nat depth) 0 SHQ0 SEPQ0c SEPQ0q SEPQ0t.
replace (q / 8 + 4 * (Z.of_nat depth) + 0 + A_SB) with (bse / 8 + 2147450880) in SHQ0 by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia).
assert (EQx : q / 8 + A_SB + (4 * (Z.of_nat depth) + 0) = bse / 8 + 2147450880) by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia). rewrite EQx in SEPQ0c, SEPQ0q, SEPQ0t. clear EQx.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 1 HP INtk ltac:(lia)) as SHT1.
replace (tk / 8 + 1 + A_SB) with (tk / 8 + 2147450881) in SHT1 by (unfold A_SB; lia).
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 2 HP INtk ltac:(lia)) as SHT2.
replace (tk / 8 + 2 + A_SB) with (tk / 8 + 2147450882) in SHT2 by (unfold A_SB; lia).
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 7 HP INtk ltac:(lia)) as SHT7.
replace (tk / 8 + 7 + A_SB) with (tk / 8 + 2147450887) in SHT7 by (unfold A_SB; lia).
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 3 HP INtk ltac:(lia)) as SHT3.
replace (tk / 8 + 3 + A_SB) with (tk / 8 + 2147450883) in SHT3 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 3 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT3c & SEPT3q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 3 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT3t & _).
cbn [hl_sb A4L] in SEPT3c, SEPT3q, SEPT3t. assert (EQx : tk / 8 + A_SB + 3 = tk / 8 + 2147450883) by (unfold A_SB; lia). rewrite EQx in SEPT3c, SEPT3q, SEPT3t. clear EQx.
destruct PB as (buf & bpos & cap & pre & post & Epbs & Lpre & CORE1). destruct CORE1 as (Hbp & Hcap & Hlen & PBC & BUFC).
assert (INpb : In (pb, PB_SZ) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA, tstate_blocks, ts0; cbn [t_pbs]; rewrite Epbs; apply in_or_app; left; left; reflexivity).
assert (INbuf : In (buf, cap) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA, tstate_blocks, ts0; cbn [t_pbs]; rewrite Epbs; apply in_or_app; left; right; left; reflexivity).
assert (CAP32 : 32 <= cap) by (destruct BK as (_ & _ & _ & (X & _) & _); unfold ts0 in X; cbn [t_pbs] in X; rewrite Epbs in X; unfold pb_capA in X; cbn [nth snd] in X; exact X).
blk_factsA A4L HIx HP pb 16 Hpal Hplo Hphi Himg_p.
blk_factsA A4L HIx HP buf cap Hbal Hblo Hbhi Himg_b.
pose proof (blk_granA HIx _ _ _ _ _ _ _ pb 16 0 HP INpb ltac:(lia) ltac:(lia)) as SHP0.
replace (pb / 8 + 0 + A_SB) with (pb / 8 + 2147450880) in SHP0 by (unfold A_SB; lia).
pose proof (blk_granA HIx _ _ _ _ _ _ _ buf cap 0 HP INbuf ltac:(lia) ltac:(lia)) as SHB0.
replace (buf / 8 + 0 + A_SB) with (buf / 8 + 2147450880) in SHB0 by (unfold A_SB; lia).
pose proof (rw_cells_bytes_at' _ _ _ _ BUFC) as BUFB. cbn [cells_bytes cbytes] in BUFB. rewrite app_nil_r in BUFB.
assert (Ech : exists ch tl, pre ++ [Z_to_bv 8 0] ++ post = ch :: tl) by (destruct pre as [|c' s']; cbn; eauto).
destruct Ech as (ch & tl & Ech). rewrite Ech in BUFB.
pose proof (payload_byteA m buf (ch :: tl) 0 ch BUFB eq_refl ltac:(lia)) as RDB. rewrite Z.add_0_r in RDB.
pose proof (bv_unsigned_in_range 8 ch) as CHR; unfold bv_modulus in CHR; cbn in CHR.
unfold APE_BREAK, APE_REDO, APE_OUT, APE_ERRMEM, APE_ERRST, APE_JTAB in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
assert (cs_tk_L : csep tk 72 bse (Z.of_nat 32)) by (unfold csep; clear - Hdtq HbseR; lia).
assert (cs_L_tk : csep bse 32 tk (Z.of_nat 72)) by (unfold csep; clear - Hdtq HbseR; lia).
assert (cs_T3_T : csep (tk / 8 + 2147450883) 1 tk (Z.of_nat 72)) by (unfold csep; clear - SEPT3t; lia).
assert (cs_T3_L : csep (tk / 8 + 2147450883) 1 bse (Z.of_nat 32)) by (unfold csep; clear - SEPT3q HbseR; lia).
assert (cs_Q0_T : csep (bse / 8 + 2147450880) 1 tk (Z.of_nat 72)) by (unfold csep; clear - SEPQ0t; lia).
clear Hdtq SEPQ0c SEPQ0q SEPQ0t SEPT3c SEPT3q SEPT3t.
pose proof (munch_refl [(bse, bse + 32)] m) as MU.
stash Himg_t. stash Himg_q. stash Himg_p. stash Himg_b. stash Knext. stash Kredo. stash INV0. stash BUFC. stash BUFB. stash PBK.
clear REST LV OBJ HPR BUD GAP SAVED FSH STR ERR SBin TSK.
reenterA asegs A4L HIx asegs_wx HP.
step.
asan_rechkA.
step.
step.
asan_chkM 1.
step.
asan_chkA.
step.
change (zxb ch) with (Z_to_bv 64 (bv_unsigned ch)).

lazymatch goal with |- evt _ _ (MS ?R ?FF _ ?fcc None ?mm ?rom) =>
assert (NEXTJ : forall a2v a3v, evt asegs (AJ5e A4L HIx A T md) (MS (bvmap_set 12 a2v (bvmap_set 13 a3v R)) FF (Z_to_bv 64 0x94e5c) fcc None mm rom)) end.
{ intros a2v a3v. evt_done5. unstash Knext. apply Knext. }
step.
step.
destruct (Z.eq_dec (bv_unsigned ch) 45) as [E45 | N45].
2:{ if_truex. apply NEXTJ. }
if_falsex.
step.
step.
destruct (Z_lt_dec 1 (co - co0)) as [G1 | L1].
{ if_truex. apply NEXTJ. }
if_falsex.
step.
change (zxb cb) with (Z_to_bv 64 (bv_unsigned cb)).
step.
step.
step.
rewrite (unsigned_lit (bv_unsigned cb)) by lia.
pose proof (OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.Bytes.lor_lt_pow2 (bv_unsigned cb) 32 8 ltac:(lia) ltac:(lia)) as X32.
destruct (Z.eq_dec (Z.lor (bv_unsigned cb) 32) 105) as [E105 | N105].
2:{ if_truex. apply NEXTJ. }
if_falsex. clear NEXTJ.

asan_rechkA.
step.
asan_rechkM 1.
step.
norm_sx32.
step.
rewrite (unsigned_lit (Z.of_nat depth)) by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32.
step.
replace (q + Z.of_nat depth * 32) with bse by lia.
asan_chkA.
step.
stepz.
unstash INV0. unstash PBK.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, Lc : rw_cells asegs mc bse _ |- _ =>
pose proof MUc as MUc'; pose proof Lc as Lc'; rewrite Hbse in MUc', Lc';
destruct (PE_INV_A_lvl_write HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m mc md A B ts0 cb nb pj sv errv l ST_inf (tl_ss l) CNone false CNone STC INV0 Hl MUc' WMc MIc TOKc
ltac:(unfold srec_cells; cbn [tl_st tl_ss tl_cur tl_name]; exact Lc') Hmode ltac:(rewrite Ess; reflexivity) ltac:(unfold ST_inf; lia) SS26
(or_introl eq_refl) ltac:(rewrite Hst; reflexivity)) as [INV1 PBK1];
clear MUc' Lc' MUc WMc; pose proof (munch_refl [(tk, tk + 72)] mc) as MUt; pose proof (wmono_refl asegs mc) as WMt
end end.
set (ts1 := ts_lvl ts0 (TL ST_inf (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) in *.
assert (PBKa : PBOKat m ts0 (t_co ts0 + (kP - co))) by (cbn [t_co ts0]; replace (co + (kP - co)) with kP by lia; exact PBK).
pose proof (PBK1 (kP - co) PBKa) as PBK1'. unfold PBOK in PBK1'. cbn [t_co ts1 ts_lvl ts0] in PBK1'. replace (co + (kP - co)) with kP in PBK1' by lia.
clear PBK1 PBKa PBK INV0.
step.
asan_chkA.
stepz.
step.
step. step.
step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc2 _) =>
lazymatch goal with MUc : munch _ _ mc2, WMc : wmono asegs _ mc2, MIc : mem_inv asegs mc2, TOKc : rw_cells asegs mc2 tk _ |- _ =>
evt_done5;
destruct (PE_INV_A_tokw1 HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo _ mc2 md A B ts1
cb nb pj sv errv co (TS isd (Z_to_bv 64 0) (Z_to_bv 64 co) err ucs high quote) STC INV1 MUc WMc MIc TOKc ltac:(cbn [pf_len]; lia) eq_refl) as [INV2 PBT2]
end end.
unstash Kredo. eapply (Kredo _ _ _ _ _ _ _ _ INV2 (PBT2 _ PBK1')).
Qed.

Lemma PE_INV_A_pbw : forall pf pa q LB0 LM FRS payload me lo m mc md A B ts cb nb pj sv errv W,
PE_STATIC_A HIx pf pa lo ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
munch W m mc -> wmono asegs m mc -> mem_inv asegs mc ->
Forall (fun iv => exists a n, In (a, n) (t_pbs ts) /\ a <= fst iv /\ snd iv <= a + n) W ->
pbuf asegs mc (t_pbs ts) (t_pb ts) ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo mc md A B ts cb nb pj sv errv.
Proof.
intros pf pa q LB0 LM FRS payload me lo m mc md A B ts cb nb pj sv errv W STC [CORE REST] MU WM MI HW PBc.
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof (proj1 REST) as HP.
assert (HWL : Forall (fun iv => exists a n, In (a, n) (pe_blocksA pf q LB0 ts ++ LM) /\ a <= fst iv /\ snd iv <= a + n) W).
{ eapply Forall_impl; [| exact HW]. intros iv (a & n & Hin & H1 & H2). exists a, n. split; [| lia].
apply in_or_app; left. unfold pe_blocksA, tstate_blocks. apply in_or_app; left. apply in_or_app; left. exact Hin. }
assert (INtk : In (pf_tk pf, 72) (pe_blocksA pf q LB0 ts ++ LM)) by (unfold pe_blocksA; apply in_or_app; left; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * pf_mxd pf) (pe_blocksA pf q LB0 ts ++ LM)) by (unfold pe_blocksA; apply in_or_app; left; apply in_or_app; right; right; left; reflexivity).
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND. unfold pe_blocksA in ND. rewrite <- app_assoc in ND.
assert (AG : agree_on asegs [(pf_tk pf, 72); (q, 32 * pf_mxd pf)] m mc).
{ eapply agree_of_munch; [exact MU | exact WM |]. intros a0 n0 Hin0.
assert (X : In (a0, n0) (pe_blocksA pf q LB0 ts ++ LM) /\ forall a n, In (a, n) (t_pbs ts) -> a <> a0).
{ destruct Hin0 as [E | [E | []]]; injection E as <- <-.
- split; [exact INtk|]. intros a n Hin ->. refine (nodup_app_ne _ _ _ _ _ _ ND _ _ eq_refl); [unfold tstate_blocks; apply in_or_app; left; exact Hin | left; reflexivity].
- split; [exact INq|]. intros a n Hin ->. refine (nodup_app_ne _ _ _ _ _ _ ND _ _ eq_refl); [unfold tstate_blocks; apply in_or_app; left; exact Hin | right; left; reflexivity]. }
destruct X as [Hin0L Hne].
clear - HP HW Hin0L Hne. induction W as [|[lo' hi'] W IH]; [exact I|].
apply Forall_cons_iff in HW as [(a & n & Hin & H1 & H2) HW]. cbn [disjoint_from fst snd] in *. split; [| apply IH; exact HW].
assert (HinL : In (a, n) (pe_blocksA pf q LB0 ts ++ LM)) by (apply in_or_app; left; unfold pe_blocksA, tstate_blocks; apply in_or_app; left; apply in_or_app; left; exact Hin).
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ a n a0 n0 HP HinL Hin0L (Hne a n Hin)) as Hd. lia. }
split.
- split; [exact LEN32|]. split; [exact D32|]. split; [exact CO|]. split; [exact CHOFF|].
split. { eapply rw_cells_agree; [exact TOK | exact AG |]. exists (pf_tk pf), 72. split; [left; reflexivity|]. unfold tok_cells_g. cbn. lia. }
split; [exact PBc|]. split; [exact Hpb|]. split.
+ intros j l Hl. pose proof (nth_error_Some_length Hl) as Hj.
eapply rw_cells_agree; [exact (TSK j l Hl) | exact AG |]. exists q, (32 * pf_mxd pf). split; [right; left; reflexivity|]. rewrite srec_cells_size. cbn [Z.of_nat]. lia.
+ eapply (pe_frameA_blkwrite HIx); [exact STC | exact HP | exact HWL | exact FR | exact MU | exact WM].
- eapply (PE_REST_A_private_write HIx GA GA_outside); [exact STC | exact REST | exact MU | exact WM | exact MI |].
eapply Forall_impl; [| exact HW]. intros iv H. right; right; left. exact H.
Qed.

Definition trimcA (c : Z) : bool := (c =? 43) || (c =? 45) || (c =? 69) || (c =? 101).
Lemma trim_testA : forall c, 43 <= c <= 101 ->
bv_eqb (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (288230376218820613 ≫ (bv_unsigned (Z_to_bv 64 (c + -43)) mod 64)))) 1)) (Z_to_bv 64 0) = negb (trimcA c).
Proof. intros c Rc. enum_from c 43%Z 59%nat; vm_compute; reflexivity. Qed.

Lemma last_skipn1A {X} (l : list X) c rest : nth_error l (length l - 1) = Some c ->
firstn 1 (skipn (length l - 1) (l ++ rest)) = [c].
Proof.
intros H. pose proof (@nth_error_split _ l (length l - 1) c H) as (l1 & l2 & E & L1).
rewrite E at 2. rewrite <- app_assoc, skipn_app, <- L1, skipn_all, Nat.sub_diag. cbn. reflexivity.
Qed.
Lemma after_lastA {X} (l : list X) rest : (1 <= length l)%nat ->
skipn 1 (skipn (length l - 1) (l ++ rest)) = rest.
Proof.
intros H. rewrite skipn_skipn. replace (1 + (length l - 1))%nat with (length l) by lia.
rewrite skipn_app, skipn_all, Nat.sub_diag. reflexivity.
Qed.

Lemma num_trim_A :
forall (k : nat) (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (buf bpos cap : Z) (pre post : list byte)
(x1 gp t0 t1 t2 a1 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
t_pbs ts = [(t_pb ts, PB_SZ); (buf, cap)] -> Z.of_nat (length pre) = bpos ->
pbuf_core asegs m (t_pb ts) buf bpos cap (pre ++ [Z_to_bv 8 0] ++ post) ->
2 <= bpos -> (length pre <= k)%nat ->
(forall m' a0' a1' a2' a3' a4',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md A B ts cb nb pj sv errv ->
PBOKat m' ts bpos ->
AJ5 A4L HIx A T md
(Q1Y6.Mq2.pe_msE pf pa 0x95250 x1 gp t0 t1 t2 a0' a1' a2' a3' a4' a5 a6 a7 s3 s4 s5 s6 s7 (Z_to_bv 64 (pa_F pa)) s10 (Z_to_bv 64 (pf_tk pf / 8 + 2147450881)) t3 t4 t5 t6 F fc m')) ->
AJ5 A4L HIx A T md
(Q1Y6.Mq2.pe_msE pf pa 0x9517c x1 gp t0 t1 t2 (Z_to_bv 64 (t_pb ts)) a1 (Z_to_bv 64 bpos) a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 (Z_to_bv 64 (pa_F pa)) s10 (Z_to_bv 64 (pf_tk pf / 8 + 2147450881)) t3 t4 t5 t6 F fc m).
Proof.
induction k as [|k IH]; intros until fc; intros STC INV Epbs Lpre PCORE Hb2 Hk Kdone.
{ exfalso. cbn in Hk. lia. }
pose proof INV as INV0.
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
destruct INV as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof REST as (HP & _).
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
unfold pe_frameA in FR. destruct FR as (SLOTS & _). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS.
unfold Q1Y6.Mq2.pe_msE in *.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
set (PF := PEF tk oldl newl len lenr sb spf pmd mxd fl) in *. set (PA := PEFA sp0 Ff oldloc newloc bsl dsl) in *.
assert (INtk : In (tk, 72) (pe_blocksA PF q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INpb : In (pb, PB_SZ) (pe_blocksA PF q LB0 ts0)) by (unfold pe_blocksA, tstate_blocks, ts0; cbn [t_pbs]; rewrite Epbs; apply in_or_app; left; left; reflexivity).
assert (INbuf : In (buf, cap) (pe_blocksA PF q LB0 ts0)) by (unfold pe_blocksA, tstate_blocks, ts0; cbn [t_pbs]; rewrite Epbs; apply in_or_app; left; right; left; reflexivity).
assert (PBK0 : PBOKat m ts0 bpos) by (exists buf, bpos, cap, pre, post; split; [exact Epbs | split; [exact Lpre | split; [exact PCORE | lia]]]).
destruct PCORE as (Hbp & Hcap & Hlen & PBC & BUFC).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t.
blk_factsA A4L HIx HP pb 16 Hpal Hplo Hphi Himg_p.
blk_factsA A4L HIx HP buf cap Hbal Hblo Hbhi Himg_b.
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND.
assert (Hpb_buf : pb <> buf).
{ pose proof ND as ND'. unfold pe_blocksA, tstate_blocks, ts0 in ND'. cbn [t_pbs] in ND'. rewrite Epbs in ND'. cbn [app map blk_addr fst] in ND'.
apply NoDup_cons_iff in ND' as [NI _]. intros E. apply NI. left. symmetry. exact E. }
assert (Hbuf_tk : buf <> tk).
{ pose proof ND as ND'. unfold pe_blocksA in ND'. rewrite <- app_assoc in ND'.
refine (nodup_app_ne _ _ _ _ _ _ ND' _ _); [unfold tstate_blocks, ts0; cbn [t_pbs]; rewrite Epbs; apply in_or_app; left; right; left; reflexivity | left; reflexivity]. }
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ pb 16 buf cap HP (in_or_app _ LM _ (or_introl INpb)) (in_or_app _ LM _ (or_introl INbuf)) Hpb_buf) as Dpbbuf.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ buf cap tk 72 HP (in_or_app _ LM _ (or_introl INbuf)) (in_or_app _ LM _ (or_introl INtk)) Hbuf_tk) as Dbuftk.
pose proof (shadow_blk_apart HIx _ _ _ _ _ _ _ buf cap (tk + 8) 1 HP (in_or_app _ LM _ (or_introl INbuf)) ltac:(lia) ltac:(pose proof alloc_ceiling_range; lia) ltac:(lia)) as DSBT1.
pose proof (shadow_blk_apart HIx _ _ _ _ _ _ _ buf cap (pb + 8) 1 HP (in_or_app _ LM _ (or_introl INbuf)) ltac:(lia) ltac:(pose proof alloc_ceiling_range; lia) ltac:(lia)) as DSBP1.
unfold shA in DSBT1, DSBP1. rewrite (div8_add tk 8) in DSBT1 by (clear - Htal; Z.div_mod_to_equations; lia). rewrite (div8_add pb 8) in DSBP1 by (clear - Hpal; Z.div_mod_to_equations; lia). change (8 / 8) with 1 in DSBT1, DSBP1.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 1 HP INtk ltac:(lia)) as SHT1.
replace (tk / 8 + 1 + A_SB) with (tk / 8 + 2147450881) in SHT1 by (unfold A_SB; lia).
pose proof (blk_granA HIx _ _ _ _ _ _ _ pb 16 0 HP INpb ltac:(lia) ltac:(lia)) as SHP0.
replace (pb / 8 + 0 + A_SB) with (pb / 8 + 2147450880) in SHP0 by (unfold A_SB; lia).
pose proof (blk_granA HIx _ _ _ _ _ _ _ pb 16 1 HP INpb ltac:(lia) ltac:(lia)) as SHP1.
replace (pb / 8 + 1 + A_SB) with (pb / 8 + 2147450881) in SHP1 by (unfold A_SB; lia).
destruct (payload_shadow_of_blk HIx _ _ _ _ _ _ _ buf cap (buf + bpos + -1) HP INbuf ltac:(lia)) as (v1 & SHL & Hv1).
unfold A_SB in SHL.
rewrite !length_app in Hlen. cbn [length] in Hlen.
destruct (nth_error pre (length pre - 1)) as [cl|] eqn:Hcl; [| apply nth_error_None in Hcl; lia].
pose proof (rw_cells_bytes_at' _ _ _ _ BUFC) as BUFB. cbn [cells_bytes cbytes] in BUFB. rewrite app_nil_r in BUFB.
pose proof (payload_byteA m buf _ (bpos + -1) cl BUFB ltac:(rewrite nth_error_app1 by lia; replace (Z.to_nat (bpos + -1)) with (length pre - 1)%nat by lia; exact Hcl) ltac:(lia)) as RDL.
replace (buf + (bpos + -1)) with (buf + bpos + -1) in RDL by lia.
pose proof (bv_unsigned_in_range 8 cl) as CLR; unfold bv_modulus in CLR; cbn in CLR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(buf, buf + cap); (pb, pb + 16)] m) as MU.
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8, A_SB in *.
stash Himg_t. stash Himg_p. stash Himg_b. stash IH. stash Kdone. stash INV0. stash REST. stash ND. stash PB. stash TSK. stash BUFB. stash PBK0.
reenterA asegs A4L HIx asegs_wx HP.
asan_chkA.
step.
step.
step.
step. step.
sh_norm.

lazymatch goal with |- evt _ _ (MS ?R ?FF _ ?fcc None ?mm ?rom) =>
assert (JOIN1 : forall a2y a3y, evt asegs (AJ5e A4L HIx A T md) (MS (bvmap_set 12 a2y (bvmap_set 13 a3y R)) FF (Z_to_bv 64 0x951ac) fcc None mm rom)) end.
2:{ destruct Hv1 as [-> | [Hv8 Hvlt]].
- step. rewrite ?sxb_zero. step. if_false. apply JOIN1.
- step. rewrite (sxb_small v1) by lia. step. if_truex.
step.
rewrite (unsigned_lit (buf + bpos + -1)) by lia. rewrite (land7_mod8 (buf + bpos + -1)) by lia.
pose proof (Z.mod_pos_bound (buf + bpos + -1) 8 ltac:(lia)) as R8. remember ((buf + bpos + -1) mod 8) as r8 eqn:Er8 in *.
step.
if_truex. apply JOIN1. }
intros a2y a3y.

lazymatch goal with |- evt _ _ (MS ?R ?FF _ ?fcc None ?mm ?rom) =>
assert (DONEJ : forall a2v a3v, evt asegs (AJ5e A4L HIx A T md) (MS (bvmap_set 12 a2v (bvmap_set 13 a3v R)) FF (Z_to_bv 64 0x95250) fcc None mm rom)) end.
{ intros a2v a3v. evt_done5. unstash Kdone. unstash INV0. unstash PBK0. eapply Kdone; [exact INV0 | exact PBK0]. }
step.
change (zxb cl) with (Z_to_bv 64 (bv_unsigned cl)).
step. step.
step.
destruct (Z_lt_dec (bv_unsigned cl) 43) as [LT43 | GE43].
{ replace (Z_to_bv 64 (bv_unsigned cl + -43)) with (Z_to_bv 64 (bv_unsigned cl + -43 + 2^64)).
2:{ apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
rewrite <- (Z_mod_plus_full (bv_unsigned cl + -43) 1 (2^64)). f_equal. }
if_truex. apply DONEJ. }
destruct (Z_lt_dec 101 (bv_unsigned cl)) as [GT101 | LE101].
{ if_truex. apply DONEJ. }
if_falsex.
do 7 step.
step.
rewrite (trim_testA (bv_unsigned cl) ltac:(lia)).
destruct (trimcA (bv_unsigned cl)) eqn:TC; cbn [negb]; cbv iota.
2:{ apply DONEJ. }
clear DONEJ.

lazymatch goal with |- evt _ _ (MS ?R ?FF _ ?fcc None ?mm ?rom) =>
assert (JOIN2 : forall a1y a2z, evt asegs (AJ5e A4L HIx A T md) (MS (bvmap_set 11 a1y (bvmap_set 12 a2z R)) FF (Z_to_bv 64 0x951e4) fcc None mm rom)) end.
2:{ destruct Hv1 as [-> | [Hv8 Hvlt]].
- step. rewrite ?sxb_zero. step. if_false. apply JOIN2.
- step. rewrite (sxb_small v1) by lia. step. if_truex.
step.
rewrite (unsigned_lit (buf + bpos + -1)) by lia. rewrite (land7_mod8 (buf + bpos + -1)) by lia.
pose proof (Z.mod_pos_bound (buf + bpos + -1) 8 ltac:(lia)) as R8. remember ((buf + bpos + -1) mod 8) as r8 eqn:Er8 in *.
step.
if_truex. apply JOIN2. }
intros a1y a2z. clear SHL Hv1 RDL.

destruct (rw_cells_CB_cut asegs _ _ _ _ (length pre - 1) BUFC ltac:(lia)) as [PB0 PB1].
destruct (rw_cells_CB_cut asegs _ _ _ _ 1 PB1 ltac:(lia)) as [PBZ PB2]. clear BUFC PB1.
replace (buf + Z.of_nat (length pre - 1) + Z.of_nat 1) with (buf + Z.of_nat (length pre)) in PB2 by lia.
rewrite (last_skipn1A pre cl ([Z_to_bv 8 0] ++ post) Hcl) in PBZ.
rewrite (after_lastA pre ([Z_to_bv 8 0] ++ post)) in PB2 by lia.
replace (buf + Z.of_nat (length pre - 1)) with (buf + bpos + -1) in PBZ by lia.
stepz.
asan_rechkM 1.
step.
step.
asan_chkA.
step.
norm_sx32.
step.
norm_w32.
step.
stepz.
unstash INV0.
set (pre' := firstn (length pre - 1) pre).
assert (Lpre' : length pre' = (length pre - 1)%nat) by (unfold pre'; rewrite length_firstn; lia).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
assert (PC1 : pbuf_core asegs m1 pb buf (bpos + -1) cap (pre' ++ [Z_to_bv 8 0] ++ (Z_to_bv 8 0 :: post))) end.
{ split; [lia|]. split; [lia|]. split; [rewrite !length_app, Lpre'; cbn [length]; lia|]. split.
- match goal with H : rw_cells asegs _ pb _ |- _ => exact H end.
- match goal with Hz : rw_cells asegs _ (buf + bpos + -1) [C1 _] |- _ => rename Hz into PBZ1 end.
match goal with H0 : rw_cells asegs _ buf [CB (length pre - 1) _] |- _ => rename H0 into PB01 end.
match goal with H2 : rw_cells asegs _ (buf + Z.of_nat (length pre)) _ |- _ => rename H2 into PB21 end.
apply (rw_cells_recast asegs _ _ _ [CB 1 [Z_to_bv 8 0]]) in PBZ1; [| cbn; auto | reflexivity | reflexivity].
replace (buf + bpos + -1) with (buf + Z.of_nat (length pre - 1)) in PBZ1 by lia.
pose proof (rw_cells_CB_join asegs _ _ _ _ _ _ PB01 PBZ1) as J1.
replace (buf + Z.of_nat (length pre)) with (buf + Z.of_nat (length pre - 1 + 1)) in PB21 by lia.
pose proof (rw_cells_CB_join asegs _ _ _ _ _ _ J1 PB21) as J2.
replace (length pre - 1 + 1 + (Z.to_nat cap - (length pre - 1) - 1))%nat with (Z.to_nat cap) in J2 by lia.
rewrite firstn_app in J2. replace (length pre - 1 - length pre)%nat with 0%nat in J2 by lia. cbn [firstn] in J2.
rewrite app_nil_r in J2. fold pre' in J2. rewrite <- !app_assoc in J2. cbn [app] in J2 |- *. exact J2. }
assert (HWp : Forall (fun iv : Z * Z => exists a n, In (a, n) (t_pbs ts0) /\ a <= fst iv /\ snd iv <= a + n) [(buf, buf + cap); (pb, pb + 16)]).
{ cbn [t_pbs ts0]. rewrite Epbs. apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]; cbn [fst snd].
- exists buf, cap. split; [right; left; reflexivity | lia].
- exists pb, 16. split; [left; reflexivity | lia]. }
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc |- _ =>
pose proof (PE_INV_A_pbw PF PA q LB0 LM FRS payload me lo m mc md A B ts0 cb nb pj sv errv _ STC INV0 MUc WMc MIc HWp
ltac:(exists buf, (bpos + -1), cap, pre', (Z_to_bv 8 0 :: post); split; [exact Epbs | split; [lia | exact PC1]])) as INV1
end end.
step.
destruct (Z_lt_dec 2 bpos) as [MORE | DONE].
- if_truex. evt_done5. unstash IH. unstash Kdone.
eapply (IH PF PA q LB0 LM FRS payload me lo _ md A B ts0 cb nb pj sv errv T buf (bpos + -1) cap pre' (Z_to_bv 8 0 :: post));
[exact STC | exact INV1 | exact Epbs | lia | exact PC1 | lia | lia |].
intros m' a0' a1' a2' a3' a4' INV' PBK'. eapply Kdone; [exact INV' | eapply PBOKat_weaken; [| exact PBK']; lia].
- if_falsex.
step.
evt_done5. unstash Kdone.
eapply Kdone; [exact INV1 |].
exists buf, (bpos + -1), cap, pre', (Z_to_bv 8 0 :: post). split; [exact Epbs | split; [lia | split; [exact PC1 | lia]]].
Qed.

Lemma num_td_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet)
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 s4 s5 s6 s7 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
AJ5 A4L HIx A T md
(Q1Y6.Mq2.pe_msE pf pa 0x95260 x1 gp t0 t1 t2 (sx32 (ts_isd (t_x ts))) a1 a2 a3 (Z_to_bv 64 (pf_tk pf + 8)) a5 a6 (Z_to_bv 64 (pf_tk pf + 24)) (Z_to_bv 64 (pf_tk pf / 8 + 2147450883))
s4 s5 s6 s7 (Z_to_bv 64 (pa_F pa)) s10 s11 t3 t4 t5 t6 F fc m) ->
AJ5 A4L HIx A T md
(Q1Y6.Mq2.pe_msE pf pa 0x95250 x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 (Z_to_bv 64 (pf_tk pf + 24)) (Z_to_bv 64 (pf_tk pf / 8 + 2147450883))
s4 s5 s6 s7 (Z_to_bv 64 (pa_F pa)) s10 s11 t3 t4 t5 t6 F fc m).
Proof.
intros until fc. intros STC INV K.
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
destruct INV as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof REST as (HP & _).
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
unfold pe_frameA in FR. destruct FR as (SLOTS & _). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS.
unfold Q1Y6.Mq2.pe_msE in *.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 3 HP INtk ltac:(lia)) as SHT3.
replace (tk / 8 + 3 + A_SB) with (tk / 8 + 2147450883) in SHT3 by (unfold A_SB; lia).
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8, A_SB in *.
stash Himg_t. clear PB TSK REST.
reenterA asegs A4L HIx asegs_wx HP.
asan_rechkA.
step.
step.
evt_done5. apply K.
Qed.

Lemma num_pre_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP : Z)
(gp t1 t2 a0 a1 a2 a3 a5 a6 a7 s3 s6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> pf_fl pf = 0 ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
PBOKat m ts kP -> kP <= t_co ts ->
(forall m' a1' a2' a3',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md A B ts cb nb pj sv errv ->
PBOKat m' ts kP ->
AJ5 A4L HIx A T md
(Q1Y6.Mq2.pe_msE pf pa 0x95260 (Z_to_bv 64 (pf_tk pf / 8 + 2147450884)) gp (Z_to_bv 64 (pf_tk pf / 8 + 3)) t1 t2 (sx32 (ts_isd (t_x ts))) a1' a2' a3' (Z_to_bv 64 (pf_tk pf + 8)) a5 a6 (Z_to_bv 64 (pf_tk pf + 24))
(Z_to_bv 64 (pf_tk pf / 8 + 2147450883)) (Z_to_bv 64 (pf_tk pf + 20)) (Z_to_bv 64 (pf_tk pf / 8 + 2147450887)) s6 (Z_to_bv 64 (pf_tk pf + 32)) (Z_to_bv 64 (pa_F pa)) (Z_to_bv 64 (pf_tk pf + 56))
(Z_to_bv 64 (pf_tk pf / 8 + 2147450881)) (Z_to_bv 64 (pf_tk pf + 64)) (Z_to_bv 64 (pa_F pa + 64)) (Z_to_bv 64 (pf_tk pf / 8 + 2147450888)) (Z_to_bv 64 (pf_lenr pf)) F fc m')) ->
AJ5 A4L HIx A T md
(Q1Y6.Mq2.pe_msE pf pa 0x94e5c (Z_to_bv 64 (pf_tk pf / 8 + 2147450884)) gp (Z_to_bv 64 (pf_tk pf / 8 + 3)) t1 t2 a0 a1 a2 a3 (Z_to_bv 64 (pf_tk pf + 8)) a5 a6 a7
s3 (Z_to_bv 64 (pf_tk pf + 20)) (Z_to_bv 64 (pf_tk pf / 8 + 2147450887)) s6 (Z_to_bv 64 (pf_tk pf + 32)) (Z_to_bv 64 (pa_F pa)) (Z_to_bv 64 (pf_tk pf + 56))
(Z_to_bv 64 (pf_tk pf / 8 + 2147450881)) (Z_to_bv 64 (pf_tk pf + 64)) (Z_to_bv 64 (pa_F pa + 64)) (Z_to_bv 64 (pf_tk pf / 8 + 2147450888)) (Z_to_bv 64 (pf_lenr pf)) F fc m).
Proof.
intros until fc. intros STC FL0 INV PBK HkPc Kconv. pose proof INV as INV0.
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
destruct INV as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof REST as (HP & _).
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *. subst fl.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
unfold pe_frameA in FR. destruct FR as (SLOTS & _). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS.
unfold Q1Y6.Mq2.pe_msE in *.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
set (PF := PEF tk oldl newl len lenr sb spf pmd mxd 0) in *. set (PA := PEFA sp0 Ff oldloc newloc bsl dsl) in *.
assert (INtk : In (tk, 72) (pe_blocksA PF q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 1 HP INtk ltac:(lia)) as SHT1.
replace (tk / 8 + 1 + A_SB) with (tk / 8 + 2147450881) in SHT1 by (unfold A_SB; lia).
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 3 HP INtk ltac:(lia)) as SHT3.
replace (tk / 8 + 3 + A_SB) with (tk / 8 + 2147450883) in SHT3 by (unfold A_SB; lia).
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 8 HP INtk ltac:(lia)) as SHT8.
replace (tk / 8 + 8 + A_SB) with (tk / 8 + 2147450888) in SHT8 by (unfold A_SB; lia).
pose proof PBK as (buf & bpos & cap & pre & post & Epbs & Lpre & PCORE & Hbco). cbn [t_pbs t_pb t_co ts0] in Epbs, PCORE, Hbco. pose proof PCORE as (Hbp & Hcap & Hlen & PBC & BUFC).
assert (INpb : In (pb, PB_SZ) (pe_blocksA PF q LB0 ts0)) by (unfold pe_blocksA, tstate_blocks, ts0; cbn [t_pbs]; rewrite Epbs; apply in_or_app; left; left; reflexivity).
blk_factsA A4L HIx HP pb 16 Hpal Hplo Hphi Himg_p.
pose proof (blk_granA HIx _ _ _ _ _ _ _ pb 16 1 HP INpb ltac:(lia) ltac:(lia)) as SHP1.
replace (pb / 8 + 1 + A_SB) with (pb / 8 + 2147450881) in SHP1 by (unfold A_SB; lia).
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8, A_SB in *.
stash Himg_t. stash Himg_p. stash PCORE. stash BUFC. clear PB TSK REST.
reenterA asegs A4L HIx asegs_wx HP.
asan_rechkA.
step.
step.
step. step.
step.
lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with true by (vm_compute; reflexivity); cbv iota end.
step.
asan_rechkA.
step.
step.
lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with false by (vm_compute; reflexivity); cbv iota end.
step.
destruct (Z.eq_dec (bv_unsigned (sx32 isd)) 0) as [EI0 | NI0].
{ if_truex. evt_done5. eapply Kconv; [exact INV0 | exact PBK]. }
if_falsex.
asan_rechkA.
step.
step.
asan_chkA.
step.
norm_sx32.
step.
step.
unstash PCORE.
destruct (Z_lt_dec bpos 2) as [LT2 | GE2].
- if_truex. evt_done5.
eapply (num_td_A PF PA q LB0 LM FRS payload me lo m md A B ts0 cb nb pj sv errv T); [exact STC | exact INV0 |].
eapply Kconv; [exact INV0 | exact PBK].
- if_falsex. evt_done5.
eapply (num_trim_A (length pre) PF PA q LB0 LM FRS payload me lo m md A B ts0 cb nb pj sv errv T buf bpos cap pre post);
[exact STC | exact INV0 | exact Epbs | exact Lpre | exact PCORE | lia | lia |].
intros m' a0' a1' a2' a3' a4' INV' PBK'.
eapply (num_td_A PF PA q LB0 LM FRS payload me lo m' md A B ts0 cb nb pj sv errv T); [exact STC | exact INV' |].
eapply Kconv; [exact INV' |].
eapply PBOKat_weaken; [| exact PBK']. cbn [t_co ts0]. exact Hbco.
Qed.

Definition num_ffc (cb : byte) (fhd f1a f1b f2a f2c f2e : list byte) (endw n64 nu64 : word) : list cell :=
[CB 24 fhd; CB 8 f1a; C8 endw; CB 24 f1b; C1 cb; CB 79 f2a; C8 n64; CB 24 f2c; C8 nu64; CB 64 f2e].

Definition FSHN (sh4 : Z) : list Z :=
[0xf1; 0xf1; 0xf1; 0xf1; sh4; 0xf2; 0xf2; 0xf2; 0x01; 0xf2; 0xf8; 0xf2; 0xf8; 0xf2; 0xf8; 0xf2;
0xf8; 0xf2; 0; 0xf2; 0xf2; 0xf2; 0; 0xf3; 0xf3; 0xf3; 0xf3; 0xf3; 0; 0; 0; 0].

Lemma split3_bytes : forall (l : list byte) (a b : nat), l = firstn a l ++ firstn b (skipn a l) ++ skipn (a + b) l.
Proof. intros l a b. rewrite <- (firstn_skipn a l) at 1. f_equal. rewrite <- (firstn_skipn b (skipn a l)) at 1. f_equal. rewrite skipn_skipn. f_equal. lia. Qed.

Lemma num_ffc_open : forall (m : word -> option byte) (F : Z) (cb : byte) (pj : pe_junkA),
rw_cells asegs m F (ff_cellsA cb pj) ->
exists f1a f1b f2a f2c f2e endw n64 nu64,
rw_cells asegs m F (num_ffc cb (pj_fhd pj) f1a f1b f2a f2c f2e endw n64 nu64) /\
length f1a = 8%nat /\ length f1b = 24%nat /\ length f2a = 79%nat /\ length f2c = 24%nat /\ length f2e = 64%nat.
Proof.
intros m F cb pj FF. unfold ff_cellsA in FF.
pose proof FF as [[Hwf _] _]. cbn [cells_wf cell_wf] in Hwf. destruct Hwf as (Lh & L1 & _ & L2 & _).
set (f1 := pj_f1 pj) in *. set (f2 := pj_f2 pj) in *.
assert (E1 : f1 = firstn 8 f1 ++ firstn 8 (skipn 8 f1) ++ skipn 16 f1) by (exact (split3_bytes f1 8 8)).
assert (E2 : f2 = firstn 79 f2 ++ firstn 8 (skipn 79 f2) ++ firstn 24 (skipn 87 f2) ++ firstn 8 (skipn 111 f2) ++ skipn 119 f2).
{ rewrite (split3_bytes f2 79 8) at 1. f_equal. f_equal. change (79 + 8)%nat with 87%nat.
rewrite (split3_bytes (skipn 87 f2) 24 8) at 1. rewrite !skipn_skipn. reflexivity. }
assert (La : length (firstn 8 f1) = 8%nat) by (rewrite length_firstn; lia).
assert (Lm : length (firstn 8 (skipn 8 f1)) = 8%nat) by (rewrite length_firstn, length_skipn; lia).
assert (Lb : length (skipn 16 f1) = 24%nat) by (rewrite length_skipn; lia).
assert (Lc : length (firstn 79 f2) = 79%nat) by (rewrite length_firstn; lia).
assert (Ln : length (firstn 8 (skipn 79 f2)) = 8%nat) by (rewrite length_firstn, length_skipn; lia).
assert (Ld : length (firstn 24 (skipn 87 f2)) = 24%nat) by (rewrite length_firstn, length_skipn; lia).
assert (Lu : length (firstn 8 (skipn 111 f2)) = 8%nat) by (rewrite length_firstn, length_skipn; lia).
assert (Le : length (skipn 119 f2) = 64%nat) by (rewrite length_skipn; lia).
set (a1 := firstn 8 f1) in *. set (a2 := firstn 8 (skipn 8 f1)) in *. set (a3 := skipn 16 f1) in *.
set (b1 := firstn 79 f2) in *. set (b2 := firstn 8 (skipn 79 f2)) in *. set (b3 := firstn 24 (skipn 87 f2)) in *. set (b4 := firstn 8 (skipn 111 f2)) in *. set (b5 := skipn 119 f2) in *.
exists a1, a3, b1, b3, b5, (le_bytes_to_word a2), (le_bytes_to_word b2), (le_bytes_to_word b4).
split; [| repeat split; assumption].
eapply rw_cells_recast; [exact FF | | |].
- unfold num_ffc. cbn [cells_wf cell_wf]. repeat split; assumption.
- unfold num_ffc. cbn [cells_bytes cbytes app]. rewrite !app_nil_r.
rewrite !QYZ0.Mq0.le8_lbw8A by assumption.
rewrite E1, E2. rewrite <- !app_assoc. reflexivity.
- reflexivity.
Qed.

Lemma num_ffc_close : forall (m : word -> option byte) (F : Z) (cb : byte) (pj : pe_junkA) (f1a f1b f2a f2c f2e : list byte) (endw n64 nu64 : word),
rw_cells asegs m F (num_ffc cb (pj_fhd pj) f1a f1b f2a f2c f2e endw n64 nu64) ->
rw_cells asegs m F (ff_cellsA cb (PEJA (pj_0 pj) (pj_8 pj) (pj_16 pj) (pj_obj pj) (pj_288 pj) (pj_304 pj) (pj_gap pj) (pj_fhd pj)
(f1a ++ le8 endw ++ f1b) (f2a ++ le8 n64 ++ f2c ++ le8 nu64 ++ f2e))).
Proof.
intros m F cb pj f1a f1b f2a f2c f2e endw n64 nu64 FF. unfold num_ffc in FF.
pose proof FF as [[Hwf _] _]. cbn [cells_wf cell_wf] in Hwf. destruct Hwf as (Lh & La & _ & Lb & _ & Lc & _ & Ld & _ & Le & _).
eapply rw_cells_recast; [exact FF | | |].
- unfold ff_cellsA. cbn [cells_wf cell_wf pj_fhd pj_f1 pj_f2]. rewrite !length_app, !length_le8. repeat split; lia.
- unfold ff_cellsA. cbn [cells_bytes cbytes app pj_fhd pj_f1 pj_f2]. rewrite !app_nil_r, <- !app_assoc. reflexivity.
- reflexivity.
Qed.

Definition NUM_INVX (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (sh4 : Z) : Prop :=
exists f1a f1b f2a f2c f2e endw n64 nu64,
PE_INV_AX HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts errv
(pe_frameAX m pf pa nb pj sv (num_ffc cb (pj_fhd pj) f1a f1b f2a f2c f2e endw n64 nu64) (ffsh_cells (FSHN sh4))).
Definition NUM_WINX (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (p : Z) (s : option jshape) (BS : list blk)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) : Prop :=
exists f1a f1b f2a f2c f2e endw n64 nu64,
PE_WINX HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts p s BS 1 errv
(pe_frameAX m pf pa nb pj sv (num_ffc cb (pj_fhd pj) f1a f1b f2a f2c f2e endw n64 nu64) (ffsh_cells (FSHN 0xf8))).

Lemma num_conv_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kB : nat)
(gp t1 t2 a1 a2 a3 a5 a6 s6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
BOK pf pa ts B kB ->
(forall m' a0' a1' a2',
NUM_INVX pf pa q LB0 LM FRS payload me lo m' md A B ts cb nb pj sv errv 0xf8 ->
(forall b, PBOKat m ts b -> PBOKat m' ts b) ->
AJ5 A4L HIx A T md
(Q1Y6.Mq2.pe_msE pf pa 0x95350 (Z_to_bv 64 (pf_tk pf / 8 + 2147450884)) gp (Z_to_bv 64 (pf_tk pf / 8 + 3)) t1 t2 a0' a1' a2' a3 (Z_to_bv 64 (pf_tk pf + 8)) a5 a6 (Z_to_bv 64 (pf_tk pf + 24))
(Z_to_bv 64 (pf_tk pf / 8 + 2147450883)) (Z_to_bv 64 (pf_tk pf + 20)) (Z_to_bv 64 (pf_tk pf / 8 + 2147450887)) s6 (Z_to_bv 64 (pf_tk pf + 32)) (Z_to_bv 64 (pa_F pa)) (Z_to_bv 64 (pf_tk pf + 56))
(Z_to_bv 64 (pf_tk pf / 8 + 2147450881)) (Z_to_bv 64 (pf_tk pf + 64)) (Z_to_bv 64 (pa_F pa + 64)) (Z_to_bv 64 (pf_tk pf / 8 + 2147450888)) (Z_to_bv 64 (pf_lenr pf)) F fc m')) ->
(forall m' buf cap a1' a2',
t_pbs ts = [(t_pb ts, PB_SZ); (buf, cap)] ->
NUM_INVX pf pa q LB0 LM FRS payload me lo m' md A B ts cb nb pj sv errv 0xf8 ->
(forall b, PBOKat m ts b -> PBOKat m' ts b) ->
AJ5 A4L HIx A T md
(Q1Y6.Mq2.pe_msE pf pa 0x952b0 (Z_to_bv 64 (pf_tk pf / 8 + 2147450884)) gp (Z_to_bv 64 (pf_tk pf / 8 + 3)) t1 t2 (Z_to_bv 64 buf) a1' a2' a3 (Z_to_bv 64 (pf_tk pf + 8)) a5 a6 (Z_to_bv 64 (pf_tk pf + 24))
(Z_to_bv 64 (pf_tk pf / 8 + 2147450883)) (Z_to_bv 64 (pf_tk pf + 20)) (Z_to_bv 64 (pf_tk pf / 8 + 2147450887)) s6 (Z_to_bv 64 (pf_tk pf + 32)) (Z_to_bv 64 (pa_F pa)) (Z_to_bv 64 (pf_tk pf + 56))
(Z_to_bv 64 (pf_tk pf / 8 + 2147450881)) (Z_to_bv 64 (pf_tk pf + 64)) (Z_to_bv 64 (pa_F pa + 64)) (Z_to_bv 64 (pf_tk pf / 8 + 2147450888)) (Z_to_bv 64 (pf_lenr pf)) F fc m')) ->
(forall m' a0' a1' a2',
NUM_INVX pf pa q LB0 LM FRS payload me lo m' md A B ts cb nb pj sv errv 0xf8 ->
(forall b, PBOKat m ts b -> PBOKat m' ts b) ->
AJ5 A4L HIx A T md
(Q1Y6.Mq2.pe_msE pf pa 0x952c8 (Z_to_bv 64 (pf_tk pf / 8 + 2147450884)) gp (Z_to_bv 64 (pf_tk pf / 8 + 3)) t1 t2 a0' a1' a2' a3 (Z_to_bv 64 (pf_tk pf + 8)) a5 a6 (Z_to_bv 64 (pf_tk pf + 24))
(Z_to_bv 64 (pf_tk pf / 8 + 2147450883)) (Z_to_bv 64 (pf_tk pf + 20)) (Z_to_bv 64 (pf_tk pf / 8 + 2147450887)) s6 (Z_to_bv 64 (pf_tk pf + 32)) (Z_to_bv 64 (pa_F pa)) (Z_to_bv 64 (pf_tk pf + 56))
(Z_to_bv 64 (pf_tk pf / 8 + 2147450881)) (Z_to_bv 64 (pf_tk pf + 64)) (Z_to_bv 64 (pa_F pa + 64)) (Z_to_bv 64 (pf_tk pf / 8 + 2147450888)) (Z_to_bv 64 (pf_lenr pf)) F fc m')) ->
AJ5 A4L HIx A T md
(Q1Y6.Mq2.pe_msE pf pa 0x95260 (Z_to_bv 64 (pf_tk pf / 8 + 2147450884)) gp (Z_to_bv 64 (pf_tk pf / 8 + 3)) t1 t2 (sx32 (ts_isd (t_x ts))) a1 a2 a3 (Z_to_bv 64 (pf_tk pf + 8)) a5 a6 (Z_to_bv 64 (pf_tk pf + 24))
(Z_to_bv 64 (pf_tk pf / 8 + 2147450883)) (Z_to_bv 64 (pf_tk pf + 20)) (Z_to_bv 64 (pf_tk pf / 8 + 2147450887)) s6 (Z_to_bv 64 (pf_tk pf + 32)) (Z_to_bv 64 (pa_F pa)) (Z_to_bv 64 (pf_tk pf + 56))
(Z_to_bv 64 (pf_tk pf / 8 + 2147450881)) (Z_to_bv 64 (pf_tk pf + 64)) (Z_to_bv 64 (pa_F pa + 64)) (Z_to_bv 64 (pf_tk pf / 8 + 2147450888)) (Z_to_bv 64 (pf_lenr pf)) F fc m).
Proof.
intros until fc. intros STC INV BK Kdbl Kp1 Ku0. pose proof INV as INV0.
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
destruct INV as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof REST as (HP & _).
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
pose proof FR as FR0. unfold pe_frameA in FR. destruct FR as (SLOTS & GAP & SAVED & FF & FSH).
unfold pe_slotsA in SLOTS. cbn zeta in SLOTS. unfold ffsh_cells, FSH0 in FSH. cbn [map] in FSH.
destruct (num_ffc_open m _ cb pj FF) as (f1a & f1b & f2a & f2c & f2e & endw & n64 & nu64 & FFX & _). unfold num_ffc in FFX. clear FF.
unfold Q1Y6.Mq2.pe_msE in *.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
set (PF := PEF tk oldl newl len lenr sb spf pmd mxd fl) in *. set (PA := PEFA sp0 Ff oldloc newloc bsl dsl) in *.
assert (INtk : In (tk, 72) (pe_blocksA PF q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 1 HP INtk ltac:(lia)) as SHT1.
replace (tk / 8 + 1 + A_SB) with (tk / 8 + 2147450881) in SHT1 by (unfold A_SB; lia).
destruct PB as (buf & bpos & cap & pre & post & Epbs & Lpre & CORE1). destruct CORE1 as (Hbp & Hcap & Hlen & PBC & BUFC).
assert (INpb : In (pb, PB_SZ) (pe_blocksA PF q LB0 ts0)) by (unfold pe_blocksA, tstate_blocks, ts0; cbn [t_pbs]; rewrite Epbs; apply in_or_app; left; left; reflexivity).
assert (INbuf : In (buf, cap) (pe_blocksA PF q LB0 ts0)) by (unfold pe_blocksA, tstate_blocks, ts0; cbn [t_pbs]; rewrite Epbs; apply in_or_app; left; right; left; reflexivity).
assert (CAP32 : 32 <= cap) by (destruct BK as (_ & _ & _ & (X & _) & _); unfold ts0 in X; cbn [t_pbs] in X; rewrite Epbs in X; unfold pb_capA in X; cbn [nth snd] in X; exact X).
blk_factsA A4L HIx HP pb 16 Hpal Hplo Hphi Himg_p.
blk_factsA A4L HIx HP buf cap Hbal Hblo Hbhi Himg_b.
pose proof (blk_granA HIx _ _ _ _ _ _ _ pb 16 0 HP INpb ltac:(lia) ltac:(lia)) as SHP0.
replace (pb / 8 + 0 + A_SB) with (pb / 8 + 2147450880) in SHP0 by (unfold A_SB; lia).
pose proof (blk_granA HIx _ _ _ _ _ _ _ buf cap 0 HP INbuf ltac:(lia) ltac:(lia)) as SHB0.
replace (buf / 8 + 0 + A_SB) with (buf / 8 + 2147450880) in SHB0 by (unfold A_SB; lia).
assert (Ech : exists ch tl, pre ++ [Z_to_bv 8 0] ++ post = ch :: tl) by (destruct pre as [|c' s']; cbn; eauto).
destruct Ech as (ch & tl & Ech). rewrite Ech in BUFC.
pose proof (bv_unsigned_in_range 8 ch) as CHR; unfold bv_modulus in CHR; cbn in CHR.

assert (INF : In (Ff, 2) ((Ff, 2) :: FRS)) by (left; reflexivity).
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP INF) as DSF. rewrite fr_size_2 in DSF. cbn [hl_sb A4L] in DSF.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(tk, tk + 72); (Ff, Ff + 248); (Ff / 8 + 2147450880, Ff / 8 + 2147450880 + 32)] m) as MU.
assert (HW : Forall (pe_wtfA PF PA) [(tk, tk + 72); (Ff, Ff + 248); (Ff / 8 + 2147450880, Ff / 8 + 2147450880 + 32)]).
{ apply Forall_cons; [left; cbn [fst snd pf_tk PF]; lia |]. apply Forall_cons; [right; right; left; cbn [fst snd pa_F PA]; lia |].
apply Forall_cons; [| apply Forall_nil]. right; right; right. cbn [fst snd pa_F PA]. unfold shA, A_SB. lia. }
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8, A_SB in *.
pose proof alloc_ceiling_range as ACR.
assert (GF0' : 0 <= Ff) by lia. assert (GFc' : Ff < alloc_ceiling) by lia.
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP INF (in_or_app _ LM _ (or_introl INtk))) as DFt. rewrite fr_size_2 in DFt.
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP INF (in_or_app _ LM _ (or_introl INpb))) as DFp. rewrite fr_size_2 in DFp.
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP INF (in_or_app _ LM _ (or_introl INbuf))) as DFb. rewrite fr_size_2 in DFb.
pose proof (shadow_blk_apart HIx _ _ _ _ _ _ _ _ _ Ff 32 HP (in_or_app _ LM _ (or_introl INtk)) GF0' GFc' ltac:(lia)) as DSt.
pose proof (shadow_blk_apart HIx _ _ _ _ _ _ _ _ _ Ff 32 HP (in_or_app _ LM _ (or_introl INpb)) GF0' GFc' ltac:(lia)) as DSp.
pose proof (shadow_blk_apart HIx _ _ _ _ _ _ _ _ _ Ff 32 HP (in_or_app _ LM _ (or_introl INbuf)) GF0' GFc' ltac:(lia)) as DSb.
unfold shA, A_SB in DSt, DSp, DSb.
stash Himg_t. stash Himg_p. stash Himg_b. stash Kdbl. stash Kp1. stash Ku0. stash INV0. stash FR0. stash GAP. stash SAVED. stash TSK. stash REST.
reenterA asegs A4L HIx asegs_wx HP.
stepz.
stepz.

unstash INV0. unstash FR0. unstash REST.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, FFc : rw_cells asegs mc Ff ?ffc, FSHc : rw_cells asegs mc (Ff / 8 + 2147450880) ?shc |- _ =>
assert (FRXc : pe_frameAX mc PF PA nb pj sv (num_ffc cb (pj_fhd pj) f1a f1b f2a f2c f2e endw n64 nu64) (ffsh_cells (FSHN 0xf8)))
by (eapply (pe_frameAX_write HIx PF PA q LB0 LM FRS B ts0 A m mc md lo nb pj sv); [exact STC | exact HP | exact (pe_frameAX_of_A _ _ _ _ _ _ _ FR0) | exact MUc | exact WMc | exact FFc | exact FSHc]);
destruct (PE_INV_AX_tokw HIx GA GA_outside PF PA q LB0 LM FRS payload me lo m mc md A B ts0 errv _ co (t_x ts0) _ _ STC (PE_INV_AX_of_A HIx GA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV0) MUc WMc MIc HW TOKc FRXc
ltac:(unfold PF; cbn [pf_len]; lia) eq_refl) as [INVX1 PBKX1]
end end.
assert (NX1 : NUM_INVX PF PA q LB0 LM FRS payload me lo _ md A B ts0 cb nb pj sv errv 0xf8) by (exists f1a, f1b, f2a, f2c, f2e, endw, n64, nu64; exact INVX1).
clear INVX1 FRXc INV0 FR0. stash NX1. stash PBKX1.
lazymatch goal with BUFCc : rw_cells asegs ?mc buf _ |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (rw_cells_bytes_at' _ _ _ _ BUFCc) as BUFB; cbn [cells_bytes cbytes] in BUFB; rewrite app_nil_r in BUFB;
pose proof (payload_byteA mc buf (ch :: tl) 0 ch BUFB eq_refl ltac:(lia)) as RDB; rewrite Z.add_0_r in RDB end.
step.
destruct (Z.eq_dec (bv_unsigned (sx32 isd)) 0) as [EI0 | NI0].
2:{ if_truex. evt_done5. unstash Kdbl. unstash NX1. unstash PBKX1. eapply Kdbl; [exact NX1 | exact PBKX1]. }
if_falsex.
asan_rechkA.
step.
asan_chkA.
step.
asan_chkA.
step.
change (zxb ch) with (Z_to_bv 64 (bv_unsigned ch)).
step.
step.
unstash NX1. unstash PBKX1.
destruct (Z.eq_dec (bv_unsigned ch) 45) as [E45 | N45].
- if_falsex. evt_done5. unstash Kp1. eapply (Kp1 _ buf cap); [exact Epbs | exact NX1 | exact PBKX1].
- if_truex. evt_done5. unstash Ku0. eapply Ku0; [exact NX1 | exact PBKX1].
Qed.

Lemma scoped_unpoisoned8_w : forall (m : word -> option byte) (F : Z) (k : nat) (w : list byte),
F mod 256 = 0 -> 0 <= F ->
bytes_at asegs m (F / 8 + A_SB + 8 * (Z.of_nat k / 8)) w -> length w = 8%nat ->
nth_error w (Z.to_nat (Z.of_nat k mod 8)) = Some (Z_to_bv 8 0) ->
unpoisoned asegs m A_SB (F + 8 * Z.of_nat k) 8.
Proof.
intros m F k w GF GF0 WB Lw Hn.
assert (Es : (F + 8 * Z.of_nat k) / 8 = F / 8 + Z.of_nat k) by (clear - GF; Z.div_mod_to_equations; lia).
assert (Ee : (F + 8 * Z.of_nat k + 8 - 1) / 8 = F / 8 + Z.of_nat k) by (clear - GF; Z.div_mod_to_equations; lia).
unfold unpoisoned. split; [lia|]. split; [intros g Hg; rewrite Es, Ee in Hg; lia|]. split.
- exists 0. split; [| left; reflexivity].
rewrite Ee. apply nth_error_split in Hn as (l1 & l2 & Ew & Ll1). rewrite Ew in WB.
apply (proj1 (bytes_at_app asegs _ _ _ _)) in WB as [_ WB]. change (Z_to_bv 8 0 :: l2) with ([Z_to_bv 8 0] ++ l2) in WB.
apply (proj1 (bytes_at_app asegs _ _ _ _)) in WB as [WB _]. rewrite Ll1 in WB.
replace (F / 8 + Z.of_nat k + A_SB) with (F / 8 + A_SB + 8 * (Z.of_nat k / 8) + Z.of_nat (Z.to_nat (Z.of_nat k mod 8))); [exact WB|].
rewrite Z2Nat.id by (apply Z.mod_pos_bound; lia). pose proof (Z.div_mod (Z.of_nat k) 8 ltac:(lia)). lia.
- intros w' Hw'. rewrite Es, Ee in Hw'. exists w. split; [exact Lw|].
replace (w' * 8) with (F / 8 + A_SB + 8 * (Z.of_nat k / 8)); [exact WB|].
unfold A_SB in *. clear - GF Hw'. Z.div_mod_to_equations. lia.
Qed.

Lemma num_unp : forall (m : word -> option byte) (pf : pe_fix) (pa : pe_fixA) (nb : word) (pj : pe_junkA) (sv : pe_saved) (ffc : list cell) (sh4 : Z) (k : nat),
(k = 18 \/ k = 22)%nat -> pa_F pa mod 256 = 0 -> 0 <= pa_F pa ->
pe_frameAX m pf pa nb pj sv ffc (ffsh_cells (FSHN sh4)) ->
unpoisoned asegs m A_SB (pa_F pa + 8 * Z.of_nat k) 8.
Proof.
intros m pf pa nb pj sv ffc sh4 k Hk GF GF0 (_ & _ & _ & _ & FSs).
unfold ffsh_cells, FSHN in FSs. cbn [map] in FSs.
match type of FSs with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?c11 :: ?c12 :: ?c13 :: ?c14 :: ?c15 :: ?d0 :: ?d1 :: ?d2 :: ?d3 :: ?d4 :: ?d5 :: ?d6 :: ?d7 :: ?rest) =>
change (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: c8 :: c9 :: c10 :: c11 :: c12 :: c13 :: c14 :: c15 :: d0 :: d1 :: d2 :: d3 :: d4 :: d5 :: d6 :: d7 :: rest)
with ([c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11; c12; c13; c14; c15] ++ ([d0; d1; d2; d3; d4; d5; d6; d7] ++ rest)) in FSs end.
apply (proj1 (rw_cells_app asegs _ _ _ _)) in FSs as [_ FSs]. apply (proj1 (rw_cells_app asegs _ _ _ _)) in FSs as [FSs _].
cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FSs. destruct FSs as [[_ WB] _]. cbn [cells_bytes cbytes app] in WB.
unfold shA in WB.
destruct Hk as [-> | ->].
- eapply (scoped_unpoisoned8_w m (pa_F pa) 18); [exact GF | exact GF0 | change (8 * (Z.of_nat 18 / 8)) with 16; exact WB | reflexivity | reflexivity].
- eapply (scoped_unpoisoned8_w m (pa_F pa) 22); [exact GF | exact GF0 | change (8 * (Z.of_nat 22 / 8)) with 16; exact WB | reflexivity | reflexivity].
Qed.

Lemma num_pint_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP buf cap : Z)
(x1 gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s6 t4 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo ->
NUM_INVX pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv 0xf8 ->
PBOKat m ts kP -> t_pbs ts = [(t_pb ts, PB_SZ); (buf, cap)] ->
Z.of_nat (length FRS) + 1 < 4096 ->
(forall m' md' A' errv' x1' gp' t0' t1' t2' a0' a1' a2' a3' a5' a6' a7' t4' t6',
NUM_INVX pf pa q LB0 LM FRS payload me lo m' md' A' B ts cb nb pj sv errv' 0xf8 -> PBOKat m' ts kP ->
AJ5 A4L HIx A' T md'
(Q1Y6.Mq2.pe_msE pf pa 0x954c0 x1' gp' t0' t1' t2' a0' a1' a2' a3' (Z_to_bv 64 (pf_tk pf + 8)) a5' a6' a7'
(Z_to_bv 64 (pf_tk pf / 8 + 2147450883)) (Z_to_bv 64 (pf_tk pf + 20)) (Z_to_bv 64 (pf_tk pf / 8 + 2147450887)) s6 (Z_to_bv 64 (pf_tk pf + 32)) (Z_to_bv 64 (pa_F pa)) (Z_to_bv 64 (pf_tk pf + 56))
(Z_to_bv 64 (pf_tk pf / 8 + 2147450881)) (Z_to_bv 64 (pf_tk pf + 64)) t4' (Z_to_bv 64 (pf_tk pf / 8 + 2147450888)) t6' F fc m')) ->
(forall m' md' A' errv' x1' gp' t0' t1' t2' a0' a1' a2' a3' a5' a6' a7' t4' t6',
NUM_INVX pf pa q LB0 LM FRS payload me lo m' md' A' B ts cb nb pj sv errv' 0xf8 -> PBOKat m' ts kP ->
AJ5 A4L HIx A' T md'
(Q1Y6.Mq2.pe_msE pf pa 0x952c8 x1' gp' t0' t1' t2' a0' a1' a2' a3' (Z_to_bv 64 (pf_tk pf + 8)) a5' a6' a7'
(Z_to_bv 64 (pf_tk pf / 8 + 2147450883)) (Z_to_bv 64 (pf_tk pf + 20)) (Z_to_bv 64 (pf_tk pf / 8 + 2147450887)) s6 (Z_to_bv 64 (pf_tk pf + 32)) (Z_to_bv 64 (pa_F pa)) (Z_to_bv 64 (pf_tk pf + 56))
(Z_to_bv 64 (pf_tk pf / 8 + 2147450881)) (Z_to_bv 64 (pf_tk pf + 64)) t4' (Z_to_bv 64 (pf_tk pf / 8 + 2147450888)) t6' F fc m')) ->
AJ5 A4L HIx A T md
(Q1Y6.Mq2.pe_msE pf pa 0x952b0 x1 gp t0 t1 t2 (Z_to_bv 64 buf) a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (pf_tk pf / 8 + 2147450883)) (Z_to_bv 64 (pf_tk pf + 20)) (Z_to_bv 64 (pf_tk pf / 8 + 2147450887)) s6 (Z_to_bv 64 (pf_tk pf + 32)) (Z_to_bv 64 (pa_F pa)) (Z_to_bv 64 (pf_tk pf + 56))
(Z_to_bv 64 (pf_tk pf / 8 + 2147450881)) (Z_to_bv 64 (pf_tk pf + 64)) t4 (Z_to_bv 64 (pf_tk pf / 8 + 2147450888)) t6 F fc m).
Proof.
intros until fc. intros STC NX PBK Epbs FRN Kok Kfail.
destruct NX as (f1a & f1b & f2a & f2c & f2e & endw & n64 & nu64 & INVX).
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
pose proof INVX as [CORE REST]. destruct CORE as (_ & _ & _ & _ & _ & _ & _ & _ & FRX). pose proof (proj1 REST) as HP.
pose proof (num_unp m pf pa nb pj sv _ _ 18%nat (or_introl eq_refl) GF ltac:(lia) FRX) as UNP. change (8 * Z.of_nat 18) with 144 in UNP.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
set (PF := PEF tk oldl newl len lenr sb spf pmd mxd fl) in *. set (PA := PEFA sp0 Ff oldloc newloc bsl dsl) in *.
pose proof FRX as (SLOTS & _). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS. cbn [pf_tk pf_spf pf_lenr pa_F pa_sp0 pa_oldloc pa_newloc PF PA] in SLOTS.
unfold Q1Y6.Mq2.pe_msE in *. cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pa_sp0 pa_F PF PA] in *.
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8, A_SB in *.
clear REST FRX.
reenterA asegs A4L HIx asegs_wx HP.
step.
step.
evt_done5.
eapply (pe_parse_i64_cX HIx GA GA_pres 0xa39f8 PARSEI PF PA q LB0 LM FRS payload me lo m md A B ts nb pj sv errv T kP buf cap (Ff + 144) n64
[CB 24 (pj_fhd pj); CB 8 f1a; C8 endw; CB 24 f1b; C1 cb; CB 79 f2a] [CB 24 f2c; C8 nu64; CB 64 f2e] (ffsh_cells (FSHN 0xf8)));
[ exact STC | exact INVX | exact PBK | exact Epbs | reflexivity | reflexivity | reflexivity | clear - GF; Z.div_mod_to_equations; lia | exact UNP | exact FRN
| rewrite unsigned_lit by lia; reflexivity | ].
intros m2 md2 A2 errv2 rv v w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 Hrv INVX2 PBK2.
assert (NX2 : NUM_INVX PF PA q LB0 LM FRS payload me lo m2 md2 A2 B ts cb nb pj sv errv2 0xf8) by (exists f1a, f1b, f2a, f2c, f2e, endw, v, nu64; exact INVX2).
cbn [pf_spf pa_sp0 PF PA] in *. unfold A_TP in *.
clear SLOTS HP INVX UNP PBK.
pose proof INVX2 as [CORE2 REST2]. destruct CORE2 as (_ & _ & _ & _ & _ & _ & _ & _ & FRX2). pose proof (proj1 REST2) as HP.
pose proof FRX2 as (SLOTS & _). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS. cbn [pf_tk pf_spf pf_lenr pa_F pa_sp0 pa_oldloc pa_newloc PF PA] in SLOTS.
unfold shA in SLOTS. a4l. unfold SB2, SB4, SB7, SB8, A_SB in SLOTS.
clear REST2 FRX2 INVX2.
replace (ret_pc (Z_to_bv 64 611000)) with (Z_to_bv 64 611000) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
reenterA asegs A4L HIx asegs_wx HP.
step. step. step.
step.
destruct Hrv as [-> | ->].
- if_true. evt_done5. eapply Kok; [exact NX2 | exact PBK2].
- if_false. evt_done5. eapply Kfail; [exact NX2 | exact PBK2].
Qed.

Lemma num_puint_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP buf cap : Z)
(x1 gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s6 t4 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo ->
NUM_INVX pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv 0xf8 ->
PBOKat m ts kP -> t_pbs ts = [(t_pb ts, PB_SZ); (buf, cap)] ->
Z.of_nat (length FRS) + 1 < 4096 ->
(forall m' md' A' errv' x1' gp' t0' t1' t2' a0' a1' a2' a3' a5' a6' a7' t4' t6',
NUM_INVX pf pa q LB0 LM FRS payload me lo m' md' A' B ts cb nb pj sv errv' 0xf8 -> PBOKat m' ts kP ->
AJ5 A4L HIx A' T md'
(Q1Y6.Mq2.pe_msE pf pa 0x9556c x1' gp' t0' t1' t2' a0' a1' a2' a3' (Z_to_bv 64 (pf_tk pf + 8)) a5' a6' a7'
(Z_to_bv 64 (pf_tk pf / 8 + 2147450883)) (Z_to_bv 64 (pf_tk pf + 20)) (Z_to_bv 64 (pf_tk pf / 8 + 2147450887)) s6 (Z_to_bv 64 (pf_tk pf + 32)) (Z_to_bv 64 (pa_F pa)) (Z_to_bv 64 (pf_tk pf + 56))
(Z_to_bv 64 (pf_tk pf / 8 + 2147450881)) (Z_to_bv 64 (pf_tk pf + 64)) t4' (Z_to_bv 64 (pf_tk pf / 8 + 2147450888)) t6' F fc m')) ->
(forall m' md' A' errv' x1' gp' t0' t1' t2' a0' a1' a2' a3' a5' a6' a7' t4' t6',
NUM_INVX pf pa q LB0 LM FRS payload me lo m' md' A' B ts cb nb pj sv errv' 0xf8 -> PBOKat m' ts kP ->
AJ5 A4L HIx A' T md'
(Q1Y6.Mq2.pe_msE pf pa 0x95338 x1' gp' t0' t1' t2' a0' a1' a2' a3' (Z_to_bv 64 (pf_tk pf + 8)) a5' a6' a7'
(Z_to_bv 64 (pf_tk pf / 8 + 2147450883)) (Z_to_bv 64 (pf_tk pf + 20)) (Z_to_bv 64 (pf_tk pf / 8 + 2147450887)) s6 (Z_to_bv 64 (pf_tk pf + 32)) (Z_to_bv 64 (pa_F pa)) (Z_to_bv 64 (pf_tk pf + 56))
(Z_to_bv 64 (pf_tk pf / 8 + 2147450881)) (Z_to_bv 64 (pf_tk pf + 64)) t4' (Z_to_bv 64 (pf_tk pf / 8 + 2147450888)) t6' F fc m')) ->
AJ5 A4L HIx A T md
(Q1Y6.Mq2.pe_msE pf pa 0x95320 x1 gp t0 t1 t2 (Z_to_bv 64 buf) a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (pf_tk pf / 8 + 2147450883)) (Z_to_bv 64 (pf_tk pf + 20)) (Z_to_bv 64 (pf_tk pf / 8 + 2147450887)) s6 (Z_to_bv 64 (pf_tk pf + 32)) (Z_to_bv 64 (pa_F pa)) (Z_to_bv 64 (pf_tk pf + 56))
(Z_to_bv 64 (pf_tk pf / 8 + 2147450881)) (Z_to_bv 64 (pf_tk pf + 64)) t4 (Z_to_bv 64 (pf_tk pf / 8 + 2147450888)) t6 F fc m).
Proof.
intros until fc. intros STC NX PBK Epbs FRN Kok Kfail.
destruct NX as (f1a & f1b & f2a & f2c & f2e & endw & n64 & nu64 & INVX).
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
pose proof INVX as [CORE REST]. destruct CORE as (_ & _ & _ & _ & _ & _ & _ & _ & FRX). pose proof (proj1 REST) as HP.
pose proof (num_unp m pf pa nb pj sv _ _ 22%nat (or_intror eq_refl) GF ltac:(lia) FRX) as UNP. change (8 * Z.of_nat 22) with 176 in UNP.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
set (PF := PEF tk oldl newl len lenr sb spf pmd mxd fl) in *. set (PA := PEFA sp0 Ff oldloc newloc bsl dsl) in *.
pose proof FRX as (SLOTS & _). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS. cbn [pf_tk pf_spf pf_lenr pa_F pa_sp0 pa_oldloc pa_newloc PF PA] in SLOTS.
unfold Q1Y6.Mq2.pe_msE in *. cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pa_sp0 pa_F PF PA] in *.
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8, A_SB in *.
clear REST FRX.
reenterA asegs A4L HIx asegs_wx HP.
step.
step.
evt_done5.
eapply (pe_parse_i64_cX HIx GA GA_pres 0xa3c68 PARSEU PF PA q LB0 LM FRS payload me lo m md A B ts nb pj sv errv T kP buf cap (Ff + 176) nu64
[CB 24 (pj_fhd pj); CB 8 f1a; C8 endw; CB 24 f1b; C1 cb; CB 79 f2a; C8 n64; CB 24 f2c] [CB 64 f2e] (ffsh_cells (FSHN 0xf8)));
[ exact STC | exact INVX | exact PBK | exact Epbs | reflexivity | reflexivity | reflexivity | clear - GF; Z.div_mod_to_equations; lia | exact UNP | exact FRN
| rewrite unsigned_lit by lia; reflexivity | ].
intros m2 md2 A2 errv2 rv v w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 Hrv INVX2 PBK2.
assert (NX2 : NUM_INVX PF PA q LB0 LM FRS payload me lo m2 md2 A2 B ts cb nb pj sv errv2 0xf8) by (exists f1a, f1b, f2a, f2c, f2e, endw, n64, v; exact INVX2).
cbn [pf_spf pa_sp0 PF PA] in *. unfold A_TP in *.
clear SLOTS HP INVX UNP PBK.
pose proof INVX2 as [CORE2 REST2]. destruct CORE2 as (_ & _ & _ & _ & _ & _ & _ & _ & FRX2). pose proof (proj1 REST2) as HP.
pose proof FRX2 as (SLOTS & _). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS. cbn [pf_tk pf_spf pf_lenr pa_F pa_sp0 pa_oldloc pa_newloc PF PA] in SLOTS.
unfold shA in SLOTS. a4l. unfold SB2, SB4, SB7, SB8, A_SB in SLOTS.
clear REST2 FRX2 INVX2.
replace (ret_pc (Z_to_bv 64 611112)) with (Z_to_bv 64 611112) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
reenterA asegs A4L HIx asegs_wx HP.
step. step. step.
step.
destruct Hrv as [-> | ->].
- if_true. evt_done5. eapply Kok; [exact NX2 | exact PBK2].
- if_false. evt_done5. eapply Kfail; [exact NX2 | exact PBK2].
Qed.

Lemma num_u0_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kB : nat)
(x1 gp t0 t1 t2 a0 a1 a2 a3 a5 a6 a7 s6 t4 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo ->
NUM_INVX pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv 0xf8 ->
BOK pf pa ts B kB ->
(forall a0' a1' a2',
AJ5 A4L HIx A T md
(Q1Y6.Mq2.pe_msE pf pa 0x95350 x1 gp t0 t1 t2 a0' a1' a2' a3 (Z_to_bv 64 (pf_tk pf + 8)) a5 a6 a7
(Z_to_bv 64 (pf_tk pf / 8 + 2147450883)) (Z_to_bv 64 (pf_tk pf + 20)) (Z_to_bv 64 (pf_tk pf / 8 + 2147450887)) s6 (Z_to_bv 64 (pf_tk pf + 32)) (Z_to_bv 64 (pa_F pa)) (Z_to_bv 64 (pf_tk pf + 56))
(Z_to_bv 64 (pf_tk pf / 8 + 2147450881)) (Z_to_bv 64 (pf_tk pf + 64)) t4 (Z_to_bv 64 (pf_tk pf / 8 + 2147450888)) t6 F fc m)) ->
(forall buf cap a1' a2',
t_pbs ts = [(t_pb ts, PB_SZ); (buf, cap)] ->
AJ5 A4L HIx A T md
(Q1Y6.Mq2.pe_msE pf pa 0x95320 x1 gp t0 t1 t2 (Z_to_bv 64 buf) a1' a2' a3 (Z_to_bv 64 (pf_tk pf + 8)) a5 a6 a7
(Z_to_bv 64 (pf_tk pf / 8 + 2147450883)) (Z_to_bv 64 (pf_tk pf + 20)) (Z_to_bv 64 (pf_tk pf / 8 + 2147450887)) s6 (Z_to_bv 64 (pf_tk pf + 32)) (Z_to_bv 64 (pa_F pa)) (Z_to_bv 64 (pf_tk pf + 56))
(Z_to_bv 64 (pf_tk pf / 8 + 2147450881)) (Z_to_bv 64 (pf_tk pf + 64)) t4 (Z_to_bv 64 (pf_tk pf / 8 + 2147450888)) t6 F fc m)) ->
(forall a0' a1' a2',
AJ5 A4L HIx A T md
(Q1Y6.Mq2.pe_msE pf pa 0x95338 x1 gp t0 t1 t2 a0' a1' a2' a3 (Z_to_bv 64 (pf_tk pf + 8)) a5 a6 a7
(Z_to_bv 64 (pf_tk pf / 8 + 2147450883)) (Z_to_bv 64 (pf_tk pf + 20)) (Z_to_bv 64 (pf_tk pf / 8 + 2147450887)) s6 (Z_to_bv 64 (pf_tk pf + 32)) (Z_to_bv 64 (pa_F pa)) (Z_to_bv 64 (pf_tk pf + 56))
(Z_to_bv 64 (pf_tk pf / 8 + 2147450881)) (Z_to_bv 64 (pf_tk pf + 64)) t4 (Z_to_bv 64 (pf_tk pf / 8 + 2147450888)) t6 F fc m)) ->
AJ5 A4L HIx A T md
(Q1Y6.Mq2.pe_msE pf pa 0x952c8 x1 gp t0 t1 t2 a0 a1 a2 a3 (Z_to_bv 64 (pf_tk pf + 8)) a5 a6 a7
(Z_to_bv 64 (pf_tk pf / 8 + 2147450883)) (Z_to_bv 64 (pf_tk pf + 20)) (Z_to_bv 64 (pf_tk pf / 8 + 2147450887)) s6 (Z_to_bv 64 (pf_tk pf + 32)) (Z_to_bv 64 (pa_F pa)) (Z_to_bv 64 (pf_tk pf + 56))
(Z_to_bv 64 (pf_tk pf / 8 + 2147450881)) (Z_to_bv 64 (pf_tk pf + 64)) t4 (Z_to_bv 64 (pf_tk pf / 8 + 2147450888)) t6 F fc m).
Proof.
intros until fc. intros STC NX BK Kdbl Kpu Ku1.
destruct NX as (f1a & f1b & f2a & f2c & f2e & endw & n64 & nu64 & INVX).
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
destruct INVX as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FRX).
pose proof REST as (HP & _).
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
destruct FRX as (SLOTS & _). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS.
unfold Q1Y6.Mq2.pe_msE in *.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
set (PF := PEF tk oldl newl len lenr sb spf pmd mxd fl) in *.
assert (INtk : In (tk, 72) (pe_blocksA PF q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 1 HP INtk ltac:(lia)) as SHT1.
replace (tk / 8 + 1 + A_SB) with (tk / 8 + 2147450881) in SHT1 by (unfold A_SB; lia).
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 3 HP INtk ltac:(lia)) as SHT3.
replace (tk / 8 + 3 + A_SB) with (tk / 8 + 2147450883) in SHT3 by (unfold A_SB; lia).
destruct PB as (buf & bpos & cap & pre & post & Epbs & Lpre & CORE1). destruct CORE1 as (Hbp & Hcap & Hlen & PBC & BUFC).
assert (INpb : In (pb, PB_SZ) (pe_blocksA PF q LB0 ts0)) by (unfold pe_blocksA, tstate_blocks, ts0; cbn [t_pbs]; rewrite Epbs; apply in_or_app; left; left; reflexivity).
assert (INbuf : In (buf, cap) (pe_blocksA PF q LB0 ts0)) by (unfold pe_blocksA, tstate_blocks, ts0; cbn [t_pbs]; rewrite Epbs; apply in_or_app; left; right; left; reflexivity).
assert (CAP32 : 32 <= cap) by (destruct BK as (_ & _ & _ & (X & _) & _); unfold ts0 in X; cbn [t_pbs] in X; rewrite Epbs in X; unfold pb_capA in X; cbn [nth snd] in X; exact X).
blk_factsA A4L HIx HP pb 16 Hpal Hplo Hphi Himg_p.
blk_factsA A4L HIx HP buf cap Hbal Hblo Hbhi Himg_b.
pose proof (blk_granA HIx _ _ _ _ _ _ _ pb 16 0 HP INpb ltac:(lia) ltac:(lia)) as SHP0.
replace (pb / 8 + 0 + A_SB) with (pb / 8 + 2147450880) in SHP0 by (unfold A_SB; lia).
pose proof (blk_granA HIx _ _ _ _ _ _ _ buf cap 0 HP INbuf ltac:(lia) ltac:(lia)) as SHB0.
replace (buf / 8 + 0 + A_SB) with (buf / 8 + 2147450880) in SHB0 by (unfold A_SB; lia).
pose proof (rw_cells_bytes_at' _ _ _ _ BUFC) as BUFB. cbn [cells_bytes cbytes] in BUFB. rewrite app_nil_r in BUFB.
assert (Ech : exists ch tl, pre ++ [Z_to_bv 8 0] ++ post = ch :: tl) by (destruct pre as [|c' s']; cbn; eauto).
destruct Ech as (ch & tl & Ech). rewrite Ech in BUFB.
pose proof (payload_byteA m buf (ch :: tl) 0 ch BUFB eq_refl ltac:(lia)) as RDB. rewrite Z.add_0_r in RDB.
pose proof (bv_unsigned_in_range 8 ch) as CHR; unfold bv_modulus in CHR; cbn in CHR.
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8, A_SB in *.
stash Himg_t. stash Himg_p. stash Himg_b. stash TSK. stash REST. stash BUFC. stash BUFB.
reenterA asegs A4L HIx asegs_wx HP.
asan_rechkA.
step.
step.
step.
destruct (Z.eq_dec (bv_unsigned (sx32 isd)) 0) as [EI0 | NI0].
2:{ if_truex. evt_done5. apply Kdbl. }
if_falsex.
asan_rechkA.
step.
asan_chkA.
step.
asan_chkA.
step.
change (zxb ch) with (Z_to_bv 64 (bv_unsigned ch)).
step.
step.
destruct (Z.eq_dec (bv_unsigned ch) 45) as [E45 | N45].
- if_truex. evt_done5. apply Ku1.
- if_falsex. evt_done5. eapply (Kpu buf cap). exact Epbs.
Qed.

Lemma num_u1_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet)
(x1 gp t0 t1 t2 a0 a1 a2 a3 a5 a6 a7 s6 t4 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo ->
NUM_INVX pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv 0xf8 ->
(forall a0',
AJ5 A4L HIx A T md
(Q1Y6.Mq2.pe_msE pf pa 0x95350 x1 gp t0 t1 t2 a0' a1 a2 a3 (Z_to_bv 64 (pf_tk pf + 8)) a5 a6 a7
(Z_to_bv 64 (pf_tk pf / 8 + 2147450883)) (Z_to_bv 64 (pf_tk pf + 20)) (Z_to_bv 64 (pf_tk pf / 8 + 2147450887)) s6 (Z_to_bv 64 (pf_tk pf + 32)) (Z_to_bv 64 (pa_F pa)) (Z_to_bv 64 (pf_tk pf + 56))
(Z_to_bv 64 (pf_tk pf / 8 + 2147450881)) (Z_to_bv 64 (pf_tk pf + 64)) t4 (Z_to_bv 64 (pf_tk pf / 8 + 2147450888)) t6 F fc m)) ->
(forall a0',
AJ5 A4L HIx A T md
(Q1Y6.Mq2.pe_msE pf pa 0x989cc x1 gp t0 t1 t2 a0' a1 a2 a3 (Z_to_bv 64 (pf_tk pf + 8)) a5 a6 a7
(Z_to_bv 64 (pf_tk pf / 8 + 2147450883)) (Z_to_bv 64 (pf_tk pf + 20)) (Z_to_bv 64 (pf_tk pf / 8 + 2147450887)) s6 (Z_to_bv 64 (pf_tk pf + 32)) (Z_to_bv 64 (pa_F pa)) (Z_to_bv 64 (pf_tk pf + 56))
(Z_to_bv 64 (pf_tk pf / 8 + 2147450881)) (Z_to_bv 64 (pf_tk pf + 64)) t4 (Z_to_bv 64 (pf_tk pf / 8 + 2147450888)) t6 F fc m)) ->
AJ5 A4L HIx A T md
(Q1Y6.Mq2.pe_msE pf pa 0x95338 x1 gp t0 t1 t2 a0 a1 a2 a3 (Z_to_bv 64 (pf_tk pf + 8)) a5 a6 a7
(Z_to_bv 64 (pf_tk pf / 8 + 2147450883)) (Z_to_bv 64 (pf_tk pf + 20)) (Z_to_bv 64 (pf_tk pf / 8 + 2147450887)) s6 (Z_to_bv 64 (pf_tk pf + 32)) (Z_to_bv 64 (pa_F pa)) (Z_to_bv 64 (pf_tk pf + 56))
(Z_to_bv 64 (pf_tk pf / 8 + 2147450881)) (Z_to_bv 64 (pf_tk pf + 64)) t4 (Z_to_bv 64 (pf_tk pf / 8 + 2147450888)) t6 F fc m).
Proof.
intros until fc. intros STC NX Kdbl Kerr.
destruct NX as (f1a & f1b & f2a & f2c & f2e & endw & n64 & nu64 & INVX).
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
destruct INVX as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FRX).
pose proof REST as (HP & _).
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
destruct FRX as (SLOTS & _). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS.
unfold Q1Y6.Mq2.pe_msE in *.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
set (PF := PEF tk oldl newl len lenr sb spf pmd mxd fl) in *.
assert (INtk : In (tk, 72) (pe_blocksA PF q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 3 HP INtk ltac:(lia)) as SHT3.
replace (tk / 8 + 3 + A_SB) with (tk / 8 + 2147450883) in SHT3 by (unfold A_SB; lia).
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8, A_SB in *.
stash Himg_t. clear PB TSK REST.
reenterA asegs A4L HIx asegs_wx HP.
asan_rechkA.
step.
step.
step.
destruct (Z.eq_dec (bv_unsigned (sx32 isd)) 0) as [EI0 | NI0].
2:{ if_truex. evt_done5. apply Kdbl. }
if_falsex.
step.
evt_done5. apply Kerr.
Qed.

Definition num_pj (pj : pe_junkA) (f1a f1b f2a f2c f2e : list byte) (endw n64 nu64 : word) : pe_junkA :=
PEJA (pj_0 pj) (pj_8 pj) (pj_16 pj) (pj_obj pj) (pj_288 pj) (pj_304 pj) (pj_gap pj) (pj_fhd pj) (f1a ++ le8 endw ++ f1b) (f2a ++ le8 n64 ++ f2c ++ le8 nu64 ++ f2e).
Lemma num_frame_close : forall (m : word -> option byte) (pf : pe_fix) (pa : pe_fixA) (cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved)
(f1a f1b f2a f2c f2e : list byte) (endw n64 nu64 : word),
pe_frameAX m pf pa nb pj sv (num_ffc cb (pj_fhd pj) f1a f1b f2a f2c f2e endw n64 nu64) (ffsh_cells FSH0) ->
pe_frameA asegs m pf pa cb nb (num_pj pj f1a f1b f2a f2c f2e endw n64 nu64) sv.
Proof.
intros m pf pa cb nb pj sv f1a f1b f2a f2c f2e endw n64 nu64 (SL & GP & SV & FF & FSH).
split; [exact SL|]. split; [exact GP|]. split; [exact SV|]. split; [| exact FSH].
exact (num_ffc_close m (pa_F pa) cb pj f1a f1b f2a f2c f2e endw n64 nu64 FF).
Qed.

Lemma num_errx_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (e : Z)
(x1 gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5 s7 s11 t4 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo ->
NUM_INVX pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv 0xf8 ->
0 <= e < 2^31 ->
(forall m' pj' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' s11' t4' t6',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md A B (ts_set_x ts (t_co ts) (tx_err (t_x ts) (Z_to_bv 64 e))) cb nb pj' sv errv ->
AJ5 A4L HIx A T md
(pe_msO asegs pf pa APE_OUT x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' (Z_to_bv 64 (pf_tk pf + 56)) s11' t4' t6' F fc m')) ->
AJ5 A4L HIx A T md
(Q1Y6.Mq2.pe_msE pf pa 0x98498 x1 gp t0 t1 t2 (Z_to_bv 64 e) a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (pf_tk pf / 8 + 2147450882)) (Z_to_bv 64 (pf_tk pf + 20)) s5 (Z_to_bv 64 (pf_tk pf + 36)) s7 (Z_to_bv 64 (pa_F pa)) (Z_to_bv 64 (pf_tk pf + 56))
s11 (Z_to_bv 64 (pf_tk pf + 64)) t4 (Z_to_bv 64 (pf_tk pf / 8 + 2147450888)) t6 F fc m).
Proof.
intros until fc. intros STC NX He Kout.
destruct NX as (f1a & f1b & f2a & f2c & f2e & endw & n64 & nu64 & INVX). pose proof INVX as INVX0.
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
destruct INVX as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FRX).
pose proof REST as (HP & _).
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
pose proof FRX as FRX0. destruct FRX as (SLOTS & GAP & SAVED & FFX & FSH). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS.
unfold num_ffc in FFX. unfold ffsh_cells, FSHN in FSH. cbn [map] in FSH.
unfold Q1Y6.Mq2.pe_msE, pe_msO in *.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
set (PF := PEF tk oldl newl len lenr sb spf pmd mxd fl) in *. set (PA := PEFA sp0 Ff oldloc newloc bsl dsl) in *.
assert (INtk : In (tk, 72) (pe_blocksA PF q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 4 HP INtk ltac:(lia)) as SHT4.
replace (tk / 8 + 4 + A_SB) with (tk / 8 + 2147450884) in SHT4 by (unfold A_SB; lia).
assert (INF : In (Ff, 2) ((Ff, 2) :: FRS)) by (left; reflexivity).
pose proof alloc_ceiling_range as ACR.
assert (GF0' : 0 <= Ff) by lia. assert (GFc' : Ff < alloc_ceiling) by lia.
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP INF (in_or_app _ LM _ (or_introl INtk))) as DFt. rewrite fr_size_2 in DFt.
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP INF) as DSF. rewrite fr_size_2 in DSF. cbn [hl_sb A4L] in DSF.
pose proof (shadow_blk_apart HIx _ _ _ _ _ _ _ _ _ Ff 32 HP (in_or_app _ LM _ (or_introl INtk)) GF0' GFc' ltac:(lia)) as DSt. unfold shA, A_SB in DSt.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(tk, tk + 72); (Ff, Ff + 248); (Ff / 8 + 2147450880, Ff / 8 + 2147450880 + 32)] m) as MU.
assert (HW : Forall (pe_wtfA PF PA) [(tk, tk + 72); (Ff, Ff + 248); (Ff / 8 + 2147450880, Ff / 8 + 2147450880 + 32)]).
{ apply Forall_cons; [left; cbn [fst snd pf_tk PF]; lia |]. apply Forall_cons; [right; right; left; cbn [fst snd pa_F PA]; lia |].
apply Forall_cons; [| apply Forall_nil]. right; right; right. cbn [fst snd pa_F PA]. unfold shA, A_SB. lia. }
unfold APE_OUT in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8, A_SB in *.
stash Himg_t. stash Kout. stash INVX0. stash FRX0. stash GAP. stash SAVED. stash TSK. stash REST. stash PB.
reenterA asegs A4L HIx asegs_wx HP.
step.
asan_rechkA.
stepz.
step.
stepz.
stepz.
step.
unstash INVX0. unstash FRX0.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, FFc : rw_cells asegs mc Ff ?ffc, FSHc : rw_cells asegs mc (Ff / 8 + 2147450880) ?shc |- _ =>
evt_done5;
assert (FRXc : pe_frameAX mc PF PA nb pj sv (num_ffc cb (pj_fhd pj) f1a f1b f2a f2c f2e endw n64 nu64) (ffsh_cells FSH0))
by (eapply (pe_frameAX_write HIx PF PA q LB0 LM FRS B ts0 A m mc md lo nb pj sv); [exact STC | exact HP | exact FRX0 | exact MUc | exact WMc | exact FFc | exact FSHc]);
pose proof (num_frame_close mc PF PA cb nb pj sv f1a f1b f2a f2c f2e endw n64 nu64 FRXc) as FRc;
destruct (PE_INV_AX_tokw HIx GA GA_outside PF PA q LB0 LM FRS payload me lo m mc md A B ts0 errv _ co (tx_err (t_x ts0) (Z_to_bv 64 e)) _ _ STC INVX0 MUc WMc MIc HW TOKc FRc
ltac:(unfold PF; cbn [pf_len]; lia) eq_refl) as [INV1 _]
end end.
unstash Kout. eapply (Kout _ (num_pj pj f1a f1b f2a f2c f2e endw n64 nu64)). exact INV1.
Qed.

Lemma num_err7x_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet)
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s11 t4 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo ->
NUM_INVX pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv 0xf8 ->
(forall m' pj' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' s11' t4' t6',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md A B (ts_set_x ts (t_co ts) (tx_err (t_x ts) (Z_to_bv 64 7))) cb nb pj' sv errv ->
AJ5 A4L HIx A T md
(pe_msO asegs pf pa APE_OUT x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' (Z_to_bv 64 (pf_tk pf + 56)) s11' t4' t6' F fc m')) ->
AJ5 A4L HIx A T md
(Q1Y6.Mq2.pe_msE pf pa 0x989cc x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 (Z_to_bv 64 (pf_tk pf + 20)) s5 s6 s7 (Z_to_bv 64 (pa_F pa)) (Z_to_bv 64 (pf_tk pf + 56))
s11 (Z_to_bv 64 (pf_tk pf + 64)) t4 (Z_to_bv 64 (pf_tk pf / 8 + 2147450888)) t6 F fc m).
Proof.
intros until fc. intros STC NX Kout. pose proof NX as NX0.
destruct NX as (f1a & f1b & f2a & f2c & f2e & endw & n64 & nu64 & INVX).
destruct INVX as [CORE REST]. destruct CORE as (_ & _ & _ & _ & _ & _ & _ & _ & FRX). pose proof (proj1 REST) as HP.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
destruct FRX as (SLOTS & _). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS. cbn [pf_tk pf_spf pf_lenr pa_F pa_sp0 pa_oldloc pa_newloc] in SLOTS.
unfold Q1Y6.Mq2.pe_msE in *. cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pa_sp0 pa_F] in *.
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8, A_SB in *.
clear REST.
reenterA asegs A4L HIx asegs_wx HP.
step. step. step.
step.
evt_done5.
eapply (num_errx_A (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv T 7); [exact STC | exact NX0 | lia | exact Kout].
Qed.

Lemma num_err7d_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet)
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo ->
NUM_INVX pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv 0xf8 ->
(forall m' pj' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' s11' t4' t6',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md A B (ts_set_x ts (t_co ts) (tx_err (t_x ts) (Z_to_bv 64 7))) cb nb pj' sv errv ->
AJ5 A4L HIx A T md
(pe_msO asegs pf pa APE_OUT x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' (Z_to_bv 64 (pf_tk pf + 56)) s11' t4' t6' F fc m')) ->
AJ5 A4L HIx A T md
(Q1Y6.Mq2.pe_msE pf pa 0x98480 x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 (Z_to_bv 64 (pa_F pa)) (Z_to_bv 64 (pf_tk pf + 56))
s11 t3 t4 t5 t6 F fc m).
Proof.
intros until fc. intros STC NX Kout. pose proof NX as NX0.
destruct NX as (f1a & f1b & f2a & f2c & f2e & endw & n64 & nu64 & INVX).
destruct INVX as [CORE REST]. destruct CORE as (_ & _ & _ & _ & _ & _ & _ & _ & FRX). pose proof (proj1 REST) as HP.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
destruct FRX as (SLOTS & _). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS. cbn [pf_tk pf_spf pf_lenr pa_F pa_sp0 pa_oldloc pa_newloc] in SLOTS.
unfold Q1Y6.Mq2.pe_msE in *. cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pa_sp0 pa_F] in *.
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8, A_SB in *.
clear REST.
reenterA asegs A4L HIx asegs_wx HP.
step. step. step. step. step. step.
evt_done5.
eapply (num_errx_A (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv T 7); [exact STC | exact NX0 | lia | exact Kout].
Qed.

Lemma num_errno_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet)
(x1 gp t0 t1 t2 a0 a1 a2 a3 a5 a6 a7 s3 s6 t4 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> pf_fl pf = 0 ->
NUM_INVX pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv 0xf8 ->
(forall x1' a0' a1',
AJ5 A4L HIx A T md
(Q1Y6.Mq2.pe_msE pf pa 0x95504 x1' gp t0 t1 t2 a0' a1' a2 a3 (Z_to_bv 64 (pf_tk pf + 8)) a5 a6 a7
(Z_to_bv 64 (pf_tk pf / 8 + 2147450882)) (Z_to_bv 64 (pf_tk pf + 20)) (Z_to_bv 64 (pf_tk pf / 8 + 2147450887)) s6 (Z_to_bv 64 (pf_tk pf + 32)) (Z_to_bv 64 (pa_F pa)) (Z_to_bv 64 (pf_tk pf + 56))
(Z_to_bv 64 (pf_tk pf / 8 + 2147450881)) (Z_to_bv 64 (pf_tk pf + 64)) t4 (Z_to_bv 64 (pf_tk pf / 8 + 2147450888)) t6 F fc m)) ->
AJ5 A4L HIx A T md
(Q1Y6.Mq2.pe_msE pf pa 0x954c0 x1 gp t0 t1 t2 a0 a1 a2 a3 (Z_to_bv 64 (pf_tk pf + 8)) a5 a6 a7
s3 (Z_to_bv 64 (pf_tk pf + 20)) (Z_to_bv 64 (pf_tk pf / 8 + 2147450887)) s6 (Z_to_bv 64 (pf_tk pf + 32)) (Z_to_bv 64 (pa_F pa)) (Z_to_bv 64 (pf_tk pf + 56))
(Z_to_bv 64 (pf_tk pf / 8 + 2147450881)) (Z_to_bv 64 (pf_tk pf + 64)) t4 (Z_to_bv 64 (pf_tk pf / 8 + 2147450888)) t6 F fc m).
Proof.
intros until fc. intros STC FL0 NX K.
destruct NX as (f1a & f1b & f2a & f2c & f2e & endw & n64 & nu64 & INVX).
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
destruct INVX as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FRX).
pose proof REST as (HP & _ & _ & _ & ERR & _).
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *. subst fl.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
destruct FRX as (SLOTS & _). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS.
unfold Q1Y6.Mq2.pe_msE in *.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
set (PF := PEF tk oldl newl len lenr sb spf pmd mxd 0) in *.
assert (INtk : In (tk, 72) (pe_blocksA PF q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 8 HP INtk ltac:(lia)) as SHT8.
replace (tk / 8 + 8 + A_SB) with (tk / 8 + 2147450888) in SHT8 by (unfold A_SB; lia).
pose proof (errno_shadowA HIx _ _ _ _ _ _ _ HP) as ESH.
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8, A_SB in *. change ((6434400 - 164) / 8 + 2147450880) with 2148255159 in ESH.
change (6434400 - 164) with 6434236 in ERR.
pose proof (tok_flags_byteA mxd 0 m tk pb (Z.of_nat depth) q (TS isd stpos (Z_to_bv 64 co) err ucs high quote) TOK) as RDF.
stash Himg_t. clear PB TSK REST.
reenterA asegs A4L HIx asegs_wx HP.
step.
step. step. step.
try (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end).
asan_chkA.
step.
step.
step.
step.
destruct (Z.eq_dec (bv_unsigned (sx32 errv)) 34) as [E34 | N34].
2:{ if_truex. evt_done5. apply K. }
if_falsex.
step.
step.
rewrite ?sxb_zero, ?zxb_zero.
step.
step.
if_false.
step.
rewrite ?zxb_zero. clear RDF.
step.
step.
if_true.
evt_done5. apply K.
Qed.

Lemma num_errnou_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet)
(x1 gp t0 t1 t2 a0 a1 a2 a3 a5 a6 a7 s3 s6 t4 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> pf_fl pf = 0 ->
NUM_INVX pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv 0xf8 ->
(forall x1' a0' a1',
AJ5 A4L HIx A T md
(Q1Y6.Mq2.pe_msE pf pa 0x955b0 x1' gp t0 t1 t2 a0' a1' a2 a3 (Z_to_bv 64 (pf_tk pf + 8)) a5 a6 a7
(Z_to_bv 64 (pf_tk pf / 8 + 2147450882)) (Z_to_bv 64 (pf_tk pf + 20)) (Z_to_bv 64 (pf_tk pf / 8 + 2147450887)) s6 (Z_to_bv 64 (pf_tk pf + 32)) (Z_to_bv 64 (pa_F pa)) (Z_to_bv 64 (pf_tk pf + 56))
(Z_to_bv 64 (pf_tk pf / 8 + 2147450881)) (Z_to_bv 64 (pf_tk pf + 64)) t4 (Z_to_bv 64 (pf_tk pf / 8 + 2147450888)) t6 F fc m)) ->
AJ5 A4L HIx A T md
(Q1Y6.Mq2.pe_msE pf pa 0x9556c x1 gp t0 t1 t2 a0 a1 a2 a3 (Z_to_bv 64 (pf_tk pf + 8)) a5 a6 a7
s3 (Z_to_bv 64 (pf_tk pf + 20)) (Z_to_bv 64 (pf_tk pf / 8 + 2147450887)) s6 (Z_to_bv 64 (pf_tk pf + 32)) (Z_to_bv 64 (pa_F pa)) (Z_to_bv 64 (pf_tk pf + 56))
(Z_to_bv 64 (pf_tk pf / 8 + 2147450881)) (Z_to_bv 64 (pf_tk pf + 64)) t4 (Z_to_bv 64 (pf_tk pf / 8 + 2147450888)) t6 F fc m).
Proof.
intros until fc. intros STC FL0 NX K.
destruct NX as (f1a & f1b & f2a & f2c & f2e & endw & n64 & nu64 & INVX).
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
destruct INVX as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FRX).
pose proof REST as (HP & _ & _ & _ & ERR & _).
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *. subst fl.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
destruct FRX as (SLOTS & _). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS.
unfold Q1Y6.Mq2.pe_msE in *.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
set (PF := PEF tk oldl newl len lenr sb spf pmd mxd 0) in *.
assert (INtk : In (tk, 72) (pe_blocksA PF q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 8 HP INtk ltac:(lia)) as SHT8.
replace (tk / 8 + 8 + A_SB) with (tk / 8 + 2147450888) in SHT8 by (unfold A_SB; lia).
pose proof (errno_shadowA HIx _ _ _ _ _ _ _ HP) as ESH.
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8, A_SB in *. change ((6434400 - 164) / 8 + 2147450880) with 2148255159 in ESH.
change (6434400 - 164) with 6434236 in ERR.
pose proof (tok_flags_byteA mxd 0 m tk pb (Z.of_nat depth) q (TS isd stpos (Z_to_bv 64 co) err ucs high quote) TOK) as RDF.
stash Himg_t. clear PB TSK REST.
reenterA asegs A4L HIx asegs_wx HP.
step.
step. step. step.
try (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end).
asan_chkA.
step.
step.
step.
step. step.
step.
destruct (Z.eq_dec (bv_unsigned (sx32 errv)) 34) as [E34 | N34].
2:{ if_truex. evt_done5. apply K. }
if_falsex.
asan_rechkA.
step.
rewrite ?zxb_zero. clear RDF.
step.
step.
if_true.
evt_done5. apply K.
Qed.

Definition NUM_WINR (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (r : Z) (sh : jshape) (wb : Z)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) : Prop :=
(r = 0 /\ NUM_WINX pf pa q LB0 LM FRS payload me lo m md A B ts 0 None [] cb nb pj sv errv) \/
(r <> 0 /\ exists BS, (length BS <= 4)%nat /\ (exists w, jfresh sh BS w /\ w <= wb) /\ 0 < r < 2^62 /\ NUM_WINX pf pa q LB0 LM FRS payload me lo m md A B ts r (Some sh) BS cb nb pj sv errv).

Lemma num_newint_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP : Z) (nB : nat)
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s11 t4 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa -> 0 <= pa_dslack pa ->
NUM_INVX pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv 0xf8 ->
PBOKat m ts kP -> BOK pf pa ts B (S (Z.to_nat (16 * Z.max 0 (pf_len pf) + 8192) + nB)) ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_number ->
(forall m2 md2 A2 B2 errv2 (r : Z) gp' t0' t1' t2' a2' a3' a4' a5' a6' a7' F2 fc2,
NUM_WINR pf pa q LB0 LM FRS payload me lo m2 md2 A2 B2 (ts_lvl ts (TL (tl_st l) (tl_ss l) 0 None [] 0 [])) r Sint (Z.max 20 (kP + 16)) cb nb pj sv errv2 ->
PBOKat m2 (ts_lvl ts (TL (tl_st l) (tl_ss l) 0 None [] 0 [])) kP ->
bB B - newint_costB <= bB B2 -> bD B - 1 <= bD B2 ->
fsaved F F2 -> (frm0 fc -> frm0 fc2) ->
AJ5 A4L HIx A2 T md2
(Q1Y6.Mq2.pe_msE pf pa 0x95560 (Z_to_bv 64 (pf_tk pf / 8 + 2147450884)) gp' t0' t1' t2' (Z_to_bv 64 r) (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts) + 16)) a2' a3' a4' a5' a6' a7'
(Z_to_bv 64 (pf_tk pf / 8 + 2147450882)) (Z_to_bv 64 (pf_tk pf + 20)) (Z_to_bv 64 (pf_tk pf / 8 + 2147450887)) s6 (Z_to_bv 64 (pf_tk pf + 32)) (Z_to_bv 64 (pa_F pa)) (Z_to_bv 64 (pf_tk pf + 56))
s11 (Z_to_bv 64 (pf_tk pf + 64)) (Z_to_bv 64 (pa_F pa + 64)) (Z_to_bv 64 (pf_tk pf / 8 + 2147450888)) (Z_to_bv 64 (pf_lenr pf)) F2 fc2 m2)) ->
AJ5 A4L HIx A T md
(Q1Y6.Mq2.pe_msE pf pa 0x95504 x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (pf_tk pf / 8 + 2147450882)) (Z_to_bv 64 (pf_tk pf + 20)) (Z_to_bv 64 (pf_tk pf / 8 + 2147450887)) s6 (Z_to_bv 64 (pf_tk pf + 32)) (Z_to_bv 64 (pa_F pa)) (Z_to_bv 64 (pf_tk pf + 56))
s11 (Z_to_bv 64 (pf_tk pf + 64)) t4 (Z_to_bv 64 (pf_tk pf / 8 + 2147450888)) t6 F fc m).
Proof.
intros until fc. intros STC BSL DSL NX PBK BK Hl Hst Kjoin.
destruct NX as (f1a & f1b & f2a & f2c & f2e & endw & n64 & nu64 & INVX). pose proof INVX as INVX0.
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
destruct INVX as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FRX).
pose proof REST as (HP & LV & OBJ & _).
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
pose proof FRX as (SLOTS & _ & _ & FFX & _). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS. unfold num_ffc in FFX.
unfold Q1Y6.Mq2.pe_msE in *.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
set (PF := PEF tk oldl newl len lenr sb spf pmd mxd fl) in *. set (PA := PEFA sp0 Ff oldloc newloc bsl dsl) in *.
pose proof (LV depth l Hl) as LVd. pose proof LVd as (ST26 & SS26 & _ & Md).
rewrite Nat.ltb_irrefl, Nat.eqb_refl in Md. destruct Md as (c0 & hn0 & Hmode & CLS0 & NM0).
destruct (number_mode_ss _ _ _ SS26 ltac:(rewrite <- Hst; exact Hmode)) as (Ec0 & Ehn0 & Ess). subst c0 hn0.
cbn [name_ok] in NM0. destruct NM0 as [Hn0 Hnbs0].
assert (Ecs : tl_cs l = None) by (destruct (tl_cs l); [exfalso; exact CLS0 | reflexivity]).
pose proof (LV depth l Hl) as (_ & _ & JO & _). rewrite Ecs in JO. cbn [jopt] in JO. destruct JO as [Ecur Ecbs].
assert (Eobjbs : objbs = []).
{ unfold cur_st in OBJ. cbn [t_levels t_depth t_objbs ts0] in OBJ. rewrite Hl, Hst in OBJ. exact OBJ. }
pose proof (PE_WINX_open HIx GA PF PA q LB0 LM FRS payload me lo m md A B ts0 errv l _ INVX0 Hl Hn0 Hnbs0 Eobjbs) as WIN0.
rewrite Ecur, Ecs, Ecbs in WIN0.
set (lw0 := TL (tl_st l) (tl_ss l) 0 None [] 0 []) in *. set (tw0 := ts_lvl ts0 lw0) in *.
assert (PBK0 : PBOKat m tw0 kP) by (exact (PBOKat_same m ts0 tw0 _ eq_refl eq_refl PBK)).
pose proof (BOK_afford PF PA ts0 B nB newint_costB BSL BK ltac:(pose proof (K_ev_pos PF); unfold newint_costB; lia)) as COST.
assert (COSTD : 1 <= bD B) by (destruct BK as (_ & HD & _); cbn [pa_dslack PA] in HD; lia).
pose proof (TSK depth l Hl) as Ld. remember (q + 32 * Z.of_nat depth) as bse eqn:Hbse in Ld.
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8, A_SB in *.
clear REST LV OBJ PB TSK Ld.
reenterA asegs A4L HIx asegs_wx HP.
step.
step.
step.
evt_done5.
eapply (pe_new_int_wX HIx GA GA_pres 0x9c330 NEWINT PF PA q LB0 LM FRS payload me lo m md A B tw0 nb pj sv errv T kP
(num_ffc cb (pj_fhd pj) f1a f1b f2a f2c f2e endw n64 nu64) (ffsh_cells (FSHN 0xf8)));
[ exact STC | exact WIN0 | cbn; lia | cbn; lia | exact PBK0 | exact COST | exact COSTD | rewrite unsigned_lit by lia; reflexivity |].
intros m2 md2 A2 B2 errv2 r w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 F2 fc2 OUT2 PBK2 HB2 HD2 FS2 FRM2.
cbn [pf_spf pa_sp0 pa_F PF PA] in *. unfold A_TP in *.
assert (WR2 : NUM_WINR PF PA q LB0 LM FRS payload me lo m2 md2 A2 B2 tw0 r Sint (Z.max 20 (kP + 16)) cb nb pj sv errv2).
{ destruct OUT2 as [(-> & W) | (Hr & BS & LEN3 & JF & Rr & W)].
- left. split; [reflexivity|]. exists f1a, f1b, f2a, f2c, f2e, endw, n64, nu64. exact W.
- right. split; [exact Hr|]. exists BS. split; [lia|]. split; [exists 20; split; [exact JF | lia]|]. split; [exact Rr|]. exists f1a, f1b, f2a, f2c, f2e, endw, n64, nu64. exact W. }
assert (COMMON : exists p2 s2 BS2, PE_WINX HIx GA PF PA q LB0 LM FRS payload me lo m2 md2 A2 B2 tw0 p2 s2 BS2 1 errv2
(pe_frameAX m2 PF PA nb pj sv (num_ffc cb (pj_fhd pj) f1a f1b f2a f2c f2e endw n64 nu64) (ffsh_cells (FSHN 0xf8))))
by (destruct OUT2 as [(_ & W) | (_ & BS & _ & _ & _ & W)]; eauto).
destruct COMMON as (p2 & s2 & BS2 & WIN2). clear OUT2.
clear TOK SLOTS FFX HP WIN0 PBK0 INVX0 FRX PBK.
pose proof WIN2 as (CORE2 & BASE2 & _). destruct CORE2 as (_ & _ & _ & _ & TOK & _ & _ & _ & FRX2). pose proof (proj1 BASE2) as HP. clear BASE2 WIN2.
unfold tw0, ts_lvl, ts0 in TOK. cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_tk pf_mxd pf_fl PF] in TOK.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
destruct FRX2 as (SLOTS & _). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc PF PA] in SLOTS.
assert (INtk : In (tk, 72) (pe_blocksA PF q LB0 (tsF tw0 BS2))) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * mxd) (pe_blocksA PF q LB0 (tsF tw0 BS2))) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t2.
blk_factsA A4L HIx HP q (32 * mxd) Hqal Hqlo Hqhi Himg_q2.
assert (Hb8 : bse mod 8 = 0) by (subst bse; clear - Hqal; Z.div_mod_to_equations; lia).
shq_facts HP INq INtk q mxd tk (Z.of_nat depth) 2 SHQ2 SEPQ2c SEPQ2q SEPQ2t.
replace (q / 8 + 4 * (Z.of_nat depth) + 2 + A_SB) with (bse / 8 + 2147450882) in SHQ2 by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia).
clear SEPQ2c SEPQ2q SEPQ2t.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 7 HP INtk ltac:(lia)) as SHT7.
replace (tk / 8 + 7 + A_SB) with (tk / 8 + 2147450887) in SHT7 by (unfold A_SB; lia).
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 2 HP INtk ltac:(lia)) as SHT2.
replace (tk / 8 + 2 + A_SB) with (tk / 8 + 2147450882) in SHT2 by (unfold A_SB; lia).
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8, A_SB in *.
stash Himg_t2. stash Himg_q2. stash WR2.
replace (ret_pc (Z_to_bv 64 611600)) with (Z_to_bv 64 611600) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
reenterA asegs A4L HIx asegs_wx HP.
asan_rechkA.
asan_rechkM 4.
step.
norm_sx32.
step.
rewrite (unsigned_lit (Z.of_nat depth)) by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32.
step.
replace (q + Z.of_nat depth * 32) with bse by lia.
step.
asan_chkM 2.
evt_done5. unstash WR2.
replace (q + 32 * Z.of_nat depth + 16) with (bse + 16) in Kjoin by lia.
eapply (Kjoin m2 md2 A2 B2 errv2 r); [exact WR2 | exact PBK2 | exact HB2 | exact HD2 | exact FS2 | exact FRM2].
Qed.

Lemma num_newuint_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP : Z) (nB : nat)
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s11 t4 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa -> 0 <= pa_dslack pa ->
NUM_INVX pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv 0xf8 ->
PBOKat m ts kP -> BOK pf pa ts B (S (Z.to_nat (16 * Z.max 0 (pf_len pf) + 8192) + nB)) ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_number ->
(forall m2 md2 A2 B2 errv2 (r : Z) gp' t0' t1' t2' a2' a3' a4' a5' a6' a7' F2 fc2,
NUM_WINR pf pa q LB0 LM FRS payload me lo m2 md2 A2 B2 (ts_lvl ts (TL (tl_st l) (tl_ss l) 0 None [] 0 [])) r Sint (Z.max 20 (kP + 16)) cb nb pj sv errv2 ->
PBOKat m2 (ts_lvl ts (TL (tl_st l) (tl_ss l) 0 None [] 0 [])) kP ->
bB B - newint_costB <= bB B2 -> bD B - 1 <= bD B2 ->
fsaved F F2 -> (frm0 fc -> frm0 fc2) ->
AJ5 A4L HIx A2 T md2
(Q1Y6.Mq2.pe_msE pf pa 0x95560 (Z_to_bv 64 (pf_tk pf / 8 + 2147450884)) gp' t0' t1' t2' (Z_to_bv 64 r) (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts) + 16)) a2' a3' a4' a5' a6' a7'
(Z_to_bv 64 (pf_tk pf / 8 + 2147450882)) (Z_to_bv 64 (pf_tk pf + 20)) (Z_to_bv 64 (pf_tk pf / 8 + 2147450887)) s6 (Z_to_bv 64 (pf_tk pf + 32)) (Z_to_bv 64 (pa_F pa)) (Z_to_bv 64 (pf_tk pf + 56))
s11 (Z_to_bv 64 (pf_tk pf + 64)) (Z_to_bv 64 (pa_F pa + 64)) (Z_to_bv 64 (pf_tk pf / 8 + 2147450888)) (Z_to_bv 64 (pf_lenr pf)) F2 fc2 m2)) ->
AJ5 A4L HIx A T md
(Q1Y6.Mq2.pe_msE pf pa 0x95618 x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (pf_tk pf / 8 + 2147450882)) (Z_to_bv 64 (pf_tk pf + 20)) (Z_to_bv 64 (pf_tk pf / 8 + 2147450887)) s6 (Z_to_bv 64 (pf_tk pf + 32)) (Z_to_bv 64 (pa_F pa)) (Z_to_bv 64 (pf_tk pf + 56))
s11 (Z_to_bv 64 (pf_tk pf + 64)) t4 (Z_to_bv 64 (pf_tk pf / 8 + 2147450888)) t6 F fc m).
Proof.
intros until fc. intros STC BSL DSL NX PBK BK Hl Hst Kjoin.
destruct NX as (f1a & f1b & f2a & f2c & f2e & endw & n64 & nu64 & INVX). pose proof INVX as INVX0.
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
destruct INVX as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FRX).
pose proof REST as (HP & LV & OBJ & _).
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
pose proof FRX as (SLOTS & _ & _ & FFX & _). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS. unfold num_ffc in FFX.
unfold Q1Y6.Mq2.pe_msE in *.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
set (PF := PEF tk oldl newl len lenr sb spf pmd mxd fl) in *. set (PA := PEFA sp0 Ff oldloc newloc bsl dsl) in *.
pose proof (LV depth l Hl) as LVd. pose proof LVd as (ST26 & SS26 & _ & Md).
rewrite Nat.ltb_irrefl, Nat.eqb_refl in Md. destruct Md as (c0 & hn0 & Hmode & CLS0 & NM0).
destruct (number_mode_ss _ _ _ SS26 ltac:(rewrite <- Hst; exact Hmode)) as (Ec0 & Ehn0 & Ess). subst c0 hn0.
cbn [name_ok] in NM0. destruct NM0 as [Hn0 Hnbs0].
assert (Ecs : tl_cs l = None) by (destruct (tl_cs l); [exfalso; exact CLS0 | reflexivity]).
pose proof (LV depth l Hl) as (_ & _ & JO & _). rewrite Ecs in JO. cbn [jopt] in JO. destruct JO as [Ecur Ecbs].
assert (Eobjbs : objbs = []).
{ unfold cur_st in OBJ. cbn [t_levels t_depth t_objbs ts0] in OBJ. rewrite Hl, Hst in OBJ. exact OBJ. }
pose proof (PE_WINX_open HIx GA PF PA q LB0 LM FRS payload me lo m md A B ts0 errv l _ INVX0 Hl Hn0 Hnbs0 Eobjbs) as WIN0.
rewrite Ecur, Ecs, Ecbs in WIN0.
set (lw0 := TL (tl_st l) (tl_ss l) 0 None [] 0 []) in *. set (tw0 := ts_lvl ts0 lw0) in *.
assert (PBK0 : PBOKat m tw0 kP) by (exact (PBOKat_same m ts0 tw0 _ eq_refl eq_refl PBK)).
pose proof (BOK_afford PF PA ts0 B nB newint_costB BSL BK ltac:(pose proof (K_ev_pos PF); unfold newint_costB; lia)) as COST.
assert (COSTD : 1 <= bD B) by (destruct BK as (_ & HD & _); cbn [pa_dslack PA] in HD; lia).
pose proof (TSK depth l Hl) as Ld. remember (q + 32 * Z.of_nat depth) as bse eqn:Hbse in Ld.
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8, A_SB in *.
clear REST LV OBJ PB TSK Ld.
reenterA asegs A4L HIx asegs_wx HP.
step.
evt_done5.
eapply (pe_new_int_wX HIx GA GA_pres 0x9c9d4 NEWUINT PF PA q LB0 LM FRS payload me lo m md A B tw0 nb pj sv errv T kP
(num_ffc cb (pj_fhd pj) f1a f1b f2a f2c f2e endw n64 nu64) (ffsh_cells (FSHN 0xf8)));
[ exact STC | exact WIN0 | cbn; lia | cbn; lia | exact PBK0 | exact COST | exact COSTD | rewrite unsigned_lit by lia; reflexivity |].
intros m2 md2 A2 B2 errv2 r w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 F2 fc2 OUT2 PBK2 HB2 HD2 FS2 FRM2.
cbn [pf_spf pa_sp0 pa_F PF PA] in *. unfold A_TP in *.
assert (WR2 : NUM_WINR PF PA q LB0 LM FRS payload me lo m2 md2 A2 B2 tw0 r Sint (Z.max 20 (kP + 16)) cb nb pj sv errv2).
{ destruct OUT2 as [(-> & W) | (Hr & BS & LEN3 & JF & Rr & W)].
- left. split; [reflexivity|]. exists f1a, f1b, f2a, f2c, f2e, endw, n64, nu64. exact W.
- right. split; [exact Hr|]. exists BS. split; [lia|]. split; [exists 20; split; [exact JF | lia]|]. split; [exact Rr|]. exists f1a, f1b, f2a, f2c, f2e, endw, n64, nu64. exact W. }
assert (COMMON : exists p2 s2 BS2, PE_WINX HIx GA PF PA q LB0 LM FRS payload me lo m2 md2 A2 B2 tw0 p2 s2 BS2 1 errv2
(pe_frameAX m2 PF PA nb pj sv (num_ffc cb (pj_fhd pj) f1a f1b f2a f2c f2e endw n64 nu64) (ffsh_cells (FSHN 0xf8))))
by (destruct OUT2 as [(_ & W) | (_ & BS & _ & _ & _ & W)]; eauto).
destruct COMMON as (p2 & s2 & BS2 & WIN2). clear OUT2.
clear TOK SLOTS FFX HP WIN0 PBK0 INVX0 FRX PBK.
pose proof WIN2 as (CORE2 & BASE2 & _). destruct CORE2 as (_ & _ & _ & _ & TOK & _ & _ & _ & FRX2). pose proof (proj1 BASE2) as HP. clear BASE2 WIN2.
unfold tw0, ts_lvl, ts0 in TOK. cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_tk pf_mxd pf_fl PF] in TOK.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
destruct FRX2 as (SLOTS & _). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc PF PA] in SLOTS.
assert (INtk : In (tk, 72) (pe_blocksA PF q LB0 (tsF tw0 BS2))) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * mxd) (pe_blocksA PF q LB0 (tsF tw0 BS2))) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t2.
blk_factsA A4L HIx HP q (32 * mxd) Hqal Hqlo Hqhi Himg_q2.
assert (Hb8 : bse mod 8 = 0) by (subst bse; clear - Hqal; Z.div_mod_to_equations; lia).
shq_facts HP INq INtk q mxd tk (Z.of_nat depth) 2 SHQ2 SEPQ2c SEPQ2q SEPQ2t.
replace (q / 8 + 4 * (Z.of_nat depth) + 2 + A_SB) with (bse / 8 + 2147450882) in SHQ2 by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia).
clear SEPQ2c SEPQ2q SEPQ2t.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 7 HP INtk ltac:(lia)) as SHT7.
replace (tk / 8 + 7 + A_SB) with (tk / 8 + 2147450887) in SHT7 by (unfold A_SB; lia).
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 2 HP INtk ltac:(lia)) as SHT2.
replace (tk / 8 + 2 + A_SB) with (tk / 8 + 2147450882) in SHT2 by (unfold A_SB; lia).
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8, A_SB in *.
stash Himg_t2. stash Himg_q2. stash WR2.
replace (ret_pc (Z_to_bv 64 611868)) with (Z_to_bv 64 611868) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
reenterA asegs A4L HIx asegs_wx HP.
asan_rechkA.
asan_rechkM 4.
step.
norm_sx32.
step.
rewrite (unsigned_lit (Z.of_nat depth)) by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32.
step.
replace (q + Z.of_nat depth * 32) with bse by lia.
step.
asan_chkM 2.
evt_done5. unstash WR2.
replace (q + 32 * Z.of_nat depth + 16) with (bse + 16) in Kjoin by lia.
eapply (Kjoin m2 md2 A2 B2 errv2 r); [exact WR2 | exact PBK2 | exact HB2 | exact HD2 | exact FS2 | exact FRM2].
Qed.

Lemma num_newint2_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP : Z) (nB : nat)
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s11 t4 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa -> 0 <= pa_dslack pa ->
NUM_INVX pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv 0xf8 ->
PBOKat m ts kP -> BOK pf pa ts B (S (Z.to_nat (16 * Z.max 0 (pf_len pf) + 8192) + nB)) ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_number ->
(forall m2 md2 A2 B2 errv2 (r : Z) gp' t0' t1' t2' a2' a3' a4' a5' a6' a7' F2 fc2,
NUM_WINR pf pa q LB0 LM FRS payload me lo m2 md2 A2 B2 (ts_lvl ts (TL (tl_st l) (tl_ss l) 0 None [] 0 [])) r Sint (Z.max 20 (kP + 16)) cb nb pj sv errv2 ->
PBOKat m2 (ts_lvl ts (TL (tl_st l) (tl_ss l) 0 None [] 0 [])) kP ->
bB B - newint_costB <= bB B2 -> bD B - 1 <= bD B2 ->
fsaved F F2 -> (frm0 fc -> frm0 fc2) ->
AJ5 A4L HIx A2 T md2
(Q1Y6.Mq2.pe_msE pf pa 0x95560 (Z_to_bv 64 (pf_tk pf / 8 + 2147450884)) gp' t0' t1' t2' (Z_to_bv 64 r) (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts) + 16)) a2' a3' a4' a5' a6' a7'
(Z_to_bv 64 (pf_tk pf / 8 + 2147450882)) (Z_to_bv 64 (pf_tk pf + 20)) (Z_to_bv 64 (pf_tk pf / 8 + 2147450887)) s6 (Z_to_bv 64 (pf_tk pf + 32)) (Z_to_bv 64 (pa_F pa)) (Z_to_bv 64 (pf_tk pf + 56))
s11 (Z_to_bv 64 (pf_tk pf + 64)) (Z_to_bv 64 (pa_F pa + 64)) (Z_to_bv 64 (pf_tk pf / 8 + 2147450888)) (Z_to_bv 64 (pf_lenr pf)) F2 fc2 m2)) ->
AJ5 A4L HIx A T md
(Q1Y6.Mq2.pe_msE pf pa 0x955c4 x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (pf_tk pf / 8 + 2147450882)) (Z_to_bv 64 (pf_tk pf + 20)) (Z_to_bv 64 (pf_tk pf / 8 + 2147450887)) s6 (Z_to_bv 64 (pf_tk pf + 32)) (Z_to_bv 64 (pa_F pa)) (Z_to_bv 64 (pf_tk pf + 56))
s11 (Z_to_bv 64 (pf_tk pf + 64)) t4 (Z_to_bv 64 (pf_tk pf / 8 + 2147450888)) t6 F fc m).
Proof.
intros until fc. intros STC BSL DSL NX PBK BK Hl Hst Kjoin.
destruct NX as (f1a & f1b & f2a & f2c & f2e & endw & n64 & nu64 & INVX). pose proof INVX as INVX0.
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
destruct INVX as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FRX).
pose proof REST as (HP & LV & OBJ & _).
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
pose proof FRX as (SLOTS & _ & _ & FFX & _). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS. unfold num_ffc in FFX.
unfold Q1Y6.Mq2.pe_msE in *.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
set (PF := PEF tk oldl newl len lenr sb spf pmd mxd fl) in *. set (PA := PEFA sp0 Ff oldloc newloc bsl dsl) in *.
pose proof (LV depth l Hl) as LVd. pose proof LVd as (ST26 & SS26 & _ & Md).
rewrite Nat.ltb_irrefl, Nat.eqb_refl in Md. destruct Md as (c0 & hn0 & Hmode & CLS0 & NM0).
destruct (number_mode_ss _ _ _ SS26 ltac:(rewrite <- Hst; exact Hmode)) as (Ec0 & Ehn0 & Ess). subst c0 hn0.
cbn [name_ok] in NM0. destruct NM0 as [Hn0 Hnbs0].
assert (Ecs : tl_cs l = None) by (destruct (tl_cs l); [exfalso; exact CLS0 | reflexivity]).
pose proof (LV depth l Hl) as (_ & _ & JO & _). rewrite Ecs in JO. cbn [jopt] in JO. destruct JO as [Ecur Ecbs].
assert (Eobjbs : objbs = []).
{ unfold cur_st in OBJ. cbn [t_levels t_depth t_objbs ts0] in OBJ. rewrite Hl, Hst in OBJ. exact OBJ. }
pose proof (PE_WINX_open HIx GA PF PA q LB0 LM FRS payload me lo m md A B ts0 errv l _ INVX0 Hl Hn0 Hnbs0 Eobjbs) as WIN0.
rewrite Ecur, Ecs, Ecbs in WIN0.
set (lw0 := TL (tl_st l) (tl_ss l) 0 None [] 0 []) in *. set (tw0 := ts_lvl ts0 lw0) in *.
assert (PBK0 : PBOKat m tw0 kP) by (exact (PBOKat_same m ts0 tw0 _ eq_refl eq_refl PBK)).
pose proof (BOK_afford PF PA ts0 B nB newint_costB BSL BK ltac:(pose proof (K_ev_pos PF); unfold newint_costB; lia)) as COST.
assert (COSTD : 1 <= bD B) by (destruct BK as (_ & HD & _); cbn [pa_dslack PA] in HD; lia).
pose proof (TSK depth l Hl) as Ld. remember (q + 32 * Z.of_nat depth) as bse eqn:Hbse in Ld.
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8, A_SB in *.
clear REST LV OBJ PB TSK Ld.
reenterA asegs A4L HIx asegs_wx HP.
step.
evt_done5.
eapply (pe_new_int_wX HIx GA GA_pres 0x9c330 NEWINT PF PA q LB0 LM FRS payload me lo m md A B tw0 nb pj sv errv T kP
(num_ffc cb (pj_fhd pj) f1a f1b f2a f2c f2e endw n64 nu64) (ffsh_cells (FSHN 0xf8)));
[ exact STC | exact WIN0 | cbn; lia | cbn; lia | exact PBK0 | exact COST | exact COSTD | rewrite unsigned_lit by lia; reflexivity |].
intros m2 md2 A2 B2 errv2 r w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 F2 fc2 OUT2 PBK2 HB2 HD2 FS2 FRM2.
cbn [pf_spf pa_sp0 pa_F PF PA] in *. unfold A_TP in *.
assert (WR2 : NUM_WINR PF PA q LB0 LM FRS payload me lo m2 md2 A2 B2 tw0 r Sint (Z.max 20 (kP + 16)) cb nb pj sv errv2).
{ destruct OUT2 as [(-> & W) | (Hr & BS & LEN3 & JF & Rr & W)].
- left. split; [reflexivity|]. exists f1a, f1b, f2a, f2c, f2e, endw, n64, nu64. exact W.
- right. split; [exact Hr|]. exists BS. split; [lia|]. split; [exists 20; split; [exact JF | lia]|]. split; [exact Rr|]. exists f1a, f1b, f2a, f2c, f2e, endw, n64, nu64. exact W. }
assert (COMMON : exists p2 s2 BS2, PE_WINX HIx GA PF PA q LB0 LM FRS payload me lo m2 md2 A2 B2 tw0 p2 s2 BS2 1 errv2
(pe_frameAX m2 PF PA nb pj sv (num_ffc cb (pj_fhd pj) f1a f1b f2a f2c f2e endw n64 nu64) (ffsh_cells (FSHN 0xf8))))
by (destruct OUT2 as [(_ & W) | (_ & BS & _ & _ & _ & W)]; eauto).
destruct COMMON as (p2 & s2 & BS2 & WIN2). clear OUT2.
clear TOK SLOTS FFX HP WIN0 PBK0 INVX0 FRX PBK.
pose proof WIN2 as (CORE2 & BASE2 & _). destruct CORE2 as (_ & _ & _ & _ & TOK & _ & _ & _ & FRX2). pose proof (proj1 BASE2) as HP. clear BASE2 WIN2.
unfold tw0, ts_lvl, ts0 in TOK. cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_tk pf_mxd pf_fl PF] in TOK.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
destruct FRX2 as (SLOTS & _). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc PF PA] in SLOTS.
assert (INtk : In (tk, 72) (pe_blocksA PF q LB0 (tsF tw0 BS2))) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * mxd) (pe_blocksA PF q LB0 (tsF tw0 BS2))) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t2.
blk_factsA A4L HIx HP q (32 * mxd) Hqal Hqlo Hqhi Himg_q2.
assert (Hb8 : bse mod 8 = 0) by (subst bse; clear - Hqal; Z.div_mod_to_equations; lia).
shq_facts HP INq INtk q mxd tk (Z.of_nat depth) 2 SHQ2 SEPQ2c SEPQ2q SEPQ2t.
replace (q / 8 + 4 * (Z.of_nat depth) + 2 + A_SB) with (bse / 8 + 2147450882) in SHQ2 by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia).
clear SEPQ2c SEPQ2q SEPQ2t.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 7 HP INtk ltac:(lia)) as SHT7.
replace (tk / 8 + 7 + A_SB) with (tk / 8 + 2147450887) in SHT7 by (unfold A_SB; lia).
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 2 HP INtk ltac:(lia)) as SHT2.
replace (tk / 8 + 2 + A_SB) with (tk / 8 + 2147450882) in SHT2 by (unfold A_SB; lia).
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8, A_SB in *.
stash Himg_t2. stash Himg_q2. stash WR2.
replace (ret_pc (Z_to_bv 64 611784)) with (Z_to_bv 64 611784) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
reenterA asegs A4L HIx asegs_wx HP.
asan_rechkA.
asan_rechkM 4.
step.
norm_sx32.
step.
rewrite (unsigned_lit (Z.of_nat depth)) by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32.
step.
replace (q + Z.of_nat depth * 32) with bse by lia.
step.
asan_chkM 2.
evt_done5. unstash WR2.
replace (q + 32 * Z.of_nat depth + 16) with (bse + 16) in Kjoin by lia.
eapply (Kjoin m2 md2 A2 B2 errv2 r); [exact WR2 | exact PBK2 | exact HB2 | exact HD2 | exact FS2 | exact FRM2].
Qed.

Lemma num_udisp_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet)
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s11 t4 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo ->
NUM_INVX pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv 0xf8 ->
(forall a0',
AJ5 A4L HIx A T md
(Q1Y6.Mq2.pe_msE pf pa 0x95618 x1 gp t0 t1 t2 a0' a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (pf_tk pf / 8 + 2147450882)) (Z_to_bv 64 (pf_tk pf + 20)) (Z_to_bv 64 (pf_tk pf / 8 + 2147450887)) s6 (Z_to_bv 64 (pf_tk pf + 32)) (Z_to_bv 64 (pa_F pa)) (Z_to_bv 64 (pf_tk pf + 56))
s11 (Z_to_bv 64 (pf_tk pf + 64)) t4 (Z_to_bv 64 (pf_tk pf / 8 + 2147450888)) t6 F fc m)) ->
(forall m' a0' a1',
NUM_INVX pf pa q LB0 LM FRS payload me lo m' md A B ts cb nb pj sv errv 0xf8 ->
(forall b, PBOKat m ts b -> PBOKat m' ts b) ->
AJ5 A4L HIx A T md
(Q1Y6.Mq2.pe_msE pf pa 0x955c4 x1 gp t0 t1 t2 a0' a1' a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (pf_tk pf / 8 + 2147450882)) (Z_to_bv 64 (pf_tk pf + 20)) (Z_to_bv 64 (pf_tk pf / 8 + 2147450887)) s6 (Z_to_bv 64 (pf_tk pf + 32)) (Z_to_bv 64 (pa_F pa)) (Z_to_bv 64 (pf_tk pf + 56))
s11 (Z_to_bv 64 (pf_tk pf + 64)) t4 (Z_to_bv 64 (pf_tk pf / 8 + 2147450888)) t6 F fc m')) ->
AJ5 A4L HIx A T md
(Q1Y6.Mq2.pe_msE pf pa 0x955b0 x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (pf_tk pf / 8 + 2147450882)) (Z_to_bv 64 (pf_tk pf + 20)) (Z_to_bv 64 (pf_tk pf / 8 + 2147450887)) s6 (Z_to_bv 64 (pf_tk pf + 32)) (Z_to_bv 64 (pa_F pa)) (Z_to_bv 64 (pf_tk pf + 56))
s11 (Z_to_bv 64 (pf_tk pf + 64)) t4 (Z_to_bv 64 (pf_tk pf / 8 + 2147450888)) t6 F fc m).
Proof.
intros until fc. intros STC NX Ku64 Ki64.
destruct NX as (f1a & f1b & f2a & f2c & f2e & endw & n64 & nu64 & INVX). pose proof INVX as INVX0.
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
destruct INVX as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FRX).
pose proof REST as (HP & _).
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
pose proof FRX as FRX0. destruct FRX as (SLOTS & GAP & SAVED & FFX & FSH). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS.
unfold num_ffc in FFX. unfold ffsh_cells, FSHN in FSH. cbn [map] in FSH.
unfold Q1Y6.Mq2.pe_msE in *.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
set (PF := PEF tk oldl newl len lenr sb spf pmd mxd fl) in *. set (PA := PEFA sp0 Ff oldloc newloc bsl dsl) in *.
assert (INtk : In (tk, 72) (pe_blocksA PF q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t.
assert (INF : In (Ff, 2) ((Ff, 2) :: FRS)) by (left; reflexivity).
pose proof alloc_ceiling_range as ACR.
assert (GF0' : 0 <= Ff) by lia. assert (GFc' : Ff < alloc_ceiling) by lia.
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP INF (in_or_app _ LM _ (or_introl INtk))) as DFt. rewrite fr_size_2 in DFt.
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP INF) as DSF. rewrite fr_size_2 in DSF. cbn [hl_sb A4L] in DSF.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(tk, tk + 72); (Ff, Ff + 248); (Ff / 8 + 2147450880, Ff / 8 + 2147450880 + 32)] m) as MU.
assert (HW : Forall (pe_wtfA PF PA) [(tk, tk + 72); (Ff, Ff + 248); (Ff / 8 + 2147450880, Ff / 8 + 2147450880 + 32)]).
{ apply Forall_cons; [left; cbn [fst snd pf_tk PF]; lia |]. apply Forall_cons; [right; right; left; cbn [fst snd pa_F PA]; lia |].
apply Forall_cons; [| apply Forall_nil]. right; right; right. cbn [fst snd pa_F PA]. unfold shA, A_SB. lia. }
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8, A_SB in *.
stash Himg_t. stash Ku64. stash Ki64. stash INVX0. stash FRX0. stash GAP. stash SAVED. stash TSK. stash REST. stash PB.
reenterA asegs A4L HIx asegs_wx HP.
step.
step.
step.
destruct (Z_lt_dec (bv_signed nu64) 0) as [NEG | POS].
{ if_truex. evt_done5. unstash Ku64. apply Ku64. }
if_falsex.
step.
stepz.
unstash INVX0. unstash FRX0.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, FFc : rw_cells asegs mc Ff ?ffc, FSHc : rw_cells asegs mc (Ff / 8 + 2147450880) ?shc |- _ =>
evt_done5;
assert (FRXc : pe_frameAX mc PF PA nb pj sv (num_ffc cb (pj_fhd pj) f1a f1b f2a f2c f2e endw nu64 nu64) (ffsh_cells (FSHN 0xf8)))
by (eapply (pe_frameAX_write HIx PF PA q LB0 LM FRS B ts0 A m mc md lo nb pj sv); [exact STC | exact HP | exact FRX0 | exact MUc | exact WMc | exact FFc | exact FSHc]);
destruct (PE_INV_AX_tokw HIx GA GA_outside PF PA q LB0 LM FRS payload me lo m mc md A B ts0 errv _ co (t_x ts0) _ _ STC INVX0 MUc WMc MIc HW TOKc FRXc
ltac:(unfold PF; cbn [pf_len]; lia) eq_refl) as [INVX1 PBKX1]
end end.
unstash Ki64. eapply Ki64; [exists f1a, f1b, f2a, f2c, f2e, endw, nu64, nu64; exact INVX1 | exact PBKX1].
Qed.

Lemma num_dbl_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP : Z)
(x1 gp t0 t1 t2 a0 a1 a2 a3 a5 a6 a7 s3 s6 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> frm0 fc ->
NUM_INVX pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv 0xf8 ->
PBOKat m ts kP ->
(forall m' errv' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' s4' t3' t4' t5' t6' F' fc',
NUM_INVX pf pa q LB0 LM FRS payload me lo m' md A B ts cb nb pj sv errv' 0xf8 -> PBOKat m' ts kP ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A T md
(Q1Y6.Mq2.pe_msE pf pa 0x953bc x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' s4' (Z_to_bv 64 (pf_tk pf / 8 + 2147450887)) s6 (Z_to_bv 64 (pf_tk pf + 32)) (Z_to_bv 64 (pa_F pa)) (Z_to_bv 64 (pf_tk pf + 56))
(Z_to_bv 64 (pa_F pa + 32)) t3' t4' t5' t6' F' fc' m')) ->
(forall m' errv' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' s4' t3' t4' t5' t6' F' fc',
NUM_INVX pf pa q LB0 LM FRS payload me lo m' md A B ts cb nb pj sv errv' 0xf8 ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A T md
(Q1Y6.Mq2.pe_msE pf pa 0x98480 x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' s4' (Z_to_bv 64 (pf_tk pf / 8 + 2147450887)) s6 (Z_to_bv 64 (pf_tk pf + 32)) (Z_to_bv 64 (pa_F pa)) (Z_to_bv 64 (pf_tk pf + 56))
(Z_to_bv 64 (pa_F pa + 32)) t3' t4' t5' t6' F' fc' m')) ->
AJ5 A4L HIx A T md
(Q1Y6.Mq2.pe_msE pf pa 0x95350 x1 gp t0 t1 t2 a0 a1 a2 a3 (Z_to_bv 64 (pf_tk pf + 8)) a5 a6 a7
s3 (Z_to_bv 64 (pf_tk pf + 20)) (Z_to_bv 64 (pf_tk pf / 8 + 2147450887)) s6 (Z_to_bv 64 (pf_tk pf + 32)) (Z_to_bv 64 (pa_F pa)) (Z_to_bv 64 (pf_tk pf + 56))
(Z_to_bv 64 (pf_tk pf / 8 + 2147450881)) t3 t4 t5 t6 F fc m).
Proof.
intros until fc. intros STC FRM NX PBK Kds Kerr.
destruct NX as (f1a & f1b & f2a & f2c & f2e & endw & n64 & nu64 & INVX). pose proof INVX as INVX0.
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
destruct INVX as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FRX).
pose proof REST as (HP & _).
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
pose proof FRX as FRX0. destruct FRX as (SLOTS & GAP & SAVED & FFX & FSH). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS.
unfold num_ffc in FFX. unfold ffsh_cells, FSHN in FSH. cbn [map] in FSH.
unfold Q1Y6.Mq2.pe_msE in *.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
set (PF := PEF tk oldl newl len lenr sb spf pmd mxd fl) in *. set (PA := PEFA sp0 Ff oldloc newloc bsl dsl) in *.
assert (INtk : In (tk, 72) (pe_blocksA PF q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 1 HP INtk ltac:(lia)) as SHT1.
replace (tk / 8 + 1 + A_SB) with (tk / 8 + 2147450881) in SHT1 by (unfold A_SB; lia).
pose proof PBK as (buf & bpos & cap & pre & post & Epbs & Lpre & CORE1 & Hbk). cbn [t_pbs t_pb ts0] in Epbs, CORE1. destruct CORE1 as (Hbp & Hcap & Hlen & PBC & BUFC).
assert (INpb : In (pb, PB_SZ) (pe_blocksA PF q LB0 ts0)) by (unfold pe_blocksA, tstate_blocks, ts0; cbn [t_pbs]; rewrite Epbs; apply in_or_app; left; left; reflexivity).
blk_factsA A4L HIx HP pb 16 Hpal Hplo Hphi Himg_p.
pose proof (blk_granA HIx _ _ _ _ _ _ _ pb 16 0 HP INpb ltac:(lia) ltac:(lia)) as SHP0.
replace (pb / 8 + 0 + A_SB) with (pb / 8 + 2147450880) in SHP0 by (unfold A_SB; lia).
pose proof (blk_granA HIx _ _ _ _ _ _ _ pb 16 1 HP INpb ltac:(lia) ltac:(lia)) as SHP1.
replace (pb / 8 + 1 + A_SB) with (pb / 8 + 2147450881) in SHP1 by (unfold A_SB; lia).
assert (INF : In (Ff, 2) ((Ff, 2) :: FRS)) by (left; reflexivity).
pose proof alloc_ceiling_range as ACR.
assert (GF0' : 0 <= Ff) by lia. assert (GFc' : Ff < alloc_ceiling) by lia.
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP INF (in_or_app _ LM _ (or_introl INtk))) as DFt. rewrite fr_size_2 in DFt.
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP INF) as DSF. rewrite fr_size_2 in DSF. cbn [hl_sb A4L] in DSF.
pose proof (shadow_blk_apart HIx _ _ _ _ _ _ _ _ _ Ff 32 HP (in_or_app _ LM _ (or_introl INtk)) GF0' GFc' ltac:(lia)) as DSt. unfold shA, A_SB in DSt.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(tk, tk + 72); (Ff, Ff + 248); (Ff / 8 + 2147450880, Ff / 8 + 2147450880 + 32)] m) as MU.
assert (HW : Forall (pe_wtfA PF PA) [(tk, tk + 72); (Ff, Ff + 248); (Ff / 8 + 2147450880, Ff / 8 + 2147450880 + 32)]).
{ apply Forall_cons; [left; cbn [fst snd pf_tk PF]; lia |]. apply Forall_cons; [right; right; left; cbn [fst snd pa_F PA]; lia |].
apply Forall_cons; [| apply Forall_nil]. right; right; right. cbn [fst snd pa_F PA]. unfold shA, A_SB. lia. }
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8, A_SB in *.
stash Himg_t. stash Himg_p. stash Kds. stash Kerr. stash INVX0. stash FRX0. stash GAP. stash SAVED. stash TSK. stash REST. stash PB. stash BUFC.
reenterA asegs A4L HIx asegs_wx HP.
asan_rechkA.
step.
asan_chkA.
step.
asan_chkM 1.
step.
norm_sx32.
stepz.
step.
step.
step.
step.

unstash INVX0. unstash FRX0.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, FFc : rw_cells asegs mc Ff ?ffc, FSHc : rw_cells asegs mc (Ff / 8 + 2147450880) ?shc |- _ =>
evt_done5;
assert (FRXc : pe_frameAX mc PF PA nb pj sv (num_ffc cb (pj_fhd pj) f1a f1b f2a f2c f2e endw n64 nu64) (ffsh_cells (FSHN 0)))
by (eapply (pe_frameAX_write HIx PF PA q LB0 LM FRS B ts0 A m mc md lo nb pj sv); [exact STC | exact HP | exact FRX0 | exact MUc | exact WMc | exact FFc | exact FSHc]);
destruct (PE_INV_AX_tokw HIx GA GA_outside PF PA q LB0 LM FRS payload me lo m mc md A B ts0 errv _ co (t_x ts0) _ _ STC INVX0 MUc WMc MIc HW TOKc FRXc
ltac:(unfold PF; cbn [pf_len]; lia) eq_refl) as [INVX1 PBKX1];
eapply (pe_strtod_cX HIx GA GA_pres STRTOD PF PA q LB0 LM FRS payload me lo mc md A B ts0 nb pj sv errv T kP buf cap (Ff + 32) endw
[CB 24 (pj_fhd pj); CB 8 f1a] [CB 24 f1b; C1 cb; CB 79 f2a; C8 n64; CB 24 f2c; C8 nu64; CB 64 f2e] (ffsh_cells (FSHN 0)));
[ exact STC | exact INVX1 | exact (PBKX1 _ PBK) | exact Epbs | reflexivity | reflexivity | reflexivity | clear - GF; Z.div_mod_to_equations; lia | exact FRM
| rewrite unsigned_lit by lia; reflexivity | ]
end end.
intros m2 errv2 a0' v w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 F2 fc2 INVX2 PBK2 FS2 FRM2.
cbn [pf_spf pa_sp0 pa_F PF PA] in *. unfold A_TP in *.
try clear TOK; try clear SLOTS; try clear FFX; try clear FSH; try clear MU; try clear WM; try clear MI; try clear INVX0; try clear FRX0; try clear SHT1; try clear SHP0; try clear SHP1; try clear PBC; try clear FRXc; try clear INVX1; try clear PBKX1; clear HP.
pose proof INVX2 as [CORE2 REST2]. destruct CORE2 as (_ & _ & _ & _ & TOK & _ & _ & _ & FRX2). pose proof (proj1 REST2) as HP. clear REST2.
unfold ts0 in TOK. cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_tk pf_mxd pf_fl PF] in TOK.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
pose proof FRX2 as (SLOTS & _ & _ & FFX & FSH). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc PF PA app] in SLOTS, FFX.
unfold ffsh_cells, FSHN in FSH. cbn [map] in FSH. cbn [pa_F PA] in FSH.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs m2) as WM.
pose proof (munch_refl [(tk, tk + 72); (Ff, Ff + 248); (Ff / 8 + 2147450880, Ff / 8 + 2147450880 + 32)] m2) as MU.
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8, A_SB in *.
stash INVX2. stash FRX2. stash PBK2.
replace (ret_pc (Z_to_bv 64 611236)) with (Z_to_bv 64 611236) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
reenterA asegs A4L HIx asegs_wx HP.
step.
step.
step.
stepz.
unstash INVX2. unstash FRX2. unstash PBK2.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m2 mc, WMc : wmono asegs m2 mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, FFc : rw_cells asegs mc Ff ?ffc, FSHc : rw_cells asegs mc (Ff / 8 + 2147450880) ?shc |- _ =>
assert (FRXc : pe_frameAX mc PF PA nb pj sv (num_ffc cb (pj_fhd pj) f1a f1b f2a f2c f2e v n64 nu64) (ffsh_cells (FSHN 0xf8)))
by (eapply (pe_frameAX_write HIx PF PA q LB0 LM FRS B ts0 A m2 mc md lo nb pj sv); [exact STC | exact HP | exact FRX2 | exact MUc | exact WMc | exact FFc | exact FSHc]);
destruct (PE_INV_AX_tokw HIx GA GA_outside PF PA q LB0 LM FRS payload me lo m2 mc md A B ts0 errv2 _ co (t_x ts0) _ _ STC INVX2 MUc WMc MIc HW TOKc FRXc
ltac:(unfold PF; cbn [pf_len]; lia) eq_refl) as [INVX3 PBKX3]
end end.
assert (NX3 : NUM_INVX PF PA q LB0 LM FRS payload me lo _ md A B ts0 cb nb pj sv errv2 0xf8) by (exists f1a, f1b, f2a, f2c, f2e, v, n64, nu64; exact INVX3).
step.
lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => destruct c end; cbv iota.
- evt_done5. unstash Kds. eapply Kds; [exact NX3 | exact (PBKX3 _ PBK2) | exact FS2 | exact FRM2].
- step.
evt_done5. unstash Kerr. eapply Kerr; [exact NX3 | exact FS2 | exact FRM2].
Qed.

Lemma num_dbls_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP v2 ra2 : Z) (nB : nat)
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s6 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa -> 0 <= pa_dslack pa ->
NUM_INVX pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv 0xf8 ->
PBOKat m ts kP -> BOK pf pa ts B (S (Z.to_nat (16 * Z.max 0 (pf_len pf) + 8192) + nB)) ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_number ->
pj_16 pj = Z_to_bv 64 (pf_tk pf / 8 + 2147450881) -> 0 <= kP <= pf_len pf ->
pe_s0 sv = Z_to_bv 64 v2 -> pe_ra sv = Z_to_bv 64 ra2 ->
(v2 < alloc_ceiling \/ v2 mod 8 <> 0 \/ v2 <= pa_sp0 pa \/ hiA_top A4L HIx - 16 <= v2) /\ 0 <= v2 < 2^64 ->
uw_ok A4L (hl_malloc A4H) (Z_to_bv 64 0x9daec) (UWfp ra2 v2) ->
(forall m2 md2 A2 B2 errv2 (r : Z) gp' t0' t1' t2' a2' a3' a4' a5' a6' a7' F2 fc2,
NUM_WINR pf pa q LB0 LM FRS payload me lo m2 md2 A2 B2 (ts_lvl ts (TL (tl_st l) (tl_ss l) 0 None [] 0 [])) r (Sdouble true) (Z.max 20 (kP + 16)) cb nb pj sv errv2 ->
PBOKat m2 (ts_lvl ts (TL (tl_st l) (tl_ss l) 0 None [] 0 [])) kP ->
bB B - newdbls_costB kP <= bB B2 -> bD B - 1 <= bD B2 ->
fsaved F F2 -> (frm0 fc -> frm0 fc2) ->
AJ5 A4L HIx A2 T md2
(Q1Y6.Mq2.pe_msE pf pa 0x95448 (Z_to_bv 64 (pf_tk pf / 8 + 2147450884)) gp' t0' t1' t2' (Z_to_bv 64 r) (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts) + 16)) a2' a3' a4' a5' a6' a7'
(Z_to_bv 64 (pf_tk pf / 8 + 2147450882)) (Z_to_bv 64 (pf_tk pf + 20)) (Z_to_bv 64 (pf_tk pf / 8 + 2147450887)) s6 (Z_to_bv 64 (pf_tk pf + 32)) (Z_to_bv 64 (pa_F pa)) (Z_to_bv 64 (pf_tk pf + 56))
s11 (Z_to_bv 64 (pf_tk pf + 64)) (Z_to_bv 64 (pa_F pa + 64)) (Z_to_bv 64 (pf_tk pf / 8 + 2147450888)) (Z_to_bv 64 (pf_lenr pf)) F2 fc2 m2)) ->
AJ5 A4L HIx A T md
(Q1Y6.Mq2.pe_msE pf pa 0x953bc x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7
s3 s4 (Z_to_bv 64 (pf_tk pf / 8 + 2147450887)) s6 (Z_to_bv 64 (pf_tk pf + 32)) (Z_to_bv 64 (pa_F pa)) (Z_to_bv 64 (pf_tk pf + 56))
s11 t3 t4 t5 t6 F fc m).
Proof.
intros until fc. intros STC BSL DSL NX PBK BK Hl Hst P16 HkP S0V RAV HV UWK Kjoin.
destruct NX as (f1a & f1b & f2a & f2c & f2e & endw & n64 & nu64 & INVX). pose proof INVX as INVX0.
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
destruct INVX as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FRX).
pose proof REST as (HP & LV & OBJ & _).
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
pose proof FRX as (SLOTS & _ & _ & FFX & _). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS. unfold num_ffc in FFX. rewrite P16 in SLOTS.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
unfold Q1Y6.Mq2.pe_msE in *.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
set (PF := PEF tk oldl newl len lenr sb spf pmd mxd fl) in *. set (PA := PEFA sp0 Ff oldloc newloc bsl dsl) in *.
pose proof (LV depth l Hl) as LVd. pose proof LVd as (ST26 & SS26 & _ & Md).
rewrite Nat.ltb_irrefl, Nat.eqb_refl in Md. destruct Md as (c0 & hn0 & Hmode & CLS0 & NM0).
destruct (number_mode_ss _ _ _ SS26 ltac:(rewrite <- Hst; exact Hmode)) as (Ec0 & Ehn0 & Ess). subst c0 hn0.
cbn [name_ok] in NM0. destruct NM0 as [Hn0 Hnbs0].
assert (Ecs : tl_cs l = None) by (destruct (tl_cs l); [exfalso; exact CLS0 | reflexivity]).
pose proof (LV depth l Hl) as (_ & _ & JO & _). rewrite Ecs in JO. cbn [jopt] in JO. destruct JO as [Ecur Ecbs].
assert (Eobjbs : objbs = []).
{ unfold cur_st in OBJ. cbn [t_levels t_depth t_objbs ts0] in OBJ. rewrite Hl, Hst in OBJ. exact OBJ. }
pose proof (PE_WINX_open HIx GA PF PA q LB0 LM FRS payload me lo m md A B ts0 errv l _ INVX0 Hl Hn0 Hnbs0 Eobjbs) as WIN0.
rewrite Ecur, Ecs, Ecbs in WIN0.
set (lw0 := TL (tl_st l) (tl_ss l) 0 None [] 0 []) in *. set (tw0 := ts_lvl ts0 lw0) in *.
assert (PBK0 : PBOKat m tw0 kP) by (exact (PBOKat_same m ts0 tw0 _ eq_refl eq_refl PBK)).
pose proof (BOK_afford PF PA ts0 B nB (newdbls_costB kP) BSL BK ltac:(unfold newdbls_costB, K_ev, PF; cbn [pf_len]; lia)) as COST.
pose proof PBK as (buf & bpos & cap & pre & post & Epbs & Lpre & PBCORE & Hbk). cbn [t_pbs t_pb ts0] in Epbs, PBCORE. destruct PBCORE as (Hbp & Hcap & Hlen & PBC & BUFC).
assert (INtk : In (tk, 72) (pe_blocksA PF q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INpb : In (pb, PB_SZ) (pe_blocksA PF q LB0 ts0)) by (unfold pe_blocksA, tstate_blocks, ts0; cbn [t_pbs]; rewrite Epbs; apply in_or_app; left; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t. blk_factsA A4L HIx HP pb 16 Hpal Hplo Hphi Himg_p.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 1 HP INtk ltac:(lia)) as SHT1.
replace (tk / 8 + 1 + A_SB) with (tk / 8 + 2147450881) in SHT1 by (unfold A_SB; lia).
pose proof (blk_granA HIx _ _ _ _ _ _ _ pb 16 0 HP INpb ltac:(lia) ltac:(lia)) as SHP0.
replace (pb / 8 + 0 + A_SB) with (pb / 8 + 2147450880) in SHP0 by (unfold A_SB; lia).
stash Himg_t. stash Himg_p. stash BUFC.
pose proof (TSK depth l Hl) as Ld. remember (q + 32 * Z.of_nat depth) as bse eqn:Hbse in Ld.
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8, A_SB in *.
clear REST LV OBJ PB TSK Ld INtk.
reenterA asegs A4L HIx asegs_wx HP.
step.
asan_rechkM 1.
step.
step.
asan_chkM 1.
step.
step.
evt_done5.
eapply (pe_new_double_s_wX HIx GA GA_pres NEWDBLS PF PA q LB0 LM FRS payload me lo m md A B tw0 nb pj sv errv T kP buf cap v2 ra2
(num_ffc cb (pj_fhd pj) f1a f1b f2a f2c f2e endw n64 nu64) (ffsh_cells (FSHN 0xf8)));
[ exact STC | exact WIN0 | cbn; lia | cbn; lia | exact PBK0 | exact Epbs | exact COST | exact S0V | exact RAV | exact HV | exact UWK | rewrite unsigned_lit by lia; reflexivity |].
intros m2 md2 A2 B2 errv2 r w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 F2 fc2 OUT2 PBK2 HB2 HD2 FS2 FRM2.
cbn [pf_spf pa_sp0 pa_F PF PA] in *. unfold A_TP in *.
assert (WR2 : NUM_WINR PF PA q LB0 LM FRS payload me lo m2 md2 A2 B2 tw0 r (Sdouble true) (Z.max 20 (kP + 16)) cb nb pj sv errv2).
{ destruct OUT2 as [(-> & W) | (Hr & BS & LEN3 & JF & Rr & W)].
- left. split; [reflexivity|]. exists f1a, f1b, f2a, f2c, f2e, endw, n64, nu64. exact W.
- right. split; [exact Hr|]. exists BS. split; [lia|]. split; [destruct JF as (wj & JF1 & JF2); exists wj; split; [exact JF1 | lia]|]. split; [exact Rr|]. exists f1a, f1b, f2a, f2c, f2e, endw, n64, nu64. exact W. }
assert (COMMON : exists p2 s2 BS2, PE_WINX HIx GA PF PA q LB0 LM FRS payload me lo m2 md2 A2 B2 tw0 p2 s2 BS2 1 errv2
(pe_frameAX m2 PF PA nb pj sv (num_ffc cb (pj_fhd pj) f1a f1b f2a f2c f2e endw n64 nu64) (ffsh_cells (FSHN 0xf8))))
by (destruct OUT2 as [(_ & W) | (_ & BS & _ & _ & _ & W)]; eauto).
destruct COMMON as (p2 & s2 & BS2 & WIN2). clear OUT2.
clear TOK SLOTS FFX HP WIN0 PBK0 INVX0 FRX PBK SHT1 SHP0 PBC Htal Htlo Hthi Hpal Hplo Hphi INpb.
pose proof WIN2 as (CORE2 & BASE2 & _). destruct CORE2 as (_ & _ & _ & _ & TOK & _ & _ & _ & FRX2). pose proof (proj1 BASE2) as HP. clear BASE2 WIN2.
unfold tw0, ts_lvl, ts0 in TOK. cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_tk pf_mxd pf_fl PF] in TOK.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
destruct FRX2 as (SLOTS & _). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc PF PA] in SLOTS.
assert (INtk : In (tk, 72) (pe_blocksA PF q LB0 (tsF tw0 BS2))) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * mxd) (pe_blocksA PF q LB0 (tsF tw0 BS2))) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t2.
blk_factsA A4L HIx HP q (32 * mxd) Hqal Hqlo Hqhi Himg_q2.
assert (Hb8 : bse mod 8 = 0) by (subst bse; clear - Hqal; Z.div_mod_to_equations; lia).
shq_facts HP INq INtk q mxd tk (Z.of_nat depth) 2 SHQ2 SEPQ2c SEPQ2q SEPQ2t.
replace (q / 8 + 4 * (Z.of_nat depth) + 2 + A_SB) with (bse / 8 + 2147450882) in SHQ2 by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia).
clear SEPQ2c SEPQ2q SEPQ2t.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 7 HP INtk ltac:(lia)) as SHT7.
replace (tk / 8 + 7 + A_SB) with (tk / 8 + 2147450887) in SHT7 by (unfold A_SB; lia).
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 2 HP INtk ltac:(lia)) as SHT2.
replace (tk / 8 + 2 + A_SB) with (tk / 8 + 2147450882) in SHT2 by (unfold A_SB; lia).
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8, A_SB in *.
stash Himg_t2. stash Himg_q2. stash WR2.
replace (ret_pc (Z_to_bv 64 611320)) with (Z_to_bv 64 611320) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
reenterA asegs A4L HIx asegs_wx HP.
asan_rechkA.
asan_rechkM 6.
step.
norm_sx32.
step.
rewrite (unsigned_lit (Z.of_nat depth)) by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32.
step.
replace (q + Z.of_nat depth * 32) with bse by lia.
step.
asan_chkA.
evt_done5. unstash WR2.
replace (q + 32 * Z.of_nat depth + 16) with (bse + 16) in Kjoin by lia.
eapply (Kjoin m2 md2 A2 B2 errv2 r); [exact WR2 | exact PBK2 | exact HB2 | lia | exact FS2 | exact FRM2].
Qed.

Lemma num_tail_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B0 B : bud) (tw : tstate) (lw : tlevel)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP c r : Z) (sh : jshape) (nB : nat)
(gp t0 t1 t2 a2 a3 a4 a5 a6 a7 s11 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa ->
NUM_WINR pf pa q LB0 LM FRS payload me lo m md A B tw r sh (Z.max 20 (kP + 16)) cb nb pj sv errv ->
nth_error (t_levels tw) (t_depth tw) = Some lw -> tl_cur lw = 0 ->
(sh = Sint \/ sh = Sdouble true) ->
PBOKat m tw kP ->
BOK pf pa tw B0 (S (Z.to_nat (16 * Z.max 0 (pf_len pf) + 8192) + nB)) -> bB B0 - c <= bB B -> bD B0 - 1 <= bD B -> 0 <= c -> c + K_free * 4 <= 16 * Z.max 0 (pf_len pf) + 8192 ->

(forall m' pj' BS t0' a0' a1' a2' s5',
(length BS <= 4)%nat -> (exists w, jfresh sh BS w /\ w <= Z.max 20 (kP + 16)) ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md A B (ts_lvl tw (TL ST_eatws ST_finish r (Some sh) BS 0 [])) cb nb pj' sv errv ->
PBOKat m' (ts_lvl tw (TL ST_eatws ST_finish r (Some sh) BS 0 [])) kP ->
BOK pf pa (ts_lvl tw (TL ST_eatws ST_finish r (Some sh) BS 0 [])) B nB ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa APE_REDO (t_co tw) gp t0' t1 t2 a0' a1' a2' a3 a4 a5 a6 a7 s5' (Z_to_bv 64 (pf_tk pf + 56)) (Z_to_bv 64 (pa_F pa + 64)) F fc m')) ->

(forall m' pj' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' s11' t4' t6',
PE_INVW_A HIx GA pf pa q LB0 LM FRS payload me lo m' md A B (ts_set_x tw (t_co tw) (tx_err (t_x tw) (Z_to_bv 64 16))) [] cb nb pj' sv errv ->
AJ5 A4L HIx A T md
(pe_msO asegs pf pa APE_OUT x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' (Z_to_bv 64 (pf_tk pf + 56)) s11' t4' t6' F fc m')) ->
AJ5 A4L HIx A T md
(Q1Y6.Mq2.pe_msE pf pa 0x95560 (Z_to_bv 64 (pf_tk pf / 8 + 2147450884)) gp t0 t1 t2 (Z_to_bv 64 r) (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth tw) + 16)) a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (pf_tk pf / 8 + 2147450882)) (Z_to_bv 64 (pf_tk pf + 20)) (Z_to_bv 64 (pf_tk pf / 8 + 2147450887)) (Z_to_bv 64 (pf_sb pf + t_co tw)) (Z_to_bv 64 (pf_tk pf + 32)) (Z_to_bv 64 (pa_F pa)) (Z_to_bv 64 (pf_tk pf + 56))
s11 (Z_to_bv 64 (pf_tk pf + 64)) (Z_to_bv 64 (pa_F pa + 64)) (Z_to_bv 64 (pf_tk pf / 8 + 2147450888)) (Z_to_bv 64 (pf_lenr pf)) F fc m).
Proof.
intros until fc. intros STC BSL WR Hlw Hcur Hsh PBK BK HB HD Hc0 HcK Kredo Kout.
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
assert (COMMON : exists p2 s2 BS2 f1a f1b f2a f2c f2e endw n64 nu64,
PE_WINX HIx GA pf pa q LB0 LM FRS payload me lo m md A B tw p2 s2 BS2 1 errv
(pe_frameAX m pf pa nb pj sv (num_ffc cb (pj_fhd pj) f1a f1b f2a f2c f2e endw n64 nu64) (ffsh_cells (FSHN 0xf8)))).
{ destruct WR as [(_ & (f1a & f1b & f2a & f2c & f2e & endw & n64 & nu64 & W)) | (_ & BS & _ & _ & (f1a & f1b & f2a & f2c & f2e & endw & n64 & nu64 & W))]; eauto 12. }
destruct COMMON as (p2 & s2 & BS2 & f1a & f1b & f2a & f2c & f2e & endw & n64 & nu64 & WINc).
pose proof WINc as (CORE2 & BASE2 & _ & (lwx & Hlwx & BARE) & _). rewrite Hlw in Hlwx. injection Hlwx as <-.
destruct BARE as (R1 & R2 & Ecs & Ecbs & En & Enbs).
destruct CORE2 as (LEN32 & D32 & CO & CHOFF & TOK & _ & _ & TSK2 & FRX2). pose proof (proj1 BASE2) as HP. clear BASE2 WINc.
destruct tw as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
pose proof FRX2 as (SLOTS & _ & _ & FFX & FSH). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS. unfold num_ffc in FFX. unfold ffsh_cells, FSHN in FSH. cbn [map] in FSH.
unfold Q1Y6.Mq2.pe_msE, pe_msA, pe_msO in *.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
set (tw0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
set (PF := PEF tk oldl newl len lenr sb spf pmd mxd fl) in *. set (PA := PEFA sp0 Ff oldloc newloc bsl dsl) in *.
assert (INtk : In (tk, 72) (pe_blocksA PF q LB0 (tsF tw0 BS2))) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * mxd) (pe_blocksA PF q LB0 (tsF tw0 BS2))) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t.
blk_factsA A4L HIx HP q (32 * mxd) Hqal Hqlo Hqhi Himg_q.
pose proof (q_ne_tkA HIx _ _ _ _ _ _ _ _ _ _ HP) as Hqtk. cbn [pf_tk PF] in Hqtk.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ tk 72 q (32 * mxd) HP (in_or_app _ LM _ (or_introl INtk)) (in_or_app _ LM _ (or_introl INq)) ltac:(congruence)) as Hdtq.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs m) as WM.
assert (Hlen0 : length levels = Z.to_nat mxd) by exact LEN32.
pose proof (TSK2 depth lw Hlw) as Ld. remember (q + 32 * Z.of_nat depth) as bse eqn:Hbse in Ld. unfold srec_cells in Ld. rewrite Hcur, En in Ld.
assert (HbseR : q <= bse /\ bse + 32 <= q + (32 * mxd)) by (subst bse; lia).
assert (Hb8 : bse mod 8 = 0) by (subst bse; clear - Hqal; Z.div_mod_to_equations; lia).
shq_facts HP INq INtk q mxd tk (Z.of_nat depth) 0 SHQ0 SEPQ0c SEPQ0q SEPQ0t.
replace (q / 8 + 4 * (Z.of_nat depth) + 0 + A_SB) with (bse / 8 + 2147450880) in SHQ0 by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia).
assert (EQx : q / 8 + A_SB + (4 * (Z.of_nat depth) + 0) = bse / 8 + 2147450880) by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia). rewrite EQx in SEPQ0c, SEPQ0q, SEPQ0t. clear EQx.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 7 HP INtk ltac:(lia)) as SHT7.
replace (tk / 8 + 7 + A_SB) with (tk / 8 + 2147450887) in SHT7 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 7 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (_ & SEPT7q & _).
cbn [hl_sb A4L] in SEPT7q. assert (EQx : tk / 8 + A_SB + 7 = tk / 8 + 2147450887) by (unfold A_SB; lia). rewrite EQx in SEPT7q. clear EQx.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 2 HP INtk ltac:(lia)) as SHT2.
replace (tk / 8 + 2 + A_SB) with (tk / 8 + 2147450882) in SHT2 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 2 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (_ & SEPT2q & _).
cbn [hl_sb A4L] in SEPT2q. assert (EQx : tk / 8 + A_SB + 2 = tk / 8 + 2147450882) by (unfold A_SB; lia). rewrite EQx in SEPT2q. clear EQx.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 4 HP INtk ltac:(lia)) as SHT4.
replace (tk / 8 + 4 + A_SB) with (tk / 8 + 2147450884) in SHT4 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 4 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (_ & SEPT4q & _).
cbn [hl_sb A4L] in SEPT4q. assert (EQx : tk / 8 + A_SB + 4 = tk / 8 + 2147450884) by (unfold A_SB; lia). rewrite EQx in SEPT4q. clear EQx.
assert (INF : In (Ff, 2) ((Ff, 2) :: FRS)) by (left; reflexivity).
pose proof alloc_ceiling_range as ACR.
assert (GF0' : 0 <= Ff) by lia. assert (GFc' : Ff < alloc_ceiling) by lia.
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP INF (in_or_app _ LM _ (or_introl INtk))) as DFt. rewrite fr_size_2 in DFt.
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP INF (in_or_app _ LM _ (or_introl INq))) as DFq. rewrite fr_size_2 in DFq.
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP INF) as DSF. rewrite fr_size_2 in DSF. cbn [hl_sb A4L] in DSF.
pose proof (shadow_blk_apart HIx _ _ _ _ _ _ _ _ _ Ff 32 HP (in_or_app _ LM _ (or_introl INtk)) GF0' GFc' ltac:(lia)) as DSt. unfold shA, A_SB in DSt.
pose proof (shadow_blk_apart HIx _ _ _ _ _ _ _ _ _ Ff 32 HP (in_or_app _ LM _ (or_introl INq)) GF0' GFc' ltac:(lia)) as DSq. unfold shA, A_SB in DSq.
pose proof (munch_refl [(bse, bse + 32); (tk, tk + 72); (Ff, Ff + 248); (Ff / 8 + 2147450880, Ff / 8 + 2147450880 + 32)] m) as MU.
unfold APE_REDO, APE_OUT in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8, A_SB in *.
assert (cs_tk_L : csep tk 72 bse (Z.of_nat 32)) by (unfold csep; clear - Hdtq HbseR; lia).
assert (cs_L_tk : csep bse 32 tk (Z.of_nat 72)) by (unfold csep; clear - Hdtq HbseR; lia).
assert (cs_Q0_L : csep (bse / 8 + 2147450880) 1 bse (Z.of_nat 32)) by (unfold csep; clear - SEPQ0q HbseR; lia).
assert (cs_T7_L : csep (tk / 8 + 2147450887) 1 bse (Z.of_nat 32)) by (unfold csep; clear - SEPT7q HbseR; lia).
assert (cs_T2_L : csep (tk / 8 + 2147450882) 1 bse (Z.of_nat 32)) by (unfold csep; clear - SEPT2q HbseR; lia).
assert (cs_T4_L : csep (tk / 8 + 2147450884) 1 bse (Z.of_nat 32)) by (unfold csep; clear - SEPT4q HbseR; lia).
clear SEPQ0c SEPQ0q SEPQ0t SEPT7q SEPT2q SEPT4q.
assert (HWc : Forall (fun iv : Z * Z => snd iv <= alloc_ceiling) [(bse, bse + 32); (tk, tk + 72); (Ff, Ff + 248); (Ff / 8 + 2147450880, Ff / 8 + 2147450880 + 32)]).
{ repeat (apply Forall_cons; [cbn [snd]; first [lia | clear - ACR GF0' GFc'; Z.div_mod_to_equations; lia] |]). apply Forall_nil. }
assert (HWq : Forall (pe_wtqA PF PA q) [(bse, bse + 32); (tk, tk + 72); (Ff, Ff + 248); (Ff / 8 + 2147450880, Ff / 8 + 2147450880 + 32)]).
{ apply Forall_cons; [right; cbn [fst snd pf_mxd PF]; lia |]. apply Forall_cons; [left; left; cbn [fst snd pf_tk PF]; lia |].
apply Forall_cons; [left; right; right; left; cbn [fst snd pa_F PA]; lia |]. apply Forall_cons; [| apply Forall_nil]. left; right; right; right. cbn [fst snd pa_F PA]. unfold shA, A_SB. lia. }
assert (DISJ : forall j, (j < length levels)%nat -> j <> depth ->
disjoint_from [(tk, tk + 72); (Ff, Ff + 248); (Ff / 8 + 2147450880, Ff / 8 + 2147450880 + 32)] (q + 32 * Z.of_nat j) 32).
{ intros j Hj _. rewrite Hlen0 in Hj. cbn [disjoint_from fst snd]. clear - Hj Hdtq DFq DSq RR. lia. }
stash Himg_t. stash Himg_q. stash Kredo. stash Kout. stash WR. stash TSK2. stash FRX2. stash PBK. stash BK. stash DISJ. stash HWc. stash HWq.
reenterA asegs A4L HIx asegs_wx HP.
replace (q + 32 * Z.of_nat depth + 16) with (bse + 16) by lia.
stepz.
step.
unstash WR. unstash TSK2. unstash FRX2. unstash PBK. unstash BK. unstash DISJ. unstash HWc. unstash HWq.
assert (Elw : TL (tl_st lw) (tl_ss lw) 0 None [] 0 [] = lw)
by (destruct lw as [st_ ss_ cur_ cs_ cbs_ name_ nbs_]; cbn [tl_st tl_ss tl_cur tl_cs tl_cbs tl_name tl_nbs] in *; congruence).
destruct WR as [(-> & (g1 & g2 & g3 & g4 & g5 & g6 & g7 & g8 & NW)) | (Hr & BS & LBS & JF & Rr & (g1 & g2 & g3 & g4 & g5 & g6 & g7 & g8 & NW))].
-
if_false.
step.
step. step.
step.
step.
asan_rechkA.
stepz.
step.
stepz.
stepz.
step.
set (x3 := tx_err (t_x tw0) (Z_to_bv 64 16)).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, Lc : rw_cells asegs mc bse _,
FFc : rw_cells asegs mc Ff _, FSHc : rw_cells asegs mc (Ff / 8 + 2147450880) _ |- _ =>
evt_done5;
assert (FRXc : pe_frameAX mc PF PA nb pj sv (num_ffc cb (pj_fhd pj) f1a f1b f2a f2c f2e endw n64 nu64) (ffsh_cells FSH0))
by (eapply (pe_frameAX_writeG HIx PF PA nb pj sv _ _ _ _ m mc lo); [exact STC | exact FRX2 | exact MUc | exact WMc | exact HWc | exact FFc | exact FSHc]);
pose proof (num_frame_close mc PF PA cb nb pj sv f1a f1b f2a f2c f2e endw n64 nu64 FRXc) as FRc;
assert (TSKc : tstack asegs mc q (lupd (t_levels tw0) (t_depth tw0) lw))
by (pose proof MUc as MUc'; pose proof Lc as Lc'; rewrite Hbse in MUc', Lc'; eapply (tstack_put asegs m mc q levels depth lw _);
[exact TSK2 | rewrite Hlen0; lia | exact MUc' | exact WMc | exact DISJ | unfold srec_cells; rewrite Hcur, En; exact Lc']);
destruct (PE_WINX_write_x HIx GA GA_outside PF PA q LB0 LM FRS payload me lo m mc md A B tw0 0 None [] 1 errv _ lw x3 _ _ STC NW MUc WMc MIc HWq TOKc eq_refl TSKc FRc
(conj R1 (conj R2 (conj Ecs (conj Ecbs (conj En Enbs)))))) as [WIN3 _]
end end.
rewrite (ts_lvl_same tw0 lw Hlw) in WIN3.
pose proof (BOK_weak _ _ _ _ _ (BOK_pay PF PA tw0 B0 B nB c BK ltac:(unfold K_free in HcK; lia) HB HD)) as [HBw HDw].
pose proof (PE_WIN_close_weak HIx GA PF PA q LB0 LM FRS payload me lo _ md A B (ts_set_x tw0 co x3) cb nb _ sv errv 1 (PE_WIN_of_WINX HIx GA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ WIN3)
ltac:(exists lw; split; [exact Hlw | exact Hcur]) HBw HDw) as INVw.
unstash Kout. eapply Kout. exact INVw.
-
if_truex.
asan_rechkA.
asan_rechkM 1.
step.
norm_sx32.
step.
rewrite (unsigned_lit (Z.of_nat depth)) by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32.
step.
replace (q + Z.of_nat depth * 32) with bse by lia.
step.
asan_chkA.
step.
stepz.
asan_chkA.
stepz.
step.
stepz.
stepz.
step. step.
step.
set (lw2 := TL ST_eatws ST_finish r None [] 0 []).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, Lc : rw_cells asegs mc bse _,
FFc : rw_cells asegs mc Ff _, FSHc : rw_cells asegs mc (Ff / 8 + 2147450880) _ |- _ =>
evt_done5;
assert (FRXc : pe_frameAX mc PF PA nb pj sv (num_ffc cb (pj_fhd pj) f1a f1b f2a f2c f2e endw n64 nu64) (ffsh_cells FSH0))
by (eapply (pe_frameAX_writeG HIx PF PA nb pj sv _ _ _ _ m mc lo); [exact STC | exact FRX2 | exact MUc | exact WMc | exact HWc | exact FFc | exact FSHc]);
pose proof (num_frame_close mc PF PA cb nb pj sv f1a f1b f2a f2c f2e endw n64 nu64 FRXc) as FRc;
assert (TSKc : tstack asegs mc q (lupd (t_levels tw0) (t_depth tw0) lw2))
by (pose proof MUc as MUc'; pose proof Lc as Lc'; rewrite Hbse in MUc', Lc'; eapply (tstack_put asegs m mc q levels depth lw2 _);
[exact TSK2 | rewrite Hlen0; lia | exact MUc' | exact WMc | exact DISJ | exact Lc']);
destruct (PE_WINX_write HIx GA GA_outside PF PA q LB0 LM FRS payload me lo m mc md A B tw0 r (Some sh) BS 1 errv _ lw2 _ _ STC NW MUc WMc MIc HWq TOKc TSKc FRc
ltac:(unfold lvl_bare, lw2, ST_eatws, ST_finish; cbn [tl_st tl_ss tl_cs tl_cbs tl_name tl_nbs]; repeat split; try reflexivity; lia)) as [WIN3 PBT3]
end end.
set (tw2 := ts_lvl tw0 lw2) in *.
assert (Etw2 : forall lx, ts_lvl tw2 lx = ts_lvl tw0 lx) by (intros lx; unfold tw2; rewrite ts_lvl_lvl; reflexivity).
assert (Hlw2 : nth_error (t_levels tw2) (t_depth tw2) = Some lw2) by (unfold tw2, ts_lvl; cbn [t_levels t_depth tw0]; apply nth_error_lupd_eq; rewrite Hlen0; lia).
assert (Eb0 : lvl_blocks lw = []) by (unfold lvl_blocks; rewrite Ecbs, Enbs; reflexivity).
assert (PHI : phi_level (TL ST_eatws ST_finish r (Some sh) BS 0 []) = 0) by (unfold phi_level; cbn [tl_cs]; destruct Hsh as [-> | ->]; reflexivity).
assert (BKf : BOK PF PA (ts_lvl tw0 (TL ST_eatws ST_finish r (Some sh) BS 0 [])) B nB).
{ eapply (BOK_attach PF PA tw0 B0 B nB lw ST_eatws ST_finish r sh BS c BK Hlw Ecs Eb0);
[ rewrite PHI; lia
| rewrite PHI; unfold K_free in *; lia
| intros kids Ek; destruct Hsh as [-> | ->]; discriminate Ek | intros kids Ek; destruct Hsh as [-> | ->]; discriminate Ek | exact HB | exact HD ]. }
pose proof (PE_WIN_close_cur HIx GA PF PA q LB0 LM FRS payload me lo _ md A B tw2 r sh BS cb nb _ sv errv lw2 CAny (PE_WIN_of_WINX HIx GA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ WIN3) Hlw2 eq_refl
ltac:(vm_compute; reflexivity) I ltac:(reflexivity)
ltac:(cbn [tl_st tl_ss lw2]; rewrite Etw2; exact (BOK_weak _ _ _ _ _ BKf))) as INVf.
cbn [tl_st tl_ss lw2] in INVf. rewrite Etw2 in INVf.
unstash Kredo. eapply (Kredo _ _ BS); [exact LBS | exact JF | exact INVf | | exact BKf].
eapply PBOKat_same with (ts := tw2); [reflexivity | reflexivity |]. exact (PBT3 _ PBK).
Qed.

Lemma num_taild_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B0 B : bud) (tw : tstate) (lw : tlevel)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP c r : Z) (sh : jshape) (nB : nat)
(gp t0 t1 t2 a2 a3 a4 a5 a6 a7 s11 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa ->
NUM_WINR pf pa q LB0 LM FRS payload me lo m md A B tw r sh (Z.max 20 (kP + 16)) cb nb pj sv errv ->
nth_error (t_levels tw) (t_depth tw) = Some lw -> tl_cur lw = 0 ->
(sh = Sint \/ sh = Sdouble true) ->
PBOKat m tw kP ->
BOK pf pa tw B0 (S (Z.to_nat (16 * Z.max 0 (pf_len pf) + 8192) + nB)) -> bB B0 - c <= bB B -> bD B0 - 1 <= bD B -> 0 <= c -> c + K_free * 4 <= 16 * Z.max 0 (pf_len pf) + 8192 ->

(forall m' pj' BS t0' a0' a1' a2' s5',
(length BS <= 4)%nat -> (exists w, jfresh sh BS w /\ w <= Z.max 20 (kP + 16)) ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md A B (ts_lvl tw (TL ST_eatws ST_finish r (Some sh) BS 0 [])) cb nb pj' sv errv ->
PBOKat m' (ts_lvl tw (TL ST_eatws ST_finish r (Some sh) BS 0 [])) kP ->
BOK pf pa (ts_lvl tw (TL ST_eatws ST_finish r (Some sh) BS 0 [])) B nB ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa APE_REDO (t_co tw) gp t0' t1 t2 a0' a1' a2' a3 a4 a5 a6 a7 s5' (Z_to_bv 64 (pf_tk pf + 56)) (Z_to_bv 64 (pa_F pa + 64)) F fc m')) ->

(forall m' pj' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' s11' t4' t6',
PE_INVW_A HIx GA pf pa q LB0 LM FRS payload me lo m' md A B (ts_set_x tw (t_co tw) (tx_err (t_x tw) (Z_to_bv 64 16))) [] cb nb pj' sv errv ->
AJ5 A4L HIx A T md
(pe_msO asegs pf pa APE_OUT x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' (Z_to_bv 64 (pf_tk pf + 56)) s11' t4' t6' F fc m')) ->
AJ5 A4L HIx A T md
(Q1Y6.Mq2.pe_msE pf pa 0x95448 (Z_to_bv 64 (pf_tk pf / 8 + 2147450884)) gp t0 t1 t2 (Z_to_bv 64 r) (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth tw) + 16)) a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (pf_tk pf / 8 + 2147450882)) (Z_to_bv 64 (pf_tk pf + 20)) (Z_to_bv 64 (pf_tk pf / 8 + 2147450887)) (Z_to_bv 64 (pf_sb pf + t_co tw)) (Z_to_bv 64 (pf_tk pf + 32)) (Z_to_bv 64 (pa_F pa)) (Z_to_bv 64 (pf_tk pf + 56))
s11 (Z_to_bv 64 (pf_tk pf + 64)) (Z_to_bv 64 (pa_F pa + 64)) (Z_to_bv 64 (pf_tk pf / 8 + 2147450888)) (Z_to_bv 64 (pf_lenr pf)) F fc m).
Proof.
intros until fc. intros STC BSL WR Hlw Hcur Hsh PBK BK HB HD Hc0 HcK Kredo Kout.
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
assert (COMMON : exists p2 s2 BS2 f1a f1b f2a f2c f2e endw n64 nu64,
PE_WINX HIx GA pf pa q LB0 LM FRS payload me lo m md A B tw p2 s2 BS2 1 errv
(pe_frameAX m pf pa nb pj sv (num_ffc cb (pj_fhd pj) f1a f1b f2a f2c f2e endw n64 nu64) (ffsh_cells (FSHN 0xf8)))).
{ destruct WR as [(_ & (f1a & f1b & f2a & f2c & f2e & endw & n64 & nu64 & W)) | (_ & BS & _ & _ & (f1a & f1b & f2a & f2c & f2e & endw & n64 & nu64 & W))]; eauto 12. }
destruct COMMON as (p2 & s2 & BS2 & f1a & f1b & f2a & f2c & f2e & endw & n64 & nu64 & WINc).
pose proof WINc as (CORE2 & BASE2 & _ & (lwx & Hlwx & BARE) & _). rewrite Hlw in Hlwx. injection Hlwx as <-.
destruct BARE as (R1 & R2 & Ecs & Ecbs & En & Enbs).
destruct CORE2 as (LEN32 & D32 & CO & CHOFF & TOK & _ & _ & TSK2 & FRX2). pose proof (proj1 BASE2) as HP. clear BASE2 WINc.
destruct tw as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
pose proof FRX2 as (SLOTS & _ & _ & FFX & FSH). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS. unfold num_ffc in FFX. unfold ffsh_cells, FSHN in FSH. cbn [map] in FSH.
unfold Q1Y6.Mq2.pe_msE, pe_msA, pe_msO in *.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
set (tw0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
set (PF := PEF tk oldl newl len lenr sb spf pmd mxd fl) in *. set (PA := PEFA sp0 Ff oldloc newloc bsl dsl) in *.
assert (INtk : In (tk, 72) (pe_blocksA PF q LB0 (tsF tw0 BS2))) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * mxd) (pe_blocksA PF q LB0 (tsF tw0 BS2))) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t.
blk_factsA A4L HIx HP q (32 * mxd) Hqal Hqlo Hqhi Himg_q.
pose proof (q_ne_tkA HIx _ _ _ _ _ _ _ _ _ _ HP) as Hqtk. cbn [pf_tk PF] in Hqtk.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ tk 72 q (32 * mxd) HP (in_or_app _ LM _ (or_introl INtk)) (in_or_app _ LM _ (or_introl INq)) ltac:(congruence)) as Hdtq.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs m) as WM.
assert (Hlen0 : length levels = Z.to_nat mxd) by exact LEN32.
pose proof (TSK2 depth lw Hlw) as Ld. remember (q + 32 * Z.of_nat depth) as bse eqn:Hbse in Ld. unfold srec_cells in Ld. rewrite Hcur, En in Ld.
assert (HbseR : q <= bse /\ bse + 32 <= q + (32 * mxd)) by (subst bse; lia).
assert (Hb8 : bse mod 8 = 0) by (subst bse; clear - Hqal; Z.div_mod_to_equations; lia).
shq_facts HP INq INtk q mxd tk (Z.of_nat depth) 0 SHQ0 SEPQ0c SEPQ0q SEPQ0t.
replace (q / 8 + 4 * (Z.of_nat depth) + 0 + A_SB) with (bse / 8 + 2147450880) in SHQ0 by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia).
assert (EQx : q / 8 + A_SB + (4 * (Z.of_nat depth) + 0) = bse / 8 + 2147450880) by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia). rewrite EQx in SEPQ0c, SEPQ0q, SEPQ0t. clear EQx.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 7 HP INtk ltac:(lia)) as SHT7.
replace (tk / 8 + 7 + A_SB) with (tk / 8 + 2147450887) in SHT7 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 7 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (_ & SEPT7q & _).
cbn [hl_sb A4L] in SEPT7q. assert (EQx : tk / 8 + A_SB + 7 = tk / 8 + 2147450887) by (unfold A_SB; lia). rewrite EQx in SEPT7q. clear EQx.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 2 HP INtk ltac:(lia)) as SHT2.
replace (tk / 8 + 2 + A_SB) with (tk / 8 + 2147450882) in SHT2 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 2 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (_ & SEPT2q & _).
cbn [hl_sb A4L] in SEPT2q. assert (EQx : tk / 8 + A_SB + 2 = tk / 8 + 2147450882) by (unfold A_SB; lia). rewrite EQx in SEPT2q. clear EQx.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 4 HP INtk ltac:(lia)) as SHT4.
replace (tk / 8 + 4 + A_SB) with (tk / 8 + 2147450884) in SHT4 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 4 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (_ & SEPT4q & _).
cbn [hl_sb A4L] in SEPT4q. assert (EQx : tk / 8 + A_SB + 4 = tk / 8 + 2147450884) by (unfold A_SB; lia). rewrite EQx in SEPT4q. clear EQx.
assert (INF : In (Ff, 2) ((Ff, 2) :: FRS)) by (left; reflexivity).
pose proof alloc_ceiling_range as ACR.
assert (GF0' : 0 <= Ff) by lia. assert (GFc' : Ff < alloc_ceiling) by lia.
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP INF (in_or_app _ LM _ (or_introl INtk))) as DFt. rewrite fr_size_2 in DFt.
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP INF (in_or_app _ LM _ (or_introl INq))) as DFq. rewrite fr_size_2 in DFq.
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP INF) as DSF. rewrite fr_size_2 in DSF. cbn [hl_sb A4L] in DSF.
pose proof (shadow_blk_apart HIx _ _ _ _ _ _ _ _ _ Ff 32 HP (in_or_app _ LM _ (or_introl INtk)) GF0' GFc' ltac:(lia)) as DSt. unfold shA, A_SB in DSt.
pose proof (shadow_blk_apart HIx _ _ _ _ _ _ _ _ _ Ff 32 HP (in_or_app _ LM _ (or_introl INq)) GF0' GFc' ltac:(lia)) as DSq. unfold shA, A_SB in DSq.
pose proof (munch_refl [(bse, bse + 32); (tk, tk + 72); (Ff, Ff + 248); (Ff / 8 + 2147450880, Ff / 8 + 2147450880 + 32)] m) as MU.
unfold APE_REDO, APE_OUT in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8, A_SB in *.
assert (cs_tk_L : csep tk 72 bse (Z.of_nat 32)) by (unfold csep; clear - Hdtq HbseR; lia).
assert (cs_L_tk : csep bse 32 tk (Z.of_nat 72)) by (unfold csep; clear - Hdtq HbseR; lia).
assert (cs_Q0_L : csep (bse / 8 + 2147450880) 1 bse (Z.of_nat 32)) by (unfold csep; clear - SEPQ0q HbseR; lia).
assert (cs_T7_L : csep (tk / 8 + 2147450887) 1 bse (Z.of_nat 32)) by (unfold csep; clear - SEPT7q HbseR; lia).
assert (cs_T2_L : csep (tk / 8 + 2147450882) 1 bse (Z.of_nat 32)) by (unfold csep; clear - SEPT2q HbseR; lia).
assert (cs_T4_L : csep (tk / 8 + 2147450884) 1 bse (Z.of_nat 32)) by (unfold csep; clear - SEPT4q HbseR; lia).
clear SEPQ0c SEPQ0q SEPQ0t SEPT7q SEPT2q SEPT4q.
assert (HWc : Forall (fun iv : Z * Z => snd iv <= alloc_ceiling) [(bse, bse + 32); (tk, tk + 72); (Ff, Ff + 248); (Ff / 8 + 2147450880, Ff / 8 + 2147450880 + 32)]).
{ repeat (apply Forall_cons; [cbn [snd]; first [lia | clear - ACR GF0' GFc'; Z.div_mod_to_equations; lia] |]). apply Forall_nil. }
assert (HWq : Forall (pe_wtqA PF PA q) [(bse, bse + 32); (tk, tk + 72); (Ff, Ff + 248); (Ff / 8 + 2147450880, Ff / 8 + 2147450880 + 32)]).
{ apply Forall_cons; [right; cbn [fst snd pf_mxd PF]; lia |]. apply Forall_cons; [left; left; cbn [fst snd pf_tk PF]; lia |].
apply Forall_cons; [left; right; right; left; cbn [fst snd pa_F PA]; lia |]. apply Forall_cons; [| apply Forall_nil]. left; right; right; right. cbn [fst snd pa_F PA]. unfold shA, A_SB. lia. }
assert (DISJ : forall j, (j < length levels)%nat -> j <> depth ->
disjoint_from [(tk, tk + 72); (Ff, Ff + 248); (Ff / 8 + 2147450880, Ff / 8 + 2147450880 + 32)] (q + 32 * Z.of_nat j) 32).
{ intros j Hj _. rewrite Hlen0 in Hj. cbn [disjoint_from fst snd]. clear - Hj Hdtq DFq DSq RR. lia. }
stash Himg_t. stash Himg_q. stash Kredo. stash Kout. stash WR. stash TSK2. stash FRX2. stash PBK. stash BK. stash DISJ. stash HWc. stash HWq.
reenterA asegs A4L HIx asegs_wx HP.
replace (q + 32 * Z.of_nat depth + 16) with (bse + 16) by lia.
stepz.
step.
unstash WR. unstash TSK2. unstash FRX2. unstash PBK. unstash BK. unstash DISJ. unstash HWc. unstash HWq.
assert (Elw : TL (tl_st lw) (tl_ss lw) 0 None [] 0 [] = lw)
by (destruct lw as [st_ ss_ cur_ cs_ cbs_ name_ nbs_]; cbn [tl_st tl_ss tl_cur tl_cs tl_cbs tl_name tl_nbs] in *; congruence).
destruct WR as [(-> & (g1 & g2 & g3 & g4 & g5 & g6 & g7 & g8 & NW)) | (Hr & BS & LBS & JF & Rr & (g1 & g2 & g3 & g4 & g5 & g6 & g7 & g8 & NW))].
-
if_false.
step.
step. step.
step.
step.
asan_rechkA.
stepz.
step.
stepz.
stepz.
step.
set (x3 := tx_err (t_x tw0) (Z_to_bv 64 16)).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, Lc : rw_cells asegs mc bse _,
FFc : rw_cells asegs mc Ff _, FSHc : rw_cells asegs mc (Ff / 8 + 2147450880) _ |- _ =>
evt_done5;
assert (FRXc : pe_frameAX mc PF PA nb pj sv (num_ffc cb (pj_fhd pj) f1a f1b f2a f2c f2e endw n64 nu64) (ffsh_cells FSH0))
by (eapply (pe_frameAX_writeG HIx PF PA nb pj sv _ _ _ _ m mc lo); [exact STC | exact FRX2 | exact MUc | exact WMc | exact HWc | exact FFc | exact FSHc]);
pose proof (num_frame_close mc PF PA cb nb pj sv f1a f1b f2a f2c f2e endw n64 nu64 FRXc) as FRc;
assert (TSKc : tstack asegs mc q (lupd (t_levels tw0) (t_depth tw0) lw))
by (pose proof MUc as MUc'; pose proof Lc as Lc'; rewrite Hbse in MUc', Lc'; eapply (tstack_put asegs m mc q levels depth lw _);
[exact TSK2 | rewrite Hlen0; lia | exact MUc' | exact WMc | exact DISJ | unfold srec_cells; rewrite Hcur, En; exact Lc']);
destruct (PE_WINX_write_x HIx GA GA_outside PF PA q LB0 LM FRS payload me lo m mc md A B tw0 0 None [] 1 errv _ lw x3 _ _ STC NW MUc WMc MIc HWq TOKc eq_refl TSKc FRc
(conj R1 (conj R2 (conj Ecs (conj Ecbs (conj En Enbs)))))) as [WIN3 _]
end end.
rewrite (ts_lvl_same tw0 lw Hlw) in WIN3.
pose proof (BOK_weak _ _ _ _ _ (BOK_pay PF PA tw0 B0 B nB c BK ltac:(unfold K_free in HcK; lia) HB HD)) as [HBw HDw].
pose proof (PE_WIN_close_weak HIx GA PF PA q LB0 LM FRS payload me lo _ md A B (ts_set_x tw0 co x3) cb nb _ sv errv 1 (PE_WIN_of_WINX HIx GA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ WIN3)
ltac:(exists lw; split; [exact Hlw | exact Hcur]) HBw HDw) as INVw.
unstash Kout. eapply Kout. exact INVw.
-
if_truex.
asan_rechkA.
asan_rechkM 1.
step.
norm_sx32.
step.
rewrite (unsigned_lit (Z.of_nat depth)) by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32.
step.
replace (q + Z.of_nat depth * 32) with bse by lia.
step.
asan_chkA.
step.
stepz.
asan_chkA.
stepz.
step.
stepz.
stepz.
step. step.
step.
set (lw2 := TL ST_eatws ST_finish r None [] 0 []).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, Lc : rw_cells asegs mc bse _,
FFc : rw_cells asegs mc Ff _, FSHc : rw_cells asegs mc (Ff / 8 + 2147450880) _ |- _ =>
evt_done5;
assert (FRXc : pe_frameAX mc PF PA nb pj sv (num_ffc cb (pj_fhd pj) f1a f1b f2a f2c f2e endw n64 nu64) (ffsh_cells FSH0))
by (eapply (pe_frameAX_writeG HIx PF PA nb pj sv _ _ _ _ m mc lo); [exact STC | exact FRX2 | exact MUc | exact WMc | exact HWc | exact FFc | exact FSHc]);
pose proof (num_frame_close mc PF PA cb nb pj sv f1a f1b f2a f2c f2e endw n64 nu64 FRXc) as FRc;
assert (TSKc : tstack asegs mc q (lupd (t_levels tw0) (t_depth tw0) lw2))
by (pose proof MUc as MUc'; pose proof Lc as Lc'; rewrite Hbse in MUc', Lc'; eapply (tstack_put asegs m mc q levels depth lw2 _);
[exact TSK2 | rewrite Hlen0; lia | exact MUc' | exact WMc | exact DISJ | exact Lc']);
destruct (PE_WINX_write HIx GA GA_outside PF PA q LB0 LM FRS payload me lo m mc md A B tw0 r (Some sh) BS 1 errv _ lw2 _ _ STC NW MUc WMc MIc HWq TOKc TSKc FRc
ltac:(unfold lvl_bare, lw2, ST_eatws, ST_finish; cbn [tl_st tl_ss tl_cs tl_cbs tl_name tl_nbs]; repeat split; try reflexivity; lia)) as [WIN3 PBT3]
end end.
set (tw2 := ts_lvl tw0 lw2) in *.
assert (Etw2 : forall lx, ts_lvl tw2 lx = ts_lvl tw0 lx) by (intros lx; unfold tw2; rewrite ts_lvl_lvl; reflexivity).
assert (Hlw2 : nth_error (t_levels tw2) (t_depth tw2) = Some lw2) by (unfold tw2, ts_lvl; cbn [t_levels t_depth tw0]; apply nth_error_lupd_eq; rewrite Hlen0; lia).
assert (Eb0 : lvl_blocks lw = []) by (unfold lvl_blocks; rewrite Ecbs, Enbs; reflexivity).
assert (PHI : phi_level (TL ST_eatws ST_finish r (Some sh) BS 0 []) = 0) by (unfold phi_level; cbn [tl_cs]; destruct Hsh as [-> | ->]; reflexivity).
assert (BKf : BOK PF PA (ts_lvl tw0 (TL ST_eatws ST_finish r (Some sh) BS 0 [])) B nB).
{ eapply (BOK_attach PF PA tw0 B0 B nB lw ST_eatws ST_finish r sh BS c BK Hlw Ecs Eb0);
[ rewrite PHI; lia
| rewrite PHI; unfold K_free in *; lia
| intros kids Ek; destruct Hsh as [-> | ->]; discriminate Ek | intros kids Ek; destruct Hsh as [-> | ->]; discriminate Ek | exact HB | exact HD ]. }
pose proof (PE_WIN_close_cur HIx GA PF PA q LB0 LM FRS payload me lo _ md A B tw2 r sh BS cb nb _ sv errv lw2 CAny (PE_WIN_of_WINX HIx GA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ WIN3) Hlw2 eq_refl
ltac:(vm_compute; reflexivity) I ltac:(reflexivity)
ltac:(cbn [tl_st tl_ss lw2]; rewrite Etw2; exact (BOK_weak _ _ _ _ _ BKf))) as INVf.
cbn [tl_st tl_ss lw2] in INVf. rewrite Etw2 in INVf.
unstash Kredo. eapply (Kredo _ _ BS); [exact LBS | exact JF | exact INVf | | exact BKf].
eapply PBOKat_same with (ts := tw2); [reflexivity | reflexivity |]. exact (PBT3 _ PBK).
Qed.

Lemma num_entry_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet)
(gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
pbufc asegs m (t_pbs ts) (t_pb ts) [] ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_number ->
t_co ts < pf_len pf ->

(forall m' pj' a2' a5',
pj_16 pj' = Z_to_bv 64 (pf_tk pf / 8 + 2147450881) -> bv_unsigned cb <> 0 ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md A B ts cb nb pj' sv errv ->
PBOKat m' ts 0 ->
AJ5 A4L HIx A T md
(Q1Y6.Mq2.pe_msE pf pa 0x94954 (Z_to_bv 64 (pf_tk pf / 8 + 2147450884)) gp (Z_to_bv 64 (pf_tk pf / 8 + 3)) t1 t2 (Z_to_bv 64 (pf_sb pf + t_co ts + 1)) (Z_to_bv 64 0) a2' (Z_to_bv 64 0)
(Z_to_bv 64 (bv_unsigned cb)) a5' a6 (Z_to_bv 64 (t_pb ts))
(Z_to_bv 64 (t_co ts - t_co ts)) (Z_to_bv 64 1) s5 (Z_to_bv 64 (pf_sb pf + t_co ts)) (Z_to_bv 64 (pf_tk pf + 32)) (Z_to_bv 64 (pa_F pa)) (Z_to_bv 64 q)
(Z_to_bv 64 (pf_sb pf + t_co ts)) (Z_to_bv 64 (pf_tk pf + 64)) (Z_to_bv 64 (pa_F pa + 64)) (Z_to_bv 64 (pf_tk pf / 8 + 2147450888)) (Z_to_bv 64 (pf_lenr pf)) F fc m')) ->

(forall m' pj' a0' a1' a2' a3' a5',
pj_16 pj' = Z_to_bv 64 (pf_tk pf / 8 + 2147450881) -> bv_unsigned cb = 0 ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md A B ts cb nb pj' sv errv ->
PBOKat m' ts 0 ->
AJ5 A4L HIx A T md
(Q1Y6.Mq2.pe_msE pf pa 0x94b20 (Z_to_bv 64 (pf_tk pf / 8 + 2147450884)) gp (Z_to_bv 64 (pf_tk pf / 8 + 3)) t1 t2 a0' a1' a2' a3'
(Z_to_bv 64 (bv_unsigned cb)) a5' a6 (Z_to_bv 64 (t_pb ts))
(Z_to_bv 64 (t_co ts - t_co ts)) (Z_to_bv 64 (pf_tk pf + 20)) s5 (Z_to_bv 64 (pf_sb pf + t_co ts)) (Z_to_bv 64 (pf_tk pf + 32)) (Z_to_bv 64 (pa_F pa)) (Z_to_bv 64 q)
(Z_to_bv 64 (pf_sb pf + t_co ts)) (Z_to_bv 64 (pf_tk pf + 64)) (Z_to_bv 64 (pa_F pa + 64)) (Z_to_bv 64 (pf_tk pf / 8 + 2147450888)) (Z_to_bv 64 (pf_lenr pf)) F fc m')) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa (pe_jtA ST_number) (t_co ts) gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 (Z_to_bv 64 q) (Z_to_bv 64 (pa_F pa + 64)) F fc m).
Proof.
intros until fc. intros STC INV NUMC Hl Hst Hco Kloop Kexit. pose proof INV as INV0.
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
destruct INV as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof REST as (HP & _).
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
pose proof FR as FR0. unfold pe_frameA in FR. destruct FR as (SLOTS & GAP & SAVED & FF & FSH).
unfold pe_slotsA in SLOTS. cbn zeta in SLOTS. unfold ff_cellsA in FF.
unfold Q1Y6.Mq2.pe_msE, pe_msA in *.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
set (PF := PEF tk oldl newl len lenr sb spf pmd mxd fl) in *. set (PA := PEFA sp0 Ff oldloc newloc bsl dsl) in *.
assert (INtk : In (tk, 72) (pe_blocksA PF q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 1 HP INtk ltac:(lia)) as SHT1.
replace (tk / 8 + 1 + A_SB) with (tk / 8 + 2147450881) in SHT1 by (unfold A_SB; lia).
destruct NUMC as (buf & bpos & cap & post & Epbs & Lpre & PCORE). cbn [length Z.of_nat] in Lpre. subst bpos.
assert (PBK0 : PBOKat m ts0 0) by (exists buf, 0, cap, [], post; split; [exact Epbs | split; [reflexivity | split; [exact PCORE | lia]]]).
destruct PCORE as (_ & Hcap & Hlen & PBC & BUFC).
assert (INpb : In (pb, PB_SZ) (pe_blocksA PF q LB0 ts0)) by (unfold pe_blocksA, tstate_blocks, ts0; cbn [t_pbs]; rewrite Epbs; apply in_or_app; left; left; reflexivity).
blk_factsA A4L HIx HP pb 16 Hpal Hplo Hphi Himg_p.
pose proof (blk_granA HIx _ _ _ _ _ _ _ pb 16 1 HP INpb ltac:(lia) ltac:(lia)) as SHP1.
replace (pb / 8 + 1 + A_SB) with (pb / 8 + 2147450881) in SHP1 by (unfold A_SB; lia).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(spf, spf + 312)] m) as MU.
pose proof (bv_unsigned_in_range 8 cb) as CBR; unfold bv_modulus in CBR; cbn in CBR.
set (pj1 := PEJA (pj_0 pj) (pj_8 pj) (Z_to_bv 64 (tk / 8 + 2147450881)) (pj_obj pj) (pj_288 pj) (pj_304 pj) (pj_gap pj) (pj_fhd pj) (pj_f1 pj) (pj_f2 pj)).
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8, A_SB in *.
stash Himg_t. stash Himg_p. stash Kloop. stash Kexit. stash INV0. stash FR0. stash PBK0. stash TSK. stash REST. stash PB. stash BUFC.
reenterA asegs A4L HIx asegs_wx HP. unfold ST_number. cbn [pe_jtA].
step.
step. step.
sh_norm.
repeat match goal with
| |- context [ (?p + ?j) / 8 ] => is_Zlit j; rewrite (div8_add p j) by lia; let k := eval vm_compute in (Z.div j 8) in change (j / 8) with k
end.
replace (tk / 8 + 1 + 2147450880) with (tk / 8 + 2147450881) by lia.
stepz.
step.
rewrite ?sxb_zero, ?zxb_zero.
step.
first [ if_true | if_false ].
step.
step.
asan_chkA.
step.
step.
step.
lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with false by (vm_compute; reflexivity); cbv iota end.
step.
step. step.
step.
change (zxb cb) with (Z_to_bv 64 (bv_unsigned cb)).
step.
step.
sh_norm.
repeat match goal with
| |- context [ (?p + ?j) / 8 ] => is_Zlit j; rewrite (div8_add p j) by lia; let k := eval vm_compute in (Z.div j 8) in change (j / 8) with k
end.
step.
step.
unstash INV0. unstash FR0. unstash PBK0.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, SLc : rw_cells asegs mc spf _ |- _ =>
assert (FRc : pe_frameA asegs mc PF PA cb nb pj1 sv)
by (eapply (pe_frameA_slotw HIx PF PA _ LM FRS B A m mc md lo [] cb nb pj pj1 sv);
[ exact STC | exact HP | apply Forall_nil | exact FR0 | exact MUc | exact WMc | exact SLc | reflexivity | reflexivity | reflexivity | reflexivity ]);
destruct (PE_INV_A_framew HIx GA GA_outside PF PA q LB0 LM FRS payload me lo m mc md A B ts0
cb nb pj sv errv [(spf, spf + 312)] cb nb pj1 STC INV0 MUc WMc MIc
ltac:(apply Forall_cons; [right; left; cbn [fst snd pf_spf pa_sp0 PF PA]; lia | apply Forall_nil]) TOKc FRc) as [INV1 PBT1]
end end.
destruct (Z.eq_dec (bv_unsigned cb) 0) as [C0 | Cn].
- if_truex.
step. step.
evt_done5. unstash Kexit. replace (co - co) with 0 in Kexit by lia.
eapply (Kexit _ pj1); [reflexivity | exact C0 | exact INV1 | exact (PBT1 _ PBK0)].
- if_falsex.
step.
step.
step.
evt_done5. unstash Kloop. replace (co - co) with 0 in Kloop by lia.
eapply (Kloop _ pj1); [reflexivity | exact Cn | exact INV1 | exact (PBT1 _ PBK0)].
Qed.

Lemma num_bare : forall pf pa q LB0 LM FRS payload me lo m md A B ts errv (FRX : Prop) l,
PE_INV_AX HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts errv FRX ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_number ->
TL (tl_st l) (tl_ss l) 0 None [] 0 [] = l.
Proof.
intros pf pa q LB0 LM FRS payload me lo m md A B ts errv FRX l [_ REST] Hl Hst.
pose proof REST as (_ & LV & _).
pose proof (LV _ l Hl) as (_ & SS26 & JO & Md). rewrite Nat.ltb_irrefl, Nat.eqb_refl in Md. destruct Md as (c0 & hn0 & Hmode & CLS0 & NM0).
destruct (number_mode_ss _ _ _ SS26 ltac:(rewrite <- Hst; exact Hmode)) as (Ec0 & Ehn0 & Ess). subst c0 hn0.
cbn [name_ok] in NM0. destruct NM0 as [Hn0 Hnbs0].
assert (Ecs : tl_cs l = None) by (destruct (tl_cs l); [exfalso; exact CLS0 | reflexivity]).
rewrite Ecs in JO. cbn [jopt] in JO. destruct JO as [Ecur Ecbs].
destruct l as [st_ ss_ cur_ cs_ cbs_ name_ nbs_]; cbn [tl_st tl_ss tl_cur tl_cs tl_cbs tl_name tl_nbs] in *. congruence.
Qed.

Lemma num_ints_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP : Z) (nB : nat)
(x1 gp t0 t1 t2 a0 a1 a2 a3 a5 a6 a7 s3 t4 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa -> 0 <= pa_dslack pa -> pf_fl pf = 0 ->
NUM_INVX pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv 0xf8 ->
PBOKat m ts kP -> BOK pf pa ts B (S (Z.to_nat (16 * Z.max 0 (pf_len pf) + 8192) + nB)) ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_number ->
(forall m' md' A' B' errv' pj' r sh BS gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' F' fc',
(length BS <= 4)%nat -> (exists w, jfresh sh BS w /\ w <= Z.max 20 (kP + 16)) -> (sh = Sint \/ sh = Sdouble true) ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' (ts_lvl ts (TL ST_eatws ST_finish r (Some sh) BS 0 [])) cb nb pj' sv errv' ->
PBOKat m' (ts_lvl ts (TL ST_eatws ST_finish r (Some sh) BS 0 [])) kP ->
BOK pf pa (ts_lvl ts (TL ST_eatws ST_finish r (Some sh) BS 0 [])) B' nB ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msA asegs pf pa APE_REDO (t_co ts) gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' (Z_to_bv 64 (pf_tk pf + 56)) (Z_to_bv 64 (pa_F pa + 64)) F' fc' m')) ->
(forall m' md' A' B' errv' pj' ts' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' s11' t4' t6' F' fc',
t_levels ts' = t_levels ts -> t_depth ts' = t_depth ts -> t_objs ts' = t_objs ts ->
PE_INVW_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' ts' [] cb nb pj' sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msO asegs pf pa APE_OUT x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' (Z_to_bv 64 (pf_tk pf + 56)) s11' t4' t6' F' fc' m')) ->
AJ5 A4L HIx A T md
(Q1Y6.Mq2.pe_msE pf pa 0x954c0 x1 gp t0 t1 t2 a0 a1 a2 a3 (Z_to_bv 64 (pf_tk pf + 8)) a5 a6 a7
s3 (Z_to_bv 64 (pf_tk pf + 20)) (Z_to_bv 64 (pf_tk pf / 8 + 2147450887)) (Z_to_bv 64 (pf_sb pf + t_co ts)) (Z_to_bv 64 (pf_tk pf + 32)) (Z_to_bv 64 (pa_F pa)) (Z_to_bv 64 (pf_tk pf + 56))
(Z_to_bv 64 (pf_tk pf / 8 + 2147450881)) (Z_to_bv 64 (pf_tk pf + 64)) t4 (Z_to_bv 64 (pf_tk pf / 8 + 2147450888)) t6 F fc m).
Proof.
intros until fc. intros STC BSL DSL FL0 NX PBK BK Hl Hst Kredo Kout.
assert (El : TL (tl_st l) (tl_ss l) 0 None [] 0 [] = l) by (destruct NX as (? & ? & ? & ? & ? & ? & ? & ? & INVX); exact (num_bare _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ l INVX Hl Hst)).
eapply (num_errno_A pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv T); [exact STC | exact FL0 | exact NX |].
intros x1' a0' a1'.
eapply (num_newint_A pf pa q LB0 LM FRS payload me lo m md A B ts l cb nb pj sv errv T kP nB); [exact STC | exact BSL | exact DSL | exact NX | exact PBK | exact BK | exact Hl | exact Hst |].
intros m2 md2 A2 B2 errv2 r gp' t0' t1' t2' a2' a3' a4' a5' a6' a7' F2 fc2 WR PBK2 HB2 HD2 FS2 FRM2.
rewrite El in WR, PBK2. rewrite (ts_lvl_same ts l Hl) in WR, PBK2.
eapply (num_tail_A pf pa q LB0 LM FRS payload me lo m2 md2 A2 B B2 ts l cb nb pj sv errv2 T kP newint_costB r Sint nB);
[ exact STC | exact BSL | exact WR | exact Hl | rewrite <- El; reflexivity | left; reflexivity | exact PBK2 | exact BK | exact HB2 | exact HD2
| unfold newint_costB; lia | pose proof (K_ev_pos pf); unfold newint_costB, K_free; lia | | ].
- intros m' pj' BS t0'' a0'' a1'' a2'' s5'' LBS JF INV' PBK' BK'.
eapply (Kredo m' md2 A2 B2 errv2 pj' r Sint BS); [exact LBS | exact JF | left; reflexivity | exact INV' | exact PBK' | exact BK' | exact FS2 | exact FRM2].
- intros m' pj' x1'' gp'' t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' s5'' s7'' s11'' t4'' t6'' INVW'.
eapply (Kout m' md2 A2 B2 errv2 pj' _); [| | | exact INVW' | exact FS2 | exact FRM2]; reflexivity.
Qed.

Lemma num_uints_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP : Z) (nB : nat)
(x1 gp t0 t1 t2 a0 a1 a2 a3 a5 a6 a7 s3 t4 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa -> 0 <= pa_dslack pa -> pf_fl pf = 0 ->
NUM_INVX pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv 0xf8 ->
PBOKat m ts kP -> BOK pf pa ts B (S (Z.to_nat (16 * Z.max 0 (pf_len pf) + 8192) + nB)) ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_number ->
(forall m' md' A' B' errv' pj' r sh BS gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' F' fc',
(length BS <= 4)%nat -> (exists w, jfresh sh BS w /\ w <= Z.max 20 (kP + 16)) -> (sh = Sint \/ sh = Sdouble true) ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' (ts_lvl ts (TL ST_eatws ST_finish r (Some sh) BS 0 [])) cb nb pj' sv errv' ->
PBOKat m' (ts_lvl ts (TL ST_eatws ST_finish r (Some sh) BS 0 [])) kP ->
BOK pf pa (ts_lvl ts (TL ST_eatws ST_finish r (Some sh) BS 0 [])) B' nB ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msA asegs pf pa APE_REDO (t_co ts) gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' (Z_to_bv 64 (pf_tk pf + 56)) (Z_to_bv 64 (pa_F pa + 64)) F' fc' m')) ->
(forall m' md' A' B' errv' pj' ts' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' s11' t4' t6' F' fc',
t_levels ts' = t_levels ts -> t_depth ts' = t_depth ts -> t_objs ts' = t_objs ts ->
PE_INVW_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' ts' [] cb nb pj' sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msO asegs pf pa APE_OUT x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' (Z_to_bv 64 (pf_tk pf + 56)) s11' t4' t6' F' fc' m')) ->
AJ5 A4L HIx A T md
(Q1Y6.Mq2.pe_msE pf pa 0x9556c x1 gp t0 t1 t2 a0 a1 a2 a3 (Z_to_bv 64 (pf_tk pf + 8)) a5 a6 a7
s3 (Z_to_bv 64 (pf_tk pf + 20)) (Z_to_bv 64 (pf_tk pf / 8 + 2147450887)) (Z_to_bv 64 (pf_sb pf + t_co ts)) (Z_to_bv 64 (pf_tk pf + 32)) (Z_to_bv 64 (pa_F pa)) (Z_to_bv 64 (pf_tk pf + 56))
(Z_to_bv 64 (pf_tk pf / 8 + 2147450881)) (Z_to_bv 64 (pf_tk pf + 64)) t4 (Z_to_bv 64 (pf_tk pf / 8 + 2147450888)) t6 F fc m).
Proof.
intros until fc. intros STC BSL DSL FL0 NX PBK BK Hl Hst Kredo Kout.
assert (El : TL (tl_st l) (tl_ss l) 0 None [] 0 [] = l) by (destruct NX as (? & ? & ? & ? & ? & ? & ? & ? & INVX); exact (num_bare _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ l INVX Hl Hst)).
eapply (num_errnou_A pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv T); [exact STC | exact FL0 | exact NX |].
intros x1' a0' a1'.
eapply (num_udisp_A pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv T); [exact STC | exact NX | |].
- intros a0''.
eapply (num_newuint_A pf pa q LB0 LM FRS payload me lo m md A B ts l cb nb pj sv errv T kP nB); [exact STC | exact BSL | exact DSL | exact NX | exact PBK | exact BK | exact Hl | exact Hst |].
intros m2 md2 A2 B2 errv2 r gp' t0' t1' t2' a2' a3' a4' a5' a6' a7' F2 fc2 WR PBK2 HB2 HD2 FS2 FRM2.
rewrite El in WR, PBK2. rewrite (ts_lvl_same ts l Hl) in WR, PBK2.
eapply (num_tail_A pf pa q LB0 LM FRS payload me lo m2 md2 A2 B B2 ts l cb nb pj sv errv2 T kP newint_costB r Sint nB);
[ exact STC | exact BSL | exact WR | exact Hl | rewrite <- El; reflexivity | left; reflexivity | exact PBK2 | exact BK | exact HB2 | exact HD2
| unfold newint_costB; lia | pose proof (K_ev_pos pf); unfold newint_costB, K_free; lia | | ].
+ intros m' pj' BS t0x a0x a1x a2x s5x LBS JF INV' PBK' BK'.
eapply (Kredo m' md2 A2 B2 errv2 pj' r Sint BS); [exact LBS | exact JF | left; reflexivity | exact INV' | exact PBK' | exact BK' | exact FS2 | exact FRM2].
+ intros m' pj' x1x gpx t0x t1x t2x a0x a1x a2x a3x a4x a5x a6x a7x s5x s7x s11x t4x t6x INVW'.
eapply (Kout m' md2 A2 B2 errv2 pj' _); [| | | exact INVW' | exact FS2 | exact FRM2]; reflexivity.
- intros m1 a0'' a1'' NX1 PBT1.
eapply (num_newint2_A pf pa q LB0 LM FRS payload me lo m1 md A B ts l cb nb pj sv errv T kP nB); [exact STC | exact BSL | exact DSL | exact NX1 | exact (PBT1 _ PBK) | exact BK | exact Hl | exact Hst |].
intros m2 md2 A2 B2 errv2 r gp' t0' t1' t2' a2' a3' a4' a5' a6' a7' F2 fc2 WR PBK2 HB2 HD2 FS2 FRM2.
rewrite El in WR, PBK2. rewrite (ts_lvl_same ts l Hl) in WR, PBK2.
eapply (num_tail_A pf pa q LB0 LM FRS payload me lo m2 md2 A2 B B2 ts l cb nb pj sv errv2 T kP newint_costB r Sint nB);
[ exact STC | exact BSL | exact WR | exact Hl | rewrite <- El; reflexivity | left; reflexivity | exact PBK2 | exact BK | exact HB2 | exact HD2
| unfold newint_costB; lia | pose proof (K_ev_pos pf); unfold newint_costB, K_free; lia | | ].
+ intros m' pj' BS t0x a0x a1x a2x s5x LBS JF INV' PBK' BK'.
eapply (Kredo m' md2 A2 B2 errv2 pj' r Sint BS); [exact LBS | exact JF | left; reflexivity | exact INV' | exact PBK' | exact BK' | exact FS2 | exact FRM2].
+ intros m' pj' x1x gpx t0x t1x t2x a0x a1x a2x a3x a4x a5x a6x a7x s5x s7x s11x t4x t6x INVW'.
eapply (Kout m' md2 A2 B2 errv2 pj' _); [| | | exact INVW' | exact FS2 | exact FRM2]; reflexivity.
Qed.

Lemma num_dbl2_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP v2 ra2 : Z) (nB : nat)
(x1 gp t0 t1 t2 a0 a1 a2 a3 a5 a6 a7 s3 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa -> 0 <= pa_dslack pa -> pf_fl pf = 0 ->
NUM_INVX pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv 0xf8 ->
PBOKat m ts kP -> BOK pf pa ts B (S (Z.to_nat (16 * Z.max 0 (pf_len pf) + 8192) + nB)) ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_number ->
frm0 fc -> pj_16 pj = Z_to_bv 64 (pf_tk pf / 8 + 2147450881) -> 0 <= kP <= pf_len pf ->
pe_s0 sv = Z_to_bv 64 v2 -> pe_ra sv = Z_to_bv 64 ra2 ->
(v2 < alloc_ceiling \/ v2 mod 8 <> 0 \/ v2 <= pa_sp0 pa \/ hiA_top A4L HIx - 16 <= v2) /\ 0 <= v2 < 2^64 ->
uw_ok A4L (hl_malloc A4H) (Z_to_bv 64 0x9daec) (UWfp ra2 v2) ->
(forall m' md' A' B' errv' pj' r sh BS gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' F' fc',
(length BS <= 4)%nat -> (exists w, jfresh sh BS w /\ w <= Z.max 20 (kP + 16)) -> (sh = Sint \/ sh = Sdouble true) ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' (ts_lvl ts (TL ST_eatws ST_finish r (Some sh) BS 0 [])) cb nb pj' sv errv' ->
PBOKat m' (ts_lvl ts (TL ST_eatws ST_finish r (Some sh) BS 0 [])) kP ->
BOK pf pa (ts_lvl ts (TL ST_eatws ST_finish r (Some sh) BS 0 [])) B' nB ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msA asegs pf pa APE_REDO (t_co ts) gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' (Z_to_bv 64 (pf_tk pf + 56)) (Z_to_bv 64 (pa_F pa + 64)) F' fc' m')) ->
(forall m' md' A' B' errv' pj' ts' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' s11' t4' t6' F' fc',
t_levels ts' = t_levels ts -> t_depth ts' = t_depth ts -> t_objs ts' = t_objs ts ->
PE_INVW_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' ts' [] cb nb pj' sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msO asegs pf pa APE_OUT x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' (Z_to_bv 64 (pf_tk pf + 56)) s11' t4' t6' F' fc' m')) ->
AJ5 A4L HIx A T md
(Q1Y6.Mq2.pe_msE pf pa 0x95350 x1 gp t0 t1 t2 a0 a1 a2 a3 (Z_to_bv 64 (pf_tk pf + 8)) a5 a6 a7
s3 (Z_to_bv 64 (pf_tk pf + 20)) (Z_to_bv 64 (pf_tk pf / 8 + 2147450887)) (Z_to_bv 64 (pf_sb pf + t_co ts)) (Z_to_bv 64 (pf_tk pf + 32)) (Z_to_bv 64 (pa_F pa)) (Z_to_bv 64 (pf_tk pf + 56))
(Z_to_bv 64 (pf_tk pf / 8 + 2147450881)) t3 t4 t5 t6 F fc m).
Proof.
intros until fc. intros STC BSL DSL FL0 NX PBK BK Hl Hst FRM P16 HkP S0V RAV HV UWK Kredo Kout.
assert (El : TL (tl_st l) (tl_ss l) 0 None [] 0 [] = l) by (destruct NX as (? & ? & ? & ? & ? & ? & ? & ? & INVX); exact (num_bare _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ l INVX Hl Hst)).
eapply (num_dbl_A pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv T kP); [exact STC | exact FRM | exact NX | exact PBK | |].
- intros m1 errv1 x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' s4' t3' t4' t5' t6' F1 fc1 NX1 PBK1 FS1 FRM1.
eapply (num_dbls_A pf pa q LB0 LM FRS payload me lo m1 md A B ts l cb nb pj sv errv1 T kP v2 ra2 nB);
[exact STC | exact BSL | exact DSL | exact NX1 | exact PBK1 | exact BK | exact Hl | exact Hst | exact P16 | exact HkP | exact S0V | exact RAV | exact HV | exact UWK |].
intros m2 md2 A2 B2 errv2 r gp'' t0'' t1'' t2'' a2'' a3'' a4'' a5'' a6'' a7'' F2 fc2 WR PBK2 HB2 HD2 FS2 FRM2.
rewrite El in WR, PBK2. rewrite (ts_lvl_same ts l Hl) in WR, PBK2.
eapply (num_taild_A pf pa q LB0 LM FRS payload me lo m2 md2 A2 B B2 ts l cb nb pj sv errv2 T kP (newdbls_costB kP) r (Sdouble true) nB);
[ exact STC | exact BSL | exact WR | exact Hl | rewrite <- El; reflexivity | right; reflexivity | exact PBK2 | exact BK | exact HB2 | exact HD2
| unfold newdbls_costB; lia | unfold newdbls_costB, K_free, K_ev; lia | | ].
+ intros m' pj' BS t0x a0x a1x a2x s5x LBS JF INV' PBK' BK'.
eapply (Kredo m' md2 A2 B2 errv2 pj' r (Sdouble true) BS); [exact LBS | exact JF | right; reflexivity | exact INV' | exact PBK' | exact BK' | eapply fsaved_trans; [exact FS1 | exact FS2] | intros X; exact (FRM2 (FRM1 X))].
+ intros m' pj' x1x gpx t0x t1x t2x a0x a1x a2x a3x a4x a5x a6x a7x s5x s7x s11x t4x t6x INVW'.
eapply (Kout m' md2 A2 B2 errv2 pj' _); [| | | exact INVW' | eapply fsaved_trans; [exact FS1 | exact FS2] | intros X; exact (FRM2 (FRM1 X))]; reflexivity.
- intros m1 errv1 x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' s4' t3' t4' t5' t6' F1 fc1 NX1 FS1 FRM1.
eapply (num_err7d_A pf pa q LB0 LM FRS payload me lo m1 md A B ts cb nb pj sv errv1 T); [exact STC | exact NX1 |].
intros m' pj' x1x gpx t0x t1x t2x a0x a1x a2x a3x a4x a5x a6x a7x s5x s7x s11x t4x t6x INV'.
eapply (Kout m' md A B errv1 pj' _); [| | | apply (PE_INV_A_W HIx GA); exact INV' | exact FS1 | exact FRM1]; reflexivity.
Qed.

Lemma num_convs_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP v2 ra2 : Z) (nB : nat)
(gp t1 t2 a1 a2 a3 a5 a6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa -> 0 <= pa_dslack pa -> pf_fl pf = 0 -> Z.of_nat (length FRS) + 1 < 4096 ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
PBOKat m ts kP -> 0 <= kP <= t_co ts -> BOK pf pa ts B (S (Z.to_nat (16 * Z.max 0 (pf_len pf) + 8192) + nB)) ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_number ->
frm0 fc -> pj_16 pj = Z_to_bv 64 (pf_tk pf / 8 + 2147450881) ->
pe_s0 sv = Z_to_bv 64 v2 -> pe_ra sv = Z_to_bv 64 ra2 ->
(v2 < alloc_ceiling \/ v2 mod 8 <> 0 \/ v2 <= pa_sp0 pa \/ hiA_top A4L HIx - 16 <= v2) /\ 0 <= v2 < 2^64 ->
uw_ok A4L (hl_malloc A4H) (Z_to_bv 64 0x9daec) (UWfp ra2 v2) ->
(forall m' md' A' B' errv' pj' r sh BS gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' F' fc',
(length BS <= 4)%nat -> (exists w, jfresh sh BS w /\ w <= Z.max 20 (kP + 16)) -> (sh = Sint \/ sh = Sdouble true) ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' (ts_lvl ts (TL ST_eatws ST_finish r (Some sh) BS 0 [])) cb nb pj' sv errv' ->
PBOKat m' (ts_lvl ts (TL ST_eatws ST_finish r (Some sh) BS 0 [])) kP ->
BOK pf pa (ts_lvl ts (TL ST_eatws ST_finish r (Some sh) BS 0 [])) B' nB ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msA asegs pf pa APE_REDO (t_co ts) gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' (Z_to_bv 64 (pf_tk pf + 56)) (Z_to_bv 64 (pa_F pa + 64)) F' fc' m')) ->
(forall m' md' A' B' errv' pj' ts' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' s11' t4' t6' F' fc',
t_levels ts' = t_levels ts -> t_depth ts' = t_depth ts -> t_objs ts' = t_objs ts ->
PE_INVW_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' ts' [] cb nb pj' sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msO asegs pf pa APE_OUT x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' (Z_to_bv 64 (pf_tk pf + 56)) s11' t4' t6' F' fc' m')) ->
AJ5 A4L HIx A T md
(Q1Y6.Mq2.pe_msE pf pa 0x95260 (Z_to_bv 64 (pf_tk pf / 8 + 2147450884)) gp (Z_to_bv 64 (pf_tk pf / 8 + 3)) t1 t2 (sx32 (ts_isd (t_x ts))) a1 a2 a3 (Z_to_bv 64 (pf_tk pf + 8)) a5 a6 (Z_to_bv 64 (pf_tk pf + 24))
(Z_to_bv 64 (pf_tk pf / 8 + 2147450883)) (Z_to_bv 64 (pf_tk pf + 20)) (Z_to_bv 64 (pf_tk pf / 8 + 2147450887)) (Z_to_bv 64 (pf_sb pf + t_co ts)) (Z_to_bv 64 (pf_tk pf + 32)) (Z_to_bv 64 (pa_F pa)) (Z_to_bv 64 (pf_tk pf + 56))
(Z_to_bv 64 (pf_tk pf / 8 + 2147450881)) (Z_to_bv 64 (pf_tk pf + 64)) (Z_to_bv 64 (pa_F pa + 64)) (Z_to_bv 64 (pf_tk pf / 8 + 2147450888)) (Z_to_bv 64 (pf_lenr pf)) F fc m).
Proof.
intros until fc. intros STC BSL DSL FL0 FRN INV PBK HkPc BK Hl Hst FRM P16 S0V RAV HV UWK Kredo Kout.
assert (HkP : 0 <= kP <= pf_len pf) by (destruct INV as [(_ & _ & CO & _) _]; lia).

assert (DBLK : forall m1 md1 A1 errv1 x1 gp1 t0 t11 t21 a0 a11 a21 a31 a51 a61 a7 s3 t3 t4 t5 t6,
NUM_INVX pf pa q LB0 LM FRS payload me lo m1 md1 A1 B ts cb nb pj sv errv1 0xf8 -> PBOKat m1 ts kP ->
AJ5 A4L HIx A1 T md1
(Q1Y6.Mq2.pe_msE pf pa 0x95350 x1 gp1 t0 t11 t21 a0 a11 a21 a31 (Z_to_bv 64 (pf_tk pf + 8)) a51 a61 a7
s3 (Z_to_bv 64 (pf_tk pf + 20)) (Z_to_bv 64 (pf_tk pf / 8 + 2147450887)) (Z_to_bv 64 (pf_sb pf + t_co ts)) (Z_to_bv 64 (pf_tk pf + 32)) (Z_to_bv 64 (pa_F pa)) (Z_to_bv 64 (pf_tk pf + 56))
(Z_to_bv 64 (pf_tk pf / 8 + 2147450881)) t3 t4 t5 t6 F fc m1)).
{ intros m1 md1 A1 errv1 x1 gp1 t0 t11 t21 a0 a11 a21 a31 a51 a61 a7 s3 t3 t4 t5 t6 NX1 PBK1.
eapply (num_dbl2_A pf pa q LB0 LM FRS payload me lo m1 md1 A1 B ts l cb nb pj sv errv1 T kP v2 ra2 nB);
[exact STC | exact BSL | exact DSL | exact FL0 | exact NX1 | exact PBK1 | exact BK | exact Hl | exact Hst | exact FRM | exact P16 | exact HkP | exact S0V | exact RAV | exact HV | exact UWK | exact Kredo | exact Kout]. }

assert (U1K : forall m1 md1 A1 errv1 x1 gp1 t0 t11 t21 a0 a11 a21 a31 a51 a61 a7 t4 t6,
NUM_INVX pf pa q LB0 LM FRS payload me lo m1 md1 A1 B ts cb nb pj sv errv1 0xf8 -> PBOKat m1 ts kP ->
AJ5 A4L HIx A1 T md1
(Q1Y6.Mq2.pe_msE pf pa 0x95338 x1 gp1 t0 t11 t21 a0 a11 a21 a31 (Z_to_bv 64 (pf_tk pf + 8)) a51 a61 a7
(Z_to_bv 64 (pf_tk pf / 8 + 2147450883)) (Z_to_bv 64 (pf_tk pf + 20)) (Z_to_bv 64 (pf_tk pf / 8 + 2147450887)) (Z_to_bv 64 (pf_sb pf + t_co ts)) (Z_to_bv 64 (pf_tk pf + 32)) (Z_to_bv 64 (pa_F pa)) (Z_to_bv 64 (pf_tk pf + 56))
(Z_to_bv 64 (pf_tk pf / 8 + 2147450881)) (Z_to_bv 64 (pf_tk pf + 64)) t4 (Z_to_bv 64 (pf_tk pf / 8 + 2147450888)) t6 F fc m1)).
{ intros m1 md1 A1 errv1 x1 gp1 t0 t11 t21 a0 a11 a21 a31 a51 a61 a7 t4 t6 NX1 PBK1.
eapply (num_u1_A pf pa q LB0 LM FRS payload me lo m1 md1 A1 B ts cb nb pj sv errv1 T); [exact STC | exact NX1 | |].
- intros a0'. eapply DBLK; [exact NX1 | exact PBK1].
- intros a0'. eapply (num_err7x_A pf pa q LB0 LM FRS payload me lo m1 md1 A1 B ts cb nb pj sv errv1 T); [exact STC | exact NX1 |].
intros m' pj' x1x gpx t0x t1x t2x a0x a1x a2x a3x a4x a5x a6x a7x s5x s7x s11x t4x t6x INV'.
eapply (Kout m' md1 A1 B errv1 pj' _); [| | | apply (PE_INV_A_W HIx GA); exact INV' | apply fsaved_refl | intros X; exact X]; reflexivity. }

assert (U0K : forall m1 md1 A1 errv1 x1 gp1 t0 t11 t21 a0 a11 a21 a31 a51 a61 a7 t4 t6,
NUM_INVX pf pa q LB0 LM FRS payload me lo m1 md1 A1 B ts cb nb pj sv errv1 0xf8 -> PBOKat m1 ts kP ->
AJ5 A4L HIx A1 T md1
(Q1Y6.Mq2.pe_msE pf pa 0x952c8 x1 gp1 t0 t11 t21 a0 a11 a21 a31 (Z_to_bv 64 (pf_tk pf + 8)) a51 a61 a7
(Z_to_bv 64 (pf_tk pf / 8 + 2147450883)) (Z_to_bv 64 (pf_tk pf + 20)) (Z_to_bv 64 (pf_tk pf / 8 + 2147450887)) (Z_to_bv 64 (pf_sb pf + t_co ts)) (Z_to_bv 64 (pf_tk pf + 32)) (Z_to_bv 64 (pa_F pa)) (Z_to_bv 64 (pf_tk pf + 56))
(Z_to_bv 64 (pf_tk pf / 8 + 2147450881)) (Z_to_bv 64 (pf_tk pf + 64)) t4 (Z_to_bv 64 (pf_tk pf / 8 + 2147450888)) t6 F fc m1)).
{ intros m1 md1 A1 errv1 x1 gp1 t0 t11 t21 a0 a11 a21 a31 a51 a61 a7 t4 t6 NX1 PBK1.
eapply (num_u0_A pf pa q LB0 LM FRS payload me lo m1 md1 A1 B ts cb nb pj sv errv1 T _); [exact STC | exact NX1 | exact BK | | |].
- intros a0' a1' a2'. eapply DBLK; [exact NX1 | exact PBK1].
- intros buf cap a1' a2' Epbs.
eapply (num_puint_A pf pa q LB0 LM FRS payload me lo m1 md1 A1 B ts cb nb pj sv errv1 T kP buf cap); [exact STC | exact NX1 | exact PBK1 | exact Epbs | exact FRN | |].
+ intros m2 md2 A2 errv2 x1' gp' t0' t1' t2' a0' a1'' a2'' a3' a5' a6' a7' t4' t6' NX2 PBK2.
eapply (num_uints_A pf pa q LB0 LM FRS payload me lo m2 md2 A2 B ts l cb nb pj sv errv2 T kP nB);
[exact STC | exact BSL | exact DSL | exact FL0 | exact NX2 | exact PBK2 | exact BK | exact Hl | exact Hst | exact Kredo | exact Kout].
+ intros m2 md2 A2 errv2 x1' gp' t0' t1' t2' a0' a1'' a2'' a3' a5' a6' a7' t4' t6' NX2 PBK2.
eapply U1K; [exact NX2 | exact PBK2].
- intros a0' a1' a2'. eapply U1K; [exact NX1 | exact PBK1]. }
eapply (num_conv_A pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv T _); [exact STC | exact INV | exact BK | | |].
- intros m1 a0' a1' a2' NX1 PBT1. eapply DBLK; [exact NX1 | exact (PBT1 _ PBK)].
- intros m1 buf cap a1' a2' Epbs NX1 PBT1.
eapply (num_pint_A pf pa q LB0 LM FRS payload me lo m1 md A B ts cb nb pj sv errv T kP buf cap); [exact STC | exact NX1 | exact (PBT1 _ PBK) | exact Epbs | exact FRN | |].
+ intros m2 md2 A2 errv2 x1' gp' t0' t1' t2' a0' a1'' a2'' a3' a5' a6' a7' t4' t6' NX2 PBK2.
eapply (num_ints_A pf pa q LB0 LM FRS payload me lo m2 md2 A2 B ts l cb nb pj sv errv2 T kP nB);
[exact STC | exact BSL | exact DSL | exact FL0 | exact NX2 | exact PBK2 | exact BK | exact Hl | exact Hst | exact Kredo | exact Kout].
+ intros m2 md2 A2 errv2 x1' gp' t0' t1' t2' a0' a1'' a2'' a3' a5' a6' a7' t4' t6' NX2 PBK2.
eapply U0K; [exact NX2 | exact PBK2].
- intros m1 a0' a1' a2' NX1 PBT1. eapply U0K; [exact NX1 | exact (PBT1 _ PBK)].
Qed.

Lemma num_post_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel) (co0 k0 : Z)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (v2 ra2 : Z) (nB : nat)
(gp t1 t2 a0 a1 a2 a3 a5 a6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa -> 0 <= pa_dslack pa -> pf_fl pf = 0 -> Z.of_nat (length FRS) + 1 < 4096 ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
PBOKat m ts (co0 + k0) -> k0 <= 0 -> 0 <= co0 + k0 -> BOK pf pa ts B (S (Z.to_nat (16 * Z.max 0 (pf_len pf) + 8192) + nB)) ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_number ->
0 <= co0 <= t_co ts -> t_co ts < pf_len pf ->
frm0 fc -> pj_16 pj = Z_to_bv 64 (pf_tk pf / 8 + 2147450881) ->
pe_s0 sv = Z_to_bv 64 v2 -> pe_ra sv = Z_to_bv 64 ra2 ->
(v2 < alloc_ceiling \/ v2 mod 8 <> 0 \/ v2 <= pa_sp0 pa \/ hiA_top A4L HIx - 16 <= v2) /\ 0 <= v2 < 2^64 ->
uw_ok A4L (hl_malloc A4H) (Z_to_bv 64 0x9daec) (UWfp ra2 v2) ->

(forall m' md' A' B' pbs' errv' pj' r sh BS gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' F' fc',
(length BS <= 4)%nat -> (exists w, jfresh sh BS w /\ w <= Z.max 20 ((t_co ts + k0) + 16)) -> (sh = Sint \/ sh = Sdouble true) ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' (ts_lvl (ts_pbs ts pbs') (TL ST_eatws ST_finish r (Some sh) BS 0 [])) cb nb pj' sv errv' ->
PBOKat m' (ts_lvl (ts_pbs ts pbs') (TL ST_eatws ST_finish r (Some sh) BS 0 [])) (t_co ts + k0) ->
BOK pf pa (ts_lvl (ts_pbs ts pbs') (TL ST_eatws ST_finish r (Some sh) BS 0 [])) B' nB ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msA asegs pf pa APE_REDO (t_co ts) gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' (Z_to_bv 64 (pf_tk pf + 56)) (Z_to_bv 64 (pa_F pa + 64)) F' fc' m')) ->

(forall m' md' A' B' pbs' errv' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' F' fc',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B'
(ts_set_x (ts_lvl (ts_pbs ts pbs') (TL ST_inf (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) (t_co ts)
(TS (ts_isd (t_x ts)) (Z_to_bv 64 0) (ts_choff (t_x ts)) (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))) cb nb pj sv errv' ->
PBOKat m' (ts_set_x (ts_lvl (ts_pbs ts pbs') (TL ST_inf (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) (t_co ts)
(TS (ts_isd (t_x ts)) (Z_to_bv 64 0) (ts_choff (t_x ts)) (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))) (t_co ts + k0) ->
BOK pf pa (ts_pbs ts pbs') B' (S (Z.to_nat (16 * Z.max 0 (pf_len pf) + 8192) + nB)) ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msA asegs pf pa APE_REDO (t_co ts) gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' (Z_to_bv 64 (pf_tk pf + 56)) (Z_to_bv 64 (pa_F pa + 64)) F' fc' m')) ->

(forall m' md' A' B' errv' pj' ts' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' s11' t4' t6' F' fc',
t_levels ts' = t_levels ts -> t_depth ts' = t_depth ts -> t_objs ts' = t_objs ts ->
PE_INVW_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' ts' [] cb nb pj' sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msO asegs pf pa APE_OUT x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' (Z_to_bv 64 (pf_tk pf + 56)) s11' t4' t6' F' fc' m')) ->
AJ5 A4L HIx A T md
(Q1Y6.Mq2.pe_msE pf pa 0x94b20 (Z_to_bv 64 (pf_tk pf / 8 + 2147450884)) gp (Z_to_bv 64 (pf_tk pf / 8 + 3)) t1 t2 a0 a1 a2 a3 (Z_to_bv 64 (bv_unsigned cb)) a5 a6 (Z_to_bv 64 (t_pb ts))
(Z_to_bv 64 (t_co ts - co0)) (Z_to_bv 64 (pf_tk pf + 20)) (Z_to_bv 64 (Z.of_nat (t_depth ts))) (Z_to_bv 64 (pf_sb pf + t_co ts)) (Z_to_bv 64 (pf_tk pf + 32)) (Z_to_bv 64 (pa_F pa)) (Z_to_bv 64 q)
(Z_to_bv 64 (pf_sb pf + co0)) (Z_to_bv 64 (pf_tk pf + 64)) (Z_to_bv 64 (pa_F pa + 64)) (Z_to_bv 64 (pf_tk pf / 8 + 2147450888)) (Z_to_bv 64 (pf_lenr pf)) F fc m).
Proof.
intros until fc. intros STC BSL DSL FL0 FRN INV PBK K0 K1 BK Hl Hst Hco0 Hco FRM P16 S0V RAV HV UWK Kredo Kinf Kout.
eapply (num_chk_A pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv T); [exact STC | exact INV | |].
2:{ intros m' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' s11' t4' t6' INV'.
eapply (Kout m' md A B errv pj _); [| | | apply (PE_INV_A_W HIx GA); exact INV' | apply fsaved_refl | intros X; exact X]; reflexivity. }
intros a0' a1'.
eapply (num_app_A pf pa q LB0 LM FRS payload me lo m md A B ts co0 k0 cb nb pj sv errv T _); [exact STC | exact BSL | exact INV | exact PBK | exact K0 | exact BK | exact Hco0 | exact Hco | |].
2:{ intros m' md' A' B' pbs' errv' x1' gp' t0' t1' t2' a0'' a1'' a2' a3' a4' a5' a6' a7' s5' s7' s11' t4' t6' F' fc' INV' FS' FRM'.
eapply (Kout m' md' A' B' errv' pj _); [| | | apply (PE_INV_A_W HIx GA); exact INV' | exact FS' | exact FRM']; destruct ts; reflexivity. }
intros m1 md1 A1 B1 pbs1 errv1 gp1 t11 t21 a01 a11 a21 a31 a41 a51 a61 a71 s51 F1 fc1 INV1 PBK1 BK1 FS1 FRM1.
set (ts1 := ts_pbs ts pbs1) in *.
assert (Hl1 : nth_error (t_levels ts1) (t_depth ts1) = Some l) by (destruct ts; exact Hl).
assert (Eco1 : t_co ts1 = t_co ts) by (destruct ts; reflexivity).
assert (Ex1 : t_x ts1 = t_x ts) by (destruct ts; reflexivity).
assert (Epb1 : t_pb ts1 = t_pb ts) by (destruct ts; reflexivity).
assert (Ed1 : t_depth ts1 = t_depth ts) by (destruct ts; reflexivity).
rewrite <- Eco1 in PBK1 |- *.
eapply (num_minf_A pf pa q LB0 LM FRS payload me lo m1 md1 A1 B1 ts1 l co0 cb nb pj sv errv1 T (t_co ts1 + k0) _);
[exact STC | exact INV1 | exact PBK1 | lia | exact BK1 | exact Hl1 | exact Hst | exact P16 | rewrite Eco1; exact Hco0 | rewrite Eco1; exact Hco | |].
2:{ intros m' t0' a0'' a1'' a2'' a3'' a4'' s5'' INV' PBK'.
rewrite Eco1, Ex1 in INV', PBK'. rewrite Eco1.
eapply (Kinf m' md1 A1 B1 pbs1 errv1); [exact INV' | exact PBK' | exact BK1 | exact FS1 | exact FRM1]. }
intros a0'' a1'' a2'' a3''.
eapply (num_pre_A pf pa q LB0 LM FRS payload me lo m1 md1 A1 B1 ts1 cb nb pj sv errv1 T (t_co ts1 + k0)); [exact STC | exact FL0 | exact INV1 | exact PBK1 | lia |].
intros m2 a1x a2x a3x INV2 PBK2.
eapply (num_convs_A pf pa q LB0 LM FRS payload me lo m2 md1 A1 B1 ts1 l cb nb pj sv errv1 T (t_co ts1 + k0) v2 ra2 nB);
[exact STC | exact BSL | exact DSL | exact FL0 | exact FRN | exact INV2 | exact PBK2 | rewrite Eco1; lia | exact BK1 | exact Hl1 | exact Hst | exact (FRM1 FRM) | exact P16 | exact S0V | exact RAV | exact HV | exact UWK | |].
- intros m' md' A' B' errv' pj' r sh BS gp' t0' t1' t2' a0x a1y a2y a3y a4y a5y a6y a7y s5y F' fc' LBS JF Hsh INV' PBK' BK' FS' FRM'.
rewrite Eco1 in JF, PBK' |- *.
eapply (Kredo m' md' A' B' pbs1 errv' pj' r sh BS); [exact LBS | exact JF | exact Hsh | exact INV' | exact PBK' | exact BK' | eapply fsaved_trans; [exact FS1 | exact FS'] | intros X; exact (FRM' (FRM1 X))].
- intros m' md' A' B' errv' pj' ts' x1' gp' t0' t1' t2' a0x a1y a2y a3y a4y a5y a6y a7y s5y s7y s11y t4y t6y F' fc' E1 E2 E3 INVW' FS' FRM'.
eapply (Kout m' md' A' B' errv' pj' ts'); [rewrite E1; destruct ts; reflexivity | rewrite E2; destruct ts; reflexivity | rewrite E3; destruct ts; reflexivity | exact INVW' | eapply fsaved_trans; [exact FS1 | exact FS'] | intros X; exact (FRM' (FRM1 X))].
Qed.

Lemma seg_number_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (v2 ra2 : Z) (nB : nat)
(gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa -> 0 <= pa_dslack pa -> pf_fl pf = 0 -> Z.of_nat (length FRS) + 1 < 4096 ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
pbufc asegs m (t_pbs ts) (t_pb ts) [] -> BOK pf pa ts B (S (Z.to_nat (16 * Z.max 0 (pf_len pf) + 8192) + nB)) -> CSTR_OK pf payload ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_number ->
t_co ts < pf_len pf -> nth_error payload (Z.to_nat (t_co ts)) = Some cb ->
frm0 fc ->
pe_s0 sv = Z_to_bv 64 v2 -> pe_ra sv = Z_to_bv 64 ra2 ->
(v2 < alloc_ceiling \/ v2 mod 8 <> 0 \/ v2 <= pa_sp0 pa \/ hiA_top A4L HIx - 16 <= v2) /\ 0 <= v2 < 2^64 ->
uw_ok A4L (hl_malloc A4H) (Z_to_bv 64 0x9daec) (UWfp ra2 v2) ->

(forall m' md' A' B' pbs' errv' co' cb' isdq pj' r sh BS gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' F' fc',
t_co ts <= co' < pf_len pf -> nth_error payload (Z.to_nat co') = Some cb' -> (length BS <= 4)%nat -> (exists w, jfresh sh BS w /\ w <= Z.max 20 ((co' - t_co ts) + 16)) -> (sh = Sint \/ sh = Sdouble true) ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B'
(ts_lvl (ts_pbs (ts_set_x ts co' (TS isdq (ts_stpos (t_x ts)) (Z_to_bv 64 co') (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))) pbs')
(TL ST_eatws ST_finish r (Some sh) BS 0 [])) cb' nb pj' sv errv' ->
PBOKat m' (ts_lvl (ts_pbs (ts_set_x ts co' (TS isdq (ts_stpos (t_x ts)) (Z_to_bv 64 co') (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))) pbs')
(TL ST_eatws ST_finish r (Some sh) BS 0 [])) co' ->
BOK pf pa (ts_lvl (ts_pbs (ts_set_x ts co' (TS isdq (ts_stpos (t_x ts)) (Z_to_bv 64 co') (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))) pbs')
(TL ST_eatws ST_finish r (Some sh) BS 0 [])) B' nB ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msA asegs pf pa APE_REDO co' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' (Z_to_bv 64 (pf_tk pf + 56)) (Z_to_bv 64 (pa_F pa + 64)) F' fc' m')) ->

(forall m' md' A' B' pbs' errv' co' cb' isdq pj' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' F' fc',
t_co ts <= co' < pf_len pf -> nth_error payload (Z.to_nat co') = Some cb' ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B'
(ts_set_x (ts_lvl (ts_pbs (ts_set_x ts co' (TS isdq (ts_stpos (t_x ts)) (Z_to_bv 64 co') (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))) pbs')
(TL ST_inf (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) co'
(TS isdq (Z_to_bv 64 0) (Z_to_bv 64 co') (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))) cb' nb pj' sv errv' ->
PBOKat m' (ts_set_x (ts_lvl (ts_pbs (ts_set_x ts co' (TS isdq (ts_stpos (t_x ts)) (Z_to_bv 64 co') (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))) pbs')
(TL ST_inf (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) co'
(TS isdq (Z_to_bv 64 0) (Z_to_bv 64 co') (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))) co' ->
BOK pf pa (ts_pbs (ts_set_x ts co' (TS isdq (ts_stpos (t_x ts)) (Z_to_bv 64 co') (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))) pbs') B' (S (Z.to_nat (16 * Z.max 0 (pf_len pf) + 8192) + nB)) ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msA asegs pf pa APE_REDO co' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' (Z_to_bv 64 (pf_tk pf + 56)) (Z_to_bv 64 (pa_F pa + 64)) F' fc' m')) ->

(forall m' md' A' B' errv' cb' pj' ts' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' s11' t4' t6' F' fc',
t_levels ts' = t_levels ts -> t_depth ts' = t_depth ts -> t_objs ts' = t_objs ts ->
PE_INVW_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' ts' [] cb' nb pj' sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msO asegs pf pa APE_OUT x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' (Z_to_bv 64 (pf_tk pf + 56)) s11' t4' t6' F' fc' m')) ->
(forall m' md' A' B' errv' cb' pj' ts' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' s11' t4' t6' F' fc',
t_levels ts' = t_levels ts -> t_depth ts' = t_depth ts -> t_objs ts' = t_objs ts ->
PE_INVW_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' ts' [] cb' nb pj' sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msO asegs pf pa APE_ERRMEM x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' (Z_to_bv 64 (pf_tk pf + 56)) s11' t4' t6' F' fc' m')) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa (pe_jtA ST_number) (t_co ts) gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (Z.of_nat (t_depth ts))) (Z_to_bv 64 q) (Z_to_bv 64 (pa_F pa + 64)) F fc m).
Proof.
intros until fc. intros STC BSL DSL FL0 FRN INV NUMC BK CSTR Hl Hst Hco Hcb FRM S0V RAV HV UWK Kredo Kinf Kout Kerrmem.
assert (CHOFF : ts_choff (t_x ts) = Z_to_bv 64 (t_co ts)) by (destruct INV as [(_ & _ & _ & X & _) _]; exact X).
assert (CO0 : 0 <= t_co ts) by (destruct INV as [(_ & _ & X & _) _]; lia).
set (XS := fun (co' : Z) (isdq : word) => TS isdq (ts_stpos (t_x ts)) (Z_to_bv 64 co') (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts))) in *.

assert (POSTK : forall m2 co' cb' isdq pj1 a0x a1x a2x a3x a5x a6x,
t_co ts <= co' < pf_len pf -> nth_error payload (Z.to_nat co') = Some cb' -> pj_16 pj1 = Z_to_bv 64 (pf_tk pf / 8 + 2147450881) ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m2 md A B (ts_set_x ts co' (XS co' isdq)) cb' nb pj1 sv errv ->
PBOKat m2 (ts_set_x ts co' (XS co' isdq)) 0 ->
AJ5 A4L HIx A T md
(Q1Y6.Mq2.pe_msE pf pa 0x94b20 (Z_to_bv 64 (pf_tk pf / 8 + 2147450884)) gp (Z_to_bv 64 (pf_tk pf / 8 + 3)) t1 t2 a0x a1x a2x a3x (Z_to_bv 64 (bv_unsigned cb')) a5x a6x (Z_to_bv 64 (t_pb ts))
(Z_to_bv 64 (co' - t_co ts)) (Z_to_bv 64 (pf_tk pf + 20)) (Z_to_bv 64 (Z.of_nat (t_depth ts))) (Z_to_bv 64 (pf_sb pf + co')) (Z_to_bv 64 (pf_tk pf + 32)) (Z_to_bv 64 (pa_F pa)) (Z_to_bv 64 q)
(Z_to_bv 64 (pf_sb pf + t_co ts)) (Z_to_bv 64 (pf_tk pf + 64)) (Z_to_bv 64 (pa_F pa + 64)) (Z_to_bv 64 (pf_tk pf / 8 + 2147450888)) (Z_to_bv 64 (pf_lenr pf)) F fc m2)).
{ intros m2 co' cb' isdq pj1 a0x a1x a2x a3x a5x a6x Hco' Hcb' P16 INV2 PBK2.
set (tsL := ts_set_x ts co' (XS co' isdq)) in *.
assert (HlL : nth_error (t_levels tsL) (t_depth tsL) = Some l) by (destruct ts; exact Hl).
assert (EcoL : t_co tsL = co') by (destruct ts; reflexivity).
eapply (num_post_A pf pa q LB0 LM FRS payload me lo m2 md A B tsL l (t_co ts) (- t_co ts) cb' nb pj1 sv errv T v2 ra2 nB);
[ exact STC | exact BSL | exact DSL | exact FL0 | exact FRN | exact INV2 | replace (t_co ts + - t_co ts) with 0 by lia; exact PBK2 | lia | lia | exact (BOK_set_x pf pa ts B _ co' _ (proj1 Hco') BK) | exact HlL | exact Hst
| rewrite EcoL; lia | rewrite EcoL; lia | exact FRM | exact P16 | exact S0V | exact RAV | exact HV | exact UWK | | | ].
- intros m' md' A' B' pbs' errv' pj' r sh BS gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' F' fc' LBS JF Hsh INV' PBK' BK' FS' FRM'.
rewrite EcoL in *.
eapply (Kredo m' md' A' B' pbs' errv' co' cb' isdq pj' r sh BS); [exact Hco' | exact Hcb' | exact LBS | replace (co' - t_co ts) with (co' + - t_co ts) by lia; exact JF | exact Hsh | exact INV' | eapply PBOKat_weaken; [| exact PBK']; lia | exact BK' | exact FS' | exact FRM'].
- intros m' md' A' B' pbs' errv' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' F' fc' INV' PBK' BK' FS' FRM'.
rewrite EcoL in *.
eapply (Kinf m' md' A' B' pbs' errv' co' cb' isdq pj1); [exact Hco' | exact Hcb' | destruct ts; exact INV' | eapply PBOKat_weaken; [| destruct ts; exact PBK']; lia | exact BK' | exact FS' | exact FRM'].
- intros m' md' A' B' errv' pj' ts' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' s11' t4' t6' F' fc' E1 E2 E3 INVW' FS' FRM'.
eapply (Kout m' md' A' B' errv' cb' pj' ts'); [rewrite E1; destruct ts; reflexivity | rewrite E2; destruct ts; reflexivity | rewrite E3; destruct ts; reflexivity | exact INVW' | exact FS' | exact FRM']. }
eapply (num_entry_A pf pa q LB0 LM FRS payload me lo m md A B ts l cb nb pj sv errv T); [exact STC | exact INV | exact NUMC | exact Hl | exact Hst | exact Hco | |].
-
intros m1 pj1 a2' a5' P16 Cn INV1 PBK1.
eapply (num_loop_A (Z.to_nat (pf_len pf - t_co ts)) pf pa q LB0 LM FRS payload me lo m1 md A B ts l (t_co ts) 0 cb nb pj1 sv errv T);
[exact STC | exact FL0 | exact INV1 | exact PBK1 | exact CSTR | exact Hl | exact Hst | lia | exact Hco | exact Hcb | exact Cn | lia | |].
+ intros m2 co' cb' isdq a0' a1' a2'' a3' a5'' a6' Hco' Hcb' INV2 PBK2.
eapply (POSTK m2 co' cb' isdq pj1); [exact Hco' | exact Hcb' | exact P16 | exact INV2 | exact PBK2].
+
intros m2 co' cb' isdq a1' a2'' a3' a4' a5'' a6' Hco' Eco' Elr INV2 PBK2.
set (tsE := ts_set_x ts (pf_len pf) (XS (pf_len pf) isdq)) in *.
assert (HlE : nth_error (t_levels tsE) (t_depth tsE) = Some l) by (destruct ts; exact Hl).
replace (co' - t_co ts) with (pf_len pf - 1 - t_co ts) by lia.
replace (Z_to_bv 64 (t_pb ts)) with (Z_to_bv 64 (t_pb tsE)) by (destruct ts; reflexivity).
replace (Z_to_bv 64 (Z.of_nat (t_depth ts))) with (Z_to_bv 64 (Z.of_nat (t_depth tsE))) by (destruct ts; reflexivity).
eapply (num_eof_A pf pa q LB0 LM FRS payload me lo m2 md A B tsE l (t_co ts) (- t_co ts) cb' nb pj1 sv errv T _);
[ exact STC | exact BSL | exact INV2 | replace (t_co ts + - t_co ts) with 0 by lia; exact PBK2 | lia | exact (BOK_set_x pf pa ts B _ (pf_len pf) _ ltac:(lia) BK) | exact HlE | exact Hst | destruct ts; reflexivity | lia | | ].
* intros m' md' A' B' pbs' errv' x1' gp' t0' t1' t2' a0' a1'' a2x a3x a4x a5x a6x a7x s5x s7x s11x t4x t6x F' fc' INV' FS' FRM'.
eapply (Kout m' md' A' B' errv' cb' pj1 _); [| | | apply (PE_INV_A_W HIx GA); exact INV' | exact FS' | exact FRM']; destruct ts; reflexivity.
* intros m' md' A' B' pbs' errv' x1' gp' t0' t1' t2' a0' a1'' a2x a3x a4x a5x a6x a7x s5x s7x s11x t4x t6x F' fc' INV' FS' FRM'.
eapply (Kerrmem m' md' A' B' errv' cb' pj1 _); [| | | apply (PE_INV_A_W HIx GA); exact INV' | exact FS' | exact FRM']; destruct ts; reflexivity.
-
intros m1 pj1 a0' a1' a2' a3' a5' P16 C0 INV1 PBK1.
assert (Ets : ts_set_x ts (t_co ts) (XS (t_co ts) (ts_isd (t_x ts))) = ts).
{ unfold XS. destruct ts as [d lv co pb pbs x o os obs]. destruct x as [isd sp ch er uc hi qu]. cbn [t_x t_co ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote ts_set_x] in *. rewrite CHOFF. reflexivity. }
eapply (POSTK m1 (t_co ts) cb (ts_isd (t_x ts)) pj1); [lia | exact Hcb | exact P16 | rewrite Ets; exact INV1 | rewrite Ets; exact PBK1].
Qed.

End PeSNumA.
End RC__1.
