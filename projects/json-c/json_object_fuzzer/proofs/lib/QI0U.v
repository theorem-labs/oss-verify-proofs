(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmZZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmZZ. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKQo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKQo. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPZI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPZI.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QkMG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkMG. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qu4M.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qu4M.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QG8z.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QG8z. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qdyh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qdyh.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qdyh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qdyh.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLbz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLbz. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2Sr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2Sr. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qdyh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qdyh.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qa8x.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qa8x.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLbz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLbz.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6WR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6WR.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QrPc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QrPc.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbFI. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qhd4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qhd4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqj. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mqd. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qiiq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qiiq. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mqf. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4v2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4v2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqf. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mqe. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qoif.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qoif.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqe. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSHS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSHS. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Ql4f.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql4f.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1Y6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1Y6.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QGdd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QGdd.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QcmL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QcmL. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QrQv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QrQv.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEUF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEUF.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJZd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJZd.Mqg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QW22.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QW22.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnDr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnDr.Mq5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qmgs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qmgs.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdGy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdGy.Mqc. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWrz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWrz.Mq5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QV7s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QV7s.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQ2r.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQ2r.Mq7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QtyQ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QtyQ.Mq9. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QtyQ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QtyQ.Mqa. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9yh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9yh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q8H8.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q8H8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQ2r.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQ2r.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QFrL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QFrL.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QrQv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QrQv. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQPy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQPy. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qz87.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qz87.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJZd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJZd.Mqe. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZUC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZUC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q84s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q84s. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QI6Z.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QI6Z. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qiiq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qiiq.Mqc. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJZd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJZd.Mq9. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc5u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc5u.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Q2qa.Mq0.sf_vocab ::= Q2qa.Mq0.mkr__sf_vocab_5. Local Ltac QlEo_c1.solve_load ::= QXup.mkr__solve_load_3. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mq9. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QFZX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QFZX. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QFZX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QFZX.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q63E.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q63E.Mqg.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6oO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6oO.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q63E.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q63E.Mqh.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qvmy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qvmy. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QW22.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QW22.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QV7s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QV7s.Mq5.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2EX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2EX. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnDr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnDr.Mq6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition json_tokener_parse_B_entry : Z := 0x93680.
Definition tokparse_verbose_B_entry : Z := 0x93800.
Definition TOKPARSE_RA_B : Z := 0x93774.
Definition A_GOT_TPPC : Z := 0xe8e80.

Lemma lhg_outside : forall m m' W, lh_globA m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= hl_img_lo A4H \/ hl_img_hi A4H <= fst iv) W -> lh_globA m'.
Proof.
intros m m' W G MU WM HW. eapply lh_globA_frame; [exact G | exact MU | exact WM |].
eapply Forall_impl; [| exact HW]. intros [a b] H. cbn [fst snd hl_img_lo hl_img_hi A4H] in *. unfold GHASHA, GSEEDA. lia.
Qed.
Lemma lhg_loc : forall m m', lh_globA m -> munch [(LOCCELL_A, LOCCELL_A + 8)] m m' -> wmono asegs m m' -> lh_globA m'.
Proof.
intros m m' G MU WM. eapply lh_globA_frame; [exact G | exact MU | exact WM |].
apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. unfold GHASHA, GSEEDA, LOCCELL_A, A_TP. lia.
Qed.

Section ATokParseB.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).

Hypothesis MAPP : memappend_A_stmt2 HIx.
Hypothesis SHRINK : jo_array_shrink_A2J HIx.
Hypothesis AADD : jo_array_add_A2J HIx.
Hypothesis PUT : put_stmt_A HIx.
Hypothesis NEWARR : jo_new_array_A3 HIx.
Hypothesis NEWOBJ : jo_new_object_A3_stmt HIx.
Variable HD : Z.
Hypothesis HD_le : 80 + 96 + 4096 + 144 + HD <= 12288.
Hypothesis OADD : jo_object_add_A HIx HD.
Hypothesis USE : uselocale_A_stmt.
Hypothesis ERRNOL : errno_location_A_stmt.
Hypothesis DUP : duplocale_A_stmt HIx.
Hypothesis NEWL : newlocale_A_stmt HIx.
Hypothesis FREEL : freelocale_A_stmt HIx.
Hypothesis NEWDBL : jo_new_double_A_stmt HIx.
Hypothesis NEWBOOL : jo_new_boolean_A_stmt HIx.
Hypothesis NEWSTR : jo_new_string_len_A_stmt HIx.
Hypothesis PARSEI : parse_i64_A_stmt HIx 0xa6060.
Hypothesis PARSEU : parse_i64_A_stmt HIx 0xa62ec.
Hypothesis STRTOD : strtod_A_stmt HIx.
Hypothesis NEWINT : jo_new_int_A_stmt HIx 0x9dbdc.
Hypothesis NEWUINT : jo_new_int_A_stmt HIx 0x9e328.
Hypothesis NEWDBLS : new_double_s_A_stmt HIx.

Definition rtc_tppc_stmt : Prop :=
forall A LB LM FR B m md, HEAPAx A LB LM FR B m md -> bytes_at asegs m A_GOT_TPPC (le8 (Z_to_bv 64 json_tokener_parse_B_entry)).
Lemma RTC_TPPC : rtc_tppc_stmt.
Proof.
intros A LB LM FR B m md HP. pose proof (heapA_rtc A4L HIx _ _ _ _ _ _ _ HP) as R. rewrite Forall_forall in R.
apply (R (A_GOT_TPPC, le8 (Z_to_bv 64 json_tokener_parse_B_entry))). cbn [hl_rt_consts A4L]. unfold a4_rt_consts, A_GOT_TPPC, json_tokener_parse_B_entry.
repeat (first [left; reflexivity | right]).
Qed.

Definition tokparse_costB (n : Z) : Z := toknew_costB + (Z.of_nat (pe_A0 (n + 1)) + PhiPB (n + 1) 32 + K_free * 4 + K_exit) + 512 * 34.
Definition tokparse_costD (n : Z) : Z := Z.of_nat (pe_A0 (n + 1)) + 2 + M2D.

Definition wfr_cells (h0 h1 h2 : word) (jw : list byte) : list cell := [C8 h0; C8 h1; C8 h2; CB 32 jw].
Definition wfr_cells2 (h0 h1 h2 : word) (j1 : list byte) (e : word) (j2 : list byte) : list cell := [C8 h0; C8 h1; C8 h2; CB 8 j1; C4 e; CB 20 j2].
Definition wsh_cells : list cell :=
[C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 4); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243)].

Lemma wfr_fresh : forall Fw (LBall LB0 LM : list blk) FRS B A m md,
HEAPAx A LBall LM ((Fw, 0) :: FRS) B m md -> incl LB0 LBall ->
~ In (Fw, 56) (LB0 ++ LM ++ fr_ivs A4L FRS) /\ ~ In (Fw / 8 + A_SB, 8) (LB0 ++ LM ++ fr_ivs A4L FRS).
Proof.
intros Fw LBall LB0 LM FRS B A m md HP Hincl.
assert (INW : In (Fw, 0) ((Fw, 0) :: FRS)) by (left; reflexivity).
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP INW) as (_ & HFal & HF0 & HFc & _). change (fr_size 0) with 64 in HFal, HFc.
pose proof (proj1 (stdpp.base.NoDup_ListNoDup _) (heapA_frame_nodup A4L HIx _ _ _ _ _ _ _ HP)) as ND. cbn in ND. apply List.NoDup_cons_iff in ND as [Hni ND].
pose proof alloc_ceiling_range as ACR.
assert (SUB : forall b, In b (LB0 ++ LM) -> In b (LBall ++ LM)).
{ intros b Hb. apply in_app_or in Hb. apply in_or_app. destruct Hb as [Hb|Hb]; [left; apply Hincl; exact Hb | right; exact Hb]. }
split; intros Hin; rewrite app_assoc in Hin; apply in_app_or in Hin as [Hin | Hin].
- pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP INW (SUB _ Hin)) as X. change (fr_size 0) with 64 in X. lia.
- apply in_fr_ivs in Hin as (G & kg & HG & [E|E]).
+ injection E as EG _. apply Hni. cbn [fr_base fst]. rewrite EG. exact (in_map fr_base _ _ HG).
+ injection E as EG EK. pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP ltac:(right; exact HG)) as (Hkg & _).
unfold fr_shadow_len in EK. assert (kg = 0 \/ kg = 1 \/ kg = 2 \/ kg = 3) as [->|[->|[->| ->]]] by lia; cbn in EK; lia.
- pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ _ _ HP (SUB _ Hin)) as (Hn8 & _).
pose proof (shadow_blk_apart HIx _ _ _ _ _ _ _ _ _ Fw 8 HP (SUB _ Hin) ltac:(lia) ltac:(lia) ltac:(lia)) as X. unfold shA in X. lia.
- apply in_fr_ivs in Hin as (G & kg & HG & [E|E]).
+ injection E as EG EK. pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP ltac:(right; exact HG)) as (Hkg & _).
unfold fr_size in EK. assert (kg = 0 \/ kg = 1 \/ kg = 2 \/ kg = 3) as [->|[->|[->| ->]]] by lia; cbn in EK; lia.
+ injection E as EG EK. pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP ltac:(right; exact HG)) as (Hkg & HGal & HG0 & _).
unfold fr_shadow_len in EK. assert (kg = 0) by (assert (kg = 0 \/ kg = 1 \/ kg = 2 \/ kg = 3) as [->|[->|[->| ->]]] by lia; cbn in EK; lia). subst kg.
change (fr_size 0) with 64 in HGal. unfold shad in EG. cbn [hl_sb A4L] in EG.
apply Hni. cbn [fr_base fst]. replace Fw with G by (clear - EG HGal HFal; Z.div_mod_to_equations; lia). exact (in_map fr_base _ _ HG).
Qed.

Ltac heap_nowW HP MU WM MI INW :=
eapply (heapA_client_frame A4L HIx);
[ exact HP
| eapply (frame_writes_okF A4L HIx _ _ _ _ _ _ _ _ _ HP MU);
repeat (apply Forall_cons; [ first [ left; cbn [fst snd]; unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia
| right; right; right; eexists; eexists; split; [exact INW | left; cbn [fst snd]; change (fr_size 0) with 64; lia]
| right; right; right; eexists; eexists; split; [exact INW | right; unfold shad; cbn [fst snd hl_sb A4L]; change (fr_shadow_len 0) with 8; unfold A_SB; lia] ] | ]);
apply Forall_nil
| exact WM | exact MI ].

Lemma tokparse_verbose_B :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LBc LM : list blk) (FRS : list frame) (B : bud) (sb lo Fw : Z) (str0 slack : list byte) (errv : word)
(h0 h1 h2 : word) (jw : list byte),
jo_preA HIx A LBc LM ((Fw, 0) :: FRS) B m md sp tp ra lo (80 + 432 + 12288 + 4096) errv ->
bv_unsigned sp mod 32 = 0 -> Z.of_nat (length LM) < 8 ->
cstring_argA FRS m sb str0 slack -> Z.of_nat (length str0) < 2^25 ->
rw_cells asegs m LOCCELL_A [C8 (Z_to_bv 64 GLOBLOC_A)] -> rw_cells asegs m LOCALE_LOCK_A [C4 (Z_to_bv 64 0)] -> lh_globA m ->
bytes_at asegs m UTF8REP_ADDR_A Qa8x.Mq3.utf8rep ->
rw_cells asegs m Fw (wfr_cells h0 h1 h2 jw) -> rw_cells asegs m (Fw / 8 + A_SB) wsh_cells ->
Z.of_nat (length FRS) + 3 < 4096 ->
tokparse_costB (Z.of_nat (length str0)) <= bB B -> tokparse_costD (Z.of_nat (length str0)) <= bD B ->
frm0 fc -> a0 = Z_to_bv 64 sb -> a1 = Z_to_bv 64 (Fw + 32) ->
(forall ms' md' m' (A' : ASA A4L HIx) (B' : bud) (gp' : word) (r : Z) (errv' : word) (RBS LK : list blk) (e : word) (j1 j2 : list byte),
ret_statew A4H ra sp gp' tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' ->
model_vm_only (cfg_model md) (cfg_model md') ->
stk asegs m' lo (bv_unsigned sp) ->
rw_cells asegs m' A_ERRNO [C4 errv'] ->
rw_cells asegs m' LOCCELL_A [C8 (Z_to_bv 64 GLOBLOC_A)] -> rw_cells asegs m' LOCALE_LOCK_A [C4 (Z_to_bv 64 0)] -> lh_globA m' ->
bytes_at asegs m' UTF8REP_ADDR_A Qa8x.Mq3.utf8rep ->
heap_presx A4H QcmL.xlocA (LBc ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m' ->
rw_cells asegs m' Fw (wfr_cells2 h0 h1 h2 j1 e j2) -> rw_cells asegs m' (Fw / 8 + A_SB) wsh_cells ->
jo_chargeA (tokparse_costB (Z.of_nat (length str0))) (tokparse_costD (Z.of_nat (length str0))) B B' ->
HEAPAx A' (RBS ++ LK ++ LBc) LM ((Fw, 0) :: FRS) B' m' md' ->
((r = 0 /\ RBS = []) \/
(r <> 0 /\ exists s, jval asegs A4F s m' RBS r 1 /\ sdepth s <= 32 /\ exists w, jtx s RBS = Some (w, []) /\ w <= 26 * (Z.of_nat (length str0) + 1) + 64)) ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 tokparse_verbose_B_entry) fc None m (seg_rom asegs)).
Proof.
intros until jw. intros PRE SP32 LMN CSTR LEN LOC LCK G UTF WFR WSH FRN BB BD FRM A0 A1 K. subst a0 a1.
destruct PRE as (HP & ST & LO & LOS & SPA & HT & ERR & TP & RA).
destruct CSTR as (STR & NONUL & PAD & ALOC & UNP). destruct ALOC as (Fr & kf & INF & HF1 & HF2).
assert (INF' : In (Fr, kf) ((Fw, 0) :: FRS)) by (right; exact INF).
assert (INW : In (Fw, 0) ((Fw, 0) :: FRS)) by (left; reflexivity).
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP INF') as (Hkf & HFal & HF0 & HFc & _).
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP INW) as (_ & HWal & HW0 & HWc & HWimg & _).
change (fr_size 0) with 64 in HWal, HWc, HWimg. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in HWimg.
assert (EA8 : (Fw + 32) mod 8 = 0) by (clear - HWal; Z.div_mod_to_equations; lia).
assert (EA4 : (Fw + 32) mod 4 = 0) by (clear - HWal; Z.div_mod_to_equations; lia).
assert (HW8 : Fw mod 8 = 0) by (clear - HWal; Z.div_mod_to_equations; lia).
pose proof alloc_ceiling_range as ACR. pose proof (hiA_top_le A4L HIx) as HT47.
unfold tokparse_costB, tokparse_costD in BB, BD.
word_range sp SPR. assert (M2D0 : 0 <= M2D) by (unfold M2D; lia).
pose proof (bytes_at_bound _ _ _ _ STR) as SB0. rewrite length_app in SB0. cbn [length] in SB0.
unfold wfr_cells in WFR. unfold wsh_cells in WSH.

assert (TRK : forall mx, munch [(bv_unsigned sp + -80, bv_unsigned sp)] m mx -> wmono asegs m mx ->
bytes_at asegs mx sb (str0 ++ Z_to_bv 8 0 :: slack) /\ rw_cells asegs mx LOCCELL_A [C8 (Z_to_bv 64 GLOBLOC_A)] /\
rw_cells asegs mx LOCALE_LOCK_A [C4 (Z_to_bv 64 0)] /\ lh_globA mx /\ bytes_at asegs mx UTF8REP_ADDR_A Qa8x.Mq3.utf8rep /\
unpoisoned asegs mx A_SB sb (Z.of_nat (length str0) + 1) /\
rw_cells asegs mx Fw [C8 h0; C8 h1; C8 h2; CB 32 jw] /\ rw_cells asegs mx (Fw / 8 + A_SB) wsh_cells).
{ intros mx MUx WMx.
split. { eapply bytes_at_transport; [exact STR | exact MUx |]. cbn [disjoint_from]. rewrite length_app. cbn [length]. lia. }
split. { eapply rw_cells_transport; [exact LOC | exact MUx | exact WMx |]. unfold LOCCELL_A, A_TP. cbn [disjoint_from cells_size csize Nat.add]. lia. }
split. { eapply rw_cells_transport; [exact LCK | exact MUx | exact WMx |]. unfold LOCALE_LOCK_A. cbn [disjoint_from cells_size csize Nat.add]. lia. }
split. { eapply lhg_outside; [exact G | exact MUx | exact WMx |]. apply Forall_cons; [| apply Forall_nil]. cbn [fst snd hl_img_lo hl_img_hi A4H]. lia. }
split. { eapply bytes_at_transport; [exact UTF | exact MUx |]. unfold UTF8REP_ADDR_A. cbn [disjoint_from length Qa8x.Mq3.utf8rep]. lia. }
split. { eapply unpoisoned_transport; [exact UNP | exact MUx |]. intros a k Ha Hk. cbn [disjoint_from]. split; [| exact I]. left.
assert (HH : shadow_span_hi A_SB sb (Z.of_nat (length str0) + 1) <= 2^45).
{ unfold shadow_span_hi, A_SB. assert (E1 : (sb + (Z.of_nat (length str0) + 1) - 1) / 8 <= 2^44) by (apply Z.div_le_upper_bound; lia).
pose proof (Z.mul_div_le ((sb + (Z.of_nat (length str0) + 1) - 1) / 8 + 2147450880) 8 ltac:(lia)). lia. }
lia. }
split. { eapply rw_cells_transport; [exact WFR | exact MUx | exact WMx |]. cbn [disjoint_from cells_size csize Nat.add]. lia. }
eapply rw_cells_transport; [exact WSH | exact MUx | exact WMx |]. unfold wsh_cells, A_SB. cbn [disjoint_from cells_size csize Nat.add length]. lia. }
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL].
pose proof (heap_pres_refl A4H (LBc ++ LM ++ fr_ivs A4L ((Fw, 0) :: FRS)) (bv_unsigned sp) m) as HPR.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)] m) as MU.
stash TRK. stash K. clear WFR WSH.
a4l. unfold tokparse_verbose_B_entry. reenterA asegs A4L HIx asegs_wx HP. subst tp.
carve_frame 80%nat ST.
do 11 step.
step. step. step. step.
step. step. step.
evt_done5.
eapply (json_tokener_new_A_cps HIx PUT) with (u := UWpaid) (lo := lo);
[ heap_nowA A4L HIx HP MU WM MI
| apply uw_at_paid
| cbn [uw_ok uw_key]; exact I | .. ]; a4l_goal; rewrite ?unsigned_lit by lia; try first [reflexivity | lia].
all: try eassumption.
1: (unfold put_stk_A; lia).
1: (unfold toknew_costB, pbnew_costB, PhiPB, K_free, K_exit in *; lia).
1: (cbn [uw_cost]; lia).
intros ms2 md2 A2 (m2 & r & errv2 & B2 & RS2 & VM2 & ST2 & HPR2 & ERR2 & BB2 & BD2 & OUT2).
destruct RS2 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F2 & fc2 & -> & FS2 & FRM2).
a4l. rewrite ?unsigned_lit in ST2 by lia. rewrite ?unsigned_lit in HPR2 by lia.
extend_presA A4L HIx HPR MU WM HP HPR2.
lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?n)] => replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia | reflexivity]) end.
unstash TRK. destruct (TRK m1 MU WM) as (STR1 & LOC1 & LCK1 & G1 & UTF1 & UNP1 & WFR1 & WSH1). clear TRK.

assert (INWI : In (Fw, 56) (LBc ++ LM ++ fr_ivs A4L ((Fw, 0) :: FRS))) by (apply in_or_app; right; apply in_or_app; right; change 56 with (fr_size 0 - 8); apply fr_ivs_frame; exact INW).
assert (INWS : In (Fw / 8 + A_SB, 8) (LBc ++ LM ++ fr_ivs A4L ((Fw, 0) :: FRS))).
{ apply in_or_app; right; apply in_or_app; right. change 8 with (fr_shadow_len 0). change (Fw / 8 + A_SB) with (shad A4L Fw). apply fr_ivs_shadow. exact INW. }
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia].
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in LOC1; [| right; left; cbn; intros z Hz; cbn [hl_client_static A4H]; unfold a4_client_static, LOCCELL_A, A_TP in *; lia].
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in LCK1; [| right; left; cbn; intros z Hz; cbn [hl_client_static A4H]; unfold a4_client_static, LOCALE_LOCK_A in *; lia].
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in WFR1; [| eapply client_range_block; [exact INWI | lia | cbn; lia]].
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in WSH1; [| eapply client_range_block; [exact INWS | unfold A_SB; lia | unfold wsh_cells, A_SB; cbn; lia]].
pose proof (lh_globA_client _ _ _ _ HPR2 G1) as G2.
assert (UTF2 : bytes_at asegs m2 UTF8REP_ADDR_A Qa8x.Mq3.utf8rep).
{ eapply (heap_pres_bytes_at A4H); [exact HPR2 | exact UTF1 |]. right; left. intros z Hz. unfold UTF8REP_ADDR_A in Hz. cbn in Hz. cbn [hl_client_static A4H]. unfold a4_client_static. lia. }
assert (INFI : In (Fr, fr_size kf - 8) (LBc ++ LM ++ fr_ivs A4L ((Fw, 0) :: FRS))) by (apply in_or_app; right; apply in_or_app; right; apply fr_ivs_frame; exact INF').
assert (STR2 : bytes_at asegs m2 sb (str0 ++ Z_to_bv 8 0 :: slack)).
{ eapply (heap_pres_bytes_at A4H); [exact HPR2 | exact STR1 |]. eapply client_range_block; [exact INFI | exact HF1 |]. rewrite length_app. cbn [length]. lia. }
assert (UNP2 : unpoisoned asegs m2 A_SB sb (Z.of_nat (length str0) + 1)).
{ eapply (unpoisoned_pres_frame HIx A LBc LM ((Fw, 0) :: FRS) B m md LBc _ m1 m2 Fr kf); [exact HP | exact INF' | exact HF1 | lia | exact UNP1 | exact HPR2]. }
cbn [uw_cost] in BD2. unfold A_SB in WSH1. unfold wsh_cells in WSH1.
destruct OUT2 as [(-> & HP2) | (Hr & BS & TF & HP2)].
-
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI2. a4l.
unfold LOCCELL_A, LOCALE_LOCK_A, A_TP in LOC1, LCK1. stash UTF2.
pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (Fw, Fw + 56)] m2) as MU2. pose proof (wmono_refl asegs m2) as WM2.
reenterA asegs A4L HIx asegs_wx HP2.
step. if_true.
step. if_falsex.
step. step. ub_align_near EA4.
asan_chkB.
step. rewrite ?(unsigned_lit (Fw + 32)) by lia. rewrite ?(land7_of_mod8 (Fw + 32) EA8).
step. step. ub_if_lit.
step. step. stepz.
do 12 step.
evt_done5. unstash K.
lazymatch goal with |- AJ5 _ _ _ _ _ (MS _ _ _ _ _ ?mf _) =>
lazymatch goal with MUf : munch _ m2 mf, WMf : wmono asegs m2 mf, MIf : mem_inv asegs mf |- _ =>
assert (HPf : HEAPAx A2 LBc LM ((Fw, 0) :: FRS) B2 mf md2)
by (eapply (heapA_client_frame A4L HIx); [exact HP2 | | exact WMf | exact MIf];
eapply (frame_writes_okF A4L HIx _ _ _ _ _ _ _ _ _ HP2 MUf);
apply Forall_cons; [left; cbn [fst snd]; unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia |];
apply Forall_cons; [right; right; right; exists Fw, 0; split; [exact INW | left; cbn [fst snd]; change (fr_size 0) with 64; lia] | apply Forall_nil]);
eapply (K _ _ _ _ B2 _ 0 errv2 [] [])
end end.
+ apply ret_statew_intro; [exact FS2 | exact FRM2].
+ exact VM2.
+ lazymatch goal with ST' : stk asegs _ lo _ |- _ => release_frame FR ST' (bv_unsigned sp); exact ST' end.
+ eassumption.
+ unfold LOCCELL_A, A_TP; assumption.
+ unfold LOCALE_LOCK_A; assumption.
+ lazymatch goal with MUf : munch _ m2 ?mf, WMf : wmono asegs m2 ?mf |- _ => eapply lhg_outside; [exact G2 | exact MUf | exact WMf | apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]; cbn [fst snd hl_img_lo hl_img_hi A4H]; lia] end.
+ unstash UTF2. lazymatch goal with MUf : munch _ m2 ?mf |- _ => eapply bytes_at_transport; [exact UTF2 | exact MUf |]; unfold UTF8REP_ADDR_A; cbn [disjoint_from length Qa8x.Mq3.utf8rep]; lia end.
+ eapply heap_presx_trans.
{ apply heap_pres_presx. eapply heap_pres_weaken; [exact HPR | lia |]. intros b Hb. apply in_app_or in Hb as [Hb|Hb]; [apply in_or_app; left; exact Hb | apply in_or_app; right]. apply in_app_or in Hb as [Hb|Hb]; [apply in_or_app; left; exact Hb | apply in_or_app; right; cbn [fr_ivs flat_map app]; right; right; exact Hb]. }
lazymatch goal with MUf : munch _ m2 ?mf, WMf : wmono asegs m2 ?mf |- _ => eapply (presx_private HIx _ _ _ _ _ _ _ _ _ _ (bv_unsigned sp) HP2 MUf WMf); [| lia |] end.
{ intros b Hb. apply in_app_or in Hb as [Hb | Hb]; [left; apply in_or_app; left; exact Hb|]. apply in_app_or in Hb as [Hb | Hb]; [left; apply in_or_app; right; exact Hb | right; cbn [fr_ivs flat_map app]; right; right; exact Hb]. }
apply Forall_cons; [left; cbn [fst snd]; lia |].
apply Forall_cons; [| apply Forall_nil]. right; right; left. exists Fw, 0. split; [exact INW|]. change (fr_size 0 - 8) with 56. change (fr_shadow_len 0) with 8.
destruct (wfr_fresh Fw LBc LBc LM FRS B2 A2 m2 md2 HP2 (incl_refl _)) as [OFF2 OFS2].
split; [exact OFF2 | split; [unfold shad; cbn [hl_sb A4L]; exact OFS2 | left; cbn [fst snd]; change (fr_size 0) with 64; lia]].
+ lazymatch goal with H : rw_cells asegs _ Fw _ |- _ => unfold wfr_cells2; exact H end.
+ unfold wsh_cells, A_SB. assumption.
+ unfold jo_chargeA, tokparse_costB, tokparse_costD. unfold toknew_costB, pbnew_costB, PhiPB, K_free, K_exit in *. split; lia.
+ exact HPf.
+ left. split; reflexivity.
-
destruct TF as (stk0 & pb & PBS & EBS & TOK & PBF & Hpb & TSK).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI2. a4l.
pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)] m2) as MU2. pose proof (wmono_refl asegs m2) as WM2.
assert (INtk : In (r, 72) ((BS ++ LBc) ++ LM)) by (apply in_or_app; left; apply in_or_app; left; rewrite EBS; left; reflexivity).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ r 72 HP2 INtk) as (_ & Htal & Htlo & Hthi & _).
stash TOK. stash PBF. stash TSK. stash STR2. stash LOC1. stash LCK1. stash UTF2. stash WFR1. stash WSH1.
reenterA asegs A4L HIx asegs_wx HP2.
step. if_falsex. step. step. step. step.
evt_done5. unstash TOK. unstash PBF. unstash TSK. unstash STR2. unstash LOC1. unstash LCK1. unstash UTF2. unstash WFR1. unstash WSH1.
destruct PBF as (buf & post & EPBS & PCORE).
set (len := Z.of_nat (length str0) + 1).
replace (str0 ++ Z_to_bv 8 0 :: slack) with ((str0 ++ [Z_to_bv 8 0]) ++ slack) in STR2 by (rewrite <- app_assoc; reflexivity).
apply bytes_at_app in STR2 as [S1 S2]. rewrite length_app in S2. cbn [length] in S2. replace (sb + Z.of_nat (length str0 + 1)) with (sb + len) in S2 by (unfold len; lia).
assert (LBS : length BS = 4%nat) by (rewrite EBS, EPBS; reflexivity).
set (bslv := bB B2 - (Z.of_nat (pe_A0 len) + PhiPB len 32 + K_free * 4 + K_exit)).
set (dslv := bD B2 - Z.of_nat (pe_A0 len) - M2D).
eapply (json_tokener_parse_ex_B_cps HIx lh_globA lhg_outside lh_globA_client (fun _ _ _ _ _ H _ => H) (fun _ H => H) lhg_loc
MAPP SHRINK AADD PUT NEWARR NEWOBJ HD HD_le OADD USE ERRNOL DUP NEWL FREEL NEWDBL NEWBOOL NEWSTR
PARSEI PARSEU STRTOD NEWINT NEWUINT NEWDBLS)
with (TBS := BS) (LBc := LBc) (LM := LM) (FRS := (Fw, 0) :: FRS) (B := B2) (tk := r) (sb := sb) (len := len) (lenr := 2^64 - 1) (lo := lo) (bsl := bslv) (dsl := dslv)
(sp0 := bv_unsigned sp + -80) (payload := str0 ++ [Z_to_bv 8 0]) (slack := slack) (errv := errv2) (mxd := 32) (q := stk0) (pb := pb) (pbs := PBS).
1: heap_nowA A4L HIx HP2 MU2 WM2 MI2.
1: exact EBS.
1: lia.
1: exact TOK.
1: (exists buf, 0, 32, [], post; split; [exact EPBS | split; [reflexivity | exact PCORE]]).
1: exact Hpb.
1: exact TSK.
1: (exists buf, 0, 32, [], post; split; [cbn [ts_init t_pbs]; exact EPBS | split; [reflexivity | split; [exact PCORE | lia]]]).
1: (rewrite EPBS; reflexivity).
1: exact S1.
1: (rewrite length_app; cbn [length]; unfold len; lia).
1: (unfold len; lia).
1: { split.
- right; right. exists Fr, kf. split; [exact INF'|]. split; [exact HF1|]. split; [unfold len; lia | exact UNP2].
- right. split; [reflexivity|]. split; [unfold len; lia|].
split. { exists str0. split; [reflexivity|]. intros Hin. rewrite Forall_forall in NONUL. apply (NONUL _ Hin). reflexivity. }
split; [exact S2|]. split; [unfold len; replace (sb + (Z.of_nat (length str0) + 1)) with (sb + Z.of_nat (length str0) + 1) by lia; exact PAD|].
right. exists Fr, kf. split; [exact INF'|]. split; [exact HF1 | unfold len; lia]. }
1: lia.
1: (unfold len; lia).
1: exact LOC1.
1: exact LCK1.
1: exact G2.
1: exact UTF2.
1: reflexivity.
1: eassumption.
1: exact LO.
1: (unfold PE_STK_A; lia).
1: (clear - SP32 SPR; Z.div_mod_to_equations; lia).
1: lia.
1: lia.
1: exact ERR2.
1: reflexivity.
1: exact (FRM2 FRM).
1: reflexivity.
1: reflexivity.
1: (apply bv_eq; vm_compute; reflexivity).
1: reflexivity.
1: reflexivity.
1-7: try (cbn [uw_ok uw_key]; rewrite ?unsigned_lit by lia; unfold a4_straces, PE_RA2; cbn [hl_straces hl_malloc hl_free hl_strdup A4L A4H hla_base]; repeat first [left; reflexivity | right]).
all: try exact LMN.
all: try (cbn [length]; lia).
all: try (fold len in BD; cbn [uw_cost] in *; lia).
all: try (unfold bslv; rewrite LBS; unfold K_free; lia).
all: try (unfold dslv; fold len in BD; lia).
all: try (unfold bslv; unfold toknew_costB, pbnew_costB in *; fold len in BB; unfold K_free, K_exit in *; lia).
intros ms3 md3 A3 (m3 & gp3 & r3 & errv3 & RBS & TBS & LK & B3 & RS3 & VM3 & ST3 & ERR3 & LOC3 & HPRX3 & HP3 & TOKR3 & RES3 & G3 & BB3 & BD3).
cbn [pe_ra pe_s0 pe_s1 pe_s2 pe_s3 pe_s4 pe_s5 pe_s6 pe_s7 pe_s8 pe_s9 pe_s10 pe_s11 pa_sp0 pa_bslack pa_dslack pf_tk pf_mxd pf_fl pf_len] in *.
destruct RS3 as (v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & F3 & fc3 & -> & FS3 & FRM3).
replace (ret_pc (Z_to_bv 64 PE_RA2)) with (Z_to_bv 64 PE_RA2) by (symmetry; apply ret_pc_even; [unfold PE_RA2; lia | reflexivity]).

eapply (heap_presx_rw_cells A4H) in FR; [| exact HPRX3 | left; cbn; lia].
eapply (heap_presx_rw_cells A4H) in LCK1; [| exact HPRX3 | right; left; cbn; intros z Hz; split; [cbn [hl_client_static A4H]; unfold a4_client_static, LOCALE_LOCK_A in *; lia | unfold QcmL.xlocA, a4_volatile, LOCALE_LOCK_A, LOCCELL_A, A_TP in *; lia]].
eapply (heap_presx_rw_cells A4H) in WFR1; [| exact HPRX3 | eapply client_rangex_block; [exact INWI | lia | cbn; lia]].
eapply (heap_presx_rw_cells A4H) in WSH1; [| exact HPRX3 | eapply client_rangex_block; [exact INWS | unfold A_SB; lia | unfold A_SB; cbn; lia]].
assert (UTF3 : bytes_at asegs m3 UTF8REP_ADDR_A Qa8x.Mq3.utf8rep).
{ eapply (heap_presx_bytes_at A4H); [exact HPRX3 | exact UTF2 |]. right; left. intros z Hz. unfold UTF8REP_ADDR_A in Hz. cbn in Hz.
split; [cbn [hl_client_static A4H]; unfold a4_client_static; lia | unfold QcmL.xlocA, a4_volatile, LOCCELL_A, A_TP; lia]. }

pose proof TOKR3 as (stk3 & pb3 & dep3 & PBS3 & lvs3 & x3 & ETBS3 & LEN3 & DEP3 & TOK3 & _).
destruct x3 as [isd3 stp3 cho3 err3 ucs3 hi3 qu3].
assert (INtk3 : In (r, 72) (RBS ++ TBS ++ LK ++ LBc)) by (apply in_or_app; right; apply in_or_app; left; rewrite ETBS3; left; reflexivity).
assert (SHT3 : ro_cells asegs m3 (r / 8 + A_SB)
[C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]).
{ pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ r 72 HP3 INtk3) as SH. unfold shad in SH. apply shadow_ro_cells in SH.
let cs := eval cbv in (shadow_cells 72) in change (shadow_cells 72) with cs in SH. exact SH. }
unfold tok_cells_g in TOK3. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK3.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP3) as MI3.
pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (Fw, Fw + 56)] m3) as MU3. pose proof (wmono_refl asegs m3) as WM3.
unfold A_SB, PE_RA2 in *. a4l.
stash LOC3. stash LCK1. stash UTF3. stash RES3.
reenterA asegs A4L HIx asegs_wx HP3.
step. step. ub_align_near Htal.
step. if_falsex.
step. step. ub_align_near EA4.
step. asan_chkB.
step. step. sh_norm. ub_div8. step. rewrite ?sxb_zero, ?zxb_zero. step. step. if_true.
step. rewrite ?(unsigned_lit (Fw + 32)) by lia. rewrite ?(land7_of_mod8 (Fw + 32) EA8).
step. step. ub_if_lit.
step.
unstash LOC3. unstash LCK1. unstash UTF3. unstash RES3.
eapply rw_cells_transport in LOC3; [| exact MU3 | exact WM3 | unfold LOCCELL_A, A_TP; cbn [disjoint_from cells_size csize Nat.add]; lia].
eapply rw_cells_transport in LCK1; [| exact MU3 | exact WM3 | unfold LOCALE_LOCK_A; cbn [disjoint_from cells_size csize Nat.add]; lia].
lazymatch type of MU3 with munch _ _ ?mc =>
assert (UTF3c : bytes_at asegs mc UTF8REP_ADDR_A Qa8x.Mq3.utf8rep) by (eapply bytes_at_transport; [exact UTF3 | exact MU3 |]; unfold UTF8REP_ADDR_A; cbn [disjoint_from length Qa8x.Mq3.utf8rep]; lia);
assert (RES3c : (r3 = 0 /\ RBS = []) \/ (r3 <> 0 /\ exists s, jval asegs A4F s mc RBS r3 1 /\ sdepth s <= 32 /\ exists w, jtx s RBS = Some (w, []) /\ w <= 26 * (Z.of_nat (length str0) + 1) + 64));
[ destruct RES3 as [L | (NZ & sj & J & D)]; [left; exact L | right]; split; [exact NZ|]; exists sj; split; [| exact D];
eapply (jval_agree asegs A4F); [exact J | | apply incl_refl]; eapply (agree_of_munch asegs); [exact MU3 | exact WM3 |];
intros a n Hin; cbn [disjoint_from]; split; [| split; [| exact I]];
[ pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ a n HP3 ltac:(apply in_or_app; left; apply in_or_app; left; exact Hin)) as (_ & _ & _ & Hhi & _); unfold alloc_ceiling, sp_window_lo, stack_max_size in Hhi; lia
| pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP3 INW ltac:(apply in_or_app; left; apply in_or_app; left; exact Hin)) as X; change (fr_size 0) with 64 in X; lia ]
| clear UTF3 RES3 ]
end.

assert (FREE : forall (m4 : word -> option byte) (md4 : config) (A4 : ASA A4L HIx) (B4 : bud) (F4 : bvmap 5 word) (fc4 : bv 32) (RBS4 : list blk) (r4 : Z) (errv4 : word) (e4 : word) (j1 j2 : list byte)
(x1 gpx y0 y1 y2 b1 b2 b3 b4 b5 b6 b7 z6 z7 z8 y3 y4 y5 y6 y7 : word),
HEAPAx A4 (RBS4 ++ TBS ++ LK ++ LBc) LM ((Fw, 0) :: FRS) B4 m4 md4 ->
((r4 = 0 /\ RBS4 = []) \/
(r4 <> 0 /\ exists s, jval asegs A4F s m4 RBS4 r4 1 /\ sdepth s <= 32 /\ exists w, jtx s RBS4 = Some (w, []) /\ w <= 26 * (Z.of_nat (length str0) + 1) + 64)) ->
tokrep_g asegs A4F 32 0 m4 TBS r ->
heap_presx A4H QcmL.xlocA (LBc ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m4 ->
model_vm_only (cfg_model md) (cfg_model md4) -> fsaved F F4 -> (frm0 fc -> frm0 fc4) ->
rw_cells asegs m4 LOCCELL_A [C8 (Z_to_bv 64 GLOBLOC_A)] -> rw_cells asegs m4 LOCALE_LOCK_A [C4 (Z_to_bv 64 0)] -> lh_globA m4 ->
bytes_at asegs m4 UTF8REP_ADDR_A Qa8x.Mq3.utf8rep ->
stk asegs m4 lo (bv_unsigned sp + -80) ->
rw_cells asegs m4 (bv_unsigned sp + -80) [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] -> rw_cells asegs m4 A_ERRNO [C4 errv4] ->
rw_cells asegs m4 Fw [C8 h0; C8 h1; C8 h2; CB 8 j1; C4 e4; CB 20 j2] ->
rw_cells asegs m4 (Fw / 8 + 2147450880) [C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 4); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243)] ->
bB B - tokparse_costB (Z.of_nat (length str0)) + tokfree_costB TBS <= bB B4 ->
bD B - tokparse_costD (Z.of_nat (length str0)) + 1 <= bD B4 ->
AJ5 A4L HIx A4 T md4
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -80)) gpx (Z_to_bv 64 6444320) y0 y1 y2 (Z_to_bv 64 r) (Z_to_bv 64 (r + 36)) (Z_to_bv 64 r4) b1 b2 b3 b4 b5 b6 b7
(Z_to_bv 64 (Fw + 32)) z7 (Z_to_bv 64 2147450880) (Z_to_bv 64 (r / 8 + 2147450884)) z6 z8 y3 s9 s10 s11 y4 y5 y6 y7)
F4 (Z_to_bv 64 0x938ac) fc4 None m4 (seg_rom asegs))).
{ clear - K HD_le PUT ACR HT47 SPR LO LOS SPA HT RA Htlo Hthi Htal Hr BB BD HWal HWc EA8.
intros m4 md4 A4 B4 F4 fc4 RBS4 r4 errv4 e4 j1 j2 x1 gpx y0 y1 y2 b1 b2 b3 b4 b5 b6 b7 z6 z7 z8 y3 y4 y5 y6 y7 HP4 RES4 TOKR4 PX4 VM4 FS4 FRM4 LOC4 LCK4 G4 UTF4 ST4 FR4 ERR4 WFR4 WSH4 BB4 BD4.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP4) as MI4.
pose proof (munch_refl [] m4) as MU4. pose proof (wmono_refl asegs m4) as WM4.
a4l. reenterA asegs A4L HIx asegs_wx HP4.
step.
evt_done5. unstash K.
eapply (tokfree_segB HIx PUT (bv_unsigned sp + -80) r) with (BS := TBS) (LB := RBS4 ++ LK ++ LBc) (LM := LM) (FRS := (Fw, 0) :: FRS) (B := B4) (lo := lo) (errv := errv4);
[ eapply (heapA_perm A4L HIx); [heap_nowA A4L HIx HP4 MU4 WM4 MI4 | apply Permutation_app_swap_app | apply Permutation_refl | apply Permutation_refl]
| apply tokrep_g32; exact TOKR4 | exact Hr | unfold tfv_frame; exact FR4 | exact ST4 | unfold_consts_goal; lia | unfold put_stk_A; lia
| clear - SPA SPR; Z.div_mod_to_equations; lia | lia | lia | exact ERR4
| unfold tokparse_costB in BB4; unfold tokfree_costB in *; lia
| unfold tokparse_costD in BD4; lia | ].
intros ms5 md5 A5 (m5 & B5 & F5 & fc5 & z1 & u0 & u1 & u2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & u3 & u4 & u5 & u6 & q1 & q2 & q3 & q5 & q7 & q8 & -> & FS5 & FRM5 & VM5 & ST5 & FR5 & HPR5 & ERR5 & BB5 & BD5 & HP5).
unfold tfv_frame in FR5. unfold tokfree_done_B_pc.
a4l.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP5) as MI5.
pose proof (munch_refl [] m5) as MU5. pose proof (wmono_refl asegs m5) as WM5.
reenterA asegs A4L HIx asegs_wx HP5.
step. step.
do 12 step.
evt_done5. eapply (K _ _ _ _ B5 _ r4 errv4 RBS4 LK e4 j1 j2).
+ apply ret_statew_intro; [eapply fsaved_trans; [exact FS4 | exact FS5] | intros Hf; exact (FRM5 (FRM4 Hf))].
+ eapply model_vm_only_trans; [exact VM4 | exact VM5].
+ release_frame FR5 ST5 (bv_unsigned sp). exact ST5.
+ exact ERR5.
+ eapply (heap_pres_rw_cells A4H); [exact HPR5 | exact LOC4 |]. right; left. cbn. intros z Hz. cbn [hl_client_static A4H]. unfold a4_client_static, LOCCELL_A, A_TP in *. lia.
+ eapply (heap_pres_rw_cells A4H); [exact HPR5 | exact LCK4 |]. right; left. cbn. intros z Hz. cbn [hl_client_static A4H]. unfold a4_client_static, LOCALE_LOCK_A in *. lia.
+ exact (lh_globA_client _ _ _ _ HPR5 G4).
+ eapply (heap_pres_bytes_at A4H); [exact HPR5 | exact UTF4 |]. right; left. intros z Hz. unfold UTF8REP_ADDR_A in Hz. cbn in Hz. cbn [hl_client_static A4H]. unfold a4_client_static. lia.
+ eapply heap_presx_trans; [exact PX4|]. apply heap_pres_presx. eapply heap_pres_weaken; [exact HPR5 | lia |].
intros b Hb. apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; apply in_or_app; right; apply in_or_app; right; exact Hb | apply in_or_app; right].
apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; exact Hb | apply in_or_app; right; cbn [fr_ivs flat_map app]; right; right; exact Hb].
+ eapply (heap_pres_rw_cells A4H); [exact HPR5 | unfold wfr_cells2; exact WFR4 |].
eapply client_range_block; [apply in_or_app; right; apply in_or_app; right; apply fr_ivs_frame; left; reflexivity | lia | unfold wfr_cells2; change (fr_size 0) with 64; cbn; lia].
+ eapply (heap_pres_rw_cells A4H); [exact HPR5 | unfold wsh_cells, A_SB; exact WSH4 |].
eapply client_range_block; [apply in_or_app; right; apply in_or_app; right; apply fr_ivs_shadow; left; reflexivity | unfold shad; cbn [hl_sb A4L]; unfold A_SB; lia | unfold shad, wsh_cells; cbn [hl_sb A4L cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ]; unfold A_SB; change (fr_shadow_len 0) with 8; lia].
+ unfold jo_chargeA. unfold tokfree_costB in *. split; lia.
+ exact HP5.
+ destruct RES4 as [L | (NZ & s & J & D)]; [left; exact L | right]. split; [exact NZ|]. exists s. split; [| exact D].
eapply (jval_agree asegs A4F); [exact J | eapply (agree_of_heap_pres asegs A4H); [exact HPR5 | reflexivity | intros b Hb; apply in_or_app; left; apply in_or_app; left; exact Hb] | apply incl_refl]. }

assert (PX3 : heap_presx A4H QcmL.xlocA (LBc ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m3).
{ eapply heap_presx_trans.
- apply heap_pres_presx. eapply heap_pres_weaken; [exact HPR | lia |].
intros b Hb. apply in_app_or in Hb as [Hb|Hb]; [apply in_or_app; left; exact Hb | apply in_or_app; right]. apply in_app_or in Hb as [Hb|Hb]; [apply in_or_app; left; exact Hb | apply in_or_app; right; cbn [fr_ivs flat_map app]; right; right; exact Hb].
- eapply heap_presx_weaken; [exact HPRX3 | lia | | intros a Xa; exact Xa].
intros b Hb. apply in_app_or in Hb as [Hb|Hb]; [apply in_or_app; left; exact Hb | apply in_or_app; right]. apply in_app_or in Hb as [Hb|Hb]; [apply in_or_app; left; exact Hb | apply in_or_app; right; cbn [fr_ivs flat_map app]; right; right; exact Hb]. }
assert (VM03 : model_vm_only (cfg_model md) (cfg_model md3)) by (eapply model_vm_only_trans; [exact VM2 | exact VM3]).
assert (FS03 : fsaved F F3) by (eapply fsaved_trans; [exact FS2 | exact FS3]).
assert (BB03 : bB B - tokparse_costB (Z.of_nat (length str0)) + tokfree_costB TBS + 512 * Z.of_nat (length RBS) <= bB B3).
{ unfold tokparse_costB, tokfree_costB. fold len. unfold bslv in BB3. rewrite length_app, Nat2Z.inj_add in BB3. unfold toknew_costB, pbnew_costB, K_free in *. lia. }
assert (BD03 : bD B - tokparse_costD (Z.of_nat (length str0)) + 1 <= bD B3).
{ unfold tokparse_costD. fold len. unfold dslv in BD3. lia. }
lazymatch type of MU3 with munch _ _ ?mc =>
assert (HPc3 : HEAPAx A3 (RBS ++ TBS ++ LK ++ LBc) LM ((Fw, 0) :: FRS) B3 mc md3) by (heap_nowW HP3 MU3 WM3 MI3 INW);
assert (TOKRc : tokrep_g asegs A4F 32 0 mc TBS r);
[ eapply tokrep_g_agree; [exact TOKR3 |]; eapply (agree_of_munch asegs); [exact MU3 | exact WM3 |]; intros a n Hin; cbn [disjoint_from]; split; [| split; [| exact I]];
[ pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ a n HP3 ltac:(apply in_or_app; left; apply in_or_app; right; apply in_or_app; left; exact Hin)) as (_ & _ & _ & Hhi & _); unfold alloc_ceiling, sp_window_lo, stack_max_size in Hhi; lia
| pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP3 INW ltac:(apply in_or_app; left; apply in_or_app; right; apply in_or_app; left; exact Hin)) as X; change (fr_size 0) with 64 in X; lia ]
| ];
assert (Gc : lh_globA mc) by (eapply lhg_outside; [exact G3 | exact MU3 | exact WM3 | apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]; cbn [fst snd hl_img_lo hl_img_hi A4H]; lia]);
assert (PXc : heap_presx A4H QcmL.xlocA (LBc ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m mc)
end.
{ eapply heap_presx_trans; [exact PX3|]. eapply (heap_presx_of_munch A4H); [exact MU3 | exact WM3 |]. intros a Ha Hc. cbn [outside]. split; [| split; [| exact I]].
--
destruct Hc as [Hc | [Hx | (b & Hb & Hbr)]]; [lia | cbn [hl_client_static A4H] in Hx; unfold a4_client_static, alloc_ceiling, sp_window_lo, stack_max_size in *; lia |].
apply in_app_or in Hb as [Hb|Hb]; [| apply in_app_or in Hb as [Hb|Hb]].
++ destruct b as [ba bn]. pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ ba bn HP3 ltac:(apply in_or_app; left; apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; exact Hb)) as (_ & _ & _ & Hhi & _). cbn [blk_addr blk_size fst snd] in Hbr. unfold alloc_ceiling, sp_window_lo, stack_max_size in Hhi. lia.
++ destruct b as [ba bn]. pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ ba bn HP3 ltac:(apply in_or_app; right; exact Hb)) as (_ & _ & _ & Hhi & _). cbn [blk_addr blk_size fst snd] in Hbr. unfold alloc_ceiling, sp_window_lo, stack_max_size in Hhi. lia.
++ apply in_fr_ivs in Hb as (G0 & kg & HG & [E|E]); subst b; cbn [blk_addr blk_size fst snd] in Hbr.
** pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP3 ltac:(right; exact HG)) as (Hkg & _ & _ & Hhi & _). pose proof (fr_size_pos kg ltac:(lia)). unfold alloc_ceiling, sp_window_lo, stack_max_size in Hhi. lia.
** pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP3 ltac:(right; exact HG)) as (Hkg & _ & HG0 & Hhi & _). unfold shad in Hbr. cbn [hl_sb A4L] in Hbr. unfold A_SB in Hbr.
pose proof (fr_shadow_len_bnd kg ltac:(lia)) as SLB. pose proof (fr_size_pos kg ltac:(lia)) as FSP.
assert (G8 : G0 / 8 <= (2 ^ 47 - 1) / 8) by (apply Z.div_le_mono; clear - Hhi ACR FSP; unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia).
clear - Hbr G8 SLB LO LOS ACR. unfold alloc_ceiling, sp_window_lo, stack_max_size in *. lia.
--
destruct Hc as [Hc | [Hx | (b & Hb & Hbr)]]; [unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia | cbn [hl_client_static A4H] in Hx; unfold a4_client_static in Hx; lia |].
apply in_app_or in Hb as [Hb|Hb]; [| apply in_app_or in Hb as [Hb|Hb]].
++ destruct b as [ba bn]. pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP3 INW ltac:(apply in_or_app; left; apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; exact Hb)) as X. change (fr_size 0) with 64 in X. cbn [blk_addr blk_size fst snd] in Hbr. lia.
++ destruct b as [ba bn]. pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP3 INW ltac:(apply in_or_app; right; exact Hb)) as X. change (fr_size 0) with 64 in X. cbn [blk_addr blk_size fst snd] in Hbr. lia.
++ apply in_fr_ivs in Hb as (G0 & kg & HG & [E|E]); subst b; cbn [blk_addr blk_size fst snd] in Hbr.
** assert (NE : G0 <> Fw).
{ intros ->. pose proof (proj1 (stdpp.base.NoDup_ListNoDup _) (heapA_frame_nodup A4L HIx _ _ _ _ _ _ _ HP3)) as ND. cbn in ND. apply List.NoDup_cons_iff in ND as [Hni _]. apply Hni. cbn [fr_base fst]. exact (in_map fr_base _ _ HG). }
pose proof (heapA_frame_apart A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP3 INW ltac:(right; exact HG) ltac:(intros E; apply NE; symmetry; exact E)) as X. change (fr_size 0) with 64 in X.
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP3 ltac:(right; exact HG)) as (Hkg & _). pose proof (fr_size_pos kg ltac:(lia)). lia.
** pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP3 ltac:(right; exact HG)) as (Hkg & _ & HG0 & Hhi & _). unfold shad in Hbr. cbn [hl_sb A4L] in Hbr. unfold A_SB in Hbr.
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP3 INW) as AP. cbn [hl_sb A4L] in AP. change (fr_size 0) with 64 in AP. unfold A_SB in AP.
pose proof (fr_shadow_len_bnd kg ltac:(lia)) as SLB. pose proof (fr_size_shadow kg ltac:(lia)) as FSS.
assert (G9 : (G0 + fr_size kg) / 8 <= 140737479966720 / 8) by (apply Z.div_le_mono; clear - Hhi ACR; unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia).
rewrite FSS in G9. replace ((G0 + 8 * fr_shadow_len kg) / 8) with (G0 / 8 + fr_shadow_len kg) in G9 by (clear - SLB; Z.div_mod_to_equations; lia).
assert (G10 : 0 <= G0 / 8) by (apply Z.div_pos; lia).
clear - Hbr G9 SLB AP G10. change (140737479966720 / 8) with 17592184995840 in G9. change ((2 ^ 47 - 1) / 8) with 17592186044415 in AP. lia. }
step. match goal with |- context [if ?c then Z_to_bv 64 0x938ac else _] => destruct c end.
+
evt_done5.
lazymatch goal with |- AJ5 _ _ _ _ _ (MS _ _ _ _ _ ?mc _) => lazymatch goal with H : rw_cells asegs mc Fw (_ :: _ :: _ :: CB 8 ?J1 :: C4 ?E :: CB 20 ?J2 :: _) |- _ =>
eapply (FREE mc md3 A3 B3 F3 fc3 RBS r3 errv3 E J1 J2);
[ exact HPc3 | exact RES3c | exact TOKRc | exact PXc | exact VM03 | exact FS03 | intros Hf; exact (FRM3 (FRM2 Hf)) | exact LOC3 | exact LCK1 | exact Gc | exact UTF3c
| eassumption | eassumption | eassumption | exact H | eassumption | pose proof (Zle_0_nat (length RBS)); lia | exact BD03 ]
end end.
+
destruct RES3c as [[-> ->] | (NZ3 & s3v & J3 & D3)].
* step. if_true. evt_done5.
lazymatch goal with |- AJ5 _ _ _ _ _ (MS _ _ _ _ _ ?mc _) => lazymatch goal with H : rw_cells asegs mc Fw (_ :: _ :: _ :: CB 8 ?J1 :: C4 ?E :: CB 20 ?J2 :: _) |- _ =>
eapply (FREE mc md3 A3 B3 F3 fc3 [] 0 errv3 E J1 J2);
[ exact HPc3 | left; split; reflexivity | exact TOKRc | exact PXc | exact VM03 | exact FS03 | intros Hf; exact (FRM3 (FRM2 Hf)) | exact LOC3 | exact LCK1 | exact Gc | exact UTF3c
| eassumption | eassumption | eassumption | exact H | eassumption | cbn [length Z.of_nat] in BB03; lia | exact BD03 ]
end end.
* assert (RR : 0 < r3 /\ r3 + 48 <= alloc_ceiling).
{ pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP3) as ND. rewrite !map_app in ND. apply List.NoDup_app_remove_r in ND. apply List.NoDup_app_remove_r in ND.
lazymatch type of MU3 with munch _ _ ?mc =>
destruct (QmZZ.jval_hdr asegs A4F s3v mc RBS r3 1 J3 ND) as (n & tojs & pb0 & udel & ud & rest & INp & Hn & H48 & _) end.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ r3 n HP3 ltac:(apply in_or_app; left; apply in_or_app; left; exact INp)) as (_ & _ & Hlo & Hhi & _). lia. }
step. if_falsex. step. evt_done5.
eapply PUT with (s := Some s3v) (BS := RBS) (p := r3) (rc := 1) (lo := lo) (LB := TBS ++ LK ++ LBc);
[ exact HPc3 | cbn [QPIU.Mqi.put_pre]; split; [exact NZ3 | split; [lia | exact J3]] | reflexivity | .. ];
a4l_goal; rewrite ?unsigned_lit by lia; try first [reflexivity | eassumption | lia].
1: (unfold put_stk_A; lia).
all: try (clear - SPA SPR; Z.div_mod_to_equations; lia).
1: (unfold put_costA; change (1 =? 1) with true; cbv iota; unfold tokparse_costB, tokfree_costB in BB03; pose proof (Zle_0_nat (length TBS)); unfold toknew_costB, pbnew_costB, PhiPB, K_free, K_exit in *; lia).
intros ms4 md4 A4 (m4 & rv4 & B4 & RS4 & VM4 & ST4 & HPR4 & ERR4 & BB4 & BD4 & OUT4).
destruct RS4 as (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & F4 & fc4 & -> & FS4 & FRM4).
a4l. rewrite ?unsigned_lit in ST4 by lia. rewrite ?unsigned_lit in HPR4 by lia.
lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?n)] => replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia | reflexivity]) end.
assert (HP4 : HEAPAx A4 (TBS ++ LK ++ LBc) LM ((Fw, 0) :: FRS) B4 m4 md4) by (destruct OUT4 as [[_ H] | (s' & _ & RC & _)]; [exact H | lia]).
clear OUT4.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP4) as MI4.
pose proof (munch_refl [] m4) as MU4. pose proof (wmono_refl asegs m4) as WM4.
assert (INWI4 : In (Fw, 56) ((TBS ++ LK ++ LBc) ++ LM ++ fr_ivs A4L ((Fw, 0) :: FRS))) by (apply in_or_app; right; apply in_or_app; right; change 56 with (fr_size 0 - 8); apply fr_ivs_frame; exact INW).
assert (INWS4 : In (Fw / 8 + 2147450880, 8) ((TBS ++ LK ++ LBc) ++ LM ++ fr_ivs A4L ((Fw, 0) :: FRS))).
{ apply in_or_app; right; apply in_or_app; right. change (Fw / 8 + 2147450880, 8) with (shad A4L Fw, fr_shadow_len 0). apply fr_ivs_shadow. exact INW. }
lazymatch goal with H : rw_cells asegs _ Fw (_ :: _ :: _ :: CB 8 _ :: C4 _ :: CB 20 _ :: _) |- _ =>
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR4) in H; [| eapply client_range_block; [exact INWI4 | lia | cbn; lia]] end.
lazymatch goal with H : rw_cells asegs _ (Fw / 8 + 2147450880) _ |- _ =>
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR4) in H; [| eapply client_range_block; [exact INWS4 | lia | cbn; lia]] end.
a4l.
reenterA asegs A4L HIx asegs_wx HP4.
step. evt_done5.
lazymatch type of HPc3 with HEAPA _ _ _ _ _ _ _ ?mc _ =>
assert (AG4 : agree_on asegs TBS mc m4) by (eapply (agree_of_heap_pres asegs A4H); [exact HPR4 | reflexivity |]; intros b Hb; apply in_or_app; left; apply in_or_app; left; exact Hb) end.
lazymatch goal with |- AJ5 _ _ _ _ _ (MS _ _ _ _ _ ?mc _) => lazymatch goal with H : rw_cells asegs mc Fw (_ :: _ :: _ :: CB 8 ?J1 :: C4 ?E :: CB 20 ?J2 :: _) |- _ =>
eapply (FREE mc md4 A4 B4 F4 fc4 [] 0 errv3 E J1 J2)
end end.
-- exact HP4.
-- left. split; reflexivity.
-- eapply tokrep_g_agree; [exact TOKRc | exact AG4].
-- eapply heap_presx_trans; [exact PXc|]. apply heap_pres_presx. eapply heap_pres_weaken; [exact HPR4 | lia |].
intros b Hb. apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; apply in_or_app; right; apply in_or_app; right; exact Hb | apply in_or_app; right].
apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; exact Hb | apply in_or_app; right; cbn [fr_ivs flat_map app]; right; right; exact Hb].
-- eapply model_vm_only_trans; [exact VM03 | exact VM4].
-- eapply fsaved_trans; [exact FS03 | exact FS4].
-- intros Hf. exact (FRM4 (FRM3 (FRM2 Hf))).
-- eapply (heap_pres_rw_cells A4H); [exact HPR4 | exact LOC3 |]. right; left. cbn. intros z Hz. cbn [hl_client_static A4H]. unfold a4_client_static, LOCCELL_A, A_TP in *. lia.
-- eapply (heap_pres_rw_cells A4H); [exact HPR4 | exact LCK1 |]. right; left. cbn. intros z Hz. cbn [hl_client_static A4H]. unfold a4_client_static, LOCALE_LOCK_A in *. lia.
-- exact (lh_globA_client _ _ _ _ HPR4 Gc).
-- eapply (heap_pres_bytes_at A4H); [exact HPR4 | exact UTF3c |]. right; left. intros z Hz. unfold UTF8REP_ADDR_A in Hz. cbn in Hz. cbn [hl_client_static A4H]. unfold a4_client_static. lia.
-- eassumption.
-- eapply (heap_pres_rw_cells A4H) in FR; [| exact HPR4 | left; cbn; lia]. exact FR.
-- eassumption.
-- eassumption.
-- eassumption.
-- unfold put_costA in BB4. change (1 =? 1) with true in BB4. cbv iota in BB4. lia.
-- lia.
Qed.

Lemma json_tokener_parse_B_main :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LBc LM : list blk) (FRS : list frame) (B : bud) (sb lo : Z) (str0 slack : list byte) (errv : word),
jo_preA HIx A LBc LM FRS B m md sp tp ra lo (96 + 80 + 432 + 12288 + 4096) errv ->
bv_unsigned sp mod 32 = 0 -> Z.of_nat (length LM) < 8 ->
cstring_argA FRS m sb str0 slack -> Z.of_nat (length str0) < 2^25 ->
rw_cells asegs m LOCCELL_A [C8 (Z_to_bv 64 GLOBLOC_A)] -> rw_cells asegs m LOCALE_LOCK_A [C4 (Z_to_bv 64 0)] -> lh_globA m ->
bytes_at asegs m UTF8REP_ADDR_A Qa8x.Mq3.utf8rep ->
Z.of_nat (length FRS) + 3 < 4096 ->
tokparse_costB (Z.of_nat (length str0)) <= bB B -> tokparse_costD (Z.of_nat (length str0)) <= bD B ->
frm0 fc -> a0 = Z_to_bv 64 sb ->
(forall ms' md' m' (A' : ASA A4L HIx) (B' : bud) (gp' : word) (r : Z) (errv' : word) (RBS LK : list blk),
ret_statew A4H ra sp gp' tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' ->
model_vm_only (cfg_model md) (cfg_model md') ->
stk asegs m' lo (bv_unsigned sp) ->
rw_cells asegs m' A_ERRNO [C4 errv'] ->
rw_cells asegs m' LOCCELL_A [C8 (Z_to_bv 64 GLOBLOC_A)] -> rw_cells asegs m' LOCALE_LOCK_A [C4 (Z_to_bv 64 0)] -> lh_globA m' ->
bytes_at asegs m' UTF8REP_ADDR_A Qa8x.Mq3.utf8rep ->
heap_presx A4H QcmL.xlocA (LBc ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m' ->
jo_chargeA (tokparse_costB (Z.of_nat (length str0))) (tokparse_costD (Z.of_nat (length str0))) B B' ->
HEAPAx A' (RBS ++ LK ++ LBc) LM FRS B' m' md' ->
((r = 0 /\ RBS = []) \/
(r <> 0 /\ exists s, jval asegs A4F s m' RBS r 1 /\ sdepth s <= 32 /\ exists w, jtx s RBS = Some (w, []) /\ w <= 26 * (Z.of_nat (length str0) + 1) + 64)) ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 json_tokener_parse_B_entry) fc None m (seg_rom asegs)).
Proof.
intros until errv. intros PRE SP32 LMN CSTR LEN LOC LCK G UTF FRN BB BD FRM A0 K. subst a0.
destruct PRE as (HP & ST & LO & LOS & SPA & HT & ERR & TP & RA).
pose proof CSTR as (STR & NONUL & PAD & ALOC & UNP). destruct ALOC as (Fr & kf & INF & HF1 & HF2).
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP INF) as (Hkf & HFal & HF0 & HFc & _).
pose proof alloc_ceiling_range as ACR. pose proof (hiA_top_le A4L HIx) as HT47.
word_range sp SPR. word_range s0 S0R.
pose proof (bytes_at_bound _ _ _ _ STR) as SB0. rewrite length_app in SB0. cbn [length] in SB0.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
destruct (heapA_sb_cells A4L HIx _ _ _ _ _ _ _ HP) as (SB1 & SB2 & SB3 & SB4).
apply ro_C8_of_bytes_at in SB1. apply ro_C8_of_bytes_at in SB2. apply ro_C8_of_bytes_at in SB3.
assert (UARC : ro_cells asegs m (hl_uar_cell A4L) [C4 (Z_to_bv 64 1)]) by (split; [cbn; split; exact I | cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact SB4]).
clear SB4.
set (L0 := LBc ++ LM ++ fr_ivs A4L FRS).
assert (SUBa : forall b, In b L0 -> In b (LBc ++ LM) \/ In b (fr_ivs A4L FRS)).
{ intros b Hb. unfold L0 in Hb. rewrite app_assoc in Hb. apply in_app_or in Hb as [Hb | Hb]; [left; exact Hb | right; exact Hb]. }
pose proof (heap_presx_refl A4H xlocA L0 (bv_unsigned sp) m) as HPX.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)] m) as MU.

assert (TRK : forall mx, munch [(bv_unsigned sp - 64, bv_unsigned sp)] m mx -> wmono asegs m mx ->
bytes_at asegs mx sb (str0 ++ Z_to_bv 8 0 :: slack) /\ rw_cells asegs mx LOCCELL_A [C8 (Z_to_bv 64 GLOBLOC_A)] /\
rw_cells asegs mx LOCALE_LOCK_A [C4 (Z_to_bv 64 0)] /\ lh_globA mx /\ bytes_at asegs mx UTF8REP_ADDR_A Qa8x.Mq3.utf8rep /\
unpoisoned asegs mx A_SB sb (Z.of_nat (length str0) + 1)).
{ intros mx MUx WMx.
split. { eapply bytes_at_transport; [exact STR | exact MUx |]. cbn [disjoint_from]. rewrite length_app. cbn [length]. lia. }
split. { eapply rw_cells_transport; [exact LOC | exact MUx | exact WMx |]. unfold LOCCELL_A, A_TP. cbn [disjoint_from cells_size csize Nat.add]. lia. }
split. { eapply rw_cells_transport; [exact LCK | exact MUx | exact WMx |]. unfold LOCALE_LOCK_A. cbn [disjoint_from cells_size csize Nat.add]. lia. }
split. { eapply lhg_outside; [exact G | exact MUx | exact WMx |]. apply Forall_cons; [| apply Forall_nil]. cbn [fst snd hl_img_lo hl_img_hi A4H]. lia. }
split. { eapply bytes_at_transport; [exact UTF | exact MUx |]. unfold UTF8REP_ADDR_A. cbn [disjoint_from length Qa8x.Mq3.utf8rep]. lia. }
eapply unpoisoned_transport; [exact UNP | exact MUx |]. intros a k Ha Hk. cbn [disjoint_from]. split; [| exact I]. left.
assert (HH : shadow_span_hi A_SB sb (Z.of_nat (length str0) + 1) <= 2^45).
{ unfold shadow_span_hi, A_SB. assert (E1 : (sb + (Z.of_nat (length str0) + 1) - 1) / 8 <= 2^44) by (apply Z.div_le_upper_bound; lia).
pose proof (Z.mul_div_le ((sb + (Z.of_nat (length str0) + 1) - 1) / 8 + 2147450880) 8 ltac:(lia)). lia. }
lia. }
stash TRK. stash K. stash CSTR.
unfold json_tokener_parse_B_entry, LOCCELL_A, LOCALE_LOCK_A, A_ERRNO, A_TP in *.
a4l. reenterA asegs A4L HIx asegs_wx HP. subst tp.
carve_frame 64%nat ST.
step. stepz. do 6 step.
step. step.
rewrite ?(unsigned_lit (bv_unsigned sp + -64)) by lia. change 18446744073709551584 with (2^64 - 2^5). rewrite OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.land_align_down by lia. change (2^5) with 32.
replace (bv_unsigned sp + -64 - (bv_unsigned sp + -64) mod 32) with (bv_unsigned sp + -64) by (clear - SP32 SPR; Z.div_mod_to_equations; lia).
step.
step. step. step. step. step.
norm_sx32. step.
step. if_false.
step. step. step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (HPX1 : heap_presx A4H xlocA L0 (bv_unsigned sp) m mc)
by (eapply heap_presx_trans; [exact HPX | eapply (presx_private HIx _ _ _ _ _ _ _ _ _ L0 (bv_unsigned sp) HP MU WM SUBa ltac:(lia))]; apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_nil]);
unstash TRK; destruct (TRK mc MU WM) as (STR1 & LOC1 & LCK1 & G1 & UTF1 & UNP1); stash TRK
end.
clear HPX.
evt_done5.
eapply (hiA_stack_malloc A4L HIx) with (k := 0) (bytes := 64) (lo := lo) (LB := LBc) (LM := LM) (FR := FRS) (B := B);
[ heap_nowA A4L HIx HP MU WM MI | lia | change (fr_size 0) with 64; lia | reflexivity | (clear - FRN; lia) | .. ].
all: rewrite ?unsigned_lit by lia.
1: eassumption.
1: exact LO.
1: cbn [hl_stack_A A4L]; lia.
1: clear - SPA SPR; Z.div_mod_to_equations; lia.
1: lia.
1: reflexivity.
1: reflexivity.
intros ms1 m1' md1 A1 Fw RS1 VM1 ST1 HPR1 FWNZ (jff & FF1) SHB1 HP1. open_ret RS1.
rewrite ?unsigned_lit in ST1, HPR1 by lia.
clear ERR. destruct (heapA_errno A4L HIx _ _ _ _ _ _ _ HP1) as (errv1 & ERR1). unfold A_ERRNO, A_TP in ERR1.
assert (HPX2 : heap_presx A4H xlocA L0 (bv_unsigned sp) m m1').
{ eapply heap_presx_trans; [exact HPX1|]. eapply heap_presx_weaken; [apply heap_pres_presx; exact HPR1 | lia | intros b Hb; exact Hb | intros a Xa; exact Xa]. }
pose proof (lh_globA_client _ _ _ _ HPR1 G1) as G2.
clear HPX1 G1.
assert (INW : In (Fw, 0) ((Fw, 0) :: FRS)) by (left; reflexivity).
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP1 INW) as (_ & HWal & HW0 & HWc & HWimg & _ & HWshw & _).
change (fr_size 0) with 64 in HWal, HWc, HWimg. change (fr_shadow_len 0) with 8 in HWshw. cbn [hl_img_lo hl_img_hi hla_base hl_sb A4L A4H] in HWimg.
destruct (wfr_fresh Fw LBc LBc LM FRS B A1 m1' md1 HP1 (incl_refl _)) as [OFF OFS]. fold L0 in OFF, OFS.
assert (SUBb : forall b, In b L0 -> In b (LBc ++ LM) \/ In b (fr_ivs A4L ((Fw, 0) :: FRS))).
{ intros b Hb. destruct (SUBa b Hb) as [H | H]; [left; exact H | right; cbn [fr_ivs flat_map app]; right; right; exact H]. }
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR1) in FR; [| left; cbn; lia].
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR1) in LOC1; [| right; left; cbn; intros z Hz; cbn [hl_client_static A4H]; unfold a4_client_static in *; lia].
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR1) in LCK1; [| right; left; cbn; intros z Hz; cbn [hl_client_static A4H]; unfold a4_client_static; lia].
assert (UTF2 : bytes_at asegs m1' UTF8REP_ADDR_A Qa8x.Mq3.utf8rep).
{ eapply (heap_pres_bytes_at A4H); [exact HPR1 | exact UTF1 |]. right; left. intros z Hz. unfold UTF8REP_ADDR_A in Hz. cbn in Hz. cbn [hl_client_static A4H]. unfold a4_client_static. lia. }
assert (INFI : In (Fr, fr_size kf - 8) L0) by (unfold L0; apply in_or_app; right; apply in_or_app; right; apply fr_ivs_frame; exact INF).
assert (STR2 : bytes_at asegs m1' sb (str0 ++ Z_to_bv 8 0 :: slack)).
{ eapply (heap_pres_bytes_at A4H); [exact HPR1 | exact STR1 |]. eapply client_range_block; [exact INFI | exact HF1 |]. rewrite length_app. cbn [length]. lia. }
assert (UNP2 : unpoisoned asegs m1' A_SB sb (Z.of_nat (length str0) + 1)).
{ eapply (unpoisoned_pres_frame HIx A LBc LM FRS B m md LBc _ _ m1' Fr kf); [exact HP | exact INF | exact HF1 | lia | exact UNP1 | exact HPR1]. }
clear SB1 SB2 SB3 UARC STR1 UTF1 UNP1.
pose proof (RTC_TPPC _ _ _ _ _ _ _ HP1) as TPPC. apply ro_C8_of_bytes_at in TPPC. unfold A_GOT_TPPC, json_tokener_parse_B_entry in TPPC.
assert (FSH1 : rw_cells asegs m1' (shad A4L Fw) [CB 8 (repeat (Z_to_bv 8 0) 8)]).
{ split; [split; [cbn; split; [reflexivity | exact I] | cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact SHB1] | exact HWshw]. }
change (Z.to_nat (fr_size 0 - 8)) with 56%nat in FF1.
unfold shad in FSH1. a4l.
set (shw := Fw / 8 + 2147450880) in *.
assert (SHWR : 2147450880 <= shw /\ shw + 8 <= 17594333495296) by (unfold shw; clear - HW0 HWc ACR; Z.div_mod_to_equations; lia).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP1) as MI1. change (hl_segs A4L) with asegs in MI1. clear MI.
clear MU WM. pose proof (wmono_refl asegs m1') as WM. pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (Fw, Fw + 56); (shw, shw + 8)] m1') as MU.
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP1 INW) as HWapp. change (fr_size 0) with 64 in HWapp. cbn [hl_sb A4L] in HWapp. unfold A_SB in HWapp.
stash STR2. stash UNP2. stash UTF2. stash LOC1. stash LCK1. stash ERR1.
reenterA asegs A4L HIx asegs_wx HP1.
step. step. step. step. if_truex.
step.
step. step. step. step. step. step.
rewrite (unsigned_lit Fw) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. fold shw.
step. step. step. step.
stepz. stepz. stepz.
step. stepz. stepz. stepz. stepz.
step. stepz. stepz. stepz. stepz.
step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => assert (HPX3 : heap_presx A4H xlocA L0 (bv_unsigned sp) m mc) end.
{ eapply heap_presx_trans; [exact HPX2 | eapply (presx_private HIx _ _ _ _ _ _ _ _ _ L0 (bv_unsigned sp) HP1 MU WM SUBb ltac:(lia))].
apply Forall_cons; [left; cbn [fst snd]; lia |].
apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]; right; right; left; exists Fw, 0; (split; [exact INW|]); change (fr_size 0 - 8) with 56; change (fr_shadow_len 0) with 8; change (fr_size 0) with 64;
(split; [exact OFF|]); (split; [unfold shad; cbn [hl_sb A4L]; unfold A_SB; exact OFS|]); cbn [fst snd]; unfold shad; cbn [hl_sb A4L]; unfold A_SB; lia. }
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => assert (G3 : lh_globA mc) by (eapply lhg_outside; [exact G2 | exact MU | exact WM | repeat (apply Forall_cons; [cbn [fst snd hl_img_lo hl_img_hi hla_base A4L A4H]; lia | ]); apply Forall_nil]) end.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => assert (HPc : HEAPAx A1 LBc LM ((Fw, 0) :: FRS) B mc md1) by (heap_nowW HP1 MU WM MI1 INW) end.
assert (NEw : Fr <> Fw).
{ intros ->. pose proof (proj1 (stdpp.base.NoDup_ListNoDup _) (heapA_frame_nodup A4L HIx _ _ _ _ _ _ _ HP1)) as ND. cbn in ND. apply List.NoDup_cons_iff in ND as [Hni _]. apply Hni. cbn [fr_base fst]. exact (in_map fr_base _ _ INF). }
pose proof (heapA_frame_apart A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP1 INW ltac:(right; exact INF) ltac:(intros E; apply NEw; symmetry; exact E)) as APART. change (fr_size 0) with 64 in APART.
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP1 ltac:(right; exact INF)) as (_ & _ & _ & HFhi & _).
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP1 ltac:(right; exact INF)) as HFapp. cbn [hl_sb A4L] in HFapp. unfold A_SB in HFapp.
assert (HF8 : Fr mod 8 = 0) by (pose proof (fr_size_shadow kf ltac:(lia)) as X1; pose proof (fr_shadow_len_bnd kf ltac:(lia)) as X2; clear - HFal X1 X2; Z.div_mod_to_equations; nia).
assert (FRC : (Fr + fr_size kf) / 8 <= 140737479966720 / 8) by (apply Z.div_le_mono; clear - HFhi ACR; unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia).
change (140737479966720 / 8) with 17592184995840 in FRC.
unstash STR2. unstash UNP2. unstash UTF2. unstash LOC1. unstash LCK1. unstash ERR1.
eapply rw_cells_transport in ERR1; [| exact MU | exact WM | cbn [disjoint_from cells_size csize Nat.add]; unfold shw; unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia].
eapply rw_cells_transport in LOC1; [| exact MU | exact WM | cbn [disjoint_from cells_size csize Nat.add]; unfold shw; unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia].
eapply rw_cells_transport in LCK1; [| exact MU | exact WM | cbn [disjoint_from cells_size csize Nat.add]; unfold shw; unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia].
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (UTFc : bytes_at asegs mc UTF8REP_ADDR_A Qa8x.Mq3.utf8rep)
by (eapply bytes_at_transport; [exact UTF2 | exact MU |]; unfold UTF8REP_ADDR_A, shw; cbn [disjoint_from length Qa8x.Mq3.utf8rep]; unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia) end.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => assert (STRc : bytes_at asegs mc sb (str0 ++ Z_to_bv 8 0 :: slack)) end.
{ eapply bytes_at_transport; [exact STR2 | exact MU |]. rewrite length_app. cbn [length disjoint_from]. unfold alloc_ceiling, sp_window_lo, stack_max_size in *.
split; [lia | split; [lia | split; [| exact I]]].

unfold shw. destruct HFapp as [X | X]; [left; lia | right].
assert ((Fw + 64) / 8 <= 17592184995840) by (assert ((Fw + 64) / 8 <= 140737479966720 / 8) by (apply Z.div_le_mono; lia); change (140737479966720 / 8) with 17592184995840 in H; exact H).
change ((2 ^ 47 - 1) / 8) with 17592186044415 in X. Z.div_mod_to_equations. lia. }
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => assert (UNPc : unpoisoned asegs mc A_SB sb (Z.of_nat (length str0) + 1)) end.
{ eapply (unpoisoned_transport asegs); [exact UNP2 | exact MU |]. intros a k Ha Hk. cbn [disjoint_from]. unfold A_SB, shadow_span_lo, shadow_span_hi, alloc_ceiling, sp_window_lo, stack_max_size in *.
assert (S1 : (sb + (Z.of_nat (length str0) + 1) - 1) / 8 <= 17592184995840) by (assert ((sb + (Z.of_nat (length str0) + 1) - 1) / 8 <= 140737479966720 / 8) by (apply Z.div_le_mono; lia); change (140737479966720 / 8) with 17592184995840 in H; exact H).
assert (S0 : 0 <= sb / 8) by (apply Z.div_pos; lia).
split; [lia | split; [| split; [| exact I]]].
-  unfold shw in *. change ((2 ^ 47 - 1) / 8) with 17592186044415 in HWapp. destruct HWapp as [X|X]; [right; lia | left; lia].
-  unfold shw.
destruct APART as [X|X].
+ right. clear - X HWal HF1 Ha S0. Z.div_mod_to_equations. lia.
+ left. clear - X HF2 Hk HWal HF1 Ha. Z.div_mod_to_equations. lia. }
clear HPX2 G2.
evt_done5. unstash CSTR.
eapply tokparse_verbose_B with (md := md1) (T := T) (A := A1) (LBc := LBc) (LM := LM) (FRS := FRS) (B := B) (sb := sb) (lo := lo) (Fw := Fw) (str0 := str0) (slack := slack) (errv := errv1).
1: { split; [exact HPc|]. split; [rewrite unsigned_lit by lia; eassumption|]. split; [exact LO|]. split; [rewrite unsigned_lit by lia; lia|].
split; [rewrite unsigned_lit by lia; clear - SP32 SPR; Z.div_mod_to_equations; lia|]. split; [rewrite unsigned_lit by lia; lia|].
split; [unfold A_ERRNO, A_TP; exact ERR1|]. split; [reflexivity | rewrite unsigned_lit by lia; reflexivity]. }
1: (rewrite unsigned_lit by lia; clear - SP32 SPR; Z.div_mod_to_equations; lia).
1: exact LMN.
1: (destruct CSTR as (_ & NONUL' & PAD' & ALOC' & _); split; [exact STRc | split; [exact NONUL' | split; [exact PAD' | split; [exact ALOC' | exact UNPc]]]]).
1: exact LEN.
1: (unfold LOCCELL_A, A_TP; exact LOC1).
1: (unfold LOCALE_LOCK_A; exact LCK1).
1: exact G3.
1: exact UTFc.
1: (unfold wfr_cells; eassumption).
1: (unfold wsh_cells, A_SB; fold shw; eassumption).
1: exact FRN.
1: exact BB.
1: exact BD.
1: exact FRM.
1: reflexivity.
1: reflexivity.
intros ms2 md2 mV A2 B2 gp2 r errv2 RBS LK e j1 j2 RS2 VM2 ST2 ERR2 LOC2 LCK2 Gv2 UTFv2 HPX4 WFR2 WSH2 CH2 HP2 RES2.
destruct RS2 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F2 & fc2 & -> & FS2 & FRM2).
rewrite ?unsigned_lit in ST2, HPX4 by lia.
lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?n)] => replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia | reflexivity]) end.
unfold wfr_cells2 in WFR2. unfold wsh_cells, A_SB in WSH2. fold shw in WSH2. unfold LOCCELL_A, LOCALE_LOCK_A, A_ERRNO, A_TP in LOC2, LCK2, ERR2.

eapply (heap_presx_rw_cells A4H) in FR; [| exact HPX4 | left; cbn; lia].
assert (HPX5 : heap_presx A4H xlocA L0 (bv_unsigned sp) m mV).
{ eapply heap_presx_trans; [exact HPX3|]. eapply heap_presx_weaken; [exact HPX4 | lia | intros b Hb; exact Hb | intros a Xa; exact Xa]. }
clear HPX3 G3 HPc STRc UNPc MU WM MI1.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI2. a4l.
pose proof (wmono_refl asegs mV) as WM. pose proof (munch_refl [(shw, shw + 8); (Fw, Fw + 8)] mV) as MU.
stash UTFv2.
reenterA asegs A4L HIx asegs_wx HP2.
step. stepz.
step. step. stepz.
step. if_falsex.
step. do 8 stepz.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => lazymatch goal with MUc : munch _ mV mc, WMc : wmono asegs mV mc, MIc : mem_inv asegs mc |- _ =>
assert (HPc2 : HEAPAx A2 (RBS ++ LK ++ LBc) LM ((Fw, 0) :: FRS) B2 mc md2) by (heap_nowW HP2 MUc WMc MIc INW) end end.
destruct (wfr_fresh Fw (RBS ++ LK ++ LBc) LBc LM FRS B2 A2 mV md2 HP2 ltac:(intros b Hb; apply in_or_app; right; apply in_or_app; right; exact Hb)) as [OFF2 OFS2]. fold L0 in OFF2, OFS2.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => lazymatch goal with MUc : munch _ mV mc, WMc : wmono asegs mV mc |- _ =>
assert (HPX6 : heap_presx A4H xlocA L0 (bv_unsigned sp) m mc);
[ eapply heap_presx_trans; [exact HPX5|]; eapply (presx_private HIx _ _ _ _ _ _ _ _ _ L0 (bv_unsigned sp) HP2 MUc WMc); [| lia |];
[ intros b Hb; destruct (SUBb b Hb) as [H | H]; [left; apply in_app_or in H as [H|H]; apply in_or_app; [left; apply in_or_app; right; apply in_or_app; right; exact H | right; exact H] | right; exact H]
| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]; right; right; left; exists Fw, 0; (split; [exact INW|]); change (fr_size 0 - 8) with 56; change (fr_shadow_len 0) with 8; change (fr_size 0) with 64;
(split; [exact OFF2|]); (split; [unfold shad; cbn [hl_sb A4L]; unfold A_SB; exact OFS2|]); cbn [fst snd]; unfold shad; cbn [hl_sb A4L]; unfold A_SB; lia ]
| assert (G6 : lh_globA mc) by (eapply lhg_outside; [exact Gv2 | exact MUc | exact WMc | repeat (apply Forall_cons; [cbn [fst snd hl_img_lo hl_img_hi hla_base A4L A4H]; lia | ]); apply Forall_nil]) ] end end.
destruct (OBL_FP_PRIVATE HIx _ _ _ _ _ _ _ _ _ HPc2 INW) as (fp & FPB & FPR & FPnc & FPimg & FPns & FPfr).
change (fr_size 0) with 64 in FPB. replace (Fw + 64 - 8) with (Fw + 56) in FPB by lia.
pose proof (ro_C8_of_bytes_at asegs _ _ _ FPB) as FPC.
step.
evt_done5.
eapply (hiA_frame_release A4L HIx) with (Fr := Fw) (k := 0) (fp := fp) (rX := Z_to_bv 5 11);
[exact HPc2 | exact INW | change (fr_size 0) with 64; replace (Fw + 64 - 8) with (Fw + 56) by lia; exact FPB | lia | reflexivity | vm_compute; discriminate | | ].
1: vm_compute; split; reflexivity.
intros mR mdR AR VMR HPR3 Hoff Hwv.
cbn [fr_remove fr_base fst Z.eqb] in HPR3. rewrite Z.eqb_refl in HPR3.
lazymatch type of HPc2 with HEAPA _ _ _ _ _ _ _ ?mc _ =>
assert (MUr : munch [(fp, fp + 1)] mc mR);
[ intros x Hx; cbn [outside] in Hx; pose proof (bv_unsigned_in_range 64 x) as XR; unfold bv_modulus in XR; cbn in XR;
rewrite <- (Z_to_bv_bv_unsigned x); change (Z_to_bv 64 (bv_unsigned x)) with (wa (bv_unsigned x)); apply Hoff; lia
| assert (WMr : wmono asegs mc mR) by exact Hwv ];
assert (MIR : mem_inv asegs mR);
[ intros y b Hb; destruct (Z.eq_dec (bv_unsigned y) fp) as [Ey | Ny];
[ destruct (ro_addr asegs y) eqn:RO; [| reflexivity]; exfalso; apply QXUB.ro_addr_asegs in RO; cbn [hl_img_lo hl_img_hi A4H hla_base A4L] in FPimg; lia
| lazymatch goal with MIc : mem_inv asegs mc |- _ => apply (MIc y b) end; rewrite <- Hb; symmetry; rewrite <- (Z_to_bv_bv_unsigned y); change (Z_to_bv 64 (bv_unsigned y)) with (wa (bv_unsigned y)); apply Hoff; [| exact Ny];
pose proof (bv_unsigned_in_range 64 y) as YR; unfold bv_modulus in YR; cbn in YR; lia ]
| ]
end.
apply (rw_cells_transport asegs [(fp, fp + 1)] _ mR) in FR; [| exact MUr | exact WMr | cbn [disjoint_from]; simpl_sizes; unfold client_addr in FPnc; lia].
lazymatch goal with ST' : stk asegs _ lo _ |- _ => apply (stk_transport_disjoint asegs [(fp, fp + 1)] _ mR) in ST'; [| exact MUr | exact WMr | cbn [disjoint_from]; unfold client_addr in FPnc; lia] end.
change (604084 + 4) with 604088.
clear FPC.
reenterA asegs A4L HIx asegs_wx HPR3.
step. step.
do 6 step.
step. step.
evt_done5. unstash K.
lazymatch goal with ST' : stk asegs mR lo _ |- _ => release_frame FR ST' (bv_unsigned sp) end.

lazymatch type of HPc2 with HEAPA _ _ _ _ _ _ _ ?mc _ => lazymatch goal with MUc : munch _ mV mc, WMc : wmono asegs mV mc |- _ =>
assert (MU23 : munch [(shw, shw + 8); (Fw, Fw + 8); (fp, fp + 1)] mV mR)
by (eapply munch_trans; [eapply munch_weaken; [| exact MUc] | eapply munch_weaken; [| exact MUr]]; intros z Hz; cbn [outside] in Hz |- *; tauto);
assert (WM23 : wmono asegs mV mR) by (intros z Hz; apply WMr; apply WMc; exact Hz)
end end.
assert (DJ : forall a n, In (a, n) ((RBS ++ LK ++ LBc) ++ LM) -> disjoint_from [(shw, shw + 8); (Fw, Fw + 8); (fp, fp + 1)] a n).
{ intros a n Hin. pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ a n HP2 Hin) as (Hn & _ & _ & Hhi & _). cbn [disjoint_from]. split; [| split; [| split; [| exact I]]].
- pose proof (shadow_blk_apart HIx _ _ _ _ _ _ _ _ _ Fw 8 HP2 Hin ltac:(lia) ltac:(lia) ltac:(lia)) as X. unfold shw, shA, A_SB in *. lia.
- pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP2 INW Hin) as X. change (fr_size 0) with 64 in X. lia.
- destruct (Z_le_gt_dec (fp + 1) a); [lia|]. destruct (Z_le_gt_dec (a + n) fp); [lia|]. exfalso. apply FPnc. right; right. exists (a, n). split; [exact Hin | cbn [blk_addr blk_size fst snd]; lia]. }
assert (AG : agree_on asegs ((RBS ++ LK ++ LBc) ++ LM) mV mR).
{ eapply (agree_of_munch asegs); [exact MU23 | exact WM23 |]. intros a n Hin. exact (DJ a n Hin). }
eapply (K _ _ mR AR B2 _ r errv2 RBS LK).
- apply ret_statew_intro; [exact FS2 | exact FRM2].
- eapply model_vm_only_trans; [exact VM1|]. eapply model_vm_only_trans; [exact VM2 | exact VMR].
- assumption.
- eapply rw_cells_transport; [exact ERR2 | exact MUr | exact WMr |]. cbn [disjoint_from cells_size csize Nat.add]. simpl_sizes.
assert (~ (6444320 - 164 <= fp < 6444320 - 160)) by (intros X; apply FPns; cbn [hl_scratch A4H]; unfold A_TP; lia). lia.
- eapply rw_cells_transport; [exact LOC2 | exact MUr | exact WMr |]. cbn [disjoint_from cells_size csize Nat.add]. simpl_sizes.
assert (~ (6444320 - 48 <= fp < 6444320 - 40)) by (intros X; apply FPnc; right; left; cbn [hl_client_static A4H]; unfold a4_client_static; lia). lia.
- eapply rw_cells_transport; [exact LCK2 | exact MUr | exact WMr |]. cbn [disjoint_from cells_size csize Nat.add]. simpl_sizes.
assert (~ (6576272 <= fp < 6576276)) by (intros X; apply FPnc; right; left; cbn [hl_client_static A4H]; unfold a4_client_static; lia). lia.
- eapply lhg_outside; [exact G6 | exact MUr | exact WMr |]. apply Forall_cons; [| apply Forall_nil]. cbn [fst snd hl_img_lo hl_img_hi hla_base A4L A4H] in FPimg |- *. lia.
- unstash UTFv2. eapply bytes_at_transport; [exact UTFv2 | exact MU23 |]. unfold UTF8REP_ADDR_A, shw. cbn [disjoint_from length Qa8x.Mq3.utf8rep]. cbn [hl_img_lo hl_img_hi A4H hla_base A4L] in FPimg. lia.
- eapply heap_presx_trans; [exact HPX6|]. eapply (heap_presx_of_munch A4H); [exact MUr | exact WMr |].
intros a Ha Hc. cbn [outside]. split; [| exact I].
intros Hfp. assert (a = fp) by lia. subst a. destruct Hc as [Hc | [Hc | (b & Hb & Hbr)]].
+ apply FPnc. left. lia.
+ apply FPnc. right; left. exact Hc.
+ unfold L0 in Hb. apply in_app_or in Hb as [Hb | Hb]; [apply FPnc; right; right; exists b; split; [apply in_or_app; left; apply in_or_app; right; apply in_or_app; right; exact Hb | exact Hbr]|].
apply in_app_or in Hb as [Hb | Hb]; [apply FPnc; right; right; exists b; split; [apply in_or_app; right; exact Hb | exact Hbr]|].
apply in_fr_ivs in Hb as (Gf & kg & HG & [E | E]); subst b; cbn [blk_addr blk_size fst snd] in Hbr; destruct (FPfr Gf kg ltac:(right; exact HG)) as [N1 N2].
* apply N1. lia.
* apply N2. exact Hbr.
- exact CH2.
- exact HPR3.
- destruct RES2 as [R0 | (Rn & s & J & SD)]; [left; exact R0 | right]. split; [exact Rn|]. exists s. split; [| exact SD].
eapply (jval_agree asegs A4F); [exact J | exact AG |]. intros b Hb. apply in_or_app; left. apply in_or_app; left. exact Hb.
Qed.

Theorem json_tokener_parse_B_cps : jo_tokparse_A_stmt HIx json_tokener_parse_B_entry (96 + 80 + 432 + 12288 + 4096) 0x932fc tokparse_costB tokparse_costD.
Proof.
unfold jo_tokparse_A_stmt. intros until u. intros PRE SP32 LMN CSTR LEN (LOC & LCK & G & UTF) UW UWK FRN BB BD FRM A0 K.
eapply (json_tokener_parse_B_main ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m md T A LBc LM FRS B sb lo str0 slack errv);
[exact PRE | exact SP32 | exact LMN | exact CSTR | exact LEN | exact LOC | exact LCK | exact G | exact UTF | exact FRN | exact BB | pose proof (uw_cost_nonneg5 u); lia | exact FRM | exact A0 |].
intros ms' md' m' A' B' gp' r errv' RBS LK RS VM ST ERR LOC' LCK' G' UTF' PX CH HP RES.
eapply (K ms' md' m' A' B' gp' r errv' RBS LK); [exact RS | exact VM | exact ST | exact ERR | split; [exact LOC' | split; [exact LCK' | split; [exact G' | exact UTF']]] | exact PX | | exact HP | exact RES].
destruct CH as [CB CD]. split; [exact CB | pose proof (uw_cost_nonneg5 u); lia].
Qed.
End ATokParseB.

Lemma tokparse_cost_le : forall n, 0 <= n <= 20 -> 0 <= tokparse_costB n <= 322639 /\ 0 <= tokparse_costD n <= 257425 + 2^27.
Proof.
intros n Hn. unfold tokparse_costB, tokparse_costD, pe_A0, pe_N0, toknew_costB, QJZd.Mqe.pbnew_costB, PhiPB, K_free, K_exit, M2D.
assert (H : (16 * Z.max 0 (n + 1) + 11008) * (n + 1) <= (16 * 21 + 11008) * 21) by nia.
split; lia.
Qed.

End RC__1.
