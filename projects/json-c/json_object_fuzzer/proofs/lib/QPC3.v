(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEQM.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDH.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QC8c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QC8c.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw.Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QtMn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QtMn.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QkMG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkMG.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QG8z.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QG8z. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qdyh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qdyh.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2Sr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2Sr. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLbz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLbz. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QIsM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QIsM.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXfU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXfU.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qa8x.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qa8x.Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBpZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBpZ. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QT7i.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QT7i. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qv6q.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qv6q.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QgoP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QgoP.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QzWc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QzWc.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4Eu.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4Eu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc8V.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc8V.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfOM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfOM.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy2A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy2A. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdFq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdFq. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QvXs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QvXs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QX85.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QX85. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QX85.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QX85.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYrb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYrb.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QubI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QubI. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYrb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYrb. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbRq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbRq. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmOT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmOT. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QX85.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QX85.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QxRV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QxRV.
Import ListNotations. Unset Keyed Unification. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section PeNumber.
Variable HIx : heap_iface S4L.
Variables (pf : pe_fix) (q : Z) (LBc : list blk) (payload : list byte) (me : word -> option byte) (lo : Z)
(sv : pe_saved) (T : TSet) (F0 : bvmap 5 word) (utf8rep : list byte).
Hypothesis MEMMOVE : memmove_stmt.
Hypothesis STRTOLL : strtox_stmt strtoll_entry.
Hypothesis STRTOULL : strtox_stmt strtoull_entry.
Hypothesis STRTOD : rstrtod_stmt.
Hypothesis STRDUP : strdup_stmt HIx.

#[using="MEMMOVE STRTOLL STRTOULL STRTOD STRDUP"] Lemma case_number : CASE HIx pf q LBc payload me lo sv T F0 utf8rep ST_number.
Proof.
unfold CASE. intros until fc. intros STC INV Hl Hst Hco Hcb NUMC0 SPOK0 TDOK UTF GOTU CSTR FS FRM Hn KALL KOUT KERR.
assert (PBC : pbufc rsegs m (t_pbs ts) (t_pb ts) []) by (apply NUMC0; unfold cur_st; rewrite Hl; exact Hst).
assert (Hn0 : (16 * Z.to_nat (pf_len pf - t_co ts) + 8 <= n)%nat).
{ revert Hn. unfold mredo, mbase, cur_st, cur_ss. rewrite Hl, Hst. change (rank ST_number (tl_ss l)) with 8%nat. intros Hn. exact Hn. }
clear NUMC0 SPOK0 UTF Hn.
pose proof STC as (LO & LOS & SPA & HT & SP0 & LEN & SB0 & SBL).
pose proof INV as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof REST as (HP & _).
destruct ts as [depth levels co pb pbs xx obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct xx as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl_]; pe_gen fl_; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
unfold tok_cells, tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in TOK. unfold pe_frame in FR. unfold pe_ms7, pe_ms in *. cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
unfold_consts.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q (LB0 (PEF tk oldl newl len lenr sb spf pmd mxd fl) LBc) ts0)) by (unfold pe_blocks; apply in_or_app; right; left; reflexivity).
pose proof (heap_blk S4L HIx _ _ _ _ tk 72 HP INtk) as (_ & Htal & Htlo & Hthi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hthi.
pose proof PBC as (buf & bpos & cap & post & Epbs & Lpre & PCORE). cbn [length Z.of_nat pf_mxd] in Lpre. subst bpos. pose proof PCORE as (_ & Hcap & _ & PBS & _). cbn [hl_segs S4L pf_mxd] in PBS.
assert (INpb : In (pb, 16) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q (LB0 (PEF tk oldl newl len lenr sb spf pmd mxd fl) LBc) ts0)) by (unfold pe_blocks, tstate_blocks, ts0; cbn [t_pbs pf_mxd]; rewrite Epbs; apply in_or_app; left; apply in_or_app; left; left; reflexivity).
pose proof (heap_blk S4L HIx _ _ _ _ pb 16 HP INpb) as (_ & Hpbal & Hpblo & Hpbhi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hpbhi.
pose proof (bv_unsigned_in_range 8 cb) as CBR. unfold bv_modulus in CBR. cbn in CBR.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
stash PB. stash TSK. stash REST. clear PCORE.
apply rz_evt; [exact MOK|]. rewrite Hst. unfold ST_number. cbn [pe_jt pf_mxd].
step. step. norm_sx32. step. step. if_true.
step. step. step. change (zxb cb) with (Z_to_bv 64 (bv_unsigned cb)). step.
destruct (Z.eq_dec (bv_unsigned cb) 0) as [C0 | Cn].
-
if_falsex. step. step.
unstash PB. unstash TSK. unstash REST.
apply evt_RZ_done. replace (Z_to_bv 64 0) with (Z_to_bv 64 (co - co)) by (f_equal; lia).
eapply (num_charchk HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LBc payload me lo sv T F0 MEMMOVE STRTOLL STRTOULL STRTOD STRDUP n ts0 l co);
[exact STC | exact INV | exact Hl | exact Hst | exact PBC | red_ts; lia | rewrite Z.sub_diag; cbn; constructor | exact GOTU | exact Hco | exact Hcb | tdok TDOK | exact FS | exact FRM
| red_ts; lia | exact KALL | exact KOUT | exact KERR].
- if_truex. step. step. norm_sx32. step. step.
unstash PB. unstash TSK. unstash REST.
apply evt_RZ_done.
lazymatch goal with |- realizes _ (mkCfg (MS _ ?F' _ ?fc' _ ?m' _) ?md') _ =>
pose proof (num_loop HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LBc payload me lo sv T F0 MEMMOVE STRTOLL STRTOULL STRTOD STRDUP CSTR
(Z.to_nat (len - co)) n ts0 l co 0 0 1 m' md' A cb j1 j2 utf errv x1 gp t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 F' fc') as NL end.
replace (Z_to_bv 64 (t_co ts0 - co)) with (Z_to_bv 64 0) in NL by (unfold ts0; cbn [t_co pf_mxd]; f_equal; lia).
apply NL; [red_ts; lia | exact STC | exact INV | exact Hl | exact Hst | exact PBC | red_ts; lia | rewrite Z.sub_diag; cbn; constructor | exact GOTU | exact Hco | exact Hcb | exact Cn
| left; reflexivity | left; reflexivity | right; reflexivity | tdok TDOK | exact FS | exact FRM | exact Hn0 | exact KALL | exact KOUT | exact KERR].
Qed.
End PeNumber.

End RC__1.
