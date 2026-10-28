(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QWxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qtgi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qtgi. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QjDH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDH. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QjDH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDH.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UC8c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UC8c.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw.Mq2.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UtMn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UtMn.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QkMG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkMG.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UG8z.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UG8z. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Udyh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Udyh.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U2Sr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U2Sr. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require ULbz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import ULbz. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UIsM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UIsM.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UXfU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UXfU.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Ua8x.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ua8x.Mq3.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UBpZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UBpZ. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UT7i.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UT7i. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uv6q.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uv6q.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QgoP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QgoP.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UzWc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UzWc.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U4Eu.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U4Eu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uc8V.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uc8V.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UfOM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UfOM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uy2A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uy2A. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UdFq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UdFq. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UvXs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UvXs. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UX85.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UX85. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UX85.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UX85.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UYrb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UYrb.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UubI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UubI. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UYrb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UYrb. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UbRq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UbRq. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UmOT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UmOT. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UX85.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UX85.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UxRV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UxRV.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB.Tk3 Require Tk3Tac.
Import ListNotations. Unset Keyed Unification. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
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
step. step. if_truex. step. step. Tk3Tac.align_true. step. norm_sx32. step. step. if_true.
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
(Z.to_nat (len - co)) n ts0 l co 0 0 1 m' md' A cb j1 j2 utf errv x1 gp t0 t1 t2 a6 a7 s7 t3 t4 t5 t6 F' fc' (sx32 (nbw j2))) as NL end.
replace (Z_to_bv 64 (t_co ts0 - co)) with (Z_to_bv 64 0) in NL by (unfold ts0; cbn [t_co pf_mxd]; f_equal; lia).
apply NL; [red_ts; lia | exact STC | exact INV | exact Hl | exact Hst | exact PBC | red_ts; lia | rewrite Z.sub_diag; cbn; constructor | exact GOTU | exact Hco | exact Hcb | exact Cn
| left; reflexivity | left; reflexivity | right; reflexivity | tdok TDOK | exact FS | exact FRM | exact Hn0 | exact KALL | exact KOUT | exact KERR].
Qed.
End PeNumber.

End RC__1.
