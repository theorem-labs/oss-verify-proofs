(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup Lib.GwApply QWxq_c1 QRjH QHnV QCcH QfLs Q0Ek Qtgi QjDH Qsw7 QJjn QRUw QkMG QG8z Qdyh Q7UD Qhd4 Qwm6 QlKV QsKa Qiiq Q4v2 Q1Ey Ql4f Q1Y6 QrQv QEUF QW22 QdGy QnDr Qpfz Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QJjn QRUw.Mq0 QRUw QkMG. Import QG8z Qdyh.Mq0 Qdyh.Mq3 Qdyh.Mq4.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa QsKa.Mq4 Qiiq.Mq0 QsKa.Mq6 Q4v2.Mq0 Q1Ey Ql4f.Mq1 Q1Y6.Mq2 QsKa.Mq8 QrQv.Mq2 QEUF QW22.Mq3 QdGy.Mq2.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import QlKV.Mq2 QnDr.Mq3 Qpfz.Mq0.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section PeSAaddA.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_outside : forall m m' W, GA m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= hl_img_lo A4H \/ hl_img_hi A4H <= fst iv) W -> GA m'.
Hypothesis GA_pres : forall LB SP m m', heap_pres A4H LB SP m m' -> GA m -> GA m'.
Hypothesis MAPP : memappend_A_stmt2 HIx.
Hypothesis AADD : jo_array_add_A2J HIx.

Ltac pe_openA STC INV :=
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR); pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk);
destruct INV as [CORE REST];
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR);
pose proof REST as (HP & LV & OBJ & ST & ERR & STR & PLEN & SBin & HPR & MDV & G & BUD).

Lemma seg_aadd_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel) (kids : list (option jshape))
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP : Z) (nB : nat)
(gp t0 t1 t2 a3 a5 a6 a7 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv -> PBOK m ts kP -> BOK pf pa ts B (S (Z.to_nat 1280 + nB)) ->
pj_obj pj = Z_to_bv 64 (t_obj ts) ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_array_add ->
tl_cs l = Some (Sarr kids) ->

(forall m' md' A' B' cbs' errv' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' F' fc',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B'
(ts_lvl_obj ts (TL ST_eatws ST_array_sep (tl_cur l) (Some (Sarr (kids ++ [t_objs ts]))) cbs' (tl_name l) (tl_nbs l)) (t_obj ts) (t_objs ts) []) cb nb pj sv errv' ->
PBOK m' (ts_lvl_obj ts (TL ST_eatws ST_array_sep (tl_cur l) (Some (Sarr (kids ++ [t_objs ts]))) cbs' (tl_name l) (tl_nbs l)) (t_obj ts) (t_objs ts) []) kP ->
BOK pf pa (ts_lvl_obj ts (TL ST_eatws ST_array_sep (tl_cur l) (Some (Sarr (kids ++ [t_objs ts]))) cbs' (tl_name l) (tl_nbs l)) (t_obj ts) (t_objs ts) []) B' nB ->
(forall w wv, jtx (Sarr kids) (tl_cbs l) = Some (w, []) -> jtx_opt (t_objs ts) (t_objbs ts) = Some (wv, []) -> jtx (Sarr (kids ++ [t_objs ts])) cbs' = Some (w + (2 + wv), [])) ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msA asegs pf pa APE_REDO (t_co ts) gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5'
(Z_to_bv 64 (pf_tk pf + 56)) (Z_to_bv 64 (pa_F pa + 64)) F' fc' m')) ->

(forall m' md' A' B' errv' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' s11' t4' t6' F' fc',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' ts cb nb pj sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msO asegs pf pa APE_ERRMEM x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' (Z_to_bv 64 (pf_tk pf + 56)) s11' t4' t6' F' fc' m')) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa (pe_jtA ST_array_add) (t_co ts) gp t0 t1 t2
(Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) (Z_to_bv 64 (tl_st l))
(Z_to_bv 64 (q / 8 + 4 * Z.of_nat (t_depth ts) + A_SB)) a3 (Z_to_bv 64 APE_JTAB) a5 a6 a7
(Z_to_bv 64 (Z.of_nat (t_depth ts))) (Z_to_bv 64 q) (Z_to_bv 64 (pa_F pa + 64)) F fc m).
Proof.
intros until fc. intros STC BSL INV PBK BK OBJW Hl Hst Hcs Kredo Kerr16. pose proof INV as INV0. pe_openA STC INV.
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
pose proof FR as FR0. unfold pe_frameA in FR. destruct FR as (SLOTS & GAP & SAVED & FF & FSH).
unfold pe_slotsA in SLOTS. cbn zeta in SLOTS. unfold ff_cellsA in FF.
unfold pe_msA, pe_msO in *.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * mxd) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t.
blk_factsA A4L HIx HP q (32 * mxd) Hqal Hqlo Hqhi Himg_q.
pose proof (q_ne_tkA HIx _ _ _ _ _ _ _ _ _ _ HP) as Hqtk. cbn [pf_tk] in Hqtk.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ tk 72 q (32 * mxd) HP (in_or_app _ LM _ (or_introl INtk)) (in_or_app _ LM _ (or_introl INq)) ltac:(congruence)) as Hdtq.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 4 HP INtk ltac:(lia)) as SHT4.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 4 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEP4c & SEP4q & SEP4i). cbn [hl_sb A4L] in SEP4c, SEP4q, SEP4i.
replace (tk / 8 + 4 + A_SB) with (tk / 8 + SB4) in SHT4 by (unfold SB4, A_SB; lia).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs m) as WM.
pose proof (LV depth l Hl) as LVd. pose proof LVd as (ST26 & SS26 & _ & Md).
rewrite Nat.ltb_irrefl, Nat.eqb_refl in Md. destruct Md as (c0 & hn0 & Hmode & CLS0 & NM0).
pose proof (TSK depth l Hl) as Ld. remember (q + 32 * Z.of_nat depth) as bse eqn:Hbse in Ld. unfold srec_cells in Ld.
assert (HbseR : q <= bse /\ bse + 32 <= q + (32 * mxd)) by (subst bse; lia).
pose proof (stack_shadowA HIx _ _ _ _ _ _ _ q mxd (Z.of_nat depth) 0 HP INq ltac:(lia) ltac:(lia)) as SHQ.
replace (q / 8 + 4 * Z.of_nat depth + 0 + A_SB) with (q / 8 + 4 * Z.of_nat depth + A_SB) in SHQ by lia.
assert (Hb8 : bse mod 8 = 0) by (subst bse; clear - Hqal; Z.div_mod_to_equations; lia).
assert (SHQ4 : ro_cells asegs m (bse / 8 + A_SB) [C1 (Z_to_bv 8 0)]).
{ replace (bse / 8) with (q / 8 + 4 * Z.of_nat depth) by (subst bse; rewrite div8_add_mul32 by lia; lia). exact SHQ. }
pose proof (munch_refl [(bse, bse + 32)] m) as MU.
pose proof (bv_unsigned_in_range 8 cb) as CBR; unfold bv_modulus in CBR; cbn in CBR.
unfold APE_REDO, APE_ERRMEM, APE_JTAB in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
assert (MODE0 : c0 = CArr /\ hn0 = false).
{ rewrite Hst, (Qdyh.Mq0.lvl_mode_aadd (tl_ss l)) in Hmode. injection Hmode as <- <-. split; reflexivity. }
destruct MODE0 as (-> & ->). cbn [name_ok] in NM0. destruct NM0 as [Hn0 Hnbs0].
pose proof (stack_shadowA HIx _ _ _ _ _ _ _ q mxd (Z.of_nat depth) 2 HP INq ltac:(lia) ltac:(lia)) as SHQ2.
assert (SHQ16 : ro_cells asegs m (bse / 8 + 2147450882) [C1 (Z_to_bv 8 0)]).
{ replace (bse / 8 + 2147450882) with (q / 8 + 4 * Z.of_nat depth + 2 + A_SB) by (subst bse; rewrite div8_add_mul32 by lia; unfold A_SB; lia). exact SHQ2. }
destruct pj as [pj0 pj8 pj16 pjobj pj288 pj304 pjgap pjfhd pjf1 pjf2]. cbn [pj_0 pj_8 pj_16 pj_obj pj_288 pj_304 pj_gap pj_fhd pj_f1 pj_f2] in *. subst pjobj.
stash Himg_t. stash Himg_q. clear PB REST TSK HP LV OBJ HPR BUD GAP SAVED FSH.
reenterA asegs A4L HIx asegs_wx HP. rewrite Hst. unfold ST_array_add. cbn [pe_jtA].
replace (q + 32 * Z.of_nat depth) with bse by lia.
step.
asan_chkA.
step.
step.
step.
evt_done5. subst bse.
eapply (pe_aadd_cJ HIx GA GA_pres AADD (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m md A B ts0 l kids cb nb _ sv errv T kP nB);
[exact STC | exact BSL | exact INV0 | exact PBK | exact BK | exact Hl | exact Hst | exact Hcs | exact Hnbs0 | rewrite unsigned_lit by lia; reflexivity |].
intros m2 md2 A2 B2 errv2 r w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 F2 fc2 OUT FS2 FRM2.
clear TOK SLOTS FF SHT4 SEP4c SEP4q SEP4i SHQ SHQ4 SHQ2 SHQ16 Ld MU WM MI Htal Htlo Hthi Hqal Hqlo Hqhi Hdtq Hqtk INtk INq HbseR Hb8.
destruct OUT as [(-> & cbs2 & INV2 & PBK2 & BK2 & JX2) | (-> & INV2)].
- set (l2 := TL (tl_st l) (tl_ss l) (tl_cur l) (Some (Sarr (kids ++ [t_objs ts0]))) cbs2 (tl_name l) (tl_nbs l)) in *.
set (TS2 := ts_lvl_obj ts0 l2 0 None []) in *.
assert (Hl2 : nth_error (t_levels TS2) (t_depth TS2) = Some l2) by (unfold TS2, ts_lvl_obj, ts0; cbn [t_levels t_depth]; apply nth_error_lupd_eq; apply nth_error_Some; rewrite Hl; discriminate).
clear INV0 PBK BK.
cbn [pf_spf] in *. unfold A_TP in *.
pose proof INV2 as INV2'. destruct INV2' as [CORE2 REST2].
destruct CORE2 as (_ & _ & _ & _ & TOK & _ & _ & TSK & FR).
pose proof REST2 as (HP & LV & _).
unfold TS2, ts_lvl_obj, ts0 in TOK, TSK, LV. cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_tk pf_mxd pf_fl] in TOK, TSK, LV.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
unfold pe_frameA in FR. destruct FR as (SLOTS & _ & _ & FF & _). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS. unfold ff_cellsA in FF.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in SLOTS, FF.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 TS2)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * mxd) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 TS2)) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t2.
blk_factsA A4L HIx HP q (32 * mxd) Hqal Hqlo Hqhi Himg_q2.
pose proof (q_ne_tkA HIx _ _ _ _ _ _ _ _ _ _ HP) as Hqtk. cbn [pf_tk] in Hqtk.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ tk 72 q (32 * mxd) HP (in_or_app _ LM _ (or_introl INtk)) (in_or_app _ LM _ (or_introl INq)) ltac:(congruence)) as Hdtq.
pose proof (tok_shadowA HIx _ _ _ _ _ _ _ _ HP INtk) as SHT.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs m2) as WM.
pose proof (TSK depth l2 ltac:(apply nth_error_lupd_eq; apply nth_error_Some; rewrite Hl; discriminate)) as Ld. remember (q + 32 * Z.of_nat depth) as bse eqn:Hbse in Ld. unfold srec_cells in Ld. cbn [tl_st tl_ss tl_cur tl_name l2] in Ld.
assert (HbseR : q <= bse /\ bse + 32 <= q + (32 * mxd)) by (subst bse; lia).
pose proof (stack_shadowA HIx _ _ _ _ _ _ _ q mxd (Z.of_nat depth) 0 HP INq ltac:(lia) ltac:(lia)) as SHQ.
replace (q / 8 + 4 * Z.of_nat depth + 0 + A_SB) with (q / 8 + 4 * Z.of_nat depth + A_SB) in SHQ by lia.
assert (Hb8 : bse mod 8 = 0) by (subst bse; clear - Hqal; Z.div_mod_to_equations; lia).
assert (SHQ4 : ro_cells asegs m2 (bse / 8 + A_SB) [C1 (Z_to_bv 8 0)]).
{ replace (bse / 8) with (q / 8 + 4 * Z.of_nat depth) by (subst bse; rewrite div8_add_mul32 by lia; lia). exact SHQ. }
pose proof (munch_refl [(bse, bse + 32)] m2) as MU.
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
stash Himg_t2. stash Himg_q2. clear LV TSK.
reenterA asegs A4L HIx asegs_wx HP.
step. step.
if_true.
step.
asan_rechkM 2.
asan_rechkM 4.
step.
norm_sx32.
step.
rewrite (unsigned_lit (Z.of_nat depth)) by lia.
rewrite Z.shiftl_mul_pow2 by lia.
change (2 ^ 5) with 32.
step.
replace (q + Z.of_nat depth * 32) with bse by lia.
step.
asan_chkA.
step.
stepz.
asan_chkA.
stepz.
step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m2 mc, WMc : wmono asegs m2 mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, Lc : rw_cells asegs mc bse _ |- _ =>
evt_done5; subst bse;
destruct (PE_INV_A_lvl_writeG HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m2 mc md2 A2 B2 TS2
cb nb _ sv errv2 l2 ST_eatws ST_array_sep CArr false CArr STC INV2 Hl2 MUc WMc MIc TOKc Lc
ltac:(cbn [tl_st tl_ss l2]; exact Hmode) ltac:(vm_compute; reflexivity) ltac:(unfold ST_eatws; lia) ltac:(unfold ST_array_sep; lia)
(or_introl eq_refl) (or_intror (conj eq_refl eq_refl))) as [INV3 PBK3];
unfold TS2 in INV3, PBK3; rewrite ts_lvl_obj_lvl in INV3, PBK3;
pose proof (PE_INV_A_set_obj HIx GA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ obj objs INV3 eq_refl
ltac:(rewrite (cur_st_lvl_obj ts0 l _ _ _ _ Hl); exact I)) as INV4;
eapply (Kredo mc md2 A2 B2 cbs2 errv2); [exact INV4 | exact (PBK3 kP PBK2) | exact (BK2 ST_eatws ST_array_sep obj objs ltac:(unfold ST_array_sep, ST_finish; lia)) | exact JX2 | exact FS2 | exact FRM2]
end end.
- set (TS2 := ts0) in INV2.
clear INV0 PBK BK.
cbn [pf_spf] in *. unfold A_TP in *.
pose proof INV2 as INV2'. destruct INV2' as [CORE2 REST2].
destruct CORE2 as (_ & _ & _ & _ & TOK & _ & _ & TSK & FR).
pose proof REST2 as (HP & LV & _).
unfold TS2, ts0 in TOK, TSK, LV. cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_tk pf_mxd pf_fl] in TOK, TSK, LV.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
unfold pe_frameA in FR. destruct FR as (SLOTS & _ & _ & FF & _). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS. unfold ff_cellsA in FF.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in SLOTS, FF.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 TS2)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * mxd) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 TS2)) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t2.
blk_factsA A4L HIx HP q (32 * mxd) Hqal Hqlo Hqhi Himg_q2.
pose proof (q_ne_tkA HIx _ _ _ _ _ _ _ _ _ _ HP) as Hqtk. cbn [pf_tk] in Hqtk.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ tk 72 q (32 * mxd) HP (in_or_app _ LM _ (or_introl INtk)) (in_or_app _ LM _ (or_introl INq)) ltac:(congruence)) as Hdtq.
pose proof (tok_shadowA HIx _ _ _ _ _ _ _ _ HP INtk) as SHT.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs m2) as WM.
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
stash Himg_t2. stash Himg_q2. clear LV TSK.
reenterA asegs A4L HIx asegs_wx HP.
replace (Z_to_bv 64 (2^64 - 1)) with (Z_to_bv 64 (-1)) by (apply bv_eq; vm_compute; reflexivity).
step. step.
if_false.
step.
step.
asan_rechkM 2.
evt_done5.
eapply (Kerr16 m2 md2 A2 B2 errv2); [exact INV2 | exact FS2 | exact FRM2].
Qed.
End PeSAaddA.
End RC__1.
End Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI QSHS Qc5u QAzu.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QJjn QRUw.Mq0 QRUw QkMG. Import QG8z Qdyh.Mq0 Qdyh.Mq3 Qdyh.Mq4.
Import Qhd4 Qwm6.
Import QbFI.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqj QsKa.Mqd Qiiq QsKa.Mqf Q4v2 QSHS Ql4f.Mq4 Q1Y6.Mq4 QsKa.Mqh QrQv.Mq4 QEUF.Mq2 QW22.Mq8 QdGy.Mq9.
Import Qc5u QAzu.Mq0.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import QlKV.Mq2.
Import QnDr.Mq6 Qpfz.Mq2.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section PeSAaddA.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_outside : forall m m' W, GA m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= hl_img_lo A4H \/ hl_img_hi A4H <= fst iv) W -> GA m'.
Hypothesis GA_pres : forall LB SP m m', heap_pres A4H LB SP m m' -> GA m -> GA m'.
Hypothesis MAPP : memappend_A_stmt2 HIx.
Hypothesis AADD : jo_array_add_A2J HIx.

Ltac pe_openA STC INV :=
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR); pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk);
destruct INV as [CORE REST];
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR);
pose proof REST as (HP & LV & OBJ & ST & ERR & STR & PLEN & SBin & HPR & MDV & G & BUD).

Lemma seg_aadd_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel) (kids : list (option jshape))
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP : Z) (nB : nat)
(gp t0 a5 a7 s3 s6 s7 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv -> PBOK m ts kP -> BOK pf pa ts B (S (Z.to_nat 1280 + nB)) ->
pj_obj pj = Z_to_bv 64 (t_obj ts) ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_array_add ->
tl_cs l = Some (Sarr kids) ->

(forall m' md' A' B' cbs' errv' t0' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B'
(ts_lvl_obj ts (TL ST_eatws ST_array_sep (tl_cur l) (Some (Sarr (kids ++ [t_objs ts]))) cbs' (tl_name l) (tl_nbs l)) (t_obj ts) (t_objs ts) []) cb nb pj sv errv' ->
PBOK m' (ts_lvl_obj ts (TL ST_eatws ST_array_sep (tl_cur l) (Some (Sarr (kids ++ [t_objs ts]))) cbs' (tl_name l) (tl_nbs l)) (t_obj ts) (t_objs ts) []) kP ->
BOK pf pa (ts_lvl_obj ts (TL ST_eatws ST_array_sep (tl_cur l) (Some (Sarr (kids ++ [t_objs ts]))) cbs' (tl_name l) (tl_nbs l)) (t_obj ts) (t_objs ts) []) B' nB ->
(forall w wv, jtx (Sarr kids) (tl_cbs l) = Some (w, []) -> jtx_opt (t_objs ts) (t_objbs ts) = Some (wv, []) -> jtx (Sarr (kids ++ [t_objs ts])) cbs' = Some (w + (2 + wv), [])) ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msA asegs pf pa APE_REDO (t_co ts) gp t0' a0' a1' a2' a3' a4' a5' a6' a7' s3 (Z_to_bv 64 q) s6 s7 (Z_to_bv 64 (Z.of_nat (t_depth ts))) s9 s11 t3' t4' t5' t6' F' fc' m')) ->

(forall m' md' A' B' errv' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' ts cb nb pj sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msO asegs pf pa APE_ERRMEM gp t0' t1' t2' (Z_to_bv 64 (pf_tk pf + 36)) a1' a2' a3' a4' a5' a6' a7' s3 (Z_to_bv 64 (pf_sb pf + t_co ts)) (Z_to_bv 64 q) s6 s7 (Z_to_bv 64 (Z.of_nat (t_depth ts))) s9 s11 t3' t4' t5' t6' F' fc' m')) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa (pe_jtA ST_array_add) (t_co ts) gp t0 (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) (Z_to_bv 64 (tl_st l)) (Z_to_bv 64 0) (Z_to_bv 64 (q / 8 + 4 * Z.of_nat (t_depth ts) + A_SB)) (Z_to_bv 64 0) a5 (Z_to_bv 64 APE_JTAB) a7 s3 (Z_to_bv 64 q) s6 s7 (Z_to_bv 64 (Z.of_nat (t_depth ts))) s9 s11 t3 t4 t5 t6 F fc m).
Proof.
intros until fc. intros STC BSL INV PBK BK OBJW Hl Hst Hcs Kredo Kerr16. pose proof INV as INV0. pe_openA STC INV.
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
pose proof FR as FR0. unfold pe_frameA in FR. destruct FR as (SLOTS & GAP & SAVED & FF & FSH).
unfold pe_slotsA in SLOTS. cbn zeta in SLOTS. unfold ff_cellsA in FF.
unfold pe_msA, pe_msO in *.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * mxd) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t.
blk_factsA A4L HIx HP q (32 * mxd) Hqal Hqlo Hqhi Himg_q.
pose proof (q_ne_tkA HIx _ _ _ _ _ _ _ _ _ _ HP) as Hqtk. cbn [pf_tk] in Hqtk.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ tk 72 q (32 * mxd) HP (in_or_app _ LM _ (or_introl INtk)) (in_or_app _ LM _ (or_introl INq)) ltac:(congruence)) as Hdtq.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 4 HP INtk ltac:(lia)) as SHT4.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 4 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEP4c & SEP4q & SEP4i). cbn [hl_sb A4L] in SEP4c, SEP4q, SEP4i.
replace (tk / 8 + 4 + A_SB) with (tk / 8 + SB4) in SHT4 by (unfold SB4, A_SB; lia).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs m) as WM.
pose proof (LV depth l Hl) as LVd. pose proof LVd as (ST26 & SS26 & _ & Md).
rewrite Nat.ltb_irrefl, Nat.eqb_refl in Md. destruct Md as (c0 & hn0 & Hmode & CLS0 & NM0).
pose proof (TSK depth l Hl) as Ld. remember (q + 32 * Z.of_nat depth) as bse eqn:Hbse in Ld. unfold srec_cells in Ld.
assert (HbseR : q <= bse /\ bse + 32 <= q + (32 * mxd)) by (subst bse; lia).
pose proof (stack_shadowA HIx _ _ _ _ _ _ _ q mxd (Z.of_nat depth) 0 HP INq ltac:(lia) ltac:(lia)) as SHQ.
replace (q / 8 + 4 * Z.of_nat depth + 0 + A_SB) with (q / 8 + 4 * Z.of_nat depth + A_SB) in SHQ by lia.
assert (Hb8 : bse mod 8 = 0) by (subst bse; clear - Hqal; Z.div_mod_to_equations; lia).
assert (SHQ4 : ro_cells asegs m (bse / 8 + A_SB) [C1 (Z_to_bv 8 0)]).
{ replace (bse / 8) with (q / 8 + 4 * Z.of_nat depth) by (subst bse; rewrite div8_add_mul32 by lia; lia). exact SHQ. }
pose proof (munch_refl [(bse, bse + 32)] m) as MU.
pose proof (bv_unsigned_in_range 8 cb) as CBR; unfold bv_modulus in CBR; cbn in CBR.
unfold APE_REDO, APE_ERRMEM, APE_JTAB in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
assert (MODE0 : c0 = CArr /\ hn0 = false).
{ rewrite Hst, (Qdyh.Mq0.lvl_mode_aadd (tl_ss l)) in Hmode. injection Hmode as <- <-. split; reflexivity. }
destruct MODE0 as (-> & ->). cbn [name_ok] in NM0. destruct NM0 as [Hn0 Hnbs0].
pose proof (stack_shadowA HIx _ _ _ _ _ _ _ q mxd (Z.of_nat depth) 2 HP INq ltac:(lia) ltac:(lia)) as SHQ2.
assert (SHQ16 : ro_cells asegs m (bse / 8 + 2147450882) [C1 (Z_to_bv 8 0)]).
{ replace (bse / 8 + 2147450882) with (q / 8 + 4 * Z.of_nat depth + 2 + A_SB) by (subst bse; rewrite div8_add_mul32 by lia; unfold A_SB; lia). exact SHQ2. }
destruct pj as [pj0 pj8 pj16 pjobj pj288 pj304 pjgap pjfhd pjf1 pjf2]. cbn [pj_0 pj_8 pj_16 pj_obj pj_288 pj_304 pj_gap pj_fhd pj_f1 pj_f2] in *. subst pjobj.
stash Himg_t. stash Himg_q. clear PB REST TSK HP LV OBJ HPR BUD GAP SAVED FSH.
reenterA asegs A4L HIx asegs_wx HP. rewrite Hst. unfold ST_array_add. cbn [pe_jtA].
replace (q + 32 * Z.of_nat depth) with bse by lia.
step.
asan_chkB.
step.
step.
step.
evt_done5. subst bse.
eapply (pe_aadd_cJ HIx GA GA_pres AADD (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m md A B ts0 l kids cb nb _ sv errv T kP nB);
[exact STC | exact BSL | exact INV0 | exact PBK | exact BK | exact Hl | exact Hst | exact Hcs | exact Hnbs0 | rewrite unsigned_lit by lia; reflexivity |].
intros m2 md2 A2 B2 errv2 r w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 F2 fc2 OUT FS2 FRM2.
clear TOK SLOTS FF SHT4 SEP4c SEP4q SEP4i SHQ SHQ4 SHQ2 SHQ16 Ld MU WM MI Htal Htlo Hthi Hqal Hqlo Hqhi Hdtq Hqtk INtk INq HbseR Hb8.
destruct OUT as [(-> & cbs2 & INV2 & PBK2 & BK2 & JX2) | (-> & INV2)].
- set (l2 := TL (tl_st l) (tl_ss l) (tl_cur l) (Some (Sarr (kids ++ [t_objs ts0]))) cbs2 (tl_name l) (tl_nbs l)) in *.
set (TS2 := ts_lvl_obj ts0 l2 0 None []) in *.
assert (Hl2 : nth_error (t_levels TS2) (t_depth TS2) = Some l2) by (unfold TS2, ts_lvl_obj, ts0; cbn [t_levels t_depth]; apply nth_error_lupd_eq; apply nth_error_Some; rewrite Hl; discriminate).
clear INV0 PBK BK.
cbn [pf_spf] in *. unfold A_TP in *.
pose proof INV2 as INV2'. destruct INV2' as [CORE2 REST2].
destruct CORE2 as (_ & _ & _ & _ & TOK & _ & _ & TSK & FR).
pose proof REST2 as (HP & LV & _).
unfold TS2, ts_lvl_obj, ts0 in TOK, TSK, LV. cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_tk pf_mxd pf_fl] in TOK, TSK, LV.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
unfold pe_frameA in FR. destruct FR as (SLOTS & _ & _ & FF & _). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS. unfold ff_cellsA in FF.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in SLOTS, FF.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 TS2)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * mxd) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 TS2)) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t2.
blk_factsA A4L HIx HP q (32 * mxd) Hqal Hqlo Hqhi Himg_q2.
pose proof (q_ne_tkA HIx _ _ _ _ _ _ _ _ _ _ HP) as Hqtk. cbn [pf_tk] in Hqtk.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ tk 72 q (32 * mxd) HP (in_or_app _ LM _ (or_introl INtk)) (in_or_app _ LM _ (or_introl INq)) ltac:(congruence)) as Hdtq.
pose proof (tok_shadowA HIx _ _ _ _ _ _ _ _ HP INtk) as SHT.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs m2) as WM.
pose proof (TSK depth l2 ltac:(apply nth_error_lupd_eq; apply nth_error_Some; rewrite Hl; discriminate)) as Ld. remember (q + 32 * Z.of_nat depth) as bse eqn:Hbse in Ld. unfold srec_cells in Ld. cbn [tl_st tl_ss tl_cur tl_name l2] in Ld.
assert (HbseR : q <= bse /\ bse + 32 <= q + (32 * mxd)) by (subst bse; lia).
pose proof (stack_shadowA HIx _ _ _ _ _ _ _ q mxd (Z.of_nat depth) 0 HP INq ltac:(lia) ltac:(lia)) as SHQ.
replace (q / 8 + 4 * Z.of_nat depth + 0 + A_SB) with (q / 8 + 4 * Z.of_nat depth + A_SB) in SHQ by lia.
assert (Hb8 : bse mod 8 = 0) by (subst bse; clear - Hqal; Z.div_mod_to_equations; lia).
assert (SHQ4 : ro_cells asegs m2 (bse / 8 + A_SB) [C1 (Z_to_bv 8 0)]).
{ replace (bse / 8) with (q / 8 + 4 * Z.of_nat depth) by (subst bse; rewrite div8_add_mul32 by lia; lia). exact SHQ. }
pose proof (munch_refl [(bse, bse + 32)] m2) as MU.
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
stash Himg_t2. stash Himg_q2. clear LV TSK.
reenterA asegs A4L HIx asegs_wx HP.
assert (BLO : 0 < bse < 2^63 /\ q <= bse) by (subst bse; lia).
step. if_true.
step. step. rewrite ?sxb_zero, ?zxb_zero. step. step. if_true.
step. rewrite ?sxb_zero, ?zxb_zero. do 4 step. step. if_true.
step. step.
norm_sx32.
step. step.
ub_bse q bse (Z.of_nat depth).
step. step. ub_lvl q bse (Z.of_nat depth). step. ub_if_lit.
do 4 step. ub_lvl q bse (Z.of_nat depth). step. ub_if_lit.
step. if_truex.
step. ub_land Hb8. step. ub_if_lit.
step.
asan_chkB.
step.
stepz.
step. if_truex.
step. step. sh_norm. step. rewrite ?sxb_zero, ?zxb_zero. step. if_false. step.
stepz.
step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m2 mc, WMc : wmono asegs m2 mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, Lc : rw_cells asegs mc bse _ |- _ =>
evt_done5; subst bse;
destruct (PE_INV_A_lvl_writeG HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m2 mc md2 A2 B2 TS2
cb nb _ sv errv2 l2 ST_eatws ST_array_sep CArr false CArr STC INV2 Hl2 MUc WMc MIc TOKc Lc
ltac:(cbn [tl_st tl_ss l2]; exact Hmode) ltac:(vm_compute; reflexivity) ltac:(unfold ST_eatws; lia) ltac:(unfold ST_array_sep; lia)
(or_introl eq_refl) (or_intror (conj eq_refl eq_refl))) as [INV3 PBK3];
unfold TS2 in INV3, PBK3; rewrite ts_lvl_obj_lvl in INV3, PBK3;
pose proof (PE_INV_A_set_obj HIx GA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ obj objs INV3 eq_refl
ltac:(rewrite (cur_st_lvl_obj ts0 l _ _ _ _ Hl); exact I)) as INV4;
eapply (Kredo mc md2 A2 B2 cbs2 errv2); [exact INV4 | exact (PBK3 kP PBK2) | exact (BK2 ST_eatws ST_array_sep obj objs ltac:(unfold ST_array_sep, ST_finish; lia)) | exact JX2 | exact FS2 | exact FRM2]
end end.
- set (TS2 := ts0) in INV2.
clear INV0 PBK BK.
cbn [pf_spf] in *. unfold A_TP in *.
pose proof INV2 as INV2'. destruct INV2' as [CORE2 REST2].
destruct CORE2 as (_ & _ & _ & _ & TOK & _ & _ & TSK & FR).
pose proof REST2 as (HP & LV & _).
unfold TS2, ts0 in TOK, TSK, LV. cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_tk pf_mxd pf_fl] in TOK, TSK, LV.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
unfold pe_frameA in FR. destruct FR as (SLOTS & _ & _ & FF & _). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS. unfold ff_cellsA in FF.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in SLOTS, FF.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 TS2)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * mxd) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 TS2)) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t2.
blk_factsA A4L HIx HP q (32 * mxd) Hqal Hqlo Hqhi Himg_q2.
pose proof (q_ne_tkA HIx _ _ _ _ _ _ _ _ _ _ HP) as Hqtk. cbn [pf_tk] in Hqtk.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ tk 72 q (32 * mxd) HP (in_or_app _ LM _ (or_introl INtk)) (in_or_app _ LM _ (or_introl INq)) ltac:(congruence)) as Hdtq.
pose proof (tok_shadowA HIx _ _ _ _ _ _ _ _ HP INtk) as SHT.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs m2) as WM.
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
stash Himg_t2. stash Himg_q2. clear LV TSK.
reenterA asegs A4L HIx asegs_wx HP.
replace (Z_to_bv 64 (2^64 - 1)) with (Z_to_bv 64 (-1)) by (apply bv_eq; vm_compute; reflexivity).
step. if_false.
step.
step. step. rewrite ?sxb_zero, ?zxb_zero. step. step. step. if_true.
evt_done5.
eapply (Kerr16 m2 md2 A2 B2 errv2); [exact INV2 | exact FS2 | exact FRM2].
Qed.
End PeSAaddA.
End RC__1.
End Mq1.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QJjn QRUw.Mq0 QRUw QkMG. Import QG8z Qdyh.Mq3 Qdyh.Mq4.
Import Qhd4 Qwm6.
Import QbFI.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqj QsKa.Mqd Qiiq QsKa.Mqf Q4v2 QSHS Ql4f.Mq4 Q1Y6.Mq4 QsKa.Mqh QrQv.Mq4 QEUF.Mq2 QW22.Mq8 QdGy.Mq9.
Import Qc5u QAzu.Mq0.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import QlKV.Mq2.
Import QnDr.Mq6 Qpfz.Mq2.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section PeSAsepA.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_outside : forall m m' W, GA m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= hl_img_lo A4H \/ hl_img_hi A4H <= fst iv) W -> GA m'.
Hypothesis GA_pres : forall LB SP m m', heap_pres A4H LB SP m m' -> GA m -> GA m'.
Hypothesis MAPP : memappend_A_stmt2 HIx.
Hypothesis SHRINK : jo_array_shrink_A2J HIx.

Ltac pe_openA STC INV :=
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR); pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk);
destruct INV as [CORE REST];
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR);
pose proof REST as (HP & LV & OBJ & ST & ERR & STR & PLEN & SBin & HPR & MDV & G & BUD).

Lemma seg_asep_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP : Z) (nB : nat)
(gp t0 a5 a7 s3 s6 s7 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv -> PBOK m ts kP -> BOK pf pa ts B nB ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_array_sep ->
t_co ts < pf_len pf ->

(forall m' ss' a1' a4' a5',
(bv_unsigned cb = 44 /\ ss' = ST_array_after_sep) ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md A B
(ts_lvl ts (TL ST_eatws ss' (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) cb nb pj sv errv ->
PBOK m' (ts_lvl ts (TL ST_eatws ss' (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) kP ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa APE_BREAK (t_co ts) gp t0 (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) a1' (Z_to_bv 64 0) (Z_to_bv 64 (q / 8 + 4 * Z.of_nat (t_depth ts) + A_SB)) a4' a5' (Z_to_bv 64 APE_JTAB) a7 s3 (Z_to_bv 64 2) s6 s7 (Z_to_bv 64 (Z.of_nat (t_depth ts))) s9 s11 t3 t4 t5 t6 F fc m')) ->

(forall m' md' A' B' cbs' errv' t0' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' kids,
bv_unsigned cb = 93 -> tl_cs l = Some (Sarr kids) ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B'
(ts_lvl ts (TL ST_eatws ST_finish (tl_cur l) (tl_cs l) cbs' (tl_name l) (tl_nbs l))) cb nb pj sv errv' ->
PBOK m' (ts_lvl ts (TL ST_eatws ST_finish (tl_cur l) (tl_cs l) cbs' (tl_name l) (tl_nbs l))) kP ->
BOK pf pa (ts_lvl ts (TL ST_eatws ST_finish (tl_cur l) (tl_cs l) cbs' (tl_name l) (tl_nbs l))) B' nB ->
(forall w, jtx (Sarr kids) (tl_cbs l) = Some (w, []) -> jtx (Sarr kids) cbs' = Some (w, [])) ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msA asegs pf pa APE_BREAK (t_co ts) gp t0' a0' a1' a2' a3' a4' a5' a6' a7' s3 (Z_to_bv 64 2) s6 s7 (Z_to_bv 64 (Z.of_nat (t_depth ts))) s9 s11 t3' t4' t5' t6' F' fc' m')) ->

(forall a2' a5',
bv_unsigned cb <> 44 -> bv_unsigned cb <> 93 ->
AJ5 A4L HIx A T md
(pe_msO asegs pf pa APE_ERR3 gp t0 (Z_to_bv 64 (pf_lenr pf)) (Z_to_bv 64 (pf_tk pf + 32)) (Z_to_bv 64 8) (Z_to_bv 64 (bv_unsigned cb)) a2' (Z_to_bv 64 (q / 8 + 4 * Z.of_nat (t_depth ts) + A_SB)) (Z_to_bv 64 0) a5' (Z_to_bv 64 APE_JTAB) a7 s3 (Z_to_bv 64 (pf_sb pf + t_co ts)) (Z_to_bv 64 q) s6 s7 (Z_to_bv 64 (Z.of_nat (t_depth ts))) s9 s11 t3 t4 t5 t6 F fc m)) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa (pe_jtA ST_array_sep) (t_co ts) gp t0 (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) (Z_to_bv 64 (tl_st l)) (Z_to_bv 64 0) (Z_to_bv 64 (q / 8 + 4 * Z.of_nat (t_depth ts) + A_SB)) (Z_to_bv 64 0) a5 (Z_to_bv 64 APE_JTAB) a7 s3 (Z_to_bv 64 q) s6 s7 (Z_to_bv 64 (Z.of_nat (t_depth ts))) s9 s11 t3 t4 t5 t6 F fc m).
Proof.
intros until fc. intros STC BSL INV PBK BK Hl Hst Hco Kbreak Kclose Kerr. pose proof INV as INV0. pe_openA STC INV.
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
pose proof FR as FR0. unfold pe_frameA in FR. destruct FR as (SLOTS & GAP & SAVED & FF & FSH).
unfold pe_slotsA in SLOTS. cbn zeta in SLOTS. unfold ff_cellsA in FF.
unfold pe_msA in *.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * mxd) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t.
blk_factsA A4L HIx HP q (32 * mxd) Hqal Hqlo Hqhi Himg_q.
pose proof (q_ne_tkA HIx _ _ _ _ _ _ _ _ _ _ HP) as Hqtk. cbn [pf_tk] in Hqtk.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ tk 72 q (32 * mxd) HP (in_or_app _ LM _ (or_introl INtk)) (in_or_app _ LM _ (or_introl INq)) ltac:(congruence)) as Hdtq.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 4 HP INtk ltac:(lia)) as SHT4.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 4 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEP4c & SEP4q & SEP4i). cbn [hl_sb A4L] in SEP4c, SEP4q, SEP4i.
replace (tk / 8 + 4 + A_SB) with (tk / 8 + SB4) in SHT4 by (unfold SB4, A_SB; lia).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs m) as WM.
pose proof (LV depth l Hl) as LVd. pose proof LVd as (ST26 & SS26 & _ & Md).
rewrite Nat.ltb_irrefl, Nat.eqb_refl in Md. destruct Md as (c0 & hn0 & Hmode & CLS0 & NM0).
pose proof (TSK depth l Hl) as Ld. remember (q + 32 * Z.of_nat depth) as bse eqn:Hbse in Ld. unfold srec_cells in Ld.
assert (HbseR : q <= bse /\ bse + 32 <= q + (32 * mxd)) by (subst bse; lia).
pose proof (stack_shadowA HIx _ _ _ _ _ _ _ q mxd (Z.of_nat depth) 0 HP INq ltac:(lia) ltac:(lia)) as SHQ.
replace (q / 8 + 4 * Z.of_nat depth + 0 + A_SB) with (q / 8 + 4 * Z.of_nat depth + A_SB) in SHQ by lia.
assert (Hb8 : bse mod 8 = 0) by (subst bse; clear - Hqal; Z.div_mod_to_equations; lia).
assert (SHQ4 : ro_cells asegs m (bse / 8 + A_SB) [C1 (Z_to_bv 8 0)]).
{ replace (bse / 8) with (q / 8 + 4 * Z.of_nat depth) by (subst bse; rewrite div8_add_mul32 by lia; lia). exact SHQ. }
pose proof (munch_refl [(bse, bse + 32)] m) as MU.
pose proof (bv_unsigned_in_range 8 cb) as CBR; unfold bv_modulus in CBR; cbn in CBR.
unfold APE_BREAK, APE_EATBRK, APE_ERR3, APE_JTAB in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
assert (MODE0 : c0 = CArr /\ hn0 = false /\ tl_ss l <> ST_finish).
{ rewrite Hst in Hmode. unfold ST_array_sep in Hmode. clear - Hmode SS26.
assert (R : 0 <= tl_ss l <= 26) by lia. enum_z R (tl_ss l); vm_compute in Hmode; try discriminate Hmode; (split; [congruence | split; [congruence | unfold ST_finish; lia]]). }
destruct MODE0 as (-> & -> & Hop). cbn [name_ok] in NM0. destruct NM0 as [Hn0 Hnbs0].
pose proof (stack_shadowA HIx _ _ _ _ _ _ _ q mxd (Z.of_nat depth) 2 HP INq ltac:(lia) ltac:(lia)) as SHQ2.
assert (SHQ16 : ro_cells asegs m (bse / 8 + 2147450882) [C1 (Z_to_bv 8 0)]).
{ replace (bse / 8 + 2147450882) with (q / 8 + 4 * Z.of_nat depth + 2 + A_SB) by (subst bse; rewrite div8_add_mul32 by lia; unfold A_SB; lia). exact SHQ2. }
stash Himg_t. stash Himg_q. clear PB REST TSK HP LV OBJ HPR BUD GAP SAVED FSH.
reenterA asegs A4L HIx asegs_wx HP. rewrite Hst. unfold ST_array_sep. cbn [pe_jtA].
replace (q + 32 * Z.of_nat depth) with bse by lia.
step. step.
change (zxb cb) with (Z_to_bv 64 (bv_unsigned cb)).
step.
destruct (Z.eq_dec (bv_unsigned cb) 44) as [C44 | N44].
- step. if_truex.
step.
asan_chkB.
step. step.
stepz.
step. if_true.
step. rewrite ?sxb_zero, ?zxb_zero. step. if_true.
stepz.
step. step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, Lc : rw_cells asegs mc bse _ |- _ =>
evt_done5; subst bse;
destruct (PE_INV_A_lvl_write HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m mc md A B ts0
cb nb pj sv errv l ST_eatws ST_array_after_sep _ _ CArr STC INV0 Hl MUc WMc MIc TOKc Lc Hmode ltac:(vm_compute; reflexivity) ltac:(unfold ST_eatws; lia) ltac:(unfold ST_array_after_sep; lia)
(or_introl eq_refl) ltac:(rewrite Hst; vm_compute; reflexivity)) as [INV3 PBK3];
eapply (Kbreak mc ST_array_after_sep _ _ _ ltac:(split; [exact C44 | reflexivity])); [exact INV3 | exact (PBK3 kP PBK)]
end end.
- step. if_falsex.
step.
destruct (Z.eq_dec (bv_unsigned cb) 93) as [C93 | N93].
+ step. if_truex.
assert (EK : exists kids, tl_cs l = Some (Sarr kids)) by (clear - CLS0; destruct (tl_cs l) as [[| | | |okids|kids]|]; try (exfalso; exact CLS0); eexists; reflexivity).
destruct EK as [kids Ecs].
step.
asan_chkB.
step.
step.
evt_done5. subst bse.
eapply (pe_shrink_cJ HIx GA GA_pres SHRINK (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m md A B ts0 l kids cb nb pj sv errv T kP nB);
[exact STC | exact BSL | exact INV0 | exact PBK | exact BK | exact Hl | exact Ecs | exact Hop | exact Hnbs0 | rewrite unsigned_lit by lia; reflexivity |].
intros m2 md2 A2 B2 cbs2 errv2 r w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 F2 fc2 INV2 PBK2 BK2 JX2 FS2 FRM2.
cbn [pf_spf] in *. unfold A_TP in *.

clear TOK SLOTS FF SHT4 SEP4c SEP4q SEP4i SHQ SHQ4 SHQ2 SHQ16 Ld MU WM MI Htal Htlo Hthi Hqal Hqlo Hqhi Hdtq Hqtk INtk INq INV0 PBK BK HbseR Hb8.
set (l2 := TL (tl_st l) (tl_ss l) (tl_cur l) (tl_cs l) cbs2 (tl_name l) (tl_nbs l)) in *.
set (ts2 := ts_lvl ts0 l2) in *.
assert (Hl2 : nth_error (t_levels ts2) (t_depth ts2) = Some l2) by (unfold ts2, ts_lvl, ts0; cbn [t_levels t_depth]; apply nth_error_lupd_eq; apply nth_error_Some; rewrite Hl; discriminate).
pose proof INV2 as INV2'. destruct INV2' as [CORE2 REST2].
destruct CORE2 as (_ & _ & _ & _ & TOK & _ & _ & TSK & FR).
pose proof REST2 as (HP & LV & _).
unfold ts2, ts_lvl, ts0 in TOK, TSK, LV. cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_tk pf_mxd pf_fl] in TOK, TSK, LV.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
unfold pe_frameA in FR. destruct FR as (SLOTS & _ & _ & FF & _). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS. unfold ff_cellsA in FF.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in SLOTS, FF.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts2)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * mxd) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts2)) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t2.
blk_factsA A4L HIx HP q (32 * mxd) Hqal Hqlo Hqhi Himg_q2.
pose proof (q_ne_tkA HIx _ _ _ _ _ _ _ _ _ _ HP) as Hqtk. cbn [pf_tk] in Hqtk.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ tk 72 q (32 * mxd) HP (in_or_app _ LM _ (or_introl INtk)) (in_or_app _ LM _ (or_introl INq)) ltac:(congruence)) as Hdtq.
pose proof (tok_shadowA HIx _ _ _ _ _ _ _ _ HP INtk) as SHT.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs m2) as WM.
pose proof (TSK depth l2 ltac:(apply nth_error_lupd_eq; apply nth_error_Some; rewrite Hl; discriminate)) as Ld. remember (q + 32 * Z.of_nat depth) as bse eqn:Hbse in Ld. unfold srec_cells in Ld. cbn [tl_st tl_ss tl_cur tl_name l2] in Ld.
assert (HbseR : q <= bse /\ bse + 32 <= q + (32 * mxd)) by (subst bse; lia).
pose proof (stack_shadowA HIx _ _ _ _ _ _ _ q mxd (Z.of_nat depth) 0 HP INq ltac:(lia) ltac:(lia)) as SHQ.
replace (q / 8 + 4 * Z.of_nat depth + 0 + A_SB) with (q / 8 + 4 * Z.of_nat depth + A_SB) in SHQ by lia.
assert (Hb8 : bse mod 8 = 0) by (subst bse; clear - Hqal; Z.div_mod_to_equations; lia).
assert (SHQ4 : ro_cells asegs m2 (bse / 8 + A_SB) [C1 (Z_to_bv 8 0)]).
{ replace (bse / 8) with (q / 8 + 4 * Z.of_nat depth) by (subst bse; rewrite div8_add_mul32 by lia; lia). exact SHQ. }
pose proof (munch_refl [(bse, bse + 32)] m2) as MU.
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
stash Himg_t2. stash Himg_q2. clear LV TSK.
reenterA asegs A4L HIx asegs_wx HP.
assert (BLO : 0 < bse < 2^63 /\ q <= bse) by (subst bse; lia).
step. step. rewrite ?sxb_zero, ?zxb_zero. step. if_true.
step. step. rewrite ?sxb_zero, ?zxb_zero. do 4 step. step. if_true.
step. step.
norm_sx32.
step. step.
ub_bse q bse (Z.of_nat depth).
step. step. ub_lvl q bse (Z.of_nat depth). step. ub_if_lit.
do 4 step. ub_lvl q bse (Z.of_nat depth). step. ub_if_lit.
step. if_truex.
step. ub_land Hb8. step. ub_if_lit.
step.
asan_chkB.
step.
stepz.
step. if_truex.
step. step. sh_norm. step. rewrite ?sxb_zero, ?zxb_zero. step. if_true.
stepz.
step. step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m2 mc, WMc : wmono asegs m2 mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, Lc : rw_cells asegs mc bse _ |- _ =>
evt_done5; subst bse;
destruct (PE_INV_A_lvl_write HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m2 mc md2 A2 B2 ts2
cb nb pj sv errv2 l2 ST_eatws ST_finish CArr false CAny STC INV2 Hl2 MUc WMc MIc TOKc Lc Hmode ltac:(vm_compute; reflexivity) ltac:(unfold ST_eatws; lia) ltac:(unfold ST_finish; lia)
(or_intror eq_refl) ltac:(cbn [tl_st l2]; rewrite Hst; vm_compute; reflexivity)) as [INV3 PBK3];
unfold ts2 in INV3, PBK3; rewrite ts_lvl_lvl in INV3, PBK3;
eapply (Kclose mc md2 A2 B2 cbs2 errv2 _ _ _ _ _ _ _ _ _ _ _ _ _ F2 fc2 kids C93 Ecs); [exact INV3 | exact (PBK3 kP PBK2) | exact (BK2 ST_eatws eq_refl) | exact JX2 | exact FS2 | exact FRM2]
end end.
+ step. if_falsex.
step.
step.
step. rewrite ?sxb_zero, ?zxb_zero. step. if_true.
step. step.
evt_done5.
subst bse. eapply Kerr; [exact N44 | exact N93].
Qed.
End PeSAsepA.
End RC__1.
End Mq2.

From Stdlib Require Import ZArith List Lia Bool.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qdyh.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qdyh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qdyh.Mq4.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4v2.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1Ey.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1Ey. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Ql4f.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql4f.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1Y6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1Y6.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QrQv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QrQv.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEUF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEUF. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QW22.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QW22.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdGy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdGy.Mq2.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnDr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnDr.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qpfz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qpfz.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section PeSAsepA.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_outside : forall m m' W, GA m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= hl_img_lo A4H \/ hl_img_hi A4H <= fst iv) W -> GA m'.
Hypothesis GA_pres : forall LB SP m m', heap_pres A4H LB SP m m' -> GA m -> GA m'.
Hypothesis MAPP : memappend_A_stmt2 HIx.
Hypothesis SHRINK : jo_array_shrink_A2J HIx.

Ltac pe_openA STC INV :=
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR); pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk);
destruct INV as [CORE REST];
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR);
pose proof REST as (HP & LV & OBJ & ST & ERR & STR & PLEN & SBin & HPR & MDV & G & BUD).

Lemma seg_asep_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP : Z) (nB : nat)
(gp t0 t1 t2 a3 a5 a6 a7 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv -> PBOK m ts kP -> BOK pf pa ts B nB ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_array_sep ->
t_co ts < pf_len pf ->

(forall m' ss' a1' a2' a3',
(bv_unsigned cb = 44 /\ ss' = ST_array_after_sep) ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md A B
(ts_lvl ts (TL ST_eatws ss' (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) cb nb pj sv errv ->
PBOK m' (ts_lvl ts (TL ST_eatws ss' (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) kP ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa APE_ADV (t_co ts) gp t0 t1 t2 (Z_to_bv 64 125) a1' a2' a3' (Z_to_bv 64 APE_JTAB) a5 a6 a7
(Z_to_bv 64 (Z.of_nat (t_depth ts))) (Z_to_bv 64 (pf_tk pf + 56)) (Z_to_bv 64 (pa_F pa + 64)) F fc m')) ->

(forall m' md' A' B' cbs' errv' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' F' fc' kids,
bv_unsigned cb = 93 -> tl_cs l = Some (Sarr kids) ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B'
(ts_lvl ts (TL ST_eatws ST_finish (tl_cur l) (tl_cs l) cbs' (tl_name l) (tl_nbs l))) cb nb pj sv errv' ->
PBOK m' (ts_lvl ts (TL ST_eatws ST_finish (tl_cur l) (tl_cs l) cbs' (tl_name l) (tl_nbs l))) kP ->
BOK pf pa (ts_lvl ts (TL ST_eatws ST_finish (tl_cur l) (tl_cs l) cbs' (tl_name l) (tl_nbs l))) B' nB ->
(forall w, jtx (Sarr kids) (tl_cbs l) = Some (w, []) -> jtx (Sarr kids) cbs' = Some (w, [])) ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msA asegs pf pa APE_BREAK (t_co ts) gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5'
(Z_to_bv 64 (pf_tk pf + 56)) (Z_to_bv 64 (pa_F pa + 64)) F' fc' m')) ->

(forall a1' a2' a3',
bv_unsigned cb <> 44 -> bv_unsigned cb <> 93 ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa APE_ERR2 (t_co ts) gp t0 t1 t2 (Z_to_bv 64 8) a1'
a2' a3' (Z_to_bv 64 APE_JTAB) a5 a6 a7
(Z_to_bv 64 (Z.of_nat (t_depth ts))) (Z_to_bv 64 q) (Z_to_bv 64 (pa_F pa + 64)) F fc m)) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa (pe_jtA ST_array_sep) (t_co ts) gp t0 t1 t2
(Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) (Z_to_bv 64 (tl_st l))
(Z_to_bv 64 (q / 8 + 4 * Z.of_nat (t_depth ts) + A_SB)) a3 (Z_to_bv 64 APE_JTAB) a5 a6 a7
(Z_to_bv 64 (Z.of_nat (t_depth ts))) (Z_to_bv 64 q) (Z_to_bv 64 (pa_F pa + 64)) F fc m).
Proof.
intros until fc. intros STC BSL INV PBK BK Hl Hst Hco Kbreak Kclose Kerr. pose proof INV as INV0. pe_openA STC INV.
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
pose proof FR as FR0. unfold pe_frameA in FR. destruct FR as (SLOTS & GAP & SAVED & FF & FSH).
unfold pe_slotsA in SLOTS. cbn zeta in SLOTS. unfold ff_cellsA in FF.
unfold pe_msA in *.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * mxd) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t.
blk_factsA A4L HIx HP q (32 * mxd) Hqal Hqlo Hqhi Himg_q.
pose proof (q_ne_tkA HIx _ _ _ _ _ _ _ _ _ _ HP) as Hqtk. cbn [pf_tk] in Hqtk.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ tk 72 q (32 * mxd) HP (in_or_app _ LM _ (or_introl INtk)) (in_or_app _ LM _ (or_introl INq)) ltac:(congruence)) as Hdtq.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 4 HP INtk ltac:(lia)) as SHT4.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 4 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEP4c & SEP4q & SEP4i). cbn [hl_sb A4L] in SEP4c, SEP4q, SEP4i.
replace (tk / 8 + 4 + A_SB) with (tk / 8 + SB4) in SHT4 by (unfold SB4, A_SB; lia).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs m) as WM.
pose proof (LV depth l Hl) as LVd. pose proof LVd as (ST26 & SS26 & _ & Md).
rewrite Nat.ltb_irrefl, Nat.eqb_refl in Md. destruct Md as (c0 & hn0 & Hmode & CLS0 & NM0).
pose proof (TSK depth l Hl) as Ld. remember (q + 32 * Z.of_nat depth) as bse eqn:Hbse in Ld. unfold srec_cells in Ld.
assert (HbseR : q <= bse /\ bse + 32 <= q + (32 * mxd)) by (subst bse; lia).
pose proof (stack_shadowA HIx _ _ _ _ _ _ _ q mxd (Z.of_nat depth) 0 HP INq ltac:(lia) ltac:(lia)) as SHQ.
replace (q / 8 + 4 * Z.of_nat depth + 0 + A_SB) with (q / 8 + 4 * Z.of_nat depth + A_SB) in SHQ by lia.
assert (Hb8 : bse mod 8 = 0) by (subst bse; clear - Hqal; Z.div_mod_to_equations; lia).
assert (SHQ4 : ro_cells asegs m (bse / 8 + A_SB) [C1 (Z_to_bv 8 0)]).
{ replace (bse / 8) with (q / 8 + 4 * Z.of_nat depth) by (subst bse; rewrite div8_add_mul32 by lia; lia). exact SHQ. }
pose proof (munch_refl [(bse, bse + 32)] m) as MU.
pose proof (bv_unsigned_in_range 8 cb) as CBR; unfold bv_modulus in CBR; cbn in CBR.
unfold APE_ADV, APE_BREAK, APE_ERR2, APE_JTAB in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
assert (MODE0 : c0 = CArr /\ hn0 = false /\ tl_ss l <> ST_finish).
{ rewrite Hst in Hmode. unfold ST_array_sep in Hmode. clear - Hmode SS26.
assert (R : 0 <= tl_ss l <= 26) by lia. enum_z R (tl_ss l); vm_compute in Hmode; try discriminate Hmode; (split; [congruence | split; [congruence | unfold ST_finish; lia]]). }
destruct MODE0 as (-> & -> & Hop). cbn [name_ok] in NM0. destruct NM0 as [Hn0 Hnbs0].
pose proof (stack_shadowA HIx _ _ _ _ _ _ _ q mxd (Z.of_nat depth) 2 HP INq ltac:(lia) ltac:(lia)) as SHQ2.
assert (SHQ16 : ro_cells asegs m (bse / 8 + 2147450882) [C1 (Z_to_bv 8 0)]).
{ replace (bse / 8 + 2147450882) with (q / 8 + 4 * Z.of_nat depth + 2 + A_SB) by (subst bse; rewrite div8_add_mul32 by lia; unfold A_SB; lia). exact SHQ2. }
stash Himg_t. stash Himg_q. clear PB REST TSK HP LV OBJ HPR BUD GAP SAVED FSH.
reenterA asegs A4L HIx asegs_wx HP. rewrite Hst. unfold ST_array_sep. cbn [pe_jtA].
replace (q + 32 * Z.of_nat depth) with bse by lia.
step.
change (zxb cb) with (Z_to_bv 64 (bv_unsigned cb)).
step.
destruct (Z.eq_dec (bv_unsigned cb) 44) as [C44 | N44].
- step.
if_truex.
step.
asan_chkA.
step.
stepz.
asan_rechkA.
stepz.
step. step.
asan_rechkA.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, Lc : rw_cells asegs mc bse _ |- _ =>
evt_done5; subst bse;
destruct (PE_INV_A_lvl_write HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m mc md A B ts0
cb nb pj sv errv l ST_eatws ST_array_after_sep _ _ CArr STC INV0 Hl MUc WMc MIc TOKc Lc Hmode ltac:(vm_compute; reflexivity) ltac:(unfold ST_eatws; lia) ltac:(unfold ST_array_after_sep; lia)
(or_introl eq_refl) ltac:(rewrite Hst; vm_compute; reflexivity)) as [INV3 PBK3];
eapply (Kbreak mc ST_array_after_sep _ _ _ ltac:(split; [exact C44 | reflexivity])); [exact INV3 | exact (PBK3 kP PBK)]
end end.
- step.
if_falsex.
step.
destruct (Z.eq_dec (bv_unsigned cb) 93) as [C93 | N93].
+ step.
if_truex.
assert (EK : exists kids, tl_cs l = Some (Sarr kids)) by (clear - CLS0; destruct (tl_cs l) as [[| | | |okids|kids]|]; try (exfalso; exact CLS0); eexists; reflexivity).
destruct EK as [kids Ecs].
step.
asan_chkM 1.
step.
step.
evt_done5. subst bse.
eapply (pe_shrink_cJ HIx GA GA_pres SHRINK (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m md A B ts0 l kids cb nb pj sv errv T kP nB);
[exact STC | exact BSL | exact INV0 | exact PBK | exact BK | exact Hl | exact Ecs | exact Hop | exact Hnbs0 | rewrite unsigned_lit by lia; reflexivity |].
intros m2 md2 A2 B2 cbs2 errv2 r w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 F2 fc2 INV2 PBK2 BK2 JX2 FS2 FRM2.
cbn [pf_spf] in *. unfold A_TP in *.

clear TOK SLOTS FF SHT4 SEP4c SEP4q SEP4i SHQ SHQ4 SHQ2 SHQ16 Ld MU WM MI Htal Htlo Hthi Hqal Hqlo Hqhi Hdtq Hqtk INtk INq INV0 PBK BK HbseR Hb8.
set (l2 := TL (tl_st l) (tl_ss l) (tl_cur l) (tl_cs l) cbs2 (tl_name l) (tl_nbs l)) in *.
set (ts2 := ts_lvl ts0 l2) in *.
assert (Hl2 : nth_error (t_levels ts2) (t_depth ts2) = Some l2) by (unfold ts2, ts_lvl, ts0; cbn [t_levels t_depth]; apply nth_error_lupd_eq; apply nth_error_Some; rewrite Hl; discriminate).
pose proof INV2 as INV2'. destruct INV2' as [CORE2 REST2].
destruct CORE2 as (_ & _ & _ & _ & TOK & _ & _ & TSK & FR).
pose proof REST2 as (HP & LV & _).
unfold ts2, ts_lvl, ts0 in TOK, TSK, LV. cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_tk pf_mxd pf_fl] in TOK, TSK, LV.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
unfold pe_frameA in FR. destruct FR as (SLOTS & _ & _ & FF & _). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS. unfold ff_cellsA in FF.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in SLOTS, FF.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts2)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * mxd) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts2)) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t2.
blk_factsA A4L HIx HP q (32 * mxd) Hqal Hqlo Hqhi Himg_q2.
pose proof (q_ne_tkA HIx _ _ _ _ _ _ _ _ _ _ HP) as Hqtk. cbn [pf_tk] in Hqtk.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ tk 72 q (32 * mxd) HP (in_or_app _ LM _ (or_introl INtk)) (in_or_app _ LM _ (or_introl INq)) ltac:(congruence)) as Hdtq.
pose proof (tok_shadowA HIx _ _ _ _ _ _ _ _ HP INtk) as SHT.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs m2) as WM.
pose proof (TSK depth l2 ltac:(apply nth_error_lupd_eq; apply nth_error_Some; rewrite Hl; discriminate)) as Ld. remember (q + 32 * Z.of_nat depth) as bse eqn:Hbse in Ld. unfold srec_cells in Ld. cbn [tl_st tl_ss tl_cur tl_name l2] in Ld.
assert (HbseR : q <= bse /\ bse + 32 <= q + (32 * mxd)) by (subst bse; lia).
pose proof (stack_shadowA HIx _ _ _ _ _ _ _ q mxd (Z.of_nat depth) 0 HP INq ltac:(lia) ltac:(lia)) as SHQ.
replace (q / 8 + 4 * Z.of_nat depth + 0 + A_SB) with (q / 8 + 4 * Z.of_nat depth + A_SB) in SHQ by lia.
assert (Hb8 : bse mod 8 = 0) by (subst bse; clear - Hqal; Z.div_mod_to_equations; lia).
assert (SHQ4 : ro_cells asegs m2 (bse / 8 + A_SB) [C1 (Z_to_bv 8 0)]).
{ replace (bse / 8) with (q / 8 + 4 * Z.of_nat depth) by (subst bse; rewrite div8_add_mul32 by lia; lia). exact SHQ. }
pose proof (munch_refl [(bse, bse + 32)] m2) as MU.
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
stash Himg_t2. stash Himg_q2. clear LV TSK.
reenterA asegs A4L HIx asegs_wx HP.
step.
asan_rechkA.
asan_rechkM 2.
step.
norm_sx32.
step.
rewrite (unsigned_lit (Z.of_nat depth)) by lia.
rewrite Z.shiftl_mul_pow2 by lia.
change (2 ^ 5) with 32.
step.
replace (q + Z.of_nat depth * 32) with bse by lia.
step. step. step.
sh_normO.
asan_rechkM 4.
step.
stepz.
asan_chkA.
stepz.
step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m2 mc, WMc : wmono asegs m2 mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, Lc : rw_cells asegs mc bse _ |- _ =>
evt_done5; subst bse;
destruct (PE_INV_A_lvl_write HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m2 mc md2 A2 B2 ts2
cb nb pj sv errv2 l2 ST_eatws ST_finish CArr false CAny STC INV2 Hl2 MUc WMc MIc TOKc Lc Hmode ltac:(vm_compute; reflexivity) ltac:(unfold ST_eatws; lia) ltac:(unfold ST_finish; lia)
(or_intror eq_refl) ltac:(cbn [tl_st l2]; rewrite Hst; vm_compute; reflexivity)) as [INV3 PBK3];
unfold ts2 in INV3, PBK3; rewrite ts_lvl_lvl in INV3, PBK3;
eapply (Kclose mc md2 A2 B2 cbs2 errv2 _ _ _ _ _ _ _ _ _ _ _ _ _ F2 fc2 kids C93 Ecs); [exact INV3 | exact (PBK3 kP PBK2) | exact (BK2 ST_eatws eq_refl) | exact JX2 | exact FS2 | exact FRM2]
end end.
+ step.
if_falsex.
step.
step.
asan_rechkA.
step. step.
evt_done5.
subst bse. eapply Kerr; [exact N44 | exact N93].
Qed.
End PeSAsepA.
End RC__1.
