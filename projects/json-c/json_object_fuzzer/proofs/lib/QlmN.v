(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup Lib.GwApply QWxq_c1 QRjH QHnV QCcH QfLs Q0Ek Qtgi QjDH Qsw7 QJjn QRUw QkMG QG8z Qdyh Q7UD Qhd4 Qwm6 QlKV QsKa Qiiq Q4v2 Q1Ey Ql4f Q1Y6 QrQv QEUF QW22 QdGy QYZ0 Qkko QnDr Qpfz Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QJjn QRUw.Mq0 QRUw QkMG. Import QG8z Qdyh.Mq3 Qdyh.Mq4.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa QsKa.Mq4 Qiiq.Mq0 QsKa.Mq6 Q4v2.Mq0 Q1Ey Ql4f.Mq1 Q1Y6.Mq2 QsKa.Mq8 QlKV.Mq5 QrQv.Mq2 QEUF QW22.Mq3 QdGy.Mq2 QYZ0.Mq3 Qkko.Mq0.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import QlKV.Mq2 QnDr.Mq3 Qpfz.Mq0.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section PeSArrayA.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_outside : forall m m' W, GA m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= hl_img_lo A4H \/ hl_img_hi A4H <= fst iv) W -> GA m'.
Hypothesis GA_pres : forall LB SP m m', heap_pres A4H LB SP m m' -> GA m -> GA m'.
Hypothesis MAPP : memappend_A_stmt2 HIx.
Hypothesis SHRINK : jo_array_shrink_A2J HIx.
Hypothesis PUT : put_stmt_A HIx.

Ltac pe_openA STC INV :=
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR); pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk);
destruct INV as [CORE REST];
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR);
pose proof REST as (HP & LV & OBJ & ST & ERR & STR & PLEN & SBin & HPR & MDV & G & BUD).

Lemma seg_array_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP : Z) (nB : nat)
(gp t0 t1 t2 a3 a5 a6 a7 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> pf_fl pf = 0 -> 0 <= pa_bslack pa ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv -> PBOK m ts kP -> BOK pf pa ts B (S (Z.to_nat 512 + nB)) ->
nth_error (t_levels ts) (t_depth ts) = Some l -> (tl_st l = ST_array \/ tl_st l = ST_array_after_sep) ->

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

(forall m' md' A' B' errv' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' F' fc',
bv_unsigned cb <> 93 -> (S (t_depth ts) < Z.to_nat (pf_mxd pf))%nat ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B'
(ts_push ts (TL ST_array_add (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) cb nb pj sv errv' ->
PBOK m' (ts_push ts (TL ST_array_add (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) kP ->
BOK pf pa (ts_push ts (TL ST_array_add (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) B' nB ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msA asegs pf pa APE_REDO (t_co ts) gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5'
(Z_to_bv 64 (pf_tk pf + 56)) (Z_to_bv 64 (pa_F pa + 64)) F' fc' m')) ->

(forall a1' a3' a4',
bv_unsigned cb <> 93 -> (Z.to_nat (pf_mxd pf) <= S (t_depth ts))%nat ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa APE_ERRST (t_co ts) gp t0 t1 t2 (Z_to_bv 64 2) a1'
(Z_to_bv 64 (q / 8 + 4 * Z.of_nat (t_depth ts) + A_SB)) a3' a4' a5 a6 a7
(Z_to_bv 64 (Z.of_nat (t_depth ts))) (Z_to_bv 64 q) (Z_to_bv 64 (pa_F pa + 64)) F fc m)) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa (pe_jtA (tl_st l)) (t_co ts) gp t0 t1 t2
(Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) (Z_to_bv 64 (tl_st l))
(Z_to_bv 64 (q / 8 + 4 * Z.of_nat (t_depth ts) + A_SB)) a3 (Z_to_bv 64 APE_JTAB) a5 a6 a7
(Z_to_bv 64 (Z.of_nat (t_depth ts))) (Z_to_bv 64 q) (Z_to_bv 64 (pa_F pa + 64)) F fc m).
Proof.
intros until fc. intros STC Hfl BSL INV PBK BK Hl Hst Kclose Kredo Kerr. pose proof INV as INV0. pe_openA STC INV.
assert (PCE : pe_jtA (tl_st l) = 0x93694) by (destruct Hst as [E|E]; rewrite E; reflexivity). rewrite PCE. clear PCE.
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *. subst fl.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
pose proof FR as FR0. unfold pe_frameA in FR. destruct FR as (SLOTS & GAP & SAVED & FF & FSH).
unfold pe_slotsA in SLOTS. cbn zeta in SLOTS. unfold ff_cellsA in FF.
unfold pe_msA in *.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd 0) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * mxd) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd 0) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
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
unfold APE_BREAK, APE_REDO, APE_ERRST, APE_JTAB in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
destruct (lvl_mode_array _ _ _ _ Hst SS26 Hmode) as (Ec0 & Ehn0 & Hop). subst c0 hn0.
pose proof NM0 as NM0'. cbn [name_ok] in NM0. destruct NM0 as [Hn0 Hnbs0].
pose proof (stack_shadowA HIx _ _ _ _ _ _ _ q mxd (Z.of_nat depth) 2 HP INq ltac:(lia) ltac:(lia)) as SHQ2.
assert (SHQ16 : ro_cells asegs m (bse / 8 + 2147450882) [C1 (Z_to_bv 8 0)]).
{ replace (bse / 8 + 2147450882) with (q / 8 + 4 * Z.of_nat depth + 2 + A_SB) by (subst bse; rewrite div8_add_mul32 by lia; unfold A_SB; lia). exact SHQ2. }
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 2 HP INtk ltac:(lia)) as SHT2.
replace (tk / 8 + 2 + A_SB) with (tk / 8 + 2147450882) in SHT2 by (unfold A_SB; lia).
stash Himg_t. stash Himg_q. clear PB REST TSK HP LV OBJ HPR BUD GAP SAVED FSH.
reenterA asegs A4L HIx asegs_wx HP.
replace (q + 32 * Z.of_nat depth) with bse by lia.
step.
change (zxb cb) with (Z_to_bv 64 (bv_unsigned cb)).
step.
destruct (Z.eq_dec (bv_unsigned cb) 93) as [C93 | N93].
- step.
if_falsex.
step.
assert (EK : exists kids, tl_cs l = Some (Sarr kids)) by (clear - CLS0; destruct (tl_cs l) as [[| | | |okids|kids]|]; try (exfalso; exact CLS0); eexists; reflexivity).
destruct EK as [kids Ecs].
step.
asan_chkM 1.
step.
step.
evt_done5. subst bse.
eapply (pe_shrink_cJ HIx GA GA_pres SHRINK (PEF tk oldl newl len lenr sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m md A B ts0 l kids cb nb pj sv errv T kP nB);
[exact STC | exact BSL | exact INV0 | exact PBK | exact (BOK_drop _ _ _ _ _ _ BK) | exact Hl | exact Ecs | exact Hop | exact Hnbs0 | rewrite unsigned_lit by lia; reflexivity |].
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
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd 0) q LB0 ts2)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * mxd) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd 0) q LB0 ts2)) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
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
pose proof (tok_flags_byteA mxd 0 m2 tk pb (Z.of_nat depth) q (TS isd stpos (Z_to_bv 64 co) err ucs high quote) TOK) as RDF.
reenterA asegs A4L HIx asegs_wx HP.
step.
asan_rechkA.
asan_rechkM 3.
step.
norm_sx32.
step.
rewrite (unsigned_lit (Z.of_nat depth)) by lia.
rewrite Z.shiftl_mul_pow2 by lia.
change (2 ^ 5) with 32.
step.
replace (q + Z.of_nat depth * 32) with bse by lia.
asan_chkM 3.
step.
norm_sx32.
step.

lazymatch goal with |- evt _ _ (MS ?R ?FF _ ?fcc None ?mm ?rom) =>
assert (CLOSE : forall a1x a3x, evt asegs (AJ5e A4L HIx A2 T md2) (MS (bvmap_set 11 a1x (bvmap_set 13 a3x R)) FF (Z_to_bv 64 0x95e04) fcc None mm rom)) end.
{ intros a1x a3x. clear SHT RDF.
step.
asan_chkA.
step.
stepz.
asan_rechkA.
stepz.
step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m2 mc, WMc : wmono asegs m2 mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, Lc : rw_cells asegs mc bse _ |- _ =>
evt_done5; subst bse;
destruct (PE_INV_A_lvl_write HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m2 mc md2 A2 B2 ts2
cb nb pj sv errv2 l2 ST_eatws ST_finish CArr false CAny STC INV2 Hl2 MUc WMc MIc TOKc Lc Hmode ltac:(vm_compute; reflexivity) ltac:(unfold ST_eatws; lia) ltac:(unfold ST_finish; lia)
(or_intror eq_refl) ltac:(cbn [tl_st l2]; destruct Hst as [E|E]; rewrite E; vm_compute; reflexivity)) as [INV3 PBK3];
unfold ts2 in INV3, PBK3; rewrite ts_lvl_lvl in INV3, PBK3;
eapply (Kclose mc md2 A2 B2 cbs2 errv2 _ _ _ _ _ _ _ _ _ _ _ _ _ F2 fc2 kids C93 Ecs); [exact INV3 | exact (PBK3 kP PBK2) | exact (BK2 ST_eatws eq_refl) | exact JX2 | exact FS2 | exact FRM2]
end end. }
step.
destruct Hst as [E|E]; rewrite E; [unfold ST_array | unfold ST_array_after_sep].
+ if_true. apply CLOSE.
+ if_false.
asan_rechkA.
step.
rewrite ?zxb_zero.
step.
step.
if_true. apply CLOSE.
- step.
if_truex.
step.
asan_chkA.
step.
norm_sx32.
step.
norm_w32.
destruct (Nat.lt_ge_cases (S depth) (Z.to_nat mxd)) as [Dlt | Dge].
+ step.
if_truex.
evt_done5. subst bse.
eapply (seg_push_arr_A HIx GA GA_outside GA_pres PUT (PEF tk oldl newl len lenr sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m md A B ts0 l
cb nb pj sv errv T kP nB);
[exact STC | exact BSL | exact INV0 | exact PBK | exact BK | exact Hl | exact Hst | exact Dlt |].
intros until fc'. intros INV' PBK' BK' FS' FRM'. eapply (Kredo _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ N93 Dlt); eauto.
+ step.
if_falsex.
step.
step.
asan_rechkA.
step. step.
evt_done5.
subst bse. eapply Kerr; [exact N93 | exact Dge].
Qed.

Lemma seg_oval_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP : Z) (nB : nat)
(gp t0 t1 t2 a3 a5 a6 a7 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> pf_fl pf = 0 -> 0 <= pa_bslack pa ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv -> PBOK m ts kP -> BOK pf pa ts B (S (Z.to_nat 512 + nB)) ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_ovalue ->

(forall m' md' A' B' errv' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' F' fc',
(S (t_depth ts) < Z.to_nat (pf_mxd pf))%nat ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B'
(ts_push ts (TL ST_ovadd (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) cb nb pj sv errv' ->
PBOK m' (ts_push ts (TL ST_ovadd (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) kP ->
BOK pf pa (ts_push ts (TL ST_ovadd (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) B' nB ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msA asegs pf pa APE_REDO (t_co ts) gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5'
(Z_to_bv 64 (pf_tk pf + 56)) (Z_to_bv 64 (pa_F pa + 64)) F' fc' m')) ->

(forall a1' a4',
(Z.to_nat (pf_mxd pf) <= S (t_depth ts))%nat ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa APE_ERRST (t_co ts) gp t0 t1 t2 (Z_to_bv 64 2) a1'
(Z_to_bv 64 (q / 8 + 4 * Z.of_nat (t_depth ts) + A_SB)) a3 a4' a5 a6 a7
(Z_to_bv 64 (Z.of_nat (t_depth ts))) (Z_to_bv 64 q) (Z_to_bv 64 (pa_F pa + 64)) F fc m)) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa (pe_jtA ST_ovalue) (t_co ts) gp t0 t1 t2
(Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) (Z_to_bv 64 (tl_st l))
(Z_to_bv 64 (q / 8 + 4 * Z.of_nat (t_depth ts) + A_SB)) a3 (Z_to_bv 64 APE_JTAB) a5 a6 a7
(Z_to_bv 64 (Z.of_nat (t_depth ts))) (Z_to_bv 64 q) (Z_to_bv 64 (pa_F pa + 64)) F fc m).
Proof.
intros until fc. intros STC Hfl BSL INV PBK BK Hl Hst Kredo Kerr. pose proof INV as INV0. pe_openA STC INV.
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *. subst fl.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
pose proof FR as FR0. unfold pe_frameA in FR. destruct FR as (SLOTS & GAP & SAVED & FF & FSH).
unfold pe_slotsA in SLOTS. cbn zeta in SLOTS. unfold ff_cellsA in FF.
unfold pe_msA in *.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd 0) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * mxd) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd 0) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
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
unfold APE_BREAK, APE_REDO, APE_ERRST, APE_JTAB in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
pose proof Hmode as Hmode'. rewrite Hst in Hmode'. destruct (lvl_mode_ovalue _ _ _ SS26 Hmode') as (Ec0 & Ehn0 & Hop). subst c0 hn0. clear Hmode'.
pose proof (stack_shadowA HIx _ _ _ _ _ _ _ q mxd (Z.of_nat depth) 2 HP INq ltac:(lia) ltac:(lia)) as SHQ2.
assert (SHQ16 : ro_cells asegs m (bse / 8 + 2147450882) [C1 (Z_to_bv 8 0)]).
{ replace (bse / 8 + 2147450882) with (q / 8 + 4 * Z.of_nat depth + 2 + A_SB) by (subst bse; rewrite div8_add_mul32 by lia; unfold A_SB; lia). exact SHQ2. }
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 2 HP INtk ltac:(lia)) as SHT2.
replace (tk / 8 + 2 + A_SB) with (tk / 8 + 2147450882) in SHT2 by (unfold A_SB; lia).
stash Himg_t. stash Himg_q. clear PB REST TSK HP LV OBJ HPR BUD GAP SAVED FSH.
reenterA asegs A4L HIx asegs_wx HP. unfold ST_ovalue. cbn [pe_jtA].
replace (q + 32 * Z.of_nat depth) with bse by lia.
step.
asan_chkA.
step.
norm_sx32.
step.
norm_w32.
destruct (Nat.lt_ge_cases (S depth) (Z.to_nat mxd)) as [Dlt | Dge].
- step.
if_truex.
evt_done5. subst bse.
eapply (seg_push_ov_A HIx GA GA_outside GA_pres PUT (PEF tk oldl newl len lenr sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m md A B ts0 l
cb nb pj sv errv T kP nB);
[exact STC | exact BSL | exact INV0 | exact PBK | exact BK | exact Hl | exact Hst | exact Dlt |].
intros until fc'. intros INV' PBK' BK' FS' FRM'. eapply (Kredo _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Dlt); eauto.
- step.
if_falsex.
step.
step.
asan_rechkA.
step. step.
evt_done5.
subst bse. eapply Kerr; exact Dge.
Qed.
End PeSArrayA.
End RC__1.
End Mq0.
From Stdlib Require Permutation.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QIsM Qa8x.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QJjn QRUw.Mq0 QRUw QkMG. Import QG8z Qdyh.Mq0 Qdyh.Mq3 Qdyh.Mq4 QIsM.Mq2 Qa8x.Mq2.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa QsKa.Mq4 Qiiq.Mq0 QsKa.Mq6 Q4v2.Mq0 QlKV.Mq5 Q1Ey Ql4f.Mq1 Q1Y6.Mq2 QsKa.Mq8 QrQv.Mq2 QEUF QW22.Mq3 QdGy.Mq2 QYZ0.Mq3 Qkko.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section PeSSescQA.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_outside : forall m m' W, GA m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= hl_img_lo A4H \/ hl_img_hi A4H <= fst iv) W -> GA m'.
Hypothesis GA_pres : forall LB SP m m', heap_pres A4H LB SP m m' -> GA m -> GA m'.
Hypothesis MAPP : memappend_A_stmt2 HIx.

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

Ltac reopen_inv INVx TSx ts0 PF q LB0 tk mxd depth l Hl bse Hbse mX :=
pose proof INVx as [CORE2 REST2];
destruct CORE2 as (_ & _ & _ & _ & TOK & _ & _ & TSK & FR);
pose proof REST2 as (HP & _); clear REST2;
try unfold TSx in TOK, TSK; try unfold ts_pbs, ts_lvl, ts_set_x in TOK, TSK; try unfold ts0 in TOK, TSK;
cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_tk pf_mxd pf_fl] in TOK, TSK;
unfold tok_cells_g in TOK; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK;
unfold pe_frameA in FR; destruct FR as (SLOTS & _ & _ & _ & _); unfold pe_slotsA in SLOTS; cbn zeta in SLOTS;
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in SLOTS;
assert (INtk : In (tk, 72) (pe_blocksA PF q LB0 TSx)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity);
assert (INq : In (q, 32 * mxd) (pe_blocksA PF q LB0 TSx)) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity);
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI;
pose proof (wmono_refl asegs mX) as WM;
pose proof (TSK depth l Hl) as Ld; rewrite <- Hbse in Ld; unfold srec_cells in Ld;
clear TSK.

Lemma pe_memappend_cK :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP : Z)
(ra gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
PBOK m ts kP -> kP + 1 <= 1 -> forall kB : nat, BOK pf pa ts B kB -> bv_unsigned ra mod 2 = 0 ->
(forall m2 md2 A2 B2 pbs2 errv2 r (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : word) F2 fc2,
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m2 md2 A2 B2 (ts_pbs ts pbs2) cb nb pj sv errv2 ->
(r = 1 /\ PBOK m2 (ts_pbs ts pbs2) (kP + 1) /\ BOK pf pa (ts_pbs ts pbs2) B2 kB) \/ (r = 2^64 - 1 /\ pbs2 = t_pbs ts) ->
fsaved F F2 -> (frm0 fc -> frm0 fc2) ->
AJ5 A4L HIx A2 T md2
(MS (mkR ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) w0 w1 w2 s0 s1 (Z_to_bv 64 r) w3 w4 w5 w6 w7 w8 w9
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 w10 w11 w12 w13) F2 (ret_pc ra) fc2 None m2 (seg_rom asegs))) ->
AJ5 A4L HIx A T md
(MS (mkR ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2 s0 s1 (Z_to_bv 64 (t_pb ts)) (Z_to_bv 64 (pa_F pa + 64)) (Z_to_bv 64 1) a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x9a0ac) fc None m (seg_rom asegs)).
Proof.
intros until fc. intros STC BSL INV PBK HkP kB BK RA K.
pose proof STC as (_ & _ & GEO & _). pose proof GEO as (_ & _ & _ & GF & GF0 & _).
pose proof INV as [(_ & _ & _ & _ & _ & _ & _ & _ & FR1) _].
eapply (pe_memappend_g HIx GA GA_pres MAPP pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv T (pa_F pa + 64) 1 (t_co ts + kP) [cb]);
[exact STC | exact BSL | exact INV | exact PBK | lia | lia | exact BK | exact RA
| exact (pe_frameA_cbyte _ _ _ _ _ _ _ FR1) | reflexivity | lia
| right; first [left | idtac]; exists (pa_F pa), 2; split; [left; reflexivity | rewrite fr_size_2; lia]
| intros _; exact (pe_frameA_c_unpoisoned _ _ _ _ _ _ _ GEO FR1) |].
intros m2 md2 A2 B2 pbs2 errv2 r w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 F2 fc2 INV2 OUT2 FS2 FRM2.
eapply (K m2 md2 A2 B2 pbs2 errv2 r); [exact INV2 | | exact FS2 | exact FRM2].
destruct OUT2 as [(-> & PBK2 & BK2) | [-> E]]; [left | right; split; [reflexivity | exact E]].
split; [reflexivity|]. split; [| exact BK2]. unfold PBOK, ts_pbs. cbn [t_co]. replace (t_co ts + (kP + 1)) with (t_co ts + kP + 1) by lia. exact PBK2.
Qed.

Lemma sesc_quote_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP : Z) (nB : nat)
(gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s10 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv -> PBOK m ts kP -> kP + 1 <= 1 -> BOK pf pa ts B (S nB) ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_string_escape ->
(forall c hn, lvl_mode (tl_st l) (tl_ss l) = Some (c, hn) -> lvl_mode (tl_ss l) (tl_ss l) = Some (c, hn)) ->
zin (tl_ss l) [ST_array_add; ST_ovadd] = false ->
(forall m' md' A' B' pbs' errv' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' F' fc',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B'
(ts_lvl (ts_pbs ts pbs') (TL (tl_ss l) (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) cb nb pj sv errv' ->
PBOK m' (ts_lvl (ts_pbs ts pbs') (TL (tl_ss l) (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) (kP + 1) ->
BOK pf pa (ts_lvl (ts_pbs ts pbs') (TL (tl_ss l) (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) B' nB ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msA asegs pf pa APE_BREAK (t_co ts) gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5'
(Z_to_bv 64 (pf_tk pf + 56)) (Z_to_bv 64 (pa_F pa + 64)) F' fc' m')) ->
(forall m' md' A' B' errv' x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s5' t3' t4' t5' t6' F' fc',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' ts cb nb pj sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(Q1Y6.Mq2.pe_msE pf pa APE_ERR2 x1' gp' t0' t1' t2' (Z_to_bv 64 16) a1' a2' a3' a4' a5' a6' a7'
(Z_to_bv 64 (pf_tk pf / 8 + SB2)) (Z_to_bv 64 (pf_tk pf + 20)) s5' (Z_to_bv 64 (pf_tk pf + 36)) (Z_to_bv 64 (pf_tk pf + 32)) (Z_to_bv 64 (pa_F pa))
(Z_to_bv 64 (pf_tk pf + 56)) (Z_to_bv 64 (pf_sb pf + t_co ts)) t3' t4' t5' t6' F' fc' m')) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa 0x96d2c (t_co ts) gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s10 (Z_to_bv 64 (pa_F pa + 64)) F fc m).
Proof.
intros until fc. intros STC BSL INV PBK HkP BK Hl Hst HMODE Hzss Kbreak Kerr16. pose proof INV as INV0. pe_openA STC INV.
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
pose proof FR as FR0. unfold pe_frameA in FR. destruct FR as (SLOTS & GAP & SAVED & FF & FSH).
unfold pe_slotsA in SLOTS. cbn zeta in SLOTS. unfold ff_cellsA in FF.
unfold pe_msA, Q1Y6.Mq2.pe_msE in *.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * mxd) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t.
blk_factsA A4L HIx HP q (32 * mxd) Hqal Hqlo Hqhi Himg_q.
pose proof (q_ne_tkA HIx _ _ _ _ _ _ _ _ _ _ HP) as Hqtk. cbn [pf_tk] in Hqtk.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ tk 72 q (32 * mxd) HP (in_or_app _ LM _ (or_introl INtk)) (in_or_app _ LM _ (or_introl INq)) ltac:(congruence)) as Hdtq.
pose proof (tok_shadowA HIx _ _ _ _ _ _ _ _ HP INtk) as SHT.
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
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 1 HP INtk ltac:(lia)) as SHT1.
replace (tk / 8 + 1 + A_SB) with (tk / 8 + 2147450881) in SHT1 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 1 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT1c & SEPT1q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 1 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT1t & _).
cbn [hl_sb A4L] in SEPT1c, SEPT1q, SEPT1t. assert (EQx : tk / 8 + A_SB + 1 = tk / 8 + 2147450881) by (unfold A_SB; lia). rewrite EQx in SEPT1c, SEPT1q, SEPT1t. clear EQx.
unfold APE_BREAK, APE_ERR2, APE_REDO, APE_OUT, APE_ERRMEM, APE_ERRST, APE_JTAB in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
clear Hdtq SEPT1c SEPT1q SEPT1t.
stash Himg_t. stash Himg_q. stash Kbreak. stash Kerr16. clear PB REST TSK LV OBJ HPR BUD GAP SAVED FSH FF STR ERR SBin SHT SHQ SHQ4 Ld MU.
reenterA asegs A4L HIx asegs_wx HP.
step.
asan_chkA.
step.
step. step.
step.
evt_done5.
eapply (pe_memappend_cK (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m md A B ts0 cb nb pj sv errv T kP);
[exact STC | exact BSL | exact INV0 | exact PBK | exact HkP | exact BK | rewrite unsigned_lit by lia; reflexivity |].
intros mp2 md2 A2 B2 pbs2 errv2 r w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 F2 fc2 INV2 OUT2 FS2 FRM2.
cbn [pf_spf] in *. unfold A_TP in *.
clear TOK SLOTS SHT1 WM MI HP INtk INq Htal Htlo Hthi Hqal Hqlo Hqhi Hqtk INV0 PBK BK.
set (ts2 := ts_pbs ts0 pbs2) in *.
reopen_inv INV2 ts2 ts0 (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 tk mxd depth l Hl bse Hbse mp2.
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t2.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 4 HP INtk ltac:(lia)) as SHT4.
replace (tk / 8 + 4 + A_SB) with (tk / 8 + 2147450884) in SHT4 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 4 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT4c & SEPT4q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 4 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT4t & _).
cbn [hl_sb A4L] in SEPT4c, SEPT4q, SEPT4t. assert (EQx : tk / 8 + A_SB + 4 = tk / 8 + 2147450884) by (unfold A_SB; lia). rewrite EQx in SEPT4c, SEPT4q, SEPT4t. clear EQx.
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
clear SEPT4c SEPT4q SEPT4t Ld.
stash Himg_t2.
try lazymatch goal with |- AJ5 _ _ _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) => replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
reenterA asegs A4L HIx asegs_wx HP.
step.
destruct OUT2 as [(-> & PBK2 & BK2) | [-> Epbs2]].
- step.
if_true.
evt_done5.
assert (Hl2 : nth_error (t_levels ts2) (t_depth ts2) = Some l) by (unfold ts2, ts_pbs, ts0; cbn [t_levels t_depth]; exact Hl).
eapply (sesc_joinq_A HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo mp2 md2 A2 B2 ts2 l cb nb pj sv errv2 T (kP + 1));
[exact STC | exact INV2 | exact PBK2 | exact Hl2 | exact Hst | exact HMODE | exact Hzss |].
intros m' a0' a1' a2' a3' INV3 PBK3. unstash Kbreak.
eapply (Kbreak m' md2 A2 B2 pbs2 errv2); [exact INV3 | exact PBK3 | | exact FS2 | exact FRM2].
apply (BOK_lvl_restate (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) ts2 B2 nB l (tl_ss l) (tl_ss l) Hl2); [| eapply BOK_weaken; [| exact BK2]; lia].
intros CL. unfold lvl_closed in *. cbn [tl_st tl_ss]. apply andb_true_iff in CL as [CL _]. rewrite CL, Hzss. reflexivity.
- replace (Z_to_bv 64 (2^64 - 1)) with (Z_to_bv 64 (-1)) by (apply bv_eq; vm_compute; reflexivity).
step.
if_false.
step.
step.
asan_rechkA.
step.
evt_done5.
unstash Kerr16. eapply (Kerr16 mp2 md2 A2 B2 errv2); [| exact FS2 | exact FRM2].
unfold ts2 in INV2. rewrite Epbs2 in INV2. exact INV2.
Qed.

Lemma sesc_u_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP : Z)
(gp t0 t1 t2 a1 a3 a4 a5 a6 a7 s10 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv -> PBOK m ts kP ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_string_escape ->
(forall c hn, lvl_mode (tl_st l) (tl_ss l) = Some (c, hn) -> lvl_mode ST_escape_unicode (tl_ss l) = Some (c, hn)) ->

(forall m' a0' a1' a2' a3' a4',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md A B
(ts_lvl (ts_set_x ts (t_co ts) (TS (ts_isd (t_x ts)) (Z_to_bv 64 0) (ts_choff (t_x ts)) (ts_err (t_x ts)) (Z_to_bv 64 0) (ts_high (t_x ts)) (ts_quote (t_x ts)))) (TL ST_escape_unicode (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) cb nb pj sv errv ->
PBOK m' (ts_lvl (ts_set_x ts (t_co ts) (TS (ts_isd (t_x ts)) (Z_to_bv 64 0) (ts_choff (t_x ts)) (ts_err (t_x ts)) (Z_to_bv 64 0) (ts_high (t_x ts)) (ts_quote (t_x ts)))) (TL ST_escape_unicode (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) kP ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa APE_BREAK (t_co ts) gp t0 t1 t2 a0' a1' a2' a3' a4' a5 a6 a7 (Z_to_bv 64 (Z.of_nat (t_depth ts)))
(Z_to_bv 64 (pf_tk pf + 56)) (Z_to_bv 64 (pa_F pa + 64)) F fc m')) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa 0x96edc (t_co ts) gp t0 t1 t2 (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) a1
(Z_to_bv 64 (q / 8 + 4 * Z.of_nat (t_depth ts) + A_SB)) a3 a4 a5 a6 a7 (Z_to_bv 64 (Z.of_nat (t_depth ts))) s10 (Z_to_bv 64 (pa_F pa + 64)) F fc m).
Proof.
intros until fc. intros STC INV PBK Hl Hst HMODE10 Kbreak. pose proof INV as INV0. pe_openA STC INV.
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
pose proof (tok_shadowA HIx _ _ _ _ _ _ _ _ HP INtk) as SHT.
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
shq_facts HP INq INtk q mxd tk (Z.of_nat depth) 0 SHQ0 SEPQ0c SEPQ0q SEPQ0t.
replace (q / 8 + 4 * (Z.of_nat depth) + 0 + A_SB) with (bse / 8 + 2147450880) in SHQ0 by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia).
assert (EQx : q / 8 + A_SB + (4 * (Z.of_nat depth) + 0) = bse / 8 + 2147450880) by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia). rewrite EQx in SEPQ0c, SEPQ0q, SEPQ0t. clear EQx.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 5 HP INtk ltac:(lia)) as SHT5.
replace (tk / 8 + 5 + A_SB) with (tk / 8 + 2147450885) in SHT5 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 5 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT5c & SEPT5q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 5 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT5t & _).
cbn [hl_sb A4L] in SEPT5c, SEPT5q, SEPT5t. assert (EQx : tk / 8 + A_SB + 5 = tk / 8 + 2147450885) by (unfold A_SB; lia). rewrite EQx in SEPT5c, SEPT5q, SEPT5t. clear EQx.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 3 HP INtk ltac:(lia)) as SHT3.
replace (tk / 8 + 3 + A_SB) with (tk / 8 + 2147450883) in SHT3 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 3 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT3c & SEPT3q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 3 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT3t & _).
cbn [hl_sb A4L] in SEPT3c, SEPT3q, SEPT3t. assert (EQx : tk / 8 + A_SB + 3 = tk / 8 + 2147450883) by (unfold A_SB; lia). rewrite EQx in SEPT3c, SEPT3q, SEPT3t. clear EQx.
unfold APE_BREAK, APE_REDO, APE_OUT, APE_ERRMEM, APE_ERRST, APE_JTAB in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
assert (cs_tk_L : csep tk 72 bse (Z.of_nat 32)) by (unfold csep; clear - Hdtq HbseR; lia).
assert (cs_L_tk : csep bse 32 tk (Z.of_nat 72)) by (unfold csep; clear - Hdtq HbseR; lia).
assert (cs_T3_T : csep (tk / 8 + 2147450883) 1 tk (Z.of_nat 72)) by (unfold csep; clear - SEPT3t; lia).
assert (cs_Q0_T : csep (bse / 8 + 2147450880) 1 tk (Z.of_nat 72)) by (unfold csep; clear - SEPQ0t; lia).
clear Hdtq SEPQ0c SEPQ0q SEPQ0t SEPT5c SEPT5q SEPT5t SEPT3c SEPT3q SEPT3t.
stash Himg_t. stash Himg_q. stash Kbreak. clear PB REST TSK LV OBJ HPR BUD GAP SAVED FSH FF STR ERR SBin SHT SHQ SHQ4 MU.
pose proof (munch_refl [(tk, tk + 72)] m) as MU.
reenterA asegs A4L HIx asegs_wx HP.
replace (q + 32 * Z.of_nat depth) with bse by lia.
step.
asan_chkA.
stepz.
step.
asan_chkM 1.
stepz.
replace (q / 8 + 4 * Z.of_nat depth + 2147450880) with (bse / 8 + 2147450880) by (rewrite Hbse, div8_add_mul32 by lia; lia).
asan_rechkA.
step. step.
set (x3 := TS isd (Z_to_bv 64 0) (Z_to_bv 64 co) err (Z_to_bv 64 0) high quote).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _ |- _ =>
destruct (PE_INV_A_tokw1 HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m mc md A B ts0
cb nb pj sv errv co x3 STC INV0 MUc WMc MIc TOKc ltac:(cbn [pf_len]; lia) eq_refl) as [INV3 PBT3];
clear MUc WMc; pose proof (munch_refl [(bse, bse + 32)] mc) as MUl; pose proof (wmono_refl asegs mc) as WMl
end end.
set (ts3 := ts_set_x ts0 co x3) in *.
stepz.
assert (Hl3 : nth_error (t_levels ts3) (t_depth ts3) = Some l) by exact Hl.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mcF _) =>
lazymatch goal with MUc : munch _ ?mb mcF, WMc : wmono asegs ?mb mcF, MIc : mem_inv asegs mcF, TOKc : rw_cells asegs mcF tk _, Lc : rw_cells asegs mcF bse _ |- _ =>
evt_done5; rewrite Hbse in MUc, Lc;
destruct (PE_INV_A_lvl_write HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo mb mcF md A B ts3
cb nb pj sv errv l ST_escape_unicode (tl_ss l) c0 hn0 c0 STC INV3 Hl3 MUc WMc MIc TOKc Lc Hmode (HMODE10 c0 hn0 Hmode) ltac:(unfold ST_escape_unicode; lia) SS26 (or_introl eq_refl)
ltac:(rewrite Hst; reflexivity)) as [INV4 PBK4];
unstash Kbreak; eapply (Kbreak mcF); [exact INV4 | apply PBK4; unfold PBOK; cbn [t_co ts3 ts_set_x]; apply PBT3; exact PBK]
end end.
Qed.
End PeSSescQA.
End RC__1.
End Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI QSHS Qc5u QAzu Q6vt QZUC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QJjn QRUw.Mq0 QRUw QkMG. Import QG8z Qdyh.Mq3 Qdyh.Mq4.
Import Qhd4 Qwm6.
Import QbFI.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqj QsKa.Mqd Qiiq QsKa.Mqf Q4v2 QSHS Ql4f.Mq4 Q1Y6.Mq4 QsKa.Mqh QlKV.Mqf QrQv.Mq4 QEUF.Mq2 QW22.Mq8 QdGy.Mq9 QYZ0.Mq8 Qkko.Mq2.
Import Qc5u QAzu.Mq0 Q6vt QZUC.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import QlKV.Mq2.
Import QnDr.Mq6 Qpfz.Mq2.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section PeSArrayB.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_outside : forall m m' W, GA m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= hl_img_lo A4H \/ hl_img_hi A4H <= fst iv) W -> GA m'.
Hypothesis GA_pres : forall LB SP m m', heap_pres A4H LB SP m m' -> GA m -> GA m'.
Hypothesis MAPP : memappend_A_stmt2 HIx.
Hypothesis SHRINK : jo_array_shrink_A2J HIx.
Hypothesis PUT : put_stmt_A HIx.

Ltac pe_openA STC INV :=
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR); pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk);
destruct INV as [CORE REST];
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR);
pose proof REST as (HP & LV & OBJ & ST & ERR & STR & PLEN & SBin & HPR & MDV & G & BUD).

Lemma seg_array_B :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP : Z) (nB : nat)
(gp t0 a5 a7 s3 s6 s7 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> pf_fl pf = 0 -> 0 <= pa_bslack pa ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv -> PBOK m ts kP -> BOK pf pa ts B (S (Z.to_nat 512 + nB)) ->
nth_error (t_levels ts) (t_depth ts) = Some l -> (tl_st l = ST_array \/ tl_st l = ST_array_after_sep) ->

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

(forall m' md' A' B' errv' gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc',
bv_unsigned cb <> 93 -> (S (t_depth ts) < Z.to_nat (pf_mxd pf))%nat ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B'
(ts_push ts (TL ST_array_add (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) cb nb pj sv errv' ->
PBOK m' (ts_push ts (TL ST_array_add (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) kP ->
BOK pf pa (ts_push ts (TL ST_array_add (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) B' nB ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msA asegs pf pa APE_REDO (t_co ts) gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' m')) ->

(forall a1' a5' a6',
bv_unsigned cb <> 93 -> (Z.to_nat (pf_mxd pf) <= S (t_depth ts))%nat ->
AJ5 A4L HIx A T md
(pe_msO asegs pf pa APE_ERR2 gp t0 (Z_to_bv 64 (pf_lenr pf)) (Z_to_bv 64 (pf_tk pf + 32)) (Z_to_bv 64 2) a1' (Z_to_bv 64 0) (Z_to_bv 64 (q / 8 + 4 * Z.of_nat (t_depth ts) + A_SB)) (Z_to_bv 64 0) a5' a6' a7 s3 (Z_to_bv 64 (pf_sb pf + t_co ts)) (Z_to_bv 64 q) s6 s7 (Z_to_bv 64 (Z.of_nat (t_depth ts))) s9 s11 t3 t4 t5 t6 F fc m)) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa (pe_jtA (tl_st l)) (t_co ts) gp t0 (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) (Z_to_bv 64 (tl_st l)) (Z_to_bv 64 0) (Z_to_bv 64 (q / 8 + 4 * Z.of_nat (t_depth ts) + A_SB)) (Z_to_bv 64 0) a5 (Z_to_bv 64 APE_JTAB) a7 s3 (Z_to_bv 64 q) s6 s7 (Z_to_bv 64 (Z.of_nat (t_depth ts))) s9 s11 t3 t4 t5 t6 F fc m).
Proof.
intros until fc. intros STC Hfl BSL INV PBK BK Hl Hst Kclose Kredo Kerr. pose proof INV as INV0. pe_openA STC INV.
assert (PCE : pe_jtA (tl_st l) = 0x94088) by (destruct Hst as [E|E]; rewrite E; reflexivity). rewrite PCE. clear PCE.
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *. subst fl.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
pose proof FR as FR0. unfold pe_frameA in FR. destruct FR as (SLOTS & GAP & SAVED & FF & FSH).
unfold pe_slotsA in SLOTS. cbn zeta in SLOTS. unfold ff_cellsA in FF.
unfold pe_msA, pe_msO in *.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd 0) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * mxd) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd 0) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
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
unfold APE_BREAK, APE_REDO, APE_ERR2, APE_JTAB in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
destruct (lvl_mode_array _ _ _ _ Hst SS26 Hmode) as (Ec0 & Ehn0 & Hop). subst c0 hn0.
pose proof NM0 as NM0'. cbn [name_ok] in NM0. destruct NM0 as [Hn0 Hnbs0].
pose proof (stack_shadowA HIx _ _ _ _ _ _ _ q mxd (Z.of_nat depth) 2 HP INq ltac:(lia) ltac:(lia)) as SHQ2.
assert (SHQ16 : ro_cells asegs m (bse / 8 + 2147450882) [C1 (Z_to_bv 8 0)]).
{ replace (bse / 8 + 2147450882) with (q / 8 + 4 * Z.of_nat depth + 2 + A_SB) by (subst bse; rewrite div8_add_mul32 by lia; unfold A_SB; lia). exact SHQ2. }
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 2 HP INtk ltac:(lia)) as SHT2.
replace (tk / 8 + 2 + A_SB) with (tk / 8 + 2147450882) in SHT2 by (unfold A_SB; lia).
assert (BLO : 0 < bse < 2^63 /\ q <= bse) by (subst bse; lia).
stash Himg_t. stash Himg_q. clear PB REST TSK HP LV OBJ HPR BUD GAP SAVED FSH.
reenterA asegs A4L HIx asegs_wx HP.
replace (q + 32 * Z.of_nat depth) with bse by lia.
step. step.
change (zxb cb) with (Z_to_bv 64 (bv_unsigned cb)).
step.
destruct (Z.eq_dec (bv_unsigned cb) 93) as [C93 | N93].
- step.
if_falsex.
step. step.
step. if_true.
assert (EK : exists kids, tl_cs l = Some (Sarr kids)) by (clear - CLS0; destruct (tl_cs l) as [[| | | |okids|kids]|]; try (exfalso; exact CLS0); eexists; reflexivity).
destruct EK as [kids Ecs].
step.
asan_chkB.
step.
step.
evt_done5. subst bse.
eapply (pe_shrink_cJ HIx GA GA_pres SHRINK (PEF tk oldl newl len lenr sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m md A B ts0 l kids cb nb pj sv errv T kP nB);
[exact STC | exact BSL | exact INV0 | exact PBK | exact (BOK_drop _ _ _ _ _ _ BK) | exact Hl | exact Ecs | exact Hop | exact Hnbs0 | rewrite unsigned_lit by lia; reflexivity |].
intros m2 md2 A2 B2 cbs2 errv2 r w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 F2 fc2 INV2 PBK2 BK2 JX2 FS2 FRM2.
cbn [pf_spf] in *. unfold A_TP in *.

clear TOK SLOTS FF SHT4 SEP4c SEP4q SEP4i SHQ SHQ4 SHQ2 SHQ16 Ld MU WM MI Htal Htlo Hthi Hqal Hqlo Hqhi Hdtq Hqtk INtk INq INV0 PBK BK HbseR Hb8 BLO.
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
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd 0) q LB0 ts2)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * mxd) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd 0) q LB0 ts2)) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
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
pose proof (tok_flags_byteA mxd 0 m2 tk pb (Z.of_nat depth) q (TS isd stpos (Z_to_bv 64 co) err ucs high quote) TOK) as RDF.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 8 HP INtk ltac:(lia)) as SHT8.
replace (tk / 8 + 8 + 2147450880) with (tk / 8 + 2147450888) in SHT8 by lia.
assert (BLO : 0 < bse < 2^63 /\ q <= bse) by (subst bse; lia).
reenterA asegs A4L HIx asegs_wx HP.
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
asan_chkB.
step.
norm_sx32.
step.

lazymatch goal with |- evt _ _ (MS ?R ?FF _ ?fcc None ?mm ?rom) =>
assert (CLOSE : forall a1x, evt asegs (AJ5e A4L HIx A2 T md2) (MS (bvmap_set 11 a1x R) FF (Z_to_bv 64 0x96ca4) fcc None mm rom)) end.
{ intros a1x. clear SHT RDF SHT8.
step. if_truex.
step.
asan_chkB.
step.
stepz.
asan_rechkMB 1.
stepz.
step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m2 mc, WMc : wmono asegs m2 mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, Lc : rw_cells asegs mc bse _ |- _ =>
evt_done5; subst bse;
destruct (PE_INV_A_lvl_write HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m2 mc md2 A2 B2 ts2
cb nb pj sv errv2 l2 ST_eatws ST_finish CArr false CAny STC INV2 Hl2 MUc WMc MIc TOKc Lc Hmode ltac:(vm_compute; reflexivity) ltac:(unfold ST_eatws; lia) ltac:(unfold ST_finish; lia)
(or_intror eq_refl) ltac:(cbn [tl_st l2]; destruct Hst as [E|E]; rewrite E; vm_compute; reflexivity)) as [INV3 PBK3];
unfold ts2 in INV3, PBK3; rewrite ts_lvl_lvl in INV3, PBK3;
eapply (Kclose mc md2 A2 B2 cbs2 errv2 _ _ _ _ _ _ _ _ _ _ _ _ _ F2 fc2 kids C93 Ecs); [exact INV3 | exact (PBK3 kP PBK2) | exact (BK2 ST_eatws eq_refl) | exact JX2 | exact FS2 | exact FRM2]
end end. }
step.
destruct Hst as [E|E]; rewrite E; [unfold ST_array | unfold ST_array_after_sep].
+ if_true. apply CLOSE.
+ if_false.
step. asan_rechkB.
step. step.
rewrite ?zxb_zero.
step.
step.
if_true. apply CLOSE.
- step.
if_truex.
step.
asan_chkB.
step.
norm_sx32.
step.
norm_w32.
step. if_truex.
destruct (Nat.lt_ge_cases (S depth) (Z.to_nat mxd)) as [Dlt | Dge].
+ step.
if_truex.
evt_done5. subst bse.
eapply (seg_push_arr_B HIx GA GA_outside GA_pres PUT (PEF tk oldl newl len lenr sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m md A B ts0 l
cb nb pj sv errv T kP nB);
[exact STC | exact BSL | exact INV0 | exact PBK | exact BK | exact Hl | exact Hst | exact Dlt |].
intros until fc'. intros INV' PBK' BK' FS' FRM'. eapply (Kredo _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ N93 Dlt); eauto.
+ step.
if_falsex.
step.
step.
asan_rechkB.
step. step.
evt_done5.
subst bse. eapply Kerr; [exact N93 | exact Dge].
Qed.

Lemma seg_oval_B :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP : Z) (nB : nat)
(gp t0 a5 a7 s3 s6 s7 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> pf_fl pf = 0 -> 0 <= pa_bslack pa ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv -> PBOK m ts kP -> BOK pf pa ts B (S (Z.to_nat 512 + nB)) ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_ovalue ->

(forall m' md' A' B' errv' gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc',
(S (t_depth ts) < Z.to_nat (pf_mxd pf))%nat ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B'
(ts_push ts (TL ST_ovadd (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) cb nb pj sv errv' ->
PBOK m' (ts_push ts (TL ST_ovadd (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) kP ->
BOK pf pa (ts_push ts (TL ST_ovadd (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) B' nB ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msA asegs pf pa APE_REDO (t_co ts) gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' m')) ->

(forall a1' a4' a5',
(Z.to_nat (pf_mxd pf) <= S (t_depth ts))%nat ->
AJ5 A4L HIx A T md
(pe_msO asegs pf pa APE_ERR2 gp t0 (Z_to_bv 64 (pf_lenr pf)) (Z_to_bv 64 (pf_tk pf + 32)) (Z_to_bv 64 2) a1' (Z_to_bv 64 0) (Z_to_bv 64 (q / 8 + 4 * Z.of_nat (t_depth ts) + A_SB)) a4' a5' (Z_to_bv 64 APE_JTAB) a7 s3 (Z_to_bv 64 (pf_sb pf + t_co ts)) (Z_to_bv 64 q) s6 s7 (Z_to_bv 64 (Z.of_nat (t_depth ts))) s9 s11 t3 t4 t5 t6 F fc m)) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa (pe_jtA ST_ovalue) (t_co ts) gp t0 (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) (Z_to_bv 64 (tl_st l)) (Z_to_bv 64 0) (Z_to_bv 64 (q / 8 + 4 * Z.of_nat (t_depth ts) + A_SB)) (Z_to_bv 64 0) a5 (Z_to_bv 64 APE_JTAB) a7 s3 (Z_to_bv 64 q) s6 s7 (Z_to_bv 64 (Z.of_nat (t_depth ts))) s9 s11 t3 t4 t5 t6 F fc m).
Proof.
intros until fc. intros STC Hfl BSL INV PBK BK Hl Hst Kredo Kerr. pose proof INV as INV0. pe_openA STC INV.
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *. subst fl.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
pose proof FR as FR0. unfold pe_frameA in FR. destruct FR as (SLOTS & GAP & SAVED & FF & FSH).
unfold pe_slotsA in SLOTS. cbn zeta in SLOTS. unfold ff_cellsA in FF.
unfold pe_msA, pe_msO in *.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd 0) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * mxd) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd 0) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
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
unfold APE_BREAK, APE_REDO, APE_ERR2, APE_JTAB in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
pose proof Hmode as Hmode'. rewrite Hst in Hmode'. destruct (lvl_mode_ovalue _ _ _ SS26 Hmode') as (Ec0 & Ehn0 & Hop). subst c0 hn0. clear Hmode'.
pose proof (stack_shadowA HIx _ _ _ _ _ _ _ q mxd (Z.of_nat depth) 2 HP INq ltac:(lia) ltac:(lia)) as SHQ2.
assert (SHQ16 : ro_cells asegs m (bse / 8 + 2147450882) [C1 (Z_to_bv 8 0)]).
{ replace (bse / 8 + 2147450882) with (q / 8 + 4 * Z.of_nat depth + 2 + A_SB) by (subst bse; rewrite div8_add_mul32 by lia; unfold A_SB; lia). exact SHQ2. }
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 2 HP INtk ltac:(lia)) as SHT2.
replace (tk / 8 + 2 + A_SB) with (tk / 8 + 2147450882) in SHT2 by (unfold A_SB; lia).
stash Himg_t. stash Himg_q. clear PB REST TSK HP LV OBJ HPR BUD GAP SAVED FSH.
reenterA asegs A4L HIx asegs_wx HP. unfold ST_ovalue. cbn [pe_jtA].
replace (q + 32 * Z.of_nat depth) with bse by lia.
step.
asan_chkB.
step.
norm_sx32.
step.
norm_w32.
step. if_truex.
destruct (Nat.lt_ge_cases (S depth) (Z.to_nat mxd)) as [Dlt | Dge].
- step.
if_truex.
evt_done5. subst bse.
eapply (seg_push_ov_B HIx GA GA_outside GA_pres PUT (PEF tk oldl newl len lenr sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m md A B ts0 l
cb nb pj sv errv T kP nB);
[exact STC | exact BSL | exact INV0 | exact PBK | exact BK | exact Hl | exact Hst | exact Dlt |].
intros until fc'. intros INV' PBK' BK' FS' FRM'. eapply (Kredo _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Dlt); eauto.
- step.
if_falsex.
step.
step.
asan_rechkB.
step. step.
evt_done5.
subst bse. eapply Kerr; exact Dge.
Qed.
End PeSArrayB.
End RC__1.
End Mq2.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QJjn QRUw.Mq0 QRUw QkMG. Import QG8z Qdyh.Mq0 Qdyh.Mq3 Qdyh.Mq4 QIsM.Mq2 Qa8x.Mq2.
Import Qhd4 Qwm6.
Import QbFI.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqj QsKa.Mqd Qiiq QsKa.Mqf Q4v2 QlKV.Mqf QSHS Ql4f.Mq4 Q1Y6.Mq4 QsKa.Mqh QrQv.Mq4 QEUF.Mq2 QW22.Mq8 QdGy.Mq9 QYZ0.Mq8 Qkko.Mq3.
Import Qc5u QAzu.Mq0.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Lemma rodata_byte_at : forall m a v, mem_inv asegs m -> ro_bytes_b asegs a [Z_to_bv 8 v] = true -> 0 <= a -> a + 1 < 2^64 -> bytes_at asegs m a [Z_to_bv 8 v].
Proof.
intros m a v MI IMG Ha Hb. assert (RO : ro_cells asegs m a [CB 1 [Z_to_bv 8 v]]) by (apply ro_cells_image; [exact MI | exact IMG | exact Ha | cbn; lia]).
destruct RO as [_ H]. exact H.
Qed.

Section PeSSescLA.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_outside : forall m m' W, GA m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= hl_img_lo A4H \/ hl_img_hi A4H <= fst iv) W -> GA m'.
Hypothesis GA_pres : forall LB SP m m', heap_pres A4H LB SP m m' -> GA m -> GA m'.
Hypothesis MAPP : memappend_A_stmt2 HIx.

Ltac pe_openA STC INV :=
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR); pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk);
destruct INV as [CORE REST];
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR);
pose proof REST as (HP & LV & OBJ & ST & ERR & STR & PLEN & SBin & HPR & MDV & G & BUD).

Ltac reopen_inv INVx TSx ts0 PF q LB0 tk mxd depth l Hl bse Hbse mX :=
pose proof INVx as [CORE2 REST2];
destruct CORE2 as (_ & _ & _ & _ & TOK & _ & _ & TSK & FR);
pose proof REST2 as (HP & _); clear REST2;
try unfold TSx in TOK, TSK; try unfold ts_pbs, ts_lvl, ts_set_x in TOK, TSK; try unfold ts0 in TOK, TSK;
cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_tk pf_mxd pf_fl] in TOK, TSK;
unfold tok_cells_g in TOK; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK;
unfold pe_frameA in FR; destruct FR as (SLOTS & _ & _ & _ & _); unfold pe_slotsA in SLOTS; cbn zeta in SLOTS;
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in SLOTS;
assert (INtk : In (tk, 72) (pe_blocksA PF q LB0 TSx)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity);
assert (INq : In (q, 32 * mxd) (pe_blocksA PF q LB0 TSx)) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity);
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI;
pose proof (wmono_refl asegs mX) as WM;
pose proof (TSK depth l Hl) as Ld; rewrite <- Hbse in Ld; unfold srec_cells in Ld;
clear TSK.

Lemma pe_memappend_lit :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP xb v : Z)
(ra gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
PBOK m ts kP -> kP + 1 <= 1 -> forall kB : nat, BOK pf pa ts B kB -> bv_unsigned ra mod 2 = 0 ->
In xb [0x231a0; 0x231c0; 0x231e0; 0x23200; 0x23220] -> ro_bytes_b asegs xb [Z_to_bv 8 v] = true ->
(forall m2 md2 A2 B2 pbs2 errv2 r (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : word) F2 fc2,
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m2 md2 A2 B2 (ts_pbs ts pbs2) cb nb pj sv errv2 ->
(r = 1 /\ PBOK m2 (ts_pbs ts pbs2) (kP + 1) /\ BOK pf pa (ts_pbs ts pbs2) B2 kB) \/ (r = 2^64 - 1 /\ pbs2 = t_pbs ts) ->
fsaved F F2 -> (frm0 fc -> frm0 fc2) ->
AJ5 A4L HIx A2 T md2
(MS (mkR ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) w0 w1 w2 s0 s1 (Z_to_bv 64 r) w3 w4 w5 w6 w7 w8 w9
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 w10 w11 w12 w13) F2 (ret_pc ra) fc2 None m2 (seg_rom asegs))) ->
AJ5 A4L HIx A T md
(MS (mkR ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2 s0 s1 (Z_to_bv 64 (t_pb ts)) (Z_to_bv 64 xb) (Z_to_bv 64 1) a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x9b4fc) fc None m (seg_rom asegs)).
Proof.
intros until fc. intros STC BSL INV PBK HkP kB BK RA Hxb IMG K.
pose proof INV as [_ (HP & _)]. pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
assert (Hxr : 0 <= xb /\ xb + 1 < 2^64) by (cbn in Hxb; repeat (destruct Hxb as [<- | Hxb]; [lia|]); destruct Hxb).
eapply (pe_memappend_g HIx GA GA_pres MAPP pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv T xb 1 (t_co ts + kP) [Z_to_bv 8 v]);
[exact STC | exact BSL | exact INV | exact PBK | lia | lia | exact BK | exact RA
| apply rodata_byte_at; [exact MI | exact IMG | lia | lia] | reflexivity | lia
| apply esc_src_locA; exact Hxb
| intros _; exact (unpoisoned_of_glob HIx _ _ _ _ _ _ _ _ _ HP (esc_src_globA xb Hxb) ltac:(lia)) |].
intros m2 md2 A2 B2 pbs2 errv2 r w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 F2 fc2 INV2 OUT2 FS2 FRM2.
eapply (K m2 md2 A2 B2 pbs2 errv2 r); [exact INV2 | | exact FS2 | exact FRM2].
destruct OUT2 as [(-> & PBK2 & BK2) | [-> E]]; [left | right; split; [reflexivity | exact E]].
split; [reflexivity|]. split; [| exact BK2]. unfold PBOK, ts_pbs. cbn [t_co]. replace (t_co ts + (kP + 1)) with (t_co ts + kP + 1) by lia. exact PBK2.
Qed.

Lemma sesc_lit_b_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP : Z) (nB : nat)
(gp t0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv -> PBOK m ts kP -> kP + 1 <= 1 -> BOK pf pa ts B (S nB) ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_string_escape ->
(forall c hn, lvl_mode (tl_st l) (tl_ss l) = Some (c, hn) -> lvl_mode (tl_ss l) (tl_ss l) = Some (c, hn)) ->
zin (tl_ss l) [ST_array_add; ST_ovadd] = false ->

(forall m' md' A' B' pbs' errv' gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B'
(ts_lvl (ts_pbs ts pbs') (TL (tl_ss l) (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) cb nb pj sv errv' ->
PBOK m' (ts_lvl (ts_pbs ts pbs') (TL (tl_ss l) (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) (kP + 1) ->
BOK pf pa (ts_lvl (ts_pbs ts pbs') (TL (tl_ss l) (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) B' nB ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msA asegs pf pa APE_BREAK (t_co ts) gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' (Z_to_bv 64 2) s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' m')) ->

(forall m' md' A' B' errv' x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' ts cb nb pj sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msX asegs pf pa APE_ERR3 x1' gp' t0' t1' t2' (Z_to_bv 64 16) a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' m')) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa 0x9730c (t_co ts) gp t0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc m).
Proof.
intros until fc. intros STC BSL INV PBK HkP BK Hl Hst HMODE Hzss Kbreak Kerr16. pose proof INV as INV0. pe_openA STC INV.
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
pose proof FR as FR0. unfold pe_frameA in FR. destruct FR as (SLOTS & GAP & SAVED & FF & FSH).
unfold pe_slotsA in SLOTS. cbn zeta in SLOTS. unfold ff_cellsA in FF.
unfold pe_msA, pe_msX in *.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * mxd) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t.
blk_factsA A4L HIx HP q (32 * mxd) Hqal Hqlo Hqhi Himg_q.
pose proof (q_ne_tkA HIx _ _ _ _ _ _ _ _ _ _ HP) as Hqtk. cbn [pf_tk] in Hqtk.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ tk 72 q (32 * mxd) HP (in_or_app _ LM _ (or_introl INtk)) (in_or_app _ LM _ (or_introl INq)) ltac:(congruence)) as Hdtq.
pose proof (tok_shadowA HIx _ _ _ _ _ _ _ _ HP INtk) as SHT.
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
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 1 HP INtk ltac:(lia)) as SHT1.
replace (tk / 8 + 1 + A_SB) with (tk / 8 + 2147450881) in SHT1 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 1 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT1c & SEPT1q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 1 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT1t & _).
cbn [hl_sb A4L] in SEPT1c, SEPT1q, SEPT1t. assert (EQx : tk / 8 + A_SB + 1 = tk / 8 + 2147450881) by (unfold A_SB; lia). rewrite EQx in SEPT1c, SEPT1q, SEPT1t. clear EQx.
unfold APE_BREAK, APE_ERR3, APE_REDO, APE_OUT, APE_ERRMEM, APE_JTAB in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
clear Hdtq SEPT1c SEPT1q SEPT1t.
stash Himg_t. stash Himg_q. stash Kbreak. stash Kerr16. clear PB REST TSK LV OBJ HPR BUD GAP SAVED FSH FF STR ERR SBin SHT SHQ SHQ4 Ld MU.
reenterA asegs A4L HIx asegs_wx HP.
step.
asan_chkB.
step.
step. step.
step.
step.
evt_done5.
eapply (pe_memappend_lit (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m md A B ts0 cb nb pj sv errv T kP 0x231a0 8);
[exact STC | exact BSL | exact INV0 | exact PBK | exact HkP | exact BK | rewrite unsigned_lit by lia; reflexivity | cbn; tauto | vm_compute; reflexivity |].
intros mp2 md2 A2 B2 pbs2 errv2 r w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 F2 fc2 INV2 OUT2 FS2 FRM2.
cbn [pf_spf] in *. unfold A_TP in *.
clear TOK SLOTS SHT1 WM MI HP INtk INq Htal Htlo Hthi Hqal Hqlo Hqhi Hqtk INV0 PBK BK.
set (ts2 := ts_pbs ts0 pbs2) in *.
reopen_inv INV2 ts2 ts0 (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 tk mxd depth l Hl bse Hbse mp2.
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t2.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 4 HP INtk ltac:(lia)) as SHT4.
replace (tk / 8 + 4 + A_SB) with (tk / 8 + 2147450884) in SHT4 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 4 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT4c & SEPT4q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 4 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT4t & _).
cbn [hl_sb A4L] in SEPT4c, SEPT4q, SEPT4t. assert (EQx : tk / 8 + A_SB + 4 = tk / 8 + 2147450884) by (unfold A_SB; lia). rewrite EQx in SEPT4c, SEPT4q, SEPT4t. clear EQx.
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
clear SEPT4c SEPT4q SEPT4t Ld.
stash Himg_t2.
try lazymatch goal with |- AJ5 _ _ _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) => replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
reenterA asegs A4L HIx asegs_wx HP.
do 3 step.
destruct OUT2 as [(-> & PBK2 & BK2) | [-> Epbs2]].
-
step.
if_false.
step.
evt_done5.
assert (Hl2 : nth_error (t_levels ts2) (t_depth ts2) = Some l) by (unfold ts2, ts_pbs, ts0; cbn [t_levels t_depth]; exact Hl).
eapply (sesc_join_A HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo mp2 md2 A2 B2 ts2 l cb nb pj sv errv2 T (kP + 1));
[exact STC | exact INV2 | exact PBK2 | exact Hl2 | exact Hst | exact HMODE | exact Hzss |].
intros m'. intros until t6'. intros INV3 PBK3. unstash Kbreak.
eapply (Kbreak m' md2 A2 B2 pbs2 errv2); [exact INV3 | exact PBK3 | | exact FS2 | exact FRM2].
apply (BOK_lvl_restate (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) ts2 B2 nB l (tl_ss l) (tl_ss l) Hl2); [| eapply BOK_weaken; [| exact BK2]; lia].
intros CL. unfold lvl_closed in *. cbn [tl_st tl_ss]. apply andb_true_iff in CL as [CL _]. rewrite CL, Hzss. reflexivity.
-
replace (Z_to_bv 64 (2^64 - 1)) with (Z_to_bv 64 (-1)) by (apply bv_eq; vm_compute; reflexivity).
step.
if_true.
step.
step.
asan_rechkB.
step.
evt_done5.
unstash Kerr16. eapply (Kerr16 mp2 md2 A2 B2 errv2); [| exact FS2 | exact FRM2].
unfold ts2 in INV2. rewrite Epbs2 in INV2. exact INV2.
Qed.

Lemma sesc_lit_f_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP : Z) (nB : nat)
(gp t0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv -> PBOK m ts kP -> kP + 1 <= 1 -> BOK pf pa ts B (S nB) ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_string_escape ->
(forall c hn, lvl_mode (tl_st l) (tl_ss l) = Some (c, hn) -> lvl_mode (tl_ss l) (tl_ss l) = Some (c, hn)) ->
zin (tl_ss l) [ST_array_add; ST_ovadd] = false ->

(forall m' md' A' B' pbs' errv' gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B'
(ts_lvl (ts_pbs ts pbs') (TL (tl_ss l) (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) cb nb pj sv errv' ->
PBOK m' (ts_lvl (ts_pbs ts pbs') (TL (tl_ss l) (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) (kP + 1) ->
BOK pf pa (ts_lvl (ts_pbs ts pbs') (TL (tl_ss l) (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) B' nB ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msA asegs pf pa APE_BREAK (t_co ts) gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' (Z_to_bv 64 2) s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' m')) ->

(forall m' md' A' B' errv' x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' ts cb nb pj sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msX asegs pf pa APE_ERR3 x1' gp' t0' t1' t2' (Z_to_bv 64 16) a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' m')) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa 0x983ec (t_co ts) gp t0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc m).
Proof.
intros until fc. intros STC BSL INV PBK HkP BK Hl Hst HMODE Hzss Kbreak Kerr16. pose proof INV as INV0. pe_openA STC INV.
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
pose proof FR as FR0. unfold pe_frameA in FR. destruct FR as (SLOTS & GAP & SAVED & FF & FSH).
unfold pe_slotsA in SLOTS. cbn zeta in SLOTS. unfold ff_cellsA in FF.
unfold pe_msA, pe_msX in *.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * mxd) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t.
blk_factsA A4L HIx HP q (32 * mxd) Hqal Hqlo Hqhi Himg_q.
pose proof (q_ne_tkA HIx _ _ _ _ _ _ _ _ _ _ HP) as Hqtk. cbn [pf_tk] in Hqtk.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ tk 72 q (32 * mxd) HP (in_or_app _ LM _ (or_introl INtk)) (in_or_app _ LM _ (or_introl INq)) ltac:(congruence)) as Hdtq.
pose proof (tok_shadowA HIx _ _ _ _ _ _ _ _ HP INtk) as SHT.
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
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 1 HP INtk ltac:(lia)) as SHT1.
replace (tk / 8 + 1 + A_SB) with (tk / 8 + 2147450881) in SHT1 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 1 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT1c & SEPT1q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 1 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT1t & _).
cbn [hl_sb A4L] in SEPT1c, SEPT1q, SEPT1t. assert (EQx : tk / 8 + A_SB + 1 = tk / 8 + 2147450881) by (unfold A_SB; lia). rewrite EQx in SEPT1c, SEPT1q, SEPT1t. clear EQx.
unfold APE_BREAK, APE_ERR3, APE_REDO, APE_OUT, APE_ERRMEM, APE_JTAB in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
clear Hdtq SEPT1c SEPT1q SEPT1t.
stash Himg_t. stash Himg_q. stash Kbreak. stash Kerr16. clear PB REST TSK LV OBJ HPR BUD GAP SAVED FSH FF STR ERR SBin SHT SHQ SHQ4 Ld MU.
reenterA asegs A4L HIx asegs_wx HP.
step.
asan_chkB.
step.
step. step.
step.
step.
evt_done5.
eapply (pe_memappend_lit (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m md A B ts0 cb nb pj sv errv T kP 0x23220 12);
[exact STC | exact BSL | exact INV0 | exact PBK | exact HkP | exact BK | rewrite unsigned_lit by lia; reflexivity | cbn; tauto | vm_compute; reflexivity |].
intros mp2 md2 A2 B2 pbs2 errv2 r w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 F2 fc2 INV2 OUT2 FS2 FRM2.
cbn [pf_spf] in *. unfold A_TP in *.
clear TOK SLOTS SHT1 WM MI HP INtk INq Htal Htlo Hthi Hqal Hqlo Hqhi Hqtk INV0 PBK BK.
set (ts2 := ts_pbs ts0 pbs2) in *.
reopen_inv INV2 ts2 ts0 (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 tk mxd depth l Hl bse Hbse mp2.
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t2.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 4 HP INtk ltac:(lia)) as SHT4.
replace (tk / 8 + 4 + A_SB) with (tk / 8 + 2147450884) in SHT4 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 4 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT4c & SEPT4q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 4 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT4t & _).
cbn [hl_sb A4L] in SEPT4c, SEPT4q, SEPT4t. assert (EQx : tk / 8 + A_SB + 4 = tk / 8 + 2147450884) by (unfold A_SB; lia). rewrite EQx in SEPT4c, SEPT4q, SEPT4t. clear EQx.
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
clear SEPT4c SEPT4q SEPT4t Ld.
stash Himg_t2.
try lazymatch goal with |- AJ5 _ _ _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) => replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
reenterA asegs A4L HIx asegs_wx HP.
do 3 step.
destruct OUT2 as [(-> & PBK2 & BK2) | [-> Epbs2]].
-
step.
if_true.
evt_done5.
assert (Hl2 : nth_error (t_levels ts2) (t_depth ts2) = Some l) by (unfold ts2, ts_pbs, ts0; cbn [t_levels t_depth]; exact Hl).
eapply (sesc_join_A HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo mp2 md2 A2 B2 ts2 l cb nb pj sv errv2 T (kP + 1));
[exact STC | exact INV2 | exact PBK2 | exact Hl2 | exact Hst | exact HMODE | exact Hzss |].
intros m'. intros until t6'. intros INV3 PBK3. unstash Kbreak.
eapply (Kbreak m' md2 A2 B2 pbs2 errv2); [exact INV3 | exact PBK3 | | exact FS2 | exact FRM2].
apply (BOK_lvl_restate (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) ts2 B2 nB l (tl_ss l) (tl_ss l) Hl2); [| eapply BOK_weaken; [| exact BK2]; lia].
intros CL. unfold lvl_closed in *. cbn [tl_st tl_ss]. apply andb_true_iff in CL as [CL _]. rewrite CL, Hzss. reflexivity.
-
replace (Z_to_bv 64 (2^64 - 1)) with (Z_to_bv 64 (-1)) by (apply bv_eq; vm_compute; reflexivity).
step.
if_false.
step.
step.
asan_rechkB.
step.
evt_done5.
unstash Kerr16. eapply (Kerr16 mp2 md2 A2 B2 errv2); [| exact FS2 | exact FRM2].
unfold ts2 in INV2. rewrite Epbs2 in INV2. exact INV2.
Qed.

Lemma sesc_lit_n_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP : Z) (nB : nat)
(gp t0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv -> PBOK m ts kP -> kP + 1 <= 1 -> BOK pf pa ts B (S nB) ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_string_escape ->
(forall c hn, lvl_mode (tl_st l) (tl_ss l) = Some (c, hn) -> lvl_mode (tl_ss l) (tl_ss l) = Some (c, hn)) ->
zin (tl_ss l) [ST_array_add; ST_ovadd] = false ->

(forall m' md' A' B' pbs' errv' gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B'
(ts_lvl (ts_pbs ts pbs') (TL (tl_ss l) (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) cb nb pj sv errv' ->
PBOK m' (ts_lvl (ts_pbs ts pbs') (TL (tl_ss l) (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) (kP + 1) ->
BOK pf pa (ts_lvl (ts_pbs ts pbs') (TL (tl_ss l) (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) B' nB ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msA asegs pf pa APE_BREAK (t_co ts) gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' (Z_to_bv 64 2) s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' m')) ->

(forall m' md' A' B' errv' x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' ts cb nb pj sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msX asegs pf pa APE_ERR3 x1' gp' t0' t1' t2' (Z_to_bv 64 16) a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' m')) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa 0x983ac (t_co ts) gp t0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc m).
Proof.
intros until fc. intros STC BSL INV PBK HkP BK Hl Hst HMODE Hzss Kbreak Kerr16. pose proof INV as INV0. pe_openA STC INV.
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
pose proof FR as FR0. unfold pe_frameA in FR. destruct FR as (SLOTS & GAP & SAVED & FF & FSH).
unfold pe_slotsA in SLOTS. cbn zeta in SLOTS. unfold ff_cellsA in FF.
unfold pe_msA, pe_msX in *.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * mxd) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t.
blk_factsA A4L HIx HP q (32 * mxd) Hqal Hqlo Hqhi Himg_q.
pose proof (q_ne_tkA HIx _ _ _ _ _ _ _ _ _ _ HP) as Hqtk. cbn [pf_tk] in Hqtk.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ tk 72 q (32 * mxd) HP (in_or_app _ LM _ (or_introl INtk)) (in_or_app _ LM _ (or_introl INq)) ltac:(congruence)) as Hdtq.
pose proof (tok_shadowA HIx _ _ _ _ _ _ _ _ HP INtk) as SHT.
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
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 1 HP INtk ltac:(lia)) as SHT1.
replace (tk / 8 + 1 + A_SB) with (tk / 8 + 2147450881) in SHT1 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 1 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT1c & SEPT1q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 1 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT1t & _).
cbn [hl_sb A4L] in SEPT1c, SEPT1q, SEPT1t. assert (EQx : tk / 8 + A_SB + 1 = tk / 8 + 2147450881) by (unfold A_SB; lia). rewrite EQx in SEPT1c, SEPT1q, SEPT1t. clear EQx.
unfold APE_BREAK, APE_ERR3, APE_REDO, APE_OUT, APE_ERRMEM, APE_JTAB in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
clear Hdtq SEPT1c SEPT1q SEPT1t.
stash Himg_t. stash Himg_q. stash Kbreak. stash Kerr16. clear PB REST TSK LV OBJ HPR BUD GAP SAVED FSH FF STR ERR SBin SHT SHQ SHQ4 Ld MU.
reenterA asegs A4L HIx asegs_wx HP.
step.
asan_chkB.
step.
step. step.
step.
step.
evt_done5.
eapply (pe_memappend_lit (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m md A B ts0 cb nb pj sv errv T kP 0x231c0 10);
[exact STC | exact BSL | exact INV0 | exact PBK | exact HkP | exact BK | rewrite unsigned_lit by lia; reflexivity | cbn; tauto | vm_compute; reflexivity |].
intros mp2 md2 A2 B2 pbs2 errv2 r w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 F2 fc2 INV2 OUT2 FS2 FRM2.
cbn [pf_spf] in *. unfold A_TP in *.
clear TOK SLOTS SHT1 WM MI HP INtk INq Htal Htlo Hthi Hqal Hqlo Hqhi Hqtk INV0 PBK BK.
set (ts2 := ts_pbs ts0 pbs2) in *.
reopen_inv INV2 ts2 ts0 (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 tk mxd depth l Hl bse Hbse mp2.
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t2.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 4 HP INtk ltac:(lia)) as SHT4.
replace (tk / 8 + 4 + A_SB) with (tk / 8 + 2147450884) in SHT4 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 4 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT4c & SEPT4q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 4 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT4t & _).
cbn [hl_sb A4L] in SEPT4c, SEPT4q, SEPT4t. assert (EQx : tk / 8 + A_SB + 4 = tk / 8 + 2147450884) by (unfold A_SB; lia). rewrite EQx in SEPT4c, SEPT4q, SEPT4t. clear EQx.
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
clear SEPT4c SEPT4q SEPT4t Ld.
stash Himg_t2.
try lazymatch goal with |- AJ5 _ _ _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) => replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
reenterA asegs A4L HIx asegs_wx HP.
do 3 step.
destruct OUT2 as [(-> & PBK2 & BK2) | [-> Epbs2]].
-
step.
if_true.
evt_done5.
assert (Hl2 : nth_error (t_levels ts2) (t_depth ts2) = Some l) by (unfold ts2, ts_pbs, ts0; cbn [t_levels t_depth]; exact Hl).
eapply (sesc_join_A HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo mp2 md2 A2 B2 ts2 l cb nb pj sv errv2 T (kP + 1));
[exact STC | exact INV2 | exact PBK2 | exact Hl2 | exact Hst | exact HMODE | exact Hzss |].
intros m'. intros until t6'. intros INV3 PBK3. unstash Kbreak.
eapply (Kbreak m' md2 A2 B2 pbs2 errv2); [exact INV3 | exact PBK3 | | exact FS2 | exact FRM2].
apply (BOK_lvl_restate (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) ts2 B2 nB l (tl_ss l) (tl_ss l) Hl2); [| eapply BOK_weaken; [| exact BK2]; lia].
intros CL. unfold lvl_closed in *. cbn [tl_st tl_ss]. apply andb_true_iff in CL as [CL _]. rewrite CL, Hzss. reflexivity.
-
replace (Z_to_bv 64 (2^64 - 1)) with (Z_to_bv 64 (-1)) by (apply bv_eq; vm_compute; reflexivity).
step.
if_false.
step.
step.
asan_rechkB.
step.
evt_done5.
unstash Kerr16. eapply (Kerr16 mp2 md2 A2 B2 errv2); [| exact FS2 | exact FRM2].
unfold ts2 in INV2. rewrite Epbs2 in INV2. exact INV2.
Qed.

Lemma sesc_lit_r_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP : Z) (nB : nat)
(gp t0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv -> PBOK m ts kP -> kP + 1 <= 1 -> BOK pf pa ts B (S nB) ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_string_escape ->
(forall c hn, lvl_mode (tl_st l) (tl_ss l) = Some (c, hn) -> lvl_mode (tl_ss l) (tl_ss l) = Some (c, hn)) ->
zin (tl_ss l) [ST_array_add; ST_ovadd] = false ->

(forall m' md' A' B' pbs' errv' gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B'
(ts_lvl (ts_pbs ts pbs') (TL (tl_ss l) (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) cb nb pj sv errv' ->
PBOK m' (ts_lvl (ts_pbs ts pbs') (TL (tl_ss l) (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) (kP + 1) ->
BOK pf pa (ts_lvl (ts_pbs ts pbs') (TL (tl_ss l) (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) B' nB ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msA asegs pf pa APE_BREAK (t_co ts) gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' (Z_to_bv 64 2) s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' m')) ->

(forall m' md' A' B' errv' x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' ts cb nb pj sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msX asegs pf pa APE_ERR3 x1' gp' t0' t1' t2' (Z_to_bv 64 16) a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' m')) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa 0x9842c (t_co ts) gp t0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc m).
Proof.
intros until fc. intros STC BSL INV PBK HkP BK Hl Hst HMODE Hzss Kbreak Kerr16. pose proof INV as INV0. pe_openA STC INV.
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
pose proof FR as FR0. unfold pe_frameA in FR. destruct FR as (SLOTS & GAP & SAVED & FF & FSH).
unfold pe_slotsA in SLOTS. cbn zeta in SLOTS. unfold ff_cellsA in FF.
unfold pe_msA, pe_msX in *.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * mxd) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t.
blk_factsA A4L HIx HP q (32 * mxd) Hqal Hqlo Hqhi Himg_q.
pose proof (q_ne_tkA HIx _ _ _ _ _ _ _ _ _ _ HP) as Hqtk. cbn [pf_tk] in Hqtk.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ tk 72 q (32 * mxd) HP (in_or_app _ LM _ (or_introl INtk)) (in_or_app _ LM _ (or_introl INq)) ltac:(congruence)) as Hdtq.
pose proof (tok_shadowA HIx _ _ _ _ _ _ _ _ HP INtk) as SHT.
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
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 1 HP INtk ltac:(lia)) as SHT1.
replace (tk / 8 + 1 + A_SB) with (tk / 8 + 2147450881) in SHT1 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 1 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT1c & SEPT1q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 1 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT1t & _).
cbn [hl_sb A4L] in SEPT1c, SEPT1q, SEPT1t. assert (EQx : tk / 8 + A_SB + 1 = tk / 8 + 2147450881) by (unfold A_SB; lia). rewrite EQx in SEPT1c, SEPT1q, SEPT1t. clear EQx.
unfold APE_BREAK, APE_ERR3, APE_REDO, APE_OUT, APE_ERRMEM, APE_JTAB in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
clear Hdtq SEPT1c SEPT1q SEPT1t.
stash Himg_t. stash Himg_q. stash Kbreak. stash Kerr16. clear PB REST TSK LV OBJ HPR BUD GAP SAVED FSH FF STR ERR SBin SHT SHQ SHQ4 Ld MU.
reenterA asegs A4L HIx asegs_wx HP.
step.
asan_chkB.
step.
step. step.
step.
step.
evt_done5.
eapply (pe_memappend_lit (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m md A B ts0 cb nb pj sv errv T kP 0x231e0 13);
[exact STC | exact BSL | exact INV0 | exact PBK | exact HkP | exact BK | rewrite unsigned_lit by lia; reflexivity | cbn; tauto | vm_compute; reflexivity |].
intros mp2 md2 A2 B2 pbs2 errv2 r w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 F2 fc2 INV2 OUT2 FS2 FRM2.
cbn [pf_spf] in *. unfold A_TP in *.
clear TOK SLOTS SHT1 WM MI HP INtk INq Htal Htlo Hthi Hqal Hqlo Hqhi Hqtk INV0 PBK BK.
set (ts2 := ts_pbs ts0 pbs2) in *.
reopen_inv INV2 ts2 ts0 (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 tk mxd depth l Hl bse Hbse mp2.
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t2.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 4 HP INtk ltac:(lia)) as SHT4.
replace (tk / 8 + 4 + A_SB) with (tk / 8 + 2147450884) in SHT4 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 4 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT4c & SEPT4q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 4 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT4t & _).
cbn [hl_sb A4L] in SEPT4c, SEPT4q, SEPT4t. assert (EQx : tk / 8 + A_SB + 4 = tk / 8 + 2147450884) by (unfold A_SB; lia). rewrite EQx in SEPT4c, SEPT4q, SEPT4t. clear EQx.
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
clear SEPT4c SEPT4q SEPT4t Ld.
stash Himg_t2.
try lazymatch goal with |- AJ5 _ _ _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) => replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
reenterA asegs A4L HIx asegs_wx HP.
do 3 step.
destruct OUT2 as [(-> & PBK2 & BK2) | [-> Epbs2]].
-
step.
if_true.
evt_done5.
assert (Hl2 : nth_error (t_levels ts2) (t_depth ts2) = Some l) by (unfold ts2, ts_pbs, ts0; cbn [t_levels t_depth]; exact Hl).
eapply (sesc_join_A HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo mp2 md2 A2 B2 ts2 l cb nb pj sv errv2 T (kP + 1));
[exact STC | exact INV2 | exact PBK2 | exact Hl2 | exact Hst | exact HMODE | exact Hzss |].
intros m'. intros until t6'. intros INV3 PBK3. unstash Kbreak.
eapply (Kbreak m' md2 A2 B2 pbs2 errv2); [exact INV3 | exact PBK3 | | exact FS2 | exact FRM2].
apply (BOK_lvl_restate (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) ts2 B2 nB l (tl_ss l) (tl_ss l) Hl2); [| eapply BOK_weaken; [| exact BK2]; lia].
intros CL. unfold lvl_closed in *. cbn [tl_st tl_ss]. apply andb_true_iff in CL as [CL _]. rewrite CL, Hzss. reflexivity.
-
replace (Z_to_bv 64 (2^64 - 1)) with (Z_to_bv 64 (-1)) by (apply bv_eq; vm_compute; reflexivity).
step.
if_false.
step.
step.
asan_rechkB.
step.
evt_done5.
unstash Kerr16. eapply (Kerr16 mp2 md2 A2 B2 errv2); [| exact FS2 | exact FRM2].
unfold ts2 in INV2. rewrite Epbs2 in INV2. exact INV2.
Qed.

Lemma sesc_lit_t_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP : Z) (nB : nat)
(gp t0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv -> PBOK m ts kP -> kP + 1 <= 1 -> BOK pf pa ts B (S nB) ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_string_escape ->
(forall c hn, lvl_mode (tl_st l) (tl_ss l) = Some (c, hn) -> lvl_mode (tl_ss l) (tl_ss l) = Some (c, hn)) ->
zin (tl_ss l) [ST_array_add; ST_ovadd] = false ->

(forall m' md' A' B' pbs' errv' gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B'
(ts_lvl (ts_pbs ts pbs') (TL (tl_ss l) (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) cb nb pj sv errv' ->
PBOK m' (ts_lvl (ts_pbs ts pbs') (TL (tl_ss l) (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) (kP + 1) ->
BOK pf pa (ts_lvl (ts_pbs ts pbs') (TL (tl_ss l) (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) B' nB ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msA asegs pf pa APE_BREAK (t_co ts) gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' (Z_to_bv 64 2) s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' m')) ->

(forall m' md' A' B' errv' x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' ts cb nb pj sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msX asegs pf pa APE_ERR3 x1' gp' t0' t1' t2' (Z_to_bv 64 16) a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' m')) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa 0x9846c (t_co ts) gp t0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc m).
Proof.
intros until fc. intros STC BSL INV PBK HkP BK Hl Hst HMODE Hzss Kbreak Kerr16. pose proof INV as INV0. pe_openA STC INV.
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
pose proof FR as FR0. unfold pe_frameA in FR. destruct FR as (SLOTS & GAP & SAVED & FF & FSH).
unfold pe_slotsA in SLOTS. cbn zeta in SLOTS. unfold ff_cellsA in FF.
unfold pe_msA, pe_msX in *.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * mxd) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t.
blk_factsA A4L HIx HP q (32 * mxd) Hqal Hqlo Hqhi Himg_q.
pose proof (q_ne_tkA HIx _ _ _ _ _ _ _ _ _ _ HP) as Hqtk. cbn [pf_tk] in Hqtk.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ tk 72 q (32 * mxd) HP (in_or_app _ LM _ (or_introl INtk)) (in_or_app _ LM _ (or_introl INq)) ltac:(congruence)) as Hdtq.
pose proof (tok_shadowA HIx _ _ _ _ _ _ _ _ HP INtk) as SHT.
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
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 1 HP INtk ltac:(lia)) as SHT1.
replace (tk / 8 + 1 + A_SB) with (tk / 8 + 2147450881) in SHT1 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 1 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT1c & SEPT1q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 1 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT1t & _).
cbn [hl_sb A4L] in SEPT1c, SEPT1q, SEPT1t. assert (EQx : tk / 8 + A_SB + 1 = tk / 8 + 2147450881) by (unfold A_SB; lia). rewrite EQx in SEPT1c, SEPT1q, SEPT1t. clear EQx.
unfold APE_BREAK, APE_ERR3, APE_REDO, APE_OUT, APE_ERRMEM, APE_JTAB in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
clear Hdtq SEPT1c SEPT1q SEPT1t.
stash Himg_t. stash Himg_q. stash Kbreak. stash Kerr16. clear PB REST TSK LV OBJ HPR BUD GAP SAVED FSH FF STR ERR SBin SHT SHQ SHQ4 Ld MU.
reenterA asegs A4L HIx asegs_wx HP.
step.
asan_chkB.
step.
step. step.
step.
step.
evt_done5.
eapply (pe_memappend_lit (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m md A B ts0 cb nb pj sv errv T kP 0x23200 9);
[exact STC | exact BSL | exact INV0 | exact PBK | exact HkP | exact BK | rewrite unsigned_lit by lia; reflexivity | cbn; tauto | vm_compute; reflexivity |].
intros mp2 md2 A2 B2 pbs2 errv2 r w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 F2 fc2 INV2 OUT2 FS2 FRM2.
cbn [pf_spf] in *. unfold A_TP in *.
clear TOK SLOTS SHT1 WM MI HP INtk INq Htal Htlo Hthi Hqal Hqlo Hqhi Hqtk INV0 PBK BK.
set (ts2 := ts_pbs ts0 pbs2) in *.
reopen_inv INV2 ts2 ts0 (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 tk mxd depth l Hl bse Hbse mp2.
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t2.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 4 HP INtk ltac:(lia)) as SHT4.
replace (tk / 8 + 4 + A_SB) with (tk / 8 + 2147450884) in SHT4 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 4 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT4c & SEPT4q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 4 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT4t & _).
cbn [hl_sb A4L] in SEPT4c, SEPT4q, SEPT4t. assert (EQx : tk / 8 + A_SB + 4 = tk / 8 + 2147450884) by (unfold A_SB; lia). rewrite EQx in SEPT4c, SEPT4q, SEPT4t. clear EQx.
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
clear SEPT4c SEPT4q SEPT4t Ld.
stash Himg_t2.
try lazymatch goal with |- AJ5 _ _ _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) => replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
reenterA asegs A4L HIx asegs_wx HP.
do 3 step.
destruct OUT2 as [(-> & PBK2 & BK2) | [-> Epbs2]].
-
step.
if_true.
evt_done5.
assert (Hl2 : nth_error (t_levels ts2) (t_depth ts2) = Some l) by (unfold ts2, ts_pbs, ts0; cbn [t_levels t_depth]; exact Hl).
eapply (sesc_join_A HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo mp2 md2 A2 B2 ts2 l cb nb pj sv errv2 T (kP + 1));
[exact STC | exact INV2 | exact PBK2 | exact Hl2 | exact Hst | exact HMODE | exact Hzss |].
intros m'. intros until t6'. intros INV3 PBK3. unstash Kbreak.
eapply (Kbreak m' md2 A2 B2 pbs2 errv2); [exact INV3 | exact PBK3 | | exact FS2 | exact FRM2].
apply (BOK_lvl_restate (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) ts2 B2 nB l (tl_ss l) (tl_ss l) Hl2); [| eapply BOK_weaken; [| exact BK2]; lia].
intros CL. unfold lvl_closed in *. cbn [tl_st tl_ss]. apply andb_true_iff in CL as [CL _]. rewrite CL, Hzss. reflexivity.
-
replace (Z_to_bv 64 (2^64 - 1)) with (Z_to_bv 64 (-1)) by (apply bv_eq; vm_compute; reflexivity).
step.
if_false.
step.
step.
asan_rechkB.
step.
evt_done5.
unstash Kerr16. eapply (Kerr16 mp2 md2 A2 B2 errv2); [| exact FS2 | exact FRM2].
unfold ts2 in INV2. rewrite Epbs2 in INV2. exact INV2.
Qed.
End PeSSescLA.
End RC__1.
End Mq3.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QJjn QRUw.Mq0 QRUw QkMG. Import QG8z Qdyh.Mq0 Qdyh.Mq3 Qdyh.Mq4 QIsM.Mq2 Qa8x.Mq2.
Import Qhd4 Qwm6.
Import QbFI.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqj QsKa.Mqd Qiiq QsKa.Mqf Q4v2 QlKV.Mqf QSHS Ql4f.Mq4 Q1Y6.Mq4 QsKa.Mqh QrQv.Mq4 QEUF.Mq2 QW22.Mq8 QdGy.Mq9 QYZ0.Mq8 Qkko.Mq3.
Import Qc5u QAzu.Mq0.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section PeSSescQA.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_outside : forall m m' W, GA m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= hl_img_lo A4H \/ hl_img_hi A4H <= fst iv) W -> GA m'.
Hypothesis GA_pres : forall LB SP m m', heap_pres A4H LB SP m m' -> GA m -> GA m'.
Hypothesis MAPP : memappend_A_stmt2 HIx.

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

Ltac reopen_inv INVx TSx ts0 PF q LB0 tk mxd depth l Hl bse Hbse mX :=
pose proof INVx as [CORE2 REST2];
destruct CORE2 as (_ & _ & _ & _ & TOK & _ & _ & TSK & FR);
pose proof REST2 as (HP & _); clear REST2;
try unfold TSx in TOK, TSK; try unfold ts_pbs, ts_lvl, ts_set_x in TOK, TSK; try unfold ts0 in TOK, TSK;
cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_tk pf_mxd pf_fl] in TOK, TSK;
unfold tok_cells_g in TOK; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK;
unfold pe_frameA in FR; destruct FR as (SLOTS & _ & _ & _ & _); unfold pe_slotsA in SLOTS; cbn zeta in SLOTS;
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in SLOTS;
assert (INtk : In (tk, 72) (pe_blocksA PF q LB0 TSx)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity);
assert (INq : In (q, 32 * mxd) (pe_blocksA PF q LB0 TSx)) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity);
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI;
pose proof (wmono_refl asegs mX) as WM;
pose proof (TSK depth l Hl) as Ld; rewrite <- Hbse in Ld; unfold srec_cells in Ld;
clear TSK.

Lemma pe_memappend_cK :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP : Z)
(ra gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
PBOK m ts kP -> kP + 1 <= 1 -> forall kB : nat, BOK pf pa ts B kB -> bv_unsigned ra mod 2 = 0 ->
(forall m2 md2 A2 B2 pbs2 errv2 r (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : word) F2 fc2,
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m2 md2 A2 B2 (ts_pbs ts pbs2) cb nb pj sv errv2 ->
(r = 1 /\ PBOK m2 (ts_pbs ts pbs2) (kP + 1) /\ BOK pf pa (ts_pbs ts pbs2) B2 kB) \/ (r = 2^64 - 1 /\ pbs2 = t_pbs ts) ->
fsaved F F2 -> (frm0 fc -> frm0 fc2) ->
AJ5 A4L HIx A2 T md2
(MS (mkR ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) w0 w1 w2 s0 s1 (Z_to_bv 64 r) w3 w4 w5 w6 w7 w8 w9
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 w10 w11 w12 w13) F2 (ret_pc ra) fc2 None m2 (seg_rom asegs))) ->
AJ5 A4L HIx A T md
(MS (mkR ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2 s0 s1 (Z_to_bv 64 (t_pb ts)) (Z_to_bv 64 (pa_F pa + 64)) (Z_to_bv 64 1) a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x9b4fc) fc None m (seg_rom asegs)).
Proof.
intros until fc. intros STC BSL INV PBK HkP kB BK RA K.
pose proof STC as (_ & _ & GEO & _). pose proof GEO as (_ & _ & _ & GF & GF0 & _).
pose proof INV as [(_ & _ & _ & _ & _ & _ & _ & _ & FR1) _].
eapply (pe_memappend_g HIx GA GA_pres MAPP pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv T (pa_F pa + 64) 1 (t_co ts + kP) [cb]);
[exact STC | exact BSL | exact INV | exact PBK | lia | lia | exact BK | exact RA
| exact (pe_frameA_cbyte _ _ _ _ _ _ _ FR1) | reflexivity | lia
| right; first [left | idtac]; exists (pa_F pa), 2; split; [left; reflexivity | rewrite fr_size_2; lia]
| intros _; exact (pe_frameA_c_unpoisoned _ _ _ _ _ _ _ GEO FR1) |].
intros m2 md2 A2 B2 pbs2 errv2 r w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 F2 fc2 INV2 OUT2 FS2 FRM2.
eapply (K m2 md2 A2 B2 pbs2 errv2 r); [exact INV2 | | exact FS2 | exact FRM2].
destruct OUT2 as [(-> & PBK2 & BK2) | [-> E]]; [left | right; split; [reflexivity | exact E]].
split; [reflexivity|]. split; [| exact BK2]. unfold PBOK, ts_pbs. cbn [t_co]. replace (t_co ts + (kP + 1)) with (t_co ts + kP + 1) by lia. exact PBK2.
Qed.

Lemma sesc_quote_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP : Z) (nB : nat)
(gp t0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv -> PBOK m ts kP -> kP + 1 <= 1 -> BOK pf pa ts B (S nB) ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_string_escape ->
(forall c hn, lvl_mode (tl_st l) (tl_ss l) = Some (c, hn) -> lvl_mode (tl_ss l) (tl_ss l) = Some (c, hn)) ->
zin (tl_ss l) [ST_array_add; ST_ovadd] = false ->
(forall m' md' A' B' pbs' errv' gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B'
(ts_lvl (ts_pbs ts pbs') (TL (tl_ss l) (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) cb nb pj sv errv' ->
PBOK m' (ts_lvl (ts_pbs ts pbs') (TL (tl_ss l) (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) (kP + 1) ->
BOK pf pa (ts_lvl (ts_pbs ts pbs') (TL (tl_ss l) (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) B' nB ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msA asegs pf pa APE_BREAK (t_co ts) gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' (Z_to_bv 64 2) s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' m')) ->
(forall m' md' A' B' errv' x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' ts cb nb pj sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msX asegs pf pa APE_ERR3 x1' gp' t0' t1' t2' (Z_to_bv 64 16) a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' m')) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa 0x97f60 (t_co ts) gp t0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc m).
Proof.
intros until fc. intros STC BSL INV PBK HkP BK Hl Hst HMODE Hzss Kbreak Kerr16. pose proof INV as INV0. pe_openA STC INV.
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
pose proof FR as FR0. unfold pe_frameA in FR. destruct FR as (SLOTS & GAP & SAVED & FF & FSH).
unfold pe_slotsA in SLOTS. cbn zeta in SLOTS. unfold ff_cellsA in FF.
unfold pe_msA, pe_msX in *.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * mxd) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t.
blk_factsA A4L HIx HP q (32 * mxd) Hqal Hqlo Hqhi Himg_q.
pose proof (q_ne_tkA HIx _ _ _ _ _ _ _ _ _ _ HP) as Hqtk. cbn [pf_tk] in Hqtk.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ tk 72 q (32 * mxd) HP (in_or_app _ LM _ (or_introl INtk)) (in_or_app _ LM _ (or_introl INq)) ltac:(congruence)) as Hdtq.
pose proof (tok_shadowA HIx _ _ _ _ _ _ _ _ HP INtk) as SHT.
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
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 1 HP INtk ltac:(lia)) as SHT1.
replace (tk / 8 + 1 + A_SB) with (tk / 8 + 2147450881) in SHT1 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 1 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT1c & SEPT1q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 1 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT1t & _).
cbn [hl_sb A4L] in SEPT1c, SEPT1q, SEPT1t. assert (EQx : tk / 8 + A_SB + 1 = tk / 8 + 2147450881) by (unfold A_SB; lia). rewrite EQx in SEPT1c, SEPT1q, SEPT1t. clear EQx.
unfold APE_BREAK, APE_ERR3, APE_REDO, APE_OUT, APE_ERRMEM, APE_JTAB in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
clear Hdtq SEPT1c SEPT1q SEPT1t.
stash Himg_t. stash Himg_q. stash Kbreak. stash Kerr16. clear PB REST TSK LV OBJ HPR BUD GAP SAVED FSH FF STR ERR SBin SHT SHQ SHQ4 Ld MU.
reenterA asegs A4L HIx asegs_wx HP.
step.
asan_chkB.
step.
step. step.
step.
evt_done5.
eapply (pe_memappend_cK (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m md A B ts0 cb nb pj sv errv T kP);
[exact STC | exact BSL | exact INV0 | exact PBK | exact HkP | exact BK | rewrite unsigned_lit by lia; reflexivity |].
intros mp2 md2 A2 B2 pbs2 errv2 r w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 F2 fc2 INV2 OUT2 FS2 FRM2.
cbn [pf_spf] in *. unfold A_TP in *.
clear TOK SLOTS SHT1 WM MI HP INtk INq Htal Htlo Hthi Hqal Hqlo Hqhi Hqtk INV0 PBK BK.
set (ts2 := ts_pbs ts0 pbs2) in *.
reopen_inv INV2 ts2 ts0 (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 tk mxd depth l Hl bse Hbse mp2.
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t2.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 4 HP INtk ltac:(lia)) as SHT4.
replace (tk / 8 + 4 + A_SB) with (tk / 8 + 2147450884) in SHT4 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 4 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT4c & SEPT4q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 4 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT4t & _).
cbn [hl_sb A4L] in SEPT4c, SEPT4q, SEPT4t. assert (EQx : tk / 8 + A_SB + 4 = tk / 8 + 2147450884) by (unfold A_SB; lia). rewrite EQx in SEPT4c, SEPT4q, SEPT4t. clear EQx.
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
clear SEPT4c SEPT4q SEPT4t Ld.
stash Himg_t2.
try lazymatch goal with |- AJ5 _ _ _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) => replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
reenterA asegs A4L HIx asegs_wx HP.
destruct OUT2 as [(-> & PBK2 & BK2) | [-> Epbs2]].
- step.
if_true.
evt_done5.
assert (Hl2 : nth_error (t_levels ts2) (t_depth ts2) = Some l) by (unfold ts2, ts_pbs, ts0; cbn [t_levels t_depth]; exact Hl).
eapply (sesc_joinq_A HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo mp2 md2 A2 B2 ts2 l cb nb pj sv errv2 T (kP + 1));
[exact STC | exact INV2 | exact PBK2 | exact Hl2 | exact Hst | exact HMODE | exact Hzss |].
intros m'. intros until t6'. intros INV3 PBK3. unstash Kbreak.
eapply (Kbreak m' md2 A2 B2 pbs2 errv2); [exact INV3 | exact PBK3 | | exact FS2 | exact FRM2].
apply (BOK_lvl_restate (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) ts2 B2 nB l (tl_ss l) (tl_ss l) Hl2); [| eapply BOK_weaken; [| exact BK2]; lia].
intros CL. unfold lvl_closed in *. cbn [tl_st tl_ss]. apply andb_true_iff in CL as [CL _]. rewrite CL, Hzss. reflexivity.
- replace (Z_to_bv 64 (2^64 - 1)) with (Z_to_bv 64 (-1)) by (apply bv_eq; vm_compute; reflexivity).
step.
if_false.
step. step.
asan_rechkB.
step.
evt_done5.
unstash Kerr16. eapply (Kerr16 mp2 md2 A2 B2 errv2); [| exact FS2 | exact FRM2].
unfold ts2 in INV2. rewrite Epbs2 in INV2. exact INV2.
Qed.

Lemma sesc_u_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP : Z)
(gp t0 a1 a5 a6 a7 s3 s6 s7 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv -> PBOK m ts kP ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_string_escape ->
(forall c hn, lvl_mode (tl_st l) (tl_ss l) = Some (c, hn) -> lvl_mode ST_escape_unicode (tl_ss l) = Some (c, hn)) ->

(forall m' a0' a1' a3' a4' a6',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md A B
(ts_lvl (ts_set_x ts (t_co ts) (TS (ts_isd (t_x ts)) (Z_to_bv 64 0) (ts_choff (t_x ts)) (ts_err (t_x ts)) (Z_to_bv 64 0) (ts_high (t_x ts)) (ts_quote (t_x ts)))) (TL ST_escape_unicode (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) cb nb pj sv errv ->
PBOK m' (ts_lvl (ts_set_x ts (t_co ts) (TS (ts_isd (t_x ts)) (Z_to_bv 64 0) (ts_choff (t_x ts)) (ts_err (t_x ts)) (Z_to_bv 64 0) (ts_high (t_x ts)) (ts_quote (t_x ts)))) (TL ST_escape_unicode (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) kP ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa APE_BREAK (t_co ts) gp t0 a0' a1' (Z_to_bv 64 0) a3' a4' a5 a6' a7 s3 (Z_to_bv 64 2) s6 s7 (Z_to_bv 64 (Z.of_nat (t_depth ts))) s9 s11 t3 t4 t5 t6 F fc m')) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa 0x98180 (t_co ts) gp t0 (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) a1 (Z_to_bv 64 0) (Z_to_bv 64 (q / 8 + 4 * Z.of_nat (t_depth ts) + A_SB)) (Z_to_bv 64 0) a5 a6 a7 s3 (Z_to_bv 64 q) s6 s7 (Z_to_bv 64 (Z.of_nat (t_depth ts))) s9 s11 t3 t4 t5 t6 F fc m).
Proof.
intros until fc. intros STC INV PBK Hl Hst HMODE10 Kbreak. pose proof INV as INV0. pe_openA STC INV.
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
pose proof (tok_shadowA HIx _ _ _ _ _ _ _ _ HP INtk) as SHT.
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
shq_facts HP INq INtk q mxd tk (Z.of_nat depth) 0 SHQ0 SEPQ0c SEPQ0q SEPQ0t.
replace (q / 8 + 4 * (Z.of_nat depth) + 0 + A_SB) with (bse / 8 + 2147450880) in SHQ0 by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia).
assert (EQx : q / 8 + A_SB + (4 * (Z.of_nat depth) + 0) = bse / 8 + 2147450880) by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia). rewrite EQx in SEPQ0c, SEPQ0q, SEPQ0t. clear EQx.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 5 HP INtk ltac:(lia)) as SHT5.
replace (tk / 8 + 5 + A_SB) with (tk / 8 + 2147450885) in SHT5 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 5 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT5c & SEPT5q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 5 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT5t & _).
cbn [hl_sb A4L] in SEPT5c, SEPT5q, SEPT5t. assert (EQx : tk / 8 + A_SB + 5 = tk / 8 + 2147450885) by (unfold A_SB; lia). rewrite EQx in SEPT5c, SEPT5q, SEPT5t. clear EQx.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 3 HP INtk ltac:(lia)) as SHT3.
replace (tk / 8 + 3 + A_SB) with (tk / 8 + 2147450883) in SHT3 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 3 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT3c & SEPT3q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 3 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT3t & _).
cbn [hl_sb A4L] in SEPT3c, SEPT3q, SEPT3t. assert (EQx : tk / 8 + A_SB + 3 = tk / 8 + 2147450883) by (unfold A_SB; lia). rewrite EQx in SEPT3c, SEPT3q, SEPT3t. clear EQx.
unfold APE_BREAK, APE_REDO, APE_OUT, APE_ERRMEM, APE_JTAB in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
assert (cs_tk_L : csep tk 72 bse (Z.of_nat 32)) by (unfold csep; clear - Hdtq HbseR; lia).
assert (cs_L_tk : csep bse 32 tk (Z.of_nat 72)) by (unfold csep; clear - Hdtq HbseR; lia).
assert (cs_T3_T : csep (tk / 8 + 2147450883) 1 tk (Z.of_nat 72)) by (unfold csep; clear - SEPT3t; lia).
assert (cs_Q0_T : csep (bse / 8 + 2147450880) 1 tk (Z.of_nat 72)) by (unfold csep; clear - SEPQ0t; lia).
clear Hdtq SEPQ0c SEPQ0q SEPQ0t SEPT5c SEPT5q SEPT5t SEPT3c SEPT3q SEPT3t.
stash Himg_t. stash Himg_q. stash Kbreak. clear PB REST TSK LV OBJ HPR BUD GAP SAVED FSH FF STR ERR SBin SHT SHQ SHQ4 MU.
pose proof (munch_refl [(tk, tk + 72)] m) as MU.
reenterA asegs A4L HIx asegs_wx HP.
replace (q + 32 * Z.of_nat depth) with bse by lia.
step.
asan_chkB.
stepz.
step.
asan_chkB.
step.
stepz.
step. if_true.
replace (q / 8 + 4 * Z.of_nat depth + 2147450880) with (bse / 8 + 2147450880) by (rewrite Hbse, div8_add_mul32 by lia; lia).
asan_rechkB.
step.
set (x3 := TS isd (Z_to_bv 64 0) (Z_to_bv 64 co) err (Z_to_bv 64 0) high quote).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _ |- _ =>
destruct (PE_INV_A_tokw1 HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m mc md A B ts0
cb nb pj sv errv co x3 STC INV0 MUc WMc MIc TOKc ltac:(cbn [pf_len]; lia) eq_refl) as [INV3 PBT3];
clear MUc WMc; pose proof (munch_refl [(bse, bse + 32)] mc) as MUl; pose proof (wmono_refl asegs mc) as WMl
end end.
set (ts3 := ts_set_x ts0 co x3) in *.
stepz.
step. step.
assert (Hl3 : nth_error (t_levels ts3) (t_depth ts3) = Some l) by exact Hl.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mcF _) =>
lazymatch goal with MUc : munch _ ?mb mcF, WMc : wmono asegs ?mb mcF, MIc : mem_inv asegs mcF, TOKc : rw_cells asegs mcF tk _, Lc : rw_cells asegs mcF bse _ |- _ =>
evt_done5; rewrite Hbse in MUc, Lc;
destruct (PE_INV_A_lvl_write HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo mb mcF md A B ts3
cb nb pj sv errv l ST_escape_unicode (tl_ss l) c0 hn0 c0 STC INV3 Hl3 MUc WMc MIc TOKc Lc Hmode (HMODE10 c0 hn0 Hmode) ltac:(unfold ST_escape_unicode; lia) SS26 (or_introl eq_refl)
ltac:(rewrite Hst; reflexivity)) as [INV4 PBK4];
unstash Kbreak; eapply (Kbreak mcF); [exact INV4 | apply PBK4; unfold PBOK; cbn [t_co ts3 ts_set_x]; apply PBT3; exact PBK]
end end.
Qed.
End PeSSescQA.
End RC__1.
End Mq4.

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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qa8x.Mq2.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYZ0.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qkko.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qkko.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Lemma rodata_byte_at : forall m a v, mem_inv asegs m -> ro_bytes_b asegs a [Z_to_bv 8 v] = true -> 0 <= a -> a + 1 < 2^64 -> bytes_at asegs m a [Z_to_bv 8 v].
Proof.
intros m a v MI IMG Ha Hb. assert (RO : ro_cells asegs m a [CB 1 [Z_to_bv 8 v]]) by (apply ro_cells_image; [exact MI | exact IMG | exact Ha | cbn; lia]).
destruct RO as [_ H]. exact H.
Qed.

Section PeSSescLA.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_outside : forall m m' W, GA m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= hl_img_lo A4H \/ hl_img_hi A4H <= fst iv) W -> GA m'.
Hypothesis GA_pres : forall LB SP m m', heap_pres A4H LB SP m m' -> GA m -> GA m'.
Hypothesis MAPP : memappend_A_stmt2 HIx.

Ltac pe_openA STC INV :=
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR); pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk);
destruct INV as [CORE REST];
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR);
pose proof REST as (HP & LV & OBJ & ST & ERR & STR & PLEN & SBin & HPR & MDV & G & BUD).

Ltac reopen_inv INVx TSx ts0 PF q LB0 tk mxd depth l Hl bse Hbse mX :=
pose proof INVx as [CORE2 REST2];
destruct CORE2 as (_ & _ & _ & _ & TOK & _ & _ & TSK & FR);
pose proof REST2 as (HP & _); clear REST2;
try unfold TSx in TOK, TSK; try unfold ts_pbs, ts_lvl, ts_set_x in TOK, TSK; try unfold ts0 in TOK, TSK;
cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_tk pf_mxd pf_fl] in TOK, TSK;
unfold tok_cells_g in TOK; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK;
unfold pe_frameA in FR; destruct FR as (SLOTS & _ & _ & _ & _); unfold pe_slotsA in SLOTS; cbn zeta in SLOTS;
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in SLOTS;
assert (INtk : In (tk, 72) (pe_blocksA PF q LB0 TSx)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity);
assert (INq : In (q, 32 * mxd) (pe_blocksA PF q LB0 TSx)) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity);
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI;
pose proof (wmono_refl asegs mX) as WM;
pose proof (TSK depth l Hl) as Ld; rewrite <- Hbse in Ld; unfold srec_cells in Ld;
clear TSK.

Lemma pe_memappend_lit :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP xb v : Z)
(ra gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
PBOK m ts kP -> kP + 1 <= 1 -> forall kB : nat, BOK pf pa ts B kB -> bv_unsigned ra mod 2 = 0 ->
In xb [0x23140; 0x23160; 0x23180; 0x231a0; 0x231c0] -> ro_bytes_b asegs xb [Z_to_bv 8 v] = true ->
(forall m2 md2 A2 B2 pbs2 errv2 r (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : word) F2 fc2,
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m2 md2 A2 B2 (ts_pbs ts pbs2) cb nb pj sv errv2 ->
(r = 1 /\ PBOK m2 (ts_pbs ts pbs2) (kP + 1) /\ BOK pf pa (ts_pbs ts pbs2) B2 kB) \/ (r = 2^64 - 1 /\ pbs2 = t_pbs ts) ->
fsaved F F2 -> (frm0 fc -> frm0 fc2) ->
AJ5 A4L HIx A2 T md2
(MS (mkR ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) w0 w1 w2 s0 s1 (Z_to_bv 64 r) w3 w4 w5 w6 w7 w8 w9
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 w10 w11 w12 w13) F2 (ret_pc ra) fc2 None m2 (seg_rom asegs))) ->
AJ5 A4L HIx A T md
(MS (mkR ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2 s0 s1 (Z_to_bv 64 (t_pb ts)) (Z_to_bv 64 xb) (Z_to_bv 64 1) a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x9a0ac) fc None m (seg_rom asegs)).
Proof.
intros until fc. intros STC BSL INV PBK HkP kB BK RA Hxb IMG K.
pose proof INV as [_ (HP & _)]. pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
assert (Hxr : 0 <= xb /\ xb + 1 < 2^64) by (cbn in Hxb; repeat (destruct Hxb as [<- | Hxb]; [lia|]); destruct Hxb).
eapply (pe_memappend_g HIx GA GA_pres MAPP pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv T xb 1 (t_co ts + kP) [Z_to_bv 8 v]);
[exact STC | exact BSL | exact INV | exact PBK | lia | lia | exact BK | exact RA
| apply rodata_byte_at; [exact MI | exact IMG | lia | lia] | reflexivity | lia
| apply esc_src_locA; exact Hxb
| intros _; exact (unpoisoned_of_glob HIx _ _ _ _ _ _ _ _ _ HP (esc_src_globA xb Hxb) ltac:(lia)) |].
intros m2 md2 A2 B2 pbs2 errv2 r w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 F2 fc2 INV2 OUT2 FS2 FRM2.
eapply (K m2 md2 A2 B2 pbs2 errv2 r); [exact INV2 | | exact FS2 | exact FRM2].
destruct OUT2 as [(-> & PBK2 & BK2) | [-> E]]; [left | right; split; [reflexivity | exact E]].
split; [reflexivity|]. split; [| exact BK2]. unfold PBOK, ts_pbs. cbn [t_co]. replace (t_co ts + (kP + 1)) with (t_co ts + kP + 1) by lia. exact PBK2.
Qed.

Lemma sesc_lit_b_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP : Z) (nB : nat)
(gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv -> PBOK m ts kP -> kP + 1 <= 1 -> BOK pf pa ts B (S nB) ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_string_escape ->
(forall c hn, lvl_mode (tl_st l) (tl_ss l) = Some (c, hn) -> lvl_mode (tl_ss l) (tl_ss l) = Some (c, hn)) ->
zin (tl_ss l) [ST_array_add; ST_ovadd] = false ->

(forall m' md' A' B' pbs' errv' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' F' fc',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B'
(ts_lvl (ts_pbs ts pbs') (TL (tl_ss l) (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) cb nb pj sv errv' ->
PBOK m' (ts_lvl (ts_pbs ts pbs') (TL (tl_ss l) (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) (kP + 1) ->
BOK pf pa (ts_lvl (ts_pbs ts pbs') (TL (tl_ss l) (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) B' nB ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msA asegs pf pa APE_BREAK (t_co ts) gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5'
(Z_to_bv 64 (pf_tk pf + 56)) (Z_to_bv 64 (pa_F pa + 64)) F' fc' m')) ->

(forall m' md' A' B' errv' x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s5' t3' t4' t5' t6' F' fc',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' ts cb nb pj sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(Q1Y6.Mq2.pe_msE pf pa APE_ERR2 x1' gp' t0' t1' t2' (Z_to_bv 64 16) a1' a2' a3' a4' a5' a6' a7'
(Z_to_bv 64 (pf_tk pf / 8 + SB2)) (Z_to_bv 64 (pf_tk pf + 20)) s5' (Z_to_bv 64 (pf_tk pf + 36)) (Z_to_bv 64 (pf_tk pf + 32)) (Z_to_bv 64 (pa_F pa))
(Z_to_bv 64 (pf_tk pf + 56)) (Z_to_bv 64 (pf_sb pf + t_co ts)) t3' t4' t5' t6' F' fc' m')) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa 0x960a4 (t_co ts) gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 (Z_to_bv 64 (pf_tk pf + 56)) (Z_to_bv 64 (pa_F pa + 64)) F fc m).
Proof.
intros until fc. intros STC BSL INV PBK HkP BK Hl Hst HMODE Hzss Kbreak Kerr16. pose proof INV as INV0. pe_openA STC INV.
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
pose proof FR as FR0. unfold pe_frameA in FR. destruct FR as (SLOTS & GAP & SAVED & FF & FSH).
unfold pe_slotsA in SLOTS. cbn zeta in SLOTS. unfold ff_cellsA in FF.
unfold pe_msA, Q1Y6.Mq2.pe_msE in *.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * mxd) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t.
blk_factsA A4L HIx HP q (32 * mxd) Hqal Hqlo Hqhi Himg_q.
pose proof (q_ne_tkA HIx _ _ _ _ _ _ _ _ _ _ HP) as Hqtk. cbn [pf_tk] in Hqtk.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ tk 72 q (32 * mxd) HP (in_or_app _ LM _ (or_introl INtk)) (in_or_app _ LM _ (or_introl INq)) ltac:(congruence)) as Hdtq.
pose proof (tok_shadowA HIx _ _ _ _ _ _ _ _ HP INtk) as SHT.
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
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 1 HP INtk ltac:(lia)) as SHT1.
replace (tk / 8 + 1 + A_SB) with (tk / 8 + 2147450881) in SHT1 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 1 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT1c & SEPT1q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 1 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT1t & _).
cbn [hl_sb A4L] in SEPT1c, SEPT1q, SEPT1t. assert (EQx : tk / 8 + A_SB + 1 = tk / 8 + 2147450881) by (unfold A_SB; lia). rewrite EQx in SEPT1c, SEPT1q, SEPT1t. clear EQx.
unfold APE_BREAK, APE_ERR2, APE_REDO, APE_OUT, APE_ERRMEM, APE_ERRST, APE_JTAB in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
clear Hdtq SEPT1c SEPT1q SEPT1t.
stash Himg_t. stash Himg_q. stash Kbreak. stash Kerr16. clear PB REST TSK LV OBJ HPR BUD GAP SAVED FSH FF STR ERR SBin SHT SHQ SHQ4 Ld MU.
reenterA asegs A4L HIx asegs_wx HP.
step.
asan_chkA.
step.
step. step.
step.
step.
evt_done5.
eapply (pe_memappend_lit (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m md A B ts0 cb nb pj sv errv T kP 0x23140 8);
[exact STC | exact BSL | exact INV0 | exact PBK | exact HkP | exact BK | rewrite unsigned_lit by lia; reflexivity | cbn; tauto | vm_compute; reflexivity |].
intros mp2 md2 A2 B2 pbs2 errv2 r w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 F2 fc2 INV2 OUT2 FS2 FRM2.
cbn [pf_spf] in *. unfold A_TP in *.
clear TOK SLOTS SHT1 WM MI HP INtk INq Htal Htlo Hthi Hqal Hqlo Hqhi Hqtk INV0 PBK BK.
set (ts2 := ts_pbs ts0 pbs2) in *.
reopen_inv INV2 ts2 ts0 (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 tk mxd depth l Hl bse Hbse mp2.
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t2.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 4 HP INtk ltac:(lia)) as SHT4.
replace (tk / 8 + 4 + A_SB) with (tk / 8 + 2147450884) in SHT4 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 4 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT4c & SEPT4q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 4 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT4t & _).
cbn [hl_sb A4L] in SEPT4c, SEPT4q, SEPT4t. assert (EQx : tk / 8 + A_SB + 4 = tk / 8 + 2147450884) by (unfold A_SB; lia). rewrite EQx in SEPT4c, SEPT4q, SEPT4t. clear EQx.
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
clear SEPT4c SEPT4q SEPT4t Ld.
stash Himg_t2.
try lazymatch goal with |- AJ5 _ _ _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) => replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
reenterA asegs A4L HIx asegs_wx HP.
do 5 step.
destruct OUT2 as [(-> & PBK2 & BK2) | [-> Epbs2]].
-
step.
if_false.
step.
evt_done5.
assert (Hl2 : nth_error (t_levels ts2) (t_depth ts2) = Some l) by (unfold ts2, ts_pbs, ts0; cbn [t_levels t_depth]; exact Hl).
eapply (sesc_join_A HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo mp2 md2 A2 B2 ts2 l cb nb pj sv errv2 T (kP + 1));
[exact STC | exact INV2 | exact PBK2 | exact Hl2 | exact Hst | exact HMODE | exact Hzss |].
intros m' a0' a1' a2' a3' INV3 PBK3. unstash Kbreak.
eapply (Kbreak m' md2 A2 B2 pbs2 errv2); [exact INV3 | exact PBK3 | | exact FS2 | exact FRM2].
apply (BOK_lvl_restate (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) ts2 B2 nB l (tl_ss l) (tl_ss l) Hl2); [| eapply BOK_weaken; [| exact BK2]; lia].
intros CL. unfold lvl_closed in *. cbn [tl_st tl_ss]. apply andb_true_iff in CL as [CL _]. rewrite CL, Hzss. reflexivity.
-
replace (Z_to_bv 64 (2^64 - 1)) with (Z_to_bv 64 (-1)) by (apply bv_eq; vm_compute; reflexivity).
step.
if_true.
step.
step.
asan_rechkA.
step.
evt_done5.
unstash Kerr16. eapply (Kerr16 mp2 md2 A2 B2 errv2); [| exact FS2 | exact FRM2].
unfold ts2 in INV2. rewrite Epbs2 in INV2. exact INV2.
Qed.

Lemma sesc_lit_f_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP : Z) (nB : nat)
(gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv -> PBOK m ts kP -> kP + 1 <= 1 -> BOK pf pa ts B (S nB) ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_string_escape ->
(forall c hn, lvl_mode (tl_st l) (tl_ss l) = Some (c, hn) -> lvl_mode (tl_ss l) (tl_ss l) = Some (c, hn)) ->
zin (tl_ss l) [ST_array_add; ST_ovadd] = false ->

(forall m' md' A' B' pbs' errv' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' F' fc',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B'
(ts_lvl (ts_pbs ts pbs') (TL (tl_ss l) (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) cb nb pj sv errv' ->
PBOK m' (ts_lvl (ts_pbs ts pbs') (TL (tl_ss l) (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) (kP + 1) ->
BOK pf pa (ts_lvl (ts_pbs ts pbs') (TL (tl_ss l) (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) B' nB ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msA asegs pf pa APE_BREAK (t_co ts) gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5'
(Z_to_bv 64 (pf_tk pf + 56)) (Z_to_bv 64 (pa_F pa + 64)) F' fc' m')) ->

(forall m' md' A' B' errv' x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s5' t3' t4' t5' t6' F' fc',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' ts cb nb pj sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(Q1Y6.Mq2.pe_msE pf pa APE_ERR2 x1' gp' t0' t1' t2' (Z_to_bv 64 16) a1' a2' a3' a4' a5' a6' a7'
(Z_to_bv 64 (pf_tk pf / 8 + SB2)) (Z_to_bv 64 (pf_tk pf + 20)) s5' (Z_to_bv 64 (pf_tk pf + 36)) (Z_to_bv 64 (pf_tk pf + 32)) (Z_to_bv 64 (pa_F pa))
(Z_to_bv 64 (pf_tk pf + 56)) (Z_to_bv 64 (pf_sb pf + t_co ts)) t3' t4' t5' t6' F' fc' m')) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa 0x970cc (t_co ts) gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 (Z_to_bv 64 (pf_tk pf + 56)) (Z_to_bv 64 (pa_F pa + 64)) F fc m).
Proof.
intros until fc. intros STC BSL INV PBK HkP BK Hl Hst HMODE Hzss Kbreak Kerr16. pose proof INV as INV0. pe_openA STC INV.
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
pose proof FR as FR0. unfold pe_frameA in FR. destruct FR as (SLOTS & GAP & SAVED & FF & FSH).
unfold pe_slotsA in SLOTS. cbn zeta in SLOTS. unfold ff_cellsA in FF.
unfold pe_msA, Q1Y6.Mq2.pe_msE in *.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * mxd) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t.
blk_factsA A4L HIx HP q (32 * mxd) Hqal Hqlo Hqhi Himg_q.
pose proof (q_ne_tkA HIx _ _ _ _ _ _ _ _ _ _ HP) as Hqtk. cbn [pf_tk] in Hqtk.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ tk 72 q (32 * mxd) HP (in_or_app _ LM _ (or_introl INtk)) (in_or_app _ LM _ (or_introl INq)) ltac:(congruence)) as Hdtq.
pose proof (tok_shadowA HIx _ _ _ _ _ _ _ _ HP INtk) as SHT.
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
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 1 HP INtk ltac:(lia)) as SHT1.
replace (tk / 8 + 1 + A_SB) with (tk / 8 + 2147450881) in SHT1 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 1 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT1c & SEPT1q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 1 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT1t & _).
cbn [hl_sb A4L] in SEPT1c, SEPT1q, SEPT1t. assert (EQx : tk / 8 + A_SB + 1 = tk / 8 + 2147450881) by (unfold A_SB; lia). rewrite EQx in SEPT1c, SEPT1q, SEPT1t. clear EQx.
unfold APE_BREAK, APE_ERR2, APE_REDO, APE_OUT, APE_ERRMEM, APE_ERRST, APE_JTAB in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
clear Hdtq SEPT1c SEPT1q SEPT1t.
stash Himg_t. stash Himg_q. stash Kbreak. stash Kerr16. clear PB REST TSK LV OBJ HPR BUD GAP SAVED FSH FF STR ERR SBin SHT SHQ SHQ4 Ld MU.
reenterA asegs A4L HIx asegs_wx HP.
step.
asan_chkA.
step.
step. step.
step.
step.
evt_done5.
eapply (pe_memappend_lit (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m md A B ts0 cb nb pj sv errv T kP 0x231c0 12);
[exact STC | exact BSL | exact INV0 | exact PBK | exact HkP | exact BK | rewrite unsigned_lit by lia; reflexivity | cbn; tauto | vm_compute; reflexivity |].
intros mp2 md2 A2 B2 pbs2 errv2 r w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 F2 fc2 INV2 OUT2 FS2 FRM2.
cbn [pf_spf] in *. unfold A_TP in *.
clear TOK SLOTS SHT1 WM MI HP INtk INq Htal Htlo Hthi Hqal Hqlo Hqhi Hqtk INV0 PBK BK.
set (ts2 := ts_pbs ts0 pbs2) in *.
reopen_inv INV2 ts2 ts0 (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 tk mxd depth l Hl bse Hbse mp2.
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t2.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 4 HP INtk ltac:(lia)) as SHT4.
replace (tk / 8 + 4 + A_SB) with (tk / 8 + 2147450884) in SHT4 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 4 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT4c & SEPT4q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 4 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT4t & _).
cbn [hl_sb A4L] in SEPT4c, SEPT4q, SEPT4t. assert (EQx : tk / 8 + A_SB + 4 = tk / 8 + 2147450884) by (unfold A_SB; lia). rewrite EQx in SEPT4c, SEPT4q, SEPT4t. clear EQx.
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
clear SEPT4c SEPT4q SEPT4t Ld.
stash Himg_t2.
try lazymatch goal with |- AJ5 _ _ _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) => replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
reenterA asegs A4L HIx asegs_wx HP.
do 5 step.
destruct OUT2 as [(-> & PBK2 & BK2) | [-> Epbs2]].
-
step.
if_true.
evt_done5.
assert (Hl2 : nth_error (t_levels ts2) (t_depth ts2) = Some l) by (unfold ts2, ts_pbs, ts0; cbn [t_levels t_depth]; exact Hl).
eapply (sesc_join_A HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo mp2 md2 A2 B2 ts2 l cb nb pj sv errv2 T (kP + 1));
[exact STC | exact INV2 | exact PBK2 | exact Hl2 | exact Hst | exact HMODE | exact Hzss |].
intros m' a0' a1' a2' a3' INV3 PBK3. unstash Kbreak.
eapply (Kbreak m' md2 A2 B2 pbs2 errv2); [exact INV3 | exact PBK3 | | exact FS2 | exact FRM2].
apply (BOK_lvl_restate (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) ts2 B2 nB l (tl_ss l) (tl_ss l) Hl2); [| eapply BOK_weaken; [| exact BK2]; lia].
intros CL. unfold lvl_closed in *. cbn [tl_st tl_ss]. apply andb_true_iff in CL as [CL _]. rewrite CL, Hzss. reflexivity.
-
replace (Z_to_bv 64 (2^64 - 1)) with (Z_to_bv 64 (-1)) by (apply bv_eq; vm_compute; reflexivity).
step.
if_false.
step.
step.
asan_rechkA.
step.
evt_done5.
unstash Kerr16. eapply (Kerr16 mp2 md2 A2 B2 errv2); [| exact FS2 | exact FRM2].
unfold ts2 in INV2. rewrite Epbs2 in INV2. exact INV2.
Qed.

Lemma sesc_lit_n_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP : Z) (nB : nat)
(gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv -> PBOK m ts kP -> kP + 1 <= 1 -> BOK pf pa ts B (S nB) ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_string_escape ->
(forall c hn, lvl_mode (tl_st l) (tl_ss l) = Some (c, hn) -> lvl_mode (tl_ss l) (tl_ss l) = Some (c, hn)) ->
zin (tl_ss l) [ST_array_add; ST_ovadd] = false ->

(forall m' md' A' B' pbs' errv' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' F' fc',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B'
(ts_lvl (ts_pbs ts pbs') (TL (tl_ss l) (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) cb nb pj sv errv' ->
PBOK m' (ts_lvl (ts_pbs ts pbs') (TL (tl_ss l) (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) (kP + 1) ->
BOK pf pa (ts_lvl (ts_pbs ts pbs') (TL (tl_ss l) (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) B' nB ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msA asegs pf pa APE_BREAK (t_co ts) gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5'
(Z_to_bv 64 (pf_tk pf + 56)) (Z_to_bv 64 (pa_F pa + 64)) F' fc' m')) ->

(forall m' md' A' B' errv' x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s5' t3' t4' t5' t6' F' fc',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' ts cb nb pj sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(Q1Y6.Mq2.pe_msE pf pa APE_ERR2 x1' gp' t0' t1' t2' (Z_to_bv 64 16) a1' a2' a3' a4' a5' a6' a7'
(Z_to_bv 64 (pf_tk pf / 8 + SB2)) (Z_to_bv 64 (pf_tk pf + 20)) s5' (Z_to_bv 64 (pf_tk pf + 36)) (Z_to_bv 64 (pf_tk pf + 32)) (Z_to_bv 64 (pa_F pa))
(Z_to_bv 64 (pf_tk pf + 56)) (Z_to_bv 64 (pf_sb pf + t_co ts)) t3' t4' t5' t6' F' fc' m')) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa 0x97084 (t_co ts) gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 (Z_to_bv 64 (pf_tk pf + 56)) (Z_to_bv 64 (pa_F pa + 64)) F fc m).
Proof.
intros until fc. intros STC BSL INV PBK HkP BK Hl Hst HMODE Hzss Kbreak Kerr16. pose proof INV as INV0. pe_openA STC INV.
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
pose proof FR as FR0. unfold pe_frameA in FR. destruct FR as (SLOTS & GAP & SAVED & FF & FSH).
unfold pe_slotsA in SLOTS. cbn zeta in SLOTS. unfold ff_cellsA in FF.
unfold pe_msA, Q1Y6.Mq2.pe_msE in *.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * mxd) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t.
blk_factsA A4L HIx HP q (32 * mxd) Hqal Hqlo Hqhi Himg_q.
pose proof (q_ne_tkA HIx _ _ _ _ _ _ _ _ _ _ HP) as Hqtk. cbn [pf_tk] in Hqtk.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ tk 72 q (32 * mxd) HP (in_or_app _ LM _ (or_introl INtk)) (in_or_app _ LM _ (or_introl INq)) ltac:(congruence)) as Hdtq.
pose proof (tok_shadowA HIx _ _ _ _ _ _ _ _ HP INtk) as SHT.
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
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 1 HP INtk ltac:(lia)) as SHT1.
replace (tk / 8 + 1 + A_SB) with (tk / 8 + 2147450881) in SHT1 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 1 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT1c & SEPT1q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 1 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT1t & _).
cbn [hl_sb A4L] in SEPT1c, SEPT1q, SEPT1t. assert (EQx : tk / 8 + A_SB + 1 = tk / 8 + 2147450881) by (unfold A_SB; lia). rewrite EQx in SEPT1c, SEPT1q, SEPT1t. clear EQx.
unfold APE_BREAK, APE_ERR2, APE_REDO, APE_OUT, APE_ERRMEM, APE_ERRST, APE_JTAB in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
clear Hdtq SEPT1c SEPT1q SEPT1t.
stash Himg_t. stash Himg_q. stash Kbreak. stash Kerr16. clear PB REST TSK LV OBJ HPR BUD GAP SAVED FSH FF STR ERR SBin SHT SHQ SHQ4 Ld MU.
reenterA asegs A4L HIx asegs_wx HP.
step.
asan_chkA.
step.
step. step.
step.
step.
evt_done5.
eapply (pe_memappend_lit (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m md A B ts0 cb nb pj sv errv T kP 0x23160 10);
[exact STC | exact BSL | exact INV0 | exact PBK | exact HkP | exact BK | rewrite unsigned_lit by lia; reflexivity | cbn; tauto | vm_compute; reflexivity |].
intros mp2 md2 A2 B2 pbs2 errv2 r w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 F2 fc2 INV2 OUT2 FS2 FRM2.
cbn [pf_spf] in *. unfold A_TP in *.
clear TOK SLOTS SHT1 WM MI HP INtk INq Htal Htlo Hthi Hqal Hqlo Hqhi Hqtk INV0 PBK BK.
set (ts2 := ts_pbs ts0 pbs2) in *.
reopen_inv INV2 ts2 ts0 (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 tk mxd depth l Hl bse Hbse mp2.
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t2.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 4 HP INtk ltac:(lia)) as SHT4.
replace (tk / 8 + 4 + A_SB) with (tk / 8 + 2147450884) in SHT4 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 4 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT4c & SEPT4q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 4 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT4t & _).
cbn [hl_sb A4L] in SEPT4c, SEPT4q, SEPT4t. assert (EQx : tk / 8 + A_SB + 4 = tk / 8 + 2147450884) by (unfold A_SB; lia). rewrite EQx in SEPT4c, SEPT4q, SEPT4t. clear EQx.
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
clear SEPT4c SEPT4q SEPT4t Ld.
stash Himg_t2.
try lazymatch goal with |- AJ5 _ _ _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) => replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
reenterA asegs A4L HIx asegs_wx HP.
do 5 step.
destruct OUT2 as [(-> & PBK2 & BK2) | [-> Epbs2]].
-
step.
if_true.
evt_done5.
assert (Hl2 : nth_error (t_levels ts2) (t_depth ts2) = Some l) by (unfold ts2, ts_pbs, ts0; cbn [t_levels t_depth]; exact Hl).
eapply (sesc_join_A HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo mp2 md2 A2 B2 ts2 l cb nb pj sv errv2 T (kP + 1));
[exact STC | exact INV2 | exact PBK2 | exact Hl2 | exact Hst | exact HMODE | exact Hzss |].
intros m' a0' a1' a2' a3' INV3 PBK3. unstash Kbreak.
eapply (Kbreak m' md2 A2 B2 pbs2 errv2); [exact INV3 | exact PBK3 | | exact FS2 | exact FRM2].
apply (BOK_lvl_restate (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) ts2 B2 nB l (tl_ss l) (tl_ss l) Hl2); [| eapply BOK_weaken; [| exact BK2]; lia].
intros CL. unfold lvl_closed in *. cbn [tl_st tl_ss]. apply andb_true_iff in CL as [CL _]. rewrite CL, Hzss. reflexivity.
-
replace (Z_to_bv 64 (2^64 - 1)) with (Z_to_bv 64 (-1)) by (apply bv_eq; vm_compute; reflexivity).
step.
if_false.
step.
step.
asan_rechkA.
step.
evt_done5.
unstash Kerr16. eapply (Kerr16 mp2 md2 A2 B2 errv2); [| exact FS2 | exact FRM2].
unfold ts2 in INV2. rewrite Epbs2 in INV2. exact INV2.
Qed.

Lemma sesc_lit_r_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP : Z) (nB : nat)
(gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv -> PBOK m ts kP -> kP + 1 <= 1 -> BOK pf pa ts B (S nB) ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_string_escape ->
(forall c hn, lvl_mode (tl_st l) (tl_ss l) = Some (c, hn) -> lvl_mode (tl_ss l) (tl_ss l) = Some (c, hn)) ->
zin (tl_ss l) [ST_array_add; ST_ovadd] = false ->

(forall m' md' A' B' pbs' errv' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' F' fc',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B'
(ts_lvl (ts_pbs ts pbs') (TL (tl_ss l) (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) cb nb pj sv errv' ->
PBOK m' (ts_lvl (ts_pbs ts pbs') (TL (tl_ss l) (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) (kP + 1) ->
BOK pf pa (ts_lvl (ts_pbs ts pbs') (TL (tl_ss l) (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) B' nB ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msA asegs pf pa APE_BREAK (t_co ts) gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5'
(Z_to_bv 64 (pf_tk pf + 56)) (Z_to_bv 64 (pa_F pa + 64)) F' fc' m')) ->

(forall m' md' A' B' errv' x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s5' t3' t4' t5' t6' F' fc',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' ts cb nb pj sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(Q1Y6.Mq2.pe_msE pf pa APE_ERR2 x1' gp' t0' t1' t2' (Z_to_bv 64 16) a1' a2' a3' a4' a5' a6' a7'
(Z_to_bv 64 (pf_tk pf / 8 + SB2)) (Z_to_bv 64 (pf_tk pf + 20)) s5' (Z_to_bv 64 (pf_tk pf + 36)) (Z_to_bv 64 (pf_tk pf + 32)) (Z_to_bv 64 (pa_F pa))
(Z_to_bv 64 (pf_tk pf + 56)) (Z_to_bv 64 (pf_sb pf + t_co ts)) t3' t4' t5' t6' F' fc' m')) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa 0x97114 (t_co ts) gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 (Z_to_bv 64 (pf_tk pf + 56)) (Z_to_bv 64 (pa_F pa + 64)) F fc m).
Proof.
intros until fc. intros STC BSL INV PBK HkP BK Hl Hst HMODE Hzss Kbreak Kerr16. pose proof INV as INV0. pe_openA STC INV.
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
pose proof FR as FR0. unfold pe_frameA in FR. destruct FR as (SLOTS & GAP & SAVED & FF & FSH).
unfold pe_slotsA in SLOTS. cbn zeta in SLOTS. unfold ff_cellsA in FF.
unfold pe_msA, Q1Y6.Mq2.pe_msE in *.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * mxd) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t.
blk_factsA A4L HIx HP q (32 * mxd) Hqal Hqlo Hqhi Himg_q.
pose proof (q_ne_tkA HIx _ _ _ _ _ _ _ _ _ _ HP) as Hqtk. cbn [pf_tk] in Hqtk.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ tk 72 q (32 * mxd) HP (in_or_app _ LM _ (or_introl INtk)) (in_or_app _ LM _ (or_introl INq)) ltac:(congruence)) as Hdtq.
pose proof (tok_shadowA HIx _ _ _ _ _ _ _ _ HP INtk) as SHT.
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
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 1 HP INtk ltac:(lia)) as SHT1.
replace (tk / 8 + 1 + A_SB) with (tk / 8 + 2147450881) in SHT1 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 1 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT1c & SEPT1q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 1 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT1t & _).
cbn [hl_sb A4L] in SEPT1c, SEPT1q, SEPT1t. assert (EQx : tk / 8 + A_SB + 1 = tk / 8 + 2147450881) by (unfold A_SB; lia). rewrite EQx in SEPT1c, SEPT1q, SEPT1t. clear EQx.
unfold APE_BREAK, APE_ERR2, APE_REDO, APE_OUT, APE_ERRMEM, APE_ERRST, APE_JTAB in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
clear Hdtq SEPT1c SEPT1q SEPT1t.
stash Himg_t. stash Himg_q. stash Kbreak. stash Kerr16. clear PB REST TSK LV OBJ HPR BUD GAP SAVED FSH FF STR ERR SBin SHT SHQ SHQ4 Ld MU.
reenterA asegs A4L HIx asegs_wx HP.
step.
asan_chkA.
step.
step. step.
step.
step.
evt_done5.
eapply (pe_memappend_lit (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m md A B ts0 cb nb pj sv errv T kP 0x23180 13);
[exact STC | exact BSL | exact INV0 | exact PBK | exact HkP | exact BK | rewrite unsigned_lit by lia; reflexivity | cbn; tauto | vm_compute; reflexivity |].
intros mp2 md2 A2 B2 pbs2 errv2 r w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 F2 fc2 INV2 OUT2 FS2 FRM2.
cbn [pf_spf] in *. unfold A_TP in *.
clear TOK SLOTS SHT1 WM MI HP INtk INq Htal Htlo Hthi Hqal Hqlo Hqhi Hqtk INV0 PBK BK.
set (ts2 := ts_pbs ts0 pbs2) in *.
reopen_inv INV2 ts2 ts0 (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 tk mxd depth l Hl bse Hbse mp2.
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t2.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 4 HP INtk ltac:(lia)) as SHT4.
replace (tk / 8 + 4 + A_SB) with (tk / 8 + 2147450884) in SHT4 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 4 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT4c & SEPT4q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 4 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT4t & _).
cbn [hl_sb A4L] in SEPT4c, SEPT4q, SEPT4t. assert (EQx : tk / 8 + A_SB + 4 = tk / 8 + 2147450884) by (unfold A_SB; lia). rewrite EQx in SEPT4c, SEPT4q, SEPT4t. clear EQx.
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
clear SEPT4c SEPT4q SEPT4t Ld.
stash Himg_t2.
try lazymatch goal with |- AJ5 _ _ _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) => replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
reenterA asegs A4L HIx asegs_wx HP.
do 5 step.
destruct OUT2 as [(-> & PBK2 & BK2) | [-> Epbs2]].
-
step.
if_true.
evt_done5.
assert (Hl2 : nth_error (t_levels ts2) (t_depth ts2) = Some l) by (unfold ts2, ts_pbs, ts0; cbn [t_levels t_depth]; exact Hl).
eapply (sesc_join_A HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo mp2 md2 A2 B2 ts2 l cb nb pj sv errv2 T (kP + 1));
[exact STC | exact INV2 | exact PBK2 | exact Hl2 | exact Hst | exact HMODE | exact Hzss |].
intros m' a0' a1' a2' a3' INV3 PBK3. unstash Kbreak.
eapply (Kbreak m' md2 A2 B2 pbs2 errv2); [exact INV3 | exact PBK3 | | exact FS2 | exact FRM2].
apply (BOK_lvl_restate (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) ts2 B2 nB l (tl_ss l) (tl_ss l) Hl2); [| eapply BOK_weaken; [| exact BK2]; lia].
intros CL. unfold lvl_closed in *. cbn [tl_st tl_ss]. apply andb_true_iff in CL as [CL _]. rewrite CL, Hzss. reflexivity.
-
replace (Z_to_bv 64 (2^64 - 1)) with (Z_to_bv 64 (-1)) by (apply bv_eq; vm_compute; reflexivity).
step.
if_false.
step.
step.
asan_rechkA.
step.
evt_done5.
unstash Kerr16. eapply (Kerr16 mp2 md2 A2 B2 errv2); [| exact FS2 | exact FRM2].
unfold ts2 in INV2. rewrite Epbs2 in INV2. exact INV2.
Qed.

Lemma sesc_lit_t_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP : Z) (nB : nat)
(gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv -> PBOK m ts kP -> kP + 1 <= 1 -> BOK pf pa ts B (S nB) ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_string_escape ->
(forall c hn, lvl_mode (tl_st l) (tl_ss l) = Some (c, hn) -> lvl_mode (tl_ss l) (tl_ss l) = Some (c, hn)) ->
zin (tl_ss l) [ST_array_add; ST_ovadd] = false ->

(forall m' md' A' B' pbs' errv' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' F' fc',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B'
(ts_lvl (ts_pbs ts pbs') (TL (tl_ss l) (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) cb nb pj sv errv' ->
PBOK m' (ts_lvl (ts_pbs ts pbs') (TL (tl_ss l) (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) (kP + 1) ->
BOK pf pa (ts_lvl (ts_pbs ts pbs') (TL (tl_ss l) (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) B' nB ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msA asegs pf pa APE_BREAK (t_co ts) gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5'
(Z_to_bv 64 (pf_tk pf + 56)) (Z_to_bv 64 (pa_F pa + 64)) F' fc' m')) ->

(forall m' md' A' B' errv' x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s5' t3' t4' t5' t6' F' fc',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' ts cb nb pj sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(Q1Y6.Mq2.pe_msE pf pa APE_ERR2 x1' gp' t0' t1' t2' (Z_to_bv 64 16) a1' a2' a3' a4' a5' a6' a7'
(Z_to_bv 64 (pf_tk pf / 8 + SB2)) (Z_to_bv 64 (pf_tk pf + 20)) s5' (Z_to_bv 64 (pf_tk pf + 36)) (Z_to_bv 64 (pf_tk pf + 32)) (Z_to_bv 64 (pa_F pa))
(Z_to_bv 64 (pf_tk pf + 56)) (Z_to_bv 64 (pf_sb pf + t_co ts)) t3' t4' t5' t6' F' fc' m')) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa 0x9715c (t_co ts) gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 (Z_to_bv 64 (pf_tk pf + 56)) (Z_to_bv 64 (pa_F pa + 64)) F fc m).
Proof.
intros until fc. intros STC BSL INV PBK HkP BK Hl Hst HMODE Hzss Kbreak Kerr16. pose proof INV as INV0. pe_openA STC INV.
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
pose proof FR as FR0. unfold pe_frameA in FR. destruct FR as (SLOTS & GAP & SAVED & FF & FSH).
unfold pe_slotsA in SLOTS. cbn zeta in SLOTS. unfold ff_cellsA in FF.
unfold pe_msA, Q1Y6.Mq2.pe_msE in *.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * mxd) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t.
blk_factsA A4L HIx HP q (32 * mxd) Hqal Hqlo Hqhi Himg_q.
pose proof (q_ne_tkA HIx _ _ _ _ _ _ _ _ _ _ HP) as Hqtk. cbn [pf_tk] in Hqtk.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ tk 72 q (32 * mxd) HP (in_or_app _ LM _ (or_introl INtk)) (in_or_app _ LM _ (or_introl INq)) ltac:(congruence)) as Hdtq.
pose proof (tok_shadowA HIx _ _ _ _ _ _ _ _ HP INtk) as SHT.
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
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 1 HP INtk ltac:(lia)) as SHT1.
replace (tk / 8 + 1 + A_SB) with (tk / 8 + 2147450881) in SHT1 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 1 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT1c & SEPT1q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 1 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT1t & _).
cbn [hl_sb A4L] in SEPT1c, SEPT1q, SEPT1t. assert (EQx : tk / 8 + A_SB + 1 = tk / 8 + 2147450881) by (unfold A_SB; lia). rewrite EQx in SEPT1c, SEPT1q, SEPT1t. clear EQx.
unfold APE_BREAK, APE_ERR2, APE_REDO, APE_OUT, APE_ERRMEM, APE_ERRST, APE_JTAB in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
clear Hdtq SEPT1c SEPT1q SEPT1t.
stash Himg_t. stash Himg_q. stash Kbreak. stash Kerr16. clear PB REST TSK LV OBJ HPR BUD GAP SAVED FSH FF STR ERR SBin SHT SHQ SHQ4 Ld MU.
reenterA asegs A4L HIx asegs_wx HP.
step.
asan_chkA.
step.
step. step.
step.
step.
evt_done5.
eapply (pe_memappend_lit (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m md A B ts0 cb nb pj sv errv T kP 0x231a0 9);
[exact STC | exact BSL | exact INV0 | exact PBK | exact HkP | exact BK | rewrite unsigned_lit by lia; reflexivity | cbn; tauto | vm_compute; reflexivity |].
intros mp2 md2 A2 B2 pbs2 errv2 r w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 F2 fc2 INV2 OUT2 FS2 FRM2.
cbn [pf_spf] in *. unfold A_TP in *.
clear TOK SLOTS SHT1 WM MI HP INtk INq Htal Htlo Hthi Hqal Hqlo Hqhi Hqtk INV0 PBK BK.
set (ts2 := ts_pbs ts0 pbs2) in *.
reopen_inv INV2 ts2 ts0 (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 tk mxd depth l Hl bse Hbse mp2.
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t2.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 4 HP INtk ltac:(lia)) as SHT4.
replace (tk / 8 + 4 + A_SB) with (tk / 8 + 2147450884) in SHT4 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 4 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT4c & SEPT4q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 4 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT4t & _).
cbn [hl_sb A4L] in SEPT4c, SEPT4q, SEPT4t. assert (EQx : tk / 8 + A_SB + 4 = tk / 8 + 2147450884) by (unfold A_SB; lia). rewrite EQx in SEPT4c, SEPT4q, SEPT4t. clear EQx.
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
clear SEPT4c SEPT4q SEPT4t Ld.
stash Himg_t2.
try lazymatch goal with |- AJ5 _ _ _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) => replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
reenterA asegs A4L HIx asegs_wx HP.
do 5 step.
destruct OUT2 as [(-> & PBK2 & BK2) | [-> Epbs2]].
-
step.
if_true.
evt_done5.
assert (Hl2 : nth_error (t_levels ts2) (t_depth ts2) = Some l) by (unfold ts2, ts_pbs, ts0; cbn [t_levels t_depth]; exact Hl).
eapply (sesc_join_A HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo mp2 md2 A2 B2 ts2 l cb nb pj sv errv2 T (kP + 1));
[exact STC | exact INV2 | exact PBK2 | exact Hl2 | exact Hst | exact HMODE | exact Hzss |].
intros m' a0' a1' a2' a3' INV3 PBK3. unstash Kbreak.
eapply (Kbreak m' md2 A2 B2 pbs2 errv2); [exact INV3 | exact PBK3 | | exact FS2 | exact FRM2].
apply (BOK_lvl_restate (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) ts2 B2 nB l (tl_ss l) (tl_ss l) Hl2); [| eapply BOK_weaken; [| exact BK2]; lia].
intros CL. unfold lvl_closed in *. cbn [tl_st tl_ss]. apply andb_true_iff in CL as [CL _]. rewrite CL, Hzss. reflexivity.
-
replace (Z_to_bv 64 (2^64 - 1)) with (Z_to_bv 64 (-1)) by (apply bv_eq; vm_compute; reflexivity).
step.
if_false.
step.
step.
asan_rechkA.
step.
evt_done5.
unstash Kerr16. eapply (Kerr16 mp2 md2 A2 B2 errv2); [| exact FS2 | exact FRM2].
unfold ts2 in INV2. rewrite Epbs2 in INV2. exact INV2.
Qed.
End PeSSescLA.
End RC__1.
