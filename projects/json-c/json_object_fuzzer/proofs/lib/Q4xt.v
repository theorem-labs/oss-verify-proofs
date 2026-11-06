(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup Lib.GwApply QWxq_c1 QRjH QHnV QCcH QfLs Q0Ek Qtgi QjDH Qsw7 QJjn QRUw QkMG QG8z Qdyh QIsM Qa8x QLbz QMdR Q7UD Qhd4 Qwm6 QlKV QsKa Qiiq Q4v2 Q1Ey Ql4f Q1Y6 QrQv QEUF QW22 QdGy QYZ0 Q6oO Q63E QVob Qw5U QMgr Q4xz Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QJjn QRUw.Mq0 QRUw QkMG. Import QG8z Qdyh.Mq0 Qdyh.Mq3 Qdyh.Mq4 QIsM.Mq2 Qa8x.Mq2 QLbz QMdR.Mq0.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa QsKa.Mq4 Qiiq.Mq0 QsKa.Mq6 Q4v2.Mq0 QlKV.Mq5 Q1Ey Ql4f.Mq1 Q1Y6.Mq2 QsKa.Mq8 QrQv.Mq2 QEUF QW22.Mq3 QdGy.Mq2 QYZ0.Mq3 QsKa.Mq0 QlKV.Mq7 Q6oO QdGy.Mq6 Q63E.Mq4 QVob.Mq0 Qw5U.Mq2 QMgr Q4xz Q63E.Mq6.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import QlKV.Mq2 QEUF.Mq0.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section PeSNullA.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_outside : forall m m' W, GA m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= hl_img_lo A4H \/ hl_img_hi A4H <= fst iv) W -> GA m'.
Hypothesis GA_pres : forall LB SP m m', heap_pres A4H LB SP m m' -> GA m -> GA m'.
Hypothesis MAPP : memappend_A_stmt2 HIx.
Hypothesis ISTRNCMP : istrncmp_spec_U.
Hypothesis ISTRNCASECMP : istrncasecmp_spec_U.
Hypothesis NEWDBL : jo_new_double_A_stmt HIx.

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

Lemma null_head_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (nB : nat)
(gp t0 t1 t2 a3 a5 a6 a7 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv -> PBOK m ts 0 -> BOK pf pa ts B (S (Z.to_nat 2816 + nB)) ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_null ->
t_co ts < pf_len pf -> SPV (t_x ts) <= t_co ts ->

(forall m' md' A' B' pbs' errv' pj' (x1' gp' t0' t1' t2' a1' a2' a5' a6' a7' s5v s6v t3' t4' t5' t6' : word) F' fc',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' (ts_pbs ts pbs') cb nb pj' sv errv' ->
pj_16 pj' = Z_to_bv 64 (pf_tk pf / 8 + 2147450883) ->
PBOK m' (ts_pbs ts pbs') 1 -> BOK pf pa (ts_pbs ts pbs') B' (S (Z.to_nat 2816 + nB)) ->
s5v = Z_to_bv 64 (Z.min (SPV (t_x ts) + 1) 4) -> s6v = Z_to_bv 64 (Z.min (SPV (t_x ts) + 1) 3) ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(MS (mkR x1' (Z_to_bv 64 (pf_spf pf)) gp' (Z_to_bv 64 A_TP) t0' t1' t2' (Z_to_bv 64 (pa_sp0 pa)) (Z_to_bv 64 (pf_spf pf))
(Z_to_bv 64 (pf_tk pf + 64)) a1' a2' (Z_to_bv 64 (pf_tk pf / 8 + 2147450888)) (Z_to_bv 64 (pf_tk pf + 28)) a5' a6' a7'
(Z_to_bv 64 (shA (pa_F pa))) (Z_to_bv 64 (SPV (t_x ts) + 1)) (Z_to_bv 64 (SPV (t_x ts))) s5v s6v (Z_to_bv 64 (pf_tk pf + 32)) (Z_to_bv 64 (pa_F pa)) (Z_to_bv 64 A_SB)
(Z_to_bv 64 (pf_tk pf / 8 + 2147450881)) (Z_to_bv 64 (pf_sb pf + t_co ts)) t3' t4' t5' t6')
F' (Z_to_bv 64 0x93f30) fc' None m' (seg_rom asegs))) ->

(forall m' md' A' B' errv' x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s5' s7' s10' s11' t4' t6' F' fc',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' ts cb nb pj sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msO asegs pf pa APE_ERRST x1' gp' t0' t1' t2' (Z_to_bv 64 16) a1' a2' a3' a4' a5' a6' a7' s5' s7' s10' s11' t4' t6' F' fc' m')) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa (pe_jtA ST_null) (t_co ts) gp t0 t1 t2
(Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) (Z_to_bv 64 (tl_st l))
(Z_to_bv 64 (q / 8 + 4 * Z.of_nat (t_depth ts) + A_SB)) a3 (Z_to_bv 64 APE_JTAB) a5 a6 a7
(Z_to_bv 64 (Z.of_nat (t_depth ts))) (Z_to_bv 64 q) (Z_to_bv 64 (pa_F pa + 64)) F fc m).
Proof.
intros until fc. intros STC BSL INV PBK BK Hl Hst Hco SPB Kcmp Kerr16. pose proof INV as INV0. pe_openA STC INV.
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
unfold APE_BREAK, APE_REDO, APE_OUT, APE_ERRMEM, APE_ERRST, APE_JTAB in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
unfold SPV in SPB, Kcmp. cbn [t_x ts_stpos] in SPB, Kcmp.
assert (SP0' : 0 <= bv_unsigned stpos mod 2^32) by (apply Z.mod_pos_bound; lia).
set (sp := bv_unsigned stpos mod 2^32) in *.
stash Himg_t. stash Himg_q. stash Kcmp. stash Kerr16. clear PB REST TSK LV OBJ HPR BUD GAP SAVED FSH STR ERR SBin.
reenterA asegs A4L HIx asegs_wx HP. rewrite Hst. unfold ST_null. cbn [pe_jtA].
step.
asan_chkA.
do 4 step.
evt_done5.
eapply (pe_memappend_c HIx GA GA_pres MAPP (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m md A B ts0 cb nb pj sv errv T);
[exact STC | exact BSL | exact INV0 | exact PBK | exact BK | exact Hco | rewrite unsigned_lit by lia; reflexivity |].
intros m2 md2 A2 B2 pbs2 errv2 r w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 F2 fc2 INV2 OUT2 FS2 FRM2.
cbn [pf_spf] in *. unfold A_TP in *.
clear TOK SLOTS FF SHT SHQ SHQ4 SHT1 Ld MU WM MI HP INtk INq Htal Htlo Hthi Hqal Hqlo Hqhi Hqtk Hdtq INV0 PBK BK SEPT1c SEPT1q SEPT1t.
set (ts2 := ts_pbs ts0 pbs2) in *.
pose proof INV2 as [(_ & _ & _ & _ & _ & _ & _ & _ & FR2) _]. stash FR2.
set (pj1 := PEJA (pj_0 pj) (pj_8 pj) (Z_to_bv 64 (tk / 8 + 2147450883)) (pj_obj pj) (pj_288 pj) (pj_304 pj) (pj_gap pj) (pj_fhd pj) (pj_f1 pj) (pj_f2 pj)).
reopen_inv INV2 ts2 ts0 (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 tk mxd depth l Hl bse Hbse m2.
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t2.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 3 HP INtk ltac:(lia)) as SHT3.
replace (tk / 8 + 3 + A_SB) with (tk / 8 + 2147450883) in SHT3 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 3 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT3c & SEPT3q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 3 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT3t & _).
cbn [hl_sb A4L] in SEPT3c, SEPT3q, SEPT3t. assert (EQx : tk / 8 + A_SB + 3 = tk / 8 + 2147450883) by (unfold A_SB; lia). rewrite EQx in SEPT3c, SEPT3q, SEPT3t. clear EQx.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 4 HP INtk ltac:(lia)) as SHT4.
replace (tk / 8 + 4 + A_SB) with (tk / 8 + 2147450884) in SHT4 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 4 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT4c & SEPT4q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 4 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT4t & _).
cbn [hl_sb A4L] in SEPT4c, SEPT4q, SEPT4t. assert (EQx : tk / 8 + A_SB + 4 = tk / 8 + 2147450884) by (unfold A_SB; lia). rewrite EQx in SEPT4c, SEPT4q, SEPT4t. clear EQx.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 8 HP INtk ltac:(lia)) as SHT8.
replace (tk / 8 + 8 + A_SB) with (tk / 8 + 2147450888) in SHT8 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 8 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT8c & SEPT8q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 8 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT8t & _).
cbn [hl_sb A4L] in SEPT8c, SEPT8q, SEPT8t. assert (EQx : tk / 8 + A_SB + 8 = tk / 8 + 2147450888) by (unfold A_SB; lia). rewrite EQx in SEPT8c, SEPT8q, SEPT8t. clear EQx.
pose proof (munch_refl [(spf, spf + 312)] m2) as MU.
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
clear SEPT3q SEPT3t SEPT3c SEPT4q SEPT4t SEPT4c SEPT8q SEPT8t SEPT8c.
stash Himg_t2.
reenterA asegs A4L HIx asegs_wx HP.
destruct OUT2 as [(-> & PBK2 & BK2) | [-> Epbs2]].
2:{ replace (Z_to_bv 64 (2^64 - 1)) with (Z_to_bv 64 (-1)) by (apply bv_eq; vm_compute; reflexivity).
step.
if_false.
step.
step.
asan_rechkM 2.
step.
evt_done5.
unstash Kerr16. eapply (Kerr16 m2 md2 A2 B2 errv2); [| exact FS2 | exact FRM2].
subst pbs2. exact INV2. }
step.
if_true.
step.
step. step.
sh_norm.
repeat match goal with
| |- context [ (?p + ?j) / 8 ] => is_Zlit j; rewrite (div8_add p j) by lia; let k := eval vm_compute in (Z.div j 8) in change (j / 8) with k
end.
step.
step.
step. step.
step.
first [ if_false | if_true ]; rewrite ?sxb_zero, ?zxb_zero.
step.
rewrite (sx32_small_mod stpos) by (fold sp; lia). fold sp.
step.
norm_w32.
step. step.
step.
destruct (Z_lt_dec sp 3) as [L3 | G3].
- if_truex.
step. step.
step.
destruct (Z_lt_dec sp 2) as [L2 | G2].
+ if_truex.

unstash FR2.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m2 mc, WMc : wmono asegs m2 mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, SLc : rw_cells asegs mc spf _ |- _ =>
evt_done5;
assert (FRc : pe_frameA asegs mc (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) cb nb pj1 sv)
by (eapply (pe_frameA_slotw HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) _ LM FRS B2 A2 m2 mc md2 lo [] cb nb pj pj1 sv);
[ exact STC | exact HP | apply Forall_nil | exact FR2 | exact MUc | exact WMc | exact SLc | reflexivity | reflexivity | reflexivity | reflexivity ]);
destruct (PE_INV_A_framew HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m2 mc md2 A2 B2 ts2
cb nb pj sv errv2 [(spf, spf + 312)] cb nb pj1 STC INV2 MUc WMc MIc
ltac:(apply Forall_cons; [right; left; cbn [fst snd pf_spf pa_sp0]; lia | apply Forall_nil]) TOKc FRc) as [INV3 PBT3]
end end.
unstash Kcmp. eapply (Kcmp _ md2 A2 B2 pbs2 errv2 pj1); [exact INV3 | reflexivity | exact (PBT3 _ PBK2) | exact BK2 | f_equal; lia | f_equal; lia | exact FS2 | exact FRM2].
+ if_falsex.
step.

unstash FR2.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m2 mc, WMc : wmono asegs m2 mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, SLc : rw_cells asegs mc spf _ |- _ =>
evt_done5;
assert (FRc : pe_frameA asegs mc (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) cb nb pj1 sv)
by (eapply (pe_frameA_slotw HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) _ LM FRS B2 A2 m2 mc md2 lo [] cb nb pj pj1 sv);
[ exact STC | exact HP | apply Forall_nil | exact FR2 | exact MUc | exact WMc | exact SLc | reflexivity | reflexivity | reflexivity | reflexivity ]);
destruct (PE_INV_A_framew HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m2 mc md2 A2 B2 ts2
cb nb pj sv errv2 [(spf, spf + 312)] cb nb pj1 STC INV2 MUc WMc MIc
ltac:(apply Forall_cons; [right; left; cbn [fst snd pf_spf pa_sp0]; lia | apply Forall_nil]) TOKc FRc) as [INV3 PBT3]
end end.
unstash Kcmp. eapply (Kcmp _ md2 A2 B2 pbs2 errv2 pj1); [exact INV3 | reflexivity | exact (PBT3 _ PBK2) | exact BK2 | f_equal; lia | f_equal; lia | exact FS2 | exact FRM2].
- if_falsex.
step.
step. step.
step.
if_falsex.
step.

unstash FR2.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m2 mc, WMc : wmono asegs m2 mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, SLc : rw_cells asegs mc spf _ |- _ =>
evt_done5;
assert (FRc : pe_frameA asegs mc (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) cb nb pj1 sv)
by (eapply (pe_frameA_slotw HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) _ LM FRS B2 A2 m2 mc md2 lo [] cb nb pj pj1 sv);
[ exact STC | exact HP | apply Forall_nil | exact FR2 | exact MUc | exact WMc | exact SLc | reflexivity | reflexivity | reflexivity | reflexivity ]);
destruct (PE_INV_A_framew HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m2 mc md2 A2 B2 ts2
cb nb pj sv errv2 [(spf, spf + 312)] cb nb pj1 STC INV2 MUc WMc MIc
ltac:(apply Forall_cons; [right; left; cbn [fst snd pf_spf pa_sp0]; lia | apply Forall_nil]) TOKc FRc) as [INV3 PBT3]
end end.
unstash Kcmp. eapply (Kcmp _ md2 A2 B2 pbs2 errv2 pj1); [exact INV3 | reflexivity | exact (PBT3 _ PBK2) | exact BK2 | f_equal; lia | f_equal; lia | exact FS2 | exact FRM2].
Qed.

Lemma lit_cmp_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet)
(x1 gp t0 t1 t2 a1 a2 a5 a6 a7 s5v s6v t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> pf_fl pf = 0 ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
s5v = Z_to_bv 64 (Z.min (SPV (t_x ts) + 1) 4) -> s6v = Z_to_bv 64 (Z.min (SPV (t_x ts) + 1) 3) ->

(forall m' (gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s6' s8' s10' : word),
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md A B ts cb nb pj sv errv -> (forall b, PBOKat m ts b -> PBOKat m' ts b) ->
AJ5 A4L HIx A T md
(MS (mkR (Z_to_bv 64 (pf_tk pf / 8 + 2147450884)) (Z_to_bv 64 (pf_spf pf)) gp' (Z_to_bv 64 A_TP) t0' t1' t2' (Z_to_bv 64 (pa_sp0 pa)) (Z_to_bv 64 (pf_spf pf))
a0' a1' a2' a3' a4' a5' a6' a7'
(Z_to_bv 64 (shA (pa_F pa))) (Z_to_bv 64 (SPV (t_x ts) + 1)) (Z_to_bv 64 (SPV (t_x ts))) s5' s6' (Z_to_bv 64 (pf_tk pf + 32)) s8' (Z_to_bv 64 A_SB)
s10' (Z_to_bv 64 (pf_sb pf + t_co ts)) (Z_to_bv 64 (pf_tk pf + 64)) (Z_to_bv 64 (pa_F pa + 64)) (Z_to_bv 64 (pf_tk pf / 8 + 2147450888)) (Z_to_bv 64 (pf_lenr pf)))
F (Z_to_bv 64 0x94888) fc None m' (seg_rom asegs))) ->

(forall m' (x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s6' s8' s10' t3' t4' t5' t6' : word),
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md A B ts cb nb pj sv errv -> (forall b, PBOKat m ts b -> PBOKat m' ts b) ->
AJ5 A4L HIx A T md
(MS (mkR x1' (Z_to_bv 64 (pf_spf pf)) gp' (Z_to_bv 64 A_TP) t0' t1' t2' (Z_to_bv 64 (pa_sp0 pa)) (Z_to_bv 64 (pf_spf pf))
a0' a1' a2' a3' a4' a5' a6' a7'
(Z_to_bv 64 (shA (pa_F pa))) (Z_to_bv 64 (SPV (t_x ts) + 1)) (Z_to_bv 64 (SPV (t_x ts))) s5' s6' (Z_to_bv 64 (pf_tk pf + 32)) s8' (Z_to_bv 64 A_SB)
s10' (Z_to_bv 64 (pf_sb pf + t_co ts)) t3' t4' t5' t6')
F (Z_to_bv 64 0x9402c) fc None m' (seg_rom asegs))) ->

(forall m' (x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s8' s10' t3' t4' t5' t6' : word),
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md A B ts cb nb pj sv errv ->
AJ5 A4L HIx A T md
(Q1Y6.Mq2.pe_msE pf pa APE_ERRLIT x1' gp' t0' t1' t2' (Z_to_bv 64 5) a1' a2' a3' a4' a5' a6' a7'
(Z_to_bv 64 (pf_tk pf / 8 + 2147450882)) s4' s5' s6' (Z_to_bv 64 (pf_tk pf + 32)) s8' s10' (Z_to_bv 64 (pf_sb pf + t_co ts)) t3' t4' t5' t6' F fc m')) ->
AJ5 A4L HIx A T md
(MS (mkR x1 (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 (pa_sp0 pa)) (Z_to_bv 64 (pf_spf pf))
(Z_to_bv 64 (pf_tk pf + 64)) a1 a2 (Z_to_bv 64 (pf_tk pf / 8 + 2147450888)) (Z_to_bv 64 (pf_tk pf + 28)) a5 a6 a7
(Z_to_bv 64 (shA (pa_F pa))) (Z_to_bv 64 (SPV (t_x ts) + 1)) (Z_to_bv 64 (SPV (t_x ts))) s5v s6v (Z_to_bv 64 (pf_tk pf + 32)) (Z_to_bv 64 (pa_F pa)) (Z_to_bv 64 A_SB)
(Z_to_bv 64 (pf_tk pf / 8 + 2147450881)) (Z_to_bv 64 (pf_sb pf + t_co ts)) t3 t4 t5 t6)
F (Z_to_bv 64 0x93f30) fc None m (seg_rom asegs)).
Proof.
intros until fc. intros STC FL0 INV Es5 Es6 Km1 Km2 Kerrp. pose proof INV as INV0. pe_openA STC INV.
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
pose proof FR as FR0. unfold pe_frameA in FR. destruct FR as (SLOTS & GAP & SAVED & FF & FSH).
unfold pe_slotsA in SLOTS. cbn zeta in SLOTS.
unfold Q1Y6.Mq2.pe_msE, APE_ERRLIT in *.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
destruct PB as (buf & bpos & cap & pre & post & Epbs & Lpre & CORE1). destruct CORE1 as (Hbp & Hcap & Hlen & PBC & BUFC).
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * mxd) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
assert (INpb : In (pb, PB_SZ) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA, tstate_blocks, ts0; cbn [t_pbs]; rewrite Epbs; apply in_or_app; left; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t.
blk_factsA A4L HIx HP pb 16 Hpal Hplo Hphi Himg_p.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 1 HP INtk ltac:(lia)) as SHT1.
replace (tk / 8 + 1 + A_SB) with (tk / 8 + 2147450881) in SHT1 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 1 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT1c & SEPT1q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 1 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT1t & _).
cbn [hl_sb A4L] in SEPT1c, SEPT1q, SEPT1t. assert (EQx : tk / 8 + A_SB + 1 = tk / 8 + 2147450881) by (unfold A_SB; lia). rewrite EQx in SEPT1c, SEPT1q, SEPT1t. clear EQx.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 4 HP INtk ltac:(lia)) as SHT4.
replace (tk / 8 + 4 + A_SB) with (tk / 8 + 2147450884) in SHT4 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 4 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT4c & SEPT4q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 4 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT4t & _).
cbn [hl_sb A4L] in SEPT4c, SEPT4q, SEPT4t. assert (EQx : tk / 8 + A_SB + 4 = tk / 8 + 2147450884) by (unfold A_SB; lia). rewrite EQx in SEPT4c, SEPT4q, SEPT4t. clear EQx.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 8 HP INtk ltac:(lia)) as SHT8.
replace (tk / 8 + 8 + A_SB) with (tk / 8 + 2147450888) in SHT8 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 8 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT8c & SEPT8q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 8 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT8t & _).
cbn [hl_sb A4L] in SEPT8c, SEPT8q, SEPT8t. assert (EQx : tk / 8 + A_SB + 8 = tk / 8 + 2147450888) by (unfold A_SB; lia). rewrite EQx in SEPT8c, SEPT8q, SEPT8t. clear EQx.
pose proof (blk_granA HIx _ _ _ _ _ _ _ pb 16 0 HP INpb ltac:(lia) ltac:(lia)) as SHP0.
replace (pb / 8 + 0 + A_SB) with (pb / 8 + 2147450880) in SHP0 by (unfold A_SB; lia).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
unfold SPV in *. cbn [t_x ts_stpos] in *.
assert (SP0' : 0 <= bv_unsigned stpos mod 2^32) by (apply Z.mod_pos_bound; lia).
set (sp := bv_unsigned stpos mod 2^32) in *.
cbn [pf_fl] in FL0. subst s5v s6v.
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
clear SEPT1c SEPT1q SEPT1t SEPT4c SEPT4q SEPT4t SEPT8c SEPT8q SEPT8t.
stash Himg_t. stash Himg_p. clear REST TSK LV OBJ HPR BUD GAP SAVED FSH STR ERR SBin FF.
reenterA asegs A4L HIx asegs_wx HP.
asan_rechkA.
step.
step.
rewrite FL0. replace (Z_to_bv 64 (Z.land (bv_unsigned (zx32 (Z_to_bv 64 0))) 1)) with (Z_to_bv 64 0) by (apply bv_eq; vm_compute; reflexivity).
step.
if_false.
asan_rechkM 1.
step.
asan_chkA.
step.
step. step.
step.
step.
eapply (pe_istrncasecmp_c HIx GA GA_pres ISTRNCASECMP (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m md A B ts0 cb nb pj sv errv _ LIT_NULL_A (Z.min (sp + 1) 4) buf cap nullstrA);
[ exact STC | exact INV0 | exact Epbs | lia | unfold LIT_NULL_A; lia | cbn [length nullstrA]; unfold LIT_NULL_A; lia | apply null_bytesA; exact MI
| intros k' Hk1 Hk2; apply null_srcA; cbn [length nullstrA] in Hk2; lia | rewrite unsigned_lit by lia; reflexivity |].
intros m2 v2 t0_2 t1_2 t2_2 a1_2 a2_2 a3_2 a4_2 a5_2 a6_2 a7_2 t3_2 t4_2 t5_2 t6_2 Hv2 INV2 AG2.
clear TOK SLOTS PBC BUFC SHT1 SHT4 SHP0 MI HP INtk INq INpb Htal Htlo Hthi Hpal Hplo Hphi SHT8.
pose proof INV2 as [CORE2 REST2]. destruct CORE2 as (_ & _ & _ & _ & TOK & PB2 & _ & _ & FR2). pose proof (proj1 REST2) as HP. clear REST2.
unfold ts0 in TOK, PB2. cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_tk pf_mxd pf_fl] in TOK, PB2.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
destruct PB2 as (buf2 & bpos2 & cap2 & pre2 & post2 & Epbs2 & _ & CORE1_2). rewrite Epbs in Epbs2. injection Epbs2 as <- <-.
destruct CORE1_2 as (_ & _ & _ & PBC & BUFC).
unfold pe_frameA in FR2. destruct FR2 as (SLOTS & _ & _ & _ & _). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in SLOTS.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * mxd) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
assert (INpb : In (pb, PB_SZ) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA, tstate_blocks, ts0; cbn [t_pbs]; rewrite Epbs; apply in_or_app; left; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t2.
blk_factsA A4L HIx HP pb 16 Hpal Hplo Hphi Himg_p2.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 1 HP INtk ltac:(lia)) as SHT1.
replace (tk / 8 + 1 + A_SB) with (tk / 8 + 2147450881) in SHT1 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 1 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT1c & SEPT1q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 1 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT1t & _).
cbn [hl_sb A4L] in SEPT1c, SEPT1q, SEPT1t. assert (EQx : tk / 8 + A_SB + 1 = tk / 8 + 2147450881) by (unfold A_SB; lia). rewrite EQx in SEPT1c, SEPT1q, SEPT1t. clear EQx.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 4 HP INtk ltac:(lia)) as SHT4.
replace (tk / 8 + 4 + A_SB) with (tk / 8 + 2147450884) in SHT4 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 4 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT4c & SEPT4q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 4 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT4t & _).
cbn [hl_sb A4L] in SEPT4c, SEPT4q, SEPT4t. assert (EQx : tk / 8 + A_SB + 4 = tk / 8 + 2147450884) by (unfold A_SB; lia). rewrite EQx in SEPT4c, SEPT4q, SEPT4t. clear EQx.
pose proof (blk_granA HIx _ _ _ _ _ _ _ pb 16 0 HP INpb ltac:(lia) ltac:(lia)) as SHP0.
replace (pb / 8 + 0 + A_SB) with (pb / 8 + 2147450880) in SHP0 by (unfold A_SB; lia).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
clear SEPT1c SEPT1q SEPT1t SEPT4c SEPT4q SEPT4t.
stash Himg_t2. stash Himg_p2.
cbn [pf_spf] in *. unfold A_TP in *.
try lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) => replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
do 5 step.
step.
rewrite (eqb64_small_0 v2 Hv2). destruct (Z.eqb_spec v2 0) as [-> | NZ2]; cbv iota.
-
evt_done5. eapply (Km1 m2); [exact INV2 | intros bx PBKx; eapply PBOKat_agree; [exact PBKx | exact AG2 | unfold pe_blocksA, tstate_blocks; intros bz Hbz; apply in_or_app; left; apply in_or_app; left; exact Hbz]].
- asan_rechkM 1.
step.
asan_chkA.
step.
step. step.
step. step.
step.
eapply (pe_istrncmp_c HIx GA GA_pres ISTRNCMP (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m2 md A B ts0 cb nb pj sv errv _ LIT_NULL_A (Z.min (sp + 1) 4) buf cap nullstrA);
[ exact STC | exact INV2 | exact Epbs | lia | unfold LIT_NULL_A; lia | cbn [length nullstrA]; unfold LIT_NULL_A; lia | apply null_bytesA; exact MI
| intros k' Hk1 Hk2; apply null_srcA; cbn [length nullstrA] in Hk2; lia | rewrite unsigned_lit by lia; reflexivity |].
intros m3 v3 t0_3 t1_3 t2_3 a1_3 a2_3 a3_3 a4_3 a5_3 a6_3 a7_3 t3_3 t4_3 t5_3 t6_3 Hv3 INV3 AG3.
clear TOK SLOTS PBC BUFC SHT1 SHT4 SHP0 MI HP INtk INq INpb Htal Htlo Hthi Hpal Hplo Hphi.
pose proof INV3 as [CORE3 REST3]. destruct CORE3 as (_ & _ & _ & _ & TOK & PB3 & _ & _ & FR3). pose proof (proj1 REST3) as HP. clear REST3.
unfold ts0 in TOK, PB3. cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_tk pf_mxd pf_fl] in TOK, PB3.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
destruct PB3 as (buf3 & bpos3 & cap3 & pre3 & post3 & Epbs3 & _ & CORE1_3). rewrite Epbs in Epbs3. injection Epbs3 as <- <-.
destruct CORE1_3 as (_ & _ & _ & PBC & BUFC).
unfold pe_frameA in FR3. destruct FR3 as (SLOTS & _ & _ & _ & _). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in SLOTS.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * mxd) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
assert (INpb : In (pb, PB_SZ) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA, tstate_blocks, ts0; cbn [t_pbs]; rewrite Epbs; apply in_or_app; left; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t3.
blk_factsA A4L HIx HP pb 16 Hpal Hplo Hphi Himg_p3.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 1 HP INtk ltac:(lia)) as SHT1.
replace (tk / 8 + 1 + A_SB) with (tk / 8 + 2147450881) in SHT1 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 1 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT1c & SEPT1q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 1 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT1t & _).
cbn [hl_sb A4L] in SEPT1c, SEPT1q, SEPT1t. assert (EQx : tk / 8 + A_SB + 1 = tk / 8 + 2147450881) by (unfold A_SB; lia). rewrite EQx in SEPT1c, SEPT1q, SEPT1t. clear EQx.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 4 HP INtk ltac:(lia)) as SHT4.
replace (tk / 8 + 4 + A_SB) with (tk / 8 + 2147450884) in SHT4 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 4 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT4c & SEPT4q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 4 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT4t & _).
cbn [hl_sb A4L] in SEPT4c, SEPT4q, SEPT4t. assert (EQx : tk / 8 + A_SB + 4 = tk / 8 + 2147450884) by (unfold A_SB; lia). rewrite EQx in SEPT4c, SEPT4q, SEPT4t. clear EQx.
pose proof (blk_granA HIx _ _ _ _ _ _ _ pb 16 0 HP INpb ltac:(lia) ltac:(lia)) as SHP0.
replace (pb / 8 + 0 + A_SB) with (pb / 8 + 2147450880) in SHP0 by (unfold A_SB; lia).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
clear SEPT1c SEPT1q SEPT1t SEPT4c SEPT4q SEPT4t.
stash Himg_t3. stash Himg_p3.
cbn [pf_spf] in *. unfold A_TP in *.
try lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) => replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
do 5 step.
step.
rewrite (eqb64_small_0 v3 Hv3). destruct (Z.eqb_spec v3 0) as [-> | NZ3]; cbv iota.
+
evt_done5. eapply (Km1 m3); [exact INV3 | intros bx PBKx; eapply PBOKat_agree; [exact PBKx | exact (agree_on_trans _ _ _ _ _ AG2 AG3) | unfold pe_blocksA, tstate_blocks; intros bz Hbz; apply in_or_app; left; apply in_or_app; left; exact Hbz]].
+ step.
if_false.
step. step.
step. step.
step.
eapply (pe_istrncasecmp_c HIx GA GA_pres ISTRNCASECMP (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m3 md A B ts0 cb nb pj sv errv _ LIT_NAN_A (Z.min (sp + 1) 3) buf cap nanstrA);
[ exact STC | exact INV3 | exact Epbs | lia | unfold LIT_NAN_A; lia | cbn [length nanstrA]; unfold LIT_NAN_A; lia | apply nan_bytesA; exact MI
| intros k' Hk1 Hk2; apply nan_srcA; cbn [length nanstrA] in Hk2; lia | rewrite unsigned_lit by lia; reflexivity |].
intros m4 v4 t0_4 t1_4 t2_4 a1_4 a2_4 a3_4 a4_4 a5_4 a6_4 a7_4 t3_4 t4_4 t5_4 t6_4 Hv4 INV4 AG4.
cbn [pf_spf] in *. unfold A_TP in *.
try lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) => replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
step.
rewrite (eqb64_small_0 v4 Hv4). destruct (Z.eqb_spec v4 0) as [-> | NZ4]; cbv iota.
*
evt_done5. eapply (Km2 m4); [exact INV4 | intros bx PBKx; eapply PBOKat_agree; [exact PBKx | exact (agree_on_trans _ _ _ _ _ (agree_on_trans _ _ _ _ _ AG2 AG3) AG4) | unfold pe_blocksA, tstate_blocks; intros bz Hbz; apply in_or_app; left; apply in_or_app; left; exact Hbz]].
* step. step.
step. step.
step.
clear MI. pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ (proj1 (proj2 INV4))) as MI.
eapply (pe_istrncmp_c HIx GA GA_pres ISTRNCMP (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m4 md A B ts0 cb nb pj sv errv _ LIT_NAN_A (Z.min (sp + 1) 3) buf cap nanstrA);
[ exact STC | exact INV4 | exact Epbs | lia | unfold LIT_NAN_A; lia | cbn [length nanstrA]; unfold LIT_NAN_A; lia | apply nan_bytesA; exact MI
| intros k' Hk1 Hk2; apply nan_srcA; cbn [length nanstrA] in Hk2; lia | rewrite unsigned_lit by lia; reflexivity |].
intros m5 v5 t0_5 t1_5 t2_5 a1_5 a2_5 a3_5 a4_5 a5_5 a6_5 a7_5 t3_5 t4_5 t5_5 t6_5 Hv5 INV5 AG5.
cbn [pf_spf] in *. unfold A_TP in *.
try lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) => replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
step.
rewrite (eqb64_small_0 v5 Hv5). destruct (Z.eqb_spec v5 0) as [-> | NZ5]; cbv iota.
--
evt_done5. eapply (Km2 m5); [exact INV5 | intros bx PBKx; eapply PBOKat_agree; [exact PBKx | exact (agree_on_trans _ _ _ _ _ (agree_on_trans _ _ _ _ _ (agree_on_trans _ _ _ _ _ AG2 AG3) AG4) AG5) | unfold pe_blocksA, tstate_blocks; intros bz Hbz; apply in_or_app; left; apply in_or_app; left; exact Hbz]].
-- step.
clear TOK SLOTS PBC BUFC SHT1 SHT4 SHP0 MI HP INtk INq INpb Htal Htlo Hthi Hpal Hplo Hphi.
pose proof INV5 as [CORE5 REST5]. destruct CORE5 as (_ & _ & _ & _ & TOK & PB5 & _ & _ & FR5). pose proof (proj1 REST5) as HP. clear REST5.
unfold ts0 in TOK, PB5. cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_tk pf_mxd pf_fl] in TOK, PB5.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
destruct PB5 as (buf5 & bpos5 & cap5 & pre5 & post5 & Epbs5 & _ & CORE1_5). rewrite Epbs in Epbs5. injection Epbs5 as <- <-.
destruct CORE1_5 as (_ & _ & _ & PBC & BUFC).
unfold pe_frameA in FR5. destruct FR5 as (SLOTS & _ & _ & _ & _). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in SLOTS.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * mxd) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
assert (INpb : In (pb, PB_SZ) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA, tstate_blocks, ts0; cbn [t_pbs]; rewrite Epbs; apply in_or_app; left; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t5.
blk_factsA A4L HIx HP pb 16 Hpal Hplo Hphi Himg_p5.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 1 HP INtk ltac:(lia)) as SHT1.
replace (tk / 8 + 1 + A_SB) with (tk / 8 + 2147450881) in SHT1 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 1 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT1c & SEPT1q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 1 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT1t & _).
cbn [hl_sb A4L] in SEPT1c, SEPT1q, SEPT1t. assert (EQx : tk / 8 + A_SB + 1 = tk / 8 + 2147450881) by (unfold A_SB; lia). rewrite EQx in SEPT1c, SEPT1q, SEPT1t. clear EQx.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 4 HP INtk ltac:(lia)) as SHT4.
replace (tk / 8 + 4 + A_SB) with (tk / 8 + 2147450884) in SHT4 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 4 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT4c & SEPT4q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 4 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT4t & _).
cbn [hl_sb A4L] in SEPT4c, SEPT4q, SEPT4t. assert (EQx : tk / 8 + A_SB + 4 = tk / 8 + 2147450884) by (unfold A_SB; lia). rewrite EQx in SEPT4c, SEPT4q, SEPT4t. clear EQx.
pose proof (blk_granA HIx _ _ _ _ _ _ _ pb 16 0 HP INpb ltac:(lia) ltac:(lia)) as SHP0.
replace (pb / 8 + 0 + A_SB) with (pb / 8 + 2147450880) in SHP0 by (unfold A_SB; lia).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
clear SEPT1c SEPT1q SEPT1t SEPT4c SEPT4q SEPT4t.
stash Himg_t5. stash Himg_p5.
cbn [pf_spf] in *. unfold A_TP in *.
try lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) => replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
step.
asan_rechkM 1.
step. step.
evt_done5. eapply (Kerrp m5); exact INV5.
Qed.

Lemma lit_part_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet)
(gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4v s5v s6v s8v s10v : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
pj_16 pj = Z_to_bv 64 (pf_tk pf / 8 + 2147450883) ->
(forall m' a0',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md A B (ts_set_x ts (t_co ts) (TS (ts_isd (t_x ts)) (Z_to_bv 64 (SPV (t_x ts) + 1)) (ts_choff (t_x ts)) (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))) cb nb pj sv errv ->
(forall b, PBOKat m ts b -> PBOKat m' (ts_set_x ts (t_co ts) (TS (ts_isd (t_x ts)) (Z_to_bv 64 (SPV (t_x ts) + 1)) (ts_choff (t_x ts)) (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))) b) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa APE_BREAK (t_co ts) gp t0 t1 t2 a0' a1 a2 a3 a4 a5 a6 a7 s5v (Z_to_bv 64 (pf_tk pf + 56)) (Z_to_bv 64 (pa_F pa + 64)) F fc m')) ->
AJ5 A4L HIx A T md
(MS (mkR (Z_to_bv 64 (pf_tk pf / 8 + 2147450884)) (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 (pa_sp0 pa)) (Z_to_bv 64 (pf_spf pf))
a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (shA (pa_F pa))) (Z_to_bv 64 (SPV (t_x ts) + 1)) s4v s5v s6v (Z_to_bv 64 (pf_tk pf + 32)) s8v (Z_to_bv 64 A_SB)
s10v (Z_to_bv 64 (pf_sb pf + t_co ts)) (Z_to_bv 64 (pf_tk pf + 64)) (Z_to_bv 64 (pa_F pa + 64)) (Z_to_bv 64 (pf_tk pf / 8 + 2147450888)) (Z_to_bv 64 (pf_lenr pf)))
F (Z_to_bv 64 0x967b8) fc None m (seg_rom asegs)).
Proof.
intros until fc. intros STC INV P16 Kbreak. pose proof INV as INV0. pe_openA STC INV.
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
pose proof FR as FR0. unfold pe_frameA in FR. destruct FR as (SLOTS & GAP & SAVED & FF & FSH).
unfold pe_slotsA in SLOTS. cbn zeta in SLOTS. rewrite P16 in SLOTS.
unfold pe_msA in *.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * mxd) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 3 HP INtk ltac:(lia)) as SHT3.
replace (tk / 8 + 3 + A_SB) with (tk / 8 + 2147450883) in SHT3 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 3 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT3c & SEPT3q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 3 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT3t & _).
cbn [hl_sb A4L] in SEPT3c, SEPT3q, SEPT3t. assert (EQx : tk / 8 + A_SB + 3 = tk / 8 + 2147450883) by (unfold A_SB; lia). rewrite EQx in SEPT3c, SEPT3q, SEPT3t. clear EQx.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(tk, tk + 72)] m) as MU.
unfold SPV in *. cbn [t_x ts_stpos] in *.
set (sp := bv_unsigned stpos mod 2^32) in *.
unfold APE_BREAK in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
assert (cs_T3_T : csep (tk / 8 + 2147450883) 1 tk (Z.of_nat 72)) by (unfold csep; clear - SEPT3t; lia).
clear SEPT3c SEPT3q SEPT3t.
stash Himg_t. clear REST TSK LV OBJ HPR BUD GAP SAVED FSH STR ERR SBin FF PB.
reenterA asegs A4L HIx asegs_wx HP.
step.
asan_rechkM 1.
step.
stepz.
do 4 step.
step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _ |- _ =>
evt_done5;
destruct (PE_INV_A_tokw1 HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m mc md A B ts0
cb nb pj sv errv co (TS isd (Z_to_bv 64 (sp + 1)) (Z_to_bv 64 co) err ucs high quote) STC INV0 MUc WMc MIc TOKc ltac:(cbn [pf_len]; lia) eq_refl) as [INV3 PBT3]
end end.
eapply (Kbreak _ _ INV3 PBT3).
Qed.

Lemma null_m1_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet)
(gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s8 s10 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_null ->

(forall m' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5',
SPV (t_x ts) = 4 ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md A B (ts_lvl ts (TL ST_eatws ST_finish (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) cb nb pj sv errv ->
(forall k, PBOK m ts k -> PBOK m' (ts_lvl ts (TL ST_eatws ST_finish (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) k) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa APE_REDO (t_co ts) gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' (Z_to_bv 64 (pf_tk pf + 56)) (Z_to_bv 64 (pa_F pa + 64)) F fc m')) ->

(forall a0',
SPV (t_x ts) <> 4 ->
AJ5 A4L HIx A T md
(MS (mkR (Z_to_bv 64 (pf_tk pf / 8 + 2147450884)) (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 (pa_sp0 pa)) (Z_to_bv 64 (pf_spf pf))
a0' a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (shA (pa_F pa))) (Z_to_bv 64 (SPV (t_x ts) + 1)) (Z_to_bv 64 (SPV (t_x ts))) s5 s6 (Z_to_bv 64 (pf_tk pf + 32)) s8 (Z_to_bv 64 A_SB)
s10 (Z_to_bv 64 (pf_sb pf + t_co ts)) (Z_to_bv 64 (pf_tk pf + 64)) (Z_to_bv 64 (pa_F pa + 64)) (Z_to_bv 64 (pf_tk pf / 8 + 2147450888)) (Z_to_bv 64 (pf_lenr pf)))
F (Z_to_bv 64 0x967b8) fc None m (seg_rom asegs))) ->
AJ5 A4L HIx A T md
(MS (mkR (Z_to_bv 64 (pf_tk pf / 8 + 2147450884)) (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 (pa_sp0 pa)) (Z_to_bv 64 (pf_spf pf))
a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (shA (pa_F pa))) (Z_to_bv 64 (SPV (t_x ts) + 1)) (Z_to_bv 64 (SPV (t_x ts))) s5 s6 (Z_to_bv 64 (pf_tk pf + 32)) s8 (Z_to_bv 64 A_SB)
s10 (Z_to_bv 64 (pf_sb pf + t_co ts)) (Z_to_bv 64 (pf_tk pf + 64)) (Z_to_bv 64 (pa_F pa + 64)) (Z_to_bv 64 (pf_tk pf / 8 + 2147450888)) (Z_to_bv 64 (pf_lenr pf)))
F (Z_to_bv 64 0x94888) fc None m (seg_rom asegs)).
Proof.
intros until fc. intros STC INV Hl Hst Kredo Kpart. pose proof INV as INV0. pe_openA STC INV.
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
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 7 HP INtk ltac:(lia)) as SHT7.
replace (tk / 8 + 7 + A_SB) with (tk / 8 + 2147450887) in SHT7 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 7 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT7c & SEPT7q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 7 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT7t & _).
cbn [hl_sb A4L] in SEPT7c, SEPT7q, SEPT7t. assert (EQx : tk / 8 + A_SB + 7 = tk / 8 + 2147450887) by (unfold A_SB; lia). rewrite EQx in SEPT7c, SEPT7q, SEPT7t. clear EQx.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 2 HP INtk ltac:(lia)) as SHT2.
replace (tk / 8 + 2 + A_SB) with (tk / 8 + 2147450882) in SHT2 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 2 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT2c & SEPT2q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 2 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT2t & _).
cbn [hl_sb A4L] in SEPT2c, SEPT2q, SEPT2t. assert (EQx : tk / 8 + A_SB + 2 = tk / 8 + 2147450882) by (unfold A_SB; lia). rewrite EQx in SEPT2c, SEPT2q, SEPT2t. clear EQx.
shq_facts HP INq INtk q mxd tk (Z.of_nat depth) 0 SHQ0 SEPQ0c SEPQ0q SEPQ0t.
replace (q / 8 + 4 * (Z.of_nat depth) + 0 + A_SB) with (bse / 8 + 2147450880) in SHQ0 by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia).
assert (EQx : q / 8 + A_SB + (4 * (Z.of_nat depth) + 0) = bse / 8 + 2147450880) by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia). rewrite EQx in SEPQ0c, SEPQ0q, SEPQ0t. clear EQx.
shq_facts HP INq INtk q mxd tk (Z.of_nat depth) 2 SHQ2 SEPQ2c SEPQ2q SEPQ2t.
replace (q / 8 + 4 * (Z.of_nat depth) + 2 + A_SB) with (bse / 8 + 2147450882) in SHQ2 by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia).
assert (EQx : q / 8 + A_SB + (4 * (Z.of_nat depth) + 2) = bse / 8 + 2147450882) by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia). rewrite EQx in SEPQ2c, SEPQ2q, SEPQ2t. clear EQx.
unfold APE_BREAK, APE_REDO, APE_OUT, APE_ERRMEM, APE_ERRST, APE_JTAB in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
assert (cs_tk_L : csep tk 72 bse (Z.of_nat 32)) by (unfold csep; clear - Hdtq HbseR; lia).
assert (cs_L_tk : csep bse 32 tk (Z.of_nat 72)) by (unfold csep; clear - Hdtq HbseR; lia).
assert (cs_Q0_L : csep (bse / 8 + 2147450880) 1 bse (Z.of_nat 32)) by (unfold csep; clear - SEPQ0q HbseR; lia).
assert (cs_Q2_L : csep (bse / 8 + 2147450882) 1 bse (Z.of_nat 32)) by (unfold csep; clear - SEPQ2q HbseR; lia).
clear Hdtq SEPT7c SEPT7q SEPT7t SEPT2c SEPT2q SEPT2t SEPQ0c SEPQ0q SEPQ0t SEPQ2c SEPQ2q SEPQ2t.
unfold SPV in *. cbn [t_x ts_stpos] in *.
assert (SPR : 0 <= bv_unsigned stpos mod 2^32 < 2^32) by (apply Z.mod_pos_bound; lia).
set (sp := bv_unsigned stpos mod 2^32) in *.
destruct (null_mode _ _ _ SS26 ltac:(rewrite <- Hst; exact Hmode)) as (Ec0 & Ehn0). subst c0 hn0.
assert (Ecs : tl_cs l = None) by (destruct (tl_cs l); [exfalso; exact CLS0 | reflexivity]).
pose proof (LV depth l Hl) as (_ & _ & JO & _). rewrite Ecs in JO. cbn [jopt] in JO. destruct JO as [Ecur Ecbs].
stash Himg_t. stash Himg_q. stash Kredo. stash Kpart. clear PB REST TSK LV OBJ HPR BUD GAP SAVED FSH STR ERR SBin FF.
reenterA asegs A4L HIx asegs_wx HP.
step.
step.
destruct (Z.eq_dec sp 4) as [E4 | N4].
2:{ if_falsex.
step.
evt_done5. unstash Kpart. eapply (Kpart _ N4). }
if_truex.
step.
asan_rechkM 1.
step.
asan_rechkM 2.
step.
norm_sx32.
step.
rewrite (unsigned_lit (Z.of_nat depth)) by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32.
step.
replace (q + Z.of_nat depth * 32) with bse by lia.
step.
asan_chkM 2.
stepz.
step.
asan_chkA.
step.
stepz.
asan_chkA.
stepz.
step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, Lc : rw_cells asegs mc bse _ |- _ =>
evt_done5; rewrite Hbse in MUc, Lc;
destruct (PE_INV_A_lvl_write HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m mc md A B ts0 cb nb pj sv errv l ST_eatws ST_finish CNone false CAny STC INV0 Hl MUc WMc MIc TOKc
ltac:(unfold srec_cells; cbn [tl_st tl_ss tl_cur tl_name]; rewrite Ecur; exact Lc) Hmode ltac:(reflexivity) ltac:(unfold ST_eatws; lia) ltac:(unfold ST_finish; lia)
(or_intror eq_refl) ltac:(rewrite Hst; reflexivity)) as [INV3 PBK3]
end end.
unstash Kredo. eapply (Kredo _ _ _ _ _ _ _ _ _ _ _ _ _ _ E4 INV3 PBK3).
Qed.

Lemma null_m2_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP v2 ra2 : Z) (nB : nat)
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s8 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv -> PBOKat m ts kP -> BOK pf pa ts B (S (Z.to_nat 2816 + nB)) ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_null ->
pe_s0 sv = Z_to_bv 64 v2 -> pe_ra sv = Z_to_bv 64 ra2 ->
(v2 < alloc_ceiling \/ v2 mod 8 <> 0 \/ v2 <= pa_sp0 pa \/ hiA_top A4L HIx - 16 <= v2) /\ 0 <= v2 < 2^64 ->
uw_ok A4L (hl_malloc A4H) (Z_to_bv 64 0x9d9cc) (UWfp ra2 v2) ->

(forall m' md' A' B' errv' r BS gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' F' fc',
SPV (t_x ts) = 3 -> (length BS <= 3)%nat -> jfresh (Sdouble false) BS 9 ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' (ts_lvl ts (TL ST_eatws ST_finish r (Some (Sdouble false)) BS 0 [])) cb nb pj sv errv' ->
PBOKat m' (ts_lvl ts (TL ST_eatws ST_finish r (Some (Sdouble false)) BS 0 [])) kP ->
BOK pf pa (ts_lvl ts (TL ST_eatws ST_finish r (Some (Sdouble false)) BS 0 [])) B' nB ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msA asegs pf pa APE_REDO (t_co ts) gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' (Z_to_bv 64 (pf_tk pf + 56)) (Z_to_bv 64 (pa_F pa + 64)) F' fc' m')) ->

(forall m' md' A' B' errv' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' s11' t4' t6' F' fc',
PE_INVW_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' ts [] cb nb pj sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msO asegs pf pa APE_ERRMEM x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' (Z_to_bv 64 (pf_tk pf + 56)) s11' t4' t6' F' fc' m')) ->

(forall a0',
SPV (t_x ts) <> 3 ->
AJ5 A4L HIx A T md
(MS (mkR (Z_to_bv 64 (pf_tk pf / 8 + 2147450884)) (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 (pa_sp0 pa)) (Z_to_bv 64 (pf_spf pf))
a0' a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (shA (pa_F pa))) (Z_to_bv 64 (SPV (t_x ts) + 1)) (Z_to_bv 64 (SPV (t_x ts))) s5 s6 (Z_to_bv 64 (pf_tk pf + 32)) s8 (Z_to_bv 64 A_SB)
s10 (Z_to_bv 64 (pf_sb pf + t_co ts)) (Z_to_bv 64 (pf_tk pf + 64)) (Z_to_bv 64 (pa_F pa + 64)) (Z_to_bv 64 (pf_tk pf / 8 + 2147450888)) (Z_to_bv 64 (pf_lenr pf)))
F (Z_to_bv 64 0x967b8) fc None m (seg_rom asegs))) ->
AJ5 A4L HIx A T md
(MS (mkR x1 (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 (pa_sp0 pa)) (Z_to_bv 64 (pf_spf pf))
a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (shA (pa_F pa))) (Z_to_bv 64 (SPV (t_x ts) + 1)) (Z_to_bv 64 (SPV (t_x ts))) s5 s6 (Z_to_bv 64 (pf_tk pf + 32)) s8 (Z_to_bv 64 A_SB)
s10 (Z_to_bv 64 (pf_sb pf + t_co ts)) t3 t4 t5 t6)
F (Z_to_bv 64 0x9402c) fc None m (seg_rom asegs)).
Proof.
intros until fc. intros STC BSL INV PBK BK Hl Hst S0V RAV HV UWK Kredo Kerr16 Kpart. pose proof INV as INV0. pe_openA STC INV.
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
unfold APE_BREAK, APE_REDO, APE_OUT, APE_ERRMEM, APE_ERRST, APE_JTAB in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
unfold SPV in *. cbn [t_x ts_stpos] in *.
assert (SPR : 0 <= bv_unsigned stpos mod 2^32 < 2^32) by (apply Z.mod_pos_bound; lia).
set (sp := bv_unsigned stpos mod 2^32) in *.
destruct (null_mode _ _ _ SS26 ltac:(rewrite <- Hst; exact Hmode)) as (Ec0 & Ehn0). subst c0 hn0.
cbn [name_ok] in NM0. destruct NM0 as [Hn0 Hnbs0].
assert (Ecs : tl_cs l = None) by (destruct (tl_cs l); [exfalso; exact CLS0 | reflexivity]).
pose proof (LV depth l Hl) as (_ & _ & JO & _). rewrite Ecs in JO. cbn [jopt] in JO. destruct JO as [Ecur Ecbs].
assert (Eobjbs : objbs = []).
{ unfold cur_st in OBJ. cbn [t_levels t_depth t_objbs ts0] in OBJ. rewrite Hl, Hst in OBJ. exact OBJ. }
pose proof (PE_WIN_open HIx GA (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m md A B ts0 cb nb pj sv errv l INV0 Hl Hn0 Hnbs0 Eobjbs) as WIN0.
rewrite Ecur, Ecs, Ecbs in WIN0.
set (lw0 := TL (tl_st l) (tl_ss l) 0 None [] 0 []) in *. set (tw0 := ts_lvl ts0 lw0) in *.
assert (El : l = lw0) by (unfold lw0; destruct l as [st_ ss_ cur_ cs_ cbs_ name_ nbs_]; cbn [tl_st tl_ss tl_cur tl_cs tl_cbs tl_name tl_nbs] in *; congruence).
assert (Etw0 : tw0 = ts0) by (unfold tw0; rewrite <- El; apply (ts_lvl_same ts0 l Hl)).
assert (PBK0 : PBOKat m tw0 kP) by (exact (PBOKat_same m ts0 tw0 _ eq_refl eq_refl PBK)).
assert (Hlen0 : length (t_levels tw0) = Z.to_nat mxd) by (unfold tw0, ts_lvl, ts0; cbn [t_levels t_depth]; rewrite lupd_length; exact LEN32).
pose proof (BOK_afford (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) ts0 B nB new_scalar_costA BSL BK ltac:(pose proof (K_ev_pos (PEF tk oldl newl len lenr sb spf pmd mxd fl)); unfold new_scalar_costA; lia)) as COST.
pose proof (nandbl_roA m MI) as NANRO.
stash Himg_t. stash Himg_q. stash Kredo. stash Kerr16. stash Kpart. stash WIN0. stash INV0.
clear PB REST LV OBJ HPR BUD GAP SAVED FSH FF STR ERR SBin SHT SHQ4 SHQ Ld Hdtq.
reenterA asegs A4L HIx asegs_wx HP.
step.
do 5 step.
step.
destruct (Z.eq_dec sp 3) as [E3 | N3].
2:{ if_falsex.
step.
evt_done5. unstash Kpart. eapply (Kpart _ N3). }
if_truex.
step.
step.
step.

unstash WIN0.
evt_done5.
eapply (pe_new_double_w HIx GA GA_pres NEWDBL (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m md A B tw0 cb nb pj sv errv T kP v2 ra2);
[ exact STC | exact WIN0 | exact PBK0 | exact COST | exact S0V | exact RAV | exact HV | exact UWK
| unfold dbl_special; rewrite reg_get_set_same_u by (vm_compute; reflexivity); apply Z.leb_le; vm_compute; reflexivity
| rewrite unsigned_lit by lia; reflexivity |].
intros mn2 md2 A2 B2 errv2 r w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 F2 fc2 OUT2 PBK2 HB2 HD2 FS2 FRM2.
assert (FS2' : fsaved F F2) by (eapply fsaved_trans; [apply fsaved_set10 | exact FS2]).
cbn [pf_spf pa_sp0 pa_F] in *. unfold A_TP in *.
clear TOK SLOTS MU WM MI HP INtk INq Htal Htlo Hthi Hqal Hqlo Hqhi Hqtk WIN0 PBK0 FR0 NANRO FS2.
assert (Hlw0 : nth_error (t_levels tw0) depth = Some lw0) by (unfold tw0, ts_lvl, ts0; cbn [t_levels t_depth]; apply nth_error_lupd_eq; apply nth_error_Some; rewrite Hl; discriminate).
assert (Eb0 : lvl_blocks l = []) by (unfold lvl_blocks; rewrite Ecbs, Hnbs0; reflexivity).
destruct OUT2 as [(-> & WIN2) | (Hr & BS & LEN3 & JF & Rr & WIN2)].
-
pose proof WIN2 as (CORE2 & BASE2 & _). destruct CORE2 as (_ & _ & _ & _ & TOK & _ & _ & TSK2 & FR2). pose proof (proj1 BASE2) as HP. clear BASE2.
unfold tw0, ts_lvl, ts0 in TOK. cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_tk pf_mxd pf_fl] in TOK.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
pose proof FR2 as (SLOTS & _). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in SLOTS.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 (tsF tw0 []))) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * mxd) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 (tsF tw0 []))) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t2.
blk_factsA A4L HIx HP q (32 * mxd) Hqal Hqlo Hqhi Himg_q2.
pose proof (q_ne_tkA HIx _ _ _ _ _ _ _ _ _ _ HP) as Hqtk. cbn [pf_tk] in Hqtk.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ tk 72 q (32 * mxd) HP (in_or_app _ LM _ (or_introl INtk)) (in_or_app _ LM _ (or_introl INq)) ltac:(congruence)) as Hdtq.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs mn2) as WM.
pose proof (TSK2 depth lw0 Hlw0) as Ld. rewrite <- Hbse in Ld. unfold srec_cells, lw0 in Ld. cbn [tl_st tl_ss tl_cur tl_name] in Ld.
shq_facts HP INq INtk q mxd tk (Z.of_nat depth) 2 SHQ2 SEPQ2c SEPQ2q SEPQ2t.
replace (q / 8 + 4 * (Z.of_nat depth) + 2 + A_SB) with (bse / 8 + 2147450882) in SHQ2 by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia).
assert (EQx : q / 8 + A_SB + (4 * (Z.of_nat depth) + 2) = bse / 8 + 2147450882) by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia). rewrite EQx in SEPQ2c, SEPQ2q, SEPQ2t. clear EQx.
shq_facts HP INq INtk q mxd tk (Z.of_nat depth) 0 SHQ0 SEPQ0c SEPQ0q SEPQ0t.
replace (q / 8 + 4 * (Z.of_nat depth) + 0 + A_SB) with (bse / 8 + 2147450880) in SHQ0 by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia).
assert (EQx : q / 8 + A_SB + (4 * (Z.of_nat depth) + 0) = bse / 8 + 2147450880) by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia). rewrite EQx in SEPQ0c, SEPQ0q, SEPQ0t. clear EQx.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 7 HP INtk ltac:(lia)) as SHT7.
replace (tk / 8 + 7 + A_SB) with (tk / 8 + 2147450887) in SHT7 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 7 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT7c & SEPT7q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 7 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT7t & _).
cbn [hl_sb A4L] in SEPT7c, SEPT7q, SEPT7t. assert (EQx : tk / 8 + A_SB + 7 = tk / 8 + 2147450887) by (unfold A_SB; lia). rewrite EQx in SEPT7c, SEPT7q, SEPT7t. clear EQx.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 2 HP INtk ltac:(lia)) as SHT2.
replace (tk / 8 + 2 + A_SB) with (tk / 8 + 2147450882) in SHT2 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 2 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT2c & SEPT2q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 2 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT2t & _).
cbn [hl_sb A4L] in SEPT2c, SEPT2q, SEPT2t. assert (EQx : tk / 8 + A_SB + 2 = tk / 8 + 2147450882) by (unfold A_SB; lia). rewrite EQx in SEPT2c, SEPT2q, SEPT2t. clear EQx.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 4 HP INtk ltac:(lia)) as SHT4.
replace (tk / 8 + 4 + A_SB) with (tk / 8 + 2147450884) in SHT4 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 4 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT4c & SEPT4q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 4 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT4t & _).
cbn [hl_sb A4L] in SEPT4c, SEPT4q, SEPT4t. assert (EQx : tk / 8 + A_SB + 4 = tk / 8 + 2147450884) by (unfold A_SB; lia). rewrite EQx in SEPT4c, SEPT4q, SEPT4t. clear EQx.
pose proof (munch_refl [(bse, bse + 32)] mn2) as MU.
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
assert (cs_tk_L : csep tk 72 bse (Z.of_nat 32)) by (unfold csep; clear - Hdtq HbseR; lia).
assert (cs_L_tk : csep bse 32 tk (Z.of_nat 72)) by (unfold csep; clear - Hdtq HbseR; lia).
assert (cs_Q0_L : csep (bse / 8 + 2147450880) 1 bse (Z.of_nat 32)) by (unfold csep; clear - SEPQ0q HbseR; lia).
assert (cs_T4_L : csep (tk / 8 + 2147450884) 1 bse (Z.of_nat 32)) by (unfold csep; clear - SEPT4q HbseR; lia).
clear Hdtq SEPQ2c SEPQ2q SEPQ2t SEPQ0c SEPQ0q SEPQ0t SEPT7c SEPT7q SEPT7t SEPT2c SEPT2q SEPT2t SEPT4c SEPT4q SEPT4t.
stash Himg_t2. stash Himg_q2. stash WIN2. stash TSK2. stash FR2.
reenterA asegs A4L HIx asegs_wx HP.
step.
asan_rechkM 1.
step.
step.
asan_rechkM 2.
step.
norm_sx32.
step.
rewrite (unsigned_lit (Z.of_nat depth)) by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32.
step.
replace (q + Z.of_nat depth * 32) with bse by lia.
step.
asan_chkM 7.
stepz.
step.
if_false.
step.
step.
step.
rewrite ?sxb_zero, ?zxb_zero.
step.
if_true.

unstash WIN2. unstash TSK2. unstash FR2.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ mn2 mc, WMc : wmono asegs mn2 mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, Lc : rw_cells asegs mc bse _ |- _ =>
evt_done5;
assert (INqL : Forall (fun iv => exists a n, In (a, n) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 (tsF tw0 []) ++ LM) /\ a <= fst iv /\ snd iv <= a + n) [(bse, bse + 32)])
by (apply Forall_cons; [exists q, (32 * mxd); cbn [fst snd]; split; [apply in_or_app; left; exact INq | lia] | apply Forall_nil]);
assert (FRc : pe_frameA asegs mc (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) cb nb pj sv)
by (eapply (pe_frameA_blkwriteG HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) _ LM FRS B2 A2 mn2 mc md2 lo [(bse, bse + 32)] cb nb pj sv); [exact STC | exact HP | exact INqL | exact FR2 | exact MUc | exact WMc]);
assert (TSKc : tstack asegs mc q (lupd (t_levels tw0) (t_depth tw0) lw0))
by (pose proof MUc as MUc'; pose proof Lc as Lc'; rewrite Hbse in MUc', Lc'; eapply (tstack_put asegs mn2 mc q (t_levels tw0) depth lw0 []);
[exact TSK2 | rewrite Hlen0; lia | exact MUc' | exact WMc | intros; exact I | exact Lc']);
destruct (PE_WIN_write HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo mn2 mc md2 A2 B2 tw0 0 None [] 1
cb nb pj sv errv2 [(bse, bse + 32)] lw0 cb nb pj STC WIN2 MUc WMc MIc
ltac:(apply Forall_cons; [right; cbn [fst snd pf_mxd]; lia | apply Forall_nil])
TOKc TSKc FRc ltac:(unfold lvl_bare, lw0; cbn [tl_st tl_ss tl_cs tl_cbs tl_name tl_nbs]; repeat split; try reflexivity; lia)) as [WIN3 PBT3]
end end.
set (tw2 := ts_lvl tw0 lw0) in *.
assert (Etw2 : tw2 = ts0) by (unfold tw2; rewrite (ts_lvl_same tw0 lw0 Hlw0); exact Etw0).
pose proof (BOK_weak _ _ _ _ _ (BOK_pay (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) ts0 B B2 nB new_scalar_costA BK ltac:(pose proof (K_ev_pos (PEF tk oldl newl len lenr sb spf pmd mxd fl)); unfold new_scalar_costA; lia) HB2 ltac:(lia))) as [HBw HDw].
pose proof (PE_WIN_close_weak HIx GA (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo _ md2 A2 B2 tw2 cb nb pj sv errv2 1 WIN3
ltac:(exists lw0; split; [rewrite Etw2, <- El; exact Hl | reflexivity])
ltac:(rewrite Etw2; exact HBw) HDw) as INVw.
rewrite Etw2 in INVw.
unstash Kerr16. eapply (Kerr16 _ md2 A2 B2 errv2); [exact INVw | exact FS2' | exact FRM2].
-
pose proof WIN2 as (CORE2 & BASE2 & _). destruct CORE2 as (_ & _ & _ & _ & TOK & _ & _ & TSK2 & FR2). pose proof (proj1 BASE2) as HP. clear BASE2.
unfold tw0, ts_lvl, ts0 in TOK. cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_tk pf_mxd pf_fl] in TOK.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
pose proof FR2 as (SLOTS & _). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in SLOTS.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 (tsF tw0 BS))) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * mxd) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 (tsF tw0 BS))) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t2.
blk_factsA A4L HIx HP q (32 * mxd) Hqal Hqlo Hqhi Himg_q2.
pose proof (q_ne_tkA HIx _ _ _ _ _ _ _ _ _ _ HP) as Hqtk. cbn [pf_tk] in Hqtk.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ tk 72 q (32 * mxd) HP (in_or_app _ LM _ (or_introl INtk)) (in_or_app _ LM _ (or_introl INq)) ltac:(congruence)) as Hdtq.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs mn2) as WM.
pose proof (TSK2 depth lw0 Hlw0) as Ld. rewrite <- Hbse in Ld. unfold srec_cells, lw0 in Ld. cbn [tl_st tl_ss tl_cur tl_name] in Ld.
shq_facts HP INq INtk q mxd tk (Z.of_nat depth) 2 SHQ2 SEPQ2c SEPQ2q SEPQ2t.
replace (q / 8 + 4 * (Z.of_nat depth) + 2 + A_SB) with (bse / 8 + 2147450882) in SHQ2 by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia).
assert (EQx : q / 8 + A_SB + (4 * (Z.of_nat depth) + 2) = bse / 8 + 2147450882) by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia). rewrite EQx in SEPQ2c, SEPQ2q, SEPQ2t. clear EQx.
shq_facts HP INq INtk q mxd tk (Z.of_nat depth) 0 SHQ0 SEPQ0c SEPQ0q SEPQ0t.
replace (q / 8 + 4 * (Z.of_nat depth) + 0 + A_SB) with (bse / 8 + 2147450880) in SHQ0 by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia).
assert (EQx : q / 8 + A_SB + (4 * (Z.of_nat depth) + 0) = bse / 8 + 2147450880) by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia). rewrite EQx in SEPQ0c, SEPQ0q, SEPQ0t. clear EQx.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 7 HP INtk ltac:(lia)) as SHT7.
replace (tk / 8 + 7 + A_SB) with (tk / 8 + 2147450887) in SHT7 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 7 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT7c & SEPT7q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 7 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT7t & _).
cbn [hl_sb A4L] in SEPT7c, SEPT7q, SEPT7t. assert (EQx : tk / 8 + A_SB + 7 = tk / 8 + 2147450887) by (unfold A_SB; lia). rewrite EQx in SEPT7c, SEPT7q, SEPT7t. clear EQx.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 2 HP INtk ltac:(lia)) as SHT2.
replace (tk / 8 + 2 + A_SB) with (tk / 8 + 2147450882) in SHT2 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 2 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT2c & SEPT2q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 2 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT2t & _).
cbn [hl_sb A4L] in SEPT2c, SEPT2q, SEPT2t. assert (EQx : tk / 8 + A_SB + 2 = tk / 8 + 2147450882) by (unfold A_SB; lia). rewrite EQx in SEPT2c, SEPT2q, SEPT2t. clear EQx.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 4 HP INtk ltac:(lia)) as SHT4.
replace (tk / 8 + 4 + A_SB) with (tk / 8 + 2147450884) in SHT4 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 4 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT4c & SEPT4q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 4 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT4t & _).
cbn [hl_sb A4L] in SEPT4c, SEPT4q, SEPT4t. assert (EQx : tk / 8 + A_SB + 4 = tk / 8 + 2147450884) by (unfold A_SB; lia). rewrite EQx in SEPT4c, SEPT4q, SEPT4t. clear EQx.
pose proof (munch_refl [(bse, bse + 32)] mn2) as MU.
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
assert (cs_tk_L : csep tk 72 bse (Z.of_nat 32)) by (unfold csep; clear - Hdtq HbseR; lia).
assert (cs_L_tk : csep bse 32 tk (Z.of_nat 72)) by (unfold csep; clear - Hdtq HbseR; lia).
assert (cs_Q0_L : csep (bse / 8 + 2147450880) 1 bse (Z.of_nat 32)) by (unfold csep; clear - SEPQ0q HbseR; lia).
assert (cs_T4_L : csep (tk / 8 + 2147450884) 1 bse (Z.of_nat 32)) by (unfold csep; clear - SEPT4q HbseR; lia).
clear Hdtq SEPQ2c SEPQ2q SEPQ2t SEPQ0c SEPQ0q SEPQ0t SEPT7c SEPT7q SEPT7t SEPT2c SEPT2q SEPT2t SEPT4c SEPT4q SEPT4t.
stash Himg_t2. stash Himg_q2. stash WIN2. stash TSK2. stash FR2.
reenterA asegs A4L HIx asegs_wx HP.
step.
asan_rechkM 1.
step.
step.
asan_rechkM 2.
step.
norm_sx32.
step.
rewrite (unsigned_lit (Z.of_nat depth)) by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32.
step.
replace (q + Z.of_nat depth * 32) with bse by lia.
step.
asan_chkM 7.
stepz.
step.
if_truex.
step.
asan_chkA.
step.
stepz.
asan_chkA.
stepz.
step.

set (lw2 := TL ST_eatws ST_finish r None [] 0 []).
unstash WIN2. unstash TSK2. unstash FR2.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ mn2 mc, WMc : wmono asegs mn2 mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, Lc : rw_cells asegs mc bse _ |- _ =>
evt_done5;
assert (INqL : Forall (fun iv => exists a n, In (a, n) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 (tsF tw0 BS) ++ LM) /\ a <= fst iv /\ snd iv <= a + n) [(bse, bse + 32)])
by (apply Forall_cons; [exists q, (32 * mxd); cbn [fst snd]; split; [apply in_or_app; left; exact INq | lia] | apply Forall_nil]);
assert (FRc : pe_frameA asegs mc (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) cb nb pj sv)
by (eapply (pe_frameA_blkwriteG HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) _ LM FRS B2 A2 mn2 mc md2 lo [(bse, bse + 32)] cb nb pj sv); [exact STC | exact HP | exact INqL | exact FR2 | exact MUc | exact WMc]);
assert (TSKc : tstack asegs mc q (lupd (t_levels tw0) (t_depth tw0) lw2))
by (pose proof MUc as MUc'; pose proof Lc as Lc'; rewrite Hbse in MUc', Lc'; eapply (tstack_put asegs mn2 mc q (t_levels tw0) depth lw2 []);
[exact TSK2 | rewrite Hlen0; lia | exact MUc' | exact WMc | intros; exact I | exact Lc']);
destruct (PE_WIN_write HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo mn2 mc md2 A2 B2 tw0 r (Some (Sdouble false)) BS 1
cb nb pj sv errv2 [(bse, bse + 32)] lw2 cb nb pj STC WIN2 MUc WMc MIc
ltac:(apply Forall_cons; [right; cbn [fst snd pf_mxd]; lia | apply Forall_nil])
TOKc TSKc FRc ltac:(unfold lvl_bare, lw2, ST_eatws, ST_finish; cbn [tl_st tl_ss tl_cs tl_cbs tl_name tl_nbs]; repeat split; try reflexivity; lia)) as [WIN3 PBT3]
end end.
set (tw2 := ts_lvl tw0 lw2) in *.
assert (Etw2 : forall lx, ts_lvl tw2 lx = ts_lvl ts0 lx) by (intros lx; unfold tw2, tw0; rewrite !ts_lvl_lvl; reflexivity).
assert (Hlw2 : nth_error (t_levels tw2) (t_depth tw2) = Some lw2) by (unfold tw2, ts_lvl; cbn [t_levels t_depth]; apply nth_error_lupd_eq; rewrite Hlen0; cbn [t_depth tw0 ts_lvl ts0]; lia).
assert (BKf : BOK (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) (ts_lvl ts0 (TL ST_eatws ST_finish r (Some (Sdouble false)) BS 0 [])) B2 nB).
{ eapply (BOK_attach (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) ts0 B B2 nB l ST_eatws ST_finish r (Sdouble false) BS new_scalar_costA BK Hl Ecs Eb0);
[ unfold phi_level; cbn [tl_cs]; lia
| unfold phi_level; cbn [tl_cs]; pose proof (K_ev_pos (PEF tk oldl newl len lenr sb spf pmd mxd fl)); unfold K_free, new_scalar_costA; lia
| intros kids Ek; discriminate Ek | intros kids Ek; discriminate Ek | exact HB2 | lia ]. }
pose proof (PE_WIN_close_cur HIx GA (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo _ md2 A2 B2 tw2 r (Sdouble false) BS cb nb pj sv errv2 lw2 CAny WIN3 Hlw2 eq_refl
ltac:(vm_compute; reflexivity) I ltac:(reflexivity)
ltac:(cbn [tl_st tl_ss lw2]; rewrite Etw2; exact (BOK_weak _ _ _ _ _ BKf))) as INVf.
cbn [tl_st tl_ss lw2] in INVf. rewrite Etw2 in INVf.
unstash Kredo. eapply (Kredo _ md2 A2 B2 errv2 r BS); [exact E3 | exact LEN3 | exact JF | exact INVf | | exact BKf | exact FS2' | exact FRM2].
eapply PBOKat_same with (ts := tw2); [reflexivity | reflexivity |]. exact (PBT3 _ PBK2).
Qed.

Lemma seg_null_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (v2 ra2 : Z) (nB : nat)
(gp t0 t1 t2 a3 a5 a6 a7 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa -> pf_fl pf = 0 ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv -> PBOK m ts 0 -> BOK pf pa ts B (S (Z.to_nat 2816 + nB)) ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_null ->
t_co ts < pf_len pf -> SPV (t_x ts) <= t_co ts ->
pe_s0 sv = Z_to_bv 64 v2 -> pe_ra sv = Z_to_bv 64 ra2 ->
(v2 < alloc_ceiling \/ v2 mod 8 <> 0 \/ v2 <= pa_sp0 pa \/ hiA_top A4L HIx - 16 <= v2) /\ 0 <= v2 < 2^64 ->
uw_ok A4L (hl_malloc A4H) (Z_to_bv 64 0x9d9cc) (UWfp ra2 v2) ->

(forall m' md' A' B' pbs' errv' pj' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' F' fc',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' (ts_set_x (ts_pbs ts pbs') (t_co ts) (TS (ts_isd (t_x ts)) (Z_to_bv 64 (SPV (t_x ts) + 1)) (ts_choff (t_x ts)) (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))) cb nb pj' sv errv' ->
PBOK m' (ts_set_x (ts_pbs ts pbs') (t_co ts) (TS (ts_isd (t_x ts)) (Z_to_bv 64 (SPV (t_x ts) + 1)) (ts_choff (t_x ts)) (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))) 1 ->
BOK pf pa (ts_set_x (ts_pbs ts pbs') (t_co ts) (TS (ts_isd (t_x ts)) (Z_to_bv 64 (SPV (t_x ts) + 1)) (ts_choff (t_x ts)) (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))) B' nB ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msA asegs pf pa APE_BREAK (t_co ts) gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' (Z_to_bv 64 (pf_tk pf + 56)) (Z_to_bv 64 (pa_F pa + 64)) F' fc' m')) ->

(forall m' md' A' B' pbs' errv' pj' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' F' fc',
SPV (t_x ts) = 4 ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' (ts_lvl (ts_pbs ts pbs') (TL ST_eatws ST_finish (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) cb nb pj' sv errv' ->
PBOK m' (ts_lvl (ts_pbs ts pbs') (TL ST_eatws ST_finish (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) 1 ->
BOK pf pa (ts_lvl (ts_pbs ts pbs') (TL ST_eatws ST_finish (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) B' nB ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msA asegs pf pa APE_REDO (t_co ts) gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' (Z_to_bv 64 (pf_tk pf + 56)) (Z_to_bv 64 (pa_F pa + 64)) F' fc' m')) ->

(forall m' md' A' B' pbs' errv' pj' r BS gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' F' fc',
SPV (t_x ts) = 3 -> (length BS <= 3)%nat -> jfresh (Sdouble false) BS 9 ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' (ts_lvl (ts_pbs ts pbs') (TL ST_eatws ST_finish r (Some (Sdouble false)) BS 0 [])) cb nb pj' sv errv' ->
PBOK m' (ts_lvl (ts_pbs ts pbs') (TL ST_eatws ST_finish r (Some (Sdouble false)) BS 0 [])) 1 ->
BOK pf pa (ts_lvl (ts_pbs ts pbs') (TL ST_eatws ST_finish r (Some (Sdouble false)) BS 0 [])) B' nB ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msA asegs pf pa APE_REDO (t_co ts) gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' (Z_to_bv 64 (pf_tk pf + 56)) (Z_to_bv 64 (pa_F pa + 64)) F' fc' m')) ->

(forall m' md' A' B' errv' x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s5' s7' s10' s11' t4' t6' F' fc',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' ts cb nb pj sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msO asegs pf pa APE_ERRST x1' gp' t0' t1' t2' (Z_to_bv 64 16) a1' a2' a3' a4' a5' a6' a7' s5' s7' s10' s11' t4' t6' F' fc' m')) ->

(forall m' md' A' B' pbs' errv' pj' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' s11' t4' t6' F' fc',
PE_INVW_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' (ts_pbs ts pbs') [] cb nb pj' sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msO asegs pf pa APE_ERRMEM x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' (Z_to_bv 64 (pf_tk pf + 56)) s11' t4' t6' F' fc' m')) ->

(forall m' md' A' B' pbs' errv' pj' (x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s8' s10' t3' t4' t5' t6' : word) F' fc',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' (ts_pbs ts pbs') cb nb pj' sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(Q1Y6.Mq2.pe_msE pf pa APE_ERRLIT x1' gp' t0' t1' t2' (Z_to_bv 64 5) a1' a2' a3' a4' a5' a6' a7'
(Z_to_bv 64 (pf_tk pf / 8 + 2147450882)) s4' s5' s6' (Z_to_bv 64 (pf_tk pf + 32)) s8' s10' (Z_to_bv 64 (pf_sb pf + t_co ts)) t3' t4' t5' t6' F' fc' m')) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa (pe_jtA ST_null) (t_co ts) gp t0 t1 t2
(Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) (Z_to_bv 64 (tl_st l))
(Z_to_bv 64 (q / 8 + 4 * Z.of_nat (t_depth ts) + A_SB)) a3 (Z_to_bv 64 APE_JTAB) a5 a6 a7
(Z_to_bv 64 (Z.of_nat (t_depth ts))) (Z_to_bv 64 q) (Z_to_bv 64 (pa_F pa + 64)) F fc m).
Proof.
intros until fc. intros STC BSL FL0 INV PBK BK Hl Hst Hco SPB S0V RAV HV UWK Kbreak Kredo1 Kredo2 Kerr16a Kerr16b Kerrp.
pose proof STC as (_ & _ & _ & _ & _ & LEN & _).
pose proof INV as [(_ & _ & CO & _) _].
eapply (null_head_A pf pa q LB0 LM FRS payload me lo m md A B ts l cb nb pj sv errv T nB gp t0 t1 t2 a3 a5 a6 a7 F fc STC BSL INV PBK BK Hl Hst Hco SPB); [| exact Kerr16a].
intros m1 md1 A1 B1 pbs1 errv1 pj1 x1' gp' t0' t1' t2' a1' a2' a5' a6' a7' s5v s6v t3' t4' t5' t6' F1 fc1 INV1 P16 PBK1 BK1 Es5 Es6 FS1 FRM1.
set (ts1 := ts_pbs ts pbs1) in *.
assert (Hl1 : nth_error (t_levels ts1) (t_depth ts1) = Some l) by exact Hl.
eapply (lit_cmp_A pf pa q LB0 LM FRS payload me lo m1 md1 A1 B1 ts1 cb nb pj1 sv errv1 T x1' gp' t0' t1' t2' a1' a2' a5' a6' a7' s5v s6v t3' t4' t5' t6' F1 fc1 STC FL0 INV1 Es5 Es6).
-
intros m2 gp2 t0_2 t1_2 t2_2 a0_2 a1_2 a2_2 a3_2 a4_2 a5_2 a6_2 a7_2 s5_2 s6_2 s8_2 s10_2 INV2 PBT2.
eapply (null_m1_A pf pa q LB0 LM FRS payload me lo m2 md1 A1 B1 ts1 l cb nb pj1 sv errv1 T gp2 t0_2 t1_2 t2_2 a0_2 a1_2 a2_2 a3_2 a4_2 a5_2 a6_2 a7_2 s5_2 s6_2 s8_2 s10_2 F1 fc1 STC INV2 Hl1 Hst).
+ intros m3 gp3 t0_3 t1_3 t2_3 a0_3 a1_3 a2_3 a3_3 a4_3 a5_3 a6_3 a7_3 s5_3 E4 INV3 PBK3.
eapply (Kredo1 m3 md1 A1 B1 pbs1 errv1 pj1); [exact E4 | exact INV3 | exact (PBK3 1 (PBT2 _ PBK1)) | | exact FS1 | exact FRM1].
eapply (BOK_lvl_restate pf pa ts1 B1 nB l ST_eatws ST_finish Hl1); [intros _; apply lvl_closed_fin; reflexivity | exact (BOK_drop _ _ _ _ _ _ BK1)].
+ intros a0_3 N4.
eapply (lit_part_A pf pa q LB0 LM FRS payload me lo m2 md1 A1 B1 ts1 cb nb pj1 sv errv1 T gp2 t0_2 t1_2 t2_2 a0_3 a1_2 a2_2 a3_2 a4_2 a5_2 a6_2 a7_2 _ s5_2 s6_2 s8_2 s10_2 F1 fc1 STC INV2 P16).
intros m3 a0_4 INV3 PBT3.
eapply (Kbreak m3 md1 A1 B1 pbs1 errv1 pj1); [exact INV3 | exact (PBT3 _ (PBT2 _ PBK1)) | | exact FS1 | exact FRM1].
apply BOK_set_x; [apply Z.le_refl | exact (BOK_drop _ _ _ _ _ _ BK1)].
-
intros m2 x1_2 gp2 t0_2 t1_2 t2_2 a0_2 a1_2 a2_2 a3_2 a4_2 a5_2 a6_2 a7_2 s5_2 s6_2 s8_2 s10_2 t3_2 t4_2 t5_2 t6_2 INV2 PBT2.
eapply (null_m2_A pf pa q LB0 LM FRS payload me lo m2 md1 A1 B1 ts1 l cb nb pj1 sv errv1 T (t_co ts1 + 1) v2 ra2 nB x1_2 gp2 t0_2 t1_2 t2_2 a0_2 a1_2 a2_2 a3_2 a4_2 a5_2 a6_2 a7_2 s5_2 s6_2 s8_2 s10_2 t3_2 t4_2 t5_2 t6_2 F1 fc1
STC BSL INV2 (PBT2 _ PBK1) BK1 Hl1 Hst S0V RAV HV UWK).
+ intros m3 md3 A3 B3 errv3 r BS gp3 t0_3 t1_3 t2_3 a0_3 a1_3 a2_3 a3_3 a4_3 a5_3 a6_3 a7_3 s5_3 F3 fc3 E3 LEN3 JF INV3 PBK3 BK3 FS3 FRM3.
eapply (Kredo2 m3 md3 A3 B3 pbs1 errv3 pj1 r BS); [exact E3 | exact LEN3 | exact JF | exact INV3 | exact PBK3 | exact BK3 | eapply fsaved_trans; [exact FS1 | exact FS3] | intros X; exact (FRM3 (FRM1 X))].
+ intros m3 md3 A3 B3 errv3 x1_3 gp3 t0_3 t1_3 t2_3 a0_3 a1_3 a2_3 a3_3 a4_3 a5_3 a6_3 a7_3 s5_3 s7_3 s11_3 t4_3 t6_3 F3 fc3 INVW3 FS3 FRM3.
eapply (Kerr16b m3 md3 A3 B3 pbs1 errv3 pj1); [exact INVW3 | eapply fsaved_trans; [exact FS1 | exact FS3] | intros X; exact (FRM3 (FRM1 X))].
+ intros a0_3 N3.
eapply (lit_part_A pf pa q LB0 LM FRS payload me lo m2 md1 A1 B1 ts1 cb nb pj1 sv errv1 T gp2 t0_2 t1_2 t2_2 a0_3 a1_2 a2_2 a3_2 a4_2 a5_2 a6_2 a7_2 _ s5_2 s6_2 s8_2 s10_2 F1 fc1 STC INV2 P16).
intros m3 a0_4 INV3 PBT3.
eapply (Kbreak m3 md1 A1 B1 pbs1 errv1 pj1); [exact INV3 | exact (PBT3 _ (PBT2 _ PBK1)) | | exact FS1 | exact FRM1].
apply BOK_set_x; [apply Z.le_refl | exact (BOK_drop _ _ _ _ _ _ BK1)].
-
intros m2 x1_2 gp2 t0_2 t1_2 t2_2 a1_2 a2_2 a3_2 a4_2 a5_2 a6_2 a7_2 s4_2 s5_2 s6_2 s8_2 s10_2 t3_2 t4_2 t5_2 t6_2 INV2.
eapply (Kerrp m2 md1 A1 B1 pbs1 errv1 pj1); [exact INV2 | exact FS1 | exact FRM1].
Qed.
End PeSNullA.
End RC__1.
End Mq0.

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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QMdR.Mq0.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqf. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSHS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSHS. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Ql4f.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql4f.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1Y6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1Y6.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mqh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QrQv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QrQv.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEUF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEUF.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QW22.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QW22.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdGy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdGy.Mq9. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYZ0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYZ0.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mq9. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6oO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6oO.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdGy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdGy.Mqe. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q63E.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q63E.Mqe. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QVob.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QVob.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qw5U.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qw5U.Mq7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QMgr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QMgr.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUrr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUrr. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q63E.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q63E.Mqg.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc5u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc5u. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QAzu.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QAzu.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6vt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6vt. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QV7s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QV7s.Mq3.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEUF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEUF.Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section PeSNullB.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_outside : forall m m' W, GA m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= hl_img_lo A4H \/ hl_img_hi A4H <= fst iv) W -> GA m'.
Hypothesis GA_pres : forall LB SP m m', heap_pres A4H LB SP m m' -> GA m -> GA m'.
Hypothesis MAPP : memappend_A_stmt2 HIx.
Hypothesis ISTRNCMP : istrncmp_spec_U.
Hypothesis ISTRNCASECMP : istrncasecmp_spec_U.
Hypothesis NEWDBL : jo_new_double_A_stmt HIx.

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

Lemma null_head_B :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (nB : nat)
(gp t0 a5 a7 s3 s6 s7 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv -> PBOK m ts 0 -> BOK pf pa ts B (S (Z.to_nat 2816 + nB)) ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_null ->
t_co ts < pf_len pf -> SPV (t_x ts) <= t_co ts ->

(forall m' md' A' B' pbs' errv' pj' (x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3v s5v s7' s11' t3' t4' t5' t6' : word) F' fc',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' (ts_pbs ts pbs') cb nb pj' sv errv' ->
pj_8 pj' = Z_to_bv 64 (pf_tk pf / 8 + 2147450883) ->
PBOK m' (ts_pbs ts pbs') 1 -> BOK pf pa (ts_pbs ts pbs') B' (S (Z.to_nat 2816 + nB)) ->
s5v = Z_to_bv 64 (Z.min (SPV (t_x ts) + 1) 4) -> s3v = Z_to_bv 64 (Z.min (SPV (t_x ts) + 1) 3) ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(MS (mkR x1' (Z_to_bv 64 (pf_spf pf)) gp' (Z_to_bv 64 A_TP) t0' t1' t2' (Z_to_bv 64 (pa_sp0 pa)) (Z_to_bv 64 (pf_spf pf))
a0' a1' a2' a3' a4' a5' a6' a7'
(Z_to_bv 64 (shA (pa_F pa))) s3v (Z_to_bv 64 (pf_sb pf + t_co ts)) s5v (Z_to_bv 64 (pf_tk pf / 8 + 2147450881)) s7' (Z_to_bv 64 (SPV (t_x ts) + 1)) (Z_to_bv 64 (SPV (t_x ts))) (Z_to_bv 64 A_SB) s11' t3' t4' t5' t6')
F' (Z_to_bv 64 0x94940) fc' None m' (seg_rom asegs))) ->

(forall m' md' A' B' errv' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s6' t3' t4' t5' t6' F' fc',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' ts cb nb pj sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msO asegs pf pa APE_ERRMEM gp t0' t1' t2' (Z_to_bv 64 (pf_tk pf + 36)) a1' a2' a3' a4' a5' a6' a7' s3 (Z_to_bv 64 (pf_sb pf + t_co ts)) (Z_to_bv 64 q) s6' s7 (Z_to_bv 64 (Z.of_nat (t_depth ts))) s9 s11 t3' t4' t5' t6' F' fc' m')) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa (pe_jtA ST_null) (t_co ts) gp t0 (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) (Z_to_bv 64 (tl_st l)) (Z_to_bv 64 0) (Z_to_bv 64 (q / 8 + 4 * Z.of_nat (t_depth ts) + A_SB)) (Z_to_bv 64 0) a5 (Z_to_bv 64 APE_JTAB) a7 s3 (Z_to_bv 64 q) s6 s7 (Z_to_bv 64 (Z.of_nat (t_depth ts))) s9 s11 t3 t4 t5 t6 F fc m).
Proof.
intros until fc. intros STC BSL INV PBK BK Hl Hst Hco SPB Kcmp Kerr16. pose proof INV as INV0. pe_openA STC INV.
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
unfold APE_BREAK, APE_REDO, APE_OUT, APE_ERRMEM, APE_JTAB in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
unfold SPV in SPB, Kcmp. cbn [t_x ts_stpos] in SPB, Kcmp.
assert (SP0' : 0 <= bv_unsigned stpos mod 2^32) by (apply Z.mod_pos_bound; lia).
set (sp := bv_unsigned stpos mod 2^32) in *.
stash Himg_t. stash Himg_q. stash Kcmp. stash Kerr16. clear PB REST TSK LV OBJ HPR BUD GAP SAVED FSH STR ERR SBin.
reenterA asegs A4L HIx asegs_wx HP. rewrite Hst. unfold ST_null. cbn [pe_jtA].
step.
asan_chkB.
do 4 step.
evt_done5.
eapply (pe_memappend_c HIx GA GA_pres MAPP (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m md A B ts0 cb nb pj sv errv T);
[exact STC | exact BSL | exact INV0 | exact PBK | exact BK | exact Hco | rewrite unsigned_lit by lia; reflexivity |].
intros m2 md2 A2 B2 pbs2 errv2 r w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 F2 fc2 INV2 OUT2 FS2 FRM2.
cbn [pf_spf] in *. unfold A_TP in *.
clear TOK SLOTS FF SHT SHQ SHQ4 SHT1 Ld MU WM MI HP INtk INq Htal Htlo Hthi Hqal Hqlo Hqhi Hqtk Hdtq INV0 PBK BK SEPT1c SEPT1q SEPT1t.
set (ts2 := ts_pbs ts0 pbs2) in *.
pose proof INV2 as [(_ & _ & _ & _ & _ & _ & _ & _ & FR2) _]. stash FR2.
set (pj1 := PEJA (pj_0 pj) (Z_to_bv 64 (tk / 8 + 2147450883)) (pj_16 pj) (pj_obj pj) (pj_288 pj) (pj_304 pj) (pj_gap pj) (pj_fhd pj) (pj_f1 pj) (pj_f2 pj)).
reopen_inv INV2 ts2 ts0 (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 tk mxd depth l Hl bse Hbse m2.
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t2.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 3 HP INtk ltac:(lia)) as SHT3.
replace (tk / 8 + 3 + A_SB) with (tk / 8 + 2147450883) in SHT3 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 3 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT3c & SEPT3q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 3 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT3t & _).
cbn [hl_sb A4L] in SEPT3c, SEPT3q, SEPT3t. assert (EQx : tk / 8 + A_SB + 3 = tk / 8 + 2147450883) by (unfold A_SB; lia). rewrite EQx in SEPT3c, SEPT3q, SEPT3t. clear EQx.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 4 HP INtk ltac:(lia)) as SHT4.
replace (tk / 8 + 4 + A_SB) with (tk / 8 + 2147450884) in SHT4 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 4 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT4c & SEPT4q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 4 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT4t & _).
cbn [hl_sb A4L] in SEPT4c, SEPT4q, SEPT4t. assert (EQx : tk / 8 + A_SB + 4 = tk / 8 + 2147450884) by (unfold A_SB; lia). rewrite EQx in SEPT4c, SEPT4q, SEPT4t. clear EQx.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 8 HP INtk ltac:(lia)) as SHT8.
replace (tk / 8 + 8 + A_SB) with (tk / 8 + 2147450888) in SHT8 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 8 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT8c & SEPT8q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 8 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT8t & _).
cbn [hl_sb A4L] in SEPT8c, SEPT8q, SEPT8t. assert (EQx : tk / 8 + A_SB + 8 = tk / 8 + 2147450888) by (unfold A_SB; lia). rewrite EQx in SEPT8c, SEPT8q, SEPT8t. clear EQx.
pose proof (munch_refl [(spf, spf + 312)] m2) as MU.
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
clear SEPT3q SEPT3t SEPT3c SEPT4q SEPT4t SEPT4c SEPT8q SEPT8t SEPT8c.
stash Himg_t2.
reenterA asegs A4L HIx asegs_wx HP.
destruct OUT2 as [(-> & PBK2 & BK2) | [-> Epbs2]].
2:{ replace (Z_to_bv 64 (2^64 - 1)) with (Z_to_bv 64 (-1)) by (apply bv_eq; vm_compute; reflexivity).
step.
if_false.
step. step.
asan_rechkMB 2.
evt_done5.
unstash Kerr16. eapply (Kerr16 m2 md2 A2 B2 errv2); [| exact FS2 | exact FRM2].
subst pbs2. exact INV2. }
step.
if_true.
do 3 step.
sh_norm.
repeat match goal with
| |- context [ (?p + ?j) / 8 ] => is_Zlit j; rewrite (div8_add p j) by lia; let k := eval vm_compute in (Z.div j 8) in change (j / 8) with k
end.
asan_rechkB.
step.
rewrite (sx32_small_mod stpos) by (fold sp; lia). fold sp.
step.
norm_w32.
step. if_truex.
step. step.
step.
destruct (Z_lt_dec sp 3) as [L3 | G3].
- if_truex.
step. step.
step.
destruct (Z_lt_dec sp 2) as [L2 | G2].
+ if_truex.
stepz.

unstash FR2.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m2 mc, WMc : wmono asegs m2 mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, SLc : rw_cells asegs mc spf _ |- _ =>
evt_done5;
assert (FRc : pe_frameA asegs mc (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) cb nb pj1 sv)
by (eapply (pe_frameA_slotw HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) _ LM FRS B2 A2 m2 mc md2 lo [] cb nb pj pj1 sv);
[ exact STC | exact HP | apply Forall_nil | exact FR2 | exact MUc | exact WMc | exact SLc | reflexivity | reflexivity | reflexivity | reflexivity ]);
destruct (PE_INV_A_framew HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m2 mc md2 A2 B2 ts2
cb nb pj sv errv2 [(spf, spf + 312)] cb nb pj1 STC INV2 MUc WMc MIc
ltac:(apply Forall_cons; [right; left; cbn [fst snd pf_spf pa_sp0]; lia | apply Forall_nil]) TOKc FRc) as [INV3 PBT3]
end end.
unstash Kcmp. eapply (Kcmp _ md2 A2 B2 pbs2 errv2 pj1); [exact INV3 | reflexivity | exact (PBT3 _ PBK2) | exact BK2 | f_equal; lia | f_equal; lia | exact FS2 | exact FRM2].
+ if_falsex.
step.
stepz.

unstash FR2.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m2 mc, WMc : wmono asegs m2 mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, SLc : rw_cells asegs mc spf _ |- _ =>
evt_done5;
assert (FRc : pe_frameA asegs mc (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) cb nb pj1 sv)
by (eapply (pe_frameA_slotw HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) _ LM FRS B2 A2 m2 mc md2 lo [] cb nb pj pj1 sv);
[ exact STC | exact HP | apply Forall_nil | exact FR2 | exact MUc | exact WMc | exact SLc | reflexivity | reflexivity | reflexivity | reflexivity ]);
destruct (PE_INV_A_framew HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m2 mc md2 A2 B2 ts2
cb nb pj sv errv2 [(spf, spf + 312)] cb nb pj1 STC INV2 MUc WMc MIc
ltac:(apply Forall_cons; [right; left; cbn [fst snd pf_spf pa_sp0]; lia | apply Forall_nil]) TOKc FRc) as [INV3 PBT3]
end end.
unstash Kcmp. eapply (Kcmp _ md2 A2 B2 pbs2 errv2 pj1); [exact INV3 | reflexivity | exact (PBT3 _ PBK2) | exact BK2 | f_equal; lia | f_equal; lia | exact FS2 | exact FRM2].
- if_falsex.
step.
step. step.
step.
if_falsex.
step.
stepz.

unstash FR2.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m2 mc, WMc : wmono asegs m2 mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, SLc : rw_cells asegs mc spf _ |- _ =>
evt_done5;
assert (FRc : pe_frameA asegs mc (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) cb nb pj1 sv)
by (eapply (pe_frameA_slotw HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) _ LM FRS B2 A2 m2 mc md2 lo [] cb nb pj pj1 sv);
[ exact STC | exact HP | apply Forall_nil | exact FR2 | exact MUc | exact WMc | exact SLc | reflexivity | reflexivity | reflexivity | reflexivity ]);
destruct (PE_INV_A_framew HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m2 mc md2 A2 B2 ts2
cb nb pj sv errv2 [(spf, spf + 312)] cb nb pj1 STC INV2 MUc WMc MIc
ltac:(apply Forall_cons; [right; left; cbn [fst snd pf_spf pa_sp0]; lia | apply Forall_nil]) TOKc FRc) as [INV3 PBT3]
end end.
unstash Kcmp. eapply (Kcmp _ md2 A2 B2 pbs2 errv2 pj1); [exact INV3 | reflexivity | exact (PBT3 _ PBK2) | exact BK2 | f_equal; lia | f_equal; lia | exact FS2 | exact FRM2].
Qed.

Lemma lit_cmp_B :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet)
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3v s5v s7 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> pf_fl pf = 0 ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
s5v = Z_to_bv 64 (Z.min (SPV (t_x ts) + 1) 4) -> s3v = Z_to_bv 64 (Z.min (SPV (t_x ts) + 1) 3) ->

(forall m' (x1' gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' s5' s6' s7' s11' t3' t4' t5' t6' : word),
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md A B ts cb nb pj sv errv -> (forall b, PBOKat m ts b -> PBOKat m' ts b) ->
AJ5 A4L HIx A T md
(MS (mkR x1' (Z_to_bv 64 (pf_spf pf)) gp' (Z_to_bv 64 A_TP) t0' (Z_to_bv 64 (pf_lenr pf)) (Z_to_bv 64 (pf_tk pf + 32)) (Z_to_bv 64 (pa_sp0 pa)) (Z_to_bv 64 (pf_spf pf))
a0' a1' a2' a3' a4' a5' a6' a7'
(Z_to_bv 64 (shA (pa_F pa))) s3' (Z_to_bv 64 (pf_sb pf + t_co ts)) s5' s6' s7' (Z_to_bv 64 (SPV (t_x ts) + 1)) (Z_to_bv 64 (SPV (t_x ts))) (Z_to_bv 64 A_SB) s11' t3' t4' t5' t6')
F (Z_to_bv 64 0x952c4) fc None m' (seg_rom asegs))) ->

(forall m' (x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' s5' s6' s7' s11' t3' t4' t5' t6' : word),
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md A B ts cb nb pj sv errv -> (forall b, PBOKat m ts b -> PBOKat m' ts b) ->
AJ5 A4L HIx A T md
(MS (mkR x1' (Z_to_bv 64 (pf_spf pf)) gp' (Z_to_bv 64 A_TP) t0' t1' t2' (Z_to_bv 64 (pa_sp0 pa)) (Z_to_bv 64 (pf_spf pf))
a0' a1' a2' a3' a4' a5' a6' a7'
(Z_to_bv 64 (shA (pa_F pa))) s3' (Z_to_bv 64 (pf_sb pf + t_co ts)) s5' s6' s7' (Z_to_bv 64 (SPV (t_x ts) + 1)) (Z_to_bv 64 (SPV (t_x ts))) (Z_to_bv 64 A_SB) s11' t3' t4' t5' t6')
F (Z_to_bv 64 0x94a54) fc None m' (seg_rom asegs))) ->

(forall m' (x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' : word),
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md A B ts cb nb pj sv errv ->
AJ5 A4L HIx A T md
(pe_msX asegs pf pa APE_ERR3 x1' gp' t0' t1' t2' (Z_to_bv 64 5) a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F fc m')) ->
AJ5 A4L HIx A T md
(MS (mkR x1 (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 (pa_sp0 pa)) (Z_to_bv 64 (pf_spf pf))
a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (shA (pa_F pa))) s3v (Z_to_bv 64 (pf_sb pf + t_co ts)) s5v (Z_to_bv 64 (pf_tk pf / 8 + 2147450881)) s7 (Z_to_bv 64 (SPV (t_x ts) + 1)) (Z_to_bv 64 (SPV (t_x ts))) (Z_to_bv 64 A_SB) s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x94940) fc None m (seg_rom asegs)).
Proof.
intros until fc. intros STC FL0 INV Es5 Es3 Km1 Km2 Kerrp. pose proof INV as INV0. pe_openA STC INV.
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
pose proof FR as FR0. unfold pe_frameA in FR. destruct FR as (SLOTS & GAP & SAVED & FF & FSH).
unfold pe_slotsA in SLOTS. cbn zeta in SLOTS.
unfold pe_msX, APE_ERR3 in *.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
destruct PB as (buf & bpos & cap & pre & post & Epbs & Lpre & CORE1). destruct CORE1 as (Hbp & Hcap & Hlen & PBC & BUFC).
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * mxd) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
assert (INpb : In (pb, PB_SZ) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA, tstate_blocks, ts0; cbn [t_pbs]; rewrite Epbs; apply in_or_app; left; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t.
blk_factsA A4L HIx HP pb 16 Hpal Hplo Hphi Himg_p.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 1 HP INtk ltac:(lia)) as SHT1.
replace (tk / 8 + 1 + A_SB) with (tk / 8 + 2147450881) in SHT1 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 1 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT1c & SEPT1q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 1 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT1t & _).
cbn [hl_sb A4L] in SEPT1c, SEPT1q, SEPT1t. assert (EQx : tk / 8 + A_SB + 1 = tk / 8 + 2147450881) by (unfold A_SB; lia). rewrite EQx in SEPT1c, SEPT1q, SEPT1t. clear EQx.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 4 HP INtk ltac:(lia)) as SHT4.
replace (tk / 8 + 4 + A_SB) with (tk / 8 + 2147450884) in SHT4 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 4 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT4c & SEPT4q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 4 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT4t & _).
cbn [hl_sb A4L] in SEPT4c, SEPT4q, SEPT4t. assert (EQx : tk / 8 + A_SB + 4 = tk / 8 + 2147450884) by (unfold A_SB; lia). rewrite EQx in SEPT4c, SEPT4q, SEPT4t. clear EQx.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 8 HP INtk ltac:(lia)) as SHT8.
replace (tk / 8 + 8 + A_SB) with (tk / 8 + 2147450888) in SHT8 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 8 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT8c & SEPT8q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 8 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT8t & _).
cbn [hl_sb A4L] in SEPT8c, SEPT8q, SEPT8t. assert (EQx : tk / 8 + A_SB + 8 = tk / 8 + 2147450888) by (unfold A_SB; lia). rewrite EQx in SEPT8c, SEPT8q, SEPT8t. clear EQx.
pose proof (blk_granA HIx _ _ _ _ _ _ _ pb 16 0 HP INpb ltac:(lia) ltac:(lia)) as SHP0.
replace (pb / 8 + 0 + A_SB) with (pb / 8 + 2147450880) in SHP0 by (unfold A_SB; lia).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
unfold SPV in *. cbn [t_x ts_stpos] in *.
assert (SP0' : 0 <= bv_unsigned stpos mod 2^32) by (apply Z.mod_pos_bound; lia).
set (sp := bv_unsigned stpos mod 2^32) in *.
cbn [pf_fl] in FL0. subst s5v s3v.
assert (Hpb8 : pb mod 8 = 0) by (clear - Hpal; Z.div_mod_to_equations; lia).
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
clear SEPT1c SEPT1q SEPT1t SEPT4c SEPT4q SEPT4t SEPT8c SEPT8q SEPT8t.
stash Himg_t. stash Himg_p. clear REST TSK LV OBJ HPR BUD GAP SAVED FSH STR ERR SBin FF.
reenterA asegs A4L HIx asegs_wx HP.
step.
asan_rechkB.
do 2 step.
step.
rewrite FL0. replace (Z_to_bv 64 (Z.land (bv_unsigned (zx32 (Z_to_bv 64 0))) 1)) with (Z_to_bv 64 0) by (apply bv_eq; vm_compute; reflexivity).
step.
if_false.
asan_rechkMB 1.
step.
step. if_truex.
step. ub_land Hpb8. step. ub_if_lit.
asan_chkB.
step.
step. step.
step.
step.
eapply (pe_istrncasecmp_c HIx GA GA_pres ISTRNCASECMP (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m md A B ts0 cb nb pj sv errv _ LIT_NULL_A (Z.min (sp + 1) 4) buf cap nullstrA);
[ exact STC | exact INV0 | exact Epbs | lia | unfold LIT_NULL_A; lia | cbn [length nullstrA]; unfold LIT_NULL_A; lia | apply null_bytesA; exact MI
| intros k' Hk1 Hk2; apply null_srcA; cbn [length nullstrA] in Hk2; lia | rewrite unsigned_lit by lia; reflexivity |].
intros m2 v2 t0_2 t1_2 t2_2 a1_2 a2_2 a3_2 a4_2 a5_2 a6_2 a7_2 t3_2 t4_2 t5_2 t6_2 Hv2 INV2 AG2.
clear TOK SLOTS PBC BUFC SHT1 SHT4 SHP0 MI HP INtk INq INpb Htal Htlo Hthi Hpal Hplo Hphi SHT8.
pose proof INV2 as [CORE2 REST2]. destruct CORE2 as (_ & _ & _ & _ & TOK & PB2 & _ & _ & FR2). pose proof (proj1 REST2) as HP. clear REST2.
unfold ts0 in TOK, PB2. cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_tk pf_mxd pf_fl] in TOK, PB2.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
destruct PB2 as (buf2 & bpos2 & cap2 & pre2 & post2 & Epbs2 & _ & CORE1_2). rewrite Epbs in Epbs2. injection Epbs2 as <- <-.
destruct CORE1_2 as (_ & _ & _ & PBC & BUFC).
unfold pe_frameA in FR2. destruct FR2 as (SLOTS & _ & _ & _ & _). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in SLOTS.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * mxd) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
assert (INpb : In (pb, PB_SZ) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA, tstate_blocks, ts0; cbn [t_pbs]; rewrite Epbs; apply in_or_app; left; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t2.
blk_factsA A4L HIx HP pb 16 Hpal Hplo Hphi Himg_p2.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 1 HP INtk ltac:(lia)) as SHT1.
replace (tk / 8 + 1 + A_SB) with (tk / 8 + 2147450881) in SHT1 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 1 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT1c & SEPT1q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 1 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT1t & _).
cbn [hl_sb A4L] in SEPT1c, SEPT1q, SEPT1t. assert (EQx : tk / 8 + A_SB + 1 = tk / 8 + 2147450881) by (unfold A_SB; lia). rewrite EQx in SEPT1c, SEPT1q, SEPT1t. clear EQx.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 4 HP INtk ltac:(lia)) as SHT4.
replace (tk / 8 + 4 + A_SB) with (tk / 8 + 2147450884) in SHT4 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 4 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT4c & SEPT4q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 4 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT4t & _).
cbn [hl_sb A4L] in SEPT4c, SEPT4q, SEPT4t. assert (EQx : tk / 8 + A_SB + 4 = tk / 8 + 2147450884) by (unfold A_SB; lia). rewrite EQx in SEPT4c, SEPT4q, SEPT4t. clear EQx.
pose proof (blk_granA HIx _ _ _ _ _ _ _ pb 16 0 HP INpb ltac:(lia) ltac:(lia)) as SHP0.
replace (pb / 8 + 0 + A_SB) with (pb / 8 + 2147450880) in SHP0 by (unfold A_SB; lia).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
clear SEPT1c SEPT1q SEPT1t SEPT4c SEPT4q SEPT4t.
stash Himg_t2. stash Himg_p2.
cbn [pf_spf] in *. unfold A_TP in *.
try lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) => replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
step. step.
step.
rewrite (eqb64_small_0 v2 Hv2). destruct (Z.eqb_spec v2 0) as [-> | NZ2]; cbv iota.
-
evt_done5. eapply (Km1 m2); [exact INV2 | intros bx PBKx; eapply PBOKat_agree; [exact PBKx | exact AG2 | unfold pe_blocksA, tstate_blocks; intros bz Hbz; apply in_or_app; left; apply in_or_app; left; exact Hbz]].
- asan_rechkMB 1.
step.
step. if_truex.
step. ub_land Hpb8. step. ub_if_lit.
asan_chkB.
step.
step. step.
step. step.
step.
eapply (pe_istrncmp_c HIx GA GA_pres ISTRNCMP (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m2 md A B ts0 cb nb pj sv errv _ LIT_NULL_A (Z.min (sp + 1) 4) buf cap nullstrA);
[ exact STC | exact INV2 | exact Epbs | lia | unfold LIT_NULL_A; lia | cbn [length nullstrA]; unfold LIT_NULL_A; lia | apply null_bytesA; exact MI
| intros k' Hk1 Hk2; apply null_srcA; cbn [length nullstrA] in Hk2; lia | rewrite unsigned_lit by lia; reflexivity |].
intros m3 v3 t0_3 t1_3 t2_3 a1_3 a2_3 a3_3 a4_3 a5_3 a6_3 a7_3 t3_3 t4_3 t5_3 t6_3 Hv3 INV3 AG3.
clear TOK SLOTS PBC BUFC SHT1 SHT4 SHP0 MI HP INtk INq INpb Htal Htlo Hthi Hpal Hplo Hphi.
pose proof INV3 as [CORE3 REST3]. destruct CORE3 as (_ & _ & _ & _ & TOK & PB3 & _ & _ & FR3). pose proof (proj1 REST3) as HP. clear REST3.
unfold ts0 in TOK, PB3. cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_tk pf_mxd pf_fl] in TOK, PB3.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
destruct PB3 as (buf3 & bpos3 & cap3 & pre3 & post3 & Epbs3 & _ & CORE1_3). rewrite Epbs in Epbs3. injection Epbs3 as <- <-.
destruct CORE1_3 as (_ & _ & _ & PBC & BUFC).
unfold pe_frameA in FR3. destruct FR3 as (SLOTS & _ & _ & _ & _). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in SLOTS.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * mxd) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
assert (INpb : In (pb, PB_SZ) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA, tstate_blocks, ts0; cbn [t_pbs]; rewrite Epbs; apply in_or_app; left; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t3.
blk_factsA A4L HIx HP pb 16 Hpal Hplo Hphi Himg_p3.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 1 HP INtk ltac:(lia)) as SHT1.
replace (tk / 8 + 1 + A_SB) with (tk / 8 + 2147450881) in SHT1 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 1 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT1c & SEPT1q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 1 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT1t & _).
cbn [hl_sb A4L] in SEPT1c, SEPT1q, SEPT1t. assert (EQx : tk / 8 + A_SB + 1 = tk / 8 + 2147450881) by (unfold A_SB; lia). rewrite EQx in SEPT1c, SEPT1q, SEPT1t. clear EQx.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 4 HP INtk ltac:(lia)) as SHT4.
replace (tk / 8 + 4 + A_SB) with (tk / 8 + 2147450884) in SHT4 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 4 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT4c & SEPT4q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 4 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT4t & _).
cbn [hl_sb A4L] in SEPT4c, SEPT4q, SEPT4t. assert (EQx : tk / 8 + A_SB + 4 = tk / 8 + 2147450884) by (unfold A_SB; lia). rewrite EQx in SEPT4c, SEPT4q, SEPT4t. clear EQx.
pose proof (blk_granA HIx _ _ _ _ _ _ _ pb 16 0 HP INpb ltac:(lia) ltac:(lia)) as SHP0.
replace (pb / 8 + 0 + A_SB) with (pb / 8 + 2147450880) in SHP0 by (unfold A_SB; lia).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
clear SEPT1c SEPT1q SEPT1t SEPT4c SEPT4q SEPT4t.
stash Himg_t3. stash Himg_p3.
cbn [pf_spf] in *. unfold A_TP in *.
try lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) => replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
step. step.
step.
rewrite (eqb64_small_0 v3 Hv3). destruct (Z.eqb_spec v3 0) as [-> | NZ3]; cbv iota.
+
evt_done5. eapply (Km1 m3); [exact INV3 | intros bx PBKx; eapply PBOKat_agree; [exact PBKx | exact (agree_on_trans _ _ _ _ _ AG2 AG3) | unfold pe_blocksA, tstate_blocks; intros bz Hbz; apply in_or_app; left; apply in_or_app; left; exact Hbz]].
+ step.
if_false.
step. step.
step. step.
step.
eapply (pe_istrncasecmp_c HIx GA GA_pres ISTRNCASECMP (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m3 md A B ts0 cb nb pj sv errv _ LIT_NAN_A (Z.min (sp + 1) 3) buf cap nanstrA);
[ exact STC | exact INV3 | exact Epbs | lia | unfold LIT_NAN_A; lia | cbn [length nanstrA]; unfold LIT_NAN_A; lia | apply nan_bytesA; exact MI
| intros k' Hk1 Hk2; apply nan_srcA; cbn [length nanstrA] in Hk2; lia | rewrite unsigned_lit by lia; reflexivity |].
intros m4 v4 t0_4 t1_4 t2_4 a1_4 a2_4 a3_4 a4_4 a5_4 a6_4 a7_4 t3_4 t4_4 t5_4 t6_4 Hv4 INV4 AG4.
cbn [pf_spf] in *. unfold A_TP in *.
try lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) => replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
step.
rewrite (eqb64_small_0 v4 Hv4). destruct (Z.eqb_spec v4 0) as [-> | NZ4]; cbv iota.
*
evt_done5. eapply (Km2 m4); [exact INV4 | intros bx PBKx; eapply PBOKat_agree; [exact PBKx | exact (agree_on_trans _ _ _ _ _ (agree_on_trans _ _ _ _ _ AG2 AG3) AG4) | unfold pe_blocksA, tstate_blocks; intros bz Hbz; apply in_or_app; left; apply in_or_app; left; exact Hbz]].
* step. step.
step. step.
step.
clear MI. pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ (proj1 (proj2 INV4))) as MI.
eapply (pe_istrncmp_c HIx GA GA_pres ISTRNCMP (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m4 md A B ts0 cb nb pj sv errv _ LIT_NAN_A (Z.min (sp + 1) 3) buf cap nanstrA);
[ exact STC | exact INV4 | exact Epbs | lia | unfold LIT_NAN_A; lia | cbn [length nanstrA]; unfold LIT_NAN_A; lia | apply nan_bytesA; exact MI
| intros k' Hk1 Hk2; apply nan_srcA; cbn [length nanstrA] in Hk2; lia | rewrite unsigned_lit by lia; reflexivity |].
intros m5 v5 t0_5 t1_5 t2_5 a1_5 a2_5 a3_5 a4_5 a5_5 a6_5 a7_5 t3_5 t4_5 t5_5 t6_5 Hv5 INV5 AG5.
cbn [pf_spf] in *. unfold A_TP in *.
try lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) => replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
step.
rewrite (eqb64_small_0 v5 Hv5). destruct (Z.eqb_spec v5 0) as [-> | NZ5]; cbv iota.
--
evt_done5. eapply (Km2 m5); [exact INV5 | intros bx PBKx; eapply PBOKat_agree; [exact PBKx | exact (agree_on_trans _ _ _ _ _ (agree_on_trans _ _ _ _ _ (agree_on_trans _ _ _ _ _ AG2 AG3) AG4) AG5) | unfold pe_blocksA, tstate_blocks; intros bz Hbz; apply in_or_app; left; apply in_or_app; left; exact Hbz]].
-- step.
clear TOK SLOTS PBC BUFC SHT1 SHT4 SHP0 MI HP INtk INq INpb Htal Htlo Hthi Hpal Hplo Hphi.
pose proof INV5 as [CORE5 REST5]. destruct CORE5 as (_ & _ & _ & _ & TOK & PB5 & _ & _ & FR5). pose proof (proj1 REST5) as HP. clear REST5.
unfold ts0 in TOK, PB5. cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_tk pf_mxd pf_fl] in TOK, PB5.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
destruct PB5 as (buf5 & bpos5 & cap5 & pre5 & post5 & Epbs5 & _ & CORE1_5). rewrite Epbs in Epbs5. injection Epbs5 as <- <-.
destruct CORE1_5 as (_ & _ & _ & PBC & BUFC).
unfold pe_frameA in FR5. destruct FR5 as (SLOTS & _ & _ & _ & _). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in SLOTS.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * mxd) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
assert (INpb : In (pb, PB_SZ) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA, tstate_blocks, ts0; cbn [t_pbs]; rewrite Epbs; apply in_or_app; left; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t5.
blk_factsA A4L HIx HP pb 16 Hpal Hplo Hphi Himg_p5.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 1 HP INtk ltac:(lia)) as SHT1.
replace (tk / 8 + 1 + A_SB) with (tk / 8 + 2147450881) in SHT1 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 1 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT1c & SEPT1q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 1 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT1t & _).
cbn [hl_sb A4L] in SEPT1c, SEPT1q, SEPT1t. assert (EQx : tk / 8 + A_SB + 1 = tk / 8 + 2147450881) by (unfold A_SB; lia). rewrite EQx in SEPT1c, SEPT1q, SEPT1t. clear EQx.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 4 HP INtk ltac:(lia)) as SHT4.
replace (tk / 8 + 4 + A_SB) with (tk / 8 + 2147450884) in SHT4 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 4 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT4c & SEPT4q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 4 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT4t & _).
cbn [hl_sb A4L] in SEPT4c, SEPT4q, SEPT4t. assert (EQx : tk / 8 + A_SB + 4 = tk / 8 + 2147450884) by (unfold A_SB; lia). rewrite EQx in SEPT4c, SEPT4q, SEPT4t. clear EQx.
pose proof (blk_granA HIx _ _ _ _ _ _ _ pb 16 0 HP INpb ltac:(lia) ltac:(lia)) as SHP0.
replace (pb / 8 + 0 + A_SB) with (pb / 8 + 2147450880) in SHP0 by (unfold A_SB; lia).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
clear SEPT1c SEPT1q SEPT1t SEPT4c SEPT4q SEPT4t.
stash Himg_t5. stash Himg_p5.
cbn [pf_spf] in *. unfold A_TP in *.
try lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) => replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
step.
asan_rechkB.
step. step.
evt_done5. eapply (Kerrp m5); exact INV5.
Qed.

Lemma lit_part_B :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet)
(x1 gp t0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
pj_8 pj = Z_to_bv 64 (pf_tk pf / 8 + 2147450883) ->
(forall m' a0',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md A B (ts_set_x ts (t_co ts) (TS (ts_isd (t_x ts)) (Z_to_bv 64 (SPV (t_x ts) + 1)) (ts_choff (t_x ts)) (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))) cb nb pj sv errv ->
(forall b, PBOKat m ts b -> PBOKat m' (ts_set_x ts (t_co ts) (TS (ts_isd (t_x ts)) (Z_to_bv 64 (SPV (t_x ts) + 1)) (ts_choff (t_x ts)) (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))) b) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa APE_BREAK (t_co ts) gp t0 a0' a1 a2 a3 a4 a5 a6 a7 s3 (Z_to_bv 64 2) s6 s7 (Z_to_bv 64 (SPV (t_x ts) + 1)) s9 s11 t3 t4 t5 t6 F fc m')) ->
AJ5 A4L HIx A T md
(MS (mkR x1 (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 (Z_to_bv 64 (pf_lenr pf)) (Z_to_bv 64 (pf_tk pf + 32)) (Z_to_bv 64 (pa_sp0 pa)) (Z_to_bv 64 (pf_spf pf))
a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (shA (pa_F pa))) s3 (Z_to_bv 64 (pf_sb pf + t_co ts)) s5 s6 s7 (Z_to_bv 64 (SPV (t_x ts) + 1)) s9 (Z_to_bv 64 A_SB) s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x97898) fc None m (seg_rom asegs)).
Proof.
intros until fc. intros STC INV P16 Kbreak. pose proof INV as INV0. pe_openA STC INV.
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
pose proof FR as FR0. unfold pe_frameA in FR. destruct FR as (SLOTS & GAP & SAVED & FF & FSH).
unfold pe_slotsA in SLOTS. cbn zeta in SLOTS. rewrite P16 in SLOTS.
unfold pe_msA in *.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * mxd) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 3 HP INtk ltac:(lia)) as SHT3.
replace (tk / 8 + 3 + A_SB) with (tk / 8 + 2147450883) in SHT3 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 3 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT3c & SEPT3q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 3 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT3t & _).
cbn [hl_sb A4L] in SEPT3c, SEPT3q, SEPT3t. assert (EQx : tk / 8 + A_SB + 3 = tk / 8 + 2147450883) by (unfold A_SB; lia). rewrite EQx in SEPT3c, SEPT3q, SEPT3t. clear EQx.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(tk, tk + 72)] m) as MU.
unfold SPV in *. cbn [t_x ts_stpos] in *.
set (sp := bv_unsigned stpos mod 2^32) in *.
unfold APE_BREAK in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
assert (cs_T3_T : csep (tk / 8 + 2147450883) 1 tk (Z.of_nat 72)) by (unfold csep; clear - SEPT3t; lia).
clear SEPT3c SEPT3q SEPT3t.
stash Himg_t. clear REST TSK LV OBJ HPR BUD GAP SAVED FSH STR ERR SBin FF PB.
reenterA asegs A4L HIx asegs_wx HP.
step.
asan_rechkB.
step.
stepz.
do 3 step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _ |- _ =>
evt_done5;
destruct (PE_INV_A_tokw1 HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m mc md A B ts0
cb nb pj sv errv co (TS isd (Z_to_bv 64 (sp + 1)) (Z_to_bv 64 co) err ucs high quote) STC INV0 MUc WMc MIc TOKc ltac:(cbn [pf_len]; lia) eq_refl) as [INV3 PBT3]
end end.
eapply (Kbreak _ _ INV3 PBT3).
Qed.

Lemma null_m1_B :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet)
(x1 gp t0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_null ->

(forall m' gp' t0' a0' a1' a2' a3' a4' a5' a6' a7',
SPV (t_x ts) = 4 ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md A B (ts_lvl ts (TL ST_eatws ST_finish (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) cb nb pj sv errv ->
(forall k, PBOK m ts k -> PBOK m' (ts_lvl ts (TL ST_eatws ST_finish (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) k) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa APE_REDO (t_co ts) gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3 s5 s6 s7 (Z_to_bv 64 (SPV (t_x ts) + 1)) (Z_to_bv 64 (SPV (t_x ts))) s11 t3 t4 t5 t6 F fc m')) ->

(forall a0',
SPV (t_x ts) <> 4 ->
AJ5 A4L HIx A T md
(MS (mkR x1 (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 (Z_to_bv 64 (pf_lenr pf)) (Z_to_bv 64 (pf_tk pf + 32)) (Z_to_bv 64 (pa_sp0 pa)) (Z_to_bv 64 (pf_spf pf))
a0' a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (shA (pa_F pa))) s3 (Z_to_bv 64 (pf_sb pf + t_co ts)) s5 s6 s7 (Z_to_bv 64 (SPV (t_x ts) + 1)) (Z_to_bv 64 (SPV (t_x ts))) (Z_to_bv 64 A_SB) s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x97898) fc None m (seg_rom asegs))) ->
AJ5 A4L HIx A T md
(MS (mkR x1 (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 (Z_to_bv 64 (pf_lenr pf)) (Z_to_bv 64 (pf_tk pf + 32)) (Z_to_bv 64 (pa_sp0 pa)) (Z_to_bv 64 (pf_spf pf))
a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (shA (pa_F pa))) s3 (Z_to_bv 64 (pf_sb pf + t_co ts)) s5 s6 s7 (Z_to_bv 64 (SPV (t_x ts) + 1)) (Z_to_bv 64 (SPV (t_x ts))) (Z_to_bv 64 A_SB) s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x952c4) fc None m (seg_rom asegs)).
Proof.
intros until fc. intros STC INV Hl Hst Kredo Kpart. pose proof INV as INV0. pe_openA STC INV.
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
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 7 HP INtk ltac:(lia)) as SHT7.
replace (tk / 8 + 7 + A_SB) with (tk / 8 + 2147450887) in SHT7 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 7 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT7c & SEPT7q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 7 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT7t & _).
cbn [hl_sb A4L] in SEPT7c, SEPT7q, SEPT7t. assert (EQx : tk / 8 + A_SB + 7 = tk / 8 + 2147450887) by (unfold A_SB; lia). rewrite EQx in SEPT7c, SEPT7q, SEPT7t. clear EQx.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 2 HP INtk ltac:(lia)) as SHT2.
replace (tk / 8 + 2 + A_SB) with (tk / 8 + 2147450882) in SHT2 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 2 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT2c & SEPT2q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 2 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT2t & _).
cbn [hl_sb A4L] in SEPT2c, SEPT2q, SEPT2t. assert (EQx : tk / 8 + A_SB + 2 = tk / 8 + 2147450882) by (unfold A_SB; lia). rewrite EQx in SEPT2c, SEPT2q, SEPT2t. clear EQx.
shq_facts HP INq INtk q mxd tk (Z.of_nat depth) 0 SHQ0 SEPQ0c SEPQ0q SEPQ0t.
replace (q / 8 + 4 * (Z.of_nat depth) + 0 + A_SB) with (bse / 8 + 2147450880) in SHQ0 by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia).
assert (EQx : q / 8 + A_SB + (4 * (Z.of_nat depth) + 0) = bse / 8 + 2147450880) by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia). rewrite EQx in SEPQ0c, SEPQ0q, SEPQ0t. clear EQx.
shq_facts HP INq INtk q mxd tk (Z.of_nat depth) 2 SHQ2 SEPQ2c SEPQ2q SEPQ2t.
replace (q / 8 + 4 * (Z.of_nat depth) + 2 + A_SB) with (bse / 8 + 2147450882) in SHQ2 by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia).
assert (EQx : q / 8 + A_SB + (4 * (Z.of_nat depth) + 2) = bse / 8 + 2147450882) by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia). rewrite EQx in SEPQ2c, SEPQ2q, SEPQ2t. clear EQx.
unfold APE_BREAK, APE_REDO, APE_OUT, APE_ERRMEM, APE_JTAB in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
assert (cs_tk_L : csep tk 72 bse (Z.of_nat 32)) by (unfold csep; clear - Hdtq HbseR; lia).
assert (cs_L_tk : csep bse 32 tk (Z.of_nat 72)) by (unfold csep; clear - Hdtq HbseR; lia).
assert (cs_Q0_L : csep (bse / 8 + 2147450880) 1 bse (Z.of_nat 32)) by (unfold csep; clear - SEPQ0q HbseR; lia).
assert (cs_Q2_L : csep (bse / 8 + 2147450882) 1 bse (Z.of_nat 32)) by (unfold csep; clear - SEPQ2q HbseR; lia).
clear Hdtq SEPT7c SEPT7q SEPT7t SEPT2c SEPT2q SEPT2t SEPQ0c SEPQ0q SEPQ0t SEPQ2c SEPQ2q SEPQ2t.
unfold SPV in *. cbn [t_x ts_stpos] in *.
assert (SPR : 0 <= bv_unsigned stpos mod 2^32 < 2^32) by (apply Z.mod_pos_bound; lia).
set (sp := bv_unsigned stpos mod 2^32) in *.
destruct (null_mode _ _ _ SS26 ltac:(rewrite <- Hst; exact Hmode)) as (Ec0 & Ehn0). subst c0 hn0.
assert (Ecs : tl_cs l = None) by (destruct (tl_cs l); [exfalso; exact CLS0 | reflexivity]).
pose proof (LV depth l Hl) as (_ & _ & JO & _). rewrite Ecs in JO. cbn [jopt] in JO. destruct JO as [Ecur Ecbs].
stash Himg_t. stash Himg_q. stash Kredo. stash Kpart. clear PB REST TSK LV OBJ HPR BUD GAP SAVED FSH STR ERR SBin FF.
reenterA asegs A4L HIx asegs_wx HP.
assert (BLO : 0 < bse < 2^63 /\ q <= bse) by (subst bse; lia).
step.
step.
destruct (Z.eq_dec sp 4) as [E4 | N4].
2:{ if_falsex.
step.
evt_done5. unstash Kpart. eapply (Kpart _ N4). }
if_truex.
step.
asan_rechkB.
step.
asan_rechkMB 2.
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
stepz.
step. if_truex.
step.
asan_chkB.
step.
stepz.
asan_chkB.
stepz.
step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, Lc : rw_cells asegs mc bse _ |- _ =>
evt_done5; rewrite Hbse in MUc, Lc;
destruct (PE_INV_A_lvl_write HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m mc md A B ts0 cb nb pj sv errv l ST_eatws ST_finish CNone false CAny STC INV0 Hl MUc WMc MIc TOKc
ltac:(unfold srec_cells; cbn [tl_st tl_ss tl_cur tl_name]; rewrite Ecur; exact Lc) Hmode ltac:(reflexivity) ltac:(unfold ST_eatws; lia) ltac:(unfold ST_finish; lia)
(or_intror eq_refl) ltac:(rewrite Hst; reflexivity)) as [INV3 PBK3]
end end.
unstash Kredo. eapply (Kredo _ _ _ _ _ _ _ _ _ _ _ E4 INV3 PBK3).
Qed.

Lemma null_m2_B :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP v2 ra2 : Z) (nB : nat)
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv -> PBOKat m ts kP -> BOK pf pa ts B (S (Z.to_nat 2816 + nB)) ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_null ->
pe_s0 sv = Z_to_bv 64 v2 -> pe_ra sv = Z_to_bv 64 ra2 ->
(v2 < alloc_ceiling \/ v2 mod 8 <> 0 \/ v2 <= pa_sp0 pa \/ hiA_top A4L HIx - 16 <= v2) /\ 0 <= v2 < 2^64 ->
uw_ok A4L (hl_malloc A4H) (Z_to_bv 64 0x9f3fc) (UWfp ra2 v2) ->

(forall m' md' A' B' errv' r BS gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc',
SPV (t_x ts) = 3 -> (length BS <= 3)%nat -> jfresh (Sdouble false) BS 9 ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' (ts_lvl ts (TL ST_eatws ST_finish r (Some (Sdouble false)) BS 0 [])) cb nb pj sv errv' ->
PBOKat m' (ts_lvl ts (TL ST_eatws ST_finish r (Some (Sdouble false)) BS 0 [])) kP ->
BOK pf pa (ts_lvl ts (TL ST_eatws ST_finish r (Some (Sdouble false)) BS 0 [])) B' nB ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msA asegs pf pa APE_REDO (t_co ts) gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3 s5 s6 s7 (Z_to_bv 64 (SPV (t_x ts) + 1)) (Z_to_bv 64 (SPV (t_x ts))) s11 t3' t4' t5' t6' F' fc' m')) ->

(forall m' md' A' B' errv' gp' t0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc',
PE_INVW_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' ts [] cb nb pj sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msO asegs pf pa APE_ERR2 gp' t0' (Z_to_bv 64 (pf_lenr pf)) (Z_to_bv 64 (pf_tk pf + 32)) (Z_to_bv 64 16) a1' a2' a3' a4' a5' a6' a7' s3 (Z_to_bv 64 (pf_sb pf + t_co ts)) s5 s6 s7 (Z_to_bv 64 (SPV (t_x ts) + 1)) (Z_to_bv 64 (SPV (t_x ts))) s11 t3' t4' t5' t6' F' fc' m')) ->

(forall a0',
SPV (t_x ts) <> 3 ->
AJ5 A4L HIx A T md
(MS (mkR x1 (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 (Z_to_bv 64 (pf_lenr pf)) (Z_to_bv 64 (pf_tk pf + 32)) (Z_to_bv 64 (pa_sp0 pa)) (Z_to_bv 64 (pf_spf pf))
a0' a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (shA (pa_F pa))) s3 (Z_to_bv 64 (pf_sb pf + t_co ts)) s5 s6 s7 (Z_to_bv 64 (SPV (t_x ts) + 1)) (Z_to_bv 64 (SPV (t_x ts))) (Z_to_bv 64 A_SB) s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x97898) fc None m (seg_rom asegs))) ->
AJ5 A4L HIx A T md
(MS (mkR x1 (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 (pa_sp0 pa)) (Z_to_bv 64 (pf_spf pf))
a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (shA (pa_F pa))) s3 (Z_to_bv 64 (pf_sb pf + t_co ts)) s5 s6 s7 (Z_to_bv 64 (SPV (t_x ts) + 1)) (Z_to_bv 64 (SPV (t_x ts))) (Z_to_bv 64 A_SB) s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x94a54) fc None m (seg_rom asegs)).
Proof.
intros until fc. intros STC BSL INV PBK BK Hl Hst S0V RAV HV UWK Kredo Kerr16 Kpart. pose proof INV as INV0. pe_openA STC INV.
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
unfold APE_BREAK, APE_REDO, APE_OUT, APE_ERRMEM, APE_ERR2, APE_JTAB in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
unfold SPV in *. cbn [t_x ts_stpos] in *.
assert (SPR : 0 <= bv_unsigned stpos mod 2^32 < 2^32) by (apply Z.mod_pos_bound; lia).
set (sp := bv_unsigned stpos mod 2^32) in *.
destruct (null_mode _ _ _ SS26 ltac:(rewrite <- Hst; exact Hmode)) as (Ec0 & Ehn0). subst c0 hn0.
cbn [name_ok] in NM0. destruct NM0 as [Hn0 Hnbs0].
assert (Ecs : tl_cs l = None) by (destruct (tl_cs l); [exfalso; exact CLS0 | reflexivity]).
pose proof (LV depth l Hl) as (_ & _ & JO & _). rewrite Ecs in JO. cbn [jopt] in JO. destruct JO as [Ecur Ecbs].
assert (Eobjbs : objbs = []).
{ unfold cur_st in OBJ. cbn [t_levels t_depth t_objbs ts0] in OBJ. rewrite Hl, Hst in OBJ. exact OBJ. }
pose proof (PE_WIN_open HIx GA (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m md A B ts0 cb nb pj sv errv l INV0 Hl Hn0 Hnbs0 Eobjbs) as WIN0.
rewrite Ecur, Ecs, Ecbs in WIN0.
set (lw0 := TL (tl_st l) (tl_ss l) 0 None [] 0 []) in *. set (tw0 := ts_lvl ts0 lw0) in *.
assert (El : l = lw0) by (unfold lw0; destruct l as [st_ ss_ cur_ cs_ cbs_ name_ nbs_]; cbn [tl_st tl_ss tl_cur tl_cs tl_cbs tl_name tl_nbs] in *; congruence).
assert (Etw0 : tw0 = ts0) by (unfold tw0; rewrite <- El; apply (ts_lvl_same ts0 l Hl)).
assert (PBK0 : PBOKat m tw0 kP) by (exact (PBOKat_same m ts0 tw0 _ eq_refl eq_refl PBK)).
assert (Hlen0 : length (t_levels tw0) = Z.to_nat mxd) by (unfold tw0, ts_lvl, ts0; cbn [t_levels t_depth]; rewrite lupd_length; exact LEN32).
pose proof (BOK_afford (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) ts0 B nB new_scalar_costA BSL BK ltac:(pose proof (K_ev_pos (PEF tk oldl newl len lenr sb spf pmd mxd fl)); unfold new_scalar_costA; lia)) as COST.
pose proof (nandbl_roA m MI) as NANRO.
stash Himg_t. stash Himg_q. stash Kredo. stash Kerr16. stash Kpart. stash WIN0. stash INV0.
clear PB REST LV OBJ HPR BUD GAP SAVED FSH FF STR ERR SBin SHT SHQ4 SHQ Ld Hdtq.
reenterA asegs A4L HIx asegs_wx HP.
step.
step. step.
step.
destruct (Z.eq_dec sp 3) as [E3 | N3].
2:{ if_falsex.
step.
evt_done5. unstash Kpart. eapply (Kpart _ N3). }
if_truex.
step.
step.
step.

unstash WIN0.
evt_done5.
eapply (pe_new_double_w HIx GA GA_pres NEWDBL (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m md A B tw0 cb nb pj sv errv T kP v2 ra2);
[ exact STC | exact WIN0 | exact PBK0 | exact COST | exact S0V | exact RAV | exact HV | exact UWK
| unfold dbl_special; rewrite reg_get_set_same_u by (vm_compute; reflexivity); apply Z.leb_le; vm_compute; reflexivity
| rewrite unsigned_lit by lia; reflexivity |].
intros mn2 md2 A2 B2 errv2 r w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 F2 fc2 OUT2 PBK2 HB2 HD2 FS2 FRM2.
assert (FS2' : fsaved F F2) by (eapply fsaved_trans; [apply fsaved_set10 | exact FS2]).
cbn [pf_spf pa_sp0 pa_F] in *. unfold A_TP in *.
clear TOK SLOTS MU WM MI HP INtk INq Htal Htlo Hthi Hqal Hqlo Hqhi Hqtk WIN0 PBK0 FR0 NANRO FS2.
assert (Hlw0 : nth_error (t_levels tw0) depth = Some lw0) by (unfold tw0, ts_lvl, ts0; cbn [t_levels t_depth]; apply nth_error_lupd_eq; apply nth_error_Some; rewrite Hl; discriminate).
assert (Eb0 : lvl_blocks l = []) by (unfold lvl_blocks; rewrite Ecbs, Hnbs0; reflexivity).
destruct OUT2 as [(-> & WIN2) | (Hr & BS & LEN3 & JF & Rr & WIN2)].
-
pose proof WIN2 as (CORE2 & BASE2 & _). destruct CORE2 as (_ & _ & _ & _ & TOK & _ & _ & TSK2 & FR2). pose proof (proj1 BASE2) as HP. clear BASE2.
unfold tw0, ts_lvl, ts0 in TOK. cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_tk pf_mxd pf_fl] in TOK.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
pose proof FR2 as (SLOTS & _). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in SLOTS.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 (tsF tw0 []))) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * mxd) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 (tsF tw0 []))) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t2.
blk_factsA A4L HIx HP q (32 * mxd) Hqal Hqlo Hqhi Himg_q2.
pose proof (q_ne_tkA HIx _ _ _ _ _ _ _ _ _ _ HP) as Hqtk. cbn [pf_tk] in Hqtk.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ tk 72 q (32 * mxd) HP (in_or_app _ LM _ (or_introl INtk)) (in_or_app _ LM _ (or_introl INq)) ltac:(congruence)) as Hdtq.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs mn2) as WM.
pose proof (TSK2 depth lw0 Hlw0) as Ld. rewrite <- Hbse in Ld. unfold srec_cells, lw0 in Ld. cbn [tl_st tl_ss tl_cur tl_name] in Ld.
shq_facts HP INq INtk q mxd tk (Z.of_nat depth) 2 SHQ2 SEPQ2c SEPQ2q SEPQ2t.
replace (q / 8 + 4 * (Z.of_nat depth) + 2 + A_SB) with (bse / 8 + 2147450882) in SHQ2 by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia).
assert (EQx : q / 8 + A_SB + (4 * (Z.of_nat depth) + 2) = bse / 8 + 2147450882) by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia). rewrite EQx in SEPQ2c, SEPQ2q, SEPQ2t. clear EQx.
shq_facts HP INq INtk q mxd tk (Z.of_nat depth) 0 SHQ0 SEPQ0c SEPQ0q SEPQ0t.
replace (q / 8 + 4 * (Z.of_nat depth) + 0 + A_SB) with (bse / 8 + 2147450880) in SHQ0 by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia).
assert (EQx : q / 8 + A_SB + (4 * (Z.of_nat depth) + 0) = bse / 8 + 2147450880) by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia). rewrite EQx in SEPQ0c, SEPQ0q, SEPQ0t. clear EQx.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 7 HP INtk ltac:(lia)) as SHT7.
replace (tk / 8 + 7 + A_SB) with (tk / 8 + 2147450887) in SHT7 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 7 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT7c & SEPT7q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 7 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT7t & _).
cbn [hl_sb A4L] in SEPT7c, SEPT7q, SEPT7t. assert (EQx : tk / 8 + A_SB + 7 = tk / 8 + 2147450887) by (unfold A_SB; lia). rewrite EQx in SEPT7c, SEPT7q, SEPT7t. clear EQx.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 2 HP INtk ltac:(lia)) as SHT2.
replace (tk / 8 + 2 + A_SB) with (tk / 8 + 2147450882) in SHT2 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 2 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT2c & SEPT2q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 2 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT2t & _).
cbn [hl_sb A4L] in SEPT2c, SEPT2q, SEPT2t. assert (EQx : tk / 8 + A_SB + 2 = tk / 8 + 2147450882) by (unfold A_SB; lia). rewrite EQx in SEPT2c, SEPT2q, SEPT2t. clear EQx.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 4 HP INtk ltac:(lia)) as SHT4.
replace (tk / 8 + 4 + A_SB) with (tk / 8 + 2147450884) in SHT4 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 4 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT4c & SEPT4q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 4 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT4t & _).
cbn [hl_sb A4L] in SEPT4c, SEPT4q, SEPT4t. assert (EQx : tk / 8 + A_SB + 4 = tk / 8 + 2147450884) by (unfold A_SB; lia). rewrite EQx in SEPT4c, SEPT4q, SEPT4t. clear EQx.
pose proof (munch_refl [(bse, bse + 32)] mn2) as MU.
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
assert (cs_tk_L : csep tk 72 bse (Z.of_nat 32)) by (unfold csep; clear - Hdtq HbseR; lia).
assert (cs_L_tk : csep bse 32 tk (Z.of_nat 72)) by (unfold csep; clear - Hdtq HbseR; lia).
assert (cs_Q0_L : csep (bse / 8 + 2147450880) 1 bse (Z.of_nat 32)) by (unfold csep; clear - SEPQ0q HbseR; lia).
assert (cs_T4_L : csep (tk / 8 + 2147450884) 1 bse (Z.of_nat 32)) by (unfold csep; clear - SEPT4q HbseR; lia).
clear Hdtq SEPQ2c SEPQ2q SEPQ2t SEPQ0c SEPQ0q SEPQ0t SEPT7c SEPT7q SEPT7t SEPT2c SEPT2q SEPT2t SEPT4c SEPT4q SEPT4t.
stash Himg_t2. stash Himg_q2. stash WIN2. stash TSK2. stash FR2.
reenterA asegs A4L HIx asegs_wx HP.
assert (BLO : 0 < bse < 2^63 /\ q <= bse) by (subst bse; lia).
step.
asan_rechkB.
step. step.
asan_rechkMB 4.
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
stepz.
step. if_truex.
step.
if_false.
step. step.
asan_rechkB.
step. step.

unstash WIN2. unstash TSK2. unstash FR2.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ mn2 mc, WMc : wmono asegs mn2 mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, Lc : rw_cells asegs mc bse _ |- _ =>
evt_done5;
assert (INqL : Forall (fun iv => exists a n, In (a, n) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 (tsF tw0 []) ++ LM) /\ a <= fst iv /\ snd iv <= a + n) [(bse, bse + 32)])
by (apply Forall_cons; [exists q, (32 * mxd); cbn [fst snd]; split; [apply in_or_app; left; exact INq | lia] | apply Forall_nil]);
assert (FRc : pe_frameA asegs mc (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) cb nb pj sv)
by (eapply (pe_frameA_blkwriteG HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) _ LM FRS B2 A2 mn2 mc md2 lo [(bse, bse + 32)] cb nb pj sv); [exact STC | exact HP | exact INqL | exact FR2 | exact MUc | exact WMc]);
assert (TSKc : tstack asegs mc q (lupd (t_levels tw0) (t_depth tw0) lw0))
by (pose proof MUc as MUc'; pose proof Lc as Lc'; rewrite Hbse in MUc', Lc'; eapply (tstack_put asegs mn2 mc q (t_levels tw0) depth lw0 []);
[exact TSK2 | rewrite Hlen0; lia | exact MUc' | exact WMc | intros; exact I | exact Lc']);
destruct (PE_WIN_write HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo mn2 mc md2 A2 B2 tw0 0 None [] 1
cb nb pj sv errv2 [(bse, bse + 32)] lw0 cb nb pj STC WIN2 MUc WMc MIc
ltac:(apply Forall_cons; [right; cbn [fst snd pf_mxd]; lia | apply Forall_nil])
TOKc TSKc FRc ltac:(unfold lvl_bare, lw0; cbn [tl_st tl_ss tl_cs tl_cbs tl_name tl_nbs]; repeat split; try reflexivity; lia)) as [WIN3 PBT3]
end end.
set (tw2 := ts_lvl tw0 lw0) in *.
assert (Etw2 : tw2 = ts0) by (unfold tw2; rewrite (ts_lvl_same tw0 lw0 Hlw0); exact Etw0).
pose proof (BOK_weak _ _ _ _ _ (BOK_pay (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) ts0 B B2 nB new_scalar_costA BK ltac:(pose proof (K_ev_pos (PEF tk oldl newl len lenr sb spf pmd mxd fl)); unfold new_scalar_costA; lia) HB2 ltac:(lia))) as [HBw HDw].
pose proof (PE_WIN_close_weak HIx GA (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo _ md2 A2 B2 tw2 cb nb pj sv errv2 1 WIN3
ltac:(exists lw0; split; [rewrite Etw2, <- El; exact Hl | reflexivity])
ltac:(rewrite Etw2; exact HBw) HDw) as INVw.
rewrite Etw2 in INVw.
unstash Kerr16. eapply (Kerr16 _ md2 A2 B2 errv2); [exact INVw | exact FS2' | exact FRM2].
-
pose proof WIN2 as (CORE2 & BASE2 & _). destruct CORE2 as (_ & _ & _ & _ & TOK & _ & _ & TSK2 & FR2). pose proof (proj1 BASE2) as HP. clear BASE2.
unfold tw0, ts_lvl, ts0 in TOK. cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_tk pf_mxd pf_fl] in TOK.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
pose proof FR2 as (SLOTS & _). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in SLOTS.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 (tsF tw0 BS))) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * mxd) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 (tsF tw0 BS))) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t2.
blk_factsA A4L HIx HP q (32 * mxd) Hqal Hqlo Hqhi Himg_q2.
pose proof (q_ne_tkA HIx _ _ _ _ _ _ _ _ _ _ HP) as Hqtk. cbn [pf_tk] in Hqtk.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ tk 72 q (32 * mxd) HP (in_or_app _ LM _ (or_introl INtk)) (in_or_app _ LM _ (or_introl INq)) ltac:(congruence)) as Hdtq.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs mn2) as WM.
pose proof (TSK2 depth lw0 Hlw0) as Ld. rewrite <- Hbse in Ld. unfold srec_cells, lw0 in Ld. cbn [tl_st tl_ss tl_cur tl_name] in Ld.
shq_facts HP INq INtk q mxd tk (Z.of_nat depth) 2 SHQ2 SEPQ2c SEPQ2q SEPQ2t.
replace (q / 8 + 4 * (Z.of_nat depth) + 2 + A_SB) with (bse / 8 + 2147450882) in SHQ2 by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia).
assert (EQx : q / 8 + A_SB + (4 * (Z.of_nat depth) + 2) = bse / 8 + 2147450882) by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia). rewrite EQx in SEPQ2c, SEPQ2q, SEPQ2t. clear EQx.
shq_facts HP INq INtk q mxd tk (Z.of_nat depth) 0 SHQ0 SEPQ0c SEPQ0q SEPQ0t.
replace (q / 8 + 4 * (Z.of_nat depth) + 0 + A_SB) with (bse / 8 + 2147450880) in SHQ0 by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia).
assert (EQx : q / 8 + A_SB + (4 * (Z.of_nat depth) + 0) = bse / 8 + 2147450880) by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia). rewrite EQx in SEPQ0c, SEPQ0q, SEPQ0t. clear EQx.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 7 HP INtk ltac:(lia)) as SHT7.
replace (tk / 8 + 7 + A_SB) with (tk / 8 + 2147450887) in SHT7 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 7 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT7c & SEPT7q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 7 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT7t & _).
cbn [hl_sb A4L] in SEPT7c, SEPT7q, SEPT7t. assert (EQx : tk / 8 + A_SB + 7 = tk / 8 + 2147450887) by (unfold A_SB; lia). rewrite EQx in SEPT7c, SEPT7q, SEPT7t. clear EQx.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 2 HP INtk ltac:(lia)) as SHT2.
replace (tk / 8 + 2 + A_SB) with (tk / 8 + 2147450882) in SHT2 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 2 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT2c & SEPT2q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 2 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT2t & _).
cbn [hl_sb A4L] in SEPT2c, SEPT2q, SEPT2t. assert (EQx : tk / 8 + A_SB + 2 = tk / 8 + 2147450882) by (unfold A_SB; lia). rewrite EQx in SEPT2c, SEPT2q, SEPT2t. clear EQx.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 4 HP INtk ltac:(lia)) as SHT4.
replace (tk / 8 + 4 + A_SB) with (tk / 8 + 2147450884) in SHT4 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 4 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT4c & SEPT4q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 4 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT4t & _).
cbn [hl_sb A4L] in SEPT4c, SEPT4q, SEPT4t. assert (EQx : tk / 8 + A_SB + 4 = tk / 8 + 2147450884) by (unfold A_SB; lia). rewrite EQx in SEPT4c, SEPT4q, SEPT4t. clear EQx.
pose proof (munch_refl [(bse, bse + 32)] mn2) as MU.
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
assert (cs_tk_L : csep tk 72 bse (Z.of_nat 32)) by (unfold csep; clear - Hdtq HbseR; lia).
assert (cs_L_tk : csep bse 32 tk (Z.of_nat 72)) by (unfold csep; clear - Hdtq HbseR; lia).
assert (cs_Q0_L : csep (bse / 8 + 2147450880) 1 bse (Z.of_nat 32)) by (unfold csep; clear - SEPQ0q HbseR; lia).
assert (cs_T4_L : csep (tk / 8 + 2147450884) 1 bse (Z.of_nat 32)) by (unfold csep; clear - SEPT4q HbseR; lia).
clear Hdtq SEPQ2c SEPQ2q SEPQ2t SEPQ0c SEPQ0q SEPQ0t SEPT7c SEPT7q SEPT7t SEPT2c SEPT2q SEPT2t SEPT4c SEPT4q SEPT4t.
stash Himg_t2. stash Himg_q2. stash WIN2. stash TSK2. stash FR2.
reenterA asegs A4L HIx asegs_wx HP.
assert (BLO : 0 < bse < 2^63 /\ q <= bse) by (subst bse; lia).
step.
asan_rechkB.
step. step.
asan_rechkMB 4.
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
stepz.
step. if_truex.
step.
if_truex.
step.
asan_chkB.
step.
stepz.
asan_chkB.
stepz.
step.

set (lw2 := TL ST_eatws ST_finish r None [] 0 []).
unstash WIN2. unstash TSK2. unstash FR2.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ mn2 mc, WMc : wmono asegs mn2 mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, Lc : rw_cells asegs mc bse _ |- _ =>
evt_done5;
assert (INqL : Forall (fun iv => exists a n, In (a, n) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 (tsF tw0 BS) ++ LM) /\ a <= fst iv /\ snd iv <= a + n) [(bse, bse + 32)])
by (apply Forall_cons; [exists q, (32 * mxd); cbn [fst snd]; split; [apply in_or_app; left; exact INq | lia] | apply Forall_nil]);
assert (FRc : pe_frameA asegs mc (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) cb nb pj sv)
by (eapply (pe_frameA_blkwriteG HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) _ LM FRS B2 A2 mn2 mc md2 lo [(bse, bse + 32)] cb nb pj sv); [exact STC | exact HP | exact INqL | exact FR2 | exact MUc | exact WMc]);
assert (TSKc : tstack asegs mc q (lupd (t_levels tw0) (t_depth tw0) lw2))
by (pose proof MUc as MUc'; pose proof Lc as Lc'; rewrite Hbse in MUc', Lc'; eapply (tstack_put asegs mn2 mc q (t_levels tw0) depth lw2 []);
[exact TSK2 | rewrite Hlen0; lia | exact MUc' | exact WMc | intros; exact I | exact Lc']);
destruct (PE_WIN_write HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo mn2 mc md2 A2 B2 tw0 r (Some (Sdouble false)) BS 1
cb nb pj sv errv2 [(bse, bse + 32)] lw2 cb nb pj STC WIN2 MUc WMc MIc
ltac:(apply Forall_cons; [right; cbn [fst snd pf_mxd]; lia | apply Forall_nil])
TOKc TSKc FRc ltac:(unfold lvl_bare, lw2, ST_eatws, ST_finish; cbn [tl_st tl_ss tl_cs tl_cbs tl_name tl_nbs]; repeat split; try reflexivity; lia)) as [WIN3 PBT3]
end end.
set (tw2 := ts_lvl tw0 lw2) in *.
assert (Etw2 : forall lx, ts_lvl tw2 lx = ts_lvl ts0 lx) by (intros lx; unfold tw2, tw0; rewrite !ts_lvl_lvl; reflexivity).
assert (Hlw2 : nth_error (t_levels tw2) (t_depth tw2) = Some lw2) by (unfold tw2, ts_lvl; cbn [t_levels t_depth]; apply nth_error_lupd_eq; rewrite Hlen0; cbn [t_depth tw0 ts_lvl ts0]; lia).
assert (BKf : BOK (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) (ts_lvl ts0 (TL ST_eatws ST_finish r (Some (Sdouble false)) BS 0 [])) B2 nB).
{ eapply (BOK_attach (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) ts0 B B2 nB l ST_eatws ST_finish r (Sdouble false) BS new_scalar_costA BK Hl Ecs Eb0);
[ unfold phi_level; cbn [tl_cs]; lia
| unfold phi_level; cbn [tl_cs]; pose proof (K_ev_pos (PEF tk oldl newl len lenr sb spf pmd mxd fl)); unfold K_free, new_scalar_costA; lia
| intros kids Ek; discriminate Ek | intros kids Ek; discriminate Ek | exact HB2 | lia ]. }
pose proof (PE_WIN_close_cur HIx GA (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo _ md2 A2 B2 tw2 r (Sdouble false) BS cb nb pj sv errv2 lw2 CAny WIN3 Hlw2 eq_refl
ltac:(vm_compute; reflexivity) I ltac:(reflexivity)
ltac:(cbn [tl_st tl_ss lw2]; rewrite Etw2; exact (BOK_weak _ _ _ _ _ BKf))) as INVf.
cbn [tl_st tl_ss lw2] in INVf. rewrite Etw2 in INVf.
unstash Kredo. eapply (Kredo _ md2 A2 B2 errv2 r BS); [exact E3 | exact LEN3 | exact JF | exact INVf | | exact BKf | exact FS2' | exact FRM2].
eapply PBOKat_same with (ts := tw2); [reflexivity | reflexivity |]. exact (PBT3 _ PBK2).
Qed.

Lemma seg_null_B :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (v2 ra2 : Z) (nB : nat)
(gp t0 a5 a7 s3 s6 s7 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa -> pf_fl pf = 0 ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv -> PBOK m ts 0 -> BOK pf pa ts B (S (Z.to_nat 2816 + nB)) ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_null ->
t_co ts < pf_len pf -> SPV (t_x ts) <= t_co ts ->
pe_s0 sv = Z_to_bv 64 v2 -> pe_ra sv = Z_to_bv 64 ra2 ->
(v2 < alloc_ceiling \/ v2 mod 8 <> 0 \/ v2 <= pa_sp0 pa \/ hiA_top A4L HIx - 16 <= v2) /\ 0 <= v2 < 2^64 ->
uw_ok A4L (hl_malloc A4H) (Z_to_bv 64 0x9f3fc) (UWfp ra2 v2) ->

(forall m' md' A' B' pbs' errv' pj' gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' (ts_set_x (ts_pbs ts pbs') (t_co ts) (TS (ts_isd (t_x ts)) (Z_to_bv 64 (SPV (t_x ts) + 1)) (ts_choff (t_x ts)) (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))) cb nb pj' sv errv' ->
PBOK m' (ts_set_x (ts_pbs ts pbs') (t_co ts) (TS (ts_isd (t_x ts)) (Z_to_bv 64 (SPV (t_x ts) + 1)) (ts_choff (t_x ts)) (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))) 1 ->
BOK pf pa (ts_set_x (ts_pbs ts pbs') (t_co ts) (TS (ts_isd (t_x ts)) (Z_to_bv 64 (SPV (t_x ts) + 1)) (ts_choff (t_x ts)) (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))) B' nB ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msA asegs pf pa APE_BREAK (t_co ts) gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' (Z_to_bv 64 2) s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' m')) ->

(forall m' md' A' B' pbs' errv' pj' gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc',
SPV (t_x ts) = 4 ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' (ts_lvl (ts_pbs ts pbs') (TL ST_eatws ST_finish (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) cb nb pj' sv errv' ->
PBOK m' (ts_lvl (ts_pbs ts pbs') (TL ST_eatws ST_finish (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) 1 ->
BOK pf pa (ts_lvl (ts_pbs ts pbs') (TL ST_eatws ST_finish (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) B' nB ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msA asegs pf pa APE_REDO (t_co ts) gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' m')) ->

(forall m' md' A' B' pbs' errv' pj' r BS gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc',
SPV (t_x ts) = 3 -> (length BS <= 3)%nat -> jfresh (Sdouble false) BS 9 ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' (ts_lvl (ts_pbs ts pbs') (TL ST_eatws ST_finish r (Some (Sdouble false)) BS 0 [])) cb nb pj' sv errv' ->
PBOK m' (ts_lvl (ts_pbs ts pbs') (TL ST_eatws ST_finish r (Some (Sdouble false)) BS 0 [])) 1 ->
BOK pf pa (ts_lvl (ts_pbs ts pbs') (TL ST_eatws ST_finish r (Some (Sdouble false)) BS 0 [])) B' nB ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msA asegs pf pa APE_REDO (t_co ts) gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' m')) ->

(forall m' md' A' B' errv' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s6' t3' t4' t5' t6' F' fc',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' ts cb nb pj sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msO asegs pf pa APE_ERRMEM gp t0' t1' t2' (Z_to_bv 64 (pf_tk pf + 36)) a1' a2' a3' a4' a5' a6' a7' s3 (Z_to_bv 64 (pf_sb pf + t_co ts)) (Z_to_bv 64 q) s6' s7 (Z_to_bv 64 (Z.of_nat (t_depth ts))) s9 s11 t3' t4' t5' t6' F' fc' m')) ->

(forall m' md' A' B' pbs' errv' pj' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc',
PE_INVW_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' (ts_pbs ts pbs') [] cb nb pj' sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msO asegs pf pa APE_ERR2 gp' t0' t1' t2' (Z_to_bv 64 16) a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' m')) ->

(forall m' md' A' B' pbs' errv' pj' (x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' : word) F' fc',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' (ts_pbs ts pbs') cb nb pj' sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msX asegs pf pa APE_ERR3 x1' gp' t0' t1' t2' (Z_to_bv 64 5) a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' m')) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa (pe_jtA ST_null) (t_co ts) gp t0 (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) (Z_to_bv 64 (tl_st l)) (Z_to_bv 64 0) (Z_to_bv 64 (q / 8 + 4 * Z.of_nat (t_depth ts) + A_SB)) (Z_to_bv 64 0) a5 (Z_to_bv 64 APE_JTAB) a7 s3 (Z_to_bv 64 q) s6 s7 (Z_to_bv 64 (Z.of_nat (t_depth ts))) s9 s11 t3 t4 t5 t6 F fc m).
Proof.
intros until fc. intros STC BSL FL0 INV PBK BK Hl Hst Hco SPB S0V RAV HV UWK Kbreak Kredo1 Kredo2 Kerr16a Kerr16b Kerrp.
pose proof STC as (_ & _ & _ & _ & _ & LEN & _).
pose proof INV as [(_ & _ & CO & _) _].
eapply (null_head_B pf pa q LB0 LM FRS payload me lo m md A B ts l cb nb pj sv errv T nB gp t0 a5 a7 s3 s6 s7 s9 s11 t3 t4 t5 t6 F fc STC BSL INV PBK BK Hl Hst Hco SPB); [| exact Kerr16a].
intros m1 md1 A1 B1 pbs1 errv1 pj1 x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3v s5v s7' s11' t3' t4' t5' t6' F1 fc1 INV1 P16 PBK1 BK1 Es5 Es3 FS1 FRM1.
set (ts1 := ts_pbs ts pbs1) in *.
assert (Hl1 : nth_error (t_levels ts1) (t_depth ts1) = Some l) by exact Hl.
eapply (lit_cmp_B pf pa q LB0 LM FRS payload me lo m1 md1 A1 B1 ts1 cb nb pj1 sv errv1 T x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3v s5v s7' s11' t3' t4' t5' t6' F1 fc1 STC FL0 INV1 Es5 Es3).
-
intros m2 x1_2 gp2 t0_2 a0_2 a1_2 a2_2 a3_2 a4_2 a5_2 a6_2 a7_2 s3_2 s5_2 s6_2 s7_2 s11_2 t3_2 t4_2 t5_2 t6_2 INV2 PBT2.
eapply (null_m1_B pf pa q LB0 LM FRS payload me lo m2 md1 A1 B1 ts1 l cb nb pj1 sv errv1 T x1_2 gp2 t0_2 a0_2 a1_2 a2_2 a3_2 a4_2 a5_2 a6_2 a7_2 s3_2 s5_2 s6_2 s7_2 s11_2 t3_2 t4_2 t5_2 t6_2 F1 fc1 STC INV2 Hl1 Hst).
+ intros m3 gp3 t0_3 a0_3 a1_3 a2_3 a3_3 a4_3 a5_3 a6_3 a7_3 E4 INV3 PBK3.
eapply (Kredo1 m3 md1 A1 B1 pbs1 errv1 pj1); [exact E4 | exact INV3 | exact (PBK3 1 (PBT2 _ PBK1)) | | exact FS1 | exact FRM1].
eapply (BOK_lvl_restate pf pa ts1 B1 nB l ST_eatws ST_finish Hl1); [intros _; apply lvl_closed_fin; reflexivity | exact (BOK_drop _ _ _ _ _ _ BK1)].
+ intros a0_3 N4.
eapply (lit_part_B pf pa q LB0 LM FRS payload me lo m2 md1 A1 B1 ts1 cb nb pj1 sv errv1 T x1_2 gp2 t0_2 a0_3 a1_2 a2_2 a3_2 a4_2 a5_2 a6_2 a7_2 s3_2 s5_2 s6_2 s7_2 _ s11_2 t3_2 t4_2 t5_2 t6_2 F1 fc1 STC INV2 P16).
intros m3 a0_4 INV3 PBT3.
eapply (Kbreak m3 md1 A1 B1 pbs1 errv1 pj1); [exact INV3 | exact (PBT3 _ (PBT2 _ PBK1)) | | exact FS1 | exact FRM1].
apply BOK_set_x; [apply Z.le_refl | exact (BOK_drop _ _ _ _ _ _ BK1)].
-
intros m2 x1_2 gp2 t0_2 t1_2 t2_2 a0_2 a1_2 a2_2 a3_2 a4_2 a5_2 a6_2 a7_2 s3_2 s5_2 s6_2 s7_2 s11_2 t3_2 t4_2 t5_2 t6_2 INV2 PBT2.
eapply (null_m2_B pf pa q LB0 LM FRS payload me lo m2 md1 A1 B1 ts1 l cb nb pj1 sv errv1 T (t_co ts1 + 1) v2 ra2 nB x1_2 gp2 t0_2 t1_2 t2_2 a0_2 a1_2 a2_2 a3_2 a4_2 a5_2 a6_2 a7_2 s3_2 s5_2 s6_2 s7_2 s11_2 t3_2 t4_2 t5_2 t6_2 F1 fc1
STC BSL INV2 (PBT2 _ PBK1) BK1 Hl1 Hst S0V RAV HV UWK).
+ intros m3 md3 A3 B3 errv3 r BS gp3 t0_3 a0_3 a1_3 a2_3 a3_3 a4_3 a5_3 a6_3 a7_3 t3_3 t4_3 t5_3 t6_3 F3 fc3 E3 LEN3 JF INV3 PBK3 BK3 FS3 FRM3.
eapply (Kredo2 m3 md3 A3 B3 pbs1 errv3 pj1 r BS); [exact E3 | exact LEN3 | exact JF | exact INV3 | exact PBK3 | exact BK3 | eapply fsaved_trans; [exact FS1 | exact FS3] | intros X; exact (FRM3 (FRM1 X))].
+ intros m3 md3 A3 B3 errv3 gp3 t0_3 a1_3 a2_3 a3_3 a4_3 a5_3 a6_3 a7_3 t3_3 t4_3 t5_3 t6_3 F3 fc3 INVW3 FS3 FRM3.
eapply (Kerr16b m3 md3 A3 B3 pbs1 errv3 pj1); [exact INVW3 | eapply fsaved_trans; [exact FS1 | exact FS3] | intros X; exact (FRM3 (FRM1 X))].
+ intros a0_3 N3.
eapply (lit_part_B pf pa q LB0 LM FRS payload me lo m2 md1 A1 B1 ts1 cb nb pj1 sv errv1 T x1_2 gp2 t0_2 a0_3 a1_2 a2_2 a3_2 a4_2 a5_2 a6_2 a7_2 s3_2 s5_2 s6_2 s7_2 _ s11_2 t3_2 t4_2 t5_2 t6_2 F1 fc1 STC INV2 P16).
intros m3 a0_4 INV3 PBT3.
eapply (Kbreak m3 md1 A1 B1 pbs1 errv1 pj1); [exact INV3 | exact (PBT3 _ (PBT2 _ PBK1)) | | exact FS1 | exact FRM1].
apply BOK_set_x; [apply Z.le_refl | exact (BOK_drop _ _ _ _ _ _ BK1)].
-
intros m2 x1_2 gp2 t0_2 t1_2 t2_2 a1_2 a2_2 a3_2 a4_2 a5_2 a6_2 a7_2 s3_2 s4_2 s5_2 s6_2 s7_2 s8_2 s9_2 s11_2 t3_2 t4_2 t5_2 t6_2 INV2.
eapply (Kerrp m2 md1 A1 B1 pbs1 errv1 pj1); [exact INV2 | exact FS1 | exact FRM1].
Qed.
End PeSNullB.
End RC__1.
