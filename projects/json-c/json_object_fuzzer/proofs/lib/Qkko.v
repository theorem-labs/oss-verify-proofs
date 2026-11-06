(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup Lib.GwApply QWxq_c1 QRjH QHnV QCcH QfLs Q0Ek Qtgi QjDH Qsw7 QJjn QRUw QkMG QG8z Qdyh Q7UD Qhd4 Qwm6 QlKV QsKa Qiiq Q4v2 Q1Ey Ql4f Q1Y6 QrQv QEUF QW22 QdGy Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QJjn QRUw.Mq0 QRUw QkMG. Import QG8z Qdyh.Mq0 Qdyh.Mq3 Qdyh.Mq4.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa QsKa.Mq4 Qiiq.Mq0 QsKa.Mq6 Q4v2.Mq0 QlKV.Mq5 Q1Ey Ql4f.Mq1 Q1Y6.Mq2 QsKa.Mq8 QrQv.Mq2 QEUF QW22.Mq3 QdGy.Mq2.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section PeSPushA.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_outside : forall m m' W, GA m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= hl_img_lo A4H \/ hl_img_hi A4H <= fst iv) W -> GA m'.
Hypothesis GA_pres : forall LB SP m m', heap_pres A4H LB SP m m' -> GA m -> GA m'.
Hypothesis MAPP : memappend_A_stmt2 HIx.
Hypothesis PUT : put_stmt_A HIx.

Ltac pe_openA STC INV :=
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR); pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk);
destruct INV as [CORE REST];
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR);
pose proof REST as (HP & LV & OBJ & ST & ERR & STR & PLEN & SBin & HPR & MDV & G & BUD).

Ltac reopen_push INVx TS1 ts0 PF q LB0 tk mxd depth bse Hbse mX :=
pose proof INVx as [CORE2 REST2];
destruct CORE2 as (_ & _ & _ & _ & TOK & _ & _ & TSK & FR);
pose proof REST2 as (HP & _); clear REST2;
unfold TS1, ts_push, ts0 in TOK, TSK; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_tk pf_mxd pf_fl] in TOK, TSK;
unfold tok_cells_g in TOK; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK;
unfold pe_frameA in FR; destruct FR as (SLOTS & _ & _ & _ & _); unfold pe_slotsA in SLOTS; cbn zeta in SLOTS;
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in SLOTS;
assert (INtk : In (tk, 72) (pe_blocksA PF q LB0 TS1)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity);
assert (INq : In (q, 32 * mxd) (pe_blocksA PF q LB0 TS1)) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity);
pose proof (tok_shadowA HIx _ _ _ _ _ _ _ _ HP INtk) as SHT;
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI;
pose proof (wmono_refl asegs mX) as WM;
pose proof (TSK (S depth) _ ltac:(apply nth_error_lupd_eq; rewrite lupd_length; lia)) as Ln;
replace (q + 32 * Z.of_nat (S depth)) with (bse + 32) in Ln by lia; unfold srec_cells in Ln; cbn [tl_st tl_ss tl_cur tl_name] in Ln;
pose proof (stack_shadowA HIx _ _ _ _ _ _ _ q mxd (Z.of_nat depth + 1) 2 HP INq ltac:(lia) ltac:(lia)) as SHN2;
pose proof (stack_shadowA HIx _ _ _ _ _ _ _ q mxd (Z.of_nat depth + 1) 3 HP INq ltac:(lia) ltac:(lia)) as SHN3;
replace (q / 8 + 4 * (Z.of_nat depth + 1) + 2 + A_SB) with (bse / 8 + 2147450886) in SHN2 by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia);
replace (q / 8 + 4 * (Z.of_nat depth + 1) + 3 + A_SB) with (bse / 8 + 2147450887) in SHN3 by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia);
pose proof (munch_refl [(q + 32 * Z.of_nat (S depth), q + 32 * Z.of_nat (S depth) + 32)] mX) as MU;
unfold shA in *; a4l; unfold SB2, SB4, SB7, SB8 in *;
clear TSK INtk INq.

Ltac shq_facts HP INq INtk q mxd tk dz j SH SEPq SEPt :=
pose proof (stack_shadowA HIx _ _ _ _ _ _ _ q mxd dz j HP INq ltac:(lia) ltac:(lia)) as SH;
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ q (32 * mxd) (4 * dz + j) q (32 * mxd) HP INq ltac:(lia) (in_or_app _ _ _ (or_introl INq))) as (_ & SEPq & _);
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ q (32 * mxd) (4 * dz + j) tk 72 HP INq ltac:(lia) (in_or_app _ _ _ (or_introl INtk))) as (_ & SEPt & _);
cbn [hl_sb A4L] in SEPq, SEPt.

Lemma seg_push_arr_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP : Z) (nB : nat)
(gp t0 t1 t2 a1 a3 a4 a5 a6 a7 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv -> PBOK m ts kP -> BOK pf pa ts B (S (Z.to_nat 512 + nB)) ->
nth_error (t_levels ts) (t_depth ts) = Some l -> (tl_st l = ST_array \/ tl_st l = ST_array_after_sep) ->
(S (t_depth ts) < Z.to_nat (pf_mxd pf))%nat ->

(forall m' md' A' B' errv' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' F' fc',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B'
(ts_push ts (TL ST_array_add (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) cb nb pj sv errv' ->
PBOK m' (ts_push ts (TL ST_array_add (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) kP ->
BOK pf pa (ts_push ts (TL ST_array_add (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) B' nB ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msA asegs pf pa APE_REDO (t_co ts) gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5'
(Z_to_bv 64 (pf_tk pf + 56)) (Z_to_bv 64 (pa_F pa + 64)) F' fc' m')) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa 0x936cc (t_co ts) gp t0 t1 t2
(Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) a1
(Z_to_bv 64 (q / 8 + 4 * Z.of_nat (t_depth ts) + A_SB)) a3 a4 a5 a6 a7
(Z_to_bv 64 (Z.of_nat (t_depth ts))) (Z_to_bv 64 q) (Z_to_bv 64 (pa_F pa + 64)) F fc m).
Proof.
intros until fc. intros STC BSL INV PBK BK Hl Hst Hd1 Kredo. pose proof INV as INV0. pe_openA STC INV.
assert (Hd1' : (S (t_depth ts) < length (t_levels ts))%nat) by (rewrite LEN32; exact Hd1).
destruct (nth_error (t_levels ts) (S (t_depth ts))) as [l1|] eqn:Hl1; [| apply nth_error_None in Hl1; lia].
pose proof (PE_INV_A_next_clean HIx GA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ l1 INV0 Hl1) as Hcl1.
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
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs m) as WM.
pose proof (LV depth l Hl) as LVd. pose proof LVd as (ST26 & SS26 & _ & Md).
rewrite Nat.ltb_irrefl, Nat.eqb_refl in Md. destruct Md as (c0 & hn0 & Hmode & CLS0 & NM0).
destruct (lvl_mode_array _ _ _ _ Hst SS26 Hmode) as (-> & -> & SSnf).
assert (Eobjbs : objbs = []).
{ unfold cur_st in OBJ. cbn [t_levels t_depth t_objbs ts0] in OBJ. rewrite Hl in OBJ. destruct Hst as [E|E]; rewrite E in OBJ; exact OBJ. }
pose proof (TSK depth l Hl) as Ld. remember (q + 32 * Z.of_nat depth) as bse eqn:Hbse in Ld. unfold srec_cells in Ld.
pose proof (TSK (S depth) l1 Hl1) as Ln. replace (q + 32 * Z.of_nat (S depth)) with (bse + 32) in Ln by lia. unfold srec_cells in Ln.
assert (Ecl1 : tl_cur l1 = 0 /\ tl_name l1 = 0).
{ pose proof (LV (S depth) l1 Hl1) as (_ & _ & _ & M1).
replace (S depth <? depth)%nat with false in M1 by (symmetry; apply Nat.ltb_ge; lia).
replace (S depth =? depth)%nat with false in M1 by (symmetry; apply Nat.eqb_neq; lia). destruct M1 as (C1 & _ & _ & C4 & _). split; assumption. }
destruct Ecl1 as [Ec1 En1]. rewrite Ec1, En1 in Ln.
assert (HbseR : q <= bse /\ bse + 64 <= q + (32 * mxd)) by (subst bse; lia).
assert (Hb8 : bse mod 8 = 0) by (subst bse; clear - Hqal; Z.div_mod_to_equations; lia).

shq_facts HP INq INtk q mxd tk (Z.of_nat depth) 0 SHQ0 SEPQ0q SEPQ0t.
replace (q / 8 + 4 * Z.of_nat depth + 0 + A_SB) with (bse / 8 + 2147450880) in SHQ0 by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia).
shq_facts HP INq INtk q mxd tk (Z.of_nat depth + 1) 0 SHN0 SEPN0q SEPN0t.
replace (q / 8 + 4 * (Z.of_nat depth + 1) + 0 + A_SB) with (bse / 8 + 2147450884) in SHN0 by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia).
shq_facts HP INq INtk q mxd tk (Z.of_nat depth + 1) 2 SHN2 SEPN2q SEPN2t.
replace (q / 8 + 4 * (Z.of_nat depth + 1) + 2 + A_SB) with (bse / 8 + 2147450886) in SHN2 by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia).
shq_facts HP INq INtk q mxd tk (Z.of_nat depth + 1) 3 SHN3 SEPN3q SEPN3t.
replace (q / 8 + 4 * (Z.of_nat depth + 1) + 3 + A_SB) with (bse / 8 + 2147450887) in SHN3 by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia).
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 2 HP INtk ltac:(lia)) as SHT2.
replace (tk / 8 + 2 + A_SB) with (tk / 8 + 2147450882) in SHT2 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 2 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (_ & SEP2q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 2 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEP2t & _).
cbn [hl_sb A4L] in SEP2q, SEP2t.
pose proof (munch_refl [(tk, tk + 72); (bse, bse + 64)] m) as MU.
unfold APE_REDO, APE_JTAB in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
assert (EQx : q / 8 + 2147450880 + (4 * Z.of_nat depth + 0) = bse / 8 + 2147450880) by (rewrite Hbse, div8_add_mul32 by lia; lia). rewrite EQx in SEPQ0q, SEPQ0t. clear EQx.
assert (EQx : q / 8 + 2147450880 + (4 * (Z.of_nat depth + 1) + 0) = bse / 8 + 2147450884) by (rewrite Hbse, div8_add_mul32 by lia; lia). rewrite EQx in SEPN0q, SEPN0t. clear EQx.
assert (EQx : q / 8 + 2147450880 + (4 * (Z.of_nat depth + 1) + 2) = bse / 8 + 2147450886) by (rewrite Hbse, div8_add_mul32 by lia; lia). rewrite EQx in SEPN2q, SEPN2t. clear EQx.
assert (EQx : q / 8 + 2147450880 + (4 * (Z.of_nat depth + 1) + 3) = bse / 8 + 2147450887) by (rewrite Hbse, div8_add_mul32 by lia; lia). rewrite EQx in SEPN3q, SEPN3t. clear EQx.
assert (EQx : tk / 8 + 2147450880 + 2 = tk / 8 + 2147450882) by lia. rewrite EQx in SEP2q, SEP2t. clear EQx.

assert (cs_t_d : csep tk 72 bse (Z.of_nat 32)) by (unfold csep; clear - Hdtq HbseR; lia).
assert (cs_t_n : csep tk 72 (bse + 32) (Z.of_nat 32)) by (unfold csep; clear - Hdtq HbseR; lia).
assert (cs_d_t : csep bse 32 tk (Z.of_nat 72)) by (unfold csep; clear - Hdtq HbseR; lia).
assert (cs_n_t : csep (bse + 32) 32 tk (Z.of_nat 72)) by (unfold csep; clear - Hdtq HbseR; lia).
assert (cs_Q0_d : csep (bse / 8 + 2147450880) 1 bse (Z.of_nat 32)) by (unfold csep; clear - SEPQ0q HbseR; lia).
assert (cs_Q0_n : csep (bse / 8 + 2147450880) 1 (bse + 32) (Z.of_nat 32)) by (unfold csep; clear - SEPQ0q HbseR; lia).
assert (cs_Q0_t : csep (bse / 8 + 2147450880) 1 tk (Z.of_nat 72)) by (unfold csep; clear - SEPQ0t; lia).
assert (cs_N0_d : csep (bse / 8 + 2147450884) 1 bse (Z.of_nat 32)) by (unfold csep; clear - SEPN0q HbseR; lia).
assert (cs_N0_n : csep (bse / 8 + 2147450884) 1 (bse + 32) (Z.of_nat 32)) by (unfold csep; clear - SEPN0q HbseR; lia).
assert (cs_N0_t : csep (bse / 8 + 2147450884) 1 tk (Z.of_nat 72)) by (unfold csep; clear - SEPN0t; lia).
assert (cs_N2_d : csep (bse / 8 + 2147450886) 1 bse (Z.of_nat 32)) by (unfold csep; clear - SEPN2q HbseR; lia).
assert (cs_N2_n : csep (bse / 8 + 2147450886) 1 (bse + 32) (Z.of_nat 32)) by (unfold csep; clear - SEPN2q HbseR; lia).
assert (cs_N2_t : csep (bse / 8 + 2147450886) 1 tk (Z.of_nat 72)) by (unfold csep; clear - SEPN2t; lia).
assert (cs_N3_d : csep (bse / 8 + 2147450887) 1 bse (Z.of_nat 32)) by (unfold csep; clear - SEPN3q HbseR; lia).
assert (cs_N3_n : csep (bse / 8 + 2147450887) 1 (bse + 32) (Z.of_nat 32)) by (unfold csep; clear - SEPN3q HbseR; lia).
assert (cs_N3_t : csep (bse / 8 + 2147450887) 1 tk (Z.of_nat 72)) by (unfold csep; clear - SEPN3t; lia).
assert (cs_T2_d : csep (tk / 8 + 2147450882) 1 bse (Z.of_nat 32)) by (unfold csep; clear - SEP2q HbseR; lia).
assert (cs_T2_n : csep (tk / 8 + 2147450882) 1 (bse + 32) (Z.of_nat 32)) by (unfold csep; clear - SEP2q HbseR; lia).
assert (cs_T2_t : csep (tk / 8 + 2147450882) 1 tk (Z.of_nat 72)) by (unfold csep; clear - SEP2t; lia).
clear Hdtq SEPQ0q SEPQ0t SEPN0q SEPN0t SEPN2q SEPN2t SEPN3q SEPN3t SEP2q SEP2t.
stash Himg_t. stash Himg_q. stash INV0. stash Kredo. clear PB REST TSK HP LV OBJ HPR BUD GAP SAVED FSH FF STR ERR SBin.
reenterA asegs A4L HIx asegs_wx HP.
replace (q + 32 * Z.of_nat depth) with bse by lia.
replace (q / 8 + 4 * Z.of_nat depth) with (bse / 8) by (subst bse; rewrite div8_add_mul32 by lia; lia).
asan_rechkA.
step.
stepz.
asan_rechkA.
step.
norm_w32. replace (Z.of_nat depth + 1) with (Z.of_nat (S depth)) by lia.
stepz.
step.
rewrite (unsigned_lit (Z.of_nat (S depth))) by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32.
step.
replace (q + Z.of_nat (S depth) * 32) with (bse + 32) by lia.
asan_chkA.
stepz.
step.
asan_chkM 1.
step. step.
stepz.
asan_chkA.
step.
step.

set (lp := TL ST_array_add (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)) in *.
set (TS1 := ts_push ts0 lp) in *.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, Lc : rw_cells asegs mc bse _, Lnc : rw_cells asegs mc (bse + 32) _ |- _ =>
evt_done5; unstash INV0;
rewrite Hbse in MUc, Lc; replace (bse + 32) with (q + 32 * Z.of_nat (S depth)) in Lnc by lia;
destruct (PE_INV_A_push HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m mc md A B ts0
cb nb pj sv errv l ST_array_add STC INV0 Hl Hd1 Eobjbs MUc WMc MIc TOKc Lc Lnc
ltac:(intros c' hn' Hm'; rewrite Hmode in Hm'; injection Hm' as <- <-; left; repeat split)) as [INV1 PBK1];
fold lp in INV1, PBK1; fold TS1 in INV1, PBK1;
pose proof (BOK_push (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) ts0 B _ l ST_array_add Hl Hd1'
ltac:(intros l1' H1'; unfold ts0 in H1'; cbn [t_levels t_depth] in H1'; rewrite Hl1 in H1'; injection H1' as <-; exact Hcl1)
(lvl_closed_open_ss l SSnf) eq_refl BK) as BK1;
fold lp in BK1; fold TS1 in BK1;
eapply (pe_put_null_c HIx GA GA_pres PUT (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo mc md A B TS1
cb nb pj sv errv T (t_co ts0 + kP) _);
[exact STC | exact INV1 | exact (PBK1 _ PBK) | exact BK1 | rewrite unsigned_lit by lia; reflexivity |]
end end.
intros m2 md2 A2 B2 r w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 F2 fc2 INV2 PBK2 BK2 FS2 FRM2.
clear TOK SLOTS Ld Ln SHQ0 SHN0 SHN2 SHN3 SHT2 MU WM MI ST INV0 PBK BK INV1 PBK1 BK1 INtk INq.
cbn [pf_spf] in *. unfold A_TP in *.
reopen_push INV2 TS1 ts0 (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 tk mxd depth bse Hbse m2.
reenterA asegs A4L HIx asegs_wx HP.
step.
asan_rechkA.
clear SHT.
step. step.
replace (q + Z.of_nat (S depth) * 32) with (bse + 32) by lia.
step.
asan_chkA.
stepz.
step.
asan_chkA.
step.
step.

assert (Hln : nth_error (t_levels TS1) (t_depth TS1) = Some (TL ST_eatws ST_start 0 None [] 0 [])) by (exact (ts_push_cur ts0 lp Hd1')).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m2 mc, WMc : wmono asegs m2 mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, Lnc : rw_cells asegs mc (bse + 32) _ |- _ =>
evt_done5;
replace (bse + 32) with (q + 32 * Z.of_nat (S depth)) in Lnc by lia;
destruct (PE_INV_A_idwrite HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m2 mc md2 A2 B2 TS1
cb nb pj sv errv _ STC INV2 Hln MUc WMc MIc TOKc Lnc) as [INV3 PBK3];
eapply (pe_free_null_c HIx GA GA_pres (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo mc md2 A2 B2 TS1
cb nb pj sv errv T (t_co ts0 + kP) nB);
[exact STC | exact BSL | exact INV3 | exact (PBK3 _ PBK2) | exact BK2 | rewrite unsigned_lit by lia; reflexivity |]
end end.
intros m3 md3 A3 B3 r' v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 INV4 PBK4 BK4.
clear TOK SLOTS Ln SHN2 SHN3 MU WM MI INV2 PBK2 BK2 HP.
reopen_push INV4 TS1 ts0 (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 tk mxd depth bse Hbse m3.
reenterA asegs A4L HIx asegs_wx HP.
step.
asan_rechkA.
clear SHT.
step. step.
replace (q + Z.of_nat (S depth) * 32) with (bse + 32) by lia.
step. step. step.
sh_normO.
asan_rechkM 5.
stepz.
step.
step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m3 mc, WMc : wmono asegs m3 mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, Lnc : rw_cells asegs mc (bse + 32) _ |- _ =>
evt_done5;
replace (bse + 32) with (q + 32 * Z.of_nat (S depth)) in Lnc by lia;
destruct (PE_INV_A_idwrite HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m3 mc md3 A3 B3 TS1
cb nb pj sv errv _ STC INV4 Hln MUc WMc MIc TOKc Lnc) as [INV5 PBK5];
unstash Kredo; eapply (Kredo mc md3 A3 B3 errv); [exact INV5 | exact (PBK5 _ PBK4) | exact BK4 | exact FS2 | exact FRM2]
end end.
Qed.

Lemma seg_push_ov_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP : Z) (nB : nat)
(gp t0 t1 t2 a1 a3 a4 a5 a6 a7 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv -> PBOK m ts kP -> BOK pf pa ts B (S (Z.to_nat 512 + nB)) ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_ovalue ->
(S (t_depth ts) < Z.to_nat (pf_mxd pf))%nat ->

(forall m' md' A' B' errv' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' F' fc',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B'
(ts_push ts (TL ST_ovadd (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) cb nb pj sv errv' ->
PBOK m' (ts_push ts (TL ST_ovadd (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) kP ->
BOK pf pa (ts_push ts (TL ST_ovadd (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) B' nB ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msA asegs pf pa APE_REDO (t_co ts) gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5'
(Z_to_bv 64 (pf_tk pf + 56)) (Z_to_bv 64 (pa_F pa + 64)) F' fc' m')) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa 0x93818 (t_co ts) gp t0 t1 t2
(Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) a1
(Z_to_bv 64 (q / 8 + 4 * Z.of_nat (t_depth ts) + A_SB)) a3 a4 a5 a6 a7
(Z_to_bv 64 (Z.of_nat (t_depth ts))) (Z_to_bv 64 q) (Z_to_bv 64 (pa_F pa + 64)) F fc m).
Proof.
intros until fc. intros STC BSL INV PBK BK Hl Hst Hd1 Kredo. pose proof INV as INV0. pe_openA STC INV.
assert (Hd1' : (S (t_depth ts) < length (t_levels ts))%nat) by (rewrite LEN32; exact Hd1).
destruct (nth_error (t_levels ts) (S (t_depth ts))) as [l1|] eqn:Hl1; [| apply nth_error_None in Hl1; lia].
pose proof (PE_INV_A_next_clean HIx GA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ l1 INV0 Hl1) as Hcl1.
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
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs m) as WM.
pose proof (LV depth l Hl) as LVd. pose proof LVd as (ST26 & SS26 & _ & Md).
rewrite Nat.ltb_irrefl, Nat.eqb_refl in Md. destruct Md as (c0 & hn0 & Hmode & CLS0 & NM0).
pose proof Hmode as Hmode'. rewrite Hst in Hmode'. destruct (lvl_mode_ovalue _ _ _ SS26 Hmode') as (-> & -> & SSnf).
assert (Eobjbs : objbs = []).
{ unfold cur_st in OBJ. cbn [t_levels t_depth t_objbs ts0] in OBJ. rewrite Hl in OBJ. rewrite Hst in OBJ; exact OBJ. }
pose proof (TSK depth l Hl) as Ld. remember (q + 32 * Z.of_nat depth) as bse eqn:Hbse in Ld. unfold srec_cells in Ld.
pose proof (TSK (S depth) l1 Hl1) as Ln. replace (q + 32 * Z.of_nat (S depth)) with (bse + 32) in Ln by lia. unfold srec_cells in Ln.
assert (Ecl1 : tl_cur l1 = 0 /\ tl_name l1 = 0).
{ pose proof (LV (S depth) l1 Hl1) as (_ & _ & _ & M1).
replace (S depth <? depth)%nat with false in M1 by (symmetry; apply Nat.ltb_ge; lia).
replace (S depth =? depth)%nat with false in M1 by (symmetry; apply Nat.eqb_neq; lia). destruct M1 as (C1 & _ & _ & C4 & _). split; assumption. }
destruct Ecl1 as [Ec1 En1]. rewrite Ec1, En1 in Ln.
assert (HbseR : q <= bse /\ bse + 64 <= q + (32 * mxd)) by (subst bse; lia).
assert (Hb8 : bse mod 8 = 0) by (subst bse; clear - Hqal; Z.div_mod_to_equations; lia).

shq_facts HP INq INtk q mxd tk (Z.of_nat depth) 0 SHQ0 SEPQ0q SEPQ0t.
replace (q / 8 + 4 * Z.of_nat depth + 0 + A_SB) with (bse / 8 + 2147450880) in SHQ0 by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia).
shq_facts HP INq INtk q mxd tk (Z.of_nat depth + 1) 0 SHN0 SEPN0q SEPN0t.
replace (q / 8 + 4 * (Z.of_nat depth + 1) + 0 + A_SB) with (bse / 8 + 2147450884) in SHN0 by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia).
shq_facts HP INq INtk q mxd tk (Z.of_nat depth + 1) 2 SHN2 SEPN2q SEPN2t.
replace (q / 8 + 4 * (Z.of_nat depth + 1) + 2 + A_SB) with (bse / 8 + 2147450886) in SHN2 by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia).
shq_facts HP INq INtk q mxd tk (Z.of_nat depth + 1) 3 SHN3 SEPN3q SEPN3t.
replace (q / 8 + 4 * (Z.of_nat depth + 1) + 3 + A_SB) with (bse / 8 + 2147450887) in SHN3 by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia).
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 2 HP INtk ltac:(lia)) as SHT2.
replace (tk / 8 + 2 + A_SB) with (tk / 8 + 2147450882) in SHT2 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 2 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (_ & SEP2q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 2 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEP2t & _).
cbn [hl_sb A4L] in SEP2q, SEP2t.
pose proof (munch_refl [(tk, tk + 72); (bse, bse + 64)] m) as MU.
unfold APE_REDO, APE_JTAB in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
assert (EQx : q / 8 + 2147450880 + (4 * Z.of_nat depth + 0) = bse / 8 + 2147450880) by (rewrite Hbse, div8_add_mul32 by lia; lia). rewrite EQx in SEPQ0q, SEPQ0t. clear EQx.
assert (EQx : q / 8 + 2147450880 + (4 * (Z.of_nat depth + 1) + 0) = bse / 8 + 2147450884) by (rewrite Hbse, div8_add_mul32 by lia; lia). rewrite EQx in SEPN0q, SEPN0t. clear EQx.
assert (EQx : q / 8 + 2147450880 + (4 * (Z.of_nat depth + 1) + 2) = bse / 8 + 2147450886) by (rewrite Hbse, div8_add_mul32 by lia; lia). rewrite EQx in SEPN2q, SEPN2t. clear EQx.
assert (EQx : q / 8 + 2147450880 + (4 * (Z.of_nat depth + 1) + 3) = bse / 8 + 2147450887) by (rewrite Hbse, div8_add_mul32 by lia; lia). rewrite EQx in SEPN3q, SEPN3t. clear EQx.
assert (EQx : tk / 8 + 2147450880 + 2 = tk / 8 + 2147450882) by lia. rewrite EQx in SEP2q, SEP2t. clear EQx.

assert (cs_t_d : csep tk 72 bse (Z.of_nat 32)) by (unfold csep; clear - Hdtq HbseR; lia).
assert (cs_t_n : csep tk 72 (bse + 32) (Z.of_nat 32)) by (unfold csep; clear - Hdtq HbseR; lia).
assert (cs_d_t : csep bse 32 tk (Z.of_nat 72)) by (unfold csep; clear - Hdtq HbseR; lia).
assert (cs_n_t : csep (bse + 32) 32 tk (Z.of_nat 72)) by (unfold csep; clear - Hdtq HbseR; lia).
assert (cs_Q0_d : csep (bse / 8 + 2147450880) 1 bse (Z.of_nat 32)) by (unfold csep; clear - SEPQ0q HbseR; lia).
assert (cs_Q0_n : csep (bse / 8 + 2147450880) 1 (bse + 32) (Z.of_nat 32)) by (unfold csep; clear - SEPQ0q HbseR; lia).
assert (cs_Q0_t : csep (bse / 8 + 2147450880) 1 tk (Z.of_nat 72)) by (unfold csep; clear - SEPQ0t; lia).
assert (cs_N0_d : csep (bse / 8 + 2147450884) 1 bse (Z.of_nat 32)) by (unfold csep; clear - SEPN0q HbseR; lia).
assert (cs_N0_n : csep (bse / 8 + 2147450884) 1 (bse + 32) (Z.of_nat 32)) by (unfold csep; clear - SEPN0q HbseR; lia).
assert (cs_N0_t : csep (bse / 8 + 2147450884) 1 tk (Z.of_nat 72)) by (unfold csep; clear - SEPN0t; lia).
assert (cs_N2_d : csep (bse / 8 + 2147450886) 1 bse (Z.of_nat 32)) by (unfold csep; clear - SEPN2q HbseR; lia).
assert (cs_N2_n : csep (bse / 8 + 2147450886) 1 (bse + 32) (Z.of_nat 32)) by (unfold csep; clear - SEPN2q HbseR; lia).
assert (cs_N2_t : csep (bse / 8 + 2147450886) 1 tk (Z.of_nat 72)) by (unfold csep; clear - SEPN2t; lia).
assert (cs_N3_d : csep (bse / 8 + 2147450887) 1 bse (Z.of_nat 32)) by (unfold csep; clear - SEPN3q HbseR; lia).
assert (cs_N3_n : csep (bse / 8 + 2147450887) 1 (bse + 32) (Z.of_nat 32)) by (unfold csep; clear - SEPN3q HbseR; lia).
assert (cs_N3_t : csep (bse / 8 + 2147450887) 1 tk (Z.of_nat 72)) by (unfold csep; clear - SEPN3t; lia).
assert (cs_T2_d : csep (tk / 8 + 2147450882) 1 bse (Z.of_nat 32)) by (unfold csep; clear - SEP2q HbseR; lia).
assert (cs_T2_n : csep (tk / 8 + 2147450882) 1 (bse + 32) (Z.of_nat 32)) by (unfold csep; clear - SEP2q HbseR; lia).
assert (cs_T2_t : csep (tk / 8 + 2147450882) 1 tk (Z.of_nat 72)) by (unfold csep; clear - SEP2t; lia).
clear Hdtq SEPQ0q SEPQ0t SEPN0q SEPN0t SEPN2q SEPN2t SEPN3q SEPN3t SEP2q SEP2t.
stash Himg_t. stash Himg_q. stash INV0. stash Kredo. clear PB REST TSK HP LV OBJ HPR BUD GAP SAVED FSH FF STR ERR SBin.
reenterA asegs A4L HIx asegs_wx HP.
replace (q + 32 * Z.of_nat depth) with bse by lia.
replace (q / 8 + 4 * Z.of_nat depth) with (bse / 8) by (subst bse; rewrite div8_add_mul32 by lia; lia).
asan_rechkA.
step.
stepz.
asan_rechkA.
step.
norm_w32. replace (Z.of_nat depth + 1) with (Z.of_nat (S depth)) by lia.
stepz.
step.
rewrite (unsigned_lit (Z.of_nat (S depth))) by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32.
step.
replace (q + Z.of_nat (S depth) * 32) with (bse + 32) by lia.
asan_chkA.
stepz.
step.
asan_chkM 1.
step. step.
stepz.
asan_chkA.
step.
step.

set (lp := TL ST_ovadd (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)) in *.
set (TS1 := ts_push ts0 lp) in *.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, Lc : rw_cells asegs mc bse _, Lnc : rw_cells asegs mc (bse + 32) _ |- _ =>
evt_done5; unstash INV0;
rewrite Hbse in MUc, Lc; replace (bse + 32) with (q + 32 * Z.of_nat (S depth)) in Lnc by lia;
destruct (PE_INV_A_push HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m mc md A B ts0
cb nb pj sv errv l ST_ovadd STC INV0 Hl Hd1 Eobjbs MUc WMc MIc TOKc Lc Lnc
ltac:(intros c' hn' Hm'; rewrite Hmode in Hm'; injection Hm' as <- <-; right; repeat split)) as [INV1 PBK1];
fold lp in INV1, PBK1; fold TS1 in INV1, PBK1;
pose proof (BOK_push (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) ts0 B _ l ST_ovadd Hl Hd1'
ltac:(intros l1' H1'; unfold ts0 in H1'; cbn [t_levels t_depth] in H1'; rewrite Hl1 in H1'; injection H1' as <-; exact Hcl1)
(lvl_closed_open_ss l SSnf) eq_refl BK) as BK1;
fold lp in BK1; fold TS1 in BK1;
eapply (pe_put_null_c HIx GA GA_pres PUT (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo mc md A B TS1
cb nb pj sv errv T (t_co ts0 + kP) _);
[exact STC | exact INV1 | exact (PBK1 _ PBK) | exact BK1 | rewrite unsigned_lit by lia; reflexivity |]
end end.
intros m2 md2 A2 B2 r w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 F2 fc2 INV2 PBK2 BK2 FS2 FRM2.
clear TOK SLOTS Ld Ln SHQ0 SHN0 SHN2 SHN3 SHT2 MU WM MI ST INV0 PBK BK INV1 PBK1 BK1 INtk INq.
cbn [pf_spf] in *. unfold A_TP in *.
reopen_push INV2 TS1 ts0 (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 tk mxd depth bse Hbse m2.
reenterA asegs A4L HIx asegs_wx HP.
step.
asan_rechkA.
clear SHT.
step. step.
replace (q + Z.of_nat (S depth) * 32) with (bse + 32) by lia.
step.
asan_chkA.
stepz.
step.
asan_chkA.
step.
step.

assert (Hln : nth_error (t_levels TS1) (t_depth TS1) = Some (TL ST_eatws ST_start 0 None [] 0 [])) by (exact (ts_push_cur ts0 lp Hd1')).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m2 mc, WMc : wmono asegs m2 mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, Lnc : rw_cells asegs mc (bse + 32) _ |- _ =>
evt_done5;
replace (bse + 32) with (q + 32 * Z.of_nat (S depth)) in Lnc by lia;
destruct (PE_INV_A_idwrite HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m2 mc md2 A2 B2 TS1
cb nb pj sv errv _ STC INV2 Hln MUc WMc MIc TOKc Lnc) as [INV3 PBK3];
eapply (pe_free_null_c HIx GA GA_pres (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo mc md2 A2 B2 TS1
cb nb pj sv errv T (t_co ts0 + kP) nB);
[exact STC | exact BSL | exact INV3 | exact (PBK3 _ PBK2) | exact BK2 | rewrite unsigned_lit by lia; reflexivity |]
end end.
intros m3 md3 A3 B3 r' v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 INV4 PBK4 BK4.
clear TOK SLOTS Ln SHN2 SHN3 MU WM MI INV2 PBK2 BK2 HP.
reopen_push INV4 TS1 ts0 (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 tk mxd depth bse Hbse m3.
reenterA asegs A4L HIx asegs_wx HP.
step.
asan_rechkA.
clear SHT.
step. step.
replace (q + Z.of_nat (S depth) * 32) with (bse + 32) by lia.
step. step. step.
sh_normO.
asan_rechkM 5.
stepz.
step.
step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m3 mc, WMc : wmono asegs m3 mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, Lnc : rw_cells asegs mc (bse + 32) _ |- _ =>
evt_done5;
replace (bse + 32) with (q + 32 * Z.of_nat (S depth)) in Lnc by lia;
destruct (PE_INV_A_idwrite HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m3 mc md3 A3 B3 TS1
cb nb pj sv errv _ STC INV4 Hln MUc WMc MIc TOKc Lnc) as [INV5 PBK5];
unstash Kredo; eapply (Kredo mc md3 A3 B3 errv); [exact INV5 | exact (PBK5 _ PBK4) | exact BK4 | exact FS2 | exact FRM2]
end end.
Qed.
End PeSPushA.
End RC__1.
End Mq0.
From Stdlib Require Permutation.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QIsM Qa8x QYZ0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QJjn QRUw.Mq0 QRUw QkMG. Import QG8z Qdyh.Mq0 Qdyh.Mq3 Qdyh.Mq4 QIsM.Mq2 Qa8x.Mq2.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa QsKa.Mq4 Qiiq.Mq0 QsKa.Mq6 Q4v2.Mq0 QlKV.Mq5 Q1Ey Ql4f.Mq1 Q1Y6.Mq2 QsKa.Mq8 QrQv.Mq2 QEUF QW22.Mq3 QdGy.Mq2 QYZ0.Mq3.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Lemma lvl_mode_start2 : forall ss c hn, 0 <= ss <= 26 -> lvl_mode ST_start ss = Some (c, hn) -> c = CNone /\ hn = false /\ ss = ST_start.
Proof.
intros ss c hn R H. assert (CASES : exists k : nat, (k <= 26)%nat /\ ss = Z.of_nat k) by (exists (Z.to_nat ss); split; lia).
destruct CASES as (k & Hk & ->). clear R.
do 27 (destruct k as [|k]; [vm_compute in H; first [discriminate H | injection H as <- <-; split; [reflexivity | split; reflexivity]] |]); exfalso; lia.
Qed.

Lemma pbufc_agreeA : forall BS m m' pbs pb pre, pbufc asegs m pbs pb pre -> agree_on asegs BS m m' -> incl pbs BS -> pbufc asegs m' pbs pb pre.
Proof.
intros BS m m' pbs pb pre (buf & bpos & size & post & E & L & C) AG Hi. exists buf, bpos, size, post.
split; [exact E|]. split; [exact L|].
eapply (pbuf_core_agree asegs); [exact C | exact AG | apply Hi; rewrite E; left; reflexivity | apply Hi; rewrite E; right; left; reflexivity].
Qed.

Section PeSStartTA.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_outside : forall m m' W, GA m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= hl_img_lo A4H \/ hl_img_hi A4H <= fst iv) W -> GA m'.
Hypothesis GA_pres : forall LB SP m m', heap_pres A4H LB SP m m' -> GA m -> GA m'.

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

Lemma start_num_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet)
(gp t0 t1 t2 a1 a3 a4 a5 a6 a7 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_start ->

(forall m' a0' a1' a2' a3' a4',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md A B
(ts_set_x (ts_lvl ts (TL ST_number (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) (t_co ts) (TS (Z_to_bv 64 0) (ts_stpos (t_x ts)) (ts_choff (t_x ts)) (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))) cb nb pj sv errv ->
PBOK m' (ts_set_x (ts_lvl ts (TL ST_number (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) (t_co ts) (TS (Z_to_bv 64 0) (ts_stpos (t_x ts)) (ts_choff (t_x ts)) (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))) 0 ->
pbufc asegs m' (t_pbs ts) (t_pb ts) [] ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa APE_REDO (t_co ts) gp t0 t1 t2 a0' a1' a2' a3' a4' a5 a6 a7
(Z_to_bv 64 (Z.of_nat (t_depth ts))) (Z_to_bv 64 (pf_tk pf + 56)) (Z_to_bv 64 (pa_F pa + 64)) F fc m')) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa 0x9426c (t_co ts) gp t0 t1 t2
(Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) a1
(Z_to_bv 64 (q / 8 + 4 * Z.of_nat (t_depth ts) + A_SB)) a3 a4 a5 a6 a7
(Z_to_bv 64 (Z.of_nat (t_depth ts))) (Z_to_bv 64 q) (Z_to_bv 64 (pa_F pa + 64)) F fc m).
Proof.
intros until fc. intros STC INV Hl Hst Kredo. pose proof INV as INV0. pe_openA STC INV.
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
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 1 HP INtk ltac:(lia)) as SHT1.
replace (tk / 8 + 1 + A_SB) with (tk / 8 + 2147450881) in SHT1 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 1 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT1c & SEPT1q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 1 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT1t & _).
cbn [hl_sb A4L] in SEPT1c, SEPT1q, SEPT1t. assert (EQx : tk / 8 + A_SB + 1 = tk / 8 + 2147450881) by (unfold A_SB; lia). rewrite EQx in SEPT1c, SEPT1q, SEPT1t. clear EQx.
unfold APE_BREAK, APE_REDO, APE_OUT, APE_ERRMEM, APE_ERRST, APE_JTAB in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
assert (cs_tk_L : csep tk 72 bse (Z.of_nat 32)) by (unfold csep; clear - Hdtq HbseR; lia).
assert (cs_L_tk : csep bse 32 tk (Z.of_nat 72)) by (unfold csep; clear - Hdtq HbseR; lia).
assert (cs_T1_L : csep (tk / 8 + 2147450881) 1 bse (Z.of_nat 32)) by (unfold csep; clear - SEPT1q HbseR; lia).
clear Hdtq SEPT1q SEPT1t SEPT1c.
destruct (lvl_mode_start2 _ _ _ SS26 ltac:(rewrite <- Hst; exact Hmode)) as (Ec0 & Ehn0 & Ess). subst c0 hn0.
stash Himg_t. stash Himg_q. stash Kredo. clear PB REST TSK LV OBJ HPR BUD GAP SAVED FSH FF STR ERR SBin SHT SHQ4.
reenterA asegs A4L HIx asegs_wx HP.
replace (q + 32 * Z.of_nat depth) with bse by lia.
asan_rechkA.
clear SHQ.
step.
stepz.
step.
asan_chkA.
step. step.

set (l1 := TL ST_number (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, Lc : rw_cells asegs mc bse _ |- _ =>
pose proof MUc as MUc'; pose proof Lc as Lc'; rewrite Hbse in MUc', Lc';
destruct (PE_INV_A_lvl_write HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m mc md A B ts0
cb nb pj sv errv l ST_number (tl_ss l) CNone false CNone STC INV0 Hl MUc' WMc MIc TOKc Lc' Hmode
ltac:(rewrite Ess; vm_compute; reflexivity) ltac:(unfold ST_number; lia) SS26 (or_introl eq_refl)
ltac:(rewrite Hst; vm_compute; reflexivity)) as [INV1 _]; clear MUc' Lc'
end end.
set (ts1 := ts_lvl ts0 l1) in *.
eapply (pe_pbreset HIx GA GA_pres (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo _ md A B ts1 cb nb pj sv errv);
[exact STC | exact INV1 | rewrite unsigned_lit by lia; reflexivity |].
intros mr2 a1' a2' a3' a4' INV2 PBK2 PBC2.
cbn [pf_spf] in *. unfold A_TP in *.
repeat match goal with H : rw_cells asegs _ _ _ |- _ => clear H | H : ro_cells asegs _ _ _ |- _ => clear H | H : munch _ _ _ |- _ => clear H | H : wmono asegs _ _ |- _ => clear H | H : mem_inv asegs _ |- _ => clear H end.
clear Htal Htlo Hthi Hqal Hqlo Hqhi Hqtk INtk INq INV0 INV1 HP cs_tk_L cs_L_tk cs_T1_L.
assert (Hl1 : nth_error (t_levels ts1) (t_depth ts1) = Some l1) by (unfold ts1, ts_lvl, ts0; cbn [t_levels t_depth]; apply nth_error_lupd_eq; apply nth_error_Some; rewrite Hl; discriminate).
reopen_inv INV2 ts1 ts0 (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 tk mxd depth l1 Hl1 bse Hbse mr2.
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t2.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 3 HP INtk ltac:(lia)) as SHT3.
replace (tk / 8 + 3 + A_SB) with (tk / 8 + 2147450883) in SHT3 by (unfold A_SB; lia).
pose proof (munch_refl [(tk, tk + 72)] mr2) as MU.
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
stash Himg_t2. clear Ld.
lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) => replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
step.
asan_chkM 1.
clear SHT3.
stepz.
do 5 step.
step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ mr2 mc, WMc : wmono asegs mr2 mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _ |- _ =>
evt_done5;
destruct (PE_INV_A_tokw1 HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo mr2 mc md A B ts1
cb nb pj sv errv co (TS (Z_to_bv 64 0) stpos (Z_to_bv 64 co) err ucs high quote) STC INV2 MUc WMc MIc TOKc ltac:(cbn [pf_len]; lia) eq_refl) as [INV3 PBT3];
assert (AGp : agree_on asegs (t_pbs ts1) mr2 mc);
[ eapply (agree_wtqA HIx) with (ts := ts1); [exact STC | exact (proj1 (proj2 INV2)) | exact MUc | exact WMc
| apply Forall_cons; [left; left; cbn [fst snd pf_tk]; lia | apply Forall_nil] |];
intros a n Hin; assert (HinL : In (a, n) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts1 ++ LM)) by (unfold pe_blocksA, tstate_blocks; apply in_or_app; left; apply in_or_app; left; apply in_or_app; left; exact Hin);
split; [exact HinL|];
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ (proj1 (proj2 INV2))) as ND; unfold pe_blocksA in ND; rewrite <- app_assoc in ND; split;
[ intros ->; refine (nodup_app_ne _ _ _ _ _ _ ND _ _ eq_refl); [unfold tstate_blocks; apply in_or_app; left; exact Hin | left; reflexivity]
| intros ->; refine (nodup_app_ne _ _ _ _ _ _ ND _ _ eq_refl); [unfold tstate_blocks; apply in_or_app; left; exact Hin | right; left; reflexivity] ] |];
unstash Kredo; eapply (Kredo mc); [exact INV3 | exact (PBT3 _ PBK2) | exact (pbufc_agreeA _ _ _ _ _ _ PBC2 AGp (incl_refl _))]
end end.
Qed.

Lemma start_bool_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet)
(gp t0 t1 t2 a1 a3 a4 a5 a6 a7 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_start ->

(forall m' a0' a1' a2' a3' a4',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md A B
(ts_set_x (ts_lvl ts (TL ST_boolean (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) (t_co ts) (TS (ts_isd (t_x ts)) (Z_to_bv 64 0) (ts_choff (t_x ts)) (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))) cb nb pj sv errv ->
PBOK m' (ts_set_x (ts_lvl ts (TL ST_boolean (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) (t_co ts) (TS (ts_isd (t_x ts)) (Z_to_bv 64 0) (ts_choff (t_x ts)) (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))) 0 ->
pbufc asegs m' (t_pbs ts) (t_pb ts) [] ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa APE_REDO (t_co ts) gp t0 t1 t2 a0' a1' a2' a3' a4' a5 a6 a7
(Z_to_bv 64 (Z.of_nat (t_depth ts))) (Z_to_bv 64 (pf_tk pf + 56)) (Z_to_bv 64 (pa_F pa + 64)) F fc m')) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa 0x94b78 (t_co ts) gp t0 t1 t2
(Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) a1
(Z_to_bv 64 (q / 8 + 4 * Z.of_nat (t_depth ts) + A_SB)) a3 a4 a5 a6 a7
(Z_to_bv 64 (Z.of_nat (t_depth ts))) (Z_to_bv 64 q) (Z_to_bv 64 (pa_F pa + 64)) F fc m).
Proof.
intros until fc. intros STC INV Hl Hst Kredo. pose proof INV as INV0. pe_openA STC INV.
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
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 1 HP INtk ltac:(lia)) as SHT1.
replace (tk / 8 + 1 + A_SB) with (tk / 8 + 2147450881) in SHT1 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 1 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT1c & SEPT1q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 1 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT1t & _).
cbn [hl_sb A4L] in SEPT1c, SEPT1q, SEPT1t. assert (EQx : tk / 8 + A_SB + 1 = tk / 8 + 2147450881) by (unfold A_SB; lia). rewrite EQx in SEPT1c, SEPT1q, SEPT1t. clear EQx.
unfold APE_BREAK, APE_REDO, APE_OUT, APE_ERRMEM, APE_ERRST, APE_JTAB in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
assert (cs_tk_L : csep tk 72 bse (Z.of_nat 32)) by (unfold csep; clear - Hdtq HbseR; lia).
assert (cs_L_tk : csep bse 32 tk (Z.of_nat 72)) by (unfold csep; clear - Hdtq HbseR; lia).
assert (cs_T1_L : csep (tk / 8 + 2147450881) 1 bse (Z.of_nat 32)) by (unfold csep; clear - SEPT1q HbseR; lia).
clear Hdtq SEPT1q SEPT1t SEPT1c.
destruct (lvl_mode_start2 _ _ _ SS26 ltac:(rewrite <- Hst; exact Hmode)) as (Ec0 & Ehn0 & Ess). subst c0 hn0.
stash Himg_t. stash Himg_q. stash Kredo. clear PB REST TSK LV OBJ HPR BUD GAP SAVED FSH FF STR ERR SBin SHT SHQ4.
reenterA asegs A4L HIx asegs_wx HP.
replace (q + 32 * Z.of_nat depth) with bse by lia.
asan_rechkA.
clear SHQ.
step.
stepz.
step.
asan_chkA.
step. step.

set (l1 := TL ST_boolean (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, Lc : rw_cells asegs mc bse _ |- _ =>
pose proof MUc as MUc'; pose proof Lc as Lc'; rewrite Hbse in MUc', Lc';
destruct (PE_INV_A_lvl_write HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m mc md A B ts0
cb nb pj sv errv l ST_boolean (tl_ss l) CNone false CNone STC INV0 Hl MUc' WMc MIc TOKc Lc' Hmode
ltac:(rewrite Ess; vm_compute; reflexivity) ltac:(unfold ST_boolean; lia) SS26 (or_introl eq_refl)
ltac:(rewrite Hst; vm_compute; reflexivity)) as [INV1 _]; clear MUc' Lc'
end end.
set (ts1 := ts_lvl ts0 l1) in *.
eapply (pe_pbreset HIx GA GA_pres (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo _ md A B ts1 cb nb pj sv errv);
[exact STC | exact INV1 | rewrite unsigned_lit by lia; reflexivity |].
intros mr2 a1' a2' a3' a4' INV2 PBK2 PBC2.
cbn [pf_spf] in *. unfold A_TP in *.
repeat match goal with H : rw_cells asegs _ _ _ |- _ => clear H | H : ro_cells asegs _ _ _ |- _ => clear H | H : munch _ _ _ |- _ => clear H | H : wmono asegs _ _ |- _ => clear H | H : mem_inv asegs _ |- _ => clear H end.
clear Htal Htlo Hthi Hqal Hqlo Hqhi Hqtk INtk INq INV0 INV1 HP cs_tk_L cs_L_tk cs_T1_L.
assert (Hl1 : nth_error (t_levels ts1) (t_depth ts1) = Some l1) by (unfold ts1, ts_lvl, ts0; cbn [t_levels t_depth]; apply nth_error_lupd_eq; apply nth_error_Some; rewrite Hl; discriminate).
reopen_inv INV2 ts1 ts0 (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 tk mxd depth l1 Hl1 bse Hbse mr2.
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t2.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 3 HP INtk ltac:(lia)) as SHT3.
replace (tk / 8 + 3 + A_SB) with (tk / 8 + 2147450883) in SHT3 by (unfold A_SB; lia).
pose proof (munch_refl [(tk, tk + 72)] mr2) as MU.
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
stash Himg_t2. clear Ld.
lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) => replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
step.
asan_chkM 1.
clear SHT3.
stepz.
do 5 step.
step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ mr2 mc, WMc : wmono asegs mr2 mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _ |- _ =>
evt_done5;
destruct (PE_INV_A_tokw1 HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo mr2 mc md A B ts1
cb nb pj sv errv co (TS isd (Z_to_bv 64 0) (Z_to_bv 64 co) err ucs high quote) STC INV2 MUc WMc MIc TOKc ltac:(cbn [pf_len]; lia) eq_refl) as [INV3 PBT3];
assert (AGp : agree_on asegs (t_pbs ts1) mr2 mc);
[ eapply (agree_wtqA HIx) with (ts := ts1); [exact STC | exact (proj1 (proj2 INV2)) | exact MUc | exact WMc
| apply Forall_cons; [left; left; cbn [fst snd pf_tk]; lia | apply Forall_nil] |];
intros a n Hin; assert (HinL : In (a, n) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts1 ++ LM)) by (unfold pe_blocksA, tstate_blocks; apply in_or_app; left; apply in_or_app; left; apply in_or_app; left; exact Hin);
split; [exact HinL|];
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ (proj1 (proj2 INV2))) as ND; unfold pe_blocksA in ND; rewrite <- app_assoc in ND; split;
[ intros ->; refine (nodup_app_ne _ _ _ _ _ _ ND _ _ eq_refl); [unfold tstate_blocks; apply in_or_app; left; exact Hin | left; reflexivity]
| intros ->; refine (nodup_app_ne _ _ _ _ _ _ ND _ _ eq_refl); [unfold tstate_blocks; apply in_or_app; left; exact Hin | right; left; reflexivity] ] |];
unstash Kredo; eapply (Kredo mc); [exact INV3 | exact (PBT3 _ PBK2) | exact (pbufc_agreeA _ _ _ _ _ _ PBC2 AGp (incl_refl _))]
end end.
Qed.

Lemma start_null_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet)
(gp t0 t1 t2 a1 a3 a4 a5 a6 a7 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_start ->

(forall m' a0' a1' a2' a3' a4',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md A B
(ts_set_x (ts_lvl ts (TL ST_null (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) (t_co ts) (TS (ts_isd (t_x ts)) (Z_to_bv 64 0) (ts_choff (t_x ts)) (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))) cb nb pj sv errv ->
PBOK m' (ts_set_x (ts_lvl ts (TL ST_null (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) (t_co ts) (TS (ts_isd (t_x ts)) (Z_to_bv 64 0) (ts_choff (t_x ts)) (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))) 0 ->
pbufc asegs m' (t_pbs ts) (t_pb ts) [] ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa APE_REDO (t_co ts) gp t0 t1 t2 a0' a1' a2' a3' a4' a5 a6 a7
(Z_to_bv 64 (Z.of_nat (t_depth ts))) (Z_to_bv 64 (pf_tk pf + 56)) (Z_to_bv 64 (pa_F pa + 64)) F fc m')) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa 0x94f88 (t_co ts) gp t0 t1 t2
(Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) a1
(Z_to_bv 64 (q / 8 + 4 * Z.of_nat (t_depth ts) + A_SB)) a3 a4 a5 a6 a7
(Z_to_bv 64 (Z.of_nat (t_depth ts))) (Z_to_bv 64 q) (Z_to_bv 64 (pa_F pa + 64)) F fc m).
Proof.
intros until fc. intros STC INV Hl Hst Kredo. pose proof INV as INV0. pe_openA STC INV.
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
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 1 HP INtk ltac:(lia)) as SHT1.
replace (tk / 8 + 1 + A_SB) with (tk / 8 + 2147450881) in SHT1 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 1 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT1c & SEPT1q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 1 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT1t & _).
cbn [hl_sb A4L] in SEPT1c, SEPT1q, SEPT1t. assert (EQx : tk / 8 + A_SB + 1 = tk / 8 + 2147450881) by (unfold A_SB; lia). rewrite EQx in SEPT1c, SEPT1q, SEPT1t. clear EQx.
unfold APE_BREAK, APE_REDO, APE_OUT, APE_ERRMEM, APE_ERRST, APE_JTAB in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
assert (cs_tk_L : csep tk 72 bse (Z.of_nat 32)) by (unfold csep; clear - Hdtq HbseR; lia).
assert (cs_L_tk : csep bse 32 tk (Z.of_nat 72)) by (unfold csep; clear - Hdtq HbseR; lia).
assert (cs_T1_L : csep (tk / 8 + 2147450881) 1 bse (Z.of_nat 32)) by (unfold csep; clear - SEPT1q HbseR; lia).
clear Hdtq SEPT1q SEPT1t SEPT1c.
destruct (lvl_mode_start2 _ _ _ SS26 ltac:(rewrite <- Hst; exact Hmode)) as (Ec0 & Ehn0 & Ess). subst c0 hn0.
stash Himg_t. stash Himg_q. stash Kredo. clear PB REST TSK LV OBJ HPR BUD GAP SAVED FSH FF STR ERR SBin SHT SHQ4.
reenterA asegs A4L HIx asegs_wx HP.
replace (q + 32 * Z.of_nat depth) with bse by lia.
asan_rechkA.
clear SHQ.
step.
stepz.
step.
asan_chkA.
step. step.

set (l1 := TL ST_null (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, Lc : rw_cells asegs mc bse _ |- _ =>
pose proof MUc as MUc'; pose proof Lc as Lc'; rewrite Hbse in MUc', Lc';
destruct (PE_INV_A_lvl_write HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m mc md A B ts0
cb nb pj sv errv l ST_null (tl_ss l) CNone false CNone STC INV0 Hl MUc' WMc MIc TOKc Lc' Hmode
ltac:(rewrite Ess; vm_compute; reflexivity) ltac:(unfold ST_null; lia) SS26 (or_introl eq_refl)
ltac:(rewrite Hst; vm_compute; reflexivity)) as [INV1 _]; clear MUc' Lc'
end end.
set (ts1 := ts_lvl ts0 l1) in *.
eapply (pe_pbreset HIx GA GA_pres (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo _ md A B ts1 cb nb pj sv errv);
[exact STC | exact INV1 | rewrite unsigned_lit by lia; reflexivity |].
intros mr2 a1' a2' a3' a4' INV2 PBK2 PBC2.
cbn [pf_spf] in *. unfold A_TP in *.
repeat match goal with H : rw_cells asegs _ _ _ |- _ => clear H | H : ro_cells asegs _ _ _ |- _ => clear H | H : munch _ _ _ |- _ => clear H | H : wmono asegs _ _ |- _ => clear H | H : mem_inv asegs _ |- _ => clear H end.
clear Htal Htlo Hthi Hqal Hqlo Hqhi Hqtk INtk INq INV0 INV1 HP cs_tk_L cs_L_tk cs_T1_L.
assert (Hl1 : nth_error (t_levels ts1) (t_depth ts1) = Some l1) by (unfold ts1, ts_lvl, ts0; cbn [t_levels t_depth]; apply nth_error_lupd_eq; apply nth_error_Some; rewrite Hl; discriminate).
reopen_inv INV2 ts1 ts0 (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 tk mxd depth l1 Hl1 bse Hbse mr2.
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t2.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 3 HP INtk ltac:(lia)) as SHT3.
replace (tk / 8 + 3 + A_SB) with (tk / 8 + 2147450883) in SHT3 by (unfold A_SB; lia).
pose proof (munch_refl [(tk, tk + 72)] mr2) as MU.
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
stash Himg_t2. clear Ld.
lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) => replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
step.
asan_chkM 1.
clear SHT3.
stepz.
do 5 step.
step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ mr2 mc, WMc : wmono asegs mr2 mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _ |- _ =>
evt_done5;
destruct (PE_INV_A_tokw1 HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo mr2 mc md A B ts1
cb nb pj sv errv co (TS isd (Z_to_bv 64 0) (Z_to_bv 64 co) err ucs high quote) STC INV2 MUc WMc MIc TOKc ltac:(cbn [pf_len]; lia) eq_refl) as [INV3 PBT3];
assert (AGp : agree_on asegs (t_pbs ts1) mr2 mc);
[ eapply (agree_wtqA HIx) with (ts := ts1); [exact STC | exact (proj1 (proj2 INV2)) | exact MUc | exact WMc
| apply Forall_cons; [left; left; cbn [fst snd pf_tk]; lia | apply Forall_nil] |];
intros a n Hin; assert (HinL : In (a, n) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts1 ++ LM)) by (unfold pe_blocksA, tstate_blocks; apply in_or_app; left; apply in_or_app; left; apply in_or_app; left; exact Hin);
split; [exact HinL|];
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ (proj1 (proj2 INV2))) as ND; unfold pe_blocksA in ND; rewrite <- app_assoc in ND; split;
[ intros ->; refine (nodup_app_ne _ _ _ _ _ _ ND _ _ eq_refl); [unfold tstate_blocks; apply in_or_app; left; exact Hin | left; reflexivity]
| intros ->; refine (nodup_app_ne _ _ _ _ _ _ ND _ _ eq_refl); [unfold tstate_blocks; apply in_or_app; left; exact Hin | right; left; reflexivity] ] |];
unstash Kredo; eapply (Kredo mc); [exact INV3 | exact (PBT3 _ PBK2) | exact (pbufc_agreeA _ _ _ _ _ _ PBC2 AGp (incl_refl _))]
end end.
Qed.

Lemma start_inf_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet)
(gp t0 t1 t2 a1 a3 a4 a5 a6 a7 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_start ->

(forall m' a0' a1' a2' a3' a4',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md A B
(ts_set_x (ts_lvl ts (TL ST_inf (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) (t_co ts) (TS (ts_isd (t_x ts)) (Z_to_bv 64 0) (ts_choff (t_x ts)) (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))) cb nb pj sv errv ->
PBOK m' (ts_set_x (ts_lvl ts (TL ST_inf (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) (t_co ts) (TS (ts_isd (t_x ts)) (Z_to_bv 64 0) (ts_choff (t_x ts)) (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))) 0 ->
pbufc asegs m' (t_pbs ts) (t_pb ts) [] ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa APE_REDO (t_co ts) gp t0 t1 t2 a0' a1' a2' a3' a4' a5 a6 a7
(Z_to_bv 64 (Z.of_nat (t_depth ts))) (Z_to_bv 64 (pf_tk pf + 56)) (Z_to_bv 64 (pa_F pa + 64)) F fc m')) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa 0x94fe0 (t_co ts) gp t0 t1 t2
(Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) a1
(Z_to_bv 64 (q / 8 + 4 * Z.of_nat (t_depth ts) + A_SB)) a3 a4 a5 a6 a7
(Z_to_bv 64 (Z.of_nat (t_depth ts))) (Z_to_bv 64 q) (Z_to_bv 64 (pa_F pa + 64)) F fc m).
Proof.
intros until fc. intros STC INV Hl Hst Kredo. pose proof INV as INV0. pe_openA STC INV.
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
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 1 HP INtk ltac:(lia)) as SHT1.
replace (tk / 8 + 1 + A_SB) with (tk / 8 + 2147450881) in SHT1 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 1 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT1c & SEPT1q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 1 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT1t & _).
cbn [hl_sb A4L] in SEPT1c, SEPT1q, SEPT1t. assert (EQx : tk / 8 + A_SB + 1 = tk / 8 + 2147450881) by (unfold A_SB; lia). rewrite EQx in SEPT1c, SEPT1q, SEPT1t. clear EQx.
unfold APE_BREAK, APE_REDO, APE_OUT, APE_ERRMEM, APE_ERRST, APE_JTAB in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
assert (cs_tk_L : csep tk 72 bse (Z.of_nat 32)) by (unfold csep; clear - Hdtq HbseR; lia).
assert (cs_L_tk : csep bse 32 tk (Z.of_nat 72)) by (unfold csep; clear - Hdtq HbseR; lia).
assert (cs_T1_L : csep (tk / 8 + 2147450881) 1 bse (Z.of_nat 32)) by (unfold csep; clear - SEPT1q HbseR; lia).
clear Hdtq SEPT1q SEPT1t SEPT1c.
destruct (lvl_mode_start2 _ _ _ SS26 ltac:(rewrite <- Hst; exact Hmode)) as (Ec0 & Ehn0 & Ess). subst c0 hn0.
stash Himg_t. stash Himg_q. stash Kredo. clear PB REST TSK LV OBJ HPR BUD GAP SAVED FSH FF STR ERR SBin SHT SHQ4.
reenterA asegs A4L HIx asegs_wx HP.
replace (q + 32 * Z.of_nat depth) with bse by lia.
asan_rechkA.
clear SHQ.
step.
stepz.
step.
asan_chkA.
step. step.

set (l1 := TL ST_inf (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, Lc : rw_cells asegs mc bse _ |- _ =>
pose proof MUc as MUc'; pose proof Lc as Lc'; rewrite Hbse in MUc', Lc';
destruct (PE_INV_A_lvl_write HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m mc md A B ts0
cb nb pj sv errv l ST_inf (tl_ss l) CNone false CNone STC INV0 Hl MUc' WMc MIc TOKc Lc' Hmode
ltac:(rewrite Ess; vm_compute; reflexivity) ltac:(unfold ST_inf; lia) SS26 (or_introl eq_refl)
ltac:(rewrite Hst; vm_compute; reflexivity)) as [INV1 _]; clear MUc' Lc'
end end.
set (ts1 := ts_lvl ts0 l1) in *.
eapply (pe_pbreset HIx GA GA_pres (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo _ md A B ts1 cb nb pj sv errv);
[exact STC | exact INV1 | rewrite unsigned_lit by lia; reflexivity |].
intros mr2 a1' a2' a3' a4' INV2 PBK2 PBC2.
cbn [pf_spf] in *. unfold A_TP in *.
repeat match goal with H : rw_cells asegs _ _ _ |- _ => clear H | H : ro_cells asegs _ _ _ |- _ => clear H | H : munch _ _ _ |- _ => clear H | H : wmono asegs _ _ |- _ => clear H | H : mem_inv asegs _ |- _ => clear H end.
clear Htal Htlo Hthi Hqal Hqlo Hqhi Hqtk INtk INq INV0 INV1 HP cs_tk_L cs_L_tk cs_T1_L.
assert (Hl1 : nth_error (t_levels ts1) (t_depth ts1) = Some l1) by (unfold ts1, ts_lvl, ts0; cbn [t_levels t_depth]; apply nth_error_lupd_eq; apply nth_error_Some; rewrite Hl; discriminate).
reopen_inv INV2 ts1 ts0 (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 tk mxd depth l1 Hl1 bse Hbse mr2.
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t2.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 3 HP INtk ltac:(lia)) as SHT3.
replace (tk / 8 + 3 + A_SB) with (tk / 8 + 2147450883) in SHT3 by (unfold A_SB; lia).
pose proof (munch_refl [(tk, tk + 72)] mr2) as MU.
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
stash Himg_t2. clear Ld.
lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) => replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
step.
asan_chkM 1.
clear SHT3.
stepz.
do 5 step.
step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ mr2 mc, WMc : wmono asegs mr2 mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _ |- _ =>
evt_done5;
destruct (PE_INV_A_tokw1 HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo mr2 mc md A B ts1
cb nb pj sv errv co (TS isd (Z_to_bv 64 0) (Z_to_bv 64 co) err ucs high quote) STC INV2 MUc WMc MIc TOKc ltac:(cbn [pf_len]; lia) eq_refl) as [INV3 PBT3];
assert (AGp : agree_on asegs (t_pbs ts1) mr2 mc);
[ eapply (agree_wtqA HIx) with (ts := ts1); [exact STC | exact (proj1 (proj2 INV2)) | exact MUc | exact WMc
| apply Forall_cons; [left; left; cbn [fst snd pf_tk]; lia | apply Forall_nil] |];
intros a n Hin; assert (HinL : In (a, n) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts1 ++ LM)) by (unfold pe_blocksA, tstate_blocks; apply in_or_app; left; apply in_or_app; left; apply in_or_app; left; exact Hin);
split; [exact HinL|];
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ (proj1 (proj2 INV2))) as ND; unfold pe_blocksA in ND; rewrite <- app_assoc in ND; split;
[ intros ->; refine (nodup_app_ne _ _ _ _ _ _ ND _ _ eq_refl); [unfold tstate_blocks; apply in_or_app; left; exact Hin | left; reflexivity]
| intros ->; refine (nodup_app_ne _ _ _ _ _ _ ND _ _ eq_refl); [unfold tstate_blocks; apply in_or_app; left; exact Hin | right; left; reflexivity] ] |];
unstash Kredo; eapply (Kredo mc); [exact INV3 | exact (PBT3 _ PBK2) | exact (pbufc_agreeA _ _ _ _ _ _ PBC2 AGp (incl_refl _))]
end end.
Qed.
End PeSStartTA.
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
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QJjn QRUw.Mq0 QRUw QkMG. Import QG8z Qdyh.Mq0 Qdyh.Mq3 Qdyh.Mq4.
Import QbFI. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqj QsKa.Mqd Qiiq QsKa.Mqf Q4v2 QlKV.Mqf QSHS Ql4f.Mq4 Q1Y6.Mq4 QsKa.Mqh QrQv.Mq4 QEUF.Mq2 QW22.Mq8 QdGy.Mq9.
Import Qc5u QAzu.Mq0 Q6vt QZUC.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section PeSPushB.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_outside : forall m m' W, GA m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= hl_img_lo A4H \/ hl_img_hi A4H <= fst iv) W -> GA m'.
Hypothesis GA_pres : forall LB SP m m', heap_pres A4H LB SP m m' -> GA m -> GA m'.
Hypothesis PUT : put_stmt_A HIx.

Lemma PE_INV_A_pushB : forall pf pa q LB0 LM FRS payload me lo m mc m' md md' A A' B B' ts cb nb pj sv errv errv' l stp,
PE_STATIC_A HIx pf pa lo ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
nth_error (t_levels ts) (t_depth ts) = Some l -> (S (t_depth ts) < Z.to_nat (pf_mxd pf))%nat -> t_objbs ts = [] ->
munch [(pf_tk pf, pf_tk pf + 72); (q + 32 * Z.of_nat (t_depth ts), q + 32 * Z.of_nat (t_depth ts) + 32)] m mc -> wmono asegs m mc -> mem_inv asegs mc ->
model_vm_only (cfg_model md) (cfg_model md') ->
HEAPA A4L HIx A' (pe_blocksA pf q LB0 ts) LM ((pa_F pa, 2) :: FRS) B' m' md' ->
tstack asegs m' q (lupd (lupd (t_levels ts) (t_depth ts) (TL stp (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) (S (t_depth ts)) lvl_reset) ->
rw_cells asegs m' (pf_tk pf) (tok_cells_g (pf_mxd pf) (pf_fl pf) (t_pb ts) (Z.of_nat (S (t_depth ts))) q (t_x ts)) ->
stk asegs m' lo (pf_spf pf) ->
heap_pres A4H (LB0 ++ LM ++ fr_ivs A4L ((pa_F pa, 2) :: FRS)) (pf_spf pf) mc m' ->
rw_cells asegs m' A_ERRNO [C4 errv'] ->
agree_on asegs (tstate_blocks ts) mc m' ->
PE_BUD pf pa (ts_push ts (TL stp (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) B' ->
(forall c hn, lvl_mode (tl_st l) (tl_ss l) = Some (c, hn) -> (stp = ST_array_add /\ c = CArr /\ hn = false) \/ (stp = ST_ovadd /\ c = CObj /\ hn = true)) ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' (ts_push ts (TL stp (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) cb nb pj sv errv'
/\ (forall b, PBOKat m ts b -> PBOKat m' (ts_push ts (TL stp (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) b).
Proof.
intros pf pa q LB0 LM FRS payload me lo m mc m' md md' A A' B B' ts cb nb pj sv errv errv' l stp STC [CORE REST] Hl Hd1 Eobj MU WM MI VM HP2 TSK2 TOK2 ST2 HPR2 ERR2 AG2 BUD2 Hmode.
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
unfold ts_push.
set (lp := TL stp (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)) in *.
set (ln := TL ST_eatws ST_start 0 None [] 0 []) in *.
pose proof STC as (LO & LOS & GEO & _). pose proof GEO as (Gspf & Gsp0 & Gle & _).
assert (Hd : (t_depth ts < length (t_levels ts))%nat) by (apply nth_error_Some; rewrite Hl; discriminate).
assert (Hd1' : (S (t_depth ts) < length (t_levels ts))%nat) by (rewrite LEN32; exact Hd1).
destruct (nth_error (t_levels ts) (S (t_depth ts))) as [l1|] eqn:Hl1; [| apply nth_error_None in Hl1; lia].
assert (HW : Forall (pe_wtqA pf pa q) [(pf_tk pf, pf_tk pf + 72); (q + 32 * Z.of_nat (t_depth ts), q + 32 * Z.of_nat (t_depth ts) + 32)]).
{ apply Forall_cons; [left; left; cbn [fst snd]; lia |]. apply Forall_cons; [| apply Forall_nil]. right. cbn [fst snd]. lia. }
assert (INq : In (q, 32 * pf_mxd pf) (pe_blocksA pf q LB0 ts)) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
assert (INtk : In (pf_tk pf, 72) (pe_blocksA pf q LB0 ts)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
pose proof (proj1 REST) as HP.

pose proof (PE_REST_A_private_write HIx GA GA_outside _ _ _ _ _ _ _ _ _ _ mc _ _ _ ts _ _ STC REST MU WM MI (pe_wtqA_private _ _ _ _ _ HW)) as REST'.
pose proof REST' as (HP' & LV' & OBJ' & ST' & ERR' & STR' & PLEN' & SBin' & HPR' & MDV' & G' & BUD').
pose proof (LV' _ _ Hl) as LVd. pose proof (LV' _ _ Hl1) as LV1.
assert (CL1 : lvl_clean l1).
{ destruct LV1 as (_ & _ & _ & M1). replace (S (t_depth ts) <? t_depth ts)%nat with false in M1 by (symmetry; apply Nat.ltb_ge; lia).
replace (S (t_depth ts) =? t_depth ts)%nat with false in M1 by (symmetry; apply Nat.eqb_neq; lia). exact M1. }
destruct CL1 as (C1 & C2 & C3 & C4 & C5).
assert (Eblk : map lvl_blocks (lupd (lupd (t_levels ts) (t_depth ts) lp) (S (t_depth ts)) ln) = map lvl_blocks (t_levels ts)).
{ rewrite (map_lupd_same lvl_blocks (lupd (t_levels ts) (t_depth ts) lp) (S (t_depth ts)) ln l1);
[| rewrite nth_error_lupd_neq by lia; exact Hl1 | unfold lvl_blocks, ln; cbn [tl_cbs tl_nbs]; rewrite C3, C5; reflexivity].
apply (map_lupd_same lvl_blocks (t_levels ts) (t_depth ts) lp l Hl). reflexivity. }
set (ts2 := TST (S (t_depth ts)) (lupd (lupd (t_levels ts) (t_depth ts) lp) (S (t_depth ts)) ln) (t_co ts) (t_pb ts) (t_pbs ts) (t_x ts) (t_obj ts) (t_objs ts) (t_objbs ts)).
assert (EB2 : pe_blocksA pf q LB0 ts2 = pe_blocksA pf q LB0 ts).
{ unfold pe_blocksA, tstate_blocks, ts2; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs]. rewrite Eblk. reflexivity. }
assert (AGm : agree_on asegs (tstate_blocks ts) m mc).
{ eapply (agree_wtqA HIx); [exact STC | exact HP | exact MU | exact WM | exact HW |].
intros a n Hin. assert (HinL : In (a, n) (pe_blocksA pf q LB0 ts ++ LM)) by (unfold pe_blocksA; apply in_or_app; left; apply in_or_app; left; exact Hin).
split; [exact HinL|].
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND. unfold pe_blocksA in ND. rewrite <- app_assoc in ND. split.
+ intros ->. refine (nodup_app_ne _ _ _ _ _ _ ND _ _ eq_refl); [exact Hin | left; reflexivity].
+ intros ->. refine (nodup_app_ne _ _ _ _ _ _ ND _ _ eq_refl); [exact Hin | right; left; reflexivity]. }
assert (AG : agree_on asegs (tstate_blocks ts) m m') by (eapply agree_on_trans; [exact AGm | exact AG2]).
assert (LV2 : forall i li, nth_error (t_levels ts2) i = Some li -> lvl_cur asegs A4F m' (t_depth ts2) i li).
{ unfold ts2; cbn [t_levels t_depth]. intros i li Hli.
destruct (PeanoNat.Nat.eq_dec i (S (t_depth ts))) as [-> | N1].
- rewrite nth_error_lupd_eq in Hli by (rewrite lupd_length; lia). injection Hli as <-.
split; [cbn; unfold ST_eatws; lia|]. split; [cbn; unfold ST_start; lia|]. split; [cbn; split; reflexivity|].
rewrite Nat.ltb_irrefl, Nat.eqb_refl. exists CNone, false. split; [reflexivity|]. split; [exact I|]. cbn. split; reflexivity.
- rewrite nth_error_lupd_neq in Hli by congruence.
destruct (PeanoNat.Nat.eq_dec i (t_depth ts)) as [-> | N0].
+ rewrite nth_error_lupd_eq in Hli by lia. injection Hli as <-.
assert (LVd2 : lvl_cur asegs A4F m' (t_depth ts) (t_depth ts) l).
{ eapply (lvl_cur_agree asegs A4F); [exact LVd | exact AG2 |]. intros b Hb. unfold tstate_blocks. apply in_or_app; right. apply in_or_app; right.
apply in_concat. exists (lvl_blocks l). split; [| exact Hb]. apply in_map. eapply nth_error_In; exact Hl. }
destruct LVd2 as (R1 & R2 & J & Md). rewrite Nat.ltb_irrefl, Nat.eqb_refl in Md. destruct Md as (c & hn & Hm & CLS & NM).
assert (Elt : (t_depth ts <? S (t_depth ts))%nat = true) by (apply Nat.ltb_lt; lia).
destruct (Hmode c hn Hm) as [(-> & -> & ->) | (-> & -> & ->)].
* split; [cbn; unfold ST_array_add; lia|]. split; [exact R2|]. split; [exact J|]. rewrite Elt. left. split; [reflexivity|]. split; [exact CLS | exact NM].
* split; [cbn; unfold ST_ovadd; lia|]. split; [exact R2|]. split; [exact J|]. rewrite Elt. right. split; [reflexivity|]. split; [exact CLS | exact NM].
+ rewrite nth_error_lupd_neq in Hli by congruence.
assert (LVi : lvl_cur asegs A4F m' (t_depth ts) i li).
{ eapply (lvl_cur_agree asegs A4F); [exact (LV' i li Hli) | exact AG2 |]. intros b Hb. unfold tstate_blocks. apply in_or_app; right. apply in_or_app; right.
apply in_concat. exists (lvl_blocks li). split; [| exact Hb]. apply in_map. eapply nth_error_In; exact Hli. }
destruct LVi as (R1 & R2 & J & M).
split; [exact R1|]. split; [exact R2|]. split; [exact J|].
destruct (Nat.ltb_spec i (t_depth ts)) as [Hlt | Hge].
* replace (i <? S (t_depth ts))%nat with true by (symmetry; apply Nat.ltb_lt; lia). exact M.
* replace (i =? t_depth ts)%nat with false in M by (symmetry; apply Nat.eqb_neq; lia).
replace (i <? S (t_depth ts))%nat with false by (symmetry; apply Nat.ltb_ge; lia).
replace (i =? S (t_depth ts))%nat with false by (symmetry; apply Nat.eqb_neq; lia). exact M. }
assert (REST2 : PE_REST_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' ts2 errv').
{ eapply (PE_REST_A_callG HIx GA GA_pres) with (ts := ts) (LBc := LB0); [exact STC | exact REST' | exact VM | exact HPR2 | apply incl_refl | rewrite EB2; exact HP2 | exact LV2 | | exact ST2 | exact ERR2 | exact BUD2].
unfold cur_st, ts2. cbn [t_levels t_depth t_objs t_objbs t_obj]. rewrite nth_error_lupd_eq by (rewrite lupd_length; lia). cbn. exact Eobj. }
split.
- split; [| exact REST2].
unfold PE_CORE_A, ts2; cbn [t_levels t_depth t_co t_x t_pb t_pbs]. split; [rewrite !lupd_length; exact LEN32|]. split; [exact Hd1|]. split; [exact CO|]. split; [exact CHOFF|].
split; [exact TOK2|]. split; [| split; [exact Hpb | split; [exact TSK2|]]].
+ eapply (pbuf_agree asegs (tstate_blocks ts)); [exact PB | exact AG | unfold tstate_blocks; intros b Hb; apply in_or_app; left; exact Hb].
+ eapply pe_frameA_pres; [exact HPR2 | lia | exact GEO | | |].
* apply in_or_app; right. apply in_or_app; right. change 248 with (fr_size 2 - 8). apply fr_ivs_frame. left; reflexivity.
* apply in_or_app; right. apply in_or_app; right. rewrite <- fr_shadow_len_2. change (shA (pa_F pa)) with (shad A4L (pa_F pa)). apply fr_ivs_shadow. left; reflexivity.
* eapply (pe_frameA_blkwrite HIx) with (ts := ts); [exact STC | exact HP | | exact FR | exact MU | exact WM].
apply Forall_cons; [exists (pf_tk pf), 72; cbn [fst snd]; split; [apply in_or_app; left; exact INtk | lia] |].
apply Forall_cons; [exists q, (32 * pf_mxd pf); cbn [fst snd]; split; [apply in_or_app; left; exact INq | lia] | apply Forall_nil].
- intros b PBK. eapply PBOKat_same with (ts := ts); [reflexivity | reflexivity |].
eapply PBOKat_agree; [exact PBK | exact AG | unfold tstate_blocks; intros x Hx; apply in_or_app; left; exact Hx].
Qed.
Ltac pe_openA STC INV :=
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR); pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk);
destruct INV as [CORE REST];
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR);
pose proof REST as (HP & LV & OBJ & ST & ERR & STR & PLEN & SBin & HPR & MDV & G & BUD).

Ltac reopen_push INVx TS1 ts0 PF q LB0 tk mxd depth bse Hbse mX :=
pose proof INVx as [CORE2 REST2];
destruct CORE2 as (_ & _ & _ & _ & TOK & _ & _ & TSK & FR);
pose proof REST2 as (HP & _); clear REST2;
unfold TS1, ts_push, ts0 in TOK, TSK; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_tk pf_mxd pf_fl] in TOK, TSK;
unfold tok_cells_g in TOK; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK;
unfold pe_frameA in FR; destruct FR as (SLOTS & _ & _ & _ & _); unfold pe_slotsA in SLOTS; cbn zeta in SLOTS;
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in SLOTS;
assert (INtk : In (tk, 72) (pe_blocksA PF q LB0 TS1)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity);
assert (INq : In (q, 32 * mxd) (pe_blocksA PF q LB0 TS1)) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity);
pose proof (tok_shadowA HIx _ _ _ _ _ _ _ _ HP INtk) as SHT;
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI;
pose proof (wmono_refl asegs mX) as WM;
pose proof (TSK (S depth) _ ltac:(apply nth_error_lupd_eq; rewrite lupd_length; lia)) as Ln;
replace (q + 32 * Z.of_nat (S depth)) with (bse + 32) in Ln by lia; unfold srec_cells in Ln; cbn [tl_st tl_ss tl_cur tl_name] in Ln;
pose proof (stack_shadowA HIx _ _ _ _ _ _ _ q mxd (Z.of_nat depth + 1) 2 HP INq ltac:(lia) ltac:(lia)) as SHN2;
pose proof (stack_shadowA HIx _ _ _ _ _ _ _ q mxd (Z.of_nat depth + 1) 3 HP INq ltac:(lia) ltac:(lia)) as SHN3;
replace (q / 8 + 4 * (Z.of_nat depth + 1) + 2 + A_SB) with (bse / 8 + 2147450886) in SHN2 by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia);
replace (q / 8 + 4 * (Z.of_nat depth + 1) + 3 + A_SB) with (bse / 8 + 2147450887) in SHN3 by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia);
pose proof (munch_refl [(q + 32 * Z.of_nat (S depth), q + 32 * Z.of_nat (S depth) + 32)] mX) as MU;
unfold shA in *; a4l; unfold SB2, SB4, SB7, SB8 in *;
clear TSK INtk INq.

Ltac shq_facts HP INq INtk q mxd tk dz j SH SEPq SEPt :=
pose proof (stack_shadowA HIx _ _ _ _ _ _ _ q mxd dz j HP INq ltac:(lia) ltac:(lia)) as SH;
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ q (32 * mxd) (4 * dz + j) q (32 * mxd) HP INq ltac:(lia) (in_or_app _ _ _ (or_introl INq))) as (_ & SEPq & _);
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ q (32 * mxd) (4 * dz + j) tk 72 HP INq ltac:(lia) (in_or_app _ _ _ (or_introl INtk))) as (_ & SEPt & _);
cbn [hl_sb A4L] in SEPq, SEPt.

Lemma seg_push_arr_B :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP : Z) (nB : nat)
(gp t0 a1 a2 a5 a6 a7 s3 s6 s7 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv -> PBOK m ts kP -> BOK pf pa ts B (S (Z.to_nat 512 + nB)) ->
nth_error (t_levels ts) (t_depth ts) = Some l -> (tl_st l = ST_array \/ tl_st l = ST_array_after_sep) ->
(S (t_depth ts) < Z.to_nat (pf_mxd pf))%nat ->

(forall m' md' A' B' errv' gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' (ts_push ts (TL ST_array_add (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) cb nb pj sv errv' ->
PBOK m' (ts_push ts (TL ST_array_add (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) kP ->
BOK pf pa (ts_push ts (TL ST_array_add (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) B' nB ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msA asegs pf pa APE_REDO (t_co ts) gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' m')) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa 0x940cc (t_co ts) gp t0 (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) a1 a2 (Z_to_bv 64 (q / 8 + 4 * Z.of_nat (t_depth ts) + A_SB)) (Z_to_bv 64 0) a5 a6 a7 s3 (Z_to_bv 64 q) s6 s7 (Z_to_bv 64 (Z.of_nat (t_depth ts))) s9 s11 t3 t4 t5 t6 F fc m).
Proof.
intros until fc. intros STC BSL INV PBK BK Hl Hst Hd1 Kredo. pose proof INV as INV0. pe_openA STC INV.
assert (Hd1' : (S (t_depth ts) < length (t_levels ts))%nat) by (rewrite LEN32; exact Hd1).
destruct (nth_error (t_levels ts) (S (t_depth ts))) as [l1|] eqn:Hl1; [| apply nth_error_None in Hl1; lia].
pose proof (PE_INV_A_next_clean HIx GA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ l1 INV0 Hl1) as Hcl1.
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
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs m) as WM.
pose proof (LV depth l Hl) as LVd. pose proof LVd as (ST26 & SS26 & _ & Md).
rewrite Nat.ltb_irrefl, Nat.eqb_refl in Md. destruct Md as (c0 & hn0 & Hmode & CLS0 & NM0).
destruct (lvl_mode_array _ _ _ _ Hst SS26 Hmode) as (-> & -> & SSnf).
assert (Eobjbs : objbs = []).
{ unfold cur_st in OBJ. cbn [t_levels t_depth t_objbs ts0] in OBJ. rewrite Hl in OBJ. destruct Hst as [E|E]; rewrite E in OBJ; exact OBJ. }
pose proof (TSK depth l Hl) as Ld. remember (q + 32 * Z.of_nat depth) as bse eqn:Hbse in Ld. unfold srec_cells in Ld.
pose proof (TSK (S depth) l1 Hl1) as Ln. replace (q + 32 * Z.of_nat (S depth)) with (bse + 32) in Ln by lia. unfold srec_cells in Ln.
assert (Ecl1 : tl_cur l1 = 0 /\ tl_name l1 = 0).
{ pose proof (LV (S depth) l1 Hl1) as (_ & _ & _ & M1).
replace (S depth <? depth)%nat with false in M1 by (symmetry; apply Nat.ltb_ge; lia).
replace (S depth =? depth)%nat with false in M1 by (symmetry; apply Nat.eqb_neq; lia). destruct M1 as (C1 & _ & _ & C4 & _). split; assumption. }
destruct Ecl1 as [Ec1 En1]. rewrite Ec1, En1 in Ln.
assert (HbseR : q <= bse /\ bse + 64 <= q + (32 * mxd)) by (subst bse; lia).
assert (Hb8 : bse mod 8 = 0) by (subst bse; clear - Hqal; Z.div_mod_to_equations; lia).

shq_facts HP INq INtk q mxd tk (Z.of_nat depth) 0 SHQ0 SEPQ0q SEPQ0t.
replace (q / 8 + 4 * Z.of_nat depth + 0 + A_SB) with (bse / 8 + 2147450880) in SHQ0 by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia).
shq_facts HP INq INtk q mxd tk (Z.of_nat depth + 1) 0 SHN0 SEPN0q SEPN0t.
replace (q / 8 + 4 * (Z.of_nat depth + 1) + 0 + A_SB) with (bse / 8 + 2147450884) in SHN0 by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia).
shq_facts HP INq INtk q mxd tk (Z.of_nat depth + 1) 2 SHN2 SEPN2q SEPN2t.
replace (q / 8 + 4 * (Z.of_nat depth + 1) + 2 + A_SB) with (bse / 8 + 2147450886) in SHN2 by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia).
shq_facts HP INq INtk q mxd tk (Z.of_nat depth + 1) 3 SHN3 SEPN3q SEPN3t.
replace (q / 8 + 4 * (Z.of_nat depth + 1) + 3 + A_SB) with (bse / 8 + 2147450887) in SHN3 by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia).
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 2 HP INtk ltac:(lia)) as SHT2.
replace (tk / 8 + 2 + A_SB) with (tk / 8 + 2147450882) in SHT2 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 2 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (_ & SEP2q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 2 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEP2t & _).
cbn [hl_sb A4L] in SEP2q, SEP2t.
pose proof (munch_refl [(tk, tk + 72); (bse, bse + 32)] m) as MU.
unfold APE_REDO, APE_JTAB in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
assert (EQx : q / 8 + 2147450880 + (4 * Z.of_nat depth + 0) = bse / 8 + 2147450880) by (rewrite Hbse, div8_add_mul32 by lia; lia). rewrite EQx in SEPQ0q, SEPQ0t. clear EQx.
assert (EQx : q / 8 + 2147450880 + (4 * (Z.of_nat depth + 1) + 0) = bse / 8 + 2147450884) by (rewrite Hbse, div8_add_mul32 by lia; lia). rewrite EQx in SEPN0q, SEPN0t. clear EQx.
assert (EQx : q / 8 + 2147450880 + (4 * (Z.of_nat depth + 1) + 2) = bse / 8 + 2147450886) by (rewrite Hbse, div8_add_mul32 by lia; lia). rewrite EQx in SEPN2q, SEPN2t. clear EQx.
assert (EQx : q / 8 + 2147450880 + (4 * (Z.of_nat depth + 1) + 3) = bse / 8 + 2147450887) by (rewrite Hbse, div8_add_mul32 by lia; lia). rewrite EQx in SEPN3q, SEPN3t. clear EQx.
assert (EQx : tk / 8 + 2147450880 + 2 = tk / 8 + 2147450882) by lia. rewrite EQx in SEP2q, SEP2t. clear EQx.

assert (cs_t_d : csep tk 72 bse (Z.of_nat 32)) by (unfold csep; clear - Hdtq HbseR; lia).
assert (cs_t_n : csep tk 72 (bse + 32) (Z.of_nat 32)) by (unfold csep; clear - Hdtq HbseR; lia).
assert (cs_d_t : csep bse 32 tk (Z.of_nat 72)) by (unfold csep; clear - Hdtq HbseR; lia).
assert (cs_n_t : csep (bse + 32) 32 tk (Z.of_nat 72)) by (unfold csep; clear - Hdtq HbseR; lia).
assert (cs_Q0_d : csep (bse / 8 + 2147450880) 1 bse (Z.of_nat 32)) by (unfold csep; clear - SEPQ0q HbseR; lia).
assert (cs_Q0_n : csep (bse / 8 + 2147450880) 1 (bse + 32) (Z.of_nat 32)) by (unfold csep; clear - SEPQ0q HbseR; lia).
assert (cs_Q0_t : csep (bse / 8 + 2147450880) 1 tk (Z.of_nat 72)) by (unfold csep; clear - SEPQ0t; lia).
assert (cs_N0_d : csep (bse / 8 + 2147450884) 1 bse (Z.of_nat 32)) by (unfold csep; clear - SEPN0q HbseR; lia).
assert (cs_N0_n : csep (bse / 8 + 2147450884) 1 (bse + 32) (Z.of_nat 32)) by (unfold csep; clear - SEPN0q HbseR; lia).
assert (cs_N0_t : csep (bse / 8 + 2147450884) 1 tk (Z.of_nat 72)) by (unfold csep; clear - SEPN0t; lia).
assert (cs_N2_d : csep (bse / 8 + 2147450886) 1 bse (Z.of_nat 32)) by (unfold csep; clear - SEPN2q HbseR; lia).
assert (cs_N2_n : csep (bse / 8 + 2147450886) 1 (bse + 32) (Z.of_nat 32)) by (unfold csep; clear - SEPN2q HbseR; lia).
assert (cs_N2_t : csep (bse / 8 + 2147450886) 1 tk (Z.of_nat 72)) by (unfold csep; clear - SEPN2t; lia).
assert (cs_N3_d : csep (bse / 8 + 2147450887) 1 bse (Z.of_nat 32)) by (unfold csep; clear - SEPN3q HbseR; lia).
assert (cs_N3_n : csep (bse / 8 + 2147450887) 1 (bse + 32) (Z.of_nat 32)) by (unfold csep; clear - SEPN3q HbseR; lia).
assert (cs_N3_t : csep (bse / 8 + 2147450887) 1 tk (Z.of_nat 72)) by (unfold csep; clear - SEPN3t; lia).
assert (cs_T2_d : csep (tk / 8 + 2147450882) 1 bse (Z.of_nat 32)) by (unfold csep; clear - SEP2q HbseR; lia).
assert (cs_T2_n : csep (tk / 8 + 2147450882) 1 (bse + 32) (Z.of_nat 32)) by (unfold csep; clear - SEP2q HbseR; lia).
assert (cs_T2_t : csep (tk / 8 + 2147450882) 1 tk (Z.of_nat 72)) by (unfold csep; clear - SEP2t; lia).
assert (CL1 : tl_cs l1 = None /\ tl_cbs l1 = [] /\ tl_nbs l1 = []).
{ pose proof (LV (S depth) l1 Hl1) as (_ & _ & _ & M1).
replace (S depth <? depth)%nat with false in M1 by (symmetry; apply Nat.ltb_ge; lia).
replace (S depth =? depth)%nat with false in M1 by (symmetry; apply Nat.eqb_neq; lia). destruct M1 as (_ & C2 & C3 & _ & C5). repeat split; assumption. }
destruct CL1 as (Ecs1 & Ecbs1 & Enbs1).
assert (TSKW : forall stp mc, munch [(tk, tk + 72); (bse, bse + 32)] m mc -> wmono asegs m mc ->
rw_cells asegs mc bse (srec_cells (TL stp (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) ->
tstack asegs mc q (lupd levels depth (TL stp (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)))).
{ intros stp mc MUc WMc Lc j lj Hj.
destruct (PeanoNat.Nat.eq_dec j depth) as [-> | N0]; [rewrite nth_error_lupd_eq in Hj by lia; injection Hj as <-; rewrite <- Hbse; exact Lc |].
rewrite nth_error_lupd_neq in Hj by congruence. pose proof (nth_error_Some_length Hj) as Hjl.
eapply rw_cells_transport; [exact (TSK j lj Hj) | exact MUc | exact WMc |]. rewrite srec_cells_size. cbn [disjoint_from fst snd Z.of_nat].
clear - Hdtq HbseR Hbse Hjl LEN32 N0 Hqlo. split; [| split; [| exact I]]; lia. }
clear Hdtq SEPQ0q SEPQ0t SEPN0q SEPN0t SEPN2q SEPN2t SEPN3q SEPN3t SEP2q SEP2t.
stash Himg_t. stash Himg_q. stash INV0. stash Kredo. clear PB REST TSK HP LV OBJ HPR BUD GAP SAVED FSH FF STR ERR SBin.
reenterA asegs A4L HIx asegs_wx HP.
replace (q + 32 * Z.of_nat depth) with bse by lia.
replace (q / 8 + 4 * Z.of_nat depth) with (bse / 8) by (subst bse; rewrite div8_add_mul32 by lia; lia).
step.
step. if_true.
asan_rechkB.
step.
stepz.
asan_rechkB.
step. step.
norm_w32. replace (Z.of_nat depth + 1) with (Z.of_nat (S depth)) by lia.
stepz.
step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, Lc : rw_cells asegs mc bse _, STc : stk asegs mc lo spf |- _ =>
evt_done5; unstash INV0; unstash Himg_t; unstash Himg_q;
pose proof (proj1 (proj2 INV0)) as HP0;
pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV0)))))) as ERR0;
assert (HPc : HEAPA A4L HIx A (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0) LM ((Ff, 2) :: FRS) B mc md) by (heap_nowA A4L HIx HP0 MUc WMc MIc);
pose proof (TSKW ST_array_add mc MUc WMc Lc) as TSc;
assert (ERRc : rw_cells asegs mc A_ERRNO [C4 errv])
by (eapply rw_cells_transport; [exact ERR0 | exact MUc | exact WMc | unfold A_ERRNO, A_TP; cbn [disjoint_from cells_size csize Nat.add fst snd]; clear - Himg_t Himg_q HbseR; lia])
end end.
set (lp := TL ST_array_add (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)) in *.
eapply (tok_reset_level_B_cps HIx PUT) with (i := S depth) (l := l1) (levels := lupd levels depth lp) (P := tstate_blocks ts0) (LB0 := LB0) (LM := LM)
(FRS := (Ff, 2) :: FRS) (B := B) (lo := lo) (errv := errv) (q := q) (r := tk) (pb := pb) (depth := Z.of_nat (S depth)) (mxd := mxd) (fl := fl)
(x := TS isd stpos (Z_to_bv 64 co) err ucs high quote) (rc := 1) (REST := pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0).
{ rewrite nth_error_lupd_neq by lia. exact Hl1. }
{ lia. }
{ exact (proj1 (proj2 RR)). }
{ rewrite lupd_length. exact LEN32. }
{ unfold lvl_blocks. rewrite Ecbs1, Enbs1. cbn [app]. exact HPc. }
{ reflexivity. }
{ rewrite Ecs1, Ecbs1, Ec1. split; reflexivity. }
{ left. split; [exact En1 | exact Enbs1]. }
{ exact TSc. }
{ unfold tok_cells_g. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote]. assumption. }
{ rewrite unsigned_lit by lia. assumption. }
{ exact LO. }
{ rewrite unsigned_lit by lia. unfold put_stk_A. clear - LOS. lia. }
{ rewrite unsigned_lit by lia. clear - Gspf. Z.div_mod_to_equations. lia. }
{ rewrite unsigned_lit by lia. clear - HT Gle. lia. }
{ apply heap_pres_refl. }
{ exact ERRc. }
{
rewrite Ecs1. cbn [put_costA].
pose proof (BOK_ledger_nonneg _ _ _ _ _ BK) as L0. pose proof BK as (H1 & _ & H3 & _). unfold bneed in H1.
pose proof (K_ev_pos (PEF tk oldl newl len lenr sb spf pmd mxd fl)). pose proof (Zle_0_nat (length (tstate_blocks ts0))).
replace (K_ev (PEF tk oldl newl len lenr sb spf pmd mxd fl) * Z.of_nat (S (Z.to_nat 512 + nB))) with (K_ev (PEF tk oldl newl len lenr sb spf pmd mxd fl) * Z.of_nat nB + 513) in H1 by (unfold K_ev; lia).
pose proof (Z.mul_nonneg_nonneg (K_ev (PEF tk oldl newl len lenr sb spf pmd mxd fl)) (Z.of_nat nB) ltac:(lia) ltac:(lia)). unfold K_free, K_exit in *.
cbn [pa_bslack] in H1. clear - H1 H H0 H2 H3 L0 BSL. lia. }
{ rewrite unsigned_lit by lia. reflexivity. }

intros ms2 md2 A2 (m2 & B2 & rv & RS2 & VM2 & OUT2 & TS2 & TOK2 & ST2 & HPR2 & ERR2 & AG2 & BB2 & BD2).
destruct RS2 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F2 & fc2 & -> & FS2 & FRM2).
a4l. rewrite ?unsigned_lit in ST2 by lia. rewrite ?unsigned_lit in HPR2 by lia.
destruct OUT2 as [[_ HP2] | (s' & Hcs' & _)]; [| rewrite Ecs1 in Hcs'; discriminate Hcs'].
rewrite Ecs1 in BB2. cbn [put_costA] in BB2.
set (TS1 := ts_push ts0 lp) in *.
pose proof (BOK_push (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) ts0 B _ l ST_array_add Hl Hd1'
ltac:(intros l1' H1'; unfold ts0 in H1'; cbn [t_levels t_depth] in H1'; rewrite Hl1 in H1'; injection H1' as <-; exact Hcl1)
(lvl_closed_open_ss l SSnf) eq_refl BK) as BK1.
fold lp in BK1. fold TS1 in BK1.
assert (BK2 : BOK (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) TS1 B2 nB).
{ eapply (BOK_pay _ _ _ _ B2 nB 512 BK1); [lia | clear - BB2; lia | clear - BD2; lia]. }
rewrite Hbse in MU.
destruct (PE_INV_A_pushB (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m m1 m2 md md2 A A2 B B2 ts0
cb nb pj sv errv errv l ST_array_add STC INV0 Hl Hd1 Eobjbs MU WM MI VM2 HP2 TS2 TOK2 ST2 HPR2 ERR2 AG2 (BOK_weak _ _ _ _ _ BK2)
ltac:(intros c' hn' Hm'; rewrite Hmode in Hm'; injection Hm' as <- <-; left; repeat split)) as [INV2 PBK2].
fold lp in INV2, PBK2. fold TS1 in INV2, PBK2.
clear TOK SLOTS Ld Ln SHQ0 SHN0 SHN2 SHN3 SHT2 MU WM MI INV0 BK BK1 INtk INq HP0 ERR0 HPc TSc ERRc ST HP2 TS2 TOK2 ST2 HPR2 ERR2 AG2 BB2 BD2 VM2 TSKW.
cbn [pf_spf] in *. unfold A_TP in *.
reopen_push INV2 TS1 ts0 (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 tk mxd depth bse Hbse m2.
reenterA asegs A4L HIx asegs_wx HP.
step.
do 3 step.

evt_done5. unstash Kredo. eapply (Kredo m2 md2 A2 B2 errv); [exact INV2 | exact (PBK2 _ PBK) | exact BK2 | exact FS2 | exact FRM2].
Qed.

Lemma seg_push_ov_B :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP : Z) (nB : nat)
(gp t0 a1 a2 a4 a5 a6 a7 s3 s6 s7 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv -> PBOK m ts kP -> BOK pf pa ts B (S (Z.to_nat 512 + nB)) ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_ovalue ->
(S (t_depth ts) < Z.to_nat (pf_mxd pf))%nat ->

(forall m' md' A' B' errv' gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' (ts_push ts (TL ST_ovadd (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) cb nb pj sv errv' ->
PBOK m' (ts_push ts (TL ST_ovadd (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) kP ->
BOK pf pa (ts_push ts (TL ST_ovadd (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) B' nB ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msA asegs pf pa APE_REDO (t_co ts) gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' m')) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa 0x94130 (t_co ts) gp t0 (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) a1 a2 (Z_to_bv 64 (q / 8 + 4 * Z.of_nat (t_depth ts) + A_SB)) a4 a5 a6 a7 s3 (Z_to_bv 64 q) s6 s7 (Z_to_bv 64 (Z.of_nat (t_depth ts))) s9 s11 t3 t4 t5 t6 F fc m).
Proof.
intros until fc. intros STC BSL INV PBK BK Hl Hst Hd1 Kredo. pose proof INV as INV0. pe_openA STC INV.
assert (Hd1' : (S (t_depth ts) < length (t_levels ts))%nat) by (rewrite LEN32; exact Hd1).
destruct (nth_error (t_levels ts) (S (t_depth ts))) as [l1|] eqn:Hl1; [| apply nth_error_None in Hl1; lia].
pose proof (PE_INV_A_next_clean HIx GA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ l1 INV0 Hl1) as Hcl1.
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
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs m) as WM.
pose proof (LV depth l Hl) as LVd. pose proof LVd as (ST26 & SS26 & _ & Md).
rewrite Nat.ltb_irrefl, Nat.eqb_refl in Md. destruct Md as (c0 & hn0 & Hmode & CLS0 & NM0).
pose proof Hmode as Hmode0. rewrite Hst in Hmode0. destruct (lvl_mode_ovalue _ _ _ SS26 Hmode0) as (-> & -> & SSnf).
assert (Eobjbs : objbs = []).
{ unfold cur_st in OBJ. cbn [t_levels t_depth t_objbs ts0] in OBJ. rewrite Hl in OBJ. rewrite Hst in OBJ; exact OBJ. }
pose proof (TSK depth l Hl) as Ld. remember (q + 32 * Z.of_nat depth) as bse eqn:Hbse in Ld. unfold srec_cells in Ld.
pose proof (TSK (S depth) l1 Hl1) as Ln. replace (q + 32 * Z.of_nat (S depth)) with (bse + 32) in Ln by lia. unfold srec_cells in Ln.
assert (Ecl1 : tl_cur l1 = 0 /\ tl_name l1 = 0).
{ pose proof (LV (S depth) l1 Hl1) as (_ & _ & _ & M1).
replace (S depth <? depth)%nat with false in M1 by (symmetry; apply Nat.ltb_ge; lia).
replace (S depth =? depth)%nat with false in M1 by (symmetry; apply Nat.eqb_neq; lia). destruct M1 as (C1 & _ & _ & C4 & _). split; assumption. }
destruct Ecl1 as [Ec1 En1]. rewrite Ec1, En1 in Ln.
assert (HbseR : q <= bse /\ bse + 64 <= q + (32 * mxd)) by (subst bse; lia).
assert (Hb8 : bse mod 8 = 0) by (subst bse; clear - Hqal; Z.div_mod_to_equations; lia).

shq_facts HP INq INtk q mxd tk (Z.of_nat depth) 0 SHQ0 SEPQ0q SEPQ0t.
replace (q / 8 + 4 * Z.of_nat depth + 0 + A_SB) with (bse / 8 + 2147450880) in SHQ0 by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia).
shq_facts HP INq INtk q mxd tk (Z.of_nat depth + 1) 0 SHN0 SEPN0q SEPN0t.
replace (q / 8 + 4 * (Z.of_nat depth + 1) + 0 + A_SB) with (bse / 8 + 2147450884) in SHN0 by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia).
shq_facts HP INq INtk q mxd tk (Z.of_nat depth + 1) 2 SHN2 SEPN2q SEPN2t.
replace (q / 8 + 4 * (Z.of_nat depth + 1) + 2 + A_SB) with (bse / 8 + 2147450886) in SHN2 by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia).
shq_facts HP INq INtk q mxd tk (Z.of_nat depth + 1) 3 SHN3 SEPN3q SEPN3t.
replace (q / 8 + 4 * (Z.of_nat depth + 1) + 3 + A_SB) with (bse / 8 + 2147450887) in SHN3 by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia).
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 2 HP INtk ltac:(lia)) as SHT2.
replace (tk / 8 + 2 + A_SB) with (tk / 8 + 2147450882) in SHT2 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 2 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (_ & SEP2q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 2 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEP2t & _).
cbn [hl_sb A4L] in SEP2q, SEP2t.
pose proof (munch_refl [(tk, tk + 72); (bse, bse + 32)] m) as MU.
unfold APE_REDO, APE_JTAB in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
assert (EQx : q / 8 + 2147450880 + (4 * Z.of_nat depth + 0) = bse / 8 + 2147450880) by (rewrite Hbse, div8_add_mul32 by lia; lia). rewrite EQx in SEPQ0q, SEPQ0t. clear EQx.
assert (EQx : q / 8 + 2147450880 + (4 * (Z.of_nat depth + 1) + 0) = bse / 8 + 2147450884) by (rewrite Hbse, div8_add_mul32 by lia; lia). rewrite EQx in SEPN0q, SEPN0t. clear EQx.
assert (EQx : q / 8 + 2147450880 + (4 * (Z.of_nat depth + 1) + 2) = bse / 8 + 2147450886) by (rewrite Hbse, div8_add_mul32 by lia; lia). rewrite EQx in SEPN2q, SEPN2t. clear EQx.
assert (EQx : q / 8 + 2147450880 + (4 * (Z.of_nat depth + 1) + 3) = bse / 8 + 2147450887) by (rewrite Hbse, div8_add_mul32 by lia; lia). rewrite EQx in SEPN3q, SEPN3t. clear EQx.
assert (EQx : tk / 8 + 2147450880 + 2 = tk / 8 + 2147450882) by lia. rewrite EQx in SEP2q, SEP2t. clear EQx.

assert (cs_t_d : csep tk 72 bse (Z.of_nat 32)) by (unfold csep; clear - Hdtq HbseR; lia).
assert (cs_t_n : csep tk 72 (bse + 32) (Z.of_nat 32)) by (unfold csep; clear - Hdtq HbseR; lia).
assert (cs_d_t : csep bse 32 tk (Z.of_nat 72)) by (unfold csep; clear - Hdtq HbseR; lia).
assert (cs_n_t : csep (bse + 32) 32 tk (Z.of_nat 72)) by (unfold csep; clear - Hdtq HbseR; lia).
assert (cs_Q0_d : csep (bse / 8 + 2147450880) 1 bse (Z.of_nat 32)) by (unfold csep; clear - SEPQ0q HbseR; lia).
assert (cs_Q0_n : csep (bse / 8 + 2147450880) 1 (bse + 32) (Z.of_nat 32)) by (unfold csep; clear - SEPQ0q HbseR; lia).
assert (cs_Q0_t : csep (bse / 8 + 2147450880) 1 tk (Z.of_nat 72)) by (unfold csep; clear - SEPQ0t; lia).
assert (cs_N0_d : csep (bse / 8 + 2147450884) 1 bse (Z.of_nat 32)) by (unfold csep; clear - SEPN0q HbseR; lia).
assert (cs_N0_n : csep (bse / 8 + 2147450884) 1 (bse + 32) (Z.of_nat 32)) by (unfold csep; clear - SEPN0q HbseR; lia).
assert (cs_N0_t : csep (bse / 8 + 2147450884) 1 tk (Z.of_nat 72)) by (unfold csep; clear - SEPN0t; lia).
assert (cs_N2_d : csep (bse / 8 + 2147450886) 1 bse (Z.of_nat 32)) by (unfold csep; clear - SEPN2q HbseR; lia).
assert (cs_N2_n : csep (bse / 8 + 2147450886) 1 (bse + 32) (Z.of_nat 32)) by (unfold csep; clear - SEPN2q HbseR; lia).
assert (cs_N2_t : csep (bse / 8 + 2147450886) 1 tk (Z.of_nat 72)) by (unfold csep; clear - SEPN2t; lia).
assert (cs_N3_d : csep (bse / 8 + 2147450887) 1 bse (Z.of_nat 32)) by (unfold csep; clear - SEPN3q HbseR; lia).
assert (cs_N3_n : csep (bse / 8 + 2147450887) 1 (bse + 32) (Z.of_nat 32)) by (unfold csep; clear - SEPN3q HbseR; lia).
assert (cs_N3_t : csep (bse / 8 + 2147450887) 1 tk (Z.of_nat 72)) by (unfold csep; clear - SEPN3t; lia).
assert (cs_T2_d : csep (tk / 8 + 2147450882) 1 bse (Z.of_nat 32)) by (unfold csep; clear - SEP2q HbseR; lia).
assert (cs_T2_n : csep (tk / 8 + 2147450882) 1 (bse + 32) (Z.of_nat 32)) by (unfold csep; clear - SEP2q HbseR; lia).
assert (cs_T2_t : csep (tk / 8 + 2147450882) 1 tk (Z.of_nat 72)) by (unfold csep; clear - SEP2t; lia).
assert (CL1 : tl_cs l1 = None /\ tl_cbs l1 = [] /\ tl_nbs l1 = []).
{ pose proof (LV (S depth) l1 Hl1) as (_ & _ & _ & M1).
replace (S depth <? depth)%nat with false in M1 by (symmetry; apply Nat.ltb_ge; lia).
replace (S depth =? depth)%nat with false in M1 by (symmetry; apply Nat.eqb_neq; lia). destruct M1 as (_ & C2 & C3 & _ & C5). repeat split; assumption. }
destruct CL1 as (Ecs1 & Ecbs1 & Enbs1).
assert (TSKW : forall stp mc, munch [(tk, tk + 72); (bse, bse + 32)] m mc -> wmono asegs m mc ->
rw_cells asegs mc bse (srec_cells (TL stp (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) ->
tstack asegs mc q (lupd levels depth (TL stp (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)))).
{ intros stp mc MUc WMc Lc j lj Hj.
destruct (PeanoNat.Nat.eq_dec j depth) as [-> | N0]; [rewrite nth_error_lupd_eq in Hj by lia; injection Hj as <-; rewrite <- Hbse; exact Lc |].
rewrite nth_error_lupd_neq in Hj by congruence. pose proof (nth_error_Some_length Hj) as Hjl.
eapply rw_cells_transport; [exact (TSK j lj Hj) | exact MUc | exact WMc |]. rewrite srec_cells_size. cbn [disjoint_from fst snd Z.of_nat].
clear - Hdtq HbseR Hbse Hjl LEN32 N0 Hqlo. split; [| split; [| exact I]]; lia. }
clear Hdtq SEPQ0q SEPQ0t SEPN0q SEPN0t SEPN2q SEPN2t SEPN3q SEPN3t SEP2q SEP2t.
stash Himg_t. stash Himg_q. stash INV0. stash Kredo. clear PB REST TSK HP LV OBJ HPR BUD GAP SAVED FSH FF STR ERR SBin.
reenterA asegs A4L HIx asegs_wx HP.
replace (q + 32 * Z.of_nat depth) with bse by lia.
replace (q / 8 + 4 * Z.of_nat depth) with (bse / 8) by (subst bse; rewrite div8_add_mul32 by lia; lia).
asan_rechkB.
step.
stepz.
asan_rechkB.
step. step.
norm_w32. replace (Z.of_nat depth + 1) with (Z.of_nat (S depth)) by lia.
stepz.
step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, Lc : rw_cells asegs mc bse _, STc : stk asegs mc lo spf |- _ =>
evt_done5; unstash INV0; unstash Himg_t; unstash Himg_q;
pose proof (proj1 (proj2 INV0)) as HP0;
pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV0)))))) as ERR0;
assert (HPc : HEAPA A4L HIx A (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0) LM ((Ff, 2) :: FRS) B mc md) by (heap_nowA A4L HIx HP0 MUc WMc MIc);
pose proof (TSKW ST_ovadd mc MUc WMc Lc) as TSc;
assert (ERRc : rw_cells asegs mc A_ERRNO [C4 errv])
by (eapply rw_cells_transport; [exact ERR0 | exact MUc | exact WMc | unfold A_ERRNO, A_TP; cbn [disjoint_from cells_size csize Nat.add fst snd]; clear - Himg_t Himg_q HbseR; lia])
end end.
set (lp := TL ST_ovadd (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)) in *.
eapply (tok_reset_level_B_cps HIx PUT) with (i := S depth) (l := l1) (levels := lupd levels depth lp) (P := tstate_blocks ts0) (LB0 := LB0) (LM := LM)
(FRS := (Ff, 2) :: FRS) (B := B) (lo := lo) (errv := errv) (q := q) (r := tk) (pb := pb) (depth := Z.of_nat (S depth)) (mxd := mxd) (fl := fl)
(x := TS isd stpos (Z_to_bv 64 co) err ucs high quote) (rc := 1) (REST := pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0).
{ rewrite nth_error_lupd_neq by lia. exact Hl1. }
{ lia. }
{ exact (proj1 (proj2 RR)). }
{ rewrite lupd_length. exact LEN32. }
{ unfold lvl_blocks. rewrite Ecbs1, Enbs1. cbn [app]. exact HPc. }
{ reflexivity. }
{ rewrite Ecs1, Ecbs1, Ec1. split; reflexivity. }
{ left. split; [exact En1 | exact Enbs1]. }
{ exact TSc. }
{ unfold tok_cells_g. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote]. assumption. }
{ rewrite unsigned_lit by lia. assumption. }
{ exact LO. }
{ rewrite unsigned_lit by lia. unfold put_stk_A. clear - LOS. lia. }
{ rewrite unsigned_lit by lia. clear - Gspf. Z.div_mod_to_equations. lia. }
{ rewrite unsigned_lit by lia. clear - HT Gle. lia. }
{ apply heap_pres_refl. }
{ exact ERRc. }
{
rewrite Ecs1. cbn [put_costA].
pose proof (BOK_ledger_nonneg _ _ _ _ _ BK) as L0. pose proof BK as (H1 & _ & H3 & _). unfold bneed in H1.
pose proof (K_ev_pos (PEF tk oldl newl len lenr sb spf pmd mxd fl)). pose proof (Zle_0_nat (length (tstate_blocks ts0))).
replace (K_ev (PEF tk oldl newl len lenr sb spf pmd mxd fl) * Z.of_nat (S (Z.to_nat 512 + nB))) with (K_ev (PEF tk oldl newl len lenr sb spf pmd mxd fl) * Z.of_nat nB + 513) in H1 by (unfold K_ev; lia).
pose proof (Z.mul_nonneg_nonneg (K_ev (PEF tk oldl newl len lenr sb spf pmd mxd fl)) (Z.of_nat nB) ltac:(lia) ltac:(lia)). unfold K_free, K_exit in *.
cbn [pa_bslack] in H1. clear - H1 H H0 H2 H3 L0 BSL. lia. }
{ rewrite unsigned_lit by lia. reflexivity. }

intros ms2 md2 A2 (m2 & B2 & rv & RS2 & VM2 & OUT2 & TS2 & TOK2 & ST2 & HPR2 & ERR2 & AG2 & BB2 & BD2).
destruct RS2 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F2 & fc2 & -> & FS2 & FRM2).
a4l. rewrite ?unsigned_lit in ST2 by lia. rewrite ?unsigned_lit in HPR2 by lia.
destruct OUT2 as [[_ HP2] | (s' & Hcs' & _)]; [| rewrite Ecs1 in Hcs'; discriminate Hcs'].
rewrite Ecs1 in BB2. cbn [put_costA] in BB2.
set (TS1 := ts_push ts0 lp) in *.
pose proof (BOK_push (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) ts0 B _ l ST_ovadd Hl Hd1'
ltac:(intros l1' H1'; unfold ts0 in H1'; cbn [t_levels t_depth] in H1'; rewrite Hl1 in H1'; injection H1' as <-; exact Hcl1)
(lvl_closed_open_ss l SSnf) eq_refl BK) as BK1.
fold lp in BK1. fold TS1 in BK1.
assert (BK2 : BOK (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) TS1 B2 nB).
{ eapply (BOK_pay _ _ _ _ B2 nB 512 BK1); [lia | clear - BB2; lia | clear - BD2; lia]. }
rewrite Hbse in MU.
destruct (PE_INV_A_pushB (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m m1 m2 md md2 A A2 B B2 ts0
cb nb pj sv errv errv l ST_ovadd STC INV0 Hl Hd1 Eobjbs MU WM MI VM2 HP2 TS2 TOK2 ST2 HPR2 ERR2 AG2 (BOK_weak _ _ _ _ _ BK2)
ltac:(intros c' hn' Hm'; rewrite Hmode in Hm'; injection Hm' as <- <-; right; repeat split)) as [INV2 PBK2].
fold lp in INV2, PBK2. fold TS1 in INV2, PBK2.
clear TOK SLOTS Ld Ln SHQ0 SHN0 SHN2 SHN3 SHT2 MU WM MI INV0 BK BK1 INtk INq HP0 ERR0 HPc TSc ERRc ST HP2 TS2 TOK2 ST2 HPR2 ERR2 AG2 BB2 BD2 VM2 TSKW.
cbn [pf_spf] in *. unfold A_TP in *.
reopen_push INV2 TS1 ts0 (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 tk mxd depth bse Hbse m2.
reenterA asegs A4L HIx asegs_wx HP.
step.
do 3 step.

evt_done5. unstash Kredo. eapply (Kredo m2 md2 A2 B2 errv); [exact INV2 | exact (PBK2 _ PBK) | exact BK2 | exact FS2 | exact FRM2].
Qed.
End PeSPushB.
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
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqj QsKa.Mqd Qiiq QsKa.Mqf Q4v2 QlKV.Mqf QSHS Ql4f.Mq4 Q1Y6.Mq4 QsKa.Mqh QrQv.Mq4 QEUF.Mq2 QW22.Mq8 QdGy.Mq9 QYZ0.Mq8.
Import Qc5u QAzu.Mq0.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section PeSSescJA.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_outside : forall m m' W, GA m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= hl_img_lo A4H \/ hl_img_hi A4H <= fst iv) W -> GA m'.
Hypothesis GA_pres : forall LB SP m m', heap_pres A4H LB SP m m' -> GA m -> GA m'.

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

Lemma sesc_join_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP : Z)
(gp t0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv -> PBOK m ts kP ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_string_escape ->
(forall c hn, lvl_mode (tl_st l) (tl_ss l) = Some (c, hn) -> lvl_mode (tl_ss l) (tl_ss l) = Some (c, hn)) ->
zin (tl_ss l) [ST_array_add; ST_ovadd] = false ->

(forall m' gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' s6' s7' s8' s9' s11' t3' t4' t5' t6',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md A B (ts_lvl ts (TL (tl_ss l) (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) cb nb pj sv errv ->
PBOK m' (ts_lvl ts (TL (tl_ss l) (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) kP ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa APE_BREAK (t_co ts) gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' (Z_to_bv 64 2) s6' s7' s8' s9' s11' t3' t4' t5' t6' F fc m')) ->
AJ5 A4L HIx A T md (pe_msA asegs pf pa 0x984ac (t_co ts) gp t0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc m).
Proof.
intros until fc. intros STC INV PBK Hl Hst HMODE Hzss Kbreak. pose proof INV as INV0. pe_openA STC INV.
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
unfold APE_BREAK, APE_STBRK, APE_REDO, APE_OUT, APE_ERRMEM, APE_JTAB in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
assert (cs_tk_L : csep tk 72 bse (Z.of_nat 32)) by (unfold csep; clear - Hdtq HbseR; lia).
assert (cs_L_tk : csep bse 32 tk (Z.of_nat 72)) by (unfold csep; clear - Hdtq HbseR; lia).
clear Hdtq SEPQ0c SEPQ0q SEPQ0t SEPT7c SEPT7q SEPT7t SEPT2c SEPT2q SEPT2t.
stash Himg_t. stash Himg_q. stash Kbreak. clear PB REST TSK LV OBJ HPR BUD GAP SAVED FSH FF STR ERR SBin SHT SHQ SHQ4.
reenterA asegs A4L HIx asegs_wx HP.
assert (BLO : 0 < bse < 2^63 /\ q <= bse) by (subst bse; lia).
step.
asan_rechkB.
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
asan_chkMB 2.
norm_sx32.
stepz.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, Lc : rw_cells asegs mc bse _ |- _ =>
evt_done5; subst bse;
destruct (PE_INV_A_lvl_writeG HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m mc md A B ts0
cb nb pj sv errv l (tl_ss l) (tl_ss l) c0 hn0 c0 STC INV0 Hl MUc WMc MIc TOKc Lc Hmode (HMODE _ _ Hmode) SS26 SS26 (or_introl eq_refl)
ltac:(left; rewrite Hst, Hzss; reflexivity)) as [INV3 PBK3];
unstash Kbreak; eapply (Kbreak mc); [exact INV3 | exact (PBK3 kP PBK)]
end end.
Qed.

Lemma sesc_joinq_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP : Z)
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv -> PBOK m ts kP ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_string_escape ->
(forall c hn, lvl_mode (tl_st l) (tl_ss l) = Some (c, hn) -> lvl_mode (tl_ss l) (tl_ss l) = Some (c, hn)) ->
zin (tl_ss l) [ST_array_add; ST_ovadd] = false ->

(forall m' gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' s6' s7' s8' s9' s11' t3' t4' t5' t6',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md A B (ts_lvl ts (TL (tl_ss l) (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) cb nb pj sv errv ->
PBOK m' (ts_lvl ts (TL (tl_ss l) (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) kP ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa APE_BREAK (t_co ts) gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' (Z_to_bv 64 2) s6' s7' s8' s9' s11' t3' t4' t5' t6' F fc m')) ->
AJ5 A4L HIx A T md (pe_msX asegs pf pa 0x97f90 x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 (Z_to_bv 64 (pf_sb pf + t_co ts)) s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc m).
Proof.
intros until fc. intros STC INV PBK Hl Hst HMODE Hzss Kbreak. pose proof INV as INV0. pe_openA STC INV.
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
unfold APE_BREAK, APE_STBRK, APE_REDO, APE_OUT, APE_ERRMEM, APE_JTAB in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
assert (cs_tk_L : csep tk 72 bse (Z.of_nat 32)) by (unfold csep; clear - Hdtq HbseR; lia).
assert (cs_L_tk : csep bse 32 tk (Z.of_nat 72)) by (unfold csep; clear - Hdtq HbseR; lia).
clear Hdtq SEPQ0c SEPQ0q SEPQ0t SEPT7c SEPT7q SEPT7t SEPT2c SEPT2q SEPT2t.
stash Himg_t. stash Himg_q. stash Kbreak. clear PB REST TSK LV OBJ HPR BUD GAP SAVED FSH FF STR ERR SBin SHT SHQ SHQ4.
reenterA asegs A4L HIx asegs_wx HP.
assert (BLO : 0 < bse < 2^63 /\ q <= bse) by (subst bse; lia).
step.
asan_rechkMB 2.
asan_rechkMB 3.
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
asan_chkMB 2.
norm_sx32.
stepz.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, Lc : rw_cells asegs mc bse _ |- _ =>
evt_done5; subst bse;
destruct (PE_INV_A_lvl_writeG HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m mc md A B ts0
cb nb pj sv errv l (tl_ss l) (tl_ss l) c0 hn0 c0 STC INV0 Hl MUc WMc MIc TOKc Lc Hmode (HMODE _ _ Hmode) SS26 SS26 (or_introl eq_refl)
ltac:(left; rewrite Hst, Hzss; reflexivity)) as [INV3 PBK3];
unstash Kbreak; eapply (Kbreak mc); [exact INV3 | exact (PBK3 kP PBK)]
end end.
Qed.
End PeSSescJA.
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
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqj QsKa.Mqd Qiiq QsKa.Mqf Q4v2 QlKV.Mqf QSHS Ql4f.Mq4 Q1Y6.Mq4 QsKa.Mqh QrQv.Mq4 QEUF.Mq2 QW22.Mq8 QdGy.Mq9 QYZ0.Mq8.
Import Qc5u QAzu.Mq0.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Lemma lvl_mode_start2 : forall ss c hn, 0 <= ss <= 26 -> lvl_mode ST_start ss = Some (c, hn) -> c = CNone /\ hn = false /\ ss = ST_start.
Proof.
intros ss c hn R H. assert (CASES : exists k : nat, (k <= 26)%nat /\ ss = Z.of_nat k) by (exists (Z.to_nat ss); split; lia).
destruct CASES as (k & Hk & ->). clear R.
do 27 (destruct k as [|k]; [vm_compute in H; first [discriminate H | injection H as <- <-; split; [reflexivity | split; reflexivity]] |]); exfalso; lia.
Qed.

Lemma pbufc_agreeA : forall BS m m' pbs pb pre, pbufc asegs m pbs pb pre -> agree_on asegs BS m m' -> incl pbs BS -> pbufc asegs m' pbs pb pre.
Proof.
intros BS m m' pbs pb pre (buf & bpos & size & post & E & L & C) AG Hi. exists buf, bpos, size, post.
split; [exact E|]. split; [exact L|].
eapply (pbuf_core_agree asegs); [exact C | exact AG | apply Hi; rewrite E; left; reflexivity | apply Hi; rewrite E; right; left; reflexivity].
Qed.

Section PeSStartTA.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_outside : forall m m' W, GA m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= hl_img_lo A4H \/ hl_img_hi A4H <= fst iv) W -> GA m'.
Hypothesis GA_pres : forall LB SP m m', heap_pres A4H LB SP m m' -> GA m -> GA m'.

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

Lemma start_num_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet)
(gp t0 a1 a2 a5 a6 a7 s3 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_start ->

(forall m' a0' a1' a2' a3' a4',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md A B
(ts_set_x (ts_lvl ts (TL ST_number (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) (t_co ts) (TS (Z_to_bv 64 0) (ts_stpos (t_x ts)) (ts_choff (t_x ts)) (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))) cb nb pj sv errv ->
PBOK m' (ts_set_x (ts_lvl ts (TL ST_number (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) (t_co ts) (TS (Z_to_bv 64 0) (ts_stpos (t_x ts)) (ts_choff (t_x ts)) (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))) 0 ->
pbufc asegs m' (t_pbs ts) (t_pb ts) [] ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa APE_REDO (t_co ts) gp t0 a0' a1' a2' a3' a4' a5 a6 a7 s3 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc m')) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa 0x94d04 (t_co ts) gp t0 (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) a1 a2 (Z_to_bv 64 (q / 8 + 4 * Z.of_nat (t_depth ts) + A_SB)) (Z_to_bv 64 0) a5 a6 a7 s3 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc m).
Proof.
intros until fc. intros STC INV Hl Hst Kredo. pose proof INV as INV0. pe_openA STC INV.
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
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 1 HP INtk ltac:(lia)) as SHT1.
replace (tk / 8 + 1 + A_SB) with (tk / 8 + 2147450881) in SHT1 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 1 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT1c & SEPT1q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 1 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT1t & _).
cbn [hl_sb A4L] in SEPT1c, SEPT1q, SEPT1t. assert (EQx : tk / 8 + A_SB + 1 = tk / 8 + 2147450881) by (unfold A_SB; lia). rewrite EQx in SEPT1c, SEPT1q, SEPT1t. clear EQx.
unfold APE_BREAK, APE_REDO, APE_OUT, APE_ERRMEM, APE_JTAB in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
assert (cs_tk_L : csep tk 72 bse (Z.of_nat 32)) by (unfold csep; clear - Hdtq HbseR; lia).
assert (cs_L_tk : csep bse 32 tk (Z.of_nat 72)) by (unfold csep; clear - Hdtq HbseR; lia).
assert (cs_T1_L : csep (tk / 8 + 2147450881) 1 bse (Z.of_nat 32)) by (unfold csep; clear - SEPT1q HbseR; lia).
clear Hdtq SEPT1q SEPT1t SEPT1c.
destruct (lvl_mode_start2 _ _ _ SS26 ltac:(rewrite <- Hst; exact Hmode)) as (Ec0 & Ehn0 & Ess). subst c0 hn0.
stash Himg_t. stash Himg_q. stash Kredo. clear PB REST TSK LV OBJ HPR BUD GAP SAVED FSH FF STR ERR SBin SHT SHQ4.
reenterA asegs A4L HIx asegs_wx HP.
replace (q + 32 * Z.of_nat depth) with bse by lia.
step.
step. if_true.
asan_rechkB.
clear SHQ.
step.
stepz.
step.
asan_chkB.
step. step.

set (l1 := TL ST_number (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, Lc : rw_cells asegs mc bse _ |- _ =>
pose proof MUc as MUc'; pose proof Lc as Lc'; rewrite Hbse in MUc', Lc';
destruct (PE_INV_A_lvl_write HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m mc md A B ts0
cb nb pj sv errv l ST_number (tl_ss l) CNone false CNone STC INV0 Hl MUc' WMc MIc TOKc Lc' Hmode
ltac:(rewrite Ess; vm_compute; reflexivity) ltac:(unfold ST_number; lia) SS26 (or_introl eq_refl)
ltac:(rewrite Hst; vm_compute; reflexivity)) as [INV1 _]; clear MUc' Lc'
end end.
set (ts1 := ts_lvl ts0 l1) in *.
eapply (pe_pbreset HIx GA GA_pres (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo _ md A B ts1 cb nb pj sv errv);
[exact STC | exact INV1 | rewrite unsigned_lit by lia; reflexivity |].
intros mr2 a1' a2' a3' a4' INV2 PBK2 PBC2.
cbn [pf_spf] in *. unfold A_TP in *.
repeat match goal with H : rw_cells asegs _ _ _ |- _ => clear H | H : ro_cells asegs _ _ _ |- _ => clear H | H : munch _ _ _ |- _ => clear H | H : wmono asegs _ _ |- _ => clear H | H : mem_inv asegs _ |- _ => clear H end.
clear Htal Htlo Hthi Hqal Hqlo Hqhi Hqtk INtk INq INV0 INV1 HP cs_tk_L cs_L_tk cs_T1_L.
assert (Hl1 : nth_error (t_levels ts1) (t_depth ts1) = Some l1) by (unfold ts1, ts_lvl, ts0; cbn [t_levels t_depth]; apply nth_error_lupd_eq; apply nth_error_Some; rewrite Hl; discriminate).
reopen_inv INV2 ts1 ts0 (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 tk mxd depth l1 Hl1 bse Hbse mr2.
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t2.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 3 HP INtk ltac:(lia)) as SHT3.
replace (tk / 8 + 3 + A_SB) with (tk / 8 + 2147450883) in SHT3 by (unfold A_SB; lia).
pose proof (munch_refl [(tk, tk + 72)] mr2) as MU.
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
stash Himg_t2. clear Ld.
lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) => replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
step.
asan_chkB.
clear SHT3.
stepz.
do 3 step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ mr2 mc, WMc : wmono asegs mr2 mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _ |- _ =>
evt_done5;
destruct (PE_INV_A_tokw1 HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo mr2 mc md A B ts1
cb nb pj sv errv co (TS (Z_to_bv 64 0) stpos (Z_to_bv 64 co) err ucs high quote) STC INV2 MUc WMc MIc TOKc ltac:(cbn [pf_len]; lia) eq_refl) as [INV3 PBT3];
assert (AGp : agree_on asegs (t_pbs ts1) mr2 mc);
[ eapply (agree_wtqA HIx) with (ts := ts1); [exact STC | exact (proj1 (proj2 INV2)) | exact MUc | exact WMc
| apply Forall_cons; [left; left; cbn [fst snd pf_tk]; lia | apply Forall_nil] |];
intros a n Hin; assert (HinL : In (a, n) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts1 ++ LM)) by (unfold pe_blocksA, tstate_blocks; apply in_or_app; left; apply in_or_app; left; apply in_or_app; left; exact Hin);
split; [exact HinL|];
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ (proj1 (proj2 INV2))) as ND; unfold pe_blocksA in ND; rewrite <- app_assoc in ND; split;
[ intros ->; refine (nodup_app_ne _ _ _ _ _ _ ND _ _ eq_refl); [unfold tstate_blocks; apply in_or_app; left; exact Hin | left; reflexivity]
| intros ->; refine (nodup_app_ne _ _ _ _ _ _ ND _ _ eq_refl); [unfold tstate_blocks; apply in_or_app; left; exact Hin | right; left; reflexivity] ] |];
unstash Kredo; eapply (Kredo mc); [exact INV3 | exact (PBT3 _ PBK2) | exact (pbufc_agreeA _ _ _ _ _ _ PBC2 AGp (incl_refl _))]
end end.
Qed.

Lemma start_bool_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet)
(gp t0 a1 a2 a5 a6 a7 s3 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_start ->

(forall m' a0' a1' a2' a3' a4',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md A B
(ts_set_x (ts_lvl ts (TL ST_boolean (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) (t_co ts) (TS (ts_isd (t_x ts)) (Z_to_bv 64 0) (ts_choff (t_x ts)) (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))) cb nb pj sv errv ->
PBOK m' (ts_set_x (ts_lvl ts (TL ST_boolean (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) (t_co ts) (TS (ts_isd (t_x ts)) (Z_to_bv 64 0) (ts_choff (t_x ts)) (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))) 0 ->
pbufc asegs m' (t_pbs ts) (t_pb ts) [] ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa APE_REDO (t_co ts) gp t0 a0' a1' a2' a3' a4' a5 a6 a7 s3 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc m')) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa 0x95690 (t_co ts) gp t0 (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) a1 a2 (Z_to_bv 64 (q / 8 + 4 * Z.of_nat (t_depth ts) + A_SB)) (Z_to_bv 64 0) a5 a6 a7 s3 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc m).
Proof.
intros until fc. intros STC INV Hl Hst Kredo. pose proof INV as INV0. pe_openA STC INV.
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
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 1 HP INtk ltac:(lia)) as SHT1.
replace (tk / 8 + 1 + A_SB) with (tk / 8 + 2147450881) in SHT1 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 1 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT1c & SEPT1q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 1 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT1t & _).
cbn [hl_sb A4L] in SEPT1c, SEPT1q, SEPT1t. assert (EQx : tk / 8 + A_SB + 1 = tk / 8 + 2147450881) by (unfold A_SB; lia). rewrite EQx in SEPT1c, SEPT1q, SEPT1t. clear EQx.
unfold APE_BREAK, APE_REDO, APE_OUT, APE_ERRMEM, APE_JTAB in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
assert (cs_tk_L : csep tk 72 bse (Z.of_nat 32)) by (unfold csep; clear - Hdtq HbseR; lia).
assert (cs_L_tk : csep bse 32 tk (Z.of_nat 72)) by (unfold csep; clear - Hdtq HbseR; lia).
assert (cs_T1_L : csep (tk / 8 + 2147450881) 1 bse (Z.of_nat 32)) by (unfold csep; clear - SEPT1q HbseR; lia).
clear Hdtq SEPT1q SEPT1t SEPT1c.
destruct (lvl_mode_start2 _ _ _ SS26 ltac:(rewrite <- Hst; exact Hmode)) as (Ec0 & Ehn0 & Ess). subst c0 hn0.
stash Himg_t. stash Himg_q. stash Kredo. clear PB REST TSK LV OBJ HPR BUD GAP SAVED FSH FF STR ERR SBin SHT SHQ4.
reenterA asegs A4L HIx asegs_wx HP.
replace (q + 32 * Z.of_nat depth) with bse by lia.
step.
step. if_true.
asan_rechkB.
clear SHQ.
step.
stepz.
step.
asan_chkB.
step. step.

set (l1 := TL ST_boolean (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, Lc : rw_cells asegs mc bse _ |- _ =>
pose proof MUc as MUc'; pose proof Lc as Lc'; rewrite Hbse in MUc', Lc';
destruct (PE_INV_A_lvl_write HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m mc md A B ts0
cb nb pj sv errv l ST_boolean (tl_ss l) CNone false CNone STC INV0 Hl MUc' WMc MIc TOKc Lc' Hmode
ltac:(rewrite Ess; vm_compute; reflexivity) ltac:(unfold ST_boolean; lia) SS26 (or_introl eq_refl)
ltac:(rewrite Hst; vm_compute; reflexivity)) as [INV1 _]; clear MUc' Lc'
end end.
set (ts1 := ts_lvl ts0 l1) in *.
eapply (pe_pbreset HIx GA GA_pres (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo _ md A B ts1 cb nb pj sv errv);
[exact STC | exact INV1 | rewrite unsigned_lit by lia; reflexivity |].
intros mr2 a1' a2' a3' a4' INV2 PBK2 PBC2.
cbn [pf_spf] in *. unfold A_TP in *.
repeat match goal with H : rw_cells asegs _ _ _ |- _ => clear H | H : ro_cells asegs _ _ _ |- _ => clear H | H : munch _ _ _ |- _ => clear H | H : wmono asegs _ _ |- _ => clear H | H : mem_inv asegs _ |- _ => clear H end.
clear Htal Htlo Hthi Hqal Hqlo Hqhi Hqtk INtk INq INV0 INV1 HP cs_tk_L cs_L_tk cs_T1_L.
assert (Hl1 : nth_error (t_levels ts1) (t_depth ts1) = Some l1) by (unfold ts1, ts_lvl, ts0; cbn [t_levels t_depth]; apply nth_error_lupd_eq; apply nth_error_Some; rewrite Hl; discriminate).
reopen_inv INV2 ts1 ts0 (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 tk mxd depth l1 Hl1 bse Hbse mr2.
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t2.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 3 HP INtk ltac:(lia)) as SHT3.
replace (tk / 8 + 3 + A_SB) with (tk / 8 + 2147450883) in SHT3 by (unfold A_SB; lia).
pose proof (munch_refl [(tk, tk + 72)] mr2) as MU.
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
stash Himg_t2. clear Ld.
lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) => replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
step.
asan_chkB.
clear SHT3.
stepz.
do 3 step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ mr2 mc, WMc : wmono asegs mr2 mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _ |- _ =>
evt_done5;
destruct (PE_INV_A_tokw1 HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo mr2 mc md A B ts1
cb nb pj sv errv co (TS isd (Z_to_bv 64 0) (Z_to_bv 64 co) err ucs high quote) STC INV2 MUc WMc MIc TOKc ltac:(cbn [pf_len]; lia) eq_refl) as [INV3 PBT3];
assert (AGp : agree_on asegs (t_pbs ts1) mr2 mc);
[ eapply (agree_wtqA HIx) with (ts := ts1); [exact STC | exact (proj1 (proj2 INV2)) | exact MUc | exact WMc
| apply Forall_cons; [left; left; cbn [fst snd pf_tk]; lia | apply Forall_nil] |];
intros a n Hin; assert (HinL : In (a, n) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts1 ++ LM)) by (unfold pe_blocksA, tstate_blocks; apply in_or_app; left; apply in_or_app; left; apply in_or_app; left; exact Hin);
split; [exact HinL|];
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ (proj1 (proj2 INV2))) as ND; unfold pe_blocksA in ND; rewrite <- app_assoc in ND; split;
[ intros ->; refine (nodup_app_ne _ _ _ _ _ _ ND _ _ eq_refl); [unfold tstate_blocks; apply in_or_app; left; exact Hin | left; reflexivity]
| intros ->; refine (nodup_app_ne _ _ _ _ _ _ ND _ _ eq_refl); [unfold tstate_blocks; apply in_or_app; left; exact Hin | right; left; reflexivity] ] |];
unstash Kredo; eapply (Kredo mc); [exact INV3 | exact (PBT3 _ PBK2) | exact (pbufc_agreeA _ _ _ _ _ _ PBC2 AGp (incl_refl _))]
end end.
Qed.

Lemma start_null_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet)
(gp t0 a1 a2 a5 a6 a7 s3 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_start ->

(forall m' a0' a1' a2' a3' a4',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md A B
(ts_set_x (ts_lvl ts (TL ST_null (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) (t_co ts) (TS (ts_isd (t_x ts)) (Z_to_bv 64 0) (ts_choff (t_x ts)) (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))) cb nb pj sv errv ->
PBOK m' (ts_set_x (ts_lvl ts (TL ST_null (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) (t_co ts) (TS (ts_isd (t_x ts)) (Z_to_bv 64 0) (ts_choff (t_x ts)) (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))) 0 ->
pbufc asegs m' (t_pbs ts) (t_pb ts) [] ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa APE_REDO (t_co ts) gp t0 a0' a1' a2' a3' a4' a5 a6 a7 s3 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc m')) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa 0x95b04 (t_co ts) gp t0 (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) a1 a2 (Z_to_bv 64 (q / 8 + 4 * Z.of_nat (t_depth ts) + A_SB)) (Z_to_bv 64 0) a5 a6 a7 s3 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc m).
Proof.
intros until fc. intros STC INV Hl Hst Kredo. pose proof INV as INV0. pe_openA STC INV.
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
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 1 HP INtk ltac:(lia)) as SHT1.
replace (tk / 8 + 1 + A_SB) with (tk / 8 + 2147450881) in SHT1 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 1 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT1c & SEPT1q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 1 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT1t & _).
cbn [hl_sb A4L] in SEPT1c, SEPT1q, SEPT1t. assert (EQx : tk / 8 + A_SB + 1 = tk / 8 + 2147450881) by (unfold A_SB; lia). rewrite EQx in SEPT1c, SEPT1q, SEPT1t. clear EQx.
unfold APE_BREAK, APE_REDO, APE_OUT, APE_ERRMEM, APE_JTAB in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
assert (cs_tk_L : csep tk 72 bse (Z.of_nat 32)) by (unfold csep; clear - Hdtq HbseR; lia).
assert (cs_L_tk : csep bse 32 tk (Z.of_nat 72)) by (unfold csep; clear - Hdtq HbseR; lia).
assert (cs_T1_L : csep (tk / 8 + 2147450881) 1 bse (Z.of_nat 32)) by (unfold csep; clear - SEPT1q HbseR; lia).
clear Hdtq SEPT1q SEPT1t SEPT1c.
destruct (lvl_mode_start2 _ _ _ SS26 ltac:(rewrite <- Hst; exact Hmode)) as (Ec0 & Ehn0 & Ess). subst c0 hn0.
stash Himg_t. stash Himg_q. stash Kredo. clear PB REST TSK LV OBJ HPR BUD GAP SAVED FSH FF STR ERR SBin SHT SHQ4.
reenterA asegs A4L HIx asegs_wx HP.
replace (q + 32 * Z.of_nat depth) with bse by lia.
step.
step. if_true.
asan_rechkB.
clear SHQ.
step.
stepz.
step.
asan_chkB.
step. step.

set (l1 := TL ST_null (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, Lc : rw_cells asegs mc bse _ |- _ =>
pose proof MUc as MUc'; pose proof Lc as Lc'; rewrite Hbse in MUc', Lc';
destruct (PE_INV_A_lvl_write HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m mc md A B ts0
cb nb pj sv errv l ST_null (tl_ss l) CNone false CNone STC INV0 Hl MUc' WMc MIc TOKc Lc' Hmode
ltac:(rewrite Ess; vm_compute; reflexivity) ltac:(unfold ST_null; lia) SS26 (or_introl eq_refl)
ltac:(rewrite Hst; vm_compute; reflexivity)) as [INV1 _]; clear MUc' Lc'
end end.
set (ts1 := ts_lvl ts0 l1) in *.
eapply (pe_pbreset HIx GA GA_pres (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo _ md A B ts1 cb nb pj sv errv);
[exact STC | exact INV1 | rewrite unsigned_lit by lia; reflexivity |].
intros mr2 a1' a2' a3' a4' INV2 PBK2 PBC2.
cbn [pf_spf] in *. unfold A_TP in *.
repeat match goal with H : rw_cells asegs _ _ _ |- _ => clear H | H : ro_cells asegs _ _ _ |- _ => clear H | H : munch _ _ _ |- _ => clear H | H : wmono asegs _ _ |- _ => clear H | H : mem_inv asegs _ |- _ => clear H end.
clear Htal Htlo Hthi Hqal Hqlo Hqhi Hqtk INtk INq INV0 INV1 HP cs_tk_L cs_L_tk cs_T1_L.
assert (Hl1 : nth_error (t_levels ts1) (t_depth ts1) = Some l1) by (unfold ts1, ts_lvl, ts0; cbn [t_levels t_depth]; apply nth_error_lupd_eq; apply nth_error_Some; rewrite Hl; discriminate).
reopen_inv INV2 ts1 ts0 (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 tk mxd depth l1 Hl1 bse Hbse mr2.
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t2.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 3 HP INtk ltac:(lia)) as SHT3.
replace (tk / 8 + 3 + A_SB) with (tk / 8 + 2147450883) in SHT3 by (unfold A_SB; lia).
pose proof (munch_refl [(tk, tk + 72)] mr2) as MU.
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
stash Himg_t2. clear Ld.
lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) => replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
step.
asan_chkB.
clear SHT3.
stepz.
do 3 step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ mr2 mc, WMc : wmono asegs mr2 mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _ |- _ =>
evt_done5;
destruct (PE_INV_A_tokw1 HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo mr2 mc md A B ts1
cb nb pj sv errv co (TS isd (Z_to_bv 64 0) (Z_to_bv 64 co) err ucs high quote) STC INV2 MUc WMc MIc TOKc ltac:(cbn [pf_len]; lia) eq_refl) as [INV3 PBT3];
assert (AGp : agree_on asegs (t_pbs ts1) mr2 mc);
[ eapply (agree_wtqA HIx) with (ts := ts1); [exact STC | exact (proj1 (proj2 INV2)) | exact MUc | exact WMc
| apply Forall_cons; [left; left; cbn [fst snd pf_tk]; lia | apply Forall_nil] |];
intros a n Hin; assert (HinL : In (a, n) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts1 ++ LM)) by (unfold pe_blocksA, tstate_blocks; apply in_or_app; left; apply in_or_app; left; apply in_or_app; left; exact Hin);
split; [exact HinL|];
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ (proj1 (proj2 INV2))) as ND; unfold pe_blocksA in ND; rewrite <- app_assoc in ND; split;
[ intros ->; refine (nodup_app_ne _ _ _ _ _ _ ND _ _ eq_refl); [unfold tstate_blocks; apply in_or_app; left; exact Hin | left; reflexivity]
| intros ->; refine (nodup_app_ne _ _ _ _ _ _ ND _ _ eq_refl); [unfold tstate_blocks; apply in_or_app; left; exact Hin | right; left; reflexivity] ] |];
unstash Kredo; eapply (Kredo mc); [exact INV3 | exact (PBT3 _ PBK2) | exact (pbufc_agreeA _ _ _ _ _ _ PBC2 AGp (incl_refl _))]
end end.
Qed.

Lemma start_inf_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet)
(gp t0 a1 a2 a5 a6 a7 s3 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_start ->

(forall m' a0' a1' a2' a3' a4',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md A B
(ts_set_x (ts_lvl ts (TL ST_inf (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) (t_co ts) (TS (ts_isd (t_x ts)) (Z_to_bv 64 0) (ts_choff (t_x ts)) (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))) cb nb pj sv errv ->
PBOK m' (ts_set_x (ts_lvl ts (TL ST_inf (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) (t_co ts) (TS (ts_isd (t_x ts)) (Z_to_bv 64 0) (ts_choff (t_x ts)) (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))) 0 ->
pbufc asegs m' (t_pbs ts) (t_pb ts) [] ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa APE_REDO (t_co ts) gp t0 a0' a1' a2' a3' a4' a5 a6 a7 s3 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc m')) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa 0x95b64 (t_co ts) gp t0 (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) a1 a2 (Z_to_bv 64 (q / 8 + 4 * Z.of_nat (t_depth ts) + A_SB)) (Z_to_bv 64 0) a5 a6 a7 s3 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc m).
Proof.
intros until fc. intros STC INV Hl Hst Kredo. pose proof INV as INV0. pe_openA STC INV.
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
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 1 HP INtk ltac:(lia)) as SHT1.
replace (tk / 8 + 1 + A_SB) with (tk / 8 + 2147450881) in SHT1 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 1 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT1c & SEPT1q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 1 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT1t & _).
cbn [hl_sb A4L] in SEPT1c, SEPT1q, SEPT1t. assert (EQx : tk / 8 + A_SB + 1 = tk / 8 + 2147450881) by (unfold A_SB; lia). rewrite EQx in SEPT1c, SEPT1q, SEPT1t. clear EQx.
unfold APE_BREAK, APE_REDO, APE_OUT, APE_ERRMEM, APE_JTAB in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
assert (cs_tk_L : csep tk 72 bse (Z.of_nat 32)) by (unfold csep; clear - Hdtq HbseR; lia).
assert (cs_L_tk : csep bse 32 tk (Z.of_nat 72)) by (unfold csep; clear - Hdtq HbseR; lia).
assert (cs_T1_L : csep (tk / 8 + 2147450881) 1 bse (Z.of_nat 32)) by (unfold csep; clear - SEPT1q HbseR; lia).
clear Hdtq SEPT1q SEPT1t SEPT1c.
destruct (lvl_mode_start2 _ _ _ SS26 ltac:(rewrite <- Hst; exact Hmode)) as (Ec0 & Ehn0 & Ess). subst c0 hn0.
stash Himg_t. stash Himg_q. stash Kredo. clear PB REST TSK LV OBJ HPR BUD GAP SAVED FSH FF STR ERR SBin SHT SHQ4.
reenterA asegs A4L HIx asegs_wx HP.
replace (q + 32 * Z.of_nat depth) with bse by lia.
step.
step. if_true.
asan_rechkB.
clear SHQ.
step.
stepz.
step.
asan_chkB.
step. step.

set (l1 := TL ST_inf (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, Lc : rw_cells asegs mc bse _ |- _ =>
pose proof MUc as MUc'; pose proof Lc as Lc'; rewrite Hbse in MUc', Lc';
destruct (PE_INV_A_lvl_write HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m mc md A B ts0
cb nb pj sv errv l ST_inf (tl_ss l) CNone false CNone STC INV0 Hl MUc' WMc MIc TOKc Lc' Hmode
ltac:(rewrite Ess; vm_compute; reflexivity) ltac:(unfold ST_inf; lia) SS26 (or_introl eq_refl)
ltac:(rewrite Hst; vm_compute; reflexivity)) as [INV1 _]; clear MUc' Lc'
end end.
set (ts1 := ts_lvl ts0 l1) in *.
eapply (pe_pbreset HIx GA GA_pres (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo _ md A B ts1 cb nb pj sv errv);
[exact STC | exact INV1 | rewrite unsigned_lit by lia; reflexivity |].
intros mr2 a1' a2' a3' a4' INV2 PBK2 PBC2.
cbn [pf_spf] in *. unfold A_TP in *.
repeat match goal with H : rw_cells asegs _ _ _ |- _ => clear H | H : ro_cells asegs _ _ _ |- _ => clear H | H : munch _ _ _ |- _ => clear H | H : wmono asegs _ _ |- _ => clear H | H : mem_inv asegs _ |- _ => clear H end.
clear Htal Htlo Hthi Hqal Hqlo Hqhi Hqtk INtk INq INV0 INV1 HP cs_tk_L cs_L_tk cs_T1_L.
assert (Hl1 : nth_error (t_levels ts1) (t_depth ts1) = Some l1) by (unfold ts1, ts_lvl, ts0; cbn [t_levels t_depth]; apply nth_error_lupd_eq; apply nth_error_Some; rewrite Hl; discriminate).
reopen_inv INV2 ts1 ts0 (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 tk mxd depth l1 Hl1 bse Hbse mr2.
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t2.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 3 HP INtk ltac:(lia)) as SHT3.
replace (tk / 8 + 3 + A_SB) with (tk / 8 + 2147450883) in SHT3 by (unfold A_SB; lia).
pose proof (munch_refl [(tk, tk + 72)] mr2) as MU.
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
stash Himg_t2. clear Ld.
lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) => replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
step.
asan_chkB.
clear SHT3.
stepz.
do 3 step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ mr2 mc, WMc : wmono asegs mr2 mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _ |- _ =>
evt_done5;
destruct (PE_INV_A_tokw1 HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo mr2 mc md A B ts1
cb nb pj sv errv co (TS isd (Z_to_bv 64 0) (Z_to_bv 64 co) err ucs high quote) STC INV2 MUc WMc MIc TOKc ltac:(cbn [pf_len]; lia) eq_refl) as [INV3 PBT3];
assert (AGp : agree_on asegs (t_pbs ts1) mr2 mc);
[ eapply (agree_wtqA HIx) with (ts := ts1); [exact STC | exact (proj1 (proj2 INV2)) | exact MUc | exact WMc
| apply Forall_cons; [left; left; cbn [fst snd pf_tk]; lia | apply Forall_nil] |];
intros a n Hin; assert (HinL : In (a, n) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts1 ++ LM)) by (unfold pe_blocksA, tstate_blocks; apply in_or_app; left; apply in_or_app; left; apply in_or_app; left; exact Hin);
split; [exact HinL|];
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ (proj1 (proj2 INV2))) as ND; unfold pe_blocksA in ND; rewrite <- app_assoc in ND; split;
[ intros ->; refine (nodup_app_ne _ _ _ _ _ _ ND _ _ eq_refl); [unfold tstate_blocks; apply in_or_app; left; exact Hin | left; reflexivity]
| intros ->; refine (nodup_app_ne _ _ _ _ _ _ ND _ _ eq_refl); [unfold tstate_blocks; apply in_or_app; left; exact Hin | right; left; reflexivity] ] |];
unstash Kredo; eapply (Kredo mc); [exact INV3 | exact (PBT3 _ PBK2) | exact (pbufc_agreeA _ _ _ _ _ _ PBC2 AGp (incl_refl _))]
end end.
Qed.
End PeSStartTA.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYZ0.Mq3.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section PeSSescJA.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_outside : forall m m' W, GA m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= hl_img_lo A4H \/ hl_img_hi A4H <= fst iv) W -> GA m'.
Hypothesis GA_pres : forall LB SP m m', heap_pres A4H LB SP m m' -> GA m -> GA m'.

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

Lemma sesc_join_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP : Z)
(gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv -> PBOK m ts kP ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_string_escape ->
(forall c hn, lvl_mode (tl_st l) (tl_ss l) = Some (c, hn) -> lvl_mode (tl_ss l) (tl_ss l) = Some (c, hn)) ->
zin (tl_ss l) [ST_array_add; ST_ovadd] = false ->

(forall m' a0' a1' a2' a3',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md A B (ts_lvl ts (TL (tl_ss l) (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) cb nb pj sv errv ->
PBOK m' (ts_lvl ts (TL (tl_ss l) (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) kP ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa APE_BREAK (t_co ts) gp t0 t1 t2 a0' a1' a2' a3' a4 a5 a6 a7 s5 (Z_to_bv 64 (pf_tk pf + 56)) (Z_to_bv 64 (pa_F pa + 64)) F fc m')) ->
AJ5 A4L HIx A T md (pe_msA asegs pf pa 0x971a4 (t_co ts) gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 (Z_to_bv 64 (pf_tk pf + 56)) (Z_to_bv 64 (pa_F pa + 64)) F fc m).
Proof.
intros until fc. intros STC INV PBK Hl Hst HMODE Hzss Kbreak. pose proof INV as INV0. pe_openA STC INV.
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
unfold APE_BREAK, APE_REDO, APE_OUT, APE_ERRMEM, APE_ERRST, APE_JTAB in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
assert (cs_tk_L : csep tk 72 bse (Z.of_nat 32)) by (unfold csep; clear - Hdtq HbseR; lia).
assert (cs_L_tk : csep bse 32 tk (Z.of_nat 72)) by (unfold csep; clear - Hdtq HbseR; lia).
clear Hdtq SEPQ0c SEPQ0q SEPQ0t SEPT7c SEPT7q SEPT7t SEPT2c SEPT2q SEPT2t.
stash Himg_t. stash Himg_q. stash Kbreak. clear PB REST TSK LV OBJ HPR BUD GAP SAVED FSH FF STR ERR SBin SHT SHQ SHQ4.
reenterA asegs A4L HIx asegs_wx HP.
step.
asan_rechkA.
asan_rechkM 1.
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
asan_chkM 1.
norm_sx32.
stepz.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, Lc : rw_cells asegs mc bse _ |- _ =>
evt_done5; subst bse;
destruct (PE_INV_A_lvl_writeG HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m mc md A B ts0
cb nb pj sv errv l (tl_ss l) (tl_ss l) c0 hn0 c0 STC INV0 Hl MUc WMc MIc TOKc Lc Hmode (HMODE _ _ Hmode) SS26 SS26 (or_introl eq_refl)
ltac:(left; rewrite Hst, Hzss; reflexivity)) as [INV3 PBK3];
unstash Kbreak; eapply (Kbreak mc); [exact INV3 | exact (PBK3 kP PBK)]
end end.
Qed.

Lemma sesc_joinq_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP : Z)
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv -> PBOK m ts kP ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_string_escape ->
(forall c hn, lvl_mode (tl_st l) (tl_ss l) = Some (c, hn) -> lvl_mode (tl_ss l) (tl_ss l) = Some (c, hn)) ->
zin (tl_ss l) [ST_array_add; ST_ovadd] = false ->

(forall m' a0' a1' a2' a3',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md A B (ts_lvl ts (TL (tl_ss l) (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) cb nb pj sv errv ->
PBOK m' (ts_lvl ts (TL (tl_ss l) (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) kP ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa APE_BREAK (t_co ts) gp t0 t1 t2 a0' a1' a2' a3' a4 a5 a6 a7 s5 (Z_to_bv 64 (pf_tk pf + 56)) (Z_to_bv 64 (pa_F pa + 64)) F fc m')) ->
AJ5 A4L HIx A T md (Q1Y6.Mq2.pe_msE pf pa 0x96d60 x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (pf_tk pf / 8 + SB2)) (Z_to_bv 64 (pf_tk pf + 20)) s5 (Z_to_bv 64 (pf_tk pf + 36)) (Z_to_bv 64 (pf_tk pf + 32)) (Z_to_bv 64 (pa_F pa)) (Z_to_bv 64 (pf_tk pf + 56)) (Z_to_bv 64 (pf_sb pf + t_co ts)) t3 t4 t5 t6 F fc m).
Proof.
intros until fc. intros STC INV PBK Hl Hst HMODE Hzss Kbreak. pose proof INV as INV0. pe_openA STC INV.
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
unfold APE_BREAK, APE_REDO, APE_OUT, APE_ERRMEM, APE_ERRST, APE_JTAB in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
assert (cs_tk_L : csep tk 72 bse (Z.of_nat 32)) by (unfold csep; clear - Hdtq HbseR; lia).
assert (cs_L_tk : csep bse 32 tk (Z.of_nat 72)) by (unfold csep; clear - Hdtq HbseR; lia).
clear Hdtq SEPQ0c SEPQ0q SEPQ0t SEPT7c SEPT7q SEPT7t SEPT2c SEPT2q SEPT2t.
stash Himg_t. stash Himg_q. stash Kbreak. clear PB REST TSK LV OBJ HPR BUD GAP SAVED FSH FF STR ERR SBin SHT SHQ SHQ4.
reenterA asegs A4L HIx asegs_wx HP.
step.
asan_rechkA.
asan_rechkM 6.
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
asan_chkM 1.
norm_sx32.
stepz.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, Lc : rw_cells asegs mc bse _ |- _ =>
evt_done5; subst bse;
destruct (PE_INV_A_lvl_writeG HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m mc md A B ts0
cb nb pj sv errv l (tl_ss l) (tl_ss l) c0 hn0 c0 STC INV0 Hl MUc WMc MIc TOKc Lc Hmode (HMODE _ _ Hmode) SS26 SS26 (or_introl eq_refl)
ltac:(left; rewrite Hst, Hzss; reflexivity)) as [INV3 PBK3];
unstash Kbreak; eapply (Kbreak mc); [exact INV3 | exact (PBK3 kP PBK)]
end end.
Qed.
End PeSSescJA.
End RC__1.
