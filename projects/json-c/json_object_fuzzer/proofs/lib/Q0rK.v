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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXfU.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2Sr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2Sr.Mq0.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QVob.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QMmN.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QMmN. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qw5U.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qw5U.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QMgr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QMgr. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q63E.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q63E.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qt1H.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qt1H.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac QlEo_c1.solve_load ::= QXup.mkr__solve_load_3. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEUF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEUF.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QMgr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QMgr.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section PeSOfieldA.
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

Lemma ofl_flush_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (co0 k0 : Z)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kB : nat)
(x1 gp t0 t1 t2 a0 a1 a2 a4 a5 a6 a7 s3 s5 s6 s7 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
PBOKat m ts (co0 + k0) -> k0 <= 0 -> BOK pf pa ts B kB ->
0 <= co0 < t_co ts -> t_co ts <= pf_len pf ->
(forall m' md' A' B' pbs' errv' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' s11' t4' t6' F' fc',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' (ts_pbs ts pbs') cb nb pj sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msO asegs pf pa APE_OUT x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' (Z_to_bv 64 (pf_tk pf + 56)) s11' t4' t6' F' fc' m')) ->
(forall m' md' A' B' pbs' errv' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' s11' t4' t6' F' fc',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' (ts_pbs ts pbs') cb nb pj sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msO asegs pf pa APE_ERRMEM x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' (Z_to_bv 64 (pf_tk pf + 56)) s11' t4' t6' F' fc' m')) ->
AJ5 A4L HIx A T md
(Q1Y6.Mq2.pe_msE pf pa 0x988ec x1 gp t0 t1 t2 a0 a1 a2 (Z_to_bv 64 (pf_tk pf + 8)) a4 a5 a6 a7 s3 (Z_to_bv 64 (t_co ts - co0 - 1)) s5 s6 s7 (Z_to_bv 64 (pa_F pa)) s10 (Z_to_bv 64 (pf_sb pf + co0)) t3 t4 t5 t6 F fc m).
Proof.
intros until fc. intros STC BSL INV PBK K0 BK Hco0 Hcol Kout Kerr16. pose proof INV as INV0.
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
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 1 HP INtk ltac:(lia)) as SHT1.
replace (tk / 8 + 1 + A_SB) with (tk / 8 + 2147450881) in SHT1 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 1 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT1c & SEPT1q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 1 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT1t & _).
cbn [hl_sb A4L] in SEPT1c, SEPT1q, SEPT1t. assert (EQx : tk / 8 + A_SB + 1 = tk / 8 + 2147450881) by (unfold A_SB; lia). rewrite EQx in SEPT1c, SEPT1q, SEPT1t. clear EQx.
unfold APE_OUT, APE_ERRMEM in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
clear PB TSK REST LV SEPT1c SEPT1q SEPT1t.
reenterA asegs A4L HIx asegs_wx HP.
asan_chkA.
step.
step.
norm_w32. replace (co - co0 - 1 + 1) with (co - co0) by lia.
step. step.
evt_done5.
eapply (pe_memappend_pk HIx GA GA_pres MAPP (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m md A B ts0 cb nb pj sv errv T co0 k0 (co - co0));
[exact STC | exact BSL | exact INV0 | exact PBK | exact K0 | lia | lia | cbn [t_co ts0]; lia | cbn [pf_len]; lia | cbn [pf_len]; lia | exact BK | rewrite unsigned_lit by lia; reflexivity |].
intros m2 md2 A2 B2 pbs2 errv2 r w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 F2 fc2 INV2 OUT2 FS2 FRM2.
cbn [pf_spf] in *. unfold A_TP in *.
clear TOK SLOTS SHT1 Htal Htlo Hthi Himg_t Himg_q Hqal Hqlo Hqhi INtk INq HP INV0 PBK BK.
pose proof INV2 as [CORE2 REST2]. destruct CORE2 as (_ & _ & _ & _ & _ & _ & _ & _ & FR2). pose proof (proj1 REST2) as HP.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 (ts_pbs ts0 pbs2))) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 4 HP INtk ltac:(lia)) as SHT4.
replace (tk / 8 + 4 + A_SB) with (tk / 8 + 2147450884) in SHT4 by (unfold A_SB; lia).
pose proof FR2 as (SLOTS & _). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS. cbn [pf_tk pf_spf pf_lenr pa_F pa_sp0 pa_oldloc pa_newloc] in SLOTS. unfold shA in SLOTS. a4l. unfold SB2, SB4, SB7, SB8 in SLOTS.
clear REST2 FR2.
reenterA asegs A4L HIx asegs_wx HP.
destruct OUT2 as [(-> & _ & _) | [-> Epbs2]].
- do 7 step.
if_truex.
evt_done5.
eapply (Kout m2 md2 A2 B2 pbs2 errv2); [exact INV2 | exact FS2 | exact FRM2].
- replace (Z_to_bv 64 (2^64 - 1)) with (Z_to_bv 64 (-1)) by (apply bv_eq; vm_compute; reflexivity).
do 7 step.
if_false.
step.
step.
rewrite ?sxb_zero, ?zxb_zero.
step.
if_true.
evt_done5.
eapply (Kerr16 m2 md2 A2 B2 pbs2 errv2); [exact INV2 | exact FS2 | exact FRM2].
Qed.

Lemma ofl_eof_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel) (co0 k0 : Z)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kB : nat)
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s6 s7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
PBOKat m ts (co0 + k0) -> k0 <= 0 -> BOK pf pa ts B kB ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_ofield ->
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
(Q1Y6.Mq2.pe_msE pf pa 0x986f0 x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 (Z_to_bv 64 (pf_len pf - co0 - 1)) (Z_to_bv 64 (Z.of_nat (t_depth ts))) s6 s7 (Z_to_bv 64 (pa_F pa)) (Z_to_bv 64 q)
(Z_to_bv 64 (pf_sb pf + co0)) t3 t4 t5 t6 F fc m).
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
step. step.

lazymatch goal with |- evt _ _ (MS ?R ?FF _ ?fcc None ?mm ?rom) =>
assert (TAILE : forall a1v a2v s8v, s8v = Z_to_bv 64 Ff ->
evt asegs (AJ5e A4L HIx A T md) (MS (bvmap_set 11 a1v (bvmap_set 12 a2v (bvmap_set 24 s8v (bvmap_set 13 (Z_to_bv 64 1) R)))) FF (Z_to_bv 64 0x988dc) fcc None mm rom)) end.
{ intros a1v a2v s8v ->.
asan_rechkA.
stepz.
step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _ |- _ =>
evt_done5;
destruct (PE_INV_A_tokw1 HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m mc md A B ts0
cb nb pj sv errv len (tx_err (t_x ts0) (Z_to_bv 64 1)) STC INV0 MUc WMc MIc TOKc ltac:(cbn [pf_len]; lia) eq_refl) as [INVe PBKe];
eapply (ofl_flush_A (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo mc md A B
(ts_set_x ts0 len (tx_err (t_x ts0) (Z_to_bv 64 1))) co0 k0 cb nb pj sv errv T kB);
[exact STC | exact BSL | exact INVe | exact (PBKe _ PBK) | exact K0 | exact (BOK_set_x _ _ ts0 B kB len _ ltac:(cbn [t_co ts0]; lia) BK) | cbn [t_co ts_set_x]; lia | cbn [t_co ts_set_x pf_len]; lia
| intros; eapply Kout; eassumption
| intros; eapply Kerr16; eassumption]
end end. }
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
apply (TAILE _ _ _ eq_refl).
- if_truex.
step. step.
apply (TAILE _ _ _ eq_refl).
Qed.

Lemma ofl_bslash_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel) (co0 k0 : Z)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (nB : nat)
(x1 gp t0 t1 t2 a0 a1 a2 a4 a5 a6 a7 s3 s5 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
PBOKat m ts (co0 + k0) -> k0 <= 0 -> BOK pf pa ts B (S (Z.to_nat (16 * Z.max 0 (pf_len pf) + 8192) + nB)) ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_ofield ->
0 <= co0 <= t_co ts -> t_co ts < pf_len pf ->

(forall m' md' A' B' pbs' errv' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' F' fc',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' (ts_lvl (ts_pbs ts pbs') (TL ST_string_escape ST_ofield (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) cb nb pj sv errv' ->
PBOK m' (ts_lvl (ts_pbs ts pbs') (TL ST_string_escape ST_ofield (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) k0 ->
BOK pf pa (ts_lvl (ts_pbs ts pbs') (TL ST_string_escape ST_ofield (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) B' nB ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msA asegs pf pa APE_BREAK (t_co ts) gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' (Z_to_bv 64 (pf_tk pf + 56)) (Z_to_bv 64 (pa_F pa + 64)) F' fc' m')) ->

(forall m' md' A' B' errv' x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s10' s11' t3' t4' t5' t6' F' fc',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' ts cb nb pj sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(Q1Y6.Mq2.pe_msE pf pa APE_ERR2 x1' gp' t0' t1' t2' (Z_to_bv 64 16) a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s10' s11' t3' t4' t5' t6' F' fc' m')) ->
AJ5 A4L HIx A T md
(Q1Y6.Mq2.pe_msE pf pa 0x96f20 x1 gp t0 t1 t2 a0 a1 a2 (Z_to_bv 64 (pf_tk pf + 8)) a4 a5 a6 a7 s3 (Z_to_bv 64 (t_co ts - co0)) s5 (Z_to_bv 64 (pf_sb pf + t_co ts)) (Z_to_bv 64 (pf_tk pf + 32)) (Z_to_bv 64 (pa_F pa)) s10
(Z_to_bv 64 (pf_sb pf + co0)) t3 t4 t5 t6 F fc m).
Proof.
intros until fc. intros STC BSL INV PBK K0 BK Hl Hst Hco0 Hco Kbreak Kerr16. pose proof INV as INV0.
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
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 1 HP INtk ltac:(lia)) as SHT1.
replace (tk / 8 + 1 + A_SB) with (tk / 8 + 2147450881) in SHT1 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 1 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT1c & SEPT1q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 1 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT1t & _).
cbn [hl_sb A4L] in SEPT1c, SEPT1q, SEPT1t. assert (EQx : tk / 8 + A_SB + 1 = tk / 8 + 2147450881) by (unfold A_SB; lia). rewrite EQx in SEPT1c, SEPT1q, SEPT1t. clear EQx.
unfold APE_BREAK, APE_ERR2 in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
clear PB TSK REST LV SEPT1c SEPT1q SEPT1t.
reenterA asegs A4L HIx asegs_wx HP.
asan_chkA.
step.
step. step. step.
evt_done5.
eapply (pe_memappend_pk HIx GA GA_pres MAPP (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m md A B ts0 cb nb pj sv errv T co0 k0 (co - co0));
[exact STC | exact BSL | exact INV0 | exact PBK | exact K0 | lia | lia | cbn [t_co ts0]; lia | cbn [pf_len]; lia | cbn [pf_len]; lia | exact BK | rewrite unsigned_lit by lia; reflexivity |].
intros m2 md2 A2 B2 pbs2 errv2 r w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 F2 fc2 INV2 OUT2 FS2 FRM2.
cbn [pf_spf] in *. unfold A_TP in *.
clear TOK SLOTS SHT1 Htal Htlo Hthi Himg_t Himg_q Hqal Hqlo Hqhi INtk INq HP INV0 PBK BK.
set (ts2 := ts_pbs ts0 pbs2) in *.
pose proof INV2 as INV2'. destruct INV2' as [CORE2 REST2].
destruct CORE2 as (_ & _ & _ & _ & TOK & _ & _ & TSK & FR).
pose proof REST2 as (HP & LV & _).
unfold ts2, ts_pbs, ts0 in TOK, TSK, LV. cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_tk pf_mxd pf_fl] in TOK, TSK, LV.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
unfold pe_frameA in FR. destruct FR as (SLOTS & _ & _ & _ & _). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in SLOTS.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts2)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * mxd) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts2)) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t2.
blk_factsA A4L HIx HP q (32 * mxd) Hqal Hqlo Hqhi Himg_q2.
pose proof (q_ne_tkA HIx _ _ _ _ _ _ _ _ _ _ HP) as Hqtk. cbn [pf_tk] in Hqtk.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ tk 72 q (32 * mxd) HP (in_or_app _ LM _ (or_introl INtk)) (in_or_app _ LM _ (or_introl INq)) ltac:(congruence)) as Hdtq.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs m2) as WM.
pose proof (LV depth l Hl) as LVd. pose proof LVd as (ST26 & SS26 & _ & Md).
rewrite Nat.ltb_irrefl, Nat.eqb_refl in Md. destruct Md as (c0 & hn0 & Hmode & CLS0 & NM0).
pose proof (TSK depth l Hl) as Ld. remember (q + 32 * Z.of_nat depth) as bse eqn:Hbse in Ld. unfold srec_cells in Ld.
assert (HbseR : q <= bse /\ bse + 32 <= q + (32 * mxd)) by (subst bse; lia).
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
shq_facts HP INq INtk q mxd tk (Z.of_nat depth) 0 SHQ0 SEPQ0c SEPQ0q SEPQ0t.
replace (q / 8 + 4 * (Z.of_nat depth) + 0 + A_SB) with (bse / 8 + 2147450880) in SHQ0 by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia).
assert (EQx : q / 8 + A_SB + (4 * (Z.of_nat depth) + 0) = bse / 8 + 2147450880) by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia). rewrite EQx in SEPQ0c, SEPQ0q, SEPQ0t. clear EQx.
unfold shA in *.
pose proof (munch_refl [(bse, bse + 32)] m2) as MU.
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
assert (cs_tk_L : csep tk 72 bse (Z.of_nat 32)) by (unfold csep; clear - Hdtq HbseR; lia).
assert (cs_L_tk : csep bse 32 tk (Z.of_nat 72)) by (unfold csep; clear - Hdtq HbseR; lia).
assert (cs_Q0_L : csep (bse / 8 + 2147450880) 1 bse (Z.of_nat 32)) by (unfold csep; clear - SEPQ0q HbseR; lia).
clear Hdtq SEPT7c SEPT7q SEPT7t SEPT2c SEPT2q SEPT2t SEPT4c SEPT4q SEPT4t SEPQ0c SEPQ0q SEPQ0t.
stash Himg_t2. stash Himg_q2. clear LV TSK.
reenterA asegs A4L HIx asegs_wx HP.
destruct OUT2 as [(-> & PBK2 & BK2) | [-> Epbs2]].
2:{ replace (Z_to_bv 64 (2^64 - 1)) with (Z_to_bv 64 (-1)) by (apply bv_eq; vm_compute; reflexivity).
do 4 step.
if_false.
step.
step.
step.
rewrite ?sxb_zero, ?zxb_zero.
step.
if_true.
step.
evt_done5.
eapply (Kerr16 m2 md2 A2 B2 errv2); [| exact FS2 | exact FRM2].
subst pbs2. exact INV2. }
do 4 step.
if_truex.
step.
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
step.
stepz.
asan_chkA.
step.
stepz.
step. step.
step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m2 mc, WMc : wmono asegs m2 mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, Lc : rw_cells asegs mc bse _ |- _ =>
evt_done5; subst bse;
destruct (PE_INV_A_lvl_write HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m2 mc md2 A2 B2 ts2
cb nb pj sv errv2 l ST_string_escape ST_ofield c0 hn0 c0 STC INV2 Hl MUc WMc MIc TOKc Lc Hmode
ltac:(destruct (ofield_mode _ _ _ SS26 ltac:(rewrite <- Hst; exact Hmode)) as [-> ->]; reflexivity)
ltac:(unfold ST_string_escape; lia) ltac:(unfold ST_ofield; lia) (or_introl eq_refl) ltac:(rewrite Hst; reflexivity)) as [INV3 PBK3];
eapply (Kbreak mc md2 A2 B2 pbs2 errv2);
[exact INV3
| apply PBK3; unfold PBOK; eapply PBOKat_weaken; [| exact PBK2]; unfold ts2, ts_pbs, ts0; cbn [t_co]; lia
| exact (BOK_lvl_restate _ _ ts2 B2 nB l ST_string_escape ST_ofield Hl ltac:(intros CL; unfold lvl_closed in *; cbn [tl_ss tl_st]; apply andb_true_iff in CL as [CL _]; apply Z.eqb_eq in CL; exfalso; rewrite Hst, CL in Hmode; vm_compute in Hmode; discriminate Hmode) (BOK_drop _ _ _ _ _ _ BK2))
| exact FS2 | exact FRM2]
end end.
Qed.

Lemma ofl_name_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP v2 ra2 : Z) (nB : nat)
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv -> PBOKat m ts kP -> kP <= pf_len pf -> BOK pf pa ts B (S (Z.to_nat (16 * Z.max 0 (pf_len pf) + 8192) + nB)) ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_ofield ->
pe_s0 sv = Z_to_bv 64 v2 -> pe_ra sv = Z_to_bv 64 ra2 ->
(v2 < alloc_ceiling \/ v2 mod 8 <> 0 \/ v2 <= pa_sp0 pa \/ hiA_top A4L HIx - 16 <= v2) /\ 0 <= v2 < 2^64 ->
uw_ok A4L (hl_strdup A4L) (Z_to_bv 64 0x95f88) (UWfp ra2 v2) ->

(forall m' md' A' B' errv' r nn gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' F' fc',
r <> 0 -> 0 <= nn - 1 <= kP ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' (ts_lvl ts (TL ST_eatws ST_ofend (tl_cur l) (tl_cs l) (tl_cbs l) r [(r, nn)])) cb nb pj sv errv' ->
PBOKat m' (ts_lvl ts (TL ST_eatws ST_ofend (tl_cur l) (tl_cs l) (tl_cbs l) r [(r, nn)])) kP ->
BOK pf pa (ts_lvl ts (TL ST_eatws ST_ofend (tl_cur l) (tl_cs l) (tl_cbs l) r [(r, nn)])) B' nB ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msA asegs pf pa APE_BREAK (t_co ts) gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' (Z_to_bv 64 (pf_tk pf + 56)) (Z_to_bv 64 (pa_F pa + 64)) F' fc' m')) ->

(forall m' md' A' B' errv' x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s10' s11' t3' t4' t5' t6' F' fc',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' ts cb nb pj sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(Q1Y6.Mq2.pe_msE pf pa APE_ERR2 x1' gp' t0' t1' t2' (Z_to_bv 64 16) a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s10' s11' t3' t4' t5' t6' F' fc' m')) ->
AJ5 A4L HIx A T md
(Q1Y6.Mq2.pe_msE pf pa 0x95f54 x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (pf_tk pf / 8 + 2147450881)) (Z_to_bv 64 (pf_tk pf + 20)) (Z_to_bv 64 (pf_sb pf + t_co ts)) s6
(Z_to_bv 64 (pf_tk pf + 32)) (Z_to_bv 64 (pa_F pa)) (Z_to_bv 64 (pf_tk pf + 56)) s11 t3 t4 t5 t6 F fc m).
Proof.
intros until fc. intros STC BSL INV PBK HkP BK Hl Hst S0V RAV HV UWK Kbreak Kerr16. pose proof INV as INV0. pe_openA STC INV.
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
pose proof FR as FR0. unfold pe_frameA in FR. destruct FR as (SLOTS & GAP & SAVED & FF & FSH).
unfold pe_slotsA in SLOTS. cbn zeta in SLOTS. unfold ff_cellsA in FF.
unfold pe_msA, pe_msO, Q1Y6.Mq2.pe_msE in *.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * mxd) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t.
blk_factsA A4L HIx HP q (32 * mxd) Hqal Hqlo Hqhi Himg_q.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs m) as WM.
pose proof (LV depth l Hl) as LVd. pose proof LVd as (ST26 & SS26 & _ & Md).
rewrite Nat.ltb_irrefl, Nat.eqb_refl in Md. destruct Md as (c0 & hn0 & Hmode & CLS0 & NM0).
remember (q + 32 * Z.of_nat depth) as bse eqn:Hbse.
assert (HbseR : q <= bse /\ bse + 32 <= q + (32 * mxd)) by (subst bse; lia).
assert (Hb8 : bse mod 8 = 0) by (subst bse; clear - Hqal; Z.div_mod_to_equations; lia).
pose proof (munch_refl [(bse, bse + 32)] m) as MU.
destruct (ofield_mode _ _ _ SS26 ltac:(rewrite <- Hst; exact Hmode)) as (Ec0 & Ehn0). subst c0 hn0.
cbn [name_ok] in NM0. destruct NM0 as [Hn0 Hnbs0].
assert (OPl : lvl_closed l = false) by (apply lvl_closed_open_ss; intros E; rewrite Hst, E in Hmode; vm_compute in Hmode; discriminate Hmode).
assert (Eobjbs : objbs = []).
{ unfold cur_st in OBJ. cbn [t_levels t_depth t_objbs ts0] in OBJ. rewrite Hl, Hst in OBJ. exact OBJ. }
pose proof (PE_NWIN_open HIx GA (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m md A B ts0 cb nb pj sv errv l INV0 Hl Eobjbs) as WIN0.
rewrite Hn0, Hnbs0 in WIN0.
set (lw0 := TL (tl_st l) (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) 0 []) in *. set (tw0 := ts_lvl ts0 lw0) in *.
assert (El : l = lw0) by (unfold lw0; destruct l as [st_ ss_ cur_ cs_ cbs_ name_ nbs_]; cbn [tl_st tl_ss tl_cur tl_cs tl_cbs tl_name tl_nbs] in *; congruence).
assert (Etw0 : tw0 = ts0) by (unfold tw0; rewrite <- El; apply (ts_lvl_same ts0 l Hl)).
assert (PBK0 : PBOKat m tw0 kP) by (exact (PBOKat_same m ts0 tw0 _ eq_refl eq_refl PBK)).
assert (Hlen0 : length (t_levels tw0) = Z.to_nat mxd) by (unfold tw0, ts_lvl, ts0; cbn [t_levels t_depth]; rewrite lupd_length; exact LEN32).
destruct PBK0 as (buf & bpos & cap & pre & post & Epbs & Lpre & PBC & Hbk).
assert (PBK0 : PBOKat m tw0 kP) by (exists buf, bpos, cap, pre, post; split; [exact Epbs|]; split; [exact Lpre|]; split; [exact PBC | exact Hbk]).
unfold tw0, ts_lvl, ts0 in Epbs, PBC; cbn [t_pbs t_pb] in Epbs, PBC.
pose proof PBC as (Hbp & Hcap & Hlen & PBCC & BUFC).

destruct (first_nul_splitA pre post) as (str & rest & Estr & NN & Lstr). change QgoP.b0 with (Z_to_bv 8 0) in Estr, NN.
pose proof (rw_cells_bytes_at' _ _ _ _ BUFC) as BUFB. cbn [cells_bytes cbytes] in BUFB. rewrite app_nil_r in BUFB.
rewrite Estr in BUFB. replace (str ++ Z_to_bv 8 0 :: rest) with ((str ++ [Z_to_bv 8 0]) ++ rest) in BUFB by (rewrite <- app_assoc; reflexivity).
apply bytes_at_app in BUFB as [STRB _].
assert (Lcap : Z.of_nat (length str) + 1 <= cap).
{ rewrite <- Hlen, Estr, length_app. cbn [length]. lia. }
set (nn := Z.of_nat (length str) + 1) in *.
assert (Hnn : nn <= Z.max 0 len + 1) by (unfold nn; lia).
pose proof (BOK_afford (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) ts0 B nB (16 * nn + 512) BSL BK ltac:(unfold K_ev; cbn [pf_len]; lia)) as COST.
assert (INpb : In (pb, PB_SZ) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA, tstate_blocks, ts0; cbn [t_pbs]; rewrite Epbs; apply in_or_app; left; left; reflexivity).
blk_factsA A4L HIx HP pb 16 Hpal Hplo Hphi Himg_p. stash Himg_p.
pose proof (blk_granA HIx _ _ _ _ _ _ _ pb 16 0 HP INpb ltac:(lia) ltac:(lia)) as SHP0.
replace (pb / 8 + 0 + A_SB) with (pb / 8 + 2147450880) in SHP0 by (unfold A_SB; lia).
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 1 HP INtk ltac:(lia)) as SHT1.
replace (tk / 8 + 1 + A_SB) with (tk / 8 + 2147450881) in SHT1 by (unfold A_SB; lia).
unfold APE_BREAK, APE_REDO, APE_OUT, APE_ERRMEM, APE_ERRST, APE_ERR2, APE_JTAB in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
stash Himg_t. stash Himg_q. stash Kbreak. stash Kerr16. stash WIN0. stash INV0. stash STRB.
clear PB REST LV OBJ HPR BUD GAP SAVED FSH FF STR ERR SBin TSK LVd.
reenterA asegs A4L HIx asegs_wx HP.
asan_rechkM 1.
step. step.
asan_chkA.
step.
step.

unstash WIN0. unstash STRB.
evt_done5.
eapply (pe_strdup_name HIx GA GA_pres (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m md A B tw0 cb nb pj sv errv T kP v2 ra2 buf cap str);
[ exact STC | exact WIN0 | exact PBK0 | unfold tw0, ts_lvl, ts0; cbn [t_pbs]; rewrite Epbs; right; left; reflexivity | exact Lcap | unfold nn in *; lia | exact STRB | exact NN | exact COST
| exact S0V | exact RAV | exact HV | exact UWK | rewrite unsigned_lit by lia; reflexivity |].
intros mn2 md2 A2 errv2 r w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 OUT2 PBK2.
cbn [pf_spf pa_sp0 pa_F] in *. unfold A_TP in *. fold nn in OUT2.
clear TOK SLOTS MU WM MI HP INtk INq Htal Htlo Hthi Hqal Hqlo Hqhi WIN0 PBK0 FR0 SHP0 SHT1 PBCC BUFC STRB.
assert (Hlw0 : nth_error (t_levels tw0) depth = Some lw0) by (unfold tw0, ts_lvl, ts0; cbn [t_levels t_depth]; apply nth_error_lupd_eq; apply nth_error_Some; rewrite Hl; discriminate).
assert (Hlw0' : nth_error (t_levels tw0) (t_depth tw0) = Some lw0) by exact Hlw0.
destruct OUT2 as [(-> & WIN2) | (Rr & CSr & WIN2)].
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
shq_facts HP INq INtk q mxd tk (Z.of_nat depth) 3 SHQ3 SEPQ3c SEPQ3q SEPQ3t.
replace (q / 8 + 4 * (Z.of_nat depth) + 3 + A_SB) with (bse / 8 + 2147450883) in SHQ3 by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia).
assert (EQx : q / 8 + A_SB + (4 * (Z.of_nat depth) + 3) = bse / 8 + 2147450883) by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia). rewrite EQx in SEPQ3c, SEPQ3q, SEPQ3t. clear EQx.
shq_facts HP INq INtk q mxd tk (Z.of_nat depth) 0 SHQ0 SEPQ0c SEPQ0q SEPQ0t.
replace (q / 8 + 4 * (Z.of_nat depth) + 0 + A_SB) with (bse / 8 + 2147450880) in SHQ0 by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia).
assert (EQx : q / 8 + A_SB + (4 * (Z.of_nat depth) + 0) = bse / 8 + 2147450880) by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia). rewrite EQx in SEPQ0c, SEPQ0q, SEPQ0t. clear EQx.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 7 HP INtk ltac:(lia)) as SHT7.
replace (tk / 8 + 7 + A_SB) with (tk / 8 + 2147450887) in SHT7 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 7 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT7c & SEPT7q & _).
cbn [hl_sb A4L] in SEPT7c, SEPT7q. assert (EQx : tk / 8 + A_SB + 7 = tk / 8 + 2147450887) by (unfold A_SB; lia). rewrite EQx in SEPT7c, SEPT7q. clear EQx.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 2 HP INtk ltac:(lia)) as SHT2.
replace (tk / 8 + 2 + A_SB) with (tk / 8 + 2147450882) in SHT2 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 2 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT2c & SEPT2q & _).
cbn [hl_sb A4L] in SEPT2c, SEPT2q. assert (EQx : tk / 8 + A_SB + 2 = tk / 8 + 2147450882) by (unfold A_SB; lia). rewrite EQx in SEPT2c, SEPT2q. clear EQx.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 4 HP INtk ltac:(lia)) as SHT4.
replace (tk / 8 + 4 + A_SB) with (tk / 8 + 2147450884) in SHT4 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 4 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT4c & SEPT4q & _).
cbn [hl_sb A4L] in SEPT4c, SEPT4q. assert (EQx : tk / 8 + A_SB + 4 = tk / 8 + 2147450884) by (unfold A_SB; lia). rewrite EQx in SEPT4c, SEPT4q. clear EQx.
pose proof (munch_refl [(bse, bse + 32)] mn2) as MU.
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
assert (cs_tk_L : csep tk 72 bse (Z.of_nat 32)) by (unfold csep; clear - Hdtq HbseR; lia).
assert (cs_L_tk : csep bse 32 tk (Z.of_nat 72)) by (unfold csep; clear - Hdtq HbseR; lia).
assert (cs_Q0_L : csep (bse / 8 + 2147450880) 1 bse (Z.of_nat 32)) by (unfold csep; clear - SEPQ0q HbseR; lia).
assert (cs_T4_L : csep (tk / 8 + 2147450884) 1 bse (Z.of_nat 32)) by (unfold csep; clear - SEPT4q HbseR; lia).
clear Hdtq SEPQ3c SEPQ3q SEPQ3t SEPQ0c SEPQ0q SEPQ0t SEPT7c SEPT7q SEPT2c SEPT2q SEPT4c SEPT4q.
stash Himg_t2. stash Himg_q2. stash WIN2. stash TSK2. stash FR2.
lazymatch goal with |- AJ5 _ _ _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) => replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
reenterA asegs A4L HIx asegs_wx HP.
asan_rechkA.
step.
step.
asan_rechkM 7.
step.
norm_sx32.
step.
rewrite (unsigned_lit (Z.of_nat depth)) by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32.
step.
replace (q + Z.of_nat depth * 32) with bse by lia.
step.
asan_chkA.
stepz.
step.
if_false.
step.
step.
step.
rewrite ?sxb_zero, ?zxb_zero.
step.
if_true.
step.

unstash WIN2. unstash TSK2. unstash FR2.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ mn2 mc, WMc : wmono asegs mn2 mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, Lc : rw_cells asegs mc bse _ |- _ =>
evt_done5;
assert (INqL : Forall (fun iv => exists a n, In (a, n) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 (tsF tw0 []) ++ LM) /\ a <= fst iv /\ snd iv <= a + n) [(bse, bse + 32)])
by (apply Forall_cons; [exists q, (32 * mxd); cbn [fst snd]; split; [apply in_or_app; left; exact INq | lia] | apply Forall_nil]);
assert (FRc : pe_frameA asegs mc (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) cb nb pj sv)
by (eapply (pe_frameA_blkwriteG HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) _ LM FRS _ A2 mn2 mc md2 lo [(bse, bse + 32)] cb nb pj sv); [exact STC | exact HP | exact INqL | exact FR2 | exact MUc | exact WMc]);
assert (TSKc : tstack asegs mc q (lupd (t_levels tw0) (t_depth tw0) lw0))
by (pose proof MUc as MUc'; pose proof Lc as Lc'; rewrite Hbse in MUc', Lc'; eapply (tstack_put asegs mn2 mc q (t_levels tw0) depth lw0 []);
[exact TSK2 | rewrite Hlen0; lia | exact MUc' | exact WMc | intros; exact I | exact Lc']);
destruct (PE_NWIN_write HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo mn2 mc md2 A2 _ tw0 []
cb nb pj sv errv2 [(bse, bse + 32)] lw0 lw0 cb nb pj STC WIN2 Hlw0' MUc WMc MIc
ltac:(apply Forall_cons; [right; cbn [fst snd pf_mxd]; lia | apply Forall_nil])
TOKc TSKc FRc ltac:(unfold lw0; cbn [tl_st]; exact ST26) ltac:(unfold lw0; cbn [tl_ss]; exact SS26) eq_refl eq_refl eq_refl eq_refl) as (WIN3 & PBT3 & AGX3)
end end.
set (tw2 := ts_lvl tw0 lw0) in *.
assert (Etw2 : tw2 = ts0) by (unfold tw2; rewrite (ts_lvl_same tw0 lw0 Hlw0); exact Etw0).
assert (Hlw2 : nth_error (t_levels tw2) (t_depth tw2) = Some lw0) by (rewrite Etw2, <- El; exact Hl).
pose proof (BOK_pay (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) ts0 B (charge B (16 * nn + 512) 0) nB (16 * nn + 512) BK ltac:(unfold K_ev; cbn [pf_len]; lia) ltac:(cbn [bB charge]; lia) ltac:(cbn [bD charge]; lia)) as BKp.
pose proof (PE_NWIN_close HIx GA (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo _ md2 A2 _ tw2 [] cb nb pj sv errv2 lw0 CObj false WIN3 Hlw2
ltac:(unfold lw0; cbn [tl_st tl_ss]; exact Hmode) ltac:(unfold lw0; cbn [tl_cs]; exact CLS0) ltac:(cbn [name_ok tl_name tl_nbs lw0]; split; reflexivity)
ltac:(unfold lw0; cbn [tl_st]; rewrite Hst; reflexivity)
ltac:(unfold lw0; cbn [tl_st tl_ss tl_cur tl_cs tl_cbs tl_name]; fold lw0; unfold tw2; rewrite (ts_lvl_same (ts_lvl tw0 lw0) lw0 ltac:(exact Hlw2)); fold tw2; rewrite Etw2; exact (BOK_weak _ _ _ _ _ BKp))) as INVf.
unfold lw0 in INVf; cbn [tl_st tl_ss tl_cur tl_cs tl_cbs tl_name] in INVf; fold lw0 in INVf. rewrite (ts_lvl_same tw2 lw0 Hlw2), Etw2 in INVf.
unstash Kerr16. eapply (Kerr16 _ md2 A2 _ errv2); [exact INVf | apply fsaved_refl | intros X; exact X].
-
assert (Hr : r <> 0) by lia.
pose proof WIN2 as (CORE2 & BASE2 & _). destruct CORE2 as (_ & _ & _ & _ & TOK & _ & _ & TSK2 & FR2). pose proof (proj1 BASE2) as HP. clear BASE2.
unfold tw0, ts_lvl, ts0 in TOK. cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_tk pf_mxd pf_fl] in TOK.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
pose proof FR2 as (SLOTS & _). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in SLOTS.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 (tsF tw0 [(r, nn)]))) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * mxd) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 (tsF tw0 [(r, nn)]))) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t2.
blk_factsA A4L HIx HP q (32 * mxd) Hqal Hqlo Hqhi Himg_q2.
pose proof (q_ne_tkA HIx _ _ _ _ _ _ _ _ _ _ HP) as Hqtk. cbn [pf_tk] in Hqtk.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ tk 72 q (32 * mxd) HP (in_or_app _ LM _ (or_introl INtk)) (in_or_app _ LM _ (or_introl INq)) ltac:(congruence)) as Hdtq.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs mn2) as WM.
pose proof (TSK2 depth lw0 Hlw0) as Ld. rewrite <- Hbse in Ld. unfold srec_cells, lw0 in Ld. cbn [tl_st tl_ss tl_cur tl_name] in Ld.
shq_facts HP INq INtk q mxd tk (Z.of_nat depth) 3 SHQ3 SEPQ3c SEPQ3q SEPQ3t.
replace (q / 8 + 4 * (Z.of_nat depth) + 3 + A_SB) with (bse / 8 + 2147450883) in SHQ3 by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia).
assert (EQx : q / 8 + A_SB + (4 * (Z.of_nat depth) + 3) = bse / 8 + 2147450883) by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia). rewrite EQx in SEPQ3c, SEPQ3q, SEPQ3t. clear EQx.
shq_facts HP INq INtk q mxd tk (Z.of_nat depth) 0 SHQ0 SEPQ0c SEPQ0q SEPQ0t.
replace (q / 8 + 4 * (Z.of_nat depth) + 0 + A_SB) with (bse / 8 + 2147450880) in SHQ0 by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia).
assert (EQx : q / 8 + A_SB + (4 * (Z.of_nat depth) + 0) = bse / 8 + 2147450880) by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia). rewrite EQx in SEPQ0c, SEPQ0q, SEPQ0t. clear EQx.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 7 HP INtk ltac:(lia)) as SHT7.
replace (tk / 8 + 7 + A_SB) with (tk / 8 + 2147450887) in SHT7 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 7 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT7c & SEPT7q & _).
cbn [hl_sb A4L] in SEPT7c, SEPT7q. assert (EQx : tk / 8 + A_SB + 7 = tk / 8 + 2147450887) by (unfold A_SB; lia). rewrite EQx in SEPT7c, SEPT7q. clear EQx.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 2 HP INtk ltac:(lia)) as SHT2.
replace (tk / 8 + 2 + A_SB) with (tk / 8 + 2147450882) in SHT2 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 2 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT2c & SEPT2q & _).
cbn [hl_sb A4L] in SEPT2c, SEPT2q. assert (EQx : tk / 8 + A_SB + 2 = tk / 8 + 2147450882) by (unfold A_SB; lia). rewrite EQx in SEPT2c, SEPT2q. clear EQx.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 4 HP INtk ltac:(lia)) as SHT4.
replace (tk / 8 + 4 + A_SB) with (tk / 8 + 2147450884) in SHT4 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 4 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT4c & SEPT4q & _).
cbn [hl_sb A4L] in SEPT4c, SEPT4q. assert (EQx : tk / 8 + A_SB + 4 = tk / 8 + 2147450884) by (unfold A_SB; lia). rewrite EQx in SEPT4c, SEPT4q. clear EQx.
pose proof (munch_refl [(bse, bse + 32)] mn2) as MU.
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
assert (cs_tk_L : csep tk 72 bse (Z.of_nat 32)) by (unfold csep; clear - Hdtq HbseR; lia).
assert (cs_L_tk : csep bse 32 tk (Z.of_nat 72)) by (unfold csep; clear - Hdtq HbseR; lia).
assert (cs_Q0_L : csep (bse / 8 + 2147450880) 1 bse (Z.of_nat 32)) by (unfold csep; clear - SEPQ0q HbseR; lia).
assert (cs_T4_L : csep (tk / 8 + 2147450884) 1 bse (Z.of_nat 32)) by (unfold csep; clear - SEPT4q HbseR; lia).
clear Hdtq SEPQ3c SEPQ3q SEPQ3t SEPQ0c SEPQ0q SEPQ0t SEPT7c SEPT7q SEPT2c SEPT2q SEPT4c SEPT4q.
stash Himg_t2. stash Himg_q2. stash WIN2. stash TSK2. stash FR2.
lazymatch goal with |- AJ5 _ _ _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) => replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
reenterA asegs A4L HIx asegs_wx HP.
asan_rechkA.
step.
step.
asan_rechkM 7.
step.
norm_sx32.
step.
rewrite (unsigned_lit (Z.of_nat depth)) by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32.
step.
replace (q + Z.of_nat depth * 32) with bse by lia.
step.
asan_chkA.
stepz.
step.
if_truex.
step.
asan_chkA.
step.
stepz.
asan_chkA.
stepz.
step. step.
step.

set (lw2 := TL ST_eatws ST_ofend (tl_cur l) (tl_cs l) (tl_cbs l) r []).
unstash WIN2. unstash TSK2. unstash FR2.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ mn2 mc, WMc : wmono asegs mn2 mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, Lc : rw_cells asegs mc bse _ |- _ =>
evt_done5;
assert (INqL : Forall (fun iv => exists a n, In (a, n) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 (tsF tw0 [(r, nn)]) ++ LM) /\ a <= fst iv /\ snd iv <= a + n) [(bse, bse + 32)])
by (apply Forall_cons; [exists q, (32 * mxd); cbn [fst snd]; split; [apply in_or_app; left; exact INq | lia] | apply Forall_nil]);
assert (FRc : pe_frameA asegs mc (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) cb nb pj sv)
by (eapply (pe_frameA_blkwriteG HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) _ LM FRS _ A2 mn2 mc md2 lo [(bse, bse + 32)] cb nb pj sv); [exact STC | exact HP | exact INqL | exact FR2 | exact MUc | exact WMc]);
assert (TSKc : tstack asegs mc q (lupd (t_levels tw0) (t_depth tw0) lw2))
by (pose proof MUc as MUc'; pose proof Lc as Lc'; rewrite Hbse in MUc', Lc'; eapply (tstack_put asegs mn2 mc q (t_levels tw0) depth lw2 []);
[exact TSK2 | rewrite Hlen0; lia | exact MUc' | exact WMc | intros; exact I | exact Lc']);
destruct (PE_NWIN_write HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo mn2 mc md2 A2 _ tw0 [(r, nn)]
cb nb pj sv errv2 [(bse, bse + 32)] lw0 lw2 cb nb pj STC WIN2 Hlw0' MUc WMc MIc
ltac:(apply Forall_cons; [right; cbn [fst snd pf_mxd]; lia | apply Forall_nil])
TOKc TSKc FRc ltac:(unfold lw2; cbn [tl_st]; unfold ST_eatws; lia) ltac:(unfold lw2; cbn [tl_ss]; unfold ST_ofend; lia) eq_refl eq_refl eq_refl eq_refl) as (WIN3 & PBT3 & AGX3)
end end.
set (tw2 := ts_lvl tw0 lw2) in *.
assert (Etw2 : forall lx, ts_lvl tw2 lx = ts_lvl ts0 lx) by (intros lx; unfold tw2, tw0; rewrite !ts_lvl_lvl; reflexivity).
assert (Hlw2 : nth_error (t_levels tw2) (t_depth tw2) = Some lw2) by (unfold tw2, ts_lvl; cbn [t_levels t_depth]; apply nth_error_lupd_eq; rewrite Hlen0; cbn [t_depth tw0 ts_lvl ts0]; lia).
assert (BKf : BOK (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) (ts_lvl ts0 (TL ST_eatws ST_ofend (tl_cur l) (tl_cs l) (tl_cbs l) r [(r, nn)])) (charge B (16 * nn + 512) 0) nB).
{ eapply (BOK_name_attach (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) ts0 B (charge B (16 * nn + 512) 0) nB l ST_eatws ST_ofend r nn (16 * nn + 512) BK Hl Hnbs0 OPl);
[ apply lvl_closed_open_ss; cbn [tl_ss]; unfold ST_ofend, ST_finish; lia | exact Hnn | unfold K_free, K_ev; cbn [pf_len]; lia | cbn [bB charge]; lia | cbn [bD charge]; lia ]. }
assert (NMf : name_ok asegs mn2 true (TL ST_eatws ST_ofend (tl_cur l) (tl_cs l) (tl_cbs l) r [(r, nn)])).
{ cbn [name_ok tl_name tl_nbs]. split; [exact Hr|]. exists nn, str. split; [reflexivity|]. split; [unfold nn in *; lia | exact CSr]. }
pose proof (PE_NWIN_close HIx GA (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo _ md2 A2 _ tw2 [(r, nn)] cb nb pj sv errv2 lw2 CObj true WIN3 Hlw2
ltac:(vm_compute; reflexivity) ltac:(unfold lw2; cbn [tl_cs]; exact CLS0)
ltac:(unfold lw2; cbn [tl_st tl_ss tl_cur tl_cs tl_cbs tl_name]; eapply (name_ok_agree asegs [(r, nn)]); [exact NMf | exact AGX3 | cbn [tl_nbs]; apply incl_refl])
ltac:(reflexivity)
ltac:(unfold lw2; cbn [tl_st tl_ss tl_cur tl_cs tl_cbs tl_name]; rewrite Etw2; exact (BOK_weak _ _ _ _ _ BKf))) as INVf.
unfold lw2 in INVf; cbn [tl_st tl_ss tl_cur tl_cs tl_cbs tl_name] in INVf. rewrite Etw2 in INVf.
unstash Kbreak. eapply (Kbreak _ md2 A2 _ errv2 r nn); [exact Hr | unfold nn; lia | exact INVf | | exact BKf | apply fsaved_refl | intros X; exact X].
eapply PBOKat_same with (ts := tw2); [reflexivity | reflexivity |]. exact (PBT3 _ PBK2).
Qed.

Lemma ofl_quote_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (co0 k0 : Z)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kB : nat)
(x1 gp t0 t1 t2 a0 a1 a2 a4 a5 a6 a7 s3 s4 s5 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
PBOKat m ts (co0 + k0) -> k0 <= 0 -> BOK pf pa ts B kB ->
0 <= co0 <= t_co ts -> t_co ts < pf_len pf ->

(forall m' md' A' B' pbs' errv' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' (ts_pbs ts pbs') cb nb pj sv errv' ->
PBOKat m' (ts_pbs ts pbs') (t_co ts + k0) -> BOK pf pa (ts_pbs ts pbs') B' kB ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(Q1Y6.Mq2.pe_msE pf pa 0x95f54 x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 (pf_tk pf / 8 + 2147450881)) (Z_to_bv 64 (pf_tk pf + 20)) (Z_to_bv 64 (pf_sb pf + t_co ts))
(Z_to_bv 64 (pf_sb pf + t_co ts)) (Z_to_bv 64 (pf_tk pf + 32)) (Z_to_bv 64 (pa_F pa)) (Z_to_bv 64 (pf_tk pf + 56)) (Z_to_bv 64 (pf_sb pf + co0)) t3' t4' t5' t6' F' fc' m')) ->

(forall m' md' A' B' errv' x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s10' s11' t3' t4' t5' t6' F' fc',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' ts cb nb pj sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(Q1Y6.Mq2.pe_msE pf pa APE_ERR2 x1' gp' t0' t1' t2' (Z_to_bv 64 16) a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s10' s11' t3' t4' t5' t6' F' fc' m')) ->
AJ5 A4L HIx A T md
(Q1Y6.Mq2.pe_msE pf pa 0x95f1c x1 gp t0 t1 t2 a0 a1 a2 (Z_to_bv 64 (pf_tk pf + 8)) a4 a5 a6 a7 s3 s4 s5 (Z_to_bv 64 (pf_sb pf + t_co ts)) (Z_to_bv 64 (pf_tk pf + 32)) (Z_to_bv 64 (pa_F pa)) s10
(Z_to_bv 64 (pf_sb pf + co0)) t3 t4 t5 t6 F fc m).
Proof.
intros until fc. intros STC BSL INV PBK K0 BK Hco0 Hco Kctor Kerr16. pose proof INV as INV0.
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
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 1 HP INtk ltac:(lia)) as SHT1.
replace (tk / 8 + 1 + A_SB) with (tk / 8 + 2147450881) in SHT1 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 1 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT1c & SEPT1q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 1 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT1t & _).
cbn [hl_sb A4L] in SEPT1c, SEPT1q, SEPT1t. assert (EQx : tk / 8 + A_SB + 1 = tk / 8 + 2147450881) by (unfold A_SB; lia). rewrite EQx in SEPT1c, SEPT1q, SEPT1t. clear EQx.
unfold APE_ERR2 in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
clear PB TSK REST LV SEPT1c SEPT1q SEPT1t.
reenterA asegs A4L HIx asegs_wx HP.
asan_chkA.
step.
step.
step.
norm_w32. replace (sb + co - (sb + co0)) with (co - co0) by lia.
step. step.
evt_done5.
eapply (pe_memappend_pk HIx GA GA_pres MAPP (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m md A B ts0 cb nb pj sv errv T co0 k0 (co - co0));
[exact STC | exact BSL | exact INV0 | exact PBK | exact K0 | lia | lia | cbn [t_co ts0]; lia | cbn [pf_len]; lia | cbn [pf_len]; lia | exact BK | rewrite unsigned_lit by lia; reflexivity |].
intros m2 md2 A2 B2 pbs2 errv2 r w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 F2 fc2 INV2 OUT2 FS2 FRM2.
cbn [pf_spf] in *. unfold A_TP in *.
clear TOK SLOTS SHT1 Htal Htlo Hthi Himg_t Himg_q Hqal Hqlo Hqhi INtk INq HP INV0 PBK BK.
pose proof INV2 as [CORE2 REST2]. destruct CORE2 as (_ & _ & _ & _ & _ & _ & _ & _ & FR2). pose proof (proj1 REST2) as HP.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 (ts_pbs ts0 pbs2))) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 4 HP INtk ltac:(lia)) as SHT4.
replace (tk / 8 + 4 + A_SB) with (tk / 8 + 2147450884) in SHT4 by (unfold A_SB; lia).
pose proof FR2 as (SLOTS & _). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS. cbn [pf_tk pf_spf pf_lenr pa_F pa_sp0 pa_oldloc pa_newloc] in SLOTS. unfold shA in SLOTS. a4l. unfold SB2, SB4, SB7, SB8 in SLOTS.
clear REST2 FR2.
reenterA asegs A4L HIx asegs_wx HP.
destruct OUT2 as [(-> & PBK2 & BK2) | [-> Epbs2]].
- do 3 step.
if_truex.
evt_done5.
eapply (Kctor m2 md2 A2 B2 pbs2 errv2); [exact INV2 | eapply PBOKat_weaken; [| exact PBK2]; cbn [t_co ts0 ts_pbs]; lia | exact BK2 | exact FS2 | exact FRM2].
- replace (Z_to_bv 64 (2^64 - 1)) with (Z_to_bv 64 (-1)) by (apply bv_eq; vm_compute; reflexivity).
do 3 step.
if_false.
step.
step.
step.
rewrite ?sxb_zero, ?zxb_zero.
step.
if_true.
step.
evt_done5.
eapply (Kerr16 m2 md2 A2 B2 errv2); [| exact FS2 | exact FRM2].
subst pbs2. exact INV2.
Qed.

Lemma ofl_latch_A :
forall (n : nat) (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel) (co0 k0 : Z)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kB : nat)
(gp t0 t1 t2 a0 a1 a2 a5 a7 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa -> pf_fl pf = 0 ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
PBOKat m ts (co0 + k0) -> k0 <= 0 -> BOK pf pa ts B kB ->
CSTR_OK pf payload ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_ofield ->
0 <= co0 <= t_co ts -> t_co ts < pf_len pf -> nth_error payload (Z.to_nat (t_co ts)) = Some cb ->
(pf_len pf - t_co ts <= Z.of_nat n) ->

(forall m' co' cb' pj' a0' a1' a2' a5' s3',
t_co ts <= co' < pf_len pf -> nth_error payload (Z.to_nat co') = Some cb' ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md A B (ts_set_co ts co') cb' nb pj' sv errv ->
PBOKat m' (ts_set_co ts co') (co0 + k0) ->
AJ5 A4L HIx A T md
(Q1Y6.Mq2.pe_msE pf pa 0x96f20 (Z_to_bv 64 (pf_tk pf / 8 + 2147450884)) gp t0 t1 t2 a0' a1' a2' (Z_to_bv 64 (pf_tk pf + 8)) (Z_to_bv 64 (bv_unsigned cb')) a5' (Z_to_bv 64 (bv_unsigned (ts_quote (t_x ts)))) a7 s3' (Z_to_bv 64 (co' - co0)) (Z_to_bv 64 (Z.of_nat (t_depth ts))) (Z_to_bv 64 (pf_sb pf + co')) (Z_to_bv 64 (pf_tk pf + 32)) (Z_to_bv 64 (pa_F pa)) (Z_to_bv 64 q)
(Z_to_bv 64 (pf_sb pf + co0)) (Z_to_bv 64 (pf_tk pf + 64)) (Z_to_bv 64 (pa_F pa + 64)) (Z_to_bv 64 (pf_tk pf / 8 + 2147450888)) (Z_to_bv 64 (pf_lenr pf)) F fc m')) ->

(forall m' co' cb' pj' a0' a1' a2' a5' s3' s4',
t_co ts < co' < pf_len pf -> nth_error payload (Z.to_nat co') = Some cb' ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md A B (ts_set_co ts co') cb' nb pj' sv errv ->
PBOKat m' (ts_set_co ts co') (co0 + k0) ->
AJ5 A4L HIx A T md
(Q1Y6.Mq2.pe_msE pf pa 0x95f1c (Z_to_bv 64 (pf_tk pf / 8 + 2147450884)) gp t0 t1 t2 a0' a1' a2' (Z_to_bv 64 (pf_tk pf + 8)) (Z_to_bv 64 (bv_unsigned cb')) a5' (Z_to_bv 64 (bv_unsigned (ts_quote (t_x ts)))) a7 s3' s4' (Z_to_bv 64 (Z.of_nat (t_depth ts))) (Z_to_bv 64 (pf_sb pf + co')) (Z_to_bv 64 (pf_tk pf + 32)) (Z_to_bv 64 (pa_F pa)) (Z_to_bv 64 q)
(Z_to_bv 64 (pf_sb pf + co0)) (Z_to_bv 64 (pf_tk pf + 64)) (Z_to_bv 64 (pa_F pa + 64)) (Z_to_bv 64 (pf_tk pf / 8 + 2147450888)) (Z_to_bv 64 (pf_lenr pf)) F fc m')) ->

(forall m' md' A' B' pbs' (e : word) co' cb' errv' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' s11' t4' t6' F' fc',
t_co ts < co' <= pf_len pf ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' (ts_pbs (ts_set_x ts co' (TS (ts_isd (t_x ts)) (ts_stpos (t_x ts)) (Z_to_bv 64 co') e (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))) pbs') cb' nb pj sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msO asegs pf pa APE_OUT x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' (Z_to_bv 64 (pf_tk pf + 56)) s11' t4' t6' F' fc' m')) ->
(forall m' md' A' B' pbs' (e : word) co' cb' errv' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' s11' t4' t6' F' fc',
t_co ts < co' <= pf_len pf ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' (ts_pbs (ts_set_x ts co' (TS (ts_isd (t_x ts)) (ts_stpos (t_x ts)) (Z_to_bv 64 co') e (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))) pbs') cb' nb pj sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msO asegs pf pa APE_ERRMEM x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' (Z_to_bv 64 (pf_tk pf + 56)) s11' t4' t6' F' fc' m')) ->
AJ5 A4L HIx A T md
(Q1Y6.Mq2.pe_msE pf pa 0x967f8 (Z_to_bv 64 (pf_tk pf / 8 + 2147450884)) gp t0 t1 t2 a0 a1 a2 (Z_to_bv 64 (pf_tk pf + 8)) (Z_to_bv 64 (bv_unsigned cb)) a5 (Z_to_bv 64 (bv_unsigned (ts_quote (t_x ts)))) a7 (Z_to_bv 64 (pf_sb pf + t_co ts + 1)) (Z_to_bv 64 (t_co ts - co0)) (Z_to_bv 64 (Z.of_nat (t_depth ts))) (Z_to_bv 64 (pf_sb pf + t_co ts)) (Z_to_bv 64 (pf_tk pf + 32)) (Z_to_bv 64 (pa_F pa)) (Z_to_bv 64 q)
(Z_to_bv 64 (pf_sb pf + co0)) (Z_to_bv 64 (pf_tk pf + 64)) (Z_to_bv 64 (pa_F pa + 64)) (Z_to_bv 64 (pf_tk pf / 8 + 2147450888)) (Z_to_bv 64 (pf_lenr pf)) F fc m).
Proof.
induction n as [|n IH]; intros until fc; intros STC BSL FL0 INV PBK K0 BK CSTR Hl Hst Hco0 Hco Hc Hn Kbsl Kquote Kout Kerr16.
{ exfalso. destruct INV as [(_ & _ & CO & _) _]. cbn in Hn. lia. }
pose proof INV as INV0.
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
destruct INV as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof REST as (HP & LV & OBJ & ST & ERR & STR & PLEN & SBin & HPR & MDV & G & BUD).
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *. subst fl.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
unfold ts_set_co, ts_set_x, ts_pbs in Kbsl, Kquote, Kout, Kerr16.
cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in Kbsl, Kquote, Kout, Kerr16.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
pose proof FR as FR0. unfold pe_frameA in FR. destruct FR as (SLOTS & GAP & SAVED & FF & FSH). unfold Q1Y6.Mq2.pe_msE, pe_msO in *.
unfold pe_slotsA in SLOTS. cbn zeta in SLOTS. unfold pe_savedA_cells in SAVED. unfold ff_cellsA in FF. unfold ffsh_cells, FSH0 in FSH. cbn [map] in FSH.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd 0) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 4 HP INtk ltac:(lia)) as SHT4.
replace (tk / 8 + 4 + A_SB) with (tk / 8 + 2147450884) in SHT4 by (unfold A_SB; lia).
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 8 HP INtk ltac:(lia)) as SHT8.
replace (tk / 8 + 8 + A_SB) with (tk / 8 + 2147450888) in SHT8 by (unfold A_SB; lia).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs m) as WM.
pose proof (bytes_at_bound _ _ _ _ STR) as SBB.
pose proof alloc_ceiling_range as ACR.
pose proof (bv_unsigned_in_range 8 cb) as CBR; unfold bv_modulus in CBR; cbn in CBR.
pose proof (bv_unsigned_in_range 8 quote) as QR; unfold bv_modulus in QR; cbn in QR.
assert (INF : In (Ff, 2) ((Ff, 2) :: FRS)) by (left; reflexivity).
assert (INtk' : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd 0) q LB0 ts0 ++ LM)) by (apply in_or_app; left; exact INtk).
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP INF INtk') as DFt. rewrite fr_size_2 in DFt.
assert (GF0' : 0 <= Ff) by lia. assert (GFc' : Ff < alloc_ceiling) by lia.
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP INF) as DSF. rewrite fr_size_2 in DSF. cbn [hl_sb A4L] in DSF.
destruct SBin as [L00 | PL]; [exfalso; lia|].
unfold APE_OUT, APE_ERRMEM in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8, A_SB in *.
pose proof (munch_refl [(tk, tk + 72); (Ff + 64, Ff + 65)] m) as MU.
assert (HW : Forall (pe_wtfA (PEF tk oldl newl len lenr sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl)) [(tk, tk + 72); (Ff + 64, Ff + 65)]).
{ apply Forall_cons; [left; cbn [fst snd pf_tk]; lia |]. apply Forall_cons; [| apply Forall_nil]. right; right; left. cbn [fst snd pa_F]. lia. }
assert (cs_FF_T : csep Ff 248 tk (Z.of_nat 72)) by (unfold csep; clear - DFt; lia).
assert (cs_T_FF : csep tk 72 Ff (Z.of_nat 248)) by (unfold csep; clear - DFt; lia).
assert (cs_S_T : csep spf 312 tk (Z.of_nat 72)) by (unfold csep; clear - Hthi LO LOS ACR; lia).
assert (cs_S_FF : csep spf 312 Ff (Z.of_nat 248)) by (unfold csep; clear - GFc LO LOS ACR; lia).
clear LV OBJ HPR.
stash IH.
reenterA asegs A4L HIx asegs_wx HP.
step.
step.
destruct (Z.eq_dec (bv_unsigned cb) 92) as [E92 | N92].
{
if_truex. evt_done5.
eapply (Kbsl m co cb pj); [lia | exact Hc | exact INV0 | exact PBK]. }
if_falsex.
destruct (Z.eq_dec (bv_unsigned cb) 0) as [E0 | N0].
{
stash PB. stash TSK. stash SLOTS. stash GAP. stash SAVED. stash FSH.
asan_rechkA.
step.
replace (zx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0) by (apply bv_eq; vm_compute; reflexivity).
step.
lazymatch goal with |- evt _ _ (MS ?R ?FF _ ?fcc None ?mm ?rom) =>
assert (CTLJ : forall a2x, evt asegs (AJ5e A4L HIx A T md) (MS (bvmap_set 12 a2x R) FF (Z_to_bv 64 0x96820) fcc None mm rom)) end.
2:{ step.
destruct (Z_lt_dec 31 (bv_unsigned cb)) as [G31 | L31].
- if_truex. apply CTLJ.
- if_falsex. step.
step.
if_true. apply CTLJ. }
intros a2x.
asan_rechkA.
step.
norm_sx32.
step.
norm_w32.
step.
step.
if_falsex. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, FFc : rw_cells asegs mc Ff _ |- _ =>
assert (FRc : pe_frameA asegs mc (PEF tk oldl newl len lenr sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) cb nb pj sv)
by (eapply (pe_frameA_scan HIx) with (ts := ts0); [exact STC | exact (proj1 REST) | exact FR0 | exact MUc | exact WMc | exact FFc]);
evt_done5;
destruct (PE_INV_A_tokw HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m mc md A B ts0
cb nb pj sv errv _ (co + 1) (TS isd stpos (Z_to_bv 64 (co + 1)) err ucs high quote) cb nb STC INV0 MUc WMc MIc HW TOKc FRc
ltac:(cbn [pf_len]; lia) eq_refl) as [INV1 PBK1]
end end.
replace (Z_to_bv 64 (co - co0)) with (Z_to_bv 64 (co + 1 - co0 - 1)) by (f_equal; lia).
eapply (ofl_flush_A (PEF tk oldl newl len lenr sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo _ md A B
(ts_set_x ts0 (co + 1) (TS isd stpos (Z_to_bv 64 (co + 1)) err ucs high quote)) co0 k0 cb nb pj sv errv T kB);
[exact STC | exact BSL | exact INV1 | exact (PBK1 _ PBK) | exact K0 | exact (BOK_set_x _ _ ts0 B kB (co + 1) _ ltac:(cbn [t_co ts0]; lia) BK)
| cbn [t_co ts_set_x]; lia | cbn [t_co ts_set_x pf_len]; lia
| intros; eapply (Kout _ _ _ _ _ err (co + 1) cb); [cbn [pf_len]; lia | eassumption | eassumption | eassumption]
| intros; eapply (Kerr16 _ _ _ _ _ err (co + 1) cb); [cbn [pf_len]; lia | eassumption | eassumption | eassumption]]. }
destruct (peek_cases (PEF tk oldl newl len lenr sb spf pmd mxd 0) payload co cb LENR CSTR (proj1 RR) ltac:(cbn [pf_len pf_mxd]; lia) ltac:(cbn [pf_len pf_mxd]; lia) Hc N0)
as [[Elenr Heof] | [Hne Hmore]]; cbn [pf_len pf_lenr pf_mxd] in *.
{
subst lenr. stash PB. stash TSK. stash SLOTS. stash GAP. stash SAVED. stash FSH.
asan_rechkA.
step.
replace (zx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0) by (apply bv_eq; vm_compute; reflexivity).
step.
lazymatch goal with |- evt _ _ (MS ?R ?FF _ ?fcc None ?mm ?rom) =>
assert (CTLJ : forall a2x, evt asegs (AJ5e A4L HIx A T md) (MS (bvmap_set 12 a2x R) FF (Z_to_bv 64 0x96820) fcc None mm rom)) end.
2:{ step.
destruct (Z_lt_dec 31 (bv_unsigned cb)) as [G31 | L31].
- if_truex. apply CTLJ.
- if_falsex. step.
step.
if_true. apply CTLJ. }
intros a2x.
asan_rechkA.
step.
norm_sx32.
step.
norm_w32.
step.
step.
if_truex.
step.
rewrite Heof. if_false. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, FFc : rw_cells asegs mc Ff _ |- _ =>
assert (FRc : pe_frameA asegs mc (PEF tk oldl newl len len sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) cb nb pj sv)
by (eapply (pe_frameA_scan HIx) with (ts := ts0); [exact STC | exact (proj1 REST) | exact FR0 | exact MUc | exact WMc | exact FFc]);
evt_done5;
destruct (PE_INV_A_tokw HIx GA GA_outside (PEF tk oldl newl len len sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m mc md A B ts0
cb nb pj sv errv _ (co + 1) (TS isd stpos (Z_to_bv 64 (co + 1)) err ucs high quote) cb nb STC INV0 MUc WMc MIc HW TOKc FRc
ltac:(cbn [pf_len]; lia) eq_refl) as [INV1 PBK1]
end end.
replace (Z_to_bv 64 (co - co0)) with (Z_to_bv 64 (len - co0 - 1)) by (f_equal; lia).
eapply (ofl_eof_A (PEF tk oldl newl len len sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo _ md A B
(ts_set_x ts0 (co + 1) (TS isd stpos (Z_to_bv 64 (co + 1)) err ucs high quote)) l co0 k0 cb nb pj sv errv T kB);
[exact STC | exact BSL | exact INV1 | exact (PBK1 _ PBK) | exact K0 | exact (BOK_set_x _ _ ts0 B kB (co + 1) _ ltac:(cbn [t_co ts0]; lia) BK) | exact Hl | exact Hst
| cbn [t_co ts_set_x pf_len]; lia | cbn [pf_len]; lia
| intros; eapply (Kout _ _ _ _ _ (Z_to_bv 64 1) (co + 1) cb); [cbn [pf_len]; lia | eassumption | eassumption | eassumption]
| intros; eapply (Kerr16 _ _ _ _ _ (Z_to_bv 64 1) (co + 1) cb); [cbn [pf_len]; lia | eassumption | eassumption | eassumption]]. }

destruct (nth_error payload (Z.to_nat (co + 1))) as [c'|] eqn:Hc'; [| apply nth_error_None in Hc'; lia].
pose proof (bv_unsigned_in_range 8 c') as CBR'; unfold bv_modulus in CBR'; cbn in CBR'.
pose proof (payload_shadow_pe HIx (PEF tk oldl newl len lenr sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) LB0 FRS _ _ _ _ _ _ _ (co + 1) HP
ltac:(intros bb Hbb; unfold pe_blocksA; apply in_or_app; right; right; right; exact Hbb) PL ltac:(cbn [pf_len]; lia)) as (v & SHP & Hv).
cbn [pf_sb] in SHP, Hv. unfold A_SB in SHP. replace (sb + (co + 1)) with (sb + co + 1) in SHP, Hv by lia.
assert (SBc : sb + len <= alloc_ceiling).
{ destruct PL as [([b0 n0] & Hb0 & Hb1 & Hb2) | (Fh & kh & HFh & HF1 & HF2 & _)]; cbn [pf_sb pf_len pa_sp0 blk_addr blk_size fst snd] in *.
- pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ b0 n0 HP ltac:(apply in_or_app; left; unfold pe_blocksA; apply in_or_app; right; right; right; exact Hb0)) as (_ & _ & _ & Hbhi & _). lia.
- pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP (or_intror HFh)) as (_ & _ & _ & HFhc & _). lia. }
assert (SBhi : sb + len <= 2^47) by lia.
pose proof (shadow_blk_apart HIx _ _ _ _ _ _ _ _ _ (sb + co + 1) 1 HP INtk' ltac:(lia) ltac:(lia) ltac:(lia)) as DSPt. unfold shA, A_SB in DSPt.
assert (SHPF : (sb + co + 1) / 8 + 2147450880 + 1 <= Ff \/ Ff + 256 <= (sb + co + 1) / 8 + 2147450880) by (clear - DSF SBhi SB0 CO Hmore; Z.div_mod_to_equations; lia).
assert (cs_P_T : csep ((sb + co + 1) / 8 + 2147450880) 1 tk (Z.of_nat 72)) by (unfold csep; clear - DSPt; lia).
assert (LE1 : le1 (zxb c') = [c']).
{ unfold le1, zxb. cbn [Z_to_le_bytes pf_mxd]. f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 8) with 256%Z. change (bv_modulus 64) with 18446744073709551616%Z. Z.div_mod_to_equations. nia. }
stash PB. stash TSK. stash Hv. stash GAP. stash SAVED. stash FSH. stash DSF. stash SHPF. stash DSPt. stash DFt.
stash Kbsl. stash Kquote. stash Kout. stash Kerr16. stash INV0. stash REST. stash FR0. stash PBK. stash BK. stash SBc. stash SBhi. stash LE1. stash Hc'. stash Hc. stash STR. stash HW.
asan_rechkA.
step.
replace (zx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0) by (apply bv_eq; vm_compute; reflexivity).
step.
lazymatch goal with |- evt _ _ (MS ?R ?FF _ ?fcc None ?mm ?rom) =>
assert (CTLJ : forall a2x, evt asegs (AJ5e A4L HIx A T md) (MS (bvmap_set 12 a2x R) FF (Z_to_bv 64 0x96820) fcc None mm rom)) end.
2:{ step.
destruct (Z_lt_dec 31 (bv_unsigned cb)) as [G31 | L31].
- if_truex. apply CTLJ.
- if_falsex. step.
step.
if_true. apply CTLJ. }
intros a2x.
asan_rechkA.
step.
norm_sx32.
step.
norm_w32.
step.
step.
if_truex.
step.
if_truex.
step. step.
step.
step.
if_true.
step.
sh_norm.

lazymatch goal with |- evt _ _ (MS ?R ?FF _ ?fcc None ?mm ?rom) =>
assert (JOIN : forall a0x a1x, evt asegs (AJ5e A4L HIx A T md) (MS (bvmap_set 10 a0x (bvmap_set 11 a1x R)) FF (Z_to_bv 64 0x9689c) fcc None mm rom)) end.
2:{ unstash Hv. destruct Hv as [-> | [Hv8 Hvlt]].
- step. rewrite ?sxb_zero. step. if_false. apply JOIN.
- step. rewrite (sxb_small v) by lia. step. if_truex.
step.
unstash SBhi. rewrite (unsigned_lit (sb + co + 1)) by lia. rewrite (land7_mod8 (sb + co + 1)) by lia.
pose proof (Z.mod_pos_bound (sb + co + 1) 8 ltac:(lia)) as R8. remember ((sb + co + 1) mod 8) as r8 eqn:Er8 in *.
step.
if_truex. apply JOIN. }
intros a0x a1x. clear SHP.
unstash REST. unstash STR. unstash HW. unstash Hc'.
lazymatch goal with MUc : munch _ m ?mc |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (payload_privateA HIx _ _ _ _ _ _ _ ts0 _ _ _ _ _ _ _ STC (proj1 REST) STR PLEN (or_intror PL) MUc (pe_wtfA_private _ _ q pbs _ HW)) as STRc end.
cbn [pf_sb] in STRc.
pose proof (payload_byteA _ _ _ _ _ STRc Hc' ltac:(lia)) as RDC. replace (sb + (co + 1)) with (sb + co + 1) in RDC by lia.
stash REST. stash STR. stash HW. clear STRc.
step.
change (zxb c') with (Z_to_bv 64 (bv_unsigned c')). clear RDC.
step.
norm_w32.
clear SHT4 SHT8.
unstash LE1.
step.
replace (le1 (Z_to_bv 64 (bv_unsigned c'))) with [c'] by (rewrite <- LE1; reflexivity). mem_after_store.
step.
step.
step.
unstash REST. unstash HW. unstash INV0. unstash FR0. unstash PBK.
destruct (Z.eq_dec (bv_unsigned c') (bv_unsigned quote)) as [EQ | NQ].
-
if_falsex. step.
replace (sb + co + 1) with (sb + (co + 1)) by lia.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, FFc : rw_cells asegs mc Ff _ |- _ =>
assert (FRc : pe_frameA asegs mc (PEF tk oldl newl len lenr sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) c' nb pj sv)
by (eapply (pe_frameA_scan HIx) with (ts := ts0); [exact STC | exact (proj1 REST) | exact FR0 | exact MUc | exact WMc | exact FFc]);
evt_done5;
destruct (PE_INV_A_tokw HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m mc md A B ts0
cb nb pj sv errv _ (co + 1) (TS isd stpos (Z_to_bv 64 (co + 1)) err ucs high quote) c' nb STC INV0 MUc WMc MIc HW TOKc FRc
ltac:(cbn [pf_len]; lia) eq_refl) as [INV1 PBK1]
end end.
unstash Kquote. eapply (Kquote _ (co + 1) c' pj); [lia | exact Hc' | exact INV1 | exact (PBK1 _ PBK)].
- if_truex.
replace (sb + co + 2) with (sb + (co + 1) + 1) by lia. replace (sb + co + 1) with (sb + (co + 1)) by lia.
replace (co - co0 + 1) with (co + 1 - co0) by lia.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, FFc : rw_cells asegs mc Ff _ |- _ =>
assert (FRc : pe_frameA asegs mc (PEF tk oldl newl len lenr sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) c' nb pj sv)
by (eapply (pe_frameA_scan HIx) with (ts := ts0); [exact STC | exact (proj1 REST) | exact FR0 | exact MUc | exact WMc | exact FFc]);
evt_done5;
destruct (PE_INV_A_tokw HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m mc md A B ts0
cb nb pj sv errv _ (co + 1) (TS isd stpos (Z_to_bv 64 (co + 1)) err ucs high quote) c' nb STC INV0 MUc WMc MIc HW TOKc FRc
ltac:(cbn [pf_len]; lia) eq_refl) as [INV1 PBK1]
end end.
unstash IH. unstash Kbsl. unstash Kquote. unstash Kout. unstash Kerr16. unstash BK.
eapply (IH (PEF tk oldl newl len lenr sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo _ md A B
(TST depth levels (co + 1) pb pbs (TS isd stpos (Z_to_bv 64 (co + 1)) err ucs high quote) obj objs objbs) l co0 k0 c' nb pj sv errv T kB);
[ exact STC | exact BSL | reflexivity | exact INV1 | exact (PBK1 _ PBK) | exact K0 | exact (BOK_set_x _ _ ts0 B kB (co + 1) _ ltac:(cbn [t_co ts0]; lia) BK) | exact CSTR | exact Hl | exact Hst
| cbn [t_co]; lia | cbn [t_co pf_len]; lia | exact Hc' | cbn [t_co pf_len]; lia
| cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_sb pf_len pf_tk pf_lenr pa_F ts_set_co];
intros; eapply Kbsl; [cbn [pf_len] in *; lia | eassumption | eassumption | eassumption]
| cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_sb pf_len pf_tk pf_lenr pa_F ts_set_co];
intros; eapply Kquote; [cbn [pf_len] in *; lia | eassumption | eassumption | eassumption]
| cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_sb pf_len pf_tk pf_lenr pa_F ts_set_x ts_pbs];
intros; lazymatch goal with H : PE_INV_A _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => unfold ts_pbs, ts_set_x, ts_set_co in H; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in H end; eapply Kout; [| eassumption..]; cbn [pf_len t_co] in *; lia
| cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_sb pf_len pf_tk pf_lenr pa_F ts_set_x ts_pbs];
intros; lazymatch goal with H : PE_INV_A _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => unfold ts_pbs, ts_set_x, ts_set_co in H; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in H end; eapply Kerr16; [| eassumption..]; cbn [pf_len t_co] in *; lia ].
Qed.

Lemma seg_ofield_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (v2 ra2 k0 : Z) (nB : nat)
(gp t0 t1 t2 a3 a5 a6 a7 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa -> pf_fl pf = 0 ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
PBOK m ts k0 -> k0 <= 0 -> BOK pf pa ts B (S (Z.to_nat (16 * Z.max 0 (pf_len pf) + 8192) + nB)) ->
CSTR_OK pf payload ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_ofield ->
t_co ts < pf_len pf -> nth_error payload (Z.to_nat (t_co ts)) = Some cb ->
pe_s0 sv = Z_to_bv 64 v2 -> pe_ra sv = Z_to_bv 64 ra2 ->
(v2 < alloc_ceiling \/ v2 mod 8 <> 0 \/ v2 <= pa_sp0 pa \/ hiA_top A4L HIx - 16 <= v2) /\ 0 <= v2 < 2^64 ->
uw_ok A4L (hl_strdup A4L) (Z_to_bv 64 0x95f88) (UWfp ra2 v2) ->

(forall m' md' A' B' pbs' errv' co' cb' pj' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' F' fc',
t_co ts <= co' < pf_len pf -> nth_error payload (Z.to_nat co') = Some cb' ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B'
(ts_lvl (ts_pbs (ts_set_co ts co') pbs') (TL ST_string_escape ST_ofield (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) cb' nb pj' sv errv' ->
PBOK m' (ts_lvl (ts_pbs (ts_set_co ts co') pbs') (TL ST_string_escape ST_ofield (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) k0 ->
BOK pf pa (ts_lvl (ts_pbs (ts_set_co ts co') pbs') (TL ST_string_escape ST_ofield (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) B' nB ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msA asegs pf pa APE_BREAK co' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' (Z_to_bv 64 (pf_tk pf + 56)) (Z_to_bv 64 (pa_F pa + 64)) F' fc' m')) ->

(forall m' md' A' B' pbs' errv' co' cb' pj' r nn gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' F' fc',
t_co ts <= co' < pf_len pf -> nth_error payload (Z.to_nat co') = Some cb' -> r <> 0 -> 0 <= nn - 1 <= co' + k0 ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B'
(ts_lvl (ts_pbs (ts_set_co ts co') pbs') (TL ST_eatws ST_ofend (tl_cur l) (tl_cs l) (tl_cbs l) r [(r, nn)])) cb' nb pj' sv errv' ->
PBOK m' (ts_lvl (ts_pbs (ts_set_co ts co') pbs') (TL ST_eatws ST_ofend (tl_cur l) (tl_cs l) (tl_cbs l) r [(r, nn)])) k0 ->
BOK pf pa (ts_lvl (ts_pbs (ts_set_co ts co') pbs') (TL ST_eatws ST_ofend (tl_cur l) (tl_cs l) (tl_cbs l) r [(r, nn)])) B' nB ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msA asegs pf pa APE_BREAK co' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' (Z_to_bv 64 (pf_tk pf + 56)) (Z_to_bv 64 (pa_F pa + 64)) F' fc' m')) ->

(forall m' md' A' B' pbs' (e : word) co' cb' pj' errv' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' s11' t4' t6' F' fc',
t_co ts < co' <= pf_len pf ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B'
(ts_pbs (ts_set_x ts co' (TS (ts_isd (t_x ts)) (ts_stpos (t_x ts)) (Z_to_bv 64 co') e (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))) pbs') cb' nb pj' sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msO asegs pf pa APE_OUT x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' (Z_to_bv 64 (pf_tk pf + 56)) s11' t4' t6' F' fc' m')) ->

(forall m' md' A' B' pbs' (e : word) co' cb' pj' errv' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' s11' t4' t6' F' fc',
t_co ts < co' <= pf_len pf ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B'
(ts_pbs (ts_set_x ts co' (TS (ts_isd (t_x ts)) (ts_stpos (t_x ts)) (Z_to_bv 64 co') e (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))) pbs') cb' nb pj' sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msO asegs pf pa APE_ERRMEM x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' (Z_to_bv 64 (pf_tk pf + 56)) s11' t4' t6' F' fc' m')) ->

(forall m' md' A' B' pbs' errv' co' cb' pj' x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s10' s11' t3' t4' t5' t6' F' fc',
t_co ts <= co' < pf_len pf ->
PE_INVW_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' (ts_pbs (ts_set_co ts co') pbs') [] cb' nb pj' sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(Q1Y6.Mq2.pe_msE pf pa APE_ERR2 x1' gp' t0' t1' t2' (Z_to_bv 64 16) a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s10' s11' t3' t4' t5' t6' F' fc' m')) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa (pe_jtA ST_ofield) (t_co ts) gp t0 t1 t2
(Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) (Z_to_bv 64 (tl_st l))
(Z_to_bv 64 (q / 8 + 4 * Z.of_nat (t_depth ts) + A_SB)) a3 (Z_to_bv 64 APE_JTAB) a5 a6 a7
(Z_to_bv 64 (Z.of_nat (t_depth ts))) (Z_to_bv 64 q) (Z_to_bv 64 (pa_F pa + 64)) F fc m).
Proof.
intros until fc. intros STC BSL FL0 INV PBK K0 BK CSTR Hl Hst Hco Hc S0V RAV HV UWK Kbsl Kquote Kout Kerr16 Kerr2. pose proof INV as INV0. pe_openA STC INV.
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *. subst fl.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
unfold ts_set_co, ts_set_x, ts_pbs in Kbsl, Kquote, Kout, Kerr16, Kerr2.
cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in Kbsl, Kquote, Kout, Kerr16, Kerr2.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
pose proof FR as FR0. unfold pe_frameA in FR. destruct FR as (SLOTS & GAP & SAVED & FF & FSH).
unfold pe_slotsA in SLOTS. cbn zeta in SLOTS. unfold ff_cellsA in FF.
unfold pe_msA, pe_msO, Q1Y6.Mq2.pe_msE in *.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd 0) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 6 HP INtk ltac:(lia)) as SHT6.
replace (tk / 8 + 6 + A_SB) with (tk / 8 + 2147450886) in SHT6 by (unfold A_SB; lia).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(spf, spf + 312)] m) as MU.
pose proof (bv_unsigned_in_range 8 cb) as CBR; unfold bv_modulus in CBR; cbn in CBR.
pose proof (bv_unsigned_in_range 8 quote) as QR; unfold bv_modulus in QR; cbn in QR.
pose proof alloc_ceiling_range as ACR.
assert (PBK0 : PBOKat m ts0 (co + k0)) by (unfold PBOK in PBK; cbn [t_co ts0] in PBK; exact PBK).
unfold APE_BREAK, APE_OUT, APE_ERRMEM, APE_ERR2, APE_JTAB in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
stash Himg_t. stash Kbsl. stash Kquote. stash Kout. stash Kerr16. stash Kerr2. stash INV0. stash FR0. stash PBK0. stash BK. stash CSTR. stash UWK. stash HV.
clear PB REST LV OBJ HPR BUD GAP SAVED FSH STR ERR SBin TSK PBK.
reenterA asegs A4L HIx asegs_wx HP. rewrite Hst. unfold ST_ofield. cbn [pe_jtA].
step.
step. step.
sh_norm.
repeat match goal with
| |- context [ (?p + ?j) / 8 ] => is_Zlit j; rewrite (div8_add p j) by lia; let k := eval vm_compute in (Z.div j 8) in change (j / 8) with k
end.
step.
step.
step.
first [ if_true | if_false ]; rewrite ?sxb_zero, ?zxb_zero.
change (zxb cb) with (Z_to_bv 64 (bv_unsigned cb)).
step.
change (zxb quote) with (Z_to_bv 64 (bv_unsigned quote)).
step.
step.
step.
destruct (Z.eq_dec (bv_unsigned cb) (bv_unsigned quote)) as [EQ | NQ].
-
if_falsex. evt_done5.
unstash INV0. unstash PBK0. unstash BK. unstash Kquote. unstash Kerr2. unstash UWK. unstash HV.
eapply (ofl_quote_A (PEF tk oldl newl len lenr sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m md A B ts0 co k0 cb nb pj sv errv T _);
[exact STC | exact BSL | exact INV0 | exact PBK0 | exact K0 | exact BK | cbn [t_co ts0]; lia | cbn [t_co ts0 pf_len]; lia | |].
+ intros m1 md1 A1 B1 pbs1 errv1 x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F1 fc1 INV1 PBK1 BK1 FS1 FRM1.
eapply (ofl_name_A (PEF tk oldl newl len lenr sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m1 md1 A1 B1 (ts_pbs ts0 pbs1) l cb nb pj sv errv1 T (co + k0) v2 ra2 nB);
[exact STC | exact BSL | exact INV1 | exact PBK1 | cbn [pf_len]; lia | exact BK1 | exact Hl | exact Hst | exact S0V | exact RAV | exact HV | exact UWK | |].
* intros m2 md2 A2 B2 errv2 r nn gp2 t02 t12 t22 a02 a12 a22 a32 a42 a52 a62 a72 s52 F2 fc2 Hr PIN2 INV2 PBK2 BK2 FS2 FRM2.
eapply (Kquote m2 md2 A2 B2 pbs1 errv2 co cb pj r nn); [lia | exact Hc | exact Hr | exact PIN2 | exact INV2 | | exact BK2 | eapply fsaved_trans; [exact FS1 | exact FS2] | intros X; exact (FRM2 (FRM1 X))].
unfold PBOK. cbn [t_co ts_lvl ts_pbs ts0]. exact PBK2.
* intros m2 md2 A2 B2 errv2 x12 gp2 t02 t12 t22 a12 a22 a32 a42 a52 a62 a72 s32 s42 s52 s62 s72 s82 s102 s112 t32 t42 t52 t62 F2 fc2 INVW2 FS2 FRM2.
eapply (Kerr2 m2 md2 A2 B2 pbs1 errv2 co cb pj); [lia | apply (PE_INV_A_W HIx GA); exact INVW2 | eapply fsaved_trans; [exact FS1 | exact FS2] | intros X; exact (FRM2 (FRM1 X))].
+ intros m1 md1 A1 B1 errv1 x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s10' s11' t3' t4' t5' t6' F1 fc1 INV1 FS1 FRM1.
eapply (Kerr2 m1 md1 A1 B1 pbs errv1 co cb pj); [lia | apply (PE_INV_A_W HIx GA); exact INV1 | exact FS1 | exact FRM1].
-
if_truex.
step.
replace (Z_to_bv 64 0) with (Z_to_bv 64 (co - co)) by (f_equal; lia).
step. step.
step.
set (pj1 := PEJA (pj_0 pj) (pj_8 pj) (Z_to_bv 64 (bv_unsigned quote)) (pj_obj pj) (pj_288 pj) (pj_304 pj) (pj_gap pj) (pj_fhd pj) (pj_f1 pj) (pj_f2 pj)).
unstash INV0. unstash FR0. unstash PBK0.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, SLc : rw_cells asegs mc spf _ |- _ =>
evt_done5;
assert (FRc : pe_frameA asegs mc (PEF tk oldl newl len lenr sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) cb nb pj1 sv)
by (eapply (pe_frameA_slotw HIx (PEF tk oldl newl len lenr sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) _ LM FRS B A m mc md lo [] cb nb pj pj1 sv);
[ exact STC | exact HP | apply Forall_nil | exact FR0 | exact MUc | exact WMc | exact SLc | reflexivity | reflexivity | reflexivity | reflexivity ]);
destruct (PE_INV_A_framew HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m mc md A B ts0
cb nb pj sv errv [(spf, spf + 312)] cb nb pj1 STC INV0 MUc WMc MIc
ltac:(apply Forall_cons; [right; left; cbn [fst snd pf_spf pa_sp0]; lia | apply Forall_nil]) TOKc FRc) as [INV1 PBT1]
end end.
unstash BK. unstash CSTR. unstash Kbsl. unstash Kquote. unstash Kout. unstash Kerr16. unstash Kerr2. unstash UWK. unstash HV.
eapply (ofl_latch_A (Z.to_nat (len - co)) (PEF tk oldl newl len lenr sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo _ md A B ts0 l co k0 cb nb pj1 sv errv T _);
[exact STC | exact BSL | reflexivity | exact INV1 | exact (PBT1 _ PBK0) | exact K0 | exact BK | exact CSTR | exact Hl | exact Hst | cbn [t_co ts0]; lia | exact Hco | exact Hc | cbn [t_co ts0 pf_len]; lia | | | |].
+
intros m1 co' cb' pj' a0' a1' a2' a5' s3' Hco' Hcb' INV' PBK'. cbn [t_co ts0 pf_len] in Hco'.
eapply (ofl_bslash_A (PEF tk oldl newl len lenr sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m1 md A B (ts_set_co ts0 co') l co k0 cb' nb pj' sv errv T nB);
[exact STC | exact BSL | exact INV' | exact PBK' | exact K0 | exact (BOK_set_co _ _ ts0 B _ co' ltac:(cbn [t_co ts0]; lia) BK) | exact Hl | exact Hst
| cbn [t_co ts_set_co]; lia | cbn [t_co ts_set_co pf_len]; lia | |].
* intros m2 md2 A2 B2 pbs2 errv2 gp2 t02 t12 t22 a02 a12 a22 a32 a42 a52 a62 a72 s52 F2 fc2 INV2 PBK2 BK2 FS2 FRM2.
eapply (Kbsl m2 md2 A2 B2 pbs2 errv2 co' cb' pj'); [lia | exact Hcb' | exact INV2 | exact PBK2 | exact BK2 | exact FS2 | exact FRM2].
* intros m2 md2 A2 B2 errv2 x12 gp2 t02 t12 t22 a12 a22 a32 a42 a52 a62 a72 s32 s42 s52 s62 s72 s82 s102 s112 t32 t42 t52 t62 F2 fc2 INV2 FS2 FRM2.
eapply (Kerr2 m2 md2 A2 B2 pbs errv2 co' cb' pj'); [lia | apply (PE_INV_A_W HIx GA); exact INV2 | exact FS2 | exact FRM2].
+
intros m1 co' cb' pj' a0' a1' a2' a5' s3' s4' Hco' Hcb' INV' PBK'. cbn [t_co ts0 pf_len] in Hco'.
eapply (ofl_quote_A (PEF tk oldl newl len lenr sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m1 md A B (ts_set_co ts0 co') co k0 cb' nb pj' sv errv T _);
[exact STC | exact BSL | exact INV' | exact PBK' | exact K0 | exact (BOK_set_co _ _ ts0 B _ co' ltac:(cbn [t_co ts0]; lia) BK)
| cbn [t_co ts_set_co]; lia | cbn [t_co ts_set_co pf_len]; lia | |].
* intros m2 md2 A2 B2 pbs2 errv2 x12 gp2 t02 t12 t22 a02 a12 a22 a32 a42 a52 a62 a72 t32 t42 t52 t62 F2 fc2 INV2 PBK2 BK2 FS2 FRM2.
eapply (ofl_name_A (PEF tk oldl newl len lenr sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m2 md2 A2 B2 (ts_pbs (ts_set_co ts0 co') pbs2) l cb' nb pj' sv errv2 T (co' + k0) v2 ra2 nB);
[exact STC | exact BSL | exact INV2 | exact PBK2 | cbn [pf_len]; lia | exact BK2 | exact Hl | exact Hst | exact S0V | exact RAV | exact HV | exact UWK | |].
-- intros m3 md3 A3 B3 errv3 r nn gp3 t03 t13 t23 a03 a13 a23 a33 a43 a53 a63 a73 s53 F3 fc3 Hr PIN3 INV3 PBK3 BK3 FS3 FRM3.
eapply (Kquote m3 md3 A3 B3 pbs2 errv3 co' cb' pj' r nn); [lia | exact Hcb' | exact Hr | exact PIN3 | exact INV3 | | exact BK3 | eapply fsaved_trans; [exact FS2 | exact FS3] | intros X; exact (FRM3 (FRM2 X))].
unfold PBOK. cbn [t_co ts_lvl ts_pbs ts_set_co]. exact PBK3.
-- intros m3 md3 A3 B3 errv3 x13 gp3 t03 t13 t23 a13 a23 a33 a43 a53 a63 a73 s33 s43 s53 s63 s73 s83 s103 s113 t33 t43 t53 t63 F3 fc3 INVW3 FS3 FRM3.
eapply (Kerr2 m3 md3 A3 B3 pbs2 errv3 co' cb' pj'); [lia | apply (PE_INV_A_W HIx GA); exact INVW3 | eapply fsaved_trans; [exact FS2 | exact FS3] | intros X; exact (FRM3 (FRM2 X))].
* intros m2 md2 A2 B2 errv2 x12 gp2 t02 t12 t22 a12 a22 a32 a42 a52 a62 a72 s32 s42 s52 s62 s72 s82 s102 s112 t32 t42 t52 t62 F2 fc2 INV2 FS2 FRM2.
eapply (Kerr2 m2 md2 A2 B2 pbs errv2 co' cb' pj'); [lia | apply (PE_INV_A_W HIx GA); exact INV2 | exact FS2 | exact FRM2].
+
intros m1 md1 A1 B1 pbs1 e co' cb' errv1 x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' s11' t4' t6' F1 fc1 Hco' INV1' FS1 FRM1. cbn [t_co ts0 pf_len] in Hco'.
eapply (Kout m1 md1 A1 B1 pbs1 e co' cb' pj1 errv1); [lia | exact INV1' | exact FS1 | exact FRM1].
+ intros m1 md1 A1 B1 pbs1 e co' cb' errv1 x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' s11' t4' t6' F1 fc1 Hco' INV1' FS1 FRM1. cbn [t_co ts0 pf_len] in Hco'.
eapply (Kerr16 m1 md1 A1 B1 pbs1 e co' cb' pj1 errv1); [lia | exact INV1' | exact FS1 | exact FRM1].
Qed.
End PeSOfieldA.
End RC__1.
