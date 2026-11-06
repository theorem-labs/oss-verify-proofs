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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXfU.Mq0.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYZ0.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdGy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdGy.Mqe. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q63E.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q63E.Mqe. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QVob.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QVob.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QMmN.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QMmN.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QMgr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QMgr.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qeia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qeia.Mq7.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc5u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc5u. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QAzu.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QAzu.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6vt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6vt. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QV7s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QV7s.Mq3.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac QlEo_c1.solve_load ::= QXup.mkr__solve_load_3. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition APE_EUNI_HEX : Z := 0x97094.
Definition APE_EUNI_TAIL : Z := 0x98040.
Definition APE_EUNI_HSCLR : Z := 0x98588.
Definition APE_EUNI_ENC : Z := 0x98594.
Definition APE_EUNI_ARM1 : Z := 0x985a8.
Definition APE_EUNI_ARM2 : Z := 0x985f8.
Definition APE_EUNI_ARM3 : Z := 0x98abc.
Definition APE_EUNI_ARM4 : Z := 0x98b58.
Definition APE_EUNI_POP : Z := 0x9866c.
Definition APE_EUNI_REPL : Z := 0x98a70.
Definition APE_EUNI_REPB : Z := 0x98c0c.
Definition APE_EUNI_HS : Z := 0x98774.
Definition APE_EUNI_ERRP : Z := 0x99578.
Definition APE_EUNI_EOF : Z := 0x99678.
Section PeSEuniB.
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

Ltac nrm :=
sh_norm;
repeat match goal with
| |- context [ (?p + ?j) / 8 ] => is_Zlit j; rewrite (div8_add p j) by lia; let k := eval vm_compute in (Z.div j 8) in change (j / 8) with k
end.

Lemma euni_err_B :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet)
(gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
(forall m',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md A B ts cb nb pj sv errv ->
AJ5 A4L HIx A T md
(pe_msO asegs pf pa APE_ERR2 gp t0 t1 t2 (Z_to_bv 64 12) a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc m')) ->
AJ5 A4L HIx A T md
(pe_msO asegs pf pa APE_EUNI_ERRP gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc m).
Proof.
intros until fc. intros STC INV Kout. pose proof INV as INV0.
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
destruct INV as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof REST as (HP & _).
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
unfold ts_set_x, tx_err in Kout. cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in Kout.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
unfold pe_frameA in FR. destruct FR as (SLOTS & _). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS.
unfold pe_msO in *.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 4 HP INtk ltac:(lia)) as SHT4.
replace (tk / 8 + 4 + A_SB) with (tk / 8 + 2147450884) in SHT4 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 4 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT4t & _).
cbn [hl_sb A4L] in SEPT4t. assert (EQx : tk / 8 + A_SB + 4 = tk / 8 + 2147450884) by (unfold A_SB; lia). rewrite EQx in SEPT4t. clear EQx.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(tk, tk + 72)] m) as MU.
unfold APE_EUNI_ERRP, APE_ERR2 in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
stash Himg_t. clear PB TSK REST SEPT4t.
reenterA asegs A4L HIx asegs_wx HP.
step.
asan_rechkB.
step.
step.
evt_done5. eapply (Kout m). exact INV0.
Qed.

Lemma euni_eof_B :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet)
(gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_escape_unicode ->
(forall m' a1',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md A B (ts_set_x ts (t_co ts) (tx_err (t_x ts) (Z_to_bv 64 1))) cb nb pj sv errv ->
AJ5 A4L HIx A T md
(pe_msO asegs pf pa APE_OUT gp t0 t1 t2 (Z_to_bv 64 1) a1' (Z_to_bv 64 (pf_tk pf + 36)) a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc m')) ->
AJ5 A4L HIx A T md
(pe_msO asegs pf pa APE_EUNI_EOF gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc m).
Proof.
intros until fc. intros STC INV Hl Hst Kout. pose proof INV as INV0.
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
destruct INV as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof REST as (HP & _).
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
unfold ts_set_x, tx_err in Kout. cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in Kout.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
unfold pe_frameA in FR. destruct FR as (SLOTS & _). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS.
unfold pe_msO in *. unfold APE_EUNI_EOF in *.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * mxd) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t.
blk_factsA A4L HIx HP q (32 * mxd) Hqal Hqlo Hqhi Himg_q.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 4 HP INtk ltac:(lia)) as SHT4.
replace (tk / 8 + 4 + A_SB) with (tk / 8 + 2147450884) in SHT4 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 4 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT4t & _).
cbn [hl_sb A4L] in SEPT4t. assert (EQx : tk / 8 + A_SB + 4 = tk / 8 + 2147450884) by (unfold A_SB; lia). rewrite EQx in SEPT4t. clear EQx.
shq_facts HP INq INtk q mxd tk 0 0 SHQ0 SEPQ0c SEPQ0q SEPQ0t.
replace (q / 8 + 4 * 0 + 0 + A_SB) with (q / 8 + 2147450880) in SHQ0 by (unfold A_SB; lia).
pose proof (TSK depth l Hl) as Ld. unfold srec_cells in Ld. rewrite Hst in Ld.
assert (Hq8 : q mod 8 = 0) by (clear - Hqal; Z.div_mod_to_equations; lia).
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 2 HP INtk ltac:(lia)) as SHT2.
replace (tk / 8 + 2 + A_SB) with (tk / 8 + 2147450882) in SHT2 by (unfold A_SB; lia).
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 7 HP INtk ltac:(lia)) as SHT7.
replace (tk / 8 + 7 + A_SB) with (tk / 8 + 2147450887) in SHT7 by (unfold A_SB; lia).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(tk, tk + 72)] m) as MU.
unfold APE_OUT in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
stash Himg_t. stash Himg_q. clear PB TSK REST SEPT4t SEPQ0c SEPQ0q SEPQ0t.
reenterA asegs A4L HIx asegs_wx HP.
asan_rechkMB 1.

lazymatch goal with |- evt _ _ (MS ?R ?FF _ ?fcc None ?mm ?rom) =>
assert (EOFJ : forall a0x a1x, evt asegs (AJ5e A4L HIx A T md) (MS (bvmap_set 10 a0x (bvmap_set 11 a1x R)) FF (Z_to_bv 64 0x99720) fcc None mm rom)) end.
2:{ step. step.
norm_sx32.
step.
destruct depth as [|dp].
- if_false.
step.
asan_rechkB.
step. step.
step. if_falsex.
step. ub_land Hq8. step. ub_if_lit.
asan_chkB.
replace (q + 32 * Z.of_nat 0) with q in Ld by lia.
step.
norm_sx32.
step.
step.
if_truex. apply EOFJ.
- if_truex. apply EOFJ. }
intros a0x a1x.
step.
asan_rechkB.
step.
stepz.
step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _ |- _ =>
evt_done5;
destruct (PE_INV_A_tokw1 HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m mc md A B ts0
cb nb pj sv errv co (tx_err (t_x ts0) (Z_to_bv 64 1)) STC INV0 MUc WMc MIc TOKc ltac:(cbn [pf_len]; lia) eq_refl) as [INVe _];
eapply (Kout mc); exact INVe
end end.
Qed.

Lemma euni_hex_B :
forall (n : nat) (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel) (i kP : Z)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet)
(gp t0 a1 a2 a3 a4 a5 a6 a7 s3 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> pf_fl pf = 0 ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
PBOKat m ts kP -> CSTR_OK pf payload ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_escape_unicode ->
t_co ts < pf_len pf -> nth_error payload (Z.to_nat (t_co ts)) = Some cb -> bv_unsigned cb <> 0 ->
SPV (t_x ts) = i -> 0 <= i <= 3 -> bv_unsigned (ts_ucs (t_x ts)) mod 2^32 < 65536 -> 4 - i <= Z.of_nat n ->

(forall m' co' cb' (uw : Z) a0' a2' a3' a4' a6' s5',
co' = t_co ts + (3 - i) -> co' < pf_len pf -> nth_error payload (Z.to_nat co') = Some cb' -> 0 <= uw < 65536 ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md A B (ts_set_x ts co' (TS (ts_isd (t_x ts)) (Z_to_bv 64 4) (Z_to_bv 64 co') (ts_err (t_x ts)) (Z_to_bv 64 uw) (ts_high (t_x ts)) (ts_quote (t_x ts)))) cb' nb pj sv errv ->
PBOKat m' (ts_set_x ts co' (TS (ts_isd (t_x ts)) (Z_to_bv 64 4) (Z_to_bv 64 co') (ts_err (t_x ts)) (Z_to_bv 64 uw) (ts_high (t_x ts)) (ts_quote (t_x ts)))) kP ->
AJ5 A4L HIx A T md
(pe_msO asegs pf pa APE_EUNI_TAIL gp t0 (Z_to_bv 64 (pf_lenr pf)) (Z_to_bv 64 (pf_tk pf + 32)) a0' (Z_to_bv 64 (pf_tk pf / 8 + 2147450883)) a2' a3' a4' (Z_to_bv 64 uw) a6' a7 (Z_to_bv 64 (pf_tk pf / 8 + 2147450885)) (Z_to_bv 64 (pf_sb pf + co')) s5' s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc m')) ->

(forall m' co' cb' (stq uq : word) gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6',
t_co ts <= co' <= pf_len pf ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md A B (ts_set_x ts co' (TS (ts_isd (t_x ts)) stq (Z_to_bv 64 co') (ts_err (t_x ts)) uq (ts_high (t_x ts)) (ts_quote (t_x ts)))) cb' nb pj sv errv ->
AJ5 A4L HIx A T md
(pe_msO asegs pf pa APE_ERR2 gp' t0' t1' t2' (Z_to_bv 64 12) a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F fc m')) ->

(forall m' co' cb' (stq uq e : word) gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6',
t_co ts <= co' <= pf_len pf ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md A B (ts_set_x ts co' (TS (ts_isd (t_x ts)) stq (Z_to_bv 64 co') e uq (ts_high (t_x ts)) (ts_quote (t_x ts)))) cb' nb pj sv errv ->
AJ5 A4L HIx A T md
(pe_msO asegs pf pa APE_OUT gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F fc m')) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa APE_EUNI_HEX (t_co ts) gp t0 (Z_to_bv 64 (bv_unsigned cb)) a1 a2 a3 a4 a5 a6 a7 s3 (Z_to_bv 64 (pf_sb pf + t_co ts)) s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc m).
Proof.
induction n as [|n IH]; intros until fc; intros STC FL0 INV PBK CSTR Hl Hst Hco Hc Hnz ESP Hi HU Hn Ktail Kerr2 Kout.
{ exfalso. cbn in Hn. lia. }
pose proof INV as INV0. pose proof INV as INV0'.
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
destruct INV as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof REST as (HP & LV & OBJ & ST & ERR & STR & PLEN & SBin & HPR & MDV & G & BUD).
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *. subst fl.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
unfold ts_set_x in Ktail, Kerr2, Kout.
cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in Ktail, Kerr2, Kout.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
pose proof FR as FR0. unfold pe_frameA in FR. destruct FR as (SLOTS & GAP & SAVED & FF & FSH). unfold pe_msA, pe_msO in *.
unfold pe_slotsA in SLOTS. cbn zeta in SLOTS. unfold pe_savedA_cells in SAVED. unfold ff_cellsA in FF. unfold ffsh_cells, FSH0 in FSH. cbn [map] in FSH.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
unfold SPV in ESP. cbn [ts_stpos] in ESP.
set (u := bv_unsigned ucs mod 2^32) in *.
assert (U0 : 0 <= u) by (unfold u; apply Z.mod_pos_bound; lia).
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd 0) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * mxd) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd 0) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t.
blk_factsA A4L HIx HP q (32 * mxd) Hqal Hqlo Hqhi Himg_q.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 3 HP INtk ltac:(lia)) as SHT3.
replace (tk / 8 + 3 + A_SB) with (tk / 8 + 2147450883) in SHT3 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 3 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT3t & _).
cbn [hl_sb A4L] in SEPT3t. assert (EQx : tk / 8 + A_SB + 3 = tk / 8 + 2147450883) by (unfold A_SB; lia). rewrite EQx in SEPT3t. clear EQx.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 4 HP INtk ltac:(lia)) as SHT4.
replace (tk / 8 + 4 + A_SB) with (tk / 8 + 2147450884) in SHT4 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 4 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT4t & _).
cbn [hl_sb A4L] in SEPT4t. assert (EQx : tk / 8 + A_SB + 4 = tk / 8 + 2147450884) by (unfold A_SB; lia). rewrite EQx in SEPT4t. clear EQx.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 5 HP INtk ltac:(lia)) as SHT5.
replace (tk / 8 + 5 + A_SB) with (tk / 8 + 2147450885) in SHT5 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 5 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT5t & _).
cbn [hl_sb A4L] in SEPT5t. assert (EQx : tk / 8 + A_SB + 5 = tk / 8 + 2147450885) by (unfold A_SB; lia). rewrite EQx in SEPT5t. clear EQx.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 8 HP INtk ltac:(lia)) as SHT8.
replace (tk / 8 + 8 + A_SB) with (tk / 8 + 2147450888) in SHT8 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 8 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT8t & _).
cbn [hl_sb A4L] in SEPT8t. assert (EQx : tk / 8 + A_SB + 8 = tk / 8 + 2147450888) by (unfold A_SB; lia). rewrite EQx in SEPT8t. clear EQx.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (q_ne_tkA HIx _ _ _ _ _ _ _ _ _ _ HP) as Hqtk. cbn [pf_tk] in Hqtk.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ tk 72 q (32 * mxd) HP (in_or_app _ LM _ (or_introl INtk)) (in_or_app _ LM _ (or_introl INq)) ltac:(congruence)) as Hdtq.
shq_facts HP INq INtk q mxd tk 0 0 SHQ0 SEPQ0c SEPQ0q SEPQ0t.
replace (q / 8 + 4 * 0 + 0 + A_SB) with (q / 8 + 2147450880) in SHQ0 by (unfold A_SB; lia).
assert (EQx : q / 8 + A_SB + (4 * 0 + 0) = q / 8 + 2147450880) by (unfold A_SB; lia). rewrite EQx in SEPQ0c, SEPQ0q, SEPQ0t. clear EQx.
pose proof (TSK depth l Hl) as Ld. remember (q + 32 * Z.of_nat depth) as bse eqn:Hbse in Ld. unfold srec_cells in Ld. rewrite Hst in Ld.
assert (HbseR : q <= bse /\ bse + 32 <= q + (32 * mxd)) by (subst bse; lia).
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
unfold APE_OUT, APE_ERR2, APE_EUNI_HEX, APE_EUNI_TAIL in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8, A_SB in *.
pose proof (munch_refl [(tk, tk + 72); (Ff + 64, Ff + 65)] m) as MU.
assert (HW : Forall (pe_wtfA (PEF tk oldl newl len lenr sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl)) [(tk, tk + 72); (Ff + 64, Ff + 65)]).
{ apply Forall_cons; [left; cbn [fst snd pf_tk]; lia |]. apply Forall_cons; [| apply Forall_nil]. right; right; left. cbn [fst snd pa_F]. lia. }
assert (cs_L_tk : csep bse 32 tk (Z.of_nat 72)) by (unfold csep; clear - Hdtq HbseR; lia).
assert (cs_FF_T : csep Ff 248 tk (Z.of_nat 72)) by (unfold csep; clear - DFt; lia).
assert (cs_T_FF : csep tk 72 Ff (Z.of_nat 248)) by (unfold csep; clear - DFt; lia).
assert (cs_Q0_T : csep (q / 8 + 2147450880) 1 tk (Z.of_nat 72)) by (unfold csep; clear - SEPQ0t; lia).
assert (cs_T3_T : csep (tk / 8 + 2147450883) 1 tk (Z.of_nat 72)) by (unfold csep; clear - SEPT3t; lia).
assert (cs_T4_T : csep (tk / 8 + 2147450884) 1 tk (Z.of_nat 72)) by (unfold csep; clear - SEPT4t; lia).
assert (cs_T5_T : csep (tk / 8 + 2147450885) 1 tk (Z.of_nat 72)) by (unfold csep; clear - SEPT5t; lia).
assert (cs_T8_T : csep (tk / 8 + 2147450888) 1 tk (Z.of_nat 72)) by (unfold csep; clear - SEPT8t; lia).
clear LV OBJ HPR Hdtq SEPQ0c SEPQ0q SEPQ0t SEPT3t SEPT4t SEPT5t SEPT8t.
stash PB. stash TSK. stash GAP. stash SAVED. stash FSH. stash DSF. stash DFt.
stash IH. stash Ktail. stash Kerr2. stash Kout. stash INV0. stash REST. stash FR0. stash PBK. stash SBc. stash SBhi. stash Hc. stash STR. stash HW. stash Himg_t. stash Himg_q.
assert (SBpos : 0 < sb) by (exact (pe_sb_pos HIx GA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV0' ltac:(cbn [pf_len]; lia))).
reenterA asegs A4L HIx asegs_wx HP.
step. step.
step.
replace (Z_to_bv 64 (-11)) with (Z_to_bv 64 (2^64 - 11)) by (apply bv_eq; vm_compute; reflexivity).

lazymatch goal with |- evt _ _ (MS ?R ?FF _ ?fcc None ?mm ?rom) =>
assert (DIGJ : forall (d : Z) a0x a1x a2x, 0 <= d < 16 ->
evt asegs (AJ5e A4L HIx A T md) (MS (bvmap_set 16 (Z_to_bv 64 d) (bvmap_set 10 a0x (bvmap_set 11 a1x (bvmap_set 12 a2x R)))) FF (Z_to_bv 64 0x970d0) fcc None mm rom)) end.
2:{
assert (HXL : forall c, 0 <= c < 256 -> 65 <= Z.land c 223 <= 70 -> 1 <= Z.land c 7 <= 6 /\ 58 <= c).
{ intros c Rc Hc223.
assert (Hin : In c (map Z.of_nat (seq 0 256))) by (apply in_map_iff; exists (Z.to_nat c); split; [lia | apply in_seq; lia]).
assert (ALL : forallb (fun c => implb ((65 <=? Z.land c 223) && (Z.land c 223 <=? 70)) ((1 <=? Z.land c 7) && (Z.land c 7 <=? 6) && (58 <=? c))) (map Z.of_nat (seq 0 256)) = true) by (vm_compute; reflexivity).
rewrite forallb_forall in ALL. specialize (ALL c Hin).
replace ((65 <=? Z.land c 223) && (Z.land c 223 <=? 70)) with true in ALL by (symmetry; apply andb_true_iff; split; apply Z.leb_le; lia).
cbn [implb] in ALL. apply andb_true_iff in ALL as [ALL A3]. apply andb_true_iff in ALL as [A1 A2]. apply Z.leb_le in A1, A2, A3. lia. }
pose proof (OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.Bytes.land_lt_pow2 (bv_unsigned cb) 223 8 ltac:(lia) ltac:(lia)) as X223.

lazymatch goal with |- evt _ _ (MS ?R ?FF _ ?fcc None ?mm ?rom) =>
assert (LETTER : forall a1y a2y, evt asegs (AJ5e A4L HIx A T md) (MS (bvmap_set 11 a1y (bvmap_set 12 a2y R)) FF (Z_to_bv 64 0x970a0) fcc None mm rom)) end.
{ intros a1y a2y.
step. step. step.
step.
rewrite (unsigned_lit (bv_unsigned cb)) by lia.
replace (Z_to_bv 64 (-7)) with (Z_to_bv 64 (2^64 - 7)) by (apply bv_eq; vm_compute; reflexivity).
destruct (Z_le_dec 65 (Z.land (bv_unsigned cb) 223)) as [G65 | L65]; [destruct (Z_le_dec (Z.land (bv_unsigned cb) 223) 70) as [L70 | G70] |].
+
destruct (HXL _ CBR (conj G65 L70)) as [HX7 HX58].
remember (Z.land (bv_unsigned cb) 223) as x223 eqn:Ex223.
replace (Z_to_bv 64 (x223 + -71)) with (Z_to_bv 64 (x223 + -71 + 2^64)).
2:{ apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
rewrite <- (Z_mod_plus_full (x223 + -71) 1 (2^64)). f_equal. }
if_truex.
step.
step.
if_falsex.
step. step.
step.
rewrite (unsigned_lit (bv_unsigned cb)) by lia.
apply (DIGJ (Z.land (bv_unsigned cb) 7 + 9)). lia.
+
remember (Z.land (bv_unsigned cb) 223) as x223 eqn:Ex223.
if_falsex. step.
evt_done5. unstash INV0. unstash Kerr2.
eapply (euni_err_B (PEF tk oldl newl len lenr sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m md A B ts0 cb nb pj sv errv T); [exact STC | exact INV0 |].
intros m' INVe. eapply (Kerr2 m' co cb stpos ucs); [lia | exact INVe].
+
remember (Z.land (bv_unsigned cb) 223) as x223 eqn:Ex223.
replace (Z_to_bv 64 (x223 + -71)) with (Z_to_bv 64 (x223 + -71 + 2^64)).
2:{ apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
rewrite <- (Z_mod_plus_full (x223 + -71) 1 (2^64)). f_equal. }
if_falsex. step.
evt_done5. unstash INV0. unstash Kerr2.
eapply (euni_err_B (PEF tk oldl newl len lenr sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m md A B ts0 cb nb pj sv errv T); [exact STC | exact INV0 |].
intros m' INVe. eapply (Kerr2 m' co cb stpos ucs); [lia | exact INVe]. }
destruct (Z_le_dec 48 (bv_unsigned cb)) as [G48 | L48]; [destruct (Z_le_dec (bv_unsigned cb) 57) as [L57 | G57] |].
-
replace (Z_to_bv 64 (bv_unsigned cb + -58)) with (Z_to_bv 64 (bv_unsigned cb + -58 + 2^64)).
2:{ apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
rewrite <- (Z_mod_plus_full (bv_unsigned cb + -58) 1 (2^64)). f_equal. }
if_truex.
step.
step.
if_truex.
step.
step.
rewrite (unsigned_lit (bv_unsigned cb)) by lia. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. rewrite (Z.mod_small (bv_unsigned cb) (2^8)) by lia.
apply (DIGJ (bv_unsigned cb + -48)). lia.
-
if_falsex. apply LETTER.
-
replace (Z_to_bv 64 (bv_unsigned cb + -58)) with (Z_to_bv 64 (bv_unsigned cb + -58 + 2^64)).
2:{ apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
rewrite <- (Z_mod_plus_full (bv_unsigned cb + -58) 1 (2^64)). f_equal. }
if_falsex. apply LETTER. }
intros d a0x a1x a2x Hd.
step.
step. step.
nrm.
step.
rewrite ?sxb_zero.
step.
if_false.
step.
rewrite (sx32_small_mod stpos) by (rewrite ESP; lia). rewrite ESP.
step.
step.
rewrite (unsigned_lit i) by lia.
step.
norm_w32.
step. if_truex.
step. step. step.
rewrite (unsigned_lit (3 - i + 536870912)) by lia. unfold bv_wrap. change (bv_modulus 32) with (2^32). rewrite (Z.mod_small (3 - i + 536870912) (2^32)) by lia.
rewrite Z.shiftr_div_pow2 by lia. rewrite (Z.div_small (3 - i + 536870912) (2^30)) by lia. rewrite (swrap32_id 0) by lia.
step. if_truex.
step.
rewrite (unsigned_lit (3 - i)) by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4. rewrite (swrap32_id ((3 - i) * 4)) by lia. replace ((3 - i) * 4) with (12 - i * 4) by lia.
step. step.
step. if_truex.
asan_chkB.
step.
rewrite (sx32_small_mod ucs) by (fold u; lia). fold u.
step.
rewrite (unsigned_lit d) by lia. rewrite (unsigned_lit (12 - i * 4)) by lia. rewrite (Z.mod_small (12 - i * 4) 32) by lia.
assert (DS : 0 <= d ≪ (12 - i * 4) < 65536).
{ assert (Ei : i = 0 \/ i = 1 \/ i = 2 \/ i = 3) by lia. destruct Ei as [-> | [-> | [-> | ->]]]; rewrite Z.shiftl_mul_pow2 by lia;
[change (2 ^ (12 - 0 * 4)) with 4096 | change (2 ^ (12 - 1 * 4)) with 256 | change (2 ^ (12 - 2 * 4)) with 16 | change (2 ^ (12 - 3 * 4)) with 1]; lia. }
remember (d ≪ (12 - i * 4)) as ds eqn:Eds.
norm_w32.
step.
rewrite (unsigned_lit ds) by lia. rewrite (unsigned_lit u) by lia.
pose proof (OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.Bytes.lor_lt_pow2 u ds 16 ltac:(lia) ltac:(lia)) as UW. change (2 ^ 16) with 65536 in UW.
remember (Z.lor u ds) as uw eqn:Euw.
step.
norm_w32.
step.
step. if_truex.
asan_rechkB.
step.
step.
step.
step.
unstash INV0. unstash REST. unstash FR0. unstash HW. unstash PBK. unstash Hc.
clear ESP.
destruct (Z.eq_dec i 3) as [E3 | N3].
-
if_truex.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, FFc : rw_cells asegs mc Ff _ |- _ =>
assert (FRc : pe_frameA asegs mc (PEF tk oldl newl len lenr sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) cb nb pj sv)
by (eapply (pe_frameA_scan HIx) with (ts := ts0); [exact STC | exact (proj1 REST) | exact FR0 | exact MUc | exact WMc | exact FFc]);
evt_done5;
destruct (PE_INV_A_tokw HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m mc md A B ts0
cb nb pj sv errv _ co (TS isd (Z_to_bv 64 (i + 1)) (Z_to_bv 64 co) err (Z_to_bv 64 uw) high quote) cb nb STC INV0 MUc WMc MIc HW TOKc FRc
ltac:(cbn [pf_len]; lia) eq_refl) as [INV1 PBK1]
end end.
subst i. change (3 + 1) with 4 in *. unstash Ktail.
eapply (Ktail _ co cb uw); [lia | lia | exact Hc | lia | exact INV1 | exact (PBK1 _ PBK)].
- if_falsex.
step. step.
step. if_truex.
step.
asan_rechkB.
step.
norm_sx32.
step.
norm_w32.
step. if_truex.
step.
asan_rechkB.
step.
step.
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
cb nb pj sv errv _ (co + 1) (TS isd (Z_to_bv 64 (i + 1)) (Z_to_bv 64 (co + 1)) err (Z_to_bv 64 uw) high quote) cb nb STC INV0 MUc WMc MIc HW TOKc FRc
ltac:(cbn [pf_len]; lia) eq_refl) as [INV1 PBK1]
end end.
unstash Kout.
eapply (euni_eof_B (PEF tk oldl newl len len sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo _ md A B
(ts_set_x ts0 (co + 1) (TS isd (Z_to_bv 64 (i + 1)) (Z_to_bv 64 (co + 1)) err (Z_to_bv 64 uw) high quote)) l cb nb pj sv errv T);
[exact STC | exact INV1 | exact Hl | exact Hst |].
intros mq a1q INVe. eapply (Kout mq (co + 1) cb (Z_to_bv 64 (i + 1)) (Z_to_bv 64 uw) (Z_to_bv 64 1)); [cbn [pf_len]; lia | exact INVe]. }
if_truex.

destruct (nth_error payload (Z.to_nat (co + 1))) as [c2|] eqn:Hc2; [| apply nth_error_None in Hc2; lia].
pose proof (bv_unsigned_in_range 8 c2) as CBR2; unfold bv_modulus in CBR2; cbn in CBR2.
pose proof (payload_shadow_pe HIx (PEF tk oldl newl len lenr sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) LB0 FRS _ _ _ _ _ _ _ (co + 1) HP
ltac:(intros bb Hbb; unfold pe_blocksA; apply in_or_app; right; right; right; exact Hbb) PL ltac:(cbn [pf_len]; lia)) as (v1 & SHP1 & Hv1).
cbn [pf_sb] in SHP1, Hv1. unfold A_SB in SHP1. replace (sb + (co + 1)) with (sb + co + 1) in SHP1, Hv1 by lia.
unstash SBhi. unstash DSF. unstash SBc.
pose proof (shadow_blk_apart HIx _ _ _ _ _ _ _ _ _ (sb + co + 1) 1 HP INtk' ltac:(lia) ltac:(lia) ltac:(lia)) as DSPt. unfold shA, A_SB in DSPt.
assert (SHPF : (sb + co + 1) / 8 + 2147450880 + 1 <= Ff \/ Ff + 256 <= (sb + co + 1) / 8 + 2147450880) by (clear - DSF SBhi SB0 CO Hmore; Z.div_mod_to_equations; lia).
lazymatch goal with MUc : munch _ m ?mc |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
apply (fun H => ro_cells_transport asegs _ m mc _ _ H MUc) in SHP1; [| cbn [disjoint_from fst snd cells_size csize Z.of_nat]; clear - DSPt SHPF; lia] end.
assert (LE1 : le1 (zxb c2) = [c2]).
{ unfold le1, zxb. cbn [Z_to_le_bytes pf_mxd]. f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 8) with 256%Z. change (bv_modulus 64) with 18446744073709551616%Z. Z.div_mod_to_equations. nia. }
stash DSF. stash SBc. stash DSPt. stash SHPF. stash Hv1. stash LE1. stash INV0. stash REST. stash FR0. stash HW. stash Hc. stash Hc2. stash PBK.
step.
asan_rechkB.
step.
lazymatch goal with TOKc : rw_cells asegs ?mc tk _ |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (tok_flags_byteA mxd 0 mc tk pb (Z.of_nat depth) q (TS isd (Z_to_bv 64 (i + 1)) (Z_to_bv 64 (co + 1)) err (Z_to_bv 64 uw) high quote) TOKc) as RDF end.
step.
rewrite ?zxb_zero. clear RDF.
step.
step.
step.
if_true.
step. step.
sh_norm.

lazymatch goal with |- evt _ _ (MS ?R ?FF _ ?fcc None ?mm ?rom) =>
assert (JOIN : forall a0y a1y, evt asegs (AJ5e A4L HIx A T md) (MS (bvmap_set 10 a0y (bvmap_set 11 a1y R)) FF (Z_to_bv 64 0x97210) fcc None mm rom)) end.
2:{ unstash Hv1. destruct Hv1 as [-> | [Hv8 Hvlt]].
- step. rewrite ?sxb_zero. step. if_false. apply JOIN.
- step. rewrite (sxb_small v1) by lia. step. if_truex.
step.
rewrite (unsigned_lit (sb + co + 1)) by lia. rewrite (land7_mod8 (sb + co + 1)) by lia.
pose proof (Z.mod_pos_bound (sb + co + 1) 8 ltac:(lia)) as R8. remember ((sb + co + 1) mod 8) as r8 eqn:Er8 in *.
step.
if_truex. apply JOIN. }
intros a0y a1y. clear SHP1.
unstash REST. unstash STR. unstash HW. unstash Hc2.
lazymatch goal with MUc : munch _ m ?mc |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (payload_privateA HIx _ _ _ _ _ _ _ ts0 _ _ _ _ _ _ _ STC (proj1 REST) STR PLEN (or_intror PL) MUc (pe_wtfA_private _ _ q pbs _ HW)) as STRc end.
cbn [pf_sb] in STRc.
pose proof (payload_byteA _ _ _ _ _ STRc Hc2 ltac:(lia)) as RDC. replace (sb + (co + 1)) with (sb + co + 1) in RDC by lia.
stash REST. stash STR. stash HW. clear STRc.
step.
change (zxb c2) with (Z_to_bv 64 (bv_unsigned c2)). clear RDC.
clear SHT3 SHT4 SHT5 SHT8 SHQ0 Ld.
unstash LE1.
step.
step.
replace (le1 (Z_to_bv 64 (bv_unsigned c2))) with [c2] by (rewrite <- LE1; reflexivity). mem_after_store.
step.
step.
unstash REST. unstash HW. unstash INV0. unstash FR0. unstash PBK. unstash Hc2.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, FFc : rw_cells asegs mc Ff _ |- _ =>
assert (FRc : pe_frameA asegs mc (PEF tk oldl newl len lenr sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) c2 nb pj sv)
by (eapply (pe_frameA_scan HIx) with (ts := ts0); [exact STC | exact (proj1 REST) | exact FR0 | exact MUc | exact WMc | exact FFc]);
destruct (PE_INV_A_tokw HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m mc md A B ts0
cb nb pj sv errv _ (co + 1) (TS isd (Z_to_bv 64 (i + 1)) (Z_to_bv 64 (co + 1)) err (Z_to_bv 64 uw) high quote) c2 nb STC INV0 MUc WMc MIc HW TOKc FRc
ltac:(cbn [pf_len]; lia) eq_refl) as [INV1 PBK1]
end end.
destruct (Z.eq_dec (bv_unsigned c2) 0) as [E0 | N0].
+
if_falsex. step.
replace (sb + co + 1) with (sb + (co + 1)) by lia.
evt_done5. unstash Kerr2.
eapply (euni_err_B (PEF tk oldl newl len lenr sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo _ md A B
(ts_set_x ts0 (co + 1) (TS isd (Z_to_bv 64 (i + 1)) (Z_to_bv 64 (co + 1)) err (Z_to_bv 64 uw) high quote)) c2 nb pj sv errv T); [exact STC | exact INV1 |].
intros m' INVe. eapply (Kerr2 m' (co + 1) c2 (Z_to_bv 64 (i + 1)) (Z_to_bv 64 uw)); [cbn [pf_len]; lia | exact INVe].
+ if_truex.
replace (sb + co + 1) with (sb + (co + 1)) by lia.
evt_done5.
unstash IH. unstash Ktail. unstash Kerr2. unstash Kout.
eapply (IH (PEF tk oldl newl len lenr sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo _ md A B
(TST depth levels (co + 1) pb pbs (TS isd (Z_to_bv 64 (i + 1)) (Z_to_bv 64 (co + 1)) err (Z_to_bv 64 uw) high quote) obj objs objbs) l (i + 1) kP c2 nb pj sv errv T);
[ exact STC | reflexivity | exact INV1 | exact (PBK1 _ PBK) | exact CSTR | exact Hl | exact Hst | cbn [t_co pf_len]; lia | exact Hc2 | exact N0
| unfold SPV; cbn [t_x ts_stpos]; rewrite unsigned_lit by lia; apply Z.mod_small; lia | lia
| cbn [t_x ts_ucs]; rewrite unsigned_lit by lia; rewrite Z.mod_small by lia; lia | lia
| cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_sb pf_len pf_tk pf_lenr pa_F ts_set_x];
intros; eapply Ktail; [lia | eassumption | eassumption | eassumption | eassumption | eassumption]
| cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_sb pf_len pf_tk pf_lenr pa_F ts_set_x];
intros; eapply Kerr2; [| eassumption]; cbn [pf_len] in *; lia
| cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_sb pf_len pf_tk pf_lenr pa_F ts_set_x];
intros; eapply Kout; [| eassumption]; cbn [pf_len] in *; lia ].
Qed.

Lemma euni_pop_B :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP : Z)
(gp t0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv -> PBOK m ts kP ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_escape_unicode ->
(forall c hn, lvl_mode (tl_st l) (tl_ss l) = Some (c, hn) -> lvl_mode (tl_ss l) (tl_ss l) = Some (c, hn)) ->
zin (tl_ss l) [ST_array_add; ST_ovadd] = false ->

(forall m' a0' a1' a2' a3' a4',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md A B (ts_lvl ts (TL (tl_ss l) (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) cb nb pj sv errv ->
PBOK m' (ts_lvl ts (TL (tl_ss l) (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) kP ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa APE_BREAK (t_co ts) gp t0 a0' a1' a2' a3' a4' a5 a6 a7 s3 (Z_to_bv 64 2) s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc m')) ->
AJ5 A4L HIx A T md (pe_msO asegs pf pa APE_EUNI_POP gp t0 (Z_to_bv 64 (pf_lenr pf)) (Z_to_bv 64 (pf_tk pf + 32)) a0 a1 a2 a3 a4 a5 a6 a7 s3 (Z_to_bv 64 (pf_sb pf + t_co ts)) s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc m).
Proof.
intros until fc. intros STC INV PBK Hl Hst HMODE Hzss Kbreak. pose proof INV as INV0. pe_openA STC INV.
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
unfold APE_BREAK, APE_EUNI_POP in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
assert (cs_tk_L : csep tk 72 bse (Z.of_nat 32)) by (unfold csep; clear - Hdtq HbseR; lia).
assert (cs_L_tk : csep bse 32 tk (Z.of_nat 72)) by (unfold csep; clear - Hdtq HbseR; lia).
clear Hdtq SEPQ0c SEPQ0q SEPQ0t SEPT7c SEPT7q SEPT7t SEPT2c SEPT2q SEPT2t.
stash Himg_t. stash Himg_q. stash Kbreak. clear PB REST TSK LV OBJ HPR BUD GAP SAVED FSH FF STR ERR SBin SHT SHQ SHQ4.
reenterA asegs A4L HIx asegs_wx HP.
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

Lemma euni_enc1_B :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (u kP : Z)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kB : nat)
(x1 gp t0 t1 t2 a0 a1 a2 a4 a5 a6 a7 s3 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
PBOKat m ts kP -> kP + 1 <= t_co ts + 1 -> BOK pf pa ts B kB -> 0 <= u <= 127 ->

(forall m' md' A' B' pbs' errv' pj' gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' (ts_pbs ts pbs') cb nb pj' sv errv' ->
PBOKat m' (ts_pbs ts pbs') (kP + 1) -> BOK pf pa (ts_pbs ts pbs') B' kB ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msO asegs pf pa APE_EUNI_POP gp' t0' (Z_to_bv 64 (pf_lenr pf)) (Z_to_bv 64 (pf_tk pf + 32)) a0' a1' a2' a3' a4' a5' a6' a7' s3' (Z_to_bv 64 (pf_sb pf + t_co ts)) s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' m')) ->

(forall m' md' A' B' errv' pj' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' (ts_set_x ts (t_co ts) (tx_err (t_x ts) (Z_to_bv 64 16))) cb nb pj' sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msO asegs pf pa APE_OUT gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' m')) ->
AJ5 A4L HIx A T md
(pe_msX asegs pf pa APE_EUNI_ARM1 x1 gp t0 t1 t2 a0 a1 a2 (Z_to_bv 64 u) a4 a5 a6 a7 s3 (Z_to_bv 64 (pf_sb pf + t_co ts)) s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc m).
Proof.
intros until fc. intros STC BSL INV PBK Hroom BK Hu Kpop Kout. pose proof INV as INV0.
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
destruct INV as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof REST as (HP & _).
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
unfold ts_set_x, tx_err, ts_pbs in Kpop, Kout. cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in Kpop, Kout.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
pose proof FR as FR0. unfold pe_frameA in FR. destruct FR as (SLOTS & GAP & SAVED & FF & FSH).
unfold pe_slotsA in SLOTS. cbn zeta in SLOTS. unfold ff_cellsA in FF. unfold ffsh_cells, FSH0 in FSH. cbn [map] in FSH.
unfold pe_msX, pe_msA, pe_msO in *.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 1 HP INtk ltac:(lia)) as SHT1.
replace (tk / 8 + 1 + A_SB) with (tk / 8 + 2147450881) in SHT1 by (unfold A_SB; lia).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs m) as WM.
pose proof alloc_ceiling_range as ACR.
assert (INF : In (Ff, 2) ((Ff, 2) :: FRS)) by (left; reflexivity).
assert (INtk' : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0 ++ LM)) by (apply in_or_app; left; exact INtk).
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP INF INtk') as DFt. rewrite fr_size_2 in DFt.
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP INF) as DSF. rewrite fr_size_2 in DSF. cbn [hl_sb A4L] in DSF.
assert (GF0' : 0 <= Ff) by lia. assert (GFc' : Ff < alloc_ceiling) by lia.
pose proof (shadow_blk_apart HIx _ _ _ _ _ _ _ _ _ Ff 32 HP INtk' GF0' GFc' ltac:(lia)) as DSt.
unfold APE_OUT, APE_EUNI_ARM1, APE_EUNI_POP in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8, A_SB in *.
pose proof (munch_refl [(tk, tk + 72); (Ff, Ff + 248); (Ff / 8 + 2147450880, Ff / 8 + 2147450880 + 32)] m) as MU.
stash Himg_t. stash Kpop. stash Kout. stash INV0. stash FR0. stash PBK. stash BK. stash GAP. stash SAVED. stash PB. stash TSK. stash REST.
reenterA asegs A4L HIx asegs_wx HP.
step.
stepz.
assert (LEU : le1 (Z_to_bv 64 u) = [Z_to_bv 8 u]).
{ unfold le1. rewrite unsigned_lit by lia. cbn [Z_to_le_bytes]. reflexivity. }
step.
step.
step.
step.
rewrite LEU. mem_after_store.
step.
sh_norm.
repeat match goal with
| |- context [ (?p + ?j) / 8 ] => is_Zlit j; rewrite (div8_add p j) by lia; let k := eval vm_compute in (Z.div j 8) in change (j / 8) with k
end.
step.
rewrite ?sxb_zero, ?zxb_zero.
step.
first [ if_true | if_false ].
step.
step.
step.

unstash INV0. unstash FR0. unstash PBK. unstash BK. unstash REST.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, FFc : rw_cells asegs mc Ff ?ffc, FSHc : rw_cells asegs mc (Ff / 8 + 2147450880) ?shc |- _ =>
assert (HW : Forall (pe_wtfA (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl)) [(tk, tk + 72); (Ff, Ff + 248); (Ff / 8 + 2147450880, Ff / 8 + 2147450880 + 32)])
by (apply Forall_cons; [left; cbn [fst snd pf_tk]; lia |]; apply Forall_cons; [right; right; left; cbn [fst snd pa_F]; lia |]; apply Forall_cons; [right; right; right; unfold shA, A_SB; cbn [fst snd pa_F]; lia | apply Forall_nil]);
assert (FRXc : pe_frameAX mc (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) nb pj sv ffc shc)
by (eapply (pe_frameAX_write HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS B ts0 A m mc md lo nb pj sv); [exact STC | exact HP | exact (pe_frameAX_of_A _ _ _ _ _ _ _ FR0) | exact MUc | exact WMc | exact FFc | exact FSHc]);
destruct (PE_INV_AX_tokw HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m mc md A B ts0 errv _ co (t_x ts0) _ _ STC (PE_INV_AX_of_A HIx GA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV0) MUc WMc MIc HW TOKc FRXc
ltac:(cbn [pf_len]; lia) eq_refl) as [INVX1 PBKX1];

assert (SRCB : bytes_at asegs mc (Ff + 80) [Z_to_bv 8 u])
by (pose proof FFc as FFs;
change ffc with ([CB 24 (pj_fhd pj); CB 40 (pj_f1 pj); C1 cb; CB 15 (firstn 15 (pj_f2 pj))] ++ ([C1 (Z_to_bv 8 u)] ++ [CB 167 (skipn 16 (pj_f2 pj))])) in FFs;
apply (proj1 (rw_cells_app asegs _ _ _ _)) in FFs as [_ FFs]; apply (proj1 (rw_cells_app asegs _ _ _ _)) in FFs as [FFs _];
cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.add_carry] in FFs; destruct FFs as [[_ HB] _]; exact HB);
assert (UNP : unpoisoned asegs mc 2147450880 (Ff + 80) 1)
by (pose proof FSHc as FSs;
match type of FSs with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?c11 :: ?c12 :: ?c13 :: ?c14 :: ?c15 :: ?rest) =>
change (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: c8 :: c9 :: c10 :: c11 :: c12 :: c13 :: c14 :: c15 :: rest)
with ([c0; c1; c2; c3; c4; c5; c6; c7] ++ ([c8; c9; c10; c11; c12; c13; c14; c15] ++ rest)) in FSs end;
apply (proj1 (rw_cells_app asegs _ _ _ _)) in FSs as [_ FSs]; apply (proj1 (rw_cells_app asegs _ _ _ _)) in FSs as [FSs _];
cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FSs; destruct FSs as [[_ WB] _]; cbn [cells_bytes cbytes app] in WB;
replace (Ff + 80) with (Ff + 8 * Z.of_nat 10) by lia;
eapply (scoped_unpoisoned_w mc Ff 1 10); [exact GF | lia | change (8 * (Z.of_nat 10 / 8)) with 8; unfold A_SB; exact WB | reflexivity | reflexivity | lia])
end end.
evt_done5.
lazymatch goal with FRXc : pe_frameAX ?mc _ _ _ _ _ ?ffc ?shc |- _ =>
eapply (pe_memappend_gX HIx GA GA_pres MAPP (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo mc md A B ts0 nb pj sv errv T (Ff + 80) 1 kP [Z_to_bv 8 u] ffc shc);
[ exact STC | exact BSL | exact INVX1 | cbn; lia | cbn; lia | exact (PBKX1 _ PBK) | cbn [t_co ts0]; lia | lia | exact BK | rewrite unsigned_lit by lia; reflexivity
| exact SRCB | reflexivity | lia
| right; first [left | idtac]; exists Ff, 2; split; [left; reflexivity | rewrite fr_size_2; lia]
| intros _; exact UNP | ]
end.
intros m2 md2 A2 B2 pbs2 errv2 r w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 F2 fc2 INVX2 OUT2 FS2 FRM2.
cbn [pf_spf pa_sp0 pa_F] in *. unfold A_TP in *.
clear TOK SLOTS FF FSH SHT1 MU WM MI HP INtk INtk' Htal Htlo Hthi DFt DSF DSt INV0 FR0 PBK BK REST INVX1 PBKX1 FRXc SRCB UNP HW.
set (ts2 := ts_pbs ts0 pbs2) in *.
pose proof INVX2 as [CORE2 REST2]. destruct CORE2 as (_ & _ & _ & _ & TOK & _ & _ & _ & FRX2). pose proof (proj1 REST2) as HP.
unfold ts2, ts_pbs, ts0 in TOK. cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_tk pf_mxd pf_fl] in TOK.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
pose proof FRX2 as (SLOTS & _ & _ & FF & FSH). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in SLOTS, FF, FSH. unfold shA, A_SB in FSH.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts2)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t2.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 4 HP INtk ltac:(lia)) as SHT4.
replace (tk / 8 + 4 + A_SB) with (tk / 8 + 2147450884) in SHT4 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 4 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT4t & _).
cbn [hl_sb A4L] in SEPT4t. assert (EQx : tk / 8 + A_SB + 4 = tk / 8 + 2147450884) by (unfold A_SB; lia). rewrite EQx in SEPT4t. clear EQx.
assert (INtk' : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts2 ++ LM)) by (apply in_or_app; left; exact INtk).
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP INF INtk') as DFt. rewrite fr_size_2 in DFt.
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP INF) as DSF. rewrite fr_size_2 in DSF. cbn [hl_sb A4L] in DSF.
pose proof (shadow_blk_apart HIx _ _ _ _ _ _ _ _ _ Ff 32 HP INtk' GF0' GFc' ltac:(lia)) as DSt.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs m2) as WM.
pose proof (munch_refl [(tk, tk + 72); (Ff, Ff + 248); (Ff / 8 + 2147450880, Ff / 8 + 2147450880 + 32)] m2) as MU.
assert (HW : Forall (pe_wtfA (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl)) [(tk, tk + 72); (Ff, Ff + 248); (Ff / 8 + 2147450880, Ff / 8 + 2147450880 + 32)])
by (apply Forall_cons; [left; cbn [fst snd pf_tk]; lia |]; apply Forall_cons; [right; right; left; cbn [fst snd pa_F]; lia |]; apply Forall_cons; [right; right; right; unfold shA, A_SB; cbn [fst snd pa_F]; lia | apply Forall_nil]).
assert (cs_T4_T : csep (tk / 8 + 2147450884) 1 tk (Z.of_nat 72)) by (unfold csep; clear - SEPT4t; lia).
assert (cs_FF_T : csep Ff 248 tk (Z.of_nat 72)) by (unfold csep; clear - DFt; lia).
assert (cs_T_FF : csep tk 72 Ff (Z.of_nat 248)) by (unfold csep; clear - DFt; lia).
assert (LF2 : length (pj_f2 pj) = 183%nat).
{ pose proof FF as [[Hwf _] _]. cbn in Hwf. destruct Hwf as (_ & _ & _ & L15 & _ & L167 & _). rewrite length_firstn in L15. rewrite length_skipn in L167. lia. }
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8, A_SB in *.
stash Himg_t2. stash INVX2. stash FRX2. stash REST2. clear SEPT4t.
lazymatch goal with |- AJ5 _ _ _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) => replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
reenterA asegs A4L HIx asegs_wx HP.
destruct OUT2 as [(-> & PBK2 & BK2) | [-> Epbs2]].
2:{
replace (Z_to_bv 64 (2^64 - 1)) with (Z_to_bv 64 (-1)) by (apply bv_eq; vm_compute; reflexivity).
step.
if_false.
step.
step.
asan_rechkB.
step.
step.
stepz.
step.
stepz.
step.
step.
set (pj' := PEJA (pj_0 pj) (pj_8 pj) (pj_16 pj) (pj_obj pj) (pj_288 pj) (pj_304 pj) (pj_gap pj) (pj_fhd pj) (pj_f1 pj) (firstn 15 (pj_f2 pj) ++ [Z_to_bv 8 u] ++ skipn 16 (pj_f2 pj))).
unstash INVX2. unstash FRX2. cbn [t_pbs ts0] in Epbs2. subst pbs2.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m2 mc, WMc : wmono asegs m2 mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, FFc : rw_cells asegs mc Ff _, FSHc : rw_cells asegs mc (Ff / 8 + 2147450880) _ |- _ =>
evt_done5;
assert (FFc' : rw_cells asegs mc Ff (ff_cellsA cb pj'))
by (eapply rw_cells_recast;
[ exact FFc
| unfold ff_cellsA, pj'; cbn [pj_fhd pj_f1 pj_f2]; cbn [cells_wf cell_wf]; pose proof FFc as [[Hwf _] _]; cbn [cells_wf cell_wf] in Hwf; destruct Hwf as (W1 & W2 & _);
split; [exact W1|]; split; [exact W2|]; split; [exact I|]; split; [| exact I]; rewrite !length_app, length_firstn, !length_skipn; cbn [length]; lia
| unfold ff_cellsA, pj'; cbn [pj_fhd pj_f1 pj_f2 cells_bytes cbytes]; rewrite <- !app_assoc; reflexivity
| reflexivity ]);
assert (FRc : pe_frameA asegs mc (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) cb nb pj' sv)
by (apply pe_frameA_of_X; eapply (pe_frameAX_write HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS B2 ts2 A2 m2 mc md2 lo nb pj sv); [exact STC | exact HP | exact FRX2 | exact MUc | exact WMc | exact FFc' | exact FSHc]);
destruct (PE_INV_AX_tokw HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m2 mc md2 A2 B2 ts2 errv2 _ co (tx_err (t_x ts2) (Z_to_bv 64 16)) _ _ STC INVX2 MUc WMc MIc HW TOKc FRc
ltac:(cbn [pf_len]; lia) eq_refl) as [INV3 _]
end end.
unstash Kout. eapply (Kout _ md2 A2 B2 errv2 pj'); [exact INV3 | exact FS2 | exact FRM2]. }
step.
if_true.
step.
stepz.
step.
do 3 step.

set (pj' := PEJA (pj_0 pj) (pj_8 pj) (pj_16 pj) (pj_obj pj) (pj_288 pj) (pj_304 pj) (pj_gap pj) (pj_fhd pj) (pj_f1 pj) (firstn 15 (pj_f2 pj) ++ [Z_to_bv 8 u] ++ skipn 16 (pj_f2 pj))).
unstash INVX2. unstash FRX2.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m2 mc, WMc : wmono asegs m2 mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, FFc : rw_cells asegs mc Ff _, FSHc : rw_cells asegs mc (Ff / 8 + 2147450880) _ |- _ =>
evt_done5;
assert (FFc' : rw_cells asegs mc Ff (ff_cellsA cb pj'))
by (eapply rw_cells_recast;
[ exact FFc
| unfold ff_cellsA, pj'; cbn [pj_fhd pj_f1 pj_f2]; cbn [cells_wf cell_wf]; pose proof FFc as [[Hwf _] _]; cbn [cells_wf cell_wf] in Hwf; destruct Hwf as (W1 & W2 & _);
split; [exact W1|]; split; [exact W2|]; split; [exact I|]; split; [| exact I]; rewrite !length_app, length_firstn, !length_skipn; cbn [length]; lia
| unfold ff_cellsA, pj'; cbn [pj_fhd pj_f1 pj_f2 cells_bytes cbytes]; rewrite <- !app_assoc; reflexivity
| reflexivity ]);
assert (FRc : pe_frameA asegs mc (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) cb nb pj' sv)
by (apply pe_frameA_of_X; eapply (pe_frameAX_write HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS B2 ts2 A2 m2 mc md2 lo nb pj sv); [exact STC | exact HP | exact FRX2 | exact MUc | exact WMc | exact FFc' | exact FSHc]);
destruct (PE_INV_AX_tokw HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m2 mc md2 A2 B2 ts2 errv2 _ co (t_x ts2) _ _ STC INVX2 MUc WMc MIc HW TOKc FRc
ltac:(cbn [pf_len]; lia) eq_refl) as [INV3 PBK3]
end end.
unstash Kpop. eapply (Kpop _ md2 A2 B2 pbs2 errv2 pj'); [exact INV3 | exact (PBK3 _ PBK2) | exact BK2 | exact FS2 | exact FRM2].
Qed.

Lemma euni_enc2_B :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (u kP : Z)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kB : nat)
(x1 gp t0 t1 t2 a0 a1 a2 a4 a5 a6 a7 s3 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
PBOKat m ts kP -> kP + 2 <= t_co ts + 1 -> BOK pf pa ts B kB -> 0 <= u < 2^32 ->

(forall m' md' A' B' pbs' errv' pj' gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' (ts_pbs ts pbs') cb nb pj' sv errv' ->
PBOKat m' (ts_pbs ts pbs') (kP + 2) -> BOK pf pa (ts_pbs ts pbs') B' kB ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msO asegs pf pa APE_EUNI_POP gp' t0' (Z_to_bv 64 (pf_lenr pf)) (Z_to_bv 64 (pf_tk pf + 32)) a0' a1' a2' a3' a4' a5' a6' a7' s3' (Z_to_bv 64 (pf_sb pf + t_co ts)) s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' m')) ->

(forall m' md' A' B' errv' pj' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' (ts_set_x ts (t_co ts) (tx_err (t_x ts) (Z_to_bv 64 16))) cb nb pj' sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msO asegs pf pa APE_OUT gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' m')) ->
AJ5 A4L HIx A T md
(pe_msX asegs pf pa APE_EUNI_ARM2 x1 gp t0 t1 t2 a0 a1 a2 (Z_to_bv 64 u) a4 a5 a6 a7 s3 (Z_to_bv 64 (pf_sb pf + t_co ts)) s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc m).
Proof.
intros until fc. intros STC BSL INV PBK Hroom BK Hu Kpop Kout. pose proof INV as INV0.
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
destruct INV as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof REST as (HP & _).
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
unfold ts_set_x, tx_err, ts_pbs in Kpop, Kout. cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in Kpop, Kout.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
pose proof FR as FR0. unfold pe_frameA in FR. destruct FR as (SLOTS & GAP & SAVED & FF & FSH).
unfold pe_slotsA in SLOTS. cbn zeta in SLOTS. unfold ff_cellsA in FF. unfold ffsh_cells, FSH0 in FSH. cbn [map] in FSH.
unfold pe_msX, pe_msA, pe_msO in *.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 1 HP INtk ltac:(lia)) as SHT1.
replace (tk / 8 + 1 + A_SB) with (tk / 8 + 2147450881) in SHT1 by (unfold A_SB; lia).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs m) as WM.
pose proof alloc_ceiling_range as ACR.
assert (INF : In (Ff, 2) ((Ff, 2) :: FRS)) by (left; reflexivity).
assert (INtk' : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0 ++ LM)) by (apply in_or_app; left; exact INtk).
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP INF INtk') as DFt. rewrite fr_size_2 in DFt.
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP INF) as DSF. rewrite fr_size_2 in DSF. cbn [hl_sb A4L] in DSF.
assert (GF0' : 0 <= Ff) by lia. assert (GFc' : Ff < alloc_ceiling) by lia.
pose proof (shadow_blk_apart HIx _ _ _ _ _ _ _ _ _ Ff 32 HP INtk' GF0' GFc' ltac:(lia)) as DSt.
unfold APE_OUT, APE_EUNI_ARM2, APE_EUNI_POP in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8, A_SB in *.
pose proof (munch_refl [(tk, tk + 72); (Ff, Ff + 248); (Ff / 8 + 2147450880, Ff / 8 + 2147450880 + 32)] m) as MU.
stash Himg_t. stash Kpop. stash Kout. stash INV0. stash FR0. stash PBK. stash BK. stash GAP. stash SAVED. stash PB. stash TSK. stash REST.
reenterA asegs A4L HIx asegs_wx HP.
step.
nrm.
step.
nrm.
stepz.
step.
nrm.
step.
nrm.
step.
nrm.
step.
rewrite le1_w. lazymatch goal with |- context [write_to_mem _ _ [?bx]] => remember bx as b0 eqn:Eb0 end. clear Eb0. mem_after_store.
step. if_truex.
step.
nrm.
step.
nrm.
step.
nrm.
step.
rewrite le1_w. lazymatch goal with |- context [write_to_mem _ _ [?bx]] => remember bx as b1 eqn:Eb1 end. clear Eb1. mem_after_store.
step.
nrm.
step.
nrm.
step.
nrm.
step.
nrm.
rewrite ?sxb_zero, ?zxb_zero.
step.
first [ if_true | if_false ].
step.
nrm.
step.
nrm.
step.
nrm.

unstash INV0. unstash FR0. unstash PBK. unstash BK. unstash REST.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, FFc : rw_cells asegs mc Ff ?ffc, FSHc : rw_cells asegs mc (Ff / 8 + 2147450880) ?shc |- _ =>
assert (HW : Forall (pe_wtfA (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl)) [(tk, tk + 72); (Ff, Ff + 248); (Ff / 8 + 2147450880, Ff / 8 + 2147450880 + 32)])
by (apply Forall_cons; [left; cbn [fst snd pf_tk]; lia |]; apply Forall_cons; [right; right; left; cbn [fst snd pa_F]; lia |]; apply Forall_cons; [right; right; right; unfold shA, A_SB; cbn [fst snd pa_F]; lia | apply Forall_nil]);
assert (FRXc : pe_frameAX mc (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) nb pj sv ffc shc)
by (eapply (pe_frameAX_write HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS B ts0 A m mc md lo nb pj sv); [exact STC | exact HP | exact (pe_frameAX_of_A _ _ _ _ _ _ _ FR0) | exact MUc | exact WMc | exact FFc | exact FSHc]);
destruct (PE_INV_AX_tokw HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m mc md A B ts0 errv _ co (t_x ts0) _ _ STC (PE_INV_AX_of_A HIx GA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV0) MUc WMc MIc HW TOKc FRXc
ltac:(cbn [pf_len]; lia) eq_refl) as [INVX1 PBKX1];

assert (SRCB : bytes_at asegs mc (Ff + 96) [b0; b1])
by (pose proof FFc as FFs;
change ffc with ([CB 24 (pj_fhd pj); CB 40 (pj_f1 pj); C1 cb; CB 31 (firstn 31 (pj_f2 pj))] ++ ([C1 b0; C1 b1] ++ [CB 150 (skipn 1 (skipn 32 (pj_f2 pj)))])) in FFs;
apply (proj1 (rw_cells_app asegs _ _ _ _)) in FFs as [_ FFs]; apply (proj1 (rw_cells_app asegs _ _ _ _)) in FFs as [FFs _];
cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.add_carry] in FFs; destruct FFs as [[_ HB] _]; cbn [cells_bytes cbytes app] in HB; exact HB);
assert (UNP : unpoisoned asegs mc 2147450880 (Ff + 96) 2)
by (pose proof FSHc as FSs;
match type of FSs with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?c11 :: ?c12 :: ?c13 :: ?c14 :: ?c15 :: ?rest) =>
change (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: c8 :: c9 :: c10 :: c11 :: c12 :: c13 :: c14 :: c15 :: rest)
with ([c0; c1; c2; c3; c4; c5; c6; c7] ++ ([c8; c9; c10; c11; c12; c13; c14; c15] ++ rest)) in FSs end;
apply (proj1 (rw_cells_app asegs _ _ _ _)) in FSs as [_ FSs]; apply (proj1 (rw_cells_app asegs _ _ _ _)) in FSs as [FSs _];
cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FSs; destruct FSs as [[_ WB] _]; cbn [cells_bytes cbytes app] in WB;
replace (Ff + 96) with (Ff + 8 * Z.of_nat 12) by lia;
eapply (scoped_unpoisoned_w mc Ff 2 12); [exact GF | lia | change (8 * (Z.of_nat 12 / 8)) with 8; unfold A_SB; exact WB | reflexivity | reflexivity | lia])
end end.
evt_done5.
lazymatch goal with FRXc : pe_frameAX ?mc _ _ _ _ _ ?ffc ?shc |- _ =>
eapply (pe_memappend_gX HIx GA GA_pres MAPP (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo mc md A B ts0 nb pj sv errv T (Ff + 96) 2 kP [b0; b1] ffc shc);
[ exact STC | exact BSL | exact INVX1 | cbn; lia | cbn; lia | exact (PBKX1 _ PBK) | cbn [t_co ts0]; lia | lia | exact BK | rewrite unsigned_lit by lia; reflexivity
| exact SRCB | reflexivity | lia
| right; first [left | idtac]; exists Ff, 2; split; [left; reflexivity | rewrite fr_size_2; lia]
| intros _; exact UNP | ]
end.
intros m2 md2 A2 B2 pbs2 errv2 r w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 F2 fc2 INVX2 OUT2 FS2 FRM2.
cbn [pf_spf pa_sp0 pa_F] in *. unfold A_TP in *.
clear TOK SLOTS FF FSH SHT1 MU WM MI HP INtk INtk' Htal Htlo Hthi DFt DSF DSt INV0 FR0 PBK BK REST INVX1 PBKX1 FRXc SRCB UNP HW.
set (ts2 := ts_pbs ts0 pbs2) in *.
pose proof INVX2 as [CORE2 REST2]. destruct CORE2 as (_ & _ & _ & _ & TOK & _ & _ & _ & FRX2). pose proof (proj1 REST2) as HP.
unfold ts2, ts_pbs, ts0 in TOK. cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_tk pf_mxd pf_fl] in TOK.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
pose proof FRX2 as (SLOTS & _ & _ & FF & FSH). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in SLOTS, FF, FSH. unfold shA, A_SB in FSH.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts2)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t2.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 4 HP INtk ltac:(lia)) as SHT4.
replace (tk / 8 + 4 + A_SB) with (tk / 8 + 2147450884) in SHT4 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 4 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT4t & _).
cbn [hl_sb A4L] in SEPT4t. assert (EQx : tk / 8 + A_SB + 4 = tk / 8 + 2147450884) by (unfold A_SB; lia). rewrite EQx in SEPT4t. clear EQx.
assert (INtk' : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts2 ++ LM)) by (apply in_or_app; left; exact INtk).
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP INF INtk') as DFt. rewrite fr_size_2 in DFt.
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP INF) as DSF. rewrite fr_size_2 in DSF. cbn [hl_sb A4L] in DSF.
pose proof (shadow_blk_apart HIx _ _ _ _ _ _ _ _ _ Ff 32 HP INtk' GF0' GFc' ltac:(lia)) as DSt.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs m2) as WM.
pose proof (munch_refl [(tk, tk + 72); (Ff, Ff + 248); (Ff / 8 + 2147450880, Ff / 8 + 2147450880 + 32)] m2) as MU.
assert (HW : Forall (pe_wtfA (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl)) [(tk, tk + 72); (Ff, Ff + 248); (Ff / 8 + 2147450880, Ff / 8 + 2147450880 + 32)])
by (apply Forall_cons; [left; cbn [fst snd pf_tk]; lia |]; apply Forall_cons; [right; right; left; cbn [fst snd pa_F]; lia |]; apply Forall_cons; [right; right; right; unfold shA, A_SB; cbn [fst snd pa_F]; lia | apply Forall_nil]).
assert (cs_T4_T : csep (tk / 8 + 2147450884) 1 tk (Z.of_nat 72)) by (unfold csep; clear - SEPT4t; lia).
assert (cs_FF_T : csep Ff 248 tk (Z.of_nat 72)) by (unfold csep; clear - DFt; lia).
assert (cs_T_FF : csep tk 72 Ff (Z.of_nat 248)) by (unfold csep; clear - DFt; lia).
assert (LF2 : length (pj_f2 pj) = 183%nat).
{ pose proof FF as [[Hwf _] _]. cbn in Hwf. destruct Hwf as (_ & _ & _ & L15 & Hrest). rewrite length_firstn in L15. destruct Hrest as (_ & Hrest). destruct Hrest as (_ & Hrest). destruct Hrest as (L167 & _). rewrite !length_skipn in L167. lia. }
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8, A_SB in *.
stash Himg_t2. stash INVX2. stash FRX2. stash REST2. clear SEPT4t.
lazymatch goal with |- AJ5 _ _ _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) => replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
reenterA asegs A4L HIx asegs_wx HP.
destruct OUT2 as [(-> & PBK2 & BK2) | [-> Epbs2]].
2:{
replace (Z_to_bv 64 (2^64 - 1)) with (Z_to_bv 64 (-1)) by (apply bv_eq; vm_compute; reflexivity).
step.
if_false.
step.
step.
asan_rechkB.
step.
step.
stepz.
step.
stepz.
step.
step.
set (pj' := PEJA (pj_0 pj) (pj_8 pj) (pj_16 pj) (pj_obj pj) (pj_288 pj) (pj_304 pj) (pj_gap pj) (pj_fhd pj) (pj_f1 pj) (firstn 31 (pj_f2 pj) ++ [b0; b1] ++ skipn 1 (skipn 32 (pj_f2 pj)))).
unstash INVX2. unstash FRX2. cbn [t_pbs ts0] in Epbs2. subst pbs2.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m2 mc, WMc : wmono asegs m2 mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, FFc : rw_cells asegs mc Ff _, FSHc : rw_cells asegs mc (Ff / 8 + 2147450880) _ |- _ =>
evt_done5;
assert (FFc' : rw_cells asegs mc Ff (ff_cellsA cb pj'))
by (eapply rw_cells_recast;
[ exact FFc
| unfold ff_cellsA, pj'; cbn [pj_fhd pj_f1 pj_f2]; cbn [cells_wf cell_wf]; pose proof FFc as [[Hwf _] _]; cbn [cells_wf cell_wf] in Hwf; destruct Hwf as (W1 & W2 & _);
split; [exact W1|]; split; [exact W2|]; split; [exact I|]; split; [| exact I]; rewrite !length_app, length_firstn, !length_skipn; cbn [length]; lia
| unfold ff_cellsA, pj'; cbn [pj_fhd pj_f1 pj_f2 cells_bytes cbytes]; rewrite <- !app_assoc; reflexivity
| reflexivity ]);
assert (FRc : pe_frameA asegs mc (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) cb nb pj' sv)
by (apply pe_frameA_of_X; eapply (pe_frameAX_write HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS B2 ts2 A2 m2 mc md2 lo nb pj sv); [exact STC | exact HP | exact FRX2 | exact MUc | exact WMc | exact FFc' | exact FSHc]);
destruct (PE_INV_AX_tokw HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m2 mc md2 A2 B2 ts2 errv2 _ co (tx_err (t_x ts2) (Z_to_bv 64 16)) _ _ STC INVX2 MUc WMc MIc HW TOKc FRc
ltac:(cbn [pf_len]; lia) eq_refl) as [INV3 _]
end end.
unstash Kout. eapply (Kout _ md2 A2 B2 errv2 pj'); [exact INV3 | exact FS2 | exact FRM2]. }
step.
if_true.
step.
stepz.
do 3 step.

set (pj' := PEJA (pj_0 pj) (pj_8 pj) (pj_16 pj) (pj_obj pj) (pj_288 pj) (pj_304 pj) (pj_gap pj) (pj_fhd pj) (pj_f1 pj) (firstn 31 (pj_f2 pj) ++ [b0; b1] ++ skipn 1 (skipn 32 (pj_f2 pj)))).
unstash INVX2. unstash FRX2.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m2 mc, WMc : wmono asegs m2 mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, FFc : rw_cells asegs mc Ff _, FSHc : rw_cells asegs mc (Ff / 8 + 2147450880) _ |- _ =>
evt_done5;
assert (FFc' : rw_cells asegs mc Ff (ff_cellsA cb pj'))
by (eapply rw_cells_recast;
[ exact FFc
| unfold ff_cellsA, pj'; cbn [pj_fhd pj_f1 pj_f2]; cbn [cells_wf cell_wf]; pose proof FFc as [[Hwf _] _]; cbn [cells_wf cell_wf] in Hwf; destruct Hwf as (W1 & W2 & _);
split; [exact W1|]; split; [exact W2|]; split; [exact I|]; split; [| exact I]; rewrite !length_app, length_firstn, !length_skipn; cbn [length]; lia
| unfold ff_cellsA, pj'; cbn [pj_fhd pj_f1 pj_f2 cells_bytes cbytes]; rewrite <- !app_assoc; reflexivity
| reflexivity ]);
assert (FRc : pe_frameA asegs mc (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) cb nb pj' sv)
by (apply pe_frameA_of_X; eapply (pe_frameAX_write HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS B2 ts2 A2 m2 mc md2 lo nb pj sv); [exact STC | exact HP | exact FRX2 | exact MUc | exact WMc | exact FFc' | exact FSHc]);
destruct (PE_INV_AX_tokw HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m2 mc md2 A2 B2 ts2 errv2 _ co (t_x ts2) _ _ STC INVX2 MUc WMc MIc HW TOKc FRc
ltac:(cbn [pf_len]; lia) eq_refl) as [INV3 PBK3]
end end.
unstash Kpop. eapply (Kpop _ md2 A2 B2 pbs2 errv2 pj'); [exact INV3 | exact (PBK3 _ PBK2) | exact BK2 | exact FS2 | exact FRM2].
Qed.

Lemma euni_enc3_B :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (u kP : Z)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kB : nat)
(x1 gp t0 t1 t2 a0 a1 a2 a4 a5 a6 a7 s3 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
PBOKat m ts kP -> kP + 3 <= t_co ts + 1 -> BOK pf pa ts B kB -> 0 <= u < 2^32 ->

(forall m' md' A' B' pbs' errv' pj' gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' (ts_pbs ts pbs') cb nb pj' sv errv' ->
PBOKat m' (ts_pbs ts pbs') (kP + 3) -> BOK pf pa (ts_pbs ts pbs') B' kB ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msO asegs pf pa APE_EUNI_POP gp' t0' (Z_to_bv 64 (pf_lenr pf)) (Z_to_bv 64 (pf_tk pf + 32)) a0' a1' a2' a3' a4' a5' a6' a7' s3' (Z_to_bv 64 (pf_sb pf + t_co ts)) s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' m')) ->

(forall m' md' A' B' errv' pj' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' (ts_set_x ts (t_co ts) (tx_err (t_x ts) (Z_to_bv 64 16))) cb nb pj' sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msO asegs pf pa APE_OUT gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' m')) ->
AJ5 A4L HIx A T md
(pe_msX asegs pf pa APE_EUNI_ARM3 x1 gp t0 t1 t2 a0 a1 a2 (Z_to_bv 64 u) a4 a5 a6 a7 s3 (Z_to_bv 64 (pf_sb pf + t_co ts)) s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc m).
Proof.
intros until fc. intros STC BSL INV PBK Hroom BK Hu Kpop Kout. pose proof INV as INV0.
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
destruct INV as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof REST as (HP & _).
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
unfold ts_set_x, tx_err, ts_pbs in Kpop, Kout. cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in Kpop, Kout.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
pose proof FR as FR0. unfold pe_frameA in FR. destruct FR as (SLOTS & GAP & SAVED & FF & FSH).
unfold pe_slotsA in SLOTS. cbn zeta in SLOTS. unfold ff_cellsA in FF. unfold ffsh_cells, FSH0 in FSH. cbn [map] in FSH.
unfold pe_msX, pe_msA, pe_msO in *.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 1 HP INtk ltac:(lia)) as SHT1.
replace (tk / 8 + 1 + A_SB) with (tk / 8 + 2147450881) in SHT1 by (unfold A_SB; lia).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs m) as WM.
pose proof alloc_ceiling_range as ACR.
assert (INF : In (Ff, 2) ((Ff, 2) :: FRS)) by (left; reflexivity).
assert (INtk' : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0 ++ LM)) by (apply in_or_app; left; exact INtk).
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP INF INtk') as DFt. rewrite fr_size_2 in DFt.
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP INF) as DSF. rewrite fr_size_2 in DSF. cbn [hl_sb A4L] in DSF.
assert (GF0' : 0 <= Ff) by lia. assert (GFc' : Ff < alloc_ceiling) by lia.
pose proof (shadow_blk_apart HIx _ _ _ _ _ _ _ _ _ Ff 32 HP INtk' GF0' GFc' ltac:(lia)) as DSt.
unfold APE_OUT, APE_EUNI_ARM3, APE_EUNI_POP in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8, A_SB in *.
pose proof (munch_refl [(tk, tk + 72); (Ff, Ff + 248); (Ff / 8 + 2147450880, Ff / 8 + 2147450880 + 32)] m) as MU.
stash Himg_t. stash Kpop. stash Kout. stash INV0. stash FR0. stash PBK. stash BK. stash GAP. stash SAVED. stash PB. stash TSK. stash REST.
reenterA asegs A4L HIx asegs_wx HP.
step.
nrm.
step.
nrm.
stepz.
step.
nrm.
step.
nrm.
step.
nrm.
step.
rewrite le1_w. lazymatch goal with |- context [write_to_mem _ _ [?bx]] => remember bx as b0 eqn:Eb0 end. clear Eb0. mem_after_store.
step. if_truex.
step.
nrm.
step.
nrm.
step.
nrm.
step.
nrm.
step.
nrm.
step.
rewrite le1_w. lazymatch goal with |- context [write_to_mem _ _ [?bx]] => remember bx as b1 eqn:Eb1 end. clear Eb1. mem_after_store.
step. if_truex.
step.
nrm.
step.
nrm.
step.
nrm.
step.
rewrite le1_w. lazymatch goal with |- context [write_to_mem _ _ [?bx]] => remember bx as b2 eqn:Eb2 end. clear Eb2. mem_after_store.
step.
nrm.
step.
nrm.
step.
nrm.
step.
nrm.
rewrite ?sxb_zero, ?zxb_zero.
step.
first [ if_true | if_false ].
step.
nrm.
step.
nrm.
step.
nrm.
step.
nrm.
step.
nrm.

unstash INV0. unstash FR0. unstash PBK. unstash BK. unstash REST.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, FFc : rw_cells asegs mc Ff ?ffc, FSHc : rw_cells asegs mc (Ff / 8 + 2147450880) ?shc |- _ =>
assert (HW : Forall (pe_wtfA (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl)) [(tk, tk + 72); (Ff, Ff + 248); (Ff / 8 + 2147450880, Ff / 8 + 2147450880 + 32)])
by (apply Forall_cons; [left; cbn [fst snd pf_tk]; lia |]; apply Forall_cons; [right; right; left; cbn [fst snd pa_F]; lia |]; apply Forall_cons; [right; right; right; unfold shA, A_SB; cbn [fst snd pa_F]; lia | apply Forall_nil]);
assert (FRXc : pe_frameAX mc (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) nb pj sv ffc shc)
by (eapply (pe_frameAX_write HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS B ts0 A m mc md lo nb pj sv); [exact STC | exact HP | exact (pe_frameAX_of_A _ _ _ _ _ _ _ FR0) | exact MUc | exact WMc | exact FFc | exact FSHc]);
destruct (PE_INV_AX_tokw HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m mc md A B ts0 errv _ co (t_x ts0) _ _ STC (PE_INV_AX_of_A HIx GA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV0) MUc WMc MIc HW TOKc FRXc
ltac:(cbn [pf_len]; lia) eq_refl) as [INVX1 PBKX1];

assert (SRCB : bytes_at asegs mc (Ff + 112) [b0; b1; b2])
by (pose proof FFc as FFs;
change ffc with ([CB 24 (pj_fhd pj); CB 40 (pj_f1 pj); C1 cb; CB 47 (firstn 47 (pj_f2 pj))] ++ ([C1 b0; C1 b1; C1 b2] ++ [CB 133 (skipn 1 (skipn 1 (skipn 48 (pj_f2 pj))))])) in FFs;
apply (proj1 (rw_cells_app asegs _ _ _ _)) in FFs as [_ FFs]; apply (proj1 (rw_cells_app asegs _ _ _ _)) in FFs as [FFs _];
cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.add_carry] in FFs; destruct FFs as [[_ HB] _]; cbn [cells_bytes cbytes app] in HB; exact HB);
assert (UNP : unpoisoned asegs mc 2147450880 (Ff + 112) 3)
by (pose proof FSHc as FSs;
match type of FSs with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?c11 :: ?c12 :: ?c13 :: ?c14 :: ?c15 :: ?rest) =>
change (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: c8 :: c9 :: c10 :: c11 :: c12 :: c13 :: c14 :: c15 :: rest)
with ([c0; c1; c2; c3; c4; c5; c6; c7] ++ ([c8; c9; c10; c11; c12; c13; c14; c15] ++ rest)) in FSs end;
apply (proj1 (rw_cells_app asegs _ _ _ _)) in FSs as [_ FSs]; apply (proj1 (rw_cells_app asegs _ _ _ _)) in FSs as [FSs _];
cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FSs; destruct FSs as [[_ WB] _]; cbn [cells_bytes cbytes app] in WB;
replace (Ff + 112) with (Ff + 8 * Z.of_nat 14) by lia;
eapply (scoped_unpoisoned_w mc Ff 3 14); [exact GF | lia | change (8 * (Z.of_nat 14 / 8)) with 8; unfold A_SB; exact WB | reflexivity | reflexivity | lia])
end end.
evt_done5.
lazymatch goal with FRXc : pe_frameAX ?mc _ _ _ _ _ ?ffc ?shc |- _ =>
eapply (pe_memappend_gX HIx GA GA_pres MAPP (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo mc md A B ts0 nb pj sv errv T (Ff + 112) 3 kP [b0; b1; b2] ffc shc);
[ exact STC | exact BSL | exact INVX1 | cbn; lia | cbn; lia | exact (PBKX1 _ PBK) | cbn [t_co ts0]; lia | lia | exact BK | rewrite unsigned_lit by lia; reflexivity
| exact SRCB | reflexivity | lia
| right; first [left | idtac]; exists Ff, 2; split; [left; reflexivity | rewrite fr_size_2; lia]
| intros _; exact UNP | ]
end.
intros m2 md2 A2 B2 pbs2 errv2 r w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 F2 fc2 INVX2 OUT2 FS2 FRM2.
cbn [pf_spf pa_sp0 pa_F] in *. unfold A_TP in *.
clear TOK SLOTS FF FSH SHT1 MU WM MI HP INtk INtk' Htal Htlo Hthi DFt DSF DSt INV0 FR0 PBK BK REST INVX1 PBKX1 FRXc SRCB UNP HW.
set (ts2 := ts_pbs ts0 pbs2) in *.
pose proof INVX2 as [CORE2 REST2]. destruct CORE2 as (_ & _ & _ & _ & TOK & _ & _ & _ & FRX2). pose proof (proj1 REST2) as HP.
unfold ts2, ts_pbs, ts0 in TOK. cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_tk pf_mxd pf_fl] in TOK.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
pose proof FRX2 as (SLOTS & _ & _ & FF & FSH). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in SLOTS, FF, FSH. unfold shA, A_SB in FSH.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts2)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t2.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 4 HP INtk ltac:(lia)) as SHT4.
replace (tk / 8 + 4 + A_SB) with (tk / 8 + 2147450884) in SHT4 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 4 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT4t & _).
cbn [hl_sb A4L] in SEPT4t. assert (EQx : tk / 8 + A_SB + 4 = tk / 8 + 2147450884) by (unfold A_SB; lia). rewrite EQx in SEPT4t. clear EQx.
assert (INtk' : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts2 ++ LM)) by (apply in_or_app; left; exact INtk).
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP INF INtk') as DFt. rewrite fr_size_2 in DFt.
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP INF) as DSF. rewrite fr_size_2 in DSF. cbn [hl_sb A4L] in DSF.
pose proof (shadow_blk_apart HIx _ _ _ _ _ _ _ _ _ Ff 32 HP INtk' GF0' GFc' ltac:(lia)) as DSt.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs m2) as WM.
pose proof (munch_refl [(tk, tk + 72); (Ff, Ff + 248); (Ff / 8 + 2147450880, Ff / 8 + 2147450880 + 32)] m2) as MU.
assert (HW : Forall (pe_wtfA (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl)) [(tk, tk + 72); (Ff, Ff + 248); (Ff / 8 + 2147450880, Ff / 8 + 2147450880 + 32)])
by (apply Forall_cons; [left; cbn [fst snd pf_tk]; lia |]; apply Forall_cons; [right; right; left; cbn [fst snd pa_F]; lia |]; apply Forall_cons; [right; right; right; unfold shA, A_SB; cbn [fst snd pa_F]; lia | apply Forall_nil]).
assert (cs_T4_T : csep (tk / 8 + 2147450884) 1 tk (Z.of_nat 72)) by (unfold csep; clear - SEPT4t; lia).
assert (cs_FF_T : csep Ff 248 tk (Z.of_nat 72)) by (unfold csep; clear - DFt; lia).
assert (cs_T_FF : csep tk 72 Ff (Z.of_nat 248)) by (unfold csep; clear - DFt; lia).
assert (LF2 : length (pj_f2 pj) = 183%nat).
{ pose proof FF as [[Hwf _] _]. cbn in Hwf. destruct Hwf as (_ & _ & _ & L15 & Hrest). rewrite length_firstn in L15. destruct Hrest as (_ & Hrest). destruct Hrest as (_ & Hrest). destruct Hrest as (_ & Hrest). destruct Hrest as (L167 & _). rewrite !length_skipn in L167. lia. }
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8, A_SB in *.
stash Himg_t2. stash INVX2. stash FRX2. stash REST2. clear SEPT4t.
lazymatch goal with |- AJ5 _ _ _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) => replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
reenterA asegs A4L HIx asegs_wx HP.
destruct OUT2 as [(-> & PBK2 & BK2) | [-> Epbs2]].
2:{
replace (Z_to_bv 64 (2^64 - 1)) with (Z_to_bv 64 (-1)) by (apply bv_eq; vm_compute; reflexivity).
step.
if_false.
step.
step.
asan_rechkB.
step.
step.
stepz.
step.
stepz.
step.
step.
set (pj' := PEJA (pj_0 pj) (pj_8 pj) (pj_16 pj) (pj_obj pj) (pj_288 pj) (pj_304 pj) (pj_gap pj) (pj_fhd pj) (pj_f1 pj) (firstn 47 (pj_f2 pj) ++ [b0; b1; b2] ++ skipn 1 (skipn 1 (skipn 48 (pj_f2 pj))))).
unstash INVX2. unstash FRX2. cbn [t_pbs ts0] in Epbs2. subst pbs2.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m2 mc, WMc : wmono asegs m2 mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, FFc : rw_cells asegs mc Ff _, FSHc : rw_cells asegs mc (Ff / 8 + 2147450880) _ |- _ =>
evt_done5;
assert (FFc' : rw_cells asegs mc Ff (ff_cellsA cb pj'))
by (eapply rw_cells_recast;
[ exact FFc
| unfold ff_cellsA, pj'; cbn [pj_fhd pj_f1 pj_f2]; cbn [cells_wf cell_wf]; pose proof FFc as [[Hwf _] _]; cbn [cells_wf cell_wf] in Hwf; destruct Hwf as (W1 & W2 & _);
split; [exact W1|]; split; [exact W2|]; split; [exact I|]; split; [| exact I]; rewrite !length_app, length_firstn, !length_skipn; cbn [length]; lia
| unfold ff_cellsA, pj'; cbn [pj_fhd pj_f1 pj_f2 cells_bytes cbytes]; rewrite <- !app_assoc; reflexivity
| reflexivity ]);
assert (FRc : pe_frameA asegs mc (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) cb nb pj' sv)
by (apply pe_frameA_of_X; eapply (pe_frameAX_write HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS B2 ts2 A2 m2 mc md2 lo nb pj sv); [exact STC | exact HP | exact FRX2 | exact MUc | exact WMc | exact FFc' | exact FSHc]);
destruct (PE_INV_AX_tokw HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m2 mc md2 A2 B2 ts2 errv2 _ co (tx_err (t_x ts2) (Z_to_bv 64 16)) _ _ STC INVX2 MUc WMc MIc HW TOKc FRc
ltac:(cbn [pf_len]; lia) eq_refl) as [INV3 _]
end end.
unstash Kout. eapply (Kout _ md2 A2 B2 errv2 pj'); [exact INV3 | exact FS2 | exact FRM2]. }
step.
if_true.
step.
stepz.
step.
do 3 step.

set (pj' := PEJA (pj_0 pj) (pj_8 pj) (pj_16 pj) (pj_obj pj) (pj_288 pj) (pj_304 pj) (pj_gap pj) (pj_fhd pj) (pj_f1 pj) (firstn 47 (pj_f2 pj) ++ [b0; b1; b2] ++ skipn 1 (skipn 1 (skipn 48 (pj_f2 pj))))).
unstash INVX2. unstash FRX2.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m2 mc, WMc : wmono asegs m2 mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, FFc : rw_cells asegs mc Ff _, FSHc : rw_cells asegs mc (Ff / 8 + 2147450880) _ |- _ =>
evt_done5;
assert (FFc' : rw_cells asegs mc Ff (ff_cellsA cb pj'))
by (eapply rw_cells_recast;
[ exact FFc
| unfold ff_cellsA, pj'; cbn [pj_fhd pj_f1 pj_f2]; cbn [cells_wf cell_wf]; pose proof FFc as [[Hwf _] _]; cbn [cells_wf cell_wf] in Hwf; destruct Hwf as (W1 & W2 & _);
split; [exact W1|]; split; [exact W2|]; split; [exact I|]; split; [| exact I]; rewrite !length_app, length_firstn, !length_skipn; cbn [length]; lia
| unfold ff_cellsA, pj'; cbn [pj_fhd pj_f1 pj_f2 cells_bytes cbytes]; rewrite <- !app_assoc; reflexivity
| reflexivity ]);
assert (FRc : pe_frameA asegs mc (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) cb nb pj' sv)
by (apply pe_frameA_of_X; eapply (pe_frameAX_write HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS B2 ts2 A2 m2 mc md2 lo nb pj sv); [exact STC | exact HP | exact FRX2 | exact MUc | exact WMc | exact FFc' | exact FSHc]);
destruct (PE_INV_AX_tokw HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m2 mc md2 A2 B2 ts2 errv2 _ co (t_x ts2) _ _ STC INVX2 MUc WMc MIc HW TOKc FRc
ltac:(cbn [pf_len]; lia) eq_refl) as [INV3 PBK3]
end end.
unstash Kpop. eapply (Kpop _ md2 A2 B2 pbs2 errv2 pj'); [exact INV3 | exact (PBK3 _ PBK2) | exact BK2 | exact FS2 | exact FRM2].
Qed.

Lemma euni_enc4_B :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (u kP : Z)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kB : nat)
(x1 gp t0 t1 t2 a0 a1 a2 a4 a5 a6 a7 s3 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
PBOKat m ts kP -> kP + 4 <= t_co ts + 1 -> BOK pf pa ts B kB -> 0 <= u < 2^32 ->

(forall m' md' A' B' pbs' errv' pj' gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' (ts_pbs ts pbs') cb nb pj' sv errv' ->
PBOKat m' (ts_pbs ts pbs') (kP + 4) -> BOK pf pa (ts_pbs ts pbs') B' kB ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msO asegs pf pa APE_EUNI_POP gp' t0' (Z_to_bv 64 (pf_lenr pf)) (Z_to_bv 64 (pf_tk pf + 32)) a0' a1' a2' a3' a4' a5' a6' a7' s3' (Z_to_bv 64 (pf_sb pf + t_co ts)) s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' m')) ->

(forall m' md' A' B' errv' pj' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' (ts_set_x ts (t_co ts) (tx_err (t_x ts) (Z_to_bv 64 16))) cb nb pj' sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msO asegs pf pa APE_OUT gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' m')) ->
AJ5 A4L HIx A T md
(pe_msX asegs pf pa APE_EUNI_ARM4 x1 gp t0 t1 t2 a0 a1 a2 (Z_to_bv 64 u) a4 a5 a6 a7 s3 (Z_to_bv 64 (pf_sb pf + t_co ts)) s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc m).
Proof.
intros until fc. intros STC BSL INV PBK Hroom BK Hu Kpop Kout. pose proof INV as INV0.
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
destruct INV as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof REST as (HP & _).
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
unfold ts_set_x, tx_err, ts_pbs in Kpop, Kout. cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in Kpop, Kout.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
pose proof FR as FR0. unfold pe_frameA in FR. destruct FR as (SLOTS & GAP & SAVED & FF & FSH).
unfold pe_slotsA in SLOTS. cbn zeta in SLOTS. unfold ff_cellsA in FF. unfold ffsh_cells, FSH0 in FSH. cbn [map] in FSH.
unfold pe_msX, pe_msA, pe_msO in *.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 1 HP INtk ltac:(lia)) as SHT1.
replace (tk / 8 + 1 + A_SB) with (tk / 8 + 2147450881) in SHT1 by (unfold A_SB; lia).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs m) as WM.
pose proof alloc_ceiling_range as ACR.
assert (INF : In (Ff, 2) ((Ff, 2) :: FRS)) by (left; reflexivity).
assert (INtk' : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0 ++ LM)) by (apply in_or_app; left; exact INtk).
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP INF INtk') as DFt. rewrite fr_size_2 in DFt.
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP INF) as DSF. rewrite fr_size_2 in DSF. cbn [hl_sb A4L] in DSF.
assert (GF0' : 0 <= Ff) by lia. assert (GFc' : Ff < alloc_ceiling) by lia.
pose proof (shadow_blk_apart HIx _ _ _ _ _ _ _ _ _ Ff 32 HP INtk' GF0' GFc' ltac:(lia)) as DSt.
unfold APE_OUT, APE_EUNI_ARM4, APE_EUNI_POP in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8, A_SB in *.
pose proof (munch_refl [(tk, tk + 72); (Ff, Ff + 248); (Ff / 8 + 2147450880, Ff / 8 + 2147450880 + 32)] m) as MU.
stash Himg_t. stash Kpop. stash Kout. stash INV0. stash FR0. stash PBK. stash BK. stash GAP. stash SAVED. stash PB. stash TSK. stash REST.
reenterA asegs A4L HIx asegs_wx HP.
step.
nrm.
step.
nrm.
stepz.
step.
nrm.
step.
nrm.
step.
nrm.
step.
rewrite le1_w. lazymatch goal with |- context [write_to_mem _ _ [?bx]] => remember bx as b0 eqn:Eb0 end. clear Eb0. mem_after_store.
step. if_truex.
step.
nrm.
step.
nrm.
step.
nrm.
step.
nrm.
step.
nrm.
step.
rewrite le1_w. lazymatch goal with |- context [write_to_mem _ _ [?bx]] => remember bx as b1 eqn:Eb1 end. clear Eb1. mem_after_store.
step. if_truex.
step.
nrm.
step.
nrm.
step.
nrm.
step.
nrm.
step.
nrm.
step.
rewrite le1_w. lazymatch goal with |- context [write_to_mem _ _ [?bx]] => remember bx as b2 eqn:Eb2 end. clear Eb2. mem_after_store.
step. if_truex.
step.
nrm.
step.
nrm.
step.
nrm.
step.
rewrite le1_w. lazymatch goal with |- context [write_to_mem _ _ [?bx]] => remember bx as b3 eqn:Eb3 end. clear Eb3. mem_after_store.
step.
nrm.
step.
nrm.
step.
nrm.
step.
nrm.
rewrite ?sxb_zero, ?zxb_zero.
step.
first [ if_true | if_false ].
step.
nrm.
step.
nrm.
step.
nrm.
step.
nrm.
step.
nrm.

unstash INV0. unstash FR0. unstash PBK. unstash BK. unstash REST.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, FFc : rw_cells asegs mc Ff ?ffc, FSHc : rw_cells asegs mc (Ff / 8 + 2147450880) ?shc |- _ =>
assert (HW : Forall (pe_wtfA (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl)) [(tk, tk + 72); (Ff, Ff + 248); (Ff / 8 + 2147450880, Ff / 8 + 2147450880 + 32)])
by (apply Forall_cons; [left; cbn [fst snd pf_tk]; lia |]; apply Forall_cons; [right; right; left; cbn [fst snd pa_F]; lia |]; apply Forall_cons; [right; right; right; unfold shA, A_SB; cbn [fst snd pa_F]; lia | apply Forall_nil]);
assert (FRXc : pe_frameAX mc (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) nb pj sv ffc shc)
by (eapply (pe_frameAX_write HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS B ts0 A m mc md lo nb pj sv); [exact STC | exact HP | exact (pe_frameAX_of_A _ _ _ _ _ _ _ FR0) | exact MUc | exact WMc | exact FFc | exact FSHc]);
destruct (PE_INV_AX_tokw HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m mc md A B ts0 errv _ co (t_x ts0) _ _ STC (PE_INV_AX_of_A HIx GA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV0) MUc WMc MIc HW TOKc FRXc
ltac:(cbn [pf_len]; lia) eq_refl) as [INVX1 PBKX1];

assert (SRCB : bytes_at asegs mc (Ff + 128) [b0; b1; b2; b3])
by (pose proof FFc as FFs;
change ffc with ([CB 24 (pj_fhd pj); CB 40 (pj_f1 pj); C1 cb; CB 63 (firstn 63 (pj_f2 pj))] ++ ([C1 b0; C1 b1; C1 b2; C1 b3] ++ [CB 116 (skipn 1 (skipn 1 (skipn 1 (skipn 64 (pj_f2 pj)))))])) in FFs;
apply (proj1 (rw_cells_app asegs _ _ _ _)) in FFs as [_ FFs]; apply (proj1 (rw_cells_app asegs _ _ _ _)) in FFs as [FFs _];
cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.add_carry] in FFs; destruct FFs as [[_ HB] _]; cbn [cells_bytes cbytes app] in HB; exact HB);
assert (UNP : unpoisoned asegs mc 2147450880 (Ff + 128) 4)
by (pose proof FSHc as FSs;
match type of FSs with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?c11 :: ?c12 :: ?c13 :: ?c14 :: ?c15 :: ?c16 :: ?c17 :: ?c18 :: ?c19 :: ?c20 :: ?c21 :: ?c22 :: ?c23 :: ?rest) =>
change (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: c8 :: c9 :: c10 :: c11 :: c12 :: c13 :: c14 :: c15 :: c16 :: c17 :: c18 :: c19 :: c20 :: c21 :: c22 :: c23 :: rest)
with ([c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11; c12; c13; c14; c15] ++ ([c16; c17; c18; c19; c20; c21; c22; c23] ++ rest)) in FSs end;
apply (proj1 (rw_cells_app asegs _ _ _ _)) in FSs as [_ FSs]; apply (proj1 (rw_cells_app asegs _ _ _ _)) in FSs as [FSs _];
cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FSs; destruct FSs as [[_ WB] _]; cbn [cells_bytes cbytes app] in WB;
replace (Ff + 128) with (Ff + 8 * Z.of_nat 16) by lia;
eapply (scoped_unpoisoned_w mc Ff 4 16); [exact GF | lia | change (8 * (Z.of_nat 16 / 8)) with 16; unfold A_SB; exact WB | reflexivity | reflexivity | lia])
end end.
evt_done5.
lazymatch goal with FRXc : pe_frameAX ?mc _ _ _ _ _ ?ffc ?shc |- _ =>
eapply (pe_memappend_gX HIx GA GA_pres MAPP (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo mc md A B ts0 nb pj sv errv T (Ff + 128) 4 kP [b0; b1; b2; b3] ffc shc);
[ exact STC | exact BSL | exact INVX1 | cbn; lia | cbn; lia | exact (PBKX1 _ PBK) | cbn [t_co ts0]; lia | lia | exact BK | rewrite unsigned_lit by lia; reflexivity
| exact SRCB | reflexivity | lia
| right; first [left | idtac]; exists Ff, 2; split; [left; reflexivity | rewrite fr_size_2; lia]
| intros _; exact UNP | ]
end.
intros m2 md2 A2 B2 pbs2 errv2 r w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 F2 fc2 INVX2 OUT2 FS2 FRM2.
cbn [pf_spf pa_sp0 pa_F] in *. unfold A_TP in *.
clear TOK SLOTS FF FSH SHT1 MU WM MI HP INtk INtk' Htal Htlo Hthi DFt DSF DSt INV0 FR0 PBK BK REST INVX1 PBKX1 FRXc SRCB UNP HW.
set (ts2 := ts_pbs ts0 pbs2) in *.
pose proof INVX2 as [CORE2 REST2]. destruct CORE2 as (_ & _ & _ & _ & TOK & _ & _ & _ & FRX2). pose proof (proj1 REST2) as HP.
unfold ts2, ts_pbs, ts0 in TOK. cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_tk pf_mxd pf_fl] in TOK.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
pose proof FRX2 as (SLOTS & _ & _ & FF & FSH). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in SLOTS, FF, FSH. unfold shA, A_SB in FSH.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts2)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t2.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 4 HP INtk ltac:(lia)) as SHT4.
replace (tk / 8 + 4 + A_SB) with (tk / 8 + 2147450884) in SHT4 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 4 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT4t & _).
cbn [hl_sb A4L] in SEPT4t. assert (EQx : tk / 8 + A_SB + 4 = tk / 8 + 2147450884) by (unfold A_SB; lia). rewrite EQx in SEPT4t. clear EQx.
assert (INtk' : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts2 ++ LM)) by (apply in_or_app; left; exact INtk).
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP INF INtk') as DFt. rewrite fr_size_2 in DFt.
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP INF) as DSF. rewrite fr_size_2 in DSF. cbn [hl_sb A4L] in DSF.
pose proof (shadow_blk_apart HIx _ _ _ _ _ _ _ _ _ Ff 32 HP INtk' GF0' GFc' ltac:(lia)) as DSt.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs m2) as WM.
pose proof (munch_refl [(tk, tk + 72); (Ff, Ff + 248); (Ff / 8 + 2147450880, Ff / 8 + 2147450880 + 32)] m2) as MU.
assert (HW : Forall (pe_wtfA (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl)) [(tk, tk + 72); (Ff, Ff + 248); (Ff / 8 + 2147450880, Ff / 8 + 2147450880 + 32)])
by (apply Forall_cons; [left; cbn [fst snd pf_tk]; lia |]; apply Forall_cons; [right; right; left; cbn [fst snd pa_F]; lia |]; apply Forall_cons; [right; right; right; unfold shA, A_SB; cbn [fst snd pa_F]; lia | apply Forall_nil]).
assert (cs_T4_T : csep (tk / 8 + 2147450884) 1 tk (Z.of_nat 72)) by (unfold csep; clear - SEPT4t; lia).
assert (cs_FF_T : csep Ff 248 tk (Z.of_nat 72)) by (unfold csep; clear - DFt; lia).
assert (cs_T_FF : csep tk 72 Ff (Z.of_nat 248)) by (unfold csep; clear - DFt; lia).
assert (LF2 : length (pj_f2 pj) = 183%nat).
{ pose proof FF as [[Hwf _] _]. cbn in Hwf. destruct Hwf as (_ & _ & _ & L15 & Hrest). rewrite length_firstn in L15. destruct Hrest as (_ & Hrest). destruct Hrest as (_ & Hrest). destruct Hrest as (_ & Hrest). destruct Hrest as (_ & Hrest). destruct Hrest as (L167 & _). rewrite !length_skipn in L167. lia. }
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8, A_SB in *.
stash Himg_t2. stash INVX2. stash FRX2. stash REST2. clear SEPT4t.
lazymatch goal with |- AJ5 _ _ _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) => replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
reenterA asegs A4L HIx asegs_wx HP.
destruct OUT2 as [(-> & PBK2 & BK2) | [-> Epbs2]].
2:{
replace (Z_to_bv 64 (2^64 - 1)) with (Z_to_bv 64 (-1)) by (apply bv_eq; vm_compute; reflexivity).
step.
if_false.
step.
step.
asan_rechkB.
step.
step.
stepz.
step.
stepz.
step.
step.
set (pj' := PEJA (pj_0 pj) (pj_8 pj) (pj_16 pj) (pj_obj pj) (pj_288 pj) (pj_304 pj) (pj_gap pj) (pj_fhd pj) (pj_f1 pj) (firstn 63 (pj_f2 pj) ++ [b0; b1; b2; b3] ++ skipn 1 (skipn 1 (skipn 1 (skipn 64 (pj_f2 pj)))))).
unstash INVX2. unstash FRX2. cbn [t_pbs ts0] in Epbs2. subst pbs2.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m2 mc, WMc : wmono asegs m2 mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, FFc : rw_cells asegs mc Ff _, FSHc : rw_cells asegs mc (Ff / 8 + 2147450880) _ |- _ =>
evt_done5;
assert (FFc' : rw_cells asegs mc Ff (ff_cellsA cb pj'))
by (eapply rw_cells_recast;
[ exact FFc
| unfold ff_cellsA, pj'; cbn [pj_fhd pj_f1 pj_f2]; cbn [cells_wf cell_wf]; pose proof FFc as [[Hwf _] _]; cbn [cells_wf cell_wf] in Hwf; destruct Hwf as (W1 & W2 & _);
split; [exact W1|]; split; [exact W2|]; split; [exact I|]; split; [| exact I]; rewrite !length_app, length_firstn, !length_skipn; cbn [length]; lia
| unfold ff_cellsA, pj'; cbn [pj_fhd pj_f1 pj_f2 cells_bytes cbytes]; rewrite <- !app_assoc; reflexivity
| reflexivity ]);
assert (FRc : pe_frameA asegs mc (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) cb nb pj' sv)
by (apply pe_frameA_of_X; eapply (pe_frameAX_write HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS B2 ts2 A2 m2 mc md2 lo nb pj sv); [exact STC | exact HP | exact FRX2 | exact MUc | exact WMc | exact FFc' | exact FSHc]);
destruct (PE_INV_AX_tokw HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m2 mc md2 A2 B2 ts2 errv2 _ co (tx_err (t_x ts2) (Z_to_bv 64 16)) _ _ STC INVX2 MUc WMc MIc HW TOKc FRc
ltac:(cbn [pf_len]; lia) eq_refl) as [INV3 _]
end end.
unstash Kout. eapply (Kout _ md2 A2 B2 errv2 pj'); [exact INV3 | exact FS2 | exact FRM2]. }
step.
if_true.
step.
stepz.
step.
do 3 step.

set (pj' := PEJA (pj_0 pj) (pj_8 pj) (pj_16 pj) (pj_obj pj) (pj_288 pj) (pj_304 pj) (pj_gap pj) (pj_fhd pj) (pj_f1 pj) (firstn 63 (pj_f2 pj) ++ [b0; b1; b2; b3] ++ skipn 1 (skipn 1 (skipn 1 (skipn 64 (pj_f2 pj)))))).
unstash INVX2. unstash FRX2.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m2 mc, WMc : wmono asegs m2 mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, FFc : rw_cells asegs mc Ff _, FSHc : rw_cells asegs mc (Ff / 8 + 2147450880) _ |- _ =>
evt_done5;
assert (FFc' : rw_cells asegs mc Ff (ff_cellsA cb pj'))
by (eapply rw_cells_recast;
[ exact FFc
| unfold ff_cellsA, pj'; cbn [pj_fhd pj_f1 pj_f2]; cbn [cells_wf cell_wf]; pose proof FFc as [[Hwf _] _]; cbn [cells_wf cell_wf] in Hwf; destruct Hwf as (W1 & W2 & _);
split; [exact W1|]; split; [exact W2|]; split; [exact I|]; split; [| exact I]; rewrite !length_app, length_firstn, !length_skipn; cbn [length]; lia
| unfold ff_cellsA, pj'; cbn [pj_fhd pj_f1 pj_f2 cells_bytes cbytes]; rewrite <- !app_assoc; reflexivity
| reflexivity ]);
assert (FRc : pe_frameA asegs mc (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) cb nb pj' sv)
by (apply pe_frameA_of_X; eapply (pe_frameAX_write HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS B2 ts2 A2 m2 mc md2 lo nb pj sv); [exact STC | exact HP | exact FRX2 | exact MUc | exact WMc | exact FFc' | exact FSHc]);
destruct (PE_INV_AX_tokw HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m2 mc md2 A2 B2 ts2 errv2 _ co (t_x ts2) _ _ STC INVX2 MUc WMc MIc HW TOKc FRc
ltac:(cbn [pf_len]; lia) eq_refl) as [INV3 PBK3]
end end.
unstash Kpop. eapply (Kpop _ md2 A2 B2 pbs2 errv2 pj'); [exact INV3 | exact (PBK3 _ PBK2) | exact BK2 | exact FS2 | exact FRM2].
Qed.

Lemma euni_rep2_B :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (kP : Z)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kB : nat)
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
PBOKat m ts kP -> kP + 3 <= t_co ts + 1 -> BOK pf pa ts B kB ->
bytes_at asegs me UTF8REP_ADDR_A Qa8x.Mq3.utf8rep ->

(forall m' md' A' B' pbs' errv' pj' gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' (ts_pbs ts pbs') cb nb pj' sv errv' ->
PBOKat m' (ts_pbs ts pbs') (kP + 3) -> BOK pf pa (ts_pbs ts pbs') B' kB ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msO asegs pf pa APE_EUNI_POP gp' t0' (Z_to_bv 64 (pf_lenr pf)) (Z_to_bv 64 (pf_tk pf + 32)) a0' a1' a2' a3' a4' a5' a6' a7' s3' (Z_to_bv 64 (pf_sb pf + t_co ts)) s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' m')) ->

(forall m' md' A' B' errv' x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' ts cb nb pj sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msX asegs pf pa APE_ERR3 x1' gp' t0' t1' t2' (Z_to_bv 64 16) a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' m')) ->
AJ5 A4L HIx A T md
(pe_msX asegs pf pa APE_EUNI_REPL x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 (Z_to_bv 64 (pf_sb pf + t_co ts)) s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc m).
Proof.
intros until fc. intros STC BSL INV PBK Hroom BK UTF Kpop Kerr3. pose proof INV as INV0.
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
destruct INV as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof REST as (HP & LV & OBJ & ST & ERR & STR & PLEN & SBin & HPR & MDV & G & BUD).
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
unfold ts_pbs in Kpop. cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs] in Kpop.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
unfold pe_frameA in FR. destruct FR as (SLOTS & _). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS.
unfold pe_msX, pe_msO in *.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 1 HP INtk ltac:(lia)) as SHT1.
replace (tk / 8 + 1 + A_SB) with (tk / 8 + 2147450881) in SHT1 by (unfold A_SB; lia).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [] m) as MU.
assert (SRC : bytes_at asegs m UTF8REP_ADDR_A Qa8x.Mq3.utf8rep).
{ eapply (heap_presx_bytes_at A4H); [exact HPR | exact UTF |]. right; left. intros a Ha. cbn [length Qa8x.Mq3.utf8rep Z.of_nat Pos.of_succ_nat Pos.succ] in Ha. unfold UTF8REP_ADDR_A in Ha.
cbn [hl_client_static A4H]. unfold a4_client_static, a4_volatile. lia. }
unfold APE_ERR3, APE_EUNI_REPL, APE_EUNI_POP in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
stash Himg_t. clear PB TSK REST LV OBJ HPR BUD STR ERR SBin.
reenterA asegs A4L HIx asegs_wx HP.
step.
asan_chkB.
step.
step.
step. step.
step.
step.
evt_done5.
eapply (pe_memappend_g HIx GA GA_pres MAPP (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m md A B ts0 cb nb pj sv errv T UTF8REP_ADDR_A 3 kP Qa8x.Mq3.utf8rep);
[ exact STC | exact BSL | exact INV0 | exact PBK | cbn [t_co ts0]; lia | lia | exact BK | rewrite unsigned_lit by lia; reflexivity
| exact SRC | reflexivity | unfold UTF8REP_ADDR_A; lia | apply utf8rep_src_locA | intros _; exact (unpoisoned_of_glob HIx _ _ _ _ _ _ _ _ _ HP utf8rep_src_globA ltac:(lia)) |].
intros m2 md2 A2 B2 pbs2 errv2 r w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 F2 fc2 INV2 OUT2 FS2 FRM2.
cbn [pf_spf pa_sp0 pa_F] in *. unfold A_TP in *.
clear TOK SLOTS SHT1 MU WM MI HP INtk Htal Htlo Hthi SRC INV0 PBK BK.
pose proof INV2 as [CORE2 REST2]. destruct CORE2 as (_ & _ & _ & _ & _ & _ & _ & _ & FR2). pose proof (proj1 REST2) as HP. clear REST2.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 (ts_pbs ts0 pbs2))) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t2.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 4 HP INtk ltac:(lia)) as SHT4.
replace (tk / 8 + 4 + A_SB) with (tk / 8 + 2147450884) in SHT4 by (unfold A_SB; lia).
pose proof FR2 as (SLOTS & _). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS. cbn [pf_tk pf_spf pf_lenr pa_F pa_sp0 pa_oldloc pa_newloc] in SLOTS. unfold shA in SLOTS. a4l. unfold SB2, SB4, SB7, SB8 in SLOTS.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs m2) as WM.
pose proof (munch_refl [] m2) as MU.
clear FR2. stash Himg_t2.
lazymatch goal with |- AJ5 _ _ _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) => replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
reenterA asegs A4L HIx asegs_wx HP.
do 3 step.
destruct OUT2 as [(-> & PBK2 & BK2) | [-> Epbs2]].
2:{ replace (Z_to_bv 64 (2^64 - 1)) with (Z_to_bv 64 (-1)) by (apply bv_eq; vm_compute; reflexivity).
step.
if_false.
step.
step.
asan_rechkB.
step.
evt_done5.
eapply (Kerr3 m2 md2 A2 B2 errv2); [| exact FS2 | exact FRM2].
subst pbs2. exact INV2. }
step.
if_true.
evt_done5.
eapply (Kpop m2 md2 A2 B2 pbs2 errv2 pj); [exact INV2 | exact PBK2 | exact BK2 | exact FS2 | exact FRM2].
Qed.

Lemma euni_rep3_B :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (kP : Z)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kB : nat)
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
PBOKat m ts kP -> kP + 3 <= t_co ts + 1 -> BOK pf pa ts B kB ->
bytes_at asegs me UTF8REP_ADDR_A Qa8x.Mq3.utf8rep ->

(forall m' md' A' B' pbs' errv' pj' gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' (ts_pbs ts pbs') cb nb pj' sv errv' ->
PBOKat m' (ts_pbs ts pbs') (kP + 3) -> BOK pf pa (ts_pbs ts pbs') B' kB ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msO asegs pf pa APE_EUNI_POP gp' t0' (Z_to_bv 64 (pf_lenr pf)) (Z_to_bv 64 (pf_tk pf + 32)) a0' a1' a2' a3' a4' a5' a6' a7' s3' (Z_to_bv 64 (pf_sb pf + t_co ts)) s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' m')) ->

(forall m' md' A' B' errv' x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' ts cb nb pj sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msX asegs pf pa APE_ERR3 x1' gp' t0' t1' t2' (Z_to_bv 64 16) a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' m')) ->
AJ5 A4L HIx A T md
(pe_msX asegs pf pa APE_EUNI_REPB x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 (Z_to_bv 64 (pf_sb pf + t_co ts)) s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc m).
Proof.
intros until fc. intros STC BSL INV PBK Hroom BK UTF Kpop Kerr3. pose proof INV as INV0.
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
destruct INV as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof REST as (HP & LV & OBJ & ST & ERR & STR & PLEN & SBin & HPR & MDV & G & BUD).
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
unfold ts_pbs in Kpop. cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs] in Kpop.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
unfold pe_frameA in FR. destruct FR as (SLOTS & _). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS.
unfold pe_msX, pe_msO in *.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 1 HP INtk ltac:(lia)) as SHT1.
replace (tk / 8 + 1 + A_SB) with (tk / 8 + 2147450881) in SHT1 by (unfold A_SB; lia).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [] m) as MU.
assert (SRC : bytes_at asegs m UTF8REP_ADDR_A Qa8x.Mq3.utf8rep).
{ eapply (heap_presx_bytes_at A4H); [exact HPR | exact UTF |]. right; left. intros a Ha. cbn [length Qa8x.Mq3.utf8rep Z.of_nat Pos.of_succ_nat Pos.succ] in Ha. unfold UTF8REP_ADDR_A in Ha.
cbn [hl_client_static A4H]. unfold a4_client_static, a4_volatile. lia. }
unfold APE_ERR3, APE_EUNI_REPB, APE_EUNI_POP in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
stash Himg_t. clear PB TSK REST LV OBJ HPR BUD STR ERR SBin.
reenterA asegs A4L HIx asegs_wx HP.
step.
asan_chkB.
step.
step.
step. step.
step.
step.
evt_done5.
eapply (pe_memappend_g HIx GA GA_pres MAPP (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m md A B ts0 cb nb pj sv errv T UTF8REP_ADDR_A 3 kP Qa8x.Mq3.utf8rep);
[ exact STC | exact BSL | exact INV0 | exact PBK | cbn [t_co ts0]; lia | lia | exact BK | rewrite unsigned_lit by lia; reflexivity
| exact SRC | reflexivity | unfold UTF8REP_ADDR_A; lia | apply utf8rep_src_locA | intros _; exact (unpoisoned_of_glob HIx _ _ _ _ _ _ _ _ _ HP utf8rep_src_globA ltac:(lia)) |].
intros m2 md2 A2 B2 pbs2 errv2 r w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 F2 fc2 INV2 OUT2 FS2 FRM2.
cbn [pf_spf pa_sp0 pa_F] in *. unfold A_TP in *.
clear TOK SLOTS SHT1 MU WM MI HP INtk Htal Htlo Hthi SRC INV0 PBK BK.
pose proof INV2 as [CORE2 REST2]. destruct CORE2 as (_ & _ & _ & _ & _ & _ & _ & _ & FR2). pose proof (proj1 REST2) as HP. clear REST2.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 (ts_pbs ts0 pbs2))) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t2.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 4 HP INtk ltac:(lia)) as SHT4.
replace (tk / 8 + 4 + A_SB) with (tk / 8 + 2147450884) in SHT4 by (unfold A_SB; lia).
pose proof FR2 as (SLOTS & _). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS. cbn [pf_tk pf_spf pf_lenr pa_F pa_sp0 pa_oldloc pa_newloc] in SLOTS. unfold shA in SLOTS. a4l. unfold SB2, SB4, SB7, SB8 in SLOTS.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs m2) as WM.
pose proof (munch_refl [] m2) as MU.
clear FR2. stash Himg_t2.
lazymatch goal with |- AJ5 _ _ _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) => replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
reenterA asegs A4L HIx asegs_wx HP.
do 3 step.
destruct OUT2 as [(-> & PBK2 & BK2) | [-> Epbs2]].
2:{ replace (Z_to_bv 64 (2^64 - 1)) with (Z_to_bv 64 (-1)) by (apply bv_eq; vm_compute; reflexivity).
step.
if_false.
step.
step.
asan_rechkB.
step.
evt_done5.
eapply (Kerr3 m2 md2 A2 B2 errv2); [| exact FS2 | exact FRM2].
subst pbs2. exact INV2. }
step.
if_true.
evt_done5.
eapply (Kpop m2 md2 A2 B2 pbs2 errv2 pj); [exact INV2 | exact PBK2 | exact BK2 | exact FS2 | exact FRM2].
Qed.

Lemma euni_hs_B :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel) (u : Z)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP : Z)
(x1 gp t0 t1 t2 a0 a1 a2 a4 a5 a6 a7 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv -> PBOKat m ts kP ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_escape_unicode -> 0 <= u < 2^32 ->

(forall m' a0' a1' a2' a3' a4',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md A B
(ts_lvl (ts_set_x ts (t_co ts) (TS (ts_isd (t_x ts)) (ts_stpos (t_x ts)) (ts_choff (t_x ts)) (ts_err (t_x ts)) (Z_to_bv 64 0) (Z_to_bv 64 u) (ts_quote (t_x ts)))) (TL ST_esc_need_escape (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) cb nb pj sv errv ->
PBOKat m' (ts_lvl (ts_set_x ts (t_co ts) (TS (ts_isd (t_x ts)) (ts_stpos (t_x ts)) (ts_choff (t_x ts)) (ts_err (t_x ts)) (Z_to_bv 64 0) (Z_to_bv 64 u) (ts_quote (t_x ts)))) (TL ST_esc_need_escape (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) kP ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa APE_BREAK (t_co ts) gp t0 a0' a1' a2' a3' a4' a5 a6 a7 (Z_to_bv 64 (pf_tk pf / 8 + 2147450885)) (Z_to_bv 64 2) s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc m')) ->
AJ5 A4L HIx A T md
(pe_msX asegs pf pa APE_EUNI_HS x1 gp t0 t1 t2 a0 a1 a2 (Z_to_bv 64 u) a4 a5 a6 a7 (Z_to_bv 64 (pf_tk pf / 8 + 2147450885)) (Z_to_bv 64 (pf_sb pf + t_co ts)) (Z_to_bv 64 (pf_tk pf / 8 + 2147450885)) s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc m).
Proof.
intros until fc. intros STC INV PBK Hl Hst Hu Kbreak. pose proof INV as INV0. pe_openA STC INV.
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
pose proof FR as FR0. unfold pe_frameA in FR. destruct FR as (SLOTS & GAP & SAVED & FF & FSH).
unfold pe_slotsA in SLOTS. cbn zeta in SLOTS. unfold ff_cellsA in FF.
unfold pe_msX, pe_msA in *.
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
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 7 HP INtk ltac:(lia)) as SHT7.
replace (tk / 8 + 7 + A_SB) with (tk / 8 + 2147450887) in SHT7 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 7 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT7t & _).
cbn [hl_sb A4L] in SEPT7t. assert (EQx : tk / 8 + A_SB + 7 = tk / 8 + 2147450887) by (unfold A_SB; lia). rewrite EQx in SEPT7t. clear EQx.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 2 HP INtk ltac:(lia)) as SHT2.
replace (tk / 8 + 2 + A_SB) with (tk / 8 + 2147450882) in SHT2 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 2 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT2t & _).
cbn [hl_sb A4L] in SEPT2t. assert (EQx : tk / 8 + A_SB + 2 = tk / 8 + 2147450882) by (unfold A_SB; lia). rewrite EQx in SEPT2t. clear EQx.
unfold APE_BREAK, APE_EUNI_HS in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
assert (cs_tk_L : csep tk 72 bse (Z.of_nat 32)) by (unfold csep; clear - Hdtq HbseR; lia).
assert (cs_L_tk : csep bse 32 tk (Z.of_nat 72)) by (unfold csep; clear - Hdtq HbseR; lia).
assert (cs_T5_T : csep (tk / 8 + 2147450885) 1 tk (Z.of_nat 72)) by (unfold csep; clear - SEPT5t; lia).
assert (cs_T7_T : csep (tk / 8 + 2147450887) 1 tk (Z.of_nat 72)) by (unfold csep; clear - SEPT7t; lia).
assert (cs_T2_T : csep (tk / 8 + 2147450882) 1 tk (Z.of_nat 72)) by (unfold csep; clear - SEPT2t; lia).
assert (cs_Q0_T : csep (bse / 8 + 2147450880) 1 tk (Z.of_nat 72)) by (unfold csep; clear - SEPQ0t; lia).
clear Hdtq SEPQ0c SEPQ0q SEPQ0t SEPT5c SEPT5q SEPT5t SEPT7t SEPT2t.
stash Himg_t. stash Himg_q. stash Kbreak. clear PB REST TSK LV OBJ HPR BUD GAP SAVED FSH FF STR ERR SBin SHT SHQ SHQ4 MU.
pose proof (munch_refl [(tk, tk + 72)] m) as MU.
reenterA asegs A4L HIx asegs_wx HP.
asan_rechkB.
step.
step.
asan_rechkB.
step.
stepz.
set (x3 := TS isd stpos (Z_to_bv 64 co) err (Z_to_bv 64 0) (Z_to_bv 64 u) quote).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _ |- _ =>
destruct (PE_INV_A_tokw1 HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m mc md A B ts0
cb nb pj sv errv co x3 STC INV0 MUc WMc MIc TOKc ltac:(cbn [pf_len]; lia) eq_refl) as [INV3 PBT3];
clear MUc WMc; pose proof (munch_refl [(bse, bse + 32)] mc) as MUl; pose proof (wmono_refl asegs mc) as WMl
end end.
set (ts3 := ts_set_x ts0 co x3) in *.
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
asan_chkB.
step.
stepz.
step.
do 5 step.
assert (Hl3 : nth_error (t_levels ts3) (t_depth ts3) = Some l) by exact Hl.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mcF _) =>
lazymatch goal with MUc : munch _ ?mb mcF, WMc : wmono asegs ?mb mcF, MIc : mem_inv asegs mcF, TOKc : rw_cells asegs mcF tk _, Lc : rw_cells asegs mcF bse _ |- _ =>
evt_done5; rewrite Hbse in MUc, Lc;
destruct (PE_INV_A_lvl_write HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo mb mcF md A B ts3
cb nb pj sv errv l ST_esc_need_escape (tl_ss l) c0 hn0 c0 STC INV3 Hl3 MUc WMc MIc TOKc Lc Hmode
ltac:(rewrite <- Hmode; apply Qa8x.Mq3.lvl_mode_esc_same; [rewrite Hst; reflexivity | reflexivity | exact SS26]) ltac:(unfold ST_esc_need_escape; lia) SS26 (or_introl eq_refl)
ltac:(rewrite Hst; reflexivity)) as [INV4 PBK4];
unstash Kbreak; eapply (Kbreak mcF); [exact INV4 |]
end end.
lazymatch goal with |- PBOKat ?mF ?tF _ => pose proof (PBK4 (kP - co)) as P4 end. unfold PBOK in P4. cbn [t_co ts_lvl ts3 ts_set_x] in P4. replace (co + (kP - co)) with kP in P4 by lia.
apply P4. apply PBT3. exact PBK.
Qed.

Lemma euni_enc_B :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel) (u kP nmax : Z)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kB : nat)
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
PBOKat m ts kP -> kP + nmax <= t_co ts + 1 -> BOK pf pa ts B kB ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_escape_unicode ->
ts_ucs (t_x ts) = Z_to_bv 64 u -> 0 <= u < 2^31 -> 3 <= nmax -> (65536 <= u -> 4 <= nmax) ->
bytes_at asegs me UTF8REP_ADDR_A Qa8x.Mq3.utf8rep ->

(forall m' md' A' B' pbs' errv' pj' gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' (ts_pbs ts pbs') cb nb pj' sv errv' ->
PBOKat m' (ts_pbs ts pbs') (kP + nmax) -> BOK pf pa (ts_pbs ts pbs') B' kB ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msO asegs pf pa APE_EUNI_POP gp' t0' (Z_to_bv 64 (pf_lenr pf)) (Z_to_bv 64 (pf_tk pf + 32)) a0' a1' a2' a3' a4' a5' a6' a7' s3' (Z_to_bv 64 (pf_sb pf + t_co ts)) s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' m')) ->

(forall m' a0' a1' a2' a3' a4',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md A B
(ts_lvl (ts_set_x ts (t_co ts) (TS (ts_isd (t_x ts)) (ts_stpos (t_x ts)) (ts_choff (t_x ts)) (ts_err (t_x ts)) (Z_to_bv 64 0) (Z_to_bv 64 u) (ts_quote (t_x ts)))) (TL ST_esc_need_escape (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) cb nb pj sv errv ->
PBOKat m' (ts_lvl (ts_set_x ts (t_co ts) (TS (ts_isd (t_x ts)) (ts_stpos (t_x ts)) (ts_choff (t_x ts)) (ts_err (t_x ts)) (Z_to_bv 64 0) (Z_to_bv 64 u) (ts_quote (t_x ts)))) (TL ST_esc_need_escape (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) kP ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa APE_BREAK (t_co ts) gp t0 a0' a1' a2' a3' a4' a5 a6 a7 (Z_to_bv 64 (pf_tk pf / 8 + 2147450885)) (Z_to_bv 64 2) (Z_to_bv 64 (pf_tk pf + 40)) s7 s8 s9 s11 t3 t4 t5 t6 F fc m')) ->

(forall m' md' A' B' errv' pj' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' (ts_set_x ts (t_co ts) (tx_err (t_x ts) (Z_to_bv 64 16))) cb nb pj' sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msO asegs pf pa APE_OUT gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' m')) ->

(forall m' md' A' B' errv' x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' ts cb nb pj sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msX asegs pf pa APE_ERR3 x1' gp' t0' t1' t2' (Z_to_bv 64 16) a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' m')) ->
AJ5 A4L HIx A T md
(pe_msX asegs pf pa APE_EUNI_ENC x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (pf_tk pf / 8 + 2147450885)) (Z_to_bv 64 (pf_sb pf + t_co ts)) (Z_to_bv 64 (pf_tk pf / 8 + 2147450885)) (Z_to_bv 64 (pf_tk pf + 40)) s7 s8 s9 s11 t3 t4 t5 t6 F fc m).
Proof.
intros until fc. intros STC BSL INV PBK Hroom BK Hl Hst EU Hu Hn3 Hn4 UTF Kpop Khs Kout Kerr3. pose proof INV as INV0.
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
destruct INV as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof REST as (HP & _).
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff. subst ucs.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
unfold pe_frameA in FR. destruct FR as (SLOTS & _). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS.
unfold pe_msX, pe_msO, pe_msA in *. unfold APE_EUNI_ENC in *.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err (Z_to_bv 64 u) high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 5 HP INtk ltac:(lia)) as SHT5.
replace (tk / 8 + 5 + A_SB) with (tk / 8 + 2147450885) in SHT5 by (unfold A_SB; lia).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [] m) as MU.
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
stash Himg_t. clear PB TSK REST.
reenterA asegs A4L HIx asegs_wx HP.
asan_rechkB.
step.
norm_sx32.
step.
step.
assert (KPW : forall n, n <= nmax ->
forall m' md' A' B' pbs' errv' pj' gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc',
PE_INV_A HIx GA (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m' md' A' B' (ts_pbs ts0 pbs') cb nb pj' sv errv' ->
PBOKat m' (ts_pbs ts0 pbs') (kP + n) -> BOK (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) (ts_pbs ts0 pbs') B' kB ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msO asegs (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) APE_EUNI_POP gp' t0' (Z_to_bv 64 (pf_lenr (PEF tk oldl newl len lenr sb spf pmd mxd fl))) (Z_to_bv 64 (pf_tk (PEF tk oldl newl len lenr sb spf pmd mxd fl) + 32)) a0' a1' a2' a3' a4' a5' a6' a7' s3' (Z_to_bv 64 (pf_sb (PEF tk oldl newl len lenr sb spf pmd mxd fl) + t_co ts0)) s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' m')).
{ intros n Hn m' md' A' B' pbs' errv' pj' gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' INV' PBK' BK' FS' FRM'.
eapply (Kpop m' md' A' B' pbs' errv' pj'); [exact INV' | eapply PBOKat_weaken; [| exact PBK']; lia | exact BK' | exact FS' | exact FRM']. }
destruct (Z_le_dec u 127) as [L127 | G127].
{ if_falsex. evt_done5.
eapply (euni_enc1_B (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m md A B ts0 u kP cb nb pj sv errv T kB);
[exact STC | exact BSL | exact INV0 | exact PBK | cbn [t_co ts0] in *; lia | exact BK | lia | exact (KPW 1 ltac:(lia)) | exact Kout]. }
if_truex.
step.
step.
destruct (Z_le_dec u 2047) as [L2047 | G2047].
{ if_falsex. evt_done5.
eapply (euni_enc2_B (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m md A B ts0 u kP cb nb pj sv errv T kB);
[exact STC | exact BSL | exact INV0 | exact PBK | cbn [t_co ts0] in *; lia | exact BK | lia | exact (KPW 2 ltac:(lia)) | exact Kout]. }
if_truex.
step.
step. step.
step.
rewrite (unsigned_lit u) by lia.
pose proof (Z_land_range u 18446744073709550592 ltac:(lia) ltac:(lia)) as XR.
remember (Z.land u 18446744073709550592) as xm eqn:Exm.
destruct (Z.eq_dec xm 56320) as [ELOW | NLOW].
{
if_truex. evt_done5.
eapply (euni_rep2_B (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m md A B ts0 kP cb nb pj sv errv T kB);
[exact STC | exact BSL | exact INV0 | exact PBK | cbn [t_co ts0] in *; lia | exact BK | exact UTF | exact (KPW 3 ltac:(lia)) | exact Kerr3]. }
if_falsex.
step. step.
step.
destruct (Z.eq_dec xm 55296) as [EHIGH | NHIGH].
{
if_falsex. evt_done5.
eapply (euni_hs_B (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m md A B ts0 l u cb nb pj sv errv T kP);
[exact STC | exact INV0 | exact PBK | exact Hl | exact Hst | lia |].
exact Khs. }
if_truex.
step.
step.
rewrite (unsigned_lit u) by lia. unfold bv_wrap. change (bv_modulus 32) with (2^32). rewrite (Z.mod_small u (2^32)) by lia.
rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 16) with 65536.
assert (HR : 0 <= u / 65536 < 32768) by (clear - Hu; Z.div_mod_to_equations; lia).
remember (u / 65536) as uh eqn:Euh.
rewrite (swrap32_id uh) by lia.
destruct (Z.eq_dec uh 0) as [EH0 | NH0].
{ if_falsex. evt_done5.
eapply (euni_enc3_B (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m md A B ts0 u kP cb nb pj sv errv T kB);
[exact STC | exact BSL | exact INV0 | exact PBK | cbn [t_co ts0] in *; lia | exact BK | lia | exact (KPW 3 ltac:(lia)) | exact Kout]. }
if_truex.
assert (U16 : 65536 <= u) by (clear - Euh NH0 HR Hu; Z.div_mod_to_equations; lia).
specialize (Hn4 U16).
step.
step.
destruct (Z_lt_dec 16 uh) as [G16 | L16].
{ if_truex. evt_done5.
eapply (euni_rep3_B (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m md A B ts0 kP cb nb pj sv errv T kB);
[exact STC | exact BSL | exact INV0 | exact PBK | cbn [t_co ts0] in *; lia | exact BK | exact UTF | exact (KPW 3 ltac:(lia)) | exact Kerr3]. }
if_falsex. evt_done5.
eapply (euni_enc4_B (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m md A B ts0 u kP cb nb pj sv errv T kB);
[exact STC | exact BSL | exact INV0 | exact PBK | cbn [t_co ts0] in *; lia | exact BK | lia | exact (KPW 4 ltac:(lia)) | exact Kout].
Qed.

Lemma euni_tail_B :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel) (uw kP : Z)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kB : nat)
(gp t0 a0 a2 a3 a4 a6 a7 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
PBOKat m ts kP -> kP + 6 <= t_co ts + 1 -> BOK pf pa ts B kB ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_escape_unicode ->
ts_ucs (t_x ts) = Z_to_bv 64 uw -> 0 <= uw < 65536 ->
zin (tl_ss l) [ST_array_add; ST_ovadd] = false ->
bytes_at asegs me UTF8REP_ADDR_A Qa8x.Mq3.utf8rep ->

(forall m' md' A' B' pbs' errv' pj' (stq uq hq : word) gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B'
(ts_lvl (ts_pbs (ts_set_x ts (t_co ts) (TS (ts_isd (t_x ts)) stq (ts_choff (t_x ts)) (ts_err (t_x ts)) uq hq (ts_quote (t_x ts)))) pbs') (TL (tl_ss l) (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) cb nb pj' sv errv' ->
PBOKat m' (ts_lvl (ts_pbs (ts_set_x ts (t_co ts) (TS (ts_isd (t_x ts)) stq (ts_choff (t_x ts)) (ts_err (t_x ts)) uq hq (ts_quote (t_x ts)))) pbs') (TL (tl_ss l) (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) (kP + 6) ->
BOK pf pa (ts_pbs (ts_set_x ts (t_co ts) (TS (ts_isd (t_x ts)) stq (ts_choff (t_x ts)) (ts_err (t_x ts)) uq hq (ts_quote (t_x ts)))) pbs') B' kB ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msA asegs pf pa APE_BREAK (t_co ts) gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' (Z_to_bv 64 2) s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' m')) ->

(forall m' md' A' B' pbs' errv' (hq : word) gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B'
(ts_lvl (ts_pbs (ts_set_x ts (t_co ts) (TS (ts_isd (t_x ts)) (Z_to_bv 64 0) (ts_choff (t_x ts)) (ts_err (t_x ts)) (Z_to_bv 64 0) hq (ts_quote (t_x ts)))) pbs') (TL ST_esc_need_escape (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) cb nb pj sv errv' ->
PBOKat m' (ts_lvl (ts_pbs (ts_set_x ts (t_co ts) (TS (ts_isd (t_x ts)) (Z_to_bv 64 0) (ts_choff (t_x ts)) (ts_err (t_x ts)) (Z_to_bv 64 0) hq (ts_quote (t_x ts)))) pbs') (TL ST_esc_need_escape (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) (kP + 3) ->
BOK pf pa (ts_pbs (ts_set_x ts (t_co ts) (TS (ts_isd (t_x ts)) (Z_to_bv 64 0) (ts_choff (t_x ts)) (ts_err (t_x ts)) (Z_to_bv 64 0) hq (ts_quote (t_x ts)))) pbs') B' kB ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msA asegs pf pa APE_BREAK (t_co ts) gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' (Z_to_bv 64 2) s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' m')) ->

(forall m' md' A' B' pbs' errv' pj' (stq uq hq e : word) gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' (ts_pbs (ts_set_x ts (t_co ts) (TS (ts_isd (t_x ts)) stq (ts_choff (t_x ts)) e uq hq (ts_quote (t_x ts)))) pbs') cb nb pj' sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msO asegs pf pa APE_OUT gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' m')) ->

(forall m' md' A' B' pbs' errv' (stq uq hq : word) x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' (ts_pbs (ts_set_x ts (t_co ts) (TS (ts_isd (t_x ts)) stq (ts_choff (t_x ts)) (ts_err (t_x ts)) uq hq (ts_quote (t_x ts)))) pbs') cb nb pj sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msX asegs pf pa APE_ERR3 x1' gp' t0' t1' t2' (Z_to_bv 64 16) a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' m')) ->
AJ5 A4L HIx A T md
(pe_msO asegs pf pa APE_EUNI_TAIL gp t0 (Z_to_bv 64 (pf_lenr pf)) (Z_to_bv 64 (pf_tk pf + 32)) a0 (Z_to_bv 64 (pf_tk pf / 8 + 2147450883)) a2 a3 a4 (Z_to_bv 64 uw) a6 a7 (Z_to_bv 64 (pf_tk pf / 8 + 2147450885)) (Z_to_bv 64 (pf_sb pf + t_co ts)) s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc m).
Proof.
intros until fc. intros STC BSL INV PBK Hroom BK Hl Hst EU Hu Hzss UTF Kpop Khs Kout Kerr3. pose proof INV as INV0.
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
destruct INV as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof REST as (HP & LV & _).
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff. subst ucs.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
unfold ts_set_x, ts_pbs in Kpop, Khs, Kout, Kerr3.
cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in Kpop, Khs, Kout, Kerr3.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
unfold pe_frameA in FR. destruct FR as (SLOTS & _). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS.
unfold pe_msO, pe_msA, pe_msX in *. unfold APE_EUNI_TAIL in *.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err (Z_to_bv 64 uw) high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t.
pose proof (LV depth l Hl) as LVd. pose proof LVd as (ST26 & SS26 & _ & Md).
rewrite Nat.ltb_irrefl, Nat.eqb_refl in Md. destruct Md as (c0 & hn0 & Hmode & _).
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 3 HP INtk ltac:(lia)) as SHT3.
replace (tk / 8 + 3 + A_SB) with (tk / 8 + 2147450883) in SHT3 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 3 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT3t & _).
cbn [hl_sb A4L] in SEPT3t. assert (EQx : tk / 8 + A_SB + 3 = tk / 8 + 2147450883) by (unfold A_SB; lia). rewrite EQx in SEPT3t. clear EQx.
assert (cs_T3_T : csep (tk / 8 + 2147450883) 1 tk (Z.of_nat 72)) by (unfold csep; clear - SEPT3t; lia). clear SEPT3t.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 5 HP INtk ltac:(lia)) as SHT5.
replace (tk / 8 + 5 + A_SB) with (tk / 8 + 2147450885) in SHT5 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 5 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT5t & _).
cbn [hl_sb A4L] in SEPT5t. assert (EQx : tk / 8 + A_SB + 5 = tk / 8 + 2147450885) by (unfold A_SB; lia). rewrite EQx in SEPT5t. clear EQx.
assert (cs_T5_T : csep (tk / 8 + 2147450885) 1 tk (Z.of_nat 72)) by (unfold csep; clear - SEPT5t; lia). clear SEPT5t.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 1 HP INtk ltac:(lia)) as SHT1.
replace (tk / 8 + 1 + A_SB) with (tk / 8 + 2147450881) in SHT1 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 1 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT1t & _).
cbn [hl_sb A4L] in SEPT1t. assert (EQx : tk / 8 + A_SB + 1 = tk / 8 + 2147450881) by (unfold A_SB; lia). rewrite EQx in SEPT1t. clear EQx.
assert (cs_T1_T : csep (tk / 8 + 2147450881) 1 tk (Z.of_nat 72)) by (unfold csep; clear - SEPT1t; lia). clear SEPT1t.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(tk, tk + 72)] m) as MU.
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.

assert (ENCK : forall mX mdX AX BX pbsX errvX (hqX : word) (u kPX nmax : Z) x1X gpX t0X t1X t2X a0X a1X a2X a3X a4X a5X a6X a7X s7X s8X s9X s11X t3X t4X t5X t6X FX fcX,
PE_INV_A HIx GA (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo mX mdX AX BX
(TST depth levels co pb pbsX (TS isd (Z_to_bv 64 0) (Z_to_bv 64 co) err (Z_to_bv 64 u) hqX quote) obj objs objbs) cb nb pj sv errvX ->
PBOKat mX (TST depth levels co pb pbsX (TS isd (Z_to_bv 64 0) (Z_to_bv 64 co) err (Z_to_bv 64 u) hqX quote) obj objs objbs) kPX ->
kPX + nmax <= kP + 6 -> kPX <= kP + 3 ->
BOK (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) (TST depth levels co pb pbsX (TS isd (Z_to_bv 64 0) (Z_to_bv 64 co) err (Z_to_bv 64 u) hqX quote) obj objs objbs) BX kB ->
0 <= u < 2^31 -> 3 <= nmax -> (65536 <= u -> 4 <= nmax) ->
fsaved F FX -> (frm0 fc -> frm0 fcX) ->
AJ5 A4L HIx AX T mdX
(pe_msX asegs (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) APE_EUNI_ENC x1X gpX t0X t1X t2X a0X a1X a2X a3X a4X a5X a6X a7X
(Z_to_bv 64 (tk / 8 + 2147450885)) (Z_to_bv 64 (sb + co)) (Z_to_bv 64 (tk / 8 + 2147450885)) (Z_to_bv 64 (tk + 40)) s7X s8X s9X s11X t3X t4X t5X t6X FX fcX mX)).
{ intros mX mdX AX BX pbsX errvX hqX u kPX nmax x1X gpX t0X t1X t2X a0X a1X a2X a3X a4X a5X a6X a7X s7X s8X s9X s11X t3X t4X t5X t6X FX fcX INVX PBKX HroomX HkX BKX HuX Hn3 Hn4 FSX FRMX.
set (tsX := TST depth levels co pb pbsX (TS isd (Z_to_bv 64 0) (Z_to_bv 64 co) err (Z_to_bv 64 u) hqX quote) obj objs objbs) in *.
eapply (euni_enc_B (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo mX mdX AX BX tsX l u kPX nmax cb nb pj sv errvX T kB);
[exact STC | exact BSL | exact INVX | exact PBKX | cbn [t_co tsX]; lia | exact BKX | exact Hl | exact Hst | reflexivity | exact HuX | exact Hn3 | exact Hn4 | exact UTF | | | |].
-
intros m' md' A' B' pbs' errv' pj' gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' INV' PBK' BK' FS' FRM'.
eapply (euni_pop_B (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m' md' A' B' (ts_pbs tsX pbs') l cb nb pj' sv errv' T (kPX + nmax - co));
[exact STC | exact INV' | unfold PBOK; cbn [t_co ts_pbs tsX]; replace (co + (kPX + nmax - co)) with (kPX + nmax) by lia; exact PBK' | exact Hl | exact Hst
| intros c hn Hm; apply lvl_mode_euni_pop; [exact SS26 | rewrite <- Hst; exact Hm] | exact Hzss |].
intros m'' a0'' a1'' a2'' a3'' a4'' INV'' PBK''.
eapply (Kpop m'' md' A' B' pbs' errv' pj' (Z_to_bv 64 0) (Z_to_bv 64 u) hqX); [exact INV'' | | exact BK' | eapply fsaved_trans; [exact FSX | exact FS'] | intros X; exact (FRM' (FRMX X))].
unfold PBOK in PBK''. cbn [t_co ts_lvl ts_pbs tsX] in PBK''. eapply PBOKat_weaken; [| exact PBK'']. lia.
-
intros m' a0' a1' a2' a3' a4' INV' PBK'.
eapply (Khs m' mdX AX BX pbsX errvX (Z_to_bv 64 u)); [exact INV' | eapply PBOKat_weaken; [| exact PBK']; lia | | exact FSX | exact FRMX].
exact (BOK_set_x _ _ tsX BX kB co _ ltac:(cbn [t_co tsX]; lia) BKX).
-
intros m' md' A' B' errv' pj' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' INV' FS' FRM'.
eapply (Kout m' md' A' B' pbsX errv' pj' (Z_to_bv 64 0) (Z_to_bv 64 u) hqX (Z_to_bv 64 16)); [exact INV' | eapply fsaved_trans; [exact FSX | exact FS'] | intros X; exact (FRM' (FRMX X))].
-
intros m' md' A' B' errv' x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' INV' FS' FRM'.
eapply (Kerr3 m' md' A' B' pbsX errv' (Z_to_bv 64 0) (Z_to_bv 64 u) hqX); [exact INV' | eapply fsaved_trans; [exact FSX | exact FS'] | intros X; exact (FRM' (FRMX X))]. }
stash Himg_t. stash ENCK. clear Kpop Khs Kout.
stash Kerr3. clear PB TSK REST LV LVd.
reenterA asegs A4L HIx asegs_wx HP.
asan_rechkB.
step.
stepz.
step.
asan_chkMB 1.
try replace (tk / 8 + 5 + 2147450880) with (tk / 8 + 2147450885) by lia.
step.
step.
destruct (Z.eq_dec (bv_unsigned (sx32 high)) 0) as [EH0 | NH0].
{
if_truex.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _ |- _ =>
evt_done5;
destruct (PE_INV_A_tokw1 HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m mc md A B ts0
cb nb pj sv errv co (TS isd (Z_to_bv 64 0) (Z_to_bv 64 co) err (Z_to_bv 64 uw) high quote) STC INV0 MUc WMc MIc TOKc ltac:(cbn [pf_len]; lia) eq_refl) as [INV1 PBT1]
end end.
unstash ENCK.
eapply (ENCK _ md A B pbs errv high uw kP 4); [exact INV1 | exact (PBT1 _ PBK) | lia | lia | exact (BOK_set_x _ _ ts0 B kB co _ ltac:(cbn [t_co ts0]; lia) BK) | lia | lia | lia | apply fsaved_refl | intros X; exact X]. }
if_falsex.
step.
step.
step.
rewrite (unsigned_lit uw) by lia. unfold bv_wrap. change (bv_modulus 32) with (2^32). rewrite (Z.mod_small uw (2^32)) by lia.
rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 10) with 1024.
assert (ULR : 0 <= uw / 1024 < 64) by (clear - Hu; Z.div_mod_to_equations; lia).
remember (uw / 1024) as ul eqn:Eul.
rewrite (swrap32_id ul) by lia.
destruct (Z.eq_dec ul 55) as [E55 | N55].
{
if_falsex.
asan_rechkB.
step.
step.
step.
step.
step. step.
rewrite (unsigned_lit uw) by lia.
pose proof (bv_unsigned_in_range 64 (Z_to_bv 64 (bv_unsigned (sx32 high) ≪ 54))) as XR. unfold bv_modulus in XR. remember (bv_unsigned (Z_to_bv 64 (bv_unsigned (sx32 high) ≪ 54))) as xh eqn:Exh. clear Exh.
rewrite (Z.shiftr_div_pow2 xh 44) by lia.
assert (AR : 0 <= xh / 2 ^ 44 < 2 ^ 20) by (clear - XR; change (2 ^ 44) with 17592186044416; change (2 ^ 20) with 1048576; change (2 ^ 64) with 18446744073709551616 in XR; Z.div_mod_to_equations; lia).
remember (xh / 2 ^ 44) as ah eqn:Eah. clear Eah.
pose proof (OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.Bytes.land_lt_pow2 uw 1023 20 ltac:(change (2 ^ 20) with 1048576; lia) ltac:(lia)) as BR.
remember (Z.land uw 1023) as bl eqn:Ebl. clear Ebl.
rewrite (unsigned_lit ah) by (change (2 ^ 20) with 1048576 in AR; lia). rewrite (unsigned_lit bl) by (change (2 ^ 20) with 1048576 in BR; lia).
pose proof (OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.Bytes.lor_lt_pow2 ah bl 20 AR BR) as DR. change (2 ^ 20) with 1048576 in DR.
remember (Z.lor ah bl + 65536) as dv eqn:Edv.
assert (DVR : 0 <= dv < 2^31) by lia. clear Edv DR AR BR XR.
step.
step.
asan_rechkB.
stepz.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _ |- _ =>
evt_done5;
destruct (PE_INV_A_tokw1 HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m mc md A B ts0
cb nb pj sv errv co (TS isd (Z_to_bv 64 0) (Z_to_bv 64 co) err (Z_to_bv 64 dv) (Z_to_bv 64 0) quote) STC INV0 MUc WMc MIc TOKc ltac:(cbn [pf_len]; lia) eq_refl) as [INV1 PBT1]
end end.
unstash ENCK.
eapply (ENCK _ md A B pbs errv (Z_to_bv 64 0) dv kP 4); [exact INV1 | exact (PBT1 _ PBK) | lia | lia | exact (BOK_set_x _ _ ts0 B kB co _ ltac:(cbn [t_co ts0]; lia) BK) | lia | lia | lia | apply fsaved_refl | intros X; exact X]. }

if_truex.
step.
asan_chkB.
step.
step. step.
step.
step.
set (x1 := TS isd (Z_to_bv 64 0) (Z_to_bv 64 co) err (Z_to_bv 64 uw) high quote).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _ |- _ =>
evt_done5;
destruct (PE_INV_A_tokw1 HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m mc md A B ts0
cb nb pj sv errv co x1 STC INV0 MUc WMc MIc TOKc ltac:(cbn [pf_len]; lia) eq_refl) as [INV1 PBT1]
end end.
set (ts1 := ts_set_x ts0 co x1) in *.
lazymatch type of INV1 with PE_INV_A _ _ _ _ _ _ _ _ _ _ _ ?mc _ _ _ _ _ _ _ _ _ =>
assert (SRC : bytes_at asegs mc UTF8REP_ADDR_A Qa8x.Mq3.utf8rep)
by (pose proof INV1 as [_ REST1]; pose proof REST1 as (HP1 & _ & _ & _ & _ & _ & _ & _ & HPR1 & _);
eapply (heap_presx_bytes_at A4H); [exact HPR1 | exact UTF |]; right; left; intros a Ha; cbn [length Qa8x.Mq3.utf8rep Z.of_nat Pos.of_succ_nat Pos.succ] in Ha; unfold UTF8REP_ADDR_A in Ha;
cbn [hl_client_static A4H]; unfold a4_client_static, a4_volatile; lia);
eapply (pe_memappend_g HIx GA GA_pres MAPP (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo mc md A B ts1 cb nb pj sv errv T UTF8REP_ADDR_A 3 kP Qa8x.Mq3.utf8rep);
[ exact STC | exact BSL | exact INV1 | exact (PBT1 _ PBK) | cbn [t_co ts1 ts_set_x]; lia | lia | exact (BOK_set_x _ _ ts0 B kB co _ ltac:(cbn [t_co ts0]; lia) BK) | rewrite unsigned_lit by lia; reflexivity
| exact SRC | reflexivity | unfold UTF8REP_ADDR_A; lia | apply utf8rep_src_locA
| intros _; exact (unpoisoned_of_glob HIx _ _ _ _ _ _ _ _ _ (proj1 (proj2 INV1)) utf8rep_src_globA ltac:(lia)) |]
end.
intros m2 md2 A2 B2 pbs2 errv2 r w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 F2 fc2 INV2 OUT2 FS2 FRM2.
cbn [pf_spf pa_sp0 pa_F] in *. unfold A_TP in *.
clear TOK SLOTS SHT1 SHT3 SHT5 MU WM MI HP INtk Htal Htlo Hthi INV0 PBK BK INV1 PBT1 cs_T3_T cs_T5_T cs_T1_T.
set (ts2 := ts_pbs ts1 pbs2) in *.
pose proof INV2 as [CORE2 REST2]. destruct CORE2 as (_ & _ & _ & _ & TOK & _ & _ & _ & FR2). pose proof (proj1 REST2) as HP. clear REST2.
unfold ts2, ts_pbs, ts1, ts_set_x, ts0, x1 in TOK. cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_tk pf_mxd pf_fl] in TOK.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
pose proof FR2 as (SLOTS & _). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS. cbn [pf_tk pf_spf pf_lenr pa_F pa_sp0 pa_oldloc pa_newloc] in SLOTS. clear FR2.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts2)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t2.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 5 HP INtk ltac:(lia)) as SHT5.
replace (tk / 8 + 5 + A_SB) with (tk / 8 + 2147450885) in SHT5 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 5 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT5t & _).
cbn [hl_sb A4L] in SEPT5t. assert (EQx : tk / 8 + A_SB + 5 = tk / 8 + 2147450885) by (unfold A_SB; lia). rewrite EQx in SEPT5t. clear EQx.
assert (cs_T5_T : csep (tk / 8 + 2147450885) 1 tk (Z.of_nat 72)) by (unfold csep; clear - SEPT5t; lia). clear SEPT5t.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 4 HP INtk ltac:(lia)) as SHT4.
replace (tk / 8 + 4 + A_SB) with (tk / 8 + 2147450884) in SHT4 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 4 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT4t & _).
cbn [hl_sb A4L] in SEPT4t. assert (EQx : tk / 8 + A_SB + 4 = tk / 8 + 2147450884) by (unfold A_SB; lia). rewrite EQx in SEPT4t. clear EQx.
assert (cs_T4_T : csep (tk / 8 + 2147450884) 1 tk (Z.of_nat 72)) by (unfold csep; clear - SEPT4t; lia). clear SEPT4t.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs m2) as WM.
pose proof (munch_refl [(tk, tk + 72)] m2) as MU.
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
stash Himg_t2.
lazymatch goal with |- AJ5 _ _ _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) => replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
reenterA asegs A4L HIx asegs_wx HP.
step.
destruct OUT2 as [(-> & PBK2 & BK2) | [-> Epbs2]].
2:{ replace (Z_to_bv 64 (2^64 - 1)) with (Z_to_bv 64 (-1)) by (apply bv_eq; vm_compute; reflexivity).
step.
if_false.
step.
step.
asan_rechkB.
step.
evt_done5.
unstash Kerr3. subst pbs2.
eapply (Kerr3 m2 md2 A2 B2 pbs errv2 (Z_to_bv 64 0) (Z_to_bv 64 uw) high); [exact INV2 | exact FS2 | exact FRM2]. }
step.
if_true.
asan_rechkB.
stepz.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m2 mc, WMc : wmono asegs m2 mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _ |- _ =>
evt_done5;
destruct (PE_INV_A_tokw1 HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m2 mc md2 A2 B2 ts2
cb nb pj sv errv2 co (TS isd (Z_to_bv 64 0) (Z_to_bv 64 co) err (Z_to_bv 64 uw) (Z_to_bv 64 0) quote) STC INV2 MUc WMc MIc TOKc ltac:(cbn [pf_len]; lia) eq_refl) as [INV3 PBT3]
end end.
unstash ENCK.
eapply (ENCK _ md2 A2 B2 pbs2 errv2 (Z_to_bv 64 0) uw (kP + 3) 3); [exact INV3 | exact (PBT3 _ PBK2) | lia | lia | exact (BOK_set_x _ _ ts2 B2 kB co _ ltac:(cbn [t_co ts2 ts_pbs ts1 ts_set_x]; lia) BK2) | lia | lia | lia | exact FS2 | exact FRM2].
Qed.

Lemma seg_euni_B :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (k0 : Z) (kB : nat)
(gp t0 a5 a7 s3 s6 s7 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa -> pf_fl pf = 0 ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
PBOK m ts k0 -> k0 <= -2 -> BOK pf pa ts B kB ->
CSTR_OK pf payload ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_escape_unicode ->
t_co ts < pf_len pf -> nth_error payload (Z.to_nat (t_co ts)) = Some cb ->
SPV (t_x ts) = 0 -> bv_unsigned (ts_ucs (t_x ts)) mod 2^32 < 65536 ->
zin (tl_ss l) [ST_array_add; ST_ovadd] = false ->
bytes_at asegs me UTF8REP_ADDR_A Qa8x.Mq3.utf8rep ->

(forall m' md' A' B' pbs' errv' cb' pj' (stq uq hq : word) gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc',
t_co ts + 3 < pf_len pf -> nth_error payload (Z.to_nat (t_co ts + 3)) = Some cb' ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B'
(ts_lvl (ts_pbs (ts_set_x ts (t_co ts + 3) (TS (ts_isd (t_x ts)) stq (Z_to_bv 64 (t_co ts + 3)) (ts_err (t_x ts)) uq hq (ts_quote (t_x ts)))) pbs') (TL (tl_ss l) (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) cb' nb pj' sv errv' ->
PBOKat m' (ts_lvl (ts_pbs (ts_set_x ts (t_co ts + 3) (TS (ts_isd (t_x ts)) stq (Z_to_bv 64 (t_co ts + 3)) (ts_err (t_x ts)) uq hq (ts_quote (t_x ts)))) pbs') (TL (tl_ss l) (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) (t_co ts + k0 + 6) ->
BOK pf pa (ts_pbs (ts_set_x ts (t_co ts + 3) (TS (ts_isd (t_x ts)) stq (Z_to_bv 64 (t_co ts + 3)) (ts_err (t_x ts)) uq hq (ts_quote (t_x ts)))) pbs') B' kB ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msA asegs pf pa APE_BREAK (t_co ts + 3) gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' (Z_to_bv 64 2) s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' m')) ->

(forall m' md' A' B' pbs' errv' cb' (hq : word) gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc',
t_co ts + 3 < pf_len pf -> nth_error payload (Z.to_nat (t_co ts + 3)) = Some cb' ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B'
(ts_lvl (ts_pbs (ts_set_x ts (t_co ts + 3) (TS (ts_isd (t_x ts)) (Z_to_bv 64 0) (Z_to_bv 64 (t_co ts + 3)) (ts_err (t_x ts)) (Z_to_bv 64 0) hq (ts_quote (t_x ts)))) pbs') (TL ST_esc_need_escape (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) cb' nb pj sv errv' ->
PBOKat m' (ts_lvl (ts_pbs (ts_set_x ts (t_co ts + 3) (TS (ts_isd (t_x ts)) (Z_to_bv 64 0) (Z_to_bv 64 (t_co ts + 3)) (ts_err (t_x ts)) (Z_to_bv 64 0) hq (ts_quote (t_x ts)))) pbs') (TL ST_esc_need_escape (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) (t_co ts + k0 + 3) ->
BOK pf pa (ts_pbs (ts_set_x ts (t_co ts + 3) (TS (ts_isd (t_x ts)) (Z_to_bv 64 0) (Z_to_bv 64 (t_co ts + 3)) (ts_err (t_x ts)) (Z_to_bv 64 0) hq (ts_quote (t_x ts)))) pbs') B' kB ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msA asegs pf pa APE_BREAK (t_co ts + 3) gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' (Z_to_bv 64 2) s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' m')) ->

(forall m' md' A' B' pbs' errv' co' cb' pj' (stq uq hq e : word) gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc',
t_co ts <= co' <= pf_len pf ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' (ts_pbs (ts_set_x ts co' (TS (ts_isd (t_x ts)) stq (Z_to_bv 64 co') e uq hq (ts_quote (t_x ts)))) pbs') cb' nb pj' sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msO asegs pf pa APE_OUT gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' m')) ->

(forall m' md' A' B' pbs' errv' co' cb' (stq uq hq : word) gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc',
t_co ts <= co' <= pf_len pf ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' (ts_pbs (ts_set_x ts co' (TS (ts_isd (t_x ts)) stq (Z_to_bv 64 co') (ts_err (t_x ts)) uq hq (ts_quote (t_x ts)))) pbs') cb' nb pj sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msO asegs pf pa APE_ERR2 gp' t0' t1' t2' (Z_to_bv 64 12) a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' m')) ->

(forall m' md' A' B' pbs' errv' co' cb' (stq uq hq : word) x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc',
t_co ts <= co' <= pf_len pf ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' (ts_pbs (ts_set_x ts co' (TS (ts_isd (t_x ts)) stq (Z_to_bv 64 co') (ts_err (t_x ts)) uq hq (ts_quote (t_x ts)))) pbs') cb' nb pj sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msX asegs pf pa APE_ERR3 x1' gp' t0' t1' t2' (Z_to_bv 64 16) a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' m')) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa (pe_jtA ST_escape_unicode) (t_co ts) gp t0 (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) (Z_to_bv 64 (tl_st l)) (Z_to_bv 64 0) (Z_to_bv 64 (q / 8 + 4 * Z.of_nat (t_depth ts) + A_SB)) (Z_to_bv 64 0) a5 (Z_to_bv 64 APE_JTAB) a7 s3 (Z_to_bv 64 q) s6 s7 (Z_to_bv 64 (Z.of_nat (t_depth ts))) s9 s11 t3 t4 t5 t6 F fc m).
Proof.
intros until fc. intros STC BSL FL0 INV PBK K0 BK CSTR Hl Hst Hco Hc ESP HU Hzss UTF Kpop Khs Kout Kerr2 Kerr3. pose proof INV as INV0.
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
destruct INV as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof REST as (HP & _).
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *. subst fl.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
unfold ts_set_x, ts_pbs in Kpop, Khs, Kout, Kerr2, Kerr3.
cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in Kpop, Khs, Kout, Kerr2, Kerr3.
unfold pe_frameA in FR. destruct FR as (SLOTS & _ & _ & FF & _). unfold ff_cellsA in FF. unfold pe_slotsA in SLOTS. cbn zeta in SLOTS.
unfold pe_msA, pe_msO, pe_msX in *. unfold APE_EUNI_HEX in *.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (PBK0 : PBOKat m ts0 (co + k0)) by (unfold PBOK in PBK; cbn [t_co ts0] in PBK; exact PBK).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [] m) as MU.
pose proof (bv_unsigned_in_range 8 cb) as CBR; unfold bv_modulus in CBR; cbn in CBR.
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
clear PB TSK REST TOK.
reenterA asegs A4L HIx asegs_wx HP. rewrite Hst. unfold ST_escape_unicode. cbn [pe_jtA].
step.
step.
change (zxb cb) with (Z_to_bv 64 (bv_unsigned cb)).
step.
destruct (Z.eq_dec (bv_unsigned cb) 0) as [E0 | N0].
{
if_falsex. step.
evt_done5.
eapply (euni_err_B (PEF tk oldl newl len lenr sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m md A B ts0 cb nb pj sv errv T); [exact STC | exact INV0 |].
intros m' INVe. eapply (Kerr2 m' md A B pbs errv co cb stpos ucs high); [cbn [pf_len]; lia | exact INVe | apply fsaved_refl | intros X; exact X]. }
if_truex.
step.
evt_done5.
eapply (euni_hex_B 4%nat (PEF tk oldl newl len lenr sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m md A B ts0 l 0 (co + k0) cb nb pj sv errv T);
[exact STC | reflexivity | exact INV0 | exact PBK0 | exact CSTR | exact Hl | exact Hst | exact Hco | exact Hc | exact N0 | exact ESP | lia | exact HU | cbn; lia | | |].
-
intros m' co' cb' uw a0' a2' a3' a4' a6' s5' Eco' Hco' Hcb' Huw INV' PBK'.
cbn [t_co ts0] in Eco'. replace (co + (3 - 0)) with (co + 3) in Eco' by lia. subst co'.
eapply (euni_tail_B (PEF tk oldl newl len lenr sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m' md A B
(ts_set_x ts0 (co + 3) (TS isd (Z_to_bv 64 4) (Z_to_bv 64 (co + 3)) err (Z_to_bv 64 uw) high quote)) l uw (co + k0) cb' nb pj sv errv T kB);
[exact STC | exact BSL | exact INV' | exact PBK' | cbn [t_co ts_set_x]; lia | exact (BOK_set_x _ _ ts0 B kB (co + 3) _ ltac:(cbn [t_co ts0]; lia) BK) | exact Hl | exact Hst | reflexivity | exact Huw | exact Hzss | exact UTF | | | |];
cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote ts_set_x ts_pbs ts0].
+ intros m'' md' A' B' pbs' errv' pj' stq uq hq gp' t0' a0'' a1' a2'' a3'' a4'' a5' a6'' a7' s3' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' INV'' PBK'' BK'' FS' FRM'.
eapply (Kpop m'' md' A' B' pbs' errv' cb' pj' stq uq hq); [cbn [pf_len] in *; lia | exact Hcb' | exact INV'' | replace (co + k0 + 6) with (co + k0 + 6) by lia; exact PBK'' | exact BK'' | exact FS' | exact FRM'].
+ intros m'' md' A' B' pbs' errv' hq gp' t0' a0'' a1' a2'' a3'' a4'' a5' a6'' a7' s3' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' INV'' PBK'' BK'' FS' FRM'.
eapply (Khs m'' md' A' B' pbs' errv' cb' hq); [cbn [pf_len] in *; lia | exact Hcb' | exact INV'' | replace (co + k0 + 3) with (co + k0 + 3) by lia; exact PBK'' | exact BK'' | exact FS' | exact FRM'].
+ intros m'' md' A' B' pbs' errv' pj' stq uq hq e gp' t0' t1' t2' a0'' a1' a2'' a3'' a4'' a5' a6'' a7' s3' s4' s5'' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' INV'' FS' FRM'.
eapply (Kout m'' md' A' B' pbs' errv' (co + 3) cb' pj' stq uq hq e); [cbn [pf_len] in *; lia | exact INV'' | exact FS' | exact FRM'].
+ intros m'' md' A' B' pbs' errv' stq uq hq x1' gp' t0' t1' t2' a1' a2'' a3'' a4'' a5' a6'' a7' s3' s4' s5'' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' INV'' FS' FRM'.
eapply (Kerr3 m'' md' A' B' pbs' errv' (co + 3) cb' stq uq hq); [cbn [pf_len] in *; lia | exact INV'' | exact FS' | exact FRM'].
-
intros m' co' cb' stq uq gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' Hco' INV'.
cbn [t_co ts0 pf_len] in Hco'.
eapply (Kerr2 m' md A B pbs errv co' cb' stq uq high); [cbn [pf_len]; lia | exact INV' | apply fsaved_refl | intros X; exact X].
-
intros m' co' cb' stq uq e gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' Hco' INV'.
cbn [t_co ts0 pf_len] in Hco'.
eapply (Kout m' md A B pbs errv co' cb' pj stq uq high e); [cbn [pf_len]; lia | exact INV' | apply fsaved_refl | intros X; exact X].
Qed.
End PeSEuniB.
End RC__1.
