(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup Lib.GwApply QWxq_c1 QRjH QHnV QCcH QfLs Q0Ek Qtgi QjDH Qsw7 QJjn QRUw QkMG QG8z Qdyh QIsM Qhd4 Qwm6 QbFI QlKV QsKa Qiiq Q4v2 QSHS Ql4f Q1Y6 QrQv QEUF QdGy QMmN Qc5u QAzu Q6vt Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QJjn QRUw.Mq0 QRUw QkMG. Import QG8z Qdyh.Mq0 QIsM.Mq2.
Import Qhd4 Qwm6.
Import QbFI.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqj QsKa.Mqd Qiiq QsKa.Mqf Q4v2 QSHS Ql4f.Mq4 Q1Y6.Mq4 QsKa.Mqh QrQv.Mq4 QEUF.Mq2 QdGy.Mq9 QMmN.Mq0.
Import Qc5u QAzu.Mq0 Q6vt.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition APE_CEOL_NL : Z := 0x97364.
Definition APE_CEOL_LATCH : Z := 0x97a40.
Definition APE_CEOL_FLUSH : Z := 0x99cac.
Definition APE_CEOL_EOF : Z := 0x99764.

Section PeSCeolA.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_outside : forall m m' W, GA m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= hl_img_lo A4H \/ hl_img_hi A4H <= fst iv) W -> GA m'.
Hypothesis GA_pres : forall LB SP m m', heap_pres A4H LB SP m m' -> GA m -> GA m'.
Hypothesis MAPP : memappend_A_stmt2 HIx.

Lemma ceol_flush_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (co0 : Z)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kB : nat)
(gp t0 t1 t2 a0 a1 a3 a4 a5 a6 a7 s3 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
PBOKat m ts co0 -> BOK pf pa ts B kB ->
0 <= co0 <= t_co ts -> co0 < pf_len pf ->
(forall m' md' A' B' pbs' errv' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' (ts_pbs ts pbs') cb nb pj sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msO asegs pf pa APE_OUT gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' m')) ->
(forall m' md' A' B' pbs' errv' gp' t0' t1' t2' a0' a1' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' (ts_pbs ts pbs') cb nb pj sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msO asegs pf pa APE_ERRMEM2 gp' t0' t1' t2' a0' a1' (Z_to_bv 64 (pf_tk pf + 36)) a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' m')) ->
AJ5 A4L HIx A T md
(pe_msO asegs pf pa APE_CEOL_FLUSH gp t0 t1 t2 a0 a1 (Z_to_bv 64 (t_co ts - co0)) a3 a4 a5 a6 a7 s3 (Z_to_bv 64 (pf_sb pf + co0)) s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc m).
Proof.
intros until fc. intros STC BSL INV PBK BK Hco0 Hco0l Kout Kerr16. pose proof INV as INV0.
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
unfold pe_msO in *.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 1 HP INtk ltac:(lia)) as SHT1.
replace (tk / 8 + 1 + A_SB) with (tk / 8 + 2147450881) in SHT1 by (unfold A_SB; lia).
unfold APE_CEOL_FLUSH, APE_OUT, APE_ERRMEM2 in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
clear PB TSK REST.
reenterA asegs A4L HIx asegs_wx HP.
step.
asan_chkB.
do 3 step.
evt_done5.
eapply (pe_memappend_p HIx GA GA_pres MAPP (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m md A B ts0 cb nb pj sv errv T co0 (co - co0));
[exact STC | exact BSL | exact INV0 | exact PBK | lia | lia | cbn [t_co ts0]; lia | cbn [pf_len]; lia | cbn [pf_len]; lia | exact BK | rewrite unsigned_lit by lia; reflexivity |].
intros m2 md2 A2 B2 pbs2 errv2 r w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 F2 fc2 INV2 OUT2 FS2 FRM2.
cbn [pf_spf] in *. unfold A_TP in *.
clear TOK SLOTS SHT1 Htal Htlo Hthi Himg_t INtk HP INV0 PBK BK.
pose proof INV2 as [CORE2 REST2]. destruct CORE2 as (_ & _ & _ & _ & _ & _ & _ & _ & FR2). pose proof (proj1 REST2) as HP.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 (ts_pbs ts0 pbs2))) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 4 HP INtk ltac:(lia)) as SHT4.
replace (tk / 8 + 4 + A_SB) with (tk / 8 + 2147450884) in SHT4 by (unfold A_SB; lia).
pose proof FR2 as (SLOTS & _). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS. cbn [pf_tk pf_spf pf_lenr pa_F pa_sp0 pa_oldloc pa_newloc] in SLOTS. unfold shA in SLOTS. a4l. unfold SB2, SB4, SB7, SB8 in SLOTS.
clear REST2 FR2.
reenterA asegs A4L HIx asegs_wx HP.
destruct OUT2 as [(-> & _ & _) | [-> Epbs2]].
- step. step.
step. if_truex.
evt_done5.
eapply (Kout m2 md2 A2 B2 pbs2 errv2); [exact INV2 | exact FS2 | exact FRM2].
- replace (Z_to_bv 64 (2^64 - 1)) with (Z_to_bv 64 (-1)) by (apply bv_eq; vm_compute; reflexivity).
step. step.
step. if_false.
step.
asan_rechkB.
evt_done5.
eapply (Kerr16 m2 md2 A2 B2 pbs2 errv2); [exact INV2 | exact FS2 | exact FRM2].
Qed.

Lemma ceol_eof_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (co0 : Z)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kB : nat)
(gp t0 t1 t2 a0 a1 a3 a4 a5 a6 a7 s3 s6 s7 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
PBOKat m ts co0 -> BOK pf pa ts B kB ->
t_co ts = pf_len pf -> 0 <= co0 < pf_len pf ->
(forall m' md' A' B' pbs' (e : word) errv' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' (ts_pbs (ts_set_x ts (t_co ts) (tx_err (t_x ts) e)) pbs') cb nb pj sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msO asegs pf pa APE_OUT gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' m')) ->
(forall m' md' A' B' pbs' (e : word) errv' gp' t0' t1' t2' a0' a1' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' (ts_pbs (ts_set_x ts (t_co ts) (tx_err (t_x ts) e)) pbs') cb nb pj sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msO asegs pf pa APE_ERRMEM2 gp' t0' t1' t2' a0' a1' (Z_to_bv 64 (pf_tk pf + 36)) a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' m')) ->
AJ5 A4L HIx A T md
(pe_msO asegs pf pa APE_CEOL_EOF gp t0 t1 t2 a0 a1 (Z_to_bv 64 (pf_len pf - co0)) a3 a4 a5 a6 a7 s3 (Z_to_bv 64 (pf_sb pf + co0)) (Z_to_bv 64 q) s6 s7 (Z_to_bv 64 (Z.of_nat (t_depth ts))) s9 s11 t3 t4 t5 t6 F fc m).
Proof.
intros until fc. intros STC BSL INV PBK BK Heof Hco0 Kout Kerr16. pose proof INV as INV0.
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
destruct INV as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof REST as (HP & LV & _).
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
subst co.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
unfold pe_frameA in FR. destruct FR as (SLOTS & _). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS.
unfold pe_msO in *.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
set (ts0 := TST depth levels len pb pbs (TS isd stpos (Z_to_bv 64 len) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * mxd) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t.
blk_factsA A4L HIx HP q (32 * mxd) Hqal Hqlo Hqhi Himg_q.
pose proof (q_ne_tkA HIx _ _ _ _ _ _ _ _ _ _ HP) as Hqtk. cbn [pf_tk] in Hqtk.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ tk 72 q (32 * mxd) HP (in_or_app _ LM _ (or_introl INtk)) (in_or_app _ LM _ (or_introl INq)) ltac:(congruence)) as Hdtq.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 4 HP INtk ltac:(lia)) as SHT4.
replace (tk / 8 + 4 + A_SB) with (tk / 8 + 2147450884) in SHT4 by (unfold A_SB; lia).
pose proof (stack_shadowA HIx _ _ _ _ _ _ _ q mxd 0 0 HP INq ltac:(lia) ltac:(lia)) as SHQ0.
replace (q / 8 + 4 * 0 + 0 + A_SB) with (q / 8 + 2147450880) in SHQ0 by (unfold A_SB; lia).
assert (Hq8 : q mod 8 = 0) by (clear - Hqal; Z.div_mod_to_equations; lia).

destruct levels as [|l0 levels']; [cbn in LEN32; lia|].
pose proof (LV 0%nat l0 eq_refl) as (ST26 & SS26 & _).
pose proof (TSK 0%nat l0 eq_refl) as L0. unfold srec_cells in L0. replace (q + 32 * Z.of_nat 0) with q in L0 by lia.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(tk, tk + 72)] m) as MU.
unfold APE_CEOL_EOF, APE_CEOL_FLUSH, APE_OUT, APE_ERRMEM2 in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
stash Himg_t. stash Himg_q. clear PB TSK REST LV.
reenterA asegs A4L HIx asegs_wx HP.

lazymatch goal with |- evt _ _ (MS ?R ?FF _ ?fcc None ?mm ?rom) =>
assert (TAILE : forall e a1v, e = 0 \/ e = 1 ->
evt asegs (AJ5e A4L HIx A T md) (MS (bvmap_set 11 a1v (bvmap_set 10 (Z_to_bv 64 e) R)) FF (Z_to_bv 64 0x99c98) fcc None mm rom)) end.
{ intros e a1v He.
step.
asan_rechkB.
step.
stepz.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _ |- _ =>
evt_done5;
destruct (PE_INV_A_tokw1 HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m mc md A B ts0
cb nb pj sv errv len (tx_err (t_x ts0) (Z_to_bv 64 e)) STC INV0 MUc WMc MIc TOKc ltac:(cbn [pf_len]; lia) eq_refl) as [INVe PBKe];
eapply (ceol_flush_A (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo mc md A B
(ts_set_x ts0 len (tx_err (t_x ts0) (Z_to_bv 64 e))) co0 cb nb pj sv errv T kB);
[exact STC | exact BSL | exact INVe | exact (PBKe co0 PBK) | exact (BOK_set_x _ _ ts0 B kB len _ ltac:(cbn [t_co ts0]; lia) BK) | cbn [t_co ts_set_x]; lia | cbn [pf_len]; lia
| intros; eapply (Kout _ _ _ _ _ (Z_to_bv 64 e)); eassumption
| intros; eapply (Kerr16 _ _ _ _ _ (Z_to_bv 64 e)); eassumption]
end end. }
step.
destruct (Nat.eq_dec depth 0) as [D0 | Dn].
- subst depth. if_false.
step. ub_land Hq8. step. ub_if_lit.
asan_chkB.
step.
norm_sx32.
destruct (Z.eq_dec (tl_st l0) 0) as [S0 | Sn].
+ rewrite S0. step.
if_false.
step.
asan_chkB.
step.
norm_sx32.
step.
destruct (Z.eq_dec (tl_ss l0) 2) as [F2 | Fn].
* rewrite F2. step.
if_false.
step.
step.
apply (TAILE 0 _). left; reflexivity.
* step.
if_truex.
step.
step.
apply (TAILE 1 _). right; reflexivity.
+ step.
if_truex.
step.
step.
apply (TAILE 1 _). right; reflexivity.
- if_truex.
step.
step.
apply (TAILE 1 _). right; reflexivity.
Qed.

Lemma ceol_nl_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel) (co0 : Z)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (nB : nat)
(gp t0 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
PBOKat m ts co0 -> BOK pf pa ts B (S nB) ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_comment_eol ->
0 <= co0 <= t_co ts -> t_co ts < pf_len pf ->

(forall m' md' A' B' pbs' errv' gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B'
(ts_lvl (ts_pbs ts pbs') (TL ST_eatws (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) cb nb pj sv errv' ->
PBOK m' (ts_lvl (ts_pbs ts pbs') (TL ST_eatws (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) 1 ->
BOK pf pa (ts_lvl (ts_pbs ts pbs') (TL ST_eatws (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) B' nB ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msA asegs pf pa APE_BREAK (t_co ts) gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' (Z_to_bv 64 2) s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' m')) ->

(forall m' md' A' B' errv' x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' ts cb nb pj sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msX asegs pf pa APE_ERR3 x1' gp' t0' t1' t2' (Z_to_bv 64 16) a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' m')) ->
AJ5 A4L HIx A T md
(pe_msO asegs pf pa APE_CEOL_NL gp t0 (Z_to_bv 64 (pf_lenr pf)) (Z_to_bv 64 (pf_tk pf + 32)) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (pf_sb pf + t_co ts)) (Z_to_bv 64 (pf_sb pf + co0)) s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc m).
Proof.
intros until fc. intros STC BSL INV PBK BK Hl Hst Hco0 Hco Kbreak Kerr16. pose proof INV as INV0.
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
unfold pe_msO, pe_msA, pe_msX in *.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 1 HP INtk ltac:(lia)) as SHT1.
replace (tk / 8 + 1 + A_SB) with (tk / 8 + 2147450881) in SHT1 by (unfold A_SB; lia).
unfold APE_CEOL_NL, APE_BREAK, APE_ERR3 in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
set (n := co - co0) in *.
assert (SBpos : 0 < sb) by (exact (pe_sb_pos HIx GA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV0 ltac:(cbn [pf_len]; lia))).
clear PB TSK REST.
reenterA asegs A4L HIx asegs_wx HP.
step.
asan_chkB.
step. step.
norm_w32. replace (sb + co - (sb + co0)) with n by (unfold n; lia).
step. step.
evt_done5.
eapply (pe_memappend_p HIx GA GA_pres MAPP (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m md A B ts0 cb nb pj sv errv T co0 n);
[exact STC | exact BSL | exact INV0 | exact PBK | lia | unfold n; lia | unfold n; cbn [t_co ts0]; lia | unfold n; cbn [pf_len]; lia | cbn [pf_len]; lia | exact BK | rewrite unsigned_lit by lia; reflexivity |].
intros m2 md2 A2 B2 pbs2 errv2 r w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 F2 fc2 INV2 OUT2 FS2 FRM2.
cbn [pf_spf] in *. unfold A_TP in *.

clear TOK SLOTS SHT1 Htal Htlo Hthi Himg_t INtk HP INV0 PBK BK.
set (ts2 := ts_pbs ts0 pbs2) in *.
pose proof INV2 as INV2'. destruct INV2' as [CORE2 REST2].
destruct CORE2 as (_ & _ & _ & _ & TOK & _ & _ & TSK & FR).
pose proof REST2 as (HP & LV & _).
unfold ts2, ts_pbs, ts0 in TOK, TSK, LV. cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_tk pf_mxd pf_fl] in TOK, TSK, LV.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
unfold pe_frameA in FR. destruct FR as (SLOTS & _ & _ & FF & _). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS. unfold ff_cellsA in FF.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in SLOTS, FF.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts2)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * mxd) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts2)) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t.
blk_factsA A4L HIx HP q (32 * mxd) Hqal Hqlo Hqhi Himg_q.
pose proof (q_ne_tkA HIx _ _ _ _ _ _ _ _ _ _ HP) as Hqtk. cbn [pf_tk] in Hqtk.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ tk 72 q (32 * mxd) HP (in_or_app _ LM _ (or_introl INtk)) (in_or_app _ LM _ (or_introl INq)) ltac:(congruence)) as Hdtq.
pose proof (tok_shadowA HIx _ _ _ _ _ _ _ _ HP INtk) as SHT.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs m2) as WM.
pose proof (LV depth l Hl) as LVd. pose proof LVd as (ST26 & SS26 & _ & Md).
rewrite Nat.ltb_irrefl, Nat.eqb_refl in Md. destruct Md as (c0 & hn0 & Hmode & CLS0 & NM0).
pose proof (TSK depth l Hl) as Ld. remember (q + 32 * Z.of_nat depth) as bse eqn:Hbse in Ld. unfold srec_cells in Ld.
assert (HbseR : q <= bse /\ bse + 32 <= q + (32 * mxd)) by (subst bse; lia).
pose proof (stack_shadowA HIx _ _ _ _ _ _ _ q mxd (Z.of_nat depth) 0 HP INq ltac:(lia) ltac:(lia)) as SHQ.
replace (q / 8 + 4 * Z.of_nat depth + 0 + A_SB) with (q / 8 + 4 * Z.of_nat depth + A_SB) in SHQ by lia.
assert (Hb8 : bse mod 8 = 0) by (subst bse; clear - Hqal; Z.div_mod_to_equations; lia).
assert (SHQ4 : ro_cells asegs m2 (bse / 8 + A_SB) [C1 (Z_to_bv 8 0)]).
{ replace (bse / 8) with (q / 8 + 4 * Z.of_nat depth) by (subst bse; rewrite div8_add_mul32 by lia; lia). exact SHQ. }
pose proof (munch_refl [(bse, bse + 32)] m2) as MU.
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
stash Himg_t. stash Himg_q. clear LV TSK.
reenterA asegs A4L HIx asegs_wx HP.
destruct OUT2 as [(-> & PBK2 & BK2) | [-> Epbs2]].
2:{ replace (Z_to_bv 64 (2^64 - 1)) with (Z_to_bv 64 (-1)) by (apply bv_eq; vm_compute; reflexivity).
step. if_false.
step. step.
asan_rechkB.
step.
evt_done5.
eapply (Kerr16 m2 md2 A2 B2 errv2); [| exact FS2 | exact FRM2].
subst pbs2. exact INV2. }
assert (BLO : 0 < bse < 2^63 /\ q <= bse) by (subst bse; lia).
step. if_truex.
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
asan_chkMB 1.
stepz.
step. step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m2 mc, WMc : wmono asegs m2 mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, Lc : rw_cells asegs mc bse _ |- _ =>
evt_done5; subst bse;
destruct (PE_INV_A_lvl_write HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m2 mc md2 A2 B2 ts2
cb nb pj sv errv2 l ST_eatws (tl_ss l) c0 hn0 c0 STC INV2 Hl MUc WMc MIc TOKc Lc Hmode
ltac:(rewrite <- Hmode; apply QIsM.Mq2.lvl_mode_ws_same; [rewrite Hst; reflexivity | reflexivity])
ltac:(unfold ST_eatws; lia) SS26 (or_introl eq_refl) ltac:(rewrite Hst; reflexivity)) as [INV3 PBK3];
eapply (Kbreak mc md2 A2 B2 pbs2 errv2);
[exact INV3
| apply PBK3; unfold PBOK; eapply PBOKat_weaken; [| exact PBK2]; unfold n, ts2, ts_pbs, ts0; cbn [t_co]; lia
| exact (BOK_lvl_restate _ _ ts2 B2 nB l ST_eatws (tl_ss l) Hl (lvl_closed_keep l ST_eatws _ _ _ _ _ eq_refl) (BOK_weaken _ _ _ _ _ nB (Nat.le_succ_diag_r nB) BK2))
| exact FS2 | exact FRM2]
end end.
Qed.

Ltac frameA_now mc :=
unfold pe_frameA, pe_slotsA, pe_savedA_cells, ff_cellsA, ffsh_cells, FSH0; cbn [map pf_tk pf_spf pf_lenr pa_F pa_sp0 pa_oldloc pa_newloc]; unfold shA, A_SB;
split; [| split; [| split; [| split]]];
match goal with H : rw_cells asegs mc ?a _ |- rw_cells asegs mc ?a _ => exact H end.

Lemma ceol_latch_A :
forall (n : nat) (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel) (co0 : Z)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kB : nat)
(gp t0 a0 a3 a5 a6 a7 s6 s7 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa -> pf_fl pf = 0 ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
PBOKat m ts co0 -> BOK pf pa ts B kB ->
CSTR_OK pf payload ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_comment_eol ->
0 <= co0 <= t_co ts -> t_co ts < pf_len pf -> nth_error payload (Z.to_nat (t_co ts)) = Some cb -> bv_unsigned cb <> 10 ->
(pf_len pf - t_co ts <= Z.of_nat n) ->

(forall m' co' cb' a0' a1' a2' a4' a5' a6',
t_co ts < co' < pf_len pf -> nth_error payload (Z.to_nat co') = Some cb' -> bv_unsigned cb' = 10 ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md A B (ts_set_co ts co') cb' nb pj sv errv ->
PBOKat m' (ts_set_co ts co') co0 ->
AJ5 A4L HIx A T md
(pe_msO asegs pf pa APE_CEOL_NL gp t0 (Z_to_bv 64 (pf_lenr pf)) (Z_to_bv 64 (pf_tk pf + 32)) a0' a1' a2' a3 a4' a5' a6' a7 (Z_to_bv 64 (pf_sb pf + co')) (Z_to_bv 64 (pf_sb pf + co0)) (Z_to_bv 64 q) s6 s7 (Z_to_bv 64 (Z.of_nat (t_depth ts))) s9 s11 t3 t4 t5 t6 F fc m')) ->

(forall m' md' A' B' pbs' (e : word) co' cb' errv' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc',
t_co ts < co' <= pf_len pf ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B'
(ts_pbs (ts_set_x ts co' (TS (ts_isd (t_x ts)) (ts_stpos (t_x ts)) (Z_to_bv 64 co') e (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))) pbs') cb' nb pj sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msO asegs pf pa APE_OUT gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' m')) ->

(forall m' md' A' B' pbs' (e : word) co' cb' errv' gp' t0' t1' t2' a0' a1' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc',
t_co ts < co' <= pf_len pf ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B'
(ts_pbs (ts_set_x ts co' (TS (ts_isd (t_x ts)) (ts_stpos (t_x ts)) (Z_to_bv 64 co') e (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))) pbs') cb' nb pj sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msO asegs pf pa APE_ERRMEM2 gp' t0' t1' t2' a0' a1' (Z_to_bv 64 (pf_tk pf + 36)) a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' m')) ->
AJ5 A4L HIx A T md
(pe_msO asegs pf pa APE_CEOL_LATCH gp t0 (Z_to_bv 64 (pf_lenr pf)) (Z_to_bv 64 (pf_tk pf + 32)) a0 (Z_to_bv 64 (pf_sb pf + t_co ts)) (Z_to_bv 64 (t_co ts + 1 - co0)) a3 (Z_to_bv 64 (bv_unsigned cb)) a5 a6 a7 (Z_to_bv 64 (pf_sb pf + t_co ts)) (Z_to_bv 64 (pf_sb pf + co0)) (Z_to_bv 64 q) s6 s7 (Z_to_bv 64 (Z.of_nat (t_depth ts))) s9 s11 t3 t4 t5 t6 F fc m).
Proof.
induction n as [|n IH]; intros until fc; intros STC BSL FL0 INV PBK BK CSTR Hl Hst Hco0 Hco Hc N42 Hn Kstar Kout Kerr16.
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
unfold ts_set_co, ts_set_x, ts_pbs in Kstar, Kout, Kerr16.
cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in Kstar, Kout, Kerr16.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
pose proof FR as FR0. unfold pe_frameA in FR. destruct FR as (SLOTS & GAP & SAVED & FF & FSH). unfold pe_msO in *.
unfold pe_slotsA in SLOTS. cbn zeta in SLOTS. unfold pe_savedA_cells in SAVED. unfold ff_cellsA in FF. unfold ffsh_cells, FSH0 in FSH. cbn [map] in FSH.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd 0) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 4 HP INtk ltac:(lia)) as SHT4.
replace (tk / 8 + 4 + A_SB) with (tk / 8 + 2147450884) in SHT4 by (unfold A_SB; lia).
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 8 HP INtk ltac:(lia)) as SHT8.
replace (tk / 8 + 8 + A_SB) with (tk / 8 + 2147450888) in SHT8 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 4 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (SEP4c & SEP4t & SEP4i). cbn [hl_sb A4L] in SEP4c, SEP4t, SEP4i.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 8 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (SEP8c & SEP8t & SEP8i). cbn [hl_sb A4L] in SEP8c, SEP8t, SEP8i.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs m) as WM.
pose proof (bytes_at_bound _ _ _ _ STR) as SBB.
pose proof alloc_ceiling_range as ACR.
pose proof (bv_unsigned_in_range 8 cb) as CBR; unfold bv_modulus in CBR; cbn in CBR.

assert (INF : In (Ff, 2) ((Ff, 2) :: FRS)) by (left; reflexivity).
assert (INtk' : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd 0) q LB0 ts0 ++ LM)) by (apply in_or_app; left; exact INtk).
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP INF INtk') as DFt. rewrite fr_size_2 in DFt.
assert (GF0' : 0 <= Ff) by lia. assert (GFc' : Ff < alloc_ceiling) by lia.
pose proof (shadow_blk_apart HIx _ _ _ _ _ _ _ _ _ Ff 32 HP INtk' GF0' GFc' ltac:(lia)) as DSt.
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP INF) as DSF. rewrite fr_size_2 in DSF. cbn [hl_sb A4L] in DSF.
destruct SBin as [L00 | PL]; [exfalso; lia|].
unfold APE_CEOL_LATCH, APE_CEOL_NL, APE_CEOL_FLUSH, APE_CEOL_EOF, APE_OUT, APE_ERRMEM2 in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8, A_SB in *.
pose proof (munch_refl [(tk, tk + 72); (Ff + 64, Ff + 65)] m) as MU.
assert (HW : Forall (pe_wtfA (PEF tk oldl newl len lenr sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl)) [(tk, tk + 72); (Ff + 64, Ff + 65)]).
{ apply Forall_cons; [left; cbn [fst snd pf_tk]; lia |]. apply Forall_cons; [| apply Forall_nil]. right; right; left. cbn [fst snd pa_F]. lia. }
clear LV OBJ HPR.
assert (SBpos : 0 < sb) by (exact (pe_sb_pos HIx GA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV0 ltac:(cbn [pf_len]; lia))).
destruct (Z.eq_dec (bv_unsigned cb) 0) as [E0 | N0].
{
stash PB. stash TSK.
reenterA asegs A4L HIx asegs_wx HP.
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
if_falsex. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _ |- _ =>
assert (FRc : pe_frameA asegs mc (PEF tk oldl newl len lenr sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) cb nb pj sv) by (frameA_now mc);
evt_done5;
destruct (PE_INV_A_tokw HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m mc md A B ts0
cb nb pj sv errv _ (co + 1) (TS isd stpos (Z_to_bv 64 (co + 1)) err ucs high quote) cb nb STC INV0 MUc WMc MIc HW TOKc FRc
ltac:(cbn [pf_len]; lia) eq_refl) as [INV1 PBK1];
eapply (ceol_flush_A (PEF tk oldl newl len lenr sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo mc md A B
(ts_set_x ts0 (co + 1) (TS isd stpos (Z_to_bv 64 (co + 1)) err ucs high quote)) co0 cb nb pj sv errv T kB);
[exact STC | exact BSL | exact INV1 | exact (PBK1 co0 PBK) | exact (BOK_set_x _ _ ts0 B kB (co + 1) _ ltac:(cbn [t_co ts0]; lia) BK)
| cbn [t_co ts_set_x]; lia | cbn [pf_len]; lia
| intros; eapply (Kout _ _ _ _ _ err (co + 1) cb); [lia | eassumption | eassumption | eassumption]
| intros; eapply (Kerr16 _ _ _ _ _ err (co + 1) cb); [lia | eassumption | eassumption | eassumption]]
end end. }
destruct (peek_cases (PEF tk oldl newl len lenr sb spf pmd mxd 0) payload co cb LENR CSTR (proj1 RR) ltac:(cbn [pf_len pf_mxd]; lia) ltac:(cbn [pf_len pf_mxd]; lia) Hc N0)
as [[Elenr Heof] | [Hne Hmore]]; cbn [pf_len pf_lenr pf_mxd] in *.
{
subst lenr. stash PB. stash TSK.
reenterA asegs A4L HIx asegs_wx HP.
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
if_truex.
step.
rewrite Heof. if_false. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _ |- _ =>
assert (FRc : pe_frameA asegs mc (PEF tk oldl newl len len sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) cb nb pj sv) by (frameA_now mc);
evt_done5;
destruct (PE_INV_A_tokw HIx GA GA_outside (PEF tk oldl newl len len sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m mc md A B ts0
cb nb pj sv errv _ (co + 1) (TS isd stpos (Z_to_bv 64 (co + 1)) err ucs high quote) cb nb STC INV0 MUc WMc MIc HW TOKc FRc
ltac:(cbn [pf_len]; lia) eq_refl) as [INV1 PBK1];
replace (Z_to_bv 64 (co + 1 - co0)) with (Z_to_bv 64 (len - co0)) by (f_equal; lia);
eapply (ceol_eof_A (PEF tk oldl newl len len sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo mc md A B
(ts_set_x ts0 (co + 1) (TS isd stpos (Z_to_bv 64 (co + 1)) err ucs high quote)) co0 cb nb pj sv errv T kB);
[exact STC | exact BSL | exact INV1 | exact (PBK1 co0 PBK) | exact (BOK_set_x _ _ ts0 B kB (co + 1) _ ltac:(cbn [t_co ts0]; lia) BK)
| cbn [t_co ts_set_x pf_len]; lia | cbn [pf_len]; lia
| intros; eapply (Kout _ _ _ _ _ e (co + 1) cb); [lia | eassumption | eassumption | eassumption]
| intros; eapply (Kerr16 _ _ _ _ _ e (co + 1) cb); [lia | eassumption | eassumption | eassumption]]
end end. }

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
assert (LE1 : le1 (zxb c') = [c']).
{ unfold le1, zxb. cbn [Z_to_le_bytes pf_mxd]. f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 8) with 256%Z. change (bv_modulus 64) with 18446744073709551616%Z. Z.div_mod_to_equations. nia. }

stash PB. stash TSK. stash Hv. stash GAP. stash SAVED. stash FSH. stash DSt. stash DSF. stash SHPF.
stash IH. stash Kstar. stash Kout. stash Kerr16. stash INV0. stash REST. stash FR0. stash PBK. stash BK. stash SBc. stash SBhi. stash LE1. stash Hc'. stash Hc. stash STR. stash HW.
reenterA asegs A4L HIx asegs_wx HP.
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
stash DFt. stash DSPt. clear SEP4c SEP4t SEP4i SEP8c SEP8t SEP8i SHT4.
step.
if_truex.
step.
if_truex.
step.
asan_rechkB.
clear SHT8.
step.
lazymatch goal with TOKc : rw_cells asegs ?mc tk _ |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (tok_flags_byteA mxd 0 mc tk pb (Z.of_nat depth) q (TS isd stpos (Z_to_bv 64 (co + 1)) err ucs high quote) TOKc) as RDF end.
step.
rewrite ?zxb_zero. clear RDF.
step. step.
step.
if_true.
step. step. step.
sh_norm.

lazymatch goal with |- evt _ _ (MS ?R ?FF _ ?fcc None ?mm ?rom) =>
assert (JOIN : forall a4x a5x, evt asegs (AJ5e A4L HIx A T md) (MS (bvmap_set 14 a4x (bvmap_set 15 a5x R)) FF (Z_to_bv 64 0x97af4) fcc None mm rom)) end.
2:{ unstash Hv. destruct Hv as [-> | [Hv8 Hvlt]].
- step. rewrite ?sxb_zero. step. if_false. apply JOIN.
- step. rewrite (sxb_small v) by lia. step. if_truex.
step.
unstash SBhi. rewrite (unsigned_lit (sb + co + 1)) by lia. rewrite (land7_mod8 (sb + co + 1)) by lia.
pose proof (Z.mod_pos_bound (sb + co + 1) 8 ltac:(lia)) as R8. remember ((sb + co + 1) mod 8) as r8 eqn:Er8 in *.
step.
if_truex. apply JOIN. }
intros a4x a5x. clear SHP.

unstash REST. unstash STR. unstash HW. unstash Hc'.
lazymatch goal with MUc : munch _ m ?mc |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (payload_privateA HIx _ _ _ _ _ _ _ ts0 _ _ _ _ _ _ _ STC (proj1 REST) STR PLEN (or_intror PL) MUc (pe_wtfA_private _ _ q pbs _ HW)) as STRc end.
cbn [pf_sb] in STRc.
pose proof (payload_byteA _ _ _ _ _ STRc Hc' ltac:(lia)) as RDC. replace (sb + (co + 1)) with (sb + co + 1) in RDC by lia.
stash REST. stash STR. stash HW. clear STRc.
step.
change (zxb c') with (Z_to_bv 64 (bv_unsigned c')). clear RDC.
unstash DFt. unstash LE1.
step.
step.
replace (le1 (Z_to_bv 64 (bv_unsigned c'))) with [c'] by (rewrite <- LE1; reflexivity). mem_after_store.
stash DFt.
step.
step.
norm_w32.
step.
step.
unstash REST. unstash HW. unstash INV0. unstash FR0. unstash PBK.
destruct (Z.eq_dec (bv_unsigned c') 10) as [E42 | N42'].
- if_falsex. step.
replace (sb + co + 1) with (sb + (co + 1)) by lia.
unstash Kstar.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, FFc : rw_cells asegs mc Ff _ |- _ =>
assert (FRc : pe_frameA asegs mc (PEF tk oldl newl len lenr sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) c' nb pj sv)
by (eapply (pe_frameA_scan HIx) with (ts := ts0); [exact STC | exact (proj1 REST) | exact FR0 | exact MUc | exact WMc | exact FFc]);
evt_done5;
destruct (PE_INV_A_tokw HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m mc md A B ts0
cb nb pj sv errv _ (co + 1) (TS isd stpos (Z_to_bv 64 (co + 1)) err ucs high quote) c' nb STC INV0 MUc WMc MIc HW TOKc FRc
ltac:(cbn [pf_len]; lia) eq_refl) as [INV1 PBK1];
eapply (Kstar mc (co + 1) c'); [lia | exact Hc' | exact E42 | exact INV1 | exact (PBK1 co0 PBK)]
end end.
- if_truex.
replace (sb + co + 1) with (sb + (co + 1)) by lia. replace (co + 1 - co0 + 1) with (co + 1 + 1 - co0) by lia.
unstash Kstar. unstash Kout. unstash Kerr16. unstash IH. unstash BK.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, FFc : rw_cells asegs mc Ff _ |- _ =>
assert (FRc : pe_frameA asegs mc (PEF tk oldl newl len lenr sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) c' nb pj sv)
by (eapply (pe_frameA_scan HIx) with (ts := ts0); [exact STC | exact (proj1 REST) | exact FR0 | exact MUc | exact WMc | exact FFc]);
evt_done5;
destruct (PE_INV_A_tokw HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m mc md A B ts0
cb nb pj sv errv _ (co + 1) (TS isd stpos (Z_to_bv 64 (co + 1)) err ucs high quote) c' nb STC INV0 MUc WMc MIc HW TOKc FRc
ltac:(cbn [pf_len]; lia) eq_refl) as [INV1 PBK1];
eapply (IH (PEF tk oldl newl len lenr sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo mc md A B
(TST depth levels (co + 1) pb pbs (TS isd stpos (Z_to_bv 64 (co + 1)) err ucs high quote) obj objs objbs) l co0 c' nb pj sv errv T kB);
[ exact STC | exact BSL | reflexivity | exact INV1 | exact (PBK1 co0 PBK) | exact (BOK_set_x _ _ ts0 B kB (co + 1) _ ltac:(cbn [t_co ts0]; lia) BK) | exact CSTR | exact Hl | exact Hst
| cbn [t_co]; lia | cbn [t_co pf_len]; lia | exact Hc' | exact N42' | cbn [t_co pf_len]; lia
| cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_sb pf_len pf_tk pf_lenr pa_F ts_set_co];
intros; eapply Kstar; [cbn [pf_len] in *; lia | eassumption | assumption | eassumption | eassumption]
| cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_sb pf_len pf_tk pf_lenr pa_F ts_set_x ts_pbs];
intros; lazymatch goal with H : PE_INV_A _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => unfold ts_pbs, ts_set_x, ts_set_co in H; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in H end; eapply Kout; [| eassumption..]; cbn [pf_len t_co] in *; lia
| cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_sb pf_len pf_tk pf_lenr pa_F ts_set_x ts_pbs];
intros; lazymatch goal with H : PE_INV_A _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => unfold ts_pbs, ts_set_x, ts_set_co in H; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in H end; eapply Kerr16; [| eassumption..]; cbn [pf_len t_co] in *; lia ]
end end.
Qed.

Lemma seg_ceol_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (nB : nat)
(gp t0 a5 a7 s3 s6 s7 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa -> pf_fl pf = 0 ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
PBOK m ts 0 -> BOK pf pa ts B (S nB) ->
CSTR_OK pf payload ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_comment_eol ->
t_co ts < pf_len pf -> nth_error payload (Z.to_nat (t_co ts)) = Some cb ->

(forall m' md' A' B' pbs' errv' co' cb' gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc',
t_co ts <= co' < pf_len pf -> nth_error payload (Z.to_nat co') = Some cb' -> bv_unsigned cb' = 10 ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B'
(ts_lvl (ts_pbs (ts_set_co ts co') pbs') (TL ST_eatws (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) cb' nb pj sv errv' ->
PBOK m' (ts_lvl (ts_pbs (ts_set_co ts co') pbs') (TL ST_eatws (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) 1 ->
BOK pf pa (ts_lvl (ts_pbs (ts_set_co ts co') pbs') (TL ST_eatws (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) B' nB ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msA asegs pf pa APE_BREAK co' gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' (Z_to_bv 64 2) s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' m')) ->

(forall m' md' A' B' pbs' (e : word) co' cb' errv' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc',
t_co ts < co' <= pf_len pf ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B'
(ts_pbs (ts_set_x ts co' (TS (ts_isd (t_x ts)) (ts_stpos (t_x ts)) (Z_to_bv 64 co') e (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))) pbs') cb' nb pj sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msO asegs pf pa APE_OUT gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' m')) ->

(forall m' md' A' B' pbs' (e : word) co' cb' errv' gp' t0' t1' t2' a0' a1' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc',
t_co ts < co' <= pf_len pf ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B'
(ts_pbs (ts_set_x ts co' (TS (ts_isd (t_x ts)) (ts_stpos (t_x ts)) (Z_to_bv 64 co') e (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))) pbs') cb' nb pj sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msO asegs pf pa APE_ERRMEM2 gp' t0' t1' t2' a0' a1' (Z_to_bv 64 (pf_tk pf + 36)) a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' m')) ->

(forall m' md' A' B' errv' co' cb' x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc',
t_co ts <= co' < pf_len pf ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' (ts_set_co ts co') cb' nb pj sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msX asegs pf pa APE_ERR3 x1' gp' t0' t1' t2' (Z_to_bv 64 16) a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' m')) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa (pe_jtA ST_comment_eol) (t_co ts) gp t0 (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) (Z_to_bv 64 (tl_st l)) (Z_to_bv 64 0) (Z_to_bv 64 (q / 8 + 4 * Z.of_nat (t_depth ts) + A_SB)) (Z_to_bv 64 0) a5 (Z_to_bv 64 APE_JTAB) a7 s3 (Z_to_bv 64 q) s6 s7 (Z_to_bv 64 (Z.of_nat (t_depth ts))) s9 s11 t3 t4 t5 t6 F fc m).
Proof.
intros until fc. intros STC BSL FL0 INV PBK BK CSTR Hl Hst Hco Hc Kbreak Kout KerrF KerrS. pose proof INV as INV0.
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
destruct INV as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof REST as (HP & _).
pose proof (bv_unsigned_in_range 8 cb) as CBR; unfold bv_modulus in CBR; cbn in CBR.
revert INV0 PBK BK Hl Kbreak Kout KerrF KerrS.
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *. subst fl.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
intros INV0 PBK BK Hl Kbreak Kout KerrF KerrS.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
unfold pe_frameA in FR. destruct FR as (SLOTS & _ & _ & FF & _). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS. unfold ff_cellsA in FF.
unfold pe_msA. cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in SLOTS, FF |- *.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd 0) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 4 HP INtk ltac:(lia)) as SHT4.
replace (tk / 8 + 4 + A_SB) with (tk / 8 + 2147450884) in SHT4 by (unfold A_SB; lia).
unfold APE_JTAB. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
stash Himg_t. stash INV0. stash PBK. stash BK. stash Kbreak. stash Kout. stash KerrF. stash KerrS. clear PB TSK REST.
reenterA asegs A4L HIx asegs_wx HP. rewrite Hst. unfold ST_comment_eol. cbn [pe_jtA].
step. step.
change (zxb cb) with (Z_to_bv 64 (bv_unsigned cb)).
step.
step.
step.
unstash INV0. unstash PBK. unstash BK. unstash Kbreak. unstash Kout. unstash KerrF. unstash KerrS.
assert (PBK0 : PBOKat m ts0 co) by (eapply PBOKat_weaken; [| exact PBK]; cbn [t_co ts0]; lia).

assert (STAR : forall m' co' cb' a0' a1' a2' a3' a4' a5' a6',
co <= co' < len -> nth_error payload (Z.to_nat co') = Some cb' -> bv_unsigned cb' = 10 ->
PE_INV_A HIx GA (PEF tk oldl newl len lenr sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m' md A B (ts_set_co ts0 co') cb' nb pj sv errv ->
PBOKat m' (ts_set_co ts0 co') co ->
AJ5 A4L HIx A T md
(pe_msO asegs (PEF tk oldl newl len lenr sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) APE_CEOL_NL gp t0 (Z_to_bv 64 lenr) (Z_to_bv 64 (tk + 32)) a0' a1' a2' a3' a4' a5' a6' a7 (Z_to_bv 64 (sb + co')) (Z_to_bv 64 (sb + co)) (Z_to_bv 64 q) s6 s7 (Z_to_bv 64 (Z.of_nat depth)) s9 s11 t3 t4 t5 t6 F fc m')).
{ intros m' co' cb' a0' a1' a2' a3' a4' a5' a6' R' Hc' E42' INV' PBK'.
eapply (ceol_nl_A (PEF tk oldl newl len lenr sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m' md A B (ts_set_co ts0 co') l co cb' nb pj sv errv T nB);
[exact STC | exact BSL | exact INV' | exact PBK' | exact (BOK_set_co _ _ ts0 B (S nB) co' ltac:(cbn [t_co ts0]; lia) BK) | exact Hl | exact Hst | cbn [t_co ts_set_co]; lia | cbn [t_co ts_set_co pf_len]; lia | |].
- intros m2 md2 A2 B2 pbs2 errv2. intros until fc'. intros I2 P2 K2 FS2 FRM2.
eapply (Kbreak m2 md2 A2 B2 pbs2 errv2 co' cb'); [cbn [t_co pf_len]; lia | exact Hc' | exact E42' | exact I2 | exact P2 | exact K2 | exact FS2 | exact FRM2].
- intros m2 md2 A2 B2 errv2. intros until fc'. intros I2 FS2 FRM2.
eapply (KerrS m2 md2 A2 B2 errv2 co' cb'); [cbn [t_co pf_len]; lia | exact I2 | exact FS2 | exact FRM2]. }
destruct (Z.eq_dec (bv_unsigned cb) 10) as [E42 | N42].
- if_falsex.
evt_done5.
unfold pe_msO, APE_CEOL_NL in STAR. cbn [pf_tk pf_spf pf_sb pf_lenr pa_sp0 pa_F] in STAR. unfold shA in STAR. unfold A_TP, A_SB in STAR. a4l. unfold SB2 in STAR.
eapply (STAR m co cb); [lia | exact Hc | exact E42 | exact INV0 | exact PBK0].
- if_truex.
step.
do 3 step.
evt_done5.
replace (Z_to_bv 64 1) with (Z_to_bv 64 (co + 1 - co)) by (f_equal; lia).
eapply (ceol_latch_A (Z.to_nat (len - co)) (PEF tk oldl newl len lenr sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m md A B ts0 l co cb nb pj sv errv T (S nB));
[ exact STC | exact BSL | reflexivity | exact INV0 | exact PBK0 | exact BK | exact CSTR | exact Hl | exact Hst | cbn [t_co ts0]; lia | exact Hco | exact Hc | exact N42 | cbn [t_co ts0 pf_len]; lia | | | ].
+ intros m' co' cb' a0' a1' a2' a4' a5' a6' R' Hc' E42' INV' PBK'.
unfold pe_msO, APE_CEOL_NL in STAR |- *. eapply (STAR m' co' cb'); [cbn [t_co ts0 pf_len] in R'; lia | exact Hc' | exact E42' | exact INV' | exact PBK'].
+ intros m' md' A' B' pbs' e co' cb' errv'. intros until fc'. intros R' I2 FS2 FRM2.
eapply (Kout m' md' A' B' pbs' e co' cb' errv'); [exact R' | exact I2 | exact FS2 | exact FRM2].
+ intros m' md' A' B' pbs' e co' cb' errv'. intros until fc'. intros R' I2 FS2 FRM2.
eapply (KerrF m' md' A' B' pbs' e co' cb' errv'); [exact R' | exact I2 | exact FS2 | exact FRM2].
Qed.

End PeSCeolA.
End RC__1.
End Mq0.

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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qdyh.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QIsM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QIsM.Mq2.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEUF. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdGy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdGy.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QMmN.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QMmN.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition APE_CEOL_NL : Z := 0x961ac.
Definition APE_CEOL_LATCH : Z := 0x96a44.
Definition APE_CEOL_FLUSH : Z := 0x98874.
Definition APE_CEOL_EOF : Z := 0x985ac.

Section PeSCeolA.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_outside : forall m m' W, GA m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= hl_img_lo A4H \/ hl_img_hi A4H <= fst iv) W -> GA m'.
Hypothesis GA_pres : forall LB SP m m', heap_pres A4H LB SP m m' -> GA m -> GA m'.
Hypothesis MAPP : memappend_A_stmt2 HIx.

Lemma ceol_flush_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (co0 : Z)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kB : nat)
(x1 gp t0 t1 t2 a0 a1 a3 a4 a5 a6 a7 s3 s5 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
PBOKat m ts co0 -> BOK pf pa ts B kB ->
0 <= co0 <= t_co ts -> co0 < pf_len pf ->
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
(pe_msS pf pa APE_CEOL_FLUSH x1 gp t0 t1 t2 a0 a1 (Z_to_bv 64 (t_co ts - co0)) a3 a4 a5 a6 a7 s3 s5 s10 (Z_to_bv 64 (pf_sb pf + co0)) t3 t4 t5 t6 F fc m).
Proof.
intros until fc. intros STC BSL INV PBK BK Hco0 Hco0l Kout Kerr16. pose proof INV as INV0.
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
unfold pe_msS, pe_msO in *.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 1 HP INtk ltac:(lia)) as SHT1.
replace (tk / 8 + 1 + A_SB) with (tk / 8 + 2147450881) in SHT1 by (unfold A_SB; lia).
unfold APE_CEOL_FLUSH, APE_OUT, APE_ERRMEM in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
clear PB TSK REST.
reenterA asegs A4L HIx asegs_wx HP.
step.
asan_chkA.
step. step. step.
evt_done5.
eapply (pe_memappend_p HIx GA GA_pres MAPP (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m md A B ts0 cb nb pj sv errv T co0 (co - co0));
[exact STC | exact BSL | exact INV0 | exact PBK | lia | lia | cbn [t_co ts0]; lia | cbn [pf_len]; lia | cbn [pf_len]; lia | exact BK | rewrite unsigned_lit by lia; reflexivity |].
intros m2 md2 A2 B2 pbs2 errv2 r w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 F2 fc2 INV2 OUT2 FS2 FRM2.
cbn [pf_spf] in *. unfold A_TP in *.
clear TOK SLOTS SHT1 Htal Htlo Hthi Himg_t INtk HP INV0 PBK BK.
pose proof INV2 as [CORE2 REST2]. destruct CORE2 as (_ & _ & _ & _ & _ & _ & _ & _ & FR2). pose proof (proj1 REST2) as HP.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 (ts_pbs ts0 pbs2))) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 4 HP INtk ltac:(lia)) as SHT4.
replace (tk / 8 + 4 + A_SB) with (tk / 8 + 2147450884) in SHT4 by (unfold A_SB; lia).
pose proof FR2 as (SLOTS & _). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS. cbn [pf_tk pf_spf pf_lenr pa_F pa_sp0 pa_oldloc pa_newloc] in SLOTS. unfold shA in SLOTS. a4l. unfold SB2, SB4, SB7, SB8 in SLOTS.
clear REST2 FR2.
reenterA asegs A4L HIx asegs_wx HP.
destruct OUT2 as [(-> & _ & _) | [-> Epbs2]].
- do 5 step.
if_truex.
evt_done5.
eapply (Kout m2 md2 A2 B2 pbs2 errv2); [exact INV2 | exact FS2 | exact FRM2].
- replace (Z_to_bv 64 (2^64 - 1)) with (Z_to_bv 64 (-1)) by (apply bv_eq; vm_compute; reflexivity).
do 5 step.
if_false.
step.
asan_rechkA.
evt_done5.
eapply (Kerr16 m2 md2 A2 B2 pbs2 errv2); [exact INV2 | exact FS2 | exact FRM2].
Qed.

Lemma ceol_eof_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (co0 : Z)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kB : nat)
(x1 gp t0 t1 t2 a0 a1 a3 a4 a5 a6 a7 s3 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
PBOKat m ts co0 -> BOK pf pa ts B kB ->
t_co ts = pf_len pf -> 0 <= co0 < pf_len pf ->
(forall m' md' A' B' pbs' (e : word) errv' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' s11' t4' t6' F' fc',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' (ts_pbs (ts_set_x ts (t_co ts) (tx_err (t_x ts) e)) pbs') cb nb pj sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msO asegs pf pa APE_OUT x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' (Z_to_bv 64 (pf_tk pf + 56)) s11' t4' t6' F' fc' m')) ->
(forall m' md' A' B' pbs' (e : word) errv' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' s11' t4' t6' F' fc',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' (ts_pbs (ts_set_x ts (t_co ts) (tx_err (t_x ts) e)) pbs') cb nb pj sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msO asegs pf pa APE_ERRMEM x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' (Z_to_bv 64 (pf_tk pf + 56)) s11' t4' t6' F' fc' m')) ->
AJ5 A4L HIx A T md
(pe_msS pf pa APE_CEOL_EOF x1 gp t0 t1 t2 a0 a1 (Z_to_bv 64 (pf_len pf - co0)) a3 a4 a5 a6 a7 s3 (Z_to_bv 64 (Z.of_nat (t_depth ts))) (Z_to_bv 64 q)
(Z_to_bv 64 (pf_sb pf + co0)) t3 t4 t5 t6 F fc m).
Proof.
intros until fc. intros STC BSL INV PBK BK Heof Hco0 Kout Kerr16. pose proof INV as INV0.
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
destruct INV as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof REST as (HP & LV & _).
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
subst co.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
unfold pe_frameA in FR. destruct FR as (SLOTS & _). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS.
unfold pe_msS, pe_msO in *.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
set (ts0 := TST depth levels len pb pbs (TS isd stpos (Z_to_bv 64 len) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * mxd) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t.
blk_factsA A4L HIx HP q (32 * mxd) Hqal Hqlo Hqhi Himg_q.
pose proof (q_ne_tkA HIx _ _ _ _ _ _ _ _ _ _ HP) as Hqtk. cbn [pf_tk] in Hqtk.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ tk 72 q (32 * mxd) HP (in_or_app _ LM _ (or_introl INtk)) (in_or_app _ LM _ (or_introl INq)) ltac:(congruence)) as Hdtq.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 4 HP INtk ltac:(lia)) as SHT4.
replace (tk / 8 + 4 + A_SB) with (tk / 8 + 2147450884) in SHT4 by (unfold A_SB; lia).
pose proof (stack_shadowA HIx _ _ _ _ _ _ _ q mxd 0 0 HP INq ltac:(lia) ltac:(lia)) as SHQ0.
replace (q / 8 + 4 * 0 + 0 + A_SB) with (q / 8 + 2147450880) in SHQ0 by (unfold A_SB; lia).
assert (Hq8 : q mod 8 = 0) by (clear - Hqal; Z.div_mod_to_equations; lia).

destruct levels as [|l0 levels']; [cbn in LEN32; lia|].
pose proof (LV 0%nat l0 eq_refl) as (ST26 & SS26 & _).
pose proof (TSK 0%nat l0 eq_refl) as L0. unfold srec_cells in L0. replace (q + 32 * Z.of_nat 0) with q in L0 by lia.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(tk, tk + 72)] m) as MU.
unfold APE_CEOL_EOF, APE_CEOL_FLUSH, APE_OUT, APE_ERRMEM in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
stash Himg_t. stash Himg_q. clear PB TSK REST LV.
reenterA asegs A4L HIx asegs_wx HP.

lazymatch goal with |- evt _ _ (MS ?R ?FF _ ?fcc None ?mm ?rom) =>
assert (TAILE : forall e a1v, e = 0 \/ e = 1 ->
evt asegs (AJ5e A4L HIx A T md) (MS (bvmap_set 11 a1v (bvmap_set 10 (Z_to_bv 64 e) R)) FF (Z_to_bv 64 0x98864) fcc None mm rom)) end.
{ intros e a1v He.
step.
asan_rechkA.
stepz.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _ |- _ =>
evt_done5;
destruct (PE_INV_A_tokw1 HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m mc md A B ts0
cb nb pj sv errv len (tx_err (t_x ts0) (Z_to_bv 64 e)) STC INV0 MUc WMc MIc TOKc ltac:(cbn [pf_len]; lia) eq_refl) as [INVe PBKe];
eapply (ceol_flush_A (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo mc md A B
(ts_set_x ts0 len (tx_err (t_x ts0) (Z_to_bv 64 e))) co0 cb nb pj sv errv T kB);
[exact STC | exact BSL | exact INVe | exact (PBKe co0 PBK) | exact (BOK_set_x _ _ ts0 B kB len _ ltac:(cbn [t_co ts0]; lia) BK) | cbn [t_co ts_set_x]; lia | cbn [pf_len]; lia
| intros; eapply (Kout _ _ _ _ _ (Z_to_bv 64 e)); eassumption
| intros; eapply (Kerr16 _ _ _ _ _ (Z_to_bv 64 e)); eassumption]
end end. }
step.
destruct (Nat.eq_dec depth 0) as [D0 | Dn].
- subst depth. if_false.
asan_chkA.
step.
norm_sx32.
destruct (Z.eq_dec (tl_st l0) 0) as [S0 | Sn].
+ rewrite S0. step.
if_false.
step.
asan_chkA.
step.
norm_sx32.
step.
destruct (Z.eq_dec (tl_ss l0) 2) as [F2 | Fn].
* rewrite F2. step.
if_false.
step.
step.
apply (TAILE 0 _). left; reflexivity.
* step.
if_truex.
step.
step.
apply (TAILE 1 _). right; reflexivity.
+ step.
if_truex.
step.
step.
apply (TAILE 1 _). right; reflexivity.
- if_truex.
step.
step.
apply (TAILE 1 _). right; reflexivity.
Qed.

Lemma ceol_nl_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel) (co0 : Z)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (nB : nat)
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
PBOKat m ts co0 -> BOK pf pa ts B (S nB) ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_comment_eol ->
0 <= co0 <= t_co ts -> t_co ts < pf_len pf ->

(forall m' md' A' B' pbs' errv' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' F' fc',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B'
(ts_lvl (ts_pbs ts pbs') (TL ST_eatws (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) cb nb pj sv errv' ->
PBOK m' (ts_lvl (ts_pbs ts pbs') (TL ST_eatws (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) 1 ->
BOK pf pa (ts_lvl (ts_pbs ts pbs') (TL ST_eatws (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) B' nB ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msA asegs pf pa APE_BREAK (t_co ts) gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5'
(Z_to_bv 64 (pf_tk pf + 56)) (Z_to_bv 64 (pa_F pa + 64)) F' fc' m')) ->

(forall m' md' A' B' errv' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' s5' t3' t4' t5' t6' F' fc',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' ts cb nb pj sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(Q1Y6.Mq2.pe_msE pf pa APE_ERRMEMC x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7'
s3' (Z_to_bv 64 (pf_tk pf + 20)) s5' (Z_to_bv 64 (pf_tk pf + 36)) (Z_to_bv 64 (pf_tk pf + 32)) (Z_to_bv 64 (pa_F pa))
(Z_to_bv 64 (pf_tk pf + 56)) (Z_to_bv 64 (pf_sb pf + co0)) t3' t4' t5' t6' F' fc' m')) ->
AJ5 A4L HIx A T md
(pe_msS pf pa APE_CEOL_NL x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (pf_sb pf + t_co ts)) s5 s10 (Z_to_bv 64 (pf_sb pf + co0)) t3 t4 t5 t6 F fc m).
Proof.
intros until fc. intros STC BSL INV PBK BK Hl Hst Hco0 Hco Kbreak Kerr16. pose proof INV as INV0.
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
unfold pe_msS, pe_msA, Q1Y6.Mq2.pe_msE in *.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 1 HP INtk ltac:(lia)) as SHT1.
replace (tk / 8 + 1 + A_SB) with (tk / 8 + 2147450881) in SHT1 by (unfold A_SB; lia).
unfold APE_CEOL_NL, APE_BREAK, APE_ERRMEMC in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
set (n := co - co0) in *.
clear PB TSK REST.
reenterA asegs A4L HIx asegs_wx HP.
step.
asan_chkA.
step. step.
norm_w32. replace (sb + co - (sb + co0)) with n by (unfold n; lia).
step. step.
evt_done5.
eapply (pe_memappend_p HIx GA GA_pres MAPP (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m md A B ts0 cb nb pj sv errv T co0 n);
[exact STC | exact BSL | exact INV0 | exact PBK | lia | unfold n; lia | unfold n; cbn [t_co ts0]; lia | unfold n; cbn [pf_len]; lia | cbn [pf_len]; lia | exact BK | rewrite unsigned_lit by lia; reflexivity |].
intros m2 md2 A2 B2 pbs2 errv2 r w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 F2 fc2 INV2 OUT2 FS2 FRM2.
cbn [pf_spf] in *. unfold A_TP in *.

clear TOK SLOTS SHT1 Htal Htlo Hthi Himg_t INtk HP INV0 PBK BK.
set (ts2 := ts_pbs ts0 pbs2) in *.
pose proof INV2 as INV2'. destruct INV2' as [CORE2 REST2].
destruct CORE2 as (_ & _ & _ & _ & TOK & _ & _ & TSK & FR).
pose proof REST2 as (HP & LV & _).
unfold ts2, ts_pbs, ts0 in TOK, TSK, LV. cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_tk pf_mxd pf_fl] in TOK, TSK, LV.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
unfold pe_frameA in FR. destruct FR as (SLOTS & _ & _ & FF & _). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS. unfold ff_cellsA in FF.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in SLOTS, FF.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts2)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * mxd) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts2)) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t.
blk_factsA A4L HIx HP q (32 * mxd) Hqal Hqlo Hqhi Himg_q.
pose proof (q_ne_tkA HIx _ _ _ _ _ _ _ _ _ _ HP) as Hqtk. cbn [pf_tk] in Hqtk.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ tk 72 q (32 * mxd) HP (in_or_app _ LM _ (or_introl INtk)) (in_or_app _ LM _ (or_introl INq)) ltac:(congruence)) as Hdtq.
pose proof (tok_shadowA HIx _ _ _ _ _ _ _ _ HP INtk) as SHT.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs m2) as WM.
pose proof (LV depth l Hl) as LVd. pose proof LVd as (ST26 & SS26 & _ & Md).
rewrite Nat.ltb_irrefl, Nat.eqb_refl in Md. destruct Md as (c0 & hn0 & Hmode & CLS0 & NM0).
pose proof (TSK depth l Hl) as Ld. remember (q + 32 * Z.of_nat depth) as bse eqn:Hbse in Ld. unfold srec_cells in Ld.
assert (HbseR : q <= bse /\ bse + 32 <= q + (32 * mxd)) by (subst bse; lia).
pose proof (stack_shadowA HIx _ _ _ _ _ _ _ q mxd (Z.of_nat depth) 0 HP INq ltac:(lia) ltac:(lia)) as SHQ.
replace (q / 8 + 4 * Z.of_nat depth + 0 + A_SB) with (q / 8 + 4 * Z.of_nat depth + A_SB) in SHQ by lia.
assert (Hb8 : bse mod 8 = 0) by (subst bse; clear - Hqal; Z.div_mod_to_equations; lia).
assert (SHQ4 : ro_cells asegs m2 (bse / 8 + A_SB) [C1 (Z_to_bv 8 0)]).
{ replace (bse / 8) with (q / 8 + 4 * Z.of_nat depth) by (subst bse; rewrite div8_add_mul32 by lia; lia). exact SHQ. }
pose proof (munch_refl [(bse, bse + 32)] m2) as MU.
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
stash Himg_t. stash Himg_q. clear LV TSK.
reenterA asegs A4L HIx asegs_wx HP.
destruct OUT2 as [(-> & PBK2 & BK2) | [-> Epbs2]].
2:{ replace (Z_to_bv 64 (2^64 - 1)) with (Z_to_bv 64 (-1)) by (apply bv_eq; vm_compute; reflexivity).
step. step.
if_false.
step.
step.
asan_rechkA.
evt_done5.
eapply (Kerr16 m2 md2 A2 B2 errv2); [| exact FS2 | exact FRM2].
subst pbs2. exact INV2. }
step. step.
if_truex.
step.
asan_rechkA.
step.
asan_rechkM 6.
step.
norm_sx32.
step.
rewrite (unsigned_lit (Z.of_nat depth)) by lia.
rewrite Z.shiftl_mul_pow2 by lia.
change (2 ^ 5) with 32.
step.
replace (q + Z.of_nat depth * 32) with bse by lia.
asan_chkA.
stepz.
do 3 step.
step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m2 mc, WMc : wmono asegs m2 mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, Lc : rw_cells asegs mc bse _ |- _ =>
evt_done5; subst bse;
destruct (PE_INV_A_lvl_write HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m2 mc md2 A2 B2 ts2
cb nb pj sv errv2 l ST_eatws (tl_ss l) c0 hn0 c0 STC INV2 Hl MUc WMc MIc TOKc Lc Hmode
ltac:(rewrite <- Hmode; apply QIsM.Mq2.lvl_mode_ws_same; [rewrite Hst; reflexivity | reflexivity])
ltac:(unfold ST_eatws; lia) SS26 (or_introl eq_refl) ltac:(rewrite Hst; reflexivity)) as [INV3 PBK3];
eapply (Kbreak mc md2 A2 B2 pbs2 errv2);
[exact INV3
| apply PBK3; unfold PBOK; eapply PBOKat_weaken; [| exact PBK2]; unfold n, ts2, ts_pbs, ts0; cbn [t_co]; lia
| exact (BOK_lvl_restate _ _ ts2 B2 nB l ST_eatws (tl_ss l) Hl (lvl_closed_keep l ST_eatws _ _ _ _ _ eq_refl) (BOK_weaken _ _ _ _ _ nB (Nat.le_succ_diag_r nB) BK2))
| exact FS2 | exact FRM2]
end end.
Qed.

Ltac frameA_now mc :=
unfold pe_frameA, pe_slotsA, pe_savedA_cells, ff_cellsA, ffsh_cells, FSH0; cbn [map pf_tk pf_spf pf_lenr pa_F pa_sp0 pa_oldloc pa_newloc]; unfold shA, A_SB;
split; [| split; [| split; [| split]]];
match goal with H : rw_cells asegs mc ?a _ |- rw_cells asegs mc ?a _ => exact H end.

Lemma ceol_latch_A :
forall (n : nat) (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel) (co0 : Z)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kB : nat)
(gp t0 t1 t2 a3 a5 a6 a7 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa -> pf_fl pf = 0 ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
PBOKat m ts co0 -> BOK pf pa ts B kB ->
CSTR_OK pf payload ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_comment_eol ->
0 <= co0 <= t_co ts -> t_co ts < pf_len pf -> nth_error payload (Z.to_nat (t_co ts)) = Some cb -> bv_unsigned cb <> 10 ->
(pf_len pf - t_co ts <= Z.of_nat n) ->

(forall m' co' cb' x1' a0' a1' a2' a3' a4' a5',
t_co ts < co' < pf_len pf -> nth_error payload (Z.to_nat co') = Some cb' -> bv_unsigned cb' = 10 ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md A B (ts_set_co ts co') cb' nb pj sv errv ->
PBOKat m' (ts_set_co ts co') co0 ->
AJ5 A4L HIx A T md
(pe_msS pf pa APE_CEOL_NL x1' gp t0 t1 t2 a0' a1' a2' a3' a4' a5' a6 a7 (Z_to_bv 64 (pf_sb pf + co')) (Z_to_bv 64 (Z.of_nat (t_depth ts))) (Z_to_bv 64 q)
(Z_to_bv 64 (pf_sb pf + co0)) (Z_to_bv 64 (pf_tk pf + 64)) (Z_to_bv 64 (pa_F pa + 64)) (Z_to_bv 64 (pf_tk pf / 8 + SB8)) (Z_to_bv 64 (pf_lenr pf)) F fc m')) ->

(forall m' md' A' B' pbs' (e : word) co' cb' errv' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' s11' t4' t6' F' fc',
t_co ts < co' <= pf_len pf ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B'
(ts_pbs (ts_set_x ts co' (TS (ts_isd (t_x ts)) (ts_stpos (t_x ts)) (Z_to_bv 64 co') e (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))) pbs') cb' nb pj sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msO asegs pf pa APE_OUT x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' (Z_to_bv 64 (pf_tk pf + 56)) s11' t4' t6' F' fc' m')) ->

(forall m' md' A' B' pbs' (e : word) co' cb' errv' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' s11' t4' t6' F' fc',
t_co ts < co' <= pf_len pf ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B'
(ts_pbs (ts_set_x ts co' (TS (ts_isd (t_x ts)) (ts_stpos (t_x ts)) (Z_to_bv 64 co') e (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))) pbs') cb' nb pj sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msO asegs pf pa APE_ERRMEM x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' (Z_to_bv 64 (pf_tk pf + 56)) s11' t4' t6' F' fc' m')) ->
AJ5 A4L HIx A T md
(pe_msS pf pa APE_CEOL_LATCH (Z_to_bv 64 (pf_tk pf / 8 + SB4)) gp t0 t1 t2
(Z_to_bv 64 (pf_sb pf + t_co ts + 1)) (Z_to_bv 64 (t_co ts + 1)) (Z_to_bv 64 (t_co ts + 1 - co0)) a3 (Z_to_bv 64 (bv_unsigned cb)) a5 a6 a7
(Z_to_bv 64 (pf_sb pf + t_co ts)) (Z_to_bv 64 (Z.of_nat (t_depth ts))) (Z_to_bv 64 q) (Z_to_bv 64 (pf_sb pf + co0))
(Z_to_bv 64 (pf_tk pf + 64)) (Z_to_bv 64 (pa_F pa + 64)) (Z_to_bv 64 (pf_tk pf / 8 + SB8)) (Z_to_bv 64 (pf_lenr pf)) F fc m).
Proof.
induction n as [|n IH]; intros until fc; intros STC BSL FL0 INV PBK BK CSTR Hl Hst Hco0 Hco Hc N42 Hn Kstar Kout Kerr16.
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
unfold ts_set_co, ts_set_x, ts_pbs in Kstar, Kout, Kerr16.
cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in Kstar, Kout, Kerr16.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
pose proof FR as FR0. unfold pe_frameA in FR. destruct FR as (SLOTS & GAP & SAVED & FF & FSH). unfold pe_msS, pe_msO in *.
unfold pe_slotsA in SLOTS. cbn zeta in SLOTS. unfold pe_savedA_cells in SAVED. unfold ff_cellsA in FF. unfold ffsh_cells, FSH0 in FSH. cbn [map] in FSH.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd 0) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 4 HP INtk ltac:(lia)) as SHT4.
replace (tk / 8 + 4 + A_SB) with (tk / 8 + 2147450884) in SHT4 by (unfold A_SB; lia).
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 8 HP INtk ltac:(lia)) as SHT8.
replace (tk / 8 + 8 + A_SB) with (tk / 8 + 2147450888) in SHT8 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 4 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (SEP4c & SEP4t & SEP4i). cbn [hl_sb A4L] in SEP4c, SEP4t, SEP4i.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 8 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (SEP8c & SEP8t & SEP8i). cbn [hl_sb A4L] in SEP8c, SEP8t, SEP8i.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs m) as WM.
pose proof (bytes_at_bound _ _ _ _ STR) as SBB.
pose proof alloc_ceiling_range as ACR.
pose proof (bv_unsigned_in_range 8 cb) as CBR; unfold bv_modulus in CBR; cbn in CBR.

assert (INF : In (Ff, 2) ((Ff, 2) :: FRS)) by (left; reflexivity).
assert (INtk' : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd 0) q LB0 ts0 ++ LM)) by (apply in_or_app; left; exact INtk).
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP INF INtk') as DFt. rewrite fr_size_2 in DFt.
assert (GF0' : 0 <= Ff) by lia. assert (GFc' : Ff < alloc_ceiling) by lia.
pose proof (shadow_blk_apart HIx _ _ _ _ _ _ _ _ _ Ff 32 HP INtk' GF0' GFc' ltac:(lia)) as DSt.
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP INF) as DSF. rewrite fr_size_2 in DSF. cbn [hl_sb A4L] in DSF.
destruct SBin as [L00 | PL]; [exfalso; lia|].
unfold APE_CEOL_LATCH, APE_CEOL_NL, APE_CEOL_FLUSH, APE_CEOL_EOF, APE_OUT, APE_ERRMEM in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8, A_SB in *.
pose proof (munch_refl [(tk, tk + 72); (Ff + 64, Ff + 65)] m) as MU.
assert (HW : Forall (pe_wtfA (PEF tk oldl newl len lenr sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl)) [(tk, tk + 72); (Ff + 64, Ff + 65)]).
{ apply Forall_cons; [left; cbn [fst snd pf_tk]; lia |]. apply Forall_cons; [| apply Forall_nil]. right; right; left. cbn [fst snd pa_F]. lia. }
clear LV OBJ HPR.
destruct (Z.eq_dec (bv_unsigned cb) 0) as [E0 | N0].
{
stash PB. stash TSK.
reenterA asegs A4L HIx asegs_wx HP.
asan_rechkA.
step.
step.
if_falsex. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _ |- _ =>
assert (FRc : pe_frameA asegs mc (PEF tk oldl newl len lenr sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) cb nb pj sv) by (frameA_now mc);
evt_done5;
destruct (PE_INV_A_tokw HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m mc md A B ts0
cb nb pj sv errv _ (co + 1) (TS isd stpos (Z_to_bv 64 (co + 1)) err ucs high quote) cb nb STC INV0 MUc WMc MIc HW TOKc FRc
ltac:(cbn [pf_len]; lia) eq_refl) as [INV1 PBK1];
eapply (ceol_flush_A (PEF tk oldl newl len lenr sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo mc md A B
(ts_set_x ts0 (co + 1) (TS isd stpos (Z_to_bv 64 (co + 1)) err ucs high quote)) co0 cb nb pj sv errv T kB);
[exact STC | exact BSL | exact INV1 | exact (PBK1 co0 PBK) | exact (BOK_set_x _ _ ts0 B kB (co + 1) _ ltac:(cbn [t_co ts0]; lia) BK)
| cbn [t_co ts_set_x]; lia | cbn [pf_len]; lia
| intros; eapply (Kout _ _ _ _ _ err (co + 1) cb); [lia | eassumption | eassumption | eassumption]
| intros; eapply (Kerr16 _ _ _ _ _ err (co + 1) cb); [lia | eassumption | eassumption | eassumption]]
end end. }
destruct (peek_cases (PEF tk oldl newl len lenr sb spf pmd mxd 0) payload co cb LENR CSTR (proj1 RR) ltac:(cbn [pf_len pf_mxd]; lia) ltac:(cbn [pf_len pf_mxd]; lia) Hc N0)
as [[Elenr Heof] | [Hne Hmore]]; cbn [pf_len pf_lenr pf_mxd] in *.
{
subst lenr. stash PB. stash TSK.
reenterA asegs A4L HIx asegs_wx HP.
asan_rechkA.
step.
step.
if_truex.
step.
rewrite Heof. if_false. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _ |- _ =>
assert (FRc : pe_frameA asegs mc (PEF tk oldl newl len len sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) cb nb pj sv) by (frameA_now mc);
evt_done5;
destruct (PE_INV_A_tokw HIx GA GA_outside (PEF tk oldl newl len len sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m mc md A B ts0
cb nb pj sv errv _ (co + 1) (TS isd stpos (Z_to_bv 64 (co + 1)) err ucs high quote) cb nb STC INV0 MUc WMc MIc HW TOKc FRc
ltac:(cbn [pf_len]; lia) eq_refl) as [INV1 PBK1];
replace (Z_to_bv 64 (co + 1 - co0)) with (Z_to_bv 64 (len - co0)) by (f_equal; lia);
eapply (ceol_eof_A (PEF tk oldl newl len len sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo mc md A B
(ts_set_x ts0 (co + 1) (TS isd stpos (Z_to_bv 64 (co + 1)) err ucs high quote)) co0 cb nb pj sv errv T kB);
[exact STC | exact BSL | exact INV1 | exact (PBK1 co0 PBK) | exact (BOK_set_x _ _ ts0 B kB (co + 1) _ ltac:(cbn [t_co ts0]; lia) BK)
| cbn [t_co ts_set_x pf_len]; lia | cbn [pf_len]; lia
| intros; eapply (Kout _ _ _ _ _ e (co + 1) cb); [lia | eassumption | eassumption | eassumption]
| intros; eapply (Kerr16 _ _ _ _ _ e (co + 1) cb); [lia | eassumption | eassumption | eassumption]]
end end. }

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
assert (LE1 : le1 (zxb c') = [c']).
{ unfold le1, zxb. cbn [Z_to_le_bytes pf_mxd]. f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 8) with 256%Z. change (bv_modulus 64) with 18446744073709551616%Z. Z.div_mod_to_equations. nia. }

stash PB. stash TSK. stash Hv. stash SLOTS. stash GAP. stash SAVED. stash FSH. stash DSt. stash DSF. stash SHPF.
stash IH. stash Kstar. stash Kout. stash Kerr16. stash INV0. stash REST. stash FR0. stash PBK. stash BK. stash SBc. stash SBhi. stash LE1. stash Hc'. stash Hc. stash STR. stash HW.
reenterA asegs A4L HIx asegs_wx HP.
asan_rechkA.
step.
stash DFt. stash DSPt. clear SEP4c SEP4t SEP4i SEP8c SEP8t SEP8i SHT4.
step.
if_truex.
step.
if_truex.
asan_rechkA.
clear SHT8.
lazymatch goal with TOKc : rw_cells asegs ?mc tk _ |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (tok_flags_byteA mxd 0 mc tk pb (Z.of_nat depth) q (TS isd stpos (Z_to_bv 64 (co + 1)) err ucs high quote) TOKc) as RDF end.
step.
rewrite ?zxb_zero. clear RDF.
step. step. step.
step.
if_true.
step.
sh_norm.

lazymatch goal with |- evt _ _ (MS ?R ?FF _ ?fcc None ?mm ?rom) =>
assert (JOIN : forall a4x a5x, evt asegs (AJ5e A4L HIx A T md) (MS (bvmap_set 14 a4x (bvmap_set 15 a5x R)) FF (Z_to_bv 64 0x96ab8) fcc None mm rom)) end.
2:{ unstash Hv. destruct Hv as [-> | [Hv8 Hvlt]].
- step. rewrite ?sxb_zero. step. if_false. apply JOIN.
- step. rewrite (sxb_small v) by lia. step. if_truex.
step.
unstash SBhi. rewrite (unsigned_lit (sb + co + 1)) by lia. rewrite (land7_mod8 (sb + co + 1)) by lia.
pose proof (Z.mod_pos_bound (sb + co + 1) 8 ltac:(lia)) as R8. remember ((sb + co + 1) mod 8) as r8 eqn:Er8 in *.
step.
if_truex. apply JOIN. }
intros a4x a5x. clear SHP.

unstash REST. unstash STR. unstash HW. unstash Hc'.
lazymatch goal with MUc : munch _ m ?mc |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (payload_privateA HIx _ _ _ _ _ _ _ ts0 _ _ _ _ _ _ _ STC (proj1 REST) STR PLEN (or_intror PL) MUc (pe_wtfA_private _ _ q pbs _ HW)) as STRc end.
cbn [pf_sb] in STRc.
pose proof (payload_byteA _ _ _ _ _ STRc Hc' ltac:(lia)) as RDC. replace (sb + (co + 1)) with (sb + co + 1) in RDC by lia.
stash REST. stash STR. stash HW. clear STRc.
step.
change (zxb c') with (Z_to_bv 64 (bv_unsigned c')). clear RDC.
unstash DFt. unstash LE1.
step.
replace (le1 (Z_to_bv 64 (bv_unsigned c'))) with [c'] by (rewrite <- LE1; reflexivity). mem_after_store.
stash DFt.
step.
norm_w32.
step. step.
step.
norm_w32.
step.
unstash REST. unstash HW. unstash INV0. unstash FR0. unstash PBK.
destruct (Z.eq_dec (bv_unsigned c') 10) as [E42 | N42'].
- if_falsex. step.
replace (sb + co + 1) with (sb + (co + 1)) by lia.
unstash Kstar.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, FFc : rw_cells asegs mc Ff _ |- _ =>
assert (FRc : pe_frameA asegs mc (PEF tk oldl newl len lenr sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) c' nb pj sv)
by (eapply (pe_frameA_scan HIx) with (ts := ts0); [exact STC | exact (proj1 REST) | exact FR0 | exact MUc | exact WMc | exact FFc]);
evt_done5;
destruct (PE_INV_A_tokw HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m mc md A B ts0
cb nb pj sv errv _ (co + 1) (TS isd stpos (Z_to_bv 64 (co + 1)) err ucs high quote) c' nb STC INV0 MUc WMc MIc HW TOKc FRc
ltac:(cbn [pf_len]; lia) eq_refl) as [INV1 PBK1];
eapply (Kstar mc (co + 1) c'); [lia | exact Hc' | exact E42 | exact INV1 | exact (PBK1 co0 PBK)]
end end.
- if_truex.
replace (sb + co + 2) with (sb + (co + 1) + 1) by lia. replace (sb + co + 1) with (sb + (co + 1)) by lia.
replace (Z_to_bv 64 (co + 2)) with (Z_to_bv 64 (co + 1 + 1)) by (f_equal; lia). replace (co + 1 - co0 + 1) with (co + 1 + 1 - co0) by lia.
unstash Kstar. unstash Kout. unstash Kerr16. unstash IH. unstash BK.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, FFc : rw_cells asegs mc Ff _ |- _ =>
assert (FRc : pe_frameA asegs mc (PEF tk oldl newl len lenr sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) c' nb pj sv)
by (eapply (pe_frameA_scan HIx) with (ts := ts0); [exact STC | exact (proj1 REST) | exact FR0 | exact MUc | exact WMc | exact FFc]);
evt_done5;
destruct (PE_INV_A_tokw HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m mc md A B ts0
cb nb pj sv errv _ (co + 1) (TS isd stpos (Z_to_bv 64 (co + 1)) err ucs high quote) c' nb STC INV0 MUc WMc MIc HW TOKc FRc
ltac:(cbn [pf_len]; lia) eq_refl) as [INV1 PBK1];
eapply (IH (PEF tk oldl newl len lenr sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo mc md A B
(TST depth levels (co + 1) pb pbs (TS isd stpos (Z_to_bv 64 (co + 1)) err ucs high quote) obj objs objbs) l co0 c' nb pj sv errv T kB);
[ exact STC | exact BSL | reflexivity | exact INV1 | exact (PBK1 co0 PBK) | exact (BOK_set_x _ _ ts0 B kB (co + 1) _ ltac:(cbn [t_co ts0]; lia) BK) | exact CSTR | exact Hl | exact Hst
| cbn [t_co]; lia | cbn [t_co pf_len]; lia | exact Hc' | exact N42' | cbn [t_co pf_len]; lia
| cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_sb pf_len pf_tk pf_lenr pa_F ts_set_co];
intros; eapply Kstar; [cbn [pf_len] in *; lia | eassumption | assumption | eassumption | eassumption]
| cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_sb pf_len pf_tk pf_lenr pa_F ts_set_x ts_pbs];
intros; lazymatch goal with H : PE_INV_A _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => unfold ts_pbs, ts_set_x, ts_set_co in H; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in H end; eapply Kout; [| eassumption..]; cbn [pf_len t_co] in *; lia
| cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_sb pf_len pf_tk pf_lenr pa_F ts_set_x ts_pbs];
intros; lazymatch goal with H : PE_INV_A _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => unfold ts_pbs, ts_set_x, ts_set_co in H; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in H end; eapply Kerr16; [| eassumption..]; cbn [pf_len t_co] in *; lia ]
end end.
Qed.

Lemma seg_ceol_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (nB : nat)
(gp t0 t1 t2 a3 a5 a6 a7 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa -> pf_fl pf = 0 ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
PBOK m ts 0 -> BOK pf pa ts B (S nB) ->
CSTR_OK pf payload ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_comment_eol ->
t_co ts < pf_len pf -> nth_error payload (Z.to_nat (t_co ts)) = Some cb ->

(forall m' md' A' B' pbs' errv' co' cb' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' F' fc',
t_co ts <= co' < pf_len pf -> nth_error payload (Z.to_nat co') = Some cb' -> bv_unsigned cb' = 10 ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B'
(ts_lvl (ts_pbs (ts_set_co ts co') pbs') (TL ST_eatws (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) cb' nb pj sv errv' ->
PBOK m' (ts_lvl (ts_pbs (ts_set_co ts co') pbs') (TL ST_eatws (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) 1 ->
BOK pf pa (ts_lvl (ts_pbs (ts_set_co ts co') pbs') (TL ST_eatws (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) B' nB ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msA asegs pf pa APE_BREAK co' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5'
(Z_to_bv 64 (pf_tk pf + 56)) (Z_to_bv 64 (pa_F pa + 64)) F' fc' m')) ->

(forall m' md' A' B' pbs' (e : word) co' cb' errv' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' s11' t4' t6' F' fc',
t_co ts < co' <= pf_len pf ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B'
(ts_pbs (ts_set_x ts co' (TS (ts_isd (t_x ts)) (ts_stpos (t_x ts)) (Z_to_bv 64 co') e (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))) pbs') cb' nb pj sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msO asegs pf pa APE_OUT x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' (Z_to_bv 64 (pf_tk pf + 56)) s11' t4' t6' F' fc' m')) ->

(forall m' md' A' B' pbs' (e : word) co' cb' errv' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' s11' t4' t6' F' fc',
t_co ts < co' <= pf_len pf ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B'
(ts_pbs (ts_set_x ts co' (TS (ts_isd (t_x ts)) (ts_stpos (t_x ts)) (Z_to_bv 64 co') e (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))) pbs') cb' nb pj sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msO asegs pf pa APE_ERRMEM x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' (Z_to_bv 64 (pf_tk pf + 56)) s11' t4' t6' F' fc' m')) ->

(forall m' md' A' B' errv' co' cb' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' s5' t3' t4' t5' t6' F' fc',
t_co ts <= co' < pf_len pf ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' (ts_set_co ts co') cb' nb pj sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(Q1Y6.Mq2.pe_msE pf pa APE_ERRMEMC x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7'
s3' (Z_to_bv 64 (pf_tk pf + 20)) s5' (Z_to_bv 64 (pf_tk pf + 36)) (Z_to_bv 64 (pf_tk pf + 32)) (Z_to_bv 64 (pa_F pa))
(Z_to_bv 64 (pf_tk pf + 56)) (Z_to_bv 64 (pf_sb pf + t_co ts)) t3' t4' t5' t6' F' fc' m')) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa (pe_jtA ST_comment_eol) (t_co ts) gp t0 t1 t2
(Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) (Z_to_bv 64 (tl_st l))
(Z_to_bv 64 (q / 8 + 4 * Z.of_nat (t_depth ts) + A_SB)) a3 (Z_to_bv 64 APE_JTAB) a5 a6 a7
(Z_to_bv 64 (Z.of_nat (t_depth ts))) (Z_to_bv 64 q) (Z_to_bv 64 (pa_F pa + 64)) F fc m).
Proof.
intros until fc. intros STC BSL FL0 INV PBK BK CSTR Hl Hst Hco Hc Kbreak Kout KerrF KerrS. pose proof INV as INV0.
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
destruct INV as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof REST as (HP & _).
pose proof (bv_unsigned_in_range 8 cb) as CBR; unfold bv_modulus in CBR; cbn in CBR.
revert INV0 PBK BK Hl Kbreak Kout KerrF KerrS.
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *. subst fl.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
intros INV0 PBK BK Hl Kbreak Kout KerrF KerrS.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
unfold pe_frameA in FR. destruct FR as (SLOTS & _ & _ & FF & _). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS. unfold ff_cellsA in FF.
unfold pe_msA. cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in SLOTS, FF |- *.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd 0) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 4 HP INtk ltac:(lia)) as SHT4.
replace (tk / 8 + 4 + A_SB) with (tk / 8 + 2147450884) in SHT4 by (unfold A_SB; lia).
unfold APE_JTAB. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
stash Himg_t. stash INV0. stash PBK. stash BK. stash Kbreak. stash Kout. stash KerrF. stash KerrS. clear PB TSK REST.
reenterA asegs A4L HIx asegs_wx HP. rewrite Hst. unfold ST_comment_eol. cbn [pe_jtA].
step.
change (zxb cb) with (Z_to_bv 64 (bv_unsigned cb)).
step.
step.
step.
unstash INV0. unstash PBK. unstash BK. unstash Kbreak. unstash Kout. unstash KerrF. unstash KerrS.
assert (PBK0 : PBOKat m ts0 co) by (eapply PBOKat_weaken; [| exact PBK]; cbn [t_co ts0]; lia).

assert (STAR : forall m' co' cb' x1' a0' a1' a2' a3' a4' a5',
co <= co' < len -> nth_error payload (Z.to_nat co') = Some cb' -> bv_unsigned cb' = 10 ->
PE_INV_A HIx GA (PEF tk oldl newl len lenr sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m' md A B (ts_set_co ts0 co') cb' nb pj sv errv ->
PBOKat m' (ts_set_co ts0 co') co ->
AJ5 A4L HIx A T md
(pe_msS (PEF tk oldl newl len lenr sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) APE_CEOL_NL x1' gp t0 t1 t2 a0' a1' a2' a3' a4' a5' a6 a7
(Z_to_bv 64 (sb + co')) (Z_to_bv 64 (Z.of_nat depth)) (Z_to_bv 64 q) (Z_to_bv 64 (sb + co))
(Z_to_bv 64 (tk + 64)) (Z_to_bv 64 (Ff + 64)) (Z_to_bv 64 (tk / 8 + 2147450888)) (Z_to_bv 64 lenr) F fc m')).
{ intros m' co' cb' x1' a0' a1' a2' a3' a4' a5' R' Hc' E42' INV' PBK'.
eapply (ceol_nl_A (PEF tk oldl newl len lenr sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m' md A B (ts_set_co ts0 co') l co cb' nb pj sv errv T nB);
[exact STC | exact BSL | exact INV' | exact PBK' | exact (BOK_set_co _ _ ts0 B (S nB) co' ltac:(cbn [t_co ts0]; lia) BK) | exact Hl | exact Hst | cbn [t_co ts_set_co]; lia | cbn [t_co ts_set_co pf_len]; lia | |].
- intros m2 md2 A2 B2 pbs2 errv2 gp' t0' t1' t2' b0' b1' b2' b3' b4' b5' b6' b7' s5' F' fc' I2 P2 K2 FS2 FRM2.
eapply (Kbreak m2 md2 A2 B2 pbs2 errv2 co' cb'); [cbn [t_co pf_len]; lia | exact Hc' | exact E42' | exact I2 | exact P2 | exact K2 | exact FS2 | exact FRM2].
- intros m2 md2 A2 B2 errv2 y1 gp' t0' t1' t2' b0' b1' b2' b3' b4' b5' b6' b7' s3' s5' t3' t4' t5' t6' F' fc' I2 FS2 FRM2.
eapply (KerrS m2 md2 A2 B2 errv2 co' cb'); [cbn [t_co pf_len]; lia | exact I2 | exact FS2 | exact FRM2]. }
destruct (Z.eq_dec (bv_unsigned cb) 10) as [E42 | N42].
- if_falsex.
evt_done5.
unfold pe_msS, APE_CEOL_NL in STAR. cbn [pf_tk pf_spf pf_sb pf_lenr pa_sp0 pa_F] in STAR. unfold shA in STAR. unfold A_TP, A_SB in STAR.
eapply (STAR m co cb); [lia | exact Hc | exact E42 | exact INV0 | exact PBK0].
- if_truex.
asan_rechkM 1.
step.
norm_sx32.
step.
step.
norm_w32.
step. step.
evt_done5.
replace (Z_to_bv 64 1) with (Z_to_bv 64 (co + 1 - co)) by (f_equal; lia).
eapply (ceol_latch_A (Z.to_nat (len - co)) (PEF tk oldl newl len lenr sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m md A B ts0 l co cb nb pj sv errv T (S nB));
[ exact STC | exact BSL | reflexivity | exact INV0 | exact PBK0 | exact BK | exact CSTR | exact Hl | exact Hst | cbn [t_co ts0]; lia | exact Hco | exact Hc | exact N42 | cbn [t_co ts0 pf_len]; lia | | | ].
+ intros m' co' cb' x1' a0' a1' a2' a3' a4' a5' R' Hc' E42' INV' PBK'.
unfold pe_msS, APE_CEOL_NL in STAR |- *. eapply (STAR m' co' cb'); [cbn [t_co ts0 pf_len] in R'; lia | exact Hc' | exact E42' | exact INV' | exact PBK'].
+ intros m' md' A' B' pbs' e co' cb' errv' y1 gp' t0' t1' t2' b0' b1' b2' b3' b4' b5' b6' b7' s5' s7' s11' t4' t6' F' fc' R' I2 FS2 FRM2.
eapply (Kout m' md' A' B' pbs' e co' cb' errv'); [exact R' | exact I2 | exact FS2 | exact FRM2].
+ intros m' md' A' B' pbs' e co' cb' errv' y1 gp' t0' t1' t2' b0' b1' b2' b3' b4' b5' b6' b7' s5' s7' s11' t4' t6' F' fc' R' I2 FS2 FRM2.
eapply (KerrF m' md' A' B' pbs' e co' cb' errv'); [exact R' | exact I2 | exact FS2 | exact FRM2].
Qed.

End PeSCeolA.
End RC__1.
