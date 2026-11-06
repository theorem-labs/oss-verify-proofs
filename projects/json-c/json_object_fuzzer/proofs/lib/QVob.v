(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup Lib.GwApply QWxq_c1 QRjH QHnV QCcH QfLs Q0Ek Qtgi QjDH Qsw7 QJjn QRUw QkMG QG8z Qdyh QIsM Qa8x Q7UD Qhd4 Qwm6 QlKV QsKa Qiiq Q4v2 Q1Ey Ql4f Q1Y6 QrQv QEUF QW22 QdGy QYZ0 QnDr Qmgs Q63E Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QJjn QRUw.Mq0 QRUw QkMG. Import QG8z Qdyh.Mq0 Qdyh.Mq3 Qdyh.Mq4 QIsM.Mq2 Qa8x.Mq2.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa QsKa.Mq4 Qiiq.Mq0 QsKa.Mq6 Q4v2.Mq0 QlKV.Mq5 Q1Ey Ql4f.Mq1 Q1Y6.Mq2 QsKa.Mq8 QrQv.Mq2 QEUF QW22.Mq3 QdGy.Mq2 QYZ0.Mq3 QlKV.Mq7 QsKa.Mq5 QnDr.Mq2 Qmgs QdGy.Mq6 Q63E.Mq4 Q63E.Mq5.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Lemma lvl_mode_start : forall ss c hn, 0 <= ss <= 26 -> lvl_mode ST_start ss = Some (c, hn) -> c = CNone /\ hn = false.
Proof.
intros ss c hn R H. assert (CASES : exists k : nat, (k <= 26)%nat /\ ss = Z.of_nat k) by (exists (Z.to_nat ss); split; lia).
destruct CASES as (k & Hk & ->). clear R.
do 27 (destruct k as [|k]; [vm_compute in H; first [discriminate H | injection H as <- <-; split; reflexivity] |]); exfalso; lia.
Qed.

Lemma BOK_afford : forall pf pa ts B n c {C}, 0 <= pa_bslack pa -> BOK pf pa ts B (S (Z.to_nat C + n)) -> c <= C -> c <= bB B.
Proof.
intros pf pa ts B n c C BSL BK Hc. pose proof (BOK_ledger_nonneg _ _ _ _ _ BK) as L0. pose proof BK as (H1 & _ & H3 & _). unfold bneed in H1.
pose proof (K_ev_pos pf). pose proof (Zle_0_nat (length (tstate_blocks ts))).
replace (K_ev pf * Z.of_nat (S (Z.to_nat C + n))) with (K_ev pf * Z.of_nat n + (Z.max 0 C + 1)) in H1 by (unfold K_ev; lia).
pose proof (Z.mul_nonneg_nonneg (K_ev pf) (Z.of_nat n) ltac:(lia) ltac:(lia)). unfold K_free, K_exit in *. lia.
Qed.

Section PeSStartCA.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_outside : forall m m' W, GA m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= hl_img_lo A4H \/ hl_img_hi A4H <= fst iv) W -> GA m'.
Hypothesis GA_pres : forall LB SP m m', heap_pres A4H LB SP m m' -> GA m -> GA m'.
Hypothesis NEWARR : jo_new_array_A3 HIx.
Hypothesis GA_lh : forall m, GA m -> lh_globA m.
Hypothesis NEWOBJ : jo_new_object_A3_stmt HIx.

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

Lemma start_arr_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP v2 ra2 : Z) (nB : nat)
(gp t0 t1 t2 a1 a3 a4 a5 a6 a7 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv -> PBOK m ts kP -> BOK pf pa ts B (S (Z.to_nat 10496 + nB)) ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_start ->
pe_s0 sv = Z_to_bv 64 v2 -> pe_ra sv = Z_to_bv 64 ra2 ->
(v2 < alloc_ceiling \/ v2 mod 8 <> 0 \/ v2 <= pa_sp0 pa \/ hiA_top A4L HIx - 16 <= v2) /\ 0 <= v2 < 2^64 ->
uw_ok A4L (hl_malloc A4H) (Z_to_bv 64 0x9eb50) (UWfp ra2 v2) ->

(forall m' md' A' B' errv' r BS gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' F' fc',
arr_capA BS = 32 -> length BS = 3%nat ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' (ts_lvl ts (TL ST_eatws ST_array r (Some (Sarr [])) BS 0 [])) cb nb pj sv errv' ->
PBOK m' (ts_lvl ts (TL ST_eatws ST_array r (Some (Sarr [])) BS 0 [])) kP ->
BOK pf pa (ts_lvl ts (TL ST_eatws ST_array r (Some (Sarr [])) BS 0 [])) B' nB ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msA asegs pf pa APE_BREAK (t_co ts) gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5'
(Z_to_bv 64 (pf_tk pf + 56)) (Z_to_bv 64 (pa_F pa + 64)) F' fc' m')) ->

(forall m' md' A' B' errv' x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s5' t3' t4' t5' t6' F' fc',
PE_INVW_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' (ts_lvl ts (TL ST_eatws ST_array 0 None [] 0 [])) [] cb nb pj sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(Q1Y6.Mq2.pe_msE pf pa APE_ERR2 x1' gp' t0' t1' t2' (Z_to_bv 64 16) a1' a2' a3' a4' a5' a6' a7'
(Z_to_bv 64 (pf_tk pf / 8 + SB2)) (Z_to_bv 64 (pf_tk pf + 20)) s5' (Z_to_bv 64 (pf_tk pf + 36)) (Z_to_bv 64 (pf_tk pf + 32)) (Z_to_bv 64 (pa_F pa))
(Z_to_bv 64 (pf_tk pf + 56)) (Z_to_bv 64 (pf_sb pf + t_co ts)) t3' t4' t5' t6' F' fc' m')) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa 0x97554 (t_co ts) gp t0 t1 t2
(Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) a1
(Z_to_bv 64 (q / 8 + 4 * Z.of_nat (t_depth ts) + A_SB)) a3 a4 a5 a6 a7
(Z_to_bv 64 (Z.of_nat (t_depth ts))) (Z_to_bv 64 q) (Z_to_bv 64 (pa_F pa + 64)) F fc m).
Proof.
intros until fc. intros STC BSL INV PBK BK Hl Hst S0V RAV HV UWK Kbreak Kerr16. pose proof INV as INV0. pe_openA STC INV.
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
unfold APE_BREAK, APE_REDO, APE_OUT, APE_ERRMEM, APE_ERRST, APE_ERR2, APE_JTAB in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
assert (cs_tk_L : csep tk 72 bse (Z.of_nat 32)) by (unfold csep; clear - Hdtq HbseR; lia).
assert (cs_L_tk : csep bse 32 tk (Z.of_nat 72)) by (unfold csep; clear - Hdtq HbseR; lia).
assert (cs_Q0_L : csep (bse / 8 + 2147450880) 1 bse (Z.of_nat 32)) by (unfold csep; clear - SEPQ0q HbseR; lia).
clear Hdtq SEPQ0q SEPQ0t SEPQ0c.
destruct (lvl_mode_start _ _ _ SS26 ltac:(rewrite <- Hst; exact Hmode)) as (Ec0 & Ehn0). subst c0 hn0.
cbn [name_ok] in NM0. destruct NM0 as [Hn0 Hnbs0].
assert (Ecs : tl_cs l = None) by (destruct (tl_cs l); [exfalso; exact CLS0 | reflexivity]).
pose proof (LV depth l Hl) as (_ & _ & JO & _). rewrite Ecs in JO. cbn [jopt] in JO. destruct JO as [Ecur Ecbs].
assert (Eobjbs : objbs = []).
{ unfold cur_st in OBJ. cbn [t_levels t_depth t_objbs ts0] in OBJ. rewrite Hl, Hst in OBJ. exact OBJ. }
rewrite Ecur, Hn0 in Ld.
pose proof (PE_WIN_open HIx GA (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m md A B ts0 cb nb pj sv errv l INV0 Hl Hn0 Hnbs0 Eobjbs) as WIN0.
rewrite Ecur, Ecs, Ecbs in WIN0.
set (lw0 := TL (tl_st l) (tl_ss l) 0 None [] 0 []) in *. set (tw0 := ts_lvl ts0 lw0) in *.
assert (PBK0 : PBOKat m tw0 (co + kP)) by (exact (PBOKat_same m ts0 tw0 _ eq_refl eq_refl PBK)).
assert (Hlen0 : length (t_levels tw0) = Z.to_nat mxd) by (unfold tw0, ts_lvl, ts0; cbn [t_levels t_depth]; rewrite lupd_length; exact LEN32).
pose proof (BOK_afford (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) ts0 B nB new_array_costA BSL BK ltac:(pose proof (K_ev_pos (PEF tk oldl newl len lenr sb spf pmd mxd fl)); unfold new_array_costA; lia)) as COST.
stash Himg_t. stash Himg_q. stash Kbreak. stash Kerr16. stash WIN0. stash INV0.
clear PB REST LV OBJ HPR BUD GAP SAVED FSH FF STR ERR SBin SHT SHQ4.
reenterA asegs A4L HIx asegs_wx HP.
replace (q + 32 * Z.of_nat depth) with bse by lia.
asan_rechkA.
clear SHQ.
stepz.
step.
asan_chkM 1.
step.
stepz.
step.

set (lw1 := TL ST_eatws ST_array 0 None [] 0 []).
unstash WIN0.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, Lc : rw_cells asegs mc bse _ |- _ =>
evt_done5;
assert (INqL : Forall (fun iv => exists a n, In (a, n) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 (tsF tw0 []) ++ LM) /\ a <= fst iv /\ snd iv <= a + n) [(bse, bse + 32)])
by (apply Forall_cons; [exists q, (32 * mxd); cbn [fst snd]; split; [apply in_or_app; left; unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity | lia] | apply Forall_nil]);
assert (FRc : pe_frameA asegs mc (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) cb nb pj sv)
by (eapply (pe_frameA_blkwriteG HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) _ LM FRS B A m mc md lo [(bse, bse + 32)] cb nb pj sv); [exact STC | exact (proj1 (proj1 (proj2 WIN0))) | exact INqL | exact FR0 | exact MUc | exact WMc]);
assert (TSKc : tstack asegs mc q (lupd (t_levels tw0) (t_depth tw0) lw1))
by (pose proof MUc as MUc'; pose proof Lc as Lc'; rewrite Hbse in MUc', Lc'; eapply (tstack_put asegs m mc q (t_levels tw0) depth lw1 []);
[exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj1 WIN0)))))))))| rewrite Hlen0; lia | exact MUc' | exact WMc | intros; exact I | exact Lc']);
destruct (PE_WIN_write HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m mc md A B tw0 0 None [] 1
cb nb pj sv errv [(bse, bse + 32)] lw1 cb nb pj STC WIN0 MUc WMc MIc
ltac:(apply Forall_cons; [right; cbn [fst snd pf_mxd]; lia | apply Forall_nil])
TOKc TSKc FRc ltac:(unfold lvl_bare, lw1, ST_eatws, ST_array; cbn [tl_st tl_ss tl_cs tl_cbs tl_name tl_nbs]; repeat split; try reflexivity; lia)) as [WIN1 PBT1]
end end.
set (tw1 := ts_lvl tw0 lw1) in *.
eapply (pe_new_array_w HIx GA GA_pres NEWARR (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo _ md A B tw1 cb nb pj sv errv T (co + kP) v2 ra2);
[exact STC | exact WIN1 | exact (PBT1 _ PBK0) | exact COST | exact S0V | exact RAV | exact HV | exact UWK | rewrite unsigned_lit by lia; reflexivity |].
intros mn2 md2 A2 B2 errv2 r w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 F2 fc2 OUT2 PBK2 HB2 HD2 FS2 FRM2.
cbn [pf_spf] in *. unfold A_TP in *.
clear TOK SLOTS Ld SHQ0 MU WM MI HP INtk INq Htal Htlo Hthi Hqal Hqlo Hqhi Hqtk WIN0 WIN1 PBT1 PBK0 FR0 cs_tk_L cs_L_tk cs_Q0_L TSKc FRc INqL.
assert (Hlen1 : length (t_levels tw1) = Z.to_nat mxd) by (unfold tw1, tw0, ts_lvl, ts0; cbn [t_levels t_depth]; rewrite !lupd_length; exact LEN32).
assert (Hlw1 : nth_error (t_levels tw1) depth = Some lw1) by (unfold tw1, tw0, ts_lvl, ts0; cbn [t_levels t_depth]; apply nth_error_lupd_eq; rewrite ?lupd_length; apply nth_error_Some; rewrite Hl; discriminate).
assert (Eb0 : lvl_blocks l = []) by (unfold lvl_blocks; rewrite Ecbs, Hnbs0; reflexivity).
destruct OUT2 as [(-> & WIN2) | (Hr & BS & CAP & LEN3 & Rr & WIN2)].
-
pose proof WIN2 as (CORE2 & BASE2 & _). destruct CORE2 as (_ & _ & _ & _ & TOK & _ & _ & TSK2 & FR2). pose proof (proj1 BASE2) as HP. clear BASE2.
unfold tw1, tw0, ts_lvl, ts0 in TOK. cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_tk pf_mxd pf_fl] in TOK.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
pose proof FR2 as (SLOTS & _). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in SLOTS.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 (tsF tw1 []))) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * mxd) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 (tsF tw1 []))) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t2.
blk_factsA A4L HIx HP q (32 * mxd) Hqal Hqlo Hqhi Himg_q2.
pose proof (q_ne_tkA HIx _ _ _ _ _ _ _ _ _ _ HP) as Hqtk. cbn [pf_tk] in Hqtk.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ tk 72 q (32 * mxd) HP (in_or_app _ LM _ (or_introl INtk)) (in_or_app _ LM _ (or_introl INq)) ltac:(congruence)) as Hdtq.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs mn2) as WM.
pose proof (TSK2 depth lw1 Hlw1) as Ld. rewrite <- Hbse in Ld. unfold srec_cells, lw1 in Ld. cbn [tl_st tl_ss tl_cur tl_name] in Ld.
shq_facts HP INq INtk q mxd tk (Z.of_nat depth) 2 SHQ2 SEPQ2c SEPQ2q SEPQ2t.
replace (q / 8 + 4 * (Z.of_nat depth) + 2 + A_SB) with (bse / 8 + 2147450882) in SHQ2 by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia).
assert (EQx : q / 8 + A_SB + (4 * (Z.of_nat depth) + 2) = bse / 8 + 2147450882) by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia). rewrite EQx in SEPQ2c, SEPQ2q, SEPQ2t. clear EQx.
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
assert (cs_T4_L : csep (tk / 8 + 2147450884) 1 bse (Z.of_nat 32)) by (unfold csep; clear - SEPT4q HbseR; lia).
clear Hdtq SEPQ2q SEPQ2t SEPT7q SEPT7t SEPT2q SEPT2t SEPT4q SEPT4t.
stash Himg_t2. stash Himg_q2. stash WIN2. stash TSK2. stash FR2.
reenterA asegs A4L HIx asegs_wx HP.
step.
asan_rechkA.
asan_rechkM 3.
clear SHT7 SHT2.
step.
norm_sx32.
step.
rewrite (unsigned_lit (Z.of_nat depth)) by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32.
step.
replace (q + Z.of_nat depth * 32) with bse by lia.
step.
asan_chkM 3.
clear SHQ2.
stepz.
step.
if_false.
step.
step.
asan_rechkA.
step.

set (lw2 := TL ST_eatws ST_array 0 None [] 0 []).
unstash WIN2. unstash TSK2. unstash FR2.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ mn2 mc, WMc : wmono asegs mn2 mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, Lc : rw_cells asegs mc bse _ |- _ =>
evt_done5;
assert (INqL : Forall (fun iv => exists a n, In (a, n) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 (tsF tw1 []) ++ LM) /\ a <= fst iv /\ snd iv <= a + n) [(bse, bse + 32)])
by (apply Forall_cons; [exists q, (32 * mxd); cbn [fst snd]; split; [apply in_or_app; left; exact INq | lia] | apply Forall_nil]);
assert (FRc : pe_frameA asegs mc (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) cb nb pj sv)
by (eapply (pe_frameA_blkwriteG HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) _ LM FRS B2 A2 mn2 mc md2 lo [(bse, bse + 32)] cb nb pj sv); [exact STC | exact HP | exact INqL | exact FR2 | exact MUc | exact WMc]);
assert (TSKc : tstack asegs mc q (lupd (t_levels tw1) (t_depth tw1) lw2))
by (pose proof MUc as MUc'; pose proof Lc as Lc'; rewrite Hbse in MUc', Lc'; eapply (tstack_put asegs mn2 mc q (t_levels tw1) depth lw2 []);
[exact TSK2 | rewrite Hlen1; lia | exact MUc' | exact WMc | intros; exact I | exact Lc']);
destruct (PE_WIN_write HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo mn2 mc md2 A2 B2 tw1 0 None [] 1
cb nb pj sv errv2 [(bse, bse + 32)] lw2 cb nb pj STC WIN2 MUc WMc MIc
ltac:(apply Forall_cons; [right; cbn [fst snd pf_mxd]; lia | apply Forall_nil])
TOKc TSKc FRc ltac:(unfold lvl_bare, lw2, ST_eatws, ST_array; cbn [tl_st tl_ss tl_cs tl_cbs tl_name tl_nbs]; repeat split; try reflexivity; lia)) as [WIN3 PBT3]
end end.
set (tw2 := ts_lvl tw1 lw2) in *.
assert (Etw2 : forall lx, ts_lvl tw2 lx = ts_lvl ts0 lx) by (intros lx; unfold tw2, tw1, tw0; rewrite !ts_lvl_lvl; reflexivity).
pose proof (BOK_weak _ _ _ _ _ (BOK_pay (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) ts0 B B2 nB new_array_costA BK ltac:(pose proof (K_ev_pos (PEF tk oldl newl len lenr sb spf pmd mxd fl)); unfold new_array_costA; lia) HB2 ltac:(lia))) as [HBw HDw].
assert (Eblk : Z.of_nat (length (tstate_blocks tw2)) = Z.of_nat (length (tstate_blocks ts0))).
{ rewrite <- (ts_lvl_same tw2 lw2) by (unfold tw2, ts_lvl; cbn [t_levels t_depth]; apply nth_error_lupd_eq; rewrite Hlen1; cbn [t_depth tw1 tw0 ts_lvl ts0]; lia).
rewrite Etw2. rewrite (tstate_blocks_lvl_length ts0 l lw2 Hl), Eb0. cbn [lvl_blocks lw2 tl_cbs tl_nbs app length]. lia. }
pose proof (PE_WIN_close_weak HIx GA (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo _ md2 A2 B2 tw2 cb nb pj sv errv2 1 WIN3
ltac:(exists lw2; split; [unfold tw2, ts_lvl; cbn [t_levels t_depth]; apply nth_error_lupd_eq; rewrite Hlen1; cbn [t_depth tw1 tw0 ts_lvl ts0]; lia | reflexivity])
ltac:(rewrite Eblk; exact HBw) HDw) as INVw.
rewrite <- (ts_lvl_same tw2 lw2) in INVw by (unfold tw2, ts_lvl; cbn [t_levels t_depth]; apply nth_error_lupd_eq; rewrite Hlen1; cbn [t_depth tw1 tw0 ts_lvl ts0]; lia).
rewrite Etw2 in INVw.
unstash Kerr16. eapply (Kerr16 _ md2 A2 B2 errv2); [exact INVw | exact FS2 | exact FRM2].
-
pose proof WIN2 as (CORE2 & BASE2 & _). destruct CORE2 as (_ & _ & _ & _ & TOK & _ & _ & TSK2 & FR2). pose proof (proj1 BASE2) as HP. clear BASE2.
unfold tw1, tw0, ts_lvl, ts0 in TOK. cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_tk pf_mxd pf_fl] in TOK.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
pose proof FR2 as (SLOTS & _). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in SLOTS.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 (tsF tw1 BS))) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * mxd) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 (tsF tw1 BS))) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t2.
blk_factsA A4L HIx HP q (32 * mxd) Hqal Hqlo Hqhi Himg_q2.
pose proof (q_ne_tkA HIx _ _ _ _ _ _ _ _ _ _ HP) as Hqtk. cbn [pf_tk] in Hqtk.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ tk 72 q (32 * mxd) HP (in_or_app _ LM _ (or_introl INtk)) (in_or_app _ LM _ (or_introl INq)) ltac:(congruence)) as Hdtq.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs mn2) as WM.
pose proof (TSK2 depth lw1 Hlw1) as Ld. rewrite <- Hbse in Ld. unfold srec_cells, lw1 in Ld. cbn [tl_st tl_ss tl_cur tl_name] in Ld.
shq_facts HP INq INtk q mxd tk (Z.of_nat depth) 2 SHQ2 SEPQ2c SEPQ2q SEPQ2t.
replace (q / 8 + 4 * (Z.of_nat depth) + 2 + A_SB) with (bse / 8 + 2147450882) in SHQ2 by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia).
assert (EQx : q / 8 + A_SB + (4 * (Z.of_nat depth) + 2) = bse / 8 + 2147450882) by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia). rewrite EQx in SEPQ2c, SEPQ2q, SEPQ2t. clear EQx.
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
assert (cs_T4_L : csep (tk / 8 + 2147450884) 1 bse (Z.of_nat 32)) by (unfold csep; clear - SEPT4q HbseR; lia).
clear Hdtq SEPQ2q SEPQ2t SEPT7q SEPT7t SEPT2q SEPT2t SEPT4q SEPT4t.
stash Himg_t2. stash Himg_q2. stash WIN2. stash TSK2. stash FR2.
reenterA asegs A4L HIx asegs_wx HP.
step.
asan_rechkA.
asan_rechkM 3.
clear SHT7 SHT2.
step.
norm_sx32.
step.
rewrite (unsigned_lit (Z.of_nat depth)) by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32.
step.
replace (q + Z.of_nat depth * 32) with bse by lia.
step.
asan_chkM 3.
clear SHQ2.
stepz.
step.
if_truex.

set (lw2 := TL ST_eatws ST_array r None [] 0 []).
unstash WIN2. unstash TSK2. unstash FR2.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ mn2 mc, WMc : wmono asegs mn2 mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, Lc : rw_cells asegs mc bse _ |- _ =>
evt_done5;
assert (INqL : Forall (fun iv => exists a n, In (a, n) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 (tsF tw1 BS) ++ LM) /\ a <= fst iv /\ snd iv <= a + n) [(bse, bse + 32)])
by (apply Forall_cons; [exists q, (32 * mxd); cbn [fst snd]; split; [apply in_or_app; left; exact INq | lia] | apply Forall_nil]);
assert (FRc : pe_frameA asegs mc (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) cb nb pj sv)
by (eapply (pe_frameA_blkwriteG HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) _ LM FRS B2 A2 mn2 mc md2 lo [(bse, bse + 32)] cb nb pj sv); [exact STC | exact HP | exact INqL | exact FR2 | exact MUc | exact WMc]);
assert (TSKc : tstack asegs mc q (lupd (t_levels tw1) (t_depth tw1) lw2))
by (pose proof MUc as MUc'; pose proof Lc as Lc'; rewrite Hbse in MUc', Lc'; eapply (tstack_put asegs mn2 mc q (t_levels tw1) depth lw2 []);
[exact TSK2 | rewrite Hlen1; lia | exact MUc' | exact WMc | intros; exact I | exact Lc']);
destruct (PE_WIN_write HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo mn2 mc md2 A2 B2 tw1 r (Some (Sarr [])) BS 1
cb nb pj sv errv2 [(bse, bse + 32)] lw2 cb nb pj STC WIN2 MUc WMc MIc
ltac:(apply Forall_cons; [right; cbn [fst snd pf_mxd]; lia | apply Forall_nil])
TOKc TSKc FRc ltac:(unfold lvl_bare, lw2, ST_eatws, ST_array; cbn [tl_st tl_ss tl_cs tl_cbs tl_name tl_nbs]; repeat split; try reflexivity; lia)) as [WIN3 PBT3]
end end.
set (tw2 := ts_lvl tw1 lw2) in *.
assert (Etw2 : forall lx, ts_lvl tw2 lx = ts_lvl ts0 lx) by (intros lx; unfold tw2, tw1, tw0; rewrite !ts_lvl_lvl; reflexivity).
assert (Hlw2 : nth_error (t_levels tw2) (t_depth tw2) = Some lw2) by (unfold tw2, ts_lvl; cbn [t_levels t_depth]; apply nth_error_lupd_eq; rewrite Hlen1; cbn [t_depth tw1 tw0 ts_lvl ts0]; lia).
assert (BKf : BOK (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) (ts_lvl ts0 (TL ST_eatws ST_array r (Some (Sarr [])) BS 0 [])) B2 nB).
{ eapply (BOK_attach (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) ts0 B B2 nB l ST_eatws ST_array r (Sarr []) BS new_array_costA BK Hl Ecs Eb0);
[ unfold phi_level; cbn [tl_cs tl_cbs length Z.of_nat]; rewrite CAP; unfold PhiA, RA; lia
| unfold phi_level; cbn [tl_cs tl_cbs length Z.of_nat]; rewrite CAP, LEN3; pose proof (K_ev_pos (PEF tk oldl newl len lenr sb spf pmd mxd fl)); unfold PhiA, RA, K_free, new_array_costA; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia
| intros kids Ek; injection Ek as <-; rewrite CAP; unfold arr_inv; cbn [length Z.of_nat]; lia | intros kids Ek; discriminate Ek | exact HB2 | lia ]. }
pose proof (PE_WIN_close_cur HIx GA (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo _ md2 A2 B2 tw2 r (Sarr []) BS cb nb pj sv errv2 lw2 CArr WIN3 Hlw2 eq_refl
ltac:(vm_compute; reflexivity) I ltac:(reflexivity)
ltac:(cbn [tl_st tl_ss lw2]; rewrite Etw2; exact (BOK_weak _ _ _ _ _ BKf))) as INVf.
cbn [tl_st tl_ss lw2] in INVf. rewrite Etw2 in INVf.
unstash Kbreak. eapply (Kbreak _ md2 A2 B2 errv2 r BS); [exact CAP | exact LEN3 | exact INVf | | exact BKf | exact FS2 | exact FRM2].
unfold PBOK. eapply PBOKat_same with (ts := tw2); [reflexivity | reflexivity |]. exact (PBT3 _ PBK2).
Qed.

Lemma start_obj_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP v2 ra2 : Z) (nB : nat)
(gp t0 t1 t2 a1 a3 a4 a5 a6 a7 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv -> PBOK m ts kP -> BOK pf pa ts B (S (Z.to_nat 17024 + nB)) ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_start ->
pe_s0 sv = Z_to_bv 64 v2 -> pe_ra sv = Z_to_bv 64 ra2 ->
(v2 < alloc_ceiling \/ v2 mod 8 <> 0 \/ v2 <= pa_sp0 pa \/ hiA_top A4L HIx - 16 <= v2) /\ 0 <= v2 < 2^64 ->
uw_ok A4L (hl_malloc A4H) (Z_to_bv 64 0x9bbfc) (UWfp ra2 v2) ->

(forall m' md' A' B' errv' r BS gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' F' fc',
obj_capA BS = 16 -> length BS = 3%nat ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' (ts_lvl ts (TL ST_eatws ST_ofs r (Some (Sobj [])) BS 0 [])) cb nb pj sv errv' ->
PBOK m' (ts_lvl ts (TL ST_eatws ST_ofs r (Some (Sobj [])) BS 0 [])) kP ->
BOK pf pa (ts_lvl ts (TL ST_eatws ST_ofs r (Some (Sobj [])) BS 0 [])) B' nB ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msA asegs pf pa APE_BREAK (t_co ts) gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5'
(Z_to_bv 64 (pf_tk pf + 56)) (Z_to_bv 64 (pa_F pa + 64)) F' fc' m')) ->

(forall m' md' A' B' errv' x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s5' t3' t4' t5' t6' F' fc',
PE_INVW_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' (ts_lvl ts (TL ST_eatws ST_ofs 0 None [] 0 [])) [] cb nb pj sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(Q1Y6.Mq2.pe_msE pf pa APE_ERR2 x1' gp' t0' t1' t2' (Z_to_bv 64 16) a1' a2' a3' a4' a5' a6' a7'
(Z_to_bv 64 (pf_tk pf / 8 + SB2)) (Z_to_bv 64 (pf_tk pf + 20)) s5' (Z_to_bv 64 (pf_tk pf + 36)) (Z_to_bv 64 (pf_tk pf + 32)) (Z_to_bv 64 (pa_F pa))
(Z_to_bv 64 (pf_tk pf + 56)) (Z_to_bv 64 (pf_sb pf + t_co ts)) t3' t4' t5' t6' F' fc' m')) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa 0x97434 (t_co ts) gp t0 t1 t2
(Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) a1
(Z_to_bv 64 (q / 8 + 4 * Z.of_nat (t_depth ts) + A_SB)) a3 a4 a5 a6 a7
(Z_to_bv 64 (Z.of_nat (t_depth ts))) (Z_to_bv 64 q) (Z_to_bv 64 (pa_F pa + 64)) F fc m).
Proof.
intros until fc. intros STC BSL INV PBK BK Hl Hst S0V RAV HV UWK Kbreak Kerr16. pose proof INV as INV0. pe_openA STC INV.
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
unfold APE_BREAK, APE_REDO, APE_OUT, APE_ERRMEM, APE_ERRST, APE_ERR2, APE_JTAB in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
assert (cs_tk_L : csep tk 72 bse (Z.of_nat 32)) by (unfold csep; clear - Hdtq HbseR; lia).
assert (cs_L_tk : csep bse 32 tk (Z.of_nat 72)) by (unfold csep; clear - Hdtq HbseR; lia).
assert (cs_Q0_L : csep (bse / 8 + 2147450880) 1 bse (Z.of_nat 32)) by (unfold csep; clear - SEPQ0q HbseR; lia).
clear Hdtq SEPQ0q SEPQ0t SEPQ0c.
destruct (lvl_mode_start _ _ _ SS26 ltac:(rewrite <- Hst; exact Hmode)) as (Ec0 & Ehn0). subst c0 hn0.
cbn [name_ok] in NM0. destruct NM0 as [Hn0 Hnbs0].
assert (Ecs : tl_cs l = None) by (destruct (tl_cs l); [exfalso; exact CLS0 | reflexivity]).
pose proof (LV depth l Hl) as (_ & _ & JO & _). rewrite Ecs in JO. cbn [jopt] in JO. destruct JO as [Ecur Ecbs].
assert (Eobjbs : objbs = []).
{ unfold cur_st in OBJ. cbn [t_levels t_depth t_objbs ts0] in OBJ. rewrite Hl, Hst in OBJ. exact OBJ. }
rewrite Ecur, Hn0 in Ld.
pose proof (PE_WIN_open HIx GA (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m md A B ts0 cb nb pj sv errv l INV0 Hl Hn0 Hnbs0 Eobjbs) as WIN0.
rewrite Ecur, Ecs, Ecbs in WIN0.
set (lw0 := TL (tl_st l) (tl_ss l) 0 None [] 0 []) in *. set (tw0 := ts_lvl ts0 lw0) in *.
assert (PBK0 : PBOKat m tw0 (co + kP)) by (exact (PBOKat_same m ts0 tw0 _ eq_refl eq_refl PBK)).
assert (Hlen0 : length (t_levels tw0) = Z.to_nat mxd) by (unfold tw0, ts_lvl, ts0; cbn [t_levels t_depth]; rewrite lupd_length; exact LEN32).
pose proof (BOK_afford (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) ts0 B nB newobj_costB BSL BK ltac:(pose proof (K_ev_pos (PEF tk oldl newl len lenr sb spf pmd mxd fl)); unfold newobj_costB; lia)) as COST.
stash Himg_t. stash Himg_q. stash Kbreak. stash Kerr16. stash WIN0. stash INV0.
clear PB REST LV OBJ HPR BUD GAP SAVED FSH FF STR ERR SBin SHT SHQ4.
reenterA asegs A4L HIx asegs_wx HP.
replace (q + 32 * Z.of_nat depth) with bse by lia.
asan_rechkA.
clear SHQ.
stepz.
step.
asan_chkM 1.
step.
stepz.
step.

set (lw1 := TL ST_eatws ST_ofs 0 None [] 0 []).
unstash WIN0.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, Lc : rw_cells asegs mc bse _ |- _ =>
evt_done5;
assert (INqL : Forall (fun iv => exists a n, In (a, n) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 (tsF tw0 []) ++ LM) /\ a <= fst iv /\ snd iv <= a + n) [(bse, bse + 32)])
by (apply Forall_cons; [exists q, (32 * mxd); cbn [fst snd]; split; [apply in_or_app; left; unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity | lia] | apply Forall_nil]);
assert (FRc : pe_frameA asegs mc (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) cb nb pj sv)
by (eapply (pe_frameA_blkwriteG HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) _ LM FRS B A m mc md lo [(bse, bse + 32)] cb nb pj sv); [exact STC | exact (proj1 (proj1 (proj2 WIN0))) | exact INqL | exact FR0 | exact MUc | exact WMc]);
assert (TSKc : tstack asegs mc q (lupd (t_levels tw0) (t_depth tw0) lw1))
by (pose proof MUc as MUc'; pose proof Lc as Lc'; rewrite Hbse in MUc', Lc'; eapply (tstack_put asegs m mc q (t_levels tw0) depth lw1 []);
[exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj1 WIN0)))))))))| rewrite Hlen0; lia | exact MUc' | exact WMc | intros; exact I | exact Lc']);
destruct (PE_WIN_write HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m mc md A B tw0 0 None [] 1
cb nb pj sv errv [(bse, bse + 32)] lw1 cb nb pj STC WIN0 MUc WMc MIc
ltac:(apply Forall_cons; [right; cbn [fst snd pf_mxd]; lia | apply Forall_nil])
TOKc TSKc FRc ltac:(unfold lvl_bare, lw1, ST_eatws, ST_ofs; cbn [tl_st tl_ss tl_cs tl_cbs tl_name tl_nbs]; repeat split; try reflexivity; lia)) as [WIN1 PBT1]
end end.
set (tw1 := ts_lvl tw0 lw1) in *.
eapply (pe_new_object_w HIx GA GA_pres GA_lh NEWOBJ (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo _ md A B tw1 cb nb pj sv errv T (co + kP) v2 ra2);
[exact STC | exact WIN1 | exact (PBT1 _ PBK0) | exact COST | exact S0V | exact RAV | exact HV | exact UWK | rewrite unsigned_lit by lia; reflexivity |].
intros mn2 md2 A2 B2 errv2 r w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 F2 fc2 OUT2 PBK2 HB2 HD2 FS2 FRM2.
cbn [pf_spf] in *. unfold A_TP in *.
clear TOK SLOTS Ld SHQ0 MU WM MI HP INtk INq Htal Htlo Hthi Hqal Hqlo Hqhi Hqtk WIN0 WIN1 PBT1 PBK0 FR0 cs_tk_L cs_L_tk cs_Q0_L TSKc FRc INqL.
assert (Hlen1 : length (t_levels tw1) = Z.to_nat mxd) by (unfold tw1, tw0, ts_lvl, ts0; cbn [t_levels t_depth]; rewrite !lupd_length; exact LEN32).
assert (Hlw1 : nth_error (t_levels tw1) depth = Some lw1) by (unfold tw1, tw0, ts_lvl, ts0; cbn [t_levels t_depth]; apply nth_error_lupd_eq; rewrite ?lupd_length; apply nth_error_Some; rewrite Hl; discriminate).
assert (Eb0 : lvl_blocks l = []) by (unfold lvl_blocks; rewrite Ecbs, Hnbs0; reflexivity).
destruct OUT2 as [(-> & WIN2) | (Hr & BS & CAP & LEN3 & Rr & WIN2)].
-
pose proof WIN2 as (CORE2 & BASE2 & _). destruct CORE2 as (_ & _ & _ & _ & TOK & _ & _ & TSK2 & FR2). pose proof (proj1 BASE2) as HP. clear BASE2.
unfold tw1, tw0, ts_lvl, ts0 in TOK. cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_tk pf_mxd pf_fl] in TOK.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
pose proof FR2 as (SLOTS & _). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in SLOTS.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 (tsF tw1 []))) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * mxd) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 (tsF tw1 []))) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t2.
blk_factsA A4L HIx HP q (32 * mxd) Hqal Hqlo Hqhi Himg_q2.
pose proof (q_ne_tkA HIx _ _ _ _ _ _ _ _ _ _ HP) as Hqtk. cbn [pf_tk] in Hqtk.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ tk 72 q (32 * mxd) HP (in_or_app _ LM _ (or_introl INtk)) (in_or_app _ LM _ (or_introl INq)) ltac:(congruence)) as Hdtq.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs mn2) as WM.
pose proof (TSK2 depth lw1 Hlw1) as Ld. rewrite <- Hbse in Ld. unfold srec_cells, lw1 in Ld. cbn [tl_st tl_ss tl_cur tl_name] in Ld.
shq_facts HP INq INtk q mxd tk (Z.of_nat depth) 2 SHQ2 SEPQ2c SEPQ2q SEPQ2t.
replace (q / 8 + 4 * (Z.of_nat depth) + 2 + A_SB) with (bse / 8 + 2147450882) in SHQ2 by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia).
assert (EQx : q / 8 + A_SB + (4 * (Z.of_nat depth) + 2) = bse / 8 + 2147450882) by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia). rewrite EQx in SEPQ2c, SEPQ2q, SEPQ2t. clear EQx.
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
assert (cs_T4_L : csep (tk / 8 + 2147450884) 1 bse (Z.of_nat 32)) by (unfold csep; clear - SEPT4q HbseR; lia).
clear Hdtq SEPQ2q SEPQ2t SEPT7q SEPT7t SEPT2q SEPT2t SEPT4q SEPT4t.
stash Himg_t2. stash Himg_q2. stash WIN2. stash TSK2. stash FR2.
reenterA asegs A4L HIx asegs_wx HP.
step.
asan_rechkA.
asan_rechkM 3.
clear SHT7 SHT2.
step.
norm_sx32.
step.
rewrite (unsigned_lit (Z.of_nat depth)) by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32.
step.
replace (q + Z.of_nat depth * 32) with bse by lia.
step.
asan_chkM 3.
clear SHQ2.
stepz.
step.
if_false.
step.
step.
asan_rechkA.
step.

set (lw2 := TL ST_eatws ST_ofs 0 None [] 0 []).
unstash WIN2. unstash TSK2. unstash FR2.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ mn2 mc, WMc : wmono asegs mn2 mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, Lc : rw_cells asegs mc bse _ |- _ =>
evt_done5;
assert (INqL : Forall (fun iv => exists a n, In (a, n) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 (tsF tw1 []) ++ LM) /\ a <= fst iv /\ snd iv <= a + n) [(bse, bse + 32)])
by (apply Forall_cons; [exists q, (32 * mxd); cbn [fst snd]; split; [apply in_or_app; left; exact INq | lia] | apply Forall_nil]);
assert (FRc : pe_frameA asegs mc (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) cb nb pj sv)
by (eapply (pe_frameA_blkwriteG HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) _ LM FRS B2 A2 mn2 mc md2 lo [(bse, bse + 32)] cb nb pj sv); [exact STC | exact HP | exact INqL | exact FR2 | exact MUc | exact WMc]);
assert (TSKc : tstack asegs mc q (lupd (t_levels tw1) (t_depth tw1) lw2))
by (pose proof MUc as MUc'; pose proof Lc as Lc'; rewrite Hbse in MUc', Lc'; eapply (tstack_put asegs mn2 mc q (t_levels tw1) depth lw2 []);
[exact TSK2 | rewrite Hlen1; lia | exact MUc' | exact WMc | intros; exact I | exact Lc']);
destruct (PE_WIN_write HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo mn2 mc md2 A2 B2 tw1 0 None [] 1
cb nb pj sv errv2 [(bse, bse + 32)] lw2 cb nb pj STC WIN2 MUc WMc MIc
ltac:(apply Forall_cons; [right; cbn [fst snd pf_mxd]; lia | apply Forall_nil])
TOKc TSKc FRc ltac:(unfold lvl_bare, lw2, ST_eatws, ST_ofs; cbn [tl_st tl_ss tl_cs tl_cbs tl_name tl_nbs]; repeat split; try reflexivity; lia)) as [WIN3 PBT3]
end end.
set (tw2 := ts_lvl tw1 lw2) in *.
assert (Etw2 : forall lx, ts_lvl tw2 lx = ts_lvl ts0 lx) by (intros lx; unfold tw2, tw1, tw0; rewrite !ts_lvl_lvl; reflexivity).
pose proof (BOK_weak _ _ _ _ _ (BOK_pay (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) ts0 B B2 nB newobj_costB BK ltac:(pose proof (K_ev_pos (PEF tk oldl newl len lenr sb spf pmd mxd fl)); unfold newobj_costB; lia) HB2 ltac:(lia))) as [HBw HDw].
assert (Eblk : Z.of_nat (length (tstate_blocks tw2)) = Z.of_nat (length (tstate_blocks ts0))).
{ rewrite <- (ts_lvl_same tw2 lw2) by (unfold tw2, ts_lvl; cbn [t_levels t_depth]; apply nth_error_lupd_eq; rewrite Hlen1; cbn [t_depth tw1 tw0 ts_lvl ts0]; lia).
rewrite Etw2. rewrite (tstate_blocks_lvl_length ts0 l lw2 Hl), Eb0. cbn [lvl_blocks lw2 tl_cbs tl_nbs app length]. lia. }
pose proof (PE_WIN_close_weak HIx GA (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo _ md2 A2 B2 tw2 cb nb pj sv errv2 1 WIN3
ltac:(exists lw2; split; [unfold tw2, ts_lvl; cbn [t_levels t_depth]; apply nth_error_lupd_eq; rewrite Hlen1; cbn [t_depth tw1 tw0 ts_lvl ts0]; lia | reflexivity])
ltac:(rewrite Eblk; exact HBw) HDw) as INVw.
rewrite <- (ts_lvl_same tw2 lw2) in INVw by (unfold tw2, ts_lvl; cbn [t_levels t_depth]; apply nth_error_lupd_eq; rewrite Hlen1; cbn [t_depth tw1 tw0 ts_lvl ts0]; lia).
rewrite Etw2 in INVw.
unstash Kerr16. eapply (Kerr16 _ md2 A2 B2 errv2); [exact INVw | exact FS2 | exact FRM2].
-
pose proof WIN2 as (CORE2 & BASE2 & _). destruct CORE2 as (_ & _ & _ & _ & TOK & _ & _ & TSK2 & FR2). pose proof (proj1 BASE2) as HP. clear BASE2.
unfold tw1, tw0, ts_lvl, ts0 in TOK. cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_tk pf_mxd pf_fl] in TOK.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
pose proof FR2 as (SLOTS & _). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in SLOTS.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 (tsF tw1 BS))) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * mxd) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 (tsF tw1 BS))) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t2.
blk_factsA A4L HIx HP q (32 * mxd) Hqal Hqlo Hqhi Himg_q2.
pose proof (q_ne_tkA HIx _ _ _ _ _ _ _ _ _ _ HP) as Hqtk. cbn [pf_tk] in Hqtk.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ tk 72 q (32 * mxd) HP (in_or_app _ LM _ (or_introl INtk)) (in_or_app _ LM _ (or_introl INq)) ltac:(congruence)) as Hdtq.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs mn2) as WM.
pose proof (TSK2 depth lw1 Hlw1) as Ld. rewrite <- Hbse in Ld. unfold srec_cells, lw1 in Ld. cbn [tl_st tl_ss tl_cur tl_name] in Ld.
shq_facts HP INq INtk q mxd tk (Z.of_nat depth) 2 SHQ2 SEPQ2c SEPQ2q SEPQ2t.
replace (q / 8 + 4 * (Z.of_nat depth) + 2 + A_SB) with (bse / 8 + 2147450882) in SHQ2 by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia).
assert (EQx : q / 8 + A_SB + (4 * (Z.of_nat depth) + 2) = bse / 8 + 2147450882) by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia). rewrite EQx in SEPQ2c, SEPQ2q, SEPQ2t. clear EQx.
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
assert (cs_T4_L : csep (tk / 8 + 2147450884) 1 bse (Z.of_nat 32)) by (unfold csep; clear - SEPT4q HbseR; lia).
clear Hdtq SEPQ2q SEPQ2t SEPT7q SEPT7t SEPT2q SEPT2t SEPT4q SEPT4t.
stash Himg_t2. stash Himg_q2. stash WIN2. stash TSK2. stash FR2.
reenterA asegs A4L HIx asegs_wx HP.
step.
asan_rechkA.
asan_rechkM 3.
clear SHT7 SHT2.
step.
norm_sx32.
step.
rewrite (unsigned_lit (Z.of_nat depth)) by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32.
step.
replace (q + Z.of_nat depth * 32) with bse by lia.
step.
asan_chkM 3.
clear SHQ2.
stepz.
step.
if_truex.

set (lw2 := TL ST_eatws ST_ofs r None [] 0 []).
unstash WIN2. unstash TSK2. unstash FR2.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ mn2 mc, WMc : wmono asegs mn2 mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, Lc : rw_cells asegs mc bse _ |- _ =>
evt_done5;
assert (INqL : Forall (fun iv => exists a n, In (a, n) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 (tsF tw1 BS) ++ LM) /\ a <= fst iv /\ snd iv <= a + n) [(bse, bse + 32)])
by (apply Forall_cons; [exists q, (32 * mxd); cbn [fst snd]; split; [apply in_or_app; left; exact INq | lia] | apply Forall_nil]);
assert (FRc : pe_frameA asegs mc (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) cb nb pj sv)
by (eapply (pe_frameA_blkwriteG HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) _ LM FRS B2 A2 mn2 mc md2 lo [(bse, bse + 32)] cb nb pj sv); [exact STC | exact HP | exact INqL | exact FR2 | exact MUc | exact WMc]);
assert (TSKc : tstack asegs mc q (lupd (t_levels tw1) (t_depth tw1) lw2))
by (pose proof MUc as MUc'; pose proof Lc as Lc'; rewrite Hbse in MUc', Lc'; eapply (tstack_put asegs mn2 mc q (t_levels tw1) depth lw2 []);
[exact TSK2 | rewrite Hlen1; lia | exact MUc' | exact WMc | intros; exact I | exact Lc']);
destruct (PE_WIN_write HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo mn2 mc md2 A2 B2 tw1 r (Some (Sobj [])) BS 1
cb nb pj sv errv2 [(bse, bse + 32)] lw2 cb nb pj STC WIN2 MUc WMc MIc
ltac:(apply Forall_cons; [right; cbn [fst snd pf_mxd]; lia | apply Forall_nil])
TOKc TSKc FRc ltac:(unfold lvl_bare, lw2, ST_eatws, ST_ofs; cbn [tl_st tl_ss tl_cs tl_cbs tl_name tl_nbs]; repeat split; try reflexivity; lia)) as [WIN3 PBT3]
end end.
set (tw2 := ts_lvl tw1 lw2) in *.
assert (Etw2 : forall lx, ts_lvl tw2 lx = ts_lvl ts0 lx) by (intros lx; unfold tw2, tw1, tw0; rewrite !ts_lvl_lvl; reflexivity).
assert (Hlw2 : nth_error (t_levels tw2) (t_depth tw2) = Some lw2) by (unfold tw2, ts_lvl; cbn [t_levels t_depth]; apply nth_error_lupd_eq; rewrite Hlen1; cbn [t_depth tw1 tw0 ts_lvl ts0]; lia).
assert (BKf : BOK (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) (ts_lvl ts0 (TL ST_eatws ST_ofs r (Some (Sobj [])) BS 0 [])) B2 nB).
{ eapply (BOK_attach (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) ts0 B B2 nB l ST_eatws ST_ofs r (Sobj []) BS newobj_costB BK Hl Ecs Eb0);
[ unfold phi_level; cbn [tl_cs tl_cbs length Z.of_nat]; rewrite CAP; unfold PhiO; lia
| unfold phi_level; cbn [tl_cs tl_cbs length Z.of_nat]; rewrite CAP, LEN3; pose proof (K_ev_pos (PEF tk oldl newl len lenr sb spf pmd mxd fl)); unfold PhiO, K_free, newobj_costB; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia
| intros kids Ek; discriminate Ek | intros kids _; rewrite CAP; left; reflexivity | exact HB2 | lia ]. }
pose proof (PE_WIN_close_cur HIx GA (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo _ md2 A2 B2 tw2 r (Sobj []) BS cb nb pj sv errv2 lw2 CObj WIN3 Hlw2 eq_refl
ltac:(vm_compute; reflexivity) I ltac:(reflexivity)
ltac:(cbn [tl_st tl_ss lw2]; rewrite Etw2; exact (BOK_weak _ _ _ _ _ BKf))) as INVf.
cbn [tl_st tl_ss lw2] in INVf. rewrite Etw2 in INVf.
unstash Kbreak. eapply (Kbreak _ md2 A2 B2 errv2 r BS); [exact CAP | exact LEN3 | exact INVf | | exact BKf | exact FS2 | exact FRM2].
unfold PBOK. eapply PBOKat_same with (ts := tw2); [reflexivity | reflexivity |]. exact (PBT3 _ PBK2).
Qed.
End PeSStartCA.
End RC__1.
End Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI QSHS Q228 QfHY Qc5u QAzu.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QJjn QRUw.Mq0 QRUw QkMG. Import QG8z Qdyh.Mq0 Qdyh.Mq3 Qdyh.Mq4 QIsM.Mq2 Qa8x.Mq2.
Import Qhd4 Qwm6.
Import QbFI.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqj QsKa.Mqd Qiiq QsKa.Mqf Q4v2 QlKV.Mqf QSHS Ql4f.Mq4 Q1Y6.Mq4 QsKa.Mqh QrQv.Mq4 QEUF.Mq2 QW22.Mq8 QdGy.Mq9 QYZ0.Mq8 Q228.Mqa QfHY.
Import Qc5u QAzu.Mq0.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition pe_jt4A (c : Z) : Z :=
match c with 98 => 0x9730c | 102 => 0x983ec | 110 => 0x983ac | 114 => 0x9842c | 116 => 0x9846c | _ => 0 end.

Section PeSSescHA.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_outside : forall m m' W, GA m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= hl_img_lo A4H \/ hl_img_hi A4H <= fst iv) W -> GA m'.
Hypothesis GA_pres : forall LB SP m m', heap_pres A4H LB SP m m' -> GA m -> GA m'.

Lemma sesc_hash_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (c : Z)
(gp t0 a0 a2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
(c = 98 \/ c = 102 \/ c = 110 \/ c = 114 \/ c = 116) ->
(forall a0' a1',
AJ5 A4L HIx A T md
(pe_msA asegs pf pa (pe_jt4A c) (t_co ts) gp t0 a0' a1' a2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc m)) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa 0x972cc (t_co ts) gp t0 a0 (Z_to_bv 64 c) a2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc m).
Proof.
intros until fc. intros STC INV Hc K.
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR). destruct INV as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR). pose proof REST as (HP & _).
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
unfold pe_frameA in FR. destruct FR as (SLOTS & _ & _ & _ & _). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS.
unfold pe_msA in *.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (pe_jtab4A_ro m MI) as JT.
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
clear TOK PB TSK REST.
reenterA asegs A4L HIx asegs_wx HP.
destruct Hc as [-> | [-> | [-> | [-> | ->]]]].
all: step; step; step; step; step; step; step.
all: step; if_truex.
all: step; step; step; step.
all: pose proof (bytes_at_read asegs m 0x22f68 pe_jtab4A 0 4 (ro_cells_bytes_atA _ _ _ _ JT) ltac:(lia) ltac:(change (length pe_jtab4A) with 40%nat; lia)) as RD0;
pose proof (bytes_at_read asegs m 0x22f68 pe_jtab4A 8 4 (ro_cells_bytes_atA _ _ _ _ JT) ltac:(lia) ltac:(change (length pe_jtab4A) with 40%nat; lia)) as RD2;
pose proof (bytes_at_read asegs m 0x22f68 pe_jtab4A 24 4 (ro_cells_bytes_atA _ _ _ _ JT) ltac:(lia) ltac:(change (length pe_jtab4A) with 40%nat; lia)) as RD6;
pose proof (bytes_at_read asegs m 0x22f68 pe_jtab4A 32 4 (ro_cells_bytes_atA _ _ _ _ JT) ltac:(lia) ltac:(change (length pe_jtab4A) with 40%nat; lia)) as RD8;
pose proof (bytes_at_read asegs m 0x22f68 pe_jtab4A 36 4 (ro_cells_bytes_atA _ _ _ _ JT) ltac:(lia) ltac:(change (length pe_jtab4A) with 40%nat; lia)) as RD9;
unfold wa in RD0, RD2, RD6, RD8, RD9;
change (0x22f68 + 0) with 143208 in RD0; change (0x22f68 + 8) with 143216 in RD2; change (0x22f68 + 24) with 143232 in RD6; change (0x22f68 + 32) with 143240 in RD8; change (0x22f68 + 36) with 143244 in RD9.
all: step; step; step.
all: evt_done5.
all: match goal with |- AJ5 _ _ _ _ _ (MS _ _ ?pc _ _ _ _) => match type of K with forall a0' a1', AJ5 _ _ _ _ _ (MS _ _ ?pk _ _ _ _) => replace pc with pk; [apply K | apply bv_eq; vm_compute; reflexivity] end end.
Qed.

Lemma sesc_default_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet)
(gp t0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
AJ5 A4L HIx A T md
(pe_msX asegs pf pa APE_ERR3 (Z_to_bv 64 (pf_tk pf / 8 + SB2)) gp t0 (Z_to_bv 64 (pf_lenr pf)) (Z_to_bv 64 (pf_tk pf + 32)) (Z_to_bv 64 12) a1 a2 a3 a4 a5 a6 a7 s3 (Z_to_bv 64 (pf_sb pf + t_co ts)) s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc m) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa 0x9a068 (t_co ts) gp t0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc m).
Proof.
intros until fc. intros STC INV K.
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR). destruct INV as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR). pose proof REST as (HP & _).
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
unfold pe_frameA in FR. destruct FR as (SLOTS & _ & _ & _ & _). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS.
unfold pe_msA, pe_msX in *.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 (TST depth levels co pb pbs x obj objs objbs))) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
pose proof (tok_shadowA HIx _ _ _ _ _ _ _ _ HP INtk) as SHT.
unfold APE_ERR3 in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
clear TOK PB TSK REST.
reenterA asegs A4L HIx asegs_wx HP.
step.
asan_rechkB.
step. step.
evt_done5.
exact K.
Qed.
End PeSSescHA.
End RC__1.
End Mq1.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QJjn QRUw.Mq0 QRUw QkMG. Import QG8z Qdyh.Mq0 Qdyh.Mq3 Qdyh.Mq4 QIsM.Mq2 Qa8x.Mq2.
Import QbFI. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqj QsKa.Mqd Qiiq QsKa.Mqf Q4v2 QlKV.Mqf QSHS Ql4f.Mq4 Q1Y6.Mq4 QsKa.Mqh QrQv.Mq4 QEUF.Mq2 QW22.Mq8 QdGy.Mq9 QYZ0.Mq8 QlKV.Mqh QsKa.Mqe QnDr.Mq5 Qmgs.Mq0 QdGy.Mqe Q63E.Mqe Q63E.Mqf.
Import Qc5u QAzu.Mq0.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Lemma lvl_mode_start : forall ss c hn, 0 <= ss <= 26 -> lvl_mode ST_start ss = Some (c, hn) -> c = CNone /\ hn = false.
Proof.
intros ss c hn R H. assert (CASES : exists k : nat, (k <= 26)%nat /\ ss = Z.of_nat k) by (exists (Z.to_nat ss); split; lia).
destruct CASES as (k & Hk & ->). clear R.
do 27 (destruct k as [|k]; [vm_compute in H; first [discriminate H | injection H as <- <-; split; reflexivity] |]); exfalso; lia.
Qed.

Lemma BOK_afford : forall pf pa ts B n c {C}, 0 <= pa_bslack pa -> BOK pf pa ts B (S (Z.to_nat C + n)) -> c <= C -> c <= bB B.
Proof.
intros pf pa ts B n c C BSL BK Hc. pose proof (BOK_ledger_nonneg _ _ _ _ _ BK) as L0. pose proof BK as (H1 & _ & H3 & _). unfold bneed in H1.
pose proof (K_ev_pos pf). pose proof (Zle_0_nat (length (tstate_blocks ts))).
replace (K_ev pf * Z.of_nat (S (Z.to_nat C + n))) with (K_ev pf * Z.of_nat n + (Z.max 0 C + 1)) in H1 by (unfold K_ev; lia).
pose proof (Z.mul_nonneg_nonneg (K_ev pf) (Z.of_nat n) ltac:(lia) ltac:(lia)). unfold K_free, K_exit in *. lia.
Qed.

Section PeSStartCA.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_outside : forall m m' W, GA m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= hl_img_lo A4H \/ hl_img_hi A4H <= fst iv) W -> GA m'.
Hypothesis GA_pres : forall LB SP m m', heap_pres A4H LB SP m m' -> GA m -> GA m'.
Hypothesis NEWARR : jo_new_array_A3 HIx.
Hypothesis GA_lh : forall m, GA m -> lh_globA m.
Hypothesis NEWOBJ : jo_new_object_A3_stmt HIx.

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

Lemma start_arr_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP v2 ra2 : Z) (nB : nat)
(gp t0 a1 a2 a5 a6 a7 s3 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv -> PBOK m ts kP -> BOK pf pa ts B (S (Z.to_nat 10496 + nB)) ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_start ->
pe_s0 sv = Z_to_bv 64 v2 -> pe_ra sv = Z_to_bv 64 ra2 ->
(v2 < alloc_ceiling \/ v2 mod 8 <> 0 \/ v2 <= pa_sp0 pa \/ hiA_top A4L HIx - 16 <= v2) /\ 0 <= v2 < 2^64 ->
uw_ok A4L (hl_malloc A4H) (Z_to_bv 64 0xa0770) (UWfp ra2 v2) ->

(forall m' md' A' B' errv' r BS gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc',
arr_capA BS = 32 -> length BS = 3%nat ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' (ts_lvl ts (TL ST_eatws ST_array r (Some (Sarr [])) BS 0 [])) cb nb pj sv errv' ->
PBOK m' (ts_lvl ts (TL ST_eatws ST_array r (Some (Sarr [])) BS 0 [])) kP ->
BOK pf pa (ts_lvl ts (TL ST_eatws ST_array r (Some (Sarr [])) BS 0 [])) B' nB ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msA asegs pf pa APE_BREAK (t_co ts) gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' (Z_to_bv 64 2) s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' m')) ->

(forall m' md' A' B' errv' x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc',
PE_INVW_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' (ts_lvl ts (TL ST_eatws ST_array 0 None [] 0 [])) [] cb nb pj sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msX asegs pf pa APE_ERR3 x1' gp' t0' t1' t2' (Z_to_bv 64 16) a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' m')) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa 0x98900 (t_co ts) gp t0 (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) a1 a2 (Z_to_bv 64 (q / 8 + 4 * Z.of_nat (t_depth ts) + A_SB)) (Z_to_bv 64 0) a5 a6 a7 s3 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc m).
Proof.
intros until fc. intros STC BSL INV PBK BK Hl Hst S0V RAV HV UWK Kbreak Kerr16. pose proof INV as INV0. pe_openA STC INV.
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
unfold APE_BREAK, APE_REDO, APE_OUT, APE_ERRMEM, APE_ERR3, APE_JTAB in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
assert (cs_tk_L : csep tk 72 bse (Z.of_nat 32)) by (unfold csep; clear - Hdtq HbseR; lia).
assert (cs_L_tk : csep bse 32 tk (Z.of_nat 72)) by (unfold csep; clear - Hdtq HbseR; lia).
assert (cs_Q0_L : csep (bse / 8 + 2147450880) 1 bse (Z.of_nat 32)) by (unfold csep; clear - SEPQ0q HbseR; lia).
clear Hdtq SEPQ0q SEPQ0t SEPQ0c.
destruct (lvl_mode_start _ _ _ SS26 ltac:(rewrite <- Hst; exact Hmode)) as (Ec0 & Ehn0). subst c0 hn0.
cbn [name_ok] in NM0. destruct NM0 as [Hn0 Hnbs0].
assert (Ecs : tl_cs l = None) by (destruct (tl_cs l); [exfalso; exact CLS0 | reflexivity]).
pose proof (LV depth l Hl) as (_ & _ & JO & _). rewrite Ecs in JO. cbn [jopt] in JO. destruct JO as [Ecur Ecbs].
assert (Eobjbs : objbs = []).
{ unfold cur_st in OBJ. cbn [t_levels t_depth t_objbs ts0] in OBJ. rewrite Hl, Hst in OBJ. exact OBJ. }
rewrite Ecur, Hn0 in Ld.
pose proof (PE_WIN_open HIx GA (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m md A B ts0 cb nb pj sv errv l INV0 Hl Hn0 Hnbs0 Eobjbs) as WIN0.
rewrite Ecur, Ecs, Ecbs in WIN0.
set (lw0 := TL (tl_st l) (tl_ss l) 0 None [] 0 []) in *. set (tw0 := ts_lvl ts0 lw0) in *.
assert (PBK0 : PBOKat m tw0 (co + kP)) by (exact (PBOKat_same m ts0 tw0 _ eq_refl eq_refl PBK)).
assert (Hlen0 : length (t_levels tw0) = Z.to_nat mxd) by (unfold tw0, ts_lvl, ts0; cbn [t_levels t_depth]; rewrite lupd_length; exact LEN32).
pose proof (BOK_afford (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) ts0 B nB new_array_costA BSL BK ltac:(pose proof (K_ev_pos (PEF tk oldl newl len lenr sb spf pmd mxd fl)); unfold new_array_costA; lia)) as COST.
stash Himg_t. stash Himg_q. stash Kbreak. stash Kerr16. stash WIN0. stash INV0.
clear PB REST LV OBJ HPR BUD GAP SAVED FSH FF STR ERR SBin SHT SHQ4.
reenterA asegs A4L HIx asegs_wx HP.
replace (q + 32 * Z.of_nat depth) with bse by lia.
asan_rechkB.
step.
stepz.
step. if_true.
step.
asan_chkB.
step.
stepz.
step.

set (lw1 := TL ST_eatws ST_array 0 None [] 0 []).
unstash WIN0.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, Lc : rw_cells asegs mc bse _ |- _ =>
evt_done5;
assert (INqL : Forall (fun iv => exists a n, In (a, n) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 (tsF tw0 []) ++ LM) /\ a <= fst iv /\ snd iv <= a + n) [(bse, bse + 32)])
by (apply Forall_cons; [exists q, (32 * mxd); cbn [fst snd]; split; [apply in_or_app; left; unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity | lia] | apply Forall_nil]);
assert (FRc : pe_frameA asegs mc (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) cb nb pj sv)
by (eapply (pe_frameA_blkwriteG HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) _ LM FRS B A m mc md lo [(bse, bse + 32)] cb nb pj sv); [exact STC | exact (proj1 (proj1 (proj2 WIN0))) | exact INqL | exact FR0 | exact MUc | exact WMc]);
assert (TSKc : tstack asegs mc q (lupd (t_levels tw0) (t_depth tw0) lw1))
by (pose proof MUc as MUc'; pose proof Lc as Lc'; rewrite Hbse in MUc', Lc'; eapply (tstack_put asegs m mc q (t_levels tw0) depth lw1 []);
[exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj1 WIN0)))))))))| rewrite Hlen0; lia | exact MUc' | exact WMc | intros; exact I | exact Lc']);
destruct (PE_WIN_write HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m mc md A B tw0 0 None [] 1
cb nb pj sv errv [(bse, bse + 32)] lw1 cb nb pj STC WIN0 MUc WMc MIc
ltac:(apply Forall_cons; [right; cbn [fst snd pf_mxd]; lia | apply Forall_nil])
TOKc TSKc FRc ltac:(unfold lvl_bare, lw1, ST_eatws, ST_array; cbn [tl_st tl_ss tl_cs tl_cbs tl_name tl_nbs]; repeat split; try reflexivity; lia)) as [WIN1 PBT1]
end end.
set (tw1 := ts_lvl tw0 lw1) in *.
eapply (pe_new_array_w HIx GA GA_pres NEWARR (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo _ md A B tw1 cb nb pj sv errv T (co + kP) v2 ra2);
[exact STC | exact WIN1 | exact (PBT1 _ PBK0) | exact COST | exact S0V | exact RAV | exact HV | exact UWK | rewrite unsigned_lit by lia; reflexivity |].
intros mn2 md2 A2 B2 errv2 r w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 F2 fc2 OUT2 PBK2 HB2 HD2 FS2 FRM2.
cbn [pf_spf] in *. unfold A_TP in *.
clear TOK SLOTS Ld SHQ0 MU WM MI HP INtk INq Htal Htlo Hthi Hqal Hqlo Hqhi Hqtk WIN0 WIN1 PBT1 PBK0 FR0 cs_tk_L cs_L_tk cs_Q0_L TSKc FRc INqL.
assert (Hlen1 : length (t_levels tw1) = Z.to_nat mxd) by (unfold tw1, tw0, ts_lvl, ts0; cbn [t_levels t_depth]; rewrite !lupd_length; exact LEN32).
assert (Hlw1 : nth_error (t_levels tw1) depth = Some lw1) by (unfold tw1, tw0, ts_lvl, ts0; cbn [t_levels t_depth]; apply nth_error_lupd_eq; rewrite ?lupd_length; apply nth_error_Some; rewrite Hl; discriminate).
assert (Eb0 : lvl_blocks l = []) by (unfold lvl_blocks; rewrite Ecbs, Hnbs0; reflexivity).
destruct OUT2 as [(-> & WIN2) | (Hr & BS & CAP & LEN3 & Rr & WIN2)].
-
pose proof WIN2 as (CORE2 & BASE2 & _). destruct CORE2 as (_ & _ & _ & _ & TOK & _ & _ & TSK2 & FR2). pose proof (proj1 BASE2) as HP. clear BASE2.
unfold tw1, tw0, ts_lvl, ts0 in TOK. cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_tk pf_mxd pf_fl] in TOK.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
pose proof FR2 as (SLOTS & _). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in SLOTS.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 (tsF tw1 []))) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * mxd) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 (tsF tw1 []))) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t2.
blk_factsA A4L HIx HP q (32 * mxd) Hqal Hqlo Hqhi Himg_q2.
pose proof (q_ne_tkA HIx _ _ _ _ _ _ _ _ _ _ HP) as Hqtk. cbn [pf_tk] in Hqtk.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ tk 72 q (32 * mxd) HP (in_or_app _ LM _ (or_introl INtk)) (in_or_app _ LM _ (or_introl INq)) ltac:(congruence)) as Hdtq.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs mn2) as WM.
pose proof (TSK2 depth lw1 Hlw1) as Ld. rewrite <- Hbse in Ld. unfold srec_cells, lw1 in Ld. cbn [tl_st tl_ss tl_cur tl_name] in Ld.
shq_facts HP INq INtk q mxd tk (Z.of_nat depth) 2 SHQ2 SEPQ2c SEPQ2q SEPQ2t.
replace (q / 8 + 4 * (Z.of_nat depth) + 2 + A_SB) with (bse / 8 + 2147450882) in SHQ2 by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia).
assert (EQx : q / 8 + A_SB + (4 * (Z.of_nat depth) + 2) = bse / 8 + 2147450882) by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia). rewrite EQx in SEPQ2c, SEPQ2q, SEPQ2t. clear EQx.
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
assert (cs_T4_L : csep (tk / 8 + 2147450884) 1 bse (Z.of_nat 32)) by (unfold csep; clear - SEPT4q HbseR; lia).
clear Hdtq SEPQ2q SEPQ2t SEPT7q SEPT7t SEPT2q SEPT2t SEPT4q SEPT4t.
stash Himg_t2. stash Himg_q2. stash WIN2. stash TSK2. stash FR2.
reenterA asegs A4L HIx asegs_wx HP.
assert (BLO : 0 < bse < 2^63 /\ q <= bse) by (subst bse; lia).
step.
asan_rechkB.
step.
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
step.
if_false.
step. step.
asan_rechkB.
step.

set (lw2 := TL ST_eatws ST_array 0 None [] 0 []).
unstash WIN2. unstash TSK2. unstash FR2.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ mn2 mc, WMc : wmono asegs mn2 mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, Lc : rw_cells asegs mc bse _ |- _ =>
evt_done5;
assert (INqL : Forall (fun iv => exists a n, In (a, n) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 (tsF tw1 []) ++ LM) /\ a <= fst iv /\ snd iv <= a + n) [(bse, bse + 32)])
by (apply Forall_cons; [exists q, (32 * mxd); cbn [fst snd]; split; [apply in_or_app; left; exact INq | lia] | apply Forall_nil]);
assert (FRc : pe_frameA asegs mc (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) cb nb pj sv)
by (eapply (pe_frameA_blkwriteG HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) _ LM FRS B2 A2 mn2 mc md2 lo [(bse, bse + 32)] cb nb pj sv); [exact STC | exact HP | exact INqL | exact FR2 | exact MUc | exact WMc]);
assert (TSKc : tstack asegs mc q (lupd (t_levels tw1) (t_depth tw1) lw2))
by (pose proof MUc as MUc'; pose proof Lc as Lc'; rewrite Hbse in MUc', Lc'; eapply (tstack_put asegs mn2 mc q (t_levels tw1) depth lw2 []);
[exact TSK2 | rewrite Hlen1; lia | exact MUc' | exact WMc | intros; exact I | exact Lc']);
destruct (PE_WIN_write HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo mn2 mc md2 A2 B2 tw1 0 None [] 1
cb nb pj sv errv2 [(bse, bse + 32)] lw2 cb nb pj STC WIN2 MUc WMc MIc
ltac:(apply Forall_cons; [right; cbn [fst snd pf_mxd]; lia | apply Forall_nil])
TOKc TSKc FRc ltac:(unfold lvl_bare, lw2, ST_eatws, ST_array; cbn [tl_st tl_ss tl_cs tl_cbs tl_name tl_nbs]; repeat split; try reflexivity; lia)) as [WIN3 PBT3]
end end.
set (tw2 := ts_lvl tw1 lw2) in *.
assert (Etw2 : forall lx, ts_lvl tw2 lx = ts_lvl ts0 lx) by (intros lx; unfold tw2, tw1, tw0; rewrite !ts_lvl_lvl; reflexivity).
pose proof (BOK_weak _ _ _ _ _ (BOK_pay (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) ts0 B B2 nB new_array_costA BK ltac:(pose proof (K_ev_pos (PEF tk oldl newl len lenr sb spf pmd mxd fl)); unfold new_array_costA; lia) HB2 ltac:(lia))) as [HBw HDw].
assert (Eblk : Z.of_nat (length (tstate_blocks tw2)) = Z.of_nat (length (tstate_blocks ts0))).
{ rewrite <- (ts_lvl_same tw2 lw2) by (unfold tw2, ts_lvl; cbn [t_levels t_depth]; apply nth_error_lupd_eq; rewrite Hlen1; cbn [t_depth tw1 tw0 ts_lvl ts0]; lia).
rewrite Etw2. rewrite (tstate_blocks_lvl_length ts0 l lw2 Hl), Eb0. cbn [lvl_blocks lw2 tl_cbs tl_nbs app length]. lia. }
pose proof (PE_WIN_close_weak HIx GA (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo _ md2 A2 B2 tw2 cb nb pj sv errv2 1 WIN3
ltac:(exists lw2; split; [unfold tw2, ts_lvl; cbn [t_levels t_depth]; apply nth_error_lupd_eq; rewrite Hlen1; cbn [t_depth tw1 tw0 ts_lvl ts0]; lia | reflexivity])
ltac:(rewrite Eblk; exact HBw) HDw) as INVw.
rewrite <- (ts_lvl_same tw2 lw2) in INVw by (unfold tw2, ts_lvl; cbn [t_levels t_depth]; apply nth_error_lupd_eq; rewrite Hlen1; cbn [t_depth tw1 tw0 ts_lvl ts0]; lia).
rewrite Etw2 in INVw.
unstash Kerr16. eapply (Kerr16 _ md2 A2 B2 errv2); [exact INVw | exact FS2 | exact FRM2].
-
pose proof WIN2 as (CORE2 & BASE2 & _). destruct CORE2 as (_ & _ & _ & _ & TOK & _ & _ & TSK2 & FR2). pose proof (proj1 BASE2) as HP. clear BASE2.
unfold tw1, tw0, ts_lvl, ts0 in TOK. cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_tk pf_mxd pf_fl] in TOK.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
pose proof FR2 as (SLOTS & _). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in SLOTS.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 (tsF tw1 BS))) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * mxd) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 (tsF tw1 BS))) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t2.
blk_factsA A4L HIx HP q (32 * mxd) Hqal Hqlo Hqhi Himg_q2.
pose proof (q_ne_tkA HIx _ _ _ _ _ _ _ _ _ _ HP) as Hqtk. cbn [pf_tk] in Hqtk.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ tk 72 q (32 * mxd) HP (in_or_app _ LM _ (or_introl INtk)) (in_or_app _ LM _ (or_introl INq)) ltac:(congruence)) as Hdtq.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs mn2) as WM.
pose proof (TSK2 depth lw1 Hlw1) as Ld. rewrite <- Hbse in Ld. unfold srec_cells, lw1 in Ld. cbn [tl_st tl_ss tl_cur tl_name] in Ld.
shq_facts HP INq INtk q mxd tk (Z.of_nat depth) 2 SHQ2 SEPQ2c SEPQ2q SEPQ2t.
replace (q / 8 + 4 * (Z.of_nat depth) + 2 + A_SB) with (bse / 8 + 2147450882) in SHQ2 by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia).
assert (EQx : q / 8 + A_SB + (4 * (Z.of_nat depth) + 2) = bse / 8 + 2147450882) by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia). rewrite EQx in SEPQ2c, SEPQ2q, SEPQ2t. clear EQx.
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
assert (cs_T4_L : csep (tk / 8 + 2147450884) 1 bse (Z.of_nat 32)) by (unfold csep; clear - SEPT4q HbseR; lia).
clear Hdtq SEPQ2q SEPQ2t SEPT7q SEPT7t SEPT2q SEPT2t SEPT4q SEPT4t.
stash Himg_t2. stash Himg_q2. stash WIN2. stash TSK2. stash FR2.
reenterA asegs A4L HIx asegs_wx HP.
assert (BLO : 0 < bse < 2^63 /\ q <= bse) by (subst bse; lia).
step.
asan_rechkB.
step.
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
step.
if_truex.

set (lw2 := TL ST_eatws ST_array r None [] 0 []).
unstash WIN2. unstash TSK2. unstash FR2.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ mn2 mc, WMc : wmono asegs mn2 mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, Lc : rw_cells asegs mc bse _ |- _ =>
evt_done5;
assert (INqL : Forall (fun iv => exists a n, In (a, n) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 (tsF tw1 BS) ++ LM) /\ a <= fst iv /\ snd iv <= a + n) [(bse, bse + 32)])
by (apply Forall_cons; [exists q, (32 * mxd); cbn [fst snd]; split; [apply in_or_app; left; exact INq | lia] | apply Forall_nil]);
assert (FRc : pe_frameA asegs mc (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) cb nb pj sv)
by (eapply (pe_frameA_blkwriteG HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) _ LM FRS B2 A2 mn2 mc md2 lo [(bse, bse + 32)] cb nb pj sv); [exact STC | exact HP | exact INqL | exact FR2 | exact MUc | exact WMc]);
assert (TSKc : tstack asegs mc q (lupd (t_levels tw1) (t_depth tw1) lw2))
by (pose proof MUc as MUc'; pose proof Lc as Lc'; rewrite Hbse in MUc', Lc'; eapply (tstack_put asegs mn2 mc q (t_levels tw1) depth lw2 []);
[exact TSK2 | rewrite Hlen1; lia | exact MUc' | exact WMc | intros; exact I | exact Lc']);
destruct (PE_WIN_write HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo mn2 mc md2 A2 B2 tw1 r (Some (Sarr [])) BS 1
cb nb pj sv errv2 [(bse, bse + 32)] lw2 cb nb pj STC WIN2 MUc WMc MIc
ltac:(apply Forall_cons; [right; cbn [fst snd pf_mxd]; lia | apply Forall_nil])
TOKc TSKc FRc ltac:(unfold lvl_bare, lw2, ST_eatws, ST_array; cbn [tl_st tl_ss tl_cs tl_cbs tl_name tl_nbs]; repeat split; try reflexivity; lia)) as [WIN3 PBT3]
end end.
set (tw2 := ts_lvl tw1 lw2) in *.
assert (Etw2 : forall lx, ts_lvl tw2 lx = ts_lvl ts0 lx) by (intros lx; unfold tw2, tw1, tw0; rewrite !ts_lvl_lvl; reflexivity).
assert (Hlw2 : nth_error (t_levels tw2) (t_depth tw2) = Some lw2) by (unfold tw2, ts_lvl; cbn [t_levels t_depth]; apply nth_error_lupd_eq; rewrite Hlen1; cbn [t_depth tw1 tw0 ts_lvl ts0]; lia).
assert (BKf : BOK (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) (ts_lvl ts0 (TL ST_eatws ST_array r (Some (Sarr [])) BS 0 [])) B2 nB).
{ eapply (BOK_attach (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) ts0 B B2 nB l ST_eatws ST_array r (Sarr []) BS new_array_costA BK Hl Ecs Eb0);
[ unfold phi_level; cbn [tl_cs tl_cbs length Z.of_nat]; rewrite CAP; unfold PhiA, RA; lia
| unfold phi_level; cbn [tl_cs tl_cbs length Z.of_nat]; rewrite CAP, LEN3; pose proof (K_ev_pos (PEF tk oldl newl len lenr sb spf pmd mxd fl)); unfold PhiA, RA, K_free, new_array_costA; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia
| intros kids Ek; injection Ek as <-; rewrite CAP; unfold arr_inv; cbn [length Z.of_nat]; lia | intros kids Ek; discriminate Ek | exact HB2 | lia ]. }
pose proof (PE_WIN_close_cur HIx GA (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo _ md2 A2 B2 tw2 r (Sarr []) BS cb nb pj sv errv2 lw2 CArr WIN3 Hlw2 eq_refl
ltac:(vm_compute; reflexivity) I ltac:(reflexivity)
ltac:(cbn [tl_st tl_ss lw2]; rewrite Etw2; exact (BOK_weak _ _ _ _ _ BKf))) as INVf.
cbn [tl_st tl_ss lw2] in INVf. rewrite Etw2 in INVf.
unstash Kbreak. eapply (Kbreak _ md2 A2 B2 errv2 r BS); [exact CAP | exact LEN3 | exact INVf | | exact BKf | exact FS2 | exact FRM2].
unfold PBOK. eapply PBOKat_same with (ts := tw2); [reflexivity | reflexivity |]. exact (PBT3 _ PBK2).
Qed.

Lemma start_obj_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP v2 ra2 : Z) (nB : nat)
(gp t0 a1 a2 a5 a6 a7 s3 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv -> PBOK m ts kP -> BOK pf pa ts B (S (Z.to_nat 17024 + nB)) ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_start ->
pe_s0 sv = Z_to_bv 64 v2 -> pe_ra sv = Z_to_bv 64 ra2 ->
(v2 < alloc_ceiling \/ v2 mod 8 <> 0 \/ v2 <= pa_sp0 pa \/ hiA_top A4L HIx - 16 <= v2) /\ 0 <= v2 < 2^64 ->
uw_ok A4L (hl_malloc A4H) (Z_to_bv 64 0x9d38c) (UWfp ra2 v2) ->

(forall m' md' A' B' errv' r BS gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc',
obj_capA BS = 16 -> length BS = 3%nat ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' (ts_lvl ts (TL ST_eatws ST_ofs r (Some (Sobj [])) BS 0 [])) cb nb pj sv errv' ->
PBOK m' (ts_lvl ts (TL ST_eatws ST_ofs r (Some (Sobj [])) BS 0 [])) kP ->
BOK pf pa (ts_lvl ts (TL ST_eatws ST_ofs r (Some (Sobj [])) BS 0 [])) B' nB ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msA asegs pf pa APE_BREAK (t_co ts) gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' (Z_to_bv 64 2) s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' m')) ->

(forall m' md' A' B' errv' x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc',
PE_INVW_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' (ts_lvl ts (TL ST_eatws ST_ofs 0 None [] 0 [])) [] cb nb pj sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msX asegs pf pa APE_ERR3 x1' gp' t0' t1' t2' (Z_to_bv 64 16) a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' m')) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa 0x98820 (t_co ts) gp t0 (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) a1 a2 (Z_to_bv 64 (q / 8 + 4 * Z.of_nat (t_depth ts) + A_SB)) (Z_to_bv 64 0) a5 a6 a7 s3 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc m).
Proof.
intros until fc. intros STC BSL INV PBK BK Hl Hst S0V RAV HV UWK Kbreak Kerr16. pose proof INV as INV0. pe_openA STC INV.
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
unfold APE_BREAK, APE_REDO, APE_OUT, APE_ERRMEM, APE_ERR3, APE_JTAB in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
assert (cs_tk_L : csep tk 72 bse (Z.of_nat 32)) by (unfold csep; clear - Hdtq HbseR; lia).
assert (cs_L_tk : csep bse 32 tk (Z.of_nat 72)) by (unfold csep; clear - Hdtq HbseR; lia).
assert (cs_Q0_L : csep (bse / 8 + 2147450880) 1 bse (Z.of_nat 32)) by (unfold csep; clear - SEPQ0q HbseR; lia).
clear Hdtq SEPQ0q SEPQ0t SEPQ0c.
destruct (lvl_mode_start _ _ _ SS26 ltac:(rewrite <- Hst; exact Hmode)) as (Ec0 & Ehn0). subst c0 hn0.
cbn [name_ok] in NM0. destruct NM0 as [Hn0 Hnbs0].
assert (Ecs : tl_cs l = None) by (destruct (tl_cs l); [exfalso; exact CLS0 | reflexivity]).
pose proof (LV depth l Hl) as (_ & _ & JO & _). rewrite Ecs in JO. cbn [jopt] in JO. destruct JO as [Ecur Ecbs].
assert (Eobjbs : objbs = []).
{ unfold cur_st in OBJ. cbn [t_levels t_depth t_objbs ts0] in OBJ. rewrite Hl, Hst in OBJ. exact OBJ. }
rewrite Ecur, Hn0 in Ld.
pose proof (PE_WIN_open HIx GA (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m md A B ts0 cb nb pj sv errv l INV0 Hl Hn0 Hnbs0 Eobjbs) as WIN0.
rewrite Ecur, Ecs, Ecbs in WIN0.
set (lw0 := TL (tl_st l) (tl_ss l) 0 None [] 0 []) in *. set (tw0 := ts_lvl ts0 lw0) in *.
assert (PBK0 : PBOKat m tw0 (co + kP)) by (exact (PBOKat_same m ts0 tw0 _ eq_refl eq_refl PBK)).
assert (Hlen0 : length (t_levels tw0) = Z.to_nat mxd) by (unfold tw0, ts_lvl, ts0; cbn [t_levels t_depth]; rewrite lupd_length; exact LEN32).
pose proof (BOK_afford (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) ts0 B nB newobj_costB BSL BK ltac:(pose proof (K_ev_pos (PEF tk oldl newl len lenr sb spf pmd mxd fl)); unfold newobj_costB; lia)) as COST.
stash Himg_t. stash Himg_q. stash Kbreak. stash Kerr16. stash WIN0. stash INV0.
clear PB REST LV OBJ HPR BUD GAP SAVED FSH FF STR ERR SBin SHT SHQ4.
reenterA asegs A4L HIx asegs_wx HP.
replace (q + 32 * Z.of_nat depth) with bse by lia.
asan_rechkB.
step.
stepz.
step. if_true.
step.
asan_chkB.
step.
stepz.
step.

set (lw1 := TL ST_eatws ST_ofs 0 None [] 0 []).
unstash WIN0.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, Lc : rw_cells asegs mc bse _ |- _ =>
evt_done5;
assert (INqL : Forall (fun iv => exists a n, In (a, n) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 (tsF tw0 []) ++ LM) /\ a <= fst iv /\ snd iv <= a + n) [(bse, bse + 32)])
by (apply Forall_cons; [exists q, (32 * mxd); cbn [fst snd]; split; [apply in_or_app; left; unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity | lia] | apply Forall_nil]);
assert (FRc : pe_frameA asegs mc (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) cb nb pj sv)
by (eapply (pe_frameA_blkwriteG HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) _ LM FRS B A m mc md lo [(bse, bse + 32)] cb nb pj sv); [exact STC | exact (proj1 (proj1 (proj2 WIN0))) | exact INqL | exact FR0 | exact MUc | exact WMc]);
assert (TSKc : tstack asegs mc q (lupd (t_levels tw0) (t_depth tw0) lw1))
by (pose proof MUc as MUc'; pose proof Lc as Lc'; rewrite Hbse in MUc', Lc'; eapply (tstack_put asegs m mc q (t_levels tw0) depth lw1 []);
[exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj1 WIN0)))))))))| rewrite Hlen0; lia | exact MUc' | exact WMc | intros; exact I | exact Lc']);
destruct (PE_WIN_write HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m mc md A B tw0 0 None [] 1
cb nb pj sv errv [(bse, bse + 32)] lw1 cb nb pj STC WIN0 MUc WMc MIc
ltac:(apply Forall_cons; [right; cbn [fst snd pf_mxd]; lia | apply Forall_nil])
TOKc TSKc FRc ltac:(unfold lvl_bare, lw1, ST_eatws, ST_ofs; cbn [tl_st tl_ss tl_cs tl_cbs tl_name tl_nbs]; repeat split; try reflexivity; lia)) as [WIN1 PBT1]
end end.
set (tw1 := ts_lvl tw0 lw1) in *.
eapply (pe_new_object_w HIx GA GA_pres GA_lh NEWOBJ (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo _ md A B tw1 cb nb pj sv errv T (co + kP) v2 ra2);
[exact STC | exact WIN1 | exact (PBT1 _ PBK0) | exact COST | exact S0V | exact RAV | exact HV | exact UWK | rewrite unsigned_lit by lia; reflexivity |].
intros mn2 md2 A2 B2 errv2 r w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 F2 fc2 OUT2 PBK2 HB2 HD2 FS2 FRM2.
cbn [pf_spf] in *. unfold A_TP in *.
clear TOK SLOTS Ld SHQ0 MU WM MI HP INtk INq Htal Htlo Hthi Hqal Hqlo Hqhi Hqtk WIN0 WIN1 PBT1 PBK0 FR0 cs_tk_L cs_L_tk cs_Q0_L TSKc FRc INqL.
assert (Hlen1 : length (t_levels tw1) = Z.to_nat mxd) by (unfold tw1, tw0, ts_lvl, ts0; cbn [t_levels t_depth]; rewrite !lupd_length; exact LEN32).
assert (Hlw1 : nth_error (t_levels tw1) depth = Some lw1) by (unfold tw1, tw0, ts_lvl, ts0; cbn [t_levels t_depth]; apply nth_error_lupd_eq; rewrite ?lupd_length; apply nth_error_Some; rewrite Hl; discriminate).
assert (Eb0 : lvl_blocks l = []) by (unfold lvl_blocks; rewrite Ecbs, Hnbs0; reflexivity).
destruct OUT2 as [(-> & WIN2) | (Hr & BS & CAP & LEN3 & Rr & WIN2)].
-
pose proof WIN2 as (CORE2 & BASE2 & _). destruct CORE2 as (_ & _ & _ & _ & TOK & _ & _ & TSK2 & FR2). pose proof (proj1 BASE2) as HP. clear BASE2.
unfold tw1, tw0, ts_lvl, ts0 in TOK. cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_tk pf_mxd pf_fl] in TOK.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
pose proof FR2 as (SLOTS & _). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in SLOTS.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 (tsF tw1 []))) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * mxd) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 (tsF tw1 []))) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t2.
blk_factsA A4L HIx HP q (32 * mxd) Hqal Hqlo Hqhi Himg_q2.
pose proof (q_ne_tkA HIx _ _ _ _ _ _ _ _ _ _ HP) as Hqtk. cbn [pf_tk] in Hqtk.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ tk 72 q (32 * mxd) HP (in_or_app _ LM _ (or_introl INtk)) (in_or_app _ LM _ (or_introl INq)) ltac:(congruence)) as Hdtq.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs mn2) as WM.
pose proof (TSK2 depth lw1 Hlw1) as Ld. rewrite <- Hbse in Ld. unfold srec_cells, lw1 in Ld. cbn [tl_st tl_ss tl_cur tl_name] in Ld.
shq_facts HP INq INtk q mxd tk (Z.of_nat depth) 2 SHQ2 SEPQ2c SEPQ2q SEPQ2t.
replace (q / 8 + 4 * (Z.of_nat depth) + 2 + A_SB) with (bse / 8 + 2147450882) in SHQ2 by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia).
assert (EQx : q / 8 + A_SB + (4 * (Z.of_nat depth) + 2) = bse / 8 + 2147450882) by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia). rewrite EQx in SEPQ2c, SEPQ2q, SEPQ2t. clear EQx.
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
assert (cs_T4_L : csep (tk / 8 + 2147450884) 1 bse (Z.of_nat 32)) by (unfold csep; clear - SEPT4q HbseR; lia).
clear Hdtq SEPQ2q SEPQ2t SEPT7q SEPT7t SEPT2q SEPT2t SEPT4q SEPT4t.
stash Himg_t2. stash Himg_q2. stash WIN2. stash TSK2. stash FR2.
reenterA asegs A4L HIx asegs_wx HP.
assert (BLO : 0 < bse < 2^63 /\ q <= bse) by (subst bse; lia).
step.
asan_rechkB.
step.
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
step.
if_false.
step. step.
asan_rechkB.
step.

set (lw2 := TL ST_eatws ST_ofs 0 None [] 0 []).
unstash WIN2. unstash TSK2. unstash FR2.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ mn2 mc, WMc : wmono asegs mn2 mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, Lc : rw_cells asegs mc bse _ |- _ =>
evt_done5;
assert (INqL : Forall (fun iv => exists a n, In (a, n) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 (tsF tw1 []) ++ LM) /\ a <= fst iv /\ snd iv <= a + n) [(bse, bse + 32)])
by (apply Forall_cons; [exists q, (32 * mxd); cbn [fst snd]; split; [apply in_or_app; left; exact INq | lia] | apply Forall_nil]);
assert (FRc : pe_frameA asegs mc (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) cb nb pj sv)
by (eapply (pe_frameA_blkwriteG HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) _ LM FRS B2 A2 mn2 mc md2 lo [(bse, bse + 32)] cb nb pj sv); [exact STC | exact HP | exact INqL | exact FR2 | exact MUc | exact WMc]);
assert (TSKc : tstack asegs mc q (lupd (t_levels tw1) (t_depth tw1) lw2))
by (pose proof MUc as MUc'; pose proof Lc as Lc'; rewrite Hbse in MUc', Lc'; eapply (tstack_put asegs mn2 mc q (t_levels tw1) depth lw2 []);
[exact TSK2 | rewrite Hlen1; lia | exact MUc' | exact WMc | intros; exact I | exact Lc']);
destruct (PE_WIN_write HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo mn2 mc md2 A2 B2 tw1 0 None [] 1
cb nb pj sv errv2 [(bse, bse + 32)] lw2 cb nb pj STC WIN2 MUc WMc MIc
ltac:(apply Forall_cons; [right; cbn [fst snd pf_mxd]; lia | apply Forall_nil])
TOKc TSKc FRc ltac:(unfold lvl_bare, lw2, ST_eatws, ST_ofs; cbn [tl_st tl_ss tl_cs tl_cbs tl_name tl_nbs]; repeat split; try reflexivity; lia)) as [WIN3 PBT3]
end end.
set (tw2 := ts_lvl tw1 lw2) in *.
assert (Etw2 : forall lx, ts_lvl tw2 lx = ts_lvl ts0 lx) by (intros lx; unfold tw2, tw1, tw0; rewrite !ts_lvl_lvl; reflexivity).
pose proof (BOK_weak _ _ _ _ _ (BOK_pay (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) ts0 B B2 nB newobj_costB BK ltac:(pose proof (K_ev_pos (PEF tk oldl newl len lenr sb spf pmd mxd fl)); unfold newobj_costB; lia) HB2 ltac:(lia))) as [HBw HDw].
assert (Eblk : Z.of_nat (length (tstate_blocks tw2)) = Z.of_nat (length (tstate_blocks ts0))).
{ rewrite <- (ts_lvl_same tw2 lw2) by (unfold tw2, ts_lvl; cbn [t_levels t_depth]; apply nth_error_lupd_eq; rewrite Hlen1; cbn [t_depth tw1 tw0 ts_lvl ts0]; lia).
rewrite Etw2. rewrite (tstate_blocks_lvl_length ts0 l lw2 Hl), Eb0. cbn [lvl_blocks lw2 tl_cbs tl_nbs app length]. lia. }
pose proof (PE_WIN_close_weak HIx GA (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo _ md2 A2 B2 tw2 cb nb pj sv errv2 1 WIN3
ltac:(exists lw2; split; [unfold tw2, ts_lvl; cbn [t_levels t_depth]; apply nth_error_lupd_eq; rewrite Hlen1; cbn [t_depth tw1 tw0 ts_lvl ts0]; lia | reflexivity])
ltac:(rewrite Eblk; exact HBw) HDw) as INVw.
rewrite <- (ts_lvl_same tw2 lw2) in INVw by (unfold tw2, ts_lvl; cbn [t_levels t_depth]; apply nth_error_lupd_eq; rewrite Hlen1; cbn [t_depth tw1 tw0 ts_lvl ts0]; lia).
rewrite Etw2 in INVw.
unstash Kerr16. eapply (Kerr16 _ md2 A2 B2 errv2); [exact INVw | exact FS2 | exact FRM2].
-
pose proof WIN2 as (CORE2 & BASE2 & _). destruct CORE2 as (_ & _ & _ & _ & TOK & _ & _ & TSK2 & FR2). pose proof (proj1 BASE2) as HP. clear BASE2.
unfold tw1, tw0, ts_lvl, ts0 in TOK. cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_tk pf_mxd pf_fl] in TOK.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
pose proof FR2 as (SLOTS & _). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in SLOTS.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 (tsF tw1 BS))) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * mxd) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 (tsF tw1 BS))) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t2.
blk_factsA A4L HIx HP q (32 * mxd) Hqal Hqlo Hqhi Himg_q2.
pose proof (q_ne_tkA HIx _ _ _ _ _ _ _ _ _ _ HP) as Hqtk. cbn [pf_tk] in Hqtk.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ tk 72 q (32 * mxd) HP (in_or_app _ LM _ (or_introl INtk)) (in_or_app _ LM _ (or_introl INq)) ltac:(congruence)) as Hdtq.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs mn2) as WM.
pose proof (TSK2 depth lw1 Hlw1) as Ld. rewrite <- Hbse in Ld. unfold srec_cells, lw1 in Ld. cbn [tl_st tl_ss tl_cur tl_name] in Ld.
shq_facts HP INq INtk q mxd tk (Z.of_nat depth) 2 SHQ2 SEPQ2c SEPQ2q SEPQ2t.
replace (q / 8 + 4 * (Z.of_nat depth) + 2 + A_SB) with (bse / 8 + 2147450882) in SHQ2 by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia).
assert (EQx : q / 8 + A_SB + (4 * (Z.of_nat depth) + 2) = bse / 8 + 2147450882) by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia). rewrite EQx in SEPQ2c, SEPQ2q, SEPQ2t. clear EQx.
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
assert (cs_T4_L : csep (tk / 8 + 2147450884) 1 bse (Z.of_nat 32)) by (unfold csep; clear - SEPT4q HbseR; lia).
clear Hdtq SEPQ2q SEPQ2t SEPT7q SEPT7t SEPT2q SEPT2t SEPT4q SEPT4t.
stash Himg_t2. stash Himg_q2. stash WIN2. stash TSK2. stash FR2.
reenterA asegs A4L HIx asegs_wx HP.
assert (BLO : 0 < bse < 2^63 /\ q <= bse) by (subst bse; lia).
step.
asan_rechkB.
step.
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
step.
if_truex.

set (lw2 := TL ST_eatws ST_ofs r None [] 0 []).
unstash WIN2. unstash TSK2. unstash FR2.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ mn2 mc, WMc : wmono asegs mn2 mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, Lc : rw_cells asegs mc bse _ |- _ =>
evt_done5;
assert (INqL : Forall (fun iv => exists a n, In (a, n) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 (tsF tw1 BS) ++ LM) /\ a <= fst iv /\ snd iv <= a + n) [(bse, bse + 32)])
by (apply Forall_cons; [exists q, (32 * mxd); cbn [fst snd]; split; [apply in_or_app; left; exact INq | lia] | apply Forall_nil]);
assert (FRc : pe_frameA asegs mc (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) cb nb pj sv)
by (eapply (pe_frameA_blkwriteG HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) _ LM FRS B2 A2 mn2 mc md2 lo [(bse, bse + 32)] cb nb pj sv); [exact STC | exact HP | exact INqL | exact FR2 | exact MUc | exact WMc]);
assert (TSKc : tstack asegs mc q (lupd (t_levels tw1) (t_depth tw1) lw2))
by (pose proof MUc as MUc'; pose proof Lc as Lc'; rewrite Hbse in MUc', Lc'; eapply (tstack_put asegs mn2 mc q (t_levels tw1) depth lw2 []);
[exact TSK2 | rewrite Hlen1; lia | exact MUc' | exact WMc | intros; exact I | exact Lc']);
destruct (PE_WIN_write HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo mn2 mc md2 A2 B2 tw1 r (Some (Sobj [])) BS 1
cb nb pj sv errv2 [(bse, bse + 32)] lw2 cb nb pj STC WIN2 MUc WMc MIc
ltac:(apply Forall_cons; [right; cbn [fst snd pf_mxd]; lia | apply Forall_nil])
TOKc TSKc FRc ltac:(unfold lvl_bare, lw2, ST_eatws, ST_ofs; cbn [tl_st tl_ss tl_cs tl_cbs tl_name tl_nbs]; repeat split; try reflexivity; lia)) as [WIN3 PBT3]
end end.
set (tw2 := ts_lvl tw1 lw2) in *.
assert (Etw2 : forall lx, ts_lvl tw2 lx = ts_lvl ts0 lx) by (intros lx; unfold tw2, tw1, tw0; rewrite !ts_lvl_lvl; reflexivity).
assert (Hlw2 : nth_error (t_levels tw2) (t_depth tw2) = Some lw2) by (unfold tw2, ts_lvl; cbn [t_levels t_depth]; apply nth_error_lupd_eq; rewrite Hlen1; cbn [t_depth tw1 tw0 ts_lvl ts0]; lia).
assert (BKf : BOK (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) (ts_lvl ts0 (TL ST_eatws ST_ofs r (Some (Sobj [])) BS 0 [])) B2 nB).
{ eapply (BOK_attach (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) ts0 B B2 nB l ST_eatws ST_ofs r (Sobj []) BS newobj_costB BK Hl Ecs Eb0);
[ unfold phi_level; cbn [tl_cs tl_cbs length Z.of_nat]; rewrite CAP; unfold PhiO; lia
| unfold phi_level; cbn [tl_cs tl_cbs length Z.of_nat]; rewrite CAP, LEN3; pose proof (K_ev_pos (PEF tk oldl newl len lenr sb spf pmd mxd fl)); unfold PhiO, K_free, newobj_costB; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia
| intros kids Ek; discriminate Ek | intros kids _; rewrite CAP; left; reflexivity | exact HB2 | lia ]. }
pose proof (PE_WIN_close_cur HIx GA (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo _ md2 A2 B2 tw2 r (Sobj []) BS cb nb pj sv errv2 lw2 CObj WIN3 Hlw2 eq_refl
ltac:(vm_compute; reflexivity) I ltac:(reflexivity)
ltac:(cbn [tl_st tl_ss lw2]; rewrite Etw2; exact (BOK_weak _ _ _ _ _ BKf))) as INVf.
cbn [tl_st tl_ss lw2] in INVf. rewrite Etw2 in INVf.
unstash Kbreak. eapply (Kbreak _ md2 A2 B2 errv2 r BS); [exact CAP | exact LEN3 | exact INVf | | exact BKf | exact FS2 | exact FRM2].
unfold PBOK. eapply PBOKat_same with (ts := tw2); [reflexivity | reflexivity |]. exact (PBT3 _ PBK2).
Qed.
End PeSStartCA.
End RC__1.
End Mq2.

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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYZ0.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q228.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q228.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfHY.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfHY.Mq0.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition pe_jt4A (c : Z) : Z :=
match c with 98 => 0x960a4 | 102 => 0x970cc | 110 => 0x97084 | 114 => 0x97114 | 116 => 0x9715c | _ => 0 end.

Section PeSSescHA.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_outside : forall m m' W, GA m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= hl_img_lo A4H \/ hl_img_hi A4H <= fst iv) W -> GA m'.
Hypothesis GA_pres : forall LB SP m m', heap_pres A4H LB SP m m' -> GA m -> GA m'.

Lemma sesc_hash_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (c : Z)
(gp t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 s5 s10 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
(c = 98 \/ c = 102 \/ c = 110 \/ c = 114 \/ c = 116) ->
(forall a0' a1',
AJ5 A4L HIx A T md
(pe_msA asegs pf pa (pe_jt4A c) (t_co ts) gp t0 t1 t2 a0' a1' a2 a3 a4 a5 a6 a7 s5 (Z_to_bv 64 (pf_tk pf + 56)) (Z_to_bv 64 (pa_F pa + 64)) F fc m)) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa 0x96060 (t_co ts) gp t0 t1 t2 a0 (Z_to_bv 64 c) a2 a3 a4 a5 a6 a7 s5 s10 (Z_to_bv 64 (pa_F pa + 64)) F fc m).
Proof.
intros until fc. intros STC INV Hc K.
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR). destruct INV as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR). pose proof REST as (HP & _).
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
unfold pe_frameA in FR. destruct FR as (SLOTS & _ & _ & _ & _). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS.
unfold pe_msA in *.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (pe_jtab4A_ro m MI) as JT.
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
clear TOK PB TSK REST.
reenterA asegs A4L HIx asegs_wx HP.
destruct Hc as [-> | [-> | [-> | [-> | ->]]]].
all: step; step; step; step; step; step; step; step.
all: step; if_truex.
all: step; step; step; step.
all: pose proof (bytes_at_read asegs m 0x22ef8 pe_jtab4A 0 4 (ro_cells_bytes_atA _ _ _ _ JT) ltac:(lia) ltac:(change (length pe_jtab4A) with 40%nat; lia)) as RD0;
pose proof (bytes_at_read asegs m 0x22ef8 pe_jtab4A 8 4 (ro_cells_bytes_atA _ _ _ _ JT) ltac:(lia) ltac:(change (length pe_jtab4A) with 40%nat; lia)) as RD2;
pose proof (bytes_at_read asegs m 0x22ef8 pe_jtab4A 24 4 (ro_cells_bytes_atA _ _ _ _ JT) ltac:(lia) ltac:(change (length pe_jtab4A) with 40%nat; lia)) as RD6;
pose proof (bytes_at_read asegs m 0x22ef8 pe_jtab4A 32 4 (ro_cells_bytes_atA _ _ _ _ JT) ltac:(lia) ltac:(change (length pe_jtab4A) with 40%nat; lia)) as RD8;
pose proof (bytes_at_read asegs m 0x22ef8 pe_jtab4A 36 4 (ro_cells_bytes_atA _ _ _ _ JT) ltac:(lia) ltac:(change (length pe_jtab4A) with 40%nat; lia)) as RD9;
unfold wa in RD0, RD2, RD6, RD8, RD9;
change (0x22ef8 + 0) with 143096 in RD0; change (0x22ef8 + 8) with 143104 in RD2; change (0x22ef8 + 24) with 143120 in RD6; change (0x22ef8 + 32) with 143128 in RD8; change (0x22ef8 + 36) with 143132 in RD9.
all: step; step; step.
all: evt_done5.
all: match goal with |- AJ5 _ _ _ _ _ (MS _ _ ?pc _ _ _ _) => match type of K with forall a0' a1', AJ5 _ _ _ _ _ (MS _ _ ?pk _ _ _ _) => replace pc with pk; [apply K | apply bv_eq; vm_compute; reflexivity] end end.
Qed.

Lemma sesc_default_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet)
(gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s10 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa APE_ERR2 (t_co ts) gp t0 t1 t2 (Z_to_bv 64 12) a1 a2 a3 a4 a5 a6 a7 s5 s10 (Z_to_bv 64 (pa_F pa + 64)) F fc m) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa 0x98bec (t_co ts) gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s10 (Z_to_bv 64 (pa_F pa + 64)) F fc m).
Proof.
intros until fc. intros STC INV K.
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR). destruct INV as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR). pose proof REST as (HP & _).
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
unfold pe_frameA in FR. destruct FR as (SLOTS & _ & _ & _ & _). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS.
unfold pe_msA in *.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 (TST depth levels co pb pbs x obj objs objbs))) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
pose proof (tok_shadowA HIx _ _ _ _ _ _ _ _ HP INtk) as SHT.
unfold APE_ERR2 in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
clear TOK PB TSK REST.
reenterA asegs A4L HIx asegs_wx HP.
step.
asan_rechkA.
step. step.
evt_done5.
exact K.
Qed.
End PeSSescHA.
End RC__1.
