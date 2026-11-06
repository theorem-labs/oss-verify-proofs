(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup Lib.GwApply QWxq_c1 QRjH QHnV QCcH QfLs Q0Ek Qtgi QjDH Qsw7 QJjn QRUw QkMG Qu4M QG8z Qdyh QLbz Q2Sr QMdR QXfU Qa8x Q7UD Qhd4 Qwm6 QlKV QsKa Qiiq Q4v2 Q1Ey Ql4f Q1Y6 QrQv QEUF QdGy QWrz QYZ0 QV7s QQ2r QMgr Q63E Q4xt QK82 QdoH_c1 Q6oO QSiU Qt1H Q0rK Qeia QiiJ Qvmy QW22 Q1Rk Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QJjn QRUw.Mq0 QRUw QkMG. Import Qu4M.Mq0 QG8z Qdyh.Mq0 Qdyh.Mq2 QLbz Q2Sr Qdyh.Mq3 QMdR.Mq0 QXfU.Mq4 Q2Sr.Mq0 Qa8x.Mq3 QXfU.Mq0.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa QsKa.Mq0 QsKa.Mq4 Qiiq.Mq0 QsKa.Mq6 Q4v2.Mq0 QlKV.Mq5 QlKV.Mq7 Q1Ey Ql4f.Mq1 Q1Y6.Mq2 QrQv.Mq2 QEUF QdGy.Mq5 QWrz.Mq1 QYZ0.Mq3 QV7s QQ2r.Mq2 QMgr Q63E.Mq6 QQ2r.Mq3 Q4xt.Mq0 QK82 QdoH_c1 Q6oO.Mq0 Q63E.Mq7 QSiU Q63E.Mq2 Qt1H Q0rK Qeia.Mq1 QiiJ Qvmy.Mq0 QW22.Mq0 QWrz.Mq2 QV7s.Mq1 Q1Rk.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import QlKV.Mq2 QEUF.Mq1 QdGy.Mq3 Q63E.Mq1 QV7s.Mq0.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section PeSCases4.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_outside : forall m m' W, GA m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= hl_img_lo A4H \/ hl_img_hi A4H <= fst iv) W -> GA m'.
Hypothesis GA_pres : forall LB SP m m', heap_pres A4H LB SP m m' -> GA m -> GA m'.
Hypothesis MAPP : memappend_A_stmt2 HIx.
Hypothesis ISTRNCMP : istrncmp_spec_U.
Hypothesis ISTRNCASECMP : istrncasecmp_spec_U.
Hypothesis NEWDBL : jo_new_double_A_stmt HIx.
Hypothesis NEWBOOL : jo_new_boolean_A_stmt HIx.
Hypothesis NEWSTR : jo_new_string_len_A_stmt HIx.
Variables (pf : pe_fix) (pa : pe_fixA) (q : Z) (LBc LM : list blk) (FRS : list frame) (payload : list byte)
(me : word -> option byte) (lo : Z) (sv : pe_saved) (T : TSet) (F0 : bvmap 5 word) (utf8rep : list byte).
Hypothesis BSL : 0 <= pa_bslack pa.
Hypothesis FL0 : pf_fl pf = 0.
Hypothesis UTFR : utf8rep = Qa8x.Mq3.utf8rep.
Variables (v2 ra2 : Z).
Hypothesis S0V : pe_s0 sv = Z_to_bv 64 v2.
Hypothesis RAV : pe_ra sv = Z_to_bv 64 ra2.
Hypothesis HV : (v2 < alloc_ceiling \/ v2 mod 8 <> 0 \/ v2 <= pa_sp0 pa \/ hiA_top A4L HIx - 16 <= v2) /\ 0 <= v2 < 2^64.
Hypothesis UWK_dbl : uw_ok A4L (hl_malloc A4H) (Z_to_bv 64 0x9d9cc) (UWfp ra2 v2).
Hypothesis UWK_str : uw_ok A4L (hl_malloc A4H) (Z_to_bv 64 0x9e570) (UWfp ra2 v2).
Hypothesis UWK_dup : uw_ok A4L (hl_strdup A4L) (Z_to_bv 64 0x95f88) (UWfp ra2 v2).
Notation CASEx := (CASE_S HIx GA pf pa q LBc LM FRS payload me lo sv T F0 utf8rep).

Lemma case_null : CASEx ST_null.
Proof.
intros n ts l m md A B cb nb pj errv gp t0 t1 t2 a3 a5 a6 a7 F fc STC INV Hl Hst Hco Hcb NUM SP TD PBK BK OW UTF CSTR FS FRM M KALL KO KE.
destruct KALL as (IHL & IHR & IHB & IHA). unfold KLOOP_S in IHL. unfold KREDO_S in IHR. unfold KBRK_S in IHB. unfold KADV_S in IHA.
pose proof (PBS_of ts l Hl) as EPBS. rewrite Hst in EPBS. pbs_norm_in EPBS. rewrite EPBS in PBK.
pose proof (cur_st_ofS ts l Hl) as Est. pose proof (cur_ss_ofS ts l Hl) as Ess.
assert (RK : rank (tl_st l) (tl_ss l) = 7%nat) by (rewrite Hst; reflexivity).
assert (Hd31 : (t_depth ts <= 31)%nat) by (pose proof INV as [(LEN32 & D32 & _) _]; pose proof STC as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & ((_ & MX) & _)) & _); lia).
assert (LENR : 0 <= pf_len pf < 2^26) by (pose proof STC as (_ & _ & _ & _ & _ & X & _); exact X).
assert (CO0 : 0 <= t_co ts) by (pose proof INV as [(_ & _ & X & _) _]; lia).
assert (SPB : SPV (t_x ts) <= t_co ts) by (unfold SPOK in SP; specialize (SP ltac:(rewrite Est, Hst; reflexivity)); lia).
assert (SP0' : 0 <= SPV (t_x ts)) by (unfold SPV; apply Z.mod_pos_bound; lia).
assert (SPR : 0 <= SPV (t_x ts) + 1 < 2^32) by lia.
assert (EM : mredo pf ts = S (mredo pf ts - 1)) by (unfold mredo; rewrite Est, Ess, RK; lia). assert (EB : bredo pf ts = S (Z.to_nat 2816 + (mredo pf ts - 1 + (bx pf ts - Z.to_nat 2816)))).
{ pose proof (bx_ge pf ts ltac:(lia)) as GE9. rewrite Est, Ess, ?Hst in GE9. bres_norm_in GE9. pose proof (BTOK_ge pf). unfold BTOK in *. unfold bredo. rewrite EM at 1. lia. }
rewrite EB in BK.
assert (Ecs : tl_cs l = None).
{ pose proof INV as [_ (_ & LV & _)]. pose proof (LV _ _ Hl) as (_ & SS26 & _ & Md). rewrite Nat.ltb_irrefl, Nat.eqb_refl in Md. destruct Md as (c0 & hn0 & Hmode & CLS0 & _).
rewrite Hst in Hmode. destruct (null_mode _ _ _ SS26 Hmode) as [-> _]. destruct (tl_cs l); [exfalso; exact CLS0 | reflexivity]. }
eapply (seg_null_A HIx GA GA_outside GA_pres MAPP ISTRNCMP ISTRNCASECMP NEWDBL pf pa q LBc LM FRS payload me lo m md A B ts l cb nb pj sv errv T v2 ra2 (mredo pf ts - 1 + (bx pf ts - Z.to_nat 2816)));
[exact STC | exact BSL | exact FL0 | exact INV | exact (PBJ_PBOK _ _ _ _ PBK) | exact BK | exact Hl | exact Hst | exact Hco | exact SPB | exact S0V | exact RAV | exact HV | exact UWK_dbl | | | | | |].
-
intros m' md' A' B' pbs' errv' pj' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' F' fc' INV' PBK' BK' FS' FRM'.
eapply (IHB (ts_set_x (ts_pbs ts pbs') (t_co ts) (TS (ts_isd (t_x ts)) (Z_to_bv 64 (SPV (t_x ts) + 1)) (ts_choff (t_x ts)) (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))));
[| exact INV' | exact Hco | exact Hcb | | | | | | | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)];
destruct ts as [depth levels co pb pbs x obj objs objbs]; unfold ts_pbs, ts_set_x in *; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs] in *.
+ unfold mbrk, mbase; cbn [t_co]. unfold mredo, mbase in M; cbn [t_co] in M. rewrite Est, Ess, RK in M. lia.
+ unfold cur_st; cbn [t_levels t_depth]. rewrite Hl, Hst. discriminate.
+ unfold SPOK. cbn [t_x t_co]. intros _. unfold SPV at 1. cbn [ts_stpos]. rewrite spv_lit by exact SPR. lia.
+ eapply (tdepth_ok_same (TST depth levels co pb pbs x obj objs objbs)); [reflexivity | reflexivity | reflexivity | exact TD].
+ unfold PBS, cur_st; cbn [t_levels t_depth]. rewrite Hl, Hst. pbs_norm.
eapply (PBJ_keep _ _ (TST depth levels co pb pbs x obj objs objbs)); [reflexivity | reflexivity | reflexivity | reflexivity | exact PBK | exact PBK' | lia | rewrite Est, Hst; reflexivity | cbn [t_co]; lia].
+ eapply BOK_weaken; [| exact BK']. 1: (unfold bredo, bbrk, bloop; apply Nat.add_le_mono; [| bx_tac Hl Hst]). unfold mbrk, mredo, mbase; cbn [t_co]. rewrite Est, Ess, RK. lia.
+ unfold NAO, cur_st; cbn [t_levels t_depth]. rewrite Hl, Hst. reflexivity.
-
intros m' md' A' B' pbs' errv' pj' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' F' fc' E4 INV' PBK' BK' FS' FRM'.
eapply (IHR (ts_lvl (ts_pbs ts pbs') (TL ST_eatws ST_finish (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))));
[| exact INV' | exact Hco | exact Hcb | | | | | | | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)];
destruct ts as [depth levels co pb pbs x obj objs objbs]; unfold ts_pbs, ts_lvl in *; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs] in *.
+ unfold mredo. rewrite (cur_st_upd _ _ l), (cur_ss_upd _ _ l) by exact Hl. cbn [tl_st tl_ss]. change (rank ST_eatws ST_finish) with 6%nat. unfold mredo in M. rewrite Est, Ess, RK in M. unfold mbase in *; cbn [t_co] in *. lia.
+ intros E. exfalso. rewrite (cur_st_upd _ _ l) in E by exact Hl. cbn [tl_st] in E. discriminate E.
+ apply (SPOK_upd_plain _ _ l); [exact Hl | reflexivity].
+ eapply (tdepth_ok_upd (TST depth levels co pb pbs x obj objs objbs) l); [exact TD | exact Hl | cbn [tl_cs]; pose proof (odep_nonneg (tl_cs l)); lia | exact Hd31 | reflexivity].
+ rewrite (PBS_upd _ _ l) by exact Hl; cbn [tl_st]; pbs_norm. pbj_rs (TST depth levels co pb pbs x obj objs objbs) l PBK PBK' Hl Hst.
+ eapply BOK_weaken; [| exact BK']. 1: (unfold bredo, bbrk, bloop; apply Nat.add_le_mono; [| bx_tac Hl Hst]). unfold mredo. rewrite (cur_st_upd _ _ l), (cur_ss_upd _ _ l), Est, Ess, RK by exact Hl. cbn [tl_st tl_ss]. change (rank ST_eatws ST_finish) with 6%nat. unfold mbase; cbn [t_co]. lia.
+ apply OBJW_of_NAO. apply (NAO_upd _ _ l); [exact Hl | reflexivity].
-
intros m' md' A' B' pbs' errv' pj' r BS gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' F' fc' E3 LEN3 JF9 INV' PBK' BK' FS' FRM'.
eapply (IHR (ts_lvl (ts_pbs ts pbs') (TL ST_eatws ST_finish r (Some (Sdouble false)) BS 0 [])));
[| exact INV' | exact Hco | exact Hcb | | | | | | | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)];
destruct ts as [depth levels co pb pbs x obj objs objbs]; unfold ts_pbs, ts_lvl in *; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs] in *.
+ unfold mredo. rewrite (cur_st_upd _ _ l), (cur_ss_upd _ _ l) by exact Hl. cbn [tl_st tl_ss]. change (rank ST_eatws ST_finish) with 6%nat. unfold mredo in M. rewrite Est, Ess, RK in M. unfold mbase in *; cbn [t_co] in *. lia.
+ intros E. exfalso. rewrite (cur_st_upd _ _ l) in E by exact Hl. cbn [tl_st] in E. discriminate E.
+ apply (SPOK_upd_plain _ _ l); [exact Hl | reflexivity].
+ eapply (tdepth_ok_upd (TST depth levels co pb pbs x obj objs objbs) l); [exact TD | exact Hl | rewrite Ecs; cbn; lia | exact Hd31 | reflexivity].
+ rewrite (PBS_upd _ _ l) by exact Hl; cbn [tl_st]; pbs_norm.
eapply (PBJ_attach _ _ (TST depth levels co pb pbs x obj objs objbs) _ l _ _ _ _ _ _ _ _ _ _ _ 9 Hl);
[reflexivity | reflexivity | reflexivity | reflexivity | jl_zin Hst | exact PBK | exact PBK' | lia | reflexivity | exact JF9 | rewrite ?Hst; jl_arith].
+ eapply BOK_weaken; [| exact BK']. 1: (unfold bredo, bbrk, bloop; apply Nat.add_le_mono; [| bx_tac Hl Hst]). unfold mredo. rewrite (cur_st_upd _ _ l), (cur_ss_upd _ _ l), Est, Ess, RK by exact Hl. cbn [tl_st tl_ss]. change (rank ST_eatws ST_finish) with 6%nat. unfold mbase; cbn [t_co]. lia.
+ apply OBJW_of_NAO. apply (NAO_upd _ _ l); [exact Hl | reflexivity].
-
intros m' md' A' B' errv' x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s5' s7' s10' s11' t4' t6' F' fc' INV' FS' FRM'.
eapply (kerrst_of_kout_O HIx GA GA_outside pf pa q LBc LM FRS payload me lo sv T F0 STC KO ts [] 16);
[apply (PE_INV_A_W HIx GA); exact INV' | exact TD | lia | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)].
-
intros m' md' A' B' pbs' errv' pj' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' s11' t4' t6' F' fc' INVW' FS' FRM'.
eapply (kerrmem_of_kout HIx GA GA_outside pf pa q LBc LM FRS payload me lo sv T F0 STC KO (ts_pbs ts pbs') []);
[exact INVW' | eapply (tdepth_ok_same ts); [reflexivity | reflexivity | reflexivity | exact TD] | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)].
-
intros m' md' A' B' pbs' errv' pj' x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s8' s10' t3' t4' t5' t6' F' fc' INV' FS' FRM'.
eapply (kerrlit_of_kout HIx GA GA_outside pf pa q LBc LM FRS payload me lo sv T F0 STC KO (ts_pbs ts pbs') [] 5);
[apply (PE_INV_A_W HIx GA); exact INV' | eapply (tdepth_ok_same ts); [reflexivity | reflexivity | reflexivity | exact TD] | lia | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)].
Qed.

Lemma case_bool : CASEx ST_boolean.
Proof.
clear S0V RAV HV UWK_dbl.
intros n ts l m md A B cb nb pj errv gp t0 t1 t2 a3 a5 a6 a7 F fc STC INV Hl Hst Hco Hcb NUM SP TD PBK BK OW UTF CSTR FS FRM M KALL KO KE.
destruct KALL as (IHL & IHR & IHB & IHA). unfold KLOOP_S in IHL. unfold KREDO_S in IHR. unfold KBRK_S in IHB. unfold KADV_S in IHA.
pose proof (PBS_of ts l Hl) as EPBS. rewrite Hst in EPBS. pbs_norm_in EPBS. rewrite EPBS in PBK.
pose proof (cur_st_ofS ts l Hl) as Est. pose proof (cur_ss_ofS ts l Hl) as Ess.
assert (RK : rank (tl_st l) (tl_ss l) = 7%nat) by (rewrite Hst; reflexivity).
assert (Hd31 : (t_depth ts <= 31)%nat) by (pose proof INV as [(LEN32 & D32 & _) _]; pose proof STC as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & ((_ & MX) & _)) & _); lia).
assert (LENR : 0 <= pf_len pf < 2^26) by (pose proof STC as (_ & _ & _ & _ & _ & X & _); exact X).
assert (CO0 : 0 <= t_co ts) by (pose proof INV as [(_ & _ & X & _) _]; lia).
assert (SPB : SPV (t_x ts) <= t_co ts) by (unfold SPOK in SP; specialize (SP ltac:(rewrite Est, Hst; reflexivity)); lia).
assert (SP0' : 0 <= SPV (t_x ts)) by (unfold SPV; apply Z.mod_pos_bound; lia).
assert (SPR : 0 <= SPV (t_x ts) + 1 < 2^32) by lia.
assert (EM : mredo pf ts = S (mredo pf ts - 1)) by (unfold mredo; rewrite Est, Ess, RK; lia). assert (EB : bredo pf ts = S (Z.to_nat 2816 + (mredo pf ts - 1 + (bx pf ts - Z.to_nat 2816)))).
{ pose proof (bx_ge pf ts ltac:(lia)) as GE9. rewrite Est, Ess, ?Hst in GE9. bres_norm_in GE9. pose proof (BTOK_ge pf). unfold BTOK in *. unfold bredo. rewrite EM at 1. lia. }
rewrite EB in BK.
assert (Ecs : tl_cs l = None).
{ pose proof INV as [_ (_ & LV & _)]. pose proof (LV _ _ Hl) as (_ & SS26 & _ & Md). rewrite Nat.ltb_irrefl, Nat.eqb_refl in Md. destruct Md as (c0 & hn0 & Hmode & CLS0 & _).
rewrite Hst in Hmode. destruct (bool_mode _ _ _ SS26 Hmode) as [-> _]. destruct (tl_cs l); [exfalso; exact CLS0 | reflexivity]. }
eapply (seg_bool_A HIx GA GA_outside GA_pres MAPP ISTRNCMP ISTRNCASECMP NEWBOOL pf pa q LBc LM FRS payload me lo m md A B ts l cb nb pj sv errv T (mredo pf ts - 1 + (bx pf ts - Z.to_nat 2816)));
[exact STC | exact BSL | exact FL0 | exact INV | exact (PBJ_PBOK _ _ _ _ PBK) | exact BK | exact Hl | exact Hst | exact Hco | exact SPB | | | | | |].
-
intros m' md' A' B' pbs' errv' pj' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' F' fc' INV' PBK' BK' FS' FRM'.
eapply (IHB (ts_set_x (ts_pbs ts pbs') (t_co ts) (TS (ts_isd (t_x ts)) (Z_to_bv 64 (SPV (t_x ts) + 1)) (ts_choff (t_x ts)) (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))));
[| exact INV' | exact Hco | exact Hcb | | | | | | | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)];
destruct ts as [depth levels co pb pbs x obj objs objbs]; unfold ts_pbs, ts_set_x in *; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs] in *.
+ unfold mbrk, mbase; cbn [t_co]. unfold mredo, mbase in M; cbn [t_co] in M. rewrite Est, Ess, RK in M. lia.
+ unfold cur_st; cbn [t_levels t_depth]. rewrite Hl, Hst. discriminate.
+ unfold SPOK. cbn [t_x t_co]. intros _. unfold SPV at 1. cbn [ts_stpos]. rewrite spv_lit by exact SPR. lia.
+ eapply (tdepth_ok_same (TST depth levels co pb pbs x obj objs objbs)); [reflexivity | reflexivity | reflexivity | exact TD].
+ unfold PBS, cur_st; cbn [t_levels t_depth]. rewrite Hl, Hst. pbs_norm.
eapply (PBJ_keep _ _ (TST depth levels co pb pbs x obj objs objbs)); [reflexivity | reflexivity | reflexivity | reflexivity | exact PBK | exact PBK' | lia | rewrite Est, Hst; reflexivity | cbn [t_co]; lia].
+ eapply BOK_weaken; [| exact BK']. 1: (unfold bredo, bbrk, bloop; apply Nat.add_le_mono; [| bx_tac Hl Hst]). unfold mbrk, mredo, mbase; cbn [t_co]. rewrite Est, Ess, RK. lia.
+ unfold NAO, cur_st; cbn [t_levels t_depth]. rewrite Hl, Hst. reflexivity.
-
intros m' md' A' B' pbs' errv' pj' r BS gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' F' fc' E3 LEN3 JF9 INV' PBK' BK' FS' FRM'.
eapply (IHR (ts_lvl (ts_pbs ts pbs') (TL ST_eatws ST_finish r (Some Sbool) BS 0 [])));
[| exact INV' | exact Hco | exact Hcb | | | | | | | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)];
destruct ts as [depth levels co pb pbs x obj objs objbs]; unfold ts_pbs, ts_lvl in *; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs] in *.
+ unfold mredo. rewrite (cur_st_upd _ _ l), (cur_ss_upd _ _ l) by exact Hl. cbn [tl_st tl_ss]. change (rank ST_eatws ST_finish) with 6%nat. unfold mredo in M. rewrite Est, Ess, RK in M. unfold mbase in *; cbn [t_co] in *. lia.
+ intros E. exfalso. rewrite (cur_st_upd _ _ l) in E by exact Hl. cbn [tl_st] in E. discriminate E.
+ apply (SPOK_upd_plain _ _ l); [exact Hl | reflexivity].
+ eapply (tdepth_ok_upd (TST depth levels co pb pbs x obj objs objbs) l); [exact TD | exact Hl | rewrite Ecs; cbn; lia | exact Hd31 | reflexivity].
+ rewrite (PBS_upd _ _ l) by exact Hl; cbn [tl_st]; pbs_norm.
eapply (PBJ_attach _ _ (TST depth levels co pb pbs x obj objs objbs) _ l _ _ _ _ _ _ _ _ _ _ _ 8 Hl);
[reflexivity | reflexivity | reflexivity | reflexivity | jl_zin Hst | exact PBK | exact PBK' | lia | reflexivity | exact JF9 | rewrite ?Hst; jl_arith].
+ eapply BOK_weaken; [| exact BK']. 1: (unfold bredo, bbrk, bloop; apply Nat.add_le_mono; [| bx_tac Hl Hst]). unfold mredo. rewrite (cur_st_upd _ _ l), (cur_ss_upd _ _ l), Est, Ess, RK by exact Hl. cbn [tl_st tl_ss]. change (rank ST_eatws ST_finish) with 6%nat. unfold mbase; cbn [t_co]. lia.
+ apply OBJW_of_NAO. apply (NAO_upd _ _ l); [exact Hl | reflexivity].
-
intros m' md' A' B' pbs' errv' pj' r BS gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' F' fc' E3 LEN3 JF9 INV' PBK' BK' FS' FRM'.
eapply (IHR (ts_lvl (ts_pbs ts pbs') (TL ST_eatws ST_finish r (Some Sbool) BS 0 [])));
[| exact INV' | exact Hco | exact Hcb | | | | | | | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)];
destruct ts as [depth levels co pb pbs x obj objs objbs]; unfold ts_pbs, ts_lvl in *; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs] in *.
+ unfold mredo. rewrite (cur_st_upd _ _ l), (cur_ss_upd _ _ l) by exact Hl. cbn [tl_st tl_ss]. change (rank ST_eatws ST_finish) with 6%nat. unfold mredo in M. rewrite Est, Ess, RK in M. unfold mbase in *; cbn [t_co] in *. lia.
+ intros E. exfalso. rewrite (cur_st_upd _ _ l) in E by exact Hl. cbn [tl_st] in E. discriminate E.
+ apply (SPOK_upd_plain _ _ l); [exact Hl | reflexivity].
+ eapply (tdepth_ok_upd (TST depth levels co pb pbs x obj objs objbs) l); [exact TD | exact Hl | rewrite Ecs; cbn; lia | exact Hd31 | reflexivity].
+ rewrite (PBS_upd _ _ l) by exact Hl; cbn [tl_st]; pbs_norm.
eapply (PBJ_attach _ _ (TST depth levels co pb pbs x obj objs objbs) _ l _ _ _ _ _ _ _ _ _ _ _ 8 Hl);
[reflexivity | reflexivity | reflexivity | reflexivity | jl_zin Hst | exact PBK | exact PBK' | lia | reflexivity | exact JF9 | rewrite ?Hst; jl_arith].
+ eapply BOK_weaken; [| exact BK']. 1: (unfold bredo, bbrk, bloop; apply Nat.add_le_mono; [| bx_tac Hl Hst]). unfold mredo. rewrite (cur_st_upd _ _ l), (cur_ss_upd _ _ l), Est, Ess, RK by exact Hl. cbn [tl_st tl_ss]. change (rank ST_eatws ST_finish) with 6%nat. unfold mbase; cbn [t_co]. lia.
+ apply OBJW_of_NAO. apply (NAO_upd _ _ l); [exact Hl | reflexivity].
-
intros m' md' A' B' errv' x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s5' s7' s10' s11' t4' t6' F' fc' INV' FS' FRM'.
eapply (kerrst_of_kout_O HIx GA GA_outside pf pa q LBc LM FRS payload me lo sv T F0 STC KO ts [] 16);
[apply (PE_INV_A_W HIx GA); exact INV' | exact TD | lia | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)].
-
intros m' md' A' B' pbs' errv' pj' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' s11' t4' t6' F' fc' INVW' FS' FRM'.
eapply (kerrmem_of_kout HIx GA GA_outside pf pa q LBc LM FRS payload me lo sv T F0 STC KO (ts_pbs ts pbs') []);
[exact INVW' | eapply (tdepth_ok_same ts); [reflexivity | reflexivity | reflexivity | exact TD] | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)].
-
intros m' md' A' B' pbs' errv' pj' x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s8' s10' t3' t4' t5' t6' F' fc' INV' FS' FRM'.
eapply (kerrlit_of_kout HIx GA GA_outside pf pa q LBc LM FRS payload me lo sv T F0 STC KO (ts_pbs ts pbs') [] 6);
[apply (PE_INV_A_W HIx GA); exact INV' | eapply (tdepth_ok_same ts); [reflexivity | reflexivity | reflexivity | exact TD] | lia | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)].
Qed.

Lemma case_inf : CASEx ST_inf.
Proof.
intros n ts l m md A B cb nb pj errv gp t0 t1 t2 a3 a5 a6 a7 F fc STC INV Hl Hst Hco Hcb NUM SP TD PBK BK OW UTF CSTR FS FRM M KALL KO KE.
destruct KALL as (IHL & IHR & IHB & IHA). unfold KLOOP_S in IHL. unfold KREDO_S in IHR. unfold KBRK_S in IHB. unfold KADV_S in IHA.
pose proof (PBS_of ts l Hl) as EPBS. rewrite Hst in EPBS. pbs_norm_in EPBS. rewrite EPBS in PBK.
pose proof (cur_st_ofS ts l Hl) as Est. pose proof (cur_ss_ofS ts l Hl) as Ess.
assert (RK : rank (tl_st l) (tl_ss l) = 7%nat) by (rewrite Hst; reflexivity).
assert (Hd31 : (t_depth ts <= 31)%nat) by (pose proof INV as [(LEN32 & D32 & _) _]; pose proof STC as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & ((_ & MX) & _)) & _); lia).
assert (LENR : 0 <= pf_len pf < 2^26) by (pose proof STC as (_ & _ & _ & _ & _ & X & _); exact X).
assert (CO0 : 0 <= t_co ts) by (pose proof INV as [(_ & _ & X & _) _]; lia).
assert (SPB : SPV (t_x ts) <= t_co ts) by (unfold SPOK in SP; specialize (SP ltac:(rewrite Est, Hst; reflexivity)); lia).
assert (EM : mredo pf ts = S (mredo pf ts - 1)) by (unfold mredo; rewrite Est, Ess, RK; lia). assert (EB : bredo pf ts = S (Z.to_nat 2816 + (mredo pf ts - 1 + (bx pf ts - Z.to_nat 2816)))).
{ pose proof (bx_ge pf ts ltac:(lia)) as GE9. rewrite Est, Ess, ?Hst in GE9. bres_norm_in GE9. pose proof (BTOK_ge pf). unfold BTOK in *. unfold bredo. rewrite EM at 1. lia. }
rewrite EB in BK.
assert (Ecs : tl_cs l = None).
{ pose proof INV as [_ (_ & LV & _)]. pose proof (LV _ _ Hl) as (_ & SS26 & _ & Md). rewrite Nat.ltb_irrefl, Nat.eqb_refl in Md. destruct Md as (c0 & hn0 & Hmode & CLS0 & _).
rewrite Hst in Hmode. destruct (inf_mode _ _ _ SS26 Hmode) as [-> _]. destruct (tl_cs l); [exfalso; exact CLS0 | reflexivity]. }
eapply (seg_inf_A HIx GA GA_outside GA_pres NEWDBL pf pa q LBc LM FRS payload me lo m md A B ts l cb nb pj sv errv T (t_co ts + 0) v2 ra2 (mredo pf ts - 1 + (bx pf ts - Z.to_nat 2816)));
[exact STC | exact BSL | exact FL0 | exact INV | exact (PBJ_PBOK _ _ _ _ PBK) | exact BK | exact CSTR | exact Hl | exact Hst | exact Hco | exact Hcb | exact SPB | exact S0V | exact RAV | exact HV | exact UWK_dbl | | |].
-
intros m' md' A' B' errv' co' cb' stq r BS gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' F' fc' Hco' Hcb' LEN3 JF9 INV' PBK' BK' FS' FRM'.
eapply (IHR (ts_lvl (ts_set_x ts co' (TS (ts_isd (t_x ts)) stq (Z_to_bv 64 co') (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))) (TL ST_eatws ST_finish r (Some (Sdouble false)) BS 0 [])));
[| exact INV' | | | | | | | | | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)];
destruct ts as [depth levels co pb pbs x obj objs objbs]; unfold ts_set_x, ts_lvl in *; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs] in *.
+ unfold mredo. rewrite (cur_st_upd _ _ l), (cur_ss_upd _ _ l) by exact Hl. cbn [tl_st tl_ss]. change (rank ST_eatws ST_finish) with 6%nat. unfold mredo in M. rewrite Est, Ess, RK in M. unfold mbase in *; cbn [t_co] in *. lia.
+ lia.
+ exact Hcb'.
+ intros E. exfalso. rewrite (cur_st_upd _ _ l) in E by exact Hl. cbn [tl_st] in E. discriminate E.
+ apply (SPOK_upd_plain _ _ l); [exact Hl | reflexivity].
+ eapply (tdepth_ok_upd (TST depth levels co pb pbs x obj objs objbs) l); [exact TD | exact Hl | rewrite Ecs; cbn; lia | exact Hd31 | reflexivity].
+ rewrite (PBS_upd _ _ l) by exact Hl; cbn [tl_st]; pbs_norm. pose proof (PBOK_of_at _ _ _ PBK') as PBK9; cbn [t_co] in PBK9.
eapply (PBJ_attach _ _ (TST depth levels co pb pbs x obj objs objbs) _ l _ _ _ _ _ _ _ _ _ _ _ 9 Hl);
[reflexivity | reflexivity | reflexivity | reflexivity | jl_zin Hst | exact PBK | exact PBK9 | lia | reflexivity | exact JF9 | rewrite ?Hst; jl_arith].
+ eapply BOK_weaken; [| exact BK']. 1: (unfold bredo, bbrk, bloop; apply Nat.add_le_mono; [| bx_tac Hl Hst]). unfold mredo. rewrite (cur_st_upd _ _ l), (cur_ss_upd _ _ l), Est, Ess, RK by exact Hl. cbn [tl_st tl_ss]. change (rank ST_eatws ST_finish) with 6%nat. unfold mbase; cbn [t_co]. lia.
+ apply OBJW_of_NAO. apply (NAO_upd _ _ l); [exact Hl | reflexivity].
-
intros m' md' A' B' errv' co' cb' stq x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' s11' t4' t6' F' fc' Hco' INVW' FS' FRM'.
eapply (kerrmem_of_kout HIx GA GA_outside pf pa q LBc LM FRS payload me lo sv T F0 STC KO _ []);
[exact INVW' | eapply (tdepth_ok_same ts); [reflexivity | reflexivity | reflexivity | exact TD] | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)].
-
intros m' co' cb' stq e x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s5' s7' s10' s11' t4' t6' He Hco' INV'.
eapply (kerrst_of_kout_O HIx GA GA_outside pf pa q LBc LM FRS payload me lo sv T F0 STC KO _ [] e);
[apply (PE_INV_A_W HIx GA); exact INV' | eapply (tdepth_ok_same ts); [reflexivity | reflexivity | reflexivity | exact TD] | destruct He as [-> | ->]; lia | exact FS | exact FRM].
Qed.

Lemma case_string : CASEx ST_string.
Proof.
intros n ts l m md A B cb nb pj errv gp t0 t1 t2 a3 a5 a6 a7 F fc STC INV Hl Hst Hco Hcb NUM SP TD PBK BK OW UTF CSTR FS FRM M KALL KO KE.
clear UWK_dbl.
destruct KALL as (IHL & IHR & IHB & IHA). unfold KLOOP_S in IHL. unfold KREDO_S in IHR. unfold KBRK_S in IHB. unfold KADV_S in IHA.
pose proof (PBS_of ts l Hl) as EPBS. rewrite Hst in EPBS. pbs_norm_in EPBS. rewrite EPBS in PBK.
destruct (PBJ_open _ _ _ _ PBK) as (g & G0 & PBg & Hg & JLg).
assert (PBKg : PBOK m ts (g - t_co ts)) by (unfold PBOK; replace (t_co ts + (g - t_co ts)) with g by lia; exact PBg).
pose proof (cur_st_ofS ts l Hl) as Est. pose proof (cur_ss_ofS ts l Hl) as Ess. pose proof (rank_ge1S (tl_st l) (tl_ss l)) as RG1.
assert (Hd31 : (t_depth ts <= 31)%nat) by (pose proof INV as [(LEN32 & D32 & _) _]; pose proof STC as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & ((_ & MX) & _)) & _); lia).
assert (EM : mredo pf ts = S (mredo pf ts - 1)) by (unfold mredo; rewrite Est, Ess; lia). assert (EB : bredo pf ts = S (Z.to_nat (16 * Z.max 0 (pf_len pf) + 8192) + (mredo pf ts - 1 + (bx pf ts - Z.to_nat (16 * Z.max 0 (pf_len pf) + 8192))))).
{ pose proof (bx_ge pf ts ltac:(lia)) as GE9. rewrite Est, Ess, ?Hst in GE9. bres_norm_in GE9. pose proof (BTOK_ge pf). unfold BTOK in *. unfold bredo. rewrite EM at 1. lia. }
rewrite EB in BK.
assert (Ecs : tl_cs l = None).
{ pose proof INV as [_ (_ & LV & _)]. pose proof (LV _ _ Hl) as (_ & SS26 & _ & Md). rewrite Nat.ltb_irrefl, Nat.eqb_refl in Md. destruct Md as (c0 & hn0 & Hmode & CLS0 & _).
rewrite Hst in Hmode. destruct (string_mode _ _ _ SS26 Hmode) as [-> _]. destruct (tl_cs l); [exfalso; exact CLS0 | reflexivity]. }
eapply (seg_string_A HIx GA GA_outside GA_pres MAPP NEWSTR pf pa q LBc LM FRS payload me lo m md A B ts l cb nb pj sv errv T v2 ra2 (g - t_co ts) (mredo pf ts - 1 + (bx pf ts - Z.to_nat (16 * Z.max 0 (pf_len pf) + 8192))));
[exact STC | exact BSL | exact FL0 | exact INV | exact PBKg | lia | exact BK | exact CSTR | exact Hl | exact Hst | exact Hco | exact Hcb | exact S0V | exact RAV | exact HV | exact UWK_str | | | | |].
-
intros m' md' A' B' pbs' errv' co' cb' pj' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' F' fc' Hco' Hcb' INV' PBK' BK' FS' FRM'.
eapply (IHB (ts_lvl (ts_pbs (ts_set_co ts co') pbs') (TL ST_string_escape ST_string (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))));
[| exact INV' | | exact Hcb' | | | | | | | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)];
destruct ts as [depth levels co pb pbs x obj objs objbs]; unfold ts_pbs, ts_lvl, ts_set_co in *; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs] in *.
+ unfold mbrk, mbase; cbn [t_co]. unfold mredo, mbase in M; cbn [t_co] in M. rewrite Est, Ess in M. lia.
+ lia.
+ rewrite (cur_st_upd _ _ l) by exact Hl. discriminate.
+ apply (SPOK_upd_plain _ _ l); [exact Hl | reflexivity].
+ eapply (tdepth_ok_upd (TST depth levels co pb pbs x obj objs objbs) l); [exact TD | exact Hl | cbn [tl_cs]; pose proof (odep_nonneg (tl_cs l)); lia | exact Hd31 | reflexivity].
+ rewrite (PBS_upd _ _ l) by exact Hl; cbn [tl_st]; pbs_norm. pbj_rsg (TST depth levels co pb pbs x obj objs objbs) l g JLg PBK' Hl Hst.
+ eapply BOK_weaken; [| exact BK']. 1: (unfold bredo, bbrk, bloop; apply Nat.add_le_mono; [| bx_tac Hl Hst]). unfold mbrk, mredo, mbase; cbn [t_co]. rewrite Est, Ess. lia.
+ apply (NAO_upd _ _ l); [exact Hl | reflexivity].
-
intros m' md' A' B' pbs' errv' co' cb' pj' r BS gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' F' fc' Hco' Hcb' LBS PIN9 INV' PBK' BK' FS' FRM'.
eapply (IHB (ts_lvl (ts_pbs (ts_set_co ts co') pbs') (TL ST_eatws ST_finish r (Some (Sstr false)) BS 0 [])));
[| exact INV' | | exact Hcb' | | | | | | | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)];
destruct ts as [depth levels co pb pbs x obj objs objbs]; unfold ts_pbs, ts_lvl, ts_set_co in *; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs] in *.
+ unfold mbrk, mbase; cbn [t_co]. unfold mredo, mbase in M; cbn [t_co] in M. rewrite Est, Ess in M. lia.
+ lia.
+ rewrite (cur_st_upd _ _ l) by exact Hl. discriminate.
+ apply (SPOK_upd_plain _ _ l); [exact Hl | reflexivity].
+ eapply (tdepth_ok_upd (TST depth levels co pb pbs x obj objs objbs) l); [exact TD | exact Hl | rewrite Ecs; cbn; lia | exact Hd31 | reflexivity].
+ rewrite (PBS_upd _ _ l) by exact Hl; cbn [tl_st]; pbs_norm. destruct PIN9 as (len9 & EBS9 & Hlen9).
assert (JF9 : jfresh (Sstr false) BS (6 * Z.max len9 8 + 2)) by (rewrite EBS9; apply jtx_str; lia).
eapply (PBJ_attach_g _ (TST depth levels co pb pbs x obj objs objbs) _ l _ _ _ _ _ _ g _ _ _ _ (6 * Z.max len9 8 + 2) Hl);
[reflexivity | reflexivity | reflexivity | reflexivity | jl_zin Hst | exact JLg | exact PBK' | lia | reflexivity | exact JF9 | rewrite ?Hst; jl_arith].
+ eapply BOK_weaken; [| exact BK']. 1: (unfold bredo, bbrk, bloop; apply Nat.add_le_mono; [| bx_tac Hl Hst]). unfold mbrk, mredo, mbase; cbn [t_co]. rewrite Est, Ess. lia.
+ apply (NAO_upd _ _ l); [exact Hl | reflexivity].
-
intros m' md' A' B' pbs' e co' cb' pj' errv' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' s11' t4' t6' F' fc' Hco' INV' FS' FRM'.
eapply KO; [apply (PE_INV_A_W HIx GA); exact INV' | | | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)].
{ eapply (tdepth_ok_same ts); [reflexivity | reflexivity | reflexivity | exact TD]. }
eapply (JOUT_of_PBJ (pf_len pf) m ts _ _ _ PBK); [lia | reflexivity | reflexivity | intros _; split; reflexivity].
-
intros m' md' A' B' pbs' e co' cb' pj' errv' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' s11' t4' t6' F' fc' Hco' INV' FS' FRM'.
eapply (kerrmem_of_kout HIx GA GA_outside pf pa q LBc LM FRS payload me lo sv T F0 STC KO _ []);
[apply (PE_INV_A_W HIx GA); exact INV' | | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)].
eapply (tdepth_ok_same ts); [reflexivity | reflexivity | reflexivity | exact TD].
-
intros m' md' A' B' pbs' errv' co' cb' pj' x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s10' s11' t3' t4' t5' t6' F' fc' Hco' INVW' FS' FRM'.
eapply (KE (ts_pbs (ts_set_co ts co') pbs') [] 16); [exact INVW' | | lia | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)].
eapply (tdepth_ok_same ts); [reflexivity | reflexivity | reflexivity | exact TD].
Qed.

Lemma case_ofield : CASEx ST_ofield.
Proof.
intros n ts l m md A B cb nb pj errv gp t0 t1 t2 a3 a5 a6 a7 F fc STC INV Hl Hst Hco Hcb NUM SP TD PBK BK OW UTF CSTR FS FRM M KALL KO KE.
clear UWK_dbl UWK_str.
destruct KALL as (IHL & IHR & IHB & IHA). unfold KLOOP_S in IHL. unfold KREDO_S in IHR. unfold KBRK_S in IHB. unfold KADV_S in IHA.
pose proof (PBS_of ts l Hl) as EPBS. rewrite Hst in EPBS. pbs_norm_in EPBS. rewrite EPBS in PBK.
destruct (PBJ_open _ _ _ _ PBK) as (g & G0 & PBg & Hg & JLg).
assert (PBKg : PBOK m ts (g - t_co ts)) by (unfold PBOK; replace (t_co ts + (g - t_co ts)) with g by lia; exact PBg).
pose proof (cur_st_ofS ts l Hl) as Est. pose proof (cur_ss_ofS ts l Hl) as Ess. pose proof (rank_ge1S (tl_st l) (tl_ss l)) as RG1.
assert (Hd31 : (t_depth ts <= 31)%nat) by (pose proof INV as [(LEN32 & D32 & _) _]; pose proof STC as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & ((_ & MX) & _)) & _); lia).
assert (EM : mredo pf ts = S (mredo pf ts - 1)) by (unfold mredo; rewrite Est, Ess; lia). assert (EB : bredo pf ts = S (Z.to_nat (16 * Z.max 0 (pf_len pf) + 8192) + (mredo pf ts - 1 + (bx pf ts - Z.to_nat (16 * Z.max 0 (pf_len pf) + 8192))))).
{ pose proof (bx_ge pf ts ltac:(lia)) as GE9. rewrite Est, Ess, ?Hst in GE9. bres_norm_in GE9. pose proof (BTOK_ge pf). unfold BTOK in *. unfold bredo. rewrite EM at 1. lia. }
rewrite EB in BK.
eapply (seg_ofield_A HIx GA GA_outside GA_pres MAPP pf pa q LBc LM FRS payload me lo m md A B ts l cb nb pj sv errv T v2 ra2 (g - t_co ts) (mredo pf ts - 1 + (bx pf ts - Z.to_nat (16 * Z.max 0 (pf_len pf) + 8192))));
[exact STC | exact BSL | exact FL0 | exact INV | exact PBKg | lia | exact BK | exact CSTR | exact Hl | exact Hst | exact Hco | exact Hcb | exact S0V | exact RAV | exact HV | exact UWK_dup | | | | |].
-
intros m' md' A' B' pbs' errv' co' cb' pj' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' F' fc' Hco' Hcb' INV' PBK' BK' FS' FRM'.
eapply (IHB (ts_lvl (ts_pbs (ts_set_co ts co') pbs') (TL ST_string_escape ST_ofield (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))));
[| exact INV' | | exact Hcb' | | | | | | | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)];
destruct ts as [depth levels co pb pbs x obj objs objbs]; unfold ts_pbs, ts_lvl, ts_set_co in *; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs] in *.
+ unfold mbrk, mbase; cbn [t_co]. unfold mredo, mbase in M; cbn [t_co] in M. rewrite Est, Ess in M. lia.
+ lia.
+ rewrite (cur_st_upd _ _ l) by exact Hl. discriminate.
+ apply (SPOK_upd_plain _ _ l); [exact Hl | reflexivity].
+ eapply (tdepth_ok_upd (TST depth levels co pb pbs x obj objs objbs) l); [exact TD | exact Hl | cbn [tl_cs]; pose proof (odep_nonneg (tl_cs l)); lia | exact Hd31 | reflexivity].
+ rewrite (PBS_upd _ _ l) by exact Hl; cbn [tl_st]; pbs_norm. pbj_rsg (TST depth levels co pb pbs x obj objs objbs) l g JLg PBK' Hl Hst.
+ eapply BOK_weaken; [| exact BK']. 1: (unfold bredo, bbrk, bloop; apply Nat.add_le_mono; [| bx_tac Hl Hst]). unfold mbrk, mredo, mbase; cbn [t_co]. rewrite Est, Ess. lia.
+ apply (NAO_upd _ _ l); [exact Hl | reflexivity].
-
intros m' md' A' B' pbs' errv' co' cb' pj' r nn gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' F' fc' Hco' Hcb' Hr PIN9 INV' PBK' BK' FS' FRM'.
eapply (IHB (ts_lvl (ts_pbs (ts_set_co ts co') pbs') (TL ST_eatws ST_ofend (tl_cur l) (tl_cs l) (tl_cbs l) r [(r, nn)])));
[| exact INV' | | exact Hcb' | | | | | | | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)];
destruct ts as [depth levels co pb pbs x obj objs objbs]; unfold ts_pbs, ts_lvl, ts_set_co in *; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs] in *.
+ unfold mbrk, mbase; cbn [t_co]. unfold mredo, mbase in M; cbn [t_co] in M. rewrite Est, Ess in M. lia.
+ lia.
+ rewrite (cur_st_upd _ _ l) by exact Hl. discriminate.
+ apply (SPOK_upd_plain _ _ l); [exact Hl | reflexivity].
+ eapply (tdepth_ok_upd (TST depth levels co pb pbs x obj objs objbs) l); [exact TD | exact Hl | cbn [tl_cs]; pose proof (odep_nonneg (tl_cs l)); lia | exact Hd31 | reflexivity].
+ rewrite (PBS_upd _ _ l) by exact Hl; cbn [tl_st]; pbs_norm.
eapply (PBJ_name_g _ (TST depth levels co pb pbs x obj objs objbs) _ l _ _ _ _ g _ _ _ _ Hl);
[reflexivity | reflexivity | reflexivity | reflexivity | jl_zin Hst | exact JLg | exact PBK' | lia | reflexivity | rewrite ?Hst; unfold key_w; jl_arith].
+ eapply BOK_weaken; [| exact BK']. 1: (unfold bredo, bbrk, bloop; apply Nat.add_le_mono; [| bx_tac Hl Hst]). unfold mbrk, mredo, mbase; cbn [t_co]. rewrite Est, Ess. lia.
+ apply (NAO_upd _ _ l); [exact Hl | reflexivity].
-
intros m' md' A' B' pbs' e co' cb' pj' errv' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' s11' t4' t6' F' fc' Hco' INV' FS' FRM'.
eapply KO; [apply (PE_INV_A_W HIx GA); exact INV' | | | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)].
{ eapply (tdepth_ok_same ts); [reflexivity | reflexivity | reflexivity | exact TD]. }
eapply (JOUT_of_PBJ (pf_len pf) m ts _ _ _ PBK); [lia | reflexivity | reflexivity | intros _; split; reflexivity].
-
intros m' md' A' B' pbs' e co' cb' pj' errv' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' s11' t4' t6' F' fc' Hco' INV' FS' FRM'.
eapply (kerrmem_of_kout HIx GA GA_outside pf pa q LBc LM FRS payload me lo sv T F0 STC KO _ []);
[apply (PE_INV_A_W HIx GA); exact INV' | | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)].
eapply (tdepth_ok_same ts); [reflexivity | reflexivity | reflexivity | exact TD].
-
intros m' md' A' B' pbs' errv' co' cb' pj' x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s10' s11' t3' t4' t5' t6' F' fc' Hco' INVW' FS' FRM'.
eapply (KE (ts_pbs (ts_set_co ts co') pbs') [] 16); [exact INVW' | | lia | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)].
eapply (tdepth_ok_same ts); [reflexivity | reflexivity | reflexivity | exact TD].
Qed.

Lemma euni_saved : forall ss c hn, 0 <= ss <= 26 -> lvl_mode ST_escape_unicode ss = Some (c, hn) ->
ss <> ST_number /\ zin ss [ST_null; ST_boolean; ST_inf] = false /\ zin ss [ST_array_add; ST_ovadd] = false
/\ zin ss [ST_string_escape; ST_escape_unicode; ST_esc_need_escape; ST_esc_need_u] = false /\ ss <> ST_finish.
Proof.
intros ss c hn R H. enum_z R ss; vm_compute in H; try discriminate H;
(split; [cbv; discriminate|]); (split; [reflexivity|]); (split; [reflexivity|]); (split; [reflexivity | cbv; discriminate]).
Qed.

Lemma case_euni : CASEx ST_escape_unicode.
Proof.
intros n ts l m md A B cb nb pj errv gp t0 t1 t2 a3 a5 a6 a7 F fc STC INV Hl Hst Hco Hcb NUM SP TD PBK BK OW UTF CSTR FS FRM M KALL KO KE.
clear S0V RAV HV UWK_dbl UWK_str UWK_dup.
destruct KALL as (IHL & IHR & IHB & IHA). unfold KBRK_S in IHB.
pose proof INV as [(LEN32 & D32 & _) (_ & LV & _)]. pose proof (LV _ _ Hl) as (ST26 & SS26 & _ & Md).
rewrite Nat.ltb_irrefl, Nat.eqb_refl in Md. destruct Md as (c0 & hn0 & Hmode & _). rewrite Hst in Hmode.
destruct (euni_saved (tl_ss l) c0 hn0 SS26 Hmode) as (SSn & SSZ & SSA & SSP & SSF). pose proof (PBSst_plain_range (tl_ss l) SSP) as SSPB.
pose proof (cur_st_ofS ts l Hl) as Est. pose proof (cur_ss_ofS ts l Hl) as Ess. pose proof (rank_ge1S (tl_st l) (tl_ss l)) as RG1.
assert (EPBS : PBS ts = -2) by (unfold PBS; rewrite Est, Hst; reflexivity). rewrite EPBS in PBK.
destruct (PBJ_open _ _ _ _ PBK) as (g & G0 & PBg & Hg & JLg).
assert (PBKg : PBOK m ts (g - t_co ts)) by (unfold PBOK; replace (t_co ts + (g - t_co ts)) with g by lia; exact PBg).
assert (JSS : jpi0 (tl_ss l) <= 30) by (apply (esc_ss_pi ST_escape_unicode (tl_ss l) c0 hn0); [reflexivity | exact SS26 | exact Hmode]).
destruct (proj2 OW ltac:(rewrite Est, Hst; reflexivity)) as [SP0 UC0]. unfold UCSV in UC0.
assert (Hd31 : (t_depth ts <= 31)%nat) by (pose proof STC as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & ((_ & MX) & _)) & _); lia).
eapply (seg_euni_A HIx GA GA_outside GA_pres MAPP pf pa q LBc LM FRS payload me lo m md A B ts l cb nb pj sv errv T (g - t_co ts) (bredo pf ts));
[exact STC | exact BSL | exact FL0 | exact INV | exact PBKg | lia | exact BK | exact CSTR | exact Hl | exact Hst | exact Hco | exact Hcb | exact SP0 | exact UC0 | exact SSA | rewrite <- UTFR; exact UTF | | | |].
-
intros m' md' A' B' pbs' errv' cb' pj' stq uq hq gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' F' fc' Hco' Hcb' INV' PBK' BK' FS' FRM'.
eapply (IHB (ts_lvl (ts_pbs (ts_set_x ts (t_co ts + 3) (TS (ts_isd (t_x ts)) stq (Z_to_bv 64 (t_co ts + 3)) (ts_err (t_x ts)) uq hq (ts_quote (t_x ts)))) pbs')
(TL (tl_ss l) (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))));
[| exact INV' | | exact Hcb' | | | | | | | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)];
destruct ts as [depth levels co pb pbs x obj objs objbs]; unfold ts_pbs, ts_lvl, ts_set_x in *; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs] in *.
+ unfold mbrk, mbase; cbn [t_co]. unfold mredo, mbase in M; cbn [t_co] in M. rewrite Est, Ess in M. lia.
+ exact Hco'.
+ rewrite (cur_st_upd _ _ l) by exact Hl. exact SSn.
+ apply (SPOK_upd_plain _ _ l); [exact Hl | exact SSZ].
+ eapply (tdepth_ok_upd (TST depth levels co pb pbs x obj objs objbs) l); [exact TD | exact Hl | cbn [tl_cs]; pose proof (odep_nonneg (tl_cs l)); lia | exact Hd31 | exact SSA].
+ rewrite (PBS_upd _ _ l) by exact Hl; cbn [tl_st]. pose proof (PBOK_of_at _ _ _ PBK') as PBK9; cbn [t_co] in PBK9. pbj_rsg (TST depth levels co pb pbs x obj objs objbs) l g JLg PBK9 Hl Hst.
+ eapply BOK_weaken; [| apply (BOK_lvl_restate pf pa (TST depth levels (co + 3) pb pbs' _ obj objs objbs) B' _ l (tl_ss l) (tl_ss l) Hl); [| exact BK']]. 1: (unfold bredo, bbrk, bloop; apply Nat.add_le_mono; [| bx_tac Hl Hst]).
* unfold mbrk, mredo, mbase; cbn [t_co]. lia.
* intros CL. exfalso. unfold lvl_closed in CL. apply andb_true_iff in CL as [CL _]. apply Z.eqb_eq in CL. exact (SSF CL).
+ apply (NAO_upd2 _ _ l); [exact Hl | exact SSA | exact SSP].
-
intros m' md' A' B' pbs' errv' cb' hq gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' F' fc' Hco' Hcb' INV' PBK' BK' FS' FRM'.
eapply (IHB (ts_lvl (ts_pbs (ts_set_x ts (t_co ts + 3) (TS (ts_isd (t_x ts)) (Z_to_bv 64 0) (Z_to_bv 64 (t_co ts + 3)) (ts_err (t_x ts)) (Z_to_bv 64 0) hq (ts_quote (t_x ts)))) pbs')
(TL ST_esc_need_escape (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))));
[| exact INV' | | exact Hcb' | | | | | | | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)];
destruct ts as [depth levels co pb pbs x obj objs objbs]; unfold ts_pbs, ts_lvl, ts_set_x in *; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs] in *.
+ unfold mbrk, mbase; cbn [t_co]. unfold mredo, mbase in M; cbn [t_co] in M. rewrite Est, Ess in M. lia.
+ exact Hco'.
+ rewrite (cur_st_upd _ _ l) by exact Hl. discriminate.
+ apply (SPOK_upd_plain _ _ l); [exact Hl | reflexivity].
+ eapply (tdepth_ok_upd (TST depth levels co pb pbs x obj objs objbs) l); [exact TD | exact Hl | cbn [tl_cs]; pose proof (odep_nonneg (tl_cs l)); lia | exact Hd31 | reflexivity].
+ match goal with |- PBJ _ ?t _ _ => assert (E11 : PBS t = -3) by (unfold PBS; rewrite (cur_st_upd _ _ l) by exact Hl; reflexivity); rewrite E11 end.
pose proof (PBOK_of_at _ _ _ PBK') as PBK9; cbn [t_co] in PBK9. pbj_rsg (TST depth levels co pb pbs x obj objs objbs) l g JLg PBK9 Hl Hst.
+ eapply BOK_weaken; [| apply (BOK_lvl_restate pf pa (TST depth levels (co + 3) pb pbs' _ obj objs objbs) B' _ l ST_esc_need_escape (tl_ss l) Hl); [| exact BK']]. 1: (unfold bredo, bbrk, bloop; apply Nat.add_le_mono; [| bx_tac Hl Hst]).
* unfold mbrk, mredo, mbase; cbn [t_co]. lia.
* intros CL. exfalso. unfold lvl_closed in CL. apply andb_true_iff in CL as [CL _]. apply Z.eqb_eq in CL. exact (SSF CL).
+ apply (NAO_upd_eu _ _ l); [exact Hl | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity].
-
intros m' md' A' B' pbs' errv' co' cb' pj' stq uq hq e x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s7' s11' t4' t6' F' fc' Hco' INV' FS' FRM'.
eapply KO; [apply (PE_INV_A_W HIx GA); exact INV' | | | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)].
{ eapply (tdepth_ok_same ts); [reflexivity | reflexivity | reflexivity | exact TD]. }
eapply (JOUT_of_PBJ (pf_len pf) m ts _ _ _ PBK); [lia | reflexivity | reflexivity | intros _; split; reflexivity].
-
intros m' md' A' B' pbs' errv' co' cb' stq uq hq x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s10' s11' t3' t4' t5' t6' F' fc' Hco' INV' FS' FRM'.
eapply (KE _ [] 16); [apply (PE_INV_A_W HIx GA); exact INV' | | lia | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)].
eapply (tdepth_ok_same ts); [reflexivity | reflexivity | reflexivity | exact TD].
Qed.

Hypothesis PARSEI : parse_i64_A_stmt HIx 0xa39f8.
Hypothesis PARSEU : parse_i64_A_stmt HIx 0xa3c68.
Hypothesis STRTOD : strtod_A_stmt HIx.
Hypothesis NEWINT : jo_new_int_A_stmt HIx 0x9c330.
Hypothesis NEWUINT : jo_new_int_A_stmt HIx 0x9c9d4.
Hypothesis NEWDBLS : new_double_s_A_stmt HIx.
Hypothesis DSL : 0 <= pa_dslack pa.
Hypothesis FRN : Z.of_nat (length FRS) + 2 < 4096.
Hypothesis UWK_dbls : uw_ok A4L (hl_malloc A4H) (Z_to_bv 64 0x9daec) (UWfp ra2 v2).
Lemma case_number : CASEx ST_number.
Proof.
intros n ts l m md A B cb nb pj errv gp t0 t1 t2 a3 a5 a6 a7 F fc STC INV Hl Hst Hco Hcb NUM SP TD PBK BK OW UTF CSTR FS FRM M KALL KO KE.
clear UWK_dbl UWK_str UWK_dup.
destruct KALL as (IHL & IHR & IHB & IHA). unfold KLOOP_S in IHL. unfold KREDO_S in IHR. unfold KBRK_S in IHB. unfold KADV_S in IHA.
pose proof (cur_st_ofS ts l Hl) as Est. pose proof (cur_ss_ofS ts l Hl) as Ess.
assert (RK : rank (tl_st l) (tl_ss l) = 8%nat) by (rewrite Hst; reflexivity).
assert (Hd31 : (t_depth ts <= 31)%nat) by (pose proof INV as [(LEN32 & D32 & _) _]; pose proof STC as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & ((_ & MX) & _)) & _); lia).
assert (CO0 : 0 <= t_co ts) by (pose proof INV as [(_ & _ & X & _) _]; lia).
assert (EM : mredo pf ts = S (mredo pf ts - 1)) by (unfold mredo; rewrite Est, Ess, RK; lia). assert (EB : bredo pf ts = S (Z.to_nat (16 * Z.max 0 (pf_len pf) + 8192) + (mredo pf ts - 1 + (bx pf ts - Z.to_nat (16 * Z.max 0 (pf_len pf) + 8192))))).
{ pose proof (bx_ge pf ts ltac:(lia)) as GE9. rewrite Est, Ess, ?Hst in GE9. bres_norm_in GE9. pose proof (BTOK_ge pf). unfold BTOK in *. unfold bredo. rewrite EM at 1. lia. }
rewrite EB in BK.
assert (NUMC : pbufc asegs m (t_pbs ts) (t_pb ts) []) by (apply NUM; rewrite Est; exact Hst).
assert (FRN' : Z.of_nat (length FRS) + 1 < 4096) by (clear - FRN; lia).
eapply (seg_number_A HIx GA GA_outside GA_pres MAPP PARSEI PARSEU STRTOD NEWINT NEWUINT NEWDBLS pf pa q LBc LM FRS payload me lo m md A B ts l cb nb pj sv errv T v2 ra2 (mredo pf ts - 1 + (bx pf ts - Z.to_nat (16 * Z.max 0 (pf_len pf) + 8192))));
[exact STC | exact BSL | exact DSL | exact FL0 | exact FRN' | exact INV | exact NUMC | exact BK | exact CSTR | exact Hl | exact Hst | exact Hco | exact Hcb | exact FRM | exact S0V | exact RAV | exact HV | exact UWK_dbls | | | |].
-
intros m' md' A' B' pbs' errv' co' cb' isdq pj' r sh BS gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' F' fc' Hco' Hcb' LBS JF Hsh INV' PBK' BK' FS' FRM'.
eapply (IHR (ts_lvl (ts_pbs (ts_set_x ts co' (TS isdq (ts_stpos (t_x ts)) (Z_to_bv 64 co') (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))) pbs') (TL ST_eatws ST_finish r (Some sh) BS 0 [])));
[| exact INV' | | | | | | | | | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)];
destruct ts as [depth levels co pb pbs x obj objs objbs]; unfold ts_pbs, ts_set_x, ts_lvl in *; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs] in *.
+ unfold mredo. rewrite (cur_st_upd _ _ l), (cur_ss_upd _ _ l) by exact Hl. cbn [tl_st tl_ss]. change (rank ST_eatws ST_finish) with 6%nat. unfold mredo in M. rewrite Est, Ess, RK in M. unfold mbase in *; cbn [t_co] in *. lia.
+ lia.
+ exact Hcb'.
+ intros E. exfalso. rewrite (cur_st_upd _ _ l) in E by exact Hl. cbn [tl_st] in E. discriminate E.
+ apply (SPOK_upd_plain _ _ l); [exact Hl | reflexivity].
+ eapply (tdepth_ok_upd (TST depth levels co pb pbs x obj objs objbs) l); [exact TD | exact Hl | pose proof (odep_nonneg (tl_cs l)); destruct Hsh as [-> | ->]; cbn [odep sdepth]; lia | exact Hd31 | reflexivity].
+ rewrite (PBS_upd _ _ l) by exact Hl; cbn [tl_st]; pbs_norm. pose proof (PBOK_of_at _ _ _ PBK') as PBK9; cbn [t_co] in PBK9. destruct JF as (w9 & JF9 & Hw9).
eapply (PBJ_attach _ _ (TST depth levels co pb pbs x obj objs objbs) _ l _ _ _ _ _ _ _ _ _ _ _ w9 Hl);
[reflexivity | reflexivity | reflexivity | reflexivity | jl_zin Hst | exact PBK | exact PBK9 | lia | reflexivity | exact JF9 | rewrite ?Hst; jl_arith].
+ eapply BOK_weaken; [| exact BK']. 1: (unfold bredo, bbrk, bloop; apply Nat.add_le_mono; [| bx_tac Hl Hst]). unfold mredo. rewrite (cur_st_upd _ _ l), (cur_ss_upd _ _ l), Est, Ess, RK by exact Hl. cbn [tl_st tl_ss]. change (rank ST_eatws ST_finish) with 6%nat. unfold mbase; cbn [t_co]. lia.
+ apply OBJW_of_NAO. apply (NAO_upd _ _ l); [exact Hl | reflexivity].
-
intros m' md' A' B' pbs' errv' co' cb' isdq pj' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' F' fc' Hco' Hcb' INV' PBK' BK' FS' FRM'.
assert (BK2 : BOK pf pa (ts_set_x (ts_lvl (ts_pbs (ts_set_x ts co' (TS isdq (ts_stpos (t_x ts)) (Z_to_bv 64 co') (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))) pbs') (TL ST_inf (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) co' (TS isdq (Z_to_bv 64 0) (Z_to_bv 64 co') (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))) B' (S (Z.to_nat (16 * Z.max 0 (pf_len pf) + 8192) + (mredo pf ts - 1 + (bx pf ts - Z.to_nat (16 * Z.max 0 (pf_len pf) + 8192)))))).
{ apply BOK_set_x; [destruct ts as [depth levels co pb pbs x obj objs objbs]; unfold ts_pbs, ts_set_x, ts_lvl; cbn [t_co]; lia |].
apply (BOK_lvl_restate pf pa (ts_pbs (ts_set_x ts co' (TS isdq (ts_stpos (t_x ts)) (Z_to_bv 64 co') (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))) pbs') B' (S (Z.to_nat (16 * Z.max 0 (pf_len pf) + 8192) + (mredo pf ts - 1 + (bx pf ts - Z.to_nat (16 * Z.max 0 (pf_len pf) + 8192))))) l ST_inf (tl_ss l)); [destruct ts as [depth levels co pb pbs x obj objs objbs]; exact Hl | apply lvl_closed_keep; reflexivity | exact BK']. }
eapply (IHR (ts_set_x (ts_lvl (ts_pbs (ts_set_x ts co' (TS isdq (ts_stpos (t_x ts)) (Z_to_bv 64 co') (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))) pbs') (TL ST_inf (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) co' (TS isdq (Z_to_bv 64 0) (Z_to_bv 64 co') (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))));
[| exact INV' | | | | | | | | | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)];
destruct ts as [depth levels co pb pbs x obj objs objbs]; unfold ts_pbs, ts_set_x, ts_lvl in *; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs] in *.
+ unfold mredo. rewrite (cur_st_upd _ _ l), (cur_ss_upd _ _ l) by exact Hl. cbn [tl_st tl_ss]. change (rank ST_inf (tl_ss l)) with 7%nat. unfold mredo in M. rewrite Est, Ess, RK in M. unfold mbase in *; cbn [t_co] in *. lia.
+ lia.
+ exact Hcb'.
+ intros E. exfalso. rewrite (cur_st_upd _ _ l) in E by exact Hl. cbn [tl_st] in E. discriminate E.
+ unfold SPOK. intros _. unfold SPV. cbn [t_x ts_stpos t_co]. rewrite unsigned_lit by lia. rewrite Zmod_0_l. lia.
+ eapply (tdepth_ok_upd (TST depth levels co pb pbs x obj objs objbs) l); [exact TD | exact Hl | cbn [tl_cs]; pose proof (odep_nonneg (tl_cs l)); lia | exact Hd31 | reflexivity].
+ rewrite (PBS_upd _ _ l) by exact Hl; cbn [tl_st]; pbs_norm. pose proof (PBOK_of_at _ _ _ PBK') as PBK9; cbn [t_co] in PBK9. pbj_rs (TST depth levels co pb pbs x obj objs objbs) l PBK PBK9 Hl Hst.
+ eapply BOK_weaken; [| exact BK2]. 1: (unfold bredo; apply bsplit_S; [| bx_tac Hl Hst | pose proof (bx_ge pf (TST depth levels co pb pbs x obj objs objbs) ltac:(cbn [t_co]; lia)) as GE9; rewrite Est, Ess, ?Hst in GE9; bres_norm_in GE9; pose proof (BTOK_ge pf); unfold BTOK in *; lia]). unfold mredo. rewrite (cur_st_upd _ _ l), (cur_ss_upd _ _ l), Est, Ess, RK by exact Hl. cbn [tl_st tl_ss]. change (rank ST_inf (tl_ss l)) with 7%nat. unfold mbase; cbn [t_co]. lia.
+ apply OBJW_of_NAO. apply (NAO_upd _ _ l); [exact Hl | reflexivity].
-
intros m' md' A' B' errv' cb' pj' ts' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' s11' t4' t6' F' fc' E1 E2 E3 INVW' FS' FRM'.
eapply KO; [exact INVW' | eapply (tdepth_ok_same ts); [exact E1 | exact E2 | exact E3 | exact TD] | | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)].
eapply (JOUT_of_PBJ (pf_len pf) m ts ts' _ _ PBK); [lia | exact E1 | exact E2 | intros Z9; exfalso; rewrite Est, Hst in Z9; discriminate Z9].
-
intros m' md' A' B' errv' cb' pj' ts' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' s11' t4' t6' F' fc' E1 E2 E3 INVW' FS' FRM'.
eapply (kerrmem_of_kout HIx GA GA_outside pf pa q LBc LM FRS payload me lo sv T F0 STC KO ts' []);
[exact INVW' | eapply (tdepth_ok_same ts); [exact E1 | exact E2 | exact E3 | exact TD] | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)].
Qed.
End PeSCases4.
End RC__1.
End Mq0.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkMG. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qu4M.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qu4M.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QG8z.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QG8z. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qdyh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qdyh.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qdyh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qdyh.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLbz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLbz. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2Sr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2Sr. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qdyh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qdyh.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QMdR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QMdR.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXfU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXfU.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2Sr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2Sr.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qa8x.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mq9. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mqd. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qiiq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qiiq. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mqf. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4v2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4v2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqf. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSHS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSHS. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Ql4f.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql4f.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1Y6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1Y6.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QrQv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QrQv.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEUF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEUF.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdGy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdGy.Mqc. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWrz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWrz.Mq5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYZ0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYZ0.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QV7s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QV7s.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQ2r.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQ2r.Mq7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QMgr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QMgr.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q63E.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q63E.Mqg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4xt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4xt. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QK82.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QK82.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6oO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6oO.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q63E.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q63E.Mqh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWXt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWXt. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q63E.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q63E.Mqc. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qt1H.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qt1H.Mq6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQMn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQMn. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qitz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qitz. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qeia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qeia.Mq7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1SX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1SX. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qvmy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qvmy. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYZ0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYZ0.Mq5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJZd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJZd.Mqb. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QW22.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QW22.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QV7s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QV7s.Mq5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUop_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUop_c1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc5u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc5u. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QAzu.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QAzu.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6vt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6vt.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2EX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2EX. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdGy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdGy.Mqa. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q63E.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q63E.Mqb. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QV7s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QV7s.Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section PeSCases4B.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_outside : forall m m' W, GA m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= hl_img_lo A4H \/ hl_img_hi A4H <= fst iv) W -> GA m'.
Hypothesis GA_pres : forall LB SP m m', heap_pres A4H LB SP m m' -> GA m -> GA m'.
Hypothesis MAPP : memappend_A_stmt2 HIx.
Hypothesis ISTRNCMP : istrncmp_spec_U.
Hypothesis ISTRNCASECMP : istrncasecmp_spec_U.
Hypothesis NEWDBL : jo_new_double_A_stmt HIx.
Hypothesis NEWBOOL : jo_new_boolean_A_stmt HIx.
Hypothesis NEWSTR : jo_new_string_len_A_stmt HIx.
Variables (pf : pe_fix) (pa : pe_fixA) (q : Z) (LBc LM : list blk) (FRS : list frame) (payload : list byte)
(me : word -> option byte) (lo : Z) (sv : pe_saved) (T : TSet) (F0 : bvmap 5 word) (utf8rep : list byte).
Hypothesis BSL : 0 <= pa_bslack pa.
Hypothesis FL0 : pf_fl pf = 0.
Hypothesis UTFR : utf8rep = Qa8x.Mq3.utf8rep.
Variables (v2 ra2 : Z).
Hypothesis S0V : pe_s0 sv = Z_to_bv 64 v2.
Hypothesis RAV : pe_ra sv = Z_to_bv 64 ra2.
Hypothesis HV : (v2 < alloc_ceiling \/ v2 mod 8 <> 0 \/ v2 <= pa_sp0 pa \/ hiA_top A4L HIx - 16 <= v2) /\ 0 <= v2 < 2^64.
Hypothesis UWK_dbl : uw_ok A4L (hl_malloc A4H) (Z_to_bv 64 0x9f3fc) (UWfp ra2 v2).
Hypothesis UWK_str : uw_ok A4L (hl_malloc A4H) (Z_to_bv 64 0xa00d4) (UWfp ra2 v2).
Hypothesis UWK_dup : uw_ok A4L (hl_strdup A4L) (Z_to_bv 64 0x975cc) (UWfp ra2 v2).
Notation CASEx := (CASE_S HIx GA pf pa q LBc LM FRS payload me lo sv T F0 utf8rep).

Lemma case_null : CASEx ST_null.
Proof.
intros n ts l m md A B cb nb pj errv gp t0 a5 a7 s3 s6 s7 s9 s11 t3 t4 t5 t6 F fc STC INV Hl Hst Hco Hcb NUM SP TD PBK BK OW UTF CSTR FS FRM M KALL KO KE.
destruct KALL as (IHL & IHR & IHB & IHA). unfold KLOOP_S in IHL. unfold KREDO_S in IHR. unfold KBRK_S in IHB. unfold KADV_S in IHA.
pose proof (PBS_of ts l Hl) as EPBS. rewrite Hst in EPBS. pbs_norm_in EPBS. rewrite EPBS in PBK.
pose proof (cur_st_ofS ts l Hl) as Est. pose proof (cur_ss_ofS ts l Hl) as Ess.
assert (RK : rank (tl_st l) (tl_ss l) = 7%nat) by (rewrite Hst; reflexivity).
assert (Hd31 : (t_depth ts <= 31)%nat) by (pose proof INV as [(LEN32 & D32 & _) _]; pose proof STC as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & ((_ & MX) & _)) & _); lia).
assert (LENR : 0 <= pf_len pf < 2^26) by (pose proof STC as (_ & _ & _ & _ & _ & X & _); exact X).
assert (CO0 : 0 <= t_co ts) by (pose proof INV as [(_ & _ & X & _) _]; lia).
assert (SPB : SPV (t_x ts) <= t_co ts) by (unfold SPOK in SP; specialize (SP ltac:(rewrite Est, Hst; reflexivity)); lia).
assert (SP0' : 0 <= SPV (t_x ts)) by (unfold SPV; apply Z.mod_pos_bound; lia).
assert (SPR : 0 <= SPV (t_x ts) + 1 < 2^32) by lia.
assert (EM : mredo pf ts = S (mredo pf ts - 1)) by (unfold mredo; rewrite Est, Ess, RK; lia). assert (EB : bredo pf ts = S (Z.to_nat 2816 + (mredo pf ts - 1 + (bx pf ts - Z.to_nat 2816)))).
{ pose proof (bx_ge pf ts ltac:(lia)) as GE9. rewrite Est, Ess, ?Hst in GE9. bres_norm_in GE9. pose proof (BTOK_ge pf). unfold BTOK in *. unfold bredo. rewrite EM at 1. lia. }
rewrite EB in BK.
assert (Ecs : tl_cs l = None).
{ pose proof INV as [_ (_ & LV & _)]. pose proof (LV _ _ Hl) as (_ & SS26 & _ & Md). rewrite Nat.ltb_irrefl, Nat.eqb_refl in Md. destruct Md as (c0 & hn0 & Hmode & CLS0 & _).
rewrite Hst in Hmode. destruct (null_mode _ _ _ SS26 Hmode) as [-> _]. destruct (tl_cs l); [exfalso; exact CLS0 | reflexivity]. }
eapply (seg_null_B HIx GA GA_outside GA_pres MAPP ISTRNCMP ISTRNCASECMP NEWDBL pf pa q LBc LM FRS payload me lo m md A B ts l cb nb pj sv errv T v2 ra2 (mredo pf ts - 1 + (bx pf ts - Z.to_nat 2816)));
[exact STC | exact BSL | exact FL0 | exact INV | exact (PBJ_PBOK _ _ _ _ PBK) | exact BK | exact Hl | exact Hst | exact Hco | exact SPB | exact S0V | exact RAV | exact HV | exact UWK_dbl | | | | | |].
-
intros m' md' A' B' pbs' errv' pj' gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' INV' PBK' BK' FS' FRM'.
eapply (IHB (ts_set_x (ts_pbs ts pbs') (t_co ts) (TS (ts_isd (t_x ts)) (Z_to_bv 64 (SPV (t_x ts) + 1)) (ts_choff (t_x ts)) (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))));
[| exact INV' | exact Hco | exact Hcb | | | | | | | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)];
destruct ts as [depth levels co pb pbs x obj objs objbs]; unfold ts_pbs, ts_set_x in *; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs] in *.
+ unfold mbrk, mbase; cbn [t_co]. unfold mredo, mbase in M; cbn [t_co] in M. rewrite Est, Ess, RK in M. lia.
+ unfold cur_st; cbn [t_levels t_depth]. rewrite Hl, Hst. discriminate.
+ unfold SPOK. cbn [t_x t_co]. intros _. unfold SPV at 1. cbn [ts_stpos]. rewrite spv_lit by exact SPR. lia.
+ eapply (tdepth_ok_same (TST depth levels co pb pbs x obj objs objbs)); [reflexivity | reflexivity | reflexivity | exact TD].
+ unfold PBS, cur_st; cbn [t_levels t_depth]. rewrite Hl, Hst. pbs_norm.
eapply (PBJ_keep _ _ (TST depth levels co pb pbs x obj objs objbs)); [reflexivity | reflexivity | reflexivity | reflexivity | exact PBK | exact PBK' | lia | rewrite Est, Hst; reflexivity | cbn [t_co]; lia].
+ eapply BOK_weaken; [| exact BK']. 1: (unfold bredo, bbrk, bloop; apply Nat.add_le_mono; [| bx_tac Hl Hst]). unfold mbrk, mredo, mbase; cbn [t_co]. rewrite Est, Ess, RK. lia.
+ unfold NAO, cur_st; cbn [t_levels t_depth]. rewrite Hl, Hst. reflexivity.
-
intros m' md' A' B' pbs' errv' pj' gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' E4 INV' PBK' BK' FS' FRM'.
eapply (IHR (ts_lvl (ts_pbs ts pbs') (TL ST_eatws ST_finish (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))));
[| exact INV' | exact Hco | exact Hcb | | | | | | | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)];
destruct ts as [depth levels co pb pbs x obj objs objbs]; unfold ts_pbs, ts_lvl in *; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs] in *.
+ unfold mredo. rewrite (cur_st_upd _ _ l), (cur_ss_upd _ _ l) by exact Hl. cbn [tl_st tl_ss]. change (rank ST_eatws ST_finish) with 6%nat. unfold mredo in M. rewrite Est, Ess, RK in M. unfold mbase in *; cbn [t_co] in *. lia.
+ intros E. exfalso. rewrite (cur_st_upd _ _ l) in E by exact Hl. cbn [tl_st] in E. discriminate E.
+ apply (SPOK_upd_plain _ _ l); [exact Hl | reflexivity].
+ eapply (tdepth_ok_upd (TST depth levels co pb pbs x obj objs objbs) l); [exact TD | exact Hl | cbn [tl_cs]; pose proof (odep_nonneg (tl_cs l)); lia | exact Hd31 | reflexivity].
+ rewrite (PBS_upd _ _ l) by exact Hl; cbn [tl_st]; pbs_norm. pbj_rs (TST depth levels co pb pbs x obj objs objbs) l PBK PBK' Hl Hst.
+ eapply BOK_weaken; [| exact BK']. 1: (unfold bredo, bbrk, bloop; apply Nat.add_le_mono; [| bx_tac Hl Hst]). unfold mredo. rewrite (cur_st_upd _ _ l), (cur_ss_upd _ _ l), Est, Ess, RK by exact Hl. cbn [tl_st tl_ss]. change (rank ST_eatws ST_finish) with 6%nat. unfold mbase; cbn [t_co]. lia.
+ apply OBJW_of_NAO. apply (NAO_upd _ _ l); [exact Hl | reflexivity].
-
intros m' md' A' B' pbs' errv' pj' r BS gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' E3 LEN3 JF9 INV' PBK' BK' FS' FRM'.
eapply (IHR (ts_lvl (ts_pbs ts pbs') (TL ST_eatws ST_finish r (Some (Sdouble false)) BS 0 [])));
[| exact INV' | exact Hco | exact Hcb | | | | | | | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)];
destruct ts as [depth levels co pb pbs x obj objs objbs]; unfold ts_pbs, ts_lvl in *; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs] in *.
+ unfold mredo. rewrite (cur_st_upd _ _ l), (cur_ss_upd _ _ l) by exact Hl. cbn [tl_st tl_ss]. change (rank ST_eatws ST_finish) with 6%nat. unfold mredo in M. rewrite Est, Ess, RK in M. unfold mbase in *; cbn [t_co] in *. lia.
+ intros E. exfalso. rewrite (cur_st_upd _ _ l) in E by exact Hl. cbn [tl_st] in E. discriminate E.
+ apply (SPOK_upd_plain _ _ l); [exact Hl | reflexivity].
+ eapply (tdepth_ok_upd (TST depth levels co pb pbs x obj objs objbs) l); [exact TD | exact Hl | rewrite Ecs; cbn; lia | exact Hd31 | reflexivity].
+ rewrite (PBS_upd _ _ l) by exact Hl; cbn [tl_st]; pbs_norm.
eapply (PBJ_attach _ _ (TST depth levels co pb pbs x obj objs objbs) _ l _ _ _ _ _ _ _ _ _ _ _ 9 Hl);
[reflexivity | reflexivity | reflexivity | reflexivity | jl_zin Hst | exact PBK | exact PBK' | lia | reflexivity | exact JF9 | rewrite ?Hst; jl_arith].
+ eapply BOK_weaken; [| exact BK']. 1: (unfold bredo, bbrk, bloop; apply Nat.add_le_mono; [| bx_tac Hl Hst]). unfold mredo. rewrite (cur_st_upd _ _ l), (cur_ss_upd _ _ l), Est, Ess, RK by exact Hl. cbn [tl_st tl_ss]. change (rank ST_eatws ST_finish) with 6%nat. unfold mbase; cbn [t_co]. lia.
+ apply OBJW_of_NAO. apply (NAO_upd _ _ l); [exact Hl | reflexivity].
-
intros m' md' A' B' errv' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s6' t3' t4' t5' t6' F' fc' INV' FS' FRM'.
eapply (kerrmem_of_kout HIx GA GA_outside pf pa q LBc LM FRS payload me lo sv T F0 STC KO ts []);
[apply (PE_INV_A_W HIx GA); exact INV' | exact TD | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)].
-
intros m' md' A' B' pbs' errv' pj' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' INVW' FS' FRM'.
unfold pe_msO. pose proof (KE (ts_pbs ts pbs') [] 16 m' md' A' B' cb nb pj' errv') as KEx. unfold pe_msE, pe_msO in KEx.
eapply KEx; [exact INVW' | eapply (tdepth_ok_same ts); [reflexivity | reflexivity | reflexivity | exact TD] | lia | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)].
-
intros m' md' A' B' pbs' errv' pj' x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' INV' FS' FRM'.
unfold pe_msX. pose proof (kerr3_of_kout HIx GA GA_outside pf pa q LBc LM FRS payload me lo sv T F0 STC KO (ts_pbs ts pbs') [] 5 m' md' A' B' cb nb pj' errv') as KEx. unfold pe_msX, pe_msO in KEx.
eapply KEx; [apply (PE_INV_A_W HIx GA); exact INV' | eapply (tdepth_ok_same ts); [reflexivity | reflexivity | reflexivity | exact TD] | lia | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)].
Qed.

Lemma case_bool : CASEx ST_boolean.
Proof.
clear S0V RAV HV UWK_dbl.
intros n ts l m md A B cb nb pj errv gp t0 a5 a7 s3 s6 s7 s9 s11 t3 t4 t5 t6 F fc STC INV Hl Hst Hco Hcb NUM SP TD PBK BK OW UTF CSTR FS FRM M KALL KO KE.
destruct KALL as (IHL & IHR & IHB & IHA). unfold KLOOP_S in IHL. unfold KREDO_S in IHR. unfold KBRK_S in IHB. unfold KADV_S in IHA.
pose proof (PBS_of ts l Hl) as EPBS. rewrite Hst in EPBS. pbs_norm_in EPBS. rewrite EPBS in PBK.
pose proof (cur_st_ofS ts l Hl) as Est. pose proof (cur_ss_ofS ts l Hl) as Ess.
assert (RK : rank (tl_st l) (tl_ss l) = 7%nat) by (rewrite Hst; reflexivity).
assert (Hd31 : (t_depth ts <= 31)%nat) by (pose proof INV as [(LEN32 & D32 & _) _]; pose proof STC as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & ((_ & MX) & _)) & _); lia).
assert (LENR : 0 <= pf_len pf < 2^26) by (pose proof STC as (_ & _ & _ & _ & _ & X & _); exact X).
assert (CO0 : 0 <= t_co ts) by (pose proof INV as [(_ & _ & X & _) _]; lia).
assert (SPB : SPV (t_x ts) <= t_co ts) by (unfold SPOK in SP; specialize (SP ltac:(rewrite Est, Hst; reflexivity)); lia).
assert (SP0' : 0 <= SPV (t_x ts)) by (unfold SPV; apply Z.mod_pos_bound; lia).
assert (SPR : 0 <= SPV (t_x ts) + 1 < 2^32) by lia.
assert (EM : mredo pf ts = S (mredo pf ts - 1)) by (unfold mredo; rewrite Est, Ess, RK; lia). assert (EB : bredo pf ts = S (Z.to_nat 2816 + (mredo pf ts - 1 + (bx pf ts - Z.to_nat 2816)))).
{ pose proof (bx_ge pf ts ltac:(lia)) as GE9. rewrite Est, Ess, ?Hst in GE9. bres_norm_in GE9. pose proof (BTOK_ge pf). unfold BTOK in *. unfold bredo. rewrite EM at 1. lia. }
rewrite EB in BK.
assert (Ecs : tl_cs l = None).
{ pose proof INV as [_ (_ & LV & _)]. pose proof (LV _ _ Hl) as (_ & SS26 & _ & Md). rewrite Nat.ltb_irrefl, Nat.eqb_refl in Md. destruct Md as (c0 & hn0 & Hmode & CLS0 & _).
rewrite Hst in Hmode. destruct (bool_mode _ _ _ SS26 Hmode) as [-> _]. destruct (tl_cs l); [exfalso; exact CLS0 | reflexivity]. }
eapply (seg_bool_B HIx GA GA_outside GA_pres MAPP ISTRNCMP ISTRNCASECMP NEWBOOL pf pa q LBc LM FRS payload me lo m md A B ts l cb nb pj sv errv T (mredo pf ts - 1 + (bx pf ts - Z.to_nat 2816)));
[exact STC | exact BSL | exact FL0 | exact INV | exact (PBJ_PBOK _ _ _ _ PBK) | exact BK | exact Hl | exact Hst | exact Hco | exact SPB | | | | | |].
-
intros m' md' A' B' pbs' errv' pj' gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' INV' PBK' BK' FS' FRM'.
eapply (IHB (ts_set_x (ts_pbs ts pbs') (t_co ts) (TS (ts_isd (t_x ts)) (Z_to_bv 64 (SPV (t_x ts) + 1)) (ts_choff (t_x ts)) (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))));
[| exact INV' | exact Hco | exact Hcb | | | | | | | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)];
destruct ts as [depth levels co pb pbs x obj objs objbs]; unfold ts_pbs, ts_set_x in *; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs] in *.
+ unfold mbrk, mbase; cbn [t_co]. unfold mredo, mbase in M; cbn [t_co] in M. rewrite Est, Ess, RK in M. lia.
+ unfold cur_st; cbn [t_levels t_depth]. rewrite Hl, Hst. discriminate.
+ unfold SPOK. cbn [t_x t_co]. intros _. unfold SPV at 1. cbn [ts_stpos]. rewrite spv_lit by exact SPR. lia.
+ eapply (tdepth_ok_same (TST depth levels co pb pbs x obj objs objbs)); [reflexivity | reflexivity | reflexivity | exact TD].
+ unfold PBS, cur_st; cbn [t_levels t_depth]. rewrite Hl, Hst. pbs_norm.
eapply (PBJ_keep _ _ (TST depth levels co pb pbs x obj objs objbs)); [reflexivity | reflexivity | reflexivity | reflexivity | exact PBK | exact PBK' | lia | rewrite Est, Hst; reflexivity | cbn [t_co]; lia].
+ eapply BOK_weaken; [| exact BK']. 1: (unfold bredo, bbrk, bloop; apply Nat.add_le_mono; [| bx_tac Hl Hst]). unfold mbrk, mredo, mbase; cbn [t_co]. rewrite Est, Ess, RK. lia.
+ unfold NAO, cur_st; cbn [t_levels t_depth]. rewrite Hl, Hst. reflexivity.
-
intros m' md' A' B' pbs' errv' pj' r BS gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' E3 LEN3 JF9 INV' PBK' BK' FS' FRM'.
eapply (IHR (ts_lvl (ts_pbs ts pbs') (TL ST_eatws ST_finish r (Some Sbool) BS 0 [])));
[| exact INV' | exact Hco | exact Hcb | | | | | | | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)];
destruct ts as [depth levels co pb pbs x obj objs objbs]; unfold ts_pbs, ts_lvl in *; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs] in *.
+ unfold mredo. rewrite (cur_st_upd _ _ l), (cur_ss_upd _ _ l) by exact Hl. cbn [tl_st tl_ss]. change (rank ST_eatws ST_finish) with 6%nat. unfold mredo in M. rewrite Est, Ess, RK in M. unfold mbase in *; cbn [t_co] in *. lia.
+ intros E. exfalso. rewrite (cur_st_upd _ _ l) in E by exact Hl. cbn [tl_st] in E. discriminate E.
+ apply (SPOK_upd_plain _ _ l); [exact Hl | reflexivity].
+ eapply (tdepth_ok_upd (TST depth levels co pb pbs x obj objs objbs) l); [exact TD | exact Hl | rewrite Ecs; cbn; lia | exact Hd31 | reflexivity].
+ rewrite (PBS_upd _ _ l) by exact Hl; cbn [tl_st]; pbs_norm.
eapply (PBJ_attach _ _ (TST depth levels co pb pbs x obj objs objbs) _ l _ _ _ _ _ _ _ _ _ _ _ 8 Hl);
[reflexivity | reflexivity | reflexivity | reflexivity | jl_zin Hst | exact PBK | exact PBK' | lia | reflexivity | exact JF9 | rewrite ?Hst; jl_arith].
+ eapply BOK_weaken; [| exact BK']. 1: (unfold bredo, bbrk, bloop; apply Nat.add_le_mono; [| bx_tac Hl Hst]). unfold mredo. rewrite (cur_st_upd _ _ l), (cur_ss_upd _ _ l), Est, Ess, RK by exact Hl. cbn [tl_st tl_ss]. change (rank ST_eatws ST_finish) with 6%nat. unfold mbase; cbn [t_co]. lia.
+ apply OBJW_of_NAO. apply (NAO_upd _ _ l); [exact Hl | reflexivity].
-
intros m' md' A' B' pbs' errv' pj' r BS gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' E3 LEN3 JF9 INV' PBK' BK' FS' FRM'.
eapply (IHR (ts_lvl (ts_pbs ts pbs') (TL ST_eatws ST_finish r (Some Sbool) BS 0 [])));
[| exact INV' | exact Hco | exact Hcb | | | | | | | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)];
destruct ts as [depth levels co pb pbs x obj objs objbs]; unfold ts_pbs, ts_lvl in *; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs] in *.
+ unfold mredo. rewrite (cur_st_upd _ _ l), (cur_ss_upd _ _ l) by exact Hl. cbn [tl_st tl_ss]. change (rank ST_eatws ST_finish) with 6%nat. unfold mredo in M. rewrite Est, Ess, RK in M. unfold mbase in *; cbn [t_co] in *. lia.
+ intros E. exfalso. rewrite (cur_st_upd _ _ l) in E by exact Hl. cbn [tl_st] in E. discriminate E.
+ apply (SPOK_upd_plain _ _ l); [exact Hl | reflexivity].
+ eapply (tdepth_ok_upd (TST depth levels co pb pbs x obj objs objbs) l); [exact TD | exact Hl | rewrite Ecs; cbn; lia | exact Hd31 | reflexivity].
+ rewrite (PBS_upd _ _ l) by exact Hl; cbn [tl_st]; pbs_norm.
eapply (PBJ_attach _ _ (TST depth levels co pb pbs x obj objs objbs) _ l _ _ _ _ _ _ _ _ _ _ _ 8 Hl);
[reflexivity | reflexivity | reflexivity | reflexivity | jl_zin Hst | exact PBK | exact PBK' | lia | reflexivity | exact JF9 | rewrite ?Hst; jl_arith].
+ eapply BOK_weaken; [| exact BK']. 1: (unfold bredo, bbrk, bloop; apply Nat.add_le_mono; [| bx_tac Hl Hst]). unfold mredo. rewrite (cur_st_upd _ _ l), (cur_ss_upd _ _ l), Est, Ess, RK by exact Hl. cbn [tl_st tl_ss]. change (rank ST_eatws ST_finish) with 6%nat. unfold mbase; cbn [t_co]. lia.
+ apply OBJW_of_NAO. apply (NAO_upd _ _ l); [exact Hl | reflexivity].
-
intros m' md' A' B' errv' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s6' t3' t4' t5' t6' F' fc' INV' FS' FRM'.
eapply (kerrmem_of_kout HIx GA GA_outside pf pa q LBc LM FRS payload me lo sv T F0 STC KO ts []);
[apply (PE_INV_A_W HIx GA); exact INV' | exact TD | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)].
-
intros m' md' A' B' pbs' errv' pj' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' INVW' FS' FRM'.
unfold pe_msO. pose proof (KE (ts_pbs ts pbs') [] 16 m' md' A' B' cb nb pj' errv') as KEx. unfold pe_msE, pe_msO in KEx.
eapply KEx; [exact INVW' | eapply (tdepth_ok_same ts); [reflexivity | reflexivity | reflexivity | exact TD] | lia | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)].
-
intros m' md' A' B' pbs' errv' pj' x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' INV' FS' FRM'.
unfold pe_msX. pose proof (kerr3_of_kout HIx GA GA_outside pf pa q LBc LM FRS payload me lo sv T F0 STC KO (ts_pbs ts pbs') [] 6 m' md' A' B' cb nb pj' errv') as KEx. unfold pe_msX, pe_msO in KEx.
eapply KEx; [apply (PE_INV_A_W HIx GA); exact INV' | eapply (tdepth_ok_same ts); [reflexivity | reflexivity | reflexivity | exact TD] | lia | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)].
Qed.

Lemma case_string : CASEx ST_string.
Proof.
intros n ts l m md A B cb nb pj errv gp t0 a5 a7 s3 s6 s7 s9 s11 t3 t4 t5 t6 F fc STC INV Hl Hst Hco Hcb NUM SP TD PBK BK OW UTF CSTR FS FRM M KALL KO KE.
clear UWK_dbl.
destruct KALL as (IHL & IHR & IHB & IHA). unfold KLOOP_S in IHL. unfold KREDO_S in IHR. unfold KBRK_S in IHB. unfold KADV_S in IHA.
pose proof (PBS_of ts l Hl) as EPBS. rewrite Hst in EPBS. pbs_norm_in EPBS. rewrite EPBS in PBK.
destruct (PBJ_open _ _ _ _ PBK) as (g & G0 & PBg & Hg & JLg).
assert (PBKg : PBOK m ts (g - t_co ts)) by (unfold PBOK; replace (t_co ts + (g - t_co ts)) with g by lia; exact PBg).
pose proof (cur_st_ofS ts l Hl) as Est. pose proof (cur_ss_ofS ts l Hl) as Ess. pose proof (rank_ge1S (tl_st l) (tl_ss l)) as RG1.
assert (Hd31 : (t_depth ts <= 31)%nat) by (pose proof INV as [(LEN32 & D32 & _) _]; pose proof STC as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & ((_ & MX) & _)) & _); lia).
assert (EM : mredo pf ts = S (mredo pf ts - 1)) by (unfold mredo; rewrite Est, Ess; lia). assert (EB : bredo pf ts = S (Z.to_nat (16 * Z.max 0 (pf_len pf) + 8192) + (mredo pf ts - 1 + (bx pf ts - Z.to_nat (16 * Z.max 0 (pf_len pf) + 8192))))).
{ pose proof (bx_ge pf ts ltac:(lia)) as GE9. rewrite Est, Ess, ?Hst in GE9. bres_norm_in GE9. pose proof (BTOK_ge pf). unfold BTOK in *. unfold bredo. rewrite EM at 1. lia. }
rewrite EB in BK.
assert (Ecs : tl_cs l = None).
{ pose proof INV as [_ (_ & LV & _)]. pose proof (LV _ _ Hl) as (_ & SS26 & _ & Md). rewrite Nat.ltb_irrefl, Nat.eqb_refl in Md. destruct Md as (c0 & hn0 & Hmode & CLS0 & _).
rewrite Hst in Hmode. destruct (string_mode _ _ _ SS26 Hmode) as [-> _]. destruct (tl_cs l); [exfalso; exact CLS0 | reflexivity]. }
eapply (seg_string_B HIx GA GA_outside GA_pres MAPP NEWSTR pf pa q LBc LM FRS payload me lo m md A B ts l cb nb pj sv errv T v2 ra2 (g - t_co ts) (mredo pf ts - 1 + (bx pf ts - Z.to_nat (16 * Z.max 0 (pf_len pf) + 8192))));
[exact STC | exact BSL | exact FL0 | exact INV | exact PBKg | lia | exact BK | exact CSTR | exact Hl | exact Hst | exact Hco | exact Hcb | exact S0V | exact RAV | exact HV | exact UWK_str | | | | |].
-
intros m' md' A' B' pbs' errv' co' cb' pj' gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' Hco' Hcb' INV' PBK' BK' FS' FRM'.
eapply (IHB (ts_lvl (ts_pbs (ts_set_co ts co') pbs') (TL ST_string_escape ST_string (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))));
[| exact INV' | | exact Hcb' | | | | | | | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)];
destruct ts as [depth levels co pb pbs x obj objs objbs]; unfold ts_pbs, ts_lvl, ts_set_co in *; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs] in *.
+ unfold mbrk, mbase; cbn [t_co]. unfold mredo, mbase in M; cbn [t_co] in M. rewrite Est, Ess in M. lia.
+ lia.
+ rewrite (cur_st_upd _ _ l) by exact Hl. discriminate.
+ apply (SPOK_upd_plain _ _ l); [exact Hl | reflexivity].
+ eapply (tdepth_ok_upd (TST depth levels co pb pbs x obj objs objbs) l); [exact TD | exact Hl | cbn [tl_cs]; pose proof (odep_nonneg (tl_cs l)); lia | exact Hd31 | reflexivity].
+ rewrite (PBS_upd _ _ l) by exact Hl; cbn [tl_st]; pbs_norm. pbj_rsg (TST depth levels co pb pbs x obj objs objbs) l g JLg PBK' Hl Hst.
+ eapply BOK_weaken; [| exact BK']. 1: (unfold bredo, bbrk, bloop; apply Nat.add_le_mono; [| bx_tac Hl Hst]). unfold mbrk, mredo, mbase; cbn [t_co]. rewrite Est, Ess. lia.
+ apply (NAO_upd _ _ l); [exact Hl | reflexivity].
-
intros m' md' A' B' pbs' errv' co' cb' pj' r BS gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' Hco' Hcb' LBS PIN9 INV' PBK' BK' FS' FRM'.
eapply (IHB (ts_lvl (ts_pbs (ts_set_co ts co') pbs') (TL ST_eatws ST_finish r (Some (Sstr false)) BS 0 [])));
[| exact INV' | | exact Hcb' | | | | | | | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)];
destruct ts as [depth levels co pb pbs x obj objs objbs]; unfold ts_pbs, ts_lvl, ts_set_co in *; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs] in *.
+ unfold mbrk, mbase; cbn [t_co]. unfold mredo, mbase in M; cbn [t_co] in M. rewrite Est, Ess in M. lia.
+ lia.
+ rewrite (cur_st_upd _ _ l) by exact Hl. discriminate.
+ apply (SPOK_upd_plain _ _ l); [exact Hl | reflexivity].
+ eapply (tdepth_ok_upd (TST depth levels co pb pbs x obj objs objbs) l); [exact TD | exact Hl | rewrite Ecs; cbn; lia | exact Hd31 | reflexivity].
+ rewrite (PBS_upd _ _ l) by exact Hl; cbn [tl_st]; pbs_norm. destruct PIN9 as (len9 & EBS9 & Hlen9).
assert (JF9 : jfresh (Sstr false) BS (6 * Z.max len9 8 + 2)) by (rewrite EBS9; apply jtx_str; lia).
eapply (PBJ_attach_g _ (TST depth levels co pb pbs x obj objs objbs) _ l _ _ _ _ _ _ g _ _ _ _ (6 * Z.max len9 8 + 2) Hl);
[reflexivity | reflexivity | reflexivity | reflexivity | jl_zin Hst | exact JLg | exact PBK' | lia | reflexivity | exact JF9 | rewrite ?Hst; jl_arith].
+ eapply BOK_weaken; [| exact BK']. 1: (unfold bredo, bbrk, bloop; apply Nat.add_le_mono; [| bx_tac Hl Hst]). unfold mbrk, mredo, mbase; cbn [t_co]. rewrite Est, Ess. lia.
+ apply (NAO_upd _ _ l); [exact Hl | reflexivity].
-
intros m' md' A' B' pbs' e co' cb' pj' errv' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' Hco' INV' FS' FRM'.
eapply KO; [apply (PE_INV_A_W HIx GA); exact INV' | | | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)].
{ eapply (tdepth_ok_same ts); [reflexivity | reflexivity | reflexivity | exact TD]. }
eapply (JOUT_of_PBJ (pf_len pf) m ts _ _ _ PBK); [lia | reflexivity | reflexivity | intros _; split; reflexivity].
-
intros m' md' A' B' pbs' e co' cb' pj' errv' gp' t0' t1' t2' a0' a1' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' Hco' INV' FS' FRM'.
eapply (kerrmem2_of_kout HIx GA GA_outside pf pa q LBc LM FRS payload me lo sv T F0 STC KO _ []);
[apply (PE_INV_A_W HIx GA); exact INV' | | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)].
eapply (tdepth_ok_same ts); [reflexivity | reflexivity | reflexivity | exact TD].
-
intros m' md' A' B' pbs' errv' co' cb' pj' x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' Hco' INVW' FS' FRM'.
unfold pe_msX. pose proof (kerr3_of_kout HIx GA GA_outside pf pa q LBc LM FRS payload me lo sv T F0 STC KO (ts_pbs (ts_set_co ts co') pbs') [] 16 m' md' A' B' cb' nb pj' errv') as KEx. unfold pe_msX, pe_msO in KEx.
eapply KEx; [exact INVW' | | lia | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)].
eapply (tdepth_ok_same ts); [reflexivity | reflexivity | reflexivity | exact TD].
Qed.

Lemma case_ofield : CASEx ST_ofield.
Proof.
intros n ts l m md A B cb nb pj errv gp t0 a5 a7 s3 s6 s7 s9 s11 t3 t4 t5 t6 F fc STC INV Hl Hst Hco Hcb NUM SP TD PBK BK OW UTF CSTR FS FRM M KALL KO KE.
clear UWK_dbl UWK_str.
destruct KALL as (IHL & IHR & IHB & IHA). unfold KLOOP_S in IHL. unfold KREDO_S in IHR. unfold KBRK_S in IHB. unfold KADV_S in IHA.
pose proof (PBS_of ts l Hl) as EPBS. rewrite Hst in EPBS. pbs_norm_in EPBS. rewrite EPBS in PBK.
destruct (PBJ_open _ _ _ _ PBK) as (g & G0 & PBg & Hg & JLg).
assert (PBKg : PBOK m ts (g - t_co ts)) by (unfold PBOK; replace (t_co ts + (g - t_co ts)) with g by lia; exact PBg).
pose proof (cur_st_ofS ts l Hl) as Est. pose proof (cur_ss_ofS ts l Hl) as Ess. pose proof (rank_ge1S (tl_st l) (tl_ss l)) as RG1.
assert (Hd31 : (t_depth ts <= 31)%nat) by (pose proof INV as [(LEN32 & D32 & _) _]; pose proof STC as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & ((_ & MX) & _)) & _); lia).
assert (EM : mredo pf ts = S (mredo pf ts - 1)) by (unfold mredo; rewrite Est, Ess; lia). assert (EB : bredo pf ts = S (Z.to_nat (16 * Z.max 0 (pf_len pf) + 8192) + (mredo pf ts - 1 + (bx pf ts - Z.to_nat (16 * Z.max 0 (pf_len pf) + 8192))))).
{ pose proof (bx_ge pf ts ltac:(lia)) as GE9. rewrite Est, Ess, ?Hst in GE9. bres_norm_in GE9. pose proof (BTOK_ge pf). unfold BTOK in *. unfold bredo. rewrite EM at 1. lia. }
rewrite EB in BK.
eapply (seg_ofield_B HIx GA GA_outside GA_pres MAPP pf pa q LBc LM FRS payload me lo m md A B ts l cb nb pj sv errv T v2 ra2 (g - t_co ts) (mredo pf ts - 1 + (bx pf ts - Z.to_nat (16 * Z.max 0 (pf_len pf) + 8192))));
[exact STC | exact BSL | exact FL0 | exact INV | exact PBKg | lia | exact BK | exact CSTR | exact Hl | exact Hst | exact Hco | exact Hcb | exact S0V | exact RAV | exact HV | exact UWK_dup | | | | |].
-
intros m' md' A' B' pbs' errv' co' cb' pj' gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' Hco' Hcb' INV' PBK' BK' FS' FRM'.
eapply (IHB (ts_lvl (ts_pbs (ts_set_co ts co') pbs') (TL ST_string_escape ST_ofield (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))));
[| exact INV' | | exact Hcb' | | | | | | | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)];
destruct ts as [depth levels co pb pbs x obj objs objbs]; unfold ts_pbs, ts_lvl, ts_set_co in *; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs] in *.
+ unfold mbrk, mbase; cbn [t_co]. unfold mredo, mbase in M; cbn [t_co] in M. rewrite Est, Ess in M. lia.
+ lia.
+ rewrite (cur_st_upd _ _ l) by exact Hl. discriminate.
+ apply (SPOK_upd_plain _ _ l); [exact Hl | reflexivity].
+ eapply (tdepth_ok_upd (TST depth levels co pb pbs x obj objs objbs) l); [exact TD | exact Hl | cbn [tl_cs]; pose proof (odep_nonneg (tl_cs l)); lia | exact Hd31 | reflexivity].
+ rewrite (PBS_upd _ _ l) by exact Hl; cbn [tl_st]; pbs_norm. pbj_rsg (TST depth levels co pb pbs x obj objs objbs) l g JLg PBK' Hl Hst.
+ eapply BOK_weaken; [| exact BK']. 1: (unfold bredo, bbrk, bloop; apply Nat.add_le_mono; [| bx_tac Hl Hst]). unfold mbrk, mredo, mbase; cbn [t_co]. rewrite Est, Ess. lia.
+ apply (NAO_upd _ _ l); [exact Hl | reflexivity].
-
intros m' md' A' B' pbs' errv' co' cb' pj' r nn gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' Hco' Hcb' Hr PIN9 INV' PBK' BK' FS' FRM'.
eapply (IHB (ts_lvl (ts_pbs (ts_set_co ts co') pbs') (TL ST_eatws ST_ofend (tl_cur l) (tl_cs l) (tl_cbs l) r [(r, nn)])));
[| exact INV' | | exact Hcb' | | | | | | | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)];
destruct ts as [depth levels co pb pbs x obj objs objbs]; unfold ts_pbs, ts_lvl, ts_set_co in *; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs] in *.
+ unfold mbrk, mbase; cbn [t_co]. unfold mredo, mbase in M; cbn [t_co] in M. rewrite Est, Ess in M. lia.
+ lia.
+ rewrite (cur_st_upd _ _ l) by exact Hl. discriminate.
+ apply (SPOK_upd_plain _ _ l); [exact Hl | reflexivity].
+ eapply (tdepth_ok_upd (TST depth levels co pb pbs x obj objs objbs) l); [exact TD | exact Hl | cbn [tl_cs]; pose proof (odep_nonneg (tl_cs l)); lia | exact Hd31 | reflexivity].
+ rewrite (PBS_upd _ _ l) by exact Hl; cbn [tl_st]; pbs_norm.
eapply (PBJ_name_g _ (TST depth levels co pb pbs x obj objs objbs) _ l _ _ _ _ g _ _ _ _ Hl);
[reflexivity | reflexivity | reflexivity | reflexivity | jl_zin Hst | exact JLg | exact PBK' | lia | reflexivity | rewrite ?Hst; unfold key_w; jl_arith].
+ eapply BOK_weaken; [| exact BK']. 1: (unfold bredo, bbrk, bloop; apply Nat.add_le_mono; [| bx_tac Hl Hst]). unfold mbrk, mredo, mbase; cbn [t_co]. rewrite Est, Ess. lia.
+ apply (NAO_upd _ _ l); [exact Hl | reflexivity].
-
intros m' md' A' B' pbs' e co' cb' pj' errv' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' Hco' INV' FS' FRM'.
eapply KO; [apply (PE_INV_A_W HIx GA); exact INV' | | | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)].
{ eapply (tdepth_ok_same ts); [reflexivity | reflexivity | reflexivity | exact TD]. }
eapply (JOUT_of_PBJ (pf_len pf) m ts _ _ _ PBK); [lia | reflexivity | reflexivity | intros _; split; reflexivity].
-
intros m' md' A' B' pbs' e co' cb' pj' errv' gp' t0' t1' t2' a0' a1' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' Hco' INV' FS' FRM'.
eapply (kerrmem2_of_kout HIx GA GA_outside pf pa q LBc LM FRS payload me lo sv T F0 STC KO _ []);
[apply (PE_INV_A_W HIx GA); exact INV' | | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)].
eapply (tdepth_ok_same ts); [reflexivity | reflexivity | reflexivity | exact TD].
-
intros m' md' A' B' pbs' errv' co' cb' pj' x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' Hco' INVW' FS' FRM'.
unfold pe_msX. pose proof (kerr3_of_kout HIx GA GA_outside pf pa q LBc LM FRS payload me lo sv T F0 STC KO (ts_pbs (ts_set_co ts co') pbs') [] 16 m' md' A' B' cb' nb pj' errv') as KEx. unfold pe_msX, pe_msO in KEx.
eapply KEx; [exact INVW' | | lia | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)].
eapply (tdepth_ok_same ts); [reflexivity | reflexivity | reflexivity | exact TD].
Qed.

Lemma case_inf : CASEx ST_inf.
Proof.
intros n ts l m md A B cb nb pj errv gp t0 a5 a7 s3 s6 s7 s9 s11 t3 t4 t5 t6 F fc STC INV Hl Hst Hco Hcb NUM SP TD PBK BK OW UTF CSTR FS FRM M KALL KO KE.
destruct KALL as (IHL & IHR & IHB & IHA). unfold KLOOP_S in IHL. unfold KREDO_S in IHR. unfold KBRK_S in IHB. unfold KADV_S in IHA.
pose proof (PBS_of ts l Hl) as EPBS. rewrite Hst in EPBS. pbs_norm_in EPBS. rewrite EPBS in PBK.
pose proof (cur_st_ofS ts l Hl) as Est. pose proof (cur_ss_ofS ts l Hl) as Ess.
assert (RK : rank (tl_st l) (tl_ss l) = 7%nat) by (rewrite Hst; reflexivity).
assert (Hd31 : (t_depth ts <= 31)%nat) by (pose proof INV as [(LEN32 & D32 & _) _]; pose proof STC as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & ((_ & MX) & _)) & _); lia).
assert (LENR : 0 <= pf_len pf < 2^26) by (pose proof STC as (_ & _ & _ & _ & _ & X & _); exact X).
assert (CO0 : 0 <= t_co ts) by (pose proof INV as [(_ & _ & X & _) _]; lia).
assert (SPB : SPV (t_x ts) <= t_co ts) by (unfold SPOK in SP; specialize (SP ltac:(rewrite Est, Hst; reflexivity)); lia).
assert (EM : mredo pf ts = S (mredo pf ts - 1)) by (unfold mredo; rewrite Est, Ess, RK; lia). assert (EB : bredo pf ts = S (Z.to_nat 2816 + (mredo pf ts - 1 + (bx pf ts - Z.to_nat 2816)))).
{ pose proof (bx_ge pf ts ltac:(lia)) as GE9. rewrite Est, Ess, ?Hst in GE9. bres_norm_in GE9. pose proof (BTOK_ge pf). unfold BTOK in *. unfold bredo. rewrite EM at 1. lia. }
rewrite EB in BK.
assert (Ecs : tl_cs l = None).
{ pose proof INV as [_ (_ & LV & _)]. pose proof (LV _ _ Hl) as (_ & SS26 & _ & Md). rewrite Nat.ltb_irrefl, Nat.eqb_refl in Md. destruct Md as (c0 & hn0 & Hmode & CLS0 & _).
rewrite Hst in Hmode. destruct (inf_mode _ _ _ SS26 Hmode) as [-> _]. destruct (tl_cs l); [exfalso; exact CLS0 | reflexivity]. }
eapply (seg_inf_B HIx GA GA_outside GA_pres NEWDBL pf pa q LBc LM FRS payload me lo m md A B ts l cb nb pj sv errv T (t_co ts + 0) v2 ra2 (mredo pf ts - 1 + (bx pf ts - Z.to_nat 2816)));
[exact STC | exact BSL | exact FL0 | exact INV | exact (PBJ_PBOK _ _ _ _ PBK) | exact BK | exact CSTR | exact Hl | exact Hst | exact Hco | exact Hcb | exact SPB | exact S0V | exact RAV | exact HV | exact UWK_dbl | | |].
-
intros m' md' A' B' errv' co' cb' stq r BS gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' Hco' Hcb' LEN3 JF9 INV' PBK' BK' FS' FRM'.
eapply (IHR (ts_lvl (ts_set_x ts co' (TS (ts_isd (t_x ts)) stq (Z_to_bv 64 co') (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))) (TL ST_eatws ST_finish r (Some (Sdouble false)) BS 0 [])));
[| exact INV' | | | | | | | | | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)];
destruct ts as [depth levels co pb pbs x obj objs objbs]; unfold ts_set_x, ts_lvl in *; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs] in *.
+ unfold mredo. rewrite (cur_st_upd _ _ l), (cur_ss_upd _ _ l) by exact Hl. cbn [tl_st tl_ss]. change (rank ST_eatws ST_finish) with 6%nat. unfold mredo in M. rewrite Est, Ess, RK in M. unfold mbase in *; cbn [t_co] in *. lia.
+ lia.
+ exact Hcb'.
+ intros E. exfalso. rewrite (cur_st_upd _ _ l) in E by exact Hl. cbn [tl_st] in E. discriminate E.
+ apply (SPOK_upd_plain _ _ l); [exact Hl | reflexivity].
+ eapply (tdepth_ok_upd (TST depth levels co pb pbs x obj objs objbs) l); [exact TD | exact Hl | rewrite Ecs; cbn; lia | exact Hd31 | reflexivity].
+ rewrite (PBS_upd _ _ l) by exact Hl; cbn [tl_st]; pbs_norm. pose proof (PBOK_of_at _ _ _ PBK') as PBK9; cbn [t_co] in PBK9.
eapply (PBJ_attach _ _ (TST depth levels co pb pbs x obj objs objbs) _ l _ _ _ _ _ _ _ _ _ _ _ 9 Hl);
[reflexivity | reflexivity | reflexivity | reflexivity | jl_zin Hst | exact PBK | exact PBK9 | lia | reflexivity | exact JF9 | rewrite ?Hst; jl_arith].
+ eapply BOK_weaken; [| exact BK']. 1: (unfold bredo, bbrk, bloop; apply Nat.add_le_mono; [| bx_tac Hl Hst]). unfold mredo. rewrite (cur_st_upd _ _ l), (cur_ss_upd _ _ l), Est, Ess, RK by exact Hl. cbn [tl_st tl_ss]. change (rank ST_eatws ST_finish) with 6%nat. unfold mbase; cbn [t_co]. lia.
+ apply OBJW_of_NAO. apply (NAO_upd _ _ l); [exact Hl | reflexivity].
-
intros m' md' A' B' errv' co' cb' stq gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' Hco' INVW' FS' FRM'.
unfold pe_msO. pose proof (KE (ts_set_x ts co' (TS (ts_isd (t_x ts)) stq (Z_to_bv 64 co') (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))) [] 16 m' md' A' B' cb' nb pj errv') as KEx. unfold pe_msE, pe_msO in KEx.
eapply KEx; [exact INVW' | eapply (tdepth_ok_same ts); [reflexivity | reflexivity | reflexivity | exact TD] | lia | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)].
-
intros m' co' cb' stq e gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' He Hco' INV'.
unfold pe_msO. pose proof (KE (ts_set_x ts co' (TS (ts_isd (t_x ts)) stq (Z_to_bv 64 co') (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))) [] e m' md A B cb' nb pj errv) as KEx. unfold pe_msE, pe_msO in KEx.
eapply KEx; [apply (PE_INV_A_W HIx GA); exact INV' | eapply (tdepth_ok_same ts); [reflexivity | reflexivity | reflexivity | exact TD] | destruct He as [-> | ->]; lia | exact FS | exact FRM].
Qed.
Lemma euni_saved : forall ss c hn, 0 <= ss <= 26 -> lvl_mode ST_escape_unicode ss = Some (c, hn) ->
ss <> ST_number /\ zin ss [ST_null; ST_boolean; ST_inf] = false /\ zin ss [ST_array_add; ST_ovadd] = false
/\ zin ss [ST_string_escape; ST_escape_unicode; ST_esc_need_escape; ST_esc_need_u] = false /\ ss <> ST_finish.
Proof.
intros ss c hn R H. enum_z R ss; vm_compute in H; try discriminate H;
(split; [cbv; discriminate|]); (split; [reflexivity|]); (split; [reflexivity|]); (split; [reflexivity | cbv; discriminate]).
Qed.

Lemma case_euni : CASEx ST_escape_unicode.
Proof.
intros n ts l m md A B cb nb pj errv gp t0 a5 a7 s3 s6 s7 s9 s11 t3 t4 t5 t6 F fc STC INV Hl Hst Hco Hcb NUM SP TD PBK BK OW UTF CSTR FS FRM M KALL KO KE.
clear S0V RAV HV UWK_dbl UWK_str UWK_dup.
destruct KALL as (IHL & IHR & IHB & IHA). unfold KBRK_S in IHB.
pose proof INV as [(LEN32 & D32 & _) (_ & LV & _)]. pose proof (LV _ _ Hl) as (ST26 & SS26 & _ & Md).
rewrite Nat.ltb_irrefl, Nat.eqb_refl in Md. destruct Md as (c0 & hn0 & Hmode & _). rewrite Hst in Hmode.
destruct (euni_saved (tl_ss l) c0 hn0 SS26 Hmode) as (SSn & SSZ & SSA & SSP & SSF). pose proof (PBSst_plain_range (tl_ss l) SSP) as SSPB.
pose proof (cur_st_ofS ts l Hl) as Est. pose proof (cur_ss_ofS ts l Hl) as Ess. pose proof (rank_ge1S (tl_st l) (tl_ss l)) as RG1.
assert (EPBS : PBS ts = -2) by (unfold PBS; rewrite Est, Hst; reflexivity). rewrite EPBS in PBK.
destruct (PBJ_open _ _ _ _ PBK) as (g & G0 & PBg & Hg & JLg).
assert (PBKg : PBOK m ts (g - t_co ts)) by (unfold PBOK; replace (t_co ts + (g - t_co ts)) with g by lia; exact PBg).
assert (JSS : jpi0 (tl_ss l) <= 30) by (apply (esc_ss_pi ST_escape_unicode (tl_ss l) c0 hn0); [reflexivity | exact SS26 | exact Hmode]).
destruct (proj2 OW ltac:(rewrite Est, Hst; reflexivity)) as [SP0 UC0]. unfold UCSV in UC0.
assert (Hd31 : (t_depth ts <= 31)%nat) by (pose proof STC as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & ((_ & MX) & _)) & _); lia).
eapply (seg_euni_B HIx GA GA_outside GA_pres MAPP pf pa q LBc LM FRS payload me lo m md A B ts l cb nb pj sv errv T (g - t_co ts) (bredo pf ts));
[exact STC | exact BSL | exact FL0 | exact INV | exact PBKg | lia | exact BK | exact CSTR | exact Hl | exact Hst | exact Hco | exact Hcb | exact SP0 | exact UC0 | exact SSA | rewrite <- UTFR; exact UTF | | | | |].
-
intros m' md' A' B' pbs' errv' cb' pj' stq uq hq gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' Hco' Hcb' INV' PBK' BK' FS' FRM'.
eapply (IHB (ts_lvl (ts_pbs (ts_set_x ts (t_co ts + 3) (TS (ts_isd (t_x ts)) stq (Z_to_bv 64 (t_co ts + 3)) (ts_err (t_x ts)) uq hq (ts_quote (t_x ts)))) pbs')
(TL (tl_ss l) (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))));
[| exact INV' | | exact Hcb' | | | | | | | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)];
destruct ts as [depth levels co pb pbs x obj objs objbs]; unfold ts_pbs, ts_lvl, ts_set_x in *; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs] in *.
+ unfold mbrk, mbase; cbn [t_co]. unfold mredo, mbase in M; cbn [t_co] in M. rewrite Est, Ess in M. lia.
+ exact Hco'.
+ rewrite (cur_st_upd _ _ l) by exact Hl. exact SSn.
+ apply (SPOK_upd_plain _ _ l); [exact Hl | exact SSZ].
+ eapply (tdepth_ok_upd (TST depth levels co pb pbs x obj objs objbs) l); [exact TD | exact Hl | cbn [tl_cs]; pose proof (odep_nonneg (tl_cs l)); lia | exact Hd31 | exact SSA].
+ rewrite (PBS_upd _ _ l) by exact Hl; cbn [tl_st]. pose proof (PBOK_of_at _ _ _ PBK') as PBK9; cbn [t_co] in PBK9. pbj_rsg (TST depth levels co pb pbs x obj objs objbs) l g JLg PBK9 Hl Hst.
+ eapply BOK_weaken; [| apply (BOK_lvl_restate pf pa (TST depth levels (co + 3) pb pbs' _ obj objs objbs) B' _ l (tl_ss l) (tl_ss l) Hl); [| exact BK']]. 1: (unfold bredo, bbrk, bloop; apply Nat.add_le_mono; [| bx_tac Hl Hst]).
* unfold mbrk, mredo, mbase; cbn [t_co]. lia.
* intros CL. exfalso. unfold lvl_closed in CL. apply andb_true_iff in CL as [CL _]. apply Z.eqb_eq in CL. exact (SSF CL).
+ apply (NAO_upd2 _ _ l); [exact Hl | exact SSA | exact SSP].
-
intros m' md' A' B' pbs' errv' cb' hq gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' Hco' Hcb' INV' PBK' BK' FS' FRM'.
eapply (IHB (ts_lvl (ts_pbs (ts_set_x ts (t_co ts + 3) (TS (ts_isd (t_x ts)) (Z_to_bv 64 0) (Z_to_bv 64 (t_co ts + 3)) (ts_err (t_x ts)) (Z_to_bv 64 0) hq (ts_quote (t_x ts)))) pbs')
(TL ST_esc_need_escape (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))));
[| exact INV' | | exact Hcb' | | | | | | | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)];
destruct ts as [depth levels co pb pbs x obj objs objbs]; unfold ts_pbs, ts_lvl, ts_set_x in *; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs] in *.
+ unfold mbrk, mbase; cbn [t_co]. unfold mredo, mbase in M; cbn [t_co] in M. rewrite Est, Ess in M. lia.
+ exact Hco'.
+ rewrite (cur_st_upd _ _ l) by exact Hl. discriminate.
+ apply (SPOK_upd_plain _ _ l); [exact Hl | reflexivity].
+ eapply (tdepth_ok_upd (TST depth levels co pb pbs x obj objs objbs) l); [exact TD | exact Hl | cbn [tl_cs]; pose proof (odep_nonneg (tl_cs l)); lia | exact Hd31 | reflexivity].
+ match goal with |- PBJ _ ?t _ _ => assert (E11 : PBS t = -3) by (unfold PBS; rewrite (cur_st_upd _ _ l) by exact Hl; reflexivity); rewrite E11 end.
pose proof (PBOK_of_at _ _ _ PBK') as PBK9; cbn [t_co] in PBK9. pbj_rsg (TST depth levels co pb pbs x obj objs objbs) l g JLg PBK9 Hl Hst.
+ eapply BOK_weaken; [| apply (BOK_lvl_restate pf pa (TST depth levels (co + 3) pb pbs' _ obj objs objbs) B' _ l ST_esc_need_escape (tl_ss l) Hl); [| exact BK']]. 1: (unfold bredo, bbrk, bloop; apply Nat.add_le_mono; [| bx_tac Hl Hst]).
* unfold mbrk, mredo, mbase; cbn [t_co]. lia.
* intros CL. exfalso. unfold lvl_closed in CL. apply andb_true_iff in CL as [CL _]. apply Z.eqb_eq in CL. exact (SSF CL).
+ apply (NAO_upd_eu _ _ l); [exact Hl | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity].
-
intros m' md' A' B' pbs' errv' co' cb' pj' stq uq hq e gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' Hco' INV' FS' FRM'.
eapply KO; [apply (PE_INV_A_W HIx GA); exact INV' | | | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)].
{ eapply (tdepth_ok_same ts); [reflexivity | reflexivity | reflexivity | exact TD]. }
eapply (JOUT_of_PBJ (pf_len pf) m ts _ _ _ PBK); [lia | reflexivity | reflexivity | intros _; split; reflexivity].
-
intros m' md' A' B' pbs' errv' co' cb' stq uq hq gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' Hco' INV' FS' FRM'.
unfold pe_msO. pose proof (KE (ts_pbs (ts_set_x ts co' (TS (ts_isd (t_x ts)) stq (Z_to_bv 64 co') (ts_err (t_x ts)) uq hq (ts_quote (t_x ts)))) pbs') [] 12 m' md' A' B' cb' nb pj errv') as KEx. unfold pe_msE, pe_msO in KEx.
eapply KEx; [apply (PE_INV_A_W HIx GA); exact INV' | eapply (tdepth_ok_same ts); [reflexivity | reflexivity | reflexivity | exact TD] | lia | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)].
-
intros m' md' A' B' pbs' errv' co' cb' stq uq hq x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' Hco' INV' FS' FRM'.
unfold pe_msX. pose proof (kerr3_of_kout HIx GA GA_outside pf pa q LBc LM FRS payload me lo sv T F0 STC KO (ts_pbs (ts_set_x ts co' (TS (ts_isd (t_x ts)) stq (Z_to_bv 64 co') (ts_err (t_x ts)) uq hq (ts_quote (t_x ts)))) pbs') [] 16 m' md' A' B' cb' nb pj errv') as KEx. unfold pe_msX, pe_msO in KEx.
eapply KEx; [apply (PE_INV_A_W HIx GA); exact INV' | eapply (tdepth_ok_same ts); [reflexivity | reflexivity | reflexivity | exact TD] | lia | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)].
Qed.

Hypothesis PARSEI : parse_i64_A_stmt HIx 0xa6060.
Hypothesis PARSEU : parse_i64_A_stmt HIx 0xa62ec.
Hypothesis STRTOD : strtod_A_stmt HIx.
Hypothesis NEWINT : jo_new_int_A_stmt HIx 0x9dbdc.
Hypothesis NEWUINT : jo_new_int_A_stmt HIx 0x9e328.
Hypothesis NEWDBLS : new_double_s_A_stmt HIx.
Hypothesis DSL : 0 <= pa_dslack pa.
Hypothesis FRN : Z.of_nat (length FRS) + 2 < 4096.
Hypothesis UWK_dbls : uw_ok A4L (hl_malloc A4H) (Z_to_bv 64 0x9f57c) (UWfp ra2 v2).
Lemma case_number : CASEx ST_number.
Proof.
intros n ts l m md A B cb nb pj errv gp t0 a5 a7 s3 s6 s7 s9 s11 t3 t4 t5 t6 F fc STC INV Hl Hst Hco Hcb NUM SP TD PBK BK OW UTF CSTR FS FRM M KALL KO KE.
clear UWK_dbl UWK_str UWK_dup.
destruct KALL as (IHL & IHR & IHB & IHA). unfold KLOOP_S in IHL. unfold KREDO_S in IHR. unfold KBRK_S in IHB. unfold KADV_S in IHA.
pose proof (cur_st_ofS ts l Hl) as Est. pose proof (cur_ss_ofS ts l Hl) as Ess.
assert (RK : rank (tl_st l) (tl_ss l) = 8%nat) by (rewrite Hst; reflexivity).
assert (Hd31 : (t_depth ts <= 31)%nat) by (pose proof INV as [(LEN32 & D32 & _) _]; pose proof STC as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & ((_ & MX) & _)) & _); lia).
assert (CO0 : 0 <= t_co ts) by (pose proof INV as [(_ & _ & X & _) _]; lia).
assert (EM : mredo pf ts = S (mredo pf ts - 1)) by (unfold mredo; rewrite Est, Ess, RK; lia). assert (EB : bredo pf ts = S (Z.to_nat (16 * Z.max 0 (pf_len pf) + 8192) + (mredo pf ts - 1 + (bx pf ts - Z.to_nat (16 * Z.max 0 (pf_len pf) + 8192))))).
{ pose proof (bx_ge pf ts ltac:(lia)) as GE9. rewrite Est, Ess, ?Hst in GE9. bres_norm_in GE9. pose proof (BTOK_ge pf). unfold BTOK in *. unfold bredo. rewrite EM at 1. lia. }
rewrite EB in BK.
assert (NUMC : pbufc asegs m (t_pbs ts) (t_pb ts) []) by (apply NUM; rewrite Est; exact Hst).
assert (FRN' : Z.of_nat (length FRS) + 1 < 4096) by (clear - FRN; lia).
eapply (seg_number_B HIx GA GA_outside GA_pres MAPP PARSEI PARSEU STRTOD NEWINT NEWUINT NEWDBLS pf pa q LBc LM FRS payload me lo m md A B ts l cb nb pj sv errv T v2 ra2 (mredo pf ts - 1 + (bx pf ts - Z.to_nat (16 * Z.max 0 (pf_len pf) + 8192))));
[exact STC | exact BSL | exact DSL | exact FL0 | exact FRN' | exact INV | exact NUMC | exact BK | exact CSTR | exact Hl | exact Hst | exact Hco | exact Hcb | exact FRM | exact S0V | exact RAV | exact HV | exact UWK_dbls | | | | |].
-
intros m' md' A' B' pbs' errv' co' cb' isdq pj' r sh BS gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' Hco' Hcb' LBS JF Hsh INV' PBK' BK' FS' FRM'.
eapply (IHR (ts_lvl (ts_pbs (ts_set_x ts co' (TS isdq (ts_stpos (t_x ts)) (Z_to_bv 64 co') (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))) pbs') (TL ST_eatws ST_finish r (Some sh) BS 0 [])));
[| exact INV' | | | | | | | | | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)];
destruct ts as [depth levels co pb pbs x obj objs objbs]; unfold ts_pbs, ts_set_x, ts_lvl in *; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs] in *.
+ unfold mredo. rewrite (cur_st_upd _ _ l), (cur_ss_upd _ _ l) by exact Hl. cbn [tl_st tl_ss]. change (rank ST_eatws ST_finish) with 6%nat. unfold mredo in M. rewrite Est, Ess, RK in M. unfold mbase in *; cbn [t_co] in *. lia.
+ lia.
+ exact Hcb'.
+ intros E. exfalso. rewrite (cur_st_upd _ _ l) in E by exact Hl. cbn [tl_st] in E. discriminate E.
+ apply (SPOK_upd_plain _ _ l); [exact Hl | reflexivity].
+ eapply (tdepth_ok_upd (TST depth levels co pb pbs x obj objs objbs) l); [exact TD | exact Hl | pose proof (odep_nonneg (tl_cs l)); destruct Hsh as [-> | ->]; cbn [odep sdepth]; lia | exact Hd31 | reflexivity].
+ rewrite (PBS_upd _ _ l) by exact Hl; cbn [tl_st]; pbs_norm. pose proof (PBOK_of_at _ _ _ PBK') as PBK9; cbn [t_co] in PBK9. destruct JF as (w9 & JF9 & Hw9).
eapply (PBJ_attach _ _ (TST depth levels co pb pbs x obj objs objbs) _ l _ _ _ _ _ _ _ _ _ _ _ w9 Hl);
[reflexivity | reflexivity | reflexivity | reflexivity | jl_zin Hst | exact PBK | exact PBK9 | lia | reflexivity | exact JF9 | rewrite ?Hst; jl_arith].
+ eapply BOK_weaken; [| exact BK']. 1: (unfold bredo, bbrk, bloop; apply Nat.add_le_mono; [| bx_tac Hl Hst]). unfold mredo. rewrite (cur_st_upd _ _ l), (cur_ss_upd _ _ l), Est, Ess, RK by exact Hl. cbn [tl_st tl_ss]. change (rank ST_eatws ST_finish) with 6%nat. unfold mbase; cbn [t_co]. lia.
+ apply OBJW_of_NAO. apply (NAO_upd _ _ l); [exact Hl | reflexivity].
-
intros m' md' A' B' pbs' errv' co' cb' isdq pj' gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' Hco' Hcb' INV' PBK' BK' FS' FRM'.
assert (BK2 : BOK pf pa (ts_set_x (ts_lvl (ts_pbs (ts_set_x ts co' (TS isdq (ts_stpos (t_x ts)) (Z_to_bv 64 co') (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))) pbs') (TL ST_inf (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) co' (TS isdq (Z_to_bv 64 0) (Z_to_bv 64 co') (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))) B' (S (Z.to_nat (16 * Z.max 0 (pf_len pf) + 8192) + (mredo pf ts - 1 + (bx pf ts - Z.to_nat (16 * Z.max 0 (pf_len pf) + 8192)))))).
{ apply BOK_set_x; [destruct ts as [depth levels co pb pbs x obj objs objbs]; unfold ts_pbs, ts_set_x, ts_lvl; cbn [t_co]; lia |].
apply (BOK_lvl_restate pf pa (ts_pbs (ts_set_x ts co' (TS isdq (ts_stpos (t_x ts)) (Z_to_bv 64 co') (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))) pbs') B' (S (Z.to_nat (16 * Z.max 0 (pf_len pf) + 8192) + (mredo pf ts - 1 + (bx pf ts - Z.to_nat (16 * Z.max 0 (pf_len pf) + 8192))))) l ST_inf (tl_ss l)); [destruct ts as [depth levels co pb pbs x obj objs objbs]; exact Hl | apply lvl_closed_keep; reflexivity | exact BK']. }
eapply (IHR (ts_set_x (ts_lvl (ts_pbs (ts_set_x ts co' (TS isdq (ts_stpos (t_x ts)) (Z_to_bv 64 co') (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))) pbs') (TL ST_inf (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) co' (TS isdq (Z_to_bv 64 0) (Z_to_bv 64 co') (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))));
[| exact INV' | | | | | | | | | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)];
destruct ts as [depth levels co pb pbs x obj objs objbs]; unfold ts_pbs, ts_set_x, ts_lvl in *; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs] in *.
+ unfold mredo. rewrite (cur_st_upd _ _ l), (cur_ss_upd _ _ l) by exact Hl. cbn [tl_st tl_ss]. change (rank ST_inf (tl_ss l)) with 7%nat. unfold mredo in M. rewrite Est, Ess, RK in M. unfold mbase in *; cbn [t_co] in *. lia.
+ lia.
+ exact Hcb'.
+ intros E. exfalso. rewrite (cur_st_upd _ _ l) in E by exact Hl. cbn [tl_st] in E. discriminate E.
+ unfold SPOK. intros _. unfold SPV. cbn [t_x ts_stpos t_co]. rewrite unsigned_lit by lia. rewrite Zmod_0_l. lia.
+ eapply (tdepth_ok_upd (TST depth levels co pb pbs x obj objs objbs) l); [exact TD | exact Hl | cbn [tl_cs]; pose proof (odep_nonneg (tl_cs l)); lia | exact Hd31 | reflexivity].
+ rewrite (PBS_upd _ _ l) by exact Hl; cbn [tl_st]; pbs_norm. pose proof (PBOK_of_at _ _ _ PBK') as PBK9; cbn [t_co] in PBK9. pbj_rs (TST depth levels co pb pbs x obj objs objbs) l PBK PBK9 Hl Hst.
+ eapply BOK_weaken; [| exact BK2]. 1: (unfold bredo; apply bsplit_S; [| bx_tac Hl Hst | pose proof (bx_ge pf (TST depth levels co pb pbs x obj objs objbs) ltac:(cbn [t_co]; lia)) as GE9; rewrite Est, Ess, ?Hst in GE9; bres_norm_in GE9; pose proof (BTOK_ge pf); unfold BTOK in *; lia]). unfold mredo. rewrite (cur_st_upd _ _ l), (cur_ss_upd _ _ l), Est, Ess, RK by exact Hl. cbn [tl_st tl_ss]. change (rank ST_inf (tl_ss l)) with 7%nat. unfold mbase; cbn [t_co]. lia.
+ apply OBJW_of_NAO. apply (NAO_upd _ _ l); [exact Hl | reflexivity].
-
intros m' md' A' B' errv' cb' pj' ts' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' E1 E2 E3 INVW' FS' FRM'.
eapply KO; [exact INVW' | eapply (tdepth_ok_same ts); [exact E1 | exact E2 | exact E3 | exact TD] | | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)].
eapply (JOUT_of_PBJ (pf_len pf) m ts ts' _ _ PBK); [lia | exact E1 | exact E2 | intros Z9; exfalso; rewrite Est, Hst in Z9; discriminate Z9].
-
intros m' md' A' B' errv' cb' pj' ts' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' E1 E2 E3 INVW' FS' FRM'.
unfold pe_msO. pose proof (KE ts' [] 16 m' md' A' B' cb' nb pj' errv') as KEx. unfold pe_msE, pe_msO in KEx.
eapply KEx; [exact INVW' | eapply (tdepth_ok_same ts); [exact E1 | exact E2 | exact E3 | exact TD] | lia | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)].
-
intros m' md' A' B' errv' cb' pj' ts' gp' t0' t1' t2' a0' a1' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' E1 E2 E3 INVW' FS' FRM'.
eapply (kerrmem2_of_kout HIx GA GA_outside pf pa q LBc LM FRS payload me lo sv T F0 STC KO ts' []);
[exact INVW' | eapply (tdepth_ok_same ts); [exact E1 | exact E2 | exact E3 | exact TD] | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)].
Qed.
End PeSCases4B.
End RC__1.
