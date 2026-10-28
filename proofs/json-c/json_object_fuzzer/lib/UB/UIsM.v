(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)

From Stdlib Require ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup Lib.GwApply QRjH QHnV QCcH QfLs Q0Ek Qtgi QjDH Qsw7 QJjn QkMG Q6q3.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM UC8c UG8z Udyh Uu4M.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB.Top Require TopUbTac.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB.Tk1 Require Tk1Reset.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB.Tk2 Require Tk2Gen.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup.
Import UEQM.
Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0.
Import UC8c.Mq0.
Import Qsw7 QJjn QkMG.
Import UG8z Udyh.Mq0 Uu4M.Mq0.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.
Import TopUbTac Tk2Gen.
Import Q6q3.
Import Tk2Gen.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section PeAadd.
Variable HIx : heap_iface S4L.
Hypothesis AADD : jo_array_add_P HIx.

#[using="AADD"] Lemma seg_aadd :
forall (pf : pe_fix) (q : Z) (LB0 : list blk) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (ts : tstate) (l : tlevel) (kids : list (option jshape))
(cb : byte) (j1 j2 utf : list byte) (sv : pe_saved) (errv : word) (T : TSet)
(x1 gp t0 t1 t2 a0 a3 a4 a5 a6 a7 s6 s7 s8 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC HIx pf lo ->
PE_INV HIx pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_array_add ->
tl_cs l = Some (Sarr kids) ->

(forall m' md' A' cbs' errv' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F' fc',
PE_INV HIx pf q LB0 payload me lo m' md' A'
(TST (t_depth ts) (lupd (t_levels ts) (t_depth ts) (TL ST_eatws ST_array_sep (tl_cur l) (Some (Sarr (kids ++ [t_objs ts]))) cbs' (tl_name l) (tl_nbs l)))
(t_co ts) (t_pb ts) (t_pbs ts) (t_x ts) (t_obj ts) (t_objs ts) [])
cb j1 j2 utf sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_REDO (t_co ts) x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F' fc' m') md') T) ->

(forall m' md' A' errv' x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F' fc',
PE_INV HIx pf q LB0 payload me lo m' md' A' ts cb j1 j2 utf sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_ERR (t_co ts) x1' gp' t0' t1' t2' (Z_to_bv 64 16) a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F' fc' m') md') T) ->
realizes rsegs (mkCfg (pe_ms rsegs pf (pe_jt ST_array_add) (t_co ts) x1 gp t0 t1 t2
a0 (Z_to_bv 64 (tl_st l)) (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) a3 a4 a5 a6 a7
(Z_to_bv 64 q) s6 s7 s8 (Z_to_bv 64 (Z.of_nat (t_depth ts))) s10 t3 t4 t5 t6 F fc m) md) T.
Proof.
intros until fc. intros STC INV Hl Hst Hcs Kredo Kerr.
pose proof STC as (LO & LOS & SPA & HT & SP0 & LEN & SB0 & SBL).
destruct INV as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
apply (PE_REST_base HIx) in REST as (BASE & LV & OBJ).
pose proof (proj1 BASE) as HP.
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl_]; pe_gen fl_; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
unfold tok_cells, tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK. unfold pe_frame in FR. unfold pe_ms in *. cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
unfold_consts.

assert (JOB : jopt rsegs S4F objs m objbs obj).
{ revert OBJ. unfold cur_st. cbn [t_levels t_depth t_objbs t_objs t_obj]. rewrite Hl, Hst. cbn. intros E; exact E. }
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocks; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, (32 * mxd)) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocks; apply in_or_app; right; right; left; reflexivity).
pose proof (heap_blk S4L HIx _ _ _ _ tk 72 HP INtk) as (_ & Htal & Htlo & Hthi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ tk 72 HP INtk) as Himg_t. cbn [hl_img_lo hl_img_hi S4L] in Himg_t.
pose proof (heap_blk S4L HIx _ _ _ _ q (32 * mxd) HP INq) as (_ & Hqal & Hqlo & Hqhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ q (32 * mxd) HP INq) as Himg_q. cbn [hl_img_lo hl_img_hi S4L] in Himg_q.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hthi, Hqhi.
pose proof (heap_blk_nodup S4L HIx _ _ _ _ HP) as ND.
assert (Htq : tk <> q).
{ generalize ND; intros ND'. unfold pe_blocks in ND'. rewrite map_app in ND'. apply NoDup_app_remove_l in ND'.
cbn [map blk_addr fst pf_tk pf_md pf_mxd pf_fl] in ND'. apply List.NoDup_cons_iff in ND' as [Hni _]. intros E. apply Hni. left. symmetry. exact E. }
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ tk 72 q (32 * mxd) HP INtk INq Htq) as Hdtq.
assert (NQ0 : forall k, ~ In (q, k) LB0).
{ intros k. generalize ND; intros ND'. unfold ts0, pe_blocks, tstate_blocks in ND'. cbn [t_pbs t_objbs t_levels pf_tk pf_md pf_mxd pf_fl] in ND'.
rewrite <- !app_assoc in ND'. exact (nodup_mid_notin _ _ _ _ _ _ _ _ k ND'). }
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (LV depth l Hl) as LVd. pose proof LVd as (ST26 & SS26 & JO & Md).
rewrite Nat.ltb_irrefl, Nat.eqb_refl in Md. destruct Md as (c0 & hn0 & Hmode & CLS0 & NM0).
rewrite Hst, lvl_mode_aadd in Hmode. injection Hmode as <- <-. cbn [name_ok] in NM0. destruct NM0 as [Hn0 Hnbs0].
rewrite Hcs in JO. cbn [jopt] in JO. destruct JO as [Hc J].
set (cur := tl_cur l) in *. set (cbs := tl_cbs l) in *.
assert (Ecur0 : tl_cur l = cur) by reflexivity. assert (Ecbs0 : tl_cbs l = cbs) by reflexivity. clearbody cur cbs.

set (LBput := (pbs ++ concat (map lvl_blocks (lupd levels depth lvl_reset))) ++ (tk, 72) :: (q, (32 * mxd)) :: LB0).
assert (PERM0 : Permutation (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0) (cbs ++ objbs ++ LBput)).
{ unfold pe_blocks, tstate_blocks, ts0, LBput. cbn [t_pbs t_objbs t_levels pf_tk pf_md pf_mxd pf_fl]. rewrite <- !app_assoc.
apply (Permutation_trans (l' := pbs ++ (objbs ++ (cbs ++ (concat (map lvl_blocks (lupd levels depth lvl_reset)) ++ (tk, 72) :: (q, (32 * mxd)) :: LB0))))).
- apply Permutation_app_head. apply Permutation_app_head. rewrite (app_assoc cbs). apply Permutation_app_tail.
replace cbs with (lvl_blocks l) by (unfold lvl_blocks; rewrite Hnbs0, app_nil_r, Ecbs0; reflexivity).
apply concat_lupd_empty; [exact Hl | reflexivity].
- apply (Permutation_trans (l' := objbs ++ (pbs ++ (cbs ++ (concat (map lvl_blocks (lupd levels depth lvl_reset)) ++ (tk, 72) :: (q, (32 * mxd)) :: LB0))))); [apply Permutation_app_swap_app|].
apply (Permutation_trans (l' := objbs ++ (cbs ++ (pbs ++ (concat (map lvl_blocks (lupd levels depth lvl_reset)) ++ (tk, 72) :: (q, (32 * mxd)) :: LB0))))); [apply Permutation_app_head; apply Permutation_app_swap_app|].
apply Permutation_app_swap_app. }
assert (INqP : In (q, (32 * mxd)) LBput) by (unfold LBput; apply in_or_app; right; right; left; reflexivity).
assert (INtkP : In (tk, 72) LBput) by (unfold LBput; apply in_or_app; right; left; reflexivity).
assert (LB0P : incl LB0 LBput) by (unfold LBput; intros b Hb; apply in_or_app; right; right; right; exact Hb).
set (BL := concat (map lvl_blocks (lupd levels depth lvl_reset))).
assert (BLP : incl BL LBput) by (unfold LBput; intros b Hb; apply in_or_app; left; apply in_or_app; right; exact Hb).
pose proof (TSK depth l Hl) as Ld. unfold srec_cells in Ld. rewrite Ecur0, Hn0 in Ld.
remember (q + 32 * Z.of_nat depth) as bse eqn:Hbse in Ld.
assert (HbseR : q <= bse /\ bse + 32 <= q + (32 * mxd)) by (subst bse; lia).
assert (Hbal : bse mod 16 = 0) by (subst bse; clear - Hqal; Z.div_mod_to_equations; lia).
stash PB. stash TSK. clear OBJ.
apply rz_evt; [exact MOK|]. rewrite Hst. unfold ST_array_add. cbn [pe_jt]. replace (q + 32 * Z.of_nat depth) with bse by lia.
bst. bst. bst.

unstash PB. unstash TSK.
apply evt_RZ_done.
eapply AADD with (LB := LBput) (ABS := cbs) (VBS := objbs) (p := cur) (v := obj) (kids := kids) (vs := objs) (lo := lo) (errv := errv);
[ | exact J | exact JOB | reflexivity | reflexivity | ].
{ pose proof BASE as (_ & ST0 & ERR0 & _). unfold jo_pre. cbn [hl_segs hl_tp S4L].
split; [eapply (heap_perm S4L HIx); [exact HP | exact PERM0] |].
rewrite ?unsigned_lit by lia. unfold PE_FRAME in *.
split; [exact ST0|]. split; [clia|]. split; [clia|]. split; [exact SPA|]. split; [lia|]. split; [exact ERR0|]. split; [reflexivity|]. reflexivity. }
intros ms2 md2 mp r (RS2 & VM2 & ST2 & HPR2 & (errv2 & ERR2)) OUT.
destruct RS2 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F2 & fc2 & -> & FS2 & FRM2).
cbn [hl_segs hl_tp S4L] in *. rewrite ?(unsigned_lit spf) in ST2 by lia. rewrite ?(unsigned_lit spf) in HPR2 by lia.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in TOK; [| eapply client_range_block; [exact INtkP | lia | cbn; lia]]. cbn [hl_segs S4L] in TOK.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in Ld; [| eapply client_range_block; [exact INqP | lia | cbn; lia]]. cbn [hl_segs S4L] in Ld.
apply (tstack_pres_g S4L _ _ _ _ _ _ HPR2 INqP) in TSK; [| exact LEN32].
assert (PB2 : pbuf rsegs mp pbs pb).
{ eapply pbuf_agree; [exact PB | | apply incl_refl]. eapply (agree_of_heap_pres rsegs S4L); [exact HPR2 | reflexivity |].
unfold LBput. intros b Hb. apply in_or_app; left. apply in_or_app; left. exact Hb. }
assert (AGL2 : agree_on rsegs BL m mp) by (eapply (agree_of_heap_pres rsegs S4L); [exact HPR2 | reflexivity | exact BLP]).

assert (LV2 : forall i li, nth_error levels i = Some li -> i <> depth -> lvl_cur rsegs S4F mp depth i li).
{ intros i li Hli Hne. eapply (lvl_cur_agree rsegs S4F); [exact (LV i li Hli) | exact AGL2 |].
intros b Hb. unfold BL. apply in_concat. exists (lvl_blocks li). split; [| exact Hb]. apply in_map.
eapply (nth_error_In _ i). rewrite nth_error_lupd_neq by congruence. exact Hli. }
clear PB MI HP.
destruct OUT as [(-> & A2 & cbs' & J2 & HP2) | (-> & A2 & J2 & JOB2 & HP2)].
-
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2. reenter MOK2.
assert (BASE2 : PE_BASE HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) LB0 payload me lo mp md2 A2 (cbs' ++ LBput) errv2)
by (eapply (PE_BASE_call HIx); [exact BASE | exact HPR2 | exact LB0P | exact VM2 | exact HP2 | exact ST2 | exact ERR2]).
clear BASE HPR2.
pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI. cbn [hl_segs S4L] in MI.
pose proof (wmono_refl rsegs mp) as WM.
pose proof (munch_refl [(bse, bse + 32)] mp) as MU.
stash PB2. stash TSK. stash BASE2. stash LV2.
bst. if_true.
bst. norm_sx32. bst.
bst. rewrite (unsigned_lit (Z.of_nat depth)) by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32.
bst. replace (q + Z.of_nat depth * 32) with bse by lia.
bst. bst. bstz. bst.
unstash PB2. unstash TSK. unstash BASE2. unstash LV2.
set (l' := TL ST_eatws ST_array_sep cur (Some (Sarr (kids ++ [objs]))) cbs' (tl_name l) (tl_nbs l)).
pose proof (heap_blk_nodup S4L HIx _ _ _ _ HP2) as ND2.
assert (NEq : forall a k, In (a, k) (cbs' ++ pbs ++ BL) -> a <> q).
{ intros a k Hin ->.
assert (ND3 : List.NoDup (map blk_addr ((cbs' ++ pbs ++ BL) ++ (tk, 72) :: (q, (32 * mxd)) :: LB0))).
{ unfold LBput in ND2. rewrite <- !app_assoc. rewrite <- !app_assoc in ND2. exact ND2. }
rewrite map_app in ND3. eapply (NoDup_app_in2 _ _ q ND3); [exact (in_map blk_addr _ _ Hin) | cbn; right; left; reflexivity]. }
assert (AGX : forall BS, (forall a k, In (a, k) BS -> In (a, k) (cbs' ++ LBput) /\ a <> q) -> agree_on rsegs BS mp _)
by (intros BS HBS; eapply agree_of_munch; [exact MU | exact WM |]; intros a k Hin; destruct (HBS a k Hin) as [HinL Hnq];
pose proof (heap_blk S4L HIx _ _ _ _ a k HP2 HinL) as (Hk0 & _);
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ a k q (32 * mxd) HP2 HinL ltac:(apply in_or_app; right; exact INqP) Hnq); cbn; lia).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch type of Ld with rw_cells _ _ _ (?c1 :: ?c2 :: _) =>
pose proof (rw_cells_recast_prefix rsegs mc bse [c1; c2] [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 17)]
[C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 cur); C8 (Z_to_bv 64 0)] Ld
ltac:(cbn; repeat split) ltac:(apply bytes_eq_by_unsigned; vm_compute; reflexivity) ltac:(reflexivity)) as Ld1 end;
cbn [app] in Ld1
end.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (TSK3 : tstack rsegs mc q (lupd levels depth l'))
by (subst bse; eapply (tstack_put rsegs mp _ q levels depth l' []);
[exact TSK | lia | exact MU | exact WM | intros; exact I | unfold srec_cells, l'; cbn [tl_st tl_ss tl_cur tl_name]; rewrite Hn0; exact Ld1]);
assert (BASE3 : PE_BASE HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) LB0 payload me lo mc md2 A2 (cbs' ++ LBput) errv2)
by (eapply (PE_BASE_write HIx); [exact STC | exact BASE2 | intros b Hb; apply in_or_app; right; exact (LB0P _ Hb) | exact MU | exact WM | exact MI |];
apply Forall_cons; [| apply Forall_nil]; unfold base_w; cbn [fst snd pf_spf pf_md pf_mxd pf_fl]; left; exists q, (32 * mxd);
split; [apply in_or_app; right; exact INqP|]; split; [exact NQ0 | lia]);
assert (PB3 : pbuf rsegs mc pbs pb)
by (eapply pbuf_agree; [exact PB2 | apply AGX | apply incl_refl]; intros a k Hin; split;
[unfold LBput; apply in_or_app; right; apply in_or_app; left; apply in_or_app; left; exact Hin | eapply NEq; apply in_or_app; right; apply in_or_app; left; exact Hin]);
assert (AGL3 : agree_on rsegs BL mp mc)
by (apply AGX; intros a k Hin; split; [apply in_or_app; right; exact (BLP _ Hin) | eapply NEq; apply in_or_app; right; apply in_or_app; right; exact Hin]);
assert (J3 : jval rsegs S4F (Sarr (kids ++ [objs])) mc cbs' cur 1)
by (eapply jval_agree; [exact J2 | apply AGX | apply incl_refl]; intros a k Hin; split; [apply in_or_app; left; exact Hin | eapply NEq; apply in_or_app; left; exact Hin])
end.
apply evt_RZ_done. eapply (Kredo _ md2 A2 cbs' errv2); [ | exact FS2 | exact FRM2].
split.
+ unfold PE_CORE. cbn [t_levels t_depth t_co t_pb t_pbs t_x t_obj ts_choff pf_len pf_tk pf_spf pf_md pf_mxd pf_fl].
split; [rewrite lupd_length; exact LEN32|]. split; [exact D32|]. split; [lia|]. split; [reflexivity|].
split; [unfold tok_cells, tok_cells_g; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote]; exact TOK|].
split; [exact PB3|]. split; [exact Hpb|]. split; [exact TSK3|]. unfold pe_frame. exact FR.
+ apply (PE_REST_of_base HIx).
* eapply (PE_BASE_perm HIx); [exact BASE3|].
unfold pe_blocks, tstate_blocks, LBput. cbn [t_pbs t_objbs t_levels pf_tk pf_md pf_mxd pf_fl]. rewrite app_nil_l.
unfold BL. rewrite (lupd_split levels depth l lvl_reset Hl). fold l'. rewrite (lupd_split levels depth l l' Hl).
replace (lvl_blocks l') with cbs' by (unfold lvl_blocks, l'; cbn; rewrite Hnbs0, app_nil_r; reflexivity).
cbn [lvl_blocks lvl_reset tl_cbs tl_nbs app]. rewrite <- !app_assoc.
apply (Permutation_trans (l' := pbs ++ (cbs' ++ (concat (map lvl_blocks (firstn depth levels)) ++ (concat (map lvl_blocks (skipn (S depth) levels)) ++ (tk, 72) :: (q, (32 * mxd)) :: LB0)))));
[apply Permutation_app_swap_app | apply Permutation_app_head; apply Permutation_app_swap_app].
* cbn [t_levels t_depth]. intros i li Hli.
destruct (Nat.eq_dec i depth) as [-> | NE].
-- rewrite nth_error_lupd_eq in Hli by lia. injection Hli as <-.
split; [cbn; unfold ST_eatws; lia|]. split; [cbn; unfold ST_array_sep; lia|]. split; [cbn [tl_cs tl_cbs tl_cur l' jopt]; split; [exact Hc | exact J3]|].
rewrite Nat.ltb_irrefl, Nat.eqb_refl. exists CArr, false. split; [reflexivity|]. split; [exact I|]. cbn. split; [exact Hn0 | exact Hnbs0].
-- rewrite nth_error_lupd_neq in Hli by congruence.
eapply (lvl_cur_agree rsegs S4F); [exact (LV2 i li Hli NE) | exact AGL3 |].
intros b Hb. unfold BL. apply in_concat. exists (lvl_blocks li). split; [| exact Hb]. apply in_map.
eapply (nth_error_In _ i). rewrite nth_error_lupd_neq by congruence. exact Hli.
* unfold cur_st. cbn [t_levels t_depth t_objbs]. rewrite nth_error_lupd_eq by lia. reflexivity.
-
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2. reenter MOK2.
assert (BASE2 : PE_BASE HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) LB0 payload me lo mp md2 A2 (cbs ++ objbs ++ LBput) errv2)
by (eapply (PE_BASE_call HIx); [exact BASE | exact HPR2 | exact LB0P | exact VM2 | exact HP2 | exact ST2 | exact ERR2]).
replace (Z_to_bv 64 (2^64 - 1)) with (Z_to_bv 64 (-1)) by (apply bv_eq; vm_compute; reflexivity).
bst. if_false. bst. bst. bst.
apply evt_RZ_done. eapply (Kerr _ md2 A2 errv2); [ | exact FS2 | exact FRM2].
unfold ts0. split.
+ unfold PE_CORE. cbn [t_levels t_depth t_co t_pb t_pbs t_x t_obj ts_choff pf_len pf_tk pf_spf pf_md pf_mxd pf_fl].
split; [exact LEN32|]. split; [exact D32|]. split; [lia|]. split; [reflexivity|].
split; [unfold tok_cells, tok_cells_g; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote]; exact TOK|].
split; [exact PB2|]. split; [exact Hpb|]. split; [| unfold pe_frame; exact FR].
intros j lj Hlj. destruct (Nat.eq_dec j depth) as [-> | NE].
* rewrite Hl in Hlj. injection Hlj as <-. subst bse. unfold srec_cells. rewrite Ecur0, Hn0. exact Ld.
* exact (TSK j lj Hlj) || (eapply TSK; exact Hlj).
+ apply (PE_REST_of_base HIx).
* eapply (PE_BASE_perm HIx); [exact BASE2 | apply Permutation_sym; exact PERM0].
* cbn [t_levels t_depth]. intros i li Hli.
destruct (Nat.eq_dec i depth) as [-> | NE].
-- rewrite Hl in Hli. injection Hli as <-.
split; [exact ST26|]. split; [exact SS26|]. split; [rewrite Hcs, Ecbs0, Ecur0; cbn [jopt]; split; [exact Hc | exact J2]|].
rewrite Nat.ltb_irrefl, Nat.eqb_refl. exists CArr, false. rewrite Hst. split; [apply lvl_mode_aadd|]. split; [rewrite Hcs; exact I|]. cbn. split; [exact Hn0 | exact Hnbs0].
-- exact (LV2 i li Hli NE).
* unfold cur_st. cbn [t_levels t_depth t_objbs t_objs t_obj]. rewrite Hl, Hst. cbn. exact JOB2.
Qed.
End PeAadd.

End RC__1.
End Mq0.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup.
Import UEQM.
Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0.
Import UC8c.Mq0.
Import Qsw7 QJjn QkMG.
Import UG8z Udyh.Mq0 Uu4M.Mq0 Udyh.Mq4.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.
Import Q6q3.
Import Tk2Gen.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section PeAsep.
Variable HIx : heap_iface S4L.
Hypothesis SHRINK : jo_array_shrink_P HIx.

#[using="SHRINK"] Lemma seg_asep_close :
forall (pf : pe_fix) (q : Z) (LB0 : list blk) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (ts : tstate) (l : tlevel) (kids : list (option jshape))
(cb : byte) (j1 j2 utf : list byte) (sv : pe_saved) (errv : word) (T : TSet)
(x1 gp t0 t1 t2 a1 a3 a4 a5 a6 a7 s6 s7 s8 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC HIx pf lo ->
PE_INV HIx pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_array_sep ->
tl_cs l = Some (Sarr kids) ->
t_co ts < pf_len pf ->

(forall m' md' A' cbs' errv' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F' fc',
PE_INV HIx pf q LB0 payload me lo m' md' A'
(TST (t_depth ts) (lupd (t_levels ts) (t_depth ts) (TL ST_eatws ST_finish (tl_cur l) (tl_cs l) cbs' (tl_name l) (tl_nbs l)))
(t_co ts) (t_pb ts) (t_pbs ts) (t_x ts) (t_obj ts) (t_objs ts) (t_objbs ts))
cb j1 j2 utf sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_BREAK (t_co ts) x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F' fc' m') md') T) ->
forall a0, realizes rsegs (mkCfg (pe_ms rsegs pf 0x23534 (t_co ts) x1 gp t0 t1 t2
a0 a1 (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) a3 a4 a5 a6 a7
(Z_to_bv 64 q) s6 s7 s8 (Z_to_bv 64 (Z.of_nat (t_depth ts))) s10 t3 t4 t5 t6 F fc m) md) T.
Proof.
intros until fc. intros STC INV Hl Hst Hcs Hco Kbreak a0.
pose proof STC as (LO & LOS & SPA & HT & SP0 & LEN & SB0 & SBL).
destruct INV as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
apply (PE_REST_base HIx) in REST as (BASE & LV & OBJ).
pose proof (proj1 BASE) as HP.
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl_]; pe_gen fl_; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
unfold tok_cells, tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in TOK. unfold pe_frame in FR. unfold pe_ms in *. cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
unfold_consts.
assert (SB1 : 1 <= sb).
{ pose proof BASE as (HP0 & _ & _ & _ & _ & PLOC & _). unfold payload_loc in PLOC. cbn [pf_len pf_sb pf_spf] in PLOC.
destruct PLOC as [L0 | [STKM | ([ba bn] & Hb & Hb1 & Hb2)]].
{ lia. }
{ unfold PE_FRAME in *.
lia. }
pose proof (heap_blk S4L HIx _ _ _ _ ba bn HP0 ltac:(unfold pe_blocks; apply in_or_app; right; right; right; exact Hb)) as (_ & _ & Hba & _).
cbn [blk_addr fst] in Hb1. lia. }
assert (Eobjbs : objbs = []).
{ revert OBJ. unfold cur_st. cbn [t_levels t_depth t_objbs pf_mxd]. rewrite Hl, Hst. intros E'; exact E'. }
subst objbs.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs []) in *.
assert (INtk : In (tk, 72) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocks; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, (32 * mxd)) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocks; apply in_or_app; right; right; left; reflexivity).
pose proof (heap_blk S4L HIx _ _ _ _ tk 72 HP INtk) as (_ & Htal & Htlo & Hthi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ tk 72 HP INtk) as Himg_t. cbn [hl_img_lo hl_img_hi S4L pf_mxd] in Himg_t.
pose proof (heap_blk S4L HIx _ _ _ _ q (32 * mxd) HP INq) as (_ & Hqal & Hqlo & Hqhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ q (32 * mxd) HP INq) as Himg_q. cbn [hl_img_lo hl_img_hi S4L pf_mxd] in Himg_q.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hthi, Hqhi.
pose proof (heap_blk_nodup S4L HIx _ _ _ _ HP) as ND.
assert (Htq : tk <> q).
{ generalize ND; intros ND'. unfold pe_blocks in ND'. rewrite map_app in ND'. apply NoDup_app_remove_l in ND'.
cbn [map blk_addr fst pf_tk pf_md pf_mxd pf_fl] in ND'. apply List.NoDup_cons_iff in ND' as [Hni _]. intros E. apply Hni. left. symmetry. exact E. }
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ tk 72 q (32 * mxd) HP INtk INq Htq) as Hdtq.
assert (NQ0 : forall k, ~ In (q, k) LB0).
{ intros k. generalize ND; intros ND'. unfold ts0, pe_blocks, tstate_blocks in ND'. cbn [t_pbs t_objbs t_levels pf_tk pf_md pf_mxd pf_fl] in ND'.
rewrite <- !app_assoc in ND'. exact (nodup_mid_notin _ _ _ _ _ _ _ _ k ND'). }
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L pf_mxd] in MI.
pose proof (LV depth l Hl) as LVd. pose proof LVd as (ST26 & SS26 & JO & Md).
rewrite Nat.ltb_irrefl, Nat.eqb_refl in Md. destruct Md as (c0 & hn0 & Hmode & CLS0 & NM0).
assert (Ehn : c0 = CArr /\ hn0 = false).
{ revert Hmode. unfold lvl_mode. cbn -[zin andb].
cbn [zin existsb Z.eqb ws_states val_states esc_states app ST_eatws ST_start ST_finish ST_null ST_comment_start ST_comment ST_comment_eol ST_comment_end
ST_string ST_string_escape ST_escape_unicode ST_esc_need_escape ST_esc_need_u ST_boolean ST_number ST_array ST_array_add ST_array_sep
ST_ofs ST_ofield ST_ofend ST_ovalue ST_ovadd ST_osep ST_array_after_sep ST_ofs_after_sep ST_inf andb orb pf_mxd].
assert (CASES : exists k : nat, (k <= 26)%nat /\ tl_ss l = Z.of_nat k) by (exists (Z.to_nat (tl_ss l)); split; lia).
destruct CASES as (k & Hk & Ek). rewrite Ek.
rewrite Hst; unfold ST_array_sep;
do 27 (destruct k as [|k]; [cbn; intros EE; first [discriminate EE | injection EE as <- <-; split; reflexivity] |]); exfalso; lia. }
destruct Ehn as [-> ->]. cbn [name_ok pf_mxd] in NM0. destruct NM0 as [Hn0 Hnbs0].
rewrite Hcs in JO. cbn [jopt pf_mxd] in JO. destruct JO as [Hc J].
set (cur := tl_cur l) in *. set (cbs := tl_cbs l) in *.
assert (Ecur0 : tl_cur l = cur) by reflexivity. assert (Ecbs0 : tl_cbs l = cbs) by reflexivity. clearbody cur cbs.

set (LBput := (pbs ++ concat (map lvl_blocks (lupd levels depth lvl_reset))) ++ (tk, 72) :: (q, (32 * mxd)) :: LB0).
assert (PERM0 : Permutation (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0) (cbs ++ LBput)).
{ unfold pe_blocks, tstate_blocks, ts0, LBput. cbn [t_pbs t_objbs t_levels pf_tk pf_md pf_mxd pf_fl]. rewrite app_nil_l. rewrite <- !app_assoc.
apply (Permutation_trans (l' := pbs ++ (cbs ++ (concat (map lvl_blocks (lupd levels depth lvl_reset)) ++ (tk, 72) :: (q, (32 * mxd)) :: LB0)))).
- apply Permutation_app_head. rewrite (app_assoc cbs). apply Permutation_app_tail.
replace cbs with (lvl_blocks l) by (unfold lvl_blocks; rewrite Hnbs0, app_nil_r, Ecbs0; reflexivity).
apply concat_lupd_empty; [exact Hl | reflexivity].
- apply Permutation_app_swap_app. }
assert (INqP : In (q, (32 * mxd)) LBput) by (unfold LBput; apply in_or_app; right; right; left; reflexivity).
assert (INtkP : In (tk, 72) LBput) by (unfold LBput; apply in_or_app; right; left; reflexivity).
assert (LB0P : incl LB0 LBput) by (unfold LBput; intros b Hb; apply in_or_app; right; right; right; exact Hb).
set (BL := concat (map lvl_blocks (lupd levels depth lvl_reset))).
assert (BLP : incl BL LBput) by (unfold LBput; intros b Hb; apply in_or_app; left; apply in_or_app; right; exact Hb).
pose proof (TSK depth l Hl) as Ld. unfold srec_cells in Ld. rewrite Ecur0, Hn0 in Ld.
remember (q + 32 * Z.of_nat depth) as bse eqn:Hbse in Ld.
assert (HbseR : q <= bse /\ bse + 32 <= q + (32 * mxd)) by (subst bse; lia).
stash PB. stash TSK. clear OBJ.
apply rz_evt; [exact MOK|]. replace (q + 32 * Z.of_nat depth) with bse by lia.
bst. bst. bst.

unstash PB. unstash TSK.
apply evt_RZ_done.
eapply SHRINK with (LB := LBput) (ABS := cbs) (p := cur) (kids := kids) (lo := lo) (errv := errv);
[ | exact J | reflexivity | reflexivity | ].
{ pose proof BASE as (_ & ST0 & ERR0 & _). unfold jo_pre. cbn [hl_segs hl_tp S4L pf_mxd].
split; [eapply (heap_perm S4L HIx); [exact HP | exact PERM0] |].
rewrite ?unsigned_lit by lia. unfold PE_FRAME in *.
split; [exact ST0|]. split; [clia|]. split; [clia|]. split; [exact SPA|]. split; [lia|]. split; [exact ERR0|]. split; [reflexivity|]. reflexivity. }
intros ms2 md2 mp r (RS2 & VM2 & ST2 & HPR2 & (errv2 & ERR2)) (A2 & cbs' & J2 & HP2).
destruct RS2 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F2 & fc2 & -> & FS2 & FRM2).
cbn [hl_segs hl_tp S4L pf_mxd] in *. rewrite ?(unsigned_lit spf) in ST2 by lia. rewrite ?(unsigned_lit spf) in HPR2 by lia.
assert (BASE2 : PE_BASE HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) LB0 payload me lo mp md2 A2 (cbs' ++ LBput) errv2)
by (eapply (PE_BASE_call HIx); [exact BASE | exact HPR2 | exact LB0P | exact VM2 | exact HP2 | exact ST2 | exact ERR2]).
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. cbn [hl_segs S4L pf_mxd] in FR.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in TOK; [| eapply client_range_block; [exact INtkP | lia | cbn; lia]]. cbn [hl_segs S4L pf_mxd] in TOK.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in Ld; [| eapply client_range_block; [exact INqP | lia | cbn; lia]]. cbn [hl_segs S4L pf_mxd] in Ld.
apply (tstack_pres_g S4L _ _ _ _ _ _ HPR2 INqP) in TSK; [| exact LEN32].
assert (PB2 : pbuf rsegs mp pbs pb).
{ eapply pbuf_agree; [exact PB | | apply incl_refl]. eapply (agree_of_heap_pres rsegs S4L); [exact HPR2 | reflexivity |].
unfold LBput. intros b Hb. apply in_or_app; left. apply in_or_app; left. exact Hb. }
assert (AGL2 : agree_on rsegs BL m mp) by (eapply (agree_of_heap_pres rsegs S4L); [exact HPR2 | reflexivity | exact BLP]).
clear BASE PB HPR2 MI HP.

pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2.
pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI. cbn [hl_segs S4L pf_mxd] in MI.
pose proof (wmono_refl rsegs mp) as WM.
pose proof (munch_refl [(bse, bse + 32)] mp) as MU.
stash PB2. stash TSK. stash BASE2.
assert (SBC : 2 <= sb + co + 1 < 2^64) by lia.
reenter MOK2.
bst. norm_sx32. bst.
bst. rewrite (unsigned_lit (Z.of_nat depth)) by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32.
bst. replace (q + Z.of_nat depth * 32) with bse by lia.
bst_to 0x23d14.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch type of Ld with rw_cells _ _ _ (?c1 :: ?c2 :: _) =>
pose proof (rw_cells_recast_prefix rsegs mc bse [c1; c2] [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 2)]
[C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 cur); C8 (Z_to_bv 64 0)] Ld
ltac:(cbn; repeat split) ltac:(apply bytes_eq_by_unsigned; vm_compute; reflexivity) ltac:(reflexivity)) as Ld1 end;
clear Ld; rename Ld1 into Ld;
cbn [app pf_mxd] in Ld
end.
unstash PB2. unstash TSK. unstash BASE2.
set (l' := TL ST_eatws ST_finish cur (tl_cs l) cbs' (tl_name l) (tl_nbs l)).
assert (AGX : forall BS, (forall a k, In (a, k) BS -> In (a, k) (cbs' ++ LBput) /\ a <> q) -> agree_on rsegs BS mp _)
by (intros BS HBS; eapply agree_of_munch; [exact MU | exact WM |]; intros a k Hin; destruct (HBS a k Hin) as [HinL Hnq];
pose proof (heap_blk S4L HIx _ _ _ _ a k HP2 HinL) as (Hk0 & _);
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ a k q (32 * mxd) HP2 HinL ltac:(apply in_or_app; right; exact INqP) Hnq); cbn; lia).
pose proof (heap_blk_nodup S4L HIx _ _ _ _ HP2) as ND2.
assert (NEq : forall a k, In (a, k) (cbs' ++ pbs ++ BL) -> a <> q).
{ intros a k Hin ->. unfold LBput in ND2. rewrite (app_assoc _ _ ((tk,72) :: _)) in ND2 || idtac.
assert (ND3 : List.NoDup (map blk_addr ((cbs' ++ pbs ++ BL) ++ (tk, 72) :: (q, (32 * mxd)) :: LB0))).
{ rewrite <- !app_assoc. rewrite <- !app_assoc in ND2. exact ND2. }
rewrite map_app in ND3. eapply (NoDup_app_in2 _ _ q ND3); [exact (in_map blk_addr _ _ Hin) | cbn; right; left; reflexivity]. }
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (TSK3 : tstack rsegs mc q (lupd levels depth l'))
by (subst bse; eapply (tstack_put rsegs mp _ q levels depth l' []);
[exact TSK | lia | exact MU | exact WM | intros; exact I | unfold srec_cells, l'; cbn [tl_st tl_ss tl_cur tl_name pf_mxd]; rewrite Hn0; exact Ld]);
assert (BASE3 : PE_BASE HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) LB0 payload me lo mc md2 A2 (cbs' ++ LBput) errv2)
by (eapply (PE_BASE_write HIx); [exact STC | exact BASE2 | intros b Hb; apply in_or_app; right; exact (LB0P _ Hb) | exact MU | exact WM | exact MI |];
apply Forall_cons; [| apply Forall_nil]; unfold base_w; cbn [fst snd pf_spf pf_md pf_mxd pf_fl]; left; exists q, (32 * mxd);
split; [apply in_or_app; right; exact INqP|]; split; [exact NQ0 | lia]);
assert (PB3 : pbuf rsegs mc pbs pb)
by (eapply pbuf_agree; [exact PB2 | apply AGX | apply incl_refl]; intros a k Hin; split;
[unfold LBput; apply in_or_app; right; apply in_or_app; left; apply in_or_app; left; exact Hin | eapply NEq; apply in_or_app; right; apply in_or_app; left; exact Hin]);
assert (AGL3 : agree_on rsegs BL m mc)
by (eapply agree_on_trans; [exact AGL2|]; apply AGX; intros a k Hin; split; [apply in_or_app; right; exact (BLP _ Hin) | eapply NEq; apply in_or_app; right; apply in_or_app; right; exact Hin]);
assert (J3 : jval rsegs S4F (Sarr kids) mc cbs' cur 1)
by (eapply jval_agree; [exact J2 | apply AGX | apply incl_refl]; intros a k Hin; split; [apply in_or_app; left; exact Hin | eapply NEq; apply in_or_app; left; exact Hin])
end.
apply evt_RZ_done. eapply (Kbreak _ md2 A2 cbs' errv2); [ | exact FS2 | exact FRM2].
split.
- unfold PE_CORE. cbn [t_levels t_depth t_co t_pb t_pbs t_x t_obj ts_choff pf_len pf_tk pf_spf pf_md pf_mxd pf_fl].
split; [rewrite lupd_length; exact LEN32|]. split; [exact D32|]. split; [lia|]. split; [reflexivity|].
split; [unfold tok_cells, tok_cells_g; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd]; exact TOK|].
split; [exact PB3|]. split; [exact Hpb|]. split; [exact TSK3|]. unfold pe_frame. exact FR.
- apply (PE_REST_of_base HIx).
+ eapply (PE_BASE_perm HIx); [exact BASE3|].
unfold pe_blocks, tstate_blocks, LBput. cbn [t_pbs t_objbs t_levels pf_tk pf_md pf_mxd pf_fl]. rewrite app_nil_l.
unfold BL. rewrite (lupd_split levels depth l lvl_reset Hl). fold l'. rewrite (lupd_split levels depth l l' Hl).
replace (lvl_blocks l') with cbs' by (unfold lvl_blocks, l'; cbn; rewrite Hnbs0, app_nil_r; reflexivity).
cbn [lvl_blocks lvl_reset tl_cbs tl_nbs app pf_mxd]. rewrite <- !app_assoc.
apply (Permutation_trans (l' := pbs ++ (cbs' ++ (concat (map lvl_blocks (firstn depth levels)) ++ (concat (map lvl_blocks (skipn (S depth) levels)) ++ (tk, 72) :: (q, (32 * mxd)) :: LB0)))));
[apply Permutation_app_swap_app | apply Permutation_app_head; apply Permutation_app_swap_app].
+ cbn [t_levels t_depth pf_mxd]. intros i li Hli.
destruct (Nat.eq_dec i depth) as [-> | NE].
* rewrite nth_error_lupd_eq in Hli by lia. injection Hli as <-.
split; [cbn; unfold ST_eatws; lia|]. split; [cbn; unfold ST_finish; lia|]. split; [cbn [tl_cs tl_cbs tl_cur l' pf_mxd]; rewrite Hcs; cbn [jopt pf_mxd]; split; [exact Hc | exact J3]|].
rewrite Nat.ltb_irrefl, Nat.eqb_refl. exists CAny, false. split; [reflexivity|]. split; [exact I|]. cbn. split; [exact Hn0 | exact Hnbs0].
* rewrite nth_error_lupd_neq in Hli by congruence.
eapply (lvl_cur_agree rsegs S4F); [exact (LV i li Hli) | exact AGL3 |].
intros b Hb. unfold BL. apply in_concat. exists (lvl_blocks li). split; [| exact Hb]. apply in_map.
eapply (nth_error_In _ i). rewrite nth_error_lupd_neq by congruence. exact Hli.
+ unfold cur_st. cbn [t_levels t_depth t_objbs pf_mxd]. rewrite nth_error_lupd_eq by lia. reflexivity.
Qed.
#[using="SHRINK"] Lemma seg_asep :
forall (pf : pe_fix) (q : Z) (LB0 : list blk) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (ts : tstate) (l : tlevel)
(cb : byte) (j1 j2 utf : list byte) (sv : pe_saved) (errv : word) (T : TSet)
(x1 gp t0 t1 t2 a3 a4 a5 a6 a7 s6 s7 s8 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC HIx pf lo ->
PE_INV HIx pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_array_sep ->
t_co ts < pf_len pf ->

(forall m' ss' a0' a1' a2' a3',
(bv_unsigned cb = 44 /\ ss' = ST_array_after_sep) ->
PE_INV HIx pf q LB0 payload me lo m' md A (ts_set_level ts (TL ST_eatws ss' (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) cb j1 j2 utf sv errv ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_BREAK2 (t_co ts) x1 gp t0 t1 t2 a0' a1' a2' a3' a4 a5 a6 a7
(Z_to_bv 64 q) s6 s7 s8 (Z_to_bv 64 (Z.of_nat (t_depth ts))) s10 t3 t4 t5 t6 F fc m') md) T) ->

(forall m' md' A' cbs' errv' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F' fc' kids,
bv_unsigned cb = 93 -> tl_cs l = Some (Sarr kids) ->
PE_INV HIx pf q LB0 payload me lo m' md' A'
(TST (t_depth ts) (lupd (t_levels ts) (t_depth ts) (TL ST_eatws ST_finish (tl_cur l) (tl_cs l) cbs' (tl_name l) (tl_nbs l)))
(t_co ts) (t_pb ts) (t_pbs ts) (t_x ts) (t_obj ts) (t_objs ts) (t_objbs ts))
cb j1 j2 utf sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_BREAK (t_co ts) x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F' fc' m') md') T) ->

(forall a1' a2' a3',
bv_unsigned cb <> 44 -> bv_unsigned cb <> 93 ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_ERR (t_co ts) x1 gp t0 t1 t2 (Z_to_bv 64 8) a1' a2' a3' a4 a5 a6 a7
(Z_to_bv 64 q) s6 s7 s8 (Z_to_bv 64 (Z.of_nat (t_depth ts))) s10 t3 t4 t5 t6 F fc m) md) T) ->
realizes rsegs (mkCfg (pe_ms rsegs pf (pe_jt ST_array_sep) (t_co ts) x1 gp t0 t1 t2
(Z_to_bv 64 0) (Z_to_bv 64 (tl_st l)) (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) a3 a4 a5 a6 a7
(Z_to_bv 64 q) s6 s7 s8 (Z_to_bv 64 (Z.of_nat (t_depth ts))) s10 t3 t4 t5 t6 F fc m) md) T.
Proof.
intros until fc. intros STC INV Hl Hst Hco Kbreak Kclose Kerr. pose proof INV as INV0.
pose proof STC as (LO & LOS & SPA & HT & SP0 & LEN & SB0 & SBL).
destruct INV as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof REST as (HP & LV & _).
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl_]; pe_gen fl_; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
unfold tok_cells, tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in TOK. unfold pe_frame in FR. unfold pe_ms in *. cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
unfold_consts.
assert (SB1 : 1 <= sb).
{ pose proof (proj1 (PE_REST_base HIx _ _ _ _ _ _ _ _ _ _ _ REST)) as BASE.
pose proof BASE as (HP0 & _ & _ & _ & _ & PLOC & _). unfold payload_loc in PLOC. cbn [pf_len pf_sb pf_spf] in PLOC.
destruct PLOC as [L0 | [STKM | ([ba bn] & Hb & Hb1 & Hb2)]].
{ lia. }
{ unfold PE_FRAME in *.
lia. }
pose proof (heap_blk S4L HIx _ _ _ _ ba bn HP0 ltac:(unfold pe_blocks; apply in_or_app; right; right; right; exact Hb)) as (_ & _ & Hba & _).
cbn [blk_addr fst] in Hb1. lia. }
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocks; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, (32 * mxd)) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocks; apply in_or_app; right; right; left; reflexivity).
pose proof (heap_blk S4L HIx _ _ _ _ tk 72 HP INtk) as (_ & Htal & Htlo & Hthi & _).
pose proof (heap_blk S4L HIx _ _ _ _ q (32 * mxd) HP INq) as (_ & Hqal & Hqlo & Hqhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ q (32 * mxd) HP INq) as Himg_q. cbn [hl_img_lo hl_img_hi S4L pf_mxd] in Himg_q.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hthi, Hqhi.
assert (Htq : tk <> q).
{ pose proof (heap_blk_nodup S4L HIx _ _ _ _ HP) as ND. unfold pe_blocks in ND. rewrite map_app in ND. apply NoDup_app_remove_l in ND.
cbn [map blk_addr fst pf_mxd] in ND. apply List.NoDup_cons_iff in ND as [Hni _]. intros E. apply Hni. left. symmetry. exact E. }
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ tk 72 q (32 * mxd) HP INtk INq Htq) as Hdtq.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L pf_mxd] in MI.
pose proof (wmono_refl rsegs m) as WM.
pose proof (LV depth l Hl) as LVd. pose proof LVd as (ST26 & SS26 & _ & Md).
rewrite Nat.ltb_irrefl, Nat.eqb_refl in Md. destruct Md as (c0 & hn0 & Hmode & CLS0 & NM0).

pose proof (TSK depth l Hl) as Ld. unfold srec_cells in Ld. cbn [pf_mxd] in Ld.
remember (q + 32 * Z.of_nat depth) as bse eqn:Hbse in Ld.
assert (HbseR : q <= bse /\ bse + 32 <= q + (32 * mxd)) by (subst bse; lia).
pose proof (munch_refl [(bse, bse + 32)] m) as MU.
pose proof (bv_unsigned_in_range 8 cb) as CBR; unfold bv_modulus in CBR; cbn in CBR.
stash PB. stash REST. stash TSK. clear HP LV.
apply rz_evt; [exact MOK|]. rewrite Hst. unfold ST_array_sep. cbn [pe_jt pf_mxd].
replace (q + 32 * Z.of_nat depth) with bse by lia.
bst. change (zxb cb) with (Z_to_bv 64 (bv_unsigned cb)). bst.

assert (TAIL : forall ss' mc a0v a1v a2v a3v,
(bv_unsigned cb = 44 /\ ss' = ST_array_after_sep) ->
rw_cells rsegs mc bse [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 ss'); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (tl_cur l)); C8 (Z_to_bv 64 (tl_name l))] ->
munch [(bse, bse + 32)] m mc -> wmono rsegs m mc -> mem_inv rsegs mc ->
(forall H : rw_cells rsegs mc tk [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 pb); C4 (Z_to_bv 64 mxd); C4 (Z_to_bv 64 (Z.of_nat depth)); C4 isd; C4 stpos;
C4 (Z_to_bv 64 co); C4 err; C4 ucs; C4 high; C1 quote; CB 7 (repeat (Z_to_bv 8 0) 7); C8 (Z_to_bv 64 q); C4 (Z_to_bv 64 fl); C4 (Z_to_bv 64 0)], True) ->
rw_cells rsegs mc tk [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 pb); C4 (Z_to_bv 64 mxd); C4 (Z_to_bv 64 (Z.of_nat depth)); C4 isd; C4 stpos;
C4 (Z_to_bv 64 co); C4 err; C4 ucs; C4 high; C1 quote; CB 7 (repeat (Z_to_bv 8 0) 7); C8 (Z_to_bv 64 q); C4 (Z_to_bv 64 fl); C4 (Z_to_bv 64 0)] ->
rw_cells rsegs mc spf [C8 (Z_to_bv 64 obj); CB 16 j1; C4 (nbw j2); CB 3 (skipn 4 j2); C1 cb; CB 8 utf;
C8 (pe_s11 sv); C8 (pe_s10 sv); C8 (pe_s9 sv); C8 (pe_s8 sv); C8 (pe_s7 sv); C8 (pe_s6 sv);
C8 (pe_s5 sv); C8 (pe_s4 sv); C8 (pe_s3 sv); C8 (pe_s2 sv); C8 (pe_s1 sv); C8 (pe_s0 sv); C8 (pe_ra sv)] ->
realizes rsegs (mkCfg (MS (mkR x1 (Z_to_bv 64 spf) gp (Z_to_bv 64 490496) t0 t1 t2 (Z_to_bv 64 tk) (Z_to_bv 64 oldl)
a0v a1v a2v a3v a4 a5 a6 a7
(Z_to_bv 64 newl) (Z_to_bv 64 lenr) (Z_to_bv 64 q) (Z_to_bv 64 (sb + co)) s6 s7 s8 (Z_to_bv 64 (Z.of_nat depth)) s10 (Z_to_bv 64 79040) t3 t4 t5 t6)
F (Z_to_bv 64 PE_BREAK2) fc None mc (seg_rom rsegs)) md) T).
{ intros ss' mc a0v a1v a2v a3v Hss L8 MU' WM' MI' _ TOK' FR'.
unstash PB. unstash REST. unstash TSK.
assert (SS' : 0 <= ss' <= 26) by (unfold ST_array_after_sep in Hss; lia).
rename L8 into L5.
set (l' := TL ST_eatws ss' (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)).
assert (HW : Forall (pe_wtq (PEF tk oldl newl len lenr sb spf pmd mxd fl) q) [(bse, bse + 32)]).
{ apply Forall_cons; [right; cbn [fst snd pf_mxd]; lia | apply Forall_nil]. }
subst bse. apply (Kbreak mc ss' a0v a1v a2v a3v Hss). split.
- unfold PE_CORE, ts_set_level; cbn. split; [rewrite lupd_length; exact LEN32|]. split; [exact D32|]. split; [lia|]. split; [reflexivity|].
split; [exact TOK'|]. split; [| split; [exact Hpb | split; [| exact FR']]].
+ eapply (pbuf_wtq HIx) with (ts := ts0); [exact STC | exact (proj1 REST) | exact PB | exact MU' | exact WM' | exact HW].
+ eapply (tstack_put rsegs m _ q levels depth l' []); [exact TSK | lia | exact MU' | exact WM' | intros; exact I | exact L5].
- assert (REST' : PE_REST HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo mc md A ts0 errv).
{ eapply (PE_REST_private_write HIx) with (ts := ts0) in REST; [exact REST | exact STC | exact MU' | exact WM' | exact MI' | apply pe_wtq_private; exact HW]. }
destruct REST' as (HP' & LV' & OBJ' & ST' & ERR' & STR' & PLEN' & SBin' & HPR' & MDV' & JCG').
unfold ts_set_level; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd].
split.
{ match goal with |- HEAP _ _ _ ?L _ _ => replace L with (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0); [exact HP' |] end.
unfold pe_blocks, tstate_blocks, ts0; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd].
match goal with |- context [map lvl_blocks (lupd ?lv ?d ?x)] => rewrite (map_lupd_same lvl_blocks lv d x l Hl eq_refl) end. reflexivity. } split; [| split; [| split; [exact ST' | split; [exact ERR' | split; [exact STR' | split; [exact PLEN' | split; [exact SBin' | split; [exact HPR' | split; [exact MDV' | exact JCG']]]]]]]]].
+ assert (MODE0 : c0 = CArr /\ hn0 = false).
{ rewrite Hst in Hmode. unfold ST_array_sep in Hmode. clear - Hmode SS26.
assert (R : 0 <= tl_ss l <= 26) by lia. enum_z R (tl_ss l); vm_compute in Hmode; split; congruence. }
destruct MODE0 as [-> ->].
intros i li Hli. unfold ts0 in Hli. cbn [t_levels t_depth pf_mxd] in Hli. destruct (PeanoNat.Nat.eq_dec i depth) as [-> | NE].
* rewrite nth_error_lupd_eq in Hli by lia. injection Hli as <-.
destruct Hss as [_ Ess]; rewrite Ess in *.
eapply lvl_cur_restate with (c' := CArr); [exact (LV' depth l Hl) | exact Hmode | vm_compute; reflexivity | unfold ST_eatws; lia | unfold ST_array_after_sep; lia | left; reflexivity].
* rewrite nth_error_lupd_neq in Hli by congruence. exact (LV' i li Hli).
+ unfold cur_st in *; cbn in *. rewrite nth_error_lupd_eq by lia. cbn [tl_st pf_mxd]. unfold ST_eatws. cbn.
revert OBJ'. rewrite Hl, Hst. cbn. intros OBJ'. exact OBJ'. }
destruct (Z.eq_dec (bv_unsigned cb) 44) as [C44 | N44].
- bst. if_truex. bst_to 0x23d14.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
apply evt_RZ_done; eapply (TAIL ST_array_after_sep mc _ _ _ _); [split; [exact C44 | reflexivity] | exact Ld | exact MU | exact WM | exact MI | intros; exact I | exact TOK | exact FR] end.
- bst. if_falsex. bst.
destruct (Z.eq_dec (bv_unsigned cb) 93) as [C93 | N93].
+ bst. if_falsex. subst bse. apply evt_RZ_done.
assert (MODE0 : c0 = CArr) by (rewrite Hst in Hmode; unfold ST_array_sep in Hmode; clear - Hmode SS26; assert (R : 0 <= tl_ss l <= 26) by lia; enum_z R (tl_ss l); vm_compute in Hmode; congruence).
subst c0. destruct (tl_cs l) as [[| | | |okids|kids]|] eqn:Ecs; try (exfalso; exact CLS0).
eapply (seg_asep_close (PEF tk oldl newl len lenr sb spf pmd mxd fl)) with (ts := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) (l := l);
[exact STC | exact INV0 | exact Hl | exact Hst | exact Ecs | cbn; lia |].
cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd]. intros until fc'. intros INV' FS' FRM'. rewrite Ecs in INV'. eapply Kclose; eauto.
+ bst. if_truex. bst. bst.
subst bse. apply evt_RZ_done. eapply Kerr; [exact N44 | exact N93].
Qed.
End PeAsep.

End RC__1.
End Mq1.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UBpZ UT7i Uv6q UzWc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup.
Import UEQM.
Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0.
Import UC8c.Mq0.
Import Qsw7 QJjn QkMG.
Import UG8z.
Import UBpZ UT7i Uv6q.
Import UzWc.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.

Ltac enum_z H v :=
let rec go k := lazymatch k with
| 27%nat => exfalso; lia
| _ => let kz := eval vm_compute in (Z.of_nat k) in
let E := fresh "E" in
destruct (Z.eq_dec v kz) as [E | ?]; [ rewrite ?E in * | go (S k) ]
end in go 0%nat.
Import Q6q3.
Import Tk2Gen.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma lvl_mode_ws_same : forall st st' ss,
zin st ws_states = true -> zin st' ws_states = true -> lvl_mode st' ss = lvl_mode st ss.
Proof.
intros st st' ss H H'.
assert (C : forall x, zin x ws_states = true -> x = 0 \/ x = 4 \/ x = 5 \/ x = 6 \/ x = 7).
{ intros x Hx. unfold zin, ws_states in Hx. cbn in Hx. rewrite !Bool.orb_true_iff in Hx. rewrite !Z.eqb_eq in Hx. intuition lia. }
destruct (C st H) as [->|[->|[->|[->| ->]]]]; destruct (C st' H') as [->|[->|[->|[->| ->]]]]; reflexivity.
Qed.

Section PeCstart.
Variable HIx : heap_iface S4L.
Hypothesis MEMMOVE : memmove_stmt.

Definition ts_set_level (ts : tstate) (l : tlevel) : tstate :=
TST (t_depth ts) (lupd (t_levels ts) (t_depth ts) l) (t_co ts) (t_pb ts) (t_pbs ts) (t_x ts) (t_obj ts) (t_objs ts) (t_objbs ts).
Definition ts_set_pbs (ts : tstate) (pbs : list blk) : tstate :=
TST (t_depth ts) (t_levels ts) (t_co ts) (t_pb ts) pbs (t_x ts) (t_obj ts) (t_objs ts) (t_objbs ts).

#[using="MEMMOVE"] Lemma seg_cstart :
forall (pf : pe_fix) (q : Z) (LB0 : list blk) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (ts : tstate) (l : tlevel)
(cb : byte) (j1 j2 utf : list byte) (sv : pe_saved) (errv : word) (T : TSet)
(x1 gp t0 t1 t2 a0 a3 a4 a5 a6 a7 s6 s7 s8 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC HIx pf lo ->
PE_INV HIx pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_comment_start ->
t_co ts < pf_len pf ->

(forall m' md' A' st' pbs' errv' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F' fc',
(bv_unsigned cb = 42 /\ st' = ST_comment) \/ (bv_unsigned cb = 47 /\ st' = ST_comment_eol) ->
PE_INV HIx pf q LB0 payload me lo m' md' A' (ts_set_pbs (ts_set_level ts (TL st' (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) pbs') cb j1 j2 utf sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_BREAK (t_co ts) x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F' fc' m') md') T) ->

(forall m' md' A' st' errv' x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F' fc',
(bv_unsigned cb = 42 /\ st' = ST_comment) \/ (bv_unsigned cb = 47 /\ st' = ST_comment_eol) ->
PE_INV HIx pf q LB0 payload me lo m' md' A' (ts_set_level ts (TL st' (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) cb j1 j2 utf sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_ERR (t_co ts) x1' gp' t0' t1' t2' (Z_to_bv 64 16) a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F' fc' m') md') T) ->

(forall a0' a2',
bv_unsigned cb <> 42 -> bv_unsigned cb <> 47 ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_ERR (t_co ts) x1 gp t0 t1 t2 (Z_to_bv 64 13) a0' a2' a3 a4 a5 a6 a7
(Z_to_bv 64 q) s6 s7 s8 (Z_to_bv 64 (Z.of_nat (t_depth ts))) s10 t3 t4 t5 t6 F fc m) md) T) ->
realizes rsegs (mkCfg (pe_ms rsegs pf (pe_jt ST_comment_start) (t_co ts) x1 gp t0 t1 t2
a0 (Z_to_bv 64 (tl_st l)) (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) a3 a4 a5 a6 a7
(Z_to_bv 64 q) s6 s7 s8 (Z_to_bv 64 (Z.of_nat (t_depth ts))) s10 t3 t4 t5 t6 F fc m) md) T.
Proof.
intros until fc. intros STC INV Hl Hst Hco Kbreak Kerr16 Kerr13.
pose proof STC as (LO & LOS & SPA & HT & SP0 & LEN & SB0 & SBL).
destruct INV as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof REST as (HP & LV & _).
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl_]; pe_gen fl_; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
unfold tok_cells, tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK. unfold pe_frame in FR. unfold pe_ms in *. cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
unfold_consts.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocks; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, (32 * mxd)) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocks; apply in_or_app; right; right; left; reflexivity).
pose proof (heap_blk S4L HIx _ _ _ _ tk 72 HP INtk) as (_ & Htal & Htlo & Hthi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ tk 72 HP INtk) as Himg_t. cbn [hl_img_lo hl_img_hi S4L] in Himg_t.
pose proof (heap_blk S4L HIx _ _ _ _ q (32 * mxd) HP INq) as (_ & Hqal & Hqlo & Hqhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ q (32 * mxd) HP INq) as Himg_q. cbn [hl_img_lo hl_img_hi S4L] in Himg_q.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hthi, Hqhi.
assert (Htq : tk <> q).
{ pose proof (heap_blk_nodup S4L HIx _ _ _ _ HP) as ND. unfold pe_blocks in ND. rewrite map_app in ND. apply NoDup_app_remove_l in ND.
cbn [map blk_addr fst pf_mxd] in ND. apply List.NoDup_cons_iff in ND as [Hni _]. intros E. apply Hni. left. symmetry. exact E. }
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ tk 72 q (32 * mxd) HP INtk INq Htq) as Hdtq.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (wmono_refl rsegs m) as WM.
pose proof (LV depth l Hl) as LVd. pose proof LVd as (ST26 & SS26 & _ & Md).
rewrite Nat.ltb_irrefl, Nat.eqb_refl in Md. destruct Md as (c0 & hn0 & Hmode & CLS0 & NM0).
pose proof (TSK depth l Hl) as Ld. unfold srec_cells in Ld.
remember (q + 32 * Z.of_nat depth) as bse eqn:Hbse in Ld.
assert (HbseR : q <= bse /\ bse + 32 <= q + (32 * mxd)) by (subst bse; lia).
pose proof (munch_refl [(bse, bse + 32)] m) as MU.
pose proof (bv_unsigned_in_range 8 cb) as CBR; unfold bv_modulus in CBR; cbn in CBR.
stash PB. stash REST. stash TSK. clear HP LV.
apply rz_evt; [exact MOK|]. rewrite Hst. unfold ST_comment_start. cbn [pe_jt].
replace (q + 32 * Z.of_nat depth) with bse by lia.
bst. change (zxb cb) with (Z_to_bv 64 (bv_unsigned cb)). bst.

assert (TAIL : forall st' a1v,
(bv_unsigned cb = 42 /\ st' = ST_comment) \/ (bv_unsigned cb = 47 /\ st' = ST_comment_eol) ->
evt rsegs (RZ rsegs md T)
(MS (mkR x1 (Z_to_bv 64 spf) gp (Z_to_bv 64 490496) t0 t1 t2 (Z_to_bv 64 tk) (Z_to_bv 64 oldl)
(Z_to_bv 64 st') a1v (Z_to_bv 64 bse) a3 a4 a5 a6 a7
(Z_to_bv 64 newl) (Z_to_bv 64 lenr) (Z_to_bv 64 q) (Z_to_bv 64 (sb + co)) s6 s7 s8 (Z_to_bv 64 (Z.of_nat depth)) s10 (Z_to_bv 64 79040) t3 t4 t5 t6)
F (Z_to_bv 64 0x23834) fc None m (seg_rom rsegs))).
{ intros st' a2v Hst'.
assert (ST'R : 0 <= st' <= 26) by (unfold ST_comment, ST_comment_eol in Hst'; lia).
assert (WS' : zin st' ws_states = true) by (destruct Hst' as [[_ ->]|[_ ->]]; reflexivity).
bstz. bst. bst. bst. bst.

unstash PB. unstash REST. unstash TSK.
set (l1 := TL st' (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)).
set (ts1 := TST depth (lupd levels depth l1) co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs).
assert (HW : Forall (pe_wtq (PEF tk oldl newl len lenr sb spf pmd mxd fl) q) [(bse, bse + 32)]) by (apply Forall_cons; [right; cbn [fst snd pf_mxd]; lia | apply Forall_nil]).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (TSK1 : tstack rsegs mc q (lupd levels depth l1))
by (subst bse; eapply (tstack_put rsegs m _ q levels depth l1 []); [exact TSK | lia | exact MU | exact WM | intros; exact I | exact Ld]);
assert (PB1 : pbuf rsegs mc pbs pb)
by (eapply (pbuf_wtq HIx) with (ts := ts0); [exact STC | exact (proj1 REST) | exact PB | exact MU | exact WM | exact HW]);
assert (REST0 : PE_REST HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo mc md A ts0 errv)
by (eapply (PE_REST_private_write HIx) with (ts := ts0) in REST; [exact REST | exact STC | exact MU | exact WM | exact MI | apply pe_wtq_private; exact HW]);
assert (REST1 : PE_REST HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo mc md A ts1 errv)
end.
{ destruct REST0 as (HP' & LV' & OBJ' & ST' & ERR' & STR' & PLEN' & SBin' & HPR' & MDV' & JCG').
split.
{ match goal with |- HEAP _ _ _ ?L _ _ => replace L with (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0); [exact HP' |] end.
unfold pe_blocks, tstate_blocks, ts0, ts1; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs].
match goal with |- context [map lvl_blocks (lupd ?lv ?d ?x)] => rewrite (map_lupd_same lvl_blocks lv d x l Hl eq_refl) end. reflexivity. }
split; [| split; [| split; [exact ST' | split; [exact ERR' | split; [exact STR' | split; [exact PLEN' | split; [exact SBin' | split; [exact HPR' | split; [exact MDV' | exact JCG']]]]]]]]].
+ intros i li Hli. unfold ts1 in Hli. cbn [t_levels t_depth] in Hli. unfold ts1; cbn [t_depth].
destruct (PeanoNat.Nat.eq_dec i depth) as [-> | NE].
* rewrite nth_error_lupd_eq in Hli by lia. injection Hli as <-.
eapply lvl_cur_restate with (c' := c0); [exact (LV' depth l Hl) | exact Hmode | | exact ST'R | exact SS26 | left; reflexivity].
rewrite <- Hmode. apply lvl_mode_ws_same; [rewrite Hst; reflexivity | exact WS'].
* rewrite nth_error_lupd_neq in Hli by congruence. exact (LV' i li Hli).
+ revert OBJ'. unfold cur_st, ts0, ts1. cbn [t_levels t_depth t_objs t_objbs t_obj]. rewrite nth_error_lupd_eq by lia. cbn [tl_st].
rewrite Hl, Hst. destruct Hst' as [[_ ->]|[_ ->]]; cbn; intros OBJ'; exact OBJ'. }
clear REST TSK PB MU Ld.

pose proof PB1 as (buf & bpos & cap & pre & post & Epbs & Lpre & CORE1).
pose proof (proj1 REST1) as HP1. unfold pe_blocks, tstate_blocks, ts1 in HP1. cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_tk pf_md pf_mxd pf_fl] in HP1.
rewrite Epbs in HP1. cbn [app] in HP1.
pose proof (heap_blk S4L HIx _ _ _ _ buf cap HP1 ltac:(right; left; reflexivity)) as (_ & _ & _ & Hbufhi & _). unfold alloc_ceiling, sp_window_lo, stack_max_size in Hbufhi.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => pose proof (pe_frame_cbyte mc spf obj cb j1 j2 utf sv FR) as SRC end.
pose proof (heap_mem_inv _ _ _ _ _ _ HP1) as MI1. cbn [hl_segs S4L] in MI1.
pose proof REST1 as (_ & _ & _ & ST1 & ERR1 & _).
apply evt_RZ_done.
eapply (memappend_cps HIx MEMMOVE) with (lo := lo) (b := spf + 31) (src := [cb]) (n := 1);
[ exact HP1 | exact CORE1 | lia | exact SRC | reflexivity | left; left; rewrite ?unsigned_lit by lia; lia | lia | lia | lia | .. ]; try alloc_side.
all: try (rewrite ?unsigned_lit by lia; first [exact ST1 | exact ERR1]).
all: try (rewrite ?unsigned_lit by lia; unfold PE_FRAME in *; clia).
intros ms2 md2 (m2 & A2 & r & errv2 & buf' & cap' & RS2 & VM2 & ST2 & HPR2 & ERR2 & HP2 & OUT2).
destruct RS2 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F2 & fc2 & -> & FS2 & FRM2).
cbn [hl_segs hl_tp S4L] in *. rewrite ?(unsigned_lit spf) in ST2 by lia. rewrite ?(unsigned_lit spf) in HPR2 by lia.

set (pbs2 := [(pb, 16); (buf', cap')]).
set (ts2 := TST depth (lupd levels depth l1) co pb pbs2 (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs).
assert (INq2 : In (q, (32 * mxd)) ((objbs ++ concat (map lvl_blocks (lupd levels depth l1))) ++ (tk, 72) :: (q, (32 * mxd)) :: LB0))
by (apply in_or_app; right; right; left; reflexivity).
assert (INtk2 : In (tk, 72) ((objbs ++ concat (map lvl_blocks (lupd levels depth l1))) ++ (tk, 72) :: (q, (32 * mxd)) :: LB0))
by (apply in_or_app; right; left; reflexivity).
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in TOK; [| eapply client_range_block; [exact INtk2 | lia | cbn; lia]]. cbn [hl_segs S4L] in TOK.
apply (tstack_pres_g S4L _ _ _ _ _ _ HPR2 INq2) in TSK1; [| rewrite lupd_length; exact LEN32].
assert (REST2 : PE_REST HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo m2 md2 A2 ts2 errv2).
{ eapply (PE_REST_call_pb HIx) with (ts := ts1) (LBc := (objbs ++ concat (map lvl_blocks (lupd levels depth l1))) ++ (tk, 72) :: (q, (32 * mxd)) :: LB0);
[exact STC | exact REST1 | exact VM2 | exact HPR2 | unfold ts1; cbn [t_objbs t_levels]; intros b Hb; apply in_or_app;
apply in_app_or in Hb; destruct Hb as [Hb|Hb]; [left; apply in_or_app; left; exact Hb | apply in_app_or in Hb; destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; exact Hb | right; right; right; exact Hb]]
| unfold pe_blocks, tstate_blocks; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_tk pf_md pf_mxd pf_fl]; exact HP2
| exact ST2 | exact ERR2]. }
assert (PBany : pbuf rsegs m2 pbs2 pb).
{ destruct OUT2 as [[_ PBS] | (_ & -> & -> & PC)]; [exact PBS|].
exists buf, bpos, cap, pre, post. split; [reflexivity|]. split; [exact Lpre | exact PC]. }
assert (INV2 : PE_INV HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo m2 md2 A2 ts2 cb j1 j2 utf sv errv2).
{ split; [| exact REST2]. unfold PE_CORE, ts2; cbn. split; [rewrite lupd_length; exact LEN32|]. split; [exact D32|]. split; [lia|]. split; [reflexivity|].
split; [exact TOK|]. split; [exact PBany|]. split; [exact Hpb|]. split; [exact TSK1 | exact FR]. }
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2.
clear HP1 HP2 REST1 REST2 CORE1 SRC ST1 ERR1 MI1 TOK FR TSK1 PBany PB1.
reenter MOK2.
destruct OUT2 as [[-> _] | (-> & -> & -> & _)].
- bst. if_true. apply evt_RZ_done. eapply Kbreak; [exact Hst' | exact INV2 | exact FS2 | exact FRM2].
- replace (Z_to_bv 64 (2^64 - 1)) with (Z_to_bv 64 (-1)) by (apply bv_eq; vm_compute; reflexivity).
bst. if_false. bst. bst. bst. apply evt_RZ_done. eapply Kerr16; [exact Hst' | | exact FS2 | exact FRM2].
unfold ts2, pbs2 in INV2. rewrite <- Epbs in INV2. exact INV2. }

destruct (Z.eq_dec (bv_unsigned cb) 42) as [C42 | N42].
- bst. if_truex. bst. apply (TAIL ST_comment). left. split; [exact C42 | reflexivity].
- bst. if_falsex. bst. destruct (Z.eq_dec (bv_unsigned cb) 47) as [C47 | N47].
+ bst. if_falsex. bst. bst. apply (TAIL ST_comment_eol). right. split; [exact C47 | reflexivity].
+ bst. if_truex. bst. bst. subst bse. apply evt_RZ_done. eapply Kerr13; [exact N42 | exact N47].
Qed.
End PeCstart.

End RC__1.
End Mq2.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QmZZ. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UPZI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup.
Import UEQM.
Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0.
Import UC8c.Mq0.
Import Qsw7 QJjn QkMG.
Import UG8z Udyh.Mq0.
Import QmZZ.
Import UPZI.Mq1 UPZI.Mq4.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.
Import Q6q3.
Import TopUbTac Tk1Reset Tk2Gen.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section PeFinish.
Variable HIx : heap_iface S4L.
Hypothesis PUT : put_stmt_P HIx.

#[using="Type"] Lemma lvl_cur_pop : forall m dp i li, i <> S dp -> lvl_cur rsegs S4F m (S dp) i li -> lvl_cur rsegs S4F m dp i li.
Proof.
intros m dp i li Hne (R1 & R2 & J & M). split; [exact R1|]. split; [exact R2|]. split; [exact J|].
destruct (Nat.lt_ge_cases i dp) as [Hlt | Hge].
- rewrite (proj2 (Nat.ltb_lt i dp) Hlt). rewrite (proj2 (Nat.ltb_lt i (S dp))) in M by lia. exact M.
- rewrite (proj2 (Nat.ltb_ge i dp) Hge). destruct (Nat.eq_dec i dp) as [-> | Hne2].
+ rewrite Nat.eqb_refl. rewrite (proj2 (Nat.ltb_lt dp (S dp))) in M by lia.
destruct M as [(E & C & N) | (E & C & N)]; rewrite E.
* exists CArr, false. split; [apply lvl_mode_aadd | split; [exact C | exact N]].
* exists CObj, true. split; [apply lvl_mode_ovadd | split; [exact C | exact N]].
+ rewrite (proj2 (Nat.eqb_neq i dp) Hne2). rewrite (proj2 (Nat.ltb_ge i (S dp))) in M by lia.
rewrite (proj2 (Nat.eqb_neq i (S dp)) Hne) in M. exact M.
Qed.

#[using="PUT"] Lemma seg_finish :
forall (pf : pe_fix) (q : Z) (LB0 : list blk) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (ts : tstate) (l : tlevel)
(cb : byte) (j1 j2 utf : list byte) (sv : pe_saved) (errv : word) (T : TSet)
(x1 gp t0 t1 t2 a3 a4 a5 a6 a7 s6 s7 s8 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC HIx pf lo ->
PE_INV HIx pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_finish ->

((t_depth ts = 0)%nat ->
forall a0' a1' a2',
realizes rsegs (mkCfg (pe_ms rsegs pf PE_OUT (t_co ts) x1 gp t0 t1 t2 a0' a1' a2' a3 a4 a5 a6 a7
(Z_to_bv 64 q) s6 s7 s8 (Z_to_bv 64 0) s10 t3 t4 t5 t6 F fc m) md) T) ->

(forall m' md' A' errv' dp lp x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F' fc',
t_depth ts = S dp ->
nth_error (t_levels ts) dp = Some lp -> (tl_st lp = ST_array_add \/ tl_st lp = ST_ovadd) ->
PE_INV HIx pf q LB0 payload me lo m' md' A'
(TST dp (lupd (t_levels ts) (S dp) lvl_reset) (t_co ts) (t_pb ts) (t_pbs ts) (t_x ts) (tl_cur l) (tl_cs l) (tl_cbs l))
cb j1 j2 utf sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_REDO (t_co ts) x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F' fc' m') md') T) ->
realizes rsegs (mkCfg (pe_ms rsegs pf (pe_jt ST_finish) (t_co ts) x1 gp t0 t1 t2
(Z_to_bv 64 0) (Z_to_bv 64 (tl_st l)) (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) a3 a4 a5 a6 a7
(Z_to_bv 64 q) s6 s7 s8 (Z_to_bv 64 (Z.of_nat (t_depth ts))) s10 t3 t4 t5 t6 F fc m) md) T.
Proof.
intros until fc. intros STC INV Hl Hst Kout Kredo.
pose proof STC as (LO & LOS & SPA & HT & SP0 & LEN & SB0 & SBL).
destruct INV as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
apply (PE_REST_base HIx) in REST as (BASE & LV & OBJ).
pose proof (proj1 BASE) as HP.
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl_]; pe_gen fl_; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
assert (MXD1 : 1 <= mxd <= 32) by (pose proof STC as STC1; apply PE_STATIC_mxd in STC1; exact (proj1 STC1)).
unfold tok_cells, tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in TOK. unfold pe_frame in FR. unfold pe_ms in *. cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
unfold_consts.

assert (Eobjbs : objbs = []).
{ revert OBJ. unfold cur_st. cbn [t_levels t_depth t_objbs pf_mxd]. rewrite Hl, Hst. cbn. intros E; exact E. }
subst objbs.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs []) in *.
assert (INtk : In (tk, 72) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocks; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, (32 * mxd)) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocks; apply in_or_app; right; right; left; reflexivity).
pose proof (heap_blk S4L HIx _ _ _ _ tk 72 HP INtk) as (_ & Htal & Htlo & Hthi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ tk 72 HP INtk) as Himg_t. cbn [hl_img_lo hl_img_hi S4L pf_mxd] in Himg_t.
pose proof (heap_blk S4L HIx _ _ _ _ q (32 * mxd) HP INq) as (_ & Hqal & Hqlo & Hqhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ q (32 * mxd) HP INq) as Himg_q. cbn [hl_img_lo hl_img_hi S4L pf_mxd] in Himg_q.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hthi, Hqhi.
pose proof (heap_blk_nodup S4L HIx _ _ _ _ HP) as ND.
assert (Htq : tk <> q).
{ generalize ND; intros ND'. unfold pe_blocks in ND'. rewrite map_app in ND'. apply NoDup_app_remove_l in ND'.
cbn [map blk_addr fst pf_tk pf_md pf_mxd pf_fl] in ND'. apply List.NoDup_cons_iff in ND' as [Hni _]. intros E. apply Hni. left. symmetry. exact E. }
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ tk 72 q (32 * mxd) HP INtk INq Htq) as Hdtq.
assert (NQ0 : forall k, ~ In (q, k) LB0).
{ intros k. generalize ND; intros ND'. unfold ts0, pe_blocks, tstate_blocks in ND'. cbn [t_pbs t_objbs t_levels pf_tk pf_md pf_mxd pf_fl] in ND'.
rewrite <- !app_assoc in ND'. exact (nodup_mid_notin _ _ _ _ _ _ _ _ k ND'). }
assert (NT0 : forall k, ~ In (tk, k) LB0).
{ intros k. generalize ND; intros ND'. unfold ts0, pe_blocks, tstate_blocks in ND'. cbn [t_pbs t_objbs t_levels pf_tk pf_md pf_mxd pf_fl] in ND'.
rewrite <- !app_assoc in ND'. exact (nodup_mid_notin_r _ _ _ _ _ _ _ _ k ND'). }
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L pf_mxd] in MI.
pose proof (LV depth l Hl) as LVd. pose proof LVd as (ST26 & SS26 & JO & Md).
rewrite Nat.ltb_irrefl, Nat.eqb_refl in Md. destruct Md as (c0 & hn0 & Hmode & CLS0 & NM0).

assert (Ehn : hn0 = false).
{ revert Hmode. rewrite Hst. unfold lvl_mode, ST_finish. cbn -[zin andb].
cbn [zin existsb Z.eqb ws_states val_states esc_states app ST_eatws ST_start ST_finish ST_null ST_comment_start ST_comment ST_comment_eol ST_comment_end
ST_string ST_string_escape ST_escape_unicode ST_esc_need_escape ST_esc_need_u ST_boolean ST_number ST_array ST_array_add ST_array_sep
ST_ofs ST_ofield ST_ofend ST_ovalue ST_ovadd ST_osep ST_array_after_sep ST_ofs_after_sep ST_inf andb orb pf_mxd].
assert (CASES : exists k : nat, (k <= 26)%nat /\ tl_ss l = Z.of_nat k) by (exists (Z.to_nat (tl_ss l)); split; lia).
destruct CASES as (k & Hk & Ek). rewrite Ek.
do 27 (destruct k as [|k]; [cbn; intros E; first [discriminate E | injection E as _ <-; reflexivity] |]). exfalso; lia. }
subst hn0. cbn [name_ok pf_mxd] in NM0. destruct NM0 as [Hn0 Hnbs0].
pose proof (TSK depth l Hl) as Ld. unfold srec_cells in Ld.
remember (q + 32 * Z.of_nat depth) as bse eqn:Hbse in Ld.
assert (HbseR : q <= bse /\ bse + 32 <= q + (32 * mxd)) by (subst bse; lia).
stash PB. stash BASE. stash TSK. stash LV. clear OBJ HP.
apply rz_evt; [exact MOK|]. rewrite Hst. unfold ST_finish. cbn [pe_jt pf_mxd].
destruct depth as [|dp].
{
bst. if_false. bst. apply evt_RZ_done. apply (Kout eq_refl). }
replace (q + 32 * Z.of_nat (S dp)) with bse by lia.
bst. if_truex. bst. bst.

assert (Hdp : (dp < length levels)%nat) by lia.
destruct (nth_error levels dp) as [lp|] eqn:Hlp; [| apply nth_error_None in Hlp; lia].
assert (LVp : lvl_cur rsegs S4F m (S dp) dp lp) by (unstash LV; exact (LV dp lp Hlp)).
assert (STp : tl_st lp = ST_array_add \/ tl_st lp = ST_ovadd).
{ destruct LVp as (_ & _ & _ & Mp). replace (dp <? S dp)%nat with true in Mp by (symmetry; apply Nat.ltb_lt; lia).
destruct Mp as [(E & _) | (E & _)]; [left | right]; exact E. }

set (cur := tl_cur l) in *. set (cs := tl_cs l) in *. set (cbs := tl_cbs l) in *.
assert (Ecur0 : tl_cur l = cur) by reflexivity. assert (Ecs0 : tl_cs l = cs) by reflexivity. assert (Ecbs0 : tl_cbs l = cbs) by reflexivity.
clearbody cur cs cbs.
set (LBput := (pbs ++ concat (map lvl_blocks (lupd levels (S dp) lvl_reset))) ++ (tk, 72) :: (q, (32 * mxd)) :: LB0).
assert (PERM0 : Permutation (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0) (cbs ++ LBput)).
{ unfold pe_blocks, tstate_blocks, ts0, LBput. cbn [t_pbs t_objbs t_levels pf_tk pf_md pf_mxd pf_fl]. rewrite app_nil_l. rewrite <- !app_assoc.
apply (Permutation_trans (l' := pbs ++ (cbs ++ (concat (map lvl_blocks (lupd levels (S dp) lvl_reset)) ++ (tk, 72) :: (q, (32 * mxd)) :: LB0)))).
- apply Permutation_app_head. rewrite (app_assoc cbs). apply Permutation_app_tail.
replace cbs with (lvl_blocks l) by (unfold lvl_blocks; rewrite Hnbs0, app_nil_r, Ecbs0; reflexivity).
apply concat_lupd_empty; [exact Hl | reflexivity].
- apply Permutation_app_swap_app. }
assert (PERM1 : Permutation (cbs ++ LBput) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0
(TST dp (lupd levels (S dp) lvl_reset) co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) cur cs cbs))).
{ unfold pe_blocks, tstate_blocks, LBput. cbn [t_pbs t_objbs t_levels pf_tk pf_md pf_mxd pf_fl]. rewrite <- !app_assoc. apply Permutation_app_swap_app. }
assert (INqP : In (q, (32 * mxd)) LBput) by (unfold LBput; apply in_or_app; right; right; left; reflexivity).
assert (INtkP : In (tk, 72) LBput) by (unfold LBput; apply in_or_app; right; left; reflexivity).
assert (LB0P : incl LB0 LBput) by (unfold LBput; intros b Hb; apply in_or_app; right; right; right; exact Hb).

set (BL := concat (map lvl_blocks (lupd levels (S dp) lvl_reset))).
assert (BLP : incl BL LBput) by (unfold LBput; intros b Hb; apply in_or_app; left; apply in_or_app; right; exact Hb).
assert (BLfacts : forall a k, In (a, k) BL -> In (a, k) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0) /\ a <> tk /\ a <> q /\ a <> cur).
{ unstash BASE. pose proof (proj1 BASE) as HP'. intros a k Hin.
assert (HinP : In (a, k) (cbs ++ LBput)) by (apply in_or_app; right; apply BLP; exact Hin).
assert (HinL : In (a, k) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (eapply Permutation_in; [apply Permutation_sym; exact PERM0 | exact HinP]).
split; [exact HinL|].
pose proof (Permutation_NoDup (Permutation_map blk_addr PERM0) ND) as NDc.
unfold LBput in NDc. fold BL in NDc.
assert (NDc' : List.NoDup (map blk_addr (cbs ++ pbs ++ BL ++ (tk, 72) :: (q, (32 * mxd)) :: LB0))) by (rewrite <- (app_assoc pbs) in NDc; exact NDc).
split; [| split].
- intros ->. rewrite !map_app in NDc'. apply NoDup_app_remove_l in NDc'. apply NoDup_app_remove_l in NDc'.
eapply (NoDup_app_in2 _ _ tk NDc'); [exact (in_map blk_addr _ _ Hin) | cbn; left; reflexivity].
- intros ->. rewrite !map_app in NDc'. apply NoDup_app_remove_l in NDc'. apply NoDup_app_remove_l in NDc'.
eapply (NoDup_app_in2 _ _ q NDc'); [exact (in_map blk_addr _ _ Hin) | cbn; right; left; reflexivity].
- intros ->. rewrite (app_assoc pbs) in NDc'. rewrite map_app in NDc'.
eapply (NoDup_app_in2 _ _ cur NDc'); [| rewrite !map_app; apply in_or_app; left; apply in_or_app; right; exact (in_map blk_addr _ _ Hin)].
destruct cs as [s|] eqn:Ecs; cbn [jopt pf_mxd] in JO.
+ destruct JO as [Hc J]. pose proof ND as NDx.
eapply (Permutation_NoDup (Permutation_map blk_addr PERM0)) in NDx. rewrite map_app in NDx. apply NoDup_app_remove_r in NDx.
destruct (jval_hdr rsegs S4F s m cbs cur 1 J NDx) as (n & _ & _ & _ & _ & _ & INc & _). exact (in_map blk_addr _ _ INc).
+
destruct JO as [Hc0 _]. pose proof (heap_blk S4L HIx _ _ _ _ cur k HP' HinL) as (_ & _ & Ha0 & _). exfalso. lia. }
assert (CBSfacts : forall a k, In (a, k) cbs -> In (a, k) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0) /\ a <> tk /\ a <> q).
{ intros a k Hin.
assert (HinL : In (a, k) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (eapply Permutation_in; [apply Permutation_sym; exact PERM0 | apply in_or_app; left; exact Hin]).
split; [exact HinL|].
pose proof (Permutation_NoDup (Permutation_map blk_addr PERM0) ND) as NDc. rewrite map_app in NDc.
split; intros ->.
- eapply (NoDup_app_in2 _ _ tk NDc); [exact (in_map blk_addr _ _ Hin) | exact (in_map blk_addr _ _ INtkP)].
- eapply (NoDup_app_in2 _ _ q NDc); [exact (in_map blk_addr _ _ Hin) | exact (in_map blk_addr _ _ INqP)]. }
assert (INCL0 : incl LB0 (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocks; intros b Hb; apply in_or_app; right; right; right; exact Hb).

assert (TAIL : forall mg a1v,
mem_inv rsegs mg ->
rw_cells rsegs mg tk
[C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 pb); C4 (Z_to_bv 64 mxd); C4 (Z_to_bv 64 (Z.of_nat (S dp))); C4 isd; C4 stpos;
C4 (Z_to_bv 64 co); C4 err; C4 ucs; C4 high; C1 quote; CB 7 (repeat (Z_to_bv 8 0) 7); C8 (Z_to_bv 64 q);
C4 (Z_to_bv 64 fl); C4 (Z_to_bv 64 0)] ->
rw_cells rsegs mg bse [C4 (Z_to_bv 64 (tl_st l)); C4 (Z_to_bv 64 (tl_ss l)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 cur); C8 (Z_to_bv 64 (tl_name l))] ->
rw_cells rsegs mg spf
[C8 (Z_to_bv 64 obj); CB 16 j1; C4 (nbw j2); CB 3 (skipn 4 j2); C1 cb; CB 8 utf; C8 (pe_s11 sv); C8 (pe_s10 sv); C8 (pe_s9 sv);
C8 (pe_s8 sv); C8 (pe_s7 sv); C8 (pe_s6 sv); C8 (pe_s5 sv); C8 (pe_s4 sv); C8 (pe_s3 sv); C8 (pe_s2 sv); C8 (pe_s1 sv);
C8 (pe_s0 sv); C8 (pe_ra sv)] ->
pbuf rsegs mg pbs pb ->
tstack rsegs mg q levels ->
PE_BASE HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) LB0 payload me lo mg md A (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0) errv ->
(forall i li, nth_error levels i = Some li -> i <> S dp -> lvl_cur rsegs S4F mg (S dp) i li) ->
put_pre S4L S4F cs mg cbs cur 2 ->
evt rsegs (RZ rsegs md T)
(MS (mkR (Z_to_bv 64 139864) (Z_to_bv 64 spf) gp (Z_to_bv 64 490496) t0 t1 t2 (Z_to_bv 64 tk) (Z_to_bv 64 oldl)
(Z_to_bv 64 cur) a1v (Z_to_bv 64 bse) a3 a4 a5 a6 a7
(Z_to_bv 64 newl) (Z_to_bv 64 lenr) (Z_to_bv 64 q) (Z_to_bv 64 (sb + co)) s6 s7 s8 (Z_to_bv 64 (Z.of_nat (S dp))) s10 (Z_to_bv 64 79040) t3 t4 t5 t6)
F (Z_to_bv 64 139864) fc None mg (seg_rom rsegs))).
{ clear TOK Ld FR MI MOK. unstash PB; clear PB. unstash TSK; clear TSK. unstash LV; clear LV. unstash BASE.
intros mg a1v MI TOK Ld FR PB TSK BASE1 LV1 PP.
clear BASE.
pose proof (heap_model_ok _ _ _ _ _ _ (proj1 BASE1)) as MOK1.
pose proof (wmono_refl rsegs mg) as WM.
pose proof (munch_refl [(spf, spf + 144)] mg) as MU.
stash PB. stash TSK. stash BASE1. stash LV1. stash PP.
bst. norm_sx32.
bst.
bst.
bst.
unstash PB. unstash TSK. unstash BASE1. unstash LV1. unstash PP.
assert (HW1 : Forall (base_w (PEF tk oldl newl len lenr sb spf pmd mxd fl) LB0 (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) [(spf, spf + 144)]).
{ apply Forall_cons; [| apply Forall_nil]; unfold base_w; cbn [fst snd pf_spf pf_md pf_mxd pf_fl]. right. unfold PE_FRAME. lia. }
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (BASE2 : PE_BASE HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) LB0 payload me lo mc md A (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0) errv)
by (eapply (PE_BASE_write HIx); [exact STC | exact BASE1 | exact INCL0 | exact MU | exact WM | exact MI | exact HW1]);
assert (AGX : forall BS, (forall a k, In (a, k) BS -> In (a, k) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0) /\ a <> tk /\ a <> q) -> agree_on rsegs BS mg mc)
end.
{ intros BS HBS. eapply agree_of_munch; [exact MU | exact WM |]. intros a k Hin. destruct (HBS a k Hin) as (HinL & Hnt & Hnq).
pose proof (heap_blk S4L HIx _ _ _ _ a k (proj1 BASE1) HinL) as (Hk0 & _ & _ & Hhi & _). unfold alloc_ceiling, sp_window_lo, stack_max_size in Hhi.
cbn. (clear - LO LOS Hhi; lia). }
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (PB2 : pbuf rsegs mc pbs pb)
by (eapply pbuf_agree; [exact PB | apply AGX | apply incl_refl];
intros a k Hin; assert (HinL : In (a, k) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocks, tstate_blocks; apply in_or_app; left; apply in_or_app; left; exact Hin);
split; [exact HinL|]; pose proof ND as NDp; unfold pe_blocks, tstate_blocks in NDp; cbn [t_pbs t_objbs t_levels pf_tk pf_md pf_mxd pf_fl] in NDp;
split; intros ->;
[ refine (nodup_app_ne _ _ _ _ _ _ NDp _ _ eq_refl); [apply in_or_app; left; exact Hin | left; reflexivity]
| refine (nodup_app_ne _ _ _ _ _ _ NDp _ _ eq_refl); [apply in_or_app; left; exact Hin | right; left; reflexivity] ]);
assert (AGL : agree_on rsegs BL mg mc) by (apply AGX; intros a k Hin; destruct (BLfacts a k Hin) as (H1 & H2 & H3 & _); auto);
assert (PP2 : put_pre S4L S4F cs mc cbs cur 2)
by (destruct cs as [s|]; cbn [put_pre pf_mxd] in PP |- *; [| exact PP]; destruct PP as (Hc & Hrc & J); split; [exact Hc|]; split; [exact Hrc|];
eapply jval_agree; [exact J | apply AGX; exact CBSfacts | apply incl_refl]);
assert (TSK2 : tstack rsegs mc q levels)
by (eapply (tstack_transport rsegs); [exact TSK | exact MU | exact WM |]; intros j Hj; rewrite LEN32 in Hj; cbn; (clear - Hj Hqhi LO LOS; lia))
end.
clear PB TSK BASE1 PP MU WM.
apply evt_RZ_done.
pose proof BASE2 as (HP2 & ST2 & ERR2 & _).
eapply (reset_level_cps HIx PUT (S dp)) with (l := l) (levels := levels)
(P := pbs ++ BL) (LB0 := LB0) (REST := LBput)
(lo := lo) (errv := errv) (q := q) (r := tk) (pb := pb) (depth := Z.of_nat (S dp)) (mxd := mxd) (fl := fl)
(x := TS isd stpos (Z_to_bv 64 co) err ucs high quote) (rc := 2);
[ exact Hl | lia | exact MXD1 | exact LEN32
| unfold lvl_blocks; rewrite Hnbs0, app_nil_r, Ecbs0; eapply (heap_perm S4L HIx); [exact HP2 | exact PERM0]
| reflexivity
| rewrite Ecs0, Ecbs0, Ecur0; exact PP2
| left; split; [exact Hn0 | exact Hnbs0]
| exact TSK2
| unfold tok_cells, tok_cells_g; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote]; exact TOK
| rewrite unsigned_lit by lia; exact ST2 | exact LO
| rewrite unsigned_lit by lia; unfold RESET_STK, put_stk_P; lia
| rewrite unsigned_lit by lia; exact SPA
| rewrite unsigned_lit by lia; unfold PE_FRAME in *; lia
| apply heap_pres_refl | exact ERR2 | rewrite unsigned_lit by lia; reflexivity | ].
intros ms2 md2 (m2 & A2 & rv & RS2 & VM2 & OUT2 & TS2 & TOK2 & ST3 & HPR2 & ERR3 & AG2).
destruct RS2 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F2 & fc2 & -> & FS2 & FRM2).
rewrite ?unsigned_lit in ST3 by lia. rewrite ?unsigned_lit in HPR2 by lia.
lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?n)] => replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia | reflexivity]) end.
assert (HPJ : HEAP S4L HIx A2 (cbs ++ LBput) m2 md2 /\ jopt rsegs S4F cs m2 cbs cur).
{ destruct cs as [s|].
- cbn [put_pre] in PP2. destruct PP2 as (Hc & _ & _).
destruct OUT2 as [[[Hn|Hrc] _] | (s' & Es & Hrc & J' & HPx)]; [rewrite Ecs0 in Hn; discriminate Hn | lia |].
rewrite Ecbs0 in HPx. rewrite Ecbs0, Ecur0 in J'. rewrite Ecs0 in Es. injection Es as Es. subst s'. replace (2 - 1) with 1 in J' by lia.
split; [exact HPx|]. cbn [jopt]. split; [exact Hc | exact J'].
- cbn [put_pre] in PP2. destruct PP2 as [Hc0 Hcb0]. rewrite Hcb0.
destruct OUT2 as [[_ HPx] | (s' & Es & _)]; [| rewrite Ecs0 in Es; discriminate Es].
split; [exact HPx|]. cbn [jopt]. split; [exact Hc0 | reflexivity]. }
destruct HPJ as [HP3 JO3].
assert (INCL1 : incl LB0 (cbs ++ LBput)) by (intros b Hb; apply in_or_app; right; apply LB0P; exact Hb).
assert (BASE5 : PE_BASE HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) LB0 payload me lo m2 md2 A2 (cbs ++ LBput) errv)
by (eapply (PE_BASE_call HIx); [exact BASE2 | exact HPR2 | apply incl_refl | exact VM2 | exact HP3 | exact ST3 | exact ERR3]).
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
assert (PB5 : pbuf rsegs m2 pbs pb).
{ eapply pbuf_agree; [exact PB2 | | apply incl_refl]. eapply agree_on_incl; [exact AG2|]. intros b Hb. apply in_or_app; left; exact Hb. }
assert (AGL5 : agree_on rsegs BL mg m2).
{ eapply agree_on_trans; [exact AGL|]. eapply agree_on_incl; [exact AG2|]. intros b Hb. apply in_or_app; right; exact Hb. }
clear TOK Ld. unfold tok_cells_g in TOK2. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK2. rename TOK2 into TOK.
clear MI BASE2 PB2 AGL PP2 TSK2 HP2 ST2 ERR2 AG2 HPR2 ST3 ERR3.
pose proof (heap_model_ok _ _ _ _ _ _ HP3) as MOK3.
pose proof (heap_mem_inv _ _ _ _ _ _ HP3) as MI. cbn [hl_segs S4L pf_mxd] in MI.
pose proof (wmono_refl rsegs m2) as WM. pose proof (munch_refl [(tk, tk + 72)] m2) as MU.
stash PB5. stash BASE5. stash TS2. stash AGL5. stash JO3. stash LV1.
reenter MOK3.
bst. norm_sx32.
bst. replace (Z.of_nat (S dp) + -1) with (Z.of_nat dp) in TOK by lia.
unstash PB5. unstash BASE5. unstash TS2. unstash AGL5. unstash JO3. unstash LV1.
assert (HW3 : Forall (base_w (PEF tk oldl newl len lenr sb spf pmd mxd fl) LB0 (cbs ++ LBput)) [(tk, tk + 72)]).
{ apply Forall_cons; [| apply Forall_nil]; unfold base_w; cbn [fst snd pf_spf pf_md pf_mxd pf_fl].
left. exists tk, 72. split; [apply in_or_app; right; exact INtkP|]. split; [exact NT0 | lia]. }
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (BASE6 : PE_BASE HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) LB0 payload me lo mc md2 A2 (cbs ++ LBput) errv)
by (eapply (PE_BASE_write HIx); [exact STC | exact BASE5 | exact INCL1 | exact MU | exact WM | exact MI | exact HW3]);
assert (AGZ : forall BS, (forall a k, In (a, k) BS -> In (a, k) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0) /\ a <> tk /\ a <> q) -> agree_on rsegs BS m2 mc)
end.
{ intros BS HBS. eapply agree_of_munch; [exact MU | exact WM |]. intros a k Hin. destruct (HBS a k Hin) as (HinL & Hnt & Hnq).
assert (HinC : In (a, k) (cbs ++ LBput)) by (eapply Permutation_in; [exact PERM0 | exact HinL]).
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ a k tk 72 HP3 HinC ltac:(apply in_or_app; right; exact INtkP) Hnt). cbn. (clear - H; lia). }
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (TSK6 : tstack rsegs mc q (lupd levels (S dp) lvl_reset))
by (eapply (tstack_transport rsegs); [exact TS2 | exact MU | exact WM |]; intros j Hj; rewrite lupd_length, LEN32 in Hj; cbn in Hdtq |- *; (clear - Hj Hdtq; lia));
assert (PB6 : pbuf rsegs mc pbs pb)
by (eapply pbuf_agree; [exact PB5 | apply AGZ | apply incl_refl];
intros a k Hin; assert (HinL : In (a, k) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocks, tstate_blocks; apply in_or_app; left; apply in_or_app; left; exact Hin);
split; [exact HinL|]; pose proof ND as NDp; unfold pe_blocks, tstate_blocks in NDp; cbn [t_pbs t_objbs t_levels pf_tk pf_md pf_mxd pf_fl] in NDp;
split; intros ->;
[ refine (nodup_app_ne _ _ _ _ _ _ NDp _ _ eq_refl); [apply in_or_app; left; exact Hin | left; reflexivity]
| refine (nodup_app_ne _ _ _ _ _ _ NDp _ _ eq_refl); [apply in_or_app; left; exact Hin | right; left; reflexivity] ]);
assert (AGL6 : agree_on rsegs BL mg mc) by (eapply agree_on_trans; [exact AGL5|]; apply AGZ; intros a k Hin; destruct (BLfacts a k Hin) as (H1 & H2 & H3 & _); auto);
assert (JO6 : jopt rsegs S4F cs mc cbs cur)
by (eapply jopt_agree; [exact JO3 | apply AGZ; exact CBSfacts | apply incl_refl])
end.
apply evt_RZ_done. eapply (Kredo _ md2 A2 errv dp lp); [reflexivity | exact Hlp | exact STp | | exact FS2 | exact FRM2].
split.
-
unfold PE_CORE. cbn [t_levels t_depth t_co t_pb t_pbs t_x t_obj ts_choff pf_len pf_tk pf_spf pf_md pf_mxd pf_fl].
split; [rewrite lupd_length; exact LEN32|]. split; [lia|]. split; [lia|]. split; [reflexivity|].
split; [unfold tok_cells, tok_cells_g; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd]; exact TOK|].
split; [exact PB6|]. split; [exact Hpb|]. split; [exact TSK6|]. unfold pe_frame. exact FR.
-
apply (PE_REST_of_base HIx).
+ eapply (PE_BASE_perm HIx); [exact BASE6 | exact PERM1].
+ cbn [t_levels t_depth pf_mxd]. intros i li Hli.
destruct (Nat.eq_dec i (S dp)) as [-> | NE].
* rewrite nth_error_lupd_eq in Hli by lia. injection Hli as <-.
split; [cbn; lia|]. split; [cbn; lia|]. split; [cbn; split; reflexivity|].
rewrite (proj2 (Nat.ltb_ge (S dp) dp)) by lia. rewrite (proj2 (Nat.eqb_neq (S dp) dp)) by lia. repeat split.
* rewrite nth_error_lupd_neq in Hli by congruence.
apply lvl_cur_pop; [exact NE|].
eapply (lvl_cur_agree rsegs S4F); [exact (LV1 i li Hli NE) | exact AGL6 |].
intros b Hb. unfold BL. rewrite (lupd_split levels (S dp) l lvl_reset Hl). cbn [lvl_blocks lvl_reset tl_cbs tl_nbs app pf_mxd].
rewrite (concat_split levels (S dp) l Hl) in |- * || idtac.

destruct (Nat.lt_ge_cases i (S dp)) as [Hlt | Hge].
-- apply in_or_app; left. apply in_concat. exists (lvl_blocks li). split; [| exact Hb]. apply in_map.
rewrite <- (firstn_skipn (S dp) levels) in Hli. rewrite nth_error_app1 in Hli by (rewrite firstn_length; lia). eapply nth_error_In; exact Hli.
-- apply in_or_app; right. apply in_concat. exists (lvl_blocks li). split; [| exact Hb]. apply in_map.
rewrite <- (firstn_skipn (S (S dp)) levels) in Hli. rewrite nth_error_app2 in Hli by (rewrite firstn_length; lia).
eapply nth_error_In; exact Hli.
+ unfold cur_st. cbn [t_levels t_depth t_objs t_objbs t_obj pf_mxd]. rewrite nth_error_lupd_neq by lia. rewrite Hlp.
destruct STp as [-> | ->]; cbn; exact JO6. }

unstash PB. unstash TSK. unstash BASE. unstash LV.
destruct cs as [s|].
-
cbn [jopt pf_mxd] in JO. destruct JO as [Hc J].
pose proof (Permutation_NoDup (Permutation_map blk_addr PERM0) ND) as NDx. rewrite map_app in NDx.
pose proof NDx as NDy. apply NoDup_app_remove_r in NDx.
destruct (jval_hdr rsegs S4F s m cbs cur 1 J NDx) as (n & tojs & pb' & udel & ud & rest & INc & SZ & N48 & HDR & CLOSE).
destruct (CBSfacts cur n INc) as (INcL & Hctk & Hcq).
pose proof (heap_blk S4L HIx _ _ _ _ cur n (proj1 BASE) INcL) as (_ & Hcal & Hc0 & Hchi & _). unfold alloc_ceiling, sp_window_lo, stack_max_size in Hchi.
assert (NC0 : forall k, ~ In (cur, k) LB0).
{ intros k Hin. eapply (NoDup_app_in2 _ _ cur NDy); [exact (in_map blk_addr _ _ INc) | exact (in_map blk_addr _ _ (LB0P _ Hin))]. }
eapply evt_cut; [eapply jo_get_P; [exact HDR | lia | lia | exact Hcal | lia | lia | exact MI] |].
intros ms1 (mg & (w & ->) & MUg & WMg & MIg & HDR1).
replace (ret_pc (Z_to_bv 64 139864)) with (Z_to_bv 64 139864) by (symmetry; apply ret_pc_even; [lia | reflexivity]).

assert (DJ : forall a k, In (a, k) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0) -> a <> cur -> disjoint_from [(cur + 4, cur + 8)] a k).
{ intros a k Hin Hne. pose proof (heap_blk_disjoint S4L HIx _ _ _ _ a k cur n (proj1 BASE) Hin INcL Hne).
pose proof (heap_blk S4L HIx _ _ _ _ a k (proj1 BASE) Hin) as (Hk0 & _). cbn. (clear - N48 H; lia). }
assert (AGW : forall BS, (forall a k, In (a, k) BS -> In (a, k) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0) /\ a <> cur) -> agree_on rsegs BS m mg).
{ intros BS HBS. eapply agree_of_munch; [exact MUg | exact WMg |]. intros a k Hin. destruct (HBS a k Hin) as [H1 H2]. exact (DJ a k H1 H2). }
apply (TAIL mg w MIg).
+ eapply rw_cells_transport; [exact TOK | exact MUg | exact WMg | apply (DJ tk 72 INtk); congruence].
+ eapply rw_cells_transport; [exact Ld | exact MUg | exact WMg |]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ pf_mxd].
pose proof (DJ q (32 * mxd) INq ltac:(congruence)) as Dq. cbn in Dq |- *. (clear - D32 Hbse Dq; lia).
+ eapply rw_cells_transport; [exact FR | exact MUg | exact WMg |]. cbn. lia.
+ eapply pbuf_agree; [exact PB | apply AGW | apply incl_refl].
intros a k Hin. assert (HinL : In (a, k) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocks, tstate_blocks; apply in_or_app; left; apply in_or_app; left; exact Hin).
split; [exact HinL|]. intros ->.
unfold LBput in NDy. rewrite !map_app in NDy.
eapply (NoDup_app_in2 _ _ cur NDy); [exact (in_map blk_addr _ _ INc) | apply in_or_app; left; apply in_or_app; left; exact (in_map blk_addr _ _ Hin)].
+ eapply (tstack_transport rsegs); [exact TSK | exact MUg | exact WMg |]. intros j Hj. rewrite LEN32 in Hj.
pose proof (DJ q (32 * mxd) INq ltac:(congruence)) as Dq. cbn in Dq |- *. (clear - Hj Dq; lia).
+ eapply (PE_BASE_write HIx); [exact STC | exact BASE | exact INCL0 | exact MUg | exact WMg | exact MIg |].
apply Forall_cons; [| apply Forall_nil]. unfold base_w. cbn [fst snd pf_mxd]. left. exists cur, n. split; [exact INcL|]. split; [exact NC0 | lia].
+ intros i li Hli Hne. eapply (lvl_cur_agree rsegs S4F); [exact (LV i li Hli) | apply AGW |].
* intros a k Hin. destruct (BLfacts a k Hin) as (H1 & _ & _ & H4). split; [exact H1 | exact H4].
* intros b Hb. unfold BL. rewrite (lupd_split levels (S dp) l lvl_reset Hl). cbn [lvl_blocks lvl_reset tl_cbs tl_nbs app pf_mxd].
destruct (Nat.lt_ge_cases i (S dp)) as [Hlt | Hge].
-- apply in_or_app; left. apply in_concat. exists (lvl_blocks li). split; [| exact Hb]. apply in_map.
rewrite <- (firstn_skipn (S dp) levels) in Hli. rewrite nth_error_app1 in Hli by (rewrite firstn_length; lia). eapply nth_error_In; exact Hli.
-- apply in_or_app; right. apply in_concat. exists (lvl_blocks li). split; [| exact Hb]. apply in_map.
rewrite <- (firstn_skipn (S (S dp)) levels) in Hli. rewrite nth_error_app2 in Hli by (rewrite firstn_length; (clear - Hne Hge; lia)).
eapply nth_error_In; exact Hli.
+ cbn [put_pre pf_mxd]. split; [exact Hc|]. split; [lia|].
apply (CLOSE mg 2 HDR1). eapply (agree_others_gen rsegs); [exact MUg | exact WMg |].
intros a k Hin Hne. destruct (CBSfacts a k Hin) as (HinL & _). exact (DJ a k HinL Hne).
-
cbn [jopt pf_mxd] in JO. destruct JO as [Hc0 Ecbs].
eapply evt_cut; [rewrite Hc0; apply jo_get_null_P |]. intros ms1 ->.
replace (ret_pc (Z_to_bv 64 139864)) with (Z_to_bv 64 139864) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
eapply evt_eq; [| eapply (TAIL m _ MI TOK Ld FR PB TSK BASE)]; [rewrite Hc0; reflexivity | |].
+ intros i li Hli _. exact (LV i li Hli).
+ cbn [put_pre pf_mxd]. split; [exact Hc0 | exact Ecbs].
Qed.
End PeFinish.

End RC__1.
End Mq3.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup.
Import UEQM.
Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0.
Import UC8c.Mq0.
Import Qsw7 QJjn QkMG.
Import UG8z Udyh.Mq0 Uu4M.Mq0.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.
Import Q6q3.
Import Tk2Gen.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section PeOvadd.
Variable HIx : heap_iface S4L.
Hypothesis OADD : jo_object_add_P HIx.

#[using="OADD"] Lemma seg_ovadd :
forall (pf : pe_fix) (q : Z) (LB0 : list blk) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (ts : tstate) (l : tlevel) (kids : list (option jshape))
(cb : byte) (j1 j2 utf : list byte) (sv : pe_saved) (errv : word) (T : TSet)
(x1 gp t0 t1 t2 a0 a3 a4 a5 a6 a7 s6 s7 s8 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC HIx pf lo ->
PE_INV HIx pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_ovadd ->
tl_cs l = Some (Sobj kids) ->
frm0 fc ->

(forall m' md' A' cbs' kids' errv' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F' fc',
Z.of_nat (length kids') <= Z.of_nat (length kids) + 1 ->
okmax kids' <= Z.max (okmax kids) (odep (t_objs ts)) ->
PE_INV HIx pf q LB0 payload me lo m' md' A'
(TST (t_depth ts) (lupd (t_levels ts) (t_depth ts) (TL ST_eatws ST_osep (tl_cur l) (Some (Sobj kids')) cbs' 0 []))
(t_co ts) (t_pb ts) (t_pbs ts) (t_x ts) (t_obj ts) (t_objs ts) [])
cb j1 j2 utf sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_REDO (t_co ts) x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F' fc' m') md') T) ->

(forall m' md' A' LK errv' x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F' fc',
PE_INVK HIx pf q LB0 payload me lo m' md' A' ts LK cb j1 j2 utf sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_ERR (t_co ts) x1' gp' t0' t1' t2' (Z_to_bv 64 16) a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F' fc' m') md') T) ->
realizes rsegs (mkCfg (pe_ms rsegs pf (pe_jt ST_ovadd) (t_co ts) x1 gp t0 t1 t2
a0 (Z_to_bv 64 (tl_st l)) (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) a3 a4 a5 a6 a7
(Z_to_bv 64 q) s6 s7 s8 (Z_to_bv 64 (Z.of_nat (t_depth ts))) s10 t3 t4 t5 t6 F fc m) md) T.
Proof.
intros until fc. intros STC INV Hl Hst Hcs FRM Kredo Kerr.
pose proof STC as (LO & LOS & SPA & HT & SP0 & LEN & SB0 & SBL).
destruct INV as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
apply (PE_REST_base HIx) in REST as (BASE & LV & OBJ).
pose proof (proj1 BASE) as HP.
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl_]; pe_gen fl_; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
unfold tok_cells, tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in TOK. unfold pe_frame in FR. unfold pe_ms in *. cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
unfold_consts.
assert (JOB : jopt rsegs S4F objs m objbs obj).
{ revert OBJ. unfold cur_st. cbn [t_levels t_depth t_objbs t_objs t_obj pf_mxd]. rewrite Hl, Hst. cbn. intros E; exact E. }
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocks; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, (32 * mxd)) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocks; apply in_or_app; right; right; left; reflexivity).
pose proof (heap_blk S4L HIx _ _ _ _ tk 72 HP INtk) as (_ & Htal & Htlo & Hthi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ tk 72 HP INtk) as Himg_t. cbn [hl_img_lo hl_img_hi S4L pf_mxd] in Himg_t.
pose proof (heap_blk S4L HIx _ _ _ _ q (32 * mxd) HP INq) as (_ & Hqal & Hqlo & Hqhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ q (32 * mxd) HP INq) as Himg_q. cbn [hl_img_lo hl_img_hi S4L pf_mxd] in Himg_q.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hthi, Hqhi.
pose proof (heap_blk_nodup S4L HIx _ _ _ _ HP) as ND.
assert (Htq : tk <> q).
{ generalize ND; intros ND'. unfold pe_blocks in ND'. rewrite map_app in ND'. apply NoDup_app_remove_l in ND'.
cbn [map blk_addr fst pf_tk pf_md pf_mxd pf_fl] in ND'. apply List.NoDup_cons_iff in ND' as [Hni _]. intros E. apply Hni. left. symmetry. exact E. }
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ tk 72 q (32 * mxd) HP INtk INq Htq) as Hdtq.
assert (NQ0 : forall k, ~ In (q, k) LB0).
{ intros k. generalize ND; intros ND'. unfold ts0, pe_blocks, tstate_blocks in ND'. cbn [t_pbs t_objbs t_levels pf_tk pf_md pf_mxd pf_fl] in ND'.
rewrite <- !app_assoc in ND'. exact (nodup_mid_notin _ _ _ _ _ _ _ _ k ND'). }
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L pf_mxd] in MI.
pose proof (LV depth l Hl) as LVd. pose proof LVd as (ST26 & SS26 & JO & Md).
rewrite Nat.ltb_irrefl, Nat.eqb_refl in Md. destruct Md as (c0 & hn0 & Hmode & CLS0 & NM0).
rewrite Hst, lvl_mode_ovadd in Hmode. injection Hmode as <- <-. cbn [name_ok pf_mxd] in NM0. destruct NM0 as (Hn0 & nn & ks & Hnbs0 & Hnn & CSTR).
rewrite Hcs in JO. cbn [jopt pf_mxd] in JO. destruct JO as [Hc J].
set (cur := tl_cur l) in *. set (cbs := tl_cbs l) in *. set (name := tl_name l) in *.
assert (Ecur0 : tl_cur l = cur) by reflexivity. assert (Ecbs0 : tl_cbs l = cbs) by reflexivity. assert (Ename0 : tl_name l = name) by reflexivity.
clearbody cur cbs name.

set (LBput := (pbs ++ concat (map lvl_blocks (lupd levels depth lvl_reset))) ++ (tk, 72) :: (q, (32 * mxd)) :: LB0).
assert (PERM0 : Permutation (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0) (cbs ++ objbs ++ (name, nn) :: LBput)).
{ unfold pe_blocks, tstate_blocks, ts0, LBput. cbn [t_pbs t_objbs t_levels pf_tk pf_md pf_mxd pf_fl]. rewrite <- !app_assoc.
apply (Permutation_trans (l' := pbs ++ (objbs ++ (cbs ++ ([(name, nn)] ++ (concat (map lvl_blocks (lupd levels depth lvl_reset)) ++ (tk, 72) :: (q, (32 * mxd)) :: LB0)))))).
- apply Permutation_app_head. apply Permutation_app_head. rewrite (app_assoc cbs). rewrite (app_assoc (cbs ++ _)). apply Permutation_app_tail.
replace (cbs ++ [(name, nn)]) with (lvl_blocks l) by (unfold lvl_blocks; rewrite Hnbs0, Ecbs0; reflexivity).
apply concat_lupd_empty; [exact Hl | reflexivity].
- cbn [app pf_mxd].
apply (Permutation_trans (l' := objbs ++ (pbs ++ (cbs ++ ((name, nn) :: concat (map lvl_blocks (lupd levels depth lvl_reset)) ++ (tk, 72) :: (q, (32 * mxd)) :: LB0))))); [apply Permutation_app_swap_app|].
apply (Permutation_trans (l' := objbs ++ (cbs ++ (pbs ++ ((name, nn) :: concat (map lvl_blocks (lupd levels depth lvl_reset)) ++ (tk, 72) :: (q, (32 * mxd)) :: LB0))))); [apply Permutation_app_head; apply Permutation_app_swap_app|].
apply (Permutation_trans (l' := objbs ++ (cbs ++ ((name, nn) :: pbs ++ (concat (map lvl_blocks (lupd levels depth lvl_reset)) ++ (tk, 72) :: (q, (32 * mxd)) :: LB0))))).
+ apply Permutation_app_head. apply Permutation_app_head. apply Permutation_sym. apply Permutation_middle.
+ apply Permutation_app_swap_app. }
assert (INqP : In (q, (32 * mxd)) LBput) by (unfold LBput; apply in_or_app; right; right; left; reflexivity).
assert (INtkP : In (tk, 72) LBput) by (unfold LBput; apply in_or_app; right; left; reflexivity).
assert (LB0P : incl LB0 LBput) by (unfold LBput; intros b Hb; apply in_or_app; right; right; right; exact Hb).
set (BL := concat (map lvl_blocks (lupd levels depth lvl_reset))).
assert (BLP : incl BL LBput) by (unfold LBput; intros b Hb; apply in_or_app; left; apply in_or_app; right; exact Hb).
pose proof (TSK depth l Hl) as Ld. unfold srec_cells in Ld. rewrite Ecur0, Ename0 in Ld.
remember (q + 32 * Z.of_nat depth) as bse eqn:Hbse in Ld.
assert (HbseR : q <= bse /\ bse + 32 <= q + (32 * mxd)) by (subst bse; lia).
assert (Hbal : bse mod 16 = 0) by (subst bse; clear - Hqal; Z.div_mod_to_equations; lia).
stash PB. stash TSK. clear OBJ.
apply rz_evt; [exact MOK|]. rewrite Hst. unfold ST_ovadd. cbn [pe_jt pf_mxd]. replace (q + 32 * Z.of_nat depth) with bse by lia.
bst. bst. bst. bst.

unstash PB. unstash TSK.
apply evt_RZ_done.
eapply OADD with (LB := (name, nn) :: LBput) (OBS := cbs) (VBS := objbs) (p := cur) (v := obj) (k := name) (kn := nn) (ks := ks) (kids := kids) (vs := objs) (lo := lo) (errv := errv);
[ | exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 BASE)))))))) | exact J | exact JOB | left; reflexivity | exact CSTR | lia | exact FRM | reflexivity | reflexivity | reflexivity | ].
{ pose proof BASE as (_ & ST0 & ERR0 & _). unfold jo_pre. cbn [hl_segs hl_tp S4L pf_mxd].
split; [eapply (heap_perm S4L HIx); [exact HP | exact PERM0] |].
rewrite ?unsigned_lit by lia. unfold PE_FRAME in *.
split; [exact ST0|]. split; [clia|]. split; [clia|]. split; [exact SPA|]. split; [lia|]. split; [exact ERR0|]. split; [reflexivity|]. reflexivity. }
intros ms2 md2 mp r (RS2 & VM2 & ST2 & HPR2 & (errv2 & ERR2)) GLOB2 OUT.
destruct RS2 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F2 & fc2 & -> & FS2 & FRM2).
cbn [hl_segs hl_tp S4L pf_mxd] in *. rewrite ?(unsigned_lit spf) in ST2 by lia. rewrite ?(unsigned_lit spf) in HPR2 by lia.
apply (heap_presx_rw_cells S4L _ _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. cbn [hl_segs S4L pf_mxd] in FR.
apply (heap_presx_rw_cells S4L _ _ _ _ _ _ _ HPR2) in TOK; [| eapply client_rangex_block; [right; exact INtkP | lia | cbn; lia]]. cbn [hl_segs S4L pf_mxd] in TOK.
apply (heap_presx_rw_cells S4L _ _ _ _ _ _ _ HPR2) in Ld; [| eapply client_rangex_block; [right; exact INqP | lia | cbn; lia]]. cbn [hl_segs S4L pf_mxd] in Ld.
apply (tstack_presx_g S4L _ _ _ _ _ _ _ HPR2 ltac:(right; exact INqP)) in TSK; [| exact LEN32].
assert (PB2 : pbuf rsegs mp pbs pb).
{ eapply pbuf_agree; [exact PB | | apply incl_refl]. eapply (agree_of_heap_presx rsegs S4L); [exact HPR2 | reflexivity |].
unfold LBput. intros b Hb. right. apply in_or_app; left. apply in_or_app; left. exact Hb. }
assert (AGL2 : agree_on rsegs BL m mp) by (eapply (agree_of_heap_presx rsegs S4L); [exact HPR2 | reflexivity | intros b Hb; right; exact (BLP _ Hb)]).
assert (LV2 : forall i li, nth_error levels i = Some li -> i <> depth -> lvl_cur rsegs S4F mp depth i li).
{ intros i li Hli Hne. eapply (lvl_cur_agree rsegs S4F); [exact (LV i li Hli) | exact AGL2 |].
intros b Hb. unfold BL. apply in_concat. exists (lvl_blocks li). split; [| exact Hb]. apply in_map.
eapply (nth_error_In _ i). rewrite nth_error_lupd_neq by congruence. exact Hli. }
clear PB MI HP.
destruct OUT as [(-> & A2 & cbs' & kids' & J2 & HP2 & LENK & DEPK) | (-> & A2 & REM & J2 & JOB2 & HP2)].
-
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2. reenter MOK2.
assert (BASE2 : PE_BASE HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) LB0 payload me lo mp md2 A2 (cbs' ++ (name, nn) :: LBput) errv2)
by (eapply (PE_BASE_callx HIx); [exact BASE | exact HPR2 | intros b Hb; right; exact (LB0P _ Hb) | exact VM2 | exact GLOB2 | exact HP2 | exact ST2 | exact ERR2]).
clear BASE HPR2.
pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI. cbn [hl_segs S4L pf_mxd] in MI.
stash PB2. stash TSK. stash LV2.
bst. if_true.
step. norm_sx32. step.
step. rewrite (unsigned_lit (Z.of_nat depth)) by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32.
step. replace (q + Z.of_nat depth * 32) with bse by lia.
bst. bst.

unstash PB2. unstash TSK. unstash LV2.
apply evt_RZ_done.
eapply (hi_free S4L HIx) with (p := name) (lo := lo) (LB := (name, nn) :: (cbs' ++ LBput));
[ eapply (heap_perm S4L HIx); [exact HP2 | apply Permutation_sym; apply Permutation_middle] | right; exists nn; left; reflexivity | .. ]; try alloc_side.
all: try (pose proof BASE2 as (_ & ST4 & ERR4 & _); unfold PE_FRAME in *; rewrite ?unsigned_lit by lia; first [exact ST4 | exact ERR4 | clia]).
intros ms3 mf md3 A5 r3 RS3 VM3 ST5 HPR3 ERR5 HP5. open_ret RS3. cbn [hl_segs hl_tp S4L pf_mxd] in *.
rewrite ?(unsigned_lit spf) in ST5 by lia. rewrite ?(unsigned_lit spf) in HPR3 by lia.
rewrite lb_remove_head in HPR3, HP5.
assert (BASE5 : PE_BASE HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) LB0 payload me lo mf md3 A5 (cbs' ++ LBput) errv2)
by (eapply (PE_BASE_call HIx); [exact BASE2 | exact HPR3 | intros b Hb; apply in_or_app; right; exact (LB0P _ Hb) | exact VM3 | exact HP5 | exact ST5 | exact ERR5]).
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR3) in FR; [| left; cbn; lia]. cbn [hl_segs S4L pf_mxd] in FR.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR3) in TOK; [| eapply client_range_block; [apply in_or_app; right; exact INtkP | lia | cbn; lia]]. cbn [hl_segs S4L pf_mxd] in TOK.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR3) in Ld; [| eapply client_range_block; [apply in_or_app; right; exact INqP | lia | cbn; lia]]. cbn [hl_segs S4L pf_mxd] in Ld.
apply (tstack_pres_g S4L _ _ _ _ _ _ HPR3 ltac:(apply in_or_app; right; exact INqP)) in TSK; [| exact LEN32].
assert (PB5 : pbuf rsegs mf pbs pb).
{ eapply pbuf_agree; [exact PB2 | | apply incl_refl]. eapply (agree_of_heap_pres rsegs S4L); [exact HPR3 | reflexivity |].
unfold LBput. intros b Hb. apply in_or_app; right. apply in_or_app; left. apply in_or_app; left. exact Hb. }
assert (LV5 : forall i li, nth_error levels i = Some li -> i <> depth -> lvl_cur rsegs S4F mf depth i li).
{ intros i li Hli Hne. eapply (lvl_cur_agree rsegs S4F); [exact (LV2 i li Hli Hne) | |].
- eapply (agree_of_heap_pres rsegs S4L); [exact HPR3 | reflexivity | intros b Hb; apply in_or_app; right; exact (BLP _ Hb)].
- intros b Hb. unfold BL. apply in_concat. exists (lvl_blocks li). split; [| exact Hb]. apply in_map.
eapply (nth_error_In _ i). rewrite nth_error_lupd_neq by congruence. exact Hli. }
assert (J5 : jval rsegs S4F (Sobj kids') mf cbs' cur 1).
{ eapply jval_agree; [exact J2 | | apply incl_refl]. eapply (agree_of_heap_pres rsegs S4L); [exact HPR3 | reflexivity | intros b Hb; apply in_or_app; left; exact Hb]. }
clear BASE2 PB2 LV2 J2 ST5 ERR5 HPR3 MI HP2.

pose proof (heap_model_ok _ _ _ _ _ _ HP5) as MOK5.
pose proof (heap_mem_inv _ _ _ _ _ _ HP5) as MI. cbn [hl_segs S4L pf_mxd] in MI.
pose proof (wmono_refl rsegs mf) as WM.
pose proof (munch_refl [(bse, bse + 32)] mf) as MU.
pose proof (srec_join8 mf bse (TL (tl_st l) (tl_ss l) cur None [] name []) Ld) as Ld8. clear Ld.
cbn [tl_st tl_ss tl_cur tl_name le4 Z_to_le_bytes app pf_mxd] in Ld8.
stash PB5. stash TSK. stash BASE5. stash LV5.
reenter MOK5.
step. norm_sx32. step.
step. rewrite (unsigned_lit (Z.of_nat depth)) by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32.
step. replace (q + Z.of_nat depth * 32) with bse by lia.
bstz. bst. bst. bstz. bst.
unstash PB5. unstash TSK. unstash BASE5. unstash LV5.
set (l' := TL ST_eatws ST_osep cur (Some (Sobj kids')) cbs' 0 []).
pose proof (heap_blk_nodup S4L HIx _ _ _ _ HP5) as ND2.
assert (NEq : forall a k, In (a, k) (cbs' ++ pbs ++ BL) -> a <> q).
{ intros a k Hin ->.
assert (ND3 : List.NoDup (map blk_addr ((cbs' ++ pbs ++ BL) ++ (tk, 72) :: (q, (32 * mxd)) :: LB0))).
{ unfold LBput in ND2. rewrite <- !app_assoc. rewrite <- !app_assoc in ND2. exact ND2. }
rewrite map_app in ND3. eapply (NoDup_app_in2 _ _ q ND3); [exact (in_map blk_addr _ _ Hin) | cbn; right; left; reflexivity]. }
assert (AGX : forall BS, (forall a k, In (a, k) BS -> In (a, k) (cbs' ++ LBput) /\ a <> q) -> agree_on rsegs BS mf _)
by (intros BS HBS; eapply agree_of_munch; [exact MU | exact WM |]; intros a k Hin; destruct (HBS a k Hin) as [HinL Hnq];
pose proof (heap_blk S4L HIx _ _ _ _ a k HP5 HinL) as (Hk0 & _);
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ a k q (32 * mxd) HP5 HinL ltac:(apply in_or_app; right; exact INqP) Hnq); cbn; lia).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (rw_cells_recast_prefix rsegs mc bse [C8 (Z_to_bv 64 98784247808)] [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 23)]
[C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 cur); C8 (Z_to_bv 64 0)] Ld8
ltac:(cbn; repeat split) ltac:(apply bytes_eq_by_unsigned; vm_compute; reflexivity) ltac:(reflexivity)) as Ld1;
cbn [app pf_mxd] in Ld1;
assert (TSK3 : tstack rsegs mc q (lupd levels depth l'))
by (subst bse; eapply (tstack_put rsegs mf _ q levels depth l' []);
[exact TSK | lia | exact MU | exact WM | intros; exact I | unfold srec_cells, l'; cbn [tl_st tl_ss tl_cur tl_name pf_mxd]; exact Ld1]);
assert (BASE3 : PE_BASE HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) LB0 payload me lo mc md3 A5 (cbs' ++ LBput) errv2)
by (eapply (PE_BASE_write HIx); [exact STC | exact BASE5 | intros b Hb; apply in_or_app; right; exact (LB0P _ Hb) | exact MU | exact WM | exact MI |];
apply Forall_cons; [| apply Forall_nil]; unfold base_w; cbn [fst snd pf_spf pf_md pf_mxd pf_fl]; left; exists q, (32 * mxd);
split; [apply in_or_app; right; exact INqP|]; split; [exact NQ0 | lia]);
assert (PB3 : pbuf rsegs mc pbs pb)
by (eapply pbuf_agree; [exact PB5 | apply AGX | apply incl_refl]; intros a k Hin; split;
[unfold LBput; apply in_or_app; right; apply in_or_app; left; apply in_or_app; left; exact Hin | eapply NEq; apply in_or_app; right; apply in_or_app; left; exact Hin]);
assert (AGL3 : agree_on rsegs BL mf mc)
by (apply AGX; intros a k Hin; split; [apply in_or_app; right; exact (BLP _ Hin) | eapply NEq; apply in_or_app; right; apply in_or_app; right; exact Hin]);
assert (J3 : jval rsegs S4F (Sobj kids') mc cbs' cur 1)
by (eapply jval_agree; [exact J5 | apply AGX | apply incl_refl]; intros a k Hin; split; [apply in_or_app; left; exact Hin | eapply NEq; apply in_or_app; left; exact Hin])
end.
apply evt_RZ_done. eapply (Kredo _ md3 A5 cbs' kids' errv2); [exact LENK | exact DEPK | | exact FS2 | exact FRM2].
split.
+ unfold PE_CORE. cbn [t_levels t_depth t_co t_pb t_pbs t_x t_obj ts_choff pf_len pf_tk pf_spf pf_md pf_mxd pf_fl].
split; [rewrite lupd_length; exact LEN32|]. split; [exact D32|]. split; [lia|]. split; [reflexivity|].
split; [unfold tok_cells, tok_cells_g; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd]; exact TOK|].
split; [exact PB3|]. split; [exact Hpb|]. split; [exact TSK3|]. unfold pe_frame. exact FR.
+ apply (PE_REST_of_base HIx).
* eapply (PE_BASE_perm HIx); [exact BASE3|].
unfold pe_blocks, tstate_blocks, LBput. cbn [t_pbs t_objbs t_levels pf_tk pf_md pf_mxd pf_fl]. rewrite app_nil_l.
unfold BL. rewrite (lupd_split levels depth l lvl_reset Hl). fold l'. rewrite (lupd_split levels depth l l' Hl).
replace (lvl_blocks l') with cbs' by (unfold lvl_blocks, l'; cbn; rewrite app_nil_r; reflexivity).
cbn [lvl_blocks lvl_reset tl_cbs tl_nbs app pf_mxd]. rewrite <- !app_assoc.
apply (Permutation_trans (l' := pbs ++ (cbs' ++ (concat (map lvl_blocks (firstn depth levels)) ++ (concat (map lvl_blocks (skipn (S depth) levels)) ++ (tk, 72) :: (q, (32 * mxd)) :: LB0)))));
[apply Permutation_app_swap_app | apply Permutation_app_head; apply Permutation_app_swap_app].
* cbn [t_levels t_depth pf_mxd]. intros i li Hli.
destruct (Nat.eq_dec i depth) as [-> | NE].
-- rewrite nth_error_lupd_eq in Hli by lia. injection Hli as <-.
split; [cbn; unfold ST_eatws; lia|]. split; [cbn; unfold ST_osep; lia|]. split; [cbn [tl_cs tl_cbs tl_cur l' jopt pf_mxd]; split; [exact Hc | exact J3]|].
rewrite Nat.ltb_irrefl, Nat.eqb_refl. exists CObj, false. split; [reflexivity|]. split; [exact I|]. cbn. split; reflexivity.
-- rewrite nth_error_lupd_neq in Hli by congruence.
eapply (lvl_cur_agree rsegs S4F); [exact (LV5 i li Hli NE) | exact AGL3 |].
intros b Hb. unfold BL. apply in_concat. exists (lvl_blocks li). split; [| exact Hb]. apply in_map.
eapply (nth_error_In _ i). rewrite nth_error_lupd_neq by congruence. exact Hli.
* unfold cur_st. cbn [t_levels t_depth t_objbs pf_mxd]. rewrite nth_error_lupd_eq by lia. reflexivity.
-
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2. reenter MOK2.
assert (BASE2 : PE_BASE HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) LB0 payload me lo mp md2 A2 (cbs ++ objbs ++ REM ++ (name, nn) :: LBput) errv2)
by (eapply (PE_BASE_callx HIx); [exact BASE | exact HPR2 | intros b Hb; right; exact (LB0P _ Hb) | exact VM2 | exact GLOB2 | exact HP2 | exact ST2 | exact ERR2]).
assert (CSTR2 : cstr rsegs mp name nn ks).
{ eapply cstr_agree with (BS := (name, nn) :: LBput); [exact CSTR | | left; reflexivity | lia].
eapply (agree_of_heap_presx rsegs S4L); [exact HPR2 | reflexivity | apply incl_refl]. }
replace (Z_to_bv 64 (2^64 - 1)) with (Z_to_bv 64 (-1)) by (apply bv_eq; vm_compute; reflexivity).
bst. if_false. bst. bst. bst.
apply evt_RZ_done. eapply (Kerr _ md2 A2 REM errv2); [ | exact FS2 | exact FRM2].
unfold ts0. split; [| split; [| split]].
+ unfold PE_CORE. cbn [t_levels t_depth t_co t_pb t_pbs t_x t_obj ts_choff pf_len pf_tk pf_spf pf_md pf_mxd pf_fl].
split; [exact LEN32|]. split; [exact D32|]. split; [lia|]. split; [reflexivity|].
split; [unfold tok_cells, tok_cells_g; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd]; exact TOK|].
split; [exact PB2|]. split; [exact Hpb|]. split; [| unfold pe_frame; exact FR].
intros j lj Hlj. destruct (Nat.eq_dec j depth) as [-> | NE].
* rewrite Hl in Hlj. injection Hlj as <-. subst bse. unfold srec_cells. rewrite Ecur0, Ename0. exact Ld.
* exact (TSK j lj Hlj).
+ eapply (PE_BASE_perm HIx); [exact BASE2 |].
apply (Permutation_trans (l' := (cbs ++ objbs ++ (name, nn) :: LBput) ++ REM)).
* rewrite <- !app_assoc. apply Permutation_app_head. apply Permutation_app_head. apply Permutation_app_comm.
* apply Permutation_app_tail. apply Permutation_sym. exact PERM0.
+ cbn [t_levels t_depth pf_mxd]. intros i li Hli.
destruct (Nat.eq_dec i depth) as [-> | NE].
* rewrite Hl in Hli. injection Hli as <-.
split; [exact ST26|]. split; [exact SS26|]. split; [rewrite Hcs, Ecbs0, Ecur0; cbn [jopt pf_mxd]; split; [exact Hc | exact J2]|].
rewrite Nat.ltb_irrefl, Nat.eqb_refl. exists CObj, true. rewrite Hst. split; [apply lvl_mode_ovadd|]. split; [rewrite Hcs; exact I|].
cbn. rewrite Ename0. split; [exact Hn0|]. exists nn, ks. split; [exact Hnbs0|]. split; [exact Hnn | exact CSTR2].
* exact (LV2 i li Hli NE).
+ unfold cur_st. cbn [t_levels t_depth t_objbs t_objs t_obj pf_mxd]. rewrite Hl, Hst. cbn. exact JOB2.
Qed.
End PeOvadd.

End RC__1.
End Mq4.

Module Mq5.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup.
Import UEQM.
Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0.
Import UC8c.Mq0.
Import Qsw7 QJjn QkMG.
Import UG8z Udyh.Mq0.
Import UPZI.Mq4.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.
Import Q6q3.
Import TopUbTac Tk1Reset Tk2Gen.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section PePush.
Variable HIx : heap_iface S4L.
Hypothesis PUT : put_stmt_P HIx.

#[using="Type"] Lemma lvl_cur_push : forall m d i li, i <> d -> i <> S d -> lvl_cur rsegs S4F m d i li -> lvl_cur rsegs S4F m (S d) i li.
Proof.
intros m d i li Hne1 Hne2 (R1 & R2 & J & M). split; [exact R1|]. split; [exact R2|]. split; [exact J|].
destruct (Nat.lt_ge_cases i d) as [Hlt | Hge].
- rewrite (proj2 (Nat.ltb_lt i (S d))) by lia. rewrite (proj2 (Nat.ltb_lt i d)) in M by lia. exact M.
- rewrite (proj2 (Nat.ltb_ge i (S d))) by lia. rewrite (proj2 (Nat.eqb_neq i (S d)) Hne2).
rewrite (proj2 (Nat.ltb_ge i d)) in M by lia. rewrite (proj2 (Nat.eqb_neq i d) Hne1) in M. exact M.
Qed.


#[using="PUT"] Lemma seg_push :
forall (pf : pe_fix) (q : Z) (LB0 : list blk) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (ts : tstate) (l : tlevel) (stn : Z)
(cb : byte) (j1 j2 utf : list byte) (sv : pe_saved) (errv : word) (T : TSet)
(x1 gp t0 t1 t2 a1 a3 a4 a5 a6 a7 s4 s6 s7 s8 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC HIx pf lo ->
PE_INV HIx pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv ->
nth_error (t_levels ts) (t_depth ts) = Some l -> (S (t_depth ts) < Z.to_nat (pf_mxd pf))%nat ->
zin (tl_st l) [ST_array_add; ST_ovadd] = false ->
((stn = ST_array_add /\ cls_ok CArr (tl_cs l) /\ name_ok rsegs m false l) \/
(stn = ST_ovadd /\ cls_ok CObj (tl_cs l) /\ name_ok rsegs m true l)) ->

(forall m' md' A' errv' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F' fc',
PE_INV HIx pf q LB0 payload me lo m' md' A'
(TST (S (t_depth ts)) (lupd (lupd (t_levels ts) (t_depth ts) (TL stn (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)))
(S (t_depth ts)) lvl_reset)
(t_co ts) (t_pb ts) (t_pbs ts) (t_x ts) (t_obj ts) (t_objs ts) (t_objbs ts))
cb j1 j2 utf sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_REDO (t_co ts) x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F' fc' m') md') T) ->
realizes rsegs (mkCfg (pe_ms rsegs pf 0x21e00 (t_co ts) x1 gp t0 t1 t2
(Z_to_bv 64 stn) a1 (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) a3 a4 a5 a6 a7
s4 s6 s7 s8 (Z_to_bv 64 (Z.of_nat (t_depth ts))) s10 t3 t4 t5 t6 F fc m) md) T.
Proof.
intros until fc. intros STC INV Hl D31 NADD PARENT Kredo.
pose proof STC as (LO & LOS & SPA & HT & SP0 & LEN & SB0 & SBL).
destruct INV as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
apply (PE_REST_base HIx) in REST as (BASE & LV & OBJ).
pose proof (proj1 BASE) as HP.
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl_]; pe_gen fl_; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
assert (MXD1 : 1 <= mxd <= 32) by (pose proof STC as STC1; apply PE_STATIC_mxd in STC1; exact (proj1 STC1)).
unfold tok_cells, tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK. unfold pe_frame in FR. unfold pe_ms in *. cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
unfold_consts.
assert (Eobjbs : objbs = []).
{ revert OBJ. unfold cur_st. cbn [t_levels t_depth t_objbs]. rewrite Hl, NADD. intros E; exact E. }
subst objbs.
assert (STN : 0 <= stn <= 26) by (unfold ST_array_add, ST_ovadd in PARENT; lia).
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs []) in *.
assert (INtk : In (tk, 72) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocks; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, (32 * mxd)) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocks; apply in_or_app; right; right; left; reflexivity).
pose proof (heap_blk S4L HIx _ _ _ _ tk 72 HP INtk) as (_ & Htal & Htlo & Hthi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ tk 72 HP INtk) as Himg_t. cbn [hl_img_lo hl_img_hi S4L] in Himg_t.
pose proof (heap_blk S4L HIx _ _ _ _ q (32 * mxd) HP INq) as (_ & Hqal & Hqlo & Hqhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ q (32 * mxd) HP INq) as Himg_q. cbn [hl_img_lo hl_img_hi S4L] in Himg_q.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hthi, Hqhi.
pose proof (heap_blk_nodup S4L HIx _ _ _ _ HP) as ND.
assert (Htq : tk <> q).
{ generalize ND; intros ND'. unfold pe_blocks in ND'. rewrite map_app in ND'. apply NoDup_app_remove_l in ND'.
cbn [map blk_addr fst pf_tk pf_md pf_mxd pf_fl] in ND'. apply List.NoDup_cons_iff in ND' as [Hni _]. intros E. apply Hni. left. symmetry. exact E. }
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ tk 72 q (32 * mxd) HP INtk INq Htq) as Hdtq.
assert (NQ0 : forall k, ~ In (q, k) LB0).
{ intros k. generalize ND; intros ND'. unfold ts0, pe_blocks, tstate_blocks in ND'. cbn [t_pbs t_objbs t_levels pf_tk pf_md pf_mxd pf_fl] in ND'.
rewrite <- !app_assoc in ND'. exact (nodup_mid_notin _ _ _ _ _ _ _ _ k ND'). }
assert (NT0 : forall k, ~ In (tk, k) LB0).
{ intros k. generalize ND; intros ND'. unfold ts0, pe_blocks, tstate_blocks in ND'. cbn [t_pbs t_objbs t_levels pf_tk pf_md pf_mxd pf_fl] in ND'.
rewrite <- !app_assoc in ND'. exact (nodup_mid_notin_r _ _ _ _ _ _ _ _ k ND'). }
assert (INCL0 : incl LB0 (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocks; intros b Hb; apply in_or_app; right; right; right; exact Hb).
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (LV depth l Hl) as LVd. pose proof LVd as (ST26 & SS26 & JO & _).

assert (HdS : (S depth < length levels)%nat) by lia.
destruct (nth_error levels (S depth)) as [ln|] eqn:Hln; [| apply nth_error_None in Hln; lia].
pose proof (LV (S depth) ln Hln) as LVn. pose proof LVn as (STn26 & SSn26 & _ & CLn).
rewrite (proj2 (Nat.ltb_ge (S depth) depth)) in CLn by lia. rewrite (proj2 (Nat.eqb_neq (S depth) depth)) in CLn by lia.
pose proof CLn as (Cn1 & Cn2 & Cn3 & Cn4 & Cn5).

pose proof (TSK depth l Hl) as Ld. unfold srec_cells in Ld.
remember (q + 32 * Z.of_nat depth) as bse eqn:Hbse in Ld.
assert (HbseR : q <= bse /\ bse + 64 <= q + (32 * mxd)) by (subst bse; lia).
pose proof (TSK (S depth) ln Hln) as Ln.
replace (q + 32 * Z.of_nat (S depth)) with (bse + 32) in Ln by lia.
pose proof (srec_join8 m (bse + 32) _ Ln) as Ln8. clear Ln. cbn [tl_st tl_ss tl_cur tl_name le4 Z_to_le_bytes app] in Ln8. rewrite Cn1, Cn4 in Ln8.

set (BL := concat (map lvl_blocks levels)).
assert (BLfacts : forall a k, In (a, k) BL -> In (a, k) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0) /\ a <> tk /\ a <> q).
{ intros a k Hin.
assert (HinT : In (a, k) (tstate_blocks ts0)) by (unfold tstate_blocks, ts0; cbn [t_pbs t_objbs t_levels]; apply in_or_app; right; exact Hin).
assert (HinL : In (a, k) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocks; apply in_or_app; left; exact HinT).
split; [exact HinL|]. unfold pe_blocks in ND. cbn [pf_tk pf_md pf_mxd pf_fl] in ND. split.
- eapply (nodup_app_ne _ _ _ _ _ _ ND HinT). left; reflexivity.
- eapply (nodup_app_ne _ _ _ _ _ _ ND HinT). right; left; reflexivity. }
assert (EBL : concat (map lvl_blocks (lupd (lupd levels depth (TL stn (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) (S depth) lvl_reset)) = BL).
{ unfold BL. rewrite (map_lupd_same lvl_blocks _ (S depth) lvl_reset ln); [| rewrite nth_error_lupd_neq by lia; exact Hln | unfold lvl_blocks; cbn; rewrite Cn3, Cn5; reflexivity].
rewrite (map_lupd_same lvl_blocks levels depth (TL stn (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)) l Hl) by reflexivity. reflexivity. }
stash PB. stash BASE. stash TSK. stash LV. clear OBJ HP.

pose proof (wmono_refl rsegs m) as WM.
pose proof (munch_refl [(bse, bse + 32); (tk, tk + 72)] m) as MU.
apply rz_evt; [exact MOK|]. replace (q + 32 * Z.of_nat depth) with bse by lia.
bst.
rewrite (unsigned_lit (Z.of_nat depth)) by lia. rewrite (swrap32_id (Z.of_nat depth + 1)) by lia. replace (Z.of_nat depth + 1) with (Z.of_nat (S depth)) by lia.
bst.
bst.

set (l' := TL stn (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)) in *.
unstash TSK. unstash BASE.
assert (AGX : forall ma mz W, munch W ma mz -> wmono rsegs ma mz ->
Forall (fun iv => (q <= fst iv /\ snd iv <= q + (32 * mxd)) \/ (tk <= fst iv /\ snd iv <= tk + 72) \/ (spf <= fst iv /\ snd iv <= spf + PE_FRAME)) W ->
forall BS, (forall a k, In (a, k) BS -> In (a, k) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0) /\ a <> tk /\ a <> q) -> agree_on rsegs BS ma mz).
{ intros ma mz W MU1 WM1 HW BS HBS. eapply agree_of_munch; [exact MU1 | exact WM1 |]. intros a k Hin. destruct (HBS a k Hin) as (HinL & Hnt & Hnq).
pose proof (heap_blk S4L HIx _ _ _ _ a k (proj1 BASE) HinL) as (Hk0 & _ & _ & Hhi & _). unfold alloc_ceiling, sp_window_lo, stack_max_size in Hhi.
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ a k q (32 * mxd) (proj1 BASE) HinL INq Hnq).
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ a k tk 72 (proj1 BASE) HinL INtk Hnt).
clear - HW H H0 Hhi Hk0 LO LOS. induction W as [|[lo' hi'] W IH]; [exact I|].
apply Forall_cons_iff in HW as [H1 HW]. cbn [fst snd pf_mxd] in H1. cbn [disjoint_from]. split; [| apply IH; exact HW]. unfold PE_FRAME in H1. lia. }
assert (PBSfacts : forall a k, In (a, k) pbs -> In (a, k) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0) /\ a <> tk /\ a <> q).
{ intros a k Hin. assert (HinT : In (a, k) (tstate_blocks ts0)) by (unfold tstate_blocks, ts0; cbn [t_pbs t_objbs t_levels]; apply in_or_app; left; exact Hin).
assert (HinL : In (a, k) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocks; apply in_or_app; left; exact HinT).
split; [exact HinL|]. generalize ND; intros ND'. unfold pe_blocks in ND'. cbn [pf_tk pf_md pf_mxd pf_fl] in ND'. split.
- eapply (nodup_app_ne _ _ _ _ _ _ ND' HinT). left; reflexivity.
- eapply (nodup_app_ne _ _ _ _ _ _ ND' HinT). right; left; reflexivity. }
assert (HW1 : Forall (base_w (PEF tk oldl newl len lenr sb spf pmd mxd fl) LB0 (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) [(bse, bse + 32); (tk, tk + 72)]).
{ apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]; unfold base_w; cbn [fst snd pf_spf pf_md pf_mxd pf_fl].
- left. exists q, (32 * mxd). split; [exact INq|]. split; [exact NQ0 | lia].
- left. exists tk, 72. split; [exact INtk|]. split; [exact NT0 | lia]. }
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (TSK1 : tstack rsegs mc q (lupd levels depth l'))
by (subst bse; eapply (tstack_put rsegs m _ q levels depth l' [(tk, tk + 72)]);
[exact TSK | lia | exact MU | exact WM | intros j Hj Hne; rewrite LEN32 in Hj; cbn; split; [lia | exact I] | unfold srec_cells, l'; cbn [tl_st tl_ss tl_cur tl_name]; exact Ld]);
assert (BASE1 : PE_BASE HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) LB0 payload me lo mc md A (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0) errv)
by (eapply (PE_BASE_write HIx); [exact STC | exact BASE | exact INCL0 | exact MU | exact WM | exact MI | exact HW1]);
assert (AG1 : forall BS, (forall a k, In (a, k) BS -> In (a, k) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0) /\ a <> tk /\ a <> q) -> agree_on rsegs BS m mc)
by (apply (AGX m mc _ MU WM); apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]; cbn [fst snd pf_mxd]; lia);
clear MU WM; pose proof (wmono_refl rsegs mc) as WM; pose proof (munch_refl [(bse + 32, bse + 32 + 32)] mc) as MU
end.
clear TSK BASE Ld.
bst. bst.
apply evt_RZ_done.
pose proof BASE1 as (HP1 & ST1 & ERR1 & _).
eapply (reset_level_cps HIx PUT (S depth)) with (l := ln) (levels := lupd levels depth l')
(P := tstate_blocks ts0) (LB0 := LB0) (REST := pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)
(lo := lo) (errv := errv) (q := q) (r := tk) (pb := pb) (depth := Z.of_nat (S depth)) (mxd := mxd) (fl := fl)
(x := TS isd stpos (Z_to_bv 64 co) err ucs high quote) (rc := 1);
[ rewrite nth_error_lupd_neq by lia; exact Hln | lia | exact MXD1 | rewrite lupd_length; exact LEN32
| unfold lvl_blocks; rewrite Cn3, Cn5; exact HP1 | reflexivity
| rewrite Cn2, Cn3, Cn1; unfold put_pre; split; reflexivity
| left; split; [exact Cn4 | exact Cn5]
| exact TSK1
| unfold tok_cells, tok_cells_g; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote]; exact TOK
| rewrite unsigned_lit by lia; exact ST1 | exact LO
| rewrite unsigned_lit by lia; unfold RESET_STK, put_stk_P; lia
| rewrite unsigned_lit by lia; exact SPA
| rewrite unsigned_lit by lia; unfold PE_FRAME in *; lia
| apply heap_pres_refl | exact ERR1 | rewrite unsigned_lit by lia; reflexivity | ].
intros ms2 md2 (m2 & A2 & rv & RS2 & VM2 & OUT2 & TS2 & TOK2 & ST2 & HPR2 & ERR2 & AG2).
destruct RS2 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F2 & fc2 & -> & FS2 & FRM2).
rewrite ?unsigned_lit in ST2 by lia. rewrite ?unsigned_lit in HPR2 by lia.
lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?n)] => replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia | reflexivity]) end.
destruct OUT2 as [[_ HP3] | (s' & Es & _)]; [| rewrite Cn2 in Es; discriminate Es].
unstash PB.
assert (BASE3 : PE_BASE HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) LB0 payload me lo m2 md2 A2 (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0) errv)
by (eapply (PE_BASE_call HIx); [exact BASE1 | exact HPR2 | apply incl_refl | exact VM2 | exact HP3 | exact ST2 | exact ERR2]).
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
assert (AGB : agree_on rsegs BL m m2).
{ eapply agree_on_trans; [exact (AG1 BL BLfacts)|]. eapply agree_on_incl; [exact AG2|].
intros b Hb. unfold ts0, tstate_blocks. cbn [t_pbs t_objbs t_levels]. apply in_or_app; right; exact Hb. }
assert (PB3 : pbuf rsegs m2 pbs pb).
{ eapply pbuf_agree; [exact PB | | apply incl_refl]. eapply agree_on_trans; [exact (AG1 pbs PBSfacts)|]. eapply agree_on_incl; [exact AG2|].
intros b Hb. unfold ts0, tstate_blocks. cbn [t_pbs t_objbs t_levels]. apply in_or_app; left; exact Hb. }
unstash LV.
set (levels2 := lupd (lupd levels depth l') (S depth) lvl_reset).
eapply (Kredo _ md2 A2 errv); [ | exact FS2 | exact FRM2].
split.
-
unfold PE_CORE. cbn [t_levels t_depth t_co t_pb t_pbs t_x t_obj ts_choff pf_len pf_tk pf_spf pf_md pf_mxd pf_fl].
split; [rewrite !lupd_length; exact LEN32|]. split; [lia|]. split; [lia|]. split; [reflexivity|].
split; [exact TOK2|].
split; [exact PB3|]. split; [exact Hpb|]. split; [exact TS2|]. unfold pe_frame. exact FR.
-
apply (PE_REST_of_base HIx).
+ unfold pe_blocks, tstate_blocks. cbn [t_pbs t_objbs t_levels pf_tk pf_md pf_mxd pf_fl]. fold levels2.
replace (concat (map lvl_blocks levels2)) with BL by (symmetry; exact EBL). exact BASE3.
+ cbn [t_levels t_depth]. intros i li Hli. fold levels2 in Hli.
destruct (Nat.eq_dec i (S depth)) as [-> | NE1].
* unfold levels2 in Hli. rewrite nth_error_lupd_eq in Hli by (rewrite lupd_length; lia). injection Hli as <-.
split; [cbn; lia|]. split; [cbn; lia|]. split; [cbn; split; reflexivity|].
rewrite Nat.ltb_irrefl, Nat.eqb_refl. exists CNone, false. split; [reflexivity|]. split; [exact I|]. cbn. split; reflexivity.
* unfold levels2 in Hli. rewrite nth_error_lupd_neq in Hli by congruence.
destruct (Nat.eq_dec i depth) as [-> | NE2].
-- rewrite nth_error_lupd_eq in Hli by lia. injection Hli as <-.
split; [cbn; exact STN|]. split; [cbn; exact SS26|]. split.
{ cbn [tl_cs tl_cbs tl_cur l']. eapply (jopt_agree rsegs S4F); [exact JO | exact AGB |].
intros b Hb. unfold BL. apply in_concat. exists (lvl_blocks l). split; [apply in_map; eapply nth_error_In; exact Hl | unfold lvl_blocks; apply in_or_app; left; exact Hb]. }
rewrite (proj2 (Nat.ltb_lt depth (S depth))) by lia.
lazymatch type of AGB with agree_on _ _ _ ?mc =>
assert (NMt : forall hn, name_ok rsegs m hn l -> name_ok rsegs mc hn l')
by (intros hn N; eapply (name_ok_agree rsegs) with (l := l'); [exact N | exact AGB |];
intros b Hb; unfold BL; apply in_concat; exists (lvl_blocks l); split; [apply in_map; eapply nth_error_In; exact Hl | unfold lvl_blocks; apply in_or_app; right; exact Hb])
end.
destruct PARENT as [(E & C & N) | (E & C & N)]; [left | right]; (split; [exact E|]); (split; [exact C | exact (NMt _ N)]).
-- rewrite nth_error_lupd_neq in Hli by congruence.
apply lvl_cur_push; [exact NE2 | exact NE1 |].
eapply (lvl_cur_agree rsegs S4F); [exact (LV i li Hli) | exact AGB |].
intros b Hb. unfold BL. apply in_concat. exists (lvl_blocks li). split; [apply in_map; eapply nth_error_In; exact Hli | exact Hb].
+ unfold cur_st. cbn [t_levels t_depth t_objbs]. rewrite nth_error_lupd_eq by (rewrite lupd_length; lia). reflexivity.
Qed.

End PePush.

End RC__1.
End Mq5.

Module Mq6.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup.
Import UEQM.
Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0.
Import UC8c.Mq0.
Import Qsw7 QJjn QkMG.
Import UG8z Udyh.Mq0 Uu4M.Mq0 Udyh.Mq7.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.
Import Q6q3.
Import Tk2Gen.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section PeStartC.
Variable HIx : heap_iface S4L.
Hypothesis NEWO : jo_new_object_P HIx.
Hypothesis NEWA : jo_new_array_P HIx.

#[using="NEWO"] Lemma seg_start_object :
forall (pf : pe_fix) (q : Z) (LB0 : list blk) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (ts : tstate) (l : tlevel)
(cb : byte) (j1 j2 utf : list byte) (sv : pe_saved) (errv : word) (T : TSet)
(x1 gp t0 t1 t2 a1 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC HIx pf lo ->
PE_INV HIx pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_start ->

(forall m' md' A' r cbs' errv' x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F' fc',
r <> 0 ->
PE_INV HIx pf q LB0 payload me lo m' md' A'
(TST (t_depth ts) (lupd (t_levels ts) (t_depth ts) (TL ST_eatws ST_ofs r (Some (Sobj [])) cbs' 0 []))
(t_co ts) (t_pb ts) (t_pbs ts) (t_x ts) (t_obj ts) (t_objs ts) (t_objbs ts))
cb j1 j2 utf sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_BREAK (t_co ts) x1' gp' t0' t1' t2' (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F' fc' m') md') T) ->

(forall m' md' A' errv' x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F' fc',
PE_INVW HIx pf q LB0 payload me lo m' md' A'
(TST (t_depth ts) (lupd (t_levels ts) (t_depth ts) (TL ST_eatws ST_ofs 0 None [] 0 []))
(t_co ts) (t_pb ts) (t_pbs ts) (t_x ts) (t_obj ts) (t_objs ts) (t_objbs ts)) []
cb j1 j2 utf sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_ERR (t_co ts) x1' gp' t0' t1' t2' (Z_to_bv 64 16) a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F' fc' m') md') T) ->
realizes rsegs (mkCfg (pe_ms rsegs pf 0x23b38 (t_co ts) x1 gp t0 t1 t2
(Z_to_bv 64 0) a1 (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) a3 a4 a5 a6 a7
s4 s6 s7 s8 s9 s10 t3 t4 t5 t6 F fc m) md) T.
Proof.
intros until fc. intros STC INV Hl Hst Kbreak Kerr.
pose proof STC as (LO & LOS & SPA & HT & SP0 & LEN & SB0 & SBL).
destruct INV as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
apply (PE_REST_base HIx) in REST as (BASE & LV & OBJ).
pose proof (proj1 BASE) as HP.
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl_]; pe_gen fl_; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
unfold tok_cells, tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in TOK. unfold pe_frame in FR. unfold pe_ms in *. cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
unfold_consts.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocks; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, (32 * mxd)) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocks; apply in_or_app; right; right; left; reflexivity).
pose proof (heap_blk S4L HIx _ _ _ _ tk 72 HP INtk) as (_ & Htal & Htlo & Hthi & _).
pose proof (heap_blk S4L HIx _ _ _ _ q (32 * mxd) HP INq) as (_ & Hqal & Hqlo & Hqhi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hthi, Hqhi.
pose proof (heap_blk_nodup S4L HIx _ _ _ _ HP) as ND.
assert (Htq : tk <> q).
{ generalize ND; intros ND'. unfold pe_blocks in ND'. rewrite map_app in ND'. apply NoDup_app_remove_l in ND'.
cbn [map blk_addr fst pf_tk pf_md pf_mxd pf_fl] in ND'. apply List.NoDup_cons_iff in ND' as [Hni _]. intros E. apply Hni. left. symmetry. exact E. }
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ tk 72 q (32 * mxd) HP INtk INq Htq) as Hdtq.
assert (NQ0 : forall k, ~ In (q, k) LB0).
{ intros k. generalize ND; intros ND'. unfold ts0, pe_blocks, tstate_blocks in ND'. cbn [t_pbs t_objbs t_levels pf_tk pf_md pf_mxd pf_fl] in ND'.
rewrite <- !app_assoc in ND'. exact (nodup_mid_notin _ _ _ _ _ _ _ _ k ND'). }
assert (INCL0 : incl LB0 (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocks; intros b Hb; apply in_or_app; right; right; right; exact Hb).
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L pf_mxd] in MI.
pose proof (wmono_refl rsegs m) as WM.
pose proof (LV depth l Hl) as LVd. pose proof LVd as (ST26 & SS26 & JO & Md).
rewrite Nat.ltb_irrefl, Nat.eqb_refl in Md. destruct Md as (c0 & hn0 & Hmode & CLS0 & NM0).
rewrite Hst in Hmode. destruct (start_mode _ _ _ SS26 Hmode) as (Ess & -> & ->).
cbn [name_ok pf_mxd] in NM0. destruct NM0 as [Hn0 Hnbs0].
destruct (tl_cs l) as [s0c|] eqn:Ecs; [exfalso; exact CLS0|]. cbn [jopt pf_mxd] in JO. destruct JO as [Hc0 Hcbs0].
assert (LB0l : lvl_blocks l = []) by (unfold lvl_blocks; rewrite Hcbs0, Hnbs0; reflexivity).

set (BL := concat (map lvl_blocks levels)).
assert (BLfacts : forall a k, In (a, k) BL -> In (a, k) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0) /\ a <> tk /\ a <> q).
{ intros a k Hin.
assert (HinT : In (a, k) (tstate_blocks ts0)) by (unfold tstate_blocks, ts0; cbn [t_pbs t_objbs t_levels pf_mxd]; apply in_or_app; right; apply in_or_app; right; exact Hin).
assert (HinL : In (a, k) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocks; apply in_or_app; left; exact HinT).
split; [exact HinL|]. generalize ND; intros ND'. unfold pe_blocks in ND'. cbn [pf_tk pf_md pf_mxd pf_fl] in ND'. split.
- eapply (nodup_app_ne _ _ _ _ _ _ ND' HinT). left; reflexivity.
- eapply (nodup_app_ne _ _ _ _ _ _ ND' HinT). right; left; reflexivity. }
assert (PBSfacts : forall a k, In (a, k) pbs -> In (a, k) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0) /\ a <> tk /\ a <> q).
{ intros a k Hin. assert (HinT : In (a, k) (tstate_blocks ts0)) by (unfold tstate_blocks, ts0; cbn [t_pbs t_objbs t_levels pf_mxd]; apply in_or_app; left; exact Hin).
assert (HinL : In (a, k) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocks; apply in_or_app; left; exact HinT).
split; [exact HinL|]. generalize ND; intros ND'. unfold pe_blocks in ND'. cbn [pf_tk pf_md pf_mxd pf_fl] in ND'. split.
- eapply (nodup_app_ne _ _ _ _ _ _ ND' HinT). left; reflexivity.
- eapply (nodup_app_ne _ _ _ _ _ _ ND' HinT). right; left; reflexivity. }
assert (OBfacts : forall a k, In (a, k) objbs -> In (a, k) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0) /\ a <> tk /\ a <> q).
{ intros a k Hin. assert (HinT : In (a, k) (tstate_blocks ts0)) by (unfold tstate_blocks, ts0; cbn [t_pbs t_objbs t_levels pf_mxd]; apply in_or_app; right; apply in_or_app; left; exact Hin).
assert (HinL : In (a, k) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocks; apply in_or_app; left; exact HinT).
split; [exact HinL|]. generalize ND; intros ND'. unfold pe_blocks in ND'. cbn [pf_tk pf_md pf_mxd pf_fl] in ND'. split.
- eapply (nodup_app_ne _ _ _ _ _ _ ND' HinT). left; reflexivity.
- eapply (nodup_app_ne _ _ _ _ _ _ ND' HinT). right; left; reflexivity. }
assert (AGX : forall ma mz W, munch W ma mz -> wmono rsegs ma mz ->
Forall (fun iv => (q <= fst iv /\ snd iv <= q + (32 * mxd))) W ->
forall BS, (forall a k, In (a, k) BS -> In (a, k) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0) /\ a <> tk /\ a <> q) -> agree_on rsegs BS ma mz).
{ intros ma mz W MU1 WM1 HW BS HBS. eapply agree_of_munch; [exact MU1 | exact WM1 |]. intros a k Hin. destruct (HBS a k Hin) as (HinL & Hnt & Hnq).
pose proof (heap_blk S4L HIx _ _ _ _ a k (proj1 BASE) HinL) as (Hk0 & _ & _ & Hhi & _).
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ a k q (32 * mxd) (proj1 BASE) HinL INq Hnq).
clear - HW H Hhi Hk0 LO LOS. induction W as [|[lo' hi'] W IH]; [exact I|].
apply Forall_cons_iff in HW as [H1 HW]. cbn [fst snd pf_mxd] in H1. cbn [disjoint_from pf_mxd]. split; [| apply IH; exact HW]. lia. }
pose proof (TSK depth l Hl) as Ld. unfold srec_cells in Ld. rewrite Hc0, Hn0 in Ld.
remember (q + 32 * Z.of_nat depth) as bse eqn:Hbse in Ld.
assert (HbseR : q <= bse /\ bse + 32 <= q + (32 * mxd)) by (subst bse; lia).
assert (Hbal : bse mod 16 = 0) by (subst bse; clear - Hqal; Z.div_mod_to_equations; lia).
pose proof (munch_refl [(bse, bse + 32)] m) as MU.
stash PB. stash TSK. stash BASE. stash LV. clear HP.
apply rz_evt; [exact MOK|]. replace (q + 32 * Z.of_nat depth) with bse by lia.
step. stepz. bst. bst. bst.

set (l1 := TL ST_eatws ST_ofs 0 None [] 0 []) in *.
unstash PB. unstash TSK. unstash BASE. unstash LV.
assert (HW1 : Forall (base_w (PEF tk oldl newl len lenr sb spf pmd mxd fl) LB0 (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) [(bse, bse + 32)]).
{ apply Forall_cons; [| apply Forall_nil]; unfold base_w; cbn [fst snd pf_spf pf_md pf_mxd pf_fl]. left. exists q, (32 * mxd). split; [exact INq|]. split; [exact NQ0 | lia]. }
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (TSK1 : tstack rsegs mc q (lupd levels depth l1))
by (subst bse; eapply (tstack_put rsegs m _ q levels depth l1 []);
[exact TSK | lia | exact MU | exact WM | intros; exact I | unfold srec_cells, l1; cbn [tl_st tl_ss tl_cur tl_name pf_mxd]; exact Ld]);
assert (BASE1 : PE_BASE HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) LB0 payload me lo mc md A (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0) errv)
by (eapply (PE_BASE_write HIx); [exact STC | exact BASE | exact INCL0 | exact MU | exact WM | exact MI | exact HW1]);
assert (AG1 : forall BS, (forall a k, In (a, k) BS -> In (a, k) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0) /\ a <> tk /\ a <> q) -> agree_on rsegs BS m mc)
by (apply (AGX m mc _ MU WM); apply Forall_cons; [| apply Forall_nil]; cbn [fst snd pf_mxd]; lia)
end.
pose proof (pbuf_agree rsegs _ _ _ _ _ PB (AG1 pbs PBSfacts) (incl_refl _)) as PB1.
pose proof (AG1 BL BLfacts) as AGL1.
assert (Eobjbs : objbs = []).
{ revert OBJ. unfold cur_st, ts0. cbn [t_levels t_depth t_objbs pf_mxd]. rewrite Hl, Hst. cbn. intros E; exact E. }
clear PB TSK BASE MU WM Ld.
apply evt_RZ_done.
eapply NEWO with (LB := pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0) (lo := lo) (errv := errv); [| exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 BASE1)))))))) |].
{ pose proof BASE1 as (HP1 & ST0 & ERR0 & _). unfold jo_pre. cbn [hl_segs hl_tp S4L pf_mxd].
split; [exact HP1 |]. rewrite ?unsigned_lit by lia. unfold PE_FRAME in *.
split; [exact ST0|]. split; [clia|]. split; [clia|]. split; [exact SPA|]. split; [lia|]. split; [exact ERR0|]. split; [reflexivity|]. reflexivity. }
intros ms2 md2 mp r (RS2 & VM2 & ST2 & HPR2 & (errv2 & ERR2)) OUT.
destruct RS2 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F2 & fc2 & -> & FS2 & FRM2).
cbn [hl_segs hl_tp S4L pf_mxd] in *. rewrite ?(unsigned_lit spf) in ST2 by lia. rewrite ?(unsigned_lit spf) in HPR2 by lia.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. cbn [hl_segs S4L pf_mxd] in FR.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in TOK; [| eapply client_range_block; [exact INtk | lia | cbn; lia]]. cbn [hl_segs S4L pf_mxd] in TOK.
apply (tstack_pres_g S4L _ _ _ _ _ _ HPR2 INq) in TSK1; [| rewrite lupd_length; exact LEN32].
pose proof (TSK1 depth l1 ltac:(rewrite nth_error_lupd_eq by lia; reflexivity)) as Ld. unfold srec_cells, l1 in Ld. cbn [tl_st tl_ss tl_cur tl_name pf_mxd] in Ld.
rewrite <- Hbse in Ld. cbn [hl_segs S4L pf_mxd] in Ld, TSK1.
assert (PB2 : pbuf rsegs mp pbs pb).
{ eapply pbuf_agree; [exact PB1 | | apply incl_refl]. eapply (agree_of_heap_pres rsegs S4L); [exact HPR2 | reflexivity |].
intros b Hb. unfold pe_blocks, tstate_blocks. apply in_or_app; left. apply in_or_app; left. exact Hb. }
assert (AGL2 : agree_on rsegs BL m mp).
{ eapply agree_on_trans; [exact AGL1|]. eapply (agree_of_heap_pres rsegs S4L); [exact HPR2 | reflexivity |].
intros b Hb. unfold pe_blocks, tstate_blocks. apply in_or_app; left. apply in_or_app; right. apply in_or_app; right. exact Hb. }
assert (LV2 : forall i li, nth_error levels i = Some li -> i <> depth -> lvl_cur rsegs S4F mp depth i li).
{ intros i li Hli Hne. eapply (lvl_cur_agree rsegs S4F); [exact (LV i li Hli) | exact AGL2 |].
intros b Hb. unfold BL. apply in_concat. exists (lvl_blocks li). split; [| exact Hb]. apply in_map. eapply nth_error_In. exact Hli. }
clear PB1 AGL1 AG1 MI.

assert (OUT' : exists A2 NB, HEAP S4L HIx A2 (NB ++ pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0) mp md2 /\
((r = 0 /\ NB = []) \/ (r <> 0 /\ jval rsegs S4F (Sobj []) mp NB r 1))).
{ destruct OUT as [(-> & A2 & HP2) | (Hr & A2 & NB & J2 & HP2)].
- exists A2, []. split; [exact HP2 | left; split; reflexivity].
- exists A2, NB. split; [exact HP2 | right; split; [exact Hr | exact J2]]. }
clear OUT. destruct OUT' as (A2 & NB & HP2 & OUT).
assert (BASE2 : PE_BASE HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) LB0 payload me lo mp md2 A2 (NB ++ pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0) errv2)
by (eapply (PE_BASE_call HIx); [exact BASE1 | exact HPR2 | exact INCL0 | exact VM2 | exact HP2 | exact ST2 | exact ERR2]).
clear BASE1 HPR2.
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2.
pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI. cbn [hl_segs S4L pf_mxd] in MI.
pose proof (wmono_refl rsegs mp) as WM.
pose proof (munch_refl [(bse, bse + 32)] mp) as MU.
pose proof (heap_blk_nodup S4L HIx _ _ _ _ HP2) as ND2.
assert (NEq : forall a k, In (a, k) (NB ++ pbs ++ BL) -> In (a, k) (NB ++ pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0) /\ a <> q).
{ intros a k Hin. apply in_app_or in Hin. destruct Hin as [Hin | Hin].
- split; [apply in_or_app; left; exact Hin|]. intros ->. rewrite map_app in ND2.
eapply (NoDup_app_in2 _ _ q ND2); [exact (in_map blk_addr _ _ Hin) | exact (in_map blk_addr _ _ INq)].
- apply in_app_or in Hin. destruct Hin as [Hin | Hin].
+ destruct (PBSfacts a k Hin) as (H1 & _ & H3). split; [apply in_or_app; right; exact H1 | exact H3].
+ destruct (BLfacts a k Hin) as (H1 & _ & H3). split; [apply in_or_app; right; exact H1 | exact H3]. }
assert (AGY : forall mz, munch [(bse, bse + 32)] mp mz -> wmono rsegs mp mz ->
forall BS, (forall a k, In (a, k) BS -> In (a, k) (NB ++ pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0) /\ a <> q) -> agree_on rsegs BS mp mz).
{ intros mz MU1 WM1 BS HBS. eapply agree_of_munch; [exact MU1 | exact WM1 |]. intros a k Hin. destruct (HBS a k Hin) as (HinL & Hnq).
pose proof (heap_blk S4L HIx _ _ _ _ a k HP2 HinL) as (Hk0 & _).
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ a k q (32 * mxd) HP2 HinL ltac:(apply in_or_app; right; exact INq) Hnq). cbn. lia. }
stash PB2. stash TSK1. stash BASE2. stash LV2. stash OUT.
reenter MOK2.
bst.
step. norm_sx32. step.
step. rewrite (unsigned_lit (Z.of_nat depth)) by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32.
step. replace (q + Z.of_nat depth * 32) with bse by lia.
bst.
unstash PB2. unstash TSK1. unstash BASE2. unstash LV2. unstash OUT.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (BASE3 : PE_BASE HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) LB0 payload me lo mc md2 A2 (NB ++ pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0) errv2)
by (eapply (PE_BASE_write HIx); [exact STC | exact BASE2 | intros b Hb; apply in_or_app; right; exact (INCL0 _ Hb) | exact MU | exact WM | exact MI |];
apply Forall_cons; [| apply Forall_nil]; unfold base_w; cbn [fst snd pf_spf pf_md pf_mxd pf_fl]; left; exists q, (32 * mxd);
split; [apply in_or_app; right; exact INq|]; split; [exact NQ0 | lia]);
assert (PB3 : pbuf rsegs mc pbs pb)
by (eapply pbuf_agree; [exact PB2 | apply (AGY mc MU WM) | apply incl_refl]; intros a k Hin; eapply NEq; apply in_or_app; right; apply in_or_app; left; exact Hin);
assert (AGL3 : agree_on rsegs BL mp mc)
by (apply (AGY mc MU WM); intros a k Hin; eapply NEq; apply in_or_app; right; apply in_or_app; right; exact Hin);
assert (AGN : agree_on rsegs NB mp mc)
by (apply (AGY mc MU WM); intros a k Hin; eapply NEq; apply in_or_app; left; exact Hin);
assert (LV3 : forall i li, nth_error levels i = Some li -> i <> depth -> lvl_cur rsegs S4F mc depth i li)
by (intros i li Hli Hne; eapply (lvl_cur_agree rsegs S4F); [exact (LV2 i li Hli Hne) | exact AGL3 |];
intros b Hb; unfold BL; apply in_concat; exists (lvl_blocks li); split; [| exact Hb]; apply in_map; eapply nth_error_In; exact Hli)
end.
destruct OUT as [[-> ->] | [Hr J2]].
-
bst. if_false. bst. bst. bst.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (TSK3 : tstack rsegs mc q (lupd levels depth (TL ST_eatws ST_ofs 0 None [] 0 [])))
by (rewrite <- (lupd_lupd _ levels depth l1); subst bse;
eapply (tstack_put rsegs mp mc q (lupd levels depth l1) depth _ []);
[exact TSK1 | rewrite lupd_length; lia | exact MU | exact WM | intros; exact I | unfold srec_cells; cbn [tl_st tl_ss tl_cur tl_name pf_mxd]; exact Ld])
end.
apply evt_RZ_done. eapply (Kerr _ md2 A2 errv2); [ | exact FS2 | exact FRM2].
split; [| split].
+ unfold PE_CORE. cbn [t_levels t_depth t_co t_pb t_pbs t_x t_obj ts_choff pf_len pf_tk pf_spf pf_md pf_mxd pf_fl].
split; [rewrite lupd_length; exact LEN32|]. split; [exact D32|]. split; [lia|]. split; [reflexivity|].
split; [unfold tok_cells, tok_cells_g; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd]; exact TOK|].
split; [exact PB3|]. split; [exact Hpb|]. split; [exact TSK3 | unfold pe_frame; exact FR].
+ rewrite app_nil_r. cbn [app pf_mxd] in BASE3. eapply (PE_BASE_perm HIx); [exact BASE3|].
unfold pe_blocks, tstate_blocks, ts0. cbn [t_pbs t_objbs t_levels pf_tk pf_md pf_mxd pf_fl].
fold l1. rewrite (map_lupd_same lvl_blocks levels depth l1 l Hl) by (rewrite LB0l; reflexivity). apply Permutation_refl.
+ cbn [t_levels t_depth pf_mxd]. intros i li Hli.
destruct (Nat.eq_dec i depth) as [-> | NE].
* rewrite nth_error_lupd_eq in Hli by lia. injection Hli as <-. split; [subst l1; cbn; unfold ST_eatws, ST_ofs, ST_array; lia|]. split; [cbn; split; reflexivity|]. split; [left; cbn; split; reflexivity|]. intros; lia.
* rewrite nth_error_lupd_neq in Hli by congruence. apply lvl_cur_weak. exact (LV3 i li Hli NE).
-
assert (HrR : 0 < r < 2^64).
{ destruct J2 as (pbx & PBS & REST & ENB & _ & tx & TBS & kvs & KBS & ER & _).
pose proof (heap_blk S4L HIx _ _ _ _ r 48 HP2 ltac:(apply in_or_app; left; rewrite ENB, ER; apply in_or_app; left; left; reflexivity)) as (_ & _ & H0 & Hhi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hhi. lia. }
bst. if_truex.
set (l' := TL ST_eatws ST_ofs r (Some (Sobj [])) NB 0 []).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (TSK3 : tstack rsegs mc q (lupd levels depth l'))
by (rewrite <- (lupd_lupd _ levels depth l1); subst bse;
eapply (tstack_put rsegs mp mc q (lupd levels depth l1) depth _ []);
[exact TSK1 | rewrite lupd_length; lia | exact MU | exact WM | intros; exact I | unfold srec_cells, l'; cbn [tl_st tl_ss tl_cur tl_name pf_mxd]; exact Ld])
end.
apply evt_RZ_done. eapply (Kbreak _ md2 A2 r NB errv2); [exact Hr | | exact FS2 | exact FRM2].
split.
+ unfold PE_CORE. cbn [t_levels t_depth t_co t_pb t_pbs t_x t_obj ts_choff pf_len pf_tk pf_spf pf_md pf_mxd pf_fl].
split; [rewrite lupd_length; exact LEN32|]. split; [exact D32|]. split; [lia|]. split; [reflexivity|].
split; [unfold tok_cells, tok_cells_g; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd]; exact TOK|].
split; [exact PB3|]. split; [exact Hpb|]. split; [exact TSK3 | unfold pe_frame; exact FR].
+ apply (PE_REST_of_base HIx).
* eapply (PE_BASE_perm HIx); [exact BASE3|].
unfold pe_blocks, tstate_blocks, ts0. cbn [t_pbs t_objbs t_levels pf_tk pf_md pf_mxd pf_fl]. rewrite <- !app_assoc.
apply (Permutation_trans (l' := pbs ++ (objbs ++ (NB ++ (concat (map lvl_blocks levels) ++ (tk, 72) :: (q, (32 * mxd)) :: LB0))))).
-- apply (Permutation_trans (l' := pbs ++ (NB ++ (objbs ++ (concat (map lvl_blocks levels) ++ (tk, 72) :: (q, (32 * mxd)) :: LB0))))); [apply Permutation_app_swap_app|].
apply Permutation_app_head. apply Permutation_app_swap_app.
-- apply Permutation_app_head. apply Permutation_app_head. rewrite (app_assoc NB). apply Permutation_app_tail. fold l'.
replace (NB ++ concat (map lvl_blocks levels)) with (lvl_blocks l' ++ concat (map lvl_blocks levels)) by (unfold lvl_blocks, l'; cbn; rewrite app_nil_r; reflexivity).
apply (concat_lupd_fill levels depth l); [exact Hl | exact LB0l].
* cbn [t_levels t_depth pf_mxd]. intros i li Hli.
destruct (Nat.eq_dec i depth) as [-> | NE].
-- rewrite nth_error_lupd_eq in Hli by lia. injection Hli as <-.
split; [cbn; unfold ST_eatws; lia|]. split; [cbn; unfold ST_ofs; lia|]. split.
{ cbn [tl_cs tl_cbs tl_cur l' jopt pf_mxd]. split; [exact Hr|]. eapply jval_agree; [exact J2 | exact AGN | apply incl_refl]. }
rewrite Nat.ltb_irrefl, Nat.eqb_refl. exists CObj, false. split; [reflexivity|]. split; [exact I|]. cbn. split; reflexivity.
-- rewrite nth_error_lupd_neq in Hli by congruence. exact (LV3 i li Hli NE).
* revert OBJ. unfold cur_st, ts0. cbn [t_levels t_depth t_objs t_objbs t_obj pf_mxd]. rewrite nth_error_lupd_eq by lia. rewrite Hl, Hst. cbn. intros E; exact E.
Qed.
#[using="NEWA"] Lemma seg_start_array :
forall (pf : pe_fix) (q : Z) (LB0 : list blk) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (ts : tstate) (l : tlevel)
(cb : byte) (j1 j2 utf : list byte) (sv : pe_saved) (errv : word) (T : TSet)
(x1 gp t0 t1 t2 a1 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC HIx pf lo ->
PE_INV HIx pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_start ->

(forall m' md' A' r cbs' errv' x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F' fc',
r <> 0 ->
PE_INV HIx pf q LB0 payload me lo m' md' A'
(TST (t_depth ts) (lupd (t_levels ts) (t_depth ts) (TL ST_eatws ST_array r (Some (Sarr [])) cbs' 0 []))
(t_co ts) (t_pb ts) (t_pbs ts) (t_x ts) (t_obj ts) (t_objs ts) (t_objbs ts))
cb j1 j2 utf sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_BREAK (t_co ts) x1' gp' t0' t1' t2' (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F' fc' m') md') T) ->

(forall m' md' A' errv' x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F' fc',
PE_INVW HIx pf q LB0 payload me lo m' md' A'
(TST (t_depth ts) (lupd (t_levels ts) (t_depth ts) (TL ST_eatws ST_array 0 None [] 0 []))
(t_co ts) (t_pb ts) (t_pbs ts) (t_x ts) (t_obj ts) (t_objs ts) (t_objbs ts)) []
cb j1 j2 utf sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_ERR (t_co ts) x1' gp' t0' t1' t2' (Z_to_bv 64 16) a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F' fc' m') md') T) ->
realizes rsegs (mkCfg (pe_ms rsegs pf 0x23b84 (t_co ts) x1 gp t0 t1 t2
(Z_to_bv 64 0) a1 (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) a3 a4 a5 a6 a7
s4 s6 s7 s8 s9 s10 t3 t4 t5 t6 F fc m) md) T.
Proof.
intros until fc. intros STC INV Hl Hst Kbreak Kerr.
pose proof STC as (LO & LOS & SPA & HT & SP0 & LEN & SB0 & SBL).
destruct INV as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
apply (PE_REST_base HIx) in REST as (BASE & LV & OBJ).
pose proof (proj1 BASE) as HP.
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl_]; pe_gen fl_; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
unfold tok_cells, tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in TOK. unfold pe_frame in FR. unfold pe_ms in *. cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
unfold_consts.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocks; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, (32 * mxd)) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocks; apply in_or_app; right; right; left; reflexivity).
pose proof (heap_blk S4L HIx _ _ _ _ tk 72 HP INtk) as (_ & Htal & Htlo & Hthi & _).
pose proof (heap_blk S4L HIx _ _ _ _ q (32 * mxd) HP INq) as (_ & Hqal & Hqlo & Hqhi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hthi, Hqhi.
pose proof (heap_blk_nodup S4L HIx _ _ _ _ HP) as ND.
assert (Htq : tk <> q).
{ generalize ND; intros ND'. unfold pe_blocks in ND'. rewrite map_app in ND'. apply NoDup_app_remove_l in ND'.
cbn [map blk_addr fst pf_tk pf_md pf_mxd pf_fl] in ND'. apply List.NoDup_cons_iff in ND' as [Hni _]. intros E. apply Hni. left. symmetry. exact E. }
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ tk 72 q (32 * mxd) HP INtk INq Htq) as Hdtq.
assert (NQ0 : forall k, ~ In (q, k) LB0).
{ intros k. generalize ND; intros ND'. unfold ts0, pe_blocks, tstate_blocks in ND'. cbn [t_pbs t_objbs t_levels pf_tk pf_md pf_mxd pf_fl] in ND'.
rewrite <- !app_assoc in ND'. exact (nodup_mid_notin _ _ _ _ _ _ _ _ k ND'). }
assert (INCL0 : incl LB0 (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocks; intros b Hb; apply in_or_app; right; right; right; exact Hb).
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L pf_mxd] in MI.
pose proof (wmono_refl rsegs m) as WM.
pose proof (LV depth l Hl) as LVd. pose proof LVd as (ST26 & SS26 & JO & Md).
rewrite Nat.ltb_irrefl, Nat.eqb_refl in Md. destruct Md as (c0 & hn0 & Hmode & CLS0 & NM0).
rewrite Hst in Hmode. destruct (start_mode _ _ _ SS26 Hmode) as (Ess & -> & ->).
cbn [name_ok pf_mxd] in NM0. destruct NM0 as [Hn0 Hnbs0].
destruct (tl_cs l) as [s0c|] eqn:Ecs; [exfalso; exact CLS0|]. cbn [jopt pf_mxd] in JO. destruct JO as [Hc0 Hcbs0].
assert (LB0l : lvl_blocks l = []) by (unfold lvl_blocks; rewrite Hcbs0, Hnbs0; reflexivity).

set (BL := concat (map lvl_blocks levels)).
assert (BLfacts : forall a k, In (a, k) BL -> In (a, k) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0) /\ a <> tk /\ a <> q).
{ intros a k Hin.
assert (HinT : In (a, k) (tstate_blocks ts0)) by (unfold tstate_blocks, ts0; cbn [t_pbs t_objbs t_levels pf_mxd]; apply in_or_app; right; apply in_or_app; right; exact Hin).
assert (HinL : In (a, k) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocks; apply in_or_app; left; exact HinT).
split; [exact HinL|]. generalize ND; intros ND'. unfold pe_blocks in ND'. cbn [pf_tk pf_md pf_mxd pf_fl] in ND'. split.
- eapply (nodup_app_ne _ _ _ _ _ _ ND' HinT). left; reflexivity.
- eapply (nodup_app_ne _ _ _ _ _ _ ND' HinT). right; left; reflexivity. }
assert (PBSfacts : forall a k, In (a, k) pbs -> In (a, k) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0) /\ a <> tk /\ a <> q).
{ intros a k Hin. assert (HinT : In (a, k) (tstate_blocks ts0)) by (unfold tstate_blocks, ts0; cbn [t_pbs t_objbs t_levels pf_mxd]; apply in_or_app; left; exact Hin).
assert (HinL : In (a, k) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocks; apply in_or_app; left; exact HinT).
split; [exact HinL|]. generalize ND; intros ND'. unfold pe_blocks in ND'. cbn [pf_tk pf_md pf_mxd pf_fl] in ND'. split.
- eapply (nodup_app_ne _ _ _ _ _ _ ND' HinT). left; reflexivity.
- eapply (nodup_app_ne _ _ _ _ _ _ ND' HinT). right; left; reflexivity. }
assert (OBfacts : forall a k, In (a, k) objbs -> In (a, k) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0) /\ a <> tk /\ a <> q).
{ intros a k Hin. assert (HinT : In (a, k) (tstate_blocks ts0)) by (unfold tstate_blocks, ts0; cbn [t_pbs t_objbs t_levels pf_mxd]; apply in_or_app; right; apply in_or_app; left; exact Hin).
assert (HinL : In (a, k) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocks; apply in_or_app; left; exact HinT).
split; [exact HinL|]. generalize ND; intros ND'. unfold pe_blocks in ND'. cbn [pf_tk pf_md pf_mxd pf_fl] in ND'. split.
- eapply (nodup_app_ne _ _ _ _ _ _ ND' HinT). left; reflexivity.
- eapply (nodup_app_ne _ _ _ _ _ _ ND' HinT). right; left; reflexivity. }
assert (AGX : forall ma mz W, munch W ma mz -> wmono rsegs ma mz ->
Forall (fun iv => (q <= fst iv /\ snd iv <= q + (32 * mxd))) W ->
forall BS, (forall a k, In (a, k) BS -> In (a, k) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0) /\ a <> tk /\ a <> q) -> agree_on rsegs BS ma mz).
{ intros ma mz W MU1 WM1 HW BS HBS. eapply agree_of_munch; [exact MU1 | exact WM1 |]. intros a k Hin. destruct (HBS a k Hin) as (HinL & Hnt & Hnq).
pose proof (heap_blk S4L HIx _ _ _ _ a k (proj1 BASE) HinL) as (Hk0 & _ & _ & Hhi & _).
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ a k q (32 * mxd) (proj1 BASE) HinL INq Hnq).
clear - HW H Hhi Hk0 LO LOS. induction W as [|[lo' hi'] W IH]; [exact I|].
apply Forall_cons_iff in HW as [H1 HW]. cbn [fst snd pf_mxd] in H1. cbn [disjoint_from pf_mxd]. split; [| apply IH; exact HW]. lia. }
pose proof (TSK depth l Hl) as Ld. unfold srec_cells in Ld. rewrite Hc0, Hn0 in Ld.
remember (q + 32 * Z.of_nat depth) as bse eqn:Hbse in Ld.
assert (HbseR : q <= bse /\ bse + 32 <= q + (32 * mxd)) by (subst bse; lia).
assert (Hbal : bse mod 16 = 0) by (subst bse; clear - Hqal; Z.div_mod_to_equations; lia).
pose proof (munch_refl [(bse, bse + 32)] m) as MU.
stash PB. stash TSK. stash BASE. stash LV. clear HP.
apply rz_evt; [exact MOK|]. replace (q + 32 * Z.of_nat depth) with bse by lia.
step. stepz. bst. bst. bst.

set (l1 := TL ST_eatws ST_array 0 None [] 0 []) in *.
unstash PB. unstash TSK. unstash BASE. unstash LV.
assert (HW1 : Forall (base_w (PEF tk oldl newl len lenr sb spf pmd mxd fl) LB0 (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) [(bse, bse + 32)]).
{ apply Forall_cons; [| apply Forall_nil]; unfold base_w; cbn [fst snd pf_spf pf_md pf_mxd pf_fl]. left. exists q, (32 * mxd). split; [exact INq|]. split; [exact NQ0 | lia]. }
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (TSK1 : tstack rsegs mc q (lupd levels depth l1))
by (subst bse; eapply (tstack_put rsegs m _ q levels depth l1 []);
[exact TSK | lia | exact MU | exact WM | intros; exact I | unfold srec_cells, l1; cbn [tl_st tl_ss tl_cur tl_name pf_mxd]; exact Ld]);
assert (BASE1 : PE_BASE HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) LB0 payload me lo mc md A (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0) errv)
by (eapply (PE_BASE_write HIx); [exact STC | exact BASE | exact INCL0 | exact MU | exact WM | exact MI | exact HW1]);
assert (AG1 : forall BS, (forall a k, In (a, k) BS -> In (a, k) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0) /\ a <> tk /\ a <> q) -> agree_on rsegs BS m mc)
by (apply (AGX m mc _ MU WM); apply Forall_cons; [| apply Forall_nil]; cbn [fst snd pf_mxd]; lia)
end.
pose proof (pbuf_agree rsegs _ _ _ _ _ PB (AG1 pbs PBSfacts) (incl_refl _)) as PB1.
pose proof (AG1 BL BLfacts) as AGL1.
assert (Eobjbs : objbs = []).
{ revert OBJ. unfold cur_st, ts0. cbn [t_levels t_depth t_objbs pf_mxd]. rewrite Hl, Hst. cbn. intros E; exact E. }
clear PB TSK BASE MU WM Ld.
apply evt_RZ_done.
eapply NEWA with (LB := pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0) (lo := lo) (errv := errv); [| exact I |].
{ pose proof BASE1 as (HP1 & ST0 & ERR0 & _). unfold jo_pre. cbn [hl_segs hl_tp S4L pf_mxd].
split; [exact HP1 |]. rewrite ?unsigned_lit by lia. unfold PE_FRAME in *.
split; [exact ST0|]. split; [clia|]. split; [clia|]. split; [exact SPA|]. split; [lia|]. split; [exact ERR0|]. split; [reflexivity|]. reflexivity. }
intros ms2 md2 mp r (RS2 & VM2 & ST2 & HPR2 & (errv2 & ERR2)) OUT.
destruct RS2 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F2 & fc2 & -> & FS2 & FRM2).
cbn [hl_segs hl_tp S4L pf_mxd] in *. rewrite ?(unsigned_lit spf) in ST2 by lia. rewrite ?(unsigned_lit spf) in HPR2 by lia.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. cbn [hl_segs S4L pf_mxd] in FR.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in TOK; [| eapply client_range_block; [exact INtk | lia | cbn; lia]]. cbn [hl_segs S4L pf_mxd] in TOK.
apply (tstack_pres_g S4L _ _ _ _ _ _ HPR2 INq) in TSK1; [| rewrite lupd_length; exact LEN32].
pose proof (TSK1 depth l1 ltac:(rewrite nth_error_lupd_eq by lia; reflexivity)) as Ld. unfold srec_cells, l1 in Ld. cbn [tl_st tl_ss tl_cur tl_name pf_mxd] in Ld.
rewrite <- Hbse in Ld. cbn [hl_segs S4L pf_mxd] in Ld, TSK1.
assert (PB2 : pbuf rsegs mp pbs pb).
{ eapply pbuf_agree; [exact PB1 | | apply incl_refl]. eapply (agree_of_heap_pres rsegs S4L); [exact HPR2 | reflexivity |].
intros b Hb. unfold pe_blocks, tstate_blocks. apply in_or_app; left. apply in_or_app; left. exact Hb. }
assert (AGL2 : agree_on rsegs BL m mp).
{ eapply agree_on_trans; [exact AGL1|]. eapply (agree_of_heap_pres rsegs S4L); [exact HPR2 | reflexivity |].
intros b Hb. unfold pe_blocks, tstate_blocks. apply in_or_app; left. apply in_or_app; right. apply in_or_app; right. exact Hb. }
assert (LV2 : forall i li, nth_error levels i = Some li -> i <> depth -> lvl_cur rsegs S4F mp depth i li).
{ intros i li Hli Hne. eapply (lvl_cur_agree rsegs S4F); [exact (LV i li Hli) | exact AGL2 |].
intros b Hb. unfold BL. apply in_concat. exists (lvl_blocks li). split; [| exact Hb]. apply in_map. eapply nth_error_In. exact Hli. }
clear PB1 AGL1 AG1 MI.

assert (OUT' : exists A2 NB, HEAP S4L HIx A2 (NB ++ pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0) mp md2 /\
((r = 0 /\ NB = []) \/ (r <> 0 /\ jval rsegs S4F (Sarr []) mp NB r 1))).
{ destruct OUT as [(-> & A2 & HP2) | (Hr & A2 & NB & J2 & HP2)].
- exists A2, []. split; [exact HP2 | left; split; reflexivity].
- exists A2, NB. split; [exact HP2 | right; split; [exact Hr | exact J2]]. }
clear OUT. destruct OUT' as (A2 & NB & HP2 & OUT).
assert (BASE2 : PE_BASE HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) LB0 payload me lo mp md2 A2 (NB ++ pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0) errv2)
by (eapply (PE_BASE_call HIx); [exact BASE1 | exact HPR2 | exact INCL0 | exact VM2 | exact HP2 | exact ST2 | exact ERR2]).
clear BASE1 HPR2.
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2.
pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI. cbn [hl_segs S4L pf_mxd] in MI.
pose proof (wmono_refl rsegs mp) as WM.
pose proof (munch_refl [(bse, bse + 32)] mp) as MU.
pose proof (heap_blk_nodup S4L HIx _ _ _ _ HP2) as ND2.
assert (NEq : forall a k, In (a, k) (NB ++ pbs ++ BL) -> In (a, k) (NB ++ pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0) /\ a <> q).
{ intros a k Hin. apply in_app_or in Hin. destruct Hin as [Hin | Hin].
- split; [apply in_or_app; left; exact Hin|]. intros ->. rewrite map_app in ND2.
eapply (NoDup_app_in2 _ _ q ND2); [exact (in_map blk_addr _ _ Hin) | exact (in_map blk_addr _ _ INq)].
- apply in_app_or in Hin. destruct Hin as [Hin | Hin].
+ destruct (PBSfacts a k Hin) as (H1 & _ & H3). split; [apply in_or_app; right; exact H1 | exact H3].
+ destruct (BLfacts a k Hin) as (H1 & _ & H3). split; [apply in_or_app; right; exact H1 | exact H3]. }
assert (AGY : forall mz, munch [(bse, bse + 32)] mp mz -> wmono rsegs mp mz ->
forall BS, (forall a k, In (a, k) BS -> In (a, k) (NB ++ pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0) /\ a <> q) -> agree_on rsegs BS mp mz).
{ intros mz MU1 WM1 BS HBS. eapply agree_of_munch; [exact MU1 | exact WM1 |]. intros a k Hin. destruct (HBS a k Hin) as (HinL & Hnq).
pose proof (heap_blk S4L HIx _ _ _ _ a k HP2 HinL) as (Hk0 & _).
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ a k q (32 * mxd) HP2 HinL ltac:(apply in_or_app; right; exact INq) Hnq). cbn. lia. }
stash PB2. stash TSK1. stash BASE2. stash LV2. stash OUT.
reenter MOK2.
step. norm_sx32. step.
step. rewrite (unsigned_lit (Z.of_nat depth)) by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32.
step. replace (q + Z.of_nat depth * 32) with bse by lia.
bst.
unstash PB2. unstash TSK1. unstash BASE2. unstash LV2. unstash OUT.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (BASE3 : PE_BASE HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) LB0 payload me lo mc md2 A2 (NB ++ pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0) errv2)
by (eapply (PE_BASE_write HIx); [exact STC | exact BASE2 | intros b Hb; apply in_or_app; right; exact (INCL0 _ Hb) | exact MU | exact WM | exact MI |];
apply Forall_cons; [| apply Forall_nil]; unfold base_w; cbn [fst snd pf_spf pf_md pf_mxd pf_fl]; left; exists q, (32 * mxd);
split; [apply in_or_app; right; exact INq|]; split; [exact NQ0 | lia]);
assert (PB3 : pbuf rsegs mc pbs pb)
by (eapply pbuf_agree; [exact PB2 | apply (AGY mc MU WM) | apply incl_refl]; intros a k Hin; eapply NEq; apply in_or_app; right; apply in_or_app; left; exact Hin);
assert (AGL3 : agree_on rsegs BL mp mc)
by (apply (AGY mc MU WM); intros a k Hin; eapply NEq; apply in_or_app; right; apply in_or_app; right; exact Hin);
assert (AGN : agree_on rsegs NB mp mc)
by (apply (AGY mc MU WM); intros a k Hin; eapply NEq; apply in_or_app; left; exact Hin);
assert (LV3 : forall i li, nth_error levels i = Some li -> i <> depth -> lvl_cur rsegs S4F mc depth i li)
by (intros i li Hli Hne; eapply (lvl_cur_agree rsegs S4F); [exact (LV2 i li Hli Hne) | exact AGL3 |];
intros b Hb; unfold BL; apply in_concat; exists (lvl_blocks li); split; [| exact Hb]; apply in_map; eapply nth_error_In; exact Hli)
end.
destruct OUT as [[-> ->] | [Hr J2]].
-
bst. if_false. bst. bst. bst.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (TSK3 : tstack rsegs mc q (lupd levels depth (TL ST_eatws ST_array 0 None [] 0 [])))
by (rewrite <- (lupd_lupd _ levels depth l1); subst bse;
eapply (tstack_put rsegs mp mc q (lupd levels depth l1) depth _ []);
[exact TSK1 | rewrite lupd_length; lia | exact MU | exact WM | intros; exact I | unfold srec_cells; cbn [tl_st tl_ss tl_cur tl_name pf_mxd]; exact Ld])
end.
apply evt_RZ_done. eapply (Kerr _ md2 A2 errv2); [ | exact FS2 | exact FRM2].
split; [| split].
+ unfold PE_CORE. cbn [t_levels t_depth t_co t_pb t_pbs t_x t_obj ts_choff pf_len pf_tk pf_spf pf_md pf_mxd pf_fl].
split; [rewrite lupd_length; exact LEN32|]. split; [exact D32|]. split; [lia|]. split; [reflexivity|].
split; [unfold tok_cells, tok_cells_g; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd]; exact TOK|].
split; [exact PB3|]. split; [exact Hpb|]. split; [exact TSK3 | unfold pe_frame; exact FR].
+ rewrite app_nil_r. cbn [app pf_mxd] in BASE3. eapply (PE_BASE_perm HIx); [exact BASE3|].
unfold pe_blocks, tstate_blocks, ts0. cbn [t_pbs t_objbs t_levels pf_tk pf_md pf_mxd pf_fl].
fold l1. rewrite (map_lupd_same lvl_blocks levels depth l1 l Hl) by (rewrite LB0l; reflexivity). apply Permutation_refl.
+ cbn [t_levels t_depth pf_mxd]. intros i li Hli.
destruct (Nat.eq_dec i depth) as [-> | NE].
* rewrite nth_error_lupd_eq in Hli by lia. injection Hli as <-. split; [subst l1; cbn; unfold ST_eatws, ST_ofs, ST_array; lia|]. split; [cbn; split; reflexivity|]. split; [left; cbn; split; reflexivity|]. intros; lia.
* rewrite nth_error_lupd_neq in Hli by congruence. apply lvl_cur_weak. exact (LV3 i li Hli NE).
-
assert (HrR : 0 < r < 2^64).
{ destruct J2 as (pbx & PBS & REST & ENB & _ & tx & TBS & kvs & KBS & ER & _).
pose proof (heap_blk S4L HIx _ _ _ _ r 48 HP2 ltac:(apply in_or_app; left; rewrite ENB, ER; apply in_or_app; left; left; reflexivity)) as (_ & _ & H0 & Hhi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hhi. lia. }
bst. if_truex.
set (l' := TL ST_eatws ST_array r (Some (Sarr [])) NB 0 []).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (TSK3 : tstack rsegs mc q (lupd levels depth l'))
by (rewrite <- (lupd_lupd _ levels depth l1); subst bse;
eapply (tstack_put rsegs mp mc q (lupd levels depth l1) depth _ []);
[exact TSK1 | rewrite lupd_length; lia | exact MU | exact WM | intros; exact I | unfold srec_cells, l'; cbn [tl_st tl_ss tl_cur tl_name pf_mxd]; exact Ld])
end.
apply evt_RZ_done. eapply (Kbreak _ md2 A2 r NB errv2); [exact Hr | | exact FS2 | exact FRM2].
split.
+ unfold PE_CORE. cbn [t_levels t_depth t_co t_pb t_pbs t_x t_obj ts_choff pf_len pf_tk pf_spf pf_md pf_mxd pf_fl].
split; [rewrite lupd_length; exact LEN32|]. split; [exact D32|]. split; [lia|]. split; [reflexivity|].
split; [unfold tok_cells, tok_cells_g; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd]; exact TOK|].
split; [exact PB3|]. split; [exact Hpb|]. split; [exact TSK3 | unfold pe_frame; exact FR].
+ apply (PE_REST_of_base HIx).
* eapply (PE_BASE_perm HIx); [exact BASE3|].
unfold pe_blocks, tstate_blocks, ts0. cbn [t_pbs t_objbs t_levels pf_tk pf_md pf_mxd pf_fl]. rewrite <- !app_assoc.
apply (Permutation_trans (l' := pbs ++ (objbs ++ (NB ++ (concat (map lvl_blocks levels) ++ (tk, 72) :: (q, (32 * mxd)) :: LB0))))).
-- apply (Permutation_trans (l' := pbs ++ (NB ++ (objbs ++ (concat (map lvl_blocks levels) ++ (tk, 72) :: (q, (32 * mxd)) :: LB0))))); [apply Permutation_app_swap_app|].
apply Permutation_app_head. apply Permutation_app_swap_app.
-- apply Permutation_app_head. apply Permutation_app_head. rewrite (app_assoc NB). apply Permutation_app_tail. fold l'.
replace (NB ++ concat (map lvl_blocks levels)) with (lvl_blocks l' ++ concat (map lvl_blocks levels)) by (unfold lvl_blocks, l'; cbn; rewrite app_nil_r; reflexivity).
apply (concat_lupd_fill levels depth l); [exact Hl | exact LB0l].
* cbn [t_levels t_depth pf_mxd]. intros i li Hli.
destruct (Nat.eq_dec i depth) as [-> | NE].
-- rewrite nth_error_lupd_eq in Hli by lia. injection Hli as <-.
split; [cbn; unfold ST_eatws; lia|]. split; [cbn; unfold ST_array; lia|]. split.
{ cbn [tl_cs tl_cbs tl_cur l' jopt pf_mxd]. split; [exact Hr|]. eapply jval_agree; [exact J2 | exact AGN | apply incl_refl]. }
rewrite Nat.ltb_irrefl, Nat.eqb_refl. exists CArr, false. split; [reflexivity|]. split; [exact I|]. cbn. split; reflexivity.
-- rewrite nth_error_lupd_neq in Hli by congruence. exact (LV3 i li Hli NE).
* revert OBJ. unfold cur_st, ts0. cbn [t_levels t_depth t_objs t_objbs t_obj pf_mxd]. rewrite nth_error_lupd_eq by lia. rewrite Hl, Hst. cbn. intros E; exact E.
Qed.
End PeStartC.

End RC__1.
End Mq6.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UC8c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UC8c.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UT7i.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UT7i. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UD4E.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UD4E.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U4l4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U4l4.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QVbl QRUw.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Import Tk2Gen.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section JoNewStringLen.
Variable HIx : heap_iface S4L.
Notation HEAPx := (HEAP S4L HIx).

Definition json_object_new_string_len_entry : Z := 0x264f4.

#[using="Type"] Lemma memcpy_specZ :
forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (D S n : Z) (src junk : list byte),
0 <= D < 2^64 -> D + n <= 2^64 -> 0 <= S < 2^64 -> S + n <= 2^64 -> 0 <= n < 2^63 ->
bytes_at rsegs m S src -> length src = Z.to_nat n ->
rw_cells rsegs m D [CB (Z.to_nat n) junk] ->
(S + n <= D \/ D + n <= S) ->
mem_inv rsegs m ->
evt rsegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 D) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [(D, D + n)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ rw_cells rsegs m' D [CB (Z.to_nat n) src] /\ bytes_at rsegs m' S src)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 S) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x5f438) fc None m (seg_rom rsegs)).
Proof.
intros until junk. intros HD HDn HS HSn Hn SRC L DST SEP MI.
pose proof (QVbl.Mq3.memcpy_spec rsegs 0x5f438 ltac:(StepGen.code_at_vm) ltac:(unfold StepGen.gw_b4; reflexivity) ltac:(unfold StepGen.gw_br; vm_compute; split; discriminate)
ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 S) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m src junk) as X.
rewrite Z.add_0_r in X. unfold QVbl.Mq3.memcpy_post in X. rewrite !(unsigned_lit D), !(unsigned_lit S), !(unsigned_lit n) in X by lia.
eapply evt_mono; [eapply X; [exact SRC | exact L | exact DST | exact SEP | exact MI] |].
intros ms' P. exact P.
Qed.

Definition new_str_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : Model) (LB : list blk) (len lo : Z)
(ms' : machine_state) (md' : Model) : Prop :=
exists m' (A' : AS S4L HIx) (r : Z) (errv' : word),
ret_statew S4L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' /\
model_vm_only md md' /\
stk rsegs m' lo (bv_unsigned sp) /\
heap_pres S4L LB (bv_unsigned sp) m m' /\
rw_cells rsegs m' (0x77c00 - 164) [C4 errv'] /\
( (r = 0 /\ HEAPx A' LB m' md')
\/ (r <> 0 /\ jval rsegs S4F (Sstr false) m' [(r, str_objsize len)] r 1 /\ HEAPx A' ((r, str_objsize len) :: LB) m' md') ).

#[using="Type"] Lemma json_object_new_string_len_cps :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (T : TSet)
(A : AS S4L HIx) (LB : list blk) (s len lo : Z) (src : list byte) (errv : word),
HEAPx A LB m md ->
bytes_at rsegs m s src -> Z.of_nat (length src) = len -> src_cls LB len (bv_unsigned sp) s src ->
0 <= s -> s + len < 2^64 -> 0 <= len < 2^31 ->
stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 48 - 8256 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hi_top S4L HIx ->
rw_cells rsegs m (0x77c00 - 164) [C4 errv] ->
tp = Z_to_bv 64 0x77c00 -> bv_unsigned ra mod 2 = 0 ->
a0 = Z_to_bv 64 s -> a1 = Z_to_bv 64 len ->
(forall ms' md', new_str_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB len lo ms' md' ->
realizes rsegs (mkCfg ms' md') T) ->
realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 json_object_new_string_len_entry) fc None m (seg_rom rsegs)) md) T.
Proof.
intros until errv. intros HP SRC SRCL SCL Hs0 Hsn Hlen ST LO LOS SPA HT ERR TP RA A0 A1 K.
unfold_consts. word_range sp SPR.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (heap_pres_refl S4L LB (bv_unsigned sp) m) as HPR.
pose proof (wmono_refl rsegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU.
subst a0 a1 tp.
assert (SRCk : True -> bytes_at rsegs m s src) by (intros _; exact SRC). clear SRC.
apply rz_evt; [exact MOK|]. unfold json_object_new_string_len_entry.
carve_frame 48%nat ST.
do 6 step.
step. if_falsex.
do 4 step.
step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mcur _) =>
assert (CALL : forall x10 : word, x10 = Z_to_bv 64 (Z.max len 8) ->
evt rsegs (RZ rsegs md T)
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp (Z_to_bv 64 490496) t0 t1 t2 (Z_to_bv 64 len) (Z_to_bv 64 s)
x10 (Z_to_bv 64 8) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x26528) fc None mcur (seg_rom rsegs)))
end.
2:{ destruct (Z.lt_ge_cases 8 len) as [Hb|Hs].
- if_truex. apply CALL. f_equal. lia.
- if_falsex. step. apply CALL. f_equal. lia. }
intros x10 ->. step.
replace (Z.max len 8 + 49) with (str_objsize len) by (unfold str_objsize; lia).
step.

alloc_call (hi_malloc S4L HIx) S4L HIx HP MU WM MI.
{ unfold str_objsize. lia. }
intros ms2 m2 md2 A2 r e2 RS VM2 ST2 HPR2 ERR2 OUT2. open_ret RS. cbn [hl_segs S4L] in *.
extend_pres S4L HIx HPR MU WM HP HPR2.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
clear MU WM MI ST.
destruct OUT2 as [(-> & _ & HP2) | (Hr & [junk0 BLK] & HP2)].
-
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2.
pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI. cbn [hl_segs S4L] in MI.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m2) as MU.
pose proof (wmono_refl rsegs m2) as WM.
reenter MOK2.
step. if_truex. do 7 step.
apply evt_RZ_done. apply K. unfold new_str_post.
exists m2, A2, 0, e2.
split; [| split; [exact VM2 | split; [| split; [exact HPR | split; [exact ERR2 | left; auto]]]]].
+ apply ret_statew_same.
+ release_frame FR ST2 (bv_unsigned sp). exact ST2.
-
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2.
pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI. cbn [hl_segs S4L] in MI.
pose proof (heap_blk S4L HIx _ _ _ _ r _ HP2 ltac:(left; reflexivity)) as (_ & Hal & Hlo & Hhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ r _ HP2 ltac:(left; reflexivity)) as Himg_r. cbn [hl_img_lo hl_img_hi S4L] in Himg_r.
unfold alloc_ceiling, sp_window_lo, stack_max_size, str_objsize in Hhi.
assert (SRC2 : bytes_at rsegs m2 s src).
{ eapply (src_cls_transport LB len (bv_unsigned sp) (bv_unsigned sp) LB);
[exact SCL | exact SRCL | exact (SRCk I) | exact HPR | lia | intros x Hx; exact Hx | exact MI | lia | lia]. }

pose proof (src_cls_fresh_sep HIx _ _ _ _ _ _ _ _ _ _ HP2 SCL SRCL ltac:(lia) ltac:(lia) ltac:(unfold_consts; lia)) as SEP.

assert (LENJ : length junk0 = Z.to_nat (str_objsize len)) by (destruct BLK as [[[Hwf _] _] _]; exact Hwf).
destruct (rw_cells_CB_cut rsegs _ _ _ _ 48%nat BLK ltac:(unfold str_objsize; lia)) as [HDR REST0].
destruct (rw_cells_CB_cut rsegs _ _ _ _ (Z.to_nat len) REST0 ltac:(unfold str_objsize; lia)) as [DATA REST1].
destruct (rw_cells_CB_cut rsegs _ _ _ _ 1%nat REST1 ltac:(unfold str_objsize; lia)) as [NUL REST2].
clear BLK REST0 REST1.
replace (r + Z.of_nat 48) with (r + 48) in DATA, NUL, REST2 by lia.
replace (r + 48 + Z.of_nat (Z.to_nat len)) with (r + 48 + len) in NUL, REST2 by lia.
replace (r + 48 + len + Z.of_nat 1) with (r + 48 + len + 1) in REST2 by lia.
assert (SRCh : True -> bytes_at rsegs m2 s src) by (intros _; exact SRC2). clear SRC2.
unfold str_objsize in *.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (r, r + (49 + Z.max len 8))] m2) as MU.
pose proof (wmono_refl rsegs m2) as WM.
reenter MOK2.
step. if_falsex.
step. step. ubsan_align Hal.
step. step. stepz. stepz. step. step. step. stepz. stepz. stepz. stepz.
step. step. step. step. step. step.

pose proof (src_cls_where _ _ _ _ _ SCL SRCL ltac:(lia) ltac:(lia) HIx _ _ _ _ HP ltac:(auto)) as WHERE.
assert (SRC3 : bytes_at rsegs m3 s src).
{ destruct (Z.eq_dec len 0) as [L0|LN].
- assert (src = []) as -> by (destruct src; [reflexivity| cbn in SRCL; lia]). apply bytes_at_nil. lia.
- eapply (bytes_at_transport rsegs); [exact (SRCh I) | exact MU |]. cbn. rewrite SRCL. unfold_consts. lia. }
call memcpy_specZ; [lia | lia | lia | lia | lia | exact SRC3 | lia | exact DATA | lia | assumption |].
step. step. rewrite (unsigned_lit (r + 48)) by lia. rewrite QRUw.lxor_ones64 by lia. if_falsex.
step.
replace (r + 48 + len) with (r + 48 + len) in NUL by lia.
set (ez := r + 48 + len) in *.
stepz.
subst ez.
step. step.
do 7 step.
apply evt_RZ_done. apply K. unfold new_str_post.
match goal with |- context [MS _ _ _ _ _ ?mf _] => exists mf, A2, r, e2 end.
split; [| split; [exact VM2 | split; [| split; [ | split; [exact ERR2 | right]]]]].
+ apply ret_statew_same.
+ release_frame FR ST2 (bv_unsigned sp). exact ST2.
+ eapply heap_pres_trans; [exact HPR|].
eapply (heap_pres_of_munch S4L LB (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outside S4L HIx); [exact HP2 | intros b Hb; right; exact Hb | clia |].
solve_clientW S4L HIx HP2.
+ split; [exact Hr|]. split.
*
jhdr_split HDR.
cbn [jval]. exists 0, [], [(r, str_objsize len)]. split; [reflexivity|]. split; [left; split; reflexivity|].
exists len, src. eexists. split; [reflexivity|]. split; [lia|]. split; [lia|].
unfold jhdr_cells. cbn [fn_str_to_json_string S4F app].
apply (rw_cells_recast rsegs _ _ _ [CB 1 [Z_to_bv 8 0]]) in NUL; [| cbn; auto | reflexivity | reflexivity].
pose proof (rw_cells_CB_join rsegs _ _ _ _ _ _ PC ltac:(replace (r + 48 + Z.of_nat (Z.to_nat len)) with (r + 48 + len) by lia; exact NUL)) as J1.
pose proof (rw_cells_CB_join rsegs _ _ _ _ _ _ J1 ltac:(replace (r + 48 + Z.of_nat (Z.to_nat len + 1)) with (r + 48 + len + 1) by lia; exact REST2)) as J2.
match type of J2 with rw_cells _ _ _ [CB ?k _] => replace k with (Z.to_nat (str_objsize len - 48)) in J2 by (unfold str_objsize; lia) end.
rewrite <- app_assoc in J2. cbn [app] in J2.
unfold JT_STRING.
match goal with |- rw_cells _ _ _ (?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?rest) =>
change (c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: rest) with ([c1; c2; c3; c4; c5; c6; c7] ++ rest) end.
apply (proj2 (rw_cells_app rsegs _ _ _ _)). split; [exact HDR|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ].
exact J2.
* eapply (heap_frame S4L HIx); [exact HP2 | | exact WM | assumption].
eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HP2 MU). solve_frameW.
Qed.

End JoNewStringLen.

End RC__1.
