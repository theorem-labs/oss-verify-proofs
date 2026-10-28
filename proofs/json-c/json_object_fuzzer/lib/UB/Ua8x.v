(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)

From Stdlib Require ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup UEQM Lib.GwApply QRjH QHnV QCcH QfLs Q0Ek Qtgi QjDH UC8c Qsw7 QJjn QkMG UG8z Udyh Uu4M UPZI UIsM Q6q3.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB.Top Require TopUbTac.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB.Tk1 Require Tk1Tac.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB.Tk3 Require Tk3Tac.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UhHQ.
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
Import UPZI.Mq4 UIsM.Mq5.
Import QJjn.Mq0.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.
Import Q6q3.
Import TopUbTac Tk1Tac Tk3Tac UhHQ.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section PeArray.
Variable HIx : heap_iface S4L.
Hypothesis PUT : put_stmt_P HIx.
Hypothesis SHRINK : jo_array_shrink_P HIx.

#[using="SHRINK"] Lemma seg_array_close :
forall (pf : pe_fix) (q : Z) (LB0 : list blk) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (ts : tstate) (l : tlevel) (kids : list (option jshape))
(cb : byte) (j1 j2 utf : list byte) (sv : pe_saved) (errv : word) (T : TSet)
(x1 gp t0 t1 t2 a0 a1 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC HIx pf lo ->
PE_INV HIx pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv ->
nth_error (t_levels ts) (t_depth ts) = Some l -> (tl_st l = ST_array \/ tl_st l = ST_array_after_sep) ->
tl_cs l = Some (Sarr kids) ->

(forall m' md' A' cbs' errv' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F' fc',
PE_INV HIx pf q LB0 payload me lo m' md' A'
(TST (t_depth ts) (lupd (t_levels ts) (t_depth ts) (TL ST_eatws ST_finish (tl_cur l) (tl_cs l) cbs' (tl_name l) (tl_nbs l)))
(t_co ts) (t_pb ts) (t_pbs ts) (t_x ts) (t_obj ts) (t_objs ts) (t_objbs ts))
cb j1 j2 utf sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_BREAK (t_co ts) x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F' fc' m') md') T) ->

(forall m' md' A' cbs' errv' x1' gp' t0' t1' t2' e a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F' fc',
PE_INV HIx pf q LB0 payload me lo m' md' A'
(TST (t_depth ts) (lupd (t_levels ts) (t_depth ts) (TL (tl_st l) (tl_ss l) (tl_cur l) (tl_cs l) cbs' (tl_name l) (tl_nbs l)))
(t_co ts) (t_pb ts) (t_pbs ts) (t_x ts) (t_obj ts) (t_objs ts) (t_objbs ts))
cb j1 j2 utf sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_ERR (t_co ts) x1' gp' t0' t1' t2' e a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F' fc' m') md') T) ->
realizes rsegs (mkCfg (pe_ms rsegs pf 0x22ff0 (t_co ts) x1 gp t0 t1 t2
a0 a1 (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) a3 a4 a5 a6 a7
s4 s6 s7 s8 s9 s10 t3 t4 t5 t6 F fc m) md) T.
Proof.
intros until fc. intros STC INV Hl Hst Hcs Kbreak Kerr4.
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
assert (Eobjbs : objbs = []).
{ revert OBJ. unfold cur_st. cbn [t_levels t_depth t_objbs pf_mxd]. rewrite Hl. destruct Hst as [E|E]; rewrite E; intros E'; exact E'. }
subst objbs.
assert (ST26' : 0 <= tl_st l <= 26) by (unfold ST_array, ST_array_after_sep in Hst; lia).
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
destruct Hst as [E|E]; rewrite E; unfold ST_array, ST_array_after_sep;
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
assert (Hbal : bse mod 16 = 0) by (rewrite Hbse; Z.div_mod_to_equations; lia).
assert (HbseR : q <= bse /\ bse + 32 <= q + (32 * mxd)) by (subst bse; lia).
stash PB. stash TSK. clear OBJ.
apply rz_evt; [exact MOK|]. replace (q + 32 * Z.of_nat depth) with bse by lia.
tk3_walk 0x26938 ltac:(try norm_sx32; try replace (q + Z.of_nat depth * 32) with bse by lia).

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
pose proof (tok_flags_byte_g mxd fl mp tk pb (Z.of_nat depth) q (TS isd stpos (Z_to_bv 64 co) err ucs high quote) ltac:(unfold tok_cells, tok_cells_g; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd]; exact TOK)) as RDF.
stash PB2. stash TSK. stash BASE2.
reenter MOK2.

lazymatch type of TOK with rw_cells _ _ _ ?tkc => lazymatch type of FR with rw_cells _ _ _ ?frc =>
assert (TAIL : forall mc (x1' t0' t1' t2' a0v a1v a2v a3v a4v a5v a6v a7v s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' : word),
rw_cells rsegs mc bse (srec_cells (TL ST_eatws ST_finish cur (tl_cs l) cbs' (tl_name l) (tl_nbs l))) ->
munch [(bse, bse + 32)] mp mc -> wmono rsegs mp mc -> mem_inv rsegs mc ->
rw_cells rsegs mc tk tkc -> rw_cells rsegs mc spf frc ->
realizes rsegs (mkCfg (MS (mkR x1' (Z_to_bv 64 spf) gp (Z_to_bv 64 490496) t0' t1' t2' (Z_to_bv 64 tk) (Z_to_bv 64 oldl)
a0v a1v a2v a3v a4v a5v a6v a7v
(Z_to_bv 64 newl) (Z_to_bv 64 lenr) s4' (Z_to_bv 64 (sb + co)) s6' s7' s8' s9' s10' (Z_to_bv 64 0x134c0) t3' t4' t5' t6')
F2 (Z_to_bv 64 PE_BREAK) fc2 None mc (seg_rom rsegs)) md2) T) end end.
{ intros mc x1' t0' t1' t2' a0v a1v a2v a3v a4v a5v a6v a7v s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' L5 MUc WMc MIc TOKc FRc.
clear MU WM MI TOK FR. rename MUc into MU. rename WMc into WM. rename MIc into MI. rename TOKc into TOK. rename FRc into FR.
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
lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mc _) _) _ =>
assert (TSK3 : tstack rsegs mc q (lupd levels depth l'))
by (subst bse; eapply (tstack_put rsegs mp _ q levels depth l' []);
[exact TSK | lia | exact MU | exact WM | intros; exact I | exact L5]);
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
eapply (Kbreak _ md2 A2 cbs' errv2); [ | exact FS2 | exact FRM2].
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
+ unfold cur_st. cbn [t_levels t_depth t_objbs pf_mxd]. rewrite nth_error_lupd_eq by lia. reflexivity. }

assert (ERR4 : forall (x1' t0' t1' t2' e a1v a2v a3v a4v a5v a6v a7v s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' : word),
realizes rsegs (mkCfg (MS (mkR x1' (Z_to_bv 64 spf) gp (Z_to_bv 64 490496) t0' t1' t2' (Z_to_bv 64 tk) (Z_to_bv 64 oldl)
e a1v a2v a3v a4v a5v a6v a7v
(Z_to_bv 64 newl) (Z_to_bv 64 lenr) s4' (Z_to_bv 64 (sb + co)) s6' s7' s8' s9' s10' (Z_to_bv 64 0x134c0) t3' t4' t5' t6')
F2 (Z_to_bv 64 PE_ERR) fc2 None mp (seg_rom rsegs)) md2) T).
{ intros x1' t0' t1' t2' e a1v a2v a3v a4v a5v a6v a7v s4' s6' s7' s8' s9' s10' t3' t4' t5' t6'.
unstash PB2. unstash TSK. unstash BASE2.
set (l' := TL (tl_st l) (tl_ss l) cur (tl_cs l) cbs' (tl_name l) (tl_nbs l)).
assert (TSK3 : tstack rsegs mp q (lupd levels depth l'))
by (subst bse; eapply (tstack_put rsegs mp _ q levels depth l' []);
[exact TSK | lia | apply munch_refl | apply wmono_refl | intros; exact I | unfold srec_cells, l'; cbn [tl_st tl_ss tl_cur tl_name pf_mxd]; rewrite Hn0; exact Ld]).
unfold PE_ERR. eapply (Kerr4 _ md2 A2 cbs' errv2); [ | exact FS2 | exact FRM2].
split.
- unfold PE_CORE. cbn [t_levels t_depth t_co t_pb t_pbs t_x t_obj ts_choff pf_len pf_tk pf_spf pf_md pf_mxd pf_fl].
split; [rewrite lupd_length; exact LEN32|]. split; [exact D32|]. split; [lia|]. split; [reflexivity|].
split; [unfold tok_cells, tok_cells_g; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd]; exact TOK|].
split; [exact PB2|]. split; [exact Hpb|]. split; [exact TSK3|]. unfold pe_frame. exact FR.
- apply (PE_REST_of_base HIx).
+ eapply (PE_BASE_perm HIx); [exact BASE2|].
unfold pe_blocks, tstate_blocks, LBput. cbn [t_pbs t_objbs t_levels pf_tk pf_md pf_mxd pf_fl]. rewrite app_nil_l.
unfold BL. rewrite (lupd_split levels depth l lvl_reset Hl). fold l'. rewrite (lupd_split levels depth l l' Hl).
replace (lvl_blocks l') with cbs' by (unfold lvl_blocks, l'; cbn; rewrite Hnbs0, app_nil_r; reflexivity).
cbn [lvl_blocks lvl_reset tl_cbs tl_nbs app pf_mxd]. rewrite <- !app_assoc.
apply (Permutation_trans (l' := pbs ++ (cbs' ++ (concat (map lvl_blocks (firstn depth levels)) ++ (concat (map lvl_blocks (skipn (S depth) levels)) ++ (tk, 72) :: (q, (32 * mxd)) :: LB0)))));
[apply Permutation_app_swap_app | apply Permutation_app_head; apply Permutation_app_swap_app].
+ cbn [t_levels t_depth pf_mxd]. intros i li Hli.
destruct (Nat.eq_dec i depth) as [-> | NE].
* rewrite nth_error_lupd_eq in Hli by lia. injection Hli as <-.
split; [cbn; exact ST26|]. split; [cbn; exact SS26|]. split; [cbn [tl_cs tl_cbs tl_cur l' pf_mxd]; rewrite Hcs; cbn [jopt pf_mxd]; split; [exact Hc | exact J2]|].
rewrite Nat.ltb_irrefl, Nat.eqb_refl. exists CArr, false. split; [exact Hmode|]. split; [cbn [tl_cs l']; rewrite Hcs; exact I|]. cbn. split; [exact Hn0 | exact Hnbs0].
* rewrite nth_error_lupd_neq in Hli by congruence.
eapply (lvl_cur_agree rsegs S4F); [exact (LV i li Hli) | exact AGL2 |].
intros b Hb. unfold BL. apply in_concat. exists (lvl_blocks li). split; [| exact Hb]. apply in_map.
eapply (nth_error_In _ i). rewrite nth_error_lupd_neq by congruence. exact Hli.
+ unfold cur_st. cbn [t_levels t_depth t_objbs pf_mxd]. rewrite nth_error_lupd_eq by lia. cbn [tl_st l'].
destruct Hst as [E | E]; rewrite E; reflexivity. }
assert (Ld8 : rw_cells rsegs mp bse [CB 8 (le4 (Z_to_bv 64 (tl_st l)) ++ le4 (Z_to_bv 64 (tl_ss l))); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 cur); C8 (Z_to_bv 64 0)])
by (eapply rw_cells_recast; [exact Ld | cbn; repeat split; reflexivity | reflexivity | reflexivity]).
clear Ld. rename Ld8 into Ld.
destruct Hst as [E | E].
- tk3_walk 0x23d14 ltac:(try norm_sx32; try rewrite E; try unfold ST_array, ST_array_after_sep; try replace (q + Z.of_nat depth * 32) with bse by lia).
apply evt_RZ_done. eapply TAIL; [ | exact MU | exact WM | exact MI | exact TOK | exact FR].
unfold srec_cells; cbn [tl_st tl_ss tl_cur tl_name pf_mxd]; rewrite ?Hn0.
lazymatch goal with Lx : rw_cells rsegs ?mm bse (C8 ?v :: ?rest) |- _ =>
apply (proj1 (rw_cells_app rsegs mm bse [C8 v] rest)) in Lx as [Lx1 Lx2];
apply (proj2 (rw_cells_app rsegs mm bse [C4 (Z_to_bv 64 ST_eatws); C4 (Z_to_bv 64 ST_finish)] rest)); split;
[ eapply rw_cells_recast; [exact Lx1 | cbn; repeat split; reflexivity | vm_compute; repeat (match goal with |- (_ :: _) = (_ :: _) => apply f_equal2 end); try reflexivity; apply bv_eq; reflexivity | reflexivity]
| exact Lx2 ] end.
- destruct (land1_cases fl) as [F1 | F1].
+ tk3_walk 0x23d14 ltac:(try norm_sx32; try rewrite E; try unfold ST_array, ST_array_after_sep; try replace (q + Z.of_nat depth * 32) with bse by lia; try rewrite (zxb_byte fl) by lia; try rewrite (unsigned_lit (fl mod 256)) by (pose proof (Z.mod_pos_bound fl 256 ltac:(lia)); lia); try rewrite (land_mod256 fl 1) by lia; try rewrite F1).
apply evt_RZ_done. eapply TAIL; [ | exact MU | exact WM | exact MI | exact TOK | exact FR].
unfold srec_cells; cbn [tl_st tl_ss tl_cur tl_name pf_mxd]; rewrite ?Hn0.
lazymatch goal with Lx : rw_cells rsegs ?mm bse (C8 ?v :: ?rest) |- _ =>
apply (proj1 (rw_cells_app rsegs mm bse [C8 v] rest)) in Lx as [Lx1 Lx2];
apply (proj2 (rw_cells_app rsegs mm bse [C4 (Z_to_bv 64 ST_eatws); C4 (Z_to_bv 64 ST_finish)] rest)); split;
[ eapply rw_cells_recast; [exact Lx1 | cbn; repeat split; reflexivity | vm_compute; repeat (match goal with |- (_ :: _) = (_ :: _) => apply f_equal2 end); try reflexivity; apply bv_eq; reflexivity | reflexivity]
| exact Lx2 ] end.
+ tk3_walk 0x23ea4 ltac:(try norm_sx32; try rewrite E; try unfold ST_array, ST_array_after_sep; try replace (q + Z.of_nat depth * 32) with bse by lia; try rewrite (zxb_byte fl) by lia; try rewrite (unsigned_lit (fl mod 256)) by (pose proof (Z.mod_pos_bound fl 256 ltac:(lia)); lia); try rewrite (land_mod256 fl 1) by lia; try rewrite F1).
apply evt_RZ_done. eapply ERR4.
Qed.

#[using="PUT SHRINK"] Lemma seg_array :
forall (pf : pe_fix) (q : Z) (LB0 : list blk) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (ts : tstate) (l : tlevel)
(cb : byte) (j1 j2 utf : list byte) (sv : pe_saved) (errv : word) (T : TSet)
(x1 gp t0 t1 t2 a3 a4 a5 a6 a7 s6 s7 s8 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC HIx pf lo ->
PE_INV HIx pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv ->
nth_error (t_levels ts) (t_depth ts) = Some l -> (tl_st l = ST_array \/ tl_st l = ST_array_after_sep) ->

(forall m' md' A' cbs' errv' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F' fc',
bv_unsigned cb = 93 ->
PE_INV HIx pf q LB0 payload me lo m' md' A'
(TST (t_depth ts) (lupd (t_levels ts) (t_depth ts) (TL ST_eatws ST_finish (tl_cur l) (tl_cs l) cbs' (tl_name l) (tl_nbs l)))
(t_co ts) (t_pb ts) (t_pbs ts) (t_x ts) (t_obj ts) (t_objs ts) (t_objbs ts))
cb j1 j2 utf sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_BREAK (t_co ts) x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F' fc' m') md') T) ->

(forall m' md' A' errv' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F' fc',
bv_unsigned cb <> 93 -> (S (t_depth ts) < Z.to_nat (pf_mxd pf))%nat ->
PE_INV HIx pf q LB0 payload me lo m' md' A'
(TST (S (t_depth ts)) (lupd (lupd (t_levels ts) (t_depth ts) (TL ST_array_add (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)))
(S (t_depth ts)) lvl_reset)
(t_co ts) (t_pb ts) (t_pbs ts) (t_x ts) (t_obj ts) (t_objs ts) (t_objbs ts))
cb j1 j2 utf sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_REDO (t_co ts) x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F' fc' m') md') T) ->

(forall x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6', bv_unsigned cb <> 93 -> (Z.to_nat (pf_mxd pf) <= S (t_depth ts))%nat  ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_ERR (t_co ts) x1' gp' t0' t1' t2' (Z_to_bv 64 2)
a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F fc m) md) T) ->

(forall m' md' A' cbs' errv' x1' gp' t0' t1' t2' e a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F' fc',
bv_unsigned cb = 93 ->
PE_INV HIx pf q LB0 payload me lo m' md' A'
(TST (t_depth ts) (lupd (t_levels ts) (t_depth ts) (TL (tl_st l) (tl_ss l) (tl_cur l) (tl_cs l) cbs' (tl_name l) (tl_nbs l)))
(t_co ts) (t_pb ts) (t_pbs ts) (t_x ts) (t_obj ts) (t_objs ts) (t_objbs ts))
cb j1 j2 utf sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_ERR (t_co ts) x1' gp' t0' t1' t2' e a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F' fc' m') md') T) ->
realizes rsegs (mkCfg (pe_ms rsegs pf (pe_jt (tl_st l)) (t_co ts) x1 gp t0 t1 t2
(Z_to_bv 64 0) (Z_to_bv 64 (tl_st l)) (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) a3 a4 a5 a6 a7
(Z_to_bv 64 q) s6 s7 s8 (Z_to_bv 64 (Z.of_nat (t_depth ts))) s10 t3 t4 t5 t6 F fc m) md) T.
Proof.
intros until fc. intros STC INV Hl Hst Kbreak Kredo Kerr Kerr4.
pose proof INV as INV0.
pose proof STC as (LO & LOS & SPA & HT & SP0 & LEN & SB0 & SBL).
destruct INV as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof REST as (HP & LV & _).
assert (PCE : pe_jt (tl_st l) = 0x21e88) by (destruct Hst as [E|E]; rewrite E; reflexivity). rewrite PCE.
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl_]; pe_gen fl_; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
unfold tok_cells, tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in TOK. unfold pe_frame in FR. unfold pe_ms in *. cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
unfold_consts.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (LV depth l Hl) as LVd. pose proof LVd as (ST26 & SS26 & JO & Md).
rewrite Nat.ltb_irrefl, Nat.eqb_refl in Md. destruct Md as (c0 & hn0 & Hmode & CLS0 & NM0).
assert (Ehn : c0 = CArr /\ hn0 = false).
{ revert Hmode. unfold lvl_mode. cbn -[zin andb].
cbn [zin existsb Z.eqb ws_states val_states esc_states app ST_eatws ST_start ST_finish ST_null ST_comment_start ST_comment ST_comment_eol ST_comment_end
ST_string ST_string_escape ST_escape_unicode ST_esc_need_escape ST_esc_need_u ST_boolean ST_number ST_array ST_array_add ST_array_sep
ST_ofs ST_ofield ST_ofend ST_ovalue ST_ovadd ST_osep ST_array_after_sep ST_ofs_after_sep ST_inf andb orb pf_mxd].
assert (CASES : exists k : nat, (k <= 26)%nat /\ tl_ss l = Z.of_nat k) by (exists (Z.to_nat (tl_ss l)); split; lia).
destruct CASES as (k & Hk & Ek). rewrite Ek.
destruct Hst as [E|E]; rewrite E; unfold ST_array, ST_array_after_sep;
do 27 (destruct k as [|k]; [cbn; intros EE; first [discriminate EE | injection EE as <- <-; split; reflexivity] |]); exfalso; lia. }
destruct Ehn as [-> ->].
pose proof (bv_unsigned_in_range 8 cb) as CBR; unfold bv_modulus in CBR; cbn in CBR.
clear PB TSK REST LV.
apply rz_evt; [exact MOK|].
destruct (Z.eq_dec (bv_unsigned cb) 93) as [C93 | N93].
- tk3_walk 0x22ff0 ltac:(try norm_sx32; try norm_w32; try unfold zxb; try rewrite (unsigned_lit (bv_unsigned cb)) by lia). apply evt_RZ_done.
destruct (tl_cs l) as [[| | | |okids|kids]|] eqn:Ecs; try (exfalso; exact CLS0).
eapply (seg_array_close (PEF tk oldl newl len lenr sb spf pmd mxd fl)) with (ts := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) (l := l);
[exact STC | exact INV0 | exact Hl | exact Hst | exact Ecs | |].
+ cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd]. intros until fc'. intros INV' FS' FRM'. rewrite Ecs in INV'. eapply Kbreak; eauto.
+ cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd]. intros until fc'. intros INV' FS' FRM'. rewrite Ecs in INV'. eapply Kerr4; eauto.
- destruct (Nat.lt_ge_cases (S depth) (Z.to_nat mxd)) as [Dlt | Dge].
+ tk3_walk 0x21e00 ltac:(try norm_sx32; try norm_w32; try unfold zxb; try rewrite (unsigned_lit (bv_unsigned cb)) by lia). apply evt_RZ_done.
eapply (seg_push HIx PUT (PEF tk oldl newl len lenr sb spf pmd mxd fl)) with (ts := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) (l := l);
[exact STC | exact INV0 | exact Hl | cbn [t_depth pf_mxd]; lia | destruct Hst as [E|E]; rewrite E; reflexivity | left; split; [reflexivity | split; [exact CLS0 | exact NM0]] |].
cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd]. intros. eapply Kredo; eauto; lia.
+ tk3_walk 0x23ea4 ltac:(try norm_sx32; try norm_w32; try unfold zxb; try rewrite (unsigned_lit (bv_unsigned cb)) by lia). apply evt_RZ_done. eapply Kerr; [exact N93 | lia].
Qed.

#[using="PUT"] Lemma seg_oval :
forall (pf : pe_fix) (q : Z) (LB0 : list blk) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (ts : tstate) (l : tlevel)
(cb : byte) (j1 j2 utf : list byte) (sv : pe_saved) (errv : word) (T : TSet)
(x1 gp t0 t1 t2 a0 a3 a4 a5 a6 a7 s6 s7 s8 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC HIx pf lo ->
PE_INV HIx pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_ovalue ->

(forall m' md' A' errv' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F' fc',
(S (t_depth ts) < Z.to_nat (pf_mxd pf))%nat ->
PE_INV HIx pf q LB0 payload me lo m' md' A'
(TST (S (t_depth ts)) (lupd (lupd (t_levels ts) (t_depth ts) (TL ST_ovadd (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)))
(S (t_depth ts)) lvl_reset)
(t_co ts) (t_pb ts) (t_pbs ts) (t_x ts) (t_obj ts) (t_objs ts) (t_objbs ts))
cb j1 j2 utf sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_REDO (t_co ts) x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F' fc' m') md') T) ->

(forall x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6', (Z.to_nat (pf_mxd pf) <= S (t_depth ts))%nat  ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_ERR (t_co ts) x1' gp' t0' t1' t2' (Z_to_bv 64 2)
a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F fc m) md) T) ->
realizes rsegs (mkCfg (pe_ms rsegs pf (pe_jt ST_ovalue) (t_co ts) x1 gp t0 t1 t2
a0 (Z_to_bv 64 (tl_st l)) (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) a3 a4 a5 a6 a7
(Z_to_bv 64 q) s6 s7 s8 (Z_to_bv 64 (Z.of_nat (t_depth ts))) s10 t3 t4 t5 t6 F fc m) md) T.
Proof.
intros until fc. intros STC INV Hl Hst Kredo Kerr.
pose proof INV as INV0.
pose proof STC as (LO & LOS & SPA & HT & SP0 & LEN & SB0 & SBL).
destruct INV as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof REST as (HP & LV & _).
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl_]; pe_gen fl_; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
unfold tok_cells, tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in TOK. unfold pe_frame in FR. unfold pe_ms in *. cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
unfold_consts.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (LV depth l Hl) as LVd. pose proof LVd as (ST26 & SS26 & JO & Md).
rewrite Nat.ltb_irrefl, Nat.eqb_refl in Md. destruct Md as (c0 & hn0 & Hmode & CLS0 & NM0).
assert (Ehn : c0 = CObj /\ hn0 = true).
{ revert Hmode. rewrite Hst. unfold lvl_mode. cbn -[zin andb].
cbn [zin existsb Z.eqb ws_states val_states esc_states app ST_eatws ST_start ST_finish ST_null ST_comment_start ST_comment ST_comment_eol ST_comment_end
ST_string ST_string_escape ST_escape_unicode ST_esc_need_escape ST_esc_need_u ST_boolean ST_number ST_array ST_array_add ST_array_sep
ST_ofs ST_ofield ST_ofend ST_ovalue ST_ovadd ST_osep ST_array_after_sep ST_ofs_after_sep ST_inf andb orb pf_mxd].
assert (CASES : exists k : nat, (k <= 26)%nat /\ tl_ss l = Z.of_nat k) by (exists (Z.to_nat (tl_ss l)); split; lia).
destruct CASES as (k & Hk & Ek). rewrite Ek. unfold ST_ovalue.
do 27 (destruct k as [|k]; [cbn; intros EE; first [discriminate EE | injection EE as <- <-; split; reflexivity] |]); exfalso; lia. }
destruct Ehn as [-> ->].
clear PB TSK REST LV.
apply rz_evt; [exact MOK|]. rewrite Hst. unfold ST_ovalue. cbn [pe_jt pf_mxd].
destruct (Nat.lt_ge_cases (S depth) (Z.to_nat mxd)) as [Dlt | Dge].
- tk3_walk 0x21e00 ltac:(try norm_sx32; try norm_w32). apply evt_RZ_done.
eapply (seg_push HIx PUT (PEF tk oldl newl len lenr sb spf pmd mxd fl)) with (ts := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) (l := l);
[exact STC | exact INV0 | exact Hl | cbn [t_depth pf_mxd]; lia | rewrite Hst; reflexivity | right; split; [reflexivity | split; [exact CLS0 | exact NM0]] |].
cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd]. intros. eapply Kredo; eauto; lia.
- tk3_walk 0x23ea4 ltac:(try norm_sx32; try norm_w32). apply evt_RZ_done. eapply Kerr. lia.
Qed.

End PeArray.

End RC__1.
End Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UBpZ UT7i Uv6q UzWc.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB.Tk1 Require Tk1Tac.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB.Tk3 Require Tk3Tac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

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
Import UG8z UIsM.Mq2.
Import UBpZ UT7i Uv6q.
Import UzWc.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.
Import Q6q3.
Import TopUbTac Tk1Tac Tk3Tac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.


Section PeCend.
Variable HIx : heap_iface S4L.
Hypothesis MEMMOVE : memmove_stmt.

#[using="MEMMOVE"] Lemma seg_cend :
forall (pf : pe_fix) (q : Z) (LB0 : list blk) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (ts : tstate) (l : tlevel)
(cb : byte) (j1 j2 utf : list byte) (sv : pe_saved) (errv : word) (T : TSet)
(x1 gp t0 t1 t2 a0 a3 a4 a5 a6 a7 s6 s7 s8 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC HIx pf lo ->
PE_INV HIx pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_comment_end ->
t_co ts < pf_len pf ->

(forall m' md' A' st' pbs' errv' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F' fc',
(bv_unsigned cb = 47 /\ st' = ST_eatws) \/ (bv_unsigned cb <> 47 /\ st' = ST_comment) ->
PE_INV HIx pf q LB0 payload me lo m' md' A' (ts_set_pbs (ts_set_level ts (TL st' (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) pbs') cb j1 j2 utf sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_BREAK (t_co ts) x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F' fc' m') md') T) ->

(forall m' md' A' pbs' errv' x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F' fc',
PE_INV HIx pf q LB0 payload me lo m' md' A' (ts_set_pbs ts pbs') cb j1 j2 utf sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_ERR (t_co ts) x1' gp' t0' t1' t2' (Z_to_bv 64 16) a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F' fc' m') md') T) ->
realizes rsegs (mkCfg (pe_ms rsegs pf (pe_jt ST_comment_end) (t_co ts) x1 gp t0 t1 t2
a0 (Z_to_bv 64 (tl_st l)) (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) a3 a4 a5 a6 a7
(Z_to_bv 64 q) s6 s7 s8 (Z_to_bv 64 (Z.of_nat (t_depth ts))) s10 t3 t4 t5 t6 F fc m) md) T.
Proof.
intros until fc. intros STC INV Hl Hst Hco Kbreak Kerr16.
pose proof STC as (LO & LOS & SPA & HT & SP0 & LEN & SB0 & SBL).
destruct INV as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof REST as (HP & LV & _).
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl_]; pe_gen fl_; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
unfold tok_cells, tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in TOK. unfold pe_frame in FR. unfold pe_ms in *. cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
unfold_consts.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocks; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, (32 * mxd)) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocks; apply in_or_app; right; right; left; reflexivity).
pose proof (heap_blk S4L HIx _ _ _ _ tk 72 HP INtk) as (_ & Htal & Htlo & Hthi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ tk 72 HP INtk) as Himg_t. cbn [hl_img_lo hl_img_hi S4L pf_mxd] in Himg_t.
pose proof (heap_blk S4L HIx _ _ _ _ q (32 * mxd) HP INq) as (_ & Hqal & Hqlo & Hqhi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hthi, Hqhi.
assert (Htq : tk <> q).
{ pose proof (heap_blk_nodup S4L HIx _ _ _ _ HP) as ND. unfold pe_blocks in ND. rewrite map_app in ND. apply NoDup_app_remove_l in ND.
cbn [map blk_addr fst pf_mxd] in ND. apply List.NoDup_cons_iff in ND as [Hni _]. intros E. apply Hni. left. symmetry. exact E. }
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ tk 72 q (32 * mxd) HP INtk INq Htq) as Hdtq.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L pf_mxd] in MI.
pose proof (LV depth l Hl) as LVd. pose proof LVd as (ST26 & SS26 & _ & Md).
rewrite Nat.ltb_irrefl, Nat.eqb_refl in Md. destruct Md as (c0 & hn0 & Hmode & CLS0 & NM0).
pose proof (bv_unsigned_in_range 8 cb) as CBR; unfold bv_modulus in CBR; cbn in CBR.
stash TSK. stash Himg_t. clear LV.
apply rz_evt; [exact MOK|]. rewrite Hst. unfold ST_comment_end. cbn [pe_jt pf_mxd].
tk3_walk 0x241a4 idtac.

pose proof PB as (buf & bpos & cap & pre & post & Epbs & Lpre & CORE1).
pose proof HP as HP1. unfold pe_blocks, tstate_blocks, ts0 in HP1. cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_tk pf_md pf_mxd pf_fl] in HP1.
rewrite Epbs in HP1. cbn [app pf_mxd] in HP1.
pose proof (heap_blk S4L HIx _ _ _ _ buf cap HP1 ltac:(right; left; reflexivity)) as (_ & _ & _ & Hbufhi & _). unfold alloc_ceiling, sp_window_lo, stack_max_size in Hbufhi.
pose proof (pe_frame_cbyte m spf obj cb j1 j2 utf sv FR) as SRC.
pose proof REST as (_ & _ & _ & ST1 & ERR1 & _).
apply evt_RZ_done.
eapply (memappend_cps HIx MEMMOVE) with (lo := lo) (b := spf + 31) (src := [cb]) (n := 1);
[ exact HP1 | exact CORE1 | lia | exact SRC | reflexivity | left; left; rewrite ?unsigned_lit by lia; lia | lia | lia | lia | .. ]; try alloc_side.
all: try (rewrite ?unsigned_lit by lia; first [exact ST1 | exact ERR1]).
all: try (rewrite ?unsigned_lit by lia; unfold PE_FRAME in *; clia).
intros ms2 md2 (m2 & A2 & r & errv2 & buf' & cap' & RS2 & VM2 & ST2 & HPR2 & ERR2 & HP2 & OUT2).
destruct RS2 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F2 & fc2 & -> & FS2 & FRM2).
cbn [hl_segs hl_tp S4L pf_mxd] in *. rewrite ?(unsigned_lit spf) in ST2 by lia. rewrite ?(unsigned_lit spf) in HPR2 by lia.

set (pbs2 := [(pb, 16); (buf', cap')]).
set (ts2 := TST depth levels co pb pbs2 (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs).
assert (INq2 : In (q, (32 * mxd)) ((objbs ++ concat (map lvl_blocks levels)) ++ (tk, 72) :: (q, (32 * mxd)) :: LB0))
by (apply in_or_app; right; right; left; reflexivity).
assert (INtk2 : In (tk, 72) ((objbs ++ concat (map lvl_blocks levels)) ++ (tk, 72) :: (q, (32 * mxd)) :: LB0))
by (apply in_or_app; right; left; reflexivity).
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. cbn [hl_segs S4L pf_mxd] in FR.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in TOK; [| eapply client_range_block; [exact INtk2 | lia | cbn; lia]]. cbn [hl_segs S4L pf_mxd] in TOK.
unstash TSK. apply (tstack_pres_g S4L _ _ _ _ _ _ HPR2 INq2) in TSK; [| exact LEN32].
assert (REST2 : PE_REST HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo m2 md2 A2 ts2 errv2).
{ eapply (PE_REST_call_pb HIx) with (ts := ts0) (LBc := (objbs ++ concat (map lvl_blocks levels)) ++ (tk, 72) :: (q, (32 * mxd)) :: LB0);
[exact STC | exact REST | exact VM2 | exact HPR2 | unfold ts0; cbn [t_objbs t_levels pf_mxd]; intros b Hb; apply in_or_app;
apply in_app_or in Hb; destruct Hb as [Hb|Hb]; [left; apply in_or_app; left; exact Hb | apply in_app_or in Hb; destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; exact Hb | right; right; right; exact Hb]]
| unfold pe_blocks, tstate_blocks; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_tk pf_md pf_mxd pf_fl]; exact HP2
| exact ST2 | exact ERR2]. }
assert (PBany : pbuf rsegs m2 pbs2 pb).
{ destruct OUT2 as [[_ PBS] | (_ & -> & -> & PC)]; [exact PBS|].
exists buf, bpos, cap, pre, post. split; [reflexivity|]. split; [exact Lpre | exact PC]. }
assert (INV2 : PE_INV HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo m2 md2 A2 ts2 cb j1 j2 utf sv errv2).
{ split; [| exact REST2]. unfold PE_CORE, ts2; cbn. split; [exact LEN32|]. split; [exact D32|]. split; [lia|]. split; [reflexivity|].
split; [exact TOK|]. split; [exact PBany|]. split; [exact Hpb|]. split; [exact TSK | exact FR]. }
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2.
pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI2. cbn [hl_segs S4L pf_mxd] in MI2.
clear HP1 HP2 REST CORE1 SRC ST1 ERR1 MI PBany PB HP MOK.
reenter MOK2.
destruct OUT2 as [[-> _] | (-> & -> & -> & _)].
2:{
replace (Z_to_bv 64 (2^64 - 1)) with (Z_to_bv 64 (-1)) by (apply bv_eq; vm_compute; reflexivity).
tk3_walk 0x23ea4 idtac. apply evt_RZ_done. eapply Kerr16; [| exact FS2 | exact FRM2].
unfold ts2, pbs2 in INV2. exact INV2. }

bstep. if_false.
pose proof (TSK depth l Hl) as Ld. cbn [hl_segs S4L pf_mxd] in Ld. unfold srec_cells in Ld.
remember (q + 32 * Z.of_nat depth) as bse eqn:Hbse in Ld.
assert (Hbal : bse mod 16 = 0) by (rewrite Hbse; Z.div_mod_to_equations; lia).
assert (HbseR : q <= bse /\ bse + 32 <= q + (32 * mxd)) by (subst bse; lia).
pose proof (munch_refl [(bse, bse + 32)] m2) as MU. pose proof (wmono_refl rsegs m2) as WM.
pose proof REST2 as (HP2 & LV2 & _). pose proof INV2 as [_ REST2']. clear REST2'.
destruct INV2 as [CORE2 _]. pose proof CORE2 as (_ & _ & _ & _ & _ & PB2 & _).
stash PB2. stash REST2. stash TSK. clear LV2.

assert (TAIL : forall st' mc (x1' t0' t1' t2' a0v a1v a2v a3v a4v a5v a6v a7v s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' : word),
(bv_unsigned cb = 47 /\ st' = ST_eatws) \/ (bv_unsigned cb <> 47 /\ st' = ST_comment) ->
rw_cells rsegs mc bse [C4 (Z_to_bv 64 st'); C4 (Z_to_bv 64 (tl_ss l)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (tl_cur l)); C8 (Z_to_bv 64 (tl_name l))] ->
munch [(bse, bse + 32)] m2 mc -> wmono rsegs m2 mc -> mem_inv rsegs mc ->
rw_cells rsegs mc tk [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 pb); C4 (Z_to_bv 64 mxd); C4 (Z_to_bv 64 (Z.of_nat depth)); C4 isd; C4 stpos;
C4 (Z_to_bv 64 co); C4 err; C4 ucs; C4 high; C1 quote; CB 7 (repeat (Z_to_bv 8 0) 7); C8 (Z_to_bv 64 q); C4 (Z_to_bv 64 fl); C4 (Z_to_bv 64 0)] ->
rw_cells rsegs mc spf [C8 (Z_to_bv 64 obj); CB 16 j1; C4 (nbw j2); CB 3 (skipn 4 j2); C1 cb; CB 8 utf;
C8 (pe_s11 sv); C8 (pe_s10 sv); C8 (pe_s9 sv); C8 (pe_s8 sv); C8 (pe_s7 sv); C8 (pe_s6 sv);
C8 (pe_s5 sv); C8 (pe_s4 sv); C8 (pe_s3 sv); C8 (pe_s2 sv); C8 (pe_s1 sv); C8 (pe_s0 sv); C8 (pe_ra sv)] ->
realizes rsegs (mkCfg (MS (mkR x1' (Z_to_bv 64 spf) gp (Z_to_bv 64 490496) t0' t1' t2' (Z_to_bv 64 tk) (Z_to_bv 64 oldl)
a0v a1v a2v a3v a4v a5v a6v a7v
(Z_to_bv 64 newl) (Z_to_bv 64 lenr) s4' (Z_to_bv 64 (sb + co)) s6' s7' s8' s9' s10' (Z_to_bv 64 0x134c0) t3' t4' t5' t6')
F2 (Z_to_bv 64 PE_BREAK) fc2 None mc (seg_rom rsegs)) md2) T).
{ intros st' mc x1' t0' t1' t2' a0v a1v a2v a3v a4v a5v a6v a7v s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' Hst' L5 MU' WM' MI' TOK' FR'.
unstash PB2. unstash REST2. unstash TSK.
assert (ST'R : 0 <= st' <= 26) by (unfold ST_eatws, ST_comment in Hst'; lia).
assert (WS' : zin st' ws_states = true) by (destruct Hst' as [[_ ->]|[_ ->]]; reflexivity).
set (l1 := TL st' (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)).
set (ts3 := TST depth (lupd levels depth l1) co pb pbs2 (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs).
assert (HW : Forall (pe_wtq (PEF tk oldl newl len lenr sb spf pmd mxd fl) q) [(bse, bse + 32)]) by (apply Forall_cons; [right; cbn [fst snd pf_mxd]; lia | apply Forall_nil]).
assert (TSK3 : tstack rsegs mc q (lupd levels depth l1))
by (subst bse; eapply (tstack_put rsegs m2 _ q levels depth l1 []); [exact TSK | lia | exact MU' | exact WM' | intros; exact I | exact L5]).
assert (PB3 : pbuf rsegs mc pbs2 pb)
by (eapply (pbuf_wtq HIx) with (ts := ts2); [exact STC | exact (proj1 REST2) | exact PB2 | exact MU' | exact WM' | exact HW]).
assert (REST3 : PE_REST HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo mc md2 A2 ts2 errv2)
by (eapply (PE_REST_private_write HIx) with (ts := ts2) in REST2; [exact REST2 | exact STC | exact MU' | exact WM' | exact MI' | apply pe_wtq_private; exact HW]).
apply (Kbreak mc md2 A2 st' pbs2 errv2); [exact Hst' | | exact FS2 | exact FRM2].
split.
- unfold PE_CORE, ts_set_pbs, ts_set_level; cbn. split; [rewrite lupd_length; exact LEN32|]. split; [exact D32|]. split; [lia|]. split; [reflexivity|].
split; [exact TOK'|]. split; [exact PB3|]. split; [exact Hpb|]. split; [exact TSK3 | exact FR'].
- destruct REST3 as (HP' & LV' & OBJ' & ST' & ERR' & STR' & PLEN' & SBin' & HPR' & MDV' & JCG').
unfold ts_set_pbs, ts_set_level; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd].
split.
{ match goal with |- HEAP _ _ _ ?L _ _ => replace L with (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts2); [exact HP' |] end.
unfold pe_blocks, tstate_blocks, ts2; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd].
match goal with |- context [map lvl_blocks (lupd ?lv ?d ?xx)] => rewrite (map_lupd_same lvl_blocks lv d xx l Hl eq_refl) end. reflexivity. }
split; [| split; [| split; [exact ST' | split; [exact ERR' | split; [exact STR' | split; [exact PLEN' | split; [exact SBin' | split; [exact HPR' | split; [exact MDV' | exact JCG']]]]]]]]].
+ intros i li Hli. unfold ts0, ts2 in Hli; cbn [t_levels t_depth pf_mxd] in Hli. unfold ts0, ts2; cbn [t_depth pf_mxd].
destruct (PeanoNat.Nat.eq_dec i depth) as [-> | NE].
* unfold ts0, ts2 in Hli; cbn [t_levels t_depth pf_mxd] in Hli. unfold ts0, ts2; cbn [t_depth pf_mxd]. rewrite nth_error_lupd_eq in Hli by lia. injection Hli as <-.
eapply lvl_cur_restate with (c' := c0); [exact (LV' depth l Hl) | exact Hmode | | exact ST'R | exact SS26 | left; reflexivity].
rewrite <- Hmode. apply lvl_mode_ws_same; [rewrite Hst; reflexivity | exact WS'].
* rewrite nth_error_lupd_neq in Hli by congruence. exact (LV' i li Hli).
+ revert OBJ'. unfold cur_st, ts0, ts2. cbn [t_levels t_depth t_objs t_objbs t_obj pf_mxd]. rewrite nth_error_lupd_eq by lia. cbn [tl_st pf_mxd].
rewrite Hl, Hst. destruct Hst' as [[_ ->]|[_ ->]]; cbn; intros OBJ'; exact OBJ'. }

destruct (Z.eq_dec (bv_unsigned cb) 47) as [C47 | N47].
- tk3_walk 0x23d14 ltac:(try norm_sx32; try unfold zxb; try rewrite (unsigned_lit (bv_unsigned cb)) by lia; try replace (q + Z.of_nat depth * 32) with bse by lia).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
apply evt_RZ_done; eapply (TAIL ST_eatws mc); [left; split; [exact C47 | reflexivity] | exact Ld | exact MU | exact WM | assumption | exact TOK | exact FR] end.
- tk3_walk 0x23d14 ltac:(try norm_sx32; try unfold zxb; try rewrite (unsigned_lit (bv_unsigned cb)) by lia; try replace (q + Z.of_nat depth * 32) with bse by lia).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
apply evt_RZ_done; eapply (TAIL ST_comment mc); [right; split; [exact N47 | reflexivity] | exact Ld | exact MU | exact WM | assumption | exact TOK | exact FR] end.
Qed.

End PeCend.

End RC__1.
End Mq1.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QWxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup.
Import UEQM.
Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0.
Import UC8c.Mq0.
Import Qsw7 QJjn QkMG.
Import UG8z UIsM.Mq2 Udyh.Mq2.
Import QJjn.Mq0.
Import UBpZ UT7i Uv6q UPZI.Mq2.
Import UzWc.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.
Import Q6q3.
Import TopUbTac Tk1Tac Tk3Tac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition is_ws (c : Z) : bool := (c =? 32) || (c =? 9) || (c =? 10) || (c =? 13).

#[using="Type"] Lemma ws_mask : forall c, 0 <= c <= 47 -> Z.land (Z.shiftr 4294977024 c) 1 = (if is_ws c then 1 else 0).
Proof.
intros c R.
assert (E : forall k, (k <= 47)%nat -> Z.land (Z.shiftr 4294977024 (Z.of_nat k)) 1 = (if is_ws (Z.of_nat k) then 1 else 0)).
{ intros k Hk. do 48 (destruct k as [|k]; [vm_compute; reflexivity|]). lia. }
rewrite <- (Z2Nat.id c) by lia. apply E. lia.
Qed.

#[using="Type"] Lemma land255_sxb : forall c : byte, Z.land (bv_unsigned (sxb c)) 255 = bv_unsigned c.
Proof.
intros c. unfold sxb. pose proof (bv_unsigned_in_range 8 c) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R.
change 255 with (Z.ones 8). rewrite Z.land_ones by lia. change (2 ^ 8) with 256.
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_signed, bv_swrap, bv_wrap.
change (bv_half_modulus 8) with 128. change (bv_modulus 8) with 256. change (bv_modulus 64) with 18446744073709551616.
Z.div_mod_to_equations. nia.
Qed.

#[using="Type"] Lemma ws_word : forall cb : byte, bv_unsigned cb <= 47 ->
Z.land (bv_unsigned (Z_to_bv 64 (Z.shiftr 4294977024 (bv_unsigned (Z_to_bv 64 (bv_unsigned cb)) mod 64)))) 1
= (if is_ws (bv_unsigned cb) then 1 else 0).
Proof.
intros cb H. pose proof (bv_unsigned_in_range 8 cb) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R.
rewrite (unsigned_lit (bv_unsigned cb)) by lia. rewrite Z.mod_small by lia.
assert (B : 0 <= Z.shiftr 4294977024 (bv_unsigned cb) <= 4294977024).
{ split; [apply Z.shiftr_nonneg; lia|]. rewrite Z.shiftr_div_pow2 by lia.
apply Z.div_le_upper_bound; [apply Z.pow_pos_nonneg; lia|].
rewrite <- (Z.mul_1_l 4294977024) at 1. apply Z.mul_le_mono_nonneg_r; [lia|]. change 1 with (2 ^ 0) at 1. apply Z.pow_le_mono_r; lia. }
rewrite unsigned_lit by lia. apply ws_mask. lia.
Qed.

#[using="Type"] Lemma lvl_mode_ws_pop : forall st ss c hn,
zin st ws_states = true -> 0 <= ss <= 26 -> lvl_mode st ss = Some (c, hn) -> lvl_mode ss ss = Some (c, hn).
Proof.
intros st ss c hn H R Hm.
assert (C : forall x, zin x ws_states = true -> x = 0 \/ x = 4 \/ x = 5 \/ x = 6 \/ x = 7).
{ intros x Hx. unfold zin, ws_states in Hx. cbn in Hx. rewrite !Bool.orb_true_iff in Hx. rewrite !Z.eqb_eq in Hx. intuition lia. }
destruct (C st H) as [->|[->|[->|[->| ->]]]]; enum_z R ss; vm_compute in Hm; vm_compute; congruence.
Qed.

Section PeEatws.
Variable HIx : heap_iface S4L.
Hypothesis MEMMOVE : memmove_stmt.

Definition ts_ws (ts : tstate) (st' : Z) (co' : Z) (pbs' : list blk) : tstate :=
match nth_error (t_levels ts) (t_depth ts) with
| Some l => TST (t_depth ts) (lupd (t_levels ts) (t_depth ts) (TL st' (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)))
co' (t_pb ts) pbs'
(TS (ts_isd (t_x ts)) (ts_stpos (t_x ts)) (Z_to_bv 64 co') (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))
(t_obj ts) (t_objs ts) (t_objbs ts)
| None => ts
end.

Local Ltac w2 a b E := repeat (lazymatch goal with
| |- evt _ _ (MS _ _ (Z_to_bv 64 a) _ _ _ _) => fail
| |- evt _ _ (MS _ _ (Z_to_bv 64 b) _ _ _ _) => fail
| |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => try E; first [ub_if_lit_c | if_falsex | if_truex | align_true | ub_cmp_auto_c]
| |- _ => try shl_norm; try E; first [bstepz | stepz]
end).

Local Ltac wsplit a b E := w2 a b E; lazymatch goal with
| |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => let Hb := fresh "Hb" in destruct c eqn:Hb; cbv iota; wsplit a b E
| |- _ => idtac
end.

Local Ltac eE := try norm_sx32; try norm_w32; try (rewrite ?le1_sxb; mem_after_store).

Local Ltac eF fl k := eE; try rewrite (zxb_byte fl) by lia; try rewrite (unsigned_lit (fl mod 256)) by (pose proof (Z.mod_pos_bound fl 256 ltac:(lia)); lia); try rewrite (land_mod256 fl k) by lia.

#[using="Type"] Lemma eatws_loop :
forall (n : nat) (pf : pe_fix) (q : Z) (LB0 : list blk) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (ts : tstate) (l : tlevel)
(cb : byte) (j1 j2 utf : list byte) (sv : pe_saved) (errv : word) (T : TSet)
(x1 gp t0 t1 t2 a3 a5 a6 a7 s6 s7 s8 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC HIx pf lo ->
PE_INV HIx pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv ->
CSTR_OK pf payload ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_eatws ->
t_co ts < pf_len pf -> nth_error payload (Z.to_nat (t_co ts)) = Some cb ->
(pf_len pf - t_co ts <= Z.of_nat n) ->

(forall m' co' cb' j2' x1' gp' t0' t1' t2' a1' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6',
t_co ts <= co' < pf_len pf -> nth_error payload (Z.to_nat co') = Some cb' ->
is_ws (bv_unsigned cb') = false ->
PE_INV HIx pf q LB0 payload me lo m' md A (ts_set_co ts co') cb' j1 j2' utf sv errv ->
realizes rsegs (mkCfg (pe_ms rsegs pf 0x22998 co' x1' gp' t0' t1' t2' (Z_to_bv 64 0) a1' (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) a3' a4' a5' a6' a7'
s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F fc m') md) T) ->

(forall m' co' cb' j2' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6',
t_co ts <= co' < pf_len pf -> nth_error payload (Z.to_nat co') = Some cb' -> bv_unsigned cb' = 47 ->
PE_INV HIx pf q LB0 payload me lo m' md A (ts_set_co ts co') cb' j1 j2' utf sv errv ->
realizes rsegs (mkCfg (pe_ms rsegs pf 0x238cc co' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F fc m') md) T) ->

(forall m' (e : word) cb' j2' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6',
nth_error payload (Z.to_nat (pf_len pf - 1)) = Some cb' -> is_ws (bv_unsigned cb') = true ->
PE_INV HIx pf q LB0 payload me lo m' md A (ts_set_err (ts_set_co ts (pf_len pf)) e) cb' j1 j2' utf sv errv ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_OUT (pf_len pf - 1) x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F fc m') md) T) ->

(forall m' co' cb' j2' x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6',
t_co ts <= co' <= pf_len pf ->
PE_INV HIx pf q LB0 payload me lo m' md A (ts_set_co ts co') cb' j1 j2' utf sv errv ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_ERR co' x1' gp' t0' t1' t2' (Z_to_bv 64 14) a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F fc m') md) T) ->
realizes rsegs (mkCfg (pe_ms rsegs pf 0x223bc (t_co ts) x1 gp t0 t1 t2 (Z_to_bv 64 0) (Z_to_bv 64 (pf_sb pf + t_co ts)) (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) a3 (Z_to_bv 64 (bv_unsigned cb)) a5 a6 a7
(Z_to_bv 64 q) s6 s7 s8 (Z_to_bv 64 (Z.of_nat (t_depth ts))) s10 t3 t4 t5 t6 F fc m) md) T.
Proof.
induction n as [|n IH]; intros until fc; intros STC INV CSTR Hl Hst Hco Hc Hn Kns Ksl Kout Kerr14.
{ exfalso. destruct INV as [(_ & _ & CO & _) _]. cbn in Hn. lia. }
pose proof INV as INV0.
pose proof STC as (LO & LOS & SPA & HT & SP0 & LEN & SB0 & (SBL & RR & LENR)).
destruct INV as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof REST as (HP & LV & OBJ & ST & ERR & STR & PLEN & SBin & HPR & MDV & JCG).
destruct ts as [depth levels co pb pbs xx obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct xx as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl_]; pe_gen fl_; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
unfold ts_set_co, ts_set_err in Kns, Ksl, Kout, Kerr14. cbn [t_levels t_depth t_co t_pb t_pbs t_x t_obj t_objs t_objbs ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in Kns, Ksl, Kout, Kerr14.
unfold tok_cells, tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in TOK. unfold pe_frame in FR. unfold pe_ms in *. cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
unfold_consts.
pose proof (bv_unsigned_in_range 8 cb) as CBR; unfold bv_modulus in CBR; cbn in CBR.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocks; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, (32 * mxd)) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocks; apply in_or_app; right; right; left; reflexivity).
pose proof (heap_blk S4L HIx _ _ _ _ tk 72 HP INtk) as (_ & Htal & Htlo & Hthi & _).
pose proof (heap_blk S4L HIx _ _ _ _ q (32 * mxd) HP INq) as (_ & Hqal & Hqlo & Hqhi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hthi, Hqhi.
assert (Htq : tk <> q).
{ pose proof (heap_blk_nodup S4L HIx _ _ _ _ HP) as ND. unfold pe_blocks in ND. rewrite map_app in ND. apply NoDup_app_remove_l in ND.
cbn [map blk_addr fst pf_mxd] in ND. apply List.NoDup_cons_iff in ND as [Hni _]. intros E. apply Hni. left. symmetry. exact E. }
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ tk 72 q (32 * mxd) HP INtk INq Htq) as Hdtq.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L pf_mxd] in MI.
pose proof (wmono_refl rsegs m) as WM.
pose proof (bytes_at_bound _ _ _ _ STR) as SBB.
assert (SB1 : 1 <= sb).
{ unfold payload_loc in SBin; cbn [pf_spf pf_sb pf_len pf_mxd] in SBin.
destruct SBin as [L0 | [Hs | (b & Hb & Hb1 & Hb2)]]; [lia | unfold PE_FRAME in Hs; lia |].
destruct b as [ba bn]. cbn [blk_addr blk_size fst snd] in Hb1, Hb2. unfold blk_addr in Hb1 || idtac. cbn [fst] in Hb1.
assert (INb : In (ba, bn) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocks; apply in_or_app; right; right; right; exact Hb).
pose proof (heap_blk S4L HIx _ _ _ _ ba bn HP INb) as (_ & _ & Hba & _). lia. }
stash PB. stash REST. stash TSK. clear LV OBJ HPR.
apply rz_evt; [exact MOK|].
tk3_walk 0 idtac.
destruct (Z_lt_dec 47 (bv_unsigned cb)) as [GT | LE].
{ if_truex. apply evt_RZ_done. unstash PB. unstash REST. unstash TSK.
eapply (Kns m co cb); [lia | exact Hc | | exact INV0].
unfold is_ws. rewrite !(proj2 (Z.eqb_neq _ _)) by lia. reflexivity. }
if_falsex.
tk3_walk 0 idtac.
rewrite (ws_word cb) by lia.
destruct (is_ws (bv_unsigned cb)) eqn:WS.
2:{
pose proof (tok_flags_byte_g mxd fl m tk pb (Z.of_nat depth) q (TS isd stpos (Z_to_bv 64 co) err ucs high quote) TOK) as RDF.
destruct (Z.eq_dec (bv_unsigned cb) 47) as [E47 | N47].
- tk3_walk 0 ltac:(eF fl 1).
destruct (land1_cases fl) as [F1 | F1]; rewrite F1.
+ tk3_walk 0x238cc idtac. apply evt_RZ_done. unstash PB. unstash REST. unstash TSK.
eapply (Ksl m co cb); [lia | exact Hc | exact E47 | exact INV0].
+ tk3_walk 0x22998 idtac. apply evt_RZ_done. unstash PB. unstash REST. unstash TSK.
eapply (Kns m co cb); [lia | exact Hc | exact WS | exact INV0].
- tk3_walk 0x22998 idtac. apply evt_RZ_done. unstash PB. unstash REST. unstash TSK.
eapply (Kns m co cb); [lia | exact Hc | exact WS | exact INV0]. }
pose proof (munch_refl [(tk, tk + 72); (spf, spf + 144)] m) as MU.
assert (HW : Forall (pe_wtf (PEF tk oldl newl len lenr sb spf pmd mxd fl)) [(tk, tk + 72); (spf, spf + 144)]).
{ apply Forall_cons; [left; cbn; lia |]. apply Forall_cons; [| apply Forall_nil].
right; unfold PE_FRAME; cbn [pf_spf pf_tk fst snd pf_md pf_mxd pf_fl]; split; [apply Z.le_refl | apply Z.le_refl]. }
assert (Hnz : bv_unsigned cb <> 0) by (intros E0; rewrite E0 in WS; discriminate WS).
tk3_walk 0 eE.
destruct (peek_cases (PEF tk oldl newl len lenr sb spf pmd mxd fl) payload co cb LENR CSTR (proj1 RR) ltac:(cbn [pf_len pf_mxd]; lia) ltac:(cbn [pf_len pf_mxd]; lia) Hc Hnz)
as [[Elenr Heof] | [Hne Hmore]]; cbn [pf_len pf_lenr pf_mxd] in Elenr, Heof |- || cbn [pf_len pf_lenr pf_mxd] in Hne, Hmore |-.
- subst lenr. pose (lenr := len).
first [if_falsex | if_truex].
assert (TAIL : forall (e : word) mc (nv : word) x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6',
rw_cells rsegs mc tk
[C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 pb); C4 (Z_to_bv 64 mxd); C4 (Z_to_bv 64 (Z.of_nat depth)); C4 isd; C4 stpos;
C4 (Z_to_bv 64 (co + 1)); C4 e; C4 ucs; C4 high; C1 quote; CB 7 (repeat (Z_to_bv 8 0) 7); C8 (Z_to_bv 64 q); C4 (Z_to_bv 64 fl); C4 (Z_to_bv 64 0)] ->
rw_cells rsegs mc spf [C8 (Z_to_bv 64 obj); CB 16 j1; C4 nv; CB 3 (skipn 4 j2); C1 cb; CB 8 utf;
C8 (pe_s11 sv); C8 (pe_s10 sv); C8 (pe_s9 sv); C8 (pe_s8 sv); C8 (pe_s7 sv); C8 (pe_s6 sv);
C8 (pe_s5 sv); C8 (pe_s4 sv); C8 (pe_s3 sv); C8 (pe_s2 sv); C8 (pe_s1 sv); C8 (pe_s0 sv); C8 (pe_ra sv)] ->
munch [(tk, tk + 72); (spf, spf + 144)] m mc -> wmono rsegs m mc -> mem_inv rsegs mc ->
realizes rsegs (mkCfg (pe_ms rsegs (PEF tk oldl newl len lenr sb spf pmd mxd fl) PE_OUT (len - 1) x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F fc mc) md) T).
{ intros e mc nv x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' TOK' FR' MU' WM' MI'.
unstash PB. unstash REST. unstash TSK.
eapply (Kout mc e cb (le4 nv ++ skipn 4 j2)); [replace (len - 1) with co by lia; exact Hc | exact WS |].
split.
- unfold PE_CORE; cbn. split; [exact LEN32|]. split; [exact D32|]. split; [lia|]. split; [reflexivity|].
rewrite <- Heof. split; [exact TOK'|]. split; [| split; [exact Hpb | split; [| apply pe_frame_nb_set; exact FR']]].
+ eapply (pbuf_wtf HIx) with (ts := ts0); [exact STC | exact (proj1 REST) | exact PB | exact MU' | exact WM' | exact HW].
+ eapply (tstack_wtf HIx) with (ts := ts0); [exact STC | exact (proj1 REST) | exact TSK | exact LEN32 | exact MU' | exact WM' | exact HW].
- cbn. eapply (PE_REST_private_write HIx) with (ts := ts0) in REST;
[exact REST | exact STC | exact MU' | exact WM' | exact MI' | apply pe_wtf_private; exact HW]. }
tk3_walk 0 eE.
destruct (PeanoNat.Nat.eq_dec depth 0) as [D0 | Dn].
+ subst depth. cbn [Z.of_nat pf_mxd] in TOK, TAIL |- *.
destruct (nth_error levels 0) as [l0|] eqn:Hl0; [| apply nth_error_None in Hl0; lia].
assert (L0 : rw_cells rsegs m q (srec_cells l0)) by (unstash TSK; pose proof (TSK 0%nat l0 Hl0) as L0; rewrite Z.mul_0_r, Z.add_0_r in L0; exact L0).
unfold srec_cells in L0.
eapply (rw_cells_transport rsegs _ m) in L0; [| exact MU | exact WM | cbn; unfold PE_FRAME in *; lia].
wsplit 0x23ea8 0x23ea8 eE.
all: replace (sb + co) with (sb + (len - 1)) by lia; apply evt_RZ_done; eapply TAIL; eassumption.
+ tk3_walk 0x23ea8 eE.
replace (sb + co) with (sb + (len - 1)) by lia; apply evt_RZ_done; eapply TAIL; eassumption.
- first [if_truex | if_falsex].
destruct (nth_error payload (Z.to_nat (co + 1))) as [c'|] eqn:Hc'; [| apply nth_error_None in Hc'; lia].
pose proof (bv_unsigned_in_range 8 c') as CR'; unfold bv_modulus in CR'; cbn in CR'.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
assert (STR1 : bytes_at rsegs m1 sb payload)
by (unstash REST; eapply (PE_REST_private_write HIx) with (ts := ts0) in REST;
[exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 REST)))))) | exact STC | exact MU | exact WM | exact MI | apply pe_wtf_private; exact HW]);
pose proof (tok_flags_byte_g mxd fl m1 tk pb (Z.of_nat depth) q (TS isd stpos (Z_to_bv 64 (co + 1)) err ucs high quote) TOK) as RDF
end.
pose proof (payload_byte _ _ _ _ _ STR1 Hc' ltac:(lia)) as RDC. replace (sb + (co + 1)) with (sb + co + 1) in RDC by lia.
assert (INVAT : forall mc (cbx : byte) (nv : word),
rw_cells rsegs mc tk
[C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 pb); C4 (Z_to_bv 64 mxd); C4 (Z_to_bv 64 (Z.of_nat depth)); C4 isd; C4 stpos;
C4 (Z_to_bv 64 (co + 1)); C4 err; C4 ucs; C4 high; C1 quote; CB 7 (repeat (Z_to_bv 8 0) 7); C8 (Z_to_bv 64 q); C4 (Z_to_bv 64 fl); C4 (Z_to_bv 64 0)] ->
rw_cells rsegs mc spf [C8 (Z_to_bv 64 obj); CB 16 j1; C4 nv; CB 3 (skipn 4 j2); C1 cbx; CB 8 utf;
C8 (pe_s11 sv); C8 (pe_s10 sv); C8 (pe_s9 sv); C8 (pe_s8 sv); C8 (pe_s7 sv); C8 (pe_s6 sv);
C8 (pe_s5 sv); C8 (pe_s4 sv); C8 (pe_s3 sv); C8 (pe_s2 sv); C8 (pe_s1 sv); C8 (pe_s0 sv); C8 (pe_ra sv)] ->
munch [(tk, tk + 72); (spf, spf + 144)] m mc -> wmono rsegs m mc -> mem_inv rsegs mc ->
PE_INV HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo mc md A
(TST depth levels (co + 1) pb pbs (TS isd stpos (Z_to_bv 64 (co + 1)) err ucs high quote) obj objs objbs) cbx j1 (le4 nv ++ skipn 4 j2) utf sv errv).
{ intros mc cbx nv TOK' FR' MU' WM' MI'. unstash PB. unstash REST. unstash TSK.
split.
+ unfold PE_CORE; cbn. split; [exact LEN32|]. split; [exact D32|]. split; [lia|]. split; [reflexivity|].
split; [exact TOK'|]. split; [| split; [exact Hpb | split; [| apply pe_frame_nb_set; exact FR']]].
* eapply (pbuf_wtf HIx) with (ts := ts0); [exact STC | exact (proj1 REST) | exact PB | exact MU' | exact WM' | exact HW].
* eapply (tstack_wtf HIx) with (ts := ts0); [exact STC | exact (proj1 REST) | exact TSK | exact LEN32 | exact MU' | exact WM' | exact HW].
+ cbn. eapply (PE_REST_private_write HIx) with (ts := ts0) in REST;
[exact REST | exact STC | exact MU' | exact WM' | exact MI' | apply pe_wtf_private; exact HW]. }
assert (LZ : le1 (zxb c') = [c']) by exact (Udyh.Mq7.le1_zxb c').
assert (LOOPK : forall mc (cbx : byte) (nv : word) x1' gp' t0' t1' t2' a3' a4' a5' a6' a7' s6' s7' s8' s10' t3' t4' t5' t6',
rw_cells rsegs mc tk
[C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 pb); C4 (Z_to_bv 64 mxd); C4 (Z_to_bv 64 (Z.of_nat depth)); C4 isd; C4 stpos;
C4 (Z_to_bv 64 (co + 1)); C4 err; C4 ucs; C4 high; C1 quote; CB 7 (repeat (Z_to_bv 8 0) 7); C8 (Z_to_bv 64 q); C4 (Z_to_bv 64 fl); C4 (Z_to_bv 64 0)] ->
rw_cells rsegs mc spf [C8 (Z_to_bv 64 obj); CB 16 j1; C4 nv; CB 3 (skipn 4 j2); C1 cbx; CB 8 utf;
C8 (pe_s11 sv); C8 (pe_s10 sv); C8 (pe_s9 sv); C8 (pe_s8 sv); C8 (pe_s7 sv); C8 (pe_s6 sv);
C8 (pe_s5 sv); C8 (pe_s4 sv); C8 (pe_s3 sv); C8 (pe_s2 sv); C8 (pe_s1 sv); C8 (pe_s0 sv); C8 (pe_ra sv)] ->
munch [(tk, tk + 72); (spf, spf + 144)] m mc -> wmono rsegs m mc -> mem_inv rsegs mc ->
evt rsegs (RZ rsegs md T) (pe_ms rsegs (PEF tk oldl newl len lenr sb spf pmd mxd fl) 0x223b0 (co + 1) x1' gp' t0' t1' t2'
(Z_to_bv 64 0) (Z_to_bv 64 (sb + (co + 1))) (Z_to_bv 64 (q + 32 * Z.of_nat depth)) a3' a4' a5' a6' a7'
(Z_to_bv 64 q) s6' s7' s8' (Z_to_bv 64 (Z.of_nat depth)) s10' t3' t4' t5' t6' F fc mc)).
{ intros mc cbx nv x1' gp' t0' t1' t2' a3' a4' a5' a6' a7' s6' s7' s8' s10' t3' t4' t5' t6' TOK' FR' MU' WM' MI'.
unfold pe_ms; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl]. unfold_consts.
assert (STR2 : bytes_at rsegs mc sb payload)
by (unstash REST; eapply (PE_REST_private_write HIx) with (ts := ts0) in REST;
[exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 REST)))))) | exact STC | exact MU' | exact WM' | exact MI' | apply pe_wtf_private; exact HW]).
pose proof (payload_byte _ _ _ _ _ STR2 Hc' ltac:(lia)) as RDC2.
tk3_walk 0x223bc ltac:(eE; try (rewrite LZ; mem_after_store)).
change (zxb c') with (Z_to_bv 64 (bv_unsigned c')).
rewrite (unsigned_lit (bv_unsigned c')) by lia. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. change (2 ^ 8) with 256. rewrite (Z.mod_small (bv_unsigned c') 256) by lia.
apply evt_RZ_done.
eapply (IH (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo _ md A
(TST depth levels (co + 1) pb pbs (TS isd stpos (Z_to_bv 64 (co + 1)) err ucs high quote) obj objs objbs) l c');
[exact STC | eapply INVAT; eassumption | exact CSTR | exact Hl | exact Hst | cbn; lia | exact Hc' | cbn; lia
| intros; eapply Kns; [cbn in *; lia | eassumption | assumption | eassumption]
| intros; eapply Ksl; [cbn in *; lia | eassumption | assumption | eassumption]
| intros; eapply Kout; [eassumption | assumption | eassumption]
| intros; eapply Kerr14; [cbn in *; lia | eassumption] ]. }
tk3_walk 0 ltac:(eF fl 16).
destruct (land16_cases fl) as [F16 | F16]; rewrite F16.
+ tk3_walk 0x223b0 eE.
replace (sb + co + 1) with (sb + (co + 1)) by lia. eapply LOOPK; eassumption.
+ wsplit 0x223b0 0x23ea4 eE.
all: replace (sb + co + 1) with (sb + (co + 1)) by lia.
all: lazymatch goal with
| |- evt _ _ (MS _ _ (Z_to_bv 64 0x223b0) _ _ _ _) => eapply LOOPK; eassumption
| |- evt _ _ (MS _ _ (Z_to_bv 64 0x23ea4) _ _ _ _) => apply evt_RZ_done; eapply (Kerr14 _ (co + 1)); [lia | eapply INVAT; eassumption]
end.
Qed.

#[using="Type"] Lemma eatws_pop :
forall (pf : pe_fix) (q : Z) (LB0 : list blk) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (ts : tstate) (l : tlevel)
(cb : byte) (j1 j2 utf : list byte) (sv : pe_saved) (errv : word) (T : TSet)
(x1 gp t0 t1 t2 a1 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC HIx pf lo ->
PE_INV HIx pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_eatws ->
(forall m' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6',
PE_INV HIx pf q LB0 payload me lo m' md A (ts_ws ts (tl_ss l) (t_co ts) (t_pbs ts)) cb j1 j2 utf sv errv ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_REDO (t_co ts) x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F fc m') md) T) ->
realizes rsegs (mkCfg (pe_ms rsegs pf 0x22998 (t_co ts) x1 gp t0 t1 t2 (Z_to_bv 64 0) a1 (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) a3 a4 a5 a6 a7
s4 s6 s7 s8 s9 s10 t3 t4 t5 t6 F fc m) md) T.
Proof.
intros until fc. intros STC INV Hl Hst Kredo.
pose proof STC as (LO & LOS & SPA & HT & SP0 & LEN & SB0 & SBL).
destruct INV as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof REST as (HP & LV & _).
destruct ts as [depth levels co pb pbs xx obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct xx as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl_]; pe_gen fl_; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
unfold ts_ws in Kredo. cbn [t_levels t_depth t_co t_pb t_pbs t_x t_obj t_objs t_objbs ts_isd ts_stpos ts_err ts_ucs ts_high ts_quote pf_mxd] in Kredo. rewrite Hl in Kredo.
unfold tok_cells, tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in TOK. unfold pe_frame in FR. unfold pe_ms in *. cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
unfold_consts.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocks; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, (32 * mxd)) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocks; apply in_or_app; right; right; left; reflexivity).
pose proof (heap_blk S4L HIx _ _ _ _ tk 72 HP INtk) as (_ & Htal & Htlo & Hthi & _).
pose proof (heap_blk S4L HIx _ _ _ _ q (32 * mxd) HP INq) as (_ & Hqal & Hqlo & Hqhi & _).
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
pose proof (TSK depth l Hl) as Ld. unfold srec_cells in Ld.
remember (q + 32 * Z.of_nat depth) as bse eqn:Hbse in Ld.
assert (Hbal : bse mod 16 = 0) by (rewrite Hbse; Z.div_mod_to_equations; lia).
assert (HbseR : q <= bse /\ bse + 32 <= q + (32 * mxd)) by (subst bse; lia).
pose proof (munch_refl [(bse, bse + 32)] m) as MU.
stash PB. stash REST. stash TSK. clear LV. rewrite <- Hbse.
apply rz_evt; [exact MOK|].
tk3_walk 0x21e14 ltac:(try norm_sx32).
unstash PB. unstash REST. unstash TSK.
set (l1 := TL (tl_ss l) (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)).
assert (HW : Forall (pe_wtq (PEF tk oldl newl len lenr sb spf pmd mxd fl) q) [(bse, bse + 32)]) by (apply Forall_cons; [right; cbn [fst snd pf_mxd]; lia | apply Forall_nil]).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
match goal with L5 : rw_cells rsegs mc bse _ |- _ =>
assert (TSK3 : tstack rsegs mc q (lupd levels depth l1))
by (subst bse; eapply (tstack_put rsegs m _ q levels depth l1 []); [exact TSK | lia | exact MU | exact WM | intros; exact I | exact L5]);
assert (PB3 : pbuf rsegs mc pbs pb)
by (eapply (pbuf_wtq HIx) with (ts := ts0); [exact STC | exact (proj1 REST) | exact PB | exact MU | exact WM | exact HW]);
assert (REST3 : PE_REST HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo mc md A ts0 errv)
by (eapply (PE_REST_private_write HIx) with (ts := ts0) in REST; [exact REST | exact STC | exact MU | exact WM | assumption | apply pe_wtq_private; exact HW]);
subst bse; apply evt_RZ_done; apply (Kredo mc)
end end.
split.
- unfold PE_CORE; cbn. split; [rewrite lupd_length; exact LEN32|]. split; [exact D32|]. split; [lia|]. split; [reflexivity|].
split; [assumption|]. split; [exact PB3|]. split; [exact Hpb|]. split; [exact TSK3 | assumption].
- destruct REST3 as (HP' & LV' & OBJ' & ST' & ERR' & STR' & PLEN' & SBin' & HPR' & MDV' & JCG').
cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd].
split.
{ match goal with |- HEAP _ _ _ ?L _ _ => replace L with (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0); [exact HP' |] end.
unfold pe_blocks, tstate_blocks, ts0; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd].
match goal with |- context [map lvl_blocks (lupd ?lv ?d ?xx)] => rewrite (map_lupd_same lvl_blocks lv d xx l Hl eq_refl) end. reflexivity. }
split; [| split; [| split; [exact ST' | split; [exact ERR' | split; [exact STR' | split; [exact PLEN' | split; [exact SBin' | split; [exact HPR' | split; [exact MDV' | exact JCG']]]]]]]]].
+ intros i li Hli. unfold ts0 in Hli; cbn [t_levels t_depth pf_mxd] in Hli. unfold ts0; cbn [t_depth pf_mxd].
destruct (PeanoNat.Nat.eq_dec i depth) as [-> | NE].
* rewrite nth_error_lupd_eq in Hli by lia. injection Hli as <-.
eapply lvl_cur_restate with (c' := c0); [exact (LV' depth l Hl) | exact Hmode | | exact SS26 | exact SS26 | left; reflexivity].
eapply (lvl_mode_ws_pop (tl_st l)); [rewrite Hst; reflexivity | exact SS26 | exact Hmode].
* rewrite nth_error_lupd_neq in Hli by congruence. exact (LV' i li Hli).
+ revert OBJ'. unfold cur_st, ts0. cbn [t_levels t_depth t_objs t_objbs t_obj pf_mxd]. rewrite nth_error_lupd_eq by lia. cbn [tl_st pf_mxd].
rewrite Hl, Hst.
assert (Ez : zin (tl_ss l) [ST_array_add; ST_ovadd] = false).
{ destruct (zin (tl_ss l) [ST_array_add; ST_ovadd]) eqn:E; [| reflexivity]. exfalso.
revert Hmode E. rewrite Hst. clear. intros Hmode E.
assert (R : tl_ss l = 16 \/ tl_ss l = 22).
{ unfold zin in E. cbn in E. rewrite !Bool.orb_true_iff in E. rewrite !Z.eqb_eq in E. unfold ST_array_add, ST_ovadd in E. intuition lia. }
destruct R as [E'|E']; rewrite E' in Hmode; vm_compute in Hmode; discriminate Hmode. }
rewrite Ez. cbn. intros OBJ'; exact OBJ'.
Qed.

#[using="MEMMOVE"] Lemma eatws_slash :
forall (pf : pe_fix) (q : Z) (LB0 : list blk) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (ts : tstate) (l : tlevel)
(cb : byte) (j1 j2 utf : list byte) (sv : pe_saved) (errv : word) (T : TSet)
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC HIx pf lo ->
PE_INV HIx pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_eatws ->

(forall m' md' A' pbs' errv' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F' fc',
PE_INV HIx pf q LB0 payload me lo m' md' A' (ts_ws ts ST_comment_start (t_co ts) pbs') cb j1 j2 utf sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_BREAK (t_co ts) x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F' fc' m') md') T) ->

(forall m' md' A' pbs' errv' x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F' fc',
PE_INV HIx pf q LB0 payload me lo m' md' A' (ts_set_pbs ts pbs') cb j1 j2 utf sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_ERR (t_co ts) x1' gp' t0' t1' t2' (Z_to_bv 64 16) a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F' fc' m') md') T) ->
realizes rsegs (mkCfg (pe_ms rsegs pf 0x238cc (t_co ts) x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 s10 t3 t4 t5 t6 F fc m) md) T.
Proof.
intros until fc. intros STC INV Hl Hst Kbreak Kerr16.
pose proof STC as (LO & LOS & SPA & HT & SP0 & LEN & SB0 & SBL).
destruct INV as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof REST as (HP & LV & _).
destruct ts as [depth levels co pb pbs xx obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct xx as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl_]; pe_gen fl_; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
unfold ts_ws in Kbreak. cbn [t_levels t_depth t_co t_pb t_pbs t_x t_obj t_objs t_objbs ts_isd ts_stpos ts_err ts_ucs ts_high ts_quote pf_mxd] in Kbreak. rewrite Hl in Kbreak.
unfold tok_cells, tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in TOK. unfold pe_frame in FR. unfold pe_ms in *. cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
unfold_consts.
pose proof (bv_unsigned_in_range 8 cb) as CBR; unfold bv_modulus in CBR; cbn in CBR.
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

pose proof PB as (buf & bpos & cap & pre & post & Epbs & Lpre & PBC). pose proof PBC as (Hbpos & Hcap & _).
assert (INpb : In (pb, 16) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocks, tstate_blocks, ts0; cbn [t_pbs pf_mxd]; rewrite Epbs; left; reflexivity).
assert (INbuf : In (buf, cap) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocks, tstate_blocks, ts0; cbn [t_pbs pf_mxd]; rewrite Epbs; right; left; reflexivity).
pose proof (heap_blk S4L HIx _ _ _ _ pb 16 HP INpb) as (_ & Hpbal & Hpblo & Hpbhi & _).
pose proof (heap_blk S4L HIx _ _ _ _ buf cap HP INbuf) as (_ & Hbufal & Hbuflo & Hbufhi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hpbhi, Hbufhi.
assert (Hpbbuf : pb <> buf).
{ generalize ND; intros ND'. unfold pe_blocks, tstate_blocks, ts0 in ND'. cbn [t_pbs pf_mxd] in ND'. rewrite Epbs in ND'. cbn [map blk_addr fst app pf_mxd] in ND'.
apply List.NoDup_cons_iff in ND' as [Hni _]. intros E. apply Hni. left. symmetry. exact E. }
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ pb 16 buf cap HP INpb INbuf Hpbbuf) as Hdpb.
assert (Htkpb : tk <> pb /\ tk <> buf /\ q <> pb /\ q <> buf).
{ generalize ND; intros ND'. unfold pe_blocks, tstate_blocks, ts0 in ND'. cbn [t_pbs t_objbs t_levels pf_tk pf_md pf_mxd pf_fl] in ND'. rewrite Epbs in ND'.
assert (ND2 : List.NoDup (map blk_addr (([(pb, 16); (buf, cap)] ++ (objbs ++ concat (map lvl_blocks levels))) ++ (tk, 72) :: (q, (32 * mxd)) :: LB0))) by exact ND'.
rewrite map_app in ND2.
repeat split; intros E.
- eapply (NoDup_app_in2 _ _ tk ND2); [rewrite E; cbn; left; reflexivity | cbn; left; reflexivity].
- eapply (NoDup_app_in2 _ _ tk ND2); [rewrite E; cbn; right; left; reflexivity | cbn; left; reflexivity].
- eapply (NoDup_app_in2 _ _ q ND2); [rewrite E; cbn; left; reflexivity | cbn; right; left; reflexivity].
- eapply (NoDup_app_in2 _ _ q ND2); [rewrite E; cbn; right; left; reflexivity | cbn; right; left; reflexivity]. }
destruct Htkpb as (Htkpb & Htkbuf & Hqpb & Hqbuf).
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ tk 72 pb 16 HP INtk INpb Htkpb) as Hd1.
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ tk 72 buf cap HP INtk INbuf Htkbuf) as Hd2.
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ q (32 * mxd) pb 16 HP INq INpb Hqpb) as Hd3.
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ q (32 * mxd) buf cap HP INq INbuf Hqbuf) as Hd4.
stash Hd1. stash Hd2. stash Hd3. stash Hd4. stash Hdpb. clear ND.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L pf_mxd] in MI.
pose proof (LV depth l Hl) as LVd. pose proof LVd as (ST26 & SS26 & _ & Md).
rewrite Nat.ltb_irrefl, Nat.eqb_refl in Md. destruct Md as (c0 & hn0 & Hmode & CLS0 & NM0).
stash REST. stash TSK. clear LV PB.
apply rz_evt; [exact MOK|].
tk3_walk 0x245cc idtac.
eapply evt_cut; [eapply printbuf_reset_P; [exact PBC | lia | lia | first [exact Hpbal | lia] | lia | lia | unstash Hdpb; exact Hdpb | exact MI] |].
intros ms1 (mr & -> & MUr & WMr & MIr & PBC1).
replace (ret_pc (Z_to_bv 64 0x238d4)) with (Z_to_bv 64 0x238d4) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
unstash REST. unstash TSK.
assert (HWR : Forall (pe_private (PEF tk oldl newl len lenr sb spf pmd mxd fl) q pbs) [(buf, buf + 1); (pb + 8, pb + 12)]).
{ apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]; unfold pe_private; cbn [fst snd pf_tk pf_spf pf_md pf_mxd pf_fl]; right; right; left.
- exists buf, cap. rewrite Epbs. split; [right; left; reflexivity | lia].
- exists pb, 16. rewrite Epbs. split; [left; reflexivity | lia]. }
assert (RESTR : PE_REST HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo mr md A ts0 errv)
by (eapply (PE_REST_private_write HIx) with (ts := ts0) in REST; [exact REST | exact STC | exact MUr | exact WMr | exact MIr | exact HWR]).
eapply (rw_cells_transport rsegs _ m mr) in TOK; [| exact MUr | exact WMr | unstash Hd1; unstash Hd2; cbn; lia].
eapply (rw_cells_transport rsegs _ m mr) in FR; [| exact MUr | exact WMr | cbn; lia].
assert (TSKR : tstack rsegs mr q levels).
{ unstash Hd3. unstash Hd4. eapply (tstack_transport rsegs); [exact TSK | exact MUr | exact WMr |]. intros j Hj. rewrite LEN32 in Hj. cbn. (clear - Hcap Hd3 Hd4 Hj; lia). }
clear REST TSK MI MUr WMr.

tk3_walk 0x241a4 idtac.
pose proof (proj1 RESTR) as HP1. unfold pe_blocks, tstate_blocks, ts0 in HP1. cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_tk pf_md pf_mxd pf_fl] in HP1.
rewrite Epbs in HP1. cbn [app pf_mxd] in HP1.
pose proof (pe_frame_cbyte mr spf obj cb j1 j2 utf sv FR) as SRC.
pose proof RESTR as (_ & _ & _ & ST1 & ERR1 & _).
apply evt_RZ_done.
eapply (memappend_cps HIx MEMMOVE) with (lo := lo) (b := spf + 31) (src := [cb]) (n := 1);
[ exact HP1 | exact PBC1 | (clear; lia) | exact SRC | reflexivity | left; left; rewrite ?unsigned_lit by (clear - SP0; lia); (clear; lia) | (clear - LO LOS; lia) | (clear - SP0; lia) | (clear - LO LOS Hbufhi; lia) | .. ]; try alloc_side.
all: try (rewrite ?unsigned_lit by lia; first [exact ST1 | exact ERR1]).
all: try (rewrite ?unsigned_lit by lia; unfold PE_FRAME in *; clia).
intros ms2 md2 (m2 & A2 & r & errv2 & buf' & cap' & RS2 & VM2 & ST2 & HPR2 & ERR2 & HP2 & OUT2).
destruct RS2 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F2 & fc2 & -> & FS2 & FRM2).
cbn [hl_segs hl_tp S4L pf_mxd] in *. rewrite ?(unsigned_lit spf) in ST2 by lia. rewrite ?(unsigned_lit spf) in HPR2 by lia.
set (pbs2 := [(pb, 16); (buf', cap')]).
set (ts2 := TST depth levels co pb pbs2 (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs).
assert (INq2 : In (q, (32 * mxd)) ((objbs ++ concat (map lvl_blocks levels)) ++ (tk, 72) :: (q, (32 * mxd)) :: LB0))
by (apply in_or_app; right; right; left; reflexivity).
assert (INtk2 : In (tk, 72) ((objbs ++ concat (map lvl_blocks levels)) ++ (tk, 72) :: (q, (32 * mxd)) :: LB0))
by (apply in_or_app; right; left; reflexivity).
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. cbn [hl_segs S4L pf_mxd] in FR.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in TOK; [| eapply client_range_block; [exact INtk2 | lia | cbn; lia]]. cbn [hl_segs S4L pf_mxd] in TOK.
apply (tstack_pres_g S4L _ _ _ _ _ _ HPR2 INq2) in TSKR; [| exact LEN32].
assert (REST2 : PE_REST HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo m2 md2 A2 ts2 errv2).
{ eapply (PE_REST_call_pb HIx) with (ts := ts0) (LBc := (objbs ++ concat (map lvl_blocks levels)) ++ (tk, 72) :: (q, (32 * mxd)) :: LB0);
[exact STC | exact RESTR | exact VM2 | exact HPR2 | unfold ts0; cbn [t_objbs t_levels pf_mxd]; intros bb Hb; apply in_or_app;
apply in_app_or in Hb; destruct Hb as [Hb|Hb]; [left; apply in_or_app; left; exact Hb | apply in_app_or in Hb; destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; exact Hb | right; right; right; exact Hb]]
| unfold pe_blocks, tstate_blocks; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_tk pf_md pf_mxd pf_fl]; exact HP2
| exact ST2 | exact ERR2]. }
assert (PBany : pbuf rsegs m2 pbs2 pb).
{ destruct OUT2 as [[_ PBS] | (_ & -> & -> & PC)]; [exact PBS|].
exists buf, 0, cap, [], (skipn 1 (pre ++ [Z_to_bv 8 0] ++ post)). split; [reflexivity|]. split; [reflexivity | exact PC]. }
assert (INV2 : PE_INV HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo m2 md2 A2 ts2 cb j1 j2 utf sv errv2).
{ split; [| exact REST2]. unfold PE_CORE, ts2; cbn. split; [exact LEN32|]. split; [exact D32|]. split; [lia|]. split; [reflexivity|].
split; [exact TOK|]. split; [exact PBany|]. split; [exact Hpb|]. split; [exact TSKR | exact FR]. }
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2.
pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI2. cbn [hl_segs S4L pf_mxd] in MI2.
clear HP1 HP2 RESTR SRC ST1 ERR1 PBany PBC1 HP MOK MIr.
reenter MOK2.
destruct OUT2 as [[-> _] | (-> & -> & -> & _)].
2:{ replace (Z_to_bv 64 (2^64 - 1)) with (Z_to_bv 64 (-1)) by (apply bv_eq; vm_compute; reflexivity).
tk3_walk 0x23ea4 idtac. apply evt_RZ_done. eapply Kerr16; [| exact FS2 | exact FRM2].
unfold ts2, pbs2 in INV2. exact INV2. }

bstep. if_false.
pose proof (TSKR depth l Hl) as Ld. cbn [hl_segs S4L pf_mxd] in Ld. unfold srec_cells in Ld.
remember (q + 32 * Z.of_nat depth) as bse eqn:Hbse in Ld.
assert (Hbal : bse mod 16 = 0) by (rewrite Hbse; Z.div_mod_to_equations; lia).
assert (HbseR : q <= bse /\ bse + 32 <= q + (32 * mxd)) by (subst bse; lia).
pose proof (munch_refl [(bse, bse + 32)] m2) as MU. pose proof (wmono_refl rsegs m2) as WM.
pose proof REST2 as (HP2 & LV2 & _). pose proof INV2 as [CORE2 _]. pose proof CORE2 as (_ & _ & _ & _ & _ & PB2 & _).
stash PB2. stash REST2. stash TSKR. clear LV2 CORE2 INV2.
tk3_walk 0x23d14 ltac:(try norm_sx32; try replace (q + Z.of_nat depth * 32) with bse by lia).
unstash PB2. unstash REST2. unstash TSKR.
set (l1 := TL ST_comment_start (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)).
assert (HW : Forall (pe_wtq (PEF tk oldl newl len lenr sb spf pmd mxd fl) q) [(bse, bse + 32)]) by (apply Forall_cons; [right; cbn [fst snd pf_mxd]; lia | apply Forall_nil]).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
match goal with L5 : rw_cells rsegs mc bse _ |- _ =>
assert (TSK3 : tstack rsegs mc q (lupd levels depth l1))
by (subst bse; eapply (tstack_put rsegs m2 _ q levels depth l1 []); [exact TSKR | lia | exact MU | exact WM | intros; exact I | exact L5]);
assert (PB3 : pbuf rsegs mc pbs2 pb)
by (eapply (pbuf_wtq HIx) with (ts := ts2); [exact STC | exact (proj1 REST2) | exact PB2 | exact MU | exact WM | exact HW]);
assert (REST3 : PE_REST HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo mc md2 A2 ts2 errv2)
by (eapply (PE_REST_private_write HIx) with (ts := ts2) in REST2; [exact REST2 | exact STC | exact MU | exact WM | assumption | apply pe_wtq_private; exact HW]);
apply evt_RZ_done; apply (Kbreak mc md2 A2 pbs2 errv2); [| exact FS2 | exact FRM2]
end end.
split.
- unfold PE_CORE; cbn. split; [rewrite lupd_length; exact LEN32|]. split; [exact D32|]. split; [lia|]. split; [reflexivity|].
split; [assumption|]. split; [exact PB3|]. split; [exact Hpb|]. split; [exact TSK3 | assumption].
- destruct REST3 as (HP' & LV' & OBJ' & ST' & ERR' & STR' & PLEN' & SBin' & HPR' & MDV' & JCG').
cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd].
split.
{ match goal with |- HEAP _ _ _ ?L _ _ => replace L with (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts2); [exact HP' |] end.
unfold pe_blocks, tstate_blocks, ts2; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd].
match goal with |- context [map lvl_blocks (lupd ?lv ?d ?xx)] => rewrite (map_lupd_same lvl_blocks lv d xx l Hl eq_refl) end. reflexivity. }
split; [| split; [| split; [exact ST' | split; [exact ERR' | split; [exact STR' | split; [exact PLEN' | split; [exact SBin' | split; [exact HPR' | split; [exact MDV' | exact JCG']]]]]]]]].
+ intros i li Hli. unfold ts0, ts2 in Hli; cbn [t_levels t_depth pf_mxd] in Hli. unfold ts0, ts2; cbn [t_depth pf_mxd].
destruct (PeanoNat.Nat.eq_dec i depth) as [-> | NE].
* rewrite nth_error_lupd_eq in Hli by lia. injection Hli as <-.
eapply lvl_cur_restate with (c' := c0); [exact (LV' depth l Hl) | exact Hmode | | unfold ST_comment_start; lia | exact SS26 | left; reflexivity].
rewrite <- Hmode. apply lvl_mode_ws_same; [rewrite Hst; reflexivity | reflexivity].
* rewrite nth_error_lupd_neq in Hli by congruence. exact (LV' i li Hli).
+ revert OBJ'. unfold cur_st, ts0, ts2. cbn [t_levels t_depth t_objs t_objbs t_obj pf_mxd]. rewrite nth_error_lupd_eq by lia. cbn [tl_st pf_mxd].
rewrite Hl, Hst. cbn. intros OBJ'; exact OBJ'.
Qed.

#[using="MEMMOVE"] Lemma seg_eatws :
forall (pf : pe_fix) (q : Z) (LB0 : list blk) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (ts : tstate) (l : tlevel)
(cb : byte) (j1 j2 utf : list byte) (sv : pe_saved) (errv : word) (T : TSet)
(x1 gp t0 t1 t2 a3 a4 a5 a6 a7 s6 s7 s8 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC HIx pf lo ->
PE_INV HIx pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv ->
CSTR_OK pf payload ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_eatws ->
t_co ts < pf_len pf -> nth_error payload (Z.to_nat (t_co ts)) = Some cb ->

(forall m' co' cb' j2' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6',
t_co ts <= co' < pf_len pf -> nth_error payload (Z.to_nat co') = Some cb' ->
is_ws (bv_unsigned cb') = false ->
PE_INV HIx pf q LB0 payload me lo m' md A
(TST (t_depth ts) (lupd (t_levels ts) (t_depth ts) (TL (tl_ss l) (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)))
co' (t_pb ts) (t_pbs ts)
(TS (ts_isd (t_x ts)) (ts_stpos (t_x ts)) (Z_to_bv 64 co') (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))
(t_obj ts) (t_objs ts) (t_objbs ts)) cb' j1 j2' utf sv errv ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_REDO co' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F fc m') md) T) ->

(forall m' md' A' pbs' errv' co' cb' j2' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F' fc',
t_co ts <= co' < pf_len pf -> nth_error payload (Z.to_nat co') = Some cb' -> bv_unsigned cb' = 47 ->
PE_INV HIx pf q LB0 payload me lo m' md' A'
(TST (t_depth ts) (lupd (t_levels ts) (t_depth ts) (TL ST_comment_start (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)))
co' (t_pb ts) pbs'
(TS (ts_isd (t_x ts)) (ts_stpos (t_x ts)) (Z_to_bv 64 co') (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))
(t_obj ts) (t_objs ts) (t_objbs ts)) cb' j1 j2' utf sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_BREAK co' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F' fc' m') md') T) ->

(forall m' md' A' pbs' errv' co' cb' j2' x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F' fc',
t_co ts <= co' < pf_len pf -> nth_error payload (Z.to_nat co') = Some cb' -> bv_unsigned cb' = 47 ->
PE_INV HIx pf q LB0 payload me lo m' md' A'
(TST (t_depth ts) (t_levels ts) co' (t_pb ts) pbs'
(TS (ts_isd (t_x ts)) (ts_stpos (t_x ts)) (Z_to_bv 64 co') (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))
(t_obj ts) (t_objs ts) (t_objbs ts)) cb' j1 j2' utf sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_ERR co' x1' gp' t0' t1' t2' (Z_to_bv 64 16) a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F' fc' m') md') T) ->

(forall m' (e : word) cb' j2' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6',
nth_error payload (Z.to_nat (pf_len pf - 1)) = Some cb' -> is_ws (bv_unsigned cb') = true ->
PE_INV HIx pf q LB0 payload me lo m' md A
(TST (t_depth ts) (t_levels ts) (pf_len pf) (t_pb ts) (t_pbs ts)
(TS (ts_isd (t_x ts)) (ts_stpos (t_x ts)) (Z_to_bv 64 (pf_len pf)) e (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))
(t_obj ts) (t_objs ts) (t_objbs ts)) cb' j1 j2' utf sv errv ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_OUT (pf_len pf - 1) x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F fc m') md) T) ->

(forall m' co' cb' j2' x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6',
t_co ts <= co' <= pf_len pf ->
PE_INV HIx pf q LB0 payload me lo m' md A
(TST (t_depth ts) (t_levels ts) co' (t_pb ts) (t_pbs ts)
(TS (ts_isd (t_x ts)) (ts_stpos (t_x ts)) (Z_to_bv 64 co') (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))
(t_obj ts) (t_objs ts) (t_objbs ts)) cb' j1 j2' utf sv errv ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_ERR co' x1' gp' t0' t1' t2' (Z_to_bv 64 14) a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F fc m') md) T) ->
realizes rsegs (mkCfg (pe_ms rsegs pf (pe_jt ST_eatws) (t_co ts) x1 gp t0 t1 t2
(Z_to_bv 64 0) (Z_to_bv 64 (tl_st l)) (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) a3 a4 a5 a6 a7
(Z_to_bv 64 q) s6 s7 s8 (Z_to_bv 64 (Z.of_nat (t_depth ts))) s10 t3 t4 t5 t6 F fc m) md) T.
Proof.
intros until fc. intros STC INV CSTR Hl Hst Hco Hc Kredo Kbreak Kerr16 Kout Kerr14.
pose proof STC as (LO & LOS & SPA & HT & SP0 & LEN & SB0 & SBL).
pose proof INV as [CORE REST].
pose proof CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof (heap_model_ok _ _ _ _ _ _ (proj1 REST)) as MOK.
pose proof (bv_unsigned_in_range 8 cb) as CBR; unfold bv_modulus in CBR; cbn in CBR.
revert INV Kredo Kbreak Kerr16 Kout Kerr14.
destruct ts as [depth levels co pb pbs xx obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct xx as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl_]; pe_gen fl_; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
intros INV Kredo Kbreak Kerr16 Kout Kerr14.
unfold pe_frame in FR. unfold pe_ms. cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl]. unfold_consts.
clear TOK PB TSK REST CORE.
apply rz_evt; [exact MOK|].
tk3_walk 0x223bc ltac:(try norm_sx32).
try change (zxb cb) with (Z_to_bv 64 (bv_unsigned cb)).
rewrite (unsigned_lit (bv_unsigned cb)) by lia. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. change (2 ^ 8) with 256. rewrite (Z.mod_small (bv_unsigned cb) 256) by lia.
apply evt_RZ_done.
eapply (eatws_loop (Z.to_nat (len - co)) (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo m md A
(TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) l cb);
[exact STC | exact INV | exact CSTR | exact Hl | exact Hst | exact Hco | exact Hc | cbn; lia | | | exact Kout | exact Kerr14].
- cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_len pf_md pf_mxd pf_fl].
intros m' co' cb' j2' x1' gp' t0' t1' t2' a1' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' R' Hc' WS' INV'.
eapply (eatws_pop (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo m' md A (TST depth levels co' pb pbs (TS isd stpos (Z_to_bv 64 co') err ucs high quote) obj objs objbs) l cb');
[exact STC | exact INV' | exact Hl | exact Hst |].
unfold ts_ws. cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs ts_isd ts_stpos ts_err ts_ucs ts_high ts_quote pf_mxd]. rewrite Hl.
intros. eapply Kredo; eassumption.
- cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_len pf_md pf_mxd pf_fl].
intros m' co' cb' j2' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' R' Hc' E47 INV'.
eapply (eatws_slash (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo m' md A (TST depth levels co' pb pbs (TS isd stpos (Z_to_bv 64 co') err ucs high quote) obj objs objbs) l cb');
[exact STC | exact INV' | exact Hl | exact Hst | |].
+ unfold ts_ws. cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs ts_isd ts_stpos ts_err ts_ucs ts_high ts_quote pf_mxd]. rewrite Hl.
intros. eapply Kbreak; eassumption.
+ unfold ts_set_pbs. cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs ts_isd ts_stpos ts_err ts_ucs ts_high ts_quote pf_mxd].
intros. eapply Kerr16; eassumption.
Qed.

End PeEatws.

End RC__1.
End Mq2.

Module Mq3.

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
Import UG8z UIsM.Mq2.
Import UBpZ UT7i Uv6q.
Import UzWc.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.
Import Q6q3.
Import TopUbTac Tk1Tac Tk3Tac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition UTF8REP_ADDR : Z := 0x66a28.
Definition utf8rep : list byte := [Z_to_bv 8 239; Z_to_bv 8 191; Z_to_bv 8 189].

#[using="Type"] Lemma lvl_mode_esc_same : forall st st' ss,
zin st esc_states = true -> zin st' esc_states = true -> 0 <= ss <= 26 -> lvl_mode st' ss = lvl_mode st ss.
Proof.
intros st st' ss H H' R.
assert (C : forall x, zin x esc_states = true -> x = 9 \/ x = 10 \/ x = 11 \/ x = 12).
{ intros x Hx. unfold zin, esc_states in Hx. cbn in Hx. rewrite !Bool.orb_true_iff in Hx. rewrite !Z.eqb_eq in Hx. intuition lia. }
destruct (C st H) as [->|[->|[->| ->]]]; destruct (C st' H') as [->|[->|[->| ->]]]; enum_z R ss; vm_compute; reflexivity.
Qed.

#[using="Type"] Lemma tok_join40 : forall {mxd fl} m tk pb d q isd stpos choff err ucs high quote,
rw_cells rsegs m tk (tok_cells_g mxd fl pb d q (TS isd stpos choff err ucs high quote)) ->
rw_cells rsegs m tk [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 pb); C4 (Z_to_bv 64 mxd); C4 (Z_to_bv 64 d); C4 isd; C4 stpos; C4 choff; C4 err;
CB 8 (le4 ucs ++ le4 high); C1 quote; CB 7 (repeat (Z_to_bv 8 0) 7); C8 (Z_to_bv 64 q); C4 (Z_to_bv 64 fl); C4 (Z_to_bv 64 0)].
Proof. intros. eapply rw_cells_recast; [exact H | cbn; repeat split; reflexivity | reflexivity | reflexivity]. Qed.
#[using="Type"] Lemma tok_split40 : forall {mxd fl} m tk pb d q isd stpos choff err quote,
rw_cells rsegs m tk [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 pb); C4 (Z_to_bv 64 mxd); C4 (Z_to_bv 64 d); C4 isd; C4 stpos; C4 choff; C4 err;
C8 (Z_to_bv 64 0); C1 quote; CB 7 (repeat (Z_to_bv 8 0) 7); C8 (Z_to_bv 64 q); C4 (Z_to_bv 64 fl); C4 (Z_to_bv 64 0)] ->
rw_cells rsegs m tk (tok_cells_g mxd fl pb d q (TS isd stpos choff err (Z_to_bv 64 0) (Z_to_bv 64 0) quote)).
Proof. intros. eapply rw_cells_recast; [exact H | cbn; repeat split; reflexivity | reflexivity | reflexivity]. Qed.

Section PeNeedesc.
Variable HIx : heap_iface S4L.
Hypothesis MEMMOVE : memmove_stmt.

Definition ts_esc_pop (ts : tstate) (st' : Z) (pbs' : list blk) : tstate :=
match nth_error (t_levels ts) (t_depth ts) with
| Some l => TST (t_depth ts) (lupd (t_levels ts) (t_depth ts) (TL st' (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)))
(t_co ts) (t_pb ts) pbs'
(TS (ts_isd (t_x ts)) (Z_to_bv 64 0) (ts_choff (t_x ts)) (ts_err (t_x ts)) (Z_to_bv 64 0) (Z_to_bv 64 0) (ts_quote (t_x ts)))
(t_obj ts) (t_objs ts) (t_objbs ts)
| None => ts
end.

#[using="MEMMOVE"] Lemma seg_needesc :
forall (pf : pe_fix) (q : Z) (LB0 : list blk) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (ts : tstate) (l : tlevel)
(cb : byte) (j1 j2 utf : list byte) (sv : pe_saved) (errv : word) (T : TSet)
(x1 gp t0 t1 t2 a0 a3 a4 a5 a6 a7 s6 s7 s8 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC HIx pf lo ->
PE_INV HIx pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_esc_need_escape ->
t_co ts < pf_len pf ->
bytes_at rsegs me UTF8REP_ADDR utf8rep ->

(forall c hn, lvl_mode (tl_st l) (tl_ss l) = Some (c, hn) -> lvl_mode (tl_ss l) (tl_ss l) = Some (c, hn)) ->

(forall m' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6',
bv_unsigned cb = 92 ->
PE_INV HIx pf q LB0 payload me lo m' md A (ts_set_level ts (TL ST_esc_need_u (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) cb j1 j2 utf sv errv ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_BREAK2 (t_co ts) x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F fc m') md) T) ->

(forall m' md' A' pbs' errv' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F' fc',
bv_unsigned cb <> 92 ->
PE_INV HIx pf q LB0 payload me lo m' md' A' (ts_esc_pop ts (tl_ss l) pbs') cb j1 j2 utf sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_REDO (t_co ts) x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F' fc' m') md') T) ->

(forall m' md' A' pbs' errv' x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F' fc',
bv_unsigned cb <> 92 ->
PE_INV HIx pf q LB0 payload me lo m' md' A' (ts_set_pbs ts pbs') cb j1 j2 utf sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_ERR (t_co ts) x1' gp' t0' t1' t2' (Z_to_bv 64 16) a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F' fc' m') md') T) ->
realizes rsegs (mkCfg (pe_ms rsegs pf (pe_jt ST_esc_need_escape) (t_co ts) x1 gp t0 t1 t2
a0 (Z_to_bv 64 (tl_st l)) (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) a3 a4 a5 a6 a7
(Z_to_bv 64 q) s6 s7 s8 (Z_to_bv 64 (Z.of_nat (t_depth ts))) s10 t3 t4 t5 t6 F fc m) md) T.
Proof.
intros until fc. intros STC INV Hl Hst Hco UTF HMODE Kbreak Kredo Kerr16.
pose proof STC as (LO & LOS & SPA & HT & SP0 & LEN & SB0 & SBL).
destruct INV as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof REST as (HP & LV & _ & _ & _ & _ & _ & _ & HPR0 & MDV0 & JCG0).
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl_]; pe_gen fl_; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
unfold ts_esc_pop in Kredo. cbn [t_levels t_depth t_co t_pb t_x t_obj t_objs t_objbs ts_isd ts_choff ts_err ts_quote] in Kredo. rewrite Hl in Kredo.
pose proof TOK as TOK0. unfold tok_cells, tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK. unfold pe_frame in FR. unfold pe_ms in *. cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
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
assert (Hbal : bse mod 16 = 0) by (rewrite Hbse; Z.div_mod_to_equations; lia).
assert (HbseR : q <= bse /\ bse + 32 <= q + (32 * mxd)) by (subst bse; lia).
pose proof (munch_refl [(bse, bse + 32)] m) as MU.
pose proof (bv_unsigned_in_range 8 cb) as CBR; unfold bv_modulus in CBR; cbn in CBR.
assert (ESC11 : zin ST_esc_need_escape esc_states = true) by reflexivity.
stash PB. stash REST. stash TSK. stash Himg_t. stash Himg_q. clear LV.
apply rz_evt; [exact MOK|]. rewrite Hst. unfold ST_esc_need_escape. cbn [pe_jt].
replace (q + 32 * Z.of_nat depth) with bse by lia.
destruct (Z.eq_dec (bv_unsigned cb) 92) as [C92 | N92].
-
tk3_walk 0x23d14 ltac:(try norm_sx32; try unfold zxb; try rewrite (unsigned_lit (bv_unsigned cb)) by lia; try replace (q + Z.of_nat depth * 32) with bse by lia).
unstash PB. unstash REST. unstash TSK.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
match goal with L5 : rw_cells rsegs mc bse _ |- _ =>
set (l1 := TL ST_esc_need_u (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l));
assert (HW : Forall (pe_wtq (PEF tk oldl newl len lenr sb spf pmd mxd fl) q) [(bse, bse + 32)]) by (apply Forall_cons; [right; cbn [fst snd pf_mxd]; lia | apply Forall_nil]);
assert (TSK1 : tstack rsegs mc q (lupd levels depth l1))
by (subst bse; eapply (tstack_put rsegs m _ q levels depth l1 []); [exact TSK | lia | exact MU | exact WM | intros; exact I | exact L5]);
assert (PB1 : pbuf rsegs mc pbs pb)
by (eapply (pbuf_wtq HIx) with (ts := ts0); [exact STC | exact (proj1 REST) | exact PB | exact MU | exact WM | exact HW]);
assert (REST1 : PE_REST HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo mc md A ts0 errv)
by (eapply (PE_REST_private_write HIx) with (ts := ts0) in REST; [exact REST | exact STC | exact MU | exact WM | assumption | apply pe_wtq_private; exact HW]);
subst bse; apply evt_RZ_done; apply (Kbreak mc); [exact C92 |]
end end.
split.
+ unfold PE_CORE, ts_set_level; cbn. split; [rewrite lupd_length; exact LEN32|]. split; [exact D32|]. split; [lia|]. split; [reflexivity|].
split; [assumption|]. split; [exact PB1|]. split; [exact Hpb|]. split; [exact TSK1 | assumption].
+ destruct REST1 as (HP' & LV' & OBJ' & ST' & ERR' & STR' & PLEN' & SBin' & HPR' & MDV' & JCG').
unfold ts_set_level; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs].
split.
{ match goal with |- HEAP _ _ _ ?L _ _ => replace L with (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0); [exact HP' |] end.
unfold pe_blocks, tstate_blocks, ts0; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs].
match goal with |- context [map lvl_blocks (lupd ?lv ?d ?xx)] => rewrite (map_lupd_same lvl_blocks lv d xx l Hl eq_refl) end. reflexivity. }
split; [| split; [| split; [exact ST' | split; [exact ERR' | split; [exact STR' | split; [exact PLEN' | split; [exact SBin' | split; [exact HPR' | split; [exact MDV' | exact JCG']]]]]]]]].
* intros i li Hli. unfold ts0 in Hli; cbn [t_levels t_depth] in Hli. unfold ts0; cbn [t_depth].
destruct (PeanoNat.Nat.eq_dec i depth) as [-> | NE].
-- rewrite nth_error_lupd_eq in Hli by lia. injection Hli as <-.
eapply lvl_cur_restate with (c' := c0); [exact (LV' depth l Hl) | exact Hmode | | unfold ST_esc_need_u; lia | exact SS26 | left; reflexivity].
rewrite <- Hmode. apply lvl_mode_esc_same; [rewrite Hst; reflexivity | reflexivity | exact SS26].
-- rewrite nth_error_lupd_neq in Hli by congruence. exact (LV' i li Hli).
* revert OBJ'. unfold cur_st, ts0. cbn [t_levels t_depth t_objs t_objbs t_obj]. rewrite nth_error_lupd_eq by lia. cbn [tl_st].
rewrite Hl, Hst. cbn. intros OBJ'; exact OBJ'.
-
tk3_walk 0x241a4 ltac:(try norm_sx32; try unfold zxb; try rewrite (unsigned_lit (bv_unsigned cb)) by lia; try replace (q + Z.of_nat depth * 32) with bse by lia).
unstash PB. unstash REST. clear MU.
pose proof PB as (buf & bpos & cap & pre & post & Epbs & Lpre & CORE1).
pose proof HP as HP1. unfold pe_blocks, tstate_blocks, ts0 in HP1. cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_tk pf_md pf_mxd pf_fl] in HP1.
rewrite Epbs in HP1. cbn [app] in HP1.
pose proof (heap_blk S4L HIx _ _ _ _ buf cap HP1 ltac:(right; left; reflexivity)) as (_ & _ & _ & Hbufhi & _). unfold alloc_ceiling, sp_window_lo, stack_max_size in Hbufhi.
pose proof (heap_blk_img S4L HIx _ _ _ _ buf cap HP1 ltac:(right; left; reflexivity)) as Himg_b. cbn [hl_img_lo hl_img_hi S4L] in Himg_b.
assert (SRC : bytes_at rsegs m UTF8REP_ADDR utf8rep).
{ eapply (heap_presx_bytes_at S4L); [exact HPR0 | exact UTF |]. right; left. intros a Ha. cbn in Ha. cbn. unfold s4_client_static, s4_volatile. unfold UTF8REP_ADDR in Ha. lia. }
unfold UTF8REP_ADDR in SRC.
pose proof REST as (_ & _ & _ & ST1 & ERR1 & _).
apply evt_RZ_done.
eapply (memappend_cps HIx MEMMOVE) with (lo := lo) (b := 0x66a28) (src := utf8rep) (n := 3);
[ exact HP1 | exact CORE1 | lia | exact SRC | reflexivity
| left; right; left; intros a Ha; cbn; unfold s4_client_static; rewrite ?unsigned_lit in Ha by lia; lia | lia | lia | clear -Himg_b; lia | .. ]; try alloc_side.
all: try clear Himg_b.
all: try (rewrite ?unsigned_lit by lia; first [exact ST1 | exact ERR1]).
all: try (rewrite ?unsigned_lit by lia; unfold PE_FRAME in *; clia).
intros ms2 md2 (m2 & A2 & r & errv2 & buf' & cap' & RS2 & VM2 & ST2 & HPR2 & ERR2 & HP2 & OUT2).
destruct RS2 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F2 & fc2 & -> & FS2 & FRM2).
cbn [hl_segs hl_tp S4L] in *. rewrite ?(unsigned_lit spf) in ST2 by lia. rewrite ?(unsigned_lit spf) in HPR2 by lia.
set (pbs2 := [(pb, 16); (buf', cap')]).
set (ts2 := TST depth levels co pb pbs2 (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs).
assert (INq2 : In (q, (32 * mxd)) ((objbs ++ concat (map lvl_blocks levels)) ++ (tk, 72) :: (q, (32 * mxd)) :: LB0))
by (apply in_or_app; right; right; left; reflexivity).
assert (INtk2 : In (tk, 72) ((objbs ++ concat (map lvl_blocks levels)) ++ (tk, 72) :: (q, (32 * mxd)) :: LB0))
by (apply in_or_app; right; left; reflexivity).
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in TOK0; [| eapply client_range_block; [exact INtk2 | lia | cbn; lia]]. cbn [hl_segs S4L] in TOK0.
clear TOK.
unstash TSK. apply (tstack_pres_g S4L _ _ _ _ _ _ HPR2 INq2) in TSK; [| exact LEN32].
assert (REST2 : PE_REST HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo m2 md2 A2 ts2 errv2).
{ eapply (PE_REST_call_pb HIx) with (ts := ts0) (LBc := (objbs ++ concat (map lvl_blocks levels)) ++ (tk, 72) :: (q, (32 * mxd)) :: LB0);
[exact STC | exact REST | exact VM2 | exact HPR2 | unfold ts0; cbn [t_objbs t_levels]; intros b Hb; apply in_or_app;
apply in_app_or in Hb; destruct Hb as [Hb|Hb]; [left; apply in_or_app; left; exact Hb | apply in_app_or in Hb; destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; exact Hb | right; right; right; exact Hb]]
| unfold pe_blocks, tstate_blocks; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_tk pf_md pf_mxd pf_fl]; exact HP2
| exact ST2 | exact ERR2]. }
assert (PBany : pbuf rsegs m2 pbs2 pb).
{ destruct OUT2 as [[_ PBS] | (_ & -> & -> & PC)]; [exact PBS|].
exists buf, bpos, cap, pre, post. split; [reflexivity|]. split; [exact Lpre | exact PC]. }
assert (INV2 : PE_INV HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo m2 md2 A2 ts2 cb j1 j2 utf sv errv2).
{ split; [| exact REST2]. unfold PE_CORE, ts2; cbn. split; [exact LEN32|]. split; [exact D32|]. split; [lia|]. split; [reflexivity|].
split; [exact TOK0|]. split; [exact PBany|]. split; [exact Hpb|]. split; [exact TSK | exact FR]. }
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2.
pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI2. cbn [hl_segs S4L] in MI2.
clear HP1 HP2 REST CORE1 SRC ST1 ERR1 MI PB HP MOK WM.
reenter MOK2.
destruct OUT2 as [[-> _] | (-> & -> & -> & _)].
2:{
replace (Z_to_bv 64 (2^64 - 1)) with (Z_to_bv 64 (-1)) by (apply bv_eq; vm_compute; reflexivity).
tk3_walk 0x23ea4 idtac. apply evt_RZ_done. eapply Kerr16; [exact N92 | | exact FS2 | exact FRM2].
unfold ts2, pbs2 in INV2. exact INV2. }

pose proof REST2 as (HP2 & LV2 & _). destruct INV2 as [CORE2 REST2']. clear REST2'. pose proof CORE2 as (_ & _ & _ & _ & _ & PB2 & _).
pose proof (TSK depth l Hl) as Ld2. cbn [hl_segs S4L] in Ld2. unfold srec_cells in Ld2. rewrite <- Hbse in Ld2.
pose proof (tok_join40 _ _ _ _ _ _ _ _ _ _ _ _ TOK0) as TOKj. clear TOK0.
pose proof (munch_refl [(tk + 28, tk + 32); (tk + 40, tk + 48); (bse, bse + 32)] m2) as MU. pose proof (wmono_refl rsegs m2) as WM.
stash PB2. stash REST2. stash TSK. clear LV2 CORE2.
tk3_walk 0x21e14 ltac:(try norm_sx32; try unfold zxb; try rewrite (unsigned_lit (bv_unsigned cb)) by lia; try replace (q + Z.of_nat depth * 32) with bse by lia).
unstash PB2. unstash REST2. unstash TSK.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
match goal with TK : rw_cells rsegs mc tk _ |- _ => pose proof (tok_split40 _ _ _ _ _ _ _ _ _ _ TK) as TOK3 end
end.
set (l1 := TL (tl_ss l) (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)).
set (ts3 := TST depth (lupd levels depth l1) co pb pbs2 (TS isd (Z_to_bv 64 0) (Z_to_bv 64 co) err (Z_to_bv 64 0) (Z_to_bv 64 0) quote) obj objs objbs).
assert (HW : Forall (pe_wtq (PEF tk oldl newl len lenr sb spf pmd mxd fl) q) [(tk + 28, tk + 32); (tk + 40, tk + 48); (bse, bse + 32)]).
{ repeat apply Forall_cons; try apply Forall_nil; [left; left; cbn [pf_tk fst snd pf_md pf_mxd pf_fl]; lia | left; left; cbn [pf_tk fst snd pf_md pf_mxd pf_fl]; lia | right; cbn [fst snd pf_mxd]; lia]. }
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (TSK3 : tstack rsegs mc q (lupd levels depth l1))
by (subst bse; eapply (tstack_put rsegs m2 _ q levels depth l1 [(tk + 28, tk + 32); (tk + 40, tk + 48)]);
[exact TSK | lia | eapply munch_weaken; [| exact MU]; unfold sub_fp; cbn [outside]; intros; lia | exact WM
| intros j Hj Hne; cbn [disjoint_from fst snd pf_mxd]; lia
| match goal with L5 : rw_cells rsegs mc (q + 32 * Z.of_nat depth) _ |- _ => exact L5 end]);
assert (PB3 : pbuf rsegs mc pbs2 pb)
by (eapply (pbuf_wtq HIx) with (ts := ts2); [exact STC | exact (proj1 REST2) | exact PB2 | exact MU | exact WM | exact HW]);
assert (REST3 : PE_REST HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo mc md2 A2 ts2 errv2)
by (eapply (PE_REST_private_write HIx) with (ts := ts2) in REST2; [exact REST2 | exact STC | exact MU | exact WM | assumption | apply pe_wtq_private; exact HW]);
apply evt_RZ_done; apply (Kredo mc md2 A2 pbs2 errv2); [exact N92 | | exact FS2 | exact FRM2]
end.
split.
+ unfold PE_CORE; cbn. split; [rewrite lupd_length; exact LEN32|]. split; [exact D32|]. split; [lia|]. split; [reflexivity|].
split; [exact TOK3|]. split; [exact PB3|]. split; [exact Hpb|]. split; [exact TSK3 | assumption].
+ destruct REST3 as (HP' & LV' & OBJ' & ST' & ERR' & STR' & PLEN' & SBin' & HPR' & MDV' & JCG').
cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs].
split.
{ match goal with |- HEAP _ _ _ ?L _ _ => replace L with (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts2); [exact HP' |] end.
unfold pe_blocks, tstate_blocks, ts2; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs].
match goal with |- context [map lvl_blocks (lupd ?lv ?d ?xx)] => rewrite (map_lupd_same lvl_blocks lv d xx l Hl eq_refl) end. reflexivity. }
split; [| split; [| split; [exact ST' | split; [exact ERR' | split; [exact STR' | split; [exact PLEN' | split; [exact SBin' | split; [exact HPR' | split; [exact MDV' | exact JCG']]]]]]]]].
* intros i li Hli. unfold ts2 in Hli; cbn [t_levels t_depth] in Hli. unfold ts2; cbn [t_depth].
destruct (PeanoNat.Nat.eq_dec i depth) as [-> | NE].
-- rewrite nth_error_lupd_eq in Hli by lia. injection Hli as <-.
eapply lvl_cur_restate with (c' := c0); [exact (LV' depth l Hl) | exact Hmode | apply HMODE; exact Hmode | exact SS26 | exact SS26 | left; reflexivity].
-- rewrite nth_error_lupd_neq in Hli by congruence. exact (LV' i li Hli).
* revert OBJ'. unfold cur_st, ts2. cbn [t_levels t_depth t_objs t_objbs t_obj]. rewrite nth_error_lupd_eq by lia. cbn [tl_st].
rewrite Hl, Hst.

assert (Ez : zin (tl_ss l) [ST_array_add; ST_ovadd] = false).
{ destruct (zin (tl_ss l) [ST_array_add; ST_ovadd]) eqn:E; [| reflexivity]. exfalso.
revert Hmode E. rewrite Hst. clear. intros Hmode E.
assert (R : tl_ss l = 16 \/ tl_ss l = 22).
{ unfold zin in E. cbn in E. rewrite !Bool.orb_true_iff in E. rewrite !Z.eqb_eq in E. unfold ST_array_add, ST_ovadd in E. intuition lia. }
destruct R as [E'|E']; rewrite E' in Hmode; vm_compute in Hmode; discriminate Hmode. }
rewrite Ez. cbn. intros OBJ'; exact OBJ'.
Qed.
End PeNeedesc.

End RC__1.
End Mq3.
From Stdlib Require NArith.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UhHQ U5Ki.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB.Tk1 Require Tk1Reset.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup.
Import UEQM.
Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0.
Import UC8c.Mq0.
Import Qsw7 QJjn.
Import UPZI.Mq4 UG8z.
Import UhHQ U5Ki Tk1Reset.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.
Import Q6q3.
Import TopUbTac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section PeOutLoop.
Variable HIx : heap_iface S4L.
Variables (mxd fl : Z).
Hypothesis MXB : 1 <= mxd <= 32.
Notation HEAPx := (HEAP S4L HIx).
Hypothesis PUT : put_stmt_P HIx.

Definition peout_loop_pc : Z := 0x23fd4.

Definition po_frame (m : word -> option byte) (sp : Z) (obj : Z) (cbq : byte) (j1 j2 utf : list byte) (sv : pe_saved) : Prop :=
pe_frame rsegs m sp obj cbq j1 j2 utf sv.

Definition po_body_post (x2 gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(md : Model) (REST LB0 P : list blk) (SP : Z) (me mpre : word -> option byte) (lo : Z) (errv : word)
(q r pb depth : Z) (x : tscal) (levels : list tlevel) (i : nat) (obj : Z) (cbq : byte) (j1 j2 utf : list byte) (sv : pe_saved)
(ms' : machine_state) (md' : Model) : Prop :=
exists m' (A' : AS S4L HIx) F' fc' x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
ms' = MS (mkR x1 x2 gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F' (Z_to_bv 64 0x23fe0) fc' None m' (seg_rom rsegs) /\
fsaved F F' /\ (frm0 fc -> frm0 fc') /\
model_vm_only md md' /\
HEAPx A' REST m' md' /\
tstack rsegs m' q (lupd levels i lvl_reset) /\
rw_cells rsegs m' r (tok_cells_g mxd fl pb depth q x) /\
po_frame m' SP obj cbq j1 j2 utf sv /\
stk rsegs m' lo SP /\
heap_pres S4L LB0 (SP + 144) me m' /\
rw_cells rsegs m' (0x77c00 - 164) [C4 errv] /\
agree_on rsegs P mpre m'.

#[using="MXB PUT"] Lemma peout_body :
forall (i : nat) (x1 gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m me : word -> option byte) (md : Model) (T : TSet)
(A : AS S4L HIx) (REST LB0 P : list blk) (SP lo : Z) (errv : word)
(q r pb depth : Z) (x : tscal) (levels : list tlevel) (l : tlevel) (obj : Z) (cbq : byte) (j1 j2 utf : list byte) (sv : pe_saved),
nth_error levels i = Some l -> (i < Z.to_nat mxd)%nat -> length levels = Z.to_nat mxd ->
HEAPx A (lvl_blocks l ++ REST) m md ->
REST = P ++ (r, 72) :: (q, (32 * mxd)) :: LB0 ->
lvl_ok rsegs S4F m l ->
tstack rsegs m q levels ->
rw_cells rsegs m r (tok_cells_g mxd fl pb depth q x) ->
po_frame m SP obj cbq j1 j2 utf sv ->
stk rsegs m lo SP -> alloc_ceiling <= lo -> lo <= SP - RESET_STK ->
SP mod 16 = 0 -> SP + 144 <= hi_top S4L HIx -> 0 <= SP < 2^64 ->
heap_pres S4L LB0 (SP + 144) me m ->
rw_cells rsegs m (0x77c00 - 164) [C4 errv] ->
tp = Z_to_bv 64 0x77c00 ->
(forall ms' md', po_body_post (Z_to_bv 64 SP) gp tp (Z_to_bv 64 r) (Z_to_bv 64 (Z.of_nat i)) s2 (Z_to_bv 64 (-1)) s4 s5 s6 s7 s8 s9 s10 s11
F fc md REST LB0 P SP me m lo errv q r pb depth x levels i obj cbq j1 j2 utf sv ms' md' ->
realizes rsegs (mkCfg ms' md') T) ->
realizes rsegs (mkCfg (MS (mkR x1 (Z_to_bv 64 SP) gp tp t0 t1 t2 (Z_to_bv 64 r) (Z_to_bv 64 (Z.of_nat i))
a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 (-1)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 peout_loop_pc) fc None m (seg_rom rsegs)) md) T.
Proof.
intros until sv. intros Hl Hi LEN HP EREST LOK TS BLK FR ST LO LOS SPA HT SPR HPR ERR TP K.
subst tp.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
apply rz_evt; [exact MOK|]. unfold peout_loop_pc.
bstep. bstep. bstep.
apply evt_RZ_done.
destruct LOK as [JO NM].
eapply (reset_level_cps HIx PUT i) with (l := l) (levels := levels) (P := P) (LB0 := LB0) (REST := REST) (lo := lo) (errv := errv)
(q := q) (r := r) (pb := pb) (depth := depth) (mxd := mxd) (fl := fl) (x := x) (rc := 1) (me := m);
[ exact Hl | lia | exact MXB | exact LEN | exact HP | exact EREST
| unfold put_pre; destruct (tl_cs l) as [s'|]; [destruct JO as [Hp J]; split; [exact Hp | split; [lia | exact J]] | exact JO]
| exact NM | exact TS | exact BLK
| rewrite unsigned_lit by lia; exact ST | exact LO | rewrite unsigned_lit by lia; exact LOS
| rewrite unsigned_lit by lia; exact SPA | rewrite unsigned_lit by lia; lia
| apply heap_pres_refl | exact ERR | rewrite unsigned_lit by lia; reflexivity | ].
intros ms2 md2 (m2 & A2 & rv & RS2 & VM2 & OUT2 & TS2 & TOK2 & ST2 & HPR2 & ERR2 & AG2).
destruct RS2 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F2 & fc2 & -> & FS2 & FRM2).
rewrite ?unsigned_lit in ST2 by lia. rewrite ?unsigned_lit in HPR2 by lia.
lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?n)] => replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia | reflexivity]) end.
apply K. unfold po_body_post.
exists m2, A2, F2, fc2. do 16 eexists.
split; [reflexivity|]. split; [exact FS2|]. split; [exact FRM2|]. split; [exact VM2|].
split; [destruct OUT2 as [(_ & H) | (s' & _ & Hrc & _)]; [exact H | exfalso; lia]|].
split; [exact TS2|]. split; [exact TOK2|].
split; [unfold po_frame, pe_frame in FR |- *; eapply (heap_pres_rw_cells S4L); [exact HPR2 | exact FR | left; cbn; lia]|].
split; [exact ST2|].
split; [eapply heap_pres_trans; [exact HPR | eapply heap_pres_weaken; [exact HPR2 | lia | intros b Hb; exact Hb]]|].
split; [exact ERR2 | exact AG2].
Qed.
End PeOutLoop.

Section PeOutLoop2.
Variable HIx : heap_iface S4L.
Variables (mxd fl : Z).
Hypothesis MXB : 1 <= mxd <= 32.
Notation HEAPx := (HEAP S4L HIx).
Hypothesis PUT : put_stmt_P HIx.

Definition po_loop_post (x2 gp tp s0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(md : Model) (BASE LB0 PBS : list blk) (SP : Z) (me mpre : word -> option byte) (lo : Z) (errv : word)
(q r pb depth : Z) (x : tscal) (levels : list tlevel) (i : nat) (obj : Z) (cbq : byte) (j1 j2 utf : list byte) (sv : pe_saved)
(ms' : machine_state) (md' : Model) : Prop :=
exists m' (A' : AS S4L HIx) F' fc' levels' x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s1',
ms' = MS (mkR x1 x2 gp tp t0 t1 t2 s0 s1' a0 a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F' (Z_to_bv 64 0x23fe8) fc' None m' (seg_rom rsegs) /\
fsaved F F' /\ (frm0 fc -> frm0 fc') /\
model_vm_only md md' /\
HEAPx A' BASE m' md' /\
length levels' = Z.to_nat mxd /\
(forall j, (j <= i)%nat -> nth_error levels' j = Some lvl_reset) /\
(forall j, (i < j)%nat -> nth_error levels' j = nth_error levels j) /\
tstack rsegs m' q levels' /\
rw_cells rsegs m' r (tok_cells_g mxd fl pb depth q x) /\
po_frame m' SP obj cbq j1 j2 utf sv /\
stk rsegs m' lo SP /\
heap_pres S4L LB0 (SP + 144) me m' /\
rw_cells rsegs m' (0x77c00 - 164) [C4 errv] /\
agree_on rsegs PBS mpre m'.

#[using="MXB PUT"] Lemma peout_loop :
forall (i : nat) (x1 gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m me : word -> option byte) (md : Model) (T : TSet)
(A : AS S4L HIx) (PBS LB0 : list blk) (SP lo : Z) (errv : word)
(q r pb depth : Z) (x : tscal) (levels : list tlevel) (obj : Z) (cbq : byte) (j1 j2 utf : list byte) (sv : pe_saved),
(i < Z.to_nat mxd)%nat -> length levels = Z.to_nat mxd ->
HEAPx A (lvblocks levels (S i) ++ PBS ++ (r, 72) :: (q, (32 * mxd)) :: LB0) m md ->
(forall j l, nth_error levels j = Some l -> (j <= i)%nat -> lvl_ok rsegs S4F m l) ->
tstack rsegs m q levels ->
rw_cells rsegs m r (tok_cells_g mxd fl pb depth q x) ->
po_frame m SP obj cbq j1 j2 utf sv ->
stk rsegs m lo SP -> alloc_ceiling <= lo -> lo <= SP - RESET_STK ->
SP mod 16 = 0 -> SP + 144 <= hi_top S4L HIx -> 0 <= SP < 2^64 ->
heap_pres S4L LB0 (SP + 144) me m ->
rw_cells rsegs m (0x77c00 - 164) [C4 errv] ->
tp = Z_to_bv 64 0x77c00 ->
(forall ms' md', po_loop_post (Z_to_bv 64 SP) gp tp (Z_to_bv 64 r) s2 (Z_to_bv 64 (-1)) s4 s5 s6 s7 s8 s9 s10 s11
F fc md (PBS ++ (r, 72) :: (q, (32 * mxd)) :: LB0) LB0 PBS SP me m lo errv q r pb depth x levels i obj cbq j1 j2 utf sv ms' md' ->
realizes rsegs (mkCfg ms' md') T) ->
realizes rsegs (mkCfg (MS (mkR x1 (Z_to_bv 64 SP) gp tp t0 t1 t2 (Z_to_bv 64 r) (Z_to_bv 64 (Z.of_nat i))
a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 (-1)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 peout_loop_pc) fc None m (seg_rom rsegs)) md) T.
Proof.
induction i as [|i IH]; intros until sv; intros Hi LEN HP LOK TS BLK FR ST LO LOS SPA HT SPR HPR ERR TP K.
-
destruct (nth_error levels 0) as [l|] eqn:Hl; [| apply nth_error_None in Hl; lia].
rewrite (lvblocks_S _ _ _ Hl) in HP. rewrite <- app_assoc in HP.
eapply (peout_body HIx mxd fl MXB PUT 0) with (P := PBS); [exact Hl | lia | exact LEN | exact HP | rewrite lvblocks_0; reflexivity
| eapply LOK; [exact Hl | lia] | exact TS | exact BLK | exact FR | exact ST | exact LO | exact LOS | exact SPA | exact HT | exact SPR | exact HPR | exact ERR | exact TP |].
intros ms1 md1 (m1 & A1 & F1 & fc1 & y1 & u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & -> & FS1 & FRM1 & VM1 & HP1 & TS1 & BLK1 & FR1 & ST1 & HPR1 & ERR1 & AG1).
pose proof (heap_model_ok _ _ _ _ _ _ HP1) as MOK1.
apply rz_evt; [exact MOK1|].
bstep. norm_w32. bstep. if_false.
apply evt_RZ_done. apply K. unfold po_loop_post.
exists m1, A1, F1, fc1, (lupd levels 0 lvl_reset). do 17 eexists.
split; [reflexivity|]. split; [exact FS1|]. split; [exact FRM1|]. split; [exact VM1|].
split; [rewrite lvblocks_0 in HP1; exact HP1|].
split; [rewrite lupd_length; exact LEN|].
split; [intros j Hj; replace j with 0%nat by lia; apply nth_error_lupd_eq; lia|].
split; [intros j Hj; apply nth_error_lupd_neq; lia|].
split; [exact TS1|]. split; [exact BLK1|]. split; [exact FR1|]. split; [exact ST1|]. split; [exact HPR1 |]. split; [exact ERR1|]. exact AG1.
-
destruct (nth_error levels (S i)) as [l|] eqn:Hl; [| apply nth_error_None in Hl; lia].
rewrite (lvblocks_S _ _ _ Hl) in HP. rewrite <- app_assoc in HP.
eapply (peout_body HIx mxd fl MXB PUT (S i)) with (P := lvblocks levels (S i) ++ PBS); [exact Hl | lia | exact LEN | exact HP | rewrite <- app_assoc; reflexivity
| eapply LOK; [exact Hl | lia] | exact TS | exact BLK | exact FR | exact ST | exact LO | exact LOS | exact SPA | exact HT | exact SPR | exact HPR | exact ERR | exact TP |].
intros ms1 md1 (m1 & A1 & F1 & fc1 & y1 & u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & -> & FS1 & FRM1 & VM1 & HP1 & TS1 & BLK1 & FR1 & ST1 & HPR1 & ERR1 & AG1).
pose proof (heap_model_ok _ _ _ _ _ _ HP1) as MOK1.
apply rz_evt; [exact MOK1|].
bstep. norm_w32. bstep. if_truex.
replace (Z.of_nat (S i) + -1) with (Z.of_nat i) by lia.
apply evt_RZ_done.
eapply (IH _ gp tp _ _ _ _ _ _ _ _ _ _ _ s2 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F1 fc1 m1 me md1 T A1 PBS LB0 SP lo errv q r pb depth x (lupd levels (S i) lvl_reset));
[lia | rewrite lupd_length; exact LEN | rewrite lvblocks_lupd_ge by lia; exact HP1 | | exact TS1 | exact BLK1 | exact FR1 | exact ST1 | exact LO | exact LOS | exact SPA | exact HT | exact SPR | exact HPR1 | exact ERR1 | exact TP |].
+ intros j l' Hj Hji. rewrite nth_error_lupd_neq in Hj by lia.
eapply lvl_ok_agree; [eapply LOK; [exact Hj | lia] | exact AG1 | apply incl_appl; eapply incl_tran; [| eapply lvblocks_incl; [exact Hj | lia]]; unfold lvl_blocks; apply incl_appl; apply incl_refl].
+ intros ms2 md2 (m2 & A2 & F2 & fc2 & levels2 & y1' & u0' & u1' & u2' & w0 & v1' & v2' & v3' & v4' & v5' & v6' & v7' & u3' & u4' & u5' & u6' & s1' & -> & FS2 & FRM2 & VM2 & HP2 & LEN2 & RES2 & SAME2 & TS2 & BLK2 & FR2 & ST2 & HPR2 & ERR2 & AG2).
apply K. unfold po_loop_post.
exists m2, A2, F2, fc2, levels2. do 17 eexists.
split; [reflexivity|]. split; [eapply fsaved_trans; [exact FS1 | exact FS2]|]. split; [intros Hf; apply FRM2, FRM1, Hf|].
split; [eapply model_vm_only_trans; [exact VM1 | exact VM2]|].
split; [exact HP2|]. split; [exact LEN2|].
split. { intros j Hj. destruct (PeanoNat.Nat.eq_dec j (S i)) as [->|NE]; [| apply RES2; lia]. rewrite SAME2 by lia. apply nth_error_lupd_eq. lia. }
split. { intros j Hj. rewrite SAME2 by lia. apply nth_error_lupd_neq. lia. }
split; [exact TS2|]. split; [exact BLK2|]. split; [exact FR2|]. split; [exact ST2|]. split; [exact HPR2 |]. split; [exact ERR2|].
eapply agree_on_trans; [eapply agree_on_incl; [exact AG1 | apply incl_appr; apply incl_refl] | exact AG2].
Qed.

End PeOutLoop2.

End RC__1.
End Mq4.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QWxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qtgi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qtgi. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QjDH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDH. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QjDH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDH.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UC8c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UC8c.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QkMG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkMG.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UG8z.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UG8z. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UIsM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UIsM.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Udyh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Udyh.Mq2.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UBpZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UBpZ. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UT7i.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UT7i. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uv6q.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uv6q.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UzWc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UzWc.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Import TopUbTac Tk1Tac Tk3Tac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma le1_zxw : forall b : byte, le1 (Z_to_bv 64 (bv_unsigned b)) = [b].
Proof.
intros b. unfold le1, word_to_le_bytes. cbn. f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned.
pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R.
unfold bv_wrap. change (bv_modulus 64) with 18446744073709551616. change (bv_modulus 8) with 256.
rewrite (Z.mod_small _ 18446744073709551616) by lia. apply Z.mod_small. lia.
Qed.

Section PeComment.
Variable HIx : heap_iface S4L.
Hypothesis MEMMOVE : memmove_stmt.

Local Ltac ubh := repeat (lazymatch goal with
| |- evt _ _ (MS _ _ (if _ then Z_to_bv 64 147624 else ?nx) _ _ _ _) => first [ norm_w32; if_falsex | norm_w32; ub_pre_norm; ub_cmp_auto_c | norm_w32; ub_pre_norm; if_falsex ]; ub_skip
| |- evt _ _ (MS _ _ (if _ then ?nx else Z_to_bv 64 147624) _ _ _ _) => first [ norm_w32; if_truex | norm_w32; ub_pre_norm; ub_cmp_auto_c | norm_w32; ub_pre_norm; if_truex ]; ub_skip
end).
Local Ltac at_pc p := lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?q) _ _ _ _) => let b := eval vm_compute in (Z.eqb q p) in lazymatch b with true => idtac end end.
Local Ltac upto p := repeat (tryif at_pc p then fail else (ub_skip; ubh; tryif at_pc p then fail else step)); tryif at_pc p then idtac else (ub_skip; ubh).
Local Ltac go p := upto p; repeat (first [if_truex | if_falsex]; upto p).

#[using="MEMMOVE"] Lemma cmt_flush :
forall (pf : pe_fix) (q : Z) (LB0 : list blk) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (ts : tstate) (co0 : Z)
(cb : byte) (j1 j2 utf : list byte) (sv : pe_saved) (errv : word) (T : TSet)
(x1 gp t0 t1 t2 a0 a1 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC HIx pf lo ->
PE_INV HIx pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv ->
0 <= co0 <= t_co ts -> co0 < pf_len pf ->
(forall m' md' A' pbs' errv' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F' fc',
PE_INV HIx pf q LB0 payload me lo m' md' A' (ts_set_pbs ts pbs') cb j1 j2 utf sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_OUT co0 x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F' fc' m') md') T) ->
(forall m' md' A' pbs' errv' x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F' fc',
PE_INV HIx pf q LB0 payload me lo m' md' A' (ts_set_pbs ts pbs') cb j1 j2 utf sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_ERR co0 x1' gp' t0' t1' t2' (Z_to_bv 64 16) a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F' fc' m') md') T) ->
realizes rsegs (mkCfg (pe_ms rsegs pf 0x23ff8 co0 x1 gp t0 t1 t2 a0 a1 (Z_to_bv 64 (t_co ts - co0)) a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 s10 t3 t4 t5 t6 F fc m) md) T.
Proof.
intros until fc. intros STC INV Hco0 Hco0l Kout Kerr16.
pose proof STC as (LO & LOS & SPA & HT & SP0 & LEN & SB0 & (SBL & RR & LENR)).
destruct INV as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof REST as (HP & LV & OBJ & ST & ERR & STR & PLEN & SBin & HPR & MDV & JCG).
destruct ts as [depth levels co pb pbs xx obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct xx as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl_]; pe_gen fl_; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
unfold ts_set_pbs in Kout, Kerr16. cbn [t_levels t_depth t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in Kout, Kerr16.
unfold tok_cells, tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in TOK. unfold pe_frame in FR. unfold pe_ms in *. cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
unfold_consts.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
destruct SBin as [L0 | SBin]; [exfalso; lia|].
pose proof PB as (buf & bpos & cap & pre & post & Epbs & Lpre & PBC). pose proof PBC as (Hbpos & Hcap & _).
pose proof HP as HP1. unfold pe_blocks, tstate_blocks, ts0 in HP1. cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_tk pf_md pf_mxd pf_fl] in HP1.
rewrite Epbs in HP1. cbn [app pf_mxd] in HP1.
assert (INbuf : In (buf, cap) ((pb, 16) :: (buf, cap) :: (objbs ++ concat (map lvl_blocks levels)) ++ (tk, 72) :: (q, (32 * mxd)) :: LB0)) by (right; left; reflexivity).
pose proof (payload_sep HIx _ _ _ _ _ _ _ _ buf cap STC HP SBin ltac:(apply in_or_app; left; unfold ts0, tstate_blocks; cbn [t_pbs t_objbs t_levels pf_mxd]; rewrite Epbs; apply in_or_app; left; right; left; reflexivity)) as Hdsb.
cbn [pf_sb pf_len pf_mxd] in Hdsb.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L pf_mxd] in MI.
pose proof (bytes_at_bound _ _ _ _ STR) as SBB.
set (n := co - co0) in *.
pose proof (bytes_at_sub S4L m sb payload (Z.to_nat co0) (Z.to_nat n) STR ltac:(lia)) as SRC. cbn [hl_segs S4L pf_mxd] in SRC.
rewrite Z2Nat.id in SRC by lia.
assert (SRCL : Z.of_nat (length (firstn (Z.to_nat n) (skipn (Z.to_nat co0) payload))) = n) by (rewrite length_firstn, length_skipn; lia).
stash TSK. stash LV. clear OBJ HPR.
apply rz_evt; [exact MOK|].
bstep. bstep. bstep. bstep.
apply evt_RZ_done.
eapply (memappend_cps HIx MEMMOVE) with (lo := lo) (b := sb + co0) (n := n);
[ exact HP1 | exact PBC | lia | exact SRC | exact SRCL
| left; eapply (payload_crange (PEF _ _ _ _ _ _ _ _ _ _)); [exact SBin | intros bb Hbb; apply in_or_app; right; right; right; exact Hbb | cbn [pf_spf pf_mxd]; rewrite ?unsigned_lit by lia; unfold PE_FRAME; lia | lia | lia | cbn [pf_len pf_mxd]; lia] | lia | lia | lia | .. ]; try alloc_side.
all: try (rewrite ?unsigned_lit by lia; first [exact ST | exact ERR]).
all: try (rewrite ?unsigned_lit by lia; unfold PE_FRAME in *; clia).
intros ms2 md2 (m2 & A2 & r & errv2 & buf' & cap' & RS2 & VM2 & ST2 & HPR2 & ERR2 & HP2 & OUT2).
destruct RS2 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F2 & fc2 & -> & FS2 & FRM2).
cbn [hl_segs hl_tp S4L pf_mxd] in *. rewrite ?(unsigned_lit spf) in ST2 by lia. rewrite ?(unsigned_lit spf) in HPR2 by lia.
set (pbs2 := [(pb, 16); (buf', cap')]).
set (ts2 := TST depth levels co pb pbs2 (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs).
assert (INq2 : In (q, (32 * mxd)) ((objbs ++ concat (map lvl_blocks levels)) ++ (tk, 72) :: (q, (32 * mxd)) :: LB0))
by (apply in_or_app; right; right; left; reflexivity).
assert (INtk2 : In (tk, 72) ((objbs ++ concat (map lvl_blocks levels)) ++ (tk, 72) :: (q, (32 * mxd)) :: LB0))
by (apply in_or_app; right; left; reflexivity).
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. cbn [hl_segs S4L pf_mxd] in FR.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in TOK; [| eapply client_range_block; [exact INtk2 | lia | cbn; lia]]. cbn [hl_segs S4L pf_mxd] in TOK.
unstash TSK. apply (tstack_pres_g S4L _ _ _ _ _ _ HPR2 INq2) in TSK; [| exact LEN32].
assert (REST2 : PE_REST HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo m2 md2 A2 ts2 errv2).
{ unstash LV. eapply (PE_REST_call_pb HIx) with (ts := ts0) (LBc := (objbs ++ concat (map lvl_blocks levels)) ++ (tk, 72) :: (q, (32 * mxd)) :: LB0);
[exact STC | exact REST | exact VM2 | exact HPR2 | unfold ts0; cbn [t_objbs t_levels pf_mxd]; intros bb Hb; apply in_or_app;
apply in_app_or in Hb; destruct Hb as [Hb|Hb]; [left; apply in_or_app; left; exact Hb | apply in_app_or in Hb; destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; exact Hb | right; right; right; exact Hb]]
| unfold pe_blocks, tstate_blocks; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_tk pf_md pf_mxd pf_fl]; exact HP2
| exact ST2 | exact ERR2]. }
assert (PBany : pbuf rsegs m2 pbs2 pb).
{ destruct OUT2 as [[_ PBS] | (_ & -> & -> & PC)]; [exact PBS|].
exists buf, bpos, cap, pre, post. split; [reflexivity|]. split; [exact Lpre | exact PC]. }
assert (INV2 : PE_INV HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo m2 md2 A2 ts2 cb j1 j2 utf sv errv2).
{ split; [| exact REST2]. unfold PE_CORE, ts2; cbn. split; [exact LEN32|]. split; [exact D32|]. split; [lia|]. split; [reflexivity|].
split; [exact TOK|]. split; [exact PBany|]. split; [exact Hpb|]. split; [exact TSK | exact FR]. }
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2.
clear HP1 HP2 SRC PBany PBC HP MOK MI REST2 REST.
reenter MOK2.
destruct OUT2 as [[-> _] | (-> & -> & -> & _)].
- go 0x23ea8. apply evt_RZ_done. eapply Kout; [| exact FS2 | exact FRM2]. unfold ts2, pbs2 in INV2. exact INV2.
- replace (Z_to_bv 64 (2^64 - 1)) with (Z_to_bv 64 (-1)) by (apply bv_eq; vm_compute; reflexivity).
go 0x23ea4. apply evt_RZ_done. eapply Kerr16; [| exact FS2 | exact FRM2]. unfold ts2, pbs2 in INV2. exact INV2.
Qed.


#[using="MEMMOVE"] Lemma cmt_eof :
forall (pf : pe_fix) (q : Z) (LB0 : list blk) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (ts : tstate) (co0 : Z)
(cb : byte) (j1 j2 utf : list byte) (sv : pe_saved) (errv : word) (T : TSet)
(x1 gp t0 t1 t2 a0 a1 a3 a4 a5 a6 a7 s6 s7 s8 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC HIx pf lo ->
PE_INV HIx pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv ->
t_co ts = pf_len pf -> 0 <= co0 < pf_len pf ->
(forall m' md' A' pbs' (e : word) errv' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F' fc',
PE_INV HIx pf q LB0 payload me lo m' md' A' (ts_set_pbs (ts_set_err ts e) pbs') cb j1 j2 utf sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_OUT co0 x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F' fc' m') md') T) ->
(forall m' md' A' pbs' (e : word) errv' x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F' fc',
PE_INV HIx pf q LB0 payload me lo m' md' A' (ts_set_pbs (ts_set_err ts e) pbs') cb j1 j2 utf sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_ERR co0 x1' gp' t0' t1' t2' (Z_to_bv 64 16) a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F' fc' m') md') T) ->
realizes rsegs (mkCfg (pe_ms rsegs pf 0x23e50 co0 x1 gp t0 t1 t2 a0 a1 (Z_to_bv 64 (pf_len pf - co0)) a3 a4 a5 a6 a7
(Z_to_bv 64 q) s6 s7 s8 (Z_to_bv 64 (Z.of_nat (t_depth ts))) s10 t3 t4 t5 t6 F fc m) md) T.
Proof.
intros until fc. intros STC INV Heof Hco0 Kout Kerr16.
pose proof STC as (LO & LOS & SPA & HT & SP0 & LEN & SB0 & (SBL & RR & LENR)).
destruct INV as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof REST as (HP & LV & _).
destruct ts as [depth levels co pb pbs xx obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct xx as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff. subst co.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl_]; pe_gen fl_; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
unfold ts_set_pbs, ts_set_err in Kout, Kerr16. cbn [t_levels t_depth t_co t_pb t_pbs t_x t_obj t_objs t_objbs ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in Kout, Kerr16.
unfold tok_cells, tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in TOK. unfold pe_frame in FR. unfold pe_ms in *. cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
unfold_consts.
set (ts0 := TST depth levels len pb pbs (TS isd stpos (Z_to_bv 64 len) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocks; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, (32 * mxd)) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocks; apply in_or_app; right; right; left; reflexivity).
pose proof (heap_blk S4L HIx _ _ _ _ tk 72 HP INtk) as (_ & Htal & Htlo & Hthi & _).
pose proof (heap_blk S4L HIx _ _ _ _ q (32 * mxd) HP INq) as (_ & Hqal & Hqlo & Hqhi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hthi, Hqhi.
assert (Htq : tk <> q).
{ pose proof (heap_blk_nodup S4L HIx _ _ _ _ HP) as ND. unfold pe_blocks in ND. rewrite map_app in ND. apply NoDup_app_remove_l in ND.
cbn [map blk_addr fst pf_mxd] in ND. apply List.NoDup_cons_iff in ND as [Hni _]. intros E. apply Hni. left. symmetry. exact E. }
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ tk 72 q (32 * mxd) HP INtk INq Htq) as Hdtq.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L pf_mxd] in MI.
pose proof (wmono_refl rsegs m) as WM.
pose proof (munch_refl [(tk, tk + 72)] m) as MU.
assert (HW : Forall (pe_wtf (PEF tk oldl newl len lenr sb spf pmd mxd fl)) [(tk, tk + 72)]) by (apply Forall_cons; [left; cbn; lia | apply Forall_nil]).
stash PB. stash REST. clear LV.
assert (TAIL : forall (e : word) mc x1' t0' t1' t2' a0' a1' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6',
rw_cells rsegs mc tk
[C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 pb); C4 (Z_to_bv 64 mxd); C4 (Z_to_bv 64 (Z.of_nat depth)); C4 isd; C4 stpos;
C4 (Z_to_bv 64 len); C4 e; C4 ucs; C4 high; C1 quote; CB 7 (repeat (Z_to_bv 8 0) 7); C8 (Z_to_bv 64 q); C4 (Z_to_bv 64 fl); C4 (Z_to_bv 64 0)] ->
munch [(tk, tk + 72)] m mc -> wmono rsegs m mc -> mem_inv rsegs mc ->
evt rsegs (RZ rsegs md T)
(MS (mkR x1' (Z_to_bv 64 spf) gp (Z_to_bv 64 0x77c00) t0' t1' t2' (Z_to_bv 64 tk) (Z_to_bv 64 oldl) a0' a1' (Z_to_bv 64 (len - co0)) a3' a4' a5' a6' a7'
(Z_to_bv 64 newl) (Z_to_bv 64 lenr) s4' (Z_to_bv 64 (sb + co0)) s6' s7' s8' s9' s10' (Z_to_bv 64 0x134c0) t3' t4' t5' t6')
F (Z_to_bv 64 0x23ff8) fc None mc (seg_rom rsegs))).
{ intros e mc x1' t0' t1' t2' a0' a1' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' TOK' MU' WM' MI'.
unstash PB. unstash REST.
apply evt_RZ_done.
eapply (cmt_flush (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo mc md A
(TST depth levels len pb pbs (TS isd stpos (Z_to_bv 64 len) e ucs high quote) obj objs objbs) co0 cb);
[exact STC | | cbn; lia | cbn; lia
| unfold ts_set_pbs; cbn [t_levels t_depth t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd]; intros; eapply Kout; eassumption
| unfold ts_set_pbs; cbn [t_levels t_depth t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd]; intros; eapply Kerr16; eassumption ].
split.
- unfold PE_CORE; cbn. split; [exact LEN32|]. split; [exact D32|]. split; [lia|]. split; [reflexivity|].
split; [exact TOK'|]. split; [| split; [exact Hpb | split]].
+ eapply (pbuf_wtf HIx) with (ts := ts0); [exact STC | exact (proj1 REST) | exact PB | exact MU' | exact WM' | exact HW].
+ eapply (tstack_wtf HIx) with (ts := ts0); [exact STC | exact (proj1 REST) | exact TSK | exact LEN32 | exact MU' | exact WM' | exact HW].
+ eapply (rw_cells_transport rsegs _ m mc) in FR; [exact FR | exact MU' | exact WM' | cbn; unfold PE_FRAME in *; lia].
- cbn. eapply (PE_REST_private_write HIx) with (ts := ts0) in REST;
[exact REST | exact STC | exact MU' | exact WM' | exact MI' | apply pe_wtf_private; exact HW]. }
apply rz_evt; [exact MOK|].
destruct (PeanoNat.Nat.eq_dec depth 0) as [D0 | Dn].
+ subst depth. cbn [Z.of_nat pf_mxd] in TOK, TAIL |- *. upto 0x23ff8. if_falsex.
destruct (nth_error levels 0) as [l0|] eqn:Hl0; [| apply nth_error_None in Hl0; lia].
pose proof (TSK 0%nat l0 Hl0) as L0. rewrite Z.mul_0_r, Z.add_0_r in L0. unfold srec_cells in L0.
assert (SS26 : 0 <= tl_st l0 <= 26 /\ 0 <= tl_ss l0 <= 26) by (unstash REST; pose proof (proj1 (proj2 REST) 0%nat l0 Hl0) as (A1 & A2 & _); split; [exact A1 | exact A2]).
stash TSK.
upto 0x23ff8. norm_sx32.
destruct (Z.eq_dec (tl_st l0) 0) as [S0 | Sn].
* rewrite S0. if_falsex. upto 0x23ff8. norm_sx32.
destruct (Z.eq_dec (tl_ss l0) 2) as [F2 | Fn].
-- rewrite F2. if_falsex. upto 0x23ff8. unstash TSK. eapply TAIL; [exact TOK | exact MU | exact WM | exact MI].
-- if_truex. upto 0x23ff8. unstash TSK. eapply TAIL; [exact TOK | exact MU | exact WM | exact MI].
* if_truex. upto 0x23ff8. unstash TSK. eapply TAIL; [exact TOK | exact MU | exact WM | exact MI].
+ upto 0x23ff8. if_truex. upto 0x23ff8. eapply TAIL; [exact TOK | exact MU | exact WM | exact MI].
Qed.


#[using="MEMMOVE"] Lemma cmt_star :
forall (pf : pe_fix) (q : Z) (LB0 : list blk) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (ts : tstate) (l : tlevel) (co0 : Z)
(cb : byte) (j1 j2 utf : list byte) (sv : pe_saved) (errv : word) (T : TSet)
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s7 s8 s9 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC HIx pf lo ->
PE_INV HIx pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_comment ->
0 <= co0 <= t_co ts -> t_co ts < pf_len pf ->
(forall m' md' A' pbs' errv' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F' fc',
PE_INV HIx pf q LB0 payload me lo m' md' A' (ts_set_pbs (ts_set_level ts (TL ST_comment_end (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) pbs') cb j1 j2 utf sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_BREAK (t_co ts) x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F' fc' m') md') T) ->
(forall m' md' A' pbs' errv' x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F' fc',
PE_INV HIx pf q LB0 payload me lo m' md' A' (ts_set_pbs ts pbs') cb j1 j2 utf sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_ERR co0 x1' gp' t0' t1' t2' (Z_to_bv 64 16) a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F' fc' m') md') T) ->
realizes rsegs (mkCfg (pe_ms rsegs pf 0x2320c co0 x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 (Z_to_bv 64 (pf_sb pf + t_co ts)) s7 s8 s9 s10 t3 t4 t5 t6 F fc m) md) T.
Proof.
intros until fc. intros STC INV Hl Hst Hco0 Hco Kbreak Kerr16.
pose proof STC as (LO & LOS & SPA & HT & SP0 & LEN & SB0 & (SBL & RR & LENR)).
destruct INV as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof REST as (HP & LV & OBJ & ST & ERR & STR & PLEN & SBin & HPR & MDV & JCG).
destruct ts as [depth levels co pb pbs xx obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct xx as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl_]; pe_gen fl_; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
unfold ts_set_pbs, ts_set_level in Kbreak, Kerr16. cbn [t_levels t_depth t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in Kbreak, Kerr16.
unfold tok_cells, tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in TOK. unfold pe_frame in FR. unfold pe_ms in *. cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
unfold_consts.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
destruct SBin as [L0 | SBin]; [exfalso; lia|].
assert (INtk : In (tk, 72) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocks; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, (32 * mxd)) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocks; apply in_or_app; right; right; left; reflexivity).
pose proof (heap_blk S4L HIx _ _ _ _ tk 72 HP INtk) as (_ & Htal & Htlo & Hthi & _).
pose proof (heap_blk S4L HIx _ _ _ _ q (32 * mxd) HP INq) as (_ & Hqal & Hqlo & Hqhi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hthi, Hqhi.
assert (Htq : tk <> q).
{ pose proof (heap_blk_nodup S4L HIx _ _ _ _ HP) as ND. unfold pe_blocks in ND. rewrite map_app in ND. apply NoDup_app_remove_l in ND.
cbn [map blk_addr fst pf_mxd] in ND. apply List.NoDup_cons_iff in ND as [Hni _]. intros E. apply Hni. left. symmetry. exact E. }
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ tk 72 q (32 * mxd) HP INtk INq Htq) as Hdtq.
pose proof PB as (buf & bpos & cap & pre & post & Epbs & Lpre & PBC). pose proof PBC as (Hbpos & Hcap & _).
pose proof HP as HP1. unfold pe_blocks, tstate_blocks, ts0 in HP1. cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_tk pf_md pf_mxd pf_fl] in HP1.
rewrite Epbs in HP1. cbn [app pf_mxd] in HP1.
assert (INbuf : In (buf, cap) ((pb, 16) :: (buf, cap) :: (objbs ++ concat (map lvl_blocks levels)) ++ (tk, 72) :: (q, (32 * mxd)) :: LB0)) by (right; left; reflexivity).
pose proof (payload_sep HIx _ _ _ _ _ _ _ _ buf cap STC HP SBin ltac:(apply in_or_app; left; unfold ts0, tstate_blocks; cbn [t_pbs t_objbs t_levels pf_mxd]; rewrite Epbs; apply in_or_app; left; right; left; reflexivity)) as Hdsb.
cbn [pf_sb pf_len pf_mxd] in Hdsb.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L pf_mxd] in MI.
pose proof (bytes_at_bound _ _ _ _ STR) as SBB.
pose proof (LV depth l Hl) as LVd. pose proof LVd as (ST26 & SS26 & _ & Md).
rewrite Nat.ltb_irrefl, Nat.eqb_refl in Md. destruct Md as (c0 & hn0 & Hmode & CLS0 & NM0).
set (n := co - co0 + 1) in *.
pose proof (bytes_at_sub S4L m sb payload (Z.to_nat co0) (Z.to_nat n) STR ltac:(lia)) as SRC. cbn [hl_segs S4L pf_mxd] in SRC.
rewrite Z2Nat.id in SRC by lia.
assert (SRCL : Z.of_nat (length (firstn (Z.to_nat n) (skipn (Z.to_nat co0) payload))) = n) by (rewrite length_firstn, length_skipn; lia).
stash TSK. clear LV OBJ HPR.
assert (SBP : 0 < sb).
{ destruct SBin as [SBa | (bb & Hbb & Hb1 & _)]; [cbn [pf_spf pf_sb] in SBa; unfold PE_FRAME in SBa; clear - SBa SP0; lia |].
destruct bb as [ba bn]. pose proof (heap_blk S4L HIx _ _ _ _ ba bn HP ltac:(unfold pe_blocks; apply in_or_app; right; right; right; exact Hbb)) as (_ & _ & Hba & _).
cbn [blk_addr fst pf_sb] in Hb1. clear - Hb1 Hba; lia. }
apply rz_evt; [exact MOK|].
upto 0x241a4. norm_w32. replace (sb + co - (sb + co0) + 1) with n by lia.
apply evt_RZ_done.
eapply (memappend_cps HIx MEMMOVE) with (lo := lo) (b := sb + co0) (n := n);
[ exact HP1 | exact PBC | (clear - Hco0 Hco LEN; lia) | exact SRC | exact SRCL
| left; eapply (payload_crange (PEF _ _ _ _ _ _ _ _ _ _)); [exact SBin | intros bb Hbb; apply in_or_app; right; right; right; exact Hbb | cbn [pf_spf pf_mxd]; rewrite ?unsigned_lit by (clear - SP0; lia); unfold PE_FRAME; (clear; lia) | (clear - Hco0; lia) | (clear - SRCL; lia) | cbn [pf_len pf_mxd]; (clear - Hco; lia)] | (clear - Hco0 SB0; lia) | (clear - CO SBL; lia) | (clear - Hco0 Hco Hdsb; lia) | .. ]; try alloc_side.
all: try (rewrite ?unsigned_lit by lia; first [exact ST | exact ERR]).
all: try (rewrite ?unsigned_lit by lia; unfold PE_FRAME in *; clia).
intros ms2 md2 (m2 & A2 & r & errv2 & buf' & cap' & RS2 & VM2 & ST2 & HPR2 & ERR2 & HP2 & OUT2).
destruct RS2 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F2 & fc2 & -> & FS2 & FRM2).
cbn [hl_segs hl_tp S4L pf_mxd] in *. rewrite ?(unsigned_lit spf) in ST2 by lia. rewrite ?(unsigned_lit spf) in HPR2 by lia.
set (pbs2 := [(pb, 16); (buf', cap')]).
set (ts2 := TST depth levels co pb pbs2 (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs).
assert (INq2 : In (q, (32 * mxd)) ((objbs ++ concat (map lvl_blocks levels)) ++ (tk, 72) :: (q, (32 * mxd)) :: LB0))
by (apply in_or_app; right; right; left; reflexivity).
assert (INtk2 : In (tk, 72) ((objbs ++ concat (map lvl_blocks levels)) ++ (tk, 72) :: (q, (32 * mxd)) :: LB0))
by (apply in_or_app; right; left; reflexivity).
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. cbn [hl_segs S4L pf_mxd] in FR.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in TOK; [| eapply client_range_block; [exact INtk2 | lia | cbn; lia]]. cbn [hl_segs S4L pf_mxd] in TOK.
unstash TSK. apply (tstack_pres_g S4L _ _ _ _ _ _ HPR2 INq2) in TSK; [| exact LEN32].
assert (REST2 : PE_REST HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo m2 md2 A2 ts2 errv2).
{ eapply (PE_REST_call_pb HIx) with (ts := ts0) (LBc := (objbs ++ concat (map lvl_blocks levels)) ++ (tk, 72) :: (q, (32 * mxd)) :: LB0);
[exact STC | exact REST | exact VM2 | exact HPR2 | unfold ts0; cbn [t_objbs t_levels pf_mxd]; intros bb Hb; apply in_or_app;
apply in_app_or in Hb; destruct Hb as [Hb|Hb]; [left; apply in_or_app; left; exact Hb | apply in_app_or in Hb; destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; exact Hb | right; right; right; exact Hb]]
| unfold pe_blocks, tstate_blocks; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_tk pf_md pf_mxd pf_fl]; exact HP2
| exact ST2 | exact ERR2]. }
assert (PBany : pbuf rsegs m2 pbs2 pb).
{ destruct OUT2 as [[_ PBS] | (_ & -> & -> & PC)]; [exact PBS|].
exists buf, bpos, cap, pre, post. split; [reflexivity|]. split; [exact Lpre | exact PC]. }
assert (INV2 : PE_INV HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo m2 md2 A2 ts2 cb j1 j2 utf sv errv2).
{ split; [| exact REST2]. unfold PE_CORE, ts2; cbn. split; [exact LEN32|]. split; [exact D32|]. split; [lia|]. split; [reflexivity|].
split; [exact TOK|]. split; [exact PBany|]. split; [exact Hpb|]. split; [exact TSK | exact FR]. }
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2.
pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI2. cbn [hl_segs S4L pf_mxd] in MI2.
clear HP1 HP2 SRC PBany PBC HP MOK MI REST.
reenter MOK2.
destruct OUT2 as [[-> _] | (-> & -> & -> & _)].
2:{ replace (Z_to_bv 64 (2^64 - 1)) with (Z_to_bv 64 (-1)) by (apply bv_eq; vm_compute; reflexivity).
upto 0x23ea4. if_truex. upto 0x23ea4. apply evt_RZ_done. eapply Kerr16; [| exact FS2 | exact FRM2]. unfold ts2, pbs2 in INV2. exact INV2. }

upto 0x23d14. if_falsex.
pose proof (TSK depth l Hl) as Ld. cbn [hl_segs S4L pf_mxd] in Ld. unfold srec_cells in Ld.
remember (q + 32 * Z.of_nat depth) as bse eqn:Hbse in Ld.
assert (HbseR : q <= bse /\ bse + 32 <= q + (32 * mxd)) by (subst bse; lia).
pose proof (munch_refl [(bse, bse + 32)] m2) as MU. pose proof (wmono_refl rsegs m2) as WM.
pose proof INV2 as [CORE2 _]. pose proof CORE2 as (_ & _ & _ & _ & _ & PB2 & _).
stash PB2. stash REST2. stash TSK. clear CORE2 INV2.
upto 0x23d14. replace (q + Z.of_nat depth * 2 ^ 5) with bse by lia. upto 0x23d14.
unstash PB2. unstash REST2. unstash TSK.
set (l1 := TL ST_comment_end (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)).
assert (HW : Forall (pe_wtq (PEF tk oldl newl len lenr sb spf pmd mxd fl) q) [(bse, bse + 32)]) by (apply Forall_cons; [right; cbn [fst snd pf_mxd]; lia | apply Forall_nil]).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
match goal with L5 : rw_cells rsegs mc bse _ |- _ =>
assert (TSK3 : tstack rsegs mc q (lupd levels depth l1))
by (subst bse; eapply (tstack_put rsegs m2 _ q levels depth l1 []); [exact TSK | lia | exact MU | exact WM | intros; exact I | exact L5]);
assert (PB3 : pbuf rsegs mc pbs2 pb)
by (eapply (pbuf_wtq HIx) with (ts := ts2); [exact STC | exact (proj1 REST2) | exact PB2 | exact MU | exact WM | exact HW]);
assert (REST3 : PE_REST HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo mc md2 A2 ts2 errv2)
by (eapply (PE_REST_private_write HIx) with (ts := ts2) in REST2; [exact REST2 | exact STC | exact MU | exact WM | assumption | apply pe_wtq_private; exact HW]);
apply evt_RZ_done; apply (Kbreak mc md2 A2 pbs2 errv2); [| exact FS2 | exact FRM2]
end end.
split.
- unfold PE_CORE; cbn. split; [rewrite lupd_length; exact LEN32|]. split; [exact D32|]. split; [lia|]. split; [reflexivity|].
split; [assumption|]. split; [exact PB3|]. split; [exact Hpb|]. split; [exact TSK3 | assumption].
- destruct REST3 as (HP' & LV' & OBJ' & ST' & ERR' & STR' & PLEN' & SBin' & HPR' & MDV' & JCG').
cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd].
split.
{ match goal with |- HEAP _ _ _ ?L _ _ => replace L with (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts2); [exact HP' |] end.
unfold pe_blocks, tstate_blocks, ts2; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd].
match goal with |- context [map lvl_blocks (lupd ?lv ?d ?xx)] => rewrite (map_lupd_same lvl_blocks lv d xx l Hl eq_refl) end. reflexivity. }
split; [| split; [| split; [exact ST' | split; [exact ERR' | split; [exact STR' | split; [exact PLEN' | split; [exact SBin' | split; [exact HPR' | split; [exact MDV' | exact JCG']]]]]]]]].
+ intros i li Hli. unfold ts0, ts2 in Hli; cbn [t_levels t_depth pf_mxd] in Hli. unfold ts0, ts2; cbn [t_depth pf_mxd].
destruct (PeanoNat.Nat.eq_dec i depth) as [-> | NE].
* rewrite nth_error_lupd_eq in Hli by lia. injection Hli as <-.
eapply lvl_cur_restate with (c' := c0); [exact (LV' depth l Hl) | exact Hmode | | unfold ST_comment_end; lia | exact SS26 | left; reflexivity].
rewrite <- Hmode. apply lvl_mode_ws_same; [rewrite Hst; reflexivity | reflexivity].
* rewrite nth_error_lupd_neq in Hli by congruence. exact (LV' i li Hli).
+ revert OBJ'. unfold cur_st, ts0, ts2. cbn [t_levels t_depth t_objs t_objbs t_obj pf_mxd]. rewrite nth_error_lupd_eq by lia. cbn [tl_st pf_mxd].
rewrite Hl, Hst. cbn. intros OBJ'; exact OBJ'.
Qed.

Local Ltac if_any := lazymatch goal with |- evt _ _ (MS _ _ (if ?cnd then _ else _) _ _ _ _) => destruct cnd; cbv iota end.
Local Ltac wstep E := lazymatch goal with
| |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => try E; first [ub_if_lit_c | if_falsex | if_truex | align_true | ub_align_auto | ub_cmp_auto_c]
| |- _ => try shl_norm; try E; stepz; try (rewrite le1_zxw; mem_after_store)
end.
Local Ltac cwalk E := repeat (lazymatch goal with
| |- evt _ _ (MS _ _ (Z_to_bv 64 0x2320c) _ _ _ _) => fail
| |- evt _ _ (MS _ _ (Z_to_bv 64 0x23710) _ _ _ _) => fail
| |- evt _ _ (MS _ _ (Z_to_bv 64 0x23ff8) _ _ _ _) => fail
| |- _ => wstep E
end).
Local Ltac cexplore E := cwalk E; lazymatch goal with |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => if_any; cexplore E | |- _ => idtac end.
Local Ltac cnorm := try norm_w32; repeat match goal with |- context [bv_swrap 32 ?x] => rewrite (swrap32_id x) by lia end; try unfold zxb.
Local Ltac swalk p E := repeat (lazymatch goal with
| |- evt _ _ (MS _ _ (Z_to_bv 64 p) _ _ _ _) => fail
| |- _ => wstep E
end).

#[using="MEMMOVE"] Lemma cmt_latch :
forall (n : nat) (pf : pe_fix) (q : Z) (LB0 : list blk) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (ts : tstate) (l : tlevel) (co0 : Z)
(cb : byte) (j1 j2 utf : list byte) (sv : pe_saved) (errv : word) (T : TSet)
(x1 gp t0 t1 t2 a5 a6 a7 s7 s8 s10 t3 t4 t5 t6 : word) (anb : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC HIx pf lo ->
PE_INV HIx pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv ->
CSTR_OK pf payload ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_comment ->
0 <= co0 <= t_co ts -> t_co ts < pf_len pf -> nth_error payload (Z.to_nat (t_co ts)) = Some cb -> bv_unsigned cb <> 42 ->
(pf_len pf - t_co ts <= Z.of_nat n) ->

(forall m' co' cb' (j2' : list byte) x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s7' s8' s9' s10' t3' t4' t5' t6',
t_co ts < co' < pf_len pf -> nth_error payload (Z.to_nat co') = Some cb' -> bv_unsigned cb' = 42 ->
PE_INV HIx pf q LB0 payload me lo m' md A (ts_set_co ts co') cb' j1 j2' utf sv errv ->
realizes rsegs (mkCfg (pe_ms rsegs pf 0x2320c co0 x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' (Z_to_bv 64 (pf_sb pf + co')) s7' s8' s9' s10' t3' t4' t5' t6' F fc m') md) T) ->

(forall m' md' A' pbs' (e : word) co' cb' errv' (j2' : list byte) x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F' fc',
t_co ts < co' <= pf_len pf ->
PE_INV HIx pf q LB0 payload me lo m' md' A'
(TST (t_depth ts) (t_levels ts) co' (t_pb ts) pbs'
(TS (ts_isd (t_x ts)) (ts_stpos (t_x ts)) (Z_to_bv 64 co') e (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))
(t_obj ts) (t_objs ts) (t_objbs ts)) cb' j1 j2' utf sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_OUT co0 x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F' fc' m') md') T) ->

(forall m' md' A' pbs' (e : word) co' cb' errv' (j2' : list byte) x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F' fc',
t_co ts < co' <= pf_len pf ->
PE_INV HIx pf q LB0 payload me lo m' md' A'
(TST (t_depth ts) (t_levels ts) co' (t_pb ts) pbs'
(TS (ts_isd (t_x ts)) (ts_stpos (t_x ts)) (Z_to_bv 64 co') e (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))
(t_obj ts) (t_objs ts) (t_objbs ts)) cb' j1 j2' utf sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_ERR co0 x1' gp' t0' t1' t2' (Z_to_bv 64 16) a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F' fc' m') md') T) ->
realizes rsegs (mkCfg (pe_ms rsegs pf 0x23710 co0 x1 gp t0 t1 t2
(Z_to_bv 64 (pf_sb pf + t_co ts + 1)) anb (Z_to_bv 64 (t_co ts + 1 - co0)) (Z_to_bv 64 (bv_unsigned cb)) (Z_to_bv 64 (t_co ts + 1)) a5 a6 a7
(Z_to_bv 64 q) (Z_to_bv 64 (pf_sb pf + t_co ts)) s7 s8 (Z_to_bv 64 (Z.of_nat (t_depth ts))) s10 t3 t4 t5 t6 F fc m) md) T.
Proof.
induction n as [|n IH]; intros until fc; intros STC INV CSTR Hl Hst Hco0 Hco Hc N42 Hn Kstar Kout Kerr16.
{ exfalso. destruct INV as [(_ & _ & CO & _) _]. cbn in Hn. lia. }
pose proof STC as (LO & LOS & SPA & HT & SP0 & LEN & SB0 & (SBL & RR & LENR)).
destruct INV as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof REST as (HP & LV & OBJ & ST & ERR & STR & PLEN & SBin & HPR & MDV & JCG).
destruct ts as [depth levels co pb pbs xx obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct xx as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl_]; pe_gen fl_; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
unfold ts_set_co in Kstar. cbn [t_levels t_depth t_co t_pb t_pbs t_x t_obj t_objs t_objbs ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in Kstar.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in TOK. unfold pe_frame in FR. unfold pe_ms in *. cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
unfold_consts.
pose proof (bv_unsigned_in_range 8 cb) as CBR; unfold bv_modulus in CBR; cbn in CBR.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocks; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, (32 * mxd)) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocks; apply in_or_app; right; right; left; reflexivity).
pose proof (heap_blk S4L HIx _ _ _ _ tk 72 HP INtk) as (_ & Htal & Htlo & Hthi & _).
pose proof (heap_blk S4L HIx _ _ _ _ q (32 * mxd) HP INq) as (_ & Hqal & Hqlo & Hqhi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hthi, Hqhi.
assert (Htq : tk <> q).
{ pose proof (heap_blk_nodup S4L HIx _ _ _ _ HP) as ND. unfold pe_blocks in ND. rewrite map_app in ND. apply NoDup_app_remove_l in ND.
cbn [map blk_addr fst pf_mxd] in ND. apply List.NoDup_cons_iff in ND as [Hni _]. intros E. apply Hni. left. symmetry. exact E. }
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ tk 72 q (32 * mxd) HP INtk INq Htq) as Hdtq.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L pf_mxd] in MI.
pose proof (wmono_refl rsegs m) as WM.
pose proof (bytes_at_bound _ _ _ _ STR) as SBB.
pose proof (munch_refl [(tk, tk + 72); (spf, spf + 144)] m) as MU.
assert (HW : Forall (pe_wtf (PEF tk oldl newl len lenr sb spf pmd mxd fl)) [(tk, tk + 72); (spf, spf + 144)]).
{ apply Forall_cons; [left; cbn; lia |]. apply Forall_cons; [| apply Forall_nil].
right; unfold PE_FRAME; cbn [pf_spf pf_tk fst snd pf_md pf_mxd pf_fl]; split; [apply Z.le_refl | apply Z.le_refl]. }

assert (MKINV : forall mc co' (c' : byte) (e' nv : word),
0 <= co' <= len ->
rw_cells rsegs mc tk
[C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 pb); C4 (Z_to_bv 64 mxd); C4 (Z_to_bv 64 (Z.of_nat depth)); C4 isd; C4 stpos;
C4 (Z_to_bv 64 co'); C4 e'; C4 ucs; C4 high; C1 quote; CB 7 (repeat (Z_to_bv 8 0) 7); C8 (Z_to_bv 64 q); C4 (Z_to_bv 64 fl); C4 (Z_to_bv 64 0)] ->
rw_cells rsegs mc spf [C8 (Z_to_bv 64 obj); CB 16 j1; C4 nv; CB 3 (skipn 4 j2); C1 c'; CB 8 utf;
C8 (pe_s11 sv); C8 (pe_s10 sv); C8 (pe_s9 sv); C8 (pe_s8 sv); C8 (pe_s7 sv); C8 (pe_s6 sv);
C8 (pe_s5 sv); C8 (pe_s4 sv); C8 (pe_s3 sv); C8 (pe_s2 sv); C8 (pe_s1 sv); C8 (pe_s0 sv); C8 (pe_ra sv)] ->
munch [(tk, tk + 72); (spf, spf + 144)] m mc -> wmono rsegs m mc -> mem_inv rsegs mc ->
PE_INV HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo mc md A
(TST depth levels co' pb pbs (TS isd stpos (Z_to_bv 64 co') e' ucs high quote) obj objs objbs) c' j1 (le4 nv ++ skipn 4 j2) utf sv errv).
{ intros mc co' c' e' nv Hco' TOK' FR' MU' WM' MI'. split.
- unfold PE_CORE; cbn. split; [exact LEN32|]. split; [exact D32|]. split; [lia|]. split; [reflexivity|].
split; [exact TOK'|]. split; [| split; [exact Hpb | split; [| apply pe_frame_nb_set; exact FR']]].
+ eapply (pbuf_wtf HIx) with (ts := ts0); [exact STC | exact (proj1 REST) | exact PB | exact MU' | exact WM' | exact HW].
+ eapply (tstack_wtf HIx) with (ts := ts0); [exact STC | exact (proj1 REST) | exact TSK | exact LEN32 | exact MU' | exact WM' | exact HW].
- cbn. eapply (PE_REST_private_write HIx) with (ts := ts0) in REST;
[exact REST | exact STC | exact MU' | exact WM' | exact MI' | apply pe_wtf_private; exact HW]. }
stash PB. stash REST. stash TSK. clear LV OBJ HPR.
assert (SBP : 0 < sb).
{ destruct SBin as [L0 | SBin]; [exfalso; clear - L0 Hco CO; lia|]. destruct SBin as [SBa | (bb & Hbb & Hb1 & _)]; [cbn [pf_spf pf_sb] in SBa; unfold PE_FRAME in SBa; clear - SBa SP0; lia |].
destruct bb as [ba bn]. pose proof (heap_blk S4L HIx _ _ _ _ ba bn HP ltac:(unfold pe_blocks; apply in_or_app; right; right; right; exact Hbb)) as (_ & _ & Hba & _).
cbn [blk_addr fst pf_sb] in Hb1. clear - Hb1 Hba; lia. }
apply rz_evt; [exact MOK|].
tk3_walk 0x23ff8 idtac.
destruct (Z.eq_dec (bv_unsigned cb) 0) as [E0 | N0].
{ if_truex. tk3_walk 0x23ff8 idtac. unstash PB. unstash REST. unstash TSK. apply evt_RZ_done.
lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mc _) _) _ =>
eapply (cmt_flush (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo mc md A
(TST depth levels (co + 1) pb pbs (TS isd stpos (Z_to_bv 64 (co + 1)) err ucs high quote) obj objs objbs) co0 cb);
[ exact STC | eapply MKINV; [lia | exact TOK | exact FR | exact MU | exact WM | exact MI] | cbn; lia | cbn; lia
| unfold ts_set_pbs; cbn [t_levels t_depth t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd]; intros; eapply Kout; [| eassumption..]; lia
| unfold ts_set_pbs; cbn [t_levels t_depth t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd]; intros; eapply Kerr16; [| eassumption..]; lia ]
end. }
if_falsex.
tk3_walk 0x23e50 idtac.
destruct (peek_cases (PEF tk oldl newl len lenr sb spf pmd mxd fl) payload co cb LENR CSTR (proj1 RR) ltac:(cbn [pf_len pf_mxd]; lia) ltac:(cbn [pf_len pf_mxd]; lia) Hc N0)
as [[Elenr Heof] | [Hne Hmore]]; [cbn [pf_len pf_lenr pf_mxd] in Elenr, Heof; subst lenr; pose (lenr := len) | cbn [pf_len pf_lenr pf_mxd] in Hne, Hmore].
{ if_truex. tk3_walk 0x23e50 idtac. unstash PB. unstash REST. unstash TSK. apply evt_RZ_done.
replace (Z_to_bv 64 (co + 1 - co0)) with (Z_to_bv 64 (len - co0)) by (f_equal; lia).
lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mc _) _) _ =>
eapply (cmt_eof (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo mc md A
(TST depth levels (co + 1) pb pbs (TS isd stpos (Z_to_bv 64 (co + 1)) err ucs high quote) obj objs objbs) co0 cb);
[ exact STC | eapply MKINV; [lia | exact TOK | exact FR | exact MU | exact WM | exact MI] | cbn; lia | cbn; lia
| unfold ts_set_pbs, ts_set_err; cbn [t_levels t_depth t_co t_pb t_pbs t_x t_obj t_objs t_objbs ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd]; intros; eapply Kout; [| eassumption..]; lia
| unfold ts_set_pbs, ts_set_err; cbn [t_levels t_depth t_co t_pb t_pbs t_x t_obj t_objs t_objbs ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd]; intros; eapply Kerr16; [| eassumption..]; lia ]
end. }
if_falsex.
destruct (nth_error payload (Z.to_nat (co + 1))) as [c'|] eqn:Hc'; [| apply nth_error_None in Hc'; lia].
pose proof (bv_unsigned_in_range 8 c') as CBR'; unfold bv_modulus in CBR'; cbn in CBR'.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
assert (STR1 : bytes_at rsegs m1 sb payload)
by (unstash REST; eapply (PE_REST_private_write HIx) with (ts := ts0) in REST;
[exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 REST)))))) | exact STC | exact MU | exact WM | exact MI | apply pe_wtf_private; exact HW]);
pose proof (tok_flags_byte_g mxd fl m1 tk pb (Z.of_nat depth) q (TS isd stpos (Z_to_bv 64 (co + 1)) err ucs high quote) TOK) as RDF
end.
pose proof (payload_byte _ _ _ _ _ STR1 Hc' ltac:(lia)) as RDC. replace (sb + (co + 1)) with (sb + co + 1) in RDC by lia.
destruct (Z.eq_dec (bv_unsigned c') 42) as [E42 | N42'].
all: cexplore ltac:(cnorm).
all: try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x2374c) _ _ _ _) => idtac end;
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m2 _) =>
assert (STR2 : bytes_at rsegs m2 sb payload)
by (unstash REST; eapply (PE_REST_private_write HIx) with (ts := ts0) in REST;
[exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 REST)))))) | exact STC | eassumption | eassumption | eassumption | apply pe_wtf_private; exact HW]) end;
pose proof (payload_byte _ _ _ _ _ STR2 Hc' ltac:(lia)) as RDC2; replace (sb + (co + 1)) with (sb + co + 1) in RDC2 by lia;
cexplore ltac:(cnorm)).
all: unstash PB; unstash REST; unstash TSK.
all: try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x2320c) _ _ _ _) => idtac end;
apply evt_RZ_done; try replace (sb + co + 1) with (sb + (co + 1)) by lia;
lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mc _) _) _ =>
eapply (Kstar mc (co + 1) c'); [lia | exact Hc' | exact E42 | eapply MKINV; [lia | eassumption ..]]
end).
all: try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x23ff8) _ _ _ _) => idtac end;
apply evt_RZ_done;
lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mc _) _) _ =>
match goal with TOK3 : rw_cells rsegs mc _ [_; _; _; _; _; _; _; C4 ?e3; _; _; _; _; _; _; _] |- _ =>
eapply (cmt_flush (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo mc md A
(TST depth levels (co + 1) pb pbs (TS isd stpos (Z_to_bv 64 (co + 1)) e3 ucs high quote) obj objs objbs) co0 cb);
[ exact STC | eapply MKINV; [lia | exact TOK3 | eassumption | eassumption | eassumption | assumption] | cbn; lia | cbn; lia
| unfold ts_set_pbs; cbn [t_levels t_depth t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd]; intros; eapply Kout; [| eassumption..]; lia
| unfold ts_set_pbs; cbn [t_levels t_depth t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd]; intros; eapply Kerr16; [| eassumption..]; lia ]
end end).
all: try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x23710) _ _ _ _) => idtac end;
apply evt_RZ_done;
try replace (sb + co + 2) with (sb + (co + 1) + 1) by lia;
try replace (sb + co + 1 + 1) with (sb + (co + 1) + 1) by lia;
try replace (sb + co + 1) with (sb + (co + 1)) by lia;
try replace (co + 1 - co0 + 1) with (co + 1 + 1 - co0) by lia;
try replace (co + 2) with (co + 1 + 1) by lia;
lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mc _) _) _ =>
eapply (IH (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo mc md A
(TST depth levels (co + 1) pb pbs (TS isd stpos (Z_to_bv 64 (co + 1)) err ucs high quote) obj objs objbs) l co0 c');
[ exact STC | eapply MKINV; [lia | eassumption ..] | exact CSTR | exact Hl | exact Hst | cbn; lia | cbn; lia | exact Hc' | exact N42' | cbn; lia
| cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_sb pf_len pf_md pf_mxd pf_fl];
intros; eapply Kstar; [cbn in *; lia | eassumption | assumption | eassumption]
| cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_sb pf_len pf_md pf_mxd pf_fl];
intros; eapply Kout; [| eassumption..]; cbn in *; lia
| cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_sb pf_len pf_md pf_mxd pf_fl];
intros; eapply Kerr16; [| eassumption..]; cbn in *; lia ]
end).
Qed.

#[using="MEMMOVE"] Lemma seg_comment :
forall (pf : pe_fix) (q : Z) (LB0 : list blk) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (ts : tstate) (l : tlevel)
(cb : byte) (j1 j2 utf : list byte) (sv : pe_saved) (errv : word) (T : TSet)
(x1 gp t0 t1 t2 a0 a3 a4 a5 a6 a7 s6 s7 s8 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC HIx pf lo ->
PE_INV HIx pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv ->
CSTR_OK pf payload ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_comment ->
t_co ts < pf_len pf -> nth_error payload (Z.to_nat (t_co ts)) = Some cb ->

(forall m' md' A' pbs' errv' co' cb' (j2' : list byte) x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F' fc',
t_co ts <= co' < pf_len pf -> nth_error payload (Z.to_nat co') = Some cb' -> bv_unsigned cb' = 42 ->
PE_INV HIx pf q LB0 payload me lo m' md' A'
(TST (t_depth ts) (lupd (t_levels ts) (t_depth ts) (TL ST_comment_end (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)))
co' (t_pb ts) pbs'
(TS (ts_isd (t_x ts)) (ts_stpos (t_x ts)) (Z_to_bv 64 co') (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))
(t_obj ts) (t_objs ts) (t_objbs ts)) cb' j1 j2' utf sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_BREAK co' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F' fc' m') md') T) ->

(forall m' md' A' pbs' (e : word) co' cb' errv' (j2' : list byte) x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F' fc',
t_co ts < co' <= pf_len pf ->
PE_INV HIx pf q LB0 payload me lo m' md' A'
(TST (t_depth ts) (t_levels ts) co' (t_pb ts) pbs'
(TS (ts_isd (t_x ts)) (ts_stpos (t_x ts)) (Z_to_bv 64 co') e (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))
(t_obj ts) (t_objs ts) (t_objbs ts)) cb' j1 j2' utf sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_OUT (t_co ts) x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F' fc' m') md') T) ->

(forall m' md' A' pbs' (e : word) co' cb' errv' (j2' : list byte) x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F' fc',
t_co ts <= co' <= pf_len pf ->
PE_INV HIx pf q LB0 payload me lo m' md' A'
(TST (t_depth ts) (t_levels ts) co' (t_pb ts) pbs'
(TS (ts_isd (t_x ts)) (ts_stpos (t_x ts)) (Z_to_bv 64 co') e (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))
(t_obj ts) (t_objs ts) (t_objbs ts)) cb' j1 j2' utf sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_ERR (t_co ts) x1' gp' t0' t1' t2' (Z_to_bv 64 16) a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F' fc' m') md') T) ->
realizes rsegs (mkCfg (pe_ms rsegs pf (pe_jt ST_comment) (t_co ts) x1 gp t0 t1 t2
a0 (Z_to_bv 64 (tl_st l)) (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) a3 a4 a5 a6 a7
(Z_to_bv 64 q) s6 s7 s8 (Z_to_bv 64 (Z.of_nat (t_depth ts))) s10 t3 t4 t5 t6 F fc m) md) T.
Proof.
intros until fc. intros STC INV CSTR Hl Hst Hco Hc Kbreak Kout Kerr16.
pose proof INV as [CORE REST].
pose proof CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof (heap_model_ok _ _ _ _ _ _ (proj1 REST)) as MOK.
pose proof (bv_unsigned_in_range 8 cb) as CBR; unfold bv_modulus in CBR; cbn in CBR.
pose proof STC as (LO & LOS & SPA & HT & SP0 & LEN & SB0 & (SBL & RR & LENR)).
pose proof REST as (HP & _ & _ & _ & _ & _ & _ & SBin & _).
revert INV Kbreak Kout Kerr16.
destruct ts as [depth levels co pb pbs xx obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct xx as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl_]; pe_gen fl_; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
intros INV Kbreak Kout Kerr16.
assert (SBP : 0 < sb).
{ destruct SBin as [L0 | SBin]; [exfalso; clear - L0 Hco CO; lia|]. destruct SBin as [SBa | (bb & Hbb & Hb1 & _)]; [cbn [pf_spf pf_sb] in SBa; unfold PE_FRAME in SBa; clear - SBa SP0; lia |].
destruct bb as [ba bn]. pose proof (heap_blk S4L HIx _ _ _ _ ba bn HP ltac:(unfold pe_blocks; apply in_or_app; right; right; right; exact Hbb)) as (_ & _ & Hba & _).
cbn [blk_addr fst pf_sb] in Hb1. clear - Hb1 Hba; lia. }
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in TOK.
unfold pe_frame in FR. unfold pe_ms. cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl]. unfold_consts.
clear PB TSK REST CORE HP SBin.
apply rz_evt; [exact MOK|].
rewrite Hst. unfold ST_comment. cbn [pe_jt pf_mxd].
destruct (Z.eq_dec (bv_unsigned cb) 42) as [E42 | N42].
- swalk 0x2320c ltac:(cnorm).
apply evt_RZ_done.
eapply (cmt_star (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo m md A
(TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) l co cb);
[ exact STC | exact INV | exact Hl | exact Hst | cbn; lia | exact Hco
| unfold ts_set_pbs, ts_set_level; cbn [t_levels t_depth t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd]; intros; eapply Kbreak; [| exact Hc | exact E42 | eassumption..]; lia
| unfold ts_set_pbs; cbn [t_levels t_depth t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd]; intros; eapply Kerr16; [| eassumption..]; lia ].
- swalk 0x23710 ltac:(cnorm).
apply evt_RZ_done. replace (Z_to_bv 64 1) with (Z_to_bv 64 (co + 1 - co)) by (f_equal; lia).
eapply (cmt_latch (Z.to_nat (len - co)) (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo m md A
(TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) l co cb);
[ exact STC | exact INV | exact CSTR | exact Hl | exact Hst | cbn; lia | exact Hco | exact Hc | exact N42 | cbn; lia | | | ].
+ unfold ts_set_co; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_sb pf_len pf_md pf_mxd pf_fl].
intros m' co' cb' j2' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s7' s8' s9' s10' t3' t4' t5' t6' R' Hc' E42 INV'.
eapply (cmt_star (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo m' md A
(TST depth levels co' pb pbs (TS isd stpos (Z_to_bv 64 co') err ucs high quote) obj objs objbs) l co cb');
[ exact STC | exact INV' | exact Hl | exact Hst | cbn; lia | cbn; lia
| unfold ts_set_pbs, ts_set_level; cbn [t_levels t_depth t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd]; intros; eapply Kbreak; [| exact Hc' | exact E42 | eassumption..]; lia
| unfold ts_set_pbs; cbn [t_levels t_depth t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd]; intros; eapply Kerr16; [| eassumption..]; lia ].
+ cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_sb pf_len pf_md pf_mxd pf_fl].
intros. eapply Kout; eassumption.
+ cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_sb pf_len pf_md pf_mxd pf_fl].
intros. eapply Kerr16; [| eassumption..]. lia.
Qed.

End PeComment.

End RC__1.
