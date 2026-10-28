(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)

From Stdlib Require ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup Lib.GwApply QRjH QHnV QCcH QfLs Q0Ek Qtgi QjDH Qsw7 QJjn QkMG Q6q3.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM UC8c UG8z UPZI Udyh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

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
Import UG8z UPZI.Mq2 Udyh.Mq4 Udyh.Mq7.
Import QJjn.Mq0.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section PeOfs.
Variable HIx : heap_iface S4L.

#[using="Type"] Lemma seg_ofs_quote :
forall (pf : pe_fix) (q : Z) (LB0 : list blk) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (ts : tstate) (l : tlevel)
(cb : byte) (j1 j2 utf : list byte) (sv : pe_saved) (errv : word) (T : TSet)
(x1 gp t0 t1 t2 a1 a2 a4 a5 a6 a7 s4 s6 s7 s8 s9 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC HIx pf lo ->
PE_INV HIx pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv ->
nth_error (t_levels ts) (t_depth ts) = Some l -> (tl_st l = ST_ofs \/ tl_st l = ST_ofs_after_sep) ->

(forall m' x1' a2' a3' a4',
PE_INV HIx pf q LB0 payload me lo m' md A
(TST (t_depth ts) (lupd (t_levels ts) (t_depth ts) (TL ST_ofield (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)))
(t_co ts) (t_pb ts) (t_pbs ts)
(TS (ts_isd (t_x ts)) (ts_stpos (t_x ts)) (ts_choff (t_x ts)) (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) cb)
(t_obj ts) (t_objs ts) (t_objbs ts))
cb j1 j2 utf sv errv ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_BREAK (t_co ts) x1' gp t0 t1 t2 (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) (Z_to_bv 64 ST_ofield) a2' a3' a4' a5 a6 a7 s4 s6 s7 s8 s9 s10 t3 t4 t5 t6 F fc m') md) T) ->
forall a0, realizes rsegs (mkCfg (pe_ms rsegs pf 0x23094 (t_co ts) x1 gp t0 t1 t2
a0 a1 a2 (Z_to_bv 64 (bv_unsigned cb)) a4 a5 a6 a7
s4 s6 s7 s8 s9 s10 t3 t4 t5 t6 F fc m) md) T.
Proof.
intros until fc. intros STC INV Hl Hst Kbreak a0.
assert (Hstn : ST_ofield = ST_ofield) by reflexivity. set (stn := ST_ofield) in *.
pose proof STC as (LO & LOS & SPA & HT & SP0 & LEN & SB0 & SBL).
destruct INV as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof REST as (HP & LV & _).
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl_]; pe_gen fl_; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
unfold tok_cells, tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in TOK. unfold pe_frame in FR. unfold pe_ms in *. cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
unfold_consts.
assert (STN : 0 <= stn <= 26) by (subst stn; unfold ST_ofield; lia).
pose proof (bv_unsigned_in_range 8 cb) as CBR; unfold bv_modulus in CBR; cbn in CBR.
stash Hstn.
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

stash Hd1. stash Hd2. stash Hd3. stash Hd4. stash Hdpb.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L pf_mxd] in MI.
pose proof (wmono_refl rsegs m) as WM.
pose proof (LV depth l Hl) as LVd. pose proof LVd as (ST26 & SS26 & _ & Md).
rewrite Nat.ltb_irrefl, Nat.eqb_refl in Md. destruct Md as (c0 & hn0 & Hmode & CLS0 & NM0).
assert (MODE0 : c0 = CObj /\ hn0 = false /\ tl_ss l = tl_st l).
{ clear - Hmode SS26 Hst. assert (R : 0 <= tl_ss l <= 26) by lia.
destruct Hst as [E|E]; rewrite E in Hmode |- *; enum_z R (tl_ss l); vm_compute in Hmode; (repeat split); congruence. }
destruct MODE0 as (-> & -> & Ess).
assert (ST26' : 0 <= tl_st l <= 26) by (unfold ST_ofs, ST_ofs_after_sep in Hst; lia). stash Hst.
pose proof (TSK depth l Hl) as Ld. unfold srec_cells in Ld.
remember (q + 32 * Z.of_nat depth) as bse eqn:Hbse in Ld.
assert (HbseR : q <= bse /\ bse + 32 <= q + (32 * mxd)) by (subst bse; lia).
assert (Hb16 : bse mod 16 = 0) by (subst bse; clear - Hqal; Z.div_mod_to_equations; lia).
assert (Ebse : q + Z.of_nat depth * 32 = bse) by (subst bse; lia).
pose proof (munch_refl [(tk, tk + 72)] m) as MU.
stash REST. stash TSK. clear HP LV PB.
apply rz_evt; [exact MOK|].
step.
step. rewrite le1_zxb. mem_after_store.
step.

set (l' := TL stn (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)).
unstash REST. unstash TSK.
assert (HWA : Forall (pe_wtq (PEF tk oldl newl len lenr sb spf pmd mxd fl) q) [(tk, tk + 72)]) by (apply Forall_cons; [left; left; cbn [fst snd pf_tk pf_md pf_mxd pf_fl]; lia | apply Forall_nil]).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (TSKA : tstack rsegs mc q levels)
by (eapply (tstack_transport rsegs); [exact TSK | exact MU | exact WM |]; intros j Hj; rewrite LEN32 in Hj; cbn; lia);
assert (RESTA : PE_REST HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo mc md A ts0 errv)
by (eapply (PE_REST_private_write HIx) with (ts := ts0) in REST; [exact REST | exact STC | exact MU | exact WM | exact MI | apply pe_wtq_private; exact HWA]);
assert (PBCA : pbuf_core rsegs mc pb buf bpos cap (pre ++ [Z_to_bv 8 0] ++ post))
by (unstash Hd1; unstash Hd2; eapply (pbuf_core_agree rsegs [(pb, 16); (buf, cap)]); [exact PBC | | left; reflexivity | right; left; reflexivity];
eapply agree_of_munch; [exact MU | exact WM |]; intros a n [E|[E|[]]]; injection E as <- <-; cbn; lia)
end.
clear REST TSK MU WM PBC.
eapply evt_cut; [eapply printbuf_reset_P; [exact PBCA | lia | lia | exact Hpbal | lia | lia | unstash Hdpb; exact Hdpb | exact MI] |].
intros ms1 (mr & -> & MUr & WMr & MIr & PBC1).
replace (ret_pc (Z_to_bv 64 0x230a0)) with (Z_to_bv 64 0x230a0) by (symmetry; apply ret_pc_even; [lia | reflexivity]).

assert (HWR : Forall (pe_private (PEF tk oldl newl len lenr sb spf pmd mxd fl) q pbs) [(buf, buf + 1); (pb + 8, pb + 12)]).
{ apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]; unfold pe_private; cbn [fst snd pf_tk pf_spf pf_md pf_mxd pf_fl]; right; right; left.
- exists buf, cap. rewrite Epbs. split; [right; left; reflexivity | pose proof PBC1 as (_ & Hc & _); lia].
- exists pb, 16. rewrite Epbs. split; [left; reflexivity | lia]. }
assert (RESTR : PE_REST HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo mr md A ts0 errv)
by (eapply (PE_REST_private_write HIx) with (ts := ts0) in RESTA; [exact RESTA | exact STC | exact MUr | exact WMr | exact MIr | exact HWR]).
eapply (rw_cells_transport rsegs _ m0 mr) in TOK; [| exact MUr | exact WMr | unstash Hd1; unstash Hd2; cbn; lia].
eapply (rw_cells_transport rsegs _ m0 mr) in FR; [| exact MUr | exact WMr | cbn; lia].
assert (TSKR : tstack rsegs mr q levels).
{ unstash Hd3. unstash Hd4. eapply (tstack_transport rsegs); [exact TSKA | exact MUr | exact WMr |]. intros j Hj. rewrite LEN32 in Hj. cbn. (clear - Hcap Hd3 Hd4 Hj; lia). }
clear Ld. pose proof (TSKR depth l Hl) as Ld. rewrite <- Hbse in Ld. unfold srec_cells in Ld.
clear RESTA TSKA PBCA MI MUr WMr.

pose proof (wmono_refl rsegs mr) as WM. pose proof (munch_refl [(bse, bse + 32)] mr) as MU.
stash RESTR. stash TSKR. stash PBC1.
step. norm_sx32. step.
step. rewrite (unsigned_lit (Z.of_nat depth)) by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32.
step. replace (q + Z.of_nat depth * 32) with bse by lia.
OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB.Tk1.Tk1Tac.tk1_walk 0x230b0 0x230bc 8%nat Ebse.
OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB.Tk1.Tk1Tac.tk1_walk 0x230c0 0x230d4 8%nat Ebse.
step. if_truex.
step. step. OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB.Tk3.Tk3Tac.align_true.
OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB.Tk1.Tk1Tac.tk1_walk 0x230ec 0x23d14 8%nat Ebse.
unstash RESTR. unstash TSKR. unstash PBC1.
assert (HWB : Forall (pe_wtq (PEF tk oldl newl len lenr sb spf pmd mxd fl) q) [(bse, bse + 32)]) by (apply Forall_cons; [right; cbn [fst snd pf_mxd]; lia | apply Forall_nil]).
rewrite Hbse. apply evt_RZ_done. eapply Kbreak.
lazymatch goal with |- PE_INV _ _ _ _ _ _ _ ?mc _ _ _ _ _ _ _ _ _ =>
assert (RESTB : PE_REST HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo mc md A ts0 errv)
by (eapply (PE_REST_private_write HIx) with (ts := ts0) in RESTR; [exact RESTR | exact STC | exact MU | exact WM | exact MIr | apply pe_wtq_private; exact HWB]);
assert (TSKB : tstack rsegs mc q (lupd levels depth l'))
by (subst bse; eapply (tstack_put rsegs mr _ q levels depth l' []); [exact TSKR | (clear - LEN32 D32; lia) | exact MU | exact WM | intros; exact I | unfold srec_cells, l'; cbn [tl_st tl_ss tl_cur tl_name pf_mxd]; exact Ld]);
assert (PBCB : pbuf_core rsegs mc pb buf 0 cap ([Z_to_bv 8 0] ++ skipn 1 (pre ++ [Z_to_bv 8 0] ++ post)))
by (unstash Hd3; unstash Hd4; eapply (pbuf_core_agree rsegs [(pb, 16); (buf, cap)]); [exact PBC1 | | left; reflexivity | right; left; reflexivity];
eapply agree_of_munch; [exact MU | exact WM |]; intros a n [E|[E|[]]]; injection E as <- <-; cbn; (clear - Hd3 HbseR Hd4; lia))
end.
split.
- unfold PE_CORE. cbn [t_levels t_depth t_co t_pb t_pbs t_x t_obj ts_choff ts_isd ts_stpos ts_err ts_ucs ts_high ts_quote pf_len pf_tk pf_spf pf_md pf_mxd pf_fl].
split; [rewrite lupd_length; exact LEN32|]. split; [exact D32|]. split; [lia|]. split; [reflexivity|].
split; [unfold tok_cells, tok_cells_g; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd]; exact TOK|].
split; [| split; [exact Hpb | split; [exact TSKB | unfold pe_frame; exact FR]]].
exists buf, 0, cap, [], (skipn 1 (pre ++ [Z_to_bv 8 0] ++ post)). split; [exact Epbs|]. split; [reflexivity|]. exact PBCB.
- destruct RESTB as (HP' & LV' & OBJ' & ST' & ERR' & STR' & PLEN' & SBin' & HPR' & MDV' & JCG').
cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd].
split.
{ match goal with |- HEAP _ _ _ ?L _ _ => replace L with (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0); [exact HP' |] end.
unfold pe_blocks, tstate_blocks, ts0; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd].
fold l'. rewrite (map_lupd_same lvl_blocks levels depth l' l Hl) by reflexivity. reflexivity. }
split; [| split; [| split; [exact ST' | split; [exact ERR' | split; [exact STR' | split; [exact PLEN' | split; [exact SBin' | split; [exact HPR' | split; [exact MDV' | exact JCG']]]]]]]]].
+ cbn [t_levels t_depth pf_mxd]. intros i li Hli. destruct (PeanoNat.Nat.eq_dec i depth) as [-> | NE].
* rewrite nth_error_lupd_eq in Hli by lia. injection Hli as <-.
eapply lvl_cur_restate with (c' := CObj); [exact (LV' depth l Hl) | exact Hmode | | unfold ST_ofield; lia | exact SS26 | left; reflexivity].
rewrite Ess. unstash Hst. destruct Hst as [E|E]; rewrite E; vm_compute; reflexivity.
* rewrite nth_error_lupd_neq in Hli by congruence. exact (LV' i li Hli).
+ revert OBJ'. unfold cur_st, ts0. cbn [t_levels t_depth t_objs t_objbs t_obj pf_mxd]. rewrite nth_error_lupd_eq by lia. cbn [tl_st l' pf_mxd].
rewrite Hl. unstash Hst. destruct Hst as [E|E]; rewrite E; cbn; intros E'; exact E'.
Qed.

#[using="Type"] Lemma seg_ofs :
forall (pf : pe_fix) (q : Z) (LB0 : list blk) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (ts : tstate) (l : tlevel)
(cb : byte) (j1 j2 utf : list byte) (sv : pe_saved) (errv : word) (T : TSet)
(x1 gp t0 t1 t2 a3 a4 a5 a6 a7 s6 s7 s8 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC HIx pf lo ->
PE_INV HIx pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv ->
nth_error (t_levels ts) (t_depth ts) = Some l -> (tl_st l = ST_ofs \/ tl_st l = ST_ofs_after_sep) ->
t_co ts < pf_len pf ->

(forall m' ss' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6',
bv_unsigned cb = 125 /\ ss' = ST_finish ->
PE_INV HIx pf q LB0 payload me lo m' md A (ts_set_level ts (TL ST_eatws ss' (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) cb j1 j2 utf sv errv ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_BREAK (t_co ts) x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F fc m') md) T) ->

(forall m' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6',
(bv_unsigned cb = 34 \/ bv_unsigned cb = 39) ->
PE_INV HIx pf q LB0 payload me lo m' md A
(TST (t_depth ts) (lupd (t_levels ts) (t_depth ts) (TL ST_ofield (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)))
(t_co ts) (t_pb ts) (t_pbs ts)
(TS (ts_isd (t_x ts)) (ts_stpos (t_x ts)) (ts_choff (t_x ts)) (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) cb)
(t_obj ts) (t_objs ts) (t_objbs ts))
cb j1 j2 utf sv errv ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_BREAK (t_co ts) x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F fc m') md) T) ->

(forall (e : word) x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6',
realizes rsegs (mkCfg (pe_ms rsegs pf PE_ERR (t_co ts) x1' gp' t0' t1' t2' e a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F fc m) md) T) ->
realizes rsegs (mkCfg (pe_ms rsegs pf (pe_jt ST_ofs) (t_co ts) x1 gp t0 t1 t2
(Z_to_bv 64 0) (Z_to_bv 64 (tl_st l)) (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) a3 a4 a5 a6 a7
(Z_to_bv 64 q) s6 s7 s8 (Z_to_bv 64 (Z.of_nat (t_depth ts))) s10 t3 t4 t5 t6 F fc m) md) T.
Proof.
intros until fc. intros STC INV Hl Hst Hco Kbreak Kquote Kerr. pose proof INV as INV0.
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

pose proof (TSK depth l Hl) as Ld. unfold srec_cells in Ld.
remember (q + 32 * Z.of_nat depth) as bse eqn:Hbse in Ld.
assert (HbseR : q <= bse /\ bse + 32 <= q + (32 * mxd)) by (subst bse; lia).
pose proof (munch_refl [(bse, bse + 32)] m) as MU.
pose proof (bv_unsigned_in_range 8 cb) as CBR; unfold bv_modulus in CBR; cbn in CBR.
stash PB. stash REST. stash TSK. clear HP LV.
apply rz_evt; [exact MOK|].
assert (ST26' : 0 <= tl_st l <= 26) by (unfold ST_ofs, ST_ofs_after_sep in Hst; lia).
replace (q + 32 * Z.of_nat depth) with bse by lia.
assert (TAIL : forall ss' mc (x1' t0' t1' t2' a0v a1v a2v a3v a4v a5v a6v a7v s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' : word),
(bv_unsigned cb = 125 /\ ss' = ST_finish) ->
rw_cells rsegs mc bse [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 ss'); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (tl_cur l)); C8 (Z_to_bv 64 (tl_name l))] ->
munch [(bse, bse + 32)] m mc -> wmono rsegs m mc -> mem_inv rsegs mc ->
(forall H : rw_cells rsegs mc tk [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 pb); C4 (Z_to_bv 64 mxd); C4 (Z_to_bv 64 (Z.of_nat depth)); C4 isd; C4 stpos;
C4 (Z_to_bv 64 co); C4 err; C4 ucs; C4 high; C1 quote; CB 7 (repeat (Z_to_bv 8 0) 7); C8 (Z_to_bv 64 q); C4 (Z_to_bv 64 fl); C4 (Z_to_bv 64 0)], True) ->
rw_cells rsegs mc tk [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 pb); C4 (Z_to_bv 64 mxd); C4 (Z_to_bv 64 (Z.of_nat depth)); C4 isd; C4 stpos;
C4 (Z_to_bv 64 co); C4 err; C4 ucs; C4 high; C1 quote; CB 7 (repeat (Z_to_bv 8 0) 7); C8 (Z_to_bv 64 q); C4 (Z_to_bv 64 fl); C4 (Z_to_bv 64 0)] ->
rw_cells rsegs mc spf [C8 (Z_to_bv 64 obj); CB 16 j1; C4 (nbw j2); CB 3 (skipn 4 j2); C1 cb; CB 8 utf;
C8 (pe_s11 sv); C8 (pe_s10 sv); C8 (pe_s9 sv); C8 (pe_s8 sv); C8 (pe_s7 sv); C8 (pe_s6 sv);
C8 (pe_s5 sv); C8 (pe_s4 sv); C8 (pe_s3 sv); C8 (pe_s2 sv); C8 (pe_s1 sv); C8 (pe_s0 sv); C8 (pe_ra sv)] ->
realizes rsegs (mkCfg (MS (mkR x1' (Z_to_bv 64 spf) gp (Z_to_bv 64 490496) t0' t1' t2' (Z_to_bv 64 tk) (Z_to_bv 64 oldl)
a0v a1v a2v a3v a4v a5v a6v a7v
(Z_to_bv 64 newl) (Z_to_bv 64 lenr) s4' (Z_to_bv 64 (sb + co)) s6' s7' s8' s9' s10' (Z_to_bv 64 0x134c0) t3' t4' t5' t6')
F (Z_to_bv 64 PE_BREAK) fc None mc (seg_rom rsegs)) md) T).
{ intros ss' mc x1' t0' t1' t2' a0v a1v a2v a3v a4v a5v a6v a7v s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' Hss L5 MU' WM' MI' _ TOK' FR'.
unstash PB. unstash REST. unstash TSK.
assert (SS' : 0 <= ss' <= 26) by (unfold ST_finish in Hss; lia).
set (l' := TL ST_eatws ss' (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)).
assert (HW : Forall (pe_wtq (PEF tk oldl newl len lenr sb spf pmd mxd fl) q) [(bse, bse + 32)]).
{ apply Forall_cons; [right; cbn [fst snd pf_mxd]; lia | apply Forall_nil]. }
subst bse. apply (Kbreak mc ss' x1' gp t0' t1' t2' a0v a1v a2v a3v a4v a5v a6v a7v s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' Hss). split.
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
+ assert (MODE0 : c0 = CObj /\ hn0 = false).
{ clear - Hmode SS26 Hst. assert (R : 0 <= tl_ss l <= 26) by lia.
destruct Hst as [E|E]; rewrite E in Hmode; unfold ST_ofs, ST_ofs_after_sep in Hmode; enum_z R (tl_ss l); vm_compute in Hmode; split; congruence. }
destruct MODE0 as [-> ->].
intros i li Hli. unfold ts0 in Hli. cbn [t_levels t_depth pf_mxd] in Hli. destruct (PeanoNat.Nat.eq_dec i depth) as [-> | NE].
* rewrite nth_error_lupd_eq in Hli by lia. injection Hli as <-.
destruct Hss as [_ Ess]; rewrite Ess in *.
eapply lvl_cur_restate with (c' := CAny); [exact (LV' depth l Hl) | exact Hmode | vm_compute; reflexivity | unfold ST_eatws; lia | unfold ST_finish; lia | right; reflexivity].
* rewrite nth_error_lupd_neq in Hli by congruence. exact (LV' i li Hli).
+ unfold cur_st in *; cbn in *. rewrite nth_error_lupd_eq by lia. cbn [tl_st pf_mxd]. unfold ST_eatws. cbn.
revert OBJ'. rewrite Hl. destruct Hst as [E|E]; rewrite E; cbn; intros OBJ'; exact OBJ'. }
assert (Hbal : bse mod 16 = 0) by (rewrite Hbse; Z.div_mod_to_equations; lia).
destruct (Z.eq_dec (bv_unsigned cb) 34) as [C34 | N34].
{ OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB.Tk3.Tk3Tac.tk3_walk 0x23094 ltac:(try norm_sx32; try unfold zxb; try rewrite (unsigned_lit (bv_unsigned cb)) by lia). apply evt_RZ_done. subst bse.
eapply (seg_ofs_quote (PEF tk oldl newl len lenr sb spf pmd mxd fl)) with (ts := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) (l := l); [exact STC | exact INV0 | exact Hl | exact Hst |].
cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high pf_mxd]. intros m' x1' a2' a3' a4' INV'. eapply Kquote; [left; exact C34 | exact INV']. }
destruct (Z.eq_dec (bv_unsigned cb) 39) as [C39 | N39].
{ OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB.Tk3.Tk3Tac.tk3_walk 0x23094 ltac:(try norm_sx32; try unfold zxb; try rewrite (unsigned_lit (bv_unsigned cb)) by lia). apply evt_RZ_done. subst bse.
eapply (seg_ofs_quote (PEF tk oldl newl len lenr sb spf pmd mxd fl)) with (ts := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) (l := l); [exact STC | exact INV0 | exact Hl | exact Hst |].
cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high pf_mxd]. intros m' x1' a2' a3' a4' INV'. eapply Kquote; [right; exact C39 | exact INV']. }
destruct (Z.eq_dec (bv_unsigned cb) 125) as [C125 | N125].
2: { OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB.Tk3.Tk3Tac.tk3_walk 0x23ea4 ltac:(try norm_sx32; try unfold zxb; try rewrite (unsigned_lit (bv_unsigned cb)) by lia). apply evt_RZ_done. apply Kerr. }
assert (Ld8 : rw_cells rsegs m bse [CB 8 (le4 (Z_to_bv 64 (tl_st l)) ++ le4 (Z_to_bv 64 (tl_ss l))); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (tl_cur l)); C8 (Z_to_bv 64 (tl_name l))])
by (eapply rw_cells_recast; [exact Ld | cbn; repeat split; reflexivity | reflexivity | reflexivity]).
clear Ld. rename Ld8 into Ld.
destruct Hst as [E | E]; rewrite E; unfold ST_ofs, ST_ofs_after_sep.
- OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB.Tk3.Tk3Tac.tk3_walk 0x23d14 ltac:(try norm_sx32; try unfold zxb; try rewrite (unsigned_lit (bv_unsigned cb)) by lia).
apply evt_RZ_done. eapply (TAIL ST_finish); [split; [exact C125 | reflexivity] | | exact MU | exact WM | exact MI | intros; exact I | exact TOK | exact FR].
lazymatch goal with Lx : rw_cells rsegs ?mm bse (C8 ?v :: ?rest) |- _ =>
apply (proj1 (rw_cells_app rsegs mm bse [C8 v] rest)) in Lx as [Lx1 Lx2];
apply (proj2 (rw_cells_app rsegs mm bse [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 ST_finish)] rest)); split;
[ eapply rw_cells_recast; [exact Lx1 | cbn; repeat split; reflexivity | vm_compute; repeat (match goal with |- (_ :: _) = (_ :: _) => apply f_equal2 end); try reflexivity; apply bv_eq; reflexivity | reflexivity]
| exact Lx2 ] end.
- pose proof (tok_flags_byte_g mxd fl m tk pb (Z.of_nat depth) q (TS isd stpos (Z_to_bv 64 co) err ucs high quote) ltac:(unfold tok_cells, tok_cells_g; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd]; exact TOK)) as RDF.
destruct (land1_cases fl) as [F1 | F1].
+ OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB.Tk3.Tk3Tac.tk3_walk 0x23d14 ltac:(try norm_sx32; try rewrite (zxb_byte fl) by lia; try unfold zxb; try rewrite (unsigned_lit (bv_unsigned cb)) by lia; try rewrite (unsigned_lit (fl mod 256)) by (pose proof (Z.mod_pos_bound fl 256 ltac:(lia)); lia); try rewrite (land_mod256 fl 1) by lia; try rewrite F1).
apply evt_RZ_done. eapply (TAIL ST_finish); [split; [exact C125 | reflexivity] | | exact MU | exact WM | exact MI | intros; exact I | exact TOK | exact FR].
lazymatch goal with Lx : rw_cells rsegs ?mm bse (C8 ?v :: ?rest) |- _ =>
apply (proj1 (rw_cells_app rsegs mm bse [C8 v] rest)) in Lx as [Lx1 Lx2];
apply (proj2 (rw_cells_app rsegs mm bse [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 ST_finish)] rest)); split;
[ eapply rw_cells_recast; [exact Lx1 | cbn; repeat split; reflexivity | vm_compute; repeat (match goal with |- (_ :: _) = (_ :: _) => apply f_equal2 end); try reflexivity; apply bv_eq; reflexivity | reflexivity]
| exact Lx2 ] end.
+ OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB.Tk3.Tk3Tac.tk3_walk 0x23ea4 ltac:(try norm_sx32; try rewrite (zxb_byte fl) by lia; try unfold zxb; try rewrite (unsigned_lit (bv_unsigned cb)) by lia; try rewrite (unsigned_lit (fl mod 256)) by (pose proof (Z.mod_pos_bound fl 256 ltac:(lia)); lia); try rewrite (land_mod256 fl 1) by lia; try rewrite F1). apply evt_RZ_done. apply Kerr.
Qed.

End PeOfs.

End RC__1.
End Mq0.
From Stdlib Require NArith Permutation.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UTEu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB.Tk1 Require Tk1Reset.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB.Top Require TopUbTac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup.
Import UEQM.
Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi.
Import UC8c.Mq0.
Import Qsw7 QJjn.
Import UTEu.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section TokNew.
Variable HIx : heap_iface S4L.
Notation HEAPx := (HEAP S4L HIx).
Hypothesis PUT : UPZI.Mq4.put_stmt_P HIx.

Definition json_tokener_new_entry : Z := 0x21950.

#[using="Type"] Lemma tstack_of_zeros : forall m k A,
rw_cells rsegs m A [CB (32 * k)%nat (repeat (Z_to_bv 8 0) (32 * k))] ->
tstack rsegs m A (repeat lvl_zero k).
Proof.
intros m k. induction k as [|k IH]; intros A H i l Hl.
- destruct i; discriminate.
- replace (32 * S k)%nat with (32 + 32 * k)%nat in H by lia.
rewrite repeat_app in H.
destruct (rw_cells_CB_cut rsegs m A _ _ 32 H ltac:(lia)) as [H0 H1].
rewrite firstn_app, firstn_all2 in H0 by (rewrite repeat_length; lia).
rewrite repeat_length, Nat.sub_diag, firstn_O, app_nil_r in H0.
rewrite skipn_app, skipn_all2 in H1 by (rewrite repeat_length; lia).
rewrite repeat_length, Nat.sub_diag, skipn_O, app_nil_l in H1.
replace (32 + 32 * k - 32)%nat with (32 * k)%nat in H1 by lia.
destruct i as [|i].
+ cbn in Hl. injection Hl as <-. rewrite Nat2Z.inj_0, Z.mul_0_r, Z.add_0_r.
eapply rw_cells_recast; [exact H0 | cbn; repeat split | vm_compute; reflexivity | reflexivity].
+ cbn [nth_error] in Hl. specialize (IH (A + 32) H1 i l Hl).
replace (A + 32 * Z.of_nat (S i)) with (A + 32 + 32 * Z.of_nat i) by lia. exact IH.
Qed.

#[using="Type"] Lemma lb_remove_notin : forall p LB, (forall n, ~ In (p, n) LB) -> lb_remove p LB = LB.
Proof.
intros p LB. induction LB as [|[a n] LB IH]; intros H; [reflexivity|]. cbn.
destruct (Z.eqb_spec a p) as [->|NE]; [exfalso; apply (H n); left; reflexivity|].
f_equal. apply IH. intros n' Hin. apply (H n'). right. exact Hin.
Qed.
#[using="Type"] Lemma lb_remove_zero : forall A LB m md, HEAPx A LB m md -> lb_remove 0 LB = LB.
Proof.
intros A LB m md HP. apply lb_remove_notin. intros n Hin.
pose proof (heap_blk S4L HIx _ _ _ _ 0 n HP Hin) as (_ & _ & H0 & _). lia.
Qed.

Definition tok_cells0 : list cell :=
[C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0);
C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0);
C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C1 (Z_to_bv 8 0); CB 7 (repeat (Z_to_bv 8 0) 7);
C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)].
Definition lvl_cells0 : list cell := [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].

Definition toknew_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : Model) (LB : list blk) (lo : Z)
(ms' : machine_state) (md' : Model) : Prop :=
exists m' (A' : AS S4L HIx) (r : Z) (errv' : word),
ret_statew S4L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' /\
model_vm_only md md' /\
stk rsegs m' lo (bv_unsigned sp) /\
heap_pres S4L LB (bv_unsigned sp) m m' /\
rw_cells rsegs m' (0x77c00 - 164) [C4 errv'] /\
( (r = 0 /\ HEAPx A' LB m' md')
\/ (r <> 0 /\ exists BS, tok_fresh rsegs m' BS r /\ HEAPx A' (BS ++ LB) m' md') ).

#[using="PUT"] Lemma json_tokener_new_cps :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (T : TSet)
(A : AS S4L HIx) (LB : list blk) (lo : Z) (errv : word),
HEAPx A LB m md ->
stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 32 - 48 - (112 + 48 + 48 + 32 + 32 + 8256) ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hi_top S4L HIx ->
rw_cells rsegs m (0x77c00 - 164) [C4 errv] ->
tp = Z_to_bv 64 0x77c00 -> bv_unsigned ra mod 2 = 0 ->
a0 = Z_to_bv 64 32 ->
(forall ms' md', toknew_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB lo ms' md' ->
realizes rsegs (mkCfg ms' md') T) ->
realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 json_tokener_new_entry) fc None m (seg_rom rsegs)) md) T.
Proof.
intros until errv. intros HP ST LO LOS SPA HT ERR TP RA A0 K. subst a0.
unfold_consts. word_range sp SPR.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (heap_pres_refl S4L LB (bv_unsigned sp) m) as HPR.
pose proof (wmono_refl rsegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU.
subst tp.
apply rz_evt; [exact MOK|]. unfold json_tokener_new_entry.
carve_frame 32%nat ST.
do 5 step. step. if_false. do 4 step.

alloc_call (hi_calloc S4L HIx) S4L HIx HP MU WM MI.
intros ms2 m2 md2 A2 r e2 RS VM2 ST2 HPR2 ERR2 OUT2. open_ret RS. cbn [hl_segs S4L] in *.
extend_pres2 S4L HIx HPR MU WM HP HPR2.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
clear MU WM MI ST.
destruct OUT2 as [(-> & _ & HP2) | (Hr & BLK & HP2)].
-
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2.
pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI. cbn [hl_segs S4L] in MI.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m2) as MU.
pose proof (wmono_refl rsegs m2) as WM.
reenter MOK2.
step. if_true. step. do 7 step.
apply evt_RZ_done. apply K. unfold toknew_post.
exists m2, A2, 0, e2.
split; [| split; [exact VM2 | split; [| split; [exact HPR | split; [exact ERR2 | left; auto]]]]].
+ apply ret_statew_same.
+ release_frame FR ST2 (bv_unsigned sp). exact ST2.
-
change (1 * 72) with 72 in HP2.
pose proof (rw_cells_recast rsegs _ _ _ tok_cells0 BLK ltac:(cbn; repeat split; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as BLK'.
clear BLK. rename BLK' into BLK. unfold tok_cells0 in BLK.
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2.
pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI. cbn [hl_segs S4L] in MI.
pose proof (heap_blk S4L HIx _ _ _ _ r 72 HP2 ltac:(left; reflexivity)) as (_ & Hal & Hlo & Hhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ r 72 HP2 ltac:(left; reflexivity)) as Himg_r. cbn [hl_img_lo hl_img_hi S4L] in Himg_r.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hhi.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (r, r + 72)] m2) as MU.
pose proof (wmono_refl rsegs m2) as WM.
reenter MOK2.
step. if_falsex. do 4 step.

alloc_call (hi_calloc S4L HIx) S4L HIx HP2 MU WM MI.
intros ms3 m3 md3 A3 q e3 RS3 VM3 ST3 HPR3 ERR3 OUT3. open_ret RS3. cbn [hl_segs S4L] in *.
extend_pres2 S4L HIx HPR MU WM HP2 HPR3.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR3) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR3) in BLK; [| eapply client_range_block; [left; reflexivity | lia | cbn; lia]]. cbn [hl_segs S4L] in BLK.
clear MU WM MI ST2.
destruct OUT3 as [(-> & _ & HP3) | (Hq & SBLK & HP3)].
+
pose proof (heap_model_ok _ _ _ _ _ _ HP3) as MOK3.
pose proof (heap_mem_inv _ _ _ _ _ _ HP3) as MI. cbn [hl_segs S4L] in MI.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (r, r + 72)] m3) as MU.
pose proof (wmono_refl rsegs m3) as WM.
reenter MOK3.
step. step. TopUbTac.ub_resolve. stepz. step. if_true. step. step.

alloc_call (hi_free S4L HIx) S4L HIx HP3 MU WM MI.
{ right. exists 72. left. reflexivity. }
intros ms4 m4 md4 A4 r4 RS4 VM4 ST4 HPR4 ERR4 HP4. open_ret RS4. cbn [hl_segs S4L] in *.
rewrite lb_remove_head in HPR4, HP4.
extend_pres2 S4L HIx HPR MU WM HP3 HPR4.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR4) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
clear MU WM MI.
pose proof (heap_model_ok _ _ _ _ _ _ HP4) as MOK4.
pose proof (heap_mem_inv _ _ _ _ _ _ HP4) as MI. cbn [hl_segs S4L] in MI.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m4) as MU. pose proof (wmono_refl rsegs m4) as WM.
reenter MOK4.
step. do 7 step.
apply evt_RZ_done. apply K. unfold toknew_post.
exists m4, A4, 0, e3.
split; [| split; [| split; [| split; [exact HPR | split; [exact ERR4 | left; auto]]]]].
* apply ret_statew_same.
* eapply model_vm_only_trans; [exact VM2|]. eapply model_vm_only_trans; [exact VM3| exact VM4].
* release_frame FR ST4 (bv_unsigned sp). exact ST4.
+
change (32 * 32) with 1024 in HP3.
pose proof (tstack_of_zeros m3 32 q SBLK) as TS0. clear SBLK.
pose proof (heap_model_ok _ _ _ _ _ _ HP3) as MOK3.
pose proof (heap_mem_inv _ _ _ _ _ _ HP3) as MI. cbn [hl_segs S4L] in MI.
pose proof (heap_blk S4L HIx _ _ _ _ q 1024 HP3 ltac:(left; reflexivity)) as (_ & Hqal & Hqlo & Hqhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ q 1024 HP3 ltac:(left; reflexivity)) as Himg_q. cbn [hl_img_lo hl_img_hi S4L] in Himg_q.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hqhi.
pose proof (blk_ne_01 S4L HIx _ _ _ _ _ _ _ _ HP3) as Hqr.
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ q 1024 r 72 HP3 ltac:(left; reflexivity) ltac:(right; left; reflexivity) Hqr) as Hdqr.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (r, r + 72)] m3) as MU.
pose proof (wmono_refl rsegs m3) as WM.
reenter MOK3.
step. step. TopUbTac.ub_resolve. step. step. if_falsex. step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (TS1 : tstack rsegs mc q (repeat lvl_zero 32))
by (eapply tstack_transport; [exact TS0 | exact MU | exact WM | intros j Hj; rewrite repeat_length in Hj; cbn; unfold_consts; (clear - LO LOS SPR Hqhi Hdqr Hj; lia)]) end.
clear TS0. rename TS1 into TS0.
apply evt_RZ_done.
eapply (printbuf_new_cps HIx);
[ eapply (heap_frame S4L HIx); [exact HP3 | | exact WM | exact MI];
eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HP3 MU); solve_frameW_with HP3
| .. ]; try alloc_side.
intros ms4 md4 (m4 & A4 & pbr & e4 & RS4 & VM4 & ST4 & HPR4 & ERR4 & OUT4).
destruct RS4 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F4 & fc4 & -> & FS4 & FRM4).
cbn [hl_segs S4L] in *.
rewrite ?(unsigned_lit (bv_unsigned sp + -32)) in ST4 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -32)) in HPR4 by lia.
extend_pres2 S4L HIx HPR MU WM HP3 HPR4.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR4) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR4) in BLK; [| eapply client_range_block; [right; left; reflexivity | lia | cbn; lia]]. cbn [hl_segs S4L] in BLK.
assert (TS4 : tstack rsegs m4 q (repeat lvl_zero 32)) by (eapply (UG8z.tstack_pres' S4L); [exact HPR4 | left; reflexivity | reflexivity | exact TS0]).
clear TS0. rename TS4 into TS0.
clear MU WM MI ST3.
destruct OUT4 as [(-> & HP4) | (Hpbr & [PBS [PB HP4]])].
*
pose proof (heap_model_ok _ _ _ _ _ _ HP4) as MOK4.
pose proof (heap_mem_inv _ _ _ _ _ _ HP4) as MI. cbn [hl_segs S4L] in MI.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (r, r + 72)] m4) as MU.
pose proof (wmono_refl rsegs m4) as WM.
reenter MOK4.
stepz. step. if_true. step. step.

alloc_call (hi_free S4L HIx) S4L HIx HP4 MU WM MI.
{ right. exists 1024. left. reflexivity. }
intros ms5 mx5 md5 A5 r5 RS5 VM5 ST5 HPR5 ERR5 HP5. open_ret RS5. cbn [hl_segs S4L] in *.
rewrite lb_remove_head in HPR5, HP5.
extend_pres2 S4L HIx HPR MU WM HP4 HPR5.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR5) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
clear MU WM MI BLK TS0.
pose proof (heap_model_ok _ _ _ _ _ _ HP5) as MOK5.
pose proof (heap_mem_inv _ _ _ _ _ _ HP5) as MI. cbn [hl_segs S4L] in MI.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] mx5) as MU. pose proof (wmono_refl rsegs mx5) as WM.
reenter MOK5.
step. step.

alloc_call (hi_free S4L HIx) S4L HIx HP5 MU WM MI.
{ right. exists 72. left. reflexivity. }
intros ms6 mx6 md6 A6 r6 RS6 VM6 ST6 HPR6 ERR6 HP6. open_ret RS6. cbn [hl_segs S4L] in *.
rewrite lb_remove_head in HPR6, HP6.
extend_pres2 S4L HIx HPR MU WM HP5 HPR6.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR6) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
clear MU WM MI.
pose proof (heap_model_ok _ _ _ _ _ _ HP6) as MOK6.
pose proof (heap_mem_inv _ _ _ _ _ _ HP6) as MI. cbn [hl_segs S4L] in MI.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] mx6) as MU. pose proof (wmono_refl rsegs mx6) as WM.
reenter MOK6.
step. do 7 step.
apply evt_RZ_done. apply K. unfold toknew_post.
exists mx6, A6, 0, e4.
split; [| split; [| split; [| split; [exact HPR | split; [exact ERR6 | left; auto]]]]].
-- apply ret_statew_intro; [exact FS4 | exact FRM4].
-- eapply model_vm_only_trans; [exact VM2|]. eapply model_vm_only_trans; [exact VM3|]. eapply model_vm_only_trans; [exact VM4|].
eapply model_vm_only_trans; [exact VM5| exact VM6].
-- release_frame FR ST6 (bv_unsigned sp). exact ST6.
*
pose proof PB as PB0.
destruct PB as (buf & bpos & size & pre & post & EPBS & Lpre & CORE). subst PBS. cbn [app] in HP4.
pose proof (heap_blk S4L HIx _ _ _ _ pbr 16 HP4 ltac:(left; reflexivity)) as (_ & Hpal & Hplo & Hphi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ pbr 16 HP4 ltac:(left; reflexivity)) as Himg_p. cbn [hl_img_lo hl_img_hi S4L] in Himg_p.
pose proof (heap_blk S4L HIx _ _ _ _ buf size HP4 ltac:(right; left; reflexivity)) as (Hsz0 & Hbal & Hblo & Hbhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ buf size HP4 ltac:(right; left; reflexivity)) as Himg_b. cbn [hl_img_lo hl_img_hi S4L] in Himg_b.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hphi, Hbhi.
pose proof (heap_blk_nodup S4L HIx _ _ _ _ HP4) as ND. cbn [map blk_addr fst] in ND.
apply List.NoDup_cons_iff in ND as [Hni1 ND1]. apply List.NoDup_cons_iff in ND1 as [Hni2 ND2].
assert (Hpq : pbr <> q) by (intros E; apply Hni1; right; left; congruence).
assert (Hbq : buf <> q) by (intros E; apply Hni2; left; congruence).
assert (Hpr : pbr <> r) by (intros E; apply Hni1; right; right; left; congruence).
assert (Hbr : buf <> r) by (intros E; apply Hni2; right; left; congruence).
clear Hni1 Hni2 ND2.
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ pbr 16 q 1024 HP4 ltac:(left; reflexivity) ltac:(right; right; left; reflexivity) Hpq) as Hdpq.
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ buf size q 1024 HP4 ltac:(right; left; reflexivity) ltac:(right; right; left; reflexivity) Hbq) as Hdbq.
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ pbr 16 r 72 HP4 ltac:(left; reflexivity) ltac:(right; right; right; left; reflexivity) Hpr) as Hdpr.
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ buf size r 72 HP4 ltac:(right; left; reflexivity) ltac:(right; right; right; left; reflexivity) Hbr) as Hdbr.
clear CORE.
stash PB0. stash Hdpq. stash Hdbq. stash Himg_p. stash Himg_b. stash Hpal. stash Hbal. stash Hblo.
stash Hpq. stash Hbq. stash Hpr. stash Hbr.
pose proof (heap_model_ok _ _ _ _ _ _ HP4) as MOK4.
pose proof (heap_mem_inv _ _ _ _ _ _ HP4) as MI. cbn [hl_segs S4L] in MI.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (r, r + 72)] m4) as MU.
pose proof (wmono_refl rsegs m4) as WM.
reenter MOK4.
step. step. if_falsex.
step. norm_sx32.
stepz.
step. if_false.
do 4 step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (TS1 : tstack rsegs mc q (repeat lvl_zero 32))
by (eapply tstack_transport; [exact TS0 | exact MU | exact WM | intros j Hj; rewrite repeat_length in Hj; cbn; unfold_consts; (clear - LO LOS SPR Hqhi Hdqr Hj; lia)]);
assert (AG1 : QjDH.Mq0.agree_on rsegs [(pbr, 16); (buf, size)] m4 mc)
by (eapply QjDH.Mq0.agree_of_munch; [exact MU | exact WM | intros a n Hin; destruct Hin as [E|[E|[]]]; injection E as <- <-; cbn; unfold_consts; (clear - LO LOS SPR Hphi Hbhi Hsz0 Hdpr Hdbr; lia)]) end.
clear TS0.
apply evt_RZ_done.
eapply (Tk1Reset.reset_level_cps HIx PUT 0%nat) with (l := lvl_zero) (levels := repeat lvl_zero 32)
(REST := [(pbr, 16); (buf, size)] ++ (r, 72) :: (q, 1024) :: LB) (P := [(pbr, 16); (buf, size)]) (LB0 := LB)
(q := q) (r := r) (pb := pbr) (depth := 0) (mxd := 32) (fl := 0) (rc := 1) (lo := lo)
(x := TS (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 8 0));
[ reflexivity | lia | lia | reflexivity
| eapply heap_perm; [ eapply (heap_frame S4L HIx); [exact HP4 | | exact WM | exact MI];
eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HP4 MU); solve_frameW_with HP4
| cbn [lvl_blocks lvl_zero tl_cbs tl_nbs app]; apply perm_skip, perm_skip, perm_swap ]
| reflexivity | cbn; split; reflexivity | left; split; reflexivity | exact TS1 | exact BLK | .. ]; try alloc_side.
all: try (unfold Tk1Reset.RESET_STK, UPZI.Mq4.put_stk_P; rewrite ?unsigned_lit by lia; lia).
all: try (apply (heap_pres_refl S4L)).
intros ms5 md5 (m5 & A5 & rv5 & RS5 & VM5 & OUT5 & TS5 & BLK5 & ST5 & HPR5 & ERR5 & AGP5).
destruct RS5 as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & F5 & fc5 & -> & FS5 & FRM5).
cbn [hl_segs hl_tp S4L] in *.
rewrite ?(unsigned_lit (bv_unsigned sp + -32)) in ST5 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -32)) in HPR5 by lia.
destruct OUT5 as [(_ & HP5) | (s' & Es & _)]; [| cbn in Es; discriminate Es]. cbn [app] in HP5.
extend_pres2 S4L HIx HPR MU WM HP4 HPR5.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR5) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
clear BLK. rename BLK5 into BLK. unfold QjDH.tok_cells_g in BLK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in BLK.
replace (lupd (repeat lvl_zero 32) 0 lvl_reset) with (lvl_reset :: repeat lvl_zero 31) in TS5 by reflexivity.
unstash PB0.
assert (PB1 : pbuf rsegs m5 [(pbr, 16); (buf, size)] pbr) by (eapply QjDH.Mq0.pbuf_agree; [exact PB0 | eapply QjDH.Mq0.agree_on_trans; [exact AG1 | exact AGP5] | apply incl_refl]).
clear PB0 AG1 AGP5 MU WM MI ST4.
pose proof (heap_model_ok _ _ _ _ _ _ HP5) as MOK5.
pose proof (heap_mem_inv _ _ _ _ _ _ HP5) as MI. cbn [hl_segs S4L] in MI.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (r, r + 72)] m5) as MU. pose proof (wmono_refl rsegs m5) as WM.
reenter MOK5.

step. step. if_false.
stepz. stepz. step.
do 7 step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (PB2 : pbuf rsegs mc [(pbr, 16); (buf, size)] pbr)
by (eapply QjDH.Mq0.pbuf_agree with (BS := [(pbr, 16); (buf, size)]); [exact PB1 | eapply QjDH.Mq0.agree_of_munch; [exact MU | exact WM | intros a n Hin; destruct Hin as [E|[E|[]]]; injection E as <- <-; cbn; unfold_consts; (clear - LO LOS SPR Hphi Hbhi Hsz0 Hdpr Hdbr; lia)] | apply incl_refl]);
assert (TS6 : tstack rsegs mc q (lvl_reset :: repeat lvl_zero 31))
by (eapply tstack_transport; [exact TS5 | exact MU | exact WM | intros j Hj; cbn [length] in Hj; rewrite repeat_length in Hj; cbn; unfold_consts; (clear - LO LOS SPR Hqhi Hdqr Hj; lia)])
end.
clear PB1 TS5.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
apply evt_RZ_done; apply K; unfold toknew_post; exists mc, A5, r, e4 end.
split; [| split; [| split; [| split; [ | split; [assumption | right]]]]].
-- apply ret_statew_intro; [eapply fsaved_trans; [exact FS4 | exact FS5] | intros Hf; exact (FRM5 (FRM4 Hf))].
-- eapply model_vm_only_trans; [exact VM2|]. eapply model_vm_only_trans; [exact VM3|]. eapply model_vm_only_trans; [exact VM4| exact VM5].
-- release_frame FR ST5 (bv_unsigned sp). exact ST5.
-- eapply heap_pres_trans; [exact HPR|].
eapply (heap_pres_of_munch S4L LB (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outside S4L HIx); [exact HP5 | intros bb Hbb; right; right; right; right; exact Hbb | clia |]. solve_clientW S4L HIx HP5.
-- split; [exact Hr|]. exists ([(r, 72); (q, 1024)] ++ [(pbr, 16); (buf, size)]). split.
++ exists q, pbr, [(pbr, 16); (buf, size)]. split; [reflexivity|]. split; [exact BLK|]. split; [exact PB2 | split; [exact Hpbr | exact TS6]].
++ eapply heap_perm.
** eapply (heap_frame S4L HIx); [exact HP5 | | exact WM | assumption].
eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HP5 MU). solve_frameW_with HP5.
** cbn [app]. exact (Permutation_app_swap_app [(pbr,16);(buf,size)] [(r,72);(q,1024)] LB).
Qed.

End TokNew.

End RC__1.
End Mq1.

From Stdlib Require Import ZArith Lia.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Udyh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Udyh.Mq6. Unset Keyed Unification. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr.
Open Scope Z_scope.

Lemma pe_jt2_cases : forall c, 0 <= c < 256 ->
(pe_jt2 c = 0x23b60 /\ c = 34) \/ (pe_jt2 c = 0x23b54 /\ c = 39) \/
(pe_jt2 c = 0x224ac /\ (c = 45 \/ 48 <= c <= 57)) \/
(pe_jt2 c = 0x229b0 /\ (c = 70 \/ c = 84 \/ c = 102 \/ c = 116)) \/
(pe_jt2 c = 0x22b6c /\ (c = 73 \/ c = 105)) \/
(pe_jt2 c = 0x22b58 /\ (c = 78 \/ c = 110)) \/
(pe_jt2 c = 0x23b84 /\ c = 91) \/ (pe_jt2 c = 0x23b38 /\ c = 123) \/
pe_jt2 c = 0x23db4.
Proof.
intros c Hc. enum_from c 0 256%nat. all: cbv [pe_jt2].
all: first [ do 8 right; reflexivity | left; split; [reflexivity | lia] | right; left; split; [reflexivity|lia] | do 2 right; left; split; [reflexivity|lia]
| do 3 right; left; split; [reflexivity|lia] | do 4 right; left; split; [reflexivity|lia] | do 5 right; left; split; [reflexivity|lia] | do 6 right; left; split; [reflexivity|lia] | do 7 right; left; split; [reflexivity|lia] ].
Qed.
