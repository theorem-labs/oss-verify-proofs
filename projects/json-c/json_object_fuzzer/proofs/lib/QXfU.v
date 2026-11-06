(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup QEQM Lib.GwApply QWxq_c1 QRjH QHnV QCcH QfLs Q0Ek Qtgi QjDH QC8c Qsw7 QJjn QkMG QG8z QIsM Qdyh Qa8x QPZI QBpZ QT7i Qv6q QzWc Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup.
Import QEQM.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0.
Import QC8c.Mq0.
Import Qsw7 QJjn QkMG.
Import QG8z QIsM.Mq2 Qdyh.Mq2 Qa8x.Mq3 Qa8x.
Import QJjn.Mq0.
Import QPZI.Mq3.
Import QBpZ QT7i Qv6q.
Import QzWc.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma lvl_mode_euni_pop : forall ss c hn,
0 <= ss <= 26 -> lvl_mode ST_escape_unicode ss = Some (c, hn) -> lvl_mode ss ss = Some (c, hn).
Proof.
intros ss c hn R Hm. enum_z R ss; vm_compute in Hm; vm_compute; congruence.
Qed.

#[using="Type"] Lemma le1_w : forall v : word, le1 v = [Z_to_bv 8 (bv_unsigned v)].
Proof. intros v. unfold le1, word_to_le_bytes. cbn. reflexivity. Qed.

Section PeEuni.
Variable HIx : heap_iface S4L.
Hypothesis MEMMOVE : memmove_stmt.

#[using="MEMMOVE"] Lemma pe_mapp :
forall (pf : pe_fix) (q : Z) (LB0 : list blk) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (ts : tstate) (cop ra b n : Z) (src : list byte)
(cb : byte) (j1 j2 utf : list byte) (sv : pe_saved) (errv : word) (T : TSet)
(gp t0 t1 t2 a3 a4 a5 a6 a7 s4 s5 s6 s8 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC HIx pf lo ->
PE_INV HIx pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv ->
bytes_at rsegs m b src -> Z.of_nat (length src) = n -> 0 <= n <= 8 ->
((pf_spf pf <= b /\ b + n <= pf_spf pf + PE_FRAME) \/ (b = UTF8REP_ADDR /\ n = 3)) ->
ra mod 2 = 0 -> 0 <= ra < 2^64 ->
(forall m' md' A' pbs' errv' r t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc',
PE_INV HIx pf q LB0 payload me lo m' md' A' (ts_set_pbs ts pbs') cb j1 j2 utf sv errv' ->
(r = n \/ r = 2^64 - 1) -> fsaved F F' -> (frm0 fc -> frm0 fc') ->
realizes rsegs (mkCfg (pe_ms rsegs pf ra cop (Z_to_bv 64 ra) gp t0' t1' t2' (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7' s4 s5 s6 s8 s10 t3' t4' t5' t6' F' fc' m') md') T) ->
realizes rsegs (mkCfg (pe_ms rsegs pf printbuf_memappend_entry cop (Z_to_bv 64 ra) gp t0 t1 t2 (Z_to_bv 64 (t_pb ts)) (Z_to_bv 64 b) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s4 s5 s6 s8 s10 t3 t4 t5 t6 F fc m) md) T.
Proof.
intros until fc. intros STC INV SRC SRCL Hn Hb RAE RAR K.
pose proof STC as (LO & LOS & SPA & HT & SP0 & LEN & SB0 & (SBL & RR & LENR)).
destruct INV as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof REST as (HP & LV & OBJ & ST & ERR & STR & PLEN & SBin & HPR & MDV & JCG).
destruct ts as [depth levels co pb pbs xx obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct xx as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl_]; pe_gen fl_; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
unfold ts_set_pbs in K. cbn [t_levels t_depth t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in K.
unfold tok_cells, tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in TOK. unfold pe_frame in FR. unfold pe_ms in *. cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
unfold_consts.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
pose proof PB as (buf & bpos & cap & pre & post & Epbs & Lpre & PBC). pose proof PBC as (Hbpos & Hcap & _).
pose proof HP as HP1. unfold pe_blocks, tstate_blocks, ts0 in HP1. cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_tk pf_md pf_mxd pf_fl] in HP1.
rewrite Epbs in HP1. cbn [app pf_mxd] in HP1.
pose proof (heap_blk S4L HIx _ _ _ _ buf cap HP1 ltac:(right; left; reflexivity)) as (_ & _ & _ & Hbufhi & _). unfold alloc_ceiling, sp_window_lo, stack_max_size in Hbufhi.
pose proof (heap_blk_img S4L HIx _ _ _ _ buf cap HP1 ltac:(right; left; reflexivity)) as Himg_b. cbn [hl_img_lo hl_img_hi S4L pf_mxd] in Himg_b.
eapply (memappend_cps HIx MEMMOVE) with (lo := lo) (b := b) (n := n) (src := src);
[ exact HP1 | exact PBC | lia | exact SRC | exact SRCL
| destruct Hb as [[Hb1 Hb2] | [-> ->]]; [left; left; rewrite ?unsigned_lit by lia; lia | left; right; left; intros a Ha; cbn; unfold s4_client_static, UTF8REP_ADDR in *; lia]
| destruct Hb as [[Hb1 Hb2] | [-> ->]]; [lia | unfold UTF8REP_ADDR; lia]
| destruct Hb as [[Hb1 Hb2] | [-> ->]]; [unfold PE_FRAME in *; lia | unfold UTF8REP_ADDR; lia]
| destruct Hb as [[Hb1 Hb2] | [-> ->]]; [unfold PE_FRAME in *; clear Himg_b; lia | unfold UTF8REP_ADDR; clear -Himg_b; lia] | .. ]; try alloc_side.
all: try clear Himg_b.
all: try (rewrite ?unsigned_lit by lia; first [exact ST | exact ERR | exact RAE]).
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
pose proof (heap_blk S4L HIx _ _ _ _ tk 72 HP ltac:(unfold pe_blocks; apply in_or_app; right; left; reflexivity)) as (_ & Htal & Htlo & Hthi & _).
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. cbn [hl_segs S4L pf_mxd] in FR.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in TOK; [| eapply client_range_block; [exact INtk2 | lia | cbn; lia]]. cbn [hl_segs S4L pf_mxd] in TOK.
apply (tstack_pres_g S4L _ _ _ _ _ _ HPR2 INq2) in TSK; [| exact LEN32].
assert (REST2 : PE_REST HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo m2 md2 A2 ts2 errv2).
{ eapply (PE_REST_call_pb HIx) with (ts := ts0) (LBc := (objbs ++ concat (map lvl_blocks levels)) ++ (tk, 72) :: (q, (32 * mxd)) :: LB0);
[exact STC | exact REST | exact VM2 | exact HPR2 | unfold ts0; cbn [t_objbs t_levels pf_mxd]; intros bb Hbb; apply in_or_app;
apply in_app_or in Hbb; destruct Hbb as [Hbb|Hbb]; [left; apply in_or_app; left; exact Hbb | apply in_app_or in Hbb; destruct Hbb as [Hbb|Hbb]; [left; apply in_or_app; right; exact Hbb | right; right; right; exact Hbb]]
| unfold pe_blocks, tstate_blocks; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_tk pf_md pf_mxd pf_fl]; exact HP2
| exact ST2 | exact ERR2]. }
assert (PBany : pbuf rsegs m2 pbs2 pb).
{ destruct OUT2 as [[_ PBS] | (_ & -> & -> & PC)]; [exact PBS|].
exists buf, bpos, cap, pre, post. split; [reflexivity|]. split; [exact Lpre | exact PC]. }
replace (ret_pc (Z_to_bv 64 ra)) with (Z_to_bv 64 ra) by (symmetry; apply ret_pc_even; [lia | exact RAE]).
eapply (K m2 md2 A2 pbs2 errv2 r); [| destruct OUT2 as [[-> _] | (-> & _)]; [left | right]; reflexivity | exact FS2 | exact FRM2].
split; [| exact REST2]. unfold PE_CORE, ts2; cbn. split; [exact LEN32|]. split; [exact D32|]. split; [lia|]. split; [reflexivity|].
split; [exact TOK|]. split; [exact PBany|]. split; [exact Hpb|]. split; [exact TSK | exact FR].
Qed.

#[using="Type"] Lemma euni_fin :
forall (pf : pe_fix) (q : Z) (LB0 : list blk) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (ts : tstate) (l : tlevel)
(cb : byte) (j1 j2 utf : list byte) (sv : pe_saved) (errv : word) (T : TSet)
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s8 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC HIx pf lo ->
PE_INV HIx pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_escape_unicode ->
(forall m',
PE_INV HIx pf q LB0 payload me lo m' md A (ts_set_level ts (TL (tl_ss l) (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) cb j1 j2 utf sv errv ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_BREAK (t_co ts) x1 gp t0 t1 t2 (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) (Z_to_bv 64 (tl_ss l)) a2 a3 a4 a5 a6 a7
s4 s5 s6 s8 s10 t3 t4 t5 t6 F fc m') md) T) ->
realizes rsegs (mkCfg (pe_ms rsegs pf 0x22dc0 (t_co ts) x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s8 s10 t3 t4 t5 t6 F fc m) md) T.
Proof.
intros until fc. intros STC INV Hl Hst Kbreak.
pose proof STC as (LO & LOS & SPA & HT & SP0 & LEN & SB0 & (SBL & RR & LENR)).
destruct INV as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof REST as (HP & LV & _).
destruct ts as [depth levels co pb pbs xx obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct xx as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl_]; pe_gen fl_; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
unfold ts_set_level in Kbreak. cbn [t_levels t_depth t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in Kbreak.
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
assert (HbseR : q <= bse /\ bse + 32 <= q + (32 * mxd)) by (subst bse; lia).
pose proof (munch_refl [(bse, bse + 32)] m) as MU.
stash PB. stash REST. stash TSK. clear LV.
apply rz_evt; [exact MOK|].
step. norm_sx32. step.
step. rewrite (unsigned_lit (Z.of_nat depth)) by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32.
step. replace (q + Z.of_nat depth * 32) with bse by lia.
step. norm_sx32. stepz.
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
subst bse; apply evt_RZ_done; apply (Kbreak mc)
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
apply lvl_mode_euni_pop; [exact SS26 | rewrite <- Hst; exact Hmode].
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

#[using="Type"] Lemma euni_hs :
forall (pf : pe_fix) (q : Z) (LB0 : list blk) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (ts : tstate) (l : tlevel)
(cb : byte) (j1 j2 utf : list byte) (sv : pe_saved) (errv : word) (T : TSet)
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s8 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC HIx pf lo ->
PE_INV HIx pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_escape_unicode ->
(forall m' a0' a2',
PE_INV HIx pf q LB0 payload me lo m' md A
(TST (t_depth ts) (lupd (t_levels ts) (t_depth ts) (TL ST_esc_need_escape (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)))
(t_co ts) (t_pb ts) (t_pbs ts)
(TS (ts_isd (t_x ts)) (ts_stpos (t_x ts)) (ts_choff (t_x ts)) (ts_err (t_x ts)) (Z_to_bv 64 0) a1 (ts_quote (t_x ts)))
(t_obj ts) (t_objs ts) (t_objbs ts)) cb j1 j2 utf sv errv ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_BREAK (t_co ts) x1 gp t0 t1 t2 a0' (Z_to_bv 64 ST_esc_need_escape) a2' a3 a4 a5 a6 a7
s4 s5 s6 s8 s10 t3 t4 t5 t6 F fc m') md) T) ->
realizes rsegs (mkCfg (pe_ms rsegs pf 0x22e40 (t_co ts) x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s8 s10 t3 t4 t5 t6 F fc m) md) T.
Proof.
intros until fc. intros STC INV Hl Hst Kbreak.
pose proof STC as (LO & LOS & SPA & HT & SP0 & LEN & SB0 & (SBL & RR & LENR)).
destruct INV as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof REST as (HP & LV & _).
destruct ts as [depth levels co pb pbs xx obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct xx as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl_]; pe_gen fl_; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
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
assert (HbseR : q <= bse /\ bse + 32 <= q + (32 * mxd)) by (subst bse; lia).
pose proof (munch_refl [(bse, bse + 32); (tk, tk + 72)] m) as MU.
stash PB. stash REST. stash TSK. clear LV.
apply rz_evt; [exact MOK|].
step. norm_sx32. step. stepz. step.
step. rewrite (unsigned_lit (Z.of_nat depth)) by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32.
step. replace (q + Z.of_nat depth * 32) with bse by lia.
step. step. stepz.
unstash PB. unstash REST. unstash TSK.
set (l1 := TL ST_esc_need_escape (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)).
assert (HW : Forall (pe_wtq (PEF tk oldl newl len lenr sb spf pmd mxd fl) q) [(bse, bse + 32); (tk, tk + 72)]).
{ apply Forall_cons; [right; cbn [fst snd pf_mxd]; lia |]. apply Forall_cons; [left; left; cbn [fst snd pf_tk pf_md pf_mxd pf_fl]; lia | apply Forall_nil]. }
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
match goal with L5 : rw_cells rsegs mc bse _ |- _ =>
assert (TSK3 : tstack rsegs mc q (lupd levels depth l1))
by (subst bse; eapply (tstack_put rsegs m _ q levels depth l1 [(tk, tk + 72)]); [exact TSK | lia | exact MU | exact WM | intros j Hj Hne; rewrite LEN32 in Hj; cbn; lia | exact L5]);
assert (PB3 : pbuf rsegs mc pbs pb)
by (eapply (pbuf_wtq HIx) with (ts := ts0); [exact STC | exact (proj1 REST) | exact PB | exact MU | exact WM | exact HW]);
assert (REST3 : PE_REST HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo mc md A ts0 errv)
by (eapply (PE_REST_private_write HIx) with (ts := ts0) in REST; [exact REST | exact STC | exact MU | exact WM | assumption | apply pe_wtq_private; exact HW]);
subst bse; apply evt_RZ_done; apply (Kbreak mc)
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
eapply lvl_cur_restate with (c' := c0); [exact (LV' depth l Hl) | exact Hmode | | unfold ST_esc_need_escape; lia | exact SS26 | left; reflexivity].
rewrite <- Hmode, Hst. apply lvl_mode_esc_same; [reflexivity | reflexivity | exact SS26].
* rewrite nth_error_lupd_neq in Hli by congruence. exact (LV' i li Hli).
+ revert OBJ'. unfold cur_st, ts0. cbn [t_levels t_depth t_objs t_objbs t_obj pf_mxd]. rewrite nth_error_lupd_eq by lia. cbn [tl_st pf_mxd].
rewrite Hl, Hst. cbn. intros OBJ'; exact OBJ'.
Qed.

Definition pe_frame8 (m : word -> option byte) (SPF : Z) (obj : Z) (cb : byte) (j1 j2 : list byte) (u0 u1 u2 u3 u4 u5 u6 u7 : byte) (sv : pe_saved) : Prop :=
rw_cells rsegs m SPF
[C8 (Z_to_bv 64 obj); CB 16 j1; C4 (nbw j2); CB 3 (skipn 4 j2); C1 cb; C1 u0; C1 u1; C1 u2; C1 u3; C1 u4; C1 u5; C1 u6; C1 u7;
C8 (pe_s11 sv); C8 (pe_s10 sv); C8 (pe_s9 sv); C8 (pe_s8 sv); C8 (pe_s7 sv); C8 (pe_s6 sv);
C8 (pe_s5 sv); C8 (pe_s4 sv); C8 (pe_s3 sv); C8 (pe_s2 sv); C8 (pe_s1 sv); C8 (pe_s0 sv); C8 (pe_ra sv)].

#[using="Type"] Lemma pe_frame_split8 : forall m SPF obj cb j1 j2 utf sv,
pe_frame rsegs m SPF obj cb j1 j2 utf sv ->
exists u0 u1 u2 u3 u4 u5 u6 u7, utf = [u0; u1; u2; u3; u4; u5; u6; u7] /\ pe_frame8 m SPF obj cb j1 j2 u0 u1 u2 u3 u4 u5 u6 u7 sv.
Proof.
intros m SPF obj cb j1 j2 utf sv H. unfold pe_frame in H.
pose proof H as [[Hwf _] _]. cbn in Hwf. destruct Hwf as (_ & L1 & _ & L2 & _ & L8 & _).
destruct utf as [|u0 [|u1 [|u2 [|u3 [|u4 [|u5 [|u6 [|u7 [|? ?]]]]]]]]]; cbn in L8; try discriminate.
exists u0, u1, u2, u3, u4, u5, u6, u7. split; [reflexivity|]. unfold pe_frame8.
eapply rw_cells_recast; [exact H | cbn; repeat split; assumption | reflexivity | reflexivity].
Qed.

#[using="Type"] Lemma pe_frame_join8 : forall m SPF obj cb j1 j2 u0 u1 u2 u3 u4 u5 u6 u7 sv,
pe_frame8 m SPF obj cb j1 j2 u0 u1 u2 u3 u4 u5 u6 u7 sv -> pe_frame rsegs m SPF obj cb j1 j2 [u0; u1; u2; u3; u4; u5; u6; u7] sv.
Proof.
intros until sv. intros H. unfold pe_frame8 in H. pose proof H as [[Hwf _] _]. cbn in Hwf. destruct Hwf as (_ & L1 & _ & L2 & _).
unfold pe_frame. eapply rw_cells_recast; [exact H | cbn; repeat split; assumption | reflexivity | reflexivity].
Qed.

#[using="Type"] Lemma pe_frame_utf : forall m SPF obj cb j1 j2 utf sv k,
pe_frame rsegs m SPF obj cb j1 j2 utf sv -> (k <= 8)%nat -> bytes_at rsegs m (SPF + 32) (firstn k utf).
Proof.
intros m SPF obj cb j1 j2 utf sv k H Hk. unfold pe_frame in H.
pose proof H as [[Hwf _] _]. cbn in Hwf. destruct Hwf as (_ & L1 & _ & L2 & _ & L8 & _).
change ([C8 (Z_to_bv 64 obj); CB 16 j1; C4 (nbw j2); CB 3 (skipn 4 j2); C1 cb; CB 8 utf;
C8 (pe_s11 sv); C8 (pe_s10 sv); C8 (pe_s9 sv); C8 (pe_s8 sv); C8 (pe_s7 sv); C8 (pe_s6 sv);
C8 (pe_s5 sv); C8 (pe_s4 sv); C8 (pe_s3 sv); C8 (pe_s2 sv); C8 (pe_s1 sv); C8 (pe_s0 sv); C8 (pe_ra sv)])
with ([C8 (Z_to_bv 64 obj); CB 16 j1; C4 (nbw j2); CB 3 (skipn 4 j2); C1 cb] ++ ([CB 8 utf] ++ [
C8 (pe_s11 sv); C8 (pe_s10 sv); C8 (pe_s9 sv); C8 (pe_s8 sv); C8 (pe_s7 sv); C8 (pe_s6 sv);
C8 (pe_s5 sv); C8 (pe_s4 sv); C8 (pe_s3 sv); C8 (pe_s2 sv); C8 (pe_s1 sv); C8 (pe_s0 sv); C8 (pe_ra sv)])) in H.
apply (proj1 (rw_cells_app rsegs _ _ _ _)) in H as [_ H]. apply (proj1 (rw_cells_app rsegs _ _ _ _)) in H as [H _].
cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ pf_mxd] in H.
destruct H as [[_ HB] _]. cbn [cells_bytes cbytes app pf_mxd] in HB. rewrite app_nil_r in HB.
rewrite <- (firstn_skipn k utf) in HB. apply bytes_at_app in HB as [HB _].
replace (SPF + Z.of_nat 32) with (SPF + 32) in HB by lia. exact HB.
Qed.

#[using="Type"] Lemma PE_INV_retok : forall pf q LB0 payload me lo m mc md A ts cb cb' j1 j2 utf utf' sv errv x' co',
PE_STATIC HIx pf lo ->
PE_INV HIx pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv ->
munch [(pf_tk pf, pf_tk pf + 72); (pf_spf pf, pf_spf pf + PE_FRAME)] m mc -> wmono rsegs m mc -> mem_inv rsegs mc ->
rw_cells rsegs mc (pf_tk pf) (tok_cells_g (pf_mxd pf) (pf_fl pf) (t_pb ts) (Z.of_nat (t_depth ts)) q x') ->
0 <= co' <= pf_len pf -> ts_choff x' = Z_to_bv 64 co' ->
pe_frame rsegs mc (pf_spf pf) (t_obj ts) cb' j1 j2 utf' sv ->
PE_INV HIx pf q LB0 payload me lo mc md A
(TST (t_depth ts) (t_levels ts) co' (t_pb ts) (t_pbs ts) x' (t_obj ts) (t_objs ts) (t_objbs ts)) cb' j1 j2 utf' sv errv.
Proof.
intros until co'. intros STC [CORE REST] MU WM MI TOK' Hco' CH FR'.
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
assert (HW : Forall (pe_wtf pf) [(pf_tk pf, pf_tk pf + 72); (pf_spf pf, pf_spf pf + PE_FRAME)]).
{ apply Forall_cons; [left; cbn; lia|]. apply Forall_cons; [right; cbn; lia | apply Forall_nil]. }
split.
- unfold PE_CORE; cbn. split; [exact LEN32|]. split; [exact D32|]. split; [exact Hco'|]. split; [exact CH|].
split; [exact TOK'|]. split; [| split; [exact Hpb | split; [| exact FR']]].
+ eapply (pbuf_wtf HIx) with (ts := ts); [exact STC | exact (proj1 REST) | exact PB | exact MU | exact WM | exact HW].
+ eapply (tstack_wtf HIx) with (ts := ts); [exact STC | exact (proj1 REST) | exact TSK | exact LEN32 | exact MU | exact WM | exact HW].
- eapply (PE_REST_private_write HIx) with (ts := ts) in REST; [exact REST | exact STC | exact MU | exact WM | exact MI | apply pe_wtf_private; exact HW].
Qed.

#[using="MEMMOVE"] Lemma euni_enc :
forall (pf : pe_fix) (q : Z) (LB0 : list blk) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (ts : tstate) (l : tlevel)
(cb : byte) (j1 j2 utf : list byte) (sv : pe_saved) (errv : word) (T : TSet)
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s8 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC HIx pf lo ->
PE_INV HIx pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_escape_unicode ->
bytes_at rsegs me UTF8REP_ADDR utf8rep ->

(forall m' md' A' pbs' errv' st' (ucs' high' : word) utf' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s8' s10' t3' t4' t5' t6' F' fc',
(st' = tl_ss l \/ st' = ST_esc_need_escape) ->
PE_INV HIx pf q LB0 payload me lo m' md' A'
(TST (t_depth ts) (lupd (t_levels ts) (t_depth ts) (TL st' (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)))
(t_co ts) (t_pb ts) pbs'
(TS (ts_isd (t_x ts)) (ts_stpos (t_x ts)) (ts_choff (t_x ts)) (ts_err (t_x ts)) ucs' high' (ts_quote (t_x ts)))
(t_obj ts) (t_objs ts) (t_objbs ts)) cb j1 j2 utf' sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_BREAK (t_co ts) x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s8' s10' t3' t4' t5' t6' F' fc' m') md') T) ->

(forall m' md' A' pbs' errv' (ucs' high' : word) utf' x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s8' s10' t3' t4' t5' t6' F' fc',
PE_INV HIx pf q LB0 payload me lo m' md' A'
(TST (t_depth ts) (t_levels ts) (t_co ts) (t_pb ts) pbs'
(TS (ts_isd (t_x ts)) (ts_stpos (t_x ts)) (ts_choff (t_x ts)) (ts_err (t_x ts)) ucs' high' (ts_quote (t_x ts)))
(t_obj ts) (t_objs ts) (t_objbs ts)) cb j1 j2 utf' sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_ERR (t_co ts) x1' gp' t0' t1' t2' (Z_to_bv 64 16) a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s8' s10' t3' t4' t5' t6' F' fc' m') md') T) ->
realizes rsegs (mkCfg (pe_ms rsegs pf 0x22da0 (t_co ts) x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s8 s10 t3 t4 t5 t6 F fc m) md) T.
Proof.
intros until fc. intros STC INV Hl Hst UTF Kbreak Kerr16.
pose proof INV as INV0.
pose proof STC as (LO & LOS & SPA & HT & SP0 & LEN & SB0 & (SBL & RR & LENR)).
destruct INV as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof REST as (HP & LV & _ & _ & _ & _ & _ & _ & HPR0 & MDV0 & JCG0).
destruct ts as [depth levels co pb pbs xx obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct xx as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl_]; pe_gen fl_; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct (pe_frame_split8 _ _ _ _ _ _ _ _ FR) as (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & -> & FR8). unfold pe_frame8 in FR8. clear FR.
unfold tok_cells, tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in TOK. unfold pe_ms in *. cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
unfold_consts.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocks; apply in_or_app; right; left; reflexivity).
pose proof (heap_blk S4L HIx _ _ _ _ tk 72 HP INtk) as (_ & Htal & Htlo & Hthi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hthi.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L pf_mxd] in MI.
pose proof (wmono_refl rsegs m) as WM.
pose proof (munch_refl [(tk, tk + 72); (spf, spf + 144)] m) as MU.
assert (SRCU : bytes_at rsegs m UTF8REP_ADDR utf8rep).
{ eapply (heap_presx_bytes_at S4L); [exact HPR0 | exact UTF |]. right; left. intros a Ha. cbn in Ha. cbn. unfold s4_client_static, s4_volatile. unfold UTF8REP_ADDR in Ha. lia. }
unfold UTF8REP_ADDR in SRCU.

assert (RET3c : forall mc mdc Ac pbsc errvc r nn ucs' high' utf' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc',
PE_INV HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo mc mdc Ac
(TST depth levels co pb pbsc (TS isd stpos (Z_to_bv 64 co) err ucs' high' quote) obj objs objbs) cb j1 j2 utf' sv errvc ->
(r = nn \/ r = 2^64 - 1) -> 0 <= nn <= 8 -> fsaved F F' -> (frm0 fc -> frm0 fc') ->
realizes rsegs (mkCfg (MS (mkR (Z_to_bv 64 0x22dbc) (Z_to_bv 64 spf) gp (Z_to_bv 64 482928) t0' t1' t2' (Z_to_bv 64 tk) (Z_to_bv 64 oldl) (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7'
(Z_to_bv 64 newl) (Z_to_bv 64 lenr) s4 s5 s6 (Z_to_bv 64 26) s8 (Z_to_bv 64 (sb + co)) s10 (Z_to_bv 64 79024) t3' t4' t5' t6')
F' (Z_to_bv 64 0x22dbc) fc' None mc (seg_rom rsegs)) mdc) T).
{ intros mc mdc Ac pbsc errvc r nn ucs' high' utf' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' INVc Hr Hnn FS' FRM'.
pose proof (heap_model_ok _ _ _ _ _ _ (proj1 (proj2 INVc))) as MOKc.
apply rz_evt; [exact MOKc|].
destruct Hr as [-> | ->].
- step. if_falsex. apply evt_RZ_done.
eapply (euni_fin (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo mc mdc Ac
(TST depth levels co pb pbsc (TS isd stpos (Z_to_bv 64 co) err ucs' high' quote) obj objs objbs) l cb);
[exact STC | exact INVc | exact Hl | exact Hst |].
unfold ts_set_level; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd]. intros m'' INV''.
eapply Kbreak; [left; reflexivity | exact INV'' | exact FS' | exact FRM'].
- replace (Z_to_bv 64 (2^64 - 1)) with (Z_to_bv 64 (-1)) by (apply bv_eq; vm_compute; reflexivity).
step. if_true. step. step. apply evt_RZ_done. eapply Kerr16; [exact INVc | exact FS' | exact FRM']. }

assert (CALL : forall mc nn (ra : Z) v0 v1 v2 v3 t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
rw_cells rsegs mc tk
[C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 pb); C4 (Z_to_bv 64 mxd); C4 (Z_to_bv 64 (Z.of_nat depth)); C4 isd; C4 stpos;
C4 (Z_to_bv 64 co); C4 err; C4 ucs; C4 high; C1 quote; CB 7 (repeat (Z_to_bv 8 0) 7); C8 (Z_to_bv 64 q); C4 (Z_to_bv 64 fl); C4 (Z_to_bv 64 0)] ->
pe_frame8 mc spf obj cb j1 j2 v0 v1 v2 v3 u4 u5 u6 u7 sv ->
munch [(tk, tk + 72); (spf, spf + 144)] m mc -> wmono rsegs m mc -> mem_inv rsegs mc ->
1 <= nn <= 4 -> ra mod 2 = 0 -> 0 <= ra < 2^64 ->
(forall m' md' A' pbs' errv' r t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' F' fc',
PE_INV HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo m' md' A'
(TST depth levels co pb pbs' (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) cb j1 j2 [v0; v1; v2; v3; u4; u5; u6; u7] sv errv' ->
(r = nn \/ r = 2^64 - 1) -> fsaved F F' -> (frm0 fc -> frm0 fc') ->
realizes rsegs (mkCfg (MS (mkR (Z_to_bv 64 ra) (Z_to_bv 64 spf) gp (Z_to_bv 64 482928) t0'' t1'' t2'' (Z_to_bv 64 tk) (Z_to_bv 64 oldl) (Z_to_bv 64 r) a1'' a2'' a3'' a4'' a5'' a6'' a7''
(Z_to_bv 64 newl) (Z_to_bv 64 lenr) s4 s5 s6 (Z_to_bv 64 26) s8 (Z_to_bv 64 (sb + co)) s10 (Z_to_bv 64 79024) t3'' t4'' t5'' t6'')
F' (Z_to_bv 64 ra) fc' None m' (seg_rom rsegs)) md') T) ->
evt rsegs (RZ rsegs md T)
(MS (mkR (Z_to_bv 64 ra) (Z_to_bv 64 spf) gp (Z_to_bv 64 482928) t0' t1' t2' (Z_to_bv 64 tk) (Z_to_bv 64 oldl) (Z_to_bv 64 pb) (Z_to_bv 64 (spf + 32)) (Z_to_bv 64 nn) a3' a4' a5' a6' a7'
(Z_to_bv 64 newl) (Z_to_bv 64 lenr) s4 s5 s6 (Z_to_bv 64 26) s8 (Z_to_bv 64 (sb + co)) s10 (Z_to_bv 64 79024) t3' t4' t5' t6')
F (Z_to_bv 64 printbuf_memappend_entry) fc None mc (seg_rom rsegs))).
{ intros mc nn ra v0 v1 v2 v3 t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' TOK' FR8' MU' WM' MI' Hnn RAE RAR K.
apply pe_frame_join8 in FR8'.
assert (INV1 : PE_INV HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo mc md A
(TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) cb j1 j2 [v0; v1; v2; v3; u4; u5; u6; u7] sv errv).
{ eapply (PE_INV_retok _ q LB0 payload me lo m mc md A ts0); [exact STC | exact INV0 | exact MU' | exact WM' | exact MI' | exact TOK' | cbn; lia | reflexivity | exact FR8']. }
apply evt_RZ_done.
eapply (pe_mapp (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo mc md A (TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) co ra (spf + 32) nn (firstn (Z.to_nat nn) [v0; v1; v2; v3; u4; u5; u6; u7]) cb);
[exact STC | exact INV1 | eapply pe_frame_utf; [exact FR8' | lia] | rewrite length_firstn; cbn [length pf_mxd]; lia | lia
| left; cbn [pf_spf pf_md pf_mxd pf_fl]; unfold PE_FRAME; lia | exact RAE | exact RAR |].
unfold ts_set_pbs; cbn [t_levels t_depth t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_oldl pf_newl pf_len pf_sb pf_tk pf_spf pf_md pf_mxd pf_fl]. exact K. }
stash PB. stash REST. stash TSK. clear LV HPR0.
apply rz_evt; [exact MOK|].

step. step.
lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => destruct c end.
2:{
step. step. rewrite le1_w. mem_after_store. step. step. step.
eapply CALL; [exact TOK | exact FR8 | exact MU | exact WM | exact MI | lia | reflexivity | lia |].
intros. eapply RET3c; [eassumption | eassumption | lia | assumption | assumption]. }

step. step.
lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => destruct c end.
2:{
step. step. step. step. step.
step. rewrite le1_w. mem_after_store. step. rewrite le1_w. mem_after_store.
step. step. step. step.
eapply CALL; [exact TOK | exact FR8 | exact MU | exact WM | exact MI | lia | reflexivity | lia |].
intros. eapply RET3c; [eassumption | eassumption | lia | assumption | assumption]. }

step. step. step. step.
lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => destruct c end.
{
step. step. step. step. step. step.
unstash PB. unstash REST. unstash TSK. apply evt_RZ_done.
apply pe_frame_join8 in FR8.
eapply (pe_mapp (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo m md A (TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) co 0x22dbc 0x64ee0 3 utf8rep cb);
[exact STC | exact INV0 | exact SRCU | reflexivity | lia | right; split; reflexivity | reflexivity | lia |].
unfold ts_set_pbs; cbn [t_levels t_depth t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_oldl pf_newl pf_len pf_sb pf_tk pf_spf pf_md pf_mxd pf_fl].
intros. eapply RET3c; [eassumption | eassumption | lia | assumption | assumption]. }
step. step. step.
lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => destruct c end.
2:{
unstash PB. unstash REST. unstash TSK. apply evt_RZ_done. apply pe_frame_join8 in FR8.
eapply (euni_hs (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo m md A (TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) l cb);
[exact STC | exact INV0 | exact Hl | exact Hst |].
cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd].
intros m'' a0'' a2'' INV''. eapply Kbreak; [right; reflexivity | exact INV'' | apply fsaved_refl | intros Hf; exact Hf]. }

step. step.
lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => destruct c end.
2:{
step. step. step. step. step. step. step. step.
step. rewrite le1_w. mem_after_store. step. rewrite le1_w. mem_after_store. step. rewrite le1_w. mem_after_store.
step. step. step.
eapply CALL; [exact TOK | exact FR8 | exact MU | exact WM | exact MI | lia | reflexivity | lia |].
intros m' md' A' pbs' errv' r t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' F' fc' INV' Hr FS' FRM'.
pose proof (heap_model_ok _ _ _ _ _ _ (proj1 (proj2 INV'))) as MOK'. apply rz_evt; [exact MOK'|].
destruct Hr as [-> | ->].
- step. if_true. step. step. apply evt_RZ_done.
eapply (euni_fin (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo m' md' A'
(TST depth levels co pb pbs' (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) l cb);
[exact STC | exact INV' | exact Hl | exact Hst |].
unfold ts_set_level; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd]. intros m'' INV''.
eapply Kbreak; [left; reflexivity | exact INV'' | exact FS' | exact FRM'].
- replace (Z_to_bv 64 (2^64 - 1)) with (Z_to_bv 64 (-1)) by (apply bv_eq; vm_compute; reflexivity).
step. if_false. step. step. step. apply evt_RZ_done. eapply Kerr16; [exact INV' | exact FS' | exact FRM']. }

step. step.
lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => destruct c end.
{
step. step. step. step. step.
unstash PB. unstash REST. unstash TSK. apply evt_RZ_done.
apply pe_frame_join8 in FR8.
eapply (pe_mapp (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo m md A (TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) co 0x22f94 0x64ee0 3 utf8rep cb);
[exact STC | exact INV0 | exact SRCU | reflexivity | lia | right; split; reflexivity | reflexivity | lia |].
unfold ts_set_pbs; cbn [t_levels t_depth t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_oldl pf_newl pf_len pf_sb pf_tk pf_spf pf_md pf_mxd pf_fl].
intros m' md' A' pbs' errv' r t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' F' fc' INV' Hr FS' FRM'.
unfold pe_ms; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl].
pose proof (heap_model_ok _ _ _ _ _ _ (proj1 (proj2 INV'))) as MOK'. apply rz_evt; [exact MOK'|].
destruct Hr as [-> | ->].
- step. step. if_true. apply evt_RZ_done.
eapply (euni_fin (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo m' md' A'
(TST depth levels co pb pbs' (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) l cb);
[exact STC | exact INV' | exact Hl | exact Hst |].
unfold ts_set_level; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd]. intros m'' INV''.
eapply Kbreak; [left; reflexivity | exact INV'' | exact FS' | exact FRM'].
- replace (Z_to_bv 64 (2^64 - 1)) with (Z_to_bv 64 (-1)) by (apply bv_eq; vm_compute; reflexivity).
step. step. if_false. step. step. step. apply evt_RZ_done. eapply Kerr16; [exact INV' | exact FS' | exact FRM']. }

step. step. step. step. step. step. step. step. step. step. step.
step. rewrite le1_w. mem_after_store. step. rewrite le1_w. mem_after_store. step. rewrite le1_w. mem_after_store. step. rewrite le1_w. mem_after_store.
step. step. step.
eapply CALL; [exact TOK | exact FR8 | exact MU | exact WM | exact MI | lia | reflexivity | lia |].
intros m' md' A' pbs' errv' r t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' F' fc' INV' Hr FS' FRM'.
pose proof (heap_model_ok _ _ _ _ _ _ (proj1 (proj2 INV'))) as MOK'. apply rz_evt; [exact MOK'|].
destruct Hr as [-> | ->].
- step. if_false. step. step. apply evt_RZ_done.
eapply (euni_fin (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo m' md' A'
(TST depth levels co pb pbs' (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) l cb);
[exact STC | exact INV' | exact Hl | exact Hst |].
unfold ts_set_level; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd]. intros m'' INV''.
eapply Kbreak; [left; reflexivity | exact INV'' | exact FS' | exact FRM'].
- replace (Z_to_bv 64 (2^64 - 1)) with (Z_to_bv 64 (-1)) by (apply bv_eq; vm_compute; reflexivity).
step. if_true. step. step. apply evt_RZ_done. eapply Kerr16; [exact INV' | exact FS' | exact FRM'].
Qed.

#[using="MEMMOVE"] Lemma euni_tail :
forall (pf : pe_fix) (q : Z) (LB0 : list blk) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (ts : tstate) (l : tlevel)
(cb : byte) (j1 j2 utf : list byte) (sv : pe_saved) (errv : word) (T : TSet)
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s8 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC HIx pf lo ->
PE_INV HIx pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_escape_unicode ->
bytes_at rsegs me UTF8REP_ADDR utf8rep ->
(forall m' md' A' pbs' errv' st' (stpos' ucs' high' : word) utf' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s8' s10' t3' t4' t5' t6' F' fc',
(st' = tl_ss l \/ st' = ST_esc_need_escape) ->
PE_INV HIx pf q LB0 payload me lo m' md' A'
(TST (t_depth ts) (lupd (t_levels ts) (t_depth ts) (TL st' (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)))
(t_co ts) (t_pb ts) pbs'
(TS (ts_isd (t_x ts)) stpos' (ts_choff (t_x ts)) (ts_err (t_x ts)) ucs' high' (ts_quote (t_x ts)))
(t_obj ts) (t_objs ts) (t_objbs ts)) cb j1 j2 utf' sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_BREAK (t_co ts) x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s8' s10' t3' t4' t5' t6' F' fc' m') md') T) ->
(forall m' md' A' pbs' errv' (stpos' ucs' high' : word) utf' x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s8' s10' t3' t4' t5' t6' F' fc',
PE_INV HIx pf q LB0 payload me lo m' md' A'
(TST (t_depth ts) (t_levels ts) (t_co ts) (t_pb ts) pbs'
(TS (ts_isd (t_x ts)) stpos' (ts_choff (t_x ts)) (ts_err (t_x ts)) ucs' high' (ts_quote (t_x ts)))
(t_obj ts) (t_objs ts) (t_objbs ts)) cb j1 j2 utf' sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_ERR (t_co ts) x1' gp' t0' t1' t2' (Z_to_bv 64 16) a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s8' s10' t3' t4' t5' t6' F' fc' m') md') T) ->
realizes rsegs (mkCfg (pe_ms rsegs pf 0x22c54 (t_co ts) x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s8 s10 t3 t4 t5 t6 F fc m) md) T.
Proof.
intros until fc. intros STC INV Hl Hst UTF Kbreak Kerr16.
pose proof INV as INV0.
pose proof STC as (LO & LOS & SPA & HT & SP0 & LEN & SB0 & (SBL & RR & LENR)).
destruct INV as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof REST as (HP & LV & _ & _ & _ & _ & _ & _ & HPR0 & MDV0 & JCG0).
destruct ts as [depth levels co pb pbs xx obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct xx as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl_]; pe_gen fl_; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
unfold tok_cells, tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in TOK. unfold pe_frame in FR. unfold pe_ms in *. cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
unfold_consts.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocks; apply in_or_app; right; left; reflexivity).
pose proof (heap_blk S4L HIx _ _ _ _ tk 72 HP INtk) as (_ & Htal & Htlo & Hthi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hthi.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L pf_mxd] in MI.
pose proof (wmono_refl rsegs m) as WM.
pose proof (munch_refl [(tk, tk + 72); (spf, spf + 144)] m) as MU.
assert (SRCU : bytes_at rsegs m UTF8REP_ADDR utf8rep).
{ eapply (heap_presx_bytes_at S4L); [exact HPR0 | exact UTF |]. right; left. intros a Ha. cbn in Ha. cbn. unfold s4_client_static, s4_volatile. unfold UTF8REP_ADDR in Ha. lia. }
unfold UTF8REP_ADDR in SRCU.
assert (SRCUk : True -> bytes_at rsegs m 0x64ee0 utf8rep) by (intros _; exact SRCU). clear SRCU.
pose proof (heap_blk_img S4L HIx _ _ _ _ tk 72 HP INtk) as Himg_t. cbn [hl_img_lo hl_img_hi S4L pf_mxd] in Himg_t. stash Himg_t.

assert (ENC : forall mc (stpos' ucs' high' uu : word) a0' a2' a3' a4',
rw_cells rsegs mc tk
[C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 pb); C4 (Z_to_bv 64 mxd); C4 (Z_to_bv 64 (Z.of_nat depth)); C4 isd; C4 stpos';
C4 (Z_to_bv 64 co); C4 err; C4 ucs'; C4 high'; C1 quote; CB 7 (repeat (Z_to_bv 8 0) 7); C8 (Z_to_bv 64 q); C4 (Z_to_bv 64 fl); C4 (Z_to_bv 64 0)] ->
rw_cells rsegs mc spf [C8 (Z_to_bv 64 obj); CB 16 j1; C4 (nbw j2); CB 3 (skipn 4 j2); C1 cb; CB 8 utf;
C8 (pe_s11 sv); C8 (pe_s10 sv); C8 (pe_s9 sv); C8 (pe_s8 sv); C8 (pe_s7 sv); C8 (pe_s6 sv);
C8 (pe_s5 sv); C8 (pe_s4 sv); C8 (pe_s3 sv); C8 (pe_s2 sv); C8 (pe_s1 sv); C8 (pe_s0 sv); C8 (pe_ra sv)] ->
munch [(tk, tk + 72); (spf, spf + 144)] m mc -> wmono rsegs m mc -> mem_inv rsegs mc ->
evt rsegs (RZ rsegs md T)
(MS (mkR x1 (Z_to_bv 64 spf) gp (Z_to_bv 64 482928) t0 t1 t2 (Z_to_bv 64 tk) (Z_to_bv 64 oldl) a0' uu a2' a3' a4' a5 a6 a7
(Z_to_bv 64 newl) (Z_to_bv 64 lenr) s4 s5 s6 (Z_to_bv 64 26) s8 (Z_to_bv 64 (sb + co)) s10 (Z_to_bv 64 79024) t3 t4 t5 t6)
F (Z_to_bv 64 0x22da0) fc None mc (seg_rom rsegs))).
{ intros mc stpos' ucs' high' uu a0' a2' a3' a4' TOK' FR' MU' WM' MI'.
assert (INV1 : PE_INV HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo mc md A
(TST depth levels co pb pbs (TS isd stpos' (Z_to_bv 64 co) err ucs' high' quote) obj objs objbs) cb j1 j2 utf sv errv).
{ eapply (PE_INV_retok _ q LB0 payload me lo m mc md A ts0); [exact STC | exact INV0 | exact MU' | exact WM' | exact MI' | exact TOK' | cbn; lia | reflexivity | exact FR']. }
apply evt_RZ_done.
eapply (euni_enc (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo mc md A
(TST depth levels co pb pbs (TS isd stpos' (Z_to_bv 64 co) err ucs' high' quote) obj objs objbs) l cb);
[exact STC | exact INV1 | exact Hl | exact Hst | exact UTF | |];
cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_sb pf_len pf_md pf_mxd pf_fl].
- intros. eapply Kbreak; eassumption.
- intros. eapply Kerr16; eassumption. }
stash PB. stash REST. stash TSK. clear LV HPR0.
apply rz_evt; [exact MOK|].

step. stepz. step.
lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => destruct c end.
{
eapply ENC; [exact TOK | exact FR | exact MU | exact WM | exact MI]. }

step. step. step.
lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => destruct c end.
2:{
step. step. step. step. step. step. step. step. stepz.
eapply ENC; [exact TOK | exact FR | exact MU | exact WM | exact MI]. }

step. step. step. step. step.
unstash PB. unstash REST. unstash TSK.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (INV1 : PE_INV HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo mc md A
(TST depth levels co pb pbs (TS isd (Z_to_bv 64 0) (Z_to_bv 64 co) err ucs high quote) obj objs objbs) cb j1 j2 utf sv errv)
by (eapply (PE_INV_retok _ q LB0 payload me lo m mc md A ts0); [exact STC | exact INV0 | exact MU | exact WM | exact MI | exact TOK | cbn; lia | reflexivity | exact FR])
end.
apply evt_RZ_done.
lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mc _) _) _ =>
eapply (pe_mapp (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo mc md A (TST depth levels co pb pbs (TS isd (Z_to_bv 64 0) (Z_to_bv 64 co) err ucs high quote) obj objs objbs) co 0x22d94 0x64ee0 3 utf8rep cb);
[exact STC | exact INV1 | eapply bytes_at_transport; [exact (SRCUk I) | exact MU | unstash Himg_t; cbn; unfold PE_FRAME in *; lia] | reflexivity | lia | right; split; reflexivity | reflexivity | lia |]
end.
unfold ts_set_pbs; cbn [t_levels t_depth t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_oldl pf_newl pf_len pf_sb pf_tk pf_spf pf_md pf_mxd pf_fl].
intros m' md' A' pbs' errv' r t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' F' fc' INV' Hr FS' FRM'.
unfold pe_ms; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl].
pose proof (heap_model_ok _ _ _ _ _ _ (proj1 (proj2 INV'))) as MOK'. apply rz_evt; [exact MOK'|].
destruct Hr as [-> | ->].
2:{ replace (Z_to_bv 64 (2^64 - 1)) with (Z_to_bv 64 (-1)) by (apply bv_eq; vm_compute; reflexivity).
step. if_true. step. step. apply evt_RZ_done. eapply Kerr16; [exact INV' | exact FS' | exact FRM']. }
step. if_false.

pose proof INV' as [CORE' REST']. destruct CORE' as (_ & _ & _ & _ & TOK' & PB' & _ & TSK' & FR').
cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_tk pf_spf pf_md pf_mxd pf_fl] in TOK', FR', PB', TSK'.
unfold tok_cells, tok_cells_g in TOK'. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in TOK'. unfold pe_frame in FR'.
pose proof (heap_mem_inv _ _ _ _ _ _ (proj1 REST')) as MI'. cbn [hl_segs S4L pf_mxd] in MI'.
pose proof (wmono_refl rsegs m') as WM'. pose proof (munch_refl [(tk, tk + 72); (spf, spf + 144)] m') as MU'.
stash PB'. stash REST'. stash TSK'.
step. stepz.
unstash PB'. unstash REST'. unstash TSK'.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (INV2 : PE_INV HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo mc md' A'
(TST depth levels co pb pbs' (TS isd (Z_to_bv 64 0) (Z_to_bv 64 co) err ucs (Z_to_bv 64 0) quote) obj objs objbs) cb j1 j2 utf sv errv')
by (eapply (PE_INV_retok _ q LB0 payload me lo m' mc md' A' (TST depth levels co pb pbs' (TS isd (Z_to_bv 64 0) (Z_to_bv 64 co) err ucs high quote) obj objs objbs));
[exact STC | exact INV' | exact MU' | exact WM' | exact MI' | exact TOK' | cbn; lia | reflexivity | exact FR'])
end.
apply evt_RZ_done.
lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mc _) _) _ =>
eapply (euni_enc (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo mc md' A'
(TST depth levels co pb pbs' (TS isd (Z_to_bv 64 0) (Z_to_bv 64 co) err ucs (Z_to_bv 64 0) quote) obj objs objbs) l cb);
[exact STC | exact INV2 | exact Hl | exact Hst | exact UTF | |];
cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_sb pf_len pf_md pf_mxd pf_fl]
end.
- intros. eapply Kbreak; [eassumption | eassumption | eapply fsaved_trans; [exact FS' | eassumption] | intros Hf; auto].
- intros. eapply Kerr16; [eassumption | eapply fsaved_trans; [exact FS' | eassumption] | intros Hf; auto].
Qed.

#[using="Type"] Lemma pe_eof38 :
forall (pf : pe_fix) (q : Z) (LB0 : list blk) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (ts : tstate) (cop : Z)
(cb : byte) (j1 j2 utf : list byte) (sv : pe_saved) (errv : word) (T : TSet)
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC HIx pf lo ->
PE_INV HIx pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv ->
t_co ts = pf_len pf ->
(forall m' (e : word) a0' a1',
PE_INV HIx pf q LB0 payload me lo m' md A (ts_set_err ts e) cb j1 j2 utf sv errv ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_OUT cop x1 gp t0 t1 t2 a0' a1' a2 a3 a4 a5 a6 a7 s4 s5 s6
(Z_to_bv 64 q) (Z_to_bv 64 (Z.of_nat (t_depth ts))) t3 t4 t5 t6 F fc m') md) T) ->
realizes rsegs (mkCfg (pe_ms rsegs pf 0x22fb8 cop x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6
(Z_to_bv 64 q) (Z_to_bv 64 (Z.of_nat (t_depth ts))) t3 t4 t5 t6 F fc m) md) T.
Proof.
intros until fc. intros STC INV Heof Kout.
pose proof STC as (LO & LOS & SPA & HT & SP0 & LEN & SB0 & (SBL & RR & LENR)).
destruct INV as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof REST as (HP & LV & _).
destruct ts as [depth levels co pb pbs xx obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct xx as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff. subst co.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl_]; pe_gen fl_; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
unfold ts_set_err in Kout. cbn [t_levels t_depth t_co t_pb t_pbs t_x t_obj t_objs t_objbs ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in Kout.
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
assert (TAIL : forall (e : word) mc a0' a1',
rw_cells rsegs mc tk
[C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 pb); C4 (Z_to_bv 64 mxd); C4 (Z_to_bv 64 (Z.of_nat depth)); C4 isd; C4 stpos;
C4 (Z_to_bv 64 len); C4 e; C4 ucs; C4 high; C1 quote; CB 7 (repeat (Z_to_bv 8 0) 7); C8 (Z_to_bv 64 q); C4 (Z_to_bv 64 fl); C4 (Z_to_bv 64 0)] ->
munch [(tk, tk + 72)] m mc -> wmono rsegs m mc -> mem_inv rsegs mc ->
evt rsegs (RZ rsegs md T)
(MS (mkR x1 (Z_to_bv 64 spf) gp (Z_to_bv 64 482928) t0 t1 t2 (Z_to_bv 64 tk) (Z_to_bv 64 oldl) a0' a1' a2 a3 a4 a5 a6 a7
(Z_to_bv 64 newl) (Z_to_bv 64 lenr) s4 s5 s6 (Z_to_bv 64 26) (Z_to_bv 64 q) (Z_to_bv 64 (sb + cop)) (Z_to_bv 64 (Z.of_nat depth)) (Z_to_bv 64 79024) t3 t4 t5 t6)
F (Z_to_bv 64 PE_OUT) fc None mc (seg_rom rsegs))).
{ intros e mc a0' a1' TOK' MU' WM' MI'.
unstash PB. unstash REST.
apply evt_RZ_done. apply (Kout mc e).
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
+ subst depth. cbn [Z.of_nat pf_mxd] in TOK, TAIL |- *. step. if_false.
destruct (nth_error levels 0) as [l0|] eqn:Hl0; [| apply nth_error_None in Hl0; lia].
pose proof (TSK 0%nat l0 Hl0) as L0. rewrite Z.mul_0_r, Z.add_0_r in L0. unfold srec_cells in L0.
assert (SS26 : 0 <= tl_st l0 <= 26 /\ 0 <= tl_ss l0 <= 26) by (unstash REST; pose proof (proj1 (proj2 REST) 0%nat l0 Hl0) as (A1 & A2 & _); split; [exact A1 | exact A2]).
stash TSK.
step. norm_sx32.
destruct (Z.eq_dec (tl_st l0) 0) as [S0 | Sn].
* rewrite S0. step. if_false. step. norm_sx32. step.
destruct (Z.eq_dec (tl_ss l0) 2) as [F2 | Fn].
-- rewrite F2. step. if_false. stepz. step. unstash TSK. eapply TAIL; [exact TOK | exact MU | exact WM | exact MI].
-- step. if_truex. step. stepz. unstash TSK. eapply TAIL; [exact TOK | exact MU | exact WM | exact MI].
* step. if_truex. step. stepz. unstash TSK. eapply TAIL; [exact TOK | exact MU | exact WM | exact MI].
+ step. if_truex. step. stepz. eapply TAIL; [exact TOK | exact MU | exact WM | exact MI].
Qed.

#[using="Type"] Lemma PE_INV_retok2 : forall pf q LB0 payload me lo m mc md A ts cb cb' j1 j2 j2' utf utf' sv errv x' co',
PE_STATIC HIx pf lo ->
PE_INV HIx pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv ->
munch [(pf_tk pf, pf_tk pf + 72); (pf_spf pf, pf_spf pf + PE_FRAME)] m mc -> wmono rsegs m mc -> mem_inv rsegs mc ->
rw_cells rsegs mc (pf_tk pf) (tok_cells_g (pf_mxd pf) (pf_fl pf) (t_pb ts) (Z.of_nat (t_depth ts)) q x') ->
0 <= co' <= pf_len pf -> ts_choff x' = Z_to_bv 64 co' ->
pe_frame rsegs mc (pf_spf pf) (t_obj ts) cb' j1 j2' utf' sv ->
PE_INV HIx pf q LB0 payload me lo mc md A
(TST (t_depth ts) (t_levels ts) co' (t_pb ts) (t_pbs ts) x' (t_obj ts) (t_objs ts) (t_objbs ts)) cb' j1 j2' utf' sv errv.
Proof.
intros until co'. intros STC [CORE REST] MU WM MI TOK' Hco' CH FR'.
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
assert (HW : Forall (pe_wtf pf) [(pf_tk pf, pf_tk pf + 72); (pf_spf pf, pf_spf pf + PE_FRAME)]).
{ apply Forall_cons; [left; cbn; lia|]. apply Forall_cons; [right; cbn; lia | apply Forall_nil]. }
split.
- unfold PE_CORE; cbn. split; [exact LEN32|]. split; [exact D32|]. split; [exact Hco'|]. split; [exact CH|].
split; [exact TOK'|]. split; [| split; [exact Hpb | split; [| exact FR']]].
+ eapply (pbuf_wtf HIx) with (ts := ts); [exact STC | exact (proj1 REST) | exact PB | exact MU | exact WM | exact HW].
+ eapply (tstack_wtf HIx) with (ts := ts); [exact STC | exact (proj1 REST) | exact TSK | exact LEN32 | exact MU | exact WM | exact HW].
- eapply (PE_REST_private_write HIx) with (ts := ts) in REST; [exact REST | exact STC | exact MU | exact WM | exact MI | apply pe_wtf_private; exact HW].
Qed.

#[using="Type"] Lemma euni_hex :
forall (n : nat) (pf : pe_fix) (q : Z) (LB0 : list blk) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (ts : tstate) (l : tlevel)
(cb : byte) (j1 j2 utf : list byte) (sv : pe_saved) (errv : word) (T : TSet)
(x1 gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC HIx pf lo ->
PE_INV HIx pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv ->
CSTR_OK pf payload ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_escape_unicode ->
t_co ts < pf_len pf -> nth_error payload (Z.to_nat (t_co ts)) = Some cb -> bv_unsigned cb <> 0 ->
(pf_len pf - t_co ts <= Z.of_nat n) ->

(forall m' co' cb' (stpos' ucs' u : word) (j2' : list byte) x1' a0' a2' a3' a4',
t_co ts <= co' < pf_len pf -> nth_error payload (Z.to_nat co') = Some cb' ->
PE_INV HIx pf q LB0 payload me lo m' md A
(TST (t_depth ts) (t_levels ts) co' (t_pb ts) (t_pbs ts)
(TS (ts_isd (t_x ts)) stpos' (Z_to_bv 64 co') (ts_err (t_x ts)) ucs' (ts_high (t_x ts)) (ts_quote (t_x ts)))
(t_obj ts) (t_objs ts) (t_objbs ts)) cb' j1 j2' utf sv errv ->
realizes rsegs (mkCfg (pe_ms rsegs pf 0x22c54 co' x1' gp t0 t1 t2 a0' u a2' a3' a4' a5 a6 a7
s4 s5 s6 (Z_to_bv 64 q) (Z_to_bv 64 (Z.of_nat (t_depth ts))) t3 t4 t5 t6 F fc m') md) T) ->

(forall m' co' cb' (stpos' ucs' : word) (j2' : list byte) x1' a1' a2' a3' a4',
t_co ts <= co' < pf_len pf -> nth_error payload (Z.to_nat co') = Some cb' ->
PE_INV HIx pf q LB0 payload me lo m' md A
(TST (t_depth ts) (t_levels ts) co' (t_pb ts) (t_pbs ts)
(TS (ts_isd (t_x ts)) stpos' (Z_to_bv 64 co') (ts_err (t_x ts)) ucs' (ts_high (t_x ts)) (ts_quote (t_x ts)))
(t_obj ts) (t_objs ts) (t_objbs ts)) cb' j1 j2' utf sv errv ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_ERR co' x1' gp t0 t1 t2 (Z_to_bv 64 12) a1' a2' a3' a4' a5 a6 a7
s4 s5 s6 (Z_to_bv 64 q) (Z_to_bv 64 (Z.of_nat (t_depth ts))) t3 t4 t5 t6 F fc m') md) T) ->

(forall m' (e : word) cb' (stpos' ucs' : word) (j2' : list byte) x1' a0' a1' a2' a3' a4',
nth_error payload (Z.to_nat (pf_len pf - 1)) = Some cb' ->
PE_INV HIx pf q LB0 payload me lo m' md A
(TST (t_depth ts) (t_levels ts) (pf_len pf) (t_pb ts) (t_pbs ts)
(TS (ts_isd (t_x ts)) stpos' (Z_to_bv 64 (pf_len pf)) e ucs' (ts_high (t_x ts)) (ts_quote (t_x ts)))
(t_obj ts) (t_objs ts) (t_objbs ts)) cb' j1 j2' utf sv errv ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_OUT (pf_len pf - 1) x1' gp t0 t1 t2 a0' a1' a2' a3' a4' a5 a6 a7
s4 s5 s6 (Z_to_bv 64 q) (Z_to_bv 64 (Z.of_nat (t_depth ts))) t3 t4 t5 t6 F fc m') md) T) ->

(forall m' co' (cbf : byte) (stpos' ucs' : word) (j2' : list byte) x1' a1' a2' a3' a4',
t_co ts < co' < pf_len pf ->
PE_INV HIx pf q LB0 payload me lo m' md A
(TST (t_depth ts) (t_levels ts) co' (t_pb ts) (t_pbs ts)
(TS (ts_isd (t_x ts)) stpos' (Z_to_bv 64 co') (ts_err (t_x ts)) ucs' (ts_high (t_x ts)) (ts_quote (t_x ts)))
(t_obj ts) (t_objs ts) (t_objbs ts)) cbf j1 j2' utf sv errv ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_ERR co' x1' gp t0 t1 t2 (Z_to_bv 64 14) a1' a2' a3' a4' a5 a6 a7
s4 s5 s6 (Z_to_bv 64 q) (Z_to_bv 64 (Z.of_nat (t_depth ts))) t3 t4 t5 t6 F fc m') md) T) ->
realizes rsegs (mkCfg (pe_ms rsegs pf 0x22888 (t_co ts) x1 gp t0 t1 t2 (Z_to_bv 64 (bv_unsigned cb)) a1 a2 a3 a4 a5 a6 a7
s4 s5 s6 (Z_to_bv 64 q) (Z_to_bv 64 (Z.of_nat (t_depth ts))) t3 t4 t5 t6 F fc m) md) T.
Proof.
induction n as [|n IH]; intros until fc; intros STC INV CSTR Hl Hst Hco Hc NZ Hn Kdone Kerr12 Kout Kerr14.
{ exfalso. destruct INV as [(_ & _ & CO & _) _]. cbn in Hn. lia. }
pose proof INV as INV0.
pose proof STC as (LO & LOS & SPA & HT & SP0 & LEN & SB0 & (SBL & RR & LENR)).
destruct INV as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof REST as (HP & LV & OBJ & ST & ERR & STR & PLEN & SBin & HPR & MDV & JCG).
destruct ts as [depth levels co pb pbs xx obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct xx as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl_]; pe_gen fl_; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
unfold tok_cells, tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in TOK. unfold pe_frame in FR. unfold pe_ms in *. cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
unfold_consts.
pose proof (bv_unsigned_in_range 8 cb) as CBR; unfold bv_modulus in CBR; cbn in CBR.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocks; apply in_or_app; right; left; reflexivity).
pose proof (heap_blk S4L HIx _ _ _ _ tk 72 HP INtk) as (_ & Htal & Htlo & Hthi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hthi.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L pf_mxd] in MI.
pose proof (wmono_refl rsegs m) as WM.
pose proof (bytes_at_bound _ _ _ _ STR) as SBB.
pose proof (munch_refl [(tk, tk + 72); (spf, spf + 144)] m) as MU.
stash PB. stash REST. stash TSK. clear LV OBJ HPR.
apply rz_evt; [exact MOK|].

assert (T24 : forall a1v a2v,
evt rsegs (RZ rsegs md T)
(MS (mkR x1 (Z_to_bv 64 spf) gp (Z_to_bv 64 482928) t0 t1 t2 (Z_to_bv 64 tk) (Z_to_bv 64 oldl) (Z_to_bv 64 (bv_unsigned cb)) a1v a2v a3 a4 a5 a6 a7
(Z_to_bv 64 newl) (Z_to_bv 64 lenr) s4 s5 s6 (Z_to_bv 64 26) (Z_to_bv 64 q) (Z_to_bv 64 (sb + co)) (Z_to_bv 64 (Z.of_nat depth)) (Z_to_bv 64 79024) t3 t4 t5 t6)
F (Z_to_bv 64 0x228a4) fc None m (seg_rom rsegs))).
2:{ step. step. step.
lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => destruct c end; [apply T24|].
step. step. step. step.
lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => destruct c end; [| apply T24].

step. step. apply evt_RZ_done. unstash PB. unstash REST. unstash TSK.
eapply (Kerr12 m co cb stpos ucs); [lia | exact Hc | exact INV0]. }
intros a1v a2v.

assert (T40 : forall hv a2w,
evt rsegs (RZ rsegs md T)
(MS (mkR x1 (Z_to_bv 64 spf) gp (Z_to_bv 64 482928) t0 t1 t2 (Z_to_bv 64 tk) (Z_to_bv 64 oldl) hv (Z_to_bv 64 58) a2w a3 a4 a5 a6 a7
(Z_to_bv 64 newl) (Z_to_bv 64 lenr) s4 s5 s6 (Z_to_bv 64 26) (Z_to_bv 64 q) (Z_to_bv 64 (sb + co)) (Z_to_bv 64 (Z.of_nat depth)) (Z_to_bv 64 79024) t3 t4 t5 t6)
F (Z_to_bv 64 0x228c0) fc None m (seg_rom rsegs))).
2:{ step. step.
lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => destruct c end.
- step. step. apply T40.
- step. step. step. apply T40. }
intros hv a2w.

step. step. step. step. step. step. step. step. step. step. step.
step.
lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => destruct c end.
{
unstash PB. unstash REST. unstash TSK. apply evt_RZ_done.
lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mc _) _) _ =>
eapply (Kdone mc co cb); [lia | exact Hc |];
eapply (PE_INV_retok _ q LB0 payload me lo m mc md A ts0); [exact STC | exact INV0 | exact MU | exact WM | exact MI | eassumption | cbn; lia | reflexivity | exact FR]
end. }

step. norm_sx32. step. norm_w32. step. step.
destruct (peek_cases (PEF tk oldl newl len lenr sb spf pmd mxd fl) payload co cb LENR CSTR (proj1 RR) ltac:(cbn [pf_len pf_mxd]; lia) ltac:(cbn [pf_len pf_mxd]; lia) Hc NZ)
as [[Elenr Heof] | [Hne Hmore]]; [cbn [pf_len pf_lenr pf_mxd] in Elenr, Heof; subst lenr; pose (lenr := len) | cbn [pf_len pf_lenr pf_mxd] in Hne, Hmore].
{ if_truex. unstash PB. unstash REST. unstash TSK. apply evt_RZ_done.
replace (Z_to_bv 64 (sb + co)) with (Z_to_bv 64 (sb + (len - 1))) by (f_equal; lia).
lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mc _) _) _ =>
eapply (pe_eof38 (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo mc md A
(TST depth levels len pb pbs (TS isd _ (Z_to_bv 64 len) err _ high quote) obj objs objbs) (len - 1) cb);
[ exact STC
| eapply (PE_INV_retok _ q LB0 payload me lo m mc md A ts0); [exact STC | exact INV0 | exact MU | exact WM | exact MI | rewrite <- Heof; eassumption | cbn; lia | reflexivity | exact FR]
| reflexivity
| unfold ts_set_err; cbn [t_levels t_depth t_co t_pb t_pbs t_x t_obj t_objs t_objbs ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd];
intros; eapply Kout; [replace (len - 1) with co by lia; exact Hc | eassumption] ]
end. }
if_falsex.

lazymatch goal with TOK1 : rw_cells rsegs ?m1 tk [_; _; _; _; _; C4 ?stq; _; _; C4 ?ucq; _; _; _; _; _; _] |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
assert (JOINF : forall mf (nv x1x a0x a1x a2x a3x a4x : word),
rw_cells rsegs mf tk
[C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 pb); C4 (Z_to_bv 64 mxd); C4 (Z_to_bv 64 (Z.of_nat depth)); C4 isd; C4 stq;
C4 (Z_to_bv 64 (co + 1)); C4 err; C4 ucq; C4 high; C1 quote; CB 7 (repeat (Z_to_bv 8 0) 7); C8 (Z_to_bv 64 q); C4 (Z_to_bv 64 fl); C4 (Z_to_bv 64 0)] ->
rw_cells rsegs mf spf [C8 (Z_to_bv 64 obj); CB 16 j1; C4 nv; CB 3 (skipn 4 j2); C1 cb; CB 8 utf;
C8 (pe_s11 sv); C8 (pe_s10 sv); C8 (pe_s9 sv); C8 (pe_s8 sv); C8 (pe_s7 sv); C8 (pe_s6 sv);
C8 (pe_s5 sv); C8 (pe_s4 sv); C8 (pe_s3 sv); C8 (pe_s2 sv); C8 (pe_s1 sv); C8 (pe_s0 sv); C8 (pe_ra sv)] ->
munch [(tk, tk + 72); (spf, spf + 144)] m mf -> wmono rsegs m mf -> mem_inv rsegs mf ->
evt rsegs (RZ rsegs md T)
(MS (mkR x1x (Z_to_bv 64 spf) gp (Z_to_bv 64 482928) t0 t1 t2 (Z_to_bv 64 tk) (Z_to_bv 64 oldl) a0x a1x a2x a3x a4x a5 a6 a7
(Z_to_bv 64 newl) (Z_to_bv 64 lenr) s4 s5 s6 (Z_to_bv 64 26) (Z_to_bv 64 q) (Z_to_bv 64 (sb + co + 1)) (Z_to_bv 64 (Z.of_nat depth)) (Z_to_bv 64 79024) t3 t4 t5 t6)
F (Z_to_bv 64 0x2287c) fc None mf (seg_rom rsegs)))
end.
{ intros mf nv x1x a0x a1x a2x a3x a4x TOKf FRf MUf WMf MIf.
repeat match goal with H : rw_cells rsegs ?mx _ _ |- _ => lazymatch mx with mf => fail | m => fail | _ => clear H end end.
repeat match goal with H : munch _ m ?mx |- _ => lazymatch mx with mf => fail | _ => clear H end end.
repeat match goal with H : wmono rsegs m ?mx |- _ => lazymatch mx with mf => fail | m => fail | _ => clear H end end.
repeat match goal with H : mem_inv rsegs ?mx |- _ => lazymatch mx with mf => fail | m => fail | _ => clear H end end.
try clear MU; try clear WM; try clear MI. rename MUf into MU. rename WMf into WM. rename MIf into MI.

destruct (nth_error payload (Z.to_nat (co + 1))) as [c'|] eqn:Hc'; [| apply nth_error_None in Hc'; lia].
unstash PB. unstash REST. unstash TSK.
lazymatch type of TOKf with rw_cells _ _ _ [_; _; _; _; _; C4 ?stq; _; _; C4 ?ucq; _; _; _; _; _; _] =>
assert (INV1 : PE_INV HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo mf md A
(TST depth levels (co + 1) pb pbs (TS isd stq (Z_to_bv 64 (co + 1)) err ucq high quote) obj objs objbs) cb j1 (le4 nv ++ skipn 4 j2) utf sv errv)
by (eapply (PE_INV_retok2 _ q LB0 payload me lo m mf md A ts0); [exact STC | exact INV0 | exact MU | exact WM | exact MI | exact TOKf | cbn; lia | reflexivity | apply pe_frame_nb_set; exact FRf])
end.
pose proof INV1 as [_ (_ & _ & _ & _ & _ & STR1 & _)]. cbn [pf_sb pf_md pf_mxd pf_fl] in STR1.
pose proof (payload_byte _ _ _ _ _ STR1 Hc' ltac:(lia)) as RDC. replace (sb + (co + 1)) with (sb + co + 1) in RDC by lia.
pose proof (bv_unsigned_in_range 8 c') as CBR'; unfold bv_modulus in CBR'; cbn in CBR'.
stash PB. stash REST. stash TSK. stash INV1.
step. change (zxb c') with (Z_to_bv 64 (bv_unsigned c')).
step. rewrite le1_zxw. mem_after_store.
step.
try clear STR1. try clear RDC.
unstash PB. unstash REST. unstash TSK. clear INV1.
destruct (Z.eq_dec (bv_unsigned c') 0) as [E0 | N0].
- if_truex. step. step. apply evt_RZ_done. replace (sb + co + 1) with (sb + (co + 1)) by lia.
lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?m2 _) _) _ =>
lazymatch goal with TOK2 : rw_cells rsegs m2 tk [_; _; _; _; _; C4 ?stq2; _; _; C4 ?ucq2; _; _; _; _; _; _] |- _ =>
eapply (Kerr12 m2 (co + 1) c' stq2 ucq2); [lia | exact Hc' |];
eapply (PE_INV_retok2 _ q LB0 payload me lo m m2 md A ts0); [exact STC | exact INV0 | exact MU | exact WM | exact MI | exact TOK2 | cbn; lia | reflexivity | apply pe_frame_nb_set; eassumption]
end end.
- if_falsex. apply evt_RZ_done. replace (sb + co + 1) with (sb + (co + 1)) by lia.
lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?m2 _) _) _ =>
lazymatch goal with TOK2 : rw_cells rsegs m2 tk [_; _; _; _; _; C4 ?stq2; _; _; C4 ?ucq2; _; _; _; _; _; _] |- _ =>
eapply (IH (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo m2 md A
(TST depth levels (co + 1) pb pbs (TS isd stq2 (Z_to_bv 64 (co + 1)) err ucq2 high quote) obj objs objbs) l c');
[ exact STC
| eapply (PE_INV_retok2 _ q LB0 payload me lo m m2 md A ts0); [exact STC | exact INV0 | exact MU | exact WM | exact MI | exact TOK2 | cbn; lia | reflexivity | apply pe_frame_nb_set; eassumption]
| exact CSTR | exact Hl | exact Hst | cbn; lia | exact Hc' | exact N0 | cbn; lia
| cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_sb pf_len pf_md pf_mxd pf_fl];
intros; eapply Kdone; [cbn in *; lia | eassumption | eassumption]
| cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_sb pf_len pf_md pf_mxd pf_fl];
intros; eapply Kerr12; [cbn in *; lia | eassumption | eassumption]
| cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_sb pf_len pf_md pf_mxd pf_fl];
intros; eapply Kout; eassumption
| cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_sb pf_len pf_md pf_mxd pf_fl];
intros; eapply Kerr14; [cbn in *; lia | eassumption] ]
end end. }

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
match goal with TOK1 : rw_cells rsegs m1 tk _ |- _ =>
pose proof (tok_flags_byte_g mxd fl m1 tk pb (Z.of_nat depth) q (TS isd _ (Z_to_bv 64 (co + 1)) err _ high quote) TOK1) as RDF
end end.
step. rewrite (zxb_byte fl).
step. rewrite (unsigned_lit (fl mod 256)) by (pose proof (Z.mod_pos_bound fl 256 ltac:(lia)); lia). rewrite (land_mod256 fl 16) by lia.
step.
destruct (land16_cases fl) as [F16 | F16]; rewrite F16.
+
step. if_true. eapply JOINF; [eassumption | exact FR | exact MU | exact WM | exact MI].
+
step. if_false.
destruct (nth_error payload (Z.to_nat (co + 1))) as [c'|] eqn:Hc'; [| apply nth_error_None in Hc'; lia].
unstash REST.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
lazymatch goal with TOK1 : rw_cells rsegs m1 tk [_; _; _; _; _; C4 ?stq; _; _; C4 ?ucq; _; _; _; _; _; _] |- _ =>
assert (INV1 : PE_INV HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo m1 md A
(TST depth levels (co + 1) pb pbs (TS isd stq (Z_to_bv 64 (co + 1)) err ucq high quote) obj objs objbs) cb j1 j2 utf sv errv)
by (unstash PB; unstash TSK; eapply (PE_INV_retok _ q LB0 payload me lo m m1 md A ts0); [exact STC | exact INV0 | exact MU | exact WM | exact MI | exact TOK1 | cbn; lia | reflexivity | exact FR])
end end.
pose proof INV1 as [_ (_ & _ & _ & _ & _ & STR1 & _)]. cbn [pf_sb pf_md pf_mxd pf_fl] in STR1.
pose proof (payload_byte _ _ _ _ _ STR1 Hc' ltac:(lia)) as RDC. replace (sb + (co + 1)) with (sb + co + 1) in RDC by lia.
stash REST. clear INV1.
step. step. step.
eapply evt_cut.
{ eapply (validate_utf8_frame_P) with (c := c') (A := spf + 24) (B := spf) (pre := [C8 (Z_to_bv 64 obj); CB 16 j1]);
[exact FR | reflexivity | lia | lia | exact MI]. }
intros ms' (r & a2' & a3' & nv' & m2 & -> & Hr & FR2 & MU2 & WM2 & MI2). cbn [app] in FR2.
replace (ret_pc (Z_to_bv 64 0x2291c)) with (Z_to_bv 64 0x2291c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
lazymatch goal with TOK1 : rw_cells rsegs ?m1 tk [_; _; _; _; _; C4 ?stq; _; _; C4 ?ucq; _; _; _; _; _; _], MUa : munch _ m ?m1 |- _ =>
assert (TOK2 : rw_cells rsegs m2 tk (tok_cells_g mxd fl pb (Z.of_nat depth) q (TS isd stq (Z_to_bv 64 (co + 1)) err ucq high quote)))
by (eapply rw_cells_transport; [exact TOK1 | exact MU2 | exact WM2 | unfold tok_cells_g; cbn; lia]);
assert (MU2' : munch [(tk, tk + 72); (spf, spf + 144)] m m2)
by (eapply munch_trans; [exact MUa | eapply munch_weaken; [| exact MU2]; intros z Hz; cbn in Hz |- *; lia])
end.
unfold tok_cells_g in TOK2. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK2.
pose proof (wmono_trans _ _ _ _ WM WM2) as WM2'.
destruct Hr as [[-> Em] | ->].
*
step. if_false. step. step. step. apply evt_RZ_done. replace (sb + co + 1) with (sb + (co + 1)) by lia.
unstash PB. unstash REST. unstash TSK.
lazymatch type of TOK2 with rw_cells rsegs m2 tk [_; _; _; _; _; C4 ?stq; _; _; C4 ?ucq; _; _; _; _; _; _] =>
eapply (Kerr14 m2 (co + 1) cb stq ucq); [lia |] end.
eapply (PE_INV_retok2 _ q LB0 payload me lo m m2 md A ts0); [exact STC | exact INV0 | exact MU2' | exact WM2' | exact MI2 | exact TOK2 | cbn; lia | reflexivity | apply pe_frame_nb_set; exact FR2].
*
step. if_true. eapply JOINF; [exact TOK2 | exact FR2 | exact MU2' | exact WM2' | exact MI2].
Qed.

#[using="MEMMOVE"] Lemma seg_euni :
forall (pf : pe_fix) (q : Z) (LB0 : list blk) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (ts : tstate) (l : tlevel)
(cb : byte) (j1 j2 utf : list byte) (sv : pe_saved) (errv : word) (T : TSet)
(x1 gp t0 t1 t2 a3 a4 a5 a6 a7 s4 s5 s6 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC HIx pf lo ->
PE_INV HIx pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv ->
CSTR_OK pf payload ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_escape_unicode ->
t_co ts < pf_len pf -> nth_error payload (Z.to_nat (t_co ts)) = Some cb ->
bytes_at rsegs me UTF8REP_ADDR utf8rep ->

(forall m' md' A' pbs' errv' co' cb' st' (stpos' ucs' high' : word) utf' (j2' : list byte) x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s8' s10' t3' t4' t5' t6' F' fc',
t_co ts <= co' < pf_len pf -> nth_error payload (Z.to_nat co') = Some cb' -> (st' = tl_ss l \/ st' = ST_esc_need_escape) ->
PE_INV HIx pf q LB0 payload me lo m' md' A'
(TST (t_depth ts) (lupd (t_levels ts) (t_depth ts) (TL st' (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)))
co' (t_pb ts) pbs'
(TS (ts_isd (t_x ts)) stpos' (Z_to_bv 64 co') (ts_err (t_x ts)) ucs' high' (ts_quote (t_x ts)))
(t_obj ts) (t_objs ts) (t_objbs ts)) cb' j1 j2' utf' sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_BREAK co' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s8' s10' t3' t4' t5' t6' F' fc' m') md') T) ->

(forall m' co' cb' (stpos' ucs' : word) (j2' : list byte) x1' a1' a2' a3' a4',
t_co ts <= co' < pf_len pf -> nth_error payload (Z.to_nat co') = Some cb' ->
PE_INV HIx pf q LB0 payload me lo m' md A
(TST (t_depth ts) (t_levels ts) co' (t_pb ts) (t_pbs ts)
(TS (ts_isd (t_x ts)) stpos' (Z_to_bv 64 co') (ts_err (t_x ts)) ucs' (ts_high (t_x ts)) (ts_quote (t_x ts)))
(t_obj ts) (t_objs ts) (t_objbs ts)) cb' j1 j2' utf sv errv ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_ERR co' x1' gp t0 t1 t2 (Z_to_bv 64 12) a1' a2' a3' a4' a5 a6 a7
s4 s5 s6 (Z_to_bv 64 q) (Z_to_bv 64 (Z.of_nat (t_depth ts))) t3 t4 t5 t6 F fc m') md) T) ->

(forall m' md' A' pbs' errv' co' cb' (stpos' ucs' high' : word) utf' (j2' : list byte) x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s8' s10' t3' t4' t5' t6' F' fc',
t_co ts <= co' < pf_len pf -> nth_error payload (Z.to_nat co') = Some cb' ->
PE_INV HIx pf q LB0 payload me lo m' md' A'
(TST (t_depth ts) (t_levels ts) co' (t_pb ts) pbs'
(TS (ts_isd (t_x ts)) stpos' (Z_to_bv 64 co') (ts_err (t_x ts)) ucs' high' (ts_quote (t_x ts)))
(t_obj ts) (t_objs ts) (t_objbs ts)) cb' j1 j2' utf' sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_ERR co' x1' gp' t0' t1' t2' (Z_to_bv 64 16) a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s8' s10' t3' t4' t5' t6' F' fc' m') md') T) ->

(forall m' (e : word) cb' (stpos' ucs' : word) (j2' : list byte) x1' a0' a1' a2' a3' a4',
nth_error payload (Z.to_nat (pf_len pf - 1)) = Some cb' ->
PE_INV HIx pf q LB0 payload me lo m' md A
(TST (t_depth ts) (t_levels ts) (pf_len pf) (t_pb ts) (t_pbs ts)
(TS (ts_isd (t_x ts)) stpos' (Z_to_bv 64 (pf_len pf)) e ucs' (ts_high (t_x ts)) (ts_quote (t_x ts)))
(t_obj ts) (t_objs ts) (t_objbs ts)) cb' j1 j2' utf sv errv ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_OUT (pf_len pf - 1) x1' gp t0 t1 t2 a0' a1' a2' a3' a4' a5 a6 a7
s4 s5 s6 (Z_to_bv 64 q) (Z_to_bv 64 (Z.of_nat (t_depth ts))) t3 t4 t5 t6 F fc m') md) T) ->

(forall m' co' (cbf : byte) (stpos' ucs' : word) (j2' : list byte) x1' a1' a2' a3' a4',
t_co ts < co' < pf_len pf ->
PE_INV HIx pf q LB0 payload me lo m' md A
(TST (t_depth ts) (t_levels ts) co' (t_pb ts) (t_pbs ts)
(TS (ts_isd (t_x ts)) stpos' (Z_to_bv 64 co') (ts_err (t_x ts)) ucs' (ts_high (t_x ts)) (ts_quote (t_x ts)))
(t_obj ts) (t_objs ts) (t_objbs ts)) cbf j1 j2' utf sv errv ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_ERR co' x1' gp t0 t1 t2 (Z_to_bv 64 14) a1' a2' a3' a4' a5 a6 a7
s4 s5 s6 (Z_to_bv 64 q) (Z_to_bv 64 (Z.of_nat (t_depth ts))) t3 t4 t5 t6 F fc m') md) T) ->
realizes rsegs (mkCfg (pe_ms rsegs pf (pe_jt ST_escape_unicode) (t_co ts) x1 gp t0 t1 t2
(Z_to_bv 64 (32 * Z.of_nat (t_depth ts))) (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) (Z_to_bv 64 (tl_st l)) a3 a4 a5 a6 a7
s4 s5 s6 (Z_to_bv 64 q) (Z_to_bv 64 (Z.of_nat (t_depth ts))) t3 t4 t5 t6 F fc m) md) T.
Proof.
intros until fc. intros STC INV CSTR Hl Hst Hco Hc UTF Kbreak Kerr12 Kerr16 Kout Kerr14.
pose proof INV as [CORE REST].
pose proof CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof (heap_model_ok _ _ _ _ _ _ (proj1 REST)) as MOK.
pose proof (bv_unsigned_in_range 8 cb) as CBR; unfold bv_modulus in CBR; cbn in CBR.
pose proof STC as (LO & LOS & SPA & HT & SP0 & LEN & SB0 & (SBL & RR & LENR)).
revert INV Kbreak Kerr12 Kerr16 Kout Kerr14.
destruct ts as [depth levels co pb pbs xx obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct xx as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl_]; pe_gen fl_; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
intros INV Kbreak Kerr12 Kerr16 Kout Kerr14.
unfold tok_cells, tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in TOK.
unfold pe_frame in FR. unfold pe_ms. cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl]. unfold_consts.
clear PB TSK REST CORE.
apply rz_evt; [exact MOK|].
step. change (zxb cb) with (Z_to_bv 64 (bv_unsigned cb)). step.
destruct (Z.eq_dec (bv_unsigned cb) 0) as [E0 | N0].
- if_falsex. step. step. step. apply evt_RZ_done.
eapply (Kerr12 m co cb stpos ucs); [lia | exact Hc | exact INV].
- if_truex. apply evt_RZ_done.
eapply (euni_hex (Z.to_nat (len - co)) (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo m md A
(TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) l cb);
[ exact STC | exact INV | exact CSTR | exact Hl | exact Hst | exact Hco | exact Hc | exact N0 | cbn; lia | | | | ];
cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_sb pf_len pf_md pf_mxd pf_fl].
+ intros m' co' cb' stpos' ucs' u j2' x1' a0' a2' a3' a4' R' Hc' INV'.
eapply (euni_tail (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo m' md A
(TST depth levels co' pb pbs (TS isd stpos' (Z_to_bv 64 co') err ucs' high quote) obj objs objbs) l cb');
[ exact STC | exact INV' | exact Hl | exact Hst | exact UTF | | ];
cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_sb pf_len pf_md pf_mxd pf_fl].
* intros. eapply Kbreak; [exact R' | exact Hc' | eassumption | eassumption | eassumption | eassumption].
* intros. eapply Kerr16; [exact R' | exact Hc' | eassumption | eassumption | eassumption].
+ intros. eapply Kerr12; eassumption.
+ intros. eapply Kout; eassumption.
+ intros. eapply Kerr14; eassumption.
Qed.
End PeEuni.

End RC__1.
End Mq0.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup.
Import QEQM.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0.
Import QC8c.Mq0.
Import Qsw7 QJjn QkMG.
Import QG8z QIsM.Mq2 Qa8x.Mq3.
Import QBpZ QT7i Qv6q.
Import QzWc.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section PeNeedu.
Variable HIx : heap_iface S4L.
Hypothesis MEMMOVE : memmove_stmt.

Definition ts_esc_set (ts : tstate) (st' : Z) (pbs' : list blk) : tstate :=
match nth_error (t_levels ts) (t_depth ts) with
| Some l => TST (t_depth ts) (lupd (t_levels ts) (t_depth ts) (TL st' (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)))
(t_co ts) (t_pb ts) pbs'
(TS (ts_isd (t_x ts)) (Z_to_bv 64 0) (ts_choff (t_x ts)) (ts_err (t_x ts)) (Z_to_bv 64 0) (Z_to_bv 64 0) (ts_quote (t_x ts)))
(t_obj ts) (t_objs ts) (t_objbs ts)
| None => ts
end.

#[using="MEMMOVE"] Lemma seg_needu :
forall (pf : pe_fix) (q : Z) (LB0 : list blk) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (ts : tstate) (l : tlevel)
(cb : byte) (j1 j2 utf : list byte) (sv : pe_saved) (errv : word) (T : TSet)
(x1 gp t0 t1 t2 a3 a4 a5 a6 a7 s4 s5 s6 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC HIx pf lo ->
PE_INV HIx pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_esc_need_u ->
t_co ts < pf_len pf ->
bytes_at rsegs me UTF8REP_ADDR utf8rep ->

(forall m' a2',
bv_unsigned cb = 117 ->
PE_INV HIx pf q LB0 payload me lo m' md A (ts_set_level ts (TL ST_escape_unicode (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) cb j1 j2 utf sv errv ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_BREAK2 (t_co ts) x1 gp t0 t1 t2 (Z_to_bv 64 125) (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) a2' a3 a4 a5 a6 a7
s4 s5 s6 (Z_to_bv 64 q) (Z_to_bv 64 (Z.of_nat (t_depth ts))) t3 t4 t5 t6 F fc m') md) T) ->

(forall m' md' A' pbs' errv' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s8' s10' t3' t4' t5' t6' F' fc',
bv_unsigned cb <> 117 ->
PE_INV HIx pf q LB0 payload me lo m' md' A' (ts_esc_set ts ST_string_escape pbs') cb j1 j2 utf sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_REDO (t_co ts) x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s8' s10' t3' t4' t5' t6' F' fc' m') md') T) ->

(forall m' md' A' pbs' errv' x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s8' s10' t3' t4' t5' t6' F' fc',
bv_unsigned cb <> 117 ->
PE_INV HIx pf q LB0 payload me lo m' md' A' (ts_set_pbs ts pbs') cb j1 j2 utf sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_ERR (t_co ts) x1' gp' t0' t1' t2' (Z_to_bv 64 16) a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s8' s10' t3' t4' t5' t6' F' fc' m') md') T) ->
realizes rsegs (mkCfg (pe_ms rsegs pf (pe_jt ST_esc_need_u) (t_co ts) x1 gp t0 t1 t2
(Z_to_bv 64 (32 * Z.of_nat (t_depth ts))) (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) (Z_to_bv 64 (tl_st l)) a3 a4 a5 a6 a7
s4 s5 s6 (Z_to_bv 64 q) (Z_to_bv 64 (Z.of_nat (t_depth ts))) t3 t4 t5 t6 F fc m) md) T.
Proof.
intros until fc. intros STC INV Hl Hst Hco UTF Kbreak Kredo Kerr16.
pose proof STC as (LO & LOS & SPA & HT & SP0 & LEN & SB0 & SBL).
destruct INV as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof REST as (HP & LV & _ & _ & _ & _ & _ & _ & HPR0 & MDV0 & JCG0).
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl_]; pe_gen fl_; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
unfold ts_esc_set in Kredo. cbn [t_levels t_depth t_co t_pb t_x t_obj t_objs t_objbs ts_isd ts_choff ts_err ts_quote pf_mxd] in Kredo. rewrite Hl in Kredo.
pose proof TOK as TOK0. unfold tok_cells, tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in TOK. unfold pe_frame in FR. unfold pe_ms in *. cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
unfold_consts.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocks; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, (32 * mxd)) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocks; apply in_or_app; right; right; left; reflexivity).
pose proof (heap_blk S4L HIx _ _ _ _ tk 72 HP INtk) as (_ & Htal & Htlo & Hthi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ tk 72 HP INtk) as Himg_t. cbn [hl_img_lo hl_img_hi S4L pf_mxd] in Himg_t.
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
assert (ESC12 : zin ST_esc_need_u esc_states = true) by reflexivity.
stash PB. stash REST. stash TSK. stash Himg_t. stash Himg_q. clear LV.
apply rz_evt; [exact MOK|]. rewrite Hst. unfold ST_esc_need_u. cbn [pe_jt pf_mxd].
replace (q + 32 * Z.of_nat depth) with bse by lia.
step. change (zxb cb) with (Z_to_bv 64 (bv_unsigned cb)). step.
destruct (Z.eq_dec (bv_unsigned cb) 117) as [C92 | N92].
-
step. if_truex. step. step. stepz. step. step.
unstash PB. unstash REST. unstash TSK.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
match goal with L5 : rw_cells rsegs mc bse _ |- _ =>
set (l1 := TL ST_escape_unicode (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l));
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
unfold ts_set_level; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd].
split.
{ match goal with |- HEAP _ _ _ ?L _ _ => replace L with (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0); [exact HP' |] end.
unfold pe_blocks, tstate_blocks, ts0; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd].
match goal with |- context [map lvl_blocks (lupd ?lv ?d ?xx)] => rewrite (map_lupd_same lvl_blocks lv d xx l Hl eq_refl) end. reflexivity. }
split; [| split; [| split; [exact ST' | split; [exact ERR' | split; [exact STR' | split; [exact PLEN' | split; [exact SBin' | split; [exact HPR' | split; [exact MDV' | exact JCG']]]]]]]]].
* intros i li Hli. unfold ts0 in Hli; cbn [t_levels t_depth pf_mxd] in Hli. unfold ts0; cbn [t_depth pf_mxd].
destruct (PeanoNat.Nat.eq_dec i depth) as [-> | NE].
-- rewrite nth_error_lupd_eq in Hli by lia. injection Hli as <-.
eapply lvl_cur_restate with (c' := c0); [exact (LV' depth l Hl) | exact Hmode | | unfold ST_escape_unicode; lia | exact SS26 | left; reflexivity].
rewrite <- Hmode. apply lvl_mode_esc_same; [rewrite Hst; reflexivity | reflexivity | exact SS26].
-- rewrite nth_error_lupd_neq in Hli by congruence. exact (LV' i li Hli).
* revert OBJ'. unfold cur_st, ts0. cbn [t_levels t_depth t_objs t_objbs t_obj pf_mxd]. rewrite nth_error_lupd_eq by lia. cbn [tl_st pf_mxd].
rewrite Hl, Hst. cbn. intros OBJ'; exact OBJ'.
-
step. if_falsex. step. step. step. step. step.
unstash PB. unstash REST. clear MU.
pose proof PB as (buf & bpos & cap & pre & post & Epbs & Lpre & CORE1).
pose proof HP as HP1. unfold pe_blocks, tstate_blocks, ts0 in HP1. cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_tk pf_md pf_mxd pf_fl] in HP1.
rewrite Epbs in HP1. cbn [app pf_mxd] in HP1.
pose proof (heap_blk S4L HIx _ _ _ _ buf cap HP1 ltac:(right; left; reflexivity)) as (_ & _ & _ & Hbufhi & _). unfold alloc_ceiling, sp_window_lo, stack_max_size in Hbufhi.
pose proof (heap_blk_img S4L HIx _ _ _ _ buf cap HP1 ltac:(right; left; reflexivity)) as Himg_b. cbn [hl_img_lo hl_img_hi S4L pf_mxd] in Himg_b.
assert (SRC : bytes_at rsegs m UTF8REP_ADDR utf8rep).
{ eapply (heap_presx_bytes_at S4L); [exact HPR0 | exact UTF |]. right; left. intros a Ha. cbn in Ha. cbn. unfold s4_client_static, s4_volatile. unfold UTF8REP_ADDR in Ha. lia. }
unfold UTF8REP_ADDR in SRC.
pose proof REST as (_ & _ & _ & ST1 & ERR1 & _).
apply evt_RZ_done.
eapply (memappend_cps HIx MEMMOVE) with (lo := lo) (b := 0x64ee0) (src := utf8rep) (n := 3);
[ exact HP1 | exact CORE1 | lia | exact SRC | reflexivity
| left; right; left; intros a Ha; cbn; unfold s4_client_static; rewrite ?unsigned_lit in Ha by lia; lia | lia | lia | clear -Himg_b; lia | .. ]; try alloc_side.
all: try clear Himg_b.
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
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in TOK0; [| eapply client_range_block; [exact INtk2 | lia | cbn; lia]]. cbn [hl_segs S4L pf_mxd] in TOK0.
clear TOK.
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
split; [exact TOK0|]. split; [exact PBany|]. split; [exact Hpb|]. split; [exact TSK | exact FR]. }
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2.
pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI2. cbn [hl_segs S4L pf_mxd] in MI2.
clear HP1 HP2 REST CORE1 SRC ST1 ERR1 MI PB HP MOK WM.
reenter MOK2.
destruct OUT2 as [[-> _] | (-> & -> & -> & _)].
2:{
replace (Z_to_bv 64 (2^64 - 1)) with (Z_to_bv 64 (-1)) by (apply bv_eq; vm_compute; reflexivity).
step. if_false. step. step. step. apply evt_RZ_done. eapply Kerr16; [exact N92 | | exact FS2 | exact FRM2].
unfold ts2, pbs2 in INV2. exact INV2. }

step. lazymatch goal with |- evt _ _ (MS _ _ (if ?c then ?a else ?b) _ _ _ _) => change (if c then a else b) with a end.
pose proof REST2 as (HP2 & LV2 & _). destruct INV2 as [CORE2 REST2']. clear REST2'. pose proof CORE2 as (_ & _ & _ & _ & _ & PB2 & _).
pose proof (TSK depth l Hl) as Ld2. cbn [hl_segs S4L pf_mxd] in Ld2. unfold srec_cells in Ld2. rewrite <- Hbse in Ld2.
pose proof (tok_join40 _ _ _ _ _ _ _ _ _ _ _ _ TOK0) as TOKj. clear TOK0.
pose proof (munch_refl [(tk + 28, tk + 32); (tk + 40, tk + 48); (bse, bse + 32)] m2) as MU. pose proof (wmono_refl rsegs m2) as WM.
stash PB2. stash REST2. stash TSK. clear LV2 CORE2.
step. norm_sx32. step. stepz. stepz.
step. rewrite (unsigned_lit (Z.of_nat depth)) by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32.
step. replace (q + Z.of_nat depth * 32) with bse by lia.
step. stepz. step.
unstash PB2. unstash REST2. unstash TSK.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
match goal with TK : rw_cells rsegs mc tk _ |- _ => pose proof (tok_split40 _ _ _ _ _ _ _ _ _ _ TK) as TOK3 end
end.
set (l1 := TL ST_string_escape (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)).
set (ts3 := TST depth (lupd levels depth l1) co pb pbs2 (TS isd (Z_to_bv 64 0) (Z_to_bv 64 co) err (Z_to_bv 64 0) (Z_to_bv 64 0) quote) obj objs objbs).
assert (HW : Forall (pe_wtq (PEF tk oldl newl len lenr sb spf pmd mxd fl) q) [(tk + 28, tk + 32); (tk + 40, tk + 48); (bse, bse + 32)]).
{ repeat apply Forall_cons; try apply Forall_nil; [left; left; cbn [pf_tk fst snd pf_md pf_mxd pf_fl]; lia | left; left; cbn [pf_tk fst snd pf_md pf_mxd pf_fl]; lia | right; cbn [fst snd pf_mxd]; lia]. }
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (TSK3 : tstack rsegs mc q (lupd levels depth l1))
by (subst bse; eapply (tstack_put rsegs m2 _ q levels depth l1 [(tk + 28, tk + 32); (tk + 40, tk + 48)]);
[exact TSK | lia | eapply munch_weaken; [| exact MU]; unfold sub_fp; cbn [outside pf_mxd]; intros; lia | exact WM
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
cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd].
split.
{ match goal with |- HEAP _ _ _ ?L _ _ => replace L with (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts2); [exact HP' |] end.
unfold pe_blocks, tstate_blocks, ts2; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd].
match goal with |- context [map lvl_blocks (lupd ?lv ?d ?xx)] => rewrite (map_lupd_same lvl_blocks lv d xx l Hl eq_refl) end. reflexivity. }
split; [| split; [| split; [exact ST' | split; [exact ERR' | split; [exact STR' | split; [exact PLEN' | split; [exact SBin' | split; [exact HPR' | split; [exact MDV' | exact JCG']]]]]]]]].
* intros i li Hli. unfold ts2 in Hli; cbn [t_levels t_depth pf_mxd] in Hli. unfold ts2; cbn [t_depth pf_mxd].
destruct (PeanoNat.Nat.eq_dec i depth) as [-> | NE].
-- rewrite nth_error_lupd_eq in Hli by lia. injection Hli as <-.
eapply lvl_cur_restate with (c' := c0); [exact (LV' depth l Hl) | exact Hmode | | unfold ST_string_escape; lia | exact SS26 | left; reflexivity].
rewrite <- Hmode. apply lvl_mode_esc_same; [rewrite Hst; reflexivity | reflexivity | exact SS26].
-- rewrite nth_error_lupd_neq in Hli by congruence. exact (LV' i li Hli).
* revert OBJ'. unfold cur_st, ts2. cbn [t_levels t_depth t_objs t_objbs t_obj pf_mxd]. rewrite nth_error_lupd_eq by lia. cbn [tl_st pf_mxd].
rewrite Hl, Hst.
cbn. intros OBJ'; exact OBJ'.
Qed.
End PeNeedu.

End RC__1.
End Mq1.
From Stdlib Require NArith Permutation.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qihm QlCE QhHQ Q5Ki.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup.
Import QEQM.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0.
Import QC8c.Mq0.
Import Qsw7 QJjn.
Import Qihm QPZI.Mq4 QlCE.Mq1 QhHQ Q5Ki QG8z Qa8x.Mq4.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section PeOutTop.
Variable HIx : heap_iface S4L.
Variables (mxd fl : Z).
Hypothesis MXB : 1 <= mxd <= 32.
Notation HEAPx := (HEAP S4L HIx).
Hypothesis PUT : put_stmt_P HIx.

Definition po_top_post (x2 gp tp s0 s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0v : word) (F : bvmap 5 word) (fc : bv 32)
(md : Model) (l : tlevel) (REST LB0 P : list blk) (SP : Z) (me mpre : word -> option byte) (lo : Z) (errv : word)
(q r pb depth : Z) (x : tscal) (levels : list tlevel) (i : nat) (obj : Z) (cbq : byte) (j1 j2 utf : list byte) (sv : pe_saved)
(ms' : machine_state) (md' : Model) : Prop :=
exists m' (A' : AS S4L HIx) F' fc' x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
ms' = MS (mkR x1 x2 gp tp t0 t1 t2 s0 s1 a0v a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (32 * Z.of_nat i + 16 - 32)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F' (Z_to_bv 64 0x23168) fc' None m' (seg_rom rsegs) /\
fsaved F F' /\ (frm0 fc -> frm0 fc') /\
model_vm_only md md' /\
HEAPx A' (tl_cbs l ++ REST) m' md' /\
tstack rsegs m' q (lupd levels i lvl_reset) /\
rw_cells rsegs m' r (tok_cells_g mxd fl pb depth q x) /\
po_frame m' SP obj cbq j1 j2 utf sv /\
stk rsegs m' lo SP /\
heap_pres S4L LB0 (SP + 144) me m' /\
rw_cells rsegs m' (0x75e70 - 164) [C4 errv] /\
agree_on rsegs P mpre m' /\
jopt rsegs S4F (tl_cs l) m' (tl_cbs l) (tl_cur l).

#[using="MXB PUT"] Lemma peout_body_top :
forall (i : nat) (x1 gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s1 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m me : word -> option byte) (md : Model) (T : TSet)
(A : AS S4L HIx) (REST LB0 P : list blk) (SP lo : Z) (errv : word)
(q r pb depth : Z) (x : tscal) (levels : list tlevel) (l : tlevel) (obj : Z) (cbq : byte) (j1 j2 utf : list byte) (sv : pe_saved),
nth_error levels i = Some l -> (i < Z.to_nat mxd)%nat -> length levels = Z.to_nat mxd ->
HEAPx A (lvl_blocks l ++ REST) m md ->
REST = P ++ (r, 72) :: (q, (32 * mxd)) :: LB0 ->
match tl_cs l with Some s => tl_cur l <> 0 /\ jval rsegs S4F s m (tl_cbs l) (tl_cur l) 2 | None => tl_cur l = 0 /\ tl_cbs l = [] end ->
((tl_name l = 0 /\ tl_nbs l = []) \/ (tl_name l <> 0 /\ exists nn, tl_nbs l = [(tl_name l, nn)])) ->
tstack rsegs m q levels ->
rw_cells rsegs m r (tok_cells_g mxd fl pb depth q x) ->
po_frame m SP obj cbq j1 j2 utf sv ->
stk rsegs m lo SP -> alloc_ceiling <= lo -> lo <= SP - 48 - put_stk_P ->
SP mod 16 = 0 -> SP + 144 <= hi_top S4L HIx -> 0 <= SP < 2^64 ->
heap_pres S4L LB0 (SP + 144) me m ->
rw_cells rsegs m (0x75e70 - 164) [C4 errv] ->
tp = Z_to_bv 64 0x75e70 ->
(forall ms' md', po_top_post (Z_to_bv 64 SP) gp tp (Z_to_bv 64 r) s1 (Z_to_bv 64 (2^32)) (Z_to_bv 64 (-16)) s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 q)
F fc md l REST LB0 P SP me m lo errv q r pb depth x levels i obj cbq j1 j2 utf sv ms' md' ->
realizes rsegs (mkCfg ms' md') T) ->
realizes rsegs (mkCfg (MS (mkR x1 (Z_to_bv 64 SP) gp tp t0 t1 t2 (Z_to_bv 64 r) s1 (Z_to_bv 64 q)
a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (32 * Z.of_nat i + 16)) (Z_to_bv 64 (2^32)) (Z_to_bv 64 (-16)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 peout_loop_pc) fc None m (seg_rom rsegs)) md) T.
Proof.
intros until sv. intros Hl Hi LEN HP EREST JO NM TS BLK FR ST LO LOS SPA HT SPR HPR ERR TP K.
unfold put_stk_P in LOS. unfold_consts.
assert (INrR : In (r, 72) REST) by (rewrite EREST; apply in_or_app; right; left; reflexivity).
assert (INqR : In (q, (32 * mxd)) REST) by (rewrite EREST; apply in_or_app; right; right; left; reflexivity).
assert (INr : In (r, 72) (lvl_blocks l ++ REST)) by (rewrite EREST; apply in_or_app; right; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, (32 * mxd)) (lvl_blocks l ++ REST)) by (rewrite EREST; apply in_or_app; right; apply in_or_app; right; right; left; reflexivity).
pose proof (heap_blk S4L HIx _ _ _ _ r 72 HP INr) as (_ & Hral & Hrlo & Hrhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ r 72 HP INr) as Himg_r. cbn [hl_img_lo hl_img_hi S4L] in Himg_r.
pose proof (heap_blk S4L HIx _ _ _ _ q (32 * mxd) HP INq) as (_ & Hqal & Hqlo & Hqhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ q (32 * mxd) HP INq) as Himg_q. cbn [hl_img_lo hl_img_hi S4L] in Himg_q.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hrhi, Hqhi.
assert (Hqr : q <> r).
{ intros ->. pose proof (heap_blk_nodup S4L HIx _ _ _ _ HP) as ND. rewrite EREST, !map_app in ND. cbn [map blk_addr fst] in ND.
apply NoDup_app_remove_l in ND. apply NoDup_app_remove_l in ND. apply List.NoDup_cons_iff in ND as [Hni _]. apply Hni. left. reflexivity. }
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ q (32 * mxd) r 72 HP INq INr Hqr) as Hdqr.

pose proof (srec_to8 _ _ _ _ (TS i l Hl)) as LV. unfold srec_cells8 in LV. cbn [le4 Z_to_le_bytes app] in LV.
remember (q + 32 * Z.of_nat i) as bse eqn:Hbse in LV.
pose proof (nth_error_Some_length Hl) as HiL.
unfold po_frame, pe_frame in FR. unfold tok_cells, tok_cells_g in BLK.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (wmono_refl rsegs m) as WM.
pose proof (munch_refl [(bse, bse + 32)] m) as MU.
subst tp.
apply rz_evt; [exact MOK|]. unfold peout_loop_pc.
step.
replace (q + (32 * Z.of_nat i + 16)) with (bse + 16) by lia.
step. step. step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (rw_cells_recast_prefix rsegs mc bse [C8 (Z_to_bv 64 4294967296)] [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 1)]
[C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (tl_cur l)); C8 (Z_to_bv 64 (tl_name l))] LV
ltac:(cbn; repeat split) ltac:(apply bytes_eq_by_unsigned; vm_compute; reflexivity) ltac:(reflexivity)) as LV1 end.
cbn [app] in LV1.
set (l1 := TL 0 1 (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (TS1 : tstack rsegs mc q (lupd levels i l1)) end.
{ subst bse. eapply (tstack_put rsegs m _ q levels i l1 []); [exact TS | lia | exact MU | exact WM | intros; exact I | exact LV1]. }
clear LV TS.
assert (PDJ : forall a n, In (a, n) P -> a + n <= q \/ q + (32 * mxd) <= a).
{ intros a n Hin.
assert (Haq : a <> q) by (eapply (nodup_P_notq (lvl_blocks l)); [rewrite <- EREST; exact (heap_blk_nodup S4L HIx _ _ _ _ HP) | exact Hin]).
exact (heap_blk_disjoint S4L HIx _ _ _ _ a n q (32 * mxd) HP ltac:(apply in_or_app; right; rewrite EREST; apply in_or_app; left; exact Hin) INq Haq). }
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (AGP : agree_on rsegs P m mc) by (eapply agree_of_munch; [exact MU | exact WM | intros a n Hin; cbn; split; [pose proof (PDJ a n Hin); lia | exact I]]) end.

unfold lvl_blocks in HP. rewrite <- app_assoc in HP.
apply evt_RZ_done.
assert (INq2 : In (q, (32 * mxd)) (tl_cbs l ++ tl_nbs l ++ REST)).
{ apply in_or_app; right; apply in_or_app; right. rewrite EREST. apply in_or_app; right; right; left; reflexivity. }
eapply PUT with (s := tl_cs l) (BS := tl_cbs l) (LB := tl_nbs l ++ REST) (p := tl_cur l) (rc := 2) (lo := lo) (errv := errv);
[ eapply (heap_frame S4L HIx); [exact HP | | exact WM | exact MI];
eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HP MU); apply Forall_cons; [right; left; exists q, (32 * mxd); split; [exact INq2 | cbn; lia] | apply Forall_nil]
| .. ]; try alloc_side.
{ assert (AG : agree_on rsegs (tl_cbs l) m m0).
{ eapply agree_of_munch; [exact MU | exact WM |]. intros a n Hin. cbn. split; [|exact I].
assert (Haq : a <> q).
{ intros ->. refine (nodup_prefix_suffix (tl_cbs l) (tl_nbs l ++ REST) q n (32 * mxd) (heap_blk_nodup S4L HIx _ _ _ _ HP) Hin _).
apply in_or_app; right. rewrite EREST. apply in_or_app; right; right; left; reflexivity. }
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ a n q (32 * mxd) HP ltac:(apply in_or_app; left; exact Hin) INq2 Haq). lia. }
unfold put_pre. destruct (tl_cs l) as [s'|]; [|exact JO].
destruct JO as [Hc J]. split; [exact Hc|]. split; [lia|]. eapply jval_agree; [exact J | exact AG | apply incl_refl]. }
{ unfold put_stk_P. rewrite unsigned_lit by lia. lia. }
intros ms2 md2 (m2 & A2 & r2 & RS2 & VM2 & ST2 & HPR2 & ERR2 & OUT2).
destruct RS2 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F2 & fc2 & -> & FS2 & FRM2).
cbn [hl_segs hl_tp S4L] in *.
rewrite ?(unsigned_lit SP) in ST2 by lia. rewrite ?(unsigned_lit SP) in HPR2 by lia.

set (REST2 := tl_cbs l ++ REST). set (P2 := tl_cbs l ++ P).
assert (EREST2 : REST2 = P2 ++ (r, 72) :: (q, (32 * mxd)) :: LB0) by (unfold REST2, P2; rewrite EREST, app_assoc; reflexivity).
assert (OUTx : HEAPx A2 (tl_nbs l ++ REST2) m2 md2 /\ jopt rsegs S4F (tl_cs l) m2 (tl_cbs l) (tl_cur l)).
{ unfold REST2. destruct (tl_cs l) as [s'|].
- destruct OUT2 as [[[Hn|Hn] _] | (s2 & Es2 & _ & J2 & HP2x)]; [discriminate Hn | lia |]. injection Es2 as <-.
split; [| cbn [jopt]; split; [exact (proj1 JO) | replace (2 - 1) with 1 in J2 by reflexivity; exact J2]].
eapply (heap_perm S4L HIx); [exact HP2x | rewrite <- ?app_assoc; apply Permutation_app_swap_app].
- destruct JO as [Hc0 Ecbs]. rewrite Ecbs. cbn [app jopt]. destruct OUT2 as [[_ HP2x] | (s2 & Es2 & _)]; [| discriminate Es2].
split; [exact HP2x | split; [exact Hc0 | reflexivity]]. }
destruct OUTx as [HP2 JOP2].
assert (PDJ2 : forall a n, In (a, n) P2 -> a + n <= q \/ q + (32 * mxd) <= a).
{ intros a n Hin. unfold P2 in Hin. apply in_app_or in Hin. destruct Hin as [Hin | Hin]; [| exact (PDJ a n Hin)].
assert (Haq : a <> q).
{ intros ->. refine (nodup_prefix_suffix (tl_cbs l) (tl_nbs l ++ REST) q n (32 * mxd) (heap_blk_nodup S4L HIx _ _ _ _ HP) Hin _).
apply in_or_app; right. exact INqR. }
exact (heap_blk_disjoint S4L HIx _ _ _ _ a n q (32 * mxd) HP ltac:(apply in_or_app; left; exact Hin) INq2 Haq). }
rename PDJ into PDJ0. rename PDJ2 into PDJ.
assert (INP2L : forall b, In b P2 -> In b (tl_nbs l ++ REST2)).
{ intros b Hb. apply in_or_app; right. rewrite EREST2. apply in_or_app; left. exact Hb. }
assert (INPL : forall b, In b P -> In b (tl_nbs l ++ REST)).
{ intros b Hb. apply in_or_app; right. rewrite EREST. apply in_or_app; left. exact Hb. }
assert (INqR2 : In (q, (32 * mxd)) REST2) by (unfold REST2; apply in_or_app; right; exact INqR).
assert (INrR2 : In (r, 72) REST2) by (unfold REST2; apply in_or_app; right; exact INrR).
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
assert (INr2 : In (r, 72) (tl_nbs l ++ REST2)) by (apply in_or_app; right; rewrite EREST2; apply in_or_app; right; left; reflexivity).
assert (INq3 : In (q, (32 * mxd)) (tl_nbs l ++ REST2)) by (apply in_or_app; right; rewrite EREST2; apply in_or_app; right; right; left; reflexivity).
assert (INr2c : In (r, 72) (tl_nbs l ++ REST)) by (apply in_or_app; right; exact INrR).
assert (INq3c : In (q, (32 * mxd)) (tl_nbs l ++ REST)) by (apply in_or_app; right; exact INqR).
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in BLK; [| eapply client_range_block; [exact INr2c | lia | cbn; lia]]. cbn [hl_segs S4L] in BLK.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in LV1; [| eapply client_range_block; [exact INq3c | lia | cbn; lia]]. cbn [hl_segs S4L] in LV1.
apply (tstack_pres_g S4L _ _ _ _ _ _ HPR2 INq3c) in TS1; [| rewrite lupd_length; exact LEN]. clear INr2c INq3c.

assert (NQ0 : ~ In (q, (32 * mxd)) LB0).
{ pose proof (heap_blk_nodup S4L HIx _ _ _ _ HP2) as ND. rewrite EREST2 in ND. exact (nodup_mid_notin [] (tl_nbs l) P2 _ _ _ _ _ (32 * mxd) ND). }
assert (HPRa : heap_pres S4L LB0 (SP + 144) me m2).
{ eapply heap_pres_trans; [exact HPR|]. eapply heap_pres_trans.
- eapply (heap_pres_of_munch S4L LB0 (SP + 144)); [exact MU | exact WM |].
eapply (client_outside S4L HIx); [exact HP | intros bb Hbb; apply in_or_app; right; apply in_or_app; right; rewrite EREST; apply in_or_app; right; right; right; exact Hbb | clia |].
apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. right; left. exists q, (32 * mxd). split; [exact INq2|]. split; [exact NQ0 | lia].
- eapply heap_pres_weaken; [exact HPR2 | lia | intros bb Hbb; apply in_or_app; right; rewrite EREST; apply in_or_app; right; right; right; exact Hbb]. }
assert (AGP2 : agree_on rsegs P m m2).
{ eapply agree_on_trans; [exact AGP|]. eapply (agree_of_heap_pres rsegs S4L); [exact HPR2 | reflexivity | exact INPL]. }
clear MU WM MI HPR AGP.

destruct NM as [[Hn0 Hnbs] | [Hn0 [nn Hnbs]]].
+
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2.
pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI. cbn [hl_segs S4L] in MI.
pose proof (wmono_refl rsegs m2) as WM.
pose proof (munch_refl [(bse, bse + 32)] m2) as MU.
reenter MOK2.
step. step.
replace (q + (32 * Z.of_nat i + 16)) with (bse + 16) by lia.
step. stepz. step.

set (l2 := TL 0 1 0 None [] (tl_name l) (tl_nbs l)).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (TS2 : tstack rsegs mc q (lupd levels i l2)) end.
{ rewrite <- (lupd_lupd levels i l1 l2). subst bse.
eapply (tstack_put rsegs m2 _ q (lupd levels i l1) i l2 []); [exact TS1 | rewrite lupd_length; lia | exact MU | exact WM | intros; exact I | exact LV1]. }
clear TS1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (AGJ3 : agree_on rsegs P2 m2 mc) by (eapply agree_of_munch; [exact MU | exact WM | intros a n Hin; cbn; split; [pose proof (PDJ a n Hin); lia | exact I]]) end.
pose proof (agree_on_trans _ _ _ _ _ AGP2 (agree_on_incl _ _ _ _ _ AGJ3 ltac:(intros b Hb; unfold P2; apply in_or_app; right; exact Hb))) as AGP3.
apply evt_RZ_done. eapply (hi_free S4L HIx) with (p := tl_name l) (lo := lo);
[ eapply (heap_frame S4L HIx); [exact HP2 | | exact WM | exact MI];
eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HP2 MU); apply Forall_cons; [right; left; exists q, (32 * mxd); split; [exact INq3 | cbn; lia] | apply Forall_nil]
| .. ]; try alloc_side.
{ left. exact Hn0. }
intros ms3 m3 md3 A3 r3 RS3 VM3 ST3 HPR3 ERR3 HP3. open_ret RS3. cbn [hl_segs hl_tp S4L] in *.
rewrite ?(unsigned_lit SP) in ST3 by lia. rewrite ?(unsigned_lit SP) in HPR3 by lia.
replace (lb_remove (tl_name l) (tl_nbs l ++ REST2)) with (tl_nbs l ++ REST2) in HPR3, HP3 by (rewrite Hn0; symmetry; exact (lb_remove_zero HIx _ _ _ _ HP2)).
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR3) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR3) in BLK; [| eapply client_range_block; [exact INr2 | lia | cbn; lia]]. cbn [hl_segs S4L] in BLK.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR3) in LV1; [| eapply client_range_block; [exact INq3 | lia | cbn; lia]]. cbn [hl_segs S4L] in LV1.
apply (tstack_pres_g S4L _ _ _ _ _ _ HPR3 INq3) in TS2; [| rewrite lupd_length; exact LEN].
assert (HPRb : heap_pres S4L LB0 (SP + 144) me m3).
{ eapply heap_pres_trans; [exact HPRa|]. eapply heap_pres_trans.
- eapply (heap_pres_of_munch S4L LB0 (SP + 144)); [exact MU | exact WM |].
eapply (client_outside S4L HIx); [exact HP2 | intros bb Hbb; apply in_or_app; right; rewrite EREST2; apply in_or_app; right; right; right; exact Hbb | clia |].
apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. right; left. exists q, (32 * mxd). split; [exact INq3|]. split; [exact NQ0 | lia].
- eapply heap_pres_weaken; [exact HPR3 | lia | intros bb Hbb; apply in_or_app; right; rewrite EREST2; apply in_or_app; right; right; right; exact Hbb]. }
assert (AGF : agree_on rsegs P2 m2 m3).
{ eapply agree_on_trans; [exact AGJ3|]. eapply (agree_of_heap_pres rsegs S4L); [exact HPR3 | reflexivity |].
intros b Hb. first [ exact (INP2L b Hb) | rewrite EREST2; apply in_or_app; left; exact Hb ]. }
pose proof (agree_on_trans _ _ _ _ _ AGP2 (agree_on_incl _ _ _ _ _ AGF ltac:(intros b Hb; unfold P2; apply in_or_app; right; exact Hb))) as AGP4.
clear MU WM MI HPRa AGP3 AGJ3.

pose proof (heap_model_ok _ _ _ _ _ _ HP3) as MOK3.
pose proof (heap_mem_inv _ _ _ _ _ _ HP3) as MI. cbn [hl_segs S4L] in MI.
pose proof (wmono_refl rsegs m3) as WM.
pose proof (munch_refl [(bse, bse + 32)] m3) as MU.
reenter MOK3.
step. step.
replace (q + (32 * Z.of_nat i + 16)) with (bse + 16) by lia.
step. stepz.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (TS3 : tstack rsegs mc q (lupd levels i lvl_reset)) end.
{ rewrite <- (lupd_lupd levels i l2 lvl_reset). subst bse.
eapply (tstack_put rsegs m3 _ q (lupd levels i l2) i lvl_reset []); [exact TS2 | rewrite lupd_length; lia | exact MU | exact WM | intros; exact I | exact LV1]. }
apply evt_RZ_done. apply K. unfold po_top_post.
replace (32 * Z.of_nat i + 16 - 32) with (32 * Z.of_nat i + -16) by lia.
do 19 eexists.
split; [reflexivity|].
split; [exact FS2|]. split; [exact FRM2|].
split; [eapply model_vm_only_trans; [exact VM2 | exact VM3]|].
split.
{ rewrite Hnbs in HP3. cbn [app] in HP3.
eapply (heap_frame S4L HIx); [exact HP3 | | exact WM | exact MI].
eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HP3 MU). apply Forall_cons; [| apply Forall_nil]. cbn [fst snd].
right; left. exists q, (32 * mxd). split; [rewrite EREST2; apply in_or_app; right; right; left; reflexivity | lia]. }
split; [exact TS3|]. split; [exact BLK|]. split; [exact FR|]. split; [exact ST3|].
split; [| split; [exact ERR3 | split; [ eapply agree_on_trans; [exact AGP4|]; eapply agree_of_munch; [exact MU | exact WM | intros a n Hin; cbn; split; [pose proof (PDJ0 a n Hin); lia | exact I]]
| eapply (jopt_agree rsegs S4F); [exact JOP2 | | intros b Hb; unfold P2; apply in_or_app; left; exact Hb];
eapply agree_on_trans; [exact AGF|]; eapply agree_of_munch; [exact MU | exact WM | intros a n Hin; cbn; split; [pose proof (PDJ a n Hin); lia | exact I]] ]]].
eapply heap_pres_trans; [exact HPRb|].
eapply (heap_pres_of_munch S4L LB0 (SP + 144)); [exact MU | exact WM |].
eapply (client_outside S4L HIx); [exact HP3 | intros bb Hbb; apply in_or_app; right; rewrite EREST2; apply in_or_app; right; right; right; exact Hbb | clia |].
apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. right; left. exists q, (32 * mxd). split; [exact INq3|]. split; [exact NQ0 | lia].
+
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2.
pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI. cbn [hl_segs S4L] in MI.
pose proof (wmono_refl rsegs m2) as WM.
pose proof (munch_refl [(bse, bse + 32)] m2) as MU.
reenter MOK2.
step. step.
replace (q + (32 * Z.of_nat i + 16)) with (bse + 16) by lia.
step. stepz. step.

set (l2 := TL 0 1 0 None [] (tl_name l) (tl_nbs l)).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (TS2 : tstack rsegs mc q (lupd levels i l2)) end.
{ rewrite <- (lupd_lupd levels i l1 l2). subst bse.
eapply (tstack_put rsegs m2 _ q (lupd levels i l1) i l2 []); [exact TS1 | rewrite lupd_length; lia | exact MU | exact WM | intros; exact I | exact LV1]. }
clear TS1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (AGJ3 : agree_on rsegs P2 m2 mc) by (eapply agree_of_munch; [exact MU | exact WM | intros a n Hin; cbn; split; [pose proof (PDJ a n Hin); lia | exact I]]) end.
pose proof (agree_on_trans _ _ _ _ _ AGP2 (agree_on_incl _ _ _ _ _ AGJ3 ltac:(intros b Hb; unfold P2; apply in_or_app; right; exact Hb))) as AGP3.
apply evt_RZ_done. eapply (hi_free S4L HIx) with (p := tl_name l) (lo := lo);
[ eapply (heap_frame S4L HIx); [exact HP2 | | exact WM | exact MI];
eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HP2 MU); apply Forall_cons; [right; left; exists q, (32 * mxd); split; [exact INq3 | cbn; lia] | apply Forall_nil]
| .. ]; try alloc_side.
{ right. exists nn. rewrite Hnbs. left. reflexivity. }
intros ms3 m3 md3 A3 r3 RS3 VM3 ST3 HPR3 ERR3 HP3. open_ret RS3. cbn [hl_segs hl_tp S4L] in *.
rewrite ?(unsigned_lit SP) in ST3 by lia. rewrite ?(unsigned_lit SP) in HPR3 by lia.
replace (lb_remove (tl_name l) (tl_nbs l ++ REST2)) with REST2 in HPR3, HP3 by (rewrite Hnbs; cbn [app]; symmetry; apply lb_remove_head).
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR3) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR3) in BLK; [| eapply client_range_block; [exact INrR2 | lia | cbn; lia]]. cbn [hl_segs S4L] in BLK.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR3) in LV1; [| eapply client_range_block; [exact INqR2 | lia | cbn; lia]]. cbn [hl_segs S4L] in LV1.
apply (tstack_pres_g S4L _ _ _ _ _ _ HPR3 INqR2) in TS2; [| rewrite lupd_length; exact LEN].
assert (HPRb : heap_pres S4L LB0 (SP + 144) me m3).
{ eapply heap_pres_trans; [exact HPRa|]. eapply heap_pres_trans.
- eapply (heap_pres_of_munch S4L LB0 (SP + 144)); [exact MU | exact WM |].
eapply (client_outside S4L HIx); [exact HP2 | intros bb Hbb; apply in_or_app; right; rewrite EREST2; apply in_or_app; right; right; right; exact Hbb | clia |].
apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. right; left. exists q, (32 * mxd). split; [exact INq3|]. split; [exact NQ0 | lia].
- eapply heap_pres_weaken; [exact HPR3 | lia | intros bb Hbb; rewrite EREST2; apply in_or_app; right; right; right; exact Hbb]. }
assert (AGF : agree_on rsegs P2 m2 m3).
{ eapply agree_on_trans; [exact AGJ3|]. eapply (agree_of_heap_pres rsegs S4L); [exact HPR3 | reflexivity |].
intros b Hb. first [ exact (INP2L b Hb) | rewrite EREST2; apply in_or_app; left; exact Hb ]. }
pose proof (agree_on_trans _ _ _ _ _ AGP2 (agree_on_incl _ _ _ _ _ AGF ltac:(intros b Hb; unfold P2; apply in_or_app; right; exact Hb))) as AGP4.
clear MU WM MI HPRa AGP3 AGJ3.

pose proof (heap_model_ok _ _ _ _ _ _ HP3) as MOK3.
pose proof (heap_mem_inv _ _ _ _ _ _ HP3) as MI. cbn [hl_segs S4L] in MI.
pose proof (wmono_refl rsegs m3) as WM.
pose proof (munch_refl [(bse, bse + 32)] m3) as MU.
reenter MOK3.
step. step.
replace (q + (32 * Z.of_nat i + 16)) with (bse + 16) by lia.
step. stepz.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (TS3 : tstack rsegs mc q (lupd levels i lvl_reset)) end.
{ rewrite <- (lupd_lupd levels i l2 lvl_reset). subst bse.
eapply (tstack_put rsegs m3 _ q (lupd levels i l2) i lvl_reset []); [exact TS2 | rewrite lupd_length; lia | exact MU | exact WM | intros; exact I | exact LV1]. }
apply evt_RZ_done. apply K. unfold po_top_post.
replace (32 * Z.of_nat i + 16 - 32) with (32 * Z.of_nat i + -16) by lia.
do 19 eexists.
split; [reflexivity|].
split; [exact FS2|]. split; [exact FRM2|].
split; [eapply model_vm_only_trans; [exact VM2 | exact VM3]|].
split.
{ eapply (heap_frame S4L HIx); [exact HP3 | | exact WM | exact MI].
eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HP3 MU). apply Forall_cons; [| apply Forall_nil]. cbn [fst snd].
right; left. exists q, (32 * mxd). split; [rewrite EREST2; apply in_or_app; right; right; left; reflexivity | lia]. }
split; [exact TS3|]. split; [exact BLK|]. split; [exact FR|]. split; [exact ST3|].
split; [| split; [exact ERR3 | split; [ eapply agree_on_trans; [exact AGP4|]; eapply agree_of_munch; [exact MU | exact WM | intros a n Hin; cbn; split; [pose proof (PDJ0 a n Hin); lia | exact I]]
| eapply (jopt_agree rsegs S4F); [exact JOP2 | | intros b Hb; unfold P2; apply in_or_app; left; exact Hb];
eapply agree_on_trans; [exact AGF|]; eapply agree_of_munch; [exact MU | exact WM | intros a n Hin; cbn; split; [pose proof (PDJ a n Hin); lia | exact I]] ]]].
eapply heap_pres_trans; [exact HPRb|].
eapply (heap_pres_of_munch S4L LB0 (SP + 144)); [exact MU | exact WM |].
eapply (client_outside S4L HIx); [exact HP3 | intros bb Hbb; rewrite EREST2; apply in_or_app; right; right; right; exact Hbb | clia |].
apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. right; left. exists q, (32 * mxd). split; [exact INqR2|]. split; [exact NQ0 | lia].
Qed.
End PeOutTop.

End RC__1.
End Mq2.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup.
Import QEQM.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0.
Import QC8c.Mq0.
Import Qsw7 QJjn QkMG.
Import QG8z QIsM.Mq2 Qa8x.Mq3.
Import QBpZ QT7i Qv6q.
Import QzWc.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition pe_jtab3 := Eval vm_compute in match image_bytes rsegs 0x13620 336 with Some bs => bs | None => [] end.
Definition pe_jtab4 := Eval vm_compute in match image_bytes rsegs 0x13770 40 with Some bs => bs | None => [] end.
#[using="Type"] Lemma ro_cells_bytes_at' : forall segs m A cs, ro_cells segs m A cs -> bytes_at segs m A (cells_bytes cs).
Proof. intros segs m A cs [_ H]. exact H. Qed.

#[using="Type"] Lemma pe_jtab3_ro : forall m, mem_inv rsegs m -> ro_cells rsegs m 0x13620 [CB 336 pe_jtab3].
Proof.
intros m MI. change 336%nat with (length pe_jtab3).
apply ro_cells_image; [exact MI | vm_compute; reflexivity | lia | ].
change (Z.of_nat (length pe_jtab3)) with 336%Z. lia.
Qed.
#[using="Type"] Lemma pe_jtab4_ro : forall m, mem_inv rsegs m -> ro_cells rsegs m 0x13770 [CB 40 pe_jtab4].
Proof.
intros m MI. change 40%nat with (length pe_jtab4).
apply ro_cells_image; [exact MI | vm_compute; reflexivity | lia | ].
change (Z.of_nat (length pe_jtab4)) with 40%Z. lia.
Qed.

Definition pe_jt3 (c : Z) : Z :=
match c with
| 34 | 47 | 92 => 0x22c48
| 117 => 0x22cc0
| 98 | 102 | 110 | 114 | 116 => 0x22730
| _ => 0x2317c
end.

Definition esc_lit (c : Z) : Z :=
match c with 98 => 0x11e82 | 102 => 0x1305f | 110 => 0x122e9 | 114 => 0x105a0 | _ => 0x1185c end.
Definition esc_byte (c : Z) : Z :=
match c with 98 => 8 | 102 => 12 | 110 => 10 | 114 => 13 | _ => 9 end.
End RC__1.

Lemma enum_step_Z : forall v lo lo' : Z, lo' = (lo + 1)%Z -> (lo <= v)%Z -> v = lo \/ (lo' <= v)%Z.
Proof. intros v lo lo' -> H. destruct (Z.eq_dec v lo) as [E|N]; [left; exact E | right; lia]. Qed.
Ltac enum_from_go v lo n L :=
lazymatch n with
| O => exfalso; lia
| S ?n' => let E := fresh "E" in let L2 := fresh "EL" in
let lo' := eval vm_compute in (lo + 1)%Z in
destruct (enum_step_Z v lo lo' eq_refl L) as [E | L2]; clear L;
[ rewrite ?E in * | enum_from_go v lo' n' L2 ]
end.
Ltac enum_from v lo n :=
let L := fresh "EL" in assert (L : (lo <= v)%Z) by lia; enum_from_go v lo n L.
Section RC__2. Context {RC__ : Q6q3.RunConsts}.

Section PeSesc.
Variable HIx : heap_iface S4L.
Hypothesis MEMMOVE : memmove_stmt.

#[using="Type"] Lemma seg_sesc_dispatch :
forall (pf : pe_fix) (q : Z) (LB0 : list blk) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (ts : tstate) (l : tlevel)
(cb : byte) (j1 j2 utf : list byte) (sv : pe_saved) (errv : word) (T : TSet)
(x1 gp t0 t1 t2 a3 a4 a5 a6 a7 s4 s5 s6 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC HIx pf lo ->
PE_INV HIx pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_string_escape ->
(forall a2' a3',
realizes rsegs (mkCfg (pe_ms rsegs pf (pe_jt3 (bv_unsigned cb)) (t_co ts) x1 gp t0 t1 t2
(Z_to_bv 64 (bv_unsigned cb)) (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) a2' a3' a4 a5 a6 a7
s4 s5 s6 (Z_to_bv 64 q) (Z_to_bv 64 (Z.of_nat (t_depth ts))) t3 t4 t5 t6 F fc m) md) T) ->
realizes rsegs (mkCfg (pe_ms rsegs pf (pe_jt ST_string_escape) (t_co ts) x1 gp t0 t1 t2
(Z_to_bv 64 (32 * Z.of_nat (t_depth ts))) (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) (Z_to_bv 64 (tl_st l)) a3 a4 a5 a6 a7
s4 s5 s6 (Z_to_bv 64 q) (Z_to_bv 64 (Z.of_nat (t_depth ts))) t3 t4 t5 t6 F fc m) md) T.
Proof.
intros until fc. intros STC INV Hl Hst K.
destruct INV as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof (proj1 REST) as HP.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl_]; pe_gen fl_; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
unfold pe_frame in FR. unfold pe_ms in *. cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L pf_mxd] in MI.
pose proof (pe_jtab3_ro m MI) as JT.
pose proof (bv_unsigned_in_range 8 cb) as CBR; unfold bv_modulus in CBR; cbn in CBR.
clear TOK PB TSK REST HP.
apply rz_evt; [exact MOK|]. rewrite Hst. unfold ST_string_escape. cbn [pe_jt pf_mxd]. unfold PE_JTAB.
step. change (zxb cb) with (Z_to_bv 64 (bv_unsigned cb)). step. step.
destruct (Z_lt_dec (bv_unsigned cb) 34) as [LT | GE].
-
replace (Z_to_bv 64 (bv_unsigned cb + -34)) with (Z_to_bv 64 (bv_unsigned cb + -34 + 2^64)).
2:{ apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
rewrite <- (Z_mod_plus_full (bv_unsigned cb + -34) 1 (2^64)). f_equal. }
step. if_truex. apply evt_RZ_done.
replace (pe_jt3 (bv_unsigned cb)) with 0x2317c in K.
2:{ assert (R : 0 <= bv_unsigned cb <= 33) by lia. clear - R. enum_from (bv_unsigned cb) 0%Z 34%nat; reflexivity. }
apply K.
- destruct (Z_lt_dec 117 (bv_unsigned cb)) as [GT | LE].
+ step. if_truex. apply evt_RZ_done.
replace (pe_jt3 (bv_unsigned cb)) with 0x2317c in K. 2:{ assert (R : 118 <= bv_unsigned cb <= 255) by lia. clear - R. enum_from (bv_unsigned cb) 118%Z 138%nat; reflexivity. }
apply K.
+ step. if_falsex. step.
rewrite (unsigned_lit (bv_unsigned cb + -34)) by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
step. step. step.

pose proof (bytes_at_read rsegs m 0x13620 pe_jtab3 ((bv_unsigned cb + -34) * 4) 4 (ro_cells_bytes_at' _ _ _ _ JT) ltac:(lia)
ltac:(change (length pe_jtab3) with 336%nat; lia)) as RD.
unfold wa in RD. replace (0x13620 + (bv_unsigned cb + -34) * 4) with ((bv_unsigned cb + -34) * 4 + 79392) in RD by lia.
step. step. step.
apply evt_RZ_done.
assert (R : 34 <= bv_unsigned cb <= 117) by lia.
match goal with |- realizes _ (mkCfg (MS _ _ ?pc _ _ _ _) _) _ =>
replace pc with (Z_to_bv 64 (pe_jt3 (bv_unsigned cb))); [apply K |] end.
clear - R. enum_from (bv_unsigned cb) 34%Z 84%nat; apply bv_eq; vm_compute; reflexivity.
Qed.

#[using="Type"] Lemma lvl_mode_esc_pop : forall st ss c hn,
zin st esc_states = true -> 0 <= ss <= 26 -> lvl_mode st ss = Some (c, hn) -> lvl_mode ss ss = Some (c, hn).
Proof.
intros st ss c hn H R Hm.
assert (C : forall x, zin x esc_states = true -> x = 9 \/ x = 10 \/ x = 11 \/ x = 12).
{ intros x Hx. unfold zin, esc_states in Hx. cbn in Hx. rewrite !Bool.orb_true_iff in Hx. rewrite !Z.eqb_eq in Hx. intuition lia. }
destruct (C st H) as [->|[->|[->| ->]]]; enum_z R ss; vm_compute in Hm; vm_compute; congruence.
Qed.

#[using="MEMMOVE"] Lemma sesc_tail :
forall (pf : pe_fix) (q : Z) (LB0 : list blk) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (ts : tstate) (l : tlevel)
(cb : byte) (j1 j2 utf : list byte) (sv : pe_saved) (errv : word) (T : TSet)
(x1 gp t0 t1 t2 a2 a3 a4 a5 a6 a7 s4 s5 s6 s8 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (b : Z) (x : byte),
PE_STATIC HIx pf lo ->
PE_INV HIx pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_string_escape ->
bytes_at rsegs m b [x] -> ((65536 <= b /\ b + 1 <= 618496 /\ ro_bytes rsegs b [x]) \/ b = pf_spf pf + 31) ->

(forall m' md' A' pbs' errv' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s8' s10' t3' t4' t5' t6' F' fc',
PE_INV HIx pf q LB0 payload me lo m' md' A' (ts_set_pbs (ts_set_level ts (TL (tl_ss l) (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) pbs') cb j1 j2 utf sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_BREAK (t_co ts) x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s8' s10' t3' t4' t5' t6' F' fc' m') md') T) ->

(forall m' md' A' pbs' errv' x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s8' s10' t3' t4' t5' t6' F' fc',
PE_INV HIx pf q LB0 payload me lo m' md' A' (ts_set_pbs ts pbs') cb j1 j2 utf sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_ERR (t_co ts) x1' gp' t0' t1' t2' (Z_to_bv 64 16) a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s8' s10' t3' t4' t5' t6' F' fc' m') md') T) ->
realizes rsegs (mkCfg (pe_ms rsegs pf 0x22db4 (t_co ts) x1 gp t0 t1 t2
(Z_to_bv 64 (t_pb ts)) (Z_to_bv 64 b) a2 a3 a4 a5 a6 a7
s4 s5 s6 s8 s10 t3 t4 t5 t6 F fc m) md) T.
Proof.
intros until x. intros STC INV Hl Hst SRC HB Kbreak Kerr16.
pose proof STC as (LO & LOS & SPA & HT & SP0 & LEN & SB0 & SBL).
destruct INV as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof REST as (HP & LV & _).
destruct ts as [depth levels co pb pbs xx obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct xx as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl_]; pe_gen fl_; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
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
pose proof (LV depth l Hl) as LVd. pose proof LVd as (ST26 & SS26 & _ & Md).
rewrite Nat.ltb_irrefl, Nat.eqb_refl in Md. destruct Md as (c0 & hn0 & Hmode & CLS0 & NM0).
pose proof (bv_unsigned_in_range 8 cb) as CBR; unfold bv_modulus in CBR; cbn in CBR.
stash TSK. clear LV.
apply rz_evt; [exact MOK|].
step. step.

pose proof PB as (buf & bpos & cap & pre & post & Epbs & Lpre & CORE1).
pose proof HP as HP1. unfold pe_blocks, tstate_blocks, ts0 in HP1. cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_tk pf_md pf_mxd pf_fl] in HP1.
rewrite Epbs in HP1. cbn [app pf_mxd] in HP1.
pose proof (heap_blk S4L HIx _ _ _ _ buf cap HP1 ltac:(right; left; reflexivity)) as (_ & _ & _ & Hbufhi & _). unfold alloc_ceiling, sp_window_lo, stack_max_size in Hbufhi.
pose proof (heap_blk_img S4L HIx _ _ _ _ buf cap HP1 ltac:(right; left; reflexivity)) as Himg_b. cbn [hl_img_lo hl_img_hi S4L pf_mxd] in Himg_b.
pose proof REST as (_ & _ & _ & ST1 & ERR1 & _).
apply evt_RZ_done.
eapply (memappend_cps HIx MEMMOVE) with (lo := lo) (b := b) (src := [x]) (n := 1);
[ exact HP1 | exact CORE1 | lia | exact SRC | reflexivity
| destruct HB as [(Hb1 & Hb2 & RO) | ->]; [right; exact RO | left; left; rewrite ?unsigned_lit by lia; lia]
| lia | unfold PE_FRAME in *; lia | clear - Himg_b HB Hbufhi SP0 LO LOS; unfold PE_FRAME in *; lia | .. ]; try alloc_side.
all: try clear Himg_b.
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
clear HP1 HP2 REST CORE1 SRC ST1 ERR1 MI PBany PB HP MOK.
reenter MOK2.
destruct OUT2 as [[-> _] | (-> & -> & -> & _)].
2:{ replace (Z_to_bv 64 (2^64 - 1)) with (Z_to_bv 64 (-1)) by (apply bv_eq; vm_compute; reflexivity).
step. if_true. step. step. apply evt_RZ_done. eapply Kerr16; [| exact FS2 | exact FRM2].
unfold ts2, pbs2 in INV2. exact INV2. }

step. if_false.
pose proof (TSK depth l Hl) as Ld. cbn [hl_segs S4L pf_mxd] in Ld. unfold srec_cells in Ld.
remember (q + 32 * Z.of_nat depth) as bse eqn:Hbse in Ld.
assert (HbseR : q <= bse /\ bse + 32 <= q + (32 * mxd)) by (subst bse; lia).
pose proof (munch_refl [(bse, bse + 32)] m2) as MU. pose proof (wmono_refl rsegs m2) as WM.
pose proof REST2 as (HP2 & LV2 & _). pose proof INV2 as [CORE2 _]. pose proof CORE2 as (_ & _ & _ & _ & _ & PB2 & _).
stash PB2. stash REST2. stash TSK. clear LV2 CORE2 INV2.
step. norm_sx32. step.
step. rewrite (unsigned_lit (Z.of_nat depth)) by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32.
step. replace (q + Z.of_nat depth * 32) with bse by lia.
step. norm_sx32. stepz.
unstash PB2. unstash REST2. unstash TSK.
set (l1 := TL (tl_ss l) (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)).
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
- unfold PE_CORE, ts_set_pbs, ts_set_level; cbn. split; [rewrite lupd_length; exact LEN32|]. split; [exact D32|]. split; [lia|]. split; [reflexivity|].
split; [assumption|]. split; [exact PB3|]. split; [exact Hpb|]. split; [exact TSK3 | assumption].
- destruct REST3 as (HP' & LV' & OBJ' & ST' & ERR' & STR' & PLEN' & SBin' & HPR' & MDV' & JCG').
unfold ts_set_pbs, ts_set_level; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd].
split.
{ match goal with |- HEAP _ _ _ ?L _ _ => replace L with (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts2); [exact HP' |] end.
unfold pe_blocks, tstate_blocks, ts2; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd].
match goal with |- context [map lvl_blocks (lupd ?lv ?d ?xx)] => rewrite (map_lupd_same lvl_blocks lv d xx l Hl eq_refl) end. reflexivity. }
split; [| split; [| split; [exact ST' | split; [exact ERR' | split; [exact STR' | split; [exact PLEN' | split; [exact SBin' | split; [exact HPR' | split; [exact MDV' | exact JCG']]]]]]]]].
+ intros i li Hli. unfold ts0, ts2 in Hli; cbn [t_levels t_depth pf_mxd] in Hli. unfold ts0, ts2; cbn [t_depth pf_mxd].
destruct (PeanoNat.Nat.eq_dec i depth) as [-> | NE].
* rewrite nth_error_lupd_eq in Hli by lia. injection Hli as <-.
eapply lvl_cur_restate with (c' := c0); [exact (LV' depth l Hl) | exact Hmode | | exact SS26 | exact SS26 | left; reflexivity].
eapply (lvl_mode_esc_pop (tl_st l)); [rewrite Hst; reflexivity | exact SS26 | exact Hmode].
* rewrite nth_error_lupd_neq in Hli by congruence. exact (LV' i li Hli).
+ revert OBJ'. unfold cur_st, ts0, ts2. cbn [t_levels t_depth t_objs t_objbs t_obj pf_mxd]. rewrite nth_error_lupd_eq by lia. cbn [tl_st pf_mxd].
rewrite Hl, Hst.
assert (Ez : zin (tl_ss l) [ST_array_add; ST_ovadd] = false).
{ destruct (zin (tl_ss l) [ST_array_add; ST_ovadd]) eqn:E; [| reflexivity]. exfalso.
revert Hmode E. rewrite Hst. clear. intros Hmode E.
assert (R : tl_ss l = 16 \/ tl_ss l = 22).
{ unfold zin in E. cbn in E. rewrite !Bool.orb_true_iff in E. rewrite !Z.eqb_eq in E. unfold ST_array_add, ST_ovadd in E. intuition lia. }
destruct R as [E'|E']; rewrite E' in Hmode; vm_compute in Hmode; discriminate Hmode. }
rewrite Ez. cbn. intros OBJ'; exact OBJ'.
Qed.

Ltac sesc_prologue STC INV :=
pose proof STC as (LO & LOS & SPA & HT & SP0 & LEN & SB0 & SBL);
pose proof INV as INV0;
destruct INV as [CORE REST];
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR);
pose proof (proj1 REST) as HP.

#[using="MEMMOVE"] Lemma seg_sesc_quote :
forall (pf : pe_fix) (q : Z) (LB0 : list blk) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (ts : tstate) (l : tlevel)
(cb : byte) (j1 j2 utf : list byte) (sv : pe_saved) (errv : word) (T : TSet)
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s8 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC HIx pf lo ->
PE_INV HIx pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_string_escape ->
(forall m' md' A' pbs' errv' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s8' s10' t3' t4' t5' t6' F' fc',
PE_INV HIx pf q LB0 payload me lo m' md' A' (ts_set_pbs (ts_set_level ts (TL (tl_ss l) (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) pbs') cb j1 j2 utf sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_BREAK (t_co ts) x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s8' s10' t3' t4' t5' t6' F' fc' m') md') T) ->
(forall m' md' A' pbs' errv' x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s8' s10' t3' t4' t5' t6' F' fc',
PE_INV HIx pf q LB0 payload me lo m' md' A' (ts_set_pbs ts pbs') cb j1 j2 utf sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_ERR (t_co ts) x1' gp' t0' t1' t2' (Z_to_bv 64 16) a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s8' s10' t3' t4' t5' t6' F' fc' m') md') T) ->
realizes rsegs (mkCfg (pe_ms rsegs pf 0x22c48 (t_co ts) x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s8 s10 t3 t4 t5 t6 F fc m) md) T.
Proof.
intros until fc. intros STC INV Hl Hst Kbreak Kerr16. sesc_prologue STC INV.
destruct ts as [depth levels co pb pbs xx obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct xx as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl_]; pe_gen fl_; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
unfold tok_cells, tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in TOK. unfold pe_frame in FR. unfold pe_ms in *. cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
unfold_consts.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK. pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L pf_mxd] in MI.
assert (INtk : In (tk, 72) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 (TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs))) by (unfold pe_blocks; apply in_or_app; right; left; reflexivity).
pose proof (heap_blk S4L HIx _ _ _ _ tk 72 HP INtk) as (_ & Htal & Htlo & Hthi & _). unfold alloc_ceiling, sp_window_lo, stack_max_size in Hthi.
pose proof (pe_frame_cbyte m spf obj cb j1 j2 utf sv FR) as SRC.
clear PB TSK REST.
apply rz_evt; [exact MOK|]. step. step. step. apply evt_RZ_done.
eapply (sesc_tail (PEF tk oldl newl len lenr sb spf pmd mxd fl)) with (ts := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs);
[exact STC | exact INV0 | exact Hl | exact Hst | exact SRC | right; reflexivity | exact Kbreak | exact Kerr16].
Qed.

#[using="Type"] Lemma seg_sesc_u :
forall (pf : pe_fix) (q : Z) (LB0 : list blk) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (ts : tstate) (l : tlevel)
(cb : byte) (j1 j2 utf : list byte) (sv : pe_saved) (errv : word) (T : TSet)
(x1 gp t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 s4 s5 s6 s8 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC HIx pf lo ->
PE_INV HIx pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_string_escape ->
(forall m' a0',
PE_INV HIx pf q LB0 payload me lo m' md A
(TST (t_depth ts) (lupd (t_levels ts) (t_depth ts) (TL ST_escape_unicode (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)))
(t_co ts) (t_pb ts) (t_pbs ts)
(TS (ts_isd (t_x ts)) (Z_to_bv 64 0) (ts_choff (t_x ts)) (ts_err (t_x ts)) (Z_to_bv 64 0) (ts_high (t_x ts)) (ts_quote (t_x ts)))
(t_obj ts) (t_objs ts) (t_objbs ts)) cb j1 j2 utf sv errv ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_BREAK (t_co ts) x1 gp t0 t1 t2 a0' (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) a2 a3 a4 a5 a6 a7
s4 s5 s6 s8 s10 t3 t4 t5 t6 F fc m') md) T) ->
realizes rsegs (mkCfg (pe_ms rsegs pf 0x22cc0 (t_co ts) x1 gp t0 t1 t2 a0 (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) a2 a3 a4 a5 a6 a7
s4 s5 s6 s8 s10 t3 t4 t5 t6 F fc m) md) T.
Proof.
intros until fc. intros STC INV Hl Hst Kbreak. sesc_prologue STC INV. clear INV0.
pose proof REST as (_ & LV & _).
destruct ts as [depth levels co pb pbs xx obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct xx as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
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
pose proof (wmono_refl rsegs m) as WM.
pose proof (LV depth l Hl) as LVd. pose proof LVd as (ST26 & SS26 & _ & Md).
rewrite Nat.ltb_irrefl, Nat.eqb_refl in Md. destruct Md as (c0 & hn0 & Hmode & CLS0 & NM0).
pose proof (TSK depth l Hl) as Ld. unfold srec_cells in Ld.
remember (q + 32 * Z.of_nat depth) as bse eqn:Hbse in Ld.
assert (HbseR : q <= bse /\ bse + 32 <= q + (32 * mxd)) by (subst bse; lia).
pose proof (munch_refl [(tk + 28, tk + 32); (tk + 40, tk + 44); (bse, bse + 32)] m) as MU.
stash PB. stash REST. stash TSK. stash Himg_t. clear LV.
apply rz_evt; [exact MOK|]. replace (q + 32 * Z.of_nat depth) with bse by lia.
stepz. stepz. step. stepz. step.
unstash PB. unstash REST. unstash TSK.
set (l1 := TL ST_escape_unicode (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)).
assert (HW : Forall (pe_wtq (PEF tk oldl newl len lenr sb spf pmd mxd fl) q) [(tk + 28, tk + 32); (tk + 40, tk + 44); (bse, bse + 32)]).
{ repeat apply Forall_cons; try apply Forall_nil; [left; left; cbn [pf_tk fst snd pf_md pf_mxd pf_fl]; lia | left; left; cbn [pf_tk fst snd pf_md pf_mxd pf_fl]; lia | right; cbn [fst snd pf_mxd]; lia]. }
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
match goal with L5 : rw_cells rsegs mc bse _ |- _ =>
assert (TSK3 : tstack rsegs mc q (lupd levels depth l1))
by (subst bse; eapply (tstack_put rsegs m _ q levels depth l1 [(tk + 28, tk + 32); (tk + 40, tk + 44)]);
[exact TSK | lia | eapply munch_weaken; [| exact MU]; unfold sub_fp; cbn [outside pf_mxd]; intros; lia | exact WM
| intros j Hj Hne; cbn [disjoint_from fst snd pf_mxd]; lia | exact L5]);
assert (PB3 : pbuf rsegs mc pbs pb)
by (eapply (pbuf_wtq HIx) with (ts := ts0); [exact STC | exact (proj1 REST) | exact PB | exact MU | exact WM | exact HW]);
assert (REST3 : PE_REST HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo mc md A ts0 errv)
by (eapply (PE_REST_private_write HIx) with (ts := ts0) in REST; [exact REST | exact STC | exact MU | exact WM | assumption | apply pe_wtq_private; exact HW]);
subst bse; apply evt_RZ_done; apply (Kbreak mc)
end end.
split.
- unfold PE_CORE; cbn. split; [rewrite lupd_length; exact LEN32|]. split; [exact D32|]. split; [lia|]. split; [reflexivity|].
split; [unfold tok_cells, tok_cells_g; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd]; assumption|]. split; [exact PB3|]. split; [exact Hpb|]. split; [exact TSK3 | assumption].
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
eapply lvl_cur_restate with (c' := c0); [exact (LV' depth l Hl) | exact Hmode | | unfold ST_escape_unicode; lia | exact SS26 | left; reflexivity].
rewrite <- Hmode. apply lvl_mode_esc_same; [rewrite Hst; reflexivity | reflexivity | exact SS26].
* rewrite nth_error_lupd_neq in Hli by congruence. exact (LV' i li Hli).
+ revert OBJ'. unfold cur_st, ts0. cbn [t_levels t_depth t_objs t_objbs t_obj pf_mxd]. rewrite nth_error_lupd_eq by lia. cbn [tl_st pf_mxd].
rewrite Hl, Hst. cbn. intros OBJ'; exact OBJ'.
Qed.

#[using="MEMMOVE"] Lemma seg_sesc_bfnrt :
forall (pf : pe_fix) (q : Z) (LB0 : list blk) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (ts : tstate) (l : tlevel)
(cb : byte) (j1 j2 utf : list byte) (sv : pe_saved) (errv : word) (T : TSet)
(x1 gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s8 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC HIx pf lo ->
PE_INV HIx pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_string_escape ->
(bv_unsigned cb = 98 \/ bv_unsigned cb = 102 \/ bv_unsigned cb = 110 \/ bv_unsigned cb = 114 \/ bv_unsigned cb = 116) ->
(forall m' md' A' pbs' errv' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s8' s10' t3' t4' t5' t6' F' fc',
PE_INV HIx pf q LB0 payload me lo m' md' A' (ts_set_pbs (ts_set_level ts (TL (tl_ss l) (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) pbs') cb j1 j2 utf sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_BREAK (t_co ts) x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s8' s10' t3' t4' t5' t6' F' fc' m') md') T) ->
(forall m' md' A' pbs' errv' x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s8' s10' t3' t4' t5' t6' F' fc',
PE_INV HIx pf q LB0 payload me lo m' md' A' (ts_set_pbs ts pbs') cb j1 j2 utf sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_ERR (t_co ts) x1' gp' t0' t1' t2' (Z_to_bv 64 16) a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s8' s10' t3' t4' t5' t6' F' fc' m') md') T) ->
realizes rsegs (mkCfg (pe_ms rsegs pf 0x22730 (t_co ts) x1 gp t0 t1 t2 (Z_to_bv 64 (bv_unsigned cb)) a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s8 s10 t3 t4 t5 t6 F fc m) md) T.
Proof.
intros until fc. intros STC INV Hl Hst HC Kbreak Kerr16. sesc_prologue STC INV.
destruct ts as [depth levels co pb pbs xx obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct xx as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl_]; pe_gen fl_; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
unfold tok_cells, tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in TOK. unfold pe_frame in FR. unfold pe_ms in *. cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
unfold_consts.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK. pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L pf_mxd] in MI.
assert (INtk : In (tk, 72) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 (TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs))) by (unfold pe_blocks; apply in_or_app; right; left; reflexivity).
pose proof (heap_blk S4L HIx _ _ _ _ tk 72 HP INtk) as (_ & Htal & Htlo & Hthi & _). unfold alloc_ceiling, sp_window_lo, stack_max_size in Hthi.
pose proof (pe_jtab4_ro m MI) as JT4.
clear PB TSK REST FR.
assert (GO : forall (lit : Z) (xb : Z) (x1v a2v : word),
ro_bytes rsegs lit [Z_to_bv 8 xb] -> 65536 <= lit -> lit + 1 <= 618496 ->
evt rsegs (RZ rsegs md T)
(MS (mkR x1v (Z_to_bv 64 spf) gp (Z_to_bv 64 482928) t0 t1 t2 (Z_to_bv 64 tk) (Z_to_bv 64 oldl)
(Z_to_bv 64 pb) (Z_to_bv 64 lit) a2v a3 a4 a5 a6 a7
(Z_to_bv 64 newl) (Z_to_bv 64 lenr) s4 s5 s6 (Z_to_bv 64 26) s8 (Z_to_bv 64 (sb + co)) s10 (Z_to_bv 64 79024) t3 t4 t5 t6)
F (Z_to_bv 64 0x22db4) fc None m (seg_rom rsegs))).
{ intros lit xb x1v a2v RO Hl1 Hl2. apply evt_RZ_done.
eapply (sesc_tail (PEF tk oldl newl len lenr sb spf pmd mxd fl)) with (ts := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs);
[exact STC | exact INV0 | exact Hl | exact Hst | apply ro_bytes_at; [exact MI | lia | cbn; lia | exact RO] | left; split; [lia | split; [lia | exact RO]] | exact Kbreak | exact Kerr16]. }
apply rz_evt; [exact MOK|].
pose proof (bv_unsigned_in_range 8 cb) as CBR; unfold bv_modulus in CBR; cbn in CBR.
destruct HC as [E|[E|[E|[E|E]]]]; rewrite E in *;
do 8 step;
lazymatch goal with |- evt _ _ (MS _ _ (if ?c then ?a else ?b) _ _ _ _) => first [change (if c then a else b) with b | change (if c then a else b) with a] end;
do 5 step;
(match goal with |- context [sext 64 (bv_extract 0 32 (le_bytes_to_word ?lb))] =>
let v := eval vm_compute in (bv_unsigned (sext 64 (bv_extract 0 32 (le_bytes_to_word lb)))) in
replace (sext 64 (bv_extract 0 32 (le_bytes_to_word lb))) with (Z_to_bv 64 v) by (apply bv_eq; vm_compute; reflexivity) end);
do 6 step;
lazymatch type of E with bv_unsigned cb = ?cv =>
let lit := eval vm_compute in (esc_lit cv) in let xb := eval vm_compute in (esc_byte cv) in
eapply (GO lit xb); [apply (ro_bytes_b_sound rsegs); vm_compute; reflexivity | lia | lia]
end.
Qed.

#[using="Type"] Lemma seg_sesc_err :
forall (pf : pe_fix) (q : Z) (LB0 : list blk) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (ts : tstate)
(cb : byte) (j1 j2 utf : list byte) (sv : pe_saved) (errv : word) (T : TSet)
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s8 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_INV HIx pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_ERR (t_co ts) x1 gp t0 t1 t2 (Z_to_bv 64 12) a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s8 s10 t3 t4 t5 t6 F fc m) md) T ->
realizes rsegs (mkCfg (pe_ms rsegs pf 0x2317c (t_co ts) x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s8 s10 t3 t4 t5 t6 F fc m) md) T.
Proof.
intros until fc. intros INV K.
pose proof (heap_model_ok _ _ _ _ _ _ (proj1 (proj2 INV))) as MOK. pose proof (heap_mem_inv _ _ _ _ _ _ (proj1 (proj2 INV))) as MI. cbn [hl_segs S4L pf_mxd] in MI.
unfold pe_ms in *. apply rz_evt; [exact MOK|]. step. step. apply evt_RZ_done. exact K.
Qed.

#[using="MEMMOVE"] Lemma seg_sesc :
forall (pf : pe_fix) (q : Z) (LB0 : list blk) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (ts : tstate) (l : tlevel)
(cb : byte) (j1 j2 utf : list byte) (sv : pe_saved) (errv : word) (T : TSet)
(x1 gp t0 t1 t2 a3 a4 a5 a6 a7 s4 s5 s6 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC HIx pf lo ->
PE_INV HIx pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_string_escape ->
let c := bv_unsigned cb in

(forall m' md' A' pbs' errv' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s8' s10' t3' t4' t5' t6' F' fc',
(c = 34 \/ c = 47 \/ c = 92 \/ c = 98 \/ c = 102 \/ c = 110 \/ c = 114 \/ c = 116) ->
PE_INV HIx pf q LB0 payload me lo m' md' A' (ts_set_pbs (ts_set_level ts (TL (tl_ss l) (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) pbs') cb j1 j2 utf sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_BREAK (t_co ts) x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s8' s10' t3' t4' t5' t6' F' fc' m') md') T) ->

(forall m' a0' a2' a3',
c = 117 ->
PE_INV HIx pf q LB0 payload me lo m' md A
(TST (t_depth ts) (lupd (t_levels ts) (t_depth ts) (TL ST_escape_unicode (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)))
(t_co ts) (t_pb ts) (t_pbs ts)
(TS (ts_isd (t_x ts)) (Z_to_bv 64 0) (ts_choff (t_x ts)) (ts_err (t_x ts)) (Z_to_bv 64 0) (ts_high (t_x ts)) (ts_quote (t_x ts)))
(t_obj ts) (t_objs ts) (t_objbs ts)) cb j1 j2 utf sv errv ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_BREAK (t_co ts) x1 gp t0 t1 t2 a0' (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) a2' a3' a4 a5 a6 a7
s4 s5 s6 (Z_to_bv 64 q) (Z_to_bv 64 (Z.of_nat (t_depth ts))) t3 t4 t5 t6 F fc m') md) T) ->

(forall m' md' A' pbs' errv' x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s8' s10' t3' t4' t5' t6' F' fc',
(c = 34 \/ c = 47 \/ c = 92 \/ c = 98 \/ c = 102 \/ c = 110 \/ c = 114 \/ c = 116) ->
PE_INV HIx pf q LB0 payload me lo m' md' A' (ts_set_pbs ts pbs') cb j1 j2 utf sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_ERR (t_co ts) x1' gp' t0' t1' t2' (Z_to_bv 64 16) a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s8' s10' t3' t4' t5' t6' F' fc' m') md') T) ->

(forall a2' a3',
~ (c = 34 \/ c = 47 \/ c = 92 \/ c = 98 \/ c = 102 \/ c = 110 \/ c = 114 \/ c = 116 \/ c = 117) ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_ERR (t_co ts) x1 gp t0 t1 t2 (Z_to_bv 64 12) (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) a2' a3' a4 a5 a6 a7
s4 s5 s6 (Z_to_bv 64 q) (Z_to_bv 64 (Z.of_nat (t_depth ts))) t3 t4 t5 t6 F fc m) md) T) ->
realizes rsegs (mkCfg (pe_ms rsegs pf (pe_jt ST_string_escape) (t_co ts) x1 gp t0 t1 t2
(Z_to_bv 64 (32 * Z.of_nat (t_depth ts))) (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) (Z_to_bv 64 (tl_st l)) a3 a4 a5 a6 a7
s4 s5 s6 (Z_to_bv 64 q) (Z_to_bv 64 (Z.of_nat (t_depth ts))) t3 t4 t5 t6 F fc m) md) T.
Proof.
intros until fc. intros STC INV Hl Hst c Kapp Ku Kerr16 Kerr12.
pose proof (bv_unsigned_in_range 8 cb) as CBR; unfold bv_modulus in CBR; cbn in CBR. subst c.
eapply seg_sesc_dispatch; [exact STC | exact INV | exact Hl | exact Hst |]. intros a2' a3'.
destruct (Z.eq_dec (bv_unsigned cb) 117) as [E117|N117].
{ rewrite E117. cbn [pe_jt3 pf_mxd]. eapply seg_sesc_u; [exact STC | exact INV | exact Hl | exact Hst |]. intros m' a0'. apply Ku. exact E117. }
assert (CASES : ((bv_unsigned cb = 34 \/ bv_unsigned cb = 47 \/ bv_unsigned cb = 92) /\ pe_jt3 (bv_unsigned cb) = 0x22c48)
\/ ((bv_unsigned cb = 98 \/ bv_unsigned cb = 102 \/ bv_unsigned cb = 110 \/ bv_unsigned cb = 114 \/ bv_unsigned cb = 116) /\ pe_jt3 (bv_unsigned cb) = 0x22730)
\/ (~ (bv_unsigned cb = 34 \/ bv_unsigned cb = 47 \/ bv_unsigned cb = 92 \/ bv_unsigned cb = 98 \/ bv_unsigned cb = 102 \/ bv_unsigned cb = 110 \/ bv_unsigned cb = 114 \/ bv_unsigned cb = 116 \/ bv_unsigned cb = 117)
/\ pe_jt3 (bv_unsigned cb) = 0x2317c)).
{ assert (R : 0 <= bv_unsigned cb <= 255) by lia. clear - R N117.
enum_from (bv_unsigned cb) 0%Z 256%nat; first [exfalso; lia | left; split; [lia | reflexivity] | right; left; split; [lia | reflexivity] | right; right; split; [lia | reflexivity]]. }
destruct CASES as [[HC E] | [[HC E] | [HC E]]]; rewrite E.
- eapply seg_sesc_quote; [exact STC | exact INV | exact Hl | exact Hst | intros; eapply Kapp; [lia | eassumption..] | intros; eapply Kerr16; [lia | eassumption..]].
- eapply seg_sesc_bfnrt; [exact STC | exact INV | exact Hl | exact Hst | exact HC | intros; eapply Kapp; [lia | eassumption..] | intros; eapply Kerr16; [lia | eassumption..]].
- eapply seg_sesc_err; [exact INV |]. apply Kerr12. exact HC.
Qed.
End PeSesc.

End RC__2.
End Mq3.
From Stdlib Require Sorting.Permutation.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup.
Import QEQM.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0.
Import QC8c.Mq0.
Import Qsw7 QJjn QRUw.Mq2 QkMG.
Import QG8z Qdyh.Mq0 QIsM.Mq2 Qdyh.Mq2 Qa8x.
Import QJjn.Mq0.
Import QPZI.Mq3.
Import QBpZ QT7i Qv6q QIsM.
Import QzWc.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma string_mode : forall ss c hn, 0 <= ss <= 26 -> lvl_mode ST_string ss = Some (c, hn) -> c = CNone /\ hn = false.
Proof.
intros ss c hn R Hm. enum_z R ss; vm_compute in Hm; first [discriminate Hm | injection Hm as <- <-; split; reflexivity].
Qed.

#[using="Type"] Lemma zx32_fl : forall fl, 0 <= fl < 2^32 -> zx32 (Z_to_bv 64 fl) = Z_to_bv 64 fl.
Proof. intros fl H. unfold zx32. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. Qed.

Section PeString.
Variable HIx : heap_iface S4L.
Hypothesis MEMMOVE : memmove_stmt.

#[using="MEMMOVE"] Lemma str_flush :
forall (pf : pe_fix) (q : Z) (LB0 : list blk) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (ts : tstate) (co0 : Z)
(cb : byte) (j1 j2 utf : list byte) (sv : pe_saved) (errv : word) (T : TSet)
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s8 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC HIx pf lo ->
PE_INV HIx pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv ->
0 <= co0 < t_co ts ->
(forall m' md' A' pbs' errv' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s8' s10' t3' t4' t5' t6' F' fc',
PE_INV HIx pf q LB0 payload me lo m' md' A' (ts_set_pbs ts pbs') cb j1 j2 utf sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_OUT co0 x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s8' s10' t3' t4' t5' t6' F' fc' m') md') T) ->
(forall m' md' A' pbs' errv' x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s8' s10' t3' t4' t5' t6' F' fc',
PE_INV HIx pf q LB0 payload me lo m' md' A' (ts_set_pbs ts pbs') cb j1 j2 utf sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_ERR co0 x1' gp' t0' t1' t2' (Z_to_bv 64 16) a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s8' s10' t3' t4' t5' t6' F' fc' m') md') T) ->
realizes rsegs (mkCfg (pe_ms rsegs pf 0x23224 co0 x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 (Z_to_bv 64 (t_co ts - 1 - co0)) s8 s10 t3 t4 t5 t6 F fc m) md) T.
Proof.
intros until fc. intros STC INV Hco0 Kout Kerr16.
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
step. step. norm_w32. replace (co - 1 - co0 + 1) with n by lia. step. step. step.
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
- step. if_truex. apply evt_RZ_done. eapply Kout; [| exact FS2 | exact FRM2]. unfold ts2, pbs2 in INV2. exact INV2.
- replace (Z_to_bv 64 (2^64 - 1)) with (Z_to_bv 64 (-1)) by (apply bv_eq; vm_compute; reflexivity).
step. if_false. step. step. apply evt_RZ_done. eapply Kerr16; [| exact FS2 | exact FRM2]. unfold ts2, pbs2 in INV2. exact INV2.
Qed.

#[using="MEMMOVE"] Lemma str_eof :
forall (pf : pe_fix) (q : Z) (LB0 : list blk) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (ts : tstate) (co0 : Z)
(cb : byte) (j1 j2 utf : list byte) (sv : pe_saved) (errv : word) (T : TSet)
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC HIx pf lo ->
PE_INV HIx pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv ->
t_co ts = pf_len pf -> 0 <= co0 < pf_len pf ->
(forall m' md' A' pbs' (e : word) errv' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s8' s10' t3' t4' t5' t6' F' fc',
PE_INV HIx pf q LB0 payload me lo m' md' A' (ts_set_pbs (ts_set_err ts e) pbs') cb j1 j2 utf sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_OUT co0 x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s8' s10' t3' t4' t5' t6' F' fc' m') md') T) ->
(forall m' md' A' pbs' (e : word) errv' x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s8' s10' t3' t4' t5' t6' F' fc',
PE_INV HIx pf q LB0 payload me lo m' md' A' (ts_set_pbs (ts_set_err ts e) pbs') cb j1 j2 utf sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_ERR co0 x1' gp' t0' t1' t2' (Z_to_bv 64 16) a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s8' s10' t3' t4' t5' t6' F' fc' m') md') T) ->
realizes rsegs (mkCfg (pe_ms rsegs pf 0x231ac co0 x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 (Z_to_bv 64 (pf_len pf - 1 - co0))
(Z_to_bv 64 q) (Z_to_bv 64 (Z.of_nat (t_depth ts))) t3 t4 t5 t6 F fc m) md) T.
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
assert (TAIL : forall (e : word) mc a0' a1',
rw_cells rsegs mc tk
[C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 pb); C4 (Z_to_bv 64 mxd); C4 (Z_to_bv 64 (Z.of_nat depth)); C4 isd; C4 stpos;
C4 (Z_to_bv 64 len); C4 e; C4 ucs; C4 high; C1 quote; CB 7 (repeat (Z_to_bv 8 0) 7); C8 (Z_to_bv 64 q); C4 (Z_to_bv 64 fl); C4 (Z_to_bv 64 0)] ->
munch [(tk, tk + 72)] m mc -> wmono rsegs m mc -> mem_inv rsegs mc ->
evt rsegs (RZ rsegs md T)
(MS (mkR x1 (Z_to_bv 64 spf) gp (Z_to_bv 64 482928) t0 t1 t2 (Z_to_bv 64 tk) (Z_to_bv 64 oldl) a0' a1' a2 a3 a4 a5 a6 a7
(Z_to_bv 64 newl) (Z_to_bv 64 lenr) s4 s5 (Z_to_bv 64 (len - 1 - co0)) (Z_to_bv 64 26) (Z_to_bv 64 q) (Z_to_bv 64 (sb + co0)) (Z_to_bv 64 (Z.of_nat depth)) (Z_to_bv 64 79024) t3 t4 t5 t6)
F (Z_to_bv 64 0x23224) fc None mc (seg_rom rsegs))).
{ intros e mc a0' a1' TOK' MU' WM' MI'.
unstash PB. unstash REST.
apply evt_RZ_done.
eapply (str_flush (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo mc md A
(TST depth levels len pb pbs (TS isd stpos (Z_to_bv 64 len) e ucs high quote) obj objs objbs) co0 cb);
[exact STC | | cbn; lia
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
+ subst depth. cbn [Z.of_nat pf_mxd] in TOK, TAIL |- *. step. if_false.
destruct (nth_error levels 0) as [l0|] eqn:Hl0; [| apply nth_error_None in Hl0; lia].
pose proof (TSK 0%nat l0 Hl0) as L0. rewrite Z.mul_0_r, Z.add_0_r in L0. unfold srec_cells in L0.
assert (SS26 : 0 <= tl_st l0 <= 26 /\ 0 <= tl_ss l0 <= 26) by (unstash REST; pose proof (proj1 (proj2 REST) 0%nat l0 Hl0) as (A1 & A2 & _); split; [exact A1 | exact A2]).
stash TSK.
step. norm_sx32.
destruct (Z.eq_dec (tl_st l0) 0) as [S0 | Sn].
* rewrite S0. step. if_false. step. norm_sx32. step.
destruct (Z.eq_dec (tl_ss l0) 2) as [F2 | Fn].
-- rewrite F2. step. if_false. step. step. stepz. unstash TSK. eapply TAIL; [exact TOK | exact MU | exact WM | exact MI].
-- step. if_truex. step. step. stepz. unstash TSK. eapply TAIL; [exact TOK | exact MU | exact WM | exact MI].
* step. if_truex. step. step. stepz. unstash TSK. eapply TAIL; [exact TOK | exact MU | exact WM | exact MI].
+ step. if_truex. step. step. stepz. eapply TAIL; [exact TOK | exact MU | exact WM | exact MI].
Qed.

#[using="MEMMOVE"] Lemma str_bs :
forall (pf : pe_fix) (q : Z) (LB0 : list blk) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (ts : tstate) (l : tlevel) (co0 : Z)
(cb : byte) (j1 j2 utf : list byte) (sv : pe_saved) (errv : word) (T : TSet)
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s8 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC HIx pf lo ->
PE_INV HIx pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_string ->
0 <= co0 <= t_co ts -> t_co ts < pf_len pf ->
(forall m' md' A' pbs' errv' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s8' s10' t3' t4' t5' t6' F' fc',
PE_INV HIx pf q LB0 payload me lo m' md' A'
(ts_set_pbs (ts_set_level ts (TL ST_string_escape ST_string (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) pbs') cb j1 j2 utf sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_BREAK (t_co ts) x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s8' s10' t3' t4' t5' t6' F' fc' m') md') T) ->
(forall m' md' A' pbs' errv' x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s8' s10' t3' t4' t5' t6' F' fc',
PE_INV HIx pf q LB0 payload me lo m' md' A' (ts_set_pbs ts pbs') cb j1 j2 utf sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_ERR co0 x1' gp' t0' t1' t2' (Z_to_bv 64 16) a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s8' s10' t3' t4' t5' t6' F' fc' m') md') T) ->
realizes rsegs (mkCfg (pe_ms rsegs pf 0x22d04 co0 x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 (Z_to_bv 64 (pf_sb pf + t_co ts)) (Z_to_bv 64 (t_co ts - co0)) s8 s10 t3 t4 t5 t6 F fc m) md) T.
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
set (n := co - co0) in *.
pose proof (bytes_at_sub S4L m sb payload (Z.to_nat co0) (Z.to_nat n) STR ltac:(lia)) as SRC. cbn [hl_segs S4L pf_mxd] in SRC.
rewrite Z2Nat.id in SRC by lia.
assert (SRCL : Z.of_nat (length (firstn (Z.to_nat n) (skipn (Z.to_nat co0) payload))) = n) by (rewrite length_firstn, length_skipn; lia).
stash TSK. clear LV OBJ HPR.
apply rz_evt; [exact MOK|].
step. step. step. step.
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
step. if_true. step. step. apply evt_RZ_done. eapply Kerr16; [| exact FS2 | exact FRM2]. unfold ts2, pbs2 in INV2. exact INV2. }

step. if_falsex.
pose proof (srec_join8 _ _ _ (TSK depth l Hl)) as Ld. cbn [le4 Z_to_le_bytes app hl_segs S4L pf_mxd] in Ld.
remember (q + 32 * Z.of_nat depth) as bse eqn:Hbse in Ld.
assert (HbseR : q <= bse /\ bse + 32 <= q + (32 * mxd)) by (subst bse; lia).
pose proof (munch_refl [(bse, bse + 32)] m2) as MU. pose proof (wmono_refl rsegs m2) as WM.
pose proof INV2 as [CORE2 _]. pose proof CORE2 as (_ & _ & _ & _ & _ & PB2 & _).
stash PB2. stash REST2. stash TSK. clear CORE2 INV2.
step. norm_sx32. step.
step. rewrite (unsigned_lit (Z.of_nat depth)) by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32.
step. replace (q + Z.of_nat depth * 32) with bse by lia.
step. step. step. stepz. step. step.
unstash PB2. unstash REST2. unstash TSK.
set (l1 := TL ST_string_escape ST_string (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)).
assert (HW : Forall (pe_wtq (PEF tk oldl newl len lenr sb spf pmd mxd fl) q) [(bse, bse + 32)]) by (apply Forall_cons; [right; cbn [fst snd pf_mxd]; lia | apply Forall_nil]).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
match goal with L8 : rw_cells rsegs mc bse _ |- _ =>
pose proof (rw_cells_recast_prefix rsegs mc bse [C8 (Z_to_bv 64 34359738377)] [C4 (Z_to_bv 64 ST_string_escape); C4 (Z_to_bv 64 ST_string)]
[C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (tl_cur l)); C8 (Z_to_bv 64 (tl_name l))] L8 ltac:(cbn; repeat split)
ltac:(apply bytes_eq_by_unsigned; vm_compute; reflexivity) eq_refl) as L5; cbn [app pf_mxd] in L5;
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
rewrite Hst in Hmode. destruct (string_mode _ _ _ SS26 Hmode) as [-> ->].
eapply lvl_cur_restate with (c' := CNone); [exact (LV' depth l Hl) | rewrite Hst; exact Hmode | reflexivity | unfold ST_string_escape; lia | unfold ST_string; lia | left; reflexivity].
* rewrite nth_error_lupd_neq in Hli by congruence. exact (LV' i li Hli).
+ revert OBJ'. unfold cur_st, ts0, ts2. cbn [t_levels t_depth t_objs t_objbs t_obj pf_mxd]. rewrite nth_error_lupd_eq by lia. cbn [tl_st pf_mxd].
rewrite Hl, Hst. cbn. intros OBJ'; exact OBJ'.
Qed.

#[using="Type"] Lemma lupd_same : forall {X} (ls : list X) i x, nth_error ls i = Some x -> lupd ls i x = ls.
Proof.
induction ls as [|y ls IH]; intros [|i] x H; cbn in *; try discriminate.
- injection H as ->. reflexivity.
- f_equal. apply IH. exact H.
Qed.

#[using="Type"] Lemma strq_new :
forall (pf : pe_fix) (q : Z) (LB0 : list blk) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (ts : tstate) (l : tlevel) (co0 : Z)
(cb : byte) (j1 j2 utf : list byte) (sv : pe_saved) (errv : word) (T : TSet)
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s8 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC HIx pf lo ->
PE_INV HIx pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_string ->

(forall m' md' A' r cbs' errv' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s8' s10' t3' t4' t5' t6' F' fc',
r <> 0 ->
PE_INV HIx pf q LB0 payload me lo m' md' A'
(TST (t_depth ts) (lupd (t_levels ts) (t_depth ts) (TL ST_eatws ST_finish r (Some (Sstr false)) cbs' 0 []))
(t_co ts) (t_pb ts) (t_pbs ts) (t_x ts) (t_obj ts) (t_objs ts) (t_objbs ts))
cb j1 j2 utf sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_BREAK (t_co ts) x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s8' s10' t3' t4' t5' t6' F' fc' m') md') T) ->

(forall m' md' A' errv' x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s8' s10' t3' t4' t5' t6' F' fc',
PE_INV HIx pf q LB0 payload me lo m' md' A' ts cb j1 j2 utf sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_ERR co0 x1' gp' t0' t1' t2' (Z_to_bv 64 16) a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s8' s10' t3' t4' t5' t6' F' fc' m') md') T) ->
realizes rsegs (mkCfg (pe_ms rsegs pf 0x227d8 co0 x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 (Z_to_bv 64 (pf_sb pf + t_co ts)) s6 s8 s10 t3 t4 t5 t6 F fc m) md) T.
Proof.
intros until fc. intros STC INV Hl Hst Kbreak Kerr.
pose proof STC as (LO & LOS & SPA & HT & SP0 & LEN & SB0 & (SBL & RR & LENR)).
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
{ intros k. generalize ND; intros ND'. unfold pe_blocks in ND'. rewrite map_app in ND'. apply NoDup_app_remove_l in ND'. cbn [map blk_addr fst pf_tk pf_md pf_mxd pf_fl] in ND'.
apply List.NoDup_cons_iff in ND' as [_ ND']. apply List.NoDup_cons_iff in ND' as [Hnq _]. intros Hin. apply Hnq.
change q with (blk_addr (q, k)). apply in_map. exact Hin. }
assert (INCL0 : incl LB0 (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocks; intros b Hb; apply in_or_app; right; right; right; exact Hb).
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L pf_mxd] in MI.
pose proof (wmono_refl rsegs m) as WM.
pose proof (LV depth l Hl) as LVd. pose proof LVd as (ST26 & SS26 & JO & Md).
rewrite Nat.ltb_irrefl, Nat.eqb_refl in Md. destruct Md as (c0 & hn0 & Hmode & CLS0 & NM0).
rewrite Hst in Hmode. destruct (string_mode _ _ _ SS26 Hmode) as [-> ->].
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
remember (q + 32 * Z.of_nat depth) as bse eqn:Hbse.
assert (HbseR : q <= bse /\ bse + 32 <= q + (32 * mxd)) by (subst bse; lia).
assert (Eobjbs : objbs = []).
{ revert OBJ. unfold cur_st, ts0. cbn [t_levels t_depth t_objbs pf_mxd]. rewrite Hl, Hst. cbn. intros E; exact E. }

pose proof PB as (buf & bpos & cap & pre & post & Epbs & Lpre & PBC). pose proof PBC as (Hbpos & Hcap & Hclen & PBS & PBUF). cbn [hl_segs S4L pf_mxd] in PBS, PBUF.
assert (INbuf : In (buf, cap) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocks, tstate_blocks, ts0; cbn [t_pbs pf_mxd]; rewrite Epbs; apply in_or_app; left; apply in_or_app; left; right; left; reflexivity).
pose proof (heap_blk S4L HIx _ _ _ _ buf cap HP INbuf) as (_ & Hbufal & Hbuflo & Hbufhi & _). unfold alloc_ceiling, sp_window_lo, stack_max_size in Hbufhi.
assert (SRC : bytes_at rsegs m buf pre).
{ pose proof (rw_cells_bytes_at' _ _ _ _ PBUF) as X. cbn [cells_bytes cbytes app pf_mxd] in X. rewrite app_nil_r in X. apply bytes_at_app in X. exact (proj1 X). }
assert (Htkpb : tk <> pb).
{ generalize ND; intros ND'. unfold pe_blocks, tstate_blocks, ts0 in ND'. cbn [t_pbs pf_tk pf_md pf_mxd pf_fl] in ND'. rewrite Epbs in ND'.
intros E. assert (ND2 : List.NoDup (map blk_addr (([(pb, 16); (buf, cap)] ++ objbs ++ concat (map lvl_blocks levels)) ++ (tk, 72) :: (q, (32 * mxd)) :: LB0))) by exact ND'.
rewrite map_app in ND2. eapply (NoDup_app_in2 _ _ tk ND2); [rewrite E; cbn; left; reflexivity | cbn; left; reflexivity]. }
assert (INpb : In (pb, 16) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocks, tstate_blocks, ts0; cbn [t_pbs pf_mxd]; rewrite Epbs; apply in_or_app; left; apply in_or_app; left; left; reflexivity).
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ tk 72 pb 16 HP INtk INpb Htkpb) as Hdtkpb.
pose proof BASE as (_ & ST0 & ERR0 & _).
stash TSK. stash BASE. stash LV. clear HP PB.
apply rz_evt; [exact MOK|].
step. step. step. norm_sx32. step.
clear PBS PBUF.
apply evt_RZ_done.
eapply (json_object_new_string_len_cps HIx) with (LB := pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0) (lo := lo) (s := buf) (len := bpos) (src := pre);
[ unstash BASE; exact (proj1 BASE) | exact SRC | exact Lpre | left; eapply client_range_block; [exact INbuf | lia | lia] | lia | lia | lia
| .. ]; try alloc_side.
all: try (rewrite ?unsigned_lit by lia; first [exact ST0 | exact ERR0]).
all: try (rewrite ?unsigned_lit by lia; unfold PE_FRAME in *; clia).
intros ms2 md2 (mp & A2x & r & errv2 & RS2 & VM2 & ST2 & HPR2 & ERR2 & OUT).
destruct RS2 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F2 & fc2 & -> & FS2 & FRM2).
cbn [hl_segs hl_tp S4L pf_mxd] in *. rewrite ?(unsigned_lit spf) in ST2 by lia. rewrite ?(unsigned_lit spf) in HPR2 by lia.
unstash TSK. unstash BASE. unstash LV.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. cbn [hl_segs S4L pf_mxd] in FR.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in TOK; [| eapply client_range_block; [exact INtk | lia | cbn; lia]]. cbn [hl_segs S4L pf_mxd] in TOK.
apply (tstack_pres_g S4L _ _ _ _ _ _ HPR2 INq) in TSK; [| exact LEN32].
pose proof (srec_join8 _ _ _ (TSK depth l Hl)) as Ld. cbn [le4 Z_to_le_bytes app hl_segs S4L pf_mxd] in Ld. rewrite Hc0, Hn0 in Ld.
rewrite <- Hbse in Ld. cbn [hl_segs S4L pf_mxd] in TSK.
assert (PB2 : pbuf rsegs mp pbs pb).
{ exists buf, bpos, cap, pre, post. split; [exact Epbs|]. split; [exact Lpre|].
eapply pbuf_core_agree; [exact PBC | | exact INpb | exact INbuf].
eapply (agree_of_heap_pres rsegs S4L); [exact HPR2 | reflexivity | intros b Hb; exact Hb]. }
assert (AGL2 : agree_on rsegs BL m mp).
{ eapply (agree_of_heap_pres rsegs S4L); [exact HPR2 | reflexivity |].
intros b Hb. unfold pe_blocks, tstate_blocks. apply in_or_app; left. apply in_or_app; right. apply in_or_app; right. exact Hb. }
assert (LV2 : forall i li, nth_error levels i = Some li -> i <> depth -> lvl_cur rsegs S4F mp depth i li).
{ intros i li Hli Hne. eapply (lvl_cur_agree rsegs S4F); [exact (LV i li Hli) | exact AGL2 |].
intros b Hb. unfold BL. apply in_concat. exists (lvl_blocks li). split; [| exact Hb]. apply in_map. eapply nth_error_In. exact Hli. }
clear MI SRC WM.

assert (OUT' : exists A2 NB, HEAP S4L HIx A2 (NB ++ pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0) mp md2 /\
((r = 0 /\ NB = []) \/ (r <> 0 /\ NB = [(r, str_objsize bpos)] /\ jval rsegs S4F (Sstr false) mp NB r 1))).
{ destruct OUT as [(-> & HP2) | (Hr & J2 & HP2)].
- exists A2x, []. split; [exact HP2 | left; split; reflexivity].
- exists A2x, [(r, str_objsize bpos)]. split; [exact HP2 | right; split; [exact Hr | split; [reflexivity | exact J2]]]. }
clear OUT. destruct OUT' as (A2 & NB & HP2 & OUT).
assert (BASE2 : PE_BASE HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) LB0 payload me lo mp md2 A2 (NB ++ pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0) errv2)
by (eapply (PE_BASE_call HIx); [exact BASE | exact HPR2 | exact INCL0 | exact VM2 | exact HP2 | exact ST2 | exact ERR2]).
clear BASE HPR2.
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
stash PB2. stash TSK. stash BASE2. stash LV2. stash OUT.
reenter MOK2.
step. norm_sx32. step.
step. rewrite (unsigned_lit (Z.of_nat depth)) by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32.
step. replace (q + Z.of_nat depth * 32) with bse by lia.
step.
unstash PB2. unstash TSK. unstash BASE2. unstash LV2. unstash OUT.
destruct OUT as [[-> ->] | (Hr & -> & J2)].
-
step. if_true. step. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (BASE3 : PE_BASE HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) LB0 payload me lo mc md2 A2 ([] ++ pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0) errv2)
by (eapply (PE_BASE_write HIx); [exact STC | exact BASE2 | intros b Hb; apply in_or_app; right; exact (INCL0 _ Hb) | exact MU | exact WM | exact MI |];
apply Forall_cons; [| apply Forall_nil]; unfold base_w; cbn [fst snd pf_spf pf_md pf_mxd pf_fl]; left; exists q, (32 * mxd);
split; [apply in_or_app; right; exact INq|]; split; [exact NQ0 | lia]);
assert (PB3 : pbuf rsegs mc pbs pb)
by (eapply pbuf_agree; [exact PB2 | apply (AGY mc MU WM) | apply incl_refl]; intros a k Hin; eapply NEq; apply in_or_app; right; apply in_or_app; left; exact Hin);
assert (AGL3 : agree_on rsegs BL mp mc)
by (apply (AGY mc MU WM); intros a k Hin; eapply NEq; apply in_or_app; right; apply in_or_app; right; exact Hin);
assert (AGN : agree_on rsegs [] mp mc)
by (apply (AGY mc MU WM); intros a k Hin; eapply NEq; apply in_or_app; left; exact Hin);
assert (LV3 : forall i li, nth_error levels i = Some li -> i <> depth -> lvl_cur rsegs S4F mc depth i li)
by (intros i li Hli Hne; eapply (lvl_cur_agree rsegs S4F); [exact (LV2 i li Hli Hne) | exact AGL3 |];
intros b Hb; unfold BL; apply in_concat; exists (lvl_blocks li); split; [| exact Hb]; apply in_map; eapply nth_error_In; exact Hli)
end.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
match goal with L8 : rw_cells rsegs mc bse (?c1 :: ?rest) |- _ =>
pose proof (rw_cells_recast_prefix rsegs mc bse [c1] [C4 (Z_to_bv 64 (tl_st l)); C4 (Z_to_bv 64 (tl_ss l))]
rest L8 ltac:(cbn; repeat split) eq_refl eq_refl) as L5; cbn [app pf_mxd] in L5;
assert (TSK3 : tstack rsegs mc q levels)
by (rewrite <- (lupd_same levels depth l Hl) at 1; subst bse;
eapply (tstack_put rsegs mp mc q levels depth l []);
[exact TSK | lia | exact MU | exact WM | intros; exact I | unfold srec_cells; rewrite Hc0, Hn0; exact L5])
end end.
apply evt_RZ_done. eapply (Kerr _ md2 A2 errv2); [ | exact FS2 | exact FRM2].
split.
+ unfold PE_CORE, ts0. cbn [t_levels t_depth t_co t_pb t_pbs t_x t_obj ts_choff pf_len pf_tk pf_spf pf_md pf_mxd pf_fl].
split; [exact LEN32|]. split; [exact D32|]. split; [lia|]. split; [reflexivity|].
split; [unfold tok_cells, tok_cells_g; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd]; exact TOK|].
split; [exact PB3|]. split; [exact Hpb|]. split; [exact TSK3 | unfold pe_frame; exact FR].
+ cbn [app pf_mxd] in BASE3. apply (PE_REST_of_base HIx); [exact BASE3 | |].
* unfold ts0. cbn [t_levels t_depth pf_mxd]. intros i li Hli.
destruct (Nat.eq_dec i depth) as [-> | NE].
-- rewrite Hl in Hli. injection Hli as <-.
eapply (lvl_cur_agree rsegs S4F); [exact LVd | | apply incl_refl]. rewrite LB0l. intros a Ha (b & Hb & _). destruct Hb.
-- exact (LV3 i li Hli NE).
* revert OBJ. unfold cur_st, ts0. cbn [t_levels t_depth t_objs t_objbs t_obj pf_mxd]. rewrite Hl, Hst. cbn. intros E; exact E.
-
assert (HrR : 0 < r < 2^64).
{ pose proof (heap_blk S4L HIx _ _ _ _ r (str_objsize bpos) HP2 ltac:(left; reflexivity)) as (_ & _ & H0 & Hhi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size, str_objsize in Hhi. lia. }
step. if_falsex. step. step. stepz. step. step. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (BASE3 : PE_BASE HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) LB0 payload me lo mc md2 A2 ([(r, str_objsize bpos)] ++ pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0) errv2)
by (eapply (PE_BASE_write HIx); [exact STC | exact BASE2 | intros b Hb; apply in_or_app; right; exact (INCL0 _ Hb) | exact MU | exact WM | exact MI |];
apply Forall_cons; [| apply Forall_nil]; unfold base_w; cbn [fst snd pf_spf pf_md pf_mxd pf_fl]; left; exists q, (32 * mxd);
split; [apply in_or_app; right; exact INq|]; split; [exact NQ0 | lia]);
assert (PB3 : pbuf rsegs mc pbs pb)
by (eapply pbuf_agree; [exact PB2 | apply (AGY mc MU WM) | apply incl_refl]; intros a k Hin; eapply NEq; apply in_or_app; right; apply in_or_app; left; exact Hin);
assert (AGL3 : agree_on rsegs BL mp mc)
by (apply (AGY mc MU WM); intros a k Hin; eapply NEq; apply in_or_app; right; apply in_or_app; right; exact Hin);
assert (AGN : agree_on rsegs [(r, str_objsize bpos)] mp mc)
by (apply (AGY mc MU WM); intros a k Hin; eapply NEq; apply in_or_app; left; exact Hin);
assert (LV3 : forall i li, nth_error levels i = Some li -> i <> depth -> lvl_cur rsegs S4F mc depth i li)
by (intros i li Hli Hne; eapply (lvl_cur_agree rsegs S4F); [exact (LV2 i li Hli Hne) | exact AGL3 |];
intros b Hb; unfold BL; apply in_concat; exists (lvl_blocks li); split; [| exact Hb]; apply in_map; eapply nth_error_In; exact Hli)
end.
set (l' := TL ST_eatws ST_finish r (Some (Sstr false)) [(r, str_objsize bpos)] 0 []).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
match goal with L8 : rw_cells rsegs mc bse _ |- _ =>
pose proof (rw_cells_recast_prefix rsegs mc bse [C8 (Z_to_bv 64 8589934592)] [C4 (Z_to_bv 64 ST_eatws); C4 (Z_to_bv 64 ST_finish)]
[C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 r); C8 (Z_to_bv 64 0)] L8 ltac:(cbn; repeat split)
ltac:(apply bytes_eq_by_unsigned; vm_compute; reflexivity) eq_refl) as L5; cbn [app pf_mxd] in L5;
assert (TSK3 : tstack rsegs mc q (lupd levels depth l'))
by (subst bse; eapply (tstack_put rsegs mp mc q levels depth l' []);
[exact TSK | lia | exact MU | exact WM | intros; exact I | unfold srec_cells, l'; cbn [tl_st tl_ss tl_cur tl_name pf_mxd]; exact L5])
end end.
apply evt_RZ_done. eapply (Kbreak _ md2 A2 r [(r, str_objsize bpos)] errv2); [exact Hr | | exact FS2 | exact FRM2].
split.
+ unfold PE_CORE. cbn [t_levels t_depth t_co t_pb t_pbs t_x t_obj ts_choff pf_len pf_tk pf_spf pf_md pf_mxd pf_fl].
split; [rewrite lupd_length; exact LEN32|]. split; [exact D32|]. split; [lia|]. split; [reflexivity|].
split; [unfold tok_cells, tok_cells_g; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd]; exact TOK|].
split; [exact PB3|]. split; [exact Hpb|]. split; [exact TSK3 | unfold pe_frame; exact FR].
+ apply (PE_REST_of_base HIx).
* eapply (PE_BASE_perm HIx); [exact BASE3|].
unfold pe_blocks, tstate_blocks, ts0. cbn [t_pbs t_objbs t_levels pf_tk pf_md pf_mxd pf_fl]. rewrite <- !app_assoc.
apply (Permutation_trans (l' := pbs ++ (objbs ++ ([(r, str_objsize bpos)] ++ (concat (map lvl_blocks levels) ++ (tk, 72) :: (q, (32 * mxd)) :: LB0))))).
-- apply (Permutation_trans (l' := pbs ++ ([(r, str_objsize bpos)] ++ (objbs ++ (concat (map lvl_blocks levels) ++ (tk, 72) :: (q, (32 * mxd)) :: LB0))))); [apply Permutation_app_swap_app|].
apply Permutation_app_head. apply Permutation_app_swap_app.
-- apply Permutation_app_head. apply Permutation_app_head. rewrite (app_assoc [(r, str_objsize bpos)]). apply Permutation_app_tail. fold l'.
replace ([(r, str_objsize bpos)] ++ concat (map lvl_blocks levels)) with (lvl_blocks l' ++ concat (map lvl_blocks levels)) by (unfold lvl_blocks, l'; cbn; rewrite ?app_nil_r; reflexivity).
apply (concat_lupd_fill levels depth l); [exact Hl | exact LB0l].
* cbn [t_levels t_depth pf_mxd]. intros i li Hli.
destruct (Nat.eq_dec i depth) as [-> | NE].
-- rewrite nth_error_lupd_eq in Hli by lia. injection Hli as <-.
split; [cbn; unfold ST_eatws; lia|]. split; [cbn; unfold ST_finish; lia|]. split.
{ cbn [tl_cs tl_cbs tl_cur l' jopt pf_mxd]. split; [exact Hr|]. eapply jval_agree; [exact J2 | exact AGN | apply incl_refl]. }
rewrite Nat.ltb_irrefl, Nat.eqb_refl. exists CAny, false. split; [reflexivity|]. split; [exact I|]. cbn. split; reflexivity.
-- rewrite nth_error_lupd_neq in Hli by congruence. exact (LV3 i li Hli NE).
* revert OBJ. unfold cur_st, ts0. cbn [t_levels t_depth t_objs t_objbs t_obj pf_mxd]. rewrite nth_error_lupd_eq by lia. rewrite Hl, Hst. cbn. intros E; exact E.
Qed.

#[using="MEMMOVE"] Lemma strq_app :
forall (pf : pe_fix) (q : Z) (LB0 : list blk) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (ts : tstate) (l : tlevel) (co0 : Z)
(cb : byte) (j1 j2 utf : list byte) (sv : pe_saved) (errv : word) (T : TSet)
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s8 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC HIx pf lo ->
PE_INV HIx pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_string ->
0 <= co0 <= t_co ts -> t_co ts < pf_len pf ->
(forall m' md' A' r cbs' pbs' errv' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s8' s10' t3' t4' t5' t6' F' fc',
r <> 0 ->
PE_INV HIx pf q LB0 payload me lo m' md' A'
(TST (t_depth ts) (lupd (t_levels ts) (t_depth ts) (TL ST_eatws ST_finish r (Some (Sstr false)) cbs' 0 []))
(t_co ts) (t_pb ts) pbs' (t_x ts) (t_obj ts) (t_objs ts) (t_objbs ts)) cb j1 j2 utf sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_BREAK (t_co ts) x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s8' s10' t3' t4' t5' t6' F' fc' m') md') T) ->
(forall m' md' A' pbs' errv' x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s8' s10' t3' t4' t5' t6' F' fc',
PE_INV HIx pf q LB0 payload me lo m' md' A' (ts_set_pbs ts pbs') cb j1 j2 utf sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_ERR co0 x1' gp' t0' t1' t2' (Z_to_bv 64 16) a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s8' s10' t3' t4' t5' t6' F' fc' m') md') T) ->
realizes rsegs (mkCfg (pe_ms rsegs pf 0x227c4 co0 x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 (Z_to_bv 64 (pf_sb pf + t_co ts)) s6 s8 s10 t3 t4 t5 t6 F fc m) md) T.
Proof.
intros until fc. intros STC INV Hl Hst Hco0 Hco Kbreak Kerr16.
pose proof STC as (LO & LOS & SPA & HT & SP0 & LEN & SB0 & (SBL & RR & LENR)).
destruct INV as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof REST as (HP & LV & OBJ & ST & ERR & STR & PLEN & SBin & HPR & MDV & JCG).
destruct ts as [depth levels co pb pbs xx obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct xx as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl_]; pe_gen fl_; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
unfold ts_set_pbs in Kerr16. cbn [t_levels t_depth t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in Kbreak, Kerr16.
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
set (n := co - co0) in *.
pose proof (bytes_at_sub S4L m sb payload (Z.to_nat co0) (Z.to_nat n) STR ltac:(lia)) as SRC. cbn [hl_segs S4L pf_mxd] in SRC.
rewrite Z2Nat.id in SRC by lia.
assert (SRCL : Z.of_nat (length (firstn (Z.to_nat n) (skipn (Z.to_nat co0) payload))) = n) by (rewrite length_firstn, length_skipn; lia).
stash TSK. clear LV OBJ HPR.
apply rz_evt; [exact MOK|].
step. step. norm_w32. replace (sb + co - (sb + co0)) with n by lia. step. step.
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
step. if_true. step. step. apply evt_RZ_done. eapply Kerr16; [| exact FS2 | exact FRM2]. unfold ts2, pbs2 in INV2. exact INV2. }

step. if_falsex. apply evt_RZ_done.
eapply (strq_new (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo m2 md2 A2 ts2 l co0 cb);
[ exact STC | exact INV2 | exact Hl | exact Hst | | ].
- unfold ts2; cbn [t_levels t_depth t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd]. intros. eapply Kbreak; [eassumption | eassumption | eapply fsaved_trans; [exact FS2 | eassumption] | intros Hf; auto].
- unfold ts2, ts_set_pbs; cbn [t_levels t_depth t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd]. intros. eapply Kerr16; [eassumption | eapply fsaved_trans; [exact FS2 | eassumption] | intros Hf; auto].
Qed.

#[using="MEMMOVE"] Lemma str_loop :
forall (n : nat) (pf : pe_fix) (q : Z) (LB0 : list blk) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (ts : tstate) (l : tlevel) (co0 : Z)
(cb : byte) (j1 j2 utf : list byte) (sv : pe_saved) (errv : word) (T : TSet)
(x1 gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC HIx pf lo ->
PE_INV HIx pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv ->
CSTR_OK pf payload ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_string ->
0 <= co0 <= t_co ts -> t_co ts < pf_len pf -> nth_error payload (Z.to_nat (t_co ts)) = Some cb ->
bv_unsigned cb <> bv_unsigned (ts_quote (t_x ts)) ->
(pf_len pf - t_co ts <= Z.of_nat n) ->

(forall m' co' cb' (j2' : list byte) x1' a1' a2' a3',
t_co ts <= co' < pf_len pf -> nth_error payload (Z.to_nat co') = Some cb' -> bv_unsigned cb' = bv_unsigned (ts_quote (t_x ts)) ->
PE_INV HIx pf q LB0 payload me lo m' md A (ts_set_co ts co') cb' j1 j2' utf sv errv ->
realizes rsegs (mkCfg (pe_ms rsegs pf 0x227c4 co0 x1' gp t0 t1 t2 (Z_to_bv 64 (bv_unsigned cb')) a1' a2' a3' a4 a5 a6 a7
(Z_to_bv 64 (bv_unsigned (ts_quote (t_x ts)))) (Z_to_bv 64 (pf_sb pf + co')) (Z_to_bv 64 (co' - co0))
(Z_to_bv 64 q) (Z_to_bv 64 (Z.of_nat (t_depth ts))) t3 t4 t5 t6 F fc m') md) T) ->

(forall m' co' cb' (j2' : list byte) x1' a2' a3',
t_co ts <= co' < pf_len pf -> nth_error payload (Z.to_nat co') = Some cb' -> bv_unsigned cb' = 92 ->
PE_INV HIx pf q LB0 payload me lo m' md A (ts_set_co ts co') cb' j1 j2' utf sv errv ->
realizes rsegs (mkCfg (pe_ms rsegs pf 0x22d04 co0 x1' gp t0 t1 t2 (Z_to_bv 64 (bv_unsigned cb')) (Z_to_bv 64 92) a2' a3' a4 a5 a6 a7
(Z_to_bv 64 (bv_unsigned (ts_quote (t_x ts)))) (Z_to_bv 64 (pf_sb pf + co')) (Z_to_bv 64 (co' - co0))
(Z_to_bv 64 q) (Z_to_bv 64 (Z.of_nat (t_depth ts))) t3 t4 t5 t6 F fc m') md) T) ->

(forall m' md' A' pbs' (e : word) co' cb' errv' (j2' : list byte) x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s8' s10' t3' t4' t5' t6' F' fc',
t_co ts < co' <= pf_len pf ->
PE_INV HIx pf q LB0 payload me lo m' md' A'
(TST (t_depth ts) (t_levels ts) co' (t_pb ts) pbs'
(TS (ts_isd (t_x ts)) (ts_stpos (t_x ts)) (Z_to_bv 64 co') e (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))
(t_obj ts) (t_objs ts) (t_objbs ts)) cb' j1 j2' utf sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_OUT co0 x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s8' s10' t3' t4' t5' t6' F' fc' m') md') T) ->

(forall m' md' A' pbs' (e : word) co' cb' errv' (j2' : list byte) x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s8' s10' t3' t4' t5' t6' F' fc',
t_co ts < co' <= pf_len pf ->
PE_INV HIx pf q LB0 payload me lo m' md' A'
(TST (t_depth ts) (t_levels ts) co' (t_pb ts) pbs'
(TS (ts_isd (t_x ts)) (ts_stpos (t_x ts)) (Z_to_bv 64 co') e (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))
(t_obj ts) (t_objs ts) (t_objbs ts)) cb' j1 j2' utf sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_ERR co0 x1' gp' t0' t1' t2' (Z_to_bv 64 16) a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s8' s10' t3' t4' t5' t6' F' fc' m') md') T) ->

(forall m' co' cb' (j2' : list byte) x1' a1' a2' a3',
t_co ts <= co' < pf_len pf -> nth_error payload (Z.to_nat co') = Some cb' -> bv_unsigned cb' <= 31 -> Z.land (pf_fl pf) 1 = 1 ->
PE_INV HIx pf q LB0 payload me lo m' md A (ts_set_co ts co') cb' j1 j2' utf sv errv ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_ERR co0 x1' gp t0 t1 t2 (Z_to_bv 64 12) a1' a2' a3' a4 a5 a6 a7
(Z_to_bv 64 (bv_unsigned (ts_quote (t_x ts)))) (Z_to_bv 64 (pf_sb pf + co')) (Z_to_bv 64 (co' - co0))
(Z_to_bv 64 q) (Z_to_bv 64 (Z.of_nat (t_depth ts))) t3 t4 t5 t6 F fc m') md) T) ->
realizes rsegs (mkCfg (pe_ms rsegs pf 0x22afc co0 x1 gp t0 t1 t2
(Z_to_bv 64 (bv_unsigned cb)) a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (bv_unsigned (ts_quote (t_x ts)))) (Z_to_bv 64 (pf_sb pf + t_co ts)) (Z_to_bv 64 (t_co ts - co0))
(Z_to_bv 64 q) (Z_to_bv 64 (Z.of_nat (t_depth ts))) t3 t4 t5 t6 F fc m) md) T.
Proof.
induction n as [|n IH]; intros until fc; intros STC INV CSTR Hl Hst Hco0 Hco Hc NQ Hn Kquote Kbs Kout Kerr16 Kerr12s.
{ exfalso. destruct INV as [(_ & _ & CO & _) _]. cbn in Hn. lia. }
pose proof INV as INV0.
pose proof STC as (LO & LOS & SPA & HT & SP0 & LEN & SB0 & (SBL & RR & LENR)).
destruct INV as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof REST as (HP & LV & OBJ & ST & ERR & STR & PLEN & SBin & HPR & MDV & JCG).
destruct ts as [depth levels co pb pbs xx obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct xx as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl_]; pe_gen fl_; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
unfold ts_set_co in Kquote, Kbs, Kerr12s. cbn [t_levels t_depth t_co t_pb t_pbs t_x t_obj t_objs t_objbs ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd pf_fl pf_sb] in Kquote, Kbs, Kerr12s.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in TOK. unfold pe_frame in FR. unfold pe_ms in *. cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
unfold_consts.
pose proof (bv_unsigned_in_range 8 cb) as CBR; unfold bv_modulus in CBR; cbn in CBR.
pose proof (bv_unsigned_in_range 8 quote) as QR; unfold bv_modulus in QR; cbn in QR.
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
apply rz_evt; [exact MOK|].

step. step.
destruct (Z.eq_dec (bv_unsigned cb) 92) as [E92 | N92].
{ if_truex. unstash PB. unstash REST. unstash TSK. apply evt_RZ_done.
eapply (Kbs m co cb); [lia | exact Hc | exact E92 | exact INV0]. }
if_falsex.

step. rewrite (zx32_fl fl) by lia. step.
assert (TAIL : forall a2v, evt rsegs (RZ rsegs md T)
(MS (mkR x1 (Z_to_bv 64 spf) gp (Z_to_bv 64 482928) t0 t1 t2 (Z_to_bv 64 tk) (Z_to_bv 64 oldl) (Z_to_bv 64 (bv_unsigned cb)) (Z_to_bv 64 fl) a2v a3 a4 a5 a6 a7
(Z_to_bv 64 newl) (Z_to_bv 64 lenr) (Z_to_bv 64 (bv_unsigned quote)) (Z_to_bv 64 (sb + co)) (Z_to_bv 64 (co - co0)) (Z_to_bv 64 26)
(Z_to_bv 64 q) (Z_to_bv 64 (sb + co0)) (Z_to_bv 64 (Z.of_nat depth)) (Z_to_bv 64 79024) t3 t4 t5 t6)
F (Z_to_bv 64 0x22b18) fc None m (seg_rom rsegs))).
2:{ step. destruct (Z_lt_dec 31 (bv_unsigned cb)) as [GT | LE].
- if_truex. apply TAIL.
- if_falsex. step. rewrite (unsigned_lit fl) by lia.
destruct (land1_cases fl) as [F1 | F1]; rewrite F1.
+ step. if_false. apply TAIL.
+
step. if_true. step. step. unstash PB. unstash REST. unstash TSK. apply evt_RZ_done.
eapply (Kerr12s m co cb); [lia | exact Hc | lia | exact F1 | exact INV0]. }
intros a2v.

step. norm_sx32. step. norm_w32. step.

step.
destruct (Z.eq_dec (bv_unsigned cb) 0) as [E0 | N0].
{ if_truex. unstash PB. unstash REST. unstash TSK. apply evt_RZ_done.
replace (Z_to_bv 64 (co - co0)) with (Z_to_bv 64 (co + 1 - 1 - co0)) by (f_equal; lia).
lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mc _) _) _ =>
eapply (str_flush (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo mc md A
(TST depth levels (co + 1) pb pbs (TS isd stpos (Z_to_bv 64 (co + 1)) err ucs high quote) obj objs objbs) co0 cb);
[ exact STC | eapply MKINV; [lia | exact TOK | exact FR | exact MU | exact WM | exact MI] | cbn; lia
| unfold ts_set_pbs; cbn [t_levels t_depth t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd]; intros; eapply Kout; [| eassumption..]; lia
| unfold ts_set_pbs; cbn [t_levels t_depth t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd]; intros; eapply Kerr16; [| eassumption..]; lia ]
end. }
if_falsex.

step.
destruct (peek_cases (PEF tk oldl newl len lenr sb spf pmd mxd fl) payload co cb LENR CSTR (proj1 RR) ltac:(cbn [pf_len pf_mxd]; lia) ltac:(cbn [pf_len pf_mxd]; lia) Hc N0)
as [[Elenr Heof] | [Hne Hmore]]; [cbn [pf_len pf_lenr pf_mxd] in Elenr, Heof; subst lenr; pose (lenr := len) | cbn [pf_len pf_lenr pf_mxd] in Hne, Hmore].
{ if_truex. unstash PB. unstash REST. unstash TSK. apply evt_RZ_done.
replace (Z_to_bv 64 (co - co0)) with (Z_to_bv 64 (len - 1 - co0)) by (f_equal; lia).
lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mc _) _) _ =>
eapply (str_eof (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo mc md A
(TST depth levels (co + 1) pb pbs (TS isd stpos (Z_to_bv 64 (co + 1)) err ucs high quote) obj objs objbs) co0 cb);
[ exact STC | eapply MKINV; [lia | exact TOK | exact FR | exact MU | exact WM | exact MI] | cbn; lia | cbn; lia
| unfold ts_set_pbs, ts_set_err; cbn [t_levels t_depth t_co t_pb t_pbs t_x t_obj t_objs t_objbs ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd]; intros; eapply Kout; [| eassumption..]; lia
| unfold ts_set_pbs, ts_set_err; cbn [t_levels t_depth t_co t_pb t_pbs t_x t_obj t_objs t_objbs ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd]; intros; eapply Kerr16; [| eassumption..]; lia ]
end. }
if_falsex.
destruct (nth_error payload (Z.to_nat (co + 1))) as [c'|] eqn:Hc'; [| apply nth_error_None in Hc'; lia].
pose proof (bv_unsigned_in_range 8 c') as CBR'; unfold bv_modulus in CBR'; cbn in CBR'.

assert (JOINF : forall mf (nv x1x a0x a1x a2x a3x : word),
rw_cells rsegs mf tk
[C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 pb); C4 (Z_to_bv 64 mxd); C4 (Z_to_bv 64 (Z.of_nat depth)); C4 isd; C4 stpos;
C4 (Z_to_bv 64 (co + 1)); C4 err; C4 ucs; C4 high; C1 quote; CB 7 (repeat (Z_to_bv 8 0) 7); C8 (Z_to_bv 64 q); C4 (Z_to_bv 64 fl); C4 (Z_to_bv 64 0)] ->
rw_cells rsegs mf spf [C8 (Z_to_bv 64 obj); CB 16 j1; C4 nv; CB 3 (skipn 4 j2); C1 cb; CB 8 utf;
C8 (pe_s11 sv); C8 (pe_s10 sv); C8 (pe_s9 sv); C8 (pe_s8 sv); C8 (pe_s7 sv); C8 (pe_s6 sv);
C8 (pe_s5 sv); C8 (pe_s4 sv); C8 (pe_s3 sv); C8 (pe_s2 sv); C8 (pe_s1 sv); C8 (pe_s0 sv); C8 (pe_ra sv)] ->
munch [(tk, tk + 72); (spf, spf + 144)] m mf -> wmono rsegs m mf -> mem_inv rsegs mf ->
evt rsegs (RZ rsegs md T)
(MS (mkR x1x (Z_to_bv 64 spf) gp (Z_to_bv 64 482928) t0 t1 t2 (Z_to_bv 64 tk) (Z_to_bv 64 oldl) a0x a1x a2x a3x a4 a5 a6 a7
(Z_to_bv 64 newl) (Z_to_bv 64 lenr) (Z_to_bv 64 (bv_unsigned quote)) (Z_to_bv 64 (sb + co + 1)) (Z_to_bv 64 (co - co0)) (Z_to_bv 64 26)
(Z_to_bv 64 q) (Z_to_bv 64 (sb + co0)) (Z_to_bv 64 (Z.of_nat depth)) (Z_to_bv 64 79024) t3 t4 t5 t6)
F (Z_to_bv 64 0x22aec) fc None mf (seg_rom rsegs))).
{ intros mf nv x1x a0x a1x a2x a3x TOKf FRf MUf WMf MIf.
repeat match goal with H : rw_cells rsegs ?mx _ _ |- _ => lazymatch mx with mf => fail | m => fail | _ => clear H end end.
repeat match goal with H : munch _ m ?mx |- _ => lazymatch mx with mf => fail | _ => clear H end end.
repeat match goal with H : wmono rsegs m ?mx |- _ => lazymatch mx with mf => fail | m => fail | _ => clear H end end.
repeat match goal with H : mem_inv rsegs ?mx |- _ => lazymatch mx with mf => fail | m => fail | _ => clear H end end.
try clear MU; try clear WM; try clear MI. rename MUf into MU. rename WMf into WM. rename MIf into MI. rename TOKf into TOK. rename FRf into FR.
assert (STR1 : bytes_at rsegs mf sb payload)
by (unstash REST; eapply (PE_REST_private_write HIx) with (ts := ts0) in REST;
[exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 REST)))))) | exact STC | exact MU | exact WM | exact MI | apply pe_wtf_private; exact HW]).
pose proof (payload_byte _ _ _ _ _ STR1 Hc' ltac:(lia)) as RDC. replace (sb + (co + 1)) with (sb + co + 1) in RDC by lia.
step. change (zxb c') with (Z_to_bv 64 (bv_unsigned c')).
step. rewrite le1_zxw. mem_after_store.
step. norm_w32. step.
try clear STR1. try clear RDC.
unstash PB. unstash REST. unstash TSK.
destruct (Z.eq_dec (bv_unsigned c') (bv_unsigned quote)) as [EQ | NQ'].
- if_truex. apply evt_RZ_done. replace (sb + co + 1) with (sb + (co + 1)) by lia. replace (co - co0 + 1) with (co + 1 - co0) by lia.
lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mc _) _) _ =>
eapply (Kquote mc (co + 1) c'); [lia | exact Hc' | exact EQ | eapply MKINV; [lia | exact TOK | exact FR | exact MU | exact WM | exact MI]]
end.
- if_falsex. apply evt_RZ_done.
replace (sb + co + 1) with (sb + (co + 1)) by lia. replace (co - co0 + 1) with (co + 1 - co0) by lia.
lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mc _) _) _ =>
eapply (IH (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo mc md A
(TST depth levels (co + 1) pb pbs (TS isd stpos (Z_to_bv 64 (co + 1)) err ucs high quote) obj objs objbs) l co0 c');
[ exact STC | eapply MKINV; [lia | exact TOK | exact FR | exact MU | exact WM | exact MI] | exact CSTR | exact Hl | exact Hst | cbn; lia | cbn; lia | exact Hc' | exact NQ' | cbn; lia
| cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_sb pf_len pf_md pf_mxd pf_fl];
intros; eapply Kquote; [cbn in *; lia | eassumption | assumption | eassumption]
| cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_sb pf_len pf_md pf_mxd pf_fl];
intros; eapply Kbs; [cbn in *; lia | eassumption | assumption | eassumption]
| cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_sb pf_len pf_md pf_mxd pf_fl];
intros; eapply Kout; [| eassumption..]; cbn in *; lia
| cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_sb pf_len pf_md pf_mxd pf_fl];
intros; eapply Kerr16; [| eassumption..]; cbn in *; lia
| cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_sb pf_len pf_md pf_mxd pf_fl];
intros; eapply Kerr12s; [cbn in *; lia | eassumption | assumption | assumption | eassumption] ]
end. }

step. rewrite (unsigned_lit fl) by lia. step.
destruct (land16_cases fl) as [F16 | F16]; rewrite F16.
+
step. if_true. eapply JOINF; [exact TOK | exact FR | exact MU | exact WM | exact MI].
+
step. if_false.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
assert (STR1 : bytes_at rsegs m1 sb payload)
by (unstash REST; eapply (PE_REST_private_write HIx) with (ts := ts0) in REST;
[exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 REST)))))) | exact STC | exact MU | exact WM | exact MI | apply pe_wtf_private; exact HW])
end.
pose proof (payload_byte _ _ _ _ _ STR1 Hc' ltac:(lia)) as RDC. replace (sb + (co + 1)) with (sb + co + 1) in RDC by lia.
step. step. step.
eapply evt_cut.
{ eapply (validate_utf8_frame_P) with (c := c') (A := spf + 24) (B := spf) (pre := [C8 (Z_to_bv 64 obj); CB 16 j1]);
[exact FR | reflexivity | lia | lia | exact MI]. }
intros ms' (r & a2' & a3' & nv' & m2 & -> & Hr & FR2 & MU2 & WM2 & MI2). cbn [app] in FR2.
replace (ret_pc (Z_to_bv 64 0x22b44)) with (Z_to_bv 64 0x22b44) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
lazymatch goal with MUa : munch _ m ?m1 |- _ =>
lazymatch type of TOK with rw_cells rsegs ?m1' tk ?cells =>
assert (TOK2 : rw_cells rsegs m2 tk cells)
by (eapply rw_cells_transport; [exact TOK | exact MU2 | exact WM2 | cbn; lia]);
assert (MU2' : munch [(tk, tk + 72); (spf, spf + 144)] m m2)
by (eapply munch_trans; [exact MUa | eapply munch_weaken; [| exact MU2]; intros z Hz; cbn in Hz |- *; lia])
end end.
pose proof (wmono_trans _ _ _ _ WM WM2) as WM2'. clear STR1 RDC MU2 WM2.
lazymatch type of MU2' with munch _ _ ?m2x => repeat match goal with H : munch _ _ ?mx |- _ => lazymatch mx with m2x => fail | _ => clear H end end end.
destruct Hr as [[-> Em] | ->].
*
step. if_false. step. step. stepz.
unstash PB. unstash REST. unstash TSK. apply evt_RZ_done.
replace (Z_to_bv 64 (co - co0)) with (Z_to_bv 64 (co + 1 - 1 - co0)) by (f_equal; lia).
lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mc _) _) _ =>
lazymatch goal with TOK3 : rw_cells rsegs mc tk [_; _; _; _; _; _; _; C4 ?e3; _; _; _; _; _; _; _] |- _ =>
eapply (str_flush (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo mc md A
(TST depth levels (co + 1) pb pbs (TS isd stpos (Z_to_bv 64 (co + 1)) e3 ucs high quote) obj objs objbs) co0 cb);
[ exact STC | eapply MKINV; [lia | exact TOK3 | eassumption | eassumption | eassumption | assumption] | cbn; lia
| unfold ts_set_pbs; cbn [t_levels t_depth t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd]; intros; eapply Kout; [| eassumption..]; lia
| unfold ts_set_pbs; cbn [t_levels t_depth t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd]; intros; eapply Kerr16; [| eassumption..]; lia ]
end end.
*
step. if_true. eapply JOINF; [exact TOK2 | exact FR2 | exact MU2' | exact WM2' | exact MI2].
Qed.

#[using="MEMMOVE"] Lemma seg_string :
forall (pf : pe_fix) (q : Z) (LB0 : list blk) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (ts : tstate) (l : tlevel)
(cb : byte) (j1 j2 utf : list byte) (sv : pe_saved) (errv : word) (T : TSet)
(x1 gp t0 t1 t2 a3 a4 a5 a6 a7 s4 s5 s6 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC HIx pf lo ->
PE_INV HIx pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv ->
CSTR_OK pf payload ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_string ->
t_co ts < pf_len pf -> nth_error payload (Z.to_nat (t_co ts)) = Some cb ->

(forall m' md' A' r cbs' pbs' errv' co' cb' (j2' : list byte) x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s8' s10' t3' t4' t5' t6' F' fc',
t_co ts <= co' < pf_len pf -> nth_error payload (Z.to_nat co') = Some cb' -> bv_unsigned cb' = bv_unsigned (ts_quote (t_x ts)) -> r <> 0 ->
PE_INV HIx pf q LB0 payload me lo m' md' A'
(TST (t_depth ts) (lupd (t_levels ts) (t_depth ts) (TL ST_eatws ST_finish r (Some (Sstr false)) cbs' 0 []))
co' (t_pb ts) pbs'
(TS (ts_isd (t_x ts)) (ts_stpos (t_x ts)) (Z_to_bv 64 co') (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))
(t_obj ts) (t_objs ts) (t_objbs ts)) cb' j1 j2' utf sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_BREAK co' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s8' s10' t3' t4' t5' t6' F' fc' m') md') T) ->

(forall m' md' A' pbs' errv' co' cb' (j2' : list byte) x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s8' s10' t3' t4' t5' t6' F' fc',
t_co ts <= co' < pf_len pf -> nth_error payload (Z.to_nat co') = Some cb' -> bv_unsigned cb' = 92 ->
PE_INV HIx pf q LB0 payload me lo m' md' A'
(TST (t_depth ts) (lupd (t_levels ts) (t_depth ts) (TL ST_string_escape ST_string (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)))
co' (t_pb ts) pbs'
(TS (ts_isd (t_x ts)) (ts_stpos (t_x ts)) (Z_to_bv 64 co') (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))
(t_obj ts) (t_objs ts) (t_objbs ts)) cb' j1 j2' utf sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_BREAK co' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s8' s10' t3' t4' t5' t6' F' fc' m') md') T) ->

(forall m' md' A' pbs' (e : word) co' cb' errv' (j2' : list byte) x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s8' s10' t3' t4' t5' t6' F' fc',
t_co ts < co' <= pf_len pf ->
PE_INV HIx pf q LB0 payload me lo m' md' A'
(TST (t_depth ts) (t_levels ts) co' (t_pb ts) pbs'
(TS (ts_isd (t_x ts)) (ts_stpos (t_x ts)) (Z_to_bv 64 co') e (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))
(t_obj ts) (t_objs ts) (t_objbs ts)) cb' j1 j2' utf sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_OUT (t_co ts) x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s8' s10' t3' t4' t5' t6' F' fc' m') md') T) ->

(forall m' md' A' pbs' (e : word) co' cb' errv' (j2' : list byte) x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s8' s10' t3' t4' t5' t6' F' fc',
t_co ts <= co' <= pf_len pf ->
PE_INV HIx pf q LB0 payload me lo m' md' A'
(TST (t_depth ts) (t_levels ts) co' (t_pb ts) pbs'
(TS (ts_isd (t_x ts)) (ts_stpos (t_x ts)) (Z_to_bv 64 co') e (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))
(t_obj ts) (t_objs ts) (t_objbs ts)) cb' j1 j2' utf sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_ERR (t_co ts) x1' gp' t0' t1' t2' (Z_to_bv 64 16) a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s8' s10' t3' t4' t5' t6' F' fc' m') md') T) ->

(forall m' co' cb' (j2' : list byte) x1' a1' a2' a3',
t_co ts <= co' < pf_len pf -> nth_error payload (Z.to_nat co') = Some cb' -> bv_unsigned cb' <= 31 -> Z.land (pf_fl pf) 1 = 1 ->
PE_INV HIx pf q LB0 payload me lo m' md A
(TST (t_depth ts) (t_levels ts) co' (t_pb ts) (t_pbs ts)
(TS (ts_isd (t_x ts)) (ts_stpos (t_x ts)) (Z_to_bv 64 co') (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))
(t_obj ts) (t_objs ts) (t_objbs ts)) cb' j1 j2' utf sv errv ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_ERR (t_co ts) x1' gp t0 t1 t2 (Z_to_bv 64 12) a1' a2' a3' a4 a5 a6 a7
(Z_to_bv 64 (bv_unsigned (ts_quote (t_x ts)))) (Z_to_bv 64 (pf_sb pf + co')) (Z_to_bv 64 (co' - t_co ts))
(Z_to_bv 64 q) (Z_to_bv 64 (Z.of_nat (t_depth ts))) t3 t4 t5 t6 F fc m') md) T) ->
realizes rsegs (mkCfg (pe_ms rsegs pf (pe_jt ST_string) (t_co ts) x1 gp t0 t1 t2
(Z_to_bv 64 (32 * Z.of_nat (t_depth ts))) (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) (Z_to_bv 64 (tl_st l)) a3 a4 a5 a6 a7
s4 s5 s6 (Z_to_bv 64 q) (Z_to_bv 64 (Z.of_nat (t_depth ts))) t3 t4 t5 t6 F fc m) md) T.
Proof.
intros until fc. intros STC INV CSTR Hl Hst Hco Hc Kq Kbs Kout Kerr16 Kerr12s.
pose proof INV as [CORE REST].
pose proof CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof (heap_model_ok _ _ _ _ _ _ (proj1 REST)) as MOK.
pose proof (bv_unsigned_in_range 8 cb) as CBR; unfold bv_modulus in CBR; cbn in CBR.
pose proof STC as (LO & LOS & SPA & HT & SP0 & LEN & SB0 & (SBL & RR & LENR)).
revert INV Kq Kbs Kout Kerr16 Kerr12s.
destruct ts as [depth levels co pb pbs xx obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct xx as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl_]; pe_gen fl_; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
intros INV Kq Kbs Kout Kerr16 Kerr12s.
pose proof (bv_unsigned_in_range 8 quote) as QR; unfold bv_modulus in QR; cbn in QR.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in TOK.
unfold pe_frame in FR. unfold pe_ms. cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl]. unfold_consts.
clear PB TSK REST CORE.
apply rz_evt; [exact MOK|].
step. change (zxb cb) with (Z_to_bv 64 (bv_unsigned cb)). step. change (zxb quote) with (Z_to_bv 64 (bv_unsigned quote)). step. step.
destruct (Z.eq_dec (bv_unsigned cb) (bv_unsigned quote)) as [EQ | NQ].
- if_falsex. apply evt_RZ_done.
eapply (strq_app (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo m md A
(TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) l co cb);
[ exact STC | exact INV | exact Hl | exact Hst | cbn; lia | exact Hco
| cbn [t_levels t_depth t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd]; intros; eapply Kq; [| exact Hc | exact EQ | eassumption..]; lia
| unfold ts_set_pbs; cbn [t_levels t_depth t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd]; intros; eapply Kerr16; [| eassumption..]; lia ].
- if_truex. step. step. step.
apply evt_RZ_done. replace (Z_to_bv 64 0) with (Z_to_bv 64 (co - co)) by (f_equal; lia).
eapply (str_loop (Z.to_nat (len - co)) (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo m md A
(TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) l co cb);
[ exact STC | exact INV | exact CSTR | exact Hl | exact Hst | cbn; lia | exact Hco | exact Hc | exact NQ | cbn; lia | | | | | ].
+ unfold ts_set_co; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_sb pf_len pf_md pf_mxd pf_fl].
intros m' co' cb' j2' x1' a1' a2' a3' R' Hc' EQ INV'.
eapply (strq_app (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo m' md A
(TST depth levels co' pb pbs (TS isd stpos (Z_to_bv 64 co') err ucs high quote) obj objs objbs) l co cb');
[ exact STC | exact INV' | exact Hl | exact Hst | cbn; lia | cbn; lia
| cbn [t_levels t_depth t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd]; intros; eapply Kq; [| exact Hc' | exact EQ | eassumption..]; lia
| unfold ts_set_pbs; cbn [t_levels t_depth t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd]; intros; eapply Kerr16; [| eassumption..]; lia ].
+ unfold ts_set_co; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_sb pf_len pf_md pf_mxd pf_fl].
intros m' co' cb' j2' x1' a2' a3' R' Hc' E92 INV'.
eapply (str_bs (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo m' md A
(TST depth levels co' pb pbs (TS isd stpos (Z_to_bv 64 co') err ucs high quote) obj objs objbs) l co cb');
[ exact STC | exact INV' | exact Hl | exact Hst | cbn; lia | cbn; lia
| unfold ts_set_pbs, ts_set_level; cbn [t_levels t_depth t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd]; intros; eapply Kbs; [| exact Hc' | exact E92 | eassumption..]; lia
| unfold ts_set_pbs; cbn [t_levels t_depth t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd]; intros; eapply Kerr16; [| eassumption..]; lia ].
+ cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_sb pf_len pf_md pf_mxd pf_fl].
intros. eapply Kout; eassumption.
+ cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_sb pf_len pf_md pf_mxd pf_fl].
intros. eapply Kerr16; [| eassumption..]. lia.
+ cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_sb pf_len pf_md pf_mxd pf_fl].
intros. eapply Kerr12s; eassumption.
Qed.
End PeString.

End RC__1.
End Mq4.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEQM.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDH.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QC8c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QC8c.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QkMG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkMG.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QG8z.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QG8z. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QIsM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QIsM.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qdyh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qdyh.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qa8x.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qa8x.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBpZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBpZ. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QT7i.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QT7i. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qv6q.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qv6q.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QzWc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QzWc.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section PeCeol.
Variable HIx : heap_iface S4L.
Hypothesis MEMMOVE : memmove_stmt.

#[using="MEMMOVE"] Lemma ceol_eof :
forall (pf : pe_fix) (q : Z) (LB0 : list blk) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (ts : tstate) (co0 : Z)
(cb : byte) (j1 j2 utf : list byte) (sv : pe_saved) (errv : word) (T : TSet)
(x1 gp t0 t1 t2 a0 a1 a3 a4 a5 a6 a7 s4 s5 s6 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC HIx pf lo ->
PE_INV HIx pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv ->
t_co ts = pf_len pf -> 0 <= co0 < pf_len pf ->
(forall m' md' A' pbs' (e : word) errv' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s8' s10' t3' t4' t5' t6' F' fc',
PE_INV HIx pf q LB0 payload me lo m' md' A' (ts_set_pbs (ts_set_err ts e) pbs') cb j1 j2 utf sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_OUT co0 x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s8' s10' t3' t4' t5' t6' F' fc' m') md') T) ->
(forall m' md' A' pbs' (e : word) errv' x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s8' s10' t3' t4' t5' t6' F' fc',
PE_INV HIx pf q LB0 payload me lo m' md' A' (ts_set_pbs (ts_set_err ts e) pbs') cb j1 j2 utf sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_ERR co0 x1' gp' t0' t1' t2' (Z_to_bv 64 16) a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s8' s10' t3' t4' t5' t6' F' fc' m') md') T) ->
realizes rsegs (mkCfg (pe_ms rsegs pf 0x231e4 co0 x1 gp t0 t1 t2 a0 a1 (Z_to_bv 64 (pf_len pf - co0)) a3 a4 a5 a6 a7 s4 s5 s6
(Z_to_bv 64 q) (Z_to_bv 64 (Z.of_nat (t_depth ts))) t3 t4 t5 t6 F fc m) md) T.
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
assert (TAIL : forall (e : word) mc a0' a1',
rw_cells rsegs mc tk
[C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 pb); C4 (Z_to_bv 64 mxd); C4 (Z_to_bv 64 (Z.of_nat depth)); C4 isd; C4 stpos;
C4 (Z_to_bv 64 len); C4 e; C4 ucs; C4 high; C1 quote; CB 7 (repeat (Z_to_bv 8 0) 7); C8 (Z_to_bv 64 q); C4 (Z_to_bv 64 fl); C4 (Z_to_bv 64 0)] ->
munch [(tk, tk + 72)] m mc -> wmono rsegs m mc -> mem_inv rsegs mc ->
evt rsegs (RZ rsegs md T)
(MS (mkR x1 (Z_to_bv 64 spf) gp (Z_to_bv 64 482928) t0 t1 t2 (Z_to_bv 64 tk) (Z_to_bv 64 oldl) a0' a1' (Z_to_bv 64 (len - co0)) a3 a4 a5 a6 a7
(Z_to_bv 64 newl) (Z_to_bv 64 lenr) s4 s5 s6 (Z_to_bv 64 26) (Z_to_bv 64 q) (Z_to_bv 64 (sb + co0)) (Z_to_bv 64 (Z.of_nat depth)) (Z_to_bv 64 79024) t3 t4 t5 t6)
F (Z_to_bv 64 0x23214) fc None mc (seg_rom rsegs))).
{ intros e mc a0' a1' TOK' MU' WM' MI'.
unstash PB. unstash REST.
apply evt_RZ_done.
eapply (cmt_flush HIx MEMMOVE (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo mc md A
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
+ subst depth. cbn [Z.of_nat pf_mxd] in TOK, TAIL |- *. step. if_false.
destruct (nth_error levels 0) as [l0|] eqn:Hl0; [| apply nth_error_None in Hl0; lia].
pose proof (TSK 0%nat l0 Hl0) as L0. rewrite Z.mul_0_r, Z.add_0_r in L0. unfold srec_cells in L0.
assert (SS26 : 0 <= tl_st l0 <= 26 /\ 0 <= tl_ss l0 <= 26) by (unstash REST; pose proof (proj1 (proj2 REST) 0%nat l0 Hl0) as (A1 & A2 & _); split; [exact A1 | exact A2]).
stash TSK.
step. norm_sx32.
destruct (Z.eq_dec (tl_st l0) 0) as [S0 | Sn].
* rewrite S0. step. if_false. step. norm_sx32. step.
destruct (Z.eq_dec (tl_ss l0) 2) as [F2 | Fn].
-- rewrite F2. step. if_false. step. step. stepz. unstash TSK. eapply TAIL; [exact TOK | exact MU | exact WM | exact MI].
-- step. if_truex. step. step. stepz. unstash TSK. eapply TAIL; [exact TOK | exact MU | exact WM | exact MI].
* step. if_truex. step. step. stepz. unstash TSK. eapply TAIL; [exact TOK | exact MU | exact WM | exact MI].
+ step. if_truex. step. step. stepz. eapply TAIL; [exact TOK | exact MU | exact WM | exact MI].
Qed.

#[using="MEMMOVE"] Lemma ceol_nl :
forall (pf : pe_fix) (q : Z) (LB0 : list blk) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (ts : tstate) (l : tlevel) (co0 : Z)
(cb : byte) (j1 j2 utf : list byte) (sv : pe_saved) (errv : word) (T : TSet)
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s8 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC HIx pf lo ->
PE_INV HIx pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_comment_eol ->
0 <= co0 <= t_co ts -> t_co ts < pf_len pf ->
(forall m' md' A' pbs' errv' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s8' s10' t3' t4' t5' t6' F' fc',
PE_INV HIx pf q LB0 payload me lo m' md' A'
(ts_set_pbs (ts_set_level ts (TL ST_eatws (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) pbs') cb j1 j2 utf sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_BREAK (t_co ts) x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s8' s10' t3' t4' t5' t6' F' fc' m') md') T) ->
(forall m' md' A' pbs' errv' x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s8' s10' t3' t4' t5' t6' F' fc',
PE_INV HIx pf q LB0 payload me lo m' md' A' (ts_set_pbs ts pbs') cb j1 j2 utf sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_ERR co0 x1' gp' t0' t1' t2' (Z_to_bv 64 16) a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s8' s10' t3' t4' t5' t6' F' fc' m') md') T) ->
realizes rsegs (mkCfg (pe_ms rsegs pf 0x226d8 co0 x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 (Z_to_bv 64 (pf_sb pf + t_co ts)) s6 s8 s10 t3 t4 t5 t6 F fc m) md) T.
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
set (n := co - co0) in *.
pose proof (bytes_at_sub S4L m sb payload (Z.to_nat co0) (Z.to_nat n) STR ltac:(lia)) as SRC. cbn [hl_segs S4L pf_mxd] in SRC.
rewrite Z2Nat.id in SRC by lia.
assert (SRCL : Z.of_nat (length (firstn (Z.to_nat n) (skipn (Z.to_nat co0) payload))) = n) by (rewrite length_firstn, length_skipn; lia).
stash TSK. clear LV OBJ HPR.
apply rz_evt; [exact MOK|].
step. step. norm_w32. replace (sb + co - (sb + co0)) with n by lia. step. step.
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
step. if_true. step. step. apply evt_RZ_done. eapply Kerr16; [| exact FS2 | exact FRM2]. unfold ts2, pbs2 in INV2. exact INV2. }

step. if_falsex.
pose proof (TSK depth l Hl) as Ld. cbn [hl_segs S4L pf_mxd] in Ld. unfold srec_cells in Ld.
remember (q + 32 * Z.of_nat depth) as bse eqn:Hbse in Ld.
assert (HbseR : q <= bse /\ bse + 32 <= q + (32 * mxd)) by (subst bse; lia).
pose proof (munch_refl [(bse, bse + 32)] m2) as MU. pose proof (wmono_refl rsegs m2) as WM.
pose proof INV2 as [CORE2 _]. pose proof CORE2 as (_ & _ & _ & _ & _ & PB2 & _).
stash PB2. stash REST2. stash TSK. clear CORE2 INV2.
step. norm_sx32. step.
step. rewrite (unsigned_lit (Z.of_nat depth)) by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32.
step. replace (q + Z.of_nat depth * 32) with bse by lia.
stepz. step. step. step.
unstash PB2. unstash REST2. unstash TSK.
set (l1 := TL ST_eatws (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)).
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
eapply lvl_cur_restate with (c' := c0); [exact (LV' depth l Hl) | exact Hmode | | unfold ST_eatws; lia | exact SS26 | left; reflexivity].
rewrite <- Hmode. apply lvl_mode_ws_same; [rewrite Hst; reflexivity | reflexivity].
* rewrite nth_error_lupd_neq in Hli by congruence. exact (LV' i li Hli).
+ revert OBJ'. unfold cur_st, ts0, ts2. cbn [t_levels t_depth t_objs t_objbs t_obj pf_mxd]. rewrite nth_error_lupd_eq by lia. cbn [tl_st pf_mxd].
rewrite Hl, Hst. cbn. intros OBJ'; exact OBJ'.
Qed.

#[using="MEMMOVE"] Lemma ceol_latch :
forall (n : nat) (pf : pe_fix) (q : Z) (LB0 : list blk) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (ts : tstate) (l : tlevel) (co0 : Z)
(cb : byte) (j1 j2 utf : list byte) (sv : pe_saved) (errv : word) (T : TSet)
(x1 gp t0 t1 t2 a4 a5 a6 a7 s4 s6 t3 t4 t5 t6 : word) (anb : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC HIx pf lo ->
PE_INV HIx pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv ->
CSTR_OK pf payload ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_comment_eol ->
0 <= co0 <= t_co ts -> t_co ts < pf_len pf -> nth_error payload (Z.to_nat (t_co ts)) = Some cb -> bv_unsigned cb <> 10 ->
(pf_len pf - t_co ts <= Z.of_nat n) ->

(forall m' co' cb' (j2' : list byte) a0' a1' a2' a3' a4',
t_co ts < co' < pf_len pf -> nth_error payload (Z.to_nat co') = Some cb' -> bv_unsigned cb' = 10 ->
PE_INV HIx pf q LB0 payload me lo m' md A (ts_set_co ts co') cb' j1 j2' utf sv errv ->
realizes rsegs (mkCfg (pe_ms rsegs pf 0x226d8 co0 x1 gp t0 t1 t2 a0' a1' a2' a3' a4' a5 a6 a7 s4 (Z_to_bv 64 (pf_sb pf + co')) s6
(Z_to_bv 64 q) (Z_to_bv 64 (Z.of_nat (t_depth ts))) t3 t4 t5 t6 F fc m') md) T) ->

(forall m' md' A' pbs' (e : word) co' cb' errv' (j2' : list byte) x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s8' s10' t3' t4' t5' t6' F' fc',
t_co ts < co' <= pf_len pf ->
PE_INV HIx pf q LB0 payload me lo m' md' A'
(TST (t_depth ts) (t_levels ts) co' (t_pb ts) pbs'
(TS (ts_isd (t_x ts)) (ts_stpos (t_x ts)) (Z_to_bv 64 co') e (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))
(t_obj ts) (t_objs ts) (t_objbs ts)) cb' j1 j2' utf sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_OUT co0 x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s8' s10' t3' t4' t5' t6' F' fc' m') md') T) ->

(forall m' md' A' pbs' (e : word) co' cb' errv' (j2' : list byte) x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s8' s10' t3' t4' t5' t6' F' fc',
t_co ts < co' <= pf_len pf ->
PE_INV HIx pf q LB0 payload me lo m' md' A'
(TST (t_depth ts) (t_levels ts) co' (t_pb ts) pbs'
(TS (ts_isd (t_x ts)) (ts_stpos (t_x ts)) (Z_to_bv 64 co') e (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))
(t_obj ts) (t_objs ts) (t_objbs ts)) cb' j1 j2' utf sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_ERR co0 x1' gp' t0' t1' t2' (Z_to_bv 64 16) a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s8' s10' t3' t4' t5' t6' F' fc' m') md') T) ->
realizes rsegs (mkCfg (pe_ms rsegs pf 0x22a60 co0 x1 gp t0 t1 t2
(Z_to_bv 64 (t_co ts + 1)) anb  (Z_to_bv 64 (t_co ts + 1 - co0)) (Z_to_bv 64 (bv_unsigned cb)) a4 a5 a6 a7
s4 (Z_to_bv 64 (pf_sb pf + t_co ts)) s6 (Z_to_bv 64 q) (Z_to_bv 64 (Z.of_nat (t_depth ts))) t3 t4 t5 t6 F fc m) md) T.
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
apply rz_evt; [exact MOK|].

step.

step.
destruct (Z.eq_dec (bv_unsigned cb) 0) as [E0 | N0].
{ if_truex. unstash PB. unstash REST. unstash TSK. apply evt_RZ_done.
lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mc _) _) _ =>
eapply (cmt_flush HIx MEMMOVE (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo mc md A
(TST depth levels (co + 1) pb pbs (TS isd stpos (Z_to_bv 64 (co + 1)) err ucs high quote) obj objs objbs) co0 cb);
[ exact STC | eapply MKINV; [lia | exact TOK | exact FR | exact MU | exact WM | exact MI] | cbn; lia | cbn; lia
| unfold ts_set_pbs; cbn [t_levels t_depth t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd]; intros; eapply Kout; [| eassumption..]; lia
| unfold ts_set_pbs; cbn [t_levels t_depth t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd]; intros; eapply Kerr16; [| eassumption..]; lia ]
end. }
if_falsex.

step.
destruct (peek_cases (PEF tk oldl newl len lenr sb spf pmd mxd fl) payload co cb LENR CSTR (proj1 RR) ltac:(cbn [pf_len pf_mxd]; lia) ltac:(cbn [pf_len pf_mxd]; lia) Hc N0)
as [[Elenr Heof] | [Hne Hmore]]; [cbn [pf_len pf_lenr pf_mxd] in Elenr, Heof; subst lenr; pose (lenr := len) | cbn [pf_len pf_lenr pf_mxd] in Hne, Hmore].
{ if_truex. unstash PB. unstash REST. unstash TSK. apply evt_RZ_done.
replace (Z_to_bv 64 (co + 1 - co0)) with (Z_to_bv 64 (len - co0)) by (f_equal; lia).
lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mc _) _) _ =>
eapply (ceol_eof (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo mc md A
(TST depth levels (co + 1) pb pbs (TS isd stpos (Z_to_bv 64 (co + 1)) err ucs high quote) obj objs objbs) co0 cb);
[ exact STC | eapply MKINV; [lia | exact TOK | exact FR | exact MU | exact WM | exact MI] | cbn; lia | cbn; lia
| unfold ts_set_pbs, ts_set_err; cbn [t_levels t_depth t_co t_pb t_pbs t_x t_obj t_objs t_objbs ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd]; intros; eapply Kout; [| eassumption..]; lia
| unfold ts_set_pbs, ts_set_err; cbn [t_levels t_depth t_co t_pb t_pbs t_x t_obj t_objs t_objbs ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd]; intros; eapply Kerr16; [| eassumption..]; lia ]
end. }
if_falsex.
destruct (nth_error payload (Z.to_nat (co + 1))) as [c'|] eqn:Hc'; [| apply nth_error_None in Hc'; lia].
pose proof (bv_unsigned_in_range 8 c') as CBR'; unfold bv_modulus in CBR'; cbn in CBR'.

assert (JOINF0 : forall mf (nv a1x a4x : word),
rw_cells rsegs mf tk
[C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 pb); C4 (Z_to_bv 64 mxd); C4 (Z_to_bv 64 (Z.of_nat depth)); C4 isd; C4 stpos;
C4 (Z_to_bv 64 (co + 1)); C4 err; C4 ucs; C4 high; C1 quote; CB 7 (repeat (Z_to_bv 8 0) 7); C8 (Z_to_bv 64 q); C4 (Z_to_bv 64 fl); C4 (Z_to_bv 64 0)] ->
rw_cells rsegs mf spf [C8 (Z_to_bv 64 obj); CB 16 j1; C4 nv; CB 3 (skipn 4 j2); C1 cb; CB 8 utf;
C8 (pe_s11 sv); C8 (pe_s10 sv); C8 (pe_s9 sv); C8 (pe_s8 sv); C8 (pe_s7 sv); C8 (pe_s6 sv);
C8 (pe_s5 sv); C8 (pe_s4 sv); C8 (pe_s3 sv); C8 (pe_s2 sv); C8 (pe_s1 sv); C8 (pe_s0 sv); C8 (pe_ra sv)] ->
munch [(tk, tk + 72); (spf, spf + 144)] m mf -> wmono rsegs m mf -> mem_inv rsegs mf ->
evt rsegs (RZ rsegs md T)
(MS (mkR x1 (Z_to_bv 64 spf) gp (Z_to_bv 64 482928) t0 t1 t2 (Z_to_bv 64 tk) (Z_to_bv 64 oldl)
(Z_to_bv 64 (co + 1)) a1x (Z_to_bv 64 (co + 1 - co0)) (Z_to_bv 64 (bv_unsigned c')) a4x a5 a6 a7
(Z_to_bv 64 newl) (Z_to_bv 64 lenr) s4 (Z_to_bv 64 (sb + co + 1)) s6 (Z_to_bv 64 26) (Z_to_bv 64 q) (Z_to_bv 64 (sb + co0)) (Z_to_bv 64 (Z.of_nat depth)) (Z_to_bv 64 79024) t3 t4 t5 t6)
F (Z_to_bv 64 0x22a4c) fc None mf (seg_rom rsegs))).
{ intros mf nv a1x a4x TOKf FRf MUf WMf MIf.
repeat match goal with H : rw_cells rsegs ?mx _ _ |- _ => lazymatch mx with mf => fail | m => fail | _ => clear H end end.
repeat match goal with H : munch _ m ?mx |- _ => lazymatch mx with mf => fail | _ => clear H end end.
repeat match goal with H : wmono rsegs m ?mx |- _ => lazymatch mx with mf => fail | m => fail | _ => clear H end end.
repeat match goal with H : mem_inv rsegs ?mx |- _ => lazymatch mx with mf => fail | m => fail | _ => clear H end end.
try clear MU; try clear WM; try clear MI. rename MUf into MU. rename WMf into WM. rename MIf into MI. rename TOKf into TOK. rename FRf into FR.

step. rewrite le1_zxw. mem_after_store.
step. norm_w32. step. step. norm_w32. step.
unstash PB. unstash REST. unstash TSK.
destruct (Z.eq_dec (bv_unsigned c') 10) as [E42 | N42'].
- if_truex. apply evt_RZ_done. replace (sb + co + 1) with (sb + (co + 1)) by lia.
lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mc _) _) _ =>
eapply (Kstar mc (co + 1) c'); [lia | exact Hc' | exact E42 | eapply MKINV; [lia | exact TOK | exact FR | exact MU | exact WM | exact MI]]
end.
- if_falsex. apply evt_RZ_done.
replace (sb + co + 1) with (sb + (co + 1)) by lia. replace (co + 1 - co0 + 1) with (co + 1 + 1 - co0) by lia.
replace (Z_to_bv 64 (co + 2)) with (Z_to_bv 64 (co + 1 + 1)) by (f_equal; lia).
lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mc _) _) _ =>
eapply (IH (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo mc md A
(TST depth levels (co + 1) pb pbs (TS isd stpos (Z_to_bv 64 (co + 1)) err ucs high quote) obj objs objbs) l co0 c');
[ exact STC | eapply MKINV; [lia | exact TOK | exact FR | exact MU | exact WM | exact MI] | exact CSTR | exact Hl | exact Hst | cbn; lia | cbn; lia | exact Hc' | exact N42' | cbn; lia
| cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_sb pf_len pf_md pf_mxd pf_fl];
intros; eapply Kstar; [cbn in *; lia | eassumption | assumption | eassumption]
| cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_sb pf_len pf_md pf_mxd pf_fl];
intros; eapply Kout; [| eassumption..]; cbn in *; lia
| cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_sb pf_len pf_md pf_mxd pf_fl];
intros; eapply Kerr16; [| eassumption..]; cbn in *; lia ]
end. }

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
assert (STR1 : bytes_at rsegs m1 sb payload)
by (unstash REST; eapply (PE_REST_private_write HIx) with (ts := ts0) in REST;
[exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 REST)))))) | exact STC | exact MU | exact WM | exact MI | apply pe_wtf_private; exact HW]);
pose proof (tok_flags_byte_g mxd fl m1 tk pb (Z.of_nat depth) q (TS isd stpos (Z_to_bv 64 (co + 1)) err ucs high quote) TOK) as RDF
end.
pose proof (payload_byte _ _ _ _ _ STR1 Hc' ltac:(lia)) as RDC. replace (sb + (co + 1)) with (sb + co + 1) in RDC by lia.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
assert (JOINS : forall (a1x a3x a4x : word),
evt rsegs (RZ rsegs md T)
(MS (mkR x1 (Z_to_bv 64 spf) gp (Z_to_bv 64 482928) t0 t1 t2 (Z_to_bv 64 tk) (Z_to_bv 64 oldl)
(Z_to_bv 64 (co + 1)) a1x (Z_to_bv 64 (co + 1 - co0)) a3x a4x a5 a6 a7
(Z_to_bv 64 newl) (Z_to_bv 64 lenr) s4 (Z_to_bv 64 (sb + co + 1)) s6 (Z_to_bv 64 26) (Z_to_bv 64 q) (Z_to_bv 64 (sb + co0)) (Z_to_bv 64 (Z.of_nat depth)) (Z_to_bv 64 79024) t3 t4 t5 t6)
F (Z_to_bv 64 0x22a98) fc None m1 (seg_rom rsegs)))
end.
{ intros a1x a3x a4x. clear RDF RDC STR1.
step. try mem_after_store.
lazymatch goal with H : munch _ m ?mf |- evt _ _ (MS _ _ _ _ _ ?mf _) =>
rename H into MU2;
lazymatch goal with W : wmono rsegs m mf |- _ => rename W into WM2 end;
lazymatch goal with I : mem_inv rsegs mf |- _ => rename I into MI2 end
end.
assert (STR2 : bytes_at rsegs _ sb payload)
by (unstash REST; eapply (PE_REST_private_write HIx) with (ts := ts0) in REST;
[exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 REST)))))) | exact STC | exact MU2 | exact WM2 | exact MI2 | apply pe_wtf_private; exact HW]).
pose proof (payload_byte _ _ _ _ _ STR2 Hc' ltac:(lia)) as RDC2. replace (sb + (co + 1)) with (sb + co + 1) in RDC2 by lia.
step. change (zxb c') with (Z_to_bv 64 (bv_unsigned c')). step.
eapply JOINF0; [exact TOK | eassumption | eassumption | eassumption | assumption]. }

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
assert (ERR14 : forall (a0x a1x a3x a4x : word),
evt rsegs (RZ rsegs md T)
(MS (mkR x1 (Z_to_bv 64 spf) gp (Z_to_bv 64 482928) t0 t1 t2 (Z_to_bv 64 tk) (Z_to_bv 64 oldl)
a0x a1x (Z_to_bv 64 (co + 1 - co0)) a3x a4x a5 a6 a7
(Z_to_bv 64 newl) (Z_to_bv 64 lenr) s4 (Z_to_bv 64 (sb + co + 1)) s6 (Z_to_bv 64 26) (Z_to_bv 64 q) (Z_to_bv 64 (sb + co0)) (Z_to_bv 64 (Z.of_nat depth)) (Z_to_bv 64 79024) t3 t4 t5 t6)
F (Z_to_bv 64 0x2320c) fc None m1 (seg_rom rsegs)))
end.
{ intros a0x a1x a3x a4x. clear RDF RDC STR1.
step. stepz. unstash PB. unstash REST. unstash TSK. apply evt_RZ_done.
lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mc _) _) _ =>
lazymatch goal with TOK3 : rw_cells rsegs mc tk [_; _; _; _; _; _; _; C4 ?e3; _; _; _; _; _; _; _] |- _ =>
eapply (cmt_flush HIx MEMMOVE (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo mc md A
(TST depth levels (co + 1) pb pbs (TS isd stpos (Z_to_bv 64 (co + 1)) e3 ucs high quote) obj objs objbs) co0 cb);
[ exact STC | eapply MKINV; [lia | exact TOK3 | eassumption | eassumption | eassumption | assumption] | cbn; lia | cbn; lia
| unfold ts_set_pbs; cbn [t_levels t_depth t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd]; intros; eapply Kout; [| eassumption..]; lia
| unfold ts_set_pbs; cbn [t_levels t_depth t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd]; intros; eapply Kerr16; [| eassumption..]; lia ]
end end. }

step. rewrite (zxb_byte fl).
step. step. change (zxb c') with (Z_to_bv 64 (bv_unsigned c')).
step. rewrite (unsigned_lit (fl mod 256)) by (pose proof (Z.mod_pos_bound fl 256 ltac:(lia)); lia). rewrite (land_mod256 fl 16) by lia.
destruct (land16_cases fl) as [F16 | F16]; rewrite F16.
+  step. if_true. eapply JOINF0; [exact TOK | exact FR | exact MU | exact WM | exact MI].
+
step. if_false.
Local Ltac if_any := lazymatch goal with |- evt _ _ (MS _ _ (if ?cnd then _ else _) _ _ _ _) => destruct cnd; cbv iota end.
step. if_any.
*
step. step. if_any.
--
step. step. step. if_any.
++  step. step. step. if_any.
**  step. step. step. if_any.
---  apply ERR14.
--- step. step. apply JOINS.
** step. step. apply JOINS.
++ step. step. apply JOINS.
--
step. eapply JOINF0; [exact TOK | exact FR | exact MU | exact WM | exact MI].
*
step. step. step. step. if_any.
--  apply ERR14.
-- step. apply JOINS.
Qed.

#[using="MEMMOVE"] Lemma seg_ceol :
forall (pf : pe_fix) (q : Z) (LB0 : list blk) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (ts : tstate) (l : tlevel)
(cb : byte) (j1 j2 utf : list byte) (sv : pe_saved) (errv : word) (T : TSet)
(x1 gp t0 t1 t2 a3 a4 a5 a6 a7 s4 s5 s6 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC HIx pf lo ->
PE_INV HIx pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv ->
CSTR_OK pf payload ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_comment_eol ->
t_co ts < pf_len pf -> nth_error payload (Z.to_nat (t_co ts)) = Some cb ->

(forall m' md' A' pbs' errv' co' cb' (j2' : list byte) x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s8' s10' t3' t4' t5' t6' F' fc',
t_co ts <= co' < pf_len pf -> nth_error payload (Z.to_nat co') = Some cb' -> bv_unsigned cb' = 10 ->
PE_INV HIx pf q LB0 payload me lo m' md' A'
(TST (t_depth ts) (lupd (t_levels ts) (t_depth ts) (TL ST_eatws (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)))
co' (t_pb ts) pbs'
(TS (ts_isd (t_x ts)) (ts_stpos (t_x ts)) (Z_to_bv 64 co') (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))
(t_obj ts) (t_objs ts) (t_objbs ts)) cb' j1 j2' utf sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_BREAK co' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s8' s10' t3' t4' t5' t6' F' fc' m') md') T) ->

(forall m' md' A' pbs' (e : word) co' cb' errv' (j2' : list byte) x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s8' s10' t3' t4' t5' t6' F' fc',
t_co ts < co' <= pf_len pf ->
PE_INV HIx pf q LB0 payload me lo m' md' A'
(TST (t_depth ts) (t_levels ts) co' (t_pb ts) pbs'
(TS (ts_isd (t_x ts)) (ts_stpos (t_x ts)) (Z_to_bv 64 co') e (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))
(t_obj ts) (t_objs ts) (t_objbs ts)) cb' j1 j2' utf sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_OUT (t_co ts) x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s8' s10' t3' t4' t5' t6' F' fc' m') md') T) ->

(forall m' md' A' pbs' (e : word) co' cb' errv' (j2' : list byte) x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s8' s10' t3' t4' t5' t6' F' fc',
t_co ts <= co' <= pf_len pf ->
PE_INV HIx pf q LB0 payload me lo m' md' A'
(TST (t_depth ts) (t_levels ts) co' (t_pb ts) pbs'
(TS (ts_isd (t_x ts)) (ts_stpos (t_x ts)) (Z_to_bv 64 co') e (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))
(t_obj ts) (t_objs ts) (t_objbs ts)) cb' j1 j2' utf sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_ERR (t_co ts) x1' gp' t0' t1' t2' (Z_to_bv 64 16) a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s8' s10' t3' t4' t5' t6' F' fc' m') md') T) ->
realizes rsegs (mkCfg (pe_ms rsegs pf (pe_jt ST_comment_eol) (t_co ts) x1 gp t0 t1 t2
(Z_to_bv 64 (32 * Z.of_nat (t_depth ts))) (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) (Z_to_bv 64 (tl_st l)) a3 a4 a5 a6 a7
s4 s5 s6 (Z_to_bv 64 q) (Z_to_bv 64 (Z.of_nat (t_depth ts))) t3 t4 t5 t6 F fc m) md) T.
Proof.
intros until fc. intros STC INV CSTR Hl Hst Hco Hc Kbreak Kout Kerr16.
pose proof INV as [CORE REST].
pose proof CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof (heap_model_ok _ _ _ _ _ _ (proj1 REST)) as MOK.
pose proof (bv_unsigned_in_range 8 cb) as CBR; unfold bv_modulus in CBR; cbn in CBR.
pose proof STC as (LO & LOS & SPA & HT & SP0 & LEN & SB0 & (SBL & RR & LENR)).
revert INV Kbreak Kout Kerr16.
destruct ts as [depth levels co pb pbs xx obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct xx as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl_]; pe_gen fl_; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
intros INV Kbreak Kout Kerr16.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in TOK.
unfold pe_frame in FR. unfold pe_ms. cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl]. unfold_consts.
clear PB TSK REST CORE.
apply rz_evt; [exact MOK|].
step. change (zxb cb) with (Z_to_bv 64 (bv_unsigned cb)). step. step. step.
destruct (Z.eq_dec (bv_unsigned cb) 10) as [E42 | N42].
- if_falsex. apply evt_RZ_done.
eapply (ceol_nl (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo m md A
(TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) l co cb);
[ exact STC | exact INV | exact Hl | exact Hst | cbn; lia | exact Hco
| unfold ts_set_pbs, ts_set_level; cbn [t_levels t_depth t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd]; intros; eapply Kbreak; [| exact Hc | exact E42 | eassumption..]; lia
| unfold ts_set_pbs; cbn [t_levels t_depth t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd]; intros; eapply Kerr16; [| eassumption..]; lia ].
- if_truex. step. norm_sx32. step. norm_sx32. step. norm_w32. step. step. step.
apply evt_RZ_done. replace (Z_to_bv 64 1) with (Z_to_bv 64 (co + 1 - co)) by (f_equal; lia).
eapply (ceol_latch (Z.to_nat (len - co)) (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo m md A
(TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) l co cb);
[ exact STC | exact INV | exact CSTR | exact Hl | exact Hst | cbn; lia | exact Hco | exact Hc | exact N42 | cbn; lia | | | ].
+ unfold ts_set_co; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_sb pf_len pf_md pf_mxd pf_fl].
intros m' co' cb' j2' a0' a1' a2' a3' a4' R' Hc' E42 INV'.
eapply (ceol_nl (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo m' md A
(TST depth levels co' pb pbs (TS isd stpos (Z_to_bv 64 co') err ucs high quote) obj objs objbs) l co cb');
[ exact STC | exact INV' | exact Hl | exact Hst | cbn; lia | cbn; lia
| unfold ts_set_pbs, ts_set_level; cbn [t_levels t_depth t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd]; intros; eapply Kbreak; [| exact Hc' | exact E42 | eassumption..]; lia
| unfold ts_set_pbs; cbn [t_levels t_depth t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd]; intros; eapply Kerr16; [| eassumption..]; lia ].
+ cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_sb pf_len pf_md pf_mxd pf_fl].
intros. eapply Kout; eassumption.
+ cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_sb pf_len pf_md pf_mxd pf_fl].
intros. eapply Kerr16; [| eassumption..]. lia.
Qed.
End PeCeol.

End RC__1.
