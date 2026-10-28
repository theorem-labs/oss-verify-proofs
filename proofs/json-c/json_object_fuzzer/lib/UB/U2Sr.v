(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)

From Stdlib Require ZArith List Lia Bool Sorting.Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup Lib.GwApply QWxq QRjH QHnV QCcH QfLs Q0Ek Qtgi QjDH Qsw7 QJjn QRUw QkMG QgoP Q6q3.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM UC8c UG8z Udyh UIsM Ua8x UXfU UPZI UBpZ UT7i Uv6q UzWc UfOM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB.Tk2 Require Tk2Gen.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup.
Import UEQM.
Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0.
Import UC8c.Mq0.
Import Qsw7 QJjn QRUw.Mq2 QkMG.
Import UG8z Udyh.Mq0 UIsM.Mq2 Udyh.Mq2 Ua8x UXfU.Mq4.
Import QJjn.Mq0.
Import UPZI.Mq3.
Import UBpZ UT7i Uv6q.
Import UzWc.
Import QgoP.
Import UfOM.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.
Import Q6q3.
Import Tk2Gen.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma ofield_mode : forall ss c hn, 0 <= ss <= 26 -> lvl_mode ST_ofield ss = Some (c, hn) -> c = CObj /\ hn = false.
Proof.
intros ss c hn R Hm. enum_z R ss; vm_compute in Hm; first [discriminate Hm | injection Hm as <- <-; split; reflexivity].
Qed.

#[using="Type"] Lemma first_nul_split : forall (pre post : list byte),
exists str rest, pre ++ [Z_to_bv 8 0] ++ post = str ++ b0 :: rest /\ ~ In b0 str /\ (length str <= length pre)%nat.
Proof.
induction pre as [|b pre IH]; intros post.
- exists [], post. split; [reflexivity|]. split; [intros H; exact H | cbn; lia].
- destruct (Z.eq_dec (bv_unsigned b) 0) as [E|NE].
+ exists [], (pre ++ [Z_to_bv 8 0] ++ post). split; [| split; [intros H; exact H | cbn; lia]].
change ((b :: pre) ++ [Z_to_bv 8 0] ++ post) with (b :: (pre ++ [Z_to_bv 8 0] ++ post)). cbn [app pf_mxd]. f_equal. apply bv_eq. rewrite E. reflexivity.
+ destruct (IH post) as (str & rest & E & Hn & Hl). exists (b :: str), rest.
split; [change ((b :: pre) ++ [Z_to_bv 8 0] ++ post) with (b :: (pre ++ [Z_to_bv 8 0] ++ post)); rewrite E; reflexivity|].
split; [| cbn; lia]. intros [H|H]; [| exact (Hn H)]. apply NE. rewrite H. reflexivity.
Qed.

#[using="Type"] Lemma firstn_len_succ : forall {X} (s : list X) (b : X) (r : list X), firstn (length s + 1) (s ++ b :: r) = s ++ [b].
Proof. intros X s b r. rewrite firstn_app, firstn_all2, Nat.add_comm, Nat.add_sub by lia. reflexivity. Qed.

#[using="Type"] Lemma nonul_forall : forall s : list byte, ~ In b0 s -> Forall (fun b => bv_unsigned b <> 0) s.
Proof.
induction s as [|b s IH]; intros H; [constructor|]. constructor.
- intros E. apply H. left. apply bv_eq. rewrite E. reflexivity.
- apply IH. intros Hin. apply H. right. exact Hin.
Qed.

Section PeOfield.
Variable HIx : heap_iface S4L.
Hypothesis MEMMOVE : memmove_stmt.
Hypothesis STRDUP : strdup_stmt HIx.

#[using="MEMMOVE"] Lemma of_bs :
forall (pf : pe_fix) (q : Z) (LB0 : list blk) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (ts : tstate) (l : tlevel) (co0 : Z)
(cb : byte) (j1 j2 utf : list byte) (sv : pe_saved) (errv : word) (T : TSet)
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC HIx pf lo ->
PE_INV HIx pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_ofield ->
0 <= co0 <= t_co ts -> t_co ts < pf_len pf ->
(forall m' md' A' pbs' errv' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F' fc',
PE_INV HIx pf q LB0 payload me lo m' md' A'
(ts_set_pbs (ts_set_level ts (TL ST_string_escape ST_ofield (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) pbs') cb j1 j2 utf sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_BREAK (t_co ts) x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F' fc' m') md') T) ->
(forall m' md' A' pbs' errv' x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F' fc',
PE_INV HIx pf q LB0 payload me lo m' md' A' (ts_set_pbs ts pbs') cb j1 j2 utf sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_ERR co0 x1' gp' t0' t1' t2' (Z_to_bv 64 16) a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F' fc' m') md') T) ->
realizes rsegs (mkCfg (pe_ms rsegs pf 0x23948 co0 x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (pf_sb pf + t_co ts)) (Z_to_bv 64 (t_co ts - co0)) s7 s8 s9 s10 t3 t4 t5 t6 F fc m) md) T.
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
bst. bst. bst. bst.
apply evt_RZ_done.
eapply (memappend_cps HIx MEMMOVE) with (lo := lo) (b := sb + co0) (n := n);
[ exact HP1 | exact PBC | (clear - Hco0 Hco LEN; lia) | exact SRC | exact SRCL
| left; eapply (payload_crange (PEF _ _ _ _ _ _ _ _ _ _)); [exact SBin | intros bb Hbb; apply in_or_app; right; right; right; exact Hbb | cbn [pf_spf pf_mxd]; rewrite ?unsigned_lit by (clear - SP0; lia); unfold PE_FRAME; (clear; lia) | (clear - Hco0; lia) | (clear - SRCL; lia) | cbn [pf_len pf_mxd]; (clear - CO; lia)] | (clear - Hco0 SB0; lia) | (clear - CO SBL; lia) | (clear - Hco0 Hco Hdsb; lia) | .. ]; try alloc_side.
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
bst. if_true. bst. bst. apply evt_RZ_done. eapply Kerr16; [| exact FS2 | exact FRM2]. unfold ts2, pbs2 in INV2. exact INV2. }

bst. if_falsex.
pose proof (TSK depth l Hl) as Ld. unfold srec_cells in Ld. cbn [hl_segs S4L pf_mxd] in Ld.
remember (q + 32 * Z.of_nat depth) as bse eqn:Hbse in Ld.
assert (HbseR : q <= bse /\ bse + 32 <= q + (32 * mxd)) by (subst bse; lia).
assert (Hbal : bse mod 16 = 0) by (subst bse; clear - Hqal; Z.div_mod_to_equations; lia).
pose proof (munch_refl [(bse, bse + 32)] m2) as MU. pose proof (wmono_refl rsegs m2) as WM.
pose proof INV2 as [CORE2 _]. pose proof CORE2 as (_ & _ & _ & _ & _ & PB2 & _).
stash PB2. stash REST2. stash TSK. clear CORE2 INV2.
bst. norm_sx32. bst.
rewrite (unsigned_lit (Z.of_nat depth)) by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32.
bst. replace (q + Z.of_nat depth * 32) with bse by lia.
bst_to 0x23d14.
unstash PB2. unstash REST2. unstash TSK.
set (l1 := TL ST_string_escape ST_ofield (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)).
assert (HW : Forall (pe_wtq (PEF tk oldl newl len lenr sb spf pmd mxd fl) q) [(bse, bse + 32)]) by (apply Forall_cons; [right; cbn [fst snd pf_mxd]; lia | apply Forall_nil]).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
match goal with L8 : rw_cells rsegs mc bse (?c1 :: ?c2 :: _) |- _ =>
pose proof (rw_cells_recast_prefix rsegs mc bse [c1; c2] [C4 (Z_to_bv 64 ST_string_escape); C4 (Z_to_bv 64 ST_ofield)]
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
rewrite Hst in Hmode. destruct (ofield_mode _ _ _ SS26 Hmode) as [-> ->].
eapply lvl_cur_restate with (c' := CObj); [exact (LV' depth l Hl) | rewrite Hst; exact Hmode | reflexivity | unfold ST_string_escape; lia | unfold ST_ofield; lia | left; reflexivity].
* rewrite nth_error_lupd_neq in Hli by congruence. exact (LV' i li Hli).
+ revert OBJ'. unfold cur_st, ts0, ts2. cbn [t_levels t_depth t_objs t_objbs t_obj pf_mxd]. rewrite nth_error_lupd_eq by lia. cbn [tl_st pf_mxd].
rewrite Hl, Hst. cbn. intros OBJ'; exact OBJ'.
Qed.

#[using="STRDUP"] Lemma ofq_new :
forall (pf : pe_fix) (q : Z) (LB0 : list blk) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (ts : tstate) (l : tlevel) (co0 : Z)
(cb : byte) (j1 j2 utf : list byte) (sv : pe_saved) (errv : word) (T : TSet)
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC HIx pf lo ->
PE_INV HIx pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_ofield ->

(forall m' md' A' r nbs' errv' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F' fc',
r <> 0 ->
PE_INV HIx pf q LB0 payload me lo m' md' A'
(TST (t_depth ts) (lupd (t_levels ts) (t_depth ts) (TL ST_eatws ST_ofend (tl_cur l) (tl_cs l) (tl_cbs l) r nbs'))
(t_co ts) (t_pb ts) (t_pbs ts) (t_x ts) (t_obj ts) (t_objs ts) (t_objbs ts))
cb j1 j2 utf sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_BREAK (t_co ts) x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F' fc' m') md') T) ->

(forall m' md' A' errv' x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F' fc',
PE_INV HIx pf q LB0 payload me lo m' md' A' ts cb j1 j2 utf sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_ERR co0 x1' gp' t0' t1' t2' (Z_to_bv 64 16) a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F' fc' m') md') T) ->
realizes rsegs (mkCfg (pe_ms rsegs pf 0x23184 co0 x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (pf_sb pf + t_co ts)) s6 s7 s8 s9 s10 t3 t4 t5 t6 F fc m) md) T.
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
assert (Eobjbs : objbs = []).
{ revert OBJ. unfold cur_st. cbn [t_levels t_depth t_objbs pf_mxd]. rewrite Hl, Hst. cbn. intros E; exact E. }
subst objbs.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs []) in *.
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
rewrite Hst in Hmode. destruct (ofield_mode _ _ _ SS26 Hmode) as [-> ->].
cbn [name_ok pf_mxd] in NM0. destruct NM0 as [Hn0 Hnbs0].
set (cur := tl_cur l) in *. set (cbs := tl_cbs l) in *. set (cs := tl_cs l) in *.
assert (Ecur0 : tl_cur l = cur) by reflexivity. assert (Ecbs0 : tl_cbs l = cbs) by reflexivity. assert (Ecs0 : tl_cs l = cs) by reflexivity. clearbody cur cbs cs.
assert (LBl : lvl_blocks l = cbs) by (unfold lvl_blocks; rewrite Ecbs0, Hnbs0, app_nil_r; reflexivity).

set (BL := concat (map lvl_blocks levels)).
assert (ALLf : forall a k, In (a, k) (pbs ++ BL) -> In (a, k) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0) /\ a <> tk /\ a <> q).
{ intros a k Hin.
assert (HinT : In (a, k) (tstate_blocks ts0)) by (unfold tstate_blocks, ts0; cbn [t_pbs t_objbs t_levels app pf_mxd]; apply in_app_or in Hin; destruct Hin as [Hin|Hin]; apply in_or_app; [left; exact Hin | right; exact Hin]).
assert (HinL : In (a, k) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocks; apply in_or_app; left; exact HinT).
split; [exact HinL|]. generalize ND; intros ND'. unfold pe_blocks in ND'. cbn [pf_tk pf_md pf_mxd pf_fl] in ND'. split.
- eapply (nodup_app_ne _ _ _ _ _ _ ND' HinT). left; reflexivity.
- eapply (nodup_app_ne _ _ _ _ _ _ ND' HinT). right; left; reflexivity. }
assert (CBSin : incl cbs BL).
{ intros b Hb. unfold BL. apply in_concat. exists (lvl_blocks l). split; [apply in_map; eapply nth_error_In; exact Hl | rewrite LBl; exact Hb]. }
remember (q + 32 * Z.of_nat depth) as bse eqn:Hbse.
assert (HbseR : q <= bse /\ bse + 32 <= q + (32 * mxd)) by (subst bse; lia).
assert (Hbal : bse mod 16 = 0) by (subst bse; clear - Hqal; Z.div_mod_to_equations; lia).

pose proof PB as (buf & bpos & cap & pre & post & Epbs & Lpre & PBC). pose proof PBC as (Hbpos & Hcap & Hclen & PBS & PBUF). cbn [hl_segs S4L pf_mxd] in PBS, PBUF.
assert (INbuf : In (buf, cap) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocks, tstate_blocks, ts0; cbn [t_pbs pf_mxd]; rewrite Epbs; apply in_or_app; left; apply in_or_app; left; right; left; reflexivity).
pose proof (heap_blk S4L HIx _ _ _ _ buf cap HP INbuf) as (_ & Hbufal & Hbuflo & Hbufhi & _). unfold alloc_ceiling, sp_window_lo, stack_max_size in Hbufhi.
assert (Htkpb : tk <> pb).
{ generalize ND; intros ND'. unfold pe_blocks, tstate_blocks, ts0 in ND'. cbn [t_pbs pf_tk pf_md pf_mxd pf_fl] in ND'. rewrite Epbs in ND'.
intros E. assert (ND2 : List.NoDup (map blk_addr (([(pb, 16); (buf, cap)] ++ [] ++ concat (map lvl_blocks levels)) ++ (tk, 72) :: (q, (32 * mxd)) :: LB0))) by exact ND'.
rewrite map_app in ND2. eapply (NoDup_app_in2 _ _ tk ND2); [rewrite E; cbn; left; reflexivity | cbn; left; reflexivity]. }
assert (INpb : In (pb, 16) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocks, tstate_blocks, ts0; cbn [t_pbs pf_mxd]; rewrite Epbs; apply in_or_app; left; apply in_or_app; left; left; reflexivity).
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ tk 72 pb 16 HP INtk INpb Htkpb) as Hdtkpb.
pose proof (heap_blk S4L HIx _ _ _ _ pb 16 HP INpb) as (_ & Hpbal & Hpblo & Hpbhi & _). unfold alloc_ceiling, sp_window_lo, stack_max_size in Hpbhi.
destruct (first_nul_split pre post) as (str & rest & Esplit & NONUL & Hstrlen).
pose proof Hclen as Hclen'. rewrite Esplit, length_app in Hclen'. cbn [length pf_mxd] in Hclen'.
assert (SIB : str_in_block S4L m buf cap (pre ++ [Z_to_bv 8 0] ++ post) buf str).
{ split; [exact PBUF|]. split; [lia|]. split; [lia|]. split; [| exact NONUL].
rewrite Z.sub_diag. cbn [Z.to_nat skipn pf_mxd]. rewrite Esplit. apply firstn_len_succ. }
destruct (str_slack S4L HIx _ _ _ _ buf cap _ buf str HP INbuf SIB) as [slack [SRC3 [PAD3 SLK3]]]. cbn [hl_segs S4L pf_mxd] in SRC3.
pose proof (bytes_at_bound _ _ _ _ SRC3) as Hbb3. rewrite length_app in Hbb3. cbn [length pf_mxd] in Hbb3.
pose proof BASE as (_ & ST0 & ERR0 & _).
stash TSK. stash BASE. stash LV. clear HP PB SIB.
apply rz_evt; [exact MOK|].
bst. bst. bst.
clear PBS PBUF.
apply evt_RZ_done.
eapply STRDUP with (LB := pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0) (lo := lo);
[ unstash BASE; exact (proj1 BASE) | rewrite unsigned_lit by (clear - Hbpos Hbuflo Hbufhi; lia); exact SRC3 | exact NONUL | rewrite unsigned_lit by (clear - Hbpos Hbuflo Hbufhi; lia); exact PAD3
| rewrite !unsigned_lit by (clear - SP0 Hbpos Hbuflo Hbufhi; lia); eapply client_range_block; [exact INbuf | (clear; lia) | (clear - Hclen'; lia)]
| rewrite !unsigned_lit by (clear - Hbpos Hbuflo Hbufhi SP0; lia); left; unfold PE_FRAME in *; (clear - LO LOS Hbufhi SLK3; lia) | (clear - Lpre Hbpos Hcap Hstrlen; lia) | .. ]; try alloc_side.
all: try (rewrite ?unsigned_lit by lia; first [exact ST0 | exact ERR0]).
all: try (rewrite ?unsigned_lit by lia; unfold PE_FRAME in *; clia).
intros ms2 md2 (mp & A2x & r & errv2 & RS2 & VM2 & ST2 & HPR2 & ERR2 & STR2 & OUT). open_ret RS2.
cbn [hl_segs hl_tp S4L pf_mxd] in *. rewrite ?(unsigned_lit spf) in ST2 by lia. rewrite ?(unsigned_lit spf) in HPR2 by lia.
unstash TSK. unstash BASE. unstash LV.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. cbn [hl_segs S4L pf_mxd] in FR.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in TOK; [| eapply client_range_block; [exact INtk | lia | cbn; lia]]. cbn [hl_segs S4L pf_mxd] in TOK.
apply (tstack_pres_g S4L _ _ _ _ _ _ HPR2 INq) in TSK; [| exact LEN32].
pose proof (srec_join8 _ _ _ (TSK depth l Hl)) as Ld. cbn [le4 Z_to_le_bytes app hl_segs S4L pf_mxd] in Ld. rewrite Ecur0, Hn0 in Ld.
rewrite <- Hbse in Ld. cbn [hl_segs S4L pf_mxd] in TSK.
assert (PB2 : pbuf rsegs mp pbs pb).
{ exists buf, bpos, cap, pre, post. split; [exact Epbs|]. split; [exact Lpre|].
eapply pbuf_core_agree; [exact PBC | | exact INpb | exact INbuf].
eapply (agree_of_heap_pres rsegs S4L); [exact HPR2 | reflexivity | intros b Hb; exact Hb]. }
assert (AGL2 : agree_on rsegs BL m mp).
{ eapply (agree_of_heap_pres rsegs S4L); [exact HPR2 | reflexivity |].
intros b Hb. unfold pe_blocks, tstate_blocks. apply in_or_app; left. apply in_or_app; right. exact Hb. }
assert (LV2 : forall i li, nth_error levels i = Some li -> i <> depth -> lvl_cur rsegs S4F mp depth i li).
{ intros i li Hli Hne. eapply (lvl_cur_agree rsegs S4F); [exact (LV i li Hli) | exact AGL2 |].
intros b Hb. unfold BL. apply in_concat. exists (lvl_blocks li). split; [| exact Hb]. apply in_map. eapply nth_error_In. exact Hli. }
assert (JO2 : jopt rsegs S4F cs mp cbs cur) by (eapply jopt_agree; [exact JO | exact AGL2 | exact CBSin]).
clear MI WM SRC3 PAD3.
remember (Z.of_nat (length str) + 1) as nn eqn:Hnn.

assert (OUT' : exists A2 NB, HEAP S4L HIx A2 (NB ++ pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0) mp md2 /\
((r = 0 /\ NB = []) \/ (r <> 0 /\ NB = [(r, nn)] /\ rw_cells rsegs mp r [CB (Z.to_nat nn) (str ++ [b0])]))).
{ destruct OUT as [(-> & HP2) | (Hr & BLK2 & HP2)].
- exists A2x, []. split; [exact HP2 | left; split; reflexivity].
- exists A2x, [(r, nn)]. split; [exact HP2 | right; split; [exact Hr | split; [reflexivity | exact BLK2]]]. }
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
- destruct (ALLf a k Hin) as (H1 & _ & H3). split; [apply in_or_app; right; exact H1 | exact H3]. }
assert (AGY : forall mz, munch [(bse, bse + 32)] mp mz -> wmono rsegs mp mz ->
forall BS, (forall a k, In (a, k) BS -> In (a, k) (NB ++ pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0) /\ a <> q) -> agree_on rsegs BS mp mz).
{ intros mz MU1 WM1 BS HBS. eapply agree_of_munch; [exact MU1 | exact WM1 |]. intros a k Hin. destruct (HBS a k Hin) as (HinL & Hnq).
pose proof (heap_blk S4L HIx _ _ _ _ a k HP2 HinL) as (Hk0 & _).
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ a k q (32 * mxd) HP2 HinL ltac:(apply in_or_app; right; exact INq) Hnq). cbn. lia. }
stash PB2. stash TSK. stash BASE2. stash LV2. stash OUT. stash JO2.
reenter MOK2.
bst. norm_sx32. bst.
bst. rewrite (unsigned_lit (Z.of_nat depth)) by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32.
replace (q + Z.of_nat depth * 32) with bse by lia. bst.
unstash PB2. unstash TSK. unstash BASE2. unstash LV2. unstash OUT. unstash JO2.
destruct OUT as [[-> ->] | (Hr & -> & BLK2)].
-
bst. if_true. bst. bst.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (BASE3 : PE_BASE HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) LB0 payload me lo mc md2 A2 ([] ++ pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0) errv2)
by (eapply (PE_BASE_write HIx); [exact STC | exact BASE2 | intros b Hb; apply in_or_app; right; exact (INCL0 _ Hb) | exact MU | exact WM | exact MI |];
apply Forall_cons; [| apply Forall_nil]; unfold base_w; cbn [fst snd pf_spf pf_md pf_mxd pf_fl]; left; exists q, (32 * mxd);
split; [apply in_or_app; right; exact INq|]; split; [exact NQ0 | lia]);
assert (PB3 : pbuf rsegs mc pbs pb)
by (eapply pbuf_agree; [exact PB2 | apply (AGY mc MU WM) | apply incl_refl]; intros a k Hin; eapply NEq; apply in_or_app; right; apply in_or_app; left; exact Hin);
assert (AGL3 : agree_on rsegs BL mp mc)
by (apply (AGY mc MU WM); intros a k Hin; eapply NEq; apply in_or_app; right; apply in_or_app; right; exact Hin);
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
[exact TSK | lia | exact MU | exact WM | intros; exact I | unfold srec_cells; rewrite Ecur0, Hn0; exact L5])
end end.
apply evt_RZ_done. eapply (Kerr _ md2 A2 errv2); [ | apply fsaved_refl | intros Hf; exact Hf].
split.
+ unfold PE_CORE, ts0. cbn [t_levels t_depth t_co t_pb t_pbs t_x t_obj ts_choff pf_len pf_tk pf_spf pf_md pf_mxd pf_fl].
split; [exact LEN32|]. split; [exact D32|]. split; [lia|]. split; [reflexivity|].
split; [unfold tok_cells, tok_cells_g; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd]; exact TOK|].
split; [exact PB3|]. split; [exact Hpb|]. split; [exact TSK3 | unfold pe_frame; exact FR].
+ cbn [app pf_mxd] in BASE3. apply (PE_REST_of_base HIx); [exact BASE3 | |].
* unfold ts0. cbn [t_levels t_depth pf_mxd]. intros i li Hli.
destruct (Nat.eq_dec i depth) as [-> | NE].
-- rewrite Hl in Hli. injection Hli as <-.
eapply (lvl_cur_agree rsegs S4F); [exact LVd | | rewrite LBl; apply incl_refl].
eapply agree_on_trans; [eapply agree_on_incl; [exact AGL2 | exact CBSin] | eapply agree_on_incl; [exact AGL3 | exact CBSin]].
-- exact (LV3 i li Hli NE).
* unfold cur_st, ts0. cbn [t_levels t_depth t_objs t_objbs t_obj pf_mxd]. rewrite Hl, Hst. cbn. reflexivity.
-
assert (HrR : 0 < r < 2^64).
{ pose proof (heap_blk S4L HIx _ _ _ _ r nn HP2 ltac:(left; reflexivity)) as (_ & _ & H0 & Hhi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hhi. lia. }
bst. if_falsex. bst. bst. bst. bstz. bst. bst.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (BASE3 : PE_BASE HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) LB0 payload me lo mc md2 A2 ([(r, nn)] ++ pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0) errv2)
by (eapply (PE_BASE_write HIx); [exact STC | exact BASE2 | intros b Hb; apply in_or_app; right; exact (INCL0 _ Hb) | exact MU | exact WM | exact MI |];
apply Forall_cons; [| apply Forall_nil]; unfold base_w; cbn [fst snd pf_spf pf_md pf_mxd pf_fl]; left; exists q, (32 * mxd);
split; [apply in_or_app; right; exact INq|]; split; [exact NQ0 | lia]);
assert (PB3 : pbuf rsegs mc pbs pb)
by (eapply pbuf_agree; [exact PB2 | apply (AGY mc MU WM) | apply incl_refl]; intros a k Hin; eapply NEq; apply in_or_app; right; apply in_or_app; left; exact Hin);
assert (AGL3 : agree_on rsegs BL mp mc)
by (apply (AGY mc MU WM); intros a k Hin; eapply NEq; apply in_or_app; right; apply in_or_app; right; exact Hin);
assert (AGN : agree_on rsegs [(r, nn)] mp mc)
by (apply (AGY mc MU WM); intros a k Hin; eapply NEq; apply in_or_app; left; exact Hin);
assert (LV3 : forall i li, nth_error levels i = Some li -> i <> depth -> lvl_cur rsegs S4F mc depth i li)
by (intros i li Hli Hne; eapply (lvl_cur_agree rsegs S4F); [exact (LV2 i li Hli Hne) | exact AGL3 |];
intros b Hb; unfold BL; apply in_concat; exists (lvl_blocks li); split; [| exact Hb]; apply in_map; eapply nth_error_In; exact Hli)
end.
set (l' := TL ST_eatws ST_ofend cur cs cbs r [(r, nn)]).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
match goal with L8 : rw_cells rsegs mc bse _ |- _ =>
pose proof (rw_cells_recast_prefix rsegs mc bse [C8 (Z_to_bv 64 85899345920)] [C4 (Z_to_bv 64 ST_eatws); C4 (Z_to_bv 64 ST_ofend)]
[C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 cur); C8 (Z_to_bv 64 r)] L8 ltac:(cbn; repeat split)
ltac:(apply bytes_eq_by_unsigned; vm_compute; reflexivity) eq_refl) as L5; cbn [app pf_mxd] in L5;
assert (TSK3 : tstack rsegs mc q (lupd levels depth l'))
by (subst bse; eapply (tstack_put rsegs mp mc q levels depth l' []);
[exact TSK | lia | exact MU | exact WM | intros; exact I | unfold srec_cells, l'; cbn [tl_st tl_ss tl_cur tl_name pf_mxd]; exact L5]);
assert (BLK3 : rw_cells rsegs mc r [CB (Z.to_nat nn) (str ++ [b0])])
by (eapply rw_cells_agree; [exact BLK2 | exact AGN | exists r, nn; split; [left; reflexivity | cbn; lia]])
end end.
apply evt_RZ_done. eapply (Kbreak _ md2 A2 r [(r, nn)] errv2); [exact Hr | | apply fsaved_refl | intros Hf; exact Hf].
split.
+ unfold PE_CORE. cbn [t_levels t_depth t_co t_pb t_pbs t_x t_obj ts_choff pf_len pf_tk pf_spf pf_md pf_mxd pf_fl].
split; [rewrite lupd_length; exact LEN32|]. split; [exact D32|]. split; [lia|]. split; [reflexivity|].
split; [unfold tok_cells, tok_cells_g; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd]; exact TOK|].
split; [exact PB3|]. split; [exact Hpb|]. split; [exact TSK3 | unfold pe_frame; exact FR].
+ fold l'. apply (PE_REST_of_base HIx).
* eapply (PE_BASE_perm HIx); [exact BASE3|].
unfold pe_blocks, tstate_blocks, ts0. cbn [t_pbs t_objbs t_levels pf_tk app pf_md pf_mxd pf_fl].
rewrite (concat_split levels depth l Hl), (lupd_split levels depth l l' Hl), LBl.
replace (lvl_blocks l') with (cbs ++ [(r, nn)]) by reflexivity.
rewrite <- !app_assoc. cbn [app pf_mxd].
apply (Permutation_trans (l' := (pbs ++ concat (map lvl_blocks (firstn depth levels)) ++ cbs) ++ (r, nn) :: (concat (map lvl_blocks (skipn (S depth) levels)) ++ (tk, 72) :: (q, (32 * mxd)) :: LB0))).
-- apply Permutation_cons_app. rewrite <- !app_assoc. apply Permutation_refl.
-- rewrite <- !app_assoc. apply Permutation_refl.
* cbn [t_levels t_depth pf_mxd]. intros i li Hli.
destruct (Nat.eq_dec i depth) as [-> | NE].
-- rewrite nth_error_lupd_eq in Hli by lia. injection Hli as <-.
split; [cbn; unfold ST_eatws; lia|]. split; [cbn; unfold ST_ofend; lia|]. split.
{ cbn [tl_cs tl_cbs tl_cur l' pf_mxd]. eapply jopt_agree; [exact JO2 | exact AGL3 | exact CBSin]. }
rewrite Nat.ltb_irrefl, Nat.eqb_refl. exists CObj, true. split; [reflexivity|]. split; [exact CLS0|].
cbn [name_ok tl_name tl_nbs l' pf_mxd]. split; [exact Hr|]. exists nn, str. split; [reflexivity|]. split; [lia|].
split; [lia|]. split; [apply nonul_forall; exact NONUL|]. exists []. rewrite app_nil_r. exact BLK3.
-- rewrite nth_error_lupd_neq in Hli by congruence. exact (LV3 i li Hli NE).
* unfold cur_st. cbn [t_levels t_depth t_objs t_objbs t_obj pf_mxd]. rewrite nth_error_lupd_eq by lia. cbn. reflexivity.
Qed.

#[using="MEMMOVE STRDUP"] Lemma ofq_app :
forall (pf : pe_fix) (q : Z) (LB0 : list blk) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (ts : tstate) (l : tlevel) (co0 : Z)
(cb : byte) (j1 j2 utf : list byte) (sv : pe_saved) (errv : word) (T : TSet)
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC HIx pf lo ->
PE_INV HIx pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_ofield ->
0 <= co0 <= t_co ts -> t_co ts < pf_len pf ->
(forall m' md' A' r nbs' pbs' errv' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F' fc',
r <> 0 ->
PE_INV HIx pf q LB0 payload me lo m' md' A'
(TST (t_depth ts) (lupd (t_levels ts) (t_depth ts) (TL ST_eatws ST_ofend (tl_cur l) (tl_cs l) (tl_cbs l) r nbs'))
(t_co ts) (t_pb ts) pbs' (t_x ts) (t_obj ts) (t_objs ts) (t_objbs ts)) cb j1 j2 utf sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_BREAK (t_co ts) x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F' fc' m') md') T) ->
(forall m' md' A' pbs' errv' x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F' fc',
PE_INV HIx pf q LB0 payload me lo m' md' A' (ts_set_pbs ts pbs') cb j1 j2 utf sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_ERR co0 x1' gp' t0' t1' t2' (Z_to_bv 64 16) a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F' fc' m') md') T) ->
realizes rsegs (mkCfg (pe_ms rsegs pf 0x23170 co0 x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (pf_sb pf + t_co ts)) s6 s7 s8 s9 s10 t3 t4 t5 t6 F fc m) md) T.
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
bst. bst. norm_w32. replace (sb + co - (sb + co0)) with n by lia. bst. bst.
apply evt_RZ_done.
eapply (memappend_cps HIx MEMMOVE) with (lo := lo) (b := sb + co0) (n := n);
[ exact HP1 | exact PBC | (clear - Hco0 Hco LEN; lia) | exact SRC | exact SRCL
| left; eapply (payload_crange (PEF _ _ _ _ _ _ _ _ _ _)); [exact SBin | intros bb Hbb; apply in_or_app; right; right; right; exact Hbb | cbn [pf_spf pf_mxd]; rewrite ?unsigned_lit by (clear - SP0; lia); unfold PE_FRAME; (clear; lia) | (clear - Hco0; lia) | (clear - SRCL; lia) | cbn [pf_len pf_mxd]; (clear - CO; lia)] | (clear - Hco0 SB0; lia) | (clear - CO SBL; lia) | (clear - Hco0 Hco Hdsb; lia) | .. ]; try alloc_side.
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
bst. if_true. bst. bst. apply evt_RZ_done. eapply Kerr16; [| exact FS2 | exact FRM2]. unfold ts2, pbs2 in INV2. exact INV2. }

bst. if_falsex. apply evt_RZ_done.
eapply (ofq_new (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo m2 md2 A2 ts2 l co0 cb);
[ exact STC | exact INV2 | exact Hl | exact Hst | | ].
- unfold ts2; cbn [t_levels t_depth t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd]. intros. eapply Kbreak; [eassumption | eassumption | eapply fsaved_trans; [exact FS2 | eassumption] | intros Hf; auto].
- unfold ts2, ts_set_pbs; cbn [t_levels t_depth t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd]. intros. eapply Kerr16; [eassumption | eapply fsaved_trans; [exact FS2 | eassumption] | intros Hf; auto].
Qed.

#[using="MEMMOVE"] Lemma of_loop :
forall (n : nat) (pf : pe_fix) (q : Z) (LB0 : list blk) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (ts : tstate) (l : tlevel) (co0 : Z)
(cb : byte) (j1 j2 utf : list byte) (sv : pe_saved) (errv : word) (T : TSet)
(x1 gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s8 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC HIx pf lo ->
PE_INV HIx pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv ->
CSTR_OK pf payload ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_ofield ->
0 <= co0 <= t_co ts -> t_co ts < pf_len pf -> nth_error payload (Z.to_nat (t_co ts)) = Some cb ->
bv_unsigned cb <> bv_unsigned (ts_quote (t_x ts)) ->
(pf_len pf - t_co ts <= Z.of_nat n) ->

(forall m' co' cb' (j2' : list byte) x1' a1' a2' a3',
t_co ts <= co' < pf_len pf -> nth_error payload (Z.to_nat co') = Some cb' -> bv_unsigned cb' = bv_unsigned (ts_quote (t_x ts)) ->
PE_INV HIx pf q LB0 payload me lo m' md A (ts_set_co ts co') cb' j1 j2' utf sv errv ->
realizes rsegs (mkCfg (pe_ms rsegs pf 0x23170 co0 x1' gp t0 t1 t2 (Z_to_bv 64 (bv_unsigned cb')) a1' a2' a3' a4 a5 a6 a7
(Z_to_bv 64 (pf_sb pf + co')) (Z_to_bv 64 (co' - co0)) (Z_to_bv 64 (pf_sb pf + co'))
s8 (Z_to_bv 64 (Z.of_nat (t_depth ts))) s10 t3 t4 t5 t6 F fc m') md) T) ->

(forall m' co' cb' (j2' : list byte) x1' a2' a3',
t_co ts <= co' < pf_len pf -> nth_error payload (Z.to_nat co') = Some cb' -> bv_unsigned cb' = 92 ->
PE_INV HIx pf q LB0 payload me lo m' md A (ts_set_co ts co') cb' j1 j2' utf sv errv ->
realizes rsegs (mkCfg (pe_ms rsegs pf 0x23948 co0 x1' gp t0 t1 t2 (Z_to_bv 64 (bv_unsigned cb')) (Z_to_bv 64 92) a2' a3' a4 a5 a6 a7
(Z_to_bv 64 (pf_sb pf + co')) (Z_to_bv 64 (co' - co0)) (Z_to_bv 64 (pf_sb pf + co'))
s8 (Z_to_bv 64 (Z.of_nat (t_depth ts))) s10 t3 t4 t5 t6 F fc m') md) T) ->

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

(forall m' co' cb' (j2' : list byte) x1' a1' a2' a3',
t_co ts <= co' < pf_len pf -> nth_error payload (Z.to_nat co') = Some cb' -> bv_unsigned cb' <= 31 -> Z.land (pf_fl pf) 1 = 1 ->
PE_INV HIx pf q LB0 payload me lo m' md A (ts_set_co ts co') cb' j1 j2' utf sv errv ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_ERR co0 x1' gp t0 t1 t2 (Z_to_bv 64 12) a1' a2' a3' a4 a5 a6 a7
(Z_to_bv 64 (pf_sb pf + co')) (Z_to_bv 64 (co' - co0)) (Z_to_bv 64 (pf_sb pf + co'))
s8 (Z_to_bv 64 (Z.of_nat (t_depth ts))) s10 t3 t4 t5 t6 F fc m') md) T) ->
realizes rsegs (mkCfg (pe_ms rsegs pf 0x23688 co0 x1 gp t0 t1 t2
(Z_to_bv 64 (bv_unsigned cb)) a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (pf_sb pf + t_co ts)) (Z_to_bv 64 (t_co ts - co0)) (Z_to_bv 64 (pf_sb pf + t_co ts))
s8 (Z_to_bv 64 (Z.of_nat (t_depth ts))) s10 t3 t4 t5 t6 F fc m) md) T.
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
assert (SB1 : 1 <= sb).
{ pose proof SBin as PLOC. unfold payload_loc in PLOC. cbn [pf_len pf_sb pf_spf] in PLOC.
destruct PLOC as [L0 | [STKM | ([ba bn] & Hb & Hb1 & Hb2)]].
{ lia. }
{ unfold PE_FRAME in *. lia. }
pose proof (heap_blk S4L HIx _ _ _ _ ba bn HP ltac:(unfold pe_blocks; apply in_or_app; right; right; right; exact Hb)) as (_ & _ & Hba & _).
cbn [blk_addr fst] in Hb1. lia. }
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

bst. bst.
destruct (Z.eq_dec (bv_unsigned cb) 92) as [E92 | N92].
{ if_truex. unstash PB. unstash REST. unstash TSK. apply evt_RZ_done.
eapply (Kbs m co cb); [lia | exact Hc | exact E92 | exact INV0]. }
if_falsex.

bst. rewrite (zx32_fl fl) by lia. bst. rewrite (unsigned_lit fl) by lia.
assert (TAIL : forall a2v, evt rsegs (RZ rsegs md T)
(MS (mkR x1 (Z_to_bv 64 spf) gp (Z_to_bv 64 490496) t0 t1 t2 (Z_to_bv 64 tk) (Z_to_bv 64 oldl) (Z_to_bv 64 (bv_unsigned cb)) (Z_to_bv 64 fl) a2v a3 a4 a5 a6 a7
(Z_to_bv 64 newl) (Z_to_bv 64 lenr) (Z_to_bv 64 (sb + co)) (Z_to_bv 64 (sb + co0)) (Z_to_bv 64 (co - co0)) (Z_to_bv 64 (sb + co))
s8 (Z_to_bv 64 (Z.of_nat depth)) s10 (Z_to_bv 64 79040) t3 t4 t5 t6)
F (Z_to_bv 64 0x236a4) fc None m (seg_rom rsegs))).
2:{ destruct (land1_cases fl) as [F1 | F1]; rewrite F1.
- bst. if_true. apply TAIL.
- bst. if_false. bst. bst. destruct (Z_lt_dec 31 (bv_unsigned cb)) as [GT | LE].
+ if_falsex. apply TAIL.
+ if_truex. bst. bst. unstash PB. unstash REST. unstash TSK. apply evt_RZ_done.
eapply (Kerr12s m co cb); [lia | exact Hc | lia | exact F1 | exact INV0]. }
intros a2v.

step. step. step. repeat tk2c. step. norm_sx32. step. norm_w32. step. repeat tk2c. bst.

bst.
destruct (Z.eq_dec (bv_unsigned cb) 0) as [E0 | N0].
{ if_truex. unstash PB. unstash REST. unstash TSK. apply evt_RZ_done.
replace (Z_to_bv 64 (co - co0)) with (Z_to_bv 64 (co + 1 - 1 - co0)) by (f_equal; lia).
lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mc _) _) _ =>
eapply (str_flush HIx MEMMOVE (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo mc md A
(TST depth levels (co + 1) pb pbs (TS isd stpos (Z_to_bv 64 (co + 1)) err ucs high quote) obj objs objbs) co0 cb);
[ exact STC | eapply MKINV; [lia | exact TOK | exact FR | exact MU | exact WM | exact MI] | cbn; lia
| unfold ts_set_pbs; cbn [t_levels t_depth t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd]; intros; eapply Kout; [| eassumption..]; lia
| unfold ts_set_pbs; cbn [t_levels t_depth t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd]; intros; eapply Kerr16; [| eassumption..]; lia ]
end. }
if_falsex.

bst.
destruct (peek_cases (PEF tk oldl newl len lenr sb spf pmd mxd fl) payload co cb LENR CSTR (proj1 RR) ltac:(cbn [pf_len pf_mxd]; lia) ltac:(cbn [pf_len pf_mxd]; lia) Hc N0)
as [[Elenr Heof] | [Hne Hmore]]; [cbn [pf_len pf_lenr pf_mxd] in Elenr, Heof; subst lenr; pose (lenr := len) | cbn [pf_len pf_lenr pf_mxd] in Hne, Hmore].
{ if_truex. unstash PB. unstash REST. unstash TSK. apply evt_RZ_done.
replace (Z_to_bv 64 (co - co0)) with (Z_to_bv 64 (len - 1 - co0)) by (f_equal; lia).
lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mc _) _) _ =>
eapply (str_eof HIx MEMMOVE (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo mc md A
(TST depth levels (co + 1) pb pbs (TS isd stpos (Z_to_bv 64 (co + 1)) err ucs high quote) obj objs objbs) co0 cb);
[ exact STC | eapply MKINV; [lia | exact TOK | exact FR | exact MU | exact WM | exact MI] | cbn; lia | cbn; lia | first [left; reflexivity | right; reflexivity]
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
(MS (mkR x1x (Z_to_bv 64 spf) gp (Z_to_bv 64 490496) t0 t1 t2 (Z_to_bv 64 tk) (Z_to_bv 64 oldl) a0x a1x a2x a3x a4 a5 a6 a7
(Z_to_bv 64 newl) (Z_to_bv 64 lenr) (Z_to_bv 64 (sb + co + 1)) (Z_to_bv 64 (sb + co0)) (Z_to_bv 64 (co - co0)) (Z_to_bv 64 (sb + co + 1))
s8 (Z_to_bv 64 (Z.of_nat depth)) s10 (Z_to_bv 64 79040) t3 t4 t5 t6)
F (Z_to_bv 64 0x23674) fc None mf (seg_rom rsegs))).
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
bst. change (zxb c') with (Z_to_bv 64 (bv_unsigned c')).
bst. change (zxb quote) with (Z_to_bv 64 (bv_unsigned quote)).
bst. rewrite le1_zxw. mem_after_store.
bst. norm_w32. bst.
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

bst. rewrite (unsigned_lit fl) by lia. bst.
destruct (land16_cases fl) as [F16 | F16]; rewrite F16.
+
bst. if_true. eapply JOINF; [exact TOK | exact FR | exact MU | exact WM | exact MI].
+
bst. if_false.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
assert (STR1 : bytes_at rsegs m1 sb payload)
by (unstash REST; eapply (PE_REST_private_write HIx) with (ts := ts0) in REST;
[exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 REST)))))) | exact STC | exact MU | exact WM | exact MI | apply pe_wtf_private; exact HW])
end.
pose proof (payload_byte _ _ _ _ _ STR1 Hc' ltac:(lia)) as RDC. replace (sb + (co + 1)) with (sb + co + 1) in RDC by lia.
bst. bst. bst.
eapply evt_cut.
{ eapply (validate_utf8_frame_P) with (c := c') (A := spf + 24) (B := spf) (pre := [C8 (Z_to_bv 64 obj); CB 16 j1]);
[exact FR | reflexivity | lia | lia | (clear - SPA; Z.div_mod_to_equations; lia) | exact MI]. }
intros ms' (r & a2' & a3' & nv' & m2 & -> & Hr & FR2 & MU2 & WM2 & MI2). cbn [app] in FR2.
replace (ret_pc (Z_to_bv 64 0x236e0)) with (Z_to_bv 64 0x236e0) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
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
bst. if_false. bst. bst. bstz.
unstash PB. unstash REST. unstash TSK. apply evt_RZ_done.
replace (Z_to_bv 64 (co - co0)) with (Z_to_bv 64 (co + 1 - 1 - co0)) by (f_equal; lia).
lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mc _) _) _ =>
lazymatch goal with TOK3 : rw_cells rsegs mc tk [_; _; _; _; _; _; _; C4 ?e3; _; _; _; _; _; _; _] |- _ =>
eapply (str_flush HIx MEMMOVE (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo mc md A
(TST depth levels (co + 1) pb pbs (TS isd stpos (Z_to_bv 64 (co + 1)) e3 ucs high quote) obj objs objbs) co0 cb);
[ exact STC | eapply MKINV; [lia | exact TOK3 | eassumption | eassumption | eassumption | assumption] | cbn; lia
| unfold ts_set_pbs; cbn [t_levels t_depth t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd]; intros; eapply Kout; [| eassumption..]; lia
| unfold ts_set_pbs; cbn [t_levels t_depth t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd]; intros; eapply Kerr16; [| eassumption..]; lia ]
end end.
*
bst. if_true. eapply JOINF; [exact TOK2 | exact FR2 | exact MU2' | exact WM2' | exact MI2].
Qed.
#[using="MEMMOVE STRDUP"] Lemma seg_ofield :
forall (pf : pe_fix) (q : Z) (LB0 : list blk) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (ts : tstate) (l : tlevel)
(cb : byte) (j1 j2 utf : list byte) (sv : pe_saved) (errv : word) (T : TSet)
(x1 gp t0 t1 t2 a3 a4 a5 a6 a7 s6 s7 s8 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC HIx pf lo ->
PE_INV HIx pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv ->
CSTR_OK pf payload ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_ofield ->
t_co ts < pf_len pf -> nth_error payload (Z.to_nat (t_co ts)) = Some cb ->

(forall m' md' A' r nbs' pbs' errv' co' cb' (j2' : list byte) x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F' fc',
t_co ts <= co' < pf_len pf -> nth_error payload (Z.to_nat co') = Some cb' -> bv_unsigned cb' = bv_unsigned (ts_quote (t_x ts)) -> r <> 0 ->
PE_INV HIx pf q LB0 payload me lo m' md' A'
(TST (t_depth ts) (lupd (t_levels ts) (t_depth ts) (TL ST_eatws ST_ofend (tl_cur l) (tl_cs l) (tl_cbs l) r nbs'))
co' (t_pb ts) pbs'
(TS (ts_isd (t_x ts)) (ts_stpos (t_x ts)) (Z_to_bv 64 co') (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))
(t_obj ts) (t_objs ts) (t_objbs ts)) cb' j1 j2' utf sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_BREAK co' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F' fc' m') md') T) ->

(forall m' md' A' pbs' errv' co' cb' (j2' : list byte) x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F' fc',
t_co ts <= co' < pf_len pf -> nth_error payload (Z.to_nat co') = Some cb' -> bv_unsigned cb' = 92 ->
PE_INV HIx pf q LB0 payload me lo m' md' A'
(TST (t_depth ts) (lupd (t_levels ts) (t_depth ts) (TL ST_string_escape ST_ofield (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)))
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

(forall m' co' cb' (j2' : list byte) x1' a1' a2' a3',
t_co ts <= co' < pf_len pf -> nth_error payload (Z.to_nat co') = Some cb' -> bv_unsigned cb' <= 31 -> Z.land (pf_fl pf) 1 = 1 ->
PE_INV HIx pf q LB0 payload me lo m' md A
(TST (t_depth ts) (t_levels ts) co' (t_pb ts) (t_pbs ts)
(TS (ts_isd (t_x ts)) (ts_stpos (t_x ts)) (Z_to_bv 64 co') (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))
(t_obj ts) (t_objs ts) (t_objbs ts)) cb' j1 j2' utf sv errv ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_ERR (t_co ts) x1' gp t0 t1 t2 (Z_to_bv 64 12) a1' a2' a3' a4 a5 a6 a7
(Z_to_bv 64 (pf_sb pf + co')) (Z_to_bv 64 (co' - t_co ts)) (Z_to_bv 64 (pf_sb pf + co'))
s8 (Z_to_bv 64 (Z.of_nat (t_depth ts))) s10 t3 t4 t5 t6 F fc m') md) T) ->
realizes rsegs (mkCfg (pe_ms rsegs pf (pe_jt ST_ofield) (t_co ts) x1 gp t0 t1 t2
(Z_to_bv 64 0) (Z_to_bv 64 (tl_st l)) (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) a3 a4 a5 a6 a7
(Z_to_bv 64 q) s6 s7 s8 (Z_to_bv 64 (Z.of_nat (t_depth ts))) s10 t3 t4 t5 t6 F fc m) md) T.
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
bst. change (zxb cb) with (Z_to_bv 64 (bv_unsigned cb)). bst. change (zxb quote) with (Z_to_bv 64 (bv_unsigned quote)). bst. bst.
destruct (Z.eq_dec (bv_unsigned cb) (bv_unsigned quote)) as [EQ | NQ].
- if_falsex. apply evt_RZ_done.
eapply (ofq_app (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo m md A
(TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) l co cb);
[ exact STC | exact INV | exact Hl | exact Hst | cbn; lia | exact Hco
| cbn [t_levels t_depth t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd]; intros; eapply Kq; [| exact Hc | exact EQ | eassumption..]; lia
| unfold ts_set_pbs; cbn [t_levels t_depth t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd]; intros; eapply Kerr16; [| eassumption..]; lia ].
- if_truex. bst. bst. bst. bst.
apply evt_RZ_done. replace (Z_to_bv 64 0) with (Z_to_bv 64 (co - co)) by (f_equal; lia).
eapply (of_loop (Z.to_nat (len - co)) (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo m md A
(TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) l co cb);
[ exact STC | exact INV | exact CSTR | exact Hl | exact Hst | cbn; lia | exact Hco | exact Hc | exact NQ | cbn; lia | | | | | ].
+ unfold ts_set_co; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_sb pf_len pf_md pf_mxd pf_fl].
intros m' co' cb' j2' x1' a1' a2' a3' R' Hc' EQ INV'.
eapply (ofq_app (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo m' md A
(TST depth levels co' pb pbs (TS isd stpos (Z_to_bv 64 co') err ucs high quote) obj objs objbs) l co cb');
[ exact STC | exact INV' | exact Hl | exact Hst | cbn; lia | cbn; lia
| cbn [t_levels t_depth t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd]; intros; eapply Kq; [| exact Hc' | exact EQ | eassumption..]; lia
| unfold ts_set_pbs; cbn [t_levels t_depth t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd]; intros; eapply Kerr16; [| eassumption..]; lia ].
+ unfold ts_set_co; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_sb pf_len pf_md pf_mxd pf_fl].
intros m' co' cb' j2' x1' a2' a3' R' Hc' E92 INV'.
eapply (of_bs (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo m' md A
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
End PeOfield.

End RC__1.
End Mq0.

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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qtgi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qtgi. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QjDH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDH. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QjDH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDH.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UC8c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UC8c.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uihm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uihm. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UPZI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UPZI.Mq4. 
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UhHQ. Import UhHQ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U5Ki. Import U5Ki. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB.Tk1 Require Tk1Reset. Import Tk1Reset.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UPZI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UPZI.Mq1.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QmZZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmZZ. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QkMG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkMG.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UG8z.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UG8z. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Udyh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Udyh.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Ub4w.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ub4w. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Ua8x.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ua8x.Mq4. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UXfU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UXfU.Mq2.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QKQo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKQo.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uu4M.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uu4M.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UPZI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UPZI.Mq0.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Import Tk2Gen.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition tdepth_ok (ts : tstate) : Prop :=
(forall i l, nth_error (t_levels ts) i = Some l -> odep (tl_cs l) + Z.of_nat i <= 32) /\
(zin (cur_st ts) [ST_array_add; ST_ovadd] = true -> odep (t_objs ts) + Z.of_nat (t_depth ts) <= 31).

Definition pe_ms7 (segs : list Segment) (pf : pe_fix) (pc : Z) (co : Z)
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 s10 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) : machine_state :=
MS (mkR x1 (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 0x77c00) t0 t1 t2
(Z_to_bv 64 (pf_tk pf)) (Z_to_bv 64 (pf_oldl pf)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (pf_newl pf)) (Z_to_bv 64 (pf_lenr pf)) s4 (Z_to_bv 64 (pf_sb pf + co)) s6 s7 s8
s9 s10 (Z_to_bv 64 PE_JTAB) t3 t4 t5 t6)
F (Z_to_bv 64 pc) fc None m (seg_rom segs).

#[using="Type"] Lemma pe_ms7_26 : forall segs pf pc co x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 s10 t3 t4 t5 t6 F fc m,
pe_ms7 segs pf pc co x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 s10 t3 t4 t5 t6 F fc m =
pe_ms segs pf pc co x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 s10 t3 t4 t5 t6 F fc m.
Proof. reflexivity. Qed.

Definition final_err (err : word) (cb : byte) (st ss : Z) : word :=
if ((bv_unsigned cb =? 0) && negb (st =? 2) && negb (ss =? 2))%bool then Z_to_bv 64 3 else err.

#[using="Type"] Lemma zx32_small : forall fl, 0 <= fl < 2^32 -> zx32 (Z_to_bv 64 fl) = Z_to_bv 64 fl.
Proof. intros fl H. unfold zx32. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. Qed.

Section PeOut.
Variable HIx : heap_iface S4L.
Notation HEAPx := (HEAP S4L HIx).



#[using="Type"] Lemma out_checks :
forall (m : word -> option byte)
(tk oldl newl len lenr sb spf cop q pb : Z) (pmd : Model) (mxd fl : Z) (depth : nat) (isd stpos choff err ucs high : word) (quote : bv 8)
(l : tlevel) (obj : Z) (cb : byte) (j1 j2 utf : list byte) (sv : pe_saved)
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
(K : machine_state -> Prop),

rw_cells rsegs m tk (tok_cells_g mxd fl pb (Z.of_nat depth) q (TS isd stpos choff err ucs high quote)) ->
pe_frame rsegs m spf obj cb j1 j2 utf sv ->
rw_cells rsegs m (q + 32 * Z.of_nat depth) (srec_cells l) ->
(depth < Z.to_nat mxd)%nat -> 1 <= mxd <= 32 -> 0 <= fl < 2^32 -> 0 < tk -> tk + 72 < 2^63 -> 0 < q -> q + (32 * mxd) < 2^63 -> 0 <= spf -> spf < 2^63 ->
tk + 72 <= spf -> (tk + 72 <= q \/ q + 32 * mxd <= tk) ->
0 <= tl_st l <= 26 -> 0 <= tl_ss l <= 26 -> q mod 16 = 0 ->
mem_inv rsegs m ->
(forall mc (a0' a1' a2' a3' a4' a5' a6' a7' : word) (e' : word),
rw_cells rsegs mc tk (tok_cells_g mxd fl pb (Z.of_nat depth) q (TS isd stpos choff e' ucs high quote)) ->
munch [(tk + 36, tk + 40)] m mc -> wmono rsegs m mc -> mem_inv rsegs mc ->
evt rsegs K
(MS (mkR x1 (Z_to_bv 64 spf) gp (Z_to_bv 64 0x77c00) t0 t1 t2 (Z_to_bv 64 tk) (Z_to_bv 64 oldl) a0' a1' a2' a3' a4' a5' a6' a7'
(Z_to_bv 64 newl) (Z_to_bv 64 lenr) s4 (Z_to_bv 64 (sb + cop)) s6 s7 s8 s9 s10 (Z_to_bv 64 PE_JTAB) t3 t4 t5 t6)
F (Z_to_bv 64 0x23f5c) fc None mc (seg_rom rsegs))) ->
evt rsegs K (pe_ms7 rsegs (PEF tk oldl newl len lenr sb spf pmd mxd fl) PE_OUT cop x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 s10 t3 t4 t5 t6 F fc m).
Proof.
intros until K. intros TOK FR LVL D32 MXB FLB Htlo Hthi Hqlo Hqhi SP0 SPH Dtf Dtq ST26 SS26 Hqal MI TAIL.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK. unfold pe_frame in FR.
unfold srec_cells in LVL. remember (q + 32 * Z.of_nat depth) as bse eqn:Hbse.
unfold pe_ms7. cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl]. unfold PE_OUT.
pose proof (bv_unsigned_in_range 8 cb) as CBR; unfold bv_modulus in CBR; cbn in CBR.
assert (Hbse32 : bse + 32 <= q + 32 * mxd) by nia || (assert (Hbse32 : bse + 32 <= q + 32 * mxd) by lia).
assert (Hbal : bse mod 16 = 0) by (subst bse; clear - Hqal; Z.div_mod_to_equations; lia).

assert (JOIN : forall mc (a0x : word) (e1 : word),
rw_cells rsegs mc tk
[C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 pb); C4 (Z_to_bv 64 mxd); C4 (Z_to_bv 64 (Z.of_nat depth)); C4 isd; C4 stpos;
C4 choff; C4 e1; C4 ucs; C4 high; C1 quote; CB 7 (repeat (Z_to_bv 8 0) 7); C8 (Z_to_bv 64 q); C4 (Z_to_bv 64 fl); C4 (Z_to_bv 64 0)] ->
munch [(tk + 36, tk + 40)] m mc -> wmono rsegs m mc -> mem_inv rsegs mc ->
evt rsegs K
(MS (mkR x1 (Z_to_bv 64 spf) gp (Z_to_bv 64 0x77c00) t0 t1 t2 (Z_to_bv 64 tk) (Z_to_bv 64 oldl) a0x (Z_to_bv 64 fl) a2 a3 a4 a5 a6 a7
(Z_to_bv 64 newl) (Z_to_bv 64 lenr) s4 (Z_to_bv 64 (sb + cop)) s6 s7 s8 s9 s10 (Z_to_bv 64 PE_JTAB) t3 t4 t5 t6)
F (Z_to_bv 64 0x23ec4) fc None mc (seg_rom rsegs))).
{ intros mc a0x e1 TOKc MUc WMc MIc.
assert (FRc : rw_cells rsegs mc spf [C8 (Z_to_bv 64 obj); CB 16 j1; C4 (nbw j2); CB 3 (skipn 4 j2); C1 cb; CB 8 utf;
C8 (pe_s11 sv); C8 (pe_s10 sv); C8 (pe_s9 sv); C8 (pe_s8 sv); C8 (pe_s7 sv); C8 (pe_s6 sv);
C8 (pe_s5 sv); C8 (pe_s4 sv); C8 (pe_s3 sv); C8 (pe_s2 sv); C8 (pe_s1 sv); C8 (pe_s0 sv); C8 (pe_ra sv)]).
{ eapply rw_cells_transport; [exact FR | exact MUc | exact WMc | cbn; lia]. }
assert (LVLc : rw_cells rsegs mc bse [C4 (Z_to_bv 64 (tl_st l)); C4 (Z_to_bv 64 (tl_ss l)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (tl_cur l)); C8 (Z_to_bv 64 (tl_name l))]).
{ eapply rw_cells_transport; [exact LVL | exact MUc | exact WMc | cbn; lia]. }
clear FR LVL TOK MI. pose proof MUc as MU. pose proof WMc as WM. clear MUc WMc.

assert (GO : forall mf (a0' a1' a2' a3' a4' a5' a6' a7' : word) e',
rw_cells rsegs mf tk
[C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 pb); C4 (Z_to_bv 64 mxd); C4 (Z_to_bv 64 (Z.of_nat depth)); C4 isd; C4 stpos;
C4 choff; C4 e'; C4 ucs; C4 high; C1 quote; CB 7 (repeat (Z_to_bv 8 0) 7); C8 (Z_to_bv 64 q); C4 (Z_to_bv 64 fl); C4 (Z_to_bv 64 0)] ->
munch [(tk + 36, tk + 40)] m mf -> wmono rsegs m mf -> mem_inv rsegs mf ->
evt rsegs K
(MS (mkR x1 (Z_to_bv 64 spf) gp (Z_to_bv 64 0x77c00) t0 t1 t2 (Z_to_bv 64 tk) (Z_to_bv 64 oldl) a0' a1' a2' a3' a4' a5' a6' a7'
(Z_to_bv 64 newl) (Z_to_bv 64 lenr) s4 (Z_to_bv 64 (sb + cop)) s6 s7 s8 s9 s10 (Z_to_bv 64 PE_JTAB) t3 t4 t5 t6)
F (Z_to_bv 64 0x23f5c) fc None mf (seg_rom rsegs))).
{ intros mf a0' a1' a2' a3' a4' a5' a6' a7' e' TOK' MU' WM' MI'. apply (TAIL mf a0' a1' a2' a3' a4' a5' a6' a7' e'); [| exact MU' | exact WM' | exact MI'].
unfold tok_cells_g. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote]. exact TOK'. }
clear TAIL.
bst. norm_sx32. bst. bst. bst. bst.
rewrite (unsigned_lit (Z.of_nat depth)) by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32.
bst. bst. replace (q + Z.of_nat depth * 32) with bse by lia.
change (zxb cb) with (Z_to_bv 64 (bv_unsigned cb)).
bst. bst. bst. bst. bst. bst.
destruct (Z.eq_dec (bv_unsigned cb) 0) as [CB0 | CBn].
-
rewrite CB0. bst. if_true. bst. try norm_sx32. bst.
destruct (Z.eq_dec (tl_st l) 2) as [ST2 | STn].
+ rewrite ST2. bst. if_true. eapply GO; [exact TOKc | exact MU | exact WM | exact MIc].
+ bst. if_falsex. bst. norm_sx32.
destruct (Z.eq_dec (tl_ss l) 2) as [SS2 | SSn].
* rewrite SS2. bst. if_true. eapply GO; [exact TOKc | exact MU | exact WM | exact MIc].
* bst. if_falsex. bst. bstz. eapply GO; [ | exact MU | exact WM | ]; [eassumption | assumption].
-
bst. if_falsex. bst. bst. bst. rewrite (unsigned_lit fl) by lia.
destruct (Z.eq_dec (Z.land fl 3) 1) as [F3 | F3].
+ rewrite F3. if_false.
destruct (PeanoNat.Nat.eq_dec depth 0) as [D0 | Dn].
* subst depth. cbn [Z.of_nat] in *. bst. if_false.
bst. try norm_sx32. bst. bst.
destruct (Z.eq_dec (tl_st l) 2) as [ST2 | STn].
-- rewrite ST2. if_false. bst. bst. bstz. eapply GO; [ | exact MU | exact WM | ]; [eassumption | assumption].
-- if_truex. eapply GO; [exact TOKc | exact MU | exact WM | exact MIc].
* bst. if_truex. eapply GO; [exact TOKc | exact MU | exact WM | exact MIc].
+ pose proof (land3_range fl). if_truex. eapply GO; [exact TOKc | exact MU | exact WM | exact MIc]. }

pose proof (wmono_refl rsegs m) as WM. pose proof (munch_refl [(tk + 36, tk + 40)] m) as MU.
bst. rewrite (zx32_small fl) by lia.
bst. rewrite (unsigned_lit fl) by lia.
destruct (land16_cases fl) as [F16 | F16]; rewrite F16.
- bst. if_true. eapply JOIN; [exact TOK | exact MU | exact WM | exact MI].
- bst. if_false. bst. bst.
lazymatch goal with |- evt _ _ (MS _ _ (if ?cnd then _ else _) _ _ _ _) => destruct cnd; cbv iota end.
+ eapply JOIN; [exact TOK | exact MU | exact WM | exact MI].
+ bst. bstz. eapply JOIN; [ | exact MU | exact WM | ]; [eassumption | assumption].
Qed.

#[using="Type"] Lemma pe_epilogue :
forall (m : word -> option byte) (spf : Z) (FRM : list cell) (sv : pe_saved)
(x1 gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
(K : machine_state -> Prop),
rw_cells rsegs m spf (FRM ++ [C8 (pe_s11 sv); C8 (pe_s10 sv); C8 (pe_s9 sv); C8 (pe_s8 sv); C8 (pe_s7 sv); C8 (pe_s6 sv);
C8 (pe_s5 sv); C8 (pe_s4 sv); C8 (pe_s3 sv); C8 (pe_s2 sv); C8 (pe_s1 sv); C8 (pe_s0 sv); C8 (pe_ra sv)]) ->
cells_size FRM = 40%nat ->
0 <= spf -> spf < 2^63 -> bv_unsigned (pe_ra sv) mod 2 = 0 ->
K (MS (mkR (pe_ra sv) (Z_to_bv 64 (spf + 144)) gp tp t0 t1 t2 (pe_s0 sv) (pe_s1 sv) a0 a1 a2 a3 a4 a5 a6 a7
(pe_s2 sv) (pe_s3 sv) (pe_s4 sv) (pe_s5 sv) (pe_s6 sv) (pe_s7 sv) (pe_s8 sv) (pe_s9 sv) (pe_s10 sv) (pe_s11 sv) t3 t4 t5 t6)
F (ret_pc (pe_ra sv)) fc None m (seg_rom rsegs)) ->
evt rsegs K (MS (mkR x1 (Z_to_bv 64 spf) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x21cc0) fc None m (seg_rom rsegs)).
Proof.
intros until K. intros FR F40 SP0 SPH RAE HK.
apply (rw_cells_merge rsegs m spf [] FRM) in FR. rewrite F40 in FR. cbn [app pf_mxd] in FR.
do 13 bst. bst. bst.
first [ apply evt_done; exact HK | shr; fail ].
Qed.

Hypothesis PUT : put_stmt_P HIx.
Hypothesis USE : uselocale_stmt.
Hypothesis FREEL : freelocale_stmt HIx.

Definition xloc (a : Z) : Prop := s4_volatile a \/ (LOCCELL <= a < LOCCELL + 8).

#[using="Type"] Lemma heap_presx_of_munchx : forall X LB SP W m m',
munch W m m' -> wmono rsegs m m' ->
(forall a, 0 <= a < 2^64 -> client_addrx S4L X LB SP a -> outside W a) ->
heap_presx S4L X LB SP m m'.
Proof.
intros X LB SP W m m' MU WM HW a Ha Hc. split.
- apply MU. rewrite wa_unsigned by lia. apply HW; assumption.
- apply WM.
Qed.

#[using="Type"] Lemma client_outsidex : forall (X : Z -> Prop) A LB LB0 m md W SP,
HEAPx A LB m md ->
(forall b, In b LB0 -> In b LB) ->
alloc_ceiling <= SP ->
Forall (fun iv => (alloc_ceiling <= fst iv /\ snd iv <= SP)
\/ (exists a n, In (a, n) LB /\ ~ In (a, n) LB0 /\ a <= fst iv /\ snd iv <= a + n)
\/ (forall x, fst iv <= x < snd iv -> hl_scratch S4L x)
\/ (forall x, fst iv <= x < snd iv -> X x /\ hl_img_lo S4L <= x < hl_img_hi S4L)) W ->
forall a, 0 <= a < 2^64 -> client_addrx S4L X LB0 SP a -> outside W a.
Proof.
intros X A LB LB0 m md W SP HP Hsub HSP HW a Ha Hc.
induction W as [|[lo hi] W IH]; cbn; [exact I|].
apply Forall_cons_iff in HW as [H1 HW]. split; [| apply IH; exact HW]. cbn in H1.
assert (OLD : (alloc_ceiling <= lo /\ hi <= SP
\/ (exists a n, In (a, n) LB /\ ~ In (a, n) LB0 /\ a <= lo /\ hi <= a + n)
\/ (forall x, lo <= x < hi -> hl_scratch S4L x)) -> ~ (lo <= a < hi)).
{ intros H1'. pose proof (client_outside S4L HIx A LB LB0 m md [(lo, hi)] SP HP Hsub HSP
ltac:(apply Forall_cons; [exact H1' | apply Forall_nil]) a Ha (client_addrx_addr S4L _ _ _ _ Hc)) as Ho.
cbn in Ho. exact (proj1 Ho). }
destruct H1 as [H1 | [H1 | [H1 | Hx]]]; [apply OLD; tauto | apply OLD; tauto | apply OLD; tauto |].
intros Hin. destruct (Hx a Hin) as [HXa Himg]. cbn [hl_img_lo hl_img_hi S4L pf_mxd] in Himg. unfold alloc_ceiling, sp_window_lo, stack_max_size in HSP.
destruct Hc as [Hc | [[Hc HnX] | (b & Hb0 & Hbr)]]; [lia | exact (HnX HXa) |].
destruct b as [ba bn]. cbn in Hbr. pose proof (heap_blk_img S4L HIx _ _ _ _ _ _ HP (Hsub _ Hb0)) as Hbi. cbn [hl_img_lo hl_img_hi S4L pf_mxd] in Hbi. lia.
Qed.

#[using="Type"] Lemma frame_writes_okx : forall A LB m m' md W,
HEAPx A LB m md ->
munch W m m' ->
Forall (fun iv => (alloc_ceiling <= fst iv /\ snd iv <= hi_top S4L HIx)
\/ (exists a n, In (a, n) LB /\ a <= fst iv /\ snd iv <= a + n)
\/ (forall x, fst iv <= x < snd iv -> hl_scratch S4L x)
\/ (forall x, fst iv <= x < snd iv -> hl_client_static S4L x)) W ->
alloc_ceiling <= hi_top S4L HIx ->
forall a, 0 <= a < 2^64 -> ~ (client_addr S4L LB alloc_ceiling a /\ a < hi_top S4L HIx) -> ~ hl_scratch S4L a -> m' (wa a) = m (wa a).
Proof.
intros A LB m m' md W HP MU HW HTOP a Ha Hna Hns. apply MU. rewrite wa_unsigned by lia. clear MU.
induction W as [|[lo hi] W IH]; cbn; [exact I|].
apply Forall_cons_iff in HW as [H1 HW]. split; [| apply IH; exact HW].
cbn in H1. intros Hin. destruct H1 as [H1 | [(b & n & Hb & Hlo & Hhi) | [Hsc | Hcs]]].
- apply Hna. split; [left; lia | lia].
- apply Hna. pose proof (heap_blk S4L HIx _ _ _ _ _ _ HP Hb) as (_ & _ & _ & Hbhi & _). pose proof (hi_top_hi S4L HIx).
split; [| lia]. right; right. exists (b, n). split; [exact Hb| cbn; lia].
- apply Hns. apply Hsc. lia.
- apply Hna. pose proof (Hcs a ltac:(lia)) as Hc. pose proof (hl_static_in_img S4L a Hc) as Hi.
pose proof (hl_img_range S4L) as [_ Hh]. split; [right; left; exact Hc | lia].
Qed.

Definition pe_post_g (pf : pe_fix) (sv : pe_saved) (F : bvmap 5 word) (fc : bv 32) (md : Model)
(LBc : list blk) (me : word -> option byte) (lo : Z) (ms' : machine_state) (md' : Model) : Prop :=
exists m' (A' : AS S4L HIx) (gp : word) (r : Z) (errv' : word) (RBS TBS LK : list blk),
ret_statew S4L (pe_ra sv) (Z_to_bv 64 (pf_spf pf + PE_FRAME)) gp (Z_to_bv 64 0x77c00)
(pe_s0 sv) (pe_s1 sv) (pe_s2 sv) (pe_s3 sv) (pe_s4 sv) (pe_s5 sv) (pe_s6 sv) (pe_s7 sv) (pe_s8 sv) (pe_s9 sv) (pe_s10 sv) (pe_s11 sv)
F fc (Z_to_bv 64 r) m' ms' /\
model_vm_only md md' /\
stk rsegs m' lo (pf_spf pf + PE_FRAME) /\
rw_cells rsegs m' (0x77c00 - 164) [C4 errv'] /\
rw_cells rsegs m' LOCCELL [C8 (Z_to_bv 64 GLOBLOC)] /\
heap_presx S4L xloc LBc (pf_spf pf + PE_FRAME) me m' /\
HEAPx A' (RBS ++ TBS ++ LK ++ LBc) m' md' /\
tokrep_g rsegs S4F (pf_mxd pf) (pf_fl pf) m' TBS (pf_tk pf) /\
((r = 0 /\ RBS = []) \/ (r <> 0 /\ exists s, jval rsegs S4F s m' RBS r 1 /\ sdepth s <= 32)) /\
jc_glob_P m'.

Definition pe_post (pf : pe_fix) (sv : pe_saved) (F : bvmap 5 word) (fc : bv 32) (md : Model)
(LBc : list blk) (me : word -> option byte) (lo : Z) (ms' : machine_state) (md' : Model) : Prop :=
exists m' (A' : AS S4L HIx) (gp : word) (r : Z) (errv' : word) (RBS TBS LK : list blk),
ret_statew S4L (pe_ra sv) (Z_to_bv 64 (pf_spf pf + PE_FRAME)) gp (Z_to_bv 64 0x77c00)
(pe_s0 sv) (pe_s1 sv) (pe_s2 sv) (pe_s3 sv) (pe_s4 sv) (pe_s5 sv) (pe_s6 sv) (pe_s7 sv) (pe_s8 sv) (pe_s9 sv) (pe_s10 sv) (pe_s11 sv)
F fc (Z_to_bv 64 r) m' ms' /\
model_vm_only md md' /\
stk rsegs m' lo (pf_spf pf + PE_FRAME) /\
rw_cells rsegs m' (0x77c00 - 164) [C4 errv'] /\
rw_cells rsegs m' LOCCELL [C8 (Z_to_bv 64 GLOBLOC)] /\
heap_presx S4L xloc LBc (pf_spf pf + PE_FRAME) me m' /\
HEAPx A' (RBS ++ TBS ++ LK ++ LBc) m' md' /\
tokrep rsegs S4F m' TBS (pf_tk pf) /\
((r = 0 /\ RBS = []) \/ (r <> 0 /\ exists s, jval rsegs S4F s m' RBS r 1 /\ sdepth s <= 32)) /\
jc_glob_P m'.

#[using="Type"] Lemma pe_post_of_g32 : forall pf sv F fc md LBc me lo ms' md',
pf_mxd pf = 32 -> pf_fl pf = 0 ->
pe_post_g pf sv F fc md LBc me lo ms' md' -> pe_post pf sv F fc md LBc me lo ms' md'.
Proof.
intros pf sv F fc md LBc me lo ms' md' E32 E0 P.
destruct P as (m' & A' & gp & r & errv' & RBS & TBS & LK & RS & VM' & ST & ERR & LOC & HPR & HP & TR & REST).
exists m', A', gp, r, errv', RBS, TBS, LK. rewrite E32, E0 in TR.
repeat (split; [assumption|]). split; [apply (proj2 (tokrep_g32 rsegs S4F m' TBS (pf_tk pf))); exact TR | exact REST].
Qed.

#[using="Type"] Lemma lvl_weak_agree : forall BS m m' depth i l,
lvl_weak m depth i l -> agree_on rsegs BS m m' -> incl (lvl_blocks l) BS -> lvl_weak m' depth i l.
Proof.
intros BS m m' depth i l (B & J & N & C) AG Hi. split; [exact B|]. split.
- eapply (jopt_agree rsegs S4F); [exact J | exact AG | intros b Hb; apply Hi; unfold lvl_blocks; apply in_or_app; left; exact Hb].
- split; [| exact C]. destruct N as [N|N]; [left|right]; eapply (name_ok_agree rsegs); [exact N | exact AG | | exact N | exact AG |];
intros b Hb; apply Hi; unfold lvl_blocks; apply in_or_app; right; exact Hb.
Qed.

#[using="Type"] Lemma concat_lvl_blocks_nil : forall levels, (forall i l, nth_error levels i = Some l -> lvl_blocks l = []) -> concat (map lvl_blocks levels) = [].
Proof.
induction levels as [|l0 levels IH]; intros H; [reflexivity|]. cbn. rewrite (H 0%nat l0 eq_refl). cbn. apply IH.
intros i l Hl. exact (H (S i) l Hl).
Qed.



#[using="Type"] Lemma lvblocks_all_len : forall levels, Permutation (concat (map lvl_blocks levels)) (lvblocks levels (length levels)).
Proof.
intros levels. unfold lvblocks. rewrite firstn_all2 by lia. rewrite map_rev.
apply Permutation_concat. apply Permutation_rev.
Qed.

#[using="PUT"] Lemma out_success :
forall (m2 me : word -> option byte) (md2 md0 : Model) (A2 : AS S4L HIx) (T : TSet)
(tk newl len lenr sb spf q pb lo : Z) (pmd : Model) (mxd fl : Z) (depth : nat) (levels : list tlevel) (l : tlevel) (pbs objbs LBc LK : list blk)
(isd stpos choff errw ucs high : word) (quote : bv 8) (obj : Z) (cb : byte) (j1 j2 utf : list byte) (sv : pe_saved) (errv : word)
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC HIx (PEF tk LC_GLOBAL newl len lenr sb spf pmd mxd fl) lo ->
HEAPx A2 ((pbs ++ objbs ++ concat (map lvl_blocks levels)) ++ (tk, 72) :: (q, (32 * mxd)) :: LBc ++ LK) m2 md2 ->
length levels = Z.to_nat mxd -> (depth < Z.to_nat mxd)%nat -> nth_error levels depth = Some l ->
(forall i li, nth_error levels i = Some li -> lvl_weak m2 depth i li) ->
tstack rsegs m2 q levels ->
rw_cells rsegs m2 tk (tok_cells_g mxd fl pb (Z.of_nat depth) q (TS isd stpos choff errw ucs high quote)) ->
pe_frame rsegs m2 spf obj cb j1 j2 utf sv ->
pbuf rsegs m2 pbs pb -> pb <> 0 ->
stk rsegs m2 lo spf ->
rw_cells rsegs m2 (0x77c00 - 164) [C4 errv] ->
rw_cells rsegs m2 LOCCELL [C8 (Z_to_bv 64 GLOBLOC)] ->
heap_presx S4L xloc LBc (spf + 144) me m2 ->
bv_unsigned (pe_ra sv) mod 2 = 0 ->
model_vm_only md0 md2 ->
odep (tl_cs l) <= 32 ->
jc_glob_P m2 ->
(forall ms' md', pe_post_g (PEF tk LC_GLOBAL newl len lenr sb spf pmd mxd fl) sv F fc md0 LBc me lo ms' md' -> realizes rsegs (mkCfg ms' md') T) ->
realizes rsegs (mkCfg (MS (mkR x1 (Z_to_bv 64 spf) gp (Z_to_bv 64 0x77c00) t0 t1 t2 (Z_to_bv 64 tk) (Z_to_bv 64 LC_GLOBAL) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 newl) (Z_to_bv 64 lenr) s4 s5 s6 s7 s8 s9 s10 (Z_to_bv 64 PE_JTAB) t3 t4 t5 t6)
F (Z_to_bv 64 0x23f7c) fc None m2 (seg_rom rsegs)) md2) T.
Proof.
intros until fc. intros STC HP2 LEN32 D32 Hl LVW TSK TOK FR PB Hpb ST ERR LOC HPRX RAE VM0 DEPL JG2 K.
pose proof STC as (LO & LOS & SPA & HT & SP0 & LEN & SB0 & SBL). cbn [pf_spf pf_len pf_sb pf_md pf_mxd pf_fl] in LOS, SPA, HT, SP0, LEN, SB0, SBL.
pose proof (PE_STATIC_mxd _ _ _ STC) as [MXB _]. cbn [pf_mxd pf_fl] in MXB.
unfold PE_FRAME in HT. unfold_consts. pose proof (hi_top_hi S4L HIx) as HTH. unfold_consts.
set (CC := concat (map lvl_blocks levels)) in *.
set (LBall2 := (pbs ++ objbs ++ CC) ++ (tk, 72) :: (q, (32 * mxd)) :: LBc ++ LK) in *.
assert (INtk : In (tk, 72) LBall2) by (unfold LBall2; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, (32 * mxd)) LBall2) by (unfold LBall2; apply in_or_app; right; right; left; reflexivity).
pose proof (heap_blk S4L HIx _ _ _ _ tk 72 HP2 INtk) as (_ & Htal & Htlo & Hthi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ tk 72 HP2 INtk) as Himg_t. cbn [hl_img_lo hl_img_hi S4L pf_mxd] in Himg_t.
pose proof (heap_blk S4L HIx _ _ _ _ q (32 * mxd) HP2 INq) as (_ & Hqal & Hqlo & Hqhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ q (32 * mxd) HP2 INq) as Himg_q. cbn [hl_img_lo hl_img_hi S4L pf_mxd] in Himg_q.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hthi, Hqhi.
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2.
pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI2. cbn [hl_segs S4L pf_mxd] in MI2.
pose proof (heap_blk_nodup S4L HIx _ _ _ _ HP2) as ND.
assert (Htq : tk <> q).
{ generalize ND; intros ND'. unfold LBall2 in ND'. rewrite !map_app in ND'. apply NoDup_app_remove_l in ND'.
cbn [map blk_addr fst app pf_mxd] in ND'. apply List.NoDup_cons_iff in ND' as [Hni _]. intros E. apply Hni. left. symmetry. exact E. }
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ tk 72 q (32 * mxd) HP2 INtk INq Htq) as Hdtq.

pose proof (TSK depth l Hl) as Ld. unfold srec_cells in Ld. remember (q + 32 * Z.of_nat depth) as bse eqn:Hbse.
pose proof (LVW depth l Hl) as (_ & JO & NM & _).

set (LV := lvblocks levels depth).
assert (PCC : Permutation CC (tl_cbs l ++ tl_nbs l ++ LV)).
{ unfold CC. eapply Permutation_trans; [apply lvblocks_all_len|].
rewrite (lvblocks_trunc levels (S depth)); [| | lia].
- rewrite (lvblocks_S _ _ _ Hl). unfold lvl_blocks. rewrite <- app_assoc. apply Permutation_refl.
- intros j lj Hj Hkj. destruct (LVW j lj Hj) as (_ & _ & _ & C). apply C. lia. }
set (P := LV ++ pbs ++ objbs ++ LK). set (REST := P ++ (tk, 72) :: (q, (32 * mxd)) :: LBc).
assert (HP2' : HEAPx A2 (lvl_blocks l ++ REST) m2 md2).
{ eapply (heap_perm S4L HIx); [exact HP2|]. unfold LBall2, REST, P.
eapply Permutation_trans; [apply Permutation_app_tail; apply Permutation_app_head; apply Permutation_app_head; exact PCC|].
unfold lvl_blocks. perm. }
assert (NC : forall a k, In (a, k) (tl_cbs l) -> ~ In (a, k) LBc /\ In (a, k) LBall2 /\ a <> tk /\ a <> q /\ (forall k', ~ In (a, k') pbs)).
{ intros a k Hin.
assert (HinC : In (a, k) CC) by (eapply Permutation_in; [apply Permutation_sym; exact PCC | apply in_or_app; left; exact Hin]).
assert (HinL : In (a, k) LBall2) by (unfold LBall2; apply in_or_app; left; apply in_or_app; right; apply in_or_app; right; exact HinC).
assert (PERM : Permutation LBall2 (tl_cbs l ++ (tk, 72) :: (q, (32 * mxd)) :: pbs ++ LBc ++ (tl_nbs l ++ LV ++ objbs ++ LK))).
{ unfold LBall2. eapply Permutation_trans; [apply Permutation_app_tail; apply Permutation_app_head; apply Permutation_app_head; exact PCC|]. perm. }
pose proof (Permutation_NoDup (Permutation_map blk_addr PERM) ND) as NDx. rewrite map_app in NDx. cbn [map pf_mxd] in NDx.
pose proof (in_map blk_addr _ _ Hin) as Ha.
pose proof (fun Hr => NoDup_app_in2 _ _ (blk_addr (a, k)) NDx Ha Hr) as OUT. cbn [blk_addr fst pf_mxd] in OUT.
split; [| split; [exact HinL | split; [| split]]].
- intros Hc. apply OUT. right; right. rewrite !map_app. apply in_or_app; right. apply in_or_app; left. exact (in_map blk_addr _ _ Hc).
- intros ->. apply OUT. left; reflexivity.
- intros ->. apply OUT. right; left; reflexivity.
- intros k' Hp. apply OUT. right; right. rewrite !map_app. apply in_or_app; left. exact (in_map blk_addr _ _ Hp). }

assert (FINISH : forall (m5 : word -> option byte) (md5 : Model) (A5 : AS S4L HIx) (F5 : bvmap 5 word) (fc5 : bv 32) (levels5 : list tlevel)
(y1 u0 u1 u2 w0 v1 v2 v3 v4 v5 v6 v7 z2 z3 z4 s5' s6' s7' s8' s9' s10' s11' u3 u4 u5 u6 : word),
fsaved F F5 -> (frm0 fc -> frm0 fc5) -> model_vm_only md2 md5 ->
HEAPx A5 ((pbs ++ objbs ++ LK ++ tl_cbs l) ++ (tk, 72) :: (q, (32 * mxd)) :: LBc) m5 md5 ->
length levels5 = Z.to_nat mxd ->
(forall j, (j <= depth)%nat -> nth_error levels5 j = Some lvl_reset) ->
(forall j, (depth < j)%nat -> nth_error levels5 j = nth_error levels j) ->
tstack rsegs m5 q levels5 ->
rw_cells rsegs m5 tk (tok_cells_g mxd fl pb (Z.of_nat depth) q (TS isd stpos choff errw ucs high quote)) ->
pe_frame rsegs m5 spf obj cb j1 j2 utf sv ->
stk rsegs m5 lo spf ->
heap_presx S4L xloc LBc (spf + 144) me m5 ->
rw_cells rsegs m5 (0x77c00 - 164) [C4 errv] ->
rw_cells rsegs m5 LOCCELL [C8 (Z_to_bv 64 GLOBLOC)] ->
pbuf rsegs m5 pbs pb ->
jopt rsegs S4F (tl_cs l) m5 (tl_cbs l) (tl_cur l) ->
jc_glob_P m5 ->
evt rsegs (RZ rsegs md5 T)
(MS (mkR y1 (Z_to_bv 64 spf) gp (Z_to_bv 64 0x77c00) u0 u1 u2 (Z_to_bv 64 tk) z2 w0 v1 v2 v3 v4 v5 v6 v7
(Z_to_bv 64 (tl_cur l)) z3 z4 s5' s6' s7' s8' s9' s10' s11' u3 u4 u5 u6)
F5 (Z_to_bv 64 0x23fe8) fc5 None m5 (seg_rom rsegs))).
{ intros until u6. intros FS5 FRM5 VM5 HP5 LEN5 RES5 SAME5 TS5 TOK5 FR5 ST5 HPRX5 ERR5 LOC5 PB5 JOP5 JG5.
bst. bst.
eapply (pe_epilogue _ _ [C8 _; CB 16 _; C4 _; CB 3 _; C1 _; CB 8 _]); [exact FR5 | reflexivity | lia | lia | exact RAE |].
apply K. unfold pe_post_g, PE_FRAME. cbn [pf_spf pf_tk pf_md pf_mxd pf_fl].
assert (CC5 : concat (map lvl_blocks levels5) = []).
{ apply concat_lvl_blocks_nil. intros i li Hli.
destruct (Nat.le_gt_cases i depth) as [Hle | Hgt].
- rewrite (RES5 i Hle) in Hli. injection Hli as <-. reflexivity.
- rewrite (SAME5 i Hgt) in Hli. destruct (LVW i li Hli) as (_ & _ & _ & C). apply lvl_clean_blocks. apply C. exact Hgt. }
unfold pe_frame in FR5.
lazymatch type of FR5 with rw_cells _ _ _ ?CS => pose proof (stk_release rsegs m5 lo spf CS ST5 FR5 ltac:(lia)) as STx end.
change (Z.of_nat (cells_size _)) with 144 in STx.
exists m5, A5, gp, (tl_cur l), errv, (tl_cbs l), ((tk, 72) :: (q, (32 * mxd)) :: pbs ++ concat (map lvl_blocks levels5)), (objbs ++ LK).
split; [apply ret_statew_intro; [exact FS5 | exact FRM5]|].
split; [eapply model_vm_only_trans; [exact VM0 | exact VM5]|]. split; [exact STx|]. split; [exact ERR5|]. split; [exact LOC5|]. split; [exact HPRX5|].
split; [eapply (heap_perm S4L HIx); [exact HP5 | rewrite CC5; perm]|].
split; [| split; [| exact JG5]].
- exists q, pb, (Z.of_nat depth), pbs, levels5, (TS isd stpos choff errw ucs high quote).
split; [reflexivity|]. split; [rewrite LEN5; lia|]. split; [lia|].
split; [exact TOK5|]. split; [exact PB5|]. split; [exact Hpb|]. split; [exact TS5|]. split.
+ intros i li Hli Hile. rewrite (RES5 i ltac:(lia)) in Hli. injection Hli as <-. apply lvl_clean_ok. repeat split.
+ intros i li Hli Hlt. rewrite (SAME5 i ltac:(lia)) in Hli. destruct (LVW i li Hli) as (_ & _ & _ & C). apply C. lia.
- revert DEPL. destruct (tl_cs l) as [s'|]; cbn [jopt odep pf_mxd] in JOP5 |- *; intros DEPL.
+ right. split; [exact (proj1 JOP5) | exists s'; split; [exact (proj2 JOP5) | exact DEPL]].
+ left. destruct JOP5 as [H0 Hn]. rewrite H0, Hn. split; reflexivity. }

assert (TAIL : forall (m3 : word -> option byte) (a1x a2x a3x a4x : word),
HEAPx A2 (lvl_blocks l ++ REST) m3 md2 ->
match tl_cs l with Some s' => tl_cur l <> 0 /\ jval rsegs S4F s' m3 (tl_cbs l) (tl_cur l) 2 | None => tl_cur l = 0 /\ tl_cbs l = [] end ->
(forall j lj, nth_error levels j = Some lj -> (j < depth)%nat -> lvl_ok rsegs S4F m3 lj) ->
tstack rsegs m3 q levels ->
rw_cells rsegs m3 tk [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 pb); C4 (Z_to_bv 64 mxd); C4 (Z_to_bv 64 (Z.of_nat depth)); C4 isd; C4 stpos;
C4 choff; C4 errw; C4 ucs; C4 high; C1 quote; CB 7 (repeat (Z_to_bv 8 0) 7); C8 (Z_to_bv 64 q); C4 (Z_to_bv 64 fl); C4 (Z_to_bv 64 0)] ->
pe_frame rsegs m3 spf obj cb j1 j2 utf sv ->
stk rsegs m3 lo spf ->
rw_cells rsegs m3 (0x77c00 - 164) [C4 errv] ->
rw_cells rsegs m3 LOCCELL [C8 (Z_to_bv 64 GLOBLOC)] ->
pbuf rsegs m3 pbs pb ->
heap_presx S4L xloc LBc (spf + 144) me m3 ->
mem_inv rsegs m3 ->
jc_glob_P m3 ->
evt rsegs (RZ rsegs md2 T)
(MS (mkR (Z_to_bv 64 0x23fc0) (Z_to_bv 64 spf) gp (Z_to_bv 64 0x77c00) t0 t1 t2 (Z_to_bv 64 tk) (Z_to_bv 64 LC_GLOBAL) (Z_to_bv 64 (tl_cur l)) a1x a2x a3x a4x a5 a6 a7
(Z_to_bv 64 newl) (Z_to_bv 64 lenr) s4 s5 s6 s7 s8 s9 s10 (Z_to_bv 64 PE_JTAB) t3 t4 t5 t6)
F (Z_to_bv 64 0x23fc0) fc None m3 (seg_rom rsegs))).
{ intros m3 a1x a2x a3x a4x HP3 JO3 LOK3 TS3 TOK3 FR3 ST3 ERR3 LOC3 PB3 HPRX3 MI3 JG3. unfold pe_frame in FR3.
bst. norm_sx32. bst. if_truex.
bst. bst. bst. bst. bst.
apply evt_RZ_done.
eapply (reset_level_cps HIx PUT depth) with (l := l) (levels := levels) (P := P) (LB0 := LBc) (REST := REST) (lo := lo) (errv := errv)
(q := q) (r := tk) (pb := pb) (depth := Z.of_nat depth) (mxd := mxd) (fl := fl) (x := TS isd stpos choff errw ucs high quote) (rc := 2) (me := m3);
[ exact Hl | lia | exact MXB | exact LEN32 | exact HP3 | reflexivity
| unfold put_pre; destruct (tl_cs l) as [s'|]; [destruct JO3 as [Hp J]; split; [exact Hp | split; [lia | exact J]] | exact JO3]
| | exact TS3 | unfold tok_cells, tok_cells_g; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd]; exact TOK3
| rewrite unsigned_lit by lia; exact ST3 | clia | rewrite unsigned_lit by lia; unfold RESET_STK, put_stk_P; lia
| rewrite unsigned_lit by lia; exact SPA | rewrite unsigned_lit by lia; lia
| apply heap_pres_refl | exact ERR3 | rewrite unsigned_lit by lia; reflexivity | ].
{ destruct NM as [N|N]; cbn [name_ok pf_mxd] in N; [left; exact N | right]. destruct N as (Hn & nn & ks & E & _). split; [exact Hn | exists nn; exact E]. }
intros ms4 md4 (m4 & A4 & rv & RS4 & VM4 & OUT4 & TS4 & TOK4 & ST4 & HPR4s & ERR4 & AGP4).
destruct RS4 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F4 & fc4 & -> & FS4 & FRM4).
rewrite ?unsigned_lit in ST4 by lia. rewrite ?unsigned_lit in HPR4s by lia.
lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?n)] => replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia | reflexivity]) end.
assert (HPR4 : heap_pres S4L LBc (spf + 144) m3 m4) by (eapply heap_pres_weaken; [exact HPR4s | lia | intros b Hb; exact Hb]).
assert (FR4 : po_frame m4 spf obj cb j1 j2 utf sv).
{ unfold po_frame, pe_frame. eapply (heap_pres_rw_cells S4L); [exact HPR4s | exact FR3 | left; cbn; lia]. }
assert (HJ4 : HEAPx A4 (tl_cbs l ++ REST) m4 md4 /\ jopt rsegs S4F (tl_cs l) m4 (tl_cbs l) (tl_cur l)).
{ destruct OUT4 as [(Hcs & H) | (s' & Hs & _ & J & H)].
- destruct Hcs as [Hcs | Hcs]; [| lia]. rewrite Hcs in JO3 |- *. destruct JO3 as [Hc0 Ecbs]. rewrite Ecbs. split; [exact H | split; [exact Hc0 | reflexivity]].
- rewrite Hs in JO3 |- *. cbn [jopt]. split; [exact H | split; [exact (proj1 JO3) | exact J]]. }
destruct HJ4 as [HP4 JOP4].
pose proof (heap_model_ok _ _ _ _ _ _ HP4) as MOK4.
assert (LOC4 : rw_cells rsegs m4 LOCCELL [C8 (Z_to_bv 64 GLOBLOC)]).
{ eapply (heap_pres_rw_cells S4L); [exact HPR4 | exact LOC3 | right; left; cbn; intros z Hz; exact (proj1 ((ltac:(intros a Ha; unfold LOCCELL in Ha; cbn [hl_client_static S4L pf_mxd]; unfold s4_client_static, s4_volatile; lia)
: forall a, LOCCELL <= a < LOCCELL + 8 -> hl_client_static S4L a /\ ~ s4_volatile a) z Hz))]. }
assert (PB4 : pbuf rsegs m4 pbs pb).
{ eapply pbuf_agree; [exact PB3 | exact AGP4 | intros b Hb; unfold P; apply in_or_app; right; apply in_or_app; left; exact Hb]. }
assert (HPRX4 : heap_presx S4L xloc LBc (spf + 144) me m4).
{ eapply heap_presx_trans; [exact HPRX3 | apply heap_pres_presx; exact HPR4]. }
apply rz_evt; [exact MOK4|].
destruct (Nat.eq_dec depth 0) as [D0 | Dn].
-
rewrite D0. cbn [Z.of_nat]. bst. norm_w32. bst. if_false.
eapply FINISH; [exact FS4 | exact FRM4 | exact VM4 | | rewrite lupd_length; exact LEN32 | | | exact TS4 | exact TOK4
| unfold po_frame in FR4; exact FR4 | exact ST4 | exact HPRX4 | exact ERR4 | exact LOC4 | exact PB4 | exact JOP4 | exact (jc_glob_P_pres _ _ _ _ HPR4 JG3)].
+ eapply (heap_perm S4L HIx); [exact HP4|]. unfold REST, P, LV. rewrite D0, lvblocks_0. perm.
+ intros j Hj. replace j with depth by lia. apply nth_error_lupd_eq. lia.
+ intros j Hj. apply nth_error_lupd_neq. lia.
-
destruct depth as [|dp]; [lia|].
bst. norm_w32. bst. if_truex.
replace (Z.of_nat (S dp) + -1) with (Z.of_nat dp) by lia.
apply evt_RZ_done.
eapply (peout_loop HIx mxd fl MXB PUT dp) with (PBS := pbs ++ objbs ++ LK ++ tl_cbs l) (LB0 := LBc) (me := m3) (levels := lupd levels (S dp) lvl_reset);
[lia | rewrite lupd_length; exact LEN32 | | | exact TS4 | exact TOK4 | exact FR4 | exact ST4 | clia | unfold RESET_STK, put_stk_P; lia | exact SPA | lia | lia
| exact HPR4 | exact ERR4 | reflexivity |].
+ eapply (heap_perm S4L HIx); [exact HP4|]. unfold REST, P, LV. rewrite lvblocks_lupd_ge by lia. perm.
+ intros j lj Hj Hji. rewrite nth_error_lupd_neq in Hj by lia.
eapply lvl_ok_agree; [exact (LOK3 j lj Hj ltac:(lia)) | exact AGP4 |].
intros b Hb. unfold P, LV. apply in_or_app; left. eapply (lvblocks_incl levels (S dp) j lj Hj ltac:(lia)). unfold lvl_blocks. apply in_or_app; left. exact Hb.
+ intros ms5 md5 (m5 & A5 & F5 & fc5 & levels5 & y1' & u0' & u1' & u2' & w0' & v1' & v2' & v3' & v4' & v5' & v6' & v7' & u3' & u4' & u5' & u6' & s2' & -> & FS5 & FRM5 & VM5 & HP5 & LEN5 & RES5 & SAME5 & TS5 & TOK5 & FR5 & ST5 & HPR5 & ERR5 & AG5).
pose proof (heap_model_ok _ _ _ _ _ _ HP5) as MOK5. apply rz_evt; [exact MOK5|].
eapply FINISH; [eapply fsaved_trans; [exact FS4 | exact FS5] | intros Hf; exact (FRM5 (FRM4 Hf)) | eapply model_vm_only_trans; [exact VM4 | exact VM5]
| exact HP5 | exact LEN5 | | | exact TS5 | exact TOK5 | unfold po_frame in FR5; exact FR5 | exact ST5
| eapply heap_presx_trans; [exact HPRX3 | apply heap_pres_presx; exact HPR5] | exact ERR5 | | | | exact (jc_glob_P_pres _ _ _ _ HPR5 JG3)].
* intros j Hj. destruct (Nat.eq_dec j (S dp)) as [->|NE]; [rewrite SAME5 by lia; apply nth_error_lupd_eq; lia | apply RES5; lia].
* intros j Hj. rewrite SAME5 by lia. apply nth_error_lupd_neq. lia.
* eapply (heap_pres_rw_cells S4L); [exact HPR5 | exact LOC3 | right; left; cbn; intros a Ha; unfold LOCCELL in Ha; cbn [hl_client_static S4L pf_mxd]; unfold s4_client_static; lia].
* eapply pbuf_agree; [exact PB4 | exact AG5 | intros b Hb; apply in_or_app; left; exact Hb].
* eapply (jopt_agree rsegs S4F); [exact JOP4 | exact AG5 | intros b Hb; apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; exact Hb]. }

assert (LOK2 : forall j lj, nth_error levels j = Some lj -> (j < depth)%nat -> lvl_ok rsegs S4F m2 lj).
{ intros j lj Hj Hjd. destruct (LVW j lj Hj) as (_ & J & N & _). split; [exact J|].
destruct N as [N|N]; cbn [name_ok pf_mxd] in N; [left; exact N | right]. destruct N as (Hn & nn & ks & E & _). split; [exact Hn | exists nn; exact E]. }
unfold tok_cells, tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in TOK. unfold pe_frame in FR.
assert (Hbal : bse mod 16 = 0) by (subst bse; clear - Hqal; Z.div_mod_to_equations; lia).
assert (Hbal2 : (q + Z.of_nat depth * 32) mod 16 = 0) by (clear - Hqal; Z.div_mod_to_equations; lia).
apply rz_evt; [exact MOK2|].
bst. norm_sx32. bst. bst.
rewrite (unsigned_lit (Z.of_nat depth)) by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32.
tk2_skip. replace (q + Z.of_nat depth * 32) with bse by lia.
bst. bst.
destruct (tl_cs l) as [s'|] eqn:Ecs.
-
cbn [jopt pf_mxd] in JO. destruct JO as [Hc J].
assert (NDc : List.NoDup (map blk_addr (tl_cbs l))).
{ assert (PERM : Permutation LBall2 (tl_cbs l ++ (tk, 72) :: (q, (32 * mxd)) :: pbs ++ LBc ++ (tl_nbs l ++ LV ++ objbs ++ LK))).
{ unfold LBall2. eapply Permutation_trans; [apply Permutation_app_tail; apply Permutation_app_head; apply Permutation_app_head; exact PCC|]. perm. }
pose proof (Permutation_NoDup (Permutation_map blk_addr PERM) ND) as NDx. rewrite map_app in NDx. apply NoDup_app_remove_r in NDx. exact NDx. }
destruct (jval_hdr rsegs S4F s' m2 (tl_cbs l) (tl_cur l) 1 J NDc) as (n & tojs & pb' & udel & ud & rest & INc & SZ & N48 & HDR & CLOSE).
destruct (NC _ _ INc) as (NCc & INcL & Hctk & Hcq & NCp).
pose proof (heap_blk S4L HIx _ _ _ _ (tl_cur l) n HP2 INcL) as (_ & Hcal & Hc0 & Hchi & _). unfold alloc_ceiling, sp_window_lo, stack_max_size in Hchi.
pose proof (heap_blk_img S4L HIx _ _ _ _ (tl_cur l) n HP2 INcL) as Himg_c. cbn [hl_img_lo hl_img_hi S4L pf_mxd] in Himg_c.
eapply evt_cut; [eapply jo_get_P; [exact HDR | lia | lia | exact Hcal | lia | lia | exact MI2] |].
intros ms1 (mg & (w & ->) & MUg & WMg & MIg & HDR1).
replace (ret_pc (Z_to_bv 64 0x23fc0)) with (Z_to_bv 64 0x23fc0) by (symmetry; apply ret_pc_even; [lia | reflexivity]).

assert (DJ : forall a k, In (a, k) LBall2 -> a <> tl_cur l -> disjoint_from [(tl_cur l + 4, tl_cur l + 8)] a k).
{ intros a k Hin Hne. pose proof (heap_blk_disjoint S4L HIx _ _ _ _ a k (tl_cur l) n HP2 Hin INcL Hne).
pose proof (heap_blk S4L HIx _ _ _ _ a k HP2 Hin) as (Hk0 & _). cbn. (clear - N48 H; lia). }
apply (TAIL mg w _ _ _).
+ eapply (heap_frame S4L HIx); [exact HP2' | | exact WMg | exact MIg].
eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HP2' MUg). apply Forall_cons; [| apply Forall_nil]. cbn [fst snd pf_mxd].
right; left. exists (tl_cur l), n. split; [apply in_or_app; left; unfold lvl_blocks; apply in_or_app; left; exact INc | lia].
+ split; [exact Hc|]. apply (CLOSE mg 2 HDR1). eapply (agree_others_gen rsegs); [exact MUg | exact WMg |].
intros a k Hin Hne. apply (DJ a k); [| exact Hne]. destruct (NC _ _ Hin) as (_ & HinL & _). exact HinL.
+ intros j lj Hj Hjd. eapply lvl_ok_agree; [exact (LOK2 j lj Hj Hjd) | eapply agree_of_munch; [exact MUg | exact WMg |] | apply incl_refl].
intros a k Hin. apply DJ.
* unfold LBall2. apply in_or_app; left. apply in_or_app; right. apply in_or_app; right.
eapply Permutation_in; [apply Permutation_sym; exact PCC|]. apply in_or_app; right. apply in_or_app; right.
eapply (lvblocks_incl levels depth j lj Hj Hjd). unfold lvl_blocks. apply in_or_app; left. exact Hin.
* intros ->.
pose proof (Permutation_NoDup (Permutation_map blk_addr PCC)
ltac:(generalize ND; intros ND'; unfold LBall2 in ND'; rewrite !map_app in ND';
apply NoDup_app_remove_r in ND'; apply NoDup_app_remove_l in ND'; apply NoDup_app_remove_l in ND'; exact ND')) as NDC.
rewrite !map_app in NDC.
eapply (NoDup_app_in2 _ _ (tl_cur l) NDC); [exact (in_map blk_addr _ _ INc)|].
apply in_or_app; right. refine (in_map blk_addr _ (tl_cur l, k) _). eapply (lvblocks_incl levels depth j lj Hj Hjd). unfold lvl_blocks. apply in_or_app; left. exact Hin.
+ eapply (tstack_transport rsegs); [exact TSK | exact MUg | exact WMg |]. intros j Hj. rewrite LEN32 in Hj.
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ q (32 * mxd) (tl_cur l) n HP2 INq INcL ltac:(congruence)). cbn. (clear - N48 Hj H; lia).
+ eapply rw_cells_transport; [exact TOK | exact MUg | exact WMg |].
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ tk 72 (tl_cur l) n HP2 INtk INcL ltac:(congruence)). cbn. lia.
+ unfold pe_frame. eapply rw_cells_transport; [exact FR | exact MUg | exact WMg |]. cbn. lia.
+ eapply stk_transport; [exact ST | exact MUg | exact WMg |]. intros z Hz. left. cbn. lia.
+ eapply rw_cells_transport; [exact ERR | exact MUg | exact WMg |]. cbn. lia.
+ eapply rw_cells_transport; [exact LOC | exact MUg | exact WMg |]. unfold LOCCELL. cbn. lia.
+ eapply pbuf_agree; [exact PB | eapply agree_of_munch; [exact MUg | exact WMg |] | apply incl_refl].
intros a k Hin. apply DJ; [unfold LBall2; apply in_or_app; left; apply in_or_app; left; exact Hin | intros ->; exact (NCp _ Hin)].
+ eapply heap_presx_trans; [exact HPRX|]. eapply heap_presx_of_munchx; [exact MUg | exact WMg |].
eapply (client_outsidex xloc); [exact HP2 | intros b Hb; unfold LBall2; apply in_or_app; right; right; right; apply in_or_app; left; exact Hb | clia |].
apply Forall_cons; [| apply Forall_nil]. cbn [fst snd pf_mxd]. right; left. exists (tl_cur l), n. split; [exact INcL|]. split; [exact NCc | lia].
+ exact MIg.
+ eapply jc_glob_P_outside; [exact JG2 | exact MUg | exact WMg |]. apply Forall_cons; [cbn [fst snd pf_mxd]; lia | apply Forall_nil].
-
cbn [jopt pf_mxd] in JO. destruct JO as [Hc0 Ecbs].
eapply evt_cut; [rewrite Hc0; apply jo_get_null_P |]. intros ms1 ->.
replace (ret_pc (Z_to_bv 64 0x23fc0)) with (Z_to_bv 64 0x23fc0) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
rewrite <- Hc0.
apply (TAIL m2 _ _ _ _);
[exact HP2' | split; [exact Hc0 | exact Ecbs] | exact LOK2 | exact TSK | exact TOK | unfold pe_frame; exact FR | exact ST | exact ERR | exact LOC | exact PB | exact HPRX | exact MI2 | exact JG2].
Qed.
#[using="PUT USE FREEL"] Lemma seg_out :
forall (pf : pe_fix) (q : Z) (LBc : list blk) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (ts : tstate) (LK : list blk)
(cb : byte) (j1 j2 utf : list byte) (sv : pe_saved) (errv : word) (T : TSet) (cop cur0 : Z)
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC HIx pf lo ->
PE_INVW HIx pf q ((pf_newl pf, 48) :: LBc) payload me lo m md A ts LK cb j1 j2 utf sv errv ->
tdepth_ok ts ->
pf_oldl pf = LC_GLOBAL ->
rw_cells rsegs me LOCCELL [C8 (Z_to_bv 64 cur0)] -> 0 <= cur0 < 2^64 ->
bv_unsigned (pe_ra sv) mod 2 = 0 ->
(forall ms' md', pe_post_g pf sv F fc md LBc me lo ms' md' -> realizes rsegs (mkCfg ms' md') T) ->
realizes rsegs (mkCfg (pe_ms7 rsegs pf PE_OUT cop x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 s10 t3 t4 t5 t6 F fc m) md) T.
Proof.
intros until fc. intros STC INV TDOK OLDL LOC0 CUR0 RAE K.
pose proof STC as (LO & LOS & SPA & HT & SP0 & LEN & SB0 & SBL).
destruct INV as (CORE & BASE & LVW).
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof BASE as (HP & ST & ERR & STR & PLEN & SBin & HPR & MDV & JCG).
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl_]; pe_gen fl_; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *. subst oldl.
unfold_consts. unfold PE_FRAME in *.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
set (LB0 := (newl, 48) :: LBc) in *.
set (LBall := pe_blocks (PEF tk LC_GLOBAL newl len lenr sb spf pmd mxd fl) q LB0 ts0 ++ LK) in *.
assert (INtk : In (tk, 72) LBall) by (unfold LBall, pe_blocks; apply in_or_app; left; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, (32 * mxd)) LBall) by (unfold LBall, pe_blocks; apply in_or_app; left; apply in_or_app; right; right; left; reflexivity).
assert (INd : In (newl, 48) LBall) by (unfold LBall, pe_blocks; apply in_or_app; left; apply in_or_app; right; right; right; left; reflexivity).
pose proof (heap_blk S4L HIx _ _ _ _ tk 72 HP INtk) as (_ & Htal & Htlo & Hthi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ tk 72 HP INtk) as Himg_t. cbn [hl_img_lo hl_img_hi S4L pf_mxd] in Himg_t.
pose proof (heap_blk S4L HIx _ _ _ _ q (32 * mxd) HP INq) as (_ & Hqal & Hqlo & Hqhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ q (32 * mxd) HP INq) as Himg_q. cbn [hl_img_lo hl_img_hi S4L pf_mxd] in Himg_q.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hthi, Hqhi.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L pf_mxd] in MI.
pose proof (heap_blk_nodup S4L HIx _ _ _ _ HP) as ND.
assert (Htq : tk <> q).
{ generalize ND; intros ND'. unfold LBall, pe_blocks in ND'. rewrite !map_app in ND'. apply NoDup_app_remove_r in ND'. apply NoDup_app_remove_l in ND'.
cbn [map blk_addr fst pf_tk pf_md pf_mxd pf_fl] in ND'. apply List.NoDup_cons_iff in ND' as [Hni _]. intros E. apply Hni. left. symmetry. exact E. }
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ tk 72 q (32 * mxd) HP INtk INq Htq) as Hdtq.

destruct (nth_error levels depth) as [l|] eqn:Hl; [| apply nth_error_None in Hl; lia].
pose proof (TSK depth l Hl) as Ld. unfold srec_cells in Ld.
pose proof (LVW depth l Hl) as (JO & NM & _).
pose proof (LVW depth l Hl) as ([ST26 SS26] & _).
pose proof (bytes_at_bound _ _ _ _ STR) as SBB. pose proof (hi_top_hi S4L HIx) as HTH. unfold_consts.

assert (LOCcs : forall a, LOCCELL <= a < LOCCELL + 8 -> hl_client_static S4L a /\ ~ s4_volatile a).
{ intros a Ha. unfold LOCCELL in Ha. cbn [hl_client_static S4L pf_mxd]. unfold s4_client_static, s4_volatile. lia. }
assert (LOCm : rw_cells rsegs m LOCCELL [C8 (Z_to_bv 64 cur0)]).
{ eapply (heap_presx_rw_cells S4L); [exact HPR | exact LOC0 | right; left; cbn; exact LOCcs]. }
stash PB. stash HPR. clear BASE.

apply rz_evt; [exact MOK|].
eapply out_checks; [unfold tok_cells, tok_cells_g; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd]; exact TOK | exact FR | exact Ld
| exact D32 | lia | lia | lia | lia | lia | lia | lia | lia | lia | exact Hdtq | exact ST26 | exact SS26 | exact Hqal | exact MI |].
intros mc a0' a1' a2' a3' a4' a5' a6' a7' errf TOKc MUc WMc MIc.

bst. bst.
assert (LOCmc : rw_cells rsegs mc LOCCELL [C8 (Z_to_bv 64 cur0)]).
{ eapply rw_cells_transport; [exact LOCm | exact MUc | exact WMc |]. unfold LOCCELL. cbn. lia. }
eapply evt_cut; [eapply USE; [exact LOCmc | exact CUR0 | unfold LC_GLOBAL; lia | reflexivity | exact MIc] |].
intros ms1 (m1 & a1x & a2x & a3x & a4x & -> & MU1 & WM1 & MI1 & LOC1).
replace (ret_pc (Z_to_bv 64 0x23f64)) with (Z_to_bv 64 0x23f64) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
replace (usl_new cur0 LC_GLOBAL) with GLOBLOC in LOC1
by (unfold usl_new, LC_GLOBAL; destruct (Z.eqb_spec (2^64 - 1) 0); [lia|]; rewrite Z.eqb_refl; reflexivity).

assert (MU01 : munch [(tk + 36, tk + 40); (LOCCELL, LOCCELL + 8)] m m1).
{ eapply munch_trans; [eapply munch_weaken; [| exact MUc] | eapply munch_weaken; [| exact MU1]]; intros z Hz; cbn in Hz |- *; clear - Hz; tauto.    }
pose proof (wmono_trans _ _ _ _ WMc WM1) as WM01.
assert (HP1 : HEAPx A LBall m1 md).
{ eapply (heap_frame S4L HIx); [exact HP | | exact WM01 | exact MI1].
eapply frame_writes_okx; [exact HP | exact MU01 | | clia].
apply Forall_cons; [right; left; exists tk, 72; split; [exact INtk | cbn; lia] |].
apply Forall_cons; [right; right; right; cbn [fst snd pf_mxd]; intros z Hz; exact (proj1 (LOCcs z Hz)) | apply Forall_nil]. }
assert (ST1 : stk rsegs m1 lo spf).
{ eapply stk_transport; [exact ST | exact MU01 | exact WM01 |]. intros z Hz. left. unfold LOCCELL. cbn. lia. }
assert (ERR1 : rw_cells rsegs m1 (0x77c00 - 164) [C4 errv]).
{ eapply rw_cells_transport; [exact ERR | exact MU01 | exact WM01 |]. unfold LOCCELL. cbn. lia. }
assert (TOK1 : rw_cells rsegs m1 tk (tok_cells_g mxd fl pb (Z.of_nat depth) q (TS isd stpos (Z_to_bv 64 co) errf ucs high quote))).
{ eapply rw_cells_transport; [exact TOKc | exact MU1 | exact WM1 |]. unfold LOCCELL. cbn. lia. }
assert (FR1 : pe_frame rsegs m1 spf obj cb j1 j2 utf sv).
{ unfold pe_frame in FR |- *. eapply rw_cells_transport; [exact FR | exact MU01 | exact WM01 |]. unfold LOCCELL. cbn. lia. }
assert (TSK1 : tstack rsegs m1 q levels).
{ eapply (tstack_transport rsegs); [exact TSK | exact MU01 | exact WM01 |]. intros j Hj. rewrite LEN32 in Hj. unfold LOCCELL. cbn. lia. }
clear TOK TOKc FR Ld LOCm LOCmc MUc WMc MIc MU1 WM1.

bst. bst.
apply evt_RZ_done.
set (LBall2 := pe_blocks (PEF tk LC_GLOBAL newl len lenr sb spf pmd mxd fl) q LBc ts0 ++ LK) in *.
assert (HP1' : HEAPx A ((newl, 48) :: LBall2) m1 md).
{ eapply (heap_perm S4L HIx); [exact HP1 | unfold LBall, LBall2, LB0, pe_blocks; cbn [pf_tk pf_md pf_mxd pf_fl]; perm]. }
eapply FREEL;
[exact HP1' | left; reflexivity | rewrite unsigned_lit by lia; exact ST1 | clia | rewrite unsigned_lit by lia; cbn [hl_stack S4L pf_mxd]; clia
| rewrite unsigned_lit by lia; exact SPA | rewrite unsigned_lit by lia; clia | exact ERR1 | reflexivity | rewrite unsigned_lit by lia; reflexivity |].
intros ms2 m2 md2 A2 r2 RS2 VM2 ST2 HPR2 ERR2 HP2. open_ret RS2. cbn [hl_segs hl_tp S4L pf_mxd] in *.
rewrite ?(unsigned_lit spf) in ST2 by lia. rewrite ?(unsigned_lit spf) in HPR2 by lia.
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2.
pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI2.
rewrite lb_remove_head in HPR2, HP2. clear HP1'.

assert (JCG2 : jc_glob_P m2).
{ eapply jc_glob_P_pres; [exact HPR2|]. eapply jc_glob_P_munch; [exact JCG | exact MU01 | exact WM01 |].
unfold LOCCELL. apply Forall_cons; [cbn [fst snd pf_mxd]; lia|]. apply Forall_cons; [cbn [fst snd pf_mxd]; lia | apply Forall_nil]. }

assert (INtk2 : In (tk, 72) LBall2) by (unfold LBall2, pe_blocks; apply in_or_app; left; apply in_or_app; right; left; reflexivity).
assert (INq2 : In (q, (32 * mxd)) LBall2) by (unfold LBall2, pe_blocks; apply in_or_app; left; apply in_or_app; right; right; left; reflexivity).
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in TOK1; [| eapply client_range_block; [exact INtk2 | lia | cbn; lia]]. cbn [hl_segs S4L pf_mxd] in TOK1.
unfold pe_frame in FR1. apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in FR1; [| left; cbn; lia]. cbn [hl_segs S4L pf_mxd] in FR1.
apply (tstack_pres_g S4L _ _ _ _ _ _ HPR2 INq2) in TSK1; [| exact LEN32]. cbn [hl_segs S4L pf_mxd] in TSK1.
assert (LOC2 : rw_cells rsegs m2 LOCCELL [C8 (Z_to_bv 64 GLOBLOC)]).
{ eapply (heap_pres_rw_cells S4L); [exact HPR2 | exact LOC1 | right; left; cbn; intros z Hz; exact (proj1 (LOCcs z Hz))]. }

assert (TSB : forall a n, In (a, n) (tstate_blocks ts0) -> In (a, n) LBall /\ a <> tk /\ In (a, n) LBall2).
{ intros a n Hin. split; [unfold LBall, pe_blocks; apply in_or_app; left; apply in_or_app; left; exact Hin|].
split; [| unfold LBall2, pe_blocks; apply in_or_app; left; apply in_or_app; left; exact Hin].
intros ->. generalize ND; intros ND'. unfold LBall, pe_blocks in ND'. rewrite !map_app in ND'. apply NoDup_app_remove_r in ND'.
eapply (NoDup_app_in2 _ _ tk ND'); [exact (in_map blk_addr _ _ Hin) | left; reflexivity]. }
assert (AG1 : agree_on rsegs (tstate_blocks ts0) m m1).
{ eapply agree_of_munch; [exact MU01 | exact WM01 |]. intros a n Hin. destruct (TSB a n Hin) as (HinL & Hne & _).
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ a n tk 72 HP HinL INtk Hne).
pose proof (heap_blk_img S4L HIx _ _ _ _ a n HP HinL) as Hi. cbn [hl_img_lo hl_img_hi S4L pf_mxd] in Hi.
pose proof (heap_blk S4L HIx _ _ _ _ a n HP HinL) as (Hn0 & _). unfold LOCCELL. cbn. lia. }
assert (AG2 : agree_on rsegs (tstate_blocks ts0) m m2).
{ eapply agree_on_trans; [exact AG1|]. eapply (agree_of_heap_pres rsegs S4L); [exact HPR2 | reflexivity | intros [a n] Hb; exact (proj2 (proj2 (TSB a n Hb)))]. }

unstash HPR.
assert (HPRx2 : heap_presx S4L xloc LBc (spf + 144) me m2).
{ eapply heap_presx_trans; [eapply heap_presx_weaken; [exact HPR | lia | intros b Hb; right; exact Hb | intros z Hz; left; exact Hz] |].
eapply heap_presx_trans.
- eapply heap_presx_of_munchx; [exact MU01 | exact WM01 |].
eapply (client_outsidex xloc); [exact HP | intros b Hb; unfold LBall, pe_blocks; apply in_or_app; left; apply in_or_app; right; right; right; right; exact Hb | clia |].
apply Forall_cons; [right; left; exists tk, 72; cbn [fst snd pf_mxd]; split; [exact INtk |]; split; [| lia] |].
{ intros Hin. generalize ND; intros ND'. unfold LBall, pe_blocks, LB0 in ND'. rewrite !map_app in ND'. apply NoDup_app_remove_r in ND'. apply NoDup_app_remove_l in ND'.
cbn [map app blk_addr fst pf_mxd] in ND'. apply List.NoDup_cons_iff in ND' as [Hni _]. apply Hni. right; right. exact (in_map blk_addr _ _ Hin). }
apply Forall_cons; [| apply Forall_nil]. right; right; right. cbn [fst snd hl_img_lo hl_img_hi S4L pf_mxd]. intros z Hz. split; [right; exact Hz | unfold LOCCELL in Hz; lia].
- apply heap_pres_presx. eapply heap_pres_weaken; [exact HPR2 | lia | intros b Hb; unfold LBall2, pe_blocks; apply in_or_app; left; apply in_or_app; right; right; right; exact Hb]. }
stash HPR.
reenter MOK2.
unfold tok_cells, tok_cells_g in TOK1. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in TOK1.
bst. rewrite <- (Z_to_bv_bv_unsigned (sx32 errf)).
pose proof (bv_unsigned_in_range 64 (sx32 errf)) as EWR; unfold bv_modulus in EWR; cbn in EWR.
destruct (Z.eq_dec (bv_unsigned (sx32 errf)) 0) as [E0 | En].
-
rewrite E0. bst. if_true.
apply evt_RZ_done. unstash PB.
eapply out_success with (levels := levels) (objbs := objbs) (LK := LK) (pbs := pbs) (l := l);
[exact STC | | exact LEN32 | exact D32 | exact Hl | | exact TSK1 | unfold tok_cells, tok_cells_g; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd]; exact TOK1
| unfold pe_frame; exact FR1 | | exact Hpb | exact ST2 | exact ERR2 | exact LOC2 | exact HPRx2 | exact RAE | exact VM2
| pose proof (proj1 TDOK depth l Hl) as DL; cbn [t_levels pf_mxd] in DL; pose proof (odep_nonneg (tl_cs l)); lia | exact JCG2 | exact K].
+ eapply (heap_perm S4L HIx); [exact HP2|]. unfold LBall2, pe_blocks, tstate_blocks, ts0. cbn [t_pbs t_objbs t_levels pf_tk pf_md pf_mxd pf_fl]. perm.
+ intros i li Hli. eapply lvl_weak_agree; [exact (LVW i li Hli) | exact AG2 |].
intros b Hb. unfold tstate_blocks, ts0; cbn [t_pbs t_objbs t_levels pf_mxd]. apply in_or_app; right. apply in_or_app; right.
apply in_concat. exists (lvl_blocks li). split; [apply in_map; eapply nth_error_In; exact Hli | exact Hb].
+ eapply pbuf_agree; [exact PB | exact AG2 | intros b Hb; unfold tstate_blocks, ts0; cbn [t_pbs pf_mxd]; apply in_or_app; left; exact Hb].
-
bst. if_falsex. bst. bst.
eapply (pe_epilogue _ _ [C8 _; CB 16 _; C4 _; CB 3 _; C1 _; CB 8 _]); [unfold pe_frame; exact FR1 | reflexivity | lia | lia | exact RAE |].
apply K. unfold pe_post_g, PE_FRAME. cbn [pf_spf pf_tk pf_md pf_mxd pf_fl].
exists m2, A2, gp, 0, errv, [], ((tk, TOK_SZ) :: (q, 32 * mxd) :: pbs ++ concat (map lvl_blocks levels)), (objbs ++ LK).
split; [do 16 eexists; split; [reflexivity|]; split; [apply fsaved_refl | intros Hf; exact Hf]|].
split; [exact VM2|].
lazymatch type of FR1 with rw_cells _ _ _ ?CS => pose proof (stk_release rsegs m2 lo spf CS ST2 FR1 ltac:(lia)) as STx end.
change (Z.of_nat (cells_size _)) with 144 in STx.
split; [exact STx|].
split; [exact ERR2|]. split; [exact LOC2|]. split; [exact HPRx2|].
split.
{ eapply (heap_perm S4L HIx); [exact HP2|]. unfold LBall2, pe_blocks, tstate_blocks, ts0. cbn [t_pbs t_objbs t_levels pf_tk pf_md pf_mxd pf_fl].
set (CC := concat (map lvl_blocks levels)). perm. }
split; [| split; [left; split; reflexivity | exact JCG2]].

exists q, pb, (Z.of_nat depth), pbs, levels, (TS isd stpos (Z_to_bv 64 co) errf ucs high quote).
split; [reflexivity|]. split; [rewrite LEN32; lia|]. split; [lia|].
split; [unfold tok_cells, tok_cells_g; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd]; exact TOK1|].
unstash PB.
split; [eapply pbuf_agree; [exact PB | exact AG2 | intros b Hb; unfold tstate_blocks, ts0; cbn [t_pbs pf_mxd]; apply in_or_app; left; exact Hb]|].
split; [exact Hpb|]. split; [exact TSK1|].
split.
+ intros i li Hli Hile. destruct (LVW i li Hli) as (_ & Ji & Ni & _). split.
* eapply (jopt_agree rsegs S4F); [exact Ji | exact AG2 |].
intros b Hb. unfold tstate_blocks, ts0; cbn [t_pbs t_objbs t_levels pf_mxd]. apply in_or_app; right. apply in_or_app; right.
apply in_concat. exists (lvl_blocks li). split; [apply in_map; eapply nth_error_In; exact Hli | unfold lvl_blocks; apply in_or_app; left; exact Hb].
* destruct Ni as [Ni | Ni]; cbn [name_ok pf_mxd] in Ni; [left; exact Ni | right].
destruct Ni as (Hn & nn & ks & E & _). split; [exact Hn | exists nn; exact E].
+ intros i li Hli Hlt. destruct (LVW i li Hli) as (_ & _ & _ & CL). apply CL. lia.
Qed.
End PeOut.

End RC__1.
