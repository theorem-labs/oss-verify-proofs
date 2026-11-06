(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup Lib.GwApply QWxq_c1 QRjH QHnV QCcH QfLs Q0Ek Qtgi QjDH Qsw7 QJjn QRUw QPZI QkMG QG8z QIsM Q7UD Qhd4 Qwm6 QlKV QsKa Qiiq Q4v2 QugP Q1Ey Ql4f QrQv QEUF QW22 QdGy QnDr Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QJjn QRUw.Mq0 QRUw QRUw.Mq2. Import QPZI.Mq4. Import QkMG. Import QG8z QIsM.Mq2.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa QsKa.Mq4 Qiiq.Mq0 QsKa.Mq6 Q4v2.Mq0 QugP.Mq1 QlKV.Mq5 Q1Ey Ql4f.Mq1 QsKa.Mq8 QrQv.Mq2 QEUF QW22.Mq3 QdGy.Mq2 QlKV.Mq2 QnDr.Mq3.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section PeSCallAaA.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_pres : forall LB SP m m', heap_pres A4H LB SP m m' -> GA m -> GA m'.
Hypothesis SHRINK : jo_array_shrink_A2J HIx.

Lemma pe_shrink_cJ :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel) (kids : list (option jshape))
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP : Z) (nB : nat)
(ra gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
PBOK m ts kP -> BOK pf pa ts B nB ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_cs l = Some (Sarr kids) -> tl_ss l <> ST_finish -> tl_nbs l = [] ->
bv_unsigned ra mod 2 = 0 ->
(forall m2 md2 A2 B2 cbs2 errv2 r (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : word) F2 fc2,
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m2 md2 A2 B2 (ts_lvl ts (TL (tl_st l) (tl_ss l) (tl_cur l) (tl_cs l) cbs2 (tl_name l) (tl_nbs l))) cb nb pj sv errv2 ->
PBOK m2 (ts_lvl ts (TL (tl_st l) (tl_ss l) (tl_cur l) (tl_cs l) cbs2 (tl_name l) (tl_nbs l))) kP ->
(forall st', zin st' [ST_array_add; ST_ovadd] = false -> BOK pf pa (ts_lvl ts (TL st' ST_finish (tl_cur l) (tl_cs l) cbs2 (tl_name l) (tl_nbs l))) B2 nB) ->
(forall w, jtx (Sarr kids) (tl_cbs l) = Some (w, []) -> jtx (Sarr kids) cbs2 = Some (w, [])) ->
fsaved F F2 -> (frm0 fc -> frm0 fc2) ->
AJ5 A4L HIx A2 T md2
(MS (mkR ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) w0 w1 w2 s0 s1 (Z_to_bv 64 r) w3 w4 w5 w6 w7 w8 w9
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 w10 w11 w12 w13) F2 (ret_pc ra) fc2 None m2 (seg_rom asegs))) ->
AJ5 A4L HIx A T md
(MS (mkR ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2 s0 s1 (Z_to_bv 64 (tl_cur l)) (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x9ed6c) fc None m (seg_rom asegs)).
Proof.
intros until fc. intros STC BSL INV PBK BK Hl Hcs Hop Hnbs RA K.
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
pose proof INV as [CORE REST1].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK1 & FR1).
pose proof REST1 as (HP1 & LV1 & OBJ1 & ST1 & ERR1 & _).
assert (Hd : (t_depth ts < length (t_levels ts))%nat) by (apply nth_error_Some; rewrite Hl; discriminate).
set (RB := pe_restblocks pf q LB0 ts).
pose proof (LV1 _ _ Hl) as LVd. pose proof LVd as (ST26 & SS26 & JO & Md). rewrite Hcs in JO. cbn [jopt] in JO. destruct JO as [Hc J].
assert (HPa : HEAPA A4L HIx A (tl_cbs l ++ RB) LM ((pa_F pa, 2) :: FRS) B m md).
{ eapply (heapA_perm A4L HIx); [exact HP1 | | apply Permutation_refl | apply Permutation_refl].
eapply Permutation_trans; [apply (pe_blocksA_cur_perm pf q LB0 ts l Hl)|]. unfold lvl_blocks. rewrite Hnbs, app_nil_r. apply Permutation_refl. }
pose proof (arr_capA_jval _ _ _ _ _ J) as (a_ & arr_ & rest_ & EABS & Hcap1 & Hcap2 & Hcap3).
assert (Hk28 : Z.of_nat (length kids) < 2^28).
{ assert (Hin : In (arr_, 8 * arr_capA (tl_cbs l)) (tl_cbs l ++ RB)).
{ apply in_or_app; left. set (c_ := arr_capA (tl_cbs l)) in *. rewrite EABS. right; right; left; reflexivity. }
pose proof (heapA_blk_le26 A4L HIx _ _ _ _ _ _ _ arr_ (8 * arr_capA (tl_cbs l)) HPa Hin). lia. }
destruct (BOK_arr_close pf pa ts B nB l kids BK BSL Hl Hcs (lvl_closed_open_ss l Hop)) as [COST BK2].
assert (SPF1 : lo <= pf_spf pf - (16 + 48 + 4096) /\ pf_spf pf mod 16 = 0 /\ pf_spf pf <= hiA_top A4L HIx /\ 0 <= pf_spf pf < 2^62).
{ clear - LOS HT Gle Gspf SP0. split; [lia|]. split; [Z.div_mod_to_equations; lia|]. split; lia. }
destruct SPF1 as (SPF1 & SPF2 & SPF3 & SPF4).
eapply SHRINK with (LB := RB) (ABS := tl_cbs l) (p := tl_cur l) (kids := kids) (lo := lo) (errv := errv) (FRS := (pa_F pa, 2) :: FRS);
[ | exact J | reflexivity | reflexivity | exact Hk28 | exact COST | ].
{ unfold jo_preA. rewrite !unsigned_lit by lia. split; [exact HPa|]. split; [exact ST1|]. split; [exact LO|]. split; [exact SPF1|]. split; [exact SPF2|]. split; [exact SPF3|].
split; [exact ERR1|]. split; [reflexivity | exact RA]. }
intros ms2 md2 m2 r A2 B2 (RS2 & VM2 & ST2 & HPR2 & (errv2 & ERR2)) HB2 HD2 (cbs2 & J2 & Hlen2 & _ & HP2 & JX2).
destruct RS2 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F2 & fc2 & -> & FS2 & FRM2).
cbn [hl_segs hl_tp hla_base A4L A4H] in *. rewrite ?(unsigned_lit (pf_spf pf)) in ST2 by lia. rewrite ?(unsigned_lit (pf_spf pf)) in HPR2 by lia.
set (l2 := TL (tl_st l) (tl_ss l) (tl_cur l) (tl_cs l) cbs2 (tl_name l) (tl_nbs l)).
assert (INtk : In (pf_tk pf, 72) RB) by (unfold RB, pe_restblocks; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * pf_mxd pf) RB) by (unfold RB, pe_restblocks; apply in_or_app; right; right; left; reflexivity).
assert (LB0R : incl LB0 RB) by (unfold RB, pe_restblocks; intros b Hb; apply in_or_app; right; right; right; exact Hb).
assert (AG : agree_on asegs RB m m2) by (eapply (agree_of_heap_pres asegs A4H); [exact HPR2 | reflexivity | intros b Hb; apply in_or_app; left; exact Hb]).
assert (FR2 : pe_frameA asegs m2 pf pa cb nb pj sv).
{ eapply pe_frameA_pres; [exact HPR2 | lia | exact GEO | | | exact FR1].
- apply in_or_app; right. apply in_or_app; right. change 248 with (fr_size 2 - 8). apply fr_ivs_frame. left; reflexivity.
- apply in_or_app; right. apply in_or_app; right. rewrite <- fr_shadow_len_2. change (shA (pa_F pa)) with (shad A4L (pa_F pa)). apply fr_ivs_shadow. left; reflexivity. }
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in TOK; [| eapply client_range_block; [apply in_or_app; left; exact INtk | lia | unfold tok_cells_g; cbn; lia]]. cbn [hl_segs hla_base A4L A4H] in TOK.
apply (tstack_pres_g A4H _ _ _ _ _ _ HPR2 (in_or_app _ _ _ (or_introl INq))) in TSK1; [| exact LEN32]. cbn [hl_segs hla_base A4L A4H] in TSK1.
assert (PBKa : PBOK m2 ts kP).
{ eapply PBOK_agree; [exact PBK | exact AG |]. unfold RB, pe_restblocks. intros b Hb. apply in_or_app; left. apply in_or_app; left. exact Hb. }
assert (HP2' : HEAPA A4L HIx A2 (pe_blocksA pf q LB0 (ts_lvl ts l2)) LM ((pa_F pa, 2) :: FRS) B2 m2 md2).
{ eapply (heapA_perm A4L HIx); [exact HP2 | | apply Permutation_refl | apply Permutation_refl].
apply Permutation_sym. eapply Permutation_trans; [apply (pe_blocksA_lvl_perm pf q LB0 ts l l2 Hl)|]. unfold lvl_blocks, l2. cbn [tl_cbs tl_nbs]. rewrite Hnbs, app_nil_r. apply Permutation_refl. }
assert (BUD2 : PE_BUD pf pa (ts_lvl ts l2) B2).
{ eapply PE_BUD_lvl_irrel; [| exact (BOK_weak _ _ _ _ _ (BK2 B2 cbs2 ST_eatws eq_refl Hlen2 HB2 HD2))]. reflexivity. }
assert (REST2 : PE_REST_A HIx GA pf pa q LB0 LM FRS payload me lo m2 md2 A2 B2 (ts_lvl ts l2) errv2).
{ eapply (PE_REST_A_callG HIx GA GA_pres) with (ts := ts) (LBc := RB); [exact STC | exact REST1 | exact VM2 | exact HPR2 | exact LB0R | exact HP2' | | | exact ST2 | exact ERR2 | exact BUD2].
- unfold ts_lvl; cbn [t_levels t_depth]. intros i li Hli.
destruct (PeanoNat.Nat.eq_dec i (t_depth ts)) as [-> | NE].
+ rewrite nth_error_lupd_eq in Hli by exact Hd. injection Hli as <-.
split; [exact ST26|]. split; [exact SS26|]. split; [cbn [tl_cs tl_cbs tl_cur l2]; rewrite Hcs; cbn [jopt]; split; [exact Hc | exact J2]|].
rewrite Nat.ltb_irrefl, Nat.eqb_refl in Md |- *. destruct Md as (c0 & hn0 & Hmode & CLS0 & NM0). exists c0, hn0. split; [exact Hmode|]. split; [exact CLS0|].
eapply (name_ok_agree asegs) with (BS := RB); [exact NM0 | exact AG |]. cbn [tl_nbs l2]. rewrite Hnbs. intros b [].
+ rewrite nth_error_lupd_neq in Hli by congruence.
eapply (lvl_cur_agree asegs A4F); [exact (LV1 i li Hli) | exact AG | exact (pe_restblocks_other pf q LB0 ts i li NE Hli)].
- unfold cur_st, ts_lvl in *; cbn [t_levels t_depth t_objs t_objbs t_obj] in *. rewrite nth_error_lupd_eq by exact Hd. cbn [tl_st l2]. rewrite Hl in OBJ1.
destruct (zin (tl_st l) [ST_array_add; ST_ovadd]); [| exact OBJ1].
eapply (jopt_agree asegs A4F); [exact OBJ1 | exact AG |]. unfold RB, pe_restblocks. intros b Hb. apply in_or_app; left. apply in_or_app; right. apply in_or_app; left. exact Hb. }
assert (INV2 : PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m2 md2 A2 B2 (ts_lvl ts l2) cb nb pj sv errv2).
{ split; [| exact REST2]. unfold PE_CORE_A, ts_lvl; cbn [t_levels t_depth t_co t_x t_pb t_pbs]. split; [rewrite lupd_length; exact LEN32|]. split; [exact D32|]. split; [exact CO|]. split; [exact CHOFF|].
split; [exact TOK|]. split; [exact (PBOK_pbuf _ _ _ PBKa)|]. split; [exact Hpb|]. split; [| exact FR2].
eapply tstack_lupd_srec; [exact TSK1 | exact Hl | reflexivity]. }
eapply (K m2 md2 A2 B2 cbs2 errv2 r); [exact INV2 | exact PBKa | intros st' Hz'; exact (BK2 B2 cbs2 st' Hz' Hlen2 HB2 HD2) | exact JX2 | exact FS2 | exact FRM2].
Qed.

Hypothesis AADD : jo_array_add_A2J HIx.

Lemma pe_aadd_cJ :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel) (kids : list (option jshape))
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP : Z) (nB : nat)
(ra gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
PBOK m ts kP -> BOK pf pa ts B (S (Z.to_nat 1280 + nB)) ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_array_add -> tl_cs l = Some (Sarr kids) -> tl_nbs l = [] ->
bv_unsigned ra mod 2 = 0 ->
(forall m2 md2 A2 B2 errv2 r (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : word) F2 fc2,
(r = 0 /\ exists cbs2,
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m2 md2 A2 B2
(ts_lvl_obj ts (TL (tl_st l) (tl_ss l) (tl_cur l) (Some (Sarr (kids ++ [t_objs ts]))) cbs2 (tl_name l) (tl_nbs l)) 0 None []) cb nb pj sv errv2 /\
PBOK m2 (ts_lvl_obj ts (TL (tl_st l) (tl_ss l) (tl_cur l) (Some (Sarr (kids ++ [t_objs ts]))) cbs2 (tl_name l) (tl_nbs l)) 0 None []) kP /\
(forall st' ss' obj' objs', ss' <> ST_finish ->
BOK pf pa (ts_lvl_obj ts (TL st' ss' (tl_cur l) (Some (Sarr (kids ++ [t_objs ts]))) cbs2 (tl_name l) (tl_nbs l)) obj' objs' []) B2 nB) /\
(forall w wv, jtx (Sarr kids) (tl_cbs l) = Some (w, []) -> jtx_opt (t_objs ts) (t_objbs ts) = Some (wv, []) ->
jtx (Sarr (kids ++ [t_objs ts])) cbs2 = Some (w + (2 + wv), [])))
\/ (r = 2^64 - 1 /\ PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m2 md2 A2 B2 ts cb nb pj sv errv2) ->
fsaved F F2 -> (frm0 fc -> frm0 fc2) ->
AJ5 A4L HIx A2 T md2
(MS (mkR ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) w0 w1 w2 s0 s1 (Z_to_bv 64 r) w3 w4 w5 w6 w7 w8 w9
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 w10 w11 w12 w13) F2 (ret_pc ra) fc2 None m2 (seg_rom asegs))) ->
AJ5 A4L HIx A T md
(MS (mkR ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2 s0 s1 (Z_to_bv 64 (tl_cur l)) (Z_to_bv 64 (t_obj ts)) a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x9ecf4) fc None m (seg_rom asegs)).
Proof.
intros until fc. intros STC BSL INV PBK BK Hl Hst Hcs Hnbs RA K.
assert (Hop : lvl_closed l = false) by (apply lvl_closed_open_st; rewrite Hst; reflexivity).
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
pose proof INV as [CORE REST1].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK1 & FR1).
pose proof REST1 as (HP1 & LV1 & OBJ1 & ST1 & ERR1 & _).
assert (Hd : (t_depth ts < length (t_levels ts))%nat) by (apply nth_error_Some; rewrite Hl; discriminate).
assert (JOB : jopt asegs A4F (t_objs ts) m (t_objbs ts) (t_obj ts)).
{ revert OBJ1. unfold cur_st. rewrite Hl, Hst. cbn. intros E; exact E. }
set (RB := pe_restblocks2 pf q LB0 ts).
pose proof (LV1 _ _ Hl) as LVd. pose proof LVd as (ST26 & SS26 & JO & Md). rewrite Hcs in JO. cbn [jopt] in JO. destruct JO as [Hc J].
assert (HPa : HEAPA A4L HIx A (tl_cbs l ++ t_objbs ts ++ RB) LM ((pa_F pa, 2) :: FRS) B m md).
{ eapply (heapA_perm A4L HIx); [exact HP1 | | apply Permutation_refl | apply Permutation_refl].
eapply Permutation_trans; [apply (pe_blocksA_cur_perm2 pf q LB0 ts l Hl)|]. unfold lvl_blocks. rewrite Hnbs, app_nil_r. apply Permutation_refl. }
pose proof (arr_capA_jval _ _ _ _ _ J) as (a_ & arr_ & rest_ & EABS & Hcap1 & Hcap2 & Hcap3).
assert (Hk28 : Z.of_nat (length kids) + 1 < 2^28).
{ assert (Hin : In (arr_, 8 * arr_capA (tl_cbs l)) ((tl_cbs l ++ t_objbs ts ++ RB))).
{ apply in_or_app; left. set (c_ := arr_capA (tl_cbs l)) in *. rewrite EABS. right; right; left; reflexivity. }
pose proof (heapA_blk_le26 A4L HIx _ _ _ _ _ _ _ arr_ (8 * arr_capA (tl_cbs l)) HPa Hin). lia. }
destruct (BOK_arr_add pf pa ts B nB l kids BK BSL Hl Hcs Hop) as (COST & BKF & BK2).
assert (SPF1 : lo <= pf_spf pf - (16 + 96 + 4096) /\ pf_spf pf mod 16 = 0 /\ pf_spf pf <= hiA_top A4L HIx /\ 0 <= pf_spf pf < 2^62).
{ clear - LOS HT Gle Gspf SP0. split; [lia|]. split; [Z.div_mod_to_equations; lia|]. split; lia. }
destruct SPF1 as (SPF1 & SPF2 & SPF3 & SPF4).
eapply AADD with (LB := RB) (ABS := tl_cbs l) (VBS := t_objbs ts) (p := tl_cur l) (v := t_obj ts) (kids := kids) (vs := t_objs ts) (lo := lo) (errv := errv) (FRS := (pa_F pa, 2) :: FRS);
[ | exact J | exact JOB | reflexivity | reflexivity | exact Hk28 | exact COST | ].
{ unfold jo_preA. rewrite !unsigned_lit by lia. split; [exact HPa|]. split; [exact ST1|]. split; [exact LO|]. split; [exact SPF1|]. split; [exact SPF2|]. split; [exact SPF3|].
split; [exact ERR1|]. split; [reflexivity | exact RA]. }
intros ms2 md2 m2 r A2 B2 (RS2 & VM2 & ST2 & HPR2 & (errv2 & ERR2)) HD2 OUT.
destruct RS2 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F2 & fc2 & -> & FS2 & FRM2).
cbn [hl_segs hl_tp hla_base A4L A4H] in *. rewrite ?(unsigned_lit (pf_spf pf)) in ST2 by lia. rewrite ?(unsigned_lit (pf_spf pf)) in HPR2 by lia.
assert (INtk : In (pf_tk pf, 72) RB) by (unfold RB, pe_restblocks2; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * pf_mxd pf) RB) by (unfold RB, pe_restblocks2; apply in_or_app; right; right; left; reflexivity).
assert (LB0R : incl LB0 RB) by (unfold RB, pe_restblocks2; intros b Hb; apply in_or_app; right; right; right; exact Hb).
assert (AG : agree_on asegs RB m m2) by (eapply (agree_of_heap_pres asegs A4H); [exact HPR2 | reflexivity | intros b Hb; apply in_or_app; left; exact Hb]).
assert (FR2 : pe_frameA asegs m2 pf pa cb nb pj sv).
{ eapply pe_frameA_pres; [exact HPR2 | lia | exact GEO | | | exact FR1].
- apply in_or_app; right. apply in_or_app; right. change 248 with (fr_size 2 - 8). apply fr_ivs_frame. left; reflexivity.
- apply in_or_app; right. apply in_or_app; right. rewrite <- fr_shadow_len_2. change (shA (pa_F pa)) with (shad A4L (pa_F pa)). apply fr_ivs_shadow. left; reflexivity. }
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in TOK; [| eapply client_range_block; [apply in_or_app; left; exact INtk | lia | unfold tok_cells_g; cbn; lia]]. cbn [hl_segs hla_base A4L A4H] in TOK.
apply (tstack_pres_g A4H _ _ _ _ _ _ HPR2 (in_or_app _ _ _ (or_introl INq))) in TSK1; [| exact LEN32]. cbn [hl_segs hla_base A4L A4H] in TSK1.
assert (PBKa : PBOK m2 ts kP).
{ eapply PBOK_agree; [exact PBK | exact AG |]. unfold RB, pe_restblocks2. intros b Hb. apply in_or_app; left. apply in_or_app; left. exact Hb. }
eapply (K m2 md2 A2 B2 errv2 r); [| exact FS2 | exact FRM2].
destruct OUT as [(-> & cbs2 & J2 & Hlen2 & GR2 & HB2 & HP2 & JX2) | (-> & HB2 & J2 & JOB2 & HP2)].
- left. split; [reflexivity|]. exists cbs2.
set (l2 := TL (tl_st l) (tl_ss l) (tl_cur l) (Some (Sarr (kids ++ [t_objs ts]))) cbs2 (tl_name l) (tl_nbs l)).
set (ts2 := ts_lvl_obj ts l2 0 None []).
assert (BK2' := fun st' ss' obj' objs' Hss' => BK2 B2 cbs2 st' ss' obj' objs' Hss' Hlen2 GR2 HB2 HD2).
assert (HP2' : HEAPA A4L HIx A2 (pe_blocksA pf q LB0 ts2) LM ((pa_F pa, 2) :: FRS) B2 m2 md2).
{ eapply (heapA_perm A4L HIx); [exact HP2 | | apply Permutation_refl | apply Permutation_refl].
apply Permutation_sym. eapply Permutation_trans; [apply (pe_blocksA_lvl_obj_perm pf q LB0 ts l l2 0 None [] Hl)|]. unfold lvl_blocks, l2. cbn [tl_cbs tl_nbs app]. rewrite Hnbs, app_nil_r. apply Permutation_refl. }
assert (BUD2 : PE_BUD pf pa ts2 B2).
{ eapply PE_BUD_lvl_obj_irrel; [| exact (BOK_weak _ _ _ _ _ (BK2' ST_eatws ST_array_sep 0 None ltac:(unfold ST_array_sep, ST_finish; lia)))]. reflexivity. }
assert (REST2 : PE_REST_A HIx GA pf pa q LB0 LM FRS payload me lo m2 md2 A2 B2 ts2 errv2).
{ eapply (PE_REST_A_callG HIx GA GA_pres) with (ts := ts) (LBc := RB); [exact STC | exact REST1 | exact VM2 | exact HPR2 | exact LB0R | exact HP2' | | | exact ST2 | exact ERR2 | exact BUD2].
- unfold ts2, ts_lvl_obj; cbn [t_levels t_depth]. intros i li Hli.
destruct (PeanoNat.Nat.eq_dec i (t_depth ts)) as [-> | NE].
+ rewrite nth_error_lupd_eq in Hli by exact Hd. injection Hli as <-.
split; [exact ST26|]. split; [exact SS26|]. split; [cbn [tl_cs tl_cbs tl_cur l2 jopt]; split; [exact Hc | exact J2]|].
rewrite Nat.ltb_irrefl, Nat.eqb_refl in Md |- *. destruct Md as (c0 & hn0 & Hmode & CLS0 & NM0). exists c0, hn0. split; [exact Hmode|].
split; [cbn [tl_cs l2]; rewrite Hcs in CLS0; destruct c0; cbn in CLS0 |- *; exact CLS0 |].
eapply (name_ok_agree asegs) with (BS := RB); [exact NM0 | exact AG |]. cbn [tl_nbs l2]. rewrite Hnbs. intros b [].
+ rewrite nth_error_lupd_neq in Hli by congruence.
eapply (lvl_cur_agree asegs A4F); [exact (LV1 i li Hli) | exact AG | exact (pe_restblocks2_other pf q LB0 ts i li NE Hli)].
- unfold cur_st, ts2, ts_lvl_obj; cbn [t_levels t_depth t_objs t_objbs t_obj]. rewrite nth_error_lupd_eq by exact Hd. cbn [tl_st l2]. rewrite Hst. cbn. split; reflexivity. }
split; [| split; [exact PBKa | split; [exact BK2' | exact JX2]]].
split; [| exact REST2]. unfold PE_CORE_A, ts2, ts_lvl_obj; cbn [t_levels t_depth t_co t_x t_pb t_pbs]. split; [rewrite lupd_length; exact LEN32|]. split; [exact D32|]. split; [exact CO|]. split; [exact CHOFF|].
split; [exact TOK|]. split; [exact (PBOK_pbuf _ _ _ PBKa)|]. split; [exact Hpb|]. split; [| exact FR2].
eapply tstack_lupd_srec; [exact TSK1 | exact Hl | reflexivity].
- right. split; [reflexivity|].
assert (HP2' : HEAPA A4L HIx A2 (pe_blocksA pf q LB0 ts) LM ((pa_F pa, 2) :: FRS) B2 m2 md2).
{ eapply (heapA_perm A4L HIx); [exact HP2 | | apply Permutation_refl | apply Permutation_refl].
apply Permutation_sym. eapply Permutation_trans; [apply (pe_blocksA_cur_perm2 pf q LB0 ts l Hl)|]. unfold lvl_blocks. rewrite Hnbs, app_nil_r. apply Permutation_refl. }
assert (REST2 : PE_REST_A HIx GA pf pa q LB0 LM FRS payload me lo m2 md2 A2 B2 ts errv2).
{ eapply (PE_REST_A_callG HIx GA GA_pres) with (ts := ts) (LBc := RB); [exact STC | exact REST1 | exact VM2 | exact HPR2 | exact LB0R | exact HP2' | | | exact ST2 | exact ERR2 | exact (BKF B2 HB2 HD2)].
- intros i li Hli.
destruct (PeanoNat.Nat.eq_dec i (t_depth ts)) as [-> | NE].
+ rewrite Hl in Hli. injection Hli as <-.
split; [exact ST26|]. split; [exact SS26|]. split; [rewrite Hcs; cbn [jopt]; split; [exact Hc | exact J2]|].
rewrite Nat.ltb_irrefl, Nat.eqb_refl in Md |- *. destruct Md as (c0 & hn0 & Hmode & CLS0 & NM0). exists c0, hn0. split; [exact Hmode|]. split; [exact CLS0|].
eapply (name_ok_agree asegs) with (BS := RB); [exact NM0 | exact AG |]. rewrite Hnbs. intros b [].
+ eapply (lvl_cur_agree asegs A4F); [exact (LV1 i li Hli) | exact AG | exact (pe_restblocks2_other pf q LB0 ts i li NE Hli)].
- unfold cur_st. rewrite Hl, Hst. cbn. exact JOB2. }
split; [| exact REST2]. split; [exact LEN32|]. split; [exact D32|]. split; [exact CO|]. split; [exact CHOFF|].
split; [exact TOK|]. split; [exact (PBOK_pbuf _ _ _ PBKa)|]. split; [exact Hpb|]. split; [exact TSK1 | exact FR2].
Qed.
End PeSCallAaA.
End RC__1.
End Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qdyh Qa8x Q1Y6 QYZ0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QJjn QRUw.Mq0 QRUw QkMG. Import QG8z Qdyh.Mq0 Qdyh.Mq3 Qdyh.Mq4 QIsM.Mq2 Qa8x.Mq2 Qa8x.Mq3.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa QsKa.Mq4 Qiiq.Mq0 QsKa.Mq6 Q4v2.Mq0 QlKV.Mq5 Q1Ey Ql4f.Mq1 Q1Y6.Mq2 QsKa.Mq8 QrQv.Mq2 QEUF QW22.Mq3 QdGy.Mq2 QYZ0.Mq3.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section PeSNeedescA.
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

Ltac reopen_inv INVx TSx ts0 PF q LB0 tk mxd depth l Hl bse Hbse mX :=
pose proof INVx as [CORE2 REST2];
destruct CORE2 as (_ & _ & _ & _ & TOK & _ & _ & TSK & FR);
pose proof REST2 as (HP & _); clear REST2;
try unfold TSx in TOK, TSK; try unfold ts_pbs, ts_lvl, ts_set_x in TOK, TSK; try unfold ts0 in TOK, TSK;
cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_tk pf_mxd pf_fl] in TOK, TSK;
unfold tok_cells_g in TOK; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK;
unfold pe_frameA in FR; destruct FR as (SLOTS & _ & _ & _ & _); unfold pe_slotsA in SLOTS; cbn zeta in SLOTS;
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in SLOTS;
assert (INtk : In (tk, 72) (pe_blocksA PF q LB0 TSx)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity);
assert (INq : In (q, 32 * mxd) (pe_blocksA PF q LB0 TSx)) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity);
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI;
pose proof (wmono_refl asegs mX) as WM;
pose proof (TSK depth l Hl) as Ld; rewrite <- Hbse in Ld; unfold srec_cells in Ld;
clear TSK.

Lemma seg_needesc_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP : Z) (nB : nat)
(gp t0 t1 t2 a3 a5 a6 a7 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv -> PBOK m ts kP -> kP + 3 <= 1 -> BOK pf pa ts B (S nB) ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_esc_need_escape ->
t_co ts < pf_len pf ->
bytes_at asegs me UTF8REP_ADDR_A Qa8x.Mq3.utf8rep ->

(forall c hn, lvl_mode (tl_st l) (tl_ss l) = Some (c, hn) -> lvl_mode (tl_ss l) (tl_ss l) = Some (c, hn)) ->
zin (tl_ss l) [ST_array_add; ST_ovadd] = false ->

(forall m' a1' a2' a3',
bv_unsigned cb = 92 ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md A B
(ts_lvl ts (TL ST_esc_need_u (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) cb nb pj sv errv ->
PBOK m' (ts_lvl ts (TL ST_esc_need_u (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) kP ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa APE_ADV (t_co ts) gp t0 t1 t2 (Z_to_bv 64 125) a1' a2' a3' (Z_to_bv 64 APE_JTAB) a5 a6 a7
(Z_to_bv 64 (Z.of_nat (t_depth ts))) (Z_to_bv 64 (pf_tk pf + 56)) (Z_to_bv 64 (pa_F pa + 64)) F fc m')) ->

(forall m' md' A' B' pbs' errv' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' F' fc',
bv_unsigned cb <> 92 ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B'
(ts_lvl (ts_set_x (ts_pbs ts pbs') (t_co ts) (TS (ts_isd (t_x ts)) (Z_to_bv 64 0) (ts_choff (t_x ts)) (ts_err (t_x ts)) (Z_to_bv 64 0) (Z_to_bv 64 0) (ts_quote (t_x ts))))
(TL (tl_ss l) (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) cb nb pj sv errv' ->
PBOK m' (ts_lvl (ts_set_x (ts_pbs ts pbs') (t_co ts) (TS (ts_isd (t_x ts)) (Z_to_bv 64 0) (ts_choff (t_x ts)) (ts_err (t_x ts)) (Z_to_bv 64 0) (Z_to_bv 64 0) (ts_quote (t_x ts))))
(TL (tl_ss l) (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) (kP + 3) ->
BOK pf pa (ts_lvl (ts_set_x (ts_pbs ts pbs') (t_co ts) (TS (ts_isd (t_x ts)) (Z_to_bv 64 0) (ts_choff (t_x ts)) (ts_err (t_x ts)) (Z_to_bv 64 0) (Z_to_bv 64 0) (ts_quote (t_x ts))))
(TL (tl_ss l) (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) B' nB ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msA asegs pf pa APE_REDO (t_co ts) gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5'
(Z_to_bv 64 (pf_tk pf + 56)) (Z_to_bv 64 (pa_F pa + 64)) F' fc' m')) ->

(forall m' md' A' B' errv' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' s11' t4' t6' F' fc',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' ts cb nb pj sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msO asegs pf pa APE_ERRMEM x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' (Z_to_bv 64 (pf_tk pf + 56)) s11' t4' t6' F' fc' m')) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa (pe_jtA ST_esc_need_escape) (t_co ts) gp t0 t1 t2
(Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) (Z_to_bv 64 (tl_st l))
(Z_to_bv 64 (q / 8 + 4 * Z.of_nat (t_depth ts) + A_SB)) a3 (Z_to_bv 64 APE_JTAB) a5 a6 a7
(Z_to_bv 64 (Z.of_nat (t_depth ts))) (Z_to_bv 64 q) (Z_to_bv 64 (pa_F pa + 64)) F fc m).
Proof.
intros until fc. intros STC BSL INV PBK HkP BK Hl Hst Hco UTF HMODE Hzss Kadv Kredo Kerr16. pose proof INV as INV0. pe_openA STC INV.
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
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 4 HP INtk ltac:(lia)) as SHT4.
replace (tk / 8 + 4 + A_SB) with (tk / 8 + 2147450884) in SHT4 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 4 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT4c & SEPT4q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 4 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT4t & _).
cbn [hl_sb A4L] in SEPT4c, SEPT4q, SEPT4t. assert (EQx : tk / 8 + A_SB + 4 = tk / 8 + 2147450884) by (unfold A_SB; lia). rewrite EQx in SEPT4c, SEPT4q, SEPT4t. clear EQx.
unfold APE_BREAK, APE_ADV, APE_REDO, APE_OUT, APE_ERRMEM, APE_ERRST, APE_JTAB in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
assert (cs_tk_L : csep tk 72 bse (Z.of_nat 32)) by (unfold csep; clear - Hdtq HbseR; lia).
assert (cs_L_tk : csep bse 32 tk (Z.of_nat 72)) by (unfold csep; clear - Hdtq HbseR; lia).
assert (cs_T4_L : csep (tk / 8 + 2147450884) 1 bse (Z.of_nat 32)) by (unfold csep; clear - SEPT4q HbseR; lia).
clear Hdtq SEPT4q SEPT4t SEPT4c.
assert (SRC : bytes_at asegs m UTF8REP_ADDR_A Qa8x.Mq3.utf8rep).
{ eapply (heap_presx_bytes_at A4H); [exact HPR | exact UTF |]. right; left. intros a Ha. cbn [length Qa8x.Mq3.utf8rep Z.of_nat Pos.of_succ_nat Pos.succ] in Ha. unfold UTF8REP_ADDR_A in Ha.
cbn [hl_client_static A4H]. unfold a4_client_static, a4_volatile. lia. }
stash Himg_t. stash Himg_q. stash Kadv. stash Kredo. stash Kerr16. clear PB REST TSK LV OBJ HPR BUD GAP SAVED FSH STR ERR SBin.
reenterA asegs A4L HIx asegs_wx HP. rewrite Hst. unfold ST_esc_need_escape. cbn [pe_jtA].
replace (q + 32 * Z.of_nat depth) with bse by lia.
step.
change (zxb cb) with (Z_to_bv 64 (bv_unsigned cb)).
step.
destruct (Z.eq_dec (bv_unsigned cb) 92) as [C92 | N92].
- clear SRC FF SHT.
step.
if_falsex.
step.
asan_rechkA.
step.
stepz.
step.
step. step.
asan_rechkA.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, Lc : rw_cells asegs mc bse _ |- _ =>
evt_done5; rewrite Hbse in MUc, Lc;
destruct (PE_INV_A_lvl_write HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m mc md A B ts0
cb nb pj sv errv l ST_esc_need_u (tl_ss l) c0 hn0 c0 STC INV0 Hl MUc WMc MIc TOKc Lc Hmode
ltac:(rewrite <- Hmode; apply Qa8x.Mq3.lvl_mode_esc_same; [rewrite Hst; reflexivity | reflexivity | exact SS26]) ltac:(unfold ST_esc_need_u; lia) SS26 (or_introl eq_refl)
ltac:(rewrite Hst; reflexivity)) as [INV3 PBK3];
unstash Kadv; eapply (Kadv mc _ _ _ C92); [exact INV3 | exact (PBK3 kP PBK)]
end end.
- step.
if_truex.
step.
asan_chkA.
step.
step. step.
step.
step.
evt_done5.
eapply (pe_memappend_g HIx GA GA_pres MAPP (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m md A B ts0 cb nb pj sv errv T UTF8REP_ADDR_A 3 (co + kP) Qa8x.Mq3.utf8rep);
[ exact STC | exact BSL | exact INV0 | exact PBK | cbn [t_co ts0]; lia | lia | exact BK | rewrite unsigned_lit by lia; reflexivity
| exact SRC | reflexivity | unfold UTF8REP_ADDR_A; lia | apply utf8rep_src_locA | intros _; exact (unpoisoned_of_glob HIx _ _ _ _ _ _ _ _ _ HP utf8rep_src_globA ltac:(lia)) |].
intros mp2 md2 A2 B2 pbs2 errv2 r w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 F2 fc2 INV2 OUT2 FS2 FRM2.
cbn [pf_spf] in *. unfold A_TP in *.
clear TOK SLOTS FF SHT SHQ SHQ4 SHT4 Ld MU WM MI HP INtk INq Htal Htlo Hthi Hqal Hqlo Hqhi Hqtk cs_tk_L cs_L_tk cs_T4_L SRC INV0 PBK BK.
set (ts2 := ts_pbs ts0 pbs2) in *.
reopen_inv INV2 ts2 ts0 (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 tk mxd depth l Hl bse Hbse mp2.
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t2.
blk_factsA A4L HIx HP q (32 * mxd) Hqal Hqlo Hqhi Himg_q2.
pose proof (q_ne_tkA HIx _ _ _ _ _ _ _ _ _ _ HP) as Hqtk. cbn [pf_tk] in Hqtk.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ tk 72 q (32 * mxd) HP (in_or_app _ LM _ (or_introl INtk)) (in_or_app _ LM _ (or_introl INq)) ltac:(congruence)) as Hdtq.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 5 HP INtk ltac:(lia)) as SHT5.
replace (tk / 8 + 5 + A_SB) with (tk / 8 + 2147450885) in SHT5 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 5 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT5c & SEPT5q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 5 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT5t & _).
cbn [hl_sb A4L] in SEPT5c, SEPT5q, SEPT5t. assert (EQx : tk / 8 + A_SB + 5 = tk / 8 + 2147450885) by (unfold A_SB; lia). rewrite EQx in SEPT5c, SEPT5q, SEPT5t. clear EQx.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 3 HP INtk ltac:(lia)) as SHT3.
replace (tk / 8 + 3 + A_SB) with (tk / 8 + 2147450883) in SHT3 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 3 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT3c & SEPT3q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 3 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT3t & _).
cbn [hl_sb A4L] in SEPT3c, SEPT3q, SEPT3t. assert (EQx : tk / 8 + A_SB + 3 = tk / 8 + 2147450883) by (unfold A_SB; lia). rewrite EQx in SEPT3c, SEPT3q, SEPT3t. clear EQx.
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
pose proof (munch_refl [(tk, tk + 72)] mp2) as MU.
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
assert (cs_tk_L : csep tk 72 bse (Z.of_nat 32)) by (unfold csep; clear - Hdtq HbseR; lia).
assert (cs_L_tk : csep bse 32 tk (Z.of_nat 72)) by (unfold csep; clear - Hdtq HbseR; lia).
assert (cs_T5_T : csep (tk / 8 + 2147450885) 1 tk (Z.of_nat 72)) by (unfold csep; clear - SEPT5t; lia).
assert (cs_T3_T : csep (tk / 8 + 2147450883) 1 tk (Z.of_nat 72)) by (unfold csep; clear - SEPT3t; lia).
assert (cs_T7_T : csep (tk / 8 + 2147450887) 1 tk (Z.of_nat 72)) by (unfold csep; clear - SEPT7t; lia).
assert (cs_T2_T : csep (tk / 8 + 2147450882) 1 tk (Z.of_nat 72)) by (unfold csep; clear - SEPT2t; lia).
assert (cs_Q0_T : csep (bse / 8 + 2147450880) 1 tk (Z.of_nat 72)) by (unfold csep; clear - SEPQ0t; lia).
clear Hdtq SEPT5q SEPT5t SEPT3q SEPT3t SEPT7q SEPT7t SEPT2q SEPT2t SEPT4q SEPT4t SEPQ0q SEPQ0t.
stash Himg_t2. stash Himg_q2.
reenterA asegs A4L HIx asegs_wx HP.
destruct OUT2 as [(-> & PBK2 & BK2) | [-> Epbs2]].
+ clear SHT4.
step. step.
if_true.
step.
asan_chkM 2.
stepz.
step.
asan_chkM 3.
stepz.
step.
asan_chkA.
stepz.
step.
asan_rechkA.
asan_rechkM 1.

set (x3 := TS isd (Z_to_bv 64 0) (Z_to_bv 64 co) err (Z_to_bv 64 0) (Z_to_bv 64 0) quote).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ mp2 mc, WMc : wmono asegs mp2 mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _ |- _ =>
destruct (PE_INV_A_tokw1 HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo mp2 mc md2 A2 B2 ts2
cb nb pj sv errv2 co x3 STC INV2 MUc WMc MIc TOKc ltac:(cbn [pf_len]; lia) eq_refl) as [INV3 PBT3];
clear MUc WMc; pose proof (munch_refl [(bse, bse + 32)] mc) as MUl; pose proof (wmono_refl asegs mc) as WMl
end end.
set (ts3 := ts_set_x ts2 co x3) in *.
clear SHT5 SHT3 SHT7 SHT2 cs_T5_T cs_T3_T cs_T7_T cs_T2_T cs_Q0_T.
step.
norm_sx32.
step.
rewrite (unsigned_lit (Z.of_nat depth)) by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32.
step.
replace (q + Z.of_nat depth * 32) with bse by lia.
step.
asan_chkA.
asan_chkM 1.
norm_sx32.
stepz.
step.

assert (Hl3 : nth_error (t_levels ts3) (t_depth ts3) = Some l) by exact Hl.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mcF _) =>
lazymatch goal with MUc : munch _ ?mb mcF, WMc : wmono asegs ?mb mcF, MIc : mem_inv asegs mcF, TOKc : rw_cells asegs mcF tk _, Lc : rw_cells asegs mcF bse _ |- _ =>
evt_done5; rewrite Hbse in MUc, Lc;
destruct (PE_INV_A_lvl_write HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo mb mcF md2 A2 B2 ts3
cb nb pj sv errv2 l (tl_ss l) (tl_ss l) c0 hn0 c0 STC INV3 Hl3 MUc WMc MIc TOKc Lc Hmode (HMODE c0 hn0 Hmode) SS26 SS26 (or_introl eq_refl)
ltac:(rewrite Hst, Hzss; reflexivity)) as [INV4 PBK4];
unstash Kredo; eapply (Kredo mcF md2 A2 B2 pbs2 errv2 _ _ _ _ _ _ _ _ _ _ _ _ _ F2 fc2 N92);
[ exact INV4
| apply PBK4; unfold PBOK; cbn [t_co ts3 ts_set_x]; apply PBT3; replace (co + (kP + 3)) with (co + kP + 3) by lia; exact PBK2
| exact (BOK_lvl_restate _ _ ts3 B2 nB l (tl_ss l) (tl_ss l) Hl3 (lvl_closed_keep l (tl_ss l) _ _ _ _ _ Hzss)
(BOK_set_x _ _ ts2 B2 nB co x3 ltac:(cbn [t_co ts2 ts_pbs ts0]; lia) (BOK_weaken _ _ _ _ _ nB (Nat.le_succ_diag_r nB) BK2)))
| exact FS2 | exact FRM2 ]
end end.
+ replace (Z_to_bv 64 (2^64 - 1)) with (Z_to_bv 64 (-1)) by (apply bv_eq; vm_compute; reflexivity).
step. step.
if_false.
step.
step.
asan_rechkM 2.
evt_done5.
unstash Kerr16. eapply (Kerr16 mp2 md2 A2 B2 errv2); [| exact FS2 | exact FRM2].
unfold ts2 in INV2. rewrite Epbs2 in INV2. exact INV2.
Qed.
End PeSNeedescA.
End RC__1.
End Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI QSHS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QJjn QRUw.Mq0 QRUw QRUw.Mq2. Import QPZI.Mq4. Import QkMG. Import QG8z QIsM.Mq2.
Import QbFI. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqj QsKa.Mqd Qiiq QsKa.Mqf Q4v2 QugP QlKV.Mqf QSHS Ql4f.Mq4 QsKa.Mqh QrQv.Mq4 QEUF.Mq2 QW22.Mq8 QdGy.Mq9. Import QlKV.Mq2. Import QnDr.Mq6.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section PeSCallAaA.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_pres : forall LB SP m m', heap_pres A4H LB SP m m' -> GA m -> GA m'.
Hypothesis SHRINK : jo_array_shrink_A2J HIx.

Lemma pe_shrink_cJ :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel) (kids : list (option jshape))
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP : Z) (nB : nat)
(ra gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
PBOK m ts kP -> BOK pf pa ts B nB ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_cs l = Some (Sarr kids) -> tl_ss l <> ST_finish -> tl_nbs l = [] ->
bv_unsigned ra mod 2 = 0 ->
(forall m2 md2 A2 B2 cbs2 errv2 r (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : word) F2 fc2,
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m2 md2 A2 B2 (ts_lvl ts (TL (tl_st l) (tl_ss l) (tl_cur l) (tl_cs l) cbs2 (tl_name l) (tl_nbs l))) cb nb pj sv errv2 ->
PBOK m2 (ts_lvl ts (TL (tl_st l) (tl_ss l) (tl_cur l) (tl_cs l) cbs2 (tl_name l) (tl_nbs l))) kP ->
(forall st', zin st' [ST_array_add; ST_ovadd] = false -> BOK pf pa (ts_lvl ts (TL st' ST_finish (tl_cur l) (tl_cs l) cbs2 (tl_name l) (tl_nbs l))) B2 nB) ->
(forall w, jtx (Sarr kids) (tl_cbs l) = Some (w, []) -> jtx (Sarr kids) cbs2 = Some (w, [])) ->
fsaved F F2 -> (frm0 fc -> frm0 fc2) ->
AJ5 A4L HIx A2 T md2
(MS (mkR ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) w0 w1 w2 s0 s1 (Z_to_bv 64 r) w3 w4 w5 w6 w7 w8 w9
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 w10 w11 w12 w13) F2 (ret_pc ra) fc2 None m2 (seg_rom asegs))) ->
AJ5 A4L HIx A T md
(MS (mkR ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2 s0 s1 (Z_to_bv 64 (tl_cur l)) (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xa0a14) fc None m (seg_rom asegs)).
Proof.
intros until fc. intros STC BSL INV PBK BK Hl Hcs Hop Hnbs RA K.
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
pose proof INV as [CORE REST1].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK1 & FR1).
pose proof REST1 as (HP1 & LV1 & OBJ1 & ST1 & ERR1 & _).
assert (Hd : (t_depth ts < length (t_levels ts))%nat) by (apply nth_error_Some; rewrite Hl; discriminate).
set (RB := pe_restblocks pf q LB0 ts).
pose proof (LV1 _ _ Hl) as LVd. pose proof LVd as (ST26 & SS26 & JO & Md). rewrite Hcs in JO. cbn [jopt] in JO. destruct JO as [Hc J].
assert (HPa : HEAPA A4L HIx A (tl_cbs l ++ RB) LM ((pa_F pa, 2) :: FRS) B m md).
{ eapply (heapA_perm A4L HIx); [exact HP1 | | apply Permutation_refl | apply Permutation_refl].
eapply Permutation_trans; [apply (pe_blocksA_cur_perm pf q LB0 ts l Hl)|]. unfold lvl_blocks. rewrite Hnbs, app_nil_r. apply Permutation_refl. }
pose proof (arr_capA_jval _ _ _ _ _ J) as (a_ & arr_ & rest_ & EABS & Hcap1 & Hcap2 & Hcap3).
assert (Hk28 : Z.of_nat (length kids) < 2^28).
{ assert (Hin : In (arr_, 8 * arr_capA (tl_cbs l)) (tl_cbs l ++ RB)).
{ apply in_or_app; left. set (c_ := arr_capA (tl_cbs l)) in *. rewrite EABS. right; right; left; reflexivity. }
pose proof (heapA_blk_le26 A4L HIx _ _ _ _ _ _ _ arr_ (8 * arr_capA (tl_cbs l)) HPa Hin). lia. }
destruct (BOK_arr_close pf pa ts B nB l kids BK BSL Hl Hcs (lvl_closed_open_ss l Hop)) as [COST BK2].
assert (SPF1 : lo <= pf_spf pf - (16 + 48 + 4096) /\ pf_spf pf mod 16 = 0 /\ pf_spf pf <= hiA_top A4L HIx /\ 0 <= pf_spf pf < 2^62).
{ clear - LOS HT Gle Gspf SP0. split; [lia|]. split; [Z.div_mod_to_equations; lia|]. split; lia. }
destruct SPF1 as (SPF1 & SPF2 & SPF3 & SPF4).
eapply SHRINK with (LB := RB) (ABS := tl_cbs l) (p := tl_cur l) (kids := kids) (lo := lo) (errv := errv) (FRS := (pa_F pa, 2) :: FRS);
[ | exact J | reflexivity | reflexivity | exact Hk28 | exact COST | ].
{ unfold jo_preA. rewrite !unsigned_lit by lia. split; [exact HPa|]. split; [exact ST1|]. split; [exact LO|]. split; [exact SPF1|]. split; [exact SPF2|]. split; [exact SPF3|].
split; [exact ERR1|]. split; [reflexivity | exact RA]. }
intros ms2 md2 m2 r A2 B2 (RS2 & VM2 & ST2 & HPR2 & (errv2 & ERR2)) HB2 HD2 (cbs2 & J2 & Hlen2 & _ & HP2 & JX2).
destruct RS2 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F2 & fc2 & -> & FS2 & FRM2).
cbn [hl_segs hl_tp hla_base A4L A4H] in *. rewrite ?(unsigned_lit (pf_spf pf)) in ST2 by lia. rewrite ?(unsigned_lit (pf_spf pf)) in HPR2 by lia.
set (l2 := TL (tl_st l) (tl_ss l) (tl_cur l) (tl_cs l) cbs2 (tl_name l) (tl_nbs l)).
assert (INtk : In (pf_tk pf, 72) RB) by (unfold RB, pe_restblocks; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * pf_mxd pf) RB) by (unfold RB, pe_restblocks; apply in_or_app; right; right; left; reflexivity).
assert (LB0R : incl LB0 RB) by (unfold RB, pe_restblocks; intros b Hb; apply in_or_app; right; right; right; exact Hb).
assert (AG : agree_on asegs RB m m2) by (eapply (agree_of_heap_pres asegs A4H); [exact HPR2 | reflexivity | intros b Hb; apply in_or_app; left; exact Hb]).
assert (FR2 : pe_frameA asegs m2 pf pa cb nb pj sv).
{ eapply pe_frameA_pres; [exact HPR2 | lia | exact GEO | | | exact FR1].
- apply in_or_app; right. apply in_or_app; right. change 248 with (fr_size 2 - 8). apply fr_ivs_frame. left; reflexivity.
- apply in_or_app; right. apply in_or_app; right. rewrite <- fr_shadow_len_2. change (shA (pa_F pa)) with (shad A4L (pa_F pa)). apply fr_ivs_shadow. left; reflexivity. }
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in TOK; [| eapply client_range_block; [apply in_or_app; left; exact INtk | lia | unfold tok_cells_g; cbn; lia]]. cbn [hl_segs hla_base A4L A4H] in TOK.
apply (tstack_pres_g A4H _ _ _ _ _ _ HPR2 (in_or_app _ _ _ (or_introl INq))) in TSK1; [| exact LEN32]. cbn [hl_segs hla_base A4L A4H] in TSK1.
assert (PBKa : PBOK m2 ts kP).
{ eapply PBOK_agree; [exact PBK | exact AG |]. unfold RB, pe_restblocks. intros b Hb. apply in_or_app; left. apply in_or_app; left. exact Hb. }
assert (HP2' : HEAPA A4L HIx A2 (pe_blocksA pf q LB0 (ts_lvl ts l2)) LM ((pa_F pa, 2) :: FRS) B2 m2 md2).
{ eapply (heapA_perm A4L HIx); [exact HP2 | | apply Permutation_refl | apply Permutation_refl].
apply Permutation_sym. eapply Permutation_trans; [apply (pe_blocksA_lvl_perm pf q LB0 ts l l2 Hl)|]. unfold lvl_blocks, l2. cbn [tl_cbs tl_nbs]. rewrite Hnbs, app_nil_r. apply Permutation_refl. }
assert (BUD2 : PE_BUD pf pa (ts_lvl ts l2) B2).
{ eapply PE_BUD_lvl_irrel; [| exact (BOK_weak _ _ _ _ _ (BK2 B2 cbs2 ST_eatws eq_refl Hlen2 HB2 HD2))]. reflexivity. }
assert (REST2 : PE_REST_A HIx GA pf pa q LB0 LM FRS payload me lo m2 md2 A2 B2 (ts_lvl ts l2) errv2).
{ eapply (PE_REST_A_callG HIx GA GA_pres) with (ts := ts) (LBc := RB); [exact STC | exact REST1 | exact VM2 | exact HPR2 | exact LB0R | exact HP2' | | | exact ST2 | exact ERR2 | exact BUD2].
- unfold ts_lvl; cbn [t_levels t_depth]. intros i li Hli.
destruct (PeanoNat.Nat.eq_dec i (t_depth ts)) as [-> | NE].
+ rewrite nth_error_lupd_eq in Hli by exact Hd. injection Hli as <-.
split; [exact ST26|]. split; [exact SS26|]. split; [cbn [tl_cs tl_cbs tl_cur l2]; rewrite Hcs; cbn [jopt]; split; [exact Hc | exact J2]|].
rewrite Nat.ltb_irrefl, Nat.eqb_refl in Md |- *. destruct Md as (c0 & hn0 & Hmode & CLS0 & NM0). exists c0, hn0. split; [exact Hmode|]. split; [exact CLS0|].
eapply (name_ok_agree asegs) with (BS := RB); [exact NM0 | exact AG |]. cbn [tl_nbs l2]. rewrite Hnbs. intros b [].
+ rewrite nth_error_lupd_neq in Hli by congruence.
eapply (lvl_cur_agree asegs A4F); [exact (LV1 i li Hli) | exact AG | exact (pe_restblocks_other pf q LB0 ts i li NE Hli)].
- unfold cur_st, ts_lvl in *; cbn [t_levels t_depth t_objs t_objbs t_obj] in *. rewrite nth_error_lupd_eq by exact Hd. cbn [tl_st l2]. rewrite Hl in OBJ1.
destruct (zin (tl_st l) [ST_array_add; ST_ovadd]); [| exact OBJ1].
eapply (jopt_agree asegs A4F); [exact OBJ1 | exact AG |]. unfold RB, pe_restblocks. intros b Hb. apply in_or_app; left. apply in_or_app; right. apply in_or_app; left. exact Hb. }
assert (INV2 : PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m2 md2 A2 B2 (ts_lvl ts l2) cb nb pj sv errv2).
{ split; [| exact REST2]. unfold PE_CORE_A, ts_lvl; cbn [t_levels t_depth t_co t_x t_pb t_pbs]. split; [rewrite lupd_length; exact LEN32|]. split; [exact D32|]. split; [exact CO|]. split; [exact CHOFF|].
split; [exact TOK|]. split; [exact (PBOK_pbuf _ _ _ PBKa)|]. split; [exact Hpb|]. split; [| exact FR2].
eapply tstack_lupd_srec; [exact TSK1 | exact Hl | reflexivity]. }
eapply (K m2 md2 A2 B2 cbs2 errv2 r); [exact INV2 | exact PBKa | intros st' Hz'; exact (BK2 B2 cbs2 st' Hz' Hlen2 HB2 HD2) | exact JX2 | exact FS2 | exact FRM2].
Qed.

Hypothesis AADD : jo_array_add_A2J HIx.

Lemma pe_aadd_cJ :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel) (kids : list (option jshape))
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP : Z) (nB : nat)
(ra gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
PBOK m ts kP -> BOK pf pa ts B (S (Z.to_nat 1280 + nB)) ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_array_add -> tl_cs l = Some (Sarr kids) -> tl_nbs l = [] ->
bv_unsigned ra mod 2 = 0 ->
(forall m2 md2 A2 B2 errv2 r (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : word) F2 fc2,
(r = 0 /\ exists cbs2,
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m2 md2 A2 B2
(ts_lvl_obj ts (TL (tl_st l) (tl_ss l) (tl_cur l) (Some (Sarr (kids ++ [t_objs ts]))) cbs2 (tl_name l) (tl_nbs l)) 0 None []) cb nb pj sv errv2 /\
PBOK m2 (ts_lvl_obj ts (TL (tl_st l) (tl_ss l) (tl_cur l) (Some (Sarr (kids ++ [t_objs ts]))) cbs2 (tl_name l) (tl_nbs l)) 0 None []) kP /\
(forall st' ss' obj' objs', ss' <> ST_finish ->
BOK pf pa (ts_lvl_obj ts (TL st' ss' (tl_cur l) (Some (Sarr (kids ++ [t_objs ts]))) cbs2 (tl_name l) (tl_nbs l)) obj' objs' []) B2 nB) /\
(forall w wv, jtx (Sarr kids) (tl_cbs l) = Some (w, []) -> jtx_opt (t_objs ts) (t_objbs ts) = Some (wv, []) ->
jtx (Sarr (kids ++ [t_objs ts])) cbs2 = Some (w + (2 + wv), [])))
\/ (r = 2^64 - 1 /\ PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m2 md2 A2 B2 ts cb nb pj sv errv2) ->
fsaved F F2 -> (frm0 fc -> frm0 fc2) ->
AJ5 A4L HIx A2 T md2
(MS (mkR ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) w0 w1 w2 s0 s1 (Z_to_bv 64 r) w3 w4 w5 w6 w7 w8 w9
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 w10 w11 w12 w13) F2 (ret_pc ra) fc2 None m2 (seg_rom asegs))) ->
AJ5 A4L HIx A T md
(MS (mkR ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2 s0 s1 (Z_to_bv 64 (tl_cur l)) (Z_to_bv 64 (t_obj ts)) a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xa097c) fc None m (seg_rom asegs)).
Proof.
intros until fc. intros STC BSL INV PBK BK Hl Hst Hcs Hnbs RA K.
assert (Hop : lvl_closed l = false) by (apply lvl_closed_open_st; rewrite Hst; reflexivity).
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
pose proof INV as [CORE REST1].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK1 & FR1).
pose proof REST1 as (HP1 & LV1 & OBJ1 & ST1 & ERR1 & _).
assert (Hd : (t_depth ts < length (t_levels ts))%nat) by (apply nth_error_Some; rewrite Hl; discriminate).
assert (JOB : jopt asegs A4F (t_objs ts) m (t_objbs ts) (t_obj ts)).
{ revert OBJ1. unfold cur_st. rewrite Hl, Hst. cbn. intros E; exact E. }
set (RB := pe_restblocks2 pf q LB0 ts).
pose proof (LV1 _ _ Hl) as LVd. pose proof LVd as (ST26 & SS26 & JO & Md). rewrite Hcs in JO. cbn [jopt] in JO. destruct JO as [Hc J].
assert (HPa : HEAPA A4L HIx A (tl_cbs l ++ t_objbs ts ++ RB) LM ((pa_F pa, 2) :: FRS) B m md).
{ eapply (heapA_perm A4L HIx); [exact HP1 | | apply Permutation_refl | apply Permutation_refl].
eapply Permutation_trans; [apply (pe_blocksA_cur_perm2 pf q LB0 ts l Hl)|]. unfold lvl_blocks. rewrite Hnbs, app_nil_r. apply Permutation_refl. }
pose proof (arr_capA_jval _ _ _ _ _ J) as (a_ & arr_ & rest_ & EABS & Hcap1 & Hcap2 & Hcap3).
assert (Hk28 : Z.of_nat (length kids) + 1 < 2^28).
{ assert (Hin : In (arr_, 8 * arr_capA (tl_cbs l)) ((tl_cbs l ++ t_objbs ts ++ RB))).
{ apply in_or_app; left. set (c_ := arr_capA (tl_cbs l)) in *. rewrite EABS. right; right; left; reflexivity. }
pose proof (heapA_blk_le26 A4L HIx _ _ _ _ _ _ _ arr_ (8 * arr_capA (tl_cbs l)) HPa Hin). lia. }
destruct (BOK_arr_add pf pa ts B nB l kids BK BSL Hl Hcs Hop) as (COST & BKF & BK2).
assert (SPF1 : lo <= pf_spf pf - (16 + 96 + 4096) /\ pf_spf pf mod 16 = 0 /\ pf_spf pf <= hiA_top A4L HIx /\ 0 <= pf_spf pf < 2^62).
{ clear - LOS HT Gle Gspf SP0. split; [lia|]. split; [Z.div_mod_to_equations; lia|]. split; lia. }
destruct SPF1 as (SPF1 & SPF2 & SPF3 & SPF4).
eapply AADD with (LB := RB) (ABS := tl_cbs l) (VBS := t_objbs ts) (p := tl_cur l) (v := t_obj ts) (kids := kids) (vs := t_objs ts) (lo := lo) (errv := errv) (FRS := (pa_F pa, 2) :: FRS);
[ | exact J | exact JOB | reflexivity | reflexivity | exact Hk28 | exact COST | ].
{ unfold jo_preA. rewrite !unsigned_lit by lia. split; [exact HPa|]. split; [exact ST1|]. split; [exact LO|]. split; [exact SPF1|]. split; [exact SPF2|]. split; [exact SPF3|].
split; [exact ERR1|]. split; [reflexivity | exact RA]. }
intros ms2 md2 m2 r A2 B2 (RS2 & VM2 & ST2 & HPR2 & (errv2 & ERR2)) HD2 OUT.
destruct RS2 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F2 & fc2 & -> & FS2 & FRM2).
cbn [hl_segs hl_tp hla_base A4L A4H] in *. rewrite ?(unsigned_lit (pf_spf pf)) in ST2 by lia. rewrite ?(unsigned_lit (pf_spf pf)) in HPR2 by lia.
assert (INtk : In (pf_tk pf, 72) RB) by (unfold RB, pe_restblocks2; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * pf_mxd pf) RB) by (unfold RB, pe_restblocks2; apply in_or_app; right; right; left; reflexivity).
assert (LB0R : incl LB0 RB) by (unfold RB, pe_restblocks2; intros b Hb; apply in_or_app; right; right; right; exact Hb).
assert (AG : agree_on asegs RB m m2) by (eapply (agree_of_heap_pres asegs A4H); [exact HPR2 | reflexivity | intros b Hb; apply in_or_app; left; exact Hb]).
assert (FR2 : pe_frameA asegs m2 pf pa cb nb pj sv).
{ eapply pe_frameA_pres; [exact HPR2 | lia | exact GEO | | | exact FR1].
- apply in_or_app; right. apply in_or_app; right. change 248 with (fr_size 2 - 8). apply fr_ivs_frame. left; reflexivity.
- apply in_or_app; right. apply in_or_app; right. rewrite <- fr_shadow_len_2. change (shA (pa_F pa)) with (shad A4L (pa_F pa)). apply fr_ivs_shadow. left; reflexivity. }
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in TOK; [| eapply client_range_block; [apply in_or_app; left; exact INtk | lia | unfold tok_cells_g; cbn; lia]]. cbn [hl_segs hla_base A4L A4H] in TOK.
apply (tstack_pres_g A4H _ _ _ _ _ _ HPR2 (in_or_app _ _ _ (or_introl INq))) in TSK1; [| exact LEN32]. cbn [hl_segs hla_base A4L A4H] in TSK1.
assert (PBKa : PBOK m2 ts kP).
{ eapply PBOK_agree; [exact PBK | exact AG |]. unfold RB, pe_restblocks2. intros b Hb. apply in_or_app; left. apply in_or_app; left. exact Hb. }
eapply (K m2 md2 A2 B2 errv2 r); [| exact FS2 | exact FRM2].
destruct OUT as [(-> & cbs2 & J2 & Hlen2 & GR2 & HB2 & HP2 & JX2) | (-> & HB2 & J2 & JOB2 & HP2)].
- left. split; [reflexivity|]. exists cbs2.
set (l2 := TL (tl_st l) (tl_ss l) (tl_cur l) (Some (Sarr (kids ++ [t_objs ts]))) cbs2 (tl_name l) (tl_nbs l)).
set (ts2 := ts_lvl_obj ts l2 0 None []).
assert (BK2' := fun st' ss' obj' objs' Hss' => BK2 B2 cbs2 st' ss' obj' objs' Hss' Hlen2 GR2 HB2 HD2).
assert (HP2' : HEAPA A4L HIx A2 (pe_blocksA pf q LB0 ts2) LM ((pa_F pa, 2) :: FRS) B2 m2 md2).
{ eapply (heapA_perm A4L HIx); [exact HP2 | | apply Permutation_refl | apply Permutation_refl].
apply Permutation_sym. eapply Permutation_trans; [apply (pe_blocksA_lvl_obj_perm pf q LB0 ts l l2 0 None [] Hl)|]. unfold lvl_blocks, l2. cbn [tl_cbs tl_nbs app]. rewrite Hnbs, app_nil_r. apply Permutation_refl. }
assert (BUD2 : PE_BUD pf pa ts2 B2).
{ eapply PE_BUD_lvl_obj_irrel; [| exact (BOK_weak _ _ _ _ _ (BK2' ST_eatws ST_array_sep 0 None ltac:(unfold ST_array_sep, ST_finish; lia)))]. reflexivity. }
assert (REST2 : PE_REST_A HIx GA pf pa q LB0 LM FRS payload me lo m2 md2 A2 B2 ts2 errv2).
{ eapply (PE_REST_A_callG HIx GA GA_pres) with (ts := ts) (LBc := RB); [exact STC | exact REST1 | exact VM2 | exact HPR2 | exact LB0R | exact HP2' | | | exact ST2 | exact ERR2 | exact BUD2].
- unfold ts2, ts_lvl_obj; cbn [t_levels t_depth]. intros i li Hli.
destruct (PeanoNat.Nat.eq_dec i (t_depth ts)) as [-> | NE].
+ rewrite nth_error_lupd_eq in Hli by exact Hd. injection Hli as <-.
split; [exact ST26|]. split; [exact SS26|]. split; [cbn [tl_cs tl_cbs tl_cur l2 jopt]; split; [exact Hc | exact J2]|].
rewrite Nat.ltb_irrefl, Nat.eqb_refl in Md |- *. destruct Md as (c0 & hn0 & Hmode & CLS0 & NM0). exists c0, hn0. split; [exact Hmode|].
split; [cbn [tl_cs l2]; rewrite Hcs in CLS0; destruct c0; cbn in CLS0 |- *; exact CLS0 |].
eapply (name_ok_agree asegs) with (BS := RB); [exact NM0 | exact AG |]. cbn [tl_nbs l2]. rewrite Hnbs. intros b [].
+ rewrite nth_error_lupd_neq in Hli by congruence.
eapply (lvl_cur_agree asegs A4F); [exact (LV1 i li Hli) | exact AG | exact (pe_restblocks2_other pf q LB0 ts i li NE Hli)].
- unfold cur_st, ts2, ts_lvl_obj; cbn [t_levels t_depth t_objs t_objbs t_obj]. rewrite nth_error_lupd_eq by exact Hd. cbn [tl_st l2]. rewrite Hst. cbn. split; reflexivity. }
split; [| split; [exact PBKa | split; [exact BK2' | exact JX2]]].
split; [| exact REST2]. unfold PE_CORE_A, ts2, ts_lvl_obj; cbn [t_levels t_depth t_co t_x t_pb t_pbs]. split; [rewrite lupd_length; exact LEN32|]. split; [exact D32|]. split; [exact CO|]. split; [exact CHOFF|].
split; [exact TOK|]. split; [exact (PBOK_pbuf _ _ _ PBKa)|]. split; [exact Hpb|]. split; [| exact FR2].
eapply tstack_lupd_srec; [exact TSK1 | exact Hl | reflexivity].
- right. split; [reflexivity|].
assert (HP2' : HEAPA A4L HIx A2 (pe_blocksA pf q LB0 ts) LM ((pa_F pa, 2) :: FRS) B2 m2 md2).
{ eapply (heapA_perm A4L HIx); [exact HP2 | | apply Permutation_refl | apply Permutation_refl].
apply Permutation_sym. eapply Permutation_trans; [apply (pe_blocksA_cur_perm2 pf q LB0 ts l Hl)|]. unfold lvl_blocks. rewrite Hnbs, app_nil_r. apply Permutation_refl. }
assert (REST2 : PE_REST_A HIx GA pf pa q LB0 LM FRS payload me lo m2 md2 A2 B2 ts errv2).
{ eapply (PE_REST_A_callG HIx GA GA_pres) with (ts := ts) (LBc := RB); [exact STC | exact REST1 | exact VM2 | exact HPR2 | exact LB0R | exact HP2' | | | exact ST2 | exact ERR2 | exact (BKF B2 HB2 HD2)].
- intros i li Hli.
destruct (PeanoNat.Nat.eq_dec i (t_depth ts)) as [-> | NE].
+ rewrite Hl in Hli. injection Hli as <-.
split; [exact ST26|]. split; [exact SS26|]. split; [rewrite Hcs; cbn [jopt]; split; [exact Hc | exact J2]|].
rewrite Nat.ltb_irrefl, Nat.eqb_refl in Md |- *. destruct Md as (c0 & hn0 & Hmode & CLS0 & NM0). exists c0, hn0. split; [exact Hmode|]. split; [exact CLS0|].
eapply (name_ok_agree asegs) with (BS := RB); [exact NM0 | exact AG |]. rewrite Hnbs. intros b [].
+ eapply (lvl_cur_agree asegs A4F); [exact (LV1 i li Hli) | exact AG | exact (pe_restblocks2_other pf q LB0 ts i li NE Hli)].
- unfold cur_st. rewrite Hl, Hst. cbn. exact JOB2. }
split; [| exact REST2]. split; [exact LEN32|]. split; [exact D32|]. split; [exact CO|]. split; [exact CHOFF|].
split; [exact TOK|]. split; [exact (PBOK_pbuf _ _ _ PBKa)|]. split; [exact Hpb|]. split; [exact TSK1 | exact FR2].
Qed.
End PeSCallAaA.
End RC__1.
End Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc5u QAzu.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QJjn QRUw.Mq0 QRUw QkMG. Import QG8z QIsM.Mq2.
Import Qhd4 Qwm6.
Import QbFI.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqj QsKa.Mqd Qiiq QsKa.Mqf Q4v2 QSHS Ql4f.Mq4 Q1Y6.Mq4 QsKa.Mqh QrQv.Mq4 QEUF.Mq2 QdGy.Mq9.
Import Qc5u QAzu.Mq0.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section PeSCstartA.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_outside : forall m m' W, GA m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= hl_img_lo A4H \/ hl_img_hi A4H <= fst iv) W -> GA m'.
Hypothesis GA_pres : forall LB SP m m', heap_pres A4H LB SP m m' -> GA m -> GA m'.

Hypothesis MAPP : memappend_A_stmt2 HIx.
Let PRW := PE_REST_A_private_write HIx GA GA_outside.

Ltac pe_openA STC INV :=
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR); pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk);
destruct INV as [CORE REST];
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR);
pose proof REST as (HP & LV & OBJ & ST & ERR & STR & PLEN & SBin & HPR & MDV & G & BUD).

Lemma seg_cstart_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (nB : nat)
(gp t0 a5 a7 s3 s6 s7 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
PBOK m ts 0 -> BOK pf pa ts B (S nB) ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_comment_start ->
t_co ts < pf_len pf ->

(forall m' md' A' B' st' pbs' errv' t0' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc',
(bv_unsigned cb = 42 /\ st' = ST_comment) \/ (bv_unsigned cb = 47 /\ st' = ST_comment_eol) ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B'
(ts_pbs (ts_lvl ts (TL st' (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) pbs') cb nb pj sv errv' ->
PBOK m' (ts_pbs (ts_lvl ts (TL st' (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) pbs') 1 ->
BOK pf pa (ts_pbs (ts_lvl ts (TL st' (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) pbs') B' nB ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msA asegs pf pa APE_BREAK (t_co ts) gp t0' a0' a1' a2' a3' a4' a5' a6' a7' s3 (Z_to_bv 64 2) s6 s7 (Z_to_bv 64 (Z.of_nat (t_depth ts))) s9 s11 t3' t4' t5' t6' F' fc' m')) ->

(forall m' md' A' B' st' errv' t0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc',
(bv_unsigned cb = 42 /\ st' = ST_comment) \/ (bv_unsigned cb = 47 /\ st' = ST_comment_eol) ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B'
(ts_lvl ts (TL st' (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) cb nb pj sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msO asegs pf pa APE_ERR2 gp t0' (Z_to_bv 64 (pf_lenr pf)) (Z_to_bv 64 (pf_tk pf + 32)) (Z_to_bv 64 16) a1' a2' a3' a4' a5' a6' a7' s3 (Z_to_bv 64 (pf_sb pf + t_co ts)) (Z_to_bv 64 2) s6 s7 (Z_to_bv 64 (Z.of_nat (t_depth ts))) s9 s11 t3' t4' t5' t6' F' fc' m')) ->

(forall a4',
bv_unsigned cb <> 42 -> bv_unsigned cb <> 47 ->
AJ5 A4L HIx A T md
(pe_msO asegs pf pa APE_ERR3 gp t0 (Z_to_bv 64 (pf_lenr pf)) (Z_to_bv 64 (pf_tk pf + 32)) (Z_to_bv 64 13) (Z_to_bv 64 (bv_unsigned cb)) (Z_to_bv 64 0) (Z_to_bv 64 (q / 8 + 4 * Z.of_nat (t_depth ts) + A_SB)) a4' a5 (Z_to_bv 64 APE_JTAB) a7 s3 (Z_to_bv 64 (pf_sb pf + t_co ts)) (Z_to_bv 64 2) s6 s7 (Z_to_bv 64 (Z.of_nat (t_depth ts))) s9 s11 t3 t4 t5 t6 F fc m)) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa (pe_jtA ST_comment_start) (t_co ts) gp t0 (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) (Z_to_bv 64 (tl_st l)) (Z_to_bv 64 0) (Z_to_bv 64 (q / 8 + 4 * Z.of_nat (t_depth ts) + A_SB)) (Z_to_bv 64 0) a5 (Z_to_bv 64 APE_JTAB) a7 s3 (Z_to_bv 64 q) s6 s7 (Z_to_bv 64 (Z.of_nat (t_depth ts))) s9 s11 t3 t4 t5 t6 F fc m).
Proof.
intros until fc. intros STC BSL INV PBK BK Hl Hst Hco Kbreak Kerr16 Kerr13. pose proof INV as INV0. pe_openA STC INV.
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
pose proof FR as FR0. unfold pe_frameA in FR. destruct FR as (SLOTS & GAP & SAVED & FF & FSH).
unfold pe_slotsA in SLOTS. cbn zeta in SLOTS. unfold ff_cellsA in FF.
unfold pe_msA in *.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * mxd) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t.
blk_factsA A4L HIx HP q (32 * mxd) Hqal Hqlo Hqhi Himg_q.
pose proof (q_ne_tkA HIx _ _ _ _ _ _ _ _ _ _ HP) as Hqtk. cbn [pf_tk] in Hqtk.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ tk 72 q (32 * mxd) HP (in_or_app _ LM _ (or_introl INtk)) (in_or_app _ LM _ (or_introl INq)) ltac:(congruence)) as Hdtq.

pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 1 HP INtk ltac:(lia)) as SHT1.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 1 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEP1c & SEP1q & SEP1i). cbn [hl_sb A4L] in SEP1c, SEP1q, SEP1i.
replace (tk / 8 + 1 + A_SB) with (tk / 8 + 2147450881) in SHT1 by (unfold A_SB; lia).
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 4 HP INtk ltac:(lia)) as SHT4.
replace (tk / 8 + 4 + A_SB) with (tk / 8 + 2147450884) in SHT4 by (unfold A_SB; lia).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs m) as WM.
pose proof (LV depth l Hl) as LVd. pose proof LVd as (ST26 & SS26 & _ & Md).
rewrite Nat.ltb_irrefl, Nat.eqb_refl in Md. destruct Md as (c0 & hn0 & Hmode & CLS0 & NM0).
pose proof (TSK depth l Hl) as Ld. remember (q + 32 * Z.of_nat depth) as bse eqn:Hbse in Ld. unfold srec_cells in Ld.
assert (HbseR : q <= bse /\ bse + 32 <= q + (32 * mxd)) by (subst bse; lia).
pose proof (stack_shadowA HIx _ _ _ _ _ _ _ q mxd (Z.of_nat depth) 0 HP INq ltac:(lia) ltac:(lia)) as SHQ.
replace (q / 8 + 4 * Z.of_nat depth + 0 + A_SB) with (q / 8 + 4 * Z.of_nat depth + A_SB) in SHQ by lia.
pose proof (munch_refl [(bse, bse + 32)] m) as MU.
pose proof (bv_unsigned_in_range 8 cb) as CBR; unfold bv_modulus in CBR; cbn in CBR.
unfold APE_BREAK, APE_ERR2, APE_ERR3, APE_JTAB in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
stash Himg_t. stash Himg_q. clear PB REST TSK HP LV OBJ HPR BUD GAP SAVED FSH.
reenterA asegs A4L HIx asegs_wx HP. rewrite Hst. unfold ST_comment_start. cbn [pe_jtA].
replace (q + 32 * Z.of_nat depth) with bse by lia.
step. step.
change (zxb cb) with (Z_to_bv 64 (bv_unsigned cb)).
step.

assert (TAIL : forall st' a1v a4v,
(bv_unsigned cb = 42 /\ st' = ST_comment) \/ (bv_unsigned cb = 47 /\ st' = ST_comment_eol) -> a1v = Z_to_bv 64 st' ->
evt asegs (AJ5e A4L HIx A T md)
(MS (mkR (Z_to_bv 64 (tk / 8 + 2147450882)) (Z_to_bv 64 spf) gp (Z_to_bv 64 6444320) t0 (Z_to_bv 64 lenr) (Z_to_bv 64 (tk + 32)) (Z_to_bv 64 sp0) (Z_to_bv 64 spf) (Z_to_bv 64 bse) a1v (Z_to_bv 64 0) (Z_to_bv 64 (q / 8 + 4 * Z.of_nat depth + 2147450880)) a4v a5 (Z_to_bv 64 142504) a7 (Z_to_bv 64 (Ff / 8 + 2147450880)) s3 (Z_to_bv 64 (sb + co)) (Z_to_bv 64 2) s6 s7 (Z_to_bv 64 (Z.of_nat depth)) s9 (Z_to_bv 64 2147450880) s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x97e58) fc None m (seg_rom asegs))).
{ intros st' a1v a4v Hst' ->.
assert (ST'R : 0 <= st' <= 26) by (unfold ST_comment, ST_comment_eol in Hst'; lia).
assert (WS' : zin st' ws_states = true) by (destruct Hst' as [[_ ->]|[_ ->]]; reflexivity).
step. rewrite ?sxb_zero, ?zxb_zero. step. if_false.
stepz.
step.
asan_chkB.
step.
step.
step. step.

set (l1 := TL st' (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, Lc : rw_cells asegs mc bse _ |- _ =>
evt_done5; subst bse;
destruct (PE_INV_A_lvl_write HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m mc md A B ts0
cb nb pj sv errv l st' (tl_ss l) c0 hn0 c0 STC INV0 Hl MUc WMc MIc TOKc Lc Hmode
ltac:(rewrite <- Hmode; apply QIsM.Mq2.lvl_mode_ws_same; [rewrite Hst; reflexivity | exact WS']) ST'R SS26 (or_introl eq_refl)
ltac:(rewrite Hst; destruct Hst' as [[_ ->]|[_ ->]]; reflexivity)) as [INV1 PBK1]
end end.
eapply (pe_memappend_c HIx GA GA_pres MAPP (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo _ md A B (ts_lvl ts0 l1) cb nb pj sv errv T);
[exact STC | exact BSL | exact INV1 | exact (PBK1 0 PBK) | exact (BOK_lvl_restate _ _ ts0 B (S nB) l st' (tl_ss l) Hl (lvl_closed_keep l st' _ _ _ _ _ ltac:(destruct Hst' as [[_ ->]|[_ ->]]; reflexivity)) BK) | exact Hco | rewrite unsigned_lit by lia; reflexivity |].
intros m2 md2 A2 B2 pbs2 errv2 r w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 F2 fc2 INV2 OUT2 FS2 FRM2.
cbn [pf_spf] in *. unfold A_TP in *.

pose proof INV2 as [CORE2 REST2]. destruct CORE2 as (_ & _ & _ & _ & _ & _ & _ & _ & FR2). pose proof (proj1 REST2) as HP2.
assert (INtk2 : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 (ts_pbs (ts_lvl ts0 l1) pbs2))) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 4 HP2 INtk2 ltac:(lia)) as SHT4b.
replace (tk / 8 + 4 + A_SB) with (tk / 8 + 2147450884) in SHT4b by (unfold A_SB; lia).
pose proof FR2 as (SLOTS2 & _). unfold pe_slotsA in SLOTS2. cbn zeta in SLOTS2. cbn [pf_tk pf_spf pf_lenr pa_F pa_sp0 pa_oldloc pa_newloc] in SLOTS2. unfold shA in SLOTS2. a4l. unfold SB2, SB4, SB7, SB8 in SLOTS2.
clear REST2 FR2 INV1 PBK1 INV0 PBK BK.
reenterA asegs A4L HIx asegs_wx HP2.
destruct OUT2 as [(-> & PBK2 & BK2) | [-> Epbs2]].
- do 4 step.
if_true.
evt_done5.
eapply (Kbreak m2 md2 A2 B2 st' pbs2 errv2); [exact Hst' | exact INV2 | exact PBK2 | exact (BOK_weaken _ _ _ _ _ nB (Nat.le_succ_diag_r nB) BK2) | exact FS2 | exact FRM2].
- replace (Z_to_bv 64 (2^64 - 1)) with (Z_to_bv 64 (-1)) by (apply bv_eq; vm_compute; reflexivity).
do 4 step.
if_false.
step.
step.
step. rewrite ?sxb_zero, ?zxb_zero. step. if_true.
step. step.
evt_done5.
eapply (Kerr16 m2 md2 A2 B2 st' errv2); [exact Hst' | | exact FS2 | exact FRM2].
subst pbs2. exact INV2. }
destruct (Z.eq_dec (bv_unsigned cb) 42) as [C42 | N42].
- step.
if_truex.
step. step.

apply (TAIL ST_comment _ _); [left; split; [exact C42 | reflexivity] | reflexivity].
- step.
if_falsex.
step. step.
destruct (Z.eq_dec (bv_unsigned cb) 47) as [C47 | N47].
+ step.
if_truex.
step.
step.

apply (TAIL ST_comment_eol _ _); [right; split; [exact C47 | reflexivity] | reflexivity].
+ step.
if_falsex.
step.
step.
step. rewrite ?sxb_zero, ?zxb_zero. step. if_true.
step. step.
evt_done5.
subst bse. eapply Kerr13; [exact N42 | exact N47].
Qed.
End PeSCstartA.
End RC__1.
End Mq3.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QJjn QRUw.Mq0 QRUw QkMG. Import QG8z Qdyh.Mq0 Qdyh.Mq3 Qdyh.Mq4 QIsM.Mq2 Qa8x.Mq2 Qa8x.Mq3.
Import Qhd4 Qwm6.
Import QbFI.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqj QsKa.Mqd Qiiq QsKa.Mqf Q4v2 QlKV.Mqf QSHS Ql4f.Mq4 Q1Y6.Mq4 QsKa.Mqh QrQv.Mq4 QEUF.Mq2 QW22.Mq8 QdGy.Mq9 QYZ0.Mq8.
Import Qc5u QAzu.Mq0.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section PeSNeedescA.
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

Ltac reopen_inv INVx TSx ts0 PF q LB0 tk mxd depth l Hl bse Hbse mX :=
pose proof INVx as [CORE2 REST2];
destruct CORE2 as (_ & _ & _ & _ & TOK & _ & _ & TSK & FR);
pose proof REST2 as (HP & _); clear REST2;
try unfold TSx in TOK, TSK; try unfold ts_pbs, ts_lvl, ts_set_x in TOK, TSK; try unfold ts0 in TOK, TSK;
cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_tk pf_mxd pf_fl] in TOK, TSK;
unfold tok_cells_g in TOK; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK;
unfold pe_frameA in FR; destruct FR as (SLOTS & _ & _ & _ & _); unfold pe_slotsA in SLOTS; cbn zeta in SLOTS;
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in SLOTS;
assert (INtk : In (tk, 72) (pe_blocksA PF q LB0 TSx)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity);
assert (INq : In (q, 32 * mxd) (pe_blocksA PF q LB0 TSx)) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity);
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI;
pose proof (wmono_refl asegs mX) as WM;
pose proof (TSK depth l Hl) as Ld; rewrite <- Hbse in Ld; unfold srec_cells in Ld;
clear TSK.

Lemma seg_needesc_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP : Z) (nB : nat)
(gp t0 a5 a7 s3 s6 s7 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv -> PBOK m ts kP -> kP + 3 <= 1 -> BOK pf pa ts B (S nB) ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_esc_need_escape ->
t_co ts < pf_len pf ->
bytes_at asegs me UTF8REP_ADDR_A Qa8x.Mq3.utf8rep ->

(forall c hn, lvl_mode (tl_st l) (tl_ss l) = Some (c, hn) -> lvl_mode (tl_ss l) (tl_ss l) = Some (c, hn)) ->
zin (tl_ss l) [ST_array_add; ST_ovadd] = false ->

(forall m' a1' a4',
bv_unsigned cb = 92 ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md A B
(ts_lvl ts (TL ST_esc_need_u (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) cb nb pj sv errv ->
PBOK m' (ts_lvl ts (TL ST_esc_need_u (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) kP ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa APE_BREAK (t_co ts) gp t0 (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) a1' (Z_to_bv 64 0) (Z_to_bv 64 (q / 8 + 4 * Z.of_nat (t_depth ts) + A_SB)) a4' a5 (Z_to_bv 64 APE_JTAB) a7 s3 (Z_to_bv 64 2) s6 s7 (Z_to_bv 64 (Z.of_nat (t_depth ts))) s9 s11 t3 t4 t5 t6 F fc m')) ->

(forall m' md' A' B' pbs' errv' gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc',
bv_unsigned cb <> 92 ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B'
(ts_lvl (ts_set_x (ts_pbs ts pbs') (t_co ts) (TS (ts_isd (t_x ts)) (Z_to_bv 64 0) (ts_choff (t_x ts)) (ts_err (t_x ts)) (Z_to_bv 64 0) (Z_to_bv 64 0) (ts_quote (t_x ts))))
(TL (tl_ss l) (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) cb nb pj sv errv' ->
PBOK m' (ts_lvl (ts_set_x (ts_pbs ts pbs') (t_co ts) (TS (ts_isd (t_x ts)) (Z_to_bv 64 0) (ts_choff (t_x ts)) (ts_err (t_x ts)) (Z_to_bv 64 0) (Z_to_bv 64 0) (ts_quote (t_x ts))))
(TL (tl_ss l) (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) (kP + 3) ->
BOK pf pa (ts_lvl (ts_set_x (ts_pbs ts pbs') (t_co ts) (TS (ts_isd (t_x ts)) (Z_to_bv 64 0) (ts_choff (t_x ts)) (ts_err (t_x ts)) (Z_to_bv 64 0) (Z_to_bv 64 0) (ts_quote (t_x ts))))
(TL (tl_ss l) (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) B' nB ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msA asegs pf pa APE_REDO (t_co ts) gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' m')) ->

(forall m' md' A' B' errv' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' ts cb nb pj sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msO asegs pf pa APE_ERRMEM gp' t0' t1' t2' (Z_to_bv 64 (pf_tk pf + 36)) a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' m')) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa (pe_jtA ST_esc_need_escape) (t_co ts) gp t0 (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) (Z_to_bv 64 (tl_st l)) (Z_to_bv 64 0) (Z_to_bv 64 (q / 8 + 4 * Z.of_nat (t_depth ts) + A_SB)) (Z_to_bv 64 0) a5 (Z_to_bv 64 APE_JTAB) a7 s3 (Z_to_bv 64 q) s6 s7 (Z_to_bv 64 (Z.of_nat (t_depth ts))) s9 s11 t3 t4 t5 t6 F fc m).
Proof.
intros until fc. intros STC BSL INV PBK HkP BK Hl Hst Hco UTF HMODE Hzss Kadv Kredo Kerr16. pose proof INV as INV0. pe_openA STC INV.
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
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 4 HP INtk ltac:(lia)) as SHT4.
replace (tk / 8 + 4 + A_SB) with (tk / 8 + 2147450884) in SHT4 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 4 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT4c & SEPT4q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 4 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT4t & _).
cbn [hl_sb A4L] in SEPT4c, SEPT4q, SEPT4t. assert (EQx : tk / 8 + A_SB + 4 = tk / 8 + 2147450884) by (unfold A_SB; lia). rewrite EQx in SEPT4c, SEPT4q, SEPT4t. clear EQx.
unfold APE_BREAK, APE_STBRK, APE_REDO, APE_OUT, APE_ERRMEM, APE_JTAB in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
assert (cs_tk_L : csep tk 72 bse (Z.of_nat 32)) by (unfold csep; clear - Hdtq HbseR; lia).
assert (cs_L_tk : csep bse 32 tk (Z.of_nat 72)) by (unfold csep; clear - Hdtq HbseR; lia).
assert (cs_T4_L : csep (tk / 8 + 2147450884) 1 bse (Z.of_nat 32)) by (unfold csep; clear - SEPT4q HbseR; lia).
clear Hdtq SEPT4q SEPT4t SEPT4c.
assert (SRC : bytes_at asegs m UTF8REP_ADDR_A Qa8x.Mq3.utf8rep).
{ eapply (heap_presx_bytes_at A4H); [exact HPR | exact UTF |]. right; left. intros a Ha. cbn [length Qa8x.Mq3.utf8rep Z.of_nat Pos.of_succ_nat Pos.succ] in Ha. unfold UTF8REP_ADDR_A in Ha.
cbn [hl_client_static A4H]. unfold a4_client_static, a4_volatile. lia. }
stash Himg_t. stash Himg_q. stash Kadv. stash Kredo. stash Kerr16. clear PB REST TSK LV OBJ HPR BUD GAP SAVED FSH STR ERR SBin.
reenterA asegs A4L HIx asegs_wx HP. rewrite Hst. unfold ST_esc_need_escape. cbn [pe_jtA].
replace (q + 32 * Z.of_nat depth) with bse by lia.
step. step.
change (zxb cb) with (Z_to_bv 64 (bv_unsigned cb)).
step.
destruct (Z.eq_dec (bv_unsigned cb) 92) as [C92 | N92].
- clear SRC FF SHT.
step.
if_falsex.
step.
asan_rechkMB 1.
step. step.
stepz.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, Lc : rw_cells asegs mc bse _ |- _ =>
evt_done5; subst bse;
destruct (PE_INV_A_lvl_write HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m mc md A B ts0
cb nb pj sv errv l ST_esc_need_u (tl_ss l) c0 hn0 c0 STC INV0 Hl MUc WMc MIc TOKc Lc Hmode
ltac:(rewrite <- Hmode; apply Qa8x.Mq3.lvl_mode_esc_same; [rewrite Hst; reflexivity | reflexivity | exact SS26]) ltac:(unfold ST_esc_need_u; lia) SS26 (or_introl eq_refl)
ltac:(rewrite Hst; reflexivity)) as [INV3 PBK3];
unstash Kadv; eapply (Kadv mc _ _ C92); [exact INV3 | exact (PBK3 kP PBK)]
end end.
- step.
if_truex.
step.
asan_chkMB 1.
step.
step. step.
step.
step.
evt_done5.
eapply (pe_memappend_g HIx GA GA_pres MAPP (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m md A B ts0 cb nb pj sv errv T UTF8REP_ADDR_A 3 (co + kP) Qa8x.Mq3.utf8rep);
[ exact STC | exact BSL | exact INV0 | exact PBK | cbn [t_co ts0]; lia | lia | exact BK | rewrite unsigned_lit by lia; reflexivity
| exact SRC | reflexivity | unfold UTF8REP_ADDR_A; lia | apply utf8rep_src_locA | intros _; exact (unpoisoned_of_glob HIx _ _ _ _ _ _ _ _ _ HP utf8rep_src_globA ltac:(lia)) |].
intros mp2 md2 A2 B2 pbs2 errv2 r w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 F2 fc2 INV2 OUT2 FS2 FRM2.
cbn [pf_spf] in *. unfold A_TP in *.
clear TOK SLOTS FF SHT SHQ SHQ4 SHT4 Ld MU WM MI HP INtk INq Htal Htlo Hthi Hqal Hqlo Hqhi Hqtk cs_tk_L cs_L_tk cs_T4_L SRC INV0 PBK BK.
set (ts2 := ts_pbs ts0 pbs2) in *.
reopen_inv INV2 ts2 ts0 (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 tk mxd depth l Hl bse Hbse mp2.
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t2.
blk_factsA A4L HIx HP q (32 * mxd) Hqal Hqlo Hqhi Himg_q2.
pose proof (q_ne_tkA HIx _ _ _ _ _ _ _ _ _ _ HP) as Hqtk. cbn [pf_tk] in Hqtk.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ tk 72 q (32 * mxd) HP (in_or_app _ LM _ (or_introl INtk)) (in_or_app _ LM _ (or_introl INq)) ltac:(congruence)) as Hdtq.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 5 HP INtk ltac:(lia)) as SHT5.
replace (tk / 8 + 5 + A_SB) with (tk / 8 + 2147450885) in SHT5 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 5 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT5c & SEPT5q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 5 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT5t & _).
cbn [hl_sb A4L] in SEPT5c, SEPT5q, SEPT5t. assert (EQx : tk / 8 + A_SB + 5 = tk / 8 + 2147450885) by (unfold A_SB; lia). rewrite EQx in SEPT5c, SEPT5q, SEPT5t. clear EQx.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 3 HP INtk ltac:(lia)) as SHT3.
replace (tk / 8 + 3 + A_SB) with (tk / 8 + 2147450883) in SHT3 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 3 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT3c & SEPT3q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 3 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT3t & _).
cbn [hl_sb A4L] in SEPT3c, SEPT3q, SEPT3t. assert (EQx : tk / 8 + A_SB + 3 = tk / 8 + 2147450883) by (unfold A_SB; lia). rewrite EQx in SEPT3c, SEPT3q, SEPT3t. clear EQx.
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
pose proof (munch_refl [(tk, tk + 72)] mp2) as MU.
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
assert (cs_tk_L : csep tk 72 bse (Z.of_nat 32)) by (unfold csep; clear - Hdtq HbseR; lia).
assert (cs_L_tk : csep bse 32 tk (Z.of_nat 72)) by (unfold csep; clear - Hdtq HbseR; lia).
assert (cs_T5_T : csep (tk / 8 + 2147450885) 1 tk (Z.of_nat 72)) by (unfold csep; clear - SEPT5t; lia).
assert (cs_T3_T : csep (tk / 8 + 2147450883) 1 tk (Z.of_nat 72)) by (unfold csep; clear - SEPT3t; lia).
assert (cs_T7_T : csep (tk / 8 + 2147450887) 1 tk (Z.of_nat 72)) by (unfold csep; clear - SEPT7t; lia).
assert (cs_T2_T : csep (tk / 8 + 2147450882) 1 tk (Z.of_nat 72)) by (unfold csep; clear - SEPT2t; lia).
assert (cs_Q0_T : csep (bse / 8 + 2147450880) 1 tk (Z.of_nat 72)) by (unfold csep; clear - SEPQ0t; lia).
clear Hdtq SEPT5q SEPT5t SEPT3q SEPT3t SEPT7q SEPT7t SEPT2q SEPT2t SEPT4q SEPT4t SEPQ0q SEPQ0t.
stash Himg_t2. stash Himg_q2.
reenterA asegs A4L HIx asegs_wx HP.
destruct OUT2 as [(-> & PBK2 & BK2) | [-> Epbs2]].
+ clear SHT4.
step.
if_true.
step.
asan_chkMB 1.
stepz.
asan_chkMB 2.
stepz.
step.
asan_chkB.
stepz.
step.
asan_rechkB.
asan_rechkMB 2.

set (x3 := TS isd (Z_to_bv 64 0) (Z_to_bv 64 co) err (Z_to_bv 64 0) (Z_to_bv 64 0) quote).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ mp2 mc, WMc : wmono asegs mp2 mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _ |- _ =>
destruct (PE_INV_A_tokw1 HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo mp2 mc md2 A2 B2 ts2
cb nb pj sv errv2 co x3 STC INV2 MUc WMc MIc TOKc ltac:(cbn [pf_len]; lia) eq_refl) as [INV3 PBT3];
clear MUc WMc; pose proof (munch_refl [(bse, bse + 32)] mc) as MUl; pose proof (wmono_refl asegs mc) as WMl
end end.
set (ts3 := ts_set_x ts2 co x3) in *.
clear SHT5 SHT3 SHT7 SHT2 cs_T5_T cs_T3_T cs_T7_T cs_T2_T cs_Q0_T.
assert (BLO : 0 < bse < 2^63 /\ q <= bse) by (subst bse; lia).
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
asan_chkMB 1.
norm_sx32.
stepz.
step.

assert (Hl3 : nth_error (t_levels ts3) (t_depth ts3) = Some l) by exact Hl.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mcF _) =>
lazymatch goal with MUc : munch _ ?mb mcF, WMc : wmono asegs ?mb mcF, MIc : mem_inv asegs mcF, TOKc : rw_cells asegs mcF tk _, Lc : rw_cells asegs mcF bse _ |- _ =>
evt_done5; rewrite Hbse in MUc, Lc;
destruct (PE_INV_A_lvl_write HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo mb mcF md2 A2 B2 ts3
cb nb pj sv errv2 l (tl_ss l) (tl_ss l) c0 hn0 c0 STC INV3 Hl3 MUc WMc MIc TOKc Lc Hmode (HMODE c0 hn0 Hmode) SS26 SS26 (or_introl eq_refl)
ltac:(rewrite Hst, Hzss; reflexivity)) as [INV4 PBK4];
unstash Kredo; eapply (Kredo mcF md2 A2 B2 pbs2 errv2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F2 fc2 N92);
[ exact INV4
| apply PBK4; unfold PBOK; cbn [t_co ts3 ts_set_x]; apply PBT3; replace (co + (kP + 3)) with (co + kP + 3) by lia; exact PBK2
| exact (BOK_lvl_restate _ _ ts3 B2 nB l (tl_ss l) (tl_ss l) Hl3 (lvl_closed_keep l (tl_ss l) _ _ _ _ _ Hzss)
(BOK_set_x _ _ ts2 B2 nB co x3 ltac:(cbn [t_co ts2 ts_pbs ts0]; lia) (BOK_weaken _ _ _ _ _ nB (Nat.le_succ_diag_r nB) BK2)))
| exact FS2 | exact FRM2 ]
end end.
+ replace (Z_to_bv 64 (2^64 - 1)) with (Z_to_bv 64 (-1)) by (apply bv_eq; vm_compute; reflexivity).
step.
if_false.
step. step.
asan_rechkMB 2.
evt_done5.
unstash Kerr16. eapply (Kerr16 mp2 md2 A2 B2 errv2); [| exact FS2 | exact FRM2].
unfold ts2 in INV2. rewrite Epbs2 in INV2. exact INV2.
Qed.
End PeSNeedescA.
End RC__1.
End Mq4.

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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QG8z. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QIsM.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdGy.Mq2.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section PeSCstartA.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_outside : forall m m' W, GA m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= hl_img_lo A4H \/ hl_img_hi A4H <= fst iv) W -> GA m'.
Hypothesis GA_pres : forall LB SP m m', heap_pres A4H LB SP m m' -> GA m -> GA m'.

Hypothesis MAPP : memappend_A_stmt2 HIx.
Let PRW := PE_REST_A_private_write HIx GA GA_outside.

Ltac pe_openA STC INV :=
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR); pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk);
destruct INV as [CORE REST];
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR);
pose proof REST as (HP & LV & OBJ & ST & ERR & STR & PLEN & SBin & HPR & MDV & G & BUD).

Lemma seg_cstart_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (nB : nat)
(gp t0 t1 t2 a3 a5 a6 a7 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
PBOK m ts 0 -> BOK pf pa ts B (S nB) ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_comment_start ->
t_co ts < pf_len pf ->

(forall m' md' A' B' st' pbs' errv' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' F' fc',
(bv_unsigned cb = 42 /\ st' = ST_comment) \/ (bv_unsigned cb = 47 /\ st' = ST_comment_eol) ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B'
(ts_pbs (ts_lvl ts (TL st' (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) pbs') cb nb pj sv errv' ->
PBOK m' (ts_pbs (ts_lvl ts (TL st' (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) pbs') 1 ->
BOK pf pa (ts_pbs (ts_lvl ts (TL st' (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) pbs') B' nB ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msA asegs pf pa APE_BREAK (t_co ts) gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5'
(Z_to_bv 64 (pf_tk pf + 56)) (Z_to_bv 64 (pa_F pa + 64)) F' fc' m')) ->

(forall m' md' A' B' st' errv' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' F' fc',
(bv_unsigned cb = 42 /\ st' = ST_comment) \/ (bv_unsigned cb = 47 /\ st' = ST_comment_eol) ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B'
(ts_lvl ts (TL st' (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) cb nb pj sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msA asegs pf pa APE_ERRMEM (t_co ts) gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5'
(Z_to_bv 64 (pf_tk pf + 56)) (Z_to_bv 64 (pa_F pa + 64)) F' fc' m')) ->

(forall a1' a3',
bv_unsigned cb <> 42 -> bv_unsigned cb <> 47 ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa APE_ERR2 (t_co ts) gp t0 t1 t2 (Z_to_bv 64 13) a1'
(Z_to_bv 64 (q / 8 + 4 * Z.of_nat (t_depth ts) + A_SB)) a3' (Z_to_bv 64 APE_JTAB) a5 a6 a7
(Z_to_bv 64 (Z.of_nat (t_depth ts))) (Z_to_bv 64 q) (Z_to_bv 64 (pa_F pa + 64)) F fc m)) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa (pe_jtA ST_comment_start) (t_co ts) gp t0 t1 t2
(Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) (Z_to_bv 64 (tl_st l))
(Z_to_bv 64 (q / 8 + 4 * Z.of_nat (t_depth ts) + A_SB)) a3 (Z_to_bv 64 APE_JTAB) a5 a6 a7
(Z_to_bv 64 (Z.of_nat (t_depth ts))) (Z_to_bv 64 q) (Z_to_bv 64 (pa_F pa + 64)) F fc m).
Proof.
intros until fc. intros STC BSL INV PBK BK Hl Hst Hco Kbreak Kerr16 Kerr13. pose proof INV as INV0. pe_openA STC INV.
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
pose proof FR as FR0. unfold pe_frameA in FR. destruct FR as (SLOTS & GAP & SAVED & FF & FSH).
unfold pe_slotsA in SLOTS. cbn zeta in SLOTS. unfold ff_cellsA in FF.
unfold pe_msA in *.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * mxd) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t.
blk_factsA A4L HIx HP q (32 * mxd) Hqal Hqlo Hqhi Himg_q.
pose proof (q_ne_tkA HIx _ _ _ _ _ _ _ _ _ _ HP) as Hqtk. cbn [pf_tk] in Hqtk.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ tk 72 q (32 * mxd) HP (in_or_app _ LM _ (or_introl INtk)) (in_or_app _ LM _ (or_introl INq)) ltac:(congruence)) as Hdtq.

pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 1 HP INtk ltac:(lia)) as SHT1.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 1 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEP1c & SEP1q & SEP1i). cbn [hl_sb A4L] in SEP1c, SEP1q, SEP1i.
replace (tk / 8 + 1 + A_SB) with (tk / 8 + 2147450881) in SHT1 by (unfold A_SB; lia).
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 4 HP INtk ltac:(lia)) as SHT4.
replace (tk / 8 + 4 + A_SB) with (tk / 8 + 2147450884) in SHT4 by (unfold A_SB; lia).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs m) as WM.
pose proof (LV depth l Hl) as LVd. pose proof LVd as (ST26 & SS26 & _ & Md).
rewrite Nat.ltb_irrefl, Nat.eqb_refl in Md. destruct Md as (c0 & hn0 & Hmode & CLS0 & NM0).
pose proof (TSK depth l Hl) as Ld. remember (q + 32 * Z.of_nat depth) as bse eqn:Hbse in Ld. unfold srec_cells in Ld.
assert (HbseR : q <= bse /\ bse + 32 <= q + (32 * mxd)) by (subst bse; lia).
pose proof (stack_shadowA HIx _ _ _ _ _ _ _ q mxd (Z.of_nat depth) 0 HP INq ltac:(lia) ltac:(lia)) as SHQ.
replace (q / 8 + 4 * Z.of_nat depth + 0 + A_SB) with (q / 8 + 4 * Z.of_nat depth + A_SB) in SHQ by lia.
pose proof (munch_refl [(bse, bse + 32)] m) as MU.
pose proof (bv_unsigned_in_range 8 cb) as CBR; unfold bv_modulus in CBR; cbn in CBR.
unfold APE_BREAK, APE_ERRMEM, APE_ERR2, APE_JTAB in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
stash Himg_t. stash Himg_q. clear PB REST TSK HP LV OBJ HPR BUD GAP SAVED FSH.
reenterA asegs A4L HIx asegs_wx HP. rewrite Hst. unfold ST_comment_start. cbn [pe_jtA].
replace (q + 32 * Z.of_nat depth) with bse by lia.
step.
change (zxb cb) with (Z_to_bv 64 (bv_unsigned cb)).
step.

assert (TAIL : forall st' a1v a3v,
(bv_unsigned cb = 42 /\ st' = ST_comment) \/ (bv_unsigned cb = 47 /\ st' = ST_comment_eol) -> a1v = Z_to_bv 64 st' ->
evt asegs (AJ5e A4L HIx A T md)
(MS (mkR (Z_to_bv 64 (tk / 8 + 2147450884)) (Z_to_bv 64 spf) gp (Z_to_bv 64 6434400) t0 t1 t2
(Z_to_bv 64 sp0) (Z_to_bv 64 spf) (Z_to_bv 64 bse) a1v (Z_to_bv 64 (q / 8 + 4 * Z.of_nat depth + 2147450880)) a3v (Z_to_bv 64 142392) a5 a6 a7
(Z_to_bv 64 (Ff / 8 + 2147450880)) (Z_to_bv 64 (tk / 8 + 2147450882)) (Z_to_bv 64 (tk + 20)) (Z_to_bv 64 (Z.of_nat depth)) (Z_to_bv 64 (tk + 36))
(Z_to_bv 64 (tk + 32)) (Z_to_bv 64 Ff) (Z_to_bv 64 2147450880) (Z_to_bv 64 q) (Z_to_bv 64 (sb + co))
(Z_to_bv 64 (tk + 64)) (Z_to_bv 64 (Ff + 64)) (Z_to_bv 64 (tk / 8 + 2147450888)) (Z_to_bv 64 lenr))
F (Z_to_bv 64 0x96c58) fc None m (seg_rom asegs))).
{ intros st' a1v a3v Hst' ->.
assert (ST'R : 0 <= st' <= 26) by (unfold ST_comment, ST_comment_eol in Hst'; lia).
assert (WS' : zin st' ws_states = true) by (destruct Hst' as [[_ ->]|[_ ->]]; reflexivity).
step.
asan_rechkA.
stepz.
asan_chkM 1.
step.
step.
step. step.

set (l1 := TL st' (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, Lc : rw_cells asegs mc bse _ |- _ =>
evt_done5; subst bse;
destruct (PE_INV_A_lvl_write HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m mc md A B ts0
cb nb pj sv errv l st' (tl_ss l) c0 hn0 c0 STC INV0 Hl MUc WMc MIc TOKc Lc Hmode
ltac:(rewrite <- Hmode; apply QIsM.Mq2.lvl_mode_ws_same; [rewrite Hst; reflexivity | exact WS']) ST'R SS26 (or_introl eq_refl)
ltac:(rewrite Hst; destruct Hst' as [[_ ->]|[_ ->]]; reflexivity)) as [INV1 PBK1]
end end.
eapply (pe_memappend_c HIx GA GA_pres MAPP (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo _ md A B (ts_lvl ts0 l1) cb nb pj sv errv T);
[exact STC | exact BSL | exact INV1 | exact (PBK1 0 PBK) | exact (BOK_lvl_restate _ _ ts0 B (S nB) l st' (tl_ss l) Hl (lvl_closed_keep l st' _ _ _ _ _ ltac:(destruct Hst' as [[_ ->]|[_ ->]]; reflexivity)) BK) | exact Hco | rewrite unsigned_lit by lia; reflexivity |].
intros m2 md2 A2 B2 pbs2 errv2 r w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 F2 fc2 INV2 OUT2 FS2 FRM2.
cbn [pf_spf] in *. unfold A_TP in *.

pose proof INV2 as [CORE2 REST2]. destruct CORE2 as (_ & _ & _ & _ & _ & _ & _ & _ & FR2). pose proof (proj1 REST2) as HP2.
assert (INtk2 : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 (ts_pbs (ts_lvl ts0 l1) pbs2))) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 4 HP2 INtk2 ltac:(lia)) as SHT4b.
replace (tk / 8 + 4 + A_SB) with (tk / 8 + 2147450884) in SHT4b by (unfold A_SB; lia).
pose proof FR2 as (SLOTS2 & _). unfold pe_slotsA in SLOTS2. cbn zeta in SLOTS2. cbn [pf_tk pf_spf pf_lenr pa_F pa_sp0 pa_oldloc pa_newloc] in SLOTS2. unfold shA in SLOTS2. a4l. unfold SB2, SB4, SB7, SB8 in SLOTS2.
clear REST2 FR2 INV1 PBK1 INV0 PBK BK.
reenterA asegs A4L HIx asegs_wx HP2.
destruct OUT2 as [(-> & PBK2 & BK2) | [-> Epbs2]].
- do 6 step.
if_true.
evt_done5.
eapply (Kbreak m2 md2 A2 B2 st' pbs2 errv2); [exact Hst' | exact INV2 | exact PBK2 | exact (BOK_weaken _ _ _ _ _ nB (Nat.le_succ_diag_r nB) BK2) | exact FS2 | exact FRM2].
- replace (Z_to_bv 64 (2^64 - 1)) with (Z_to_bv 64 (-1)) by (apply bv_eq; vm_compute; reflexivity).
do 6 step.
if_false.
step.
step.
asan_rechkA.
evt_done5.
eapply (Kerr16 m2 md2 A2 B2 st' errv2); [exact Hst' | | exact FS2 | exact FRM2].
subst pbs2. exact INV2. }
destruct (Z.eq_dec (bv_unsigned cb) 42) as [C42 | N42].
- step.
if_truex.
step.

apply (TAIL ST_comment _ _); [left; split; [exact C42 | reflexivity] | reflexivity].
- step.
if_falsex.
step.
destruct (Z.eq_dec (bv_unsigned cb) 47) as [C47 | N47].
+ step.
if_truex.
step.
step.

apply (TAIL ST_comment_eol _ _); [right; split; [exact C47 | reflexivity] | reflexivity].
+ step.
if_falsex.
step.
step.
asan_rechkA.
step. step.
evt_done5.
subst bse. eapply Kerr13; [exact N42 | exact N47].
Qed.
End PeSCstartA.
End RC__1.
