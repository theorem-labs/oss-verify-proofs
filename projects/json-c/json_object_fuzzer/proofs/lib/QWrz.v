(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup Lib.GwApply QWxq_c1 QRjH QHnV QCcH QfLs Q0Ek Qtgi QjDH Qsw7 QJjn QRUw QkMG QG8z Qdyh Q8tj Qu4M Q7UD Qhd4 Qwm6 QlKV QsKa Qiiq Q4v2 Q1Y6 Qoif Q1Ey Ql4f QrQv QEUF Qeia QYZ0 Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QJjn QRUw.Mq0 QRUw QkMG. Import QG8z Qdyh.Mq0. Import Q8tj. Import Qu4M.Mq0.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa QsKa.Mq4 Qiiq.Mq0 QsKa.Mq6 Q4v2.Mq0 QsKa.Mq5 Q1Y6.Mq0 Qoif.Mq0 Q1Ey Ql4f.Mq1 QsKa.Mq8 QrQv.Mq2 QEUF Qeia.Mq0 QYZ0.Mq4.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import QlKV.Mq2 QEUF.Mq0.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Lemma obj_capA_jval : forall m kids BS p rc,
jval asegs A4F (Sobj kids) m BS p rc ->
exists t tbl rest, BS = (p, 48) :: (t, 56) :: (tbl, 40 * obj_capA BS) :: rest /\ In (obj_capA BS) lf_sizes.
Proof.
intros m kids BS p rc J. cbn [jval] in J.
destruct J as (pb & PBS & REST & EBS & _ & t & TBS & kvs & KBS & EREST & _ & (tbl & size & es & svs & _ & ETBS & LO) & _).
destruct LO as (_ & _ & _ & _ & INS & _ & _). pose proof (lf_size_range size INS) as SR.
subst TBS REST BS. unfold lh_blocks.
exists t, tbl, ((map (fun e => (le_k e, le_kn e)) es ++ concat KBS) ++ PBS). unfold obj_capA. cbn [app nth snd].
rewrite (Z.mul_comm 40 size), Z.div_mul by lia. split; [rewrite (Z.mul_comm size 40), <- !app_assoc; reflexivity | exact INS].
Qed.

Section PeSCallOaA.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_presx : forall LB SP m m', heap_presx A4H a4_volatile LB SP m m' -> lh_globA m' -> GA m -> GA m'.
Hypothesis GA_lh : forall m, GA m -> lh_globA m.
Variable HD : Z.
Hypothesis HD_le : 64 + 96 + 4096 + 128 + HD <= 12288.
Hypothesis OADD : jo_object_add_A HIx HD.

Lemma pe_oadd_c :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel) (kids : list (option jshape))
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP : Z) (nB : nat)
(ra gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
PBOK m ts kP -> BOK pf pa ts B (S (Z.to_nat (16 * Z.max 0 (pf_len pf) + 8192) + nB)) ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_ovadd -> tl_cs l = Some (Sobj kids) ->
frm0 fc -> Z.of_nat (length FRS) + 2 < 4096 -> bv_unsigned ra mod 2 = 0 ->
(forall m2 md2 A2 B2 errv2 r (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : word) F2 fc2,
(r = 0 /\ exists cbs2 kids2,
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m2 md2 A2 B2
(ts_lvl_obj ts (TL (tl_st l) (tl_ss l) (tl_cur l) (Some (Sobj kids2)) cbs2 (tl_name l) (tl_nbs l)) 0 None []) cb nb pj sv errv2 /\
PBOK m2 (ts_lvl_obj ts (TL (tl_st l) (tl_ss l) (tl_cur l) (Some (Sobj kids2)) cbs2 (tl_name l) (tl_nbs l)) 0 None []) kP /\
Z.of_nat (length kids2) <= Z.of_nat (length kids) + 1 /\ okmax kids2 <= Z.max (okmax kids) (odep (t_objs ts)) /\
(forall st' ss' obj' objs', (ss' <> ST_finish \/ zin st' [ST_array_add; ST_ovadd] = true) ->
BOK pf pa (ts_lvl_obj ts (TL st' ss' (tl_cur l) (Some (Sobj kids2)) cbs2 (tl_name l) (tl_nbs l)) obj' objs' []) B2 nB) /\
(forall w wv nm nn, tl_nbs l = [(nm, nn)] -> jtx (Sobj kids) (tl_cbs l) = Some (w, []) -> jtx_opt (t_objs ts) (t_objbs ts) = Some (wv, []) ->
exists w', jtx (Sobj kids2) cbs2 = Some (w', []) /\ w' <= w + key_w nn + wv))
\/ (r = 2^64 - 1 /\ exists LK, PE_INVW_A HIx GA pf pa q LB0 LM FRS payload me lo m2 md2 A2 B2 ts LK cb nb pj sv errv2) ->
fsaved F F2 -> (frm0 fc -> frm0 fc2) ->
AJ5 A4L HIx A2 T md2
(MS (mkR ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) w0 w1 w2 s0 s1 (Z_to_bv 64 r) w3 w4 w5 w6 w7 w8 w9
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 w10 w11 w12 w13) F2 (ret_pc ra) fc2 None m2 (seg_rom asegs))) ->
AJ5 A4L HIx A T md
(MS (mkR ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2 s0 s1 (Z_to_bv 64 (tl_cur l)) (Z_to_bv 64 (tl_name l)) (Z_to_bv 64 (t_obj ts)) a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x9be64) fc None m (seg_rom asegs)).
Proof.
intros until fc. intros STC BSL INV PBK BK Hl Hst Hcs FRM FRN RA K.
assert (Hop : lvl_closed l = false) by (apply lvl_closed_open_st; rewrite Hst; reflexivity).
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
pose proof INV as [CORE REST1].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK1 & FR1).
pose proof REST1 as (HP1 & LV1 & OBJ1 & ST1 & ERR1 & _ & _ & _ & _ & _ & G1 & _).
assert (Hd : (t_depth ts < length (t_levels ts))%nat) by (apply nth_error_Some; rewrite Hl; discriminate).
assert (JOB : jopt asegs A4F (t_objs ts) m (t_objbs ts) (t_obj ts)).
{ revert OBJ1. unfold cur_st. rewrite Hl, Hst. cbn. intros E; exact E. }
set (RB := pe_restblocks2 pf q LB0 ts).
pose proof (LV1 _ _ Hl) as LVd. pose proof LVd as (ST26 & SS26 & JO & Md). rewrite Hcs in JO. cbn [jopt] in JO. destruct JO as [Hc J].
rewrite Nat.ltb_irrefl, Nat.eqb_refl in Md. destruct Md as (c0 & hn0 & Hmode & CLS0 & NM0).
rewrite Hst, lvl_mode_ovadd in Hmode. injection Hmode as <- <-. cbn [name_ok] in NM0. destruct NM0 as (Hn0 & nn & ks & Hnbs & Hnn & CSTR).
set (LBk := (tl_name l, nn) :: RB).
assert (PERM0 : Permutation (pe_blocksA pf q LB0 ts) (tl_cbs l ++ t_objbs ts ++ LBk)).
{ eapply Permutation_trans; [apply (pe_blocksA_cur_perm2 pf q LB0 ts l Hl)|]. unfold lvl_blocks, LBk. rewrite Hnbs, <- app_assoc. apply Permutation_app_head.
cbn [app]. apply Permutation_middle. }
assert (HPa : HEAPA A4L HIx A (tl_cbs l ++ t_objbs ts ++ LBk) LM ((pa_F pa, 2) :: FRS) B m md)
by (eapply (heapA_perm A4L HIx); [exact HP1 | exact PERM0 | apply Permutation_refl | apply Permutation_refl]).
destruct (obj_capA_jval _ _ _ _ _ J) as (t_ & tbl_ & rest_ & EOBS & INSZ).
assert (Hcap29 : obj_capA (tl_cbs l) <= 2^29).
{ assert (Hin : In (tbl_, 40 * obj_capA (tl_cbs l)) (tl_cbs l ++ t_objbs ts ++ LBk)).
{ apply in_or_app; left. set (c_ := obj_capA (tl_cbs l)) in *. rewrite EOBS. right; right; left; reflexivity. }
pose proof (heapA_blk_le26 A4L HIx _ _ _ _ _ _ _ tbl_ (40 * obj_capA (tl_cbs l)) HPa Hin). lia. }
assert (Hklen : 0 <= Z.of_nat (length ks) <= Z.max 0 (pf_len pf)).
{ pose proof (BOK_name_bound pf pa ts B _ l (tl_name l) nn BK Hl Hnbs) as NB. destruct CSTR as (CL & _). lia. }
destruct (BOK_obj_add pf pa ts B nB l kids (Z.of_nat (length ks)) BK BSL Hl Hcs Hop Hklen Hcap29) as (COST & COSTR & BKF & BK2).
assert (SPF1 : lo <= pf_spf pf - (64 + 96 + 4096 + 128 + HD) /\ pf_spf pf mod 16 = 0 /\ pf_spf pf <= hiA_top A4L HIx /\ 0 <= pf_spf pf < 2^62).
{ clear - LOS HT Gle Gspf SP0 HD_le. split; [lia|]. split; [Z.div_mod_to_equations; lia|]. split; lia. }
destruct SPF1 as (SPF1 & SPF2 & SPF3 & SPF4).
eapply OADD with (LB := LBk) (OBS := tl_cbs l) (VBS := t_objbs ts) (p := tl_cur l) (v := t_obj ts) (k := tl_name l) (kn := nn) (ks := ks) (kids := kids) (vs := t_objs ts)
(lo := lo) (errv := errv) (FRS := (pa_F pa, 2) :: FRS);
[ | exact (GA_lh _ G1) | exact J | exact JOB | left; reflexivity | exact CSTR | lia | exact FRM | cbn [length]; rewrite Nat2Z.inj_succ; clear - FRN; lia | reflexivity | reflexivity | reflexivity | exact COST | exact COSTR
| exact (proj2 (heapA_budget A4L HIx _ _ _ _ _ _ _ HP1)) | ].
{ unfold jo_preA. rewrite !unsigned_lit by lia. split; [exact HPa|]. split; [exact ST1|]. split; [exact LO|]. split; [exact SPF1|]. split; [exact SPF2|]. split; [exact SPF3|].
split; [exact ERR1|]. split; [reflexivity | exact RA]. }
intros ms2 md2 m2 r A2 B2 (RS2 & VM2 & ST2 & HPR2 & (errv2 & ERR2)) LG2 HD2 OUT.
destruct RS2 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F2 & fc2 & -> & FS2 & FRM2).
cbn [hl_segs hl_tp hla_base A4L A4H] in *. rewrite ?(unsigned_lit (pf_spf pf)) in ST2 by lia. rewrite ?(unsigned_lit (pf_spf pf)) in HPR2 by lia.
assert (INtk : In (pf_tk pf, 72) LBk) by (unfold LBk, RB, pe_restblocks2; right; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * pf_mxd pf) LBk) by (unfold LBk, RB, pe_restblocks2; right; apply in_or_app; right; right; left; reflexivity).
assert (LB0R : incl LB0 LBk) by (unfold LBk, RB, pe_restblocks2; intros b Hb; right; apply in_or_app; right; right; right; exact Hb).
assert (AG : agree_on asegs LBk m m2) by (eapply (agree_of_heap_presx asegs A4H); [exact HPR2 | reflexivity | intros b Hb; apply in_or_app; left; exact Hb]).
assert (FR2 : pe_frameA asegs m2 pf pa cb nb pj sv).
{ eapply pe_frameA_presx; [exact HPR2 | lia | exact GEO | | | exact FR1].
- apply in_or_app; right. apply in_or_app; right. change 248 with (fr_size 2 - 8). apply fr_ivs_frame. left; reflexivity.
- apply in_or_app; right. apply in_or_app; right. rewrite <- fr_shadow_len_2. change (shA (pa_F pa)) with (shad A4L (pa_F pa)). apply fr_ivs_shadow. left; reflexivity. }
apply (heap_presx_rw_cells A4H _ _ _ _ _ _ _ HPR2) in TOK; [| eapply client_rangex_block; [apply in_or_app; left; exact INtk | lia | unfold tok_cells_g; cbn; lia]]. cbn [hl_segs hla_base A4L A4H] in TOK.
apply (tstack_presx_g A4H _ _ _ _ _ _ _ HPR2 (in_or_app _ _ _ (or_introl INq))) in TSK1; [| exact LEN32]. cbn [hl_segs hla_base A4L A4H] in TSK1.
assert (PBKa : PBOK m2 ts kP).
{ eapply PBOK_agree; [exact PBK | exact AG |]. unfold LBk, RB, pe_restblocks2. intros b Hb. right. apply in_or_app; left. apply in_or_app; left. exact Hb. }
assert (CSTR2 : cstr asegs m2 (tl_name l) nn ks) by (eapply (cstr_agree asegs) with (BS := LBk); [exact CSTR | exact AG | left; reflexivity | lia]).
assert (LVo : forall i li, nth_error (t_levels ts) i = Some li -> i <> t_depth ts -> lvl_cur asegs A4F m2 (t_depth ts) i li).
{ intros i li Hli NE. eapply (lvl_cur_agree asegs A4F); [exact (LV1 i li Hli) | exact AG |].
intros b Hb. right. exact (pe_restblocks2_other pf q LB0 ts i li NE Hli b Hb). }
eapply (K m2 md2 A2 B2 errv2 r); [| exact FS2 | exact FRM2].
destruct OUT as [(-> & cbs2 & kids2 & J2 & HP2 & LENK & DEPK & CASES) | (-> & REM & J2 & JOB2 & HP2 & HB2)].
- left. split; [reflexivity|]. exists cbs2, kids2.
set (l2 := TL (tl_st l) (tl_ss l) (tl_cur l) (Some (Sobj kids2)) cbs2 (tl_name l) (tl_nbs l)).
set (ts2 := ts_lvl_obj ts l2 0 None []).
assert (BK2' : forall st' ss' obj' objs', (ss' <> ST_finish \/ zin st' [ST_array_add; ST_ovadd] = true) ->
BOK pf pa (ts_lvl_obj ts (TL st' ss' (tl_cur l) (Some (Sobj kids2)) cbs2 (tl_name l) (tl_nbs l)) obj' objs' []) B2 nB).
{ intros st' ss' obj' objs' Hss'. apply (BK2 B2 cbs2 kids2 st' ss' obj' objs' Hss'); [| exact HD2].
destruct CASES as [(E1 & E2 & E3 & E4 & _) | (E1 & E2 & E3 & E4 & _)]; [left | right]; (split; [exact E1 | split; [exact E2 | split; [exact E3 | exact E4]]]). }
assert (HP2' : HEAPA A4L HIx A2 (pe_blocksA pf q LB0 ts2) LM ((pa_F pa, 2) :: FRS) B2 m2 md2).
{ eapply (heapA_perm A4L HIx); [exact HP2 | | apply Permutation_refl | apply Permutation_refl].
apply Permutation_sym. eapply Permutation_trans; [apply (pe_blocksA_lvl_obj_perm pf q LB0 ts l l2 0 None [] Hl)|]. unfold lvl_blocks, l2, LBk. cbn [tl_cbs tl_nbs app]. rewrite Hnbs, <- app_assoc.
apply Permutation_app_head. cbn [app]. apply Permutation_refl. }
assert (BUD2 : PE_BUD pf pa ts2 B2).
{ eapply PE_BUD_lvl_obj_irrel; [| exact (BOK_weak _ _ _ _ _ (BK2' ST_eatws ST_osep 0 None ltac:(left; unfold ST_osep, ST_finish; lia)))]. reflexivity. }
assert (REST2 : PE_REST_A HIx GA pf pa q LB0 LM FRS payload me lo m2 md2 A2 B2 ts2 errv2).
{ eapply (PE_REST_A_callGx HIx GA GA_presx) with (ts := ts) (LBc := LBk); [exact STC | exact REST1 | exact VM2 | exact HPR2 | exact LG2 | exact LB0R | exact HP2' | | | exact ST2 | exact ERR2 | exact BUD2].
- unfold ts2, ts_lvl_obj; cbn [t_levels t_depth]. intros i li Hli.
destruct (PeanoNat.Nat.eq_dec i (t_depth ts)) as [-> | NE].
+ rewrite nth_error_lupd_eq in Hli by exact Hd. injection Hli as <-.
split; [exact ST26|]. split; [exact SS26|]. split; [cbn [tl_cs tl_cbs tl_cur l2 jopt]; split; [exact Hc | exact J2]|].
rewrite Nat.ltb_irrefl, Nat.eqb_refl. exists CObj, true. split; [cbn [tl_st tl_ss l2]; rewrite Hst; apply lvl_mode_ovadd|].
split; [cbn [tl_cs l2]; exact I|]. cbn [name_ok tl_name tl_nbs l2]. split; [exact Hn0|]. exists nn, ks. split; [exact Hnbs|]. split; [exact Hnn | exact CSTR2].
+ rewrite nth_error_lupd_neq in Hli by congruence. exact (LVo i li Hli NE).
- unfold cur_st, ts2, ts_lvl_obj; cbn [t_levels t_depth t_objs t_objbs t_obj]. rewrite nth_error_lupd_eq by exact Hd. cbn [tl_st l2]. rewrite Hst. cbn. split; reflexivity. }
split; [| split; [exact PBKa | split; [exact LENK | split; [exact DEPK | split; [exact BK2' |]]]]].
2:{ intros w wv nm nn' Enbs Hw Hwv. rewrite Hnbs in Enbs. injection Enbs as _ Enn. subst nn'. destruct CSTR2 as (Lks & _).
destruct CASES as [(_ & _ & _ & _ & JX) | (_ & _ & _ & _ & JX)].
- exists (w + (key_w (Z.of_nat (length ks) + 1) + wv)). split; [exact (JX w wv Hw Hwv) | unfold key_w; lia].
- destruct (JX w wv Hw Hwv) as (w' & E' & L'). exists w'. split; [exact E' | unfold key_w; lia]. }
split; [| exact REST2]. unfold PE_CORE_A, ts2, ts_lvl_obj; cbn [t_levels t_depth t_co t_x t_pb t_pbs]. split; [rewrite lupd_length; exact LEN32|]. split; [exact D32|]. split; [exact CO|]. split; [exact CHOFF|].
split; [exact TOK|]. split; [exact (PBOK_pbuf _ _ _ PBKa)|]. split; [exact Hpb|]. split; [| exact FR2].
eapply tstack_lupd_srec; [exact TSK1 | exact Hl | reflexivity].
- right. split; [reflexivity|]. exists REM.
split; [split; [exact LEN32|]; split; [exact D32|]; split; [exact CO|]; split; [exact CHOFF|]; split; [exact TOK|]; split; [exact (PBOK_pbuf _ _ _ PBKa)|]; split; [exact Hpb|]; split; [exact TSK1 | exact FR2]|].
apply PE_REST_A_base in REST1 as (BASE1 & _ & _ & _).
split; [| split].
+ eapply (PE_BASE_A_callGx HIx GA GA_presx) with (LBc := LBk); [exact STC | exact BASE1 | exact VM2 | exact HPR2 | exact LG2 | exact LB0R | | exact ST2 | exact ERR2].
eapply (heapA_perm A4L HIx); [exact HP2 | | apply Permutation_refl | apply Permutation_refl].
apply (Permutation_trans (l' := (tl_cbs l ++ t_objbs ts ++ LBk) ++ REM)).
* rewrite <- !app_assoc. apply Permutation_app_head. apply Permutation_app_head. apply Permutation_app_comm.
* apply Permutation_app_tail. apply Permutation_sym. exact PERM0.
+ intros i li Hli.
destruct (PeanoNat.Nat.eq_dec i (t_depth ts)) as [-> | NE].
* rewrite Hl in Hli. injection Hli as <-. apply lvl_cur_weakA.
split; [exact ST26|]. split; [exact SS26|]. split; [rewrite Hcs; cbn [jopt]; split; [exact Hc | exact J2]|].
rewrite Nat.ltb_irrefl, Nat.eqb_refl. exists CObj, true. split; [rewrite Hst; apply lvl_mode_ovadd|]. split; [rewrite Hcs; exact I|].
cbn [name_ok]. split; [exact Hn0|]. exists nn, ks. split; [exact Hnbs|]. split; [exact Hnn | exact CSTR2].
* apply lvl_cur_weakA. exact (LVo i li Hli NE).
+ exact (BKF B2 HB2 HD2).
Qed.
End PeSCallOaA.
End RC__1.
End Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLbz Q2Sr QArX QdGy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QJjn QRUw.Mq0 QRUw QkMG. Import QG8z Qdyh.Mq2 QLbz Q2Sr.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QsKa.Mq4 Qiiq.Mq0 Q1Ey Ql4f.Mq1 Q1Y6.Mq2 QArX QrQv.Mq1 QYZ0.Mq1 QrQv.Mq2 QEUF QdGy.Mq5.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import QlKV.Mq2 QEUF.Mq1.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Lemma PBS_set_co : forall ts co', PBS (ts_set_co ts co') = PBS ts.
Proof. intros [d lv co pb pbs x o os obs] co'. reflexivity. Qed.
Lemma NAO_set_co : forall ts co', NAO ts -> NAO (ts_set_co ts co').
Proof. intros [d lv co pb pbs x o os obs] co' H. exact H. Qed.

Lemma PBJ_set_co : forall m m' ts k, (forall b, PBOKat m ts b -> PBOKat m' (ts_set_co ts (t_co ts + 1)) b) ->
PBJ m ts (k + 1) (t_co ts + 1) -> PBJ m' (ts_set_co ts (t_co ts + 1)) k (t_co (ts_set_co ts (t_co ts + 1))).
Proof.
intros m m' ts k PBT (g & P & Hg & J). exists g. split; [exact (PBT _ P)|]. split; [unfold ts_set_co; cbn [t_co]; lia|].
unfold ts_set_co at 2; cbn [t_co]. eapply (JL_same ts); [reflexivity | reflexivity | intros _; split; reflexivity | exact J].
Qed.
Section PeSMasterA.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_outside : forall m m' W, GA m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= hl_img_lo A4H \/ hl_img_hi A4H <= fst iv) W -> GA m'.
Variables (pf : pe_fix) (pa : pe_fixA) (q : Z) (LBc LM : list blk) (FRS : list frame) (payload : list byte)
(me : word -> option byte) (lo : Z) (sv : pe_saved) (T : TSet) (F0 : bvmap 5 word) (utf8rep : list byte).
Hypothesis STC : PE_STATIC_A HIx pf pa lo.
Hypothesis CSTR : CSTR_OK pf payload.
Hypothesis UTF : bytes_at asegs me UTF8REP_ADDR_A utf8rep.

Notation KOUTx := (KOUT_S HIx GA pf pa q LBc LM FRS payload me lo sv T F0).
Notation KERR2x := (KERR2_S HIx GA pf pa q LBc LM FRS payload me lo sv T F0).
Notation KALLx := (KALL_S HIx GA pf pa q LBc LM FRS payload me lo sv T F0).
Notation CASEx := (CASE_S HIx GA pf pa q LBc LM FRS payload me lo sv T F0 utf8rep).

Hypothesis KO : KOUTx.
Hypothesis KE : KERR2x.
Hypothesis HC : forall st, 0 <= st <= 26 -> CASEx st.

Local Ltac tdsame TD := first [ exact TD
| lazymatch type of TD with tdepth_ok ?tsd => eapply (tdepth_ok_same tsd); [ | | | exact TD]; unfold ts_set_co, ts_set_err; cbn [t_levels t_depth t_objs pf_mxd]; reflexivity end ].

Theorem pe_master_S : forall n, KALLx n.
Proof.
induction n as [|n IH].
- split; [| split; [| split]]; intros until fc; intros M; exfalso; lia.
- pose proof IH as IHall. destruct IH as (IHL & IHR & IHB & IHA).
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR).
split; [| split; [| split]].
+
intros ts m md A B cb nb pj errv gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 t4 F fc M INV NN SP TD CLT PBK BK NA FS FRM.
eapply (seg_loop_A HIx GA GA_outside); [exact STC | exact INV | exact CLT | |].
*
intros m' c nb' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' Hco Hc INV' PBT'.
eapply (IHR ts m' md A B c nb' pj errv); [| exact INV' | exact Hco | exact Hc | intros E; exfalso; exact (NN E) | exact SP | exact TD
| destruct PBK as (g & P & Hg & J); exists g; split; [exact (PBT' _ P) | split; [exact Hg | exact J]] | | apply OBJW_of_NAO; exact NA | exact FS | exact FRM].
-- unfold mloop, mredo in *. pose proof (rank_le (cur_st ts) (cur_ss ts)). lia.
-- eapply BOK_weaken; [| exact BK]. unfold bloop, bredo, mloop, mredo. pose proof (rank_le (cur_st ts) (cur_ss ts)). lia.
*
intros m' e x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' s11' t4' t6' INV'.
eapply KO; [apply (PE_INV_A_W HIx GA); exact INV' | tdsame TD | | exact FS | exact FRM].
eapply (JOUT_of_PBJ (pf_len pf) m ts (ts_set_err ts e)); [exact PBK | pose proof INV as [(_ & _ & CO9 & _) _]; lia | reflexivity | reflexivity | intros _; split; reflexivity].
+
intros ts m md A B cb nb pj errv gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 F fc M INV Hco Hcb NUM SP TD PBK BK OW FS FRM.
pose proof INV as [(LEN32 & D32 & CO & _) REST]. pose proof REST as (HP & LV & _).
destruct (nth_error (t_levels ts) (t_depth ts)) as [l|] eqn:Hl; [| exfalso; apply nth_error_None in Hl; lia].
pose proof (LV _ _ Hl) as (ST26 & SS26 & _).
eapply (seg_redo_A HIx GA); [exact STC | exact INV | exact Hl |]. intros a3'.
eapply (HC (tl_st l) ST26 n ts l); [exact STC | exact INV | exact Hl | reflexivity | exact Hco | exact Hcb | exact NUM | exact SP | exact TD
| exact PBK | exact BK | exact OW | exact UTF | exact CSTR | exact FS | exact FRM | lia | exact IHall | exact KO | exact KE].
+
intros ts m md A B cb nb pj errv gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 F fc M INV Hco Hcb NN SP TD PBK BK NA FS FRM.
eapply (seg_break_A HIx GA GA_outside); [exact STC | exact INV | exact Hco | |].
* intros m' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' s11' t4' t6' Hz INV'.
eapply KO; [apply (PE_INV_A_W HIx GA); exact INV' | tdsame TD | | exact FS | exact FRM].
eapply (JOUT_of_PBJ (pf_len pf) m ts (ts_set_co ts (t_co ts + 1))); [exact PBK | lia | reflexivity | reflexivity | intros _; split; reflexivity].
* intros m' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' t4' Hnz INV' PBT'.
eapply (IHL (ts_set_co ts (t_co ts + 1))); [| exact INV' | exact NN | | | | | | apply NAO_set_co; exact NA | exact FS | exact FRM].
{ unfold mbrk, mloop, mbase, ts_set_co in *. cbn [t_co pf_mxd]. lia. }
{ revert SP. unfold SPOK, ts_set_co, cur_st. destruct ts as [dp9 lv9 co9 pb9 pbs9 x9 ob9 os9 obs9]; cbn [t_levels t_depth t_x t_co pf_mxd]. intros SP Hz. specialize (SP Hz). unfold SPV in *. cbn [ts_stpos pf_mxd] in *. lia. }
{ tdsame TD. }
{ unfold ts_set_co; cbn [t_co pf_mxd]. intros NE. pose proof INV as [(_ & _ & CO & _) _].
destruct (peek_cases pf payload (t_co ts) cb LENR CSTR (proj1 RR) ltac:(lia) ltac:(lia) Hcb Hnz) as [[E _] | [_ LT]]; [exfalso; exact (NE E) | exact LT]. }
{ rewrite PBS_set_co. exact (PBJ_set_co m m' ts (PBS ts) PBT' PBK). }
{ eapply BOK_weaken; [| apply BOK_set_co; [| exact BK]; lia]. unfold bloop, bbrk, bx, bxb, mbrk, mloop, mbase, cur_st, cur_ss, ts_set_co. cbn [t_co t_levels t_depth pf_mxd]. lia. }
+
intros ts m md A B cb nb pj errv av gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5 F fc M INV Hco Hcb NN SP TD AVR AVZ PBK BK NA FS FRM.
eapply (seg_adv_A HIx GA GA_outside); [exact STC | exact INV | exact Hco | exact AVR | exact AVZ | |].
* intros m' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' s11' t4' t6' Hz INV'.
eapply KO; [apply (PE_INV_A_W HIx GA); exact INV' | tdsame TD | | exact FS | exact FRM].
eapply (JOUT_of_PBJ (pf_len pf) m ts (ts_set_co ts (t_co ts + 1))); [exact PBK | lia | reflexivity | reflexivity | intros _; split; reflexivity].
* intros m' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' t4' Hnz INV' PBT'.
eapply (IHL (ts_set_co ts (t_co ts + 1))); [| exact INV' | exact NN | | | | | | apply NAO_set_co; exact NA | exact FS | exact FRM].
{ unfold mbrk, mloop, mbase, ts_set_co in *. cbn [t_co pf_mxd]. lia. }
{ revert SP. unfold SPOK, ts_set_co, cur_st. destruct ts as [dp9 lv9 co9 pb9 pbs9 x9 ob9 os9 obs9]; cbn [t_levels t_depth t_x t_co pf_mxd]. intros SP Hz. specialize (SP Hz). unfold SPV in *. cbn [ts_stpos pf_mxd] in *. lia. }
{ tdsame TD. }
{ unfold ts_set_co; cbn [t_co pf_mxd]. intros NE. pose proof INV as [(_ & _ & CO & _) _].
destruct (peek_cases pf payload (t_co ts) cb LENR CSTR (proj1 RR) ltac:(lia) ltac:(lia) Hcb Hnz) as [[E _] | [_ LT]]; [exfalso; exact (NE E) | exact LT]. }
{ rewrite PBS_set_co. exact (PBJ_set_co m m' ts (PBS ts) PBT' PBK). }
{ eapply BOK_weaken; [| apply BOK_set_co; [| exact BK]; lia]. unfold bloop, bbrk, bx, bxb, mbrk, mloop, mbase, cur_st, cur_ss, ts_set_co. cbn [t_co t_levels t_depth pf_mxd]. lia. }
Qed.
End PeSMasterA.
End RC__1.
End Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmZZ QPZI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QJjn QRUw.Mq0 QRUw QRUw.Mq2 QmZZ. Import QPZI.Mq4. Import QkMG. Import QG8z Qdyh.Mq0.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa QsKa.Mq4 Qiiq.Mq0 QsKa.Mq6 Q4v2.Mq0 QlKV.Mq5 QlKV.Mq7 Q1Ey Ql4f.Mq1 QsKa.Mq8 QrQv.Mq2 QEUF QdGy.Mq6 Qeia.Mq1.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section WithIface.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_outside : forall m m' W, GA m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= hl_img_lo A4H \/ hl_img_hi A4H <= fst iv) W -> GA m'.
Hypothesis GA_pres : forall LB SP m m', heap_pres A4H LB SP m m' -> GA m -> GA m'.

Definition PE_WINX (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (p : Z) (s : option jshape) (BS : list blk) (rc : Z)
(errv : word) (FRX : Prop) : Prop :=
(length (t_levels ts) = Z.to_nat (pf_mxd pf) /\ (t_depth ts < Z.to_nat (pf_mxd pf))%nat /\
0 <= t_co ts <= pf_len pf /\ ts_choff (t_x ts) = Z_to_bv 64 (t_co ts) /\
rw_cells asegs m (pf_tk pf) (tok_cells_g (pf_mxd pf) (pf_fl pf) (t_pb ts) (Z.of_nat (t_depth ts)) q (t_x ts)) /\
pbuf asegs m (t_pbs ts) (t_pb ts) /\ t_pb ts <> 0 /\
tstack asegs m q (t_levels ts) /\
FRX) /\
PE_BASE_A HIx GA pf pa LB0 LM FRS payload me lo m md A B (pe_blocksA pf q LB0 (tsF ts BS)) errv /\
(forall i li, nth_error (t_levels ts) i = Some li -> i <> t_depth ts -> lvl_cur asegs A4F m (t_depth ts) i li) /\
(exists l, nth_error (t_levels ts) (t_depth ts) = Some l /\ lvl_bare l) /\
t_objbs ts = [] /\
put_pre A4H A4F s m BS p rc.

Lemma PE_WIN_of_WINX : forall pf pa q LB0 LM FRS payload me lo m md A B ts p s BS rc cb nb pj sv errv,
PE_WINX pf pa q LB0 LM FRS payload me lo m md A B ts p s BS rc errv (pe_frameA asegs m pf pa cb nb pj sv) ->
PE_WIN HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts p s BS rc cb nb pj sv errv.
Proof. intros until errv. intros H. exact H. Qed.

Lemma PE_WINX_open : forall pf pa q LB0 LM FRS payload me lo m md A B ts errv l (FRX : Prop),
PE_INV_AX HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts errv FRX ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_name l = 0 -> tl_nbs l = [] -> t_objbs ts = [] ->
PE_WINX pf pa q LB0 LM FRS payload me lo m md A B (ts_lvl ts (TL (tl_st l) (tl_ss l) (tl_cur l) None [] 0 [])) (tl_cur l) (tl_cs l) (tl_cbs l) 1 errv FRX.
Proof.
intros pf pa q LB0 LM FRS payload me lo m md A B ts errv l FRX [CORE REST] Hl Hn Hnbs Eobj.
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
apply PE_REST_A_base in REST as (BASE & LV & OBJ & BUD).
set (lw := TL (tl_st l) (tl_ss l) (tl_cur l) None [] 0 []).
assert (Hd : (t_depth ts < length (t_levels ts))%nat) by (apply nth_error_Some; rewrite Hl; discriminate).
pose proof (LV _ _ Hl) as (R1 & R2 & JO & _).
split; [| split; [| split; [| split; [| split]]]].
- unfold ts_lvl; cbn [t_levels t_depth t_co t_x t_pb t_pbs]. split; [rewrite lupd_length; exact LEN32|]. split; [exact D32|]. split; [exact CO|]. split; [exact CHOFF|].
split; [exact TOK|]. split; [exact PB|]. split; [exact Hpb|]. split; [| exact FR].
eapply tstack_lupd_srec; [exact TSK | exact Hl |]. unfold srec_cells, lw; cbn [tl_st tl_ss tl_cur tl_name]. rewrite Hn. reflexivity.
- destruct BASE as (HP & BASE'). split; [| exact BASE'].
eapply (heapA_perm A4L HIx); [exact HP | | apply Permutation_refl | apply Permutation_refl].
eapply Permutation_trans; [apply (pe_blocksA_cur_perm2 pf q LB0 ts l Hl)|]. apply Permutation_sym.
eapply Permutation_trans; [apply (pe_blocksA_lvl_obj_perm pf q LB0 ts l lw 0 None (tl_cbs l) Hl)|].
unfold lvl_blocks, lw; cbn [tl_cbs tl_nbs app]. rewrite Hnbs, Eobj, app_nil_r. cbn [app]. apply Permutation_refl.
- unfold ts_lvl; cbn [t_levels t_depth]. intros i li Hli Hne. rewrite nth_error_lupd_neq in Hli by congruence. exact (LV i li Hli).
- exists lw. split; [unfold ts_lvl; cbn [t_levels t_depth]; apply nth_error_lupd_eq; exact Hd|].
unfold lvl_bare, lw; cbn [tl_st tl_ss tl_cs tl_cbs tl_name tl_nbs]. repeat split; try reflexivity; lia.
- exact Eobj.
- unfold put_pre. destruct (tl_cs l) as [s'|]; cbn [jopt] in JO; [| exact JO]. destruct JO as [Hp J]. split; [exact Hp|]. split; [lia | exact J].
Qed.

Lemma PE_WINX_write : forall pf pa q LB0 LM FRS payload me lo m mc md A B ts p s BS rc errv W l' (FRX FRX' : Prop),
PE_STATIC_A HIx pf pa lo ->
PE_WINX pf pa q LB0 LM FRS payload me lo m md A B ts p s BS rc errv FRX ->
munch W m mc -> wmono asegs m mc -> mem_inv asegs mc -> Forall (pe_wtqA pf pa q) W ->
rw_cells asegs mc (pf_tk pf) (tok_cells_g (pf_mxd pf) (pf_fl pf) (t_pb ts) (Z.of_nat (t_depth ts)) q (t_x ts)) ->
tstack asegs mc q (lupd (t_levels ts) (t_depth ts) l') ->
FRX' ->
lvl_bare l' ->
PE_WINX pf pa q LB0 LM FRS payload me lo mc md A B (ts_lvl ts l') p s BS rc errv FRX'
/\ (forall b, PBOKat m ts b -> PBOKat mc (ts_lvl ts l') b).
Proof.
intros pf pa q LB0 LM FRS payload me lo m mc md A B ts p s BS rc errv W l' FRX FRX' STC (CORE & BASE & LVo & (l & Hl & BARE) & Eobj & PP) MU WM MI HW TOKc TSKc FRc BARE'.
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
assert (Hd : (t_depth ts < length (t_levels ts))%nat) by (apply nth_error_Some; rewrite Hl; discriminate).
destruct (PE_BASE_A_private_write HIx GA GA_outside pf pa q LB0 LM FRS payload me lo m mc md A B (tsF ts BS) errv W STC BASE MU WM MI (pe_wtqA_private _ _ _ _ _ HW)) as [BASEc AG].
unfold tsF in AG; cbn [t_objbs t_levels] in AG.
assert (Eb : lvl_blocks l' = lvl_blocks l).
{ destruct BARE as (_ & _ & _ & C1 & _ & C2). destruct BARE' as (_ & _ & _ & C1' & _ & C2'). unfold lvl_blocks. rewrite C1, C2, C1', C2'. reflexivity. }
split.
2:{ intros b PBK. eapply PBOKat_same with (ts := ts); [reflexivity | reflexivity |].
eapply PBOKat_agree; [exact PBK | | apply incl_refl].
eapply (agree_wtqA HIx) with (ts := tsF ts BS); [exact STC | exact (proj1 BASE) | exact MU | exact WM | exact HW |].
intros a n Hin. assert (HinL : In (a, n) (pe_blocksA pf q LB0 (tsF ts BS) ++ LM)) by (unfold pe_blocksA, tstate_blocks, tsF; cbn [t_pbs]; apply in_or_app; left; apply in_or_app; left; apply in_or_app; left; exact Hin).
split; [exact HinL|].
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ (proj1 BASE)) as ND. unfold pe_blocksA in ND. rewrite <- app_assoc in ND. split.
+ intros ->. refine (nodup_app_ne _ _ _ _ _ _ ND _ _ eq_refl); [unfold tstate_blocks, tsF; cbn [t_pbs]; apply in_or_app; left; exact Hin | left; reflexivity].
+ intros ->. refine (nodup_app_ne _ _ _ _ _ _ ND _ _ eq_refl); [unfold tstate_blocks, tsF; cbn [t_pbs]; apply in_or_app; left; exact Hin | right; left; reflexivity]. }
split; [| split; [| split; [| split; [| split]]]].
- unfold ts_lvl; cbn [t_levels t_depth t_co t_x t_pb t_pbs]. split; [rewrite lupd_length; exact LEN32|]. split; [exact D32|]. split; [exact CO|]. split; [exact CHOFF|].
split; [exact TOKc|]. split; [| split; [exact Hpb | split; [exact TSKc | exact FRc]]].
eapply (pbuf_wtqA HIx) with (ts := tsF ts BS); [exact STC | exact (proj1 BASE) | exact PB | exact MU | exact WM | exact HW].
- rewrite (pe_blocksA_tsF_lvl pf q LB0 ts BS l l' Hl Eb). exact BASEc.
- unfold ts_lvl; cbn [t_levels t_depth]. intros i li Hli Hne. rewrite nth_error_lupd_neq in Hli by congruence.
eapply (lvl_cur_agree asegs A4F); [exact (LVo i li Hli Hne) | exact AG |].
intros b Hb. apply in_or_app; right. apply in_concat. exists (lvl_blocks li). split; [| exact Hb]. apply in_map. eapply nth_error_In; exact Hli.
- exists l'. split; [unfold ts_lvl; cbn [t_levels t_depth]; apply nth_error_lupd_eq; exact Hd | exact BARE'].
- exact Eobj.
- unfold put_pre in *. destruct s as [s'|]; [| exact PP]. destruct PP as (Hp & Hrc & J). split; [exact Hp|]. split; [exact Hrc|].
eapply jval_agree; [exact J | exact AG | intros b Hb; apply in_or_app; left; exact Hb].
Qed.

Lemma PE_WINX_write_x : forall pf pa q LB0 LM FRS payload me lo m mc md A B ts p s BS rc errv W l' x' (FRX FRX' : Prop),
PE_STATIC_A HIx pf pa lo ->
PE_WINX pf pa q LB0 LM FRS payload me lo m md A B ts p s BS rc errv FRX ->
munch W m mc -> wmono asegs m mc -> mem_inv asegs mc -> Forall (pe_wtqA pf pa q) W ->
rw_cells asegs mc (pf_tk pf) (tok_cells_g (pf_mxd pf) (pf_fl pf) (t_pb ts) (Z.of_nat (t_depth ts)) q x') -> ts_choff x' = Z_to_bv 64 (t_co ts) ->
tstack asegs mc q (lupd (t_levels ts) (t_depth ts) l') ->
FRX' ->
lvl_bare l' ->
PE_WINX pf pa q LB0 LM FRS payload me lo mc md A B (ts_set_x (ts_lvl ts l') (t_co ts) x') p s BS rc errv FRX'
/\ (forall b, PBOKat m ts b -> PBOKat mc (ts_set_x (ts_lvl ts l') (t_co ts) x') b).
Proof.
intros pf pa q LB0 LM FRS payload me lo m mc md A B ts p s BS rc errv W l' x' FRX FRX' STC (CORE & BASE & LVo & (l & Hl & BARE) & Eobj & PP) MU WM MI HW TOKc Hch TSKc FRc BARE'.
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
assert (Hd : (t_depth ts < length (t_levels ts))%nat) by (apply nth_error_Some; rewrite Hl; discriminate).
destruct (PE_BASE_A_private_write HIx GA GA_outside pf pa q LB0 LM FRS payload me lo m mc md A B (tsF ts BS) errv W STC BASE MU WM MI (pe_wtqA_private _ _ _ _ _ HW)) as [BASEc AG].
unfold tsF in AG; cbn [t_objbs t_levels] in AG.
assert (Eb : lvl_blocks l' = lvl_blocks l).
{ destruct BARE as (_ & _ & _ & C1 & _ & C2). destruct BARE' as (_ & _ & _ & C1' & _ & C2'). unfold lvl_blocks. rewrite C1, C2, C1', C2'. reflexivity. }
split.
2:{ intros b PBK. eapply PBOKat_same with (ts := ts); [reflexivity | reflexivity |].
eapply PBOKat_agree; [exact PBK | | apply incl_refl].
eapply (agree_wtqA HIx) with (ts := tsF ts BS); [exact STC | exact (proj1 BASE) | exact MU | exact WM | exact HW |].
intros a n Hin. assert (HinL : In (a, n) (pe_blocksA pf q LB0 (tsF ts BS) ++ LM)) by (unfold pe_blocksA, tstate_blocks, tsF; cbn [t_pbs]; apply in_or_app; left; apply in_or_app; left; apply in_or_app; left; exact Hin).
split; [exact HinL|].
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ (proj1 BASE)) as ND. unfold pe_blocksA in ND. rewrite <- app_assoc in ND. split.
+ intros ->. refine (nodup_app_ne _ _ _ _ _ _ ND _ _ eq_refl); [unfold tstate_blocks, tsF; cbn [t_pbs]; apply in_or_app; left; exact Hin | left; reflexivity].
+ intros ->. refine (nodup_app_ne _ _ _ _ _ _ ND _ _ eq_refl); [unfold tstate_blocks, tsF; cbn [t_pbs]; apply in_or_app; left; exact Hin | right; left; reflexivity]. }
split; [| split; [| split; [| split; [| split]]]].
- unfold ts_set_x, ts_lvl; cbn [t_levels t_depth t_co t_x t_pb t_pbs]. split; [rewrite lupd_length; exact LEN32|]. split; [exact D32|]. split; [exact CO|]. split; [exact Hch|].
split; [exact TOKc|]. split; [| split; [exact Hpb | split; [exact TSKc | exact FRc]]].
eapply (pbuf_wtqA HIx) with (ts := tsF ts BS); [exact STC | exact (proj1 BASE) | exact PB | exact MU | exact WM | exact HW].
- replace (pe_blocksA pf q LB0 (tsF (ts_set_x (ts_lvl ts l') (t_co ts) x') BS)) with (pe_blocksA pf q LB0 (tsF (ts_lvl ts l') BS)) by reflexivity.
rewrite (pe_blocksA_tsF_lvl pf q LB0 ts BS l l' Hl Eb). exact BASEc.
- unfold ts_set_x, ts_lvl; cbn [t_levels t_depth]. intros i li Hli Hne. rewrite nth_error_lupd_neq in Hli by congruence.
eapply (lvl_cur_agree asegs A4F); [exact (LVo i li Hli Hne) | exact AG |].
intros b Hb. apply in_or_app; right. apply in_concat. exists (lvl_blocks li). split; [| exact Hb]. apply in_map. eapply nth_error_In; exact Hli.
- exists l'. split; [unfold ts_set_x, ts_lvl; cbn [t_levels t_depth]; apply nth_error_lupd_eq; exact Hd | exact BARE'].
- exact Eobj.
- unfold put_pre in *. destruct s as [s'|]; [| exact PP]. destruct PP as (Hp & Hrc & J). split; [exact Hp|]. split; [exact Hrc|].
eapply jval_agree; [exact J | exact AG | intros b Hb; apply in_or_app; left; exact Hb].
Qed.

Lemma PE_WINX_callG2 : forall pf pa q LB0 LM FRS payload me lo m1 m2 md md2 A A2 B B2 ts p s BS rc p2 s2 BS2 rc2 errv errv2 (FRX FRX' : Prop),
PE_STATIC_A HIx pf pa lo ->
PE_WINX pf pa q LB0 LM FRS payload me lo m1 md A B ts p s BS rc errv FRX ->
model_vm_only (cfg_model md) (cfg_model md2) ->
heap_pres A4H (pe_blocksA pf q LB0 ts ++ LM ++ fr_ivs A4L ((pa_F pa, 2) :: FRS)) (pf_spf pf) m1 m2 ->
HEAPA A4L HIx A2 (pe_blocksA pf q LB0 (tsF ts BS2)) LM ((pa_F pa, 2) :: FRS) B2 m2 md2 ->
stk asegs m2 lo (pf_spf pf) -> rw_cells asegs m2 A_ERRNO [C4 errv2] ->
put_pre A4H A4F s2 m2 BS2 p2 rc2 ->
FRX' ->
PE_WINX pf pa q LB0 LM FRS payload me lo m2 md2 A2 B2 ts p2 s2 BS2 rc2 errv2 FRX'.
Proof.
intros pf pa q LB0 LM FRS payload me lo m1 m2 md md2 A A2 B B2 ts p s BS rc p2 s2 BS2 rc2 errv errv2 FRX FRX' STC (CORE & BASE & LVo & CUR & Eobj & PP) VM HPR HP2 ST2 ERR2 PP2 FR2.
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR).
set (RB := pe_blocksA pf q LB0 ts) in *.
assert (INtk : In (pf_tk pf, 72) RB) by (unfold RB, pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * pf_mxd pf) RB) by (unfold RB, pe_blocksA; apply in_or_app; right; right; left; reflexivity).
assert (LB0R : incl LB0 RB) by (unfold RB, pe_blocksA; intros b Hb; apply in_or_app; right; right; right; exact Hb).
assert (AG : agree_on asegs RB m1 m2) by (eapply (agree_of_heap_pres asegs A4H); [exact HPR | reflexivity | intros b Hb; apply in_or_app; left; exact Hb]).
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR) in TOK; [| eapply client_range_block; [apply in_or_app; left; exact INtk | lia | unfold tok_cells_g; cbn; lia]]. cbn [hl_segs hla_base A4L A4H] in TOK.
apply (tstack_pres_g A4H _ _ _ _ _ _ HPR (in_or_app _ _ _ (or_introl INq))) in TSK; [| exact LEN32]. cbn [hl_segs hla_base A4L A4H] in TSK.
split; [| split; [| split; [| split; [exact CUR | split; [exact Eobj | exact PP2]]]]].
- split; [exact LEN32|]. split; [exact D32|]. split; [exact CO|]. split; [exact CHOFF|]. split; [exact TOK|]. split; [| split; [exact Hpb | split; [exact TSK | exact FR2]]].
eapply pbuf_agree; [exact PB | exact AG |]. unfold RB, pe_blocksA, tstate_blocks. intros b Hb. apply in_or_app; left. apply in_or_app; left. exact Hb.
- eapply (PE_BASE_A_callG HIx GA GA_pres pf pa LB0 LM FRS payload me lo m1 m2 md md2 A A2 B B2 _ _ errv errv2 RB); [exact STC | exact BASE | exact VM | exact HPR | exact LB0R | exact HP2 | exact ST2 | exact ERR2].
- intros i li Hli Hne. eapply (lvl_cur_agree asegs A4F); [exact (LVo i li Hli Hne) | exact AG |].
intros b Hb. unfold RB, pe_blocksA, tstate_blocks. apply in_or_app; left. apply in_or_app; right. apply in_or_app; right. apply in_concat. exists (lvl_blocks li). split; [| exact Hb]. apply in_map. eapply nth_error_In; exact Hli.
Qed.

Lemma pe_uw_atX : forall pf pa lo m nb pj sv v2 ra2 ffc shc,
PE_STATIC_A HIx pf pa lo -> pe_frameAX m pf pa nb pj sv ffc shc ->
pe_s0 sv = Z_to_bv 64 v2 -> pe_ra sv = Z_to_bv 64 ra2 ->
(v2 < alloc_ceiling \/ v2 mod 8 <> 0 \/ v2 <= pa_sp0 pa \/ hiA_top A4L HIx - 16 <= v2) -> 0 <= v2 < 2^64 ->
uw_at (hiA_top A4L HIx) m (pf_spf pf) (pa_sp0 pa) (UWfp ra2 v2).
Proof.
intros pf pa lo m nb pj sv v2 ra2 ffc shc STC (_ & _ & SV & _) S0V RAV HV HR.
pose proof STC as (LO & LOS & GEO & HT & SP0 & _). pose proof GEO as (Gspf & Gsp0 & Gle & _).
cbn [uw_at]. split; [lia|]. split; [clear - Gsp0; Z.div_mod_to_equations; lia|]. split; [lia|]. split; [| split; [exact HV | exact HR]].
unfold pe_savedA_cells in SV. destruct SV as [[_ SVB] _].
cbn [cells_bytes cbytes app] in SVB. rewrite <- ?app_assoc in SVB.
do 11 (apply bytes_at_app in SVB as [_ SVB]; rewrite length_le8 in SVB).
rewrite S0V, RAV in SVB. eapply bytes_at_ext; [| reflexivity].
match type of SVB with bytes_at _ _ ?a _ => replace a with (pa_sp0 pa - 16) in SVB by lia end. exact SVB.
Qed.

End WithIface.
End RC__1.
End Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI QDwa QSHS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QJjn QRUw.Mq0 QRUw QkMG. Import QG8z Qdyh.Mq0. Import Q8tj. Import Qu4M.Mq0.
Import QbFI. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqj QsKa.Mqd Qiiq QsKa.Mqf Q4v2 QsKa.Mqe QDwa Qoif.Mq4 QSHS Ql4f.Mq4 QsKa.Mqh QrQv.Mq4 QEUF.Mq2 Qeia.Mq6 QYZ0.Mq9.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import QlKV.Mq2. Import QEUF.Mq3.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Lemma obj_capA_jval : forall m kids BS p rc,
jval asegs A4F (Sobj kids) m BS p rc ->
exists t tbl rest, BS = (p, 48) :: (t, 56) :: (tbl, 40 * obj_capA BS) :: rest /\ In (obj_capA BS) lf_sizes.
Proof.
intros m kids BS p rc J. cbn [jval] in J.
destruct J as (pb & PBS & REST & EBS & _ & t & TBS & kvs & KBS & EREST & _ & (tbl & size & es & svs & _ & ETBS & LO) & _).
destruct LO as (_ & _ & _ & _ & INS & _ & _). pose proof (lf_size_range size INS) as SR.
subst TBS REST BS. unfold lh_blocks.
exists t, tbl, ((map (fun e => (le_k e, le_kn e)) es ++ concat KBS) ++ PBS). unfold obj_capA. cbn [app nth snd].
rewrite (Z.mul_comm 40 size), Z.div_mul by lia. split; [rewrite (Z.mul_comm size 40), <- !app_assoc; reflexivity | exact INS].
Qed.

Section PeSCallOaA.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_presx : forall LB SP m m', heap_presx A4H a4_volatile LB SP m m' -> lh_globA m' -> GA m -> GA m'.
Hypothesis GA_lh : forall m, GA m -> lh_globA m.
Variable HD : Z.
Hypothesis HD_le : 80 + 96 + 4096 + 144 + HD <= 12288.
Hypothesis OADD : jo_object_add_A HIx HD.

Lemma pe_oadd_c :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel) (kids : list (option jshape))
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP : Z) (nB : nat)
(ra gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
PBOK m ts kP -> BOK pf pa ts B (S (Z.to_nat (16 * Z.max 0 (pf_len pf) + 8192) + nB)) ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_ovadd -> tl_cs l = Some (Sobj kids) ->
frm0 fc -> Z.of_nat (length FRS) + 2 < 4096 -> bv_unsigned ra mod 2 = 0 ->
(forall m2 md2 A2 B2 errv2 r (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : word) F2 fc2,
(r = 0 /\ exists cbs2 kids2,
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m2 md2 A2 B2
(ts_lvl_obj ts (TL (tl_st l) (tl_ss l) (tl_cur l) (Some (Sobj kids2)) cbs2 (tl_name l) (tl_nbs l)) 0 None []) cb nb pj sv errv2 /\
PBOK m2 (ts_lvl_obj ts (TL (tl_st l) (tl_ss l) (tl_cur l) (Some (Sobj kids2)) cbs2 (tl_name l) (tl_nbs l)) 0 None []) kP /\
Z.of_nat (length kids2) <= Z.of_nat (length kids) + 1 /\ okmax kids2 <= Z.max (okmax kids) (odep (t_objs ts)) /\
(forall st' ss' obj' objs', (ss' <> ST_finish \/ zin st' [ST_array_add; ST_ovadd] = true) ->
BOK pf pa (ts_lvl_obj ts (TL st' ss' (tl_cur l) (Some (Sobj kids2)) cbs2 (tl_name l) (tl_nbs l)) obj' objs' []) B2 nB) /\
(forall w wv nm nn, tl_nbs l = [(nm, nn)] -> jtx (Sobj kids) (tl_cbs l) = Some (w, []) -> jtx_opt (t_objs ts) (t_objbs ts) = Some (wv, []) ->
exists w', jtx (Sobj kids2) cbs2 = Some (w', []) /\ w' <= w + key_w nn + wv))
\/ (r = 2^64 - 1 /\ exists LK, PE_INVW_A HIx GA pf pa q LB0 LM FRS payload me lo m2 md2 A2 B2 ts LK cb nb pj sv errv2) ->
fsaved F F2 -> (frm0 fc -> frm0 fc2) ->
AJ5 A4L HIx A2 T md2
(MS (mkR ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) w0 w1 w2 s0 s1 (Z_to_bv 64 r) w3 w4 w5 w6 w7 w8 w9
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 w10 w11 w12 w13) F2 (ret_pc ra) fc2 None m2 (seg_rom asegs))) ->
AJ5 A4L HIx A T md
(MS (mkR ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2 s0 s1 (Z_to_bv 64 (tl_cur l)) (Z_to_bv 64 (tl_name l)) (Z_to_bv 64 (t_obj ts)) a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x9d820) fc None m (seg_rom asegs)).
Proof.
intros until fc. intros STC BSL INV PBK BK Hl Hst Hcs FRM FRN RA K.
assert (Hop : lvl_closed l = false) by (apply lvl_closed_open_st; rewrite Hst; reflexivity).
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
pose proof INV as [CORE REST1].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK1 & FR1).
pose proof REST1 as (HP1 & LV1 & OBJ1 & ST1 & ERR1 & _ & _ & _ & _ & _ & G1 & _).
assert (Hd : (t_depth ts < length (t_levels ts))%nat) by (apply nth_error_Some; rewrite Hl; discriminate).
assert (JOB : jopt asegs A4F (t_objs ts) m (t_objbs ts) (t_obj ts)).
{ revert OBJ1. unfold cur_st. rewrite Hl, Hst. cbn. intros E; exact E. }
set (RB := pe_restblocks2 pf q LB0 ts).
pose proof (LV1 _ _ Hl) as LVd. pose proof LVd as (ST26 & SS26 & JO & Md). rewrite Hcs in JO. cbn [jopt] in JO. destruct JO as [Hc J].
rewrite Nat.ltb_irrefl, Nat.eqb_refl in Md. destruct Md as (c0 & hn0 & Hmode & CLS0 & NM0).
rewrite Hst, lvl_mode_ovadd in Hmode. injection Hmode as <- <-. cbn [name_ok] in NM0. destruct NM0 as (Hn0 & nn & ks & Hnbs & Hnn & CSTR).
set (LBk := (tl_name l, nn) :: RB).
assert (PERM0 : Permutation (pe_blocksA pf q LB0 ts) (tl_cbs l ++ t_objbs ts ++ LBk)).
{ eapply Permutation_trans; [apply (pe_blocksA_cur_perm2 pf q LB0 ts l Hl)|]. unfold lvl_blocks, LBk. rewrite Hnbs, <- app_assoc. apply Permutation_app_head.
cbn [app]. apply Permutation_middle. }
assert (HPa : HEAPA A4L HIx A (tl_cbs l ++ t_objbs ts ++ LBk) LM ((pa_F pa, 2) :: FRS) B m md)
by (eapply (heapA_perm A4L HIx); [exact HP1 | exact PERM0 | apply Permutation_refl | apply Permutation_refl]).
destruct (obj_capA_jval _ _ _ _ _ J) as (t_ & tbl_ & rest_ & EOBS & INSZ).
assert (Hcap29 : obj_capA (tl_cbs l) <= 2^29).
{ assert (Hin : In (tbl_, 40 * obj_capA (tl_cbs l)) (tl_cbs l ++ t_objbs ts ++ LBk)).
{ apply in_or_app; left. set (c_ := obj_capA (tl_cbs l)) in *. rewrite EOBS. right; right; left; reflexivity. }
pose proof (heapA_blk_le26 A4L HIx _ _ _ _ _ _ _ tbl_ (40 * obj_capA (tl_cbs l)) HPa Hin). lia. }
assert (Hklen : 0 <= Z.of_nat (length ks) <= Z.max 0 (pf_len pf)).
{ pose proof (BOK_name_bound pf pa ts B _ l (tl_name l) nn BK Hl Hnbs) as NB. destruct CSTR as (CL & _). lia. }
destruct (BOK_obj_add pf pa ts B nB l kids (Z.of_nat (length ks)) BK BSL Hl Hcs Hop Hklen Hcap29) as (COST & COSTR & BKF & BK2).
assert (SPF1 : lo <= pf_spf pf - (80 + 96 + 4096 + 144 + HD) /\ pf_spf pf mod 16 = 0 /\ pf_spf pf <= hiA_top A4L HIx /\ 0 <= pf_spf pf < 2^62).
{ clear - LOS HT Gle Gspf SP0 HD_le. split; [lia|]. split; [Z.div_mod_to_equations; lia|]. split; lia. }
destruct SPF1 as (SPF1 & SPF2 & SPF3 & SPF4).
eapply OADD with (LB := LBk) (OBS := tl_cbs l) (VBS := t_objbs ts) (p := tl_cur l) (v := t_obj ts) (k := tl_name l) (kn := nn) (ks := ks) (kids := kids) (vs := t_objs ts)
(lo := lo) (errv := errv) (FRS := (pa_F pa, 2) :: FRS);
[ | exact (GA_lh _ G1) | exact J | exact JOB | left; reflexivity | exact CSTR | lia | exact FRM | cbn [length]; rewrite Nat2Z.inj_succ; clear - FRN; lia | reflexivity | reflexivity | reflexivity | exact COST | exact COSTR
| exact (proj2 (heapA_budget A4L HIx _ _ _ _ _ _ _ HP1)) | ].
{ unfold jo_preA. rewrite !unsigned_lit by lia. split; [exact HPa|]. split; [exact ST1|]. split; [exact LO|]. split; [exact SPF1|]. split; [exact SPF2|]. split; [exact SPF3|].
split; [exact ERR1|]. split; [reflexivity | exact RA]. }
intros ms2 md2 m2 r A2 B2 (RS2 & VM2 & ST2 & HPR2 & (errv2 & ERR2)) LG2 HD2 OUT.
destruct RS2 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F2 & fc2 & -> & FS2 & FRM2).
cbn [hl_segs hl_tp hla_base A4L A4H] in *. rewrite ?(unsigned_lit (pf_spf pf)) in ST2 by lia. rewrite ?(unsigned_lit (pf_spf pf)) in HPR2 by lia.
assert (INtk : In (pf_tk pf, 72) LBk) by (unfold LBk, RB, pe_restblocks2; right; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * pf_mxd pf) LBk) by (unfold LBk, RB, pe_restblocks2; right; apply in_or_app; right; right; left; reflexivity).
assert (LB0R : incl LB0 LBk) by (unfold LBk, RB, pe_restblocks2; intros b Hb; right; apply in_or_app; right; right; right; exact Hb).
assert (AG : agree_on asegs LBk m m2) by (eapply (agree_of_heap_presx asegs A4H); [exact HPR2 | reflexivity | intros b Hb; apply in_or_app; left; exact Hb]).
assert (FR2 : pe_frameA asegs m2 pf pa cb nb pj sv).
{ eapply pe_frameA_presx; [exact HPR2 | lia | exact GEO | | | exact FR1].
- apply in_or_app; right. apply in_or_app; right. change 248 with (fr_size 2 - 8). apply fr_ivs_frame. left; reflexivity.
- apply in_or_app; right. apply in_or_app; right. rewrite <- fr_shadow_len_2. change (shA (pa_F pa)) with (shad A4L (pa_F pa)). apply fr_ivs_shadow. left; reflexivity. }
apply (heap_presx_rw_cells A4H _ _ _ _ _ _ _ HPR2) in TOK; [| eapply client_rangex_block; [apply in_or_app; left; exact INtk | lia | unfold tok_cells_g; cbn; lia]]. cbn [hl_segs hla_base A4L A4H] in TOK.
apply (tstack_presx_g A4H _ _ _ _ _ _ _ HPR2 (in_or_app _ _ _ (or_introl INq))) in TSK1; [| exact LEN32]. cbn [hl_segs hla_base A4L A4H] in TSK1.
assert (PBKa : PBOK m2 ts kP).
{ eapply PBOK_agree; [exact PBK | exact AG |]. unfold LBk, RB, pe_restblocks2. intros b Hb. right. apply in_or_app; left. apply in_or_app; left. exact Hb. }
assert (CSTR2 : cstr asegs m2 (tl_name l) nn ks) by (eapply (cstr_agree asegs) with (BS := LBk); [exact CSTR | exact AG | left; reflexivity | lia]).
assert (LVo : forall i li, nth_error (t_levels ts) i = Some li -> i <> t_depth ts -> lvl_cur asegs A4F m2 (t_depth ts) i li).
{ intros i li Hli NE. eapply (lvl_cur_agree asegs A4F); [exact (LV1 i li Hli) | exact AG |].
intros b Hb. right. exact (pe_restblocks2_other pf q LB0 ts i li NE Hli b Hb). }
eapply (K m2 md2 A2 B2 errv2 r); [| exact FS2 | exact FRM2].
destruct OUT as [(-> & cbs2 & kids2 & J2 & HP2 & LENK & DEPK & CASES) | (-> & REM & J2 & JOB2 & HP2 & HB2)].
- left. split; [reflexivity|]. exists cbs2, kids2.
set (l2 := TL (tl_st l) (tl_ss l) (tl_cur l) (Some (Sobj kids2)) cbs2 (tl_name l) (tl_nbs l)).
set (ts2 := ts_lvl_obj ts l2 0 None []).
assert (BK2' : forall st' ss' obj' objs', (ss' <> ST_finish \/ zin st' [ST_array_add; ST_ovadd] = true) ->
BOK pf pa (ts_lvl_obj ts (TL st' ss' (tl_cur l) (Some (Sobj kids2)) cbs2 (tl_name l) (tl_nbs l)) obj' objs' []) B2 nB).
{ intros st' ss' obj' objs' Hss'. apply (BK2 B2 cbs2 kids2 st' ss' obj' objs' Hss'); [| exact HD2].
destruct CASES as [(E1 & E2 & E3 & E4 & _) | (E1 & E2 & E3 & E4 & _)]; [left | right]; (split; [exact E1 | split; [exact E2 | split; [exact E3 | exact E4]]]). }
assert (HP2' : HEAPA A4L HIx A2 (pe_blocksA pf q LB0 ts2) LM ((pa_F pa, 2) :: FRS) B2 m2 md2).
{ eapply (heapA_perm A4L HIx); [exact HP2 | | apply Permutation_refl | apply Permutation_refl].
apply Permutation_sym. eapply Permutation_trans; [apply (pe_blocksA_lvl_obj_perm pf q LB0 ts l l2 0 None [] Hl)|]. unfold lvl_blocks, l2, LBk. cbn [tl_cbs tl_nbs app]. rewrite Hnbs, <- app_assoc.
apply Permutation_app_head. cbn [app]. apply Permutation_refl. }
assert (BUD2 : PE_BUD pf pa ts2 B2).
{ eapply PE_BUD_lvl_obj_irrel; [| exact (BOK_weak _ _ _ _ _ (BK2' ST_eatws ST_osep 0 None ltac:(left; unfold ST_osep, ST_finish; lia)))]. reflexivity. }
assert (REST2 : PE_REST_A HIx GA pf pa q LB0 LM FRS payload me lo m2 md2 A2 B2 ts2 errv2).
{ eapply (PE_REST_A_callGx HIx GA GA_presx) with (ts := ts) (LBc := LBk); [exact STC | exact REST1 | exact VM2 | exact HPR2 | exact LG2 | exact LB0R | exact HP2' | | | exact ST2 | exact ERR2 | exact BUD2].
- unfold ts2, ts_lvl_obj; cbn [t_levels t_depth]. intros i li Hli.
destruct (PeanoNat.Nat.eq_dec i (t_depth ts)) as [-> | NE].
+ rewrite nth_error_lupd_eq in Hli by exact Hd. injection Hli as <-.
split; [exact ST26|]. split; [exact SS26|]. split; [cbn [tl_cs tl_cbs tl_cur l2 jopt]; split; [exact Hc | exact J2]|].
rewrite Nat.ltb_irrefl, Nat.eqb_refl. exists CObj, true. split; [cbn [tl_st tl_ss l2]; rewrite Hst; apply lvl_mode_ovadd|].
split; [cbn [tl_cs l2]; exact I|]. cbn [name_ok tl_name tl_nbs l2]. split; [exact Hn0|]. exists nn, ks. split; [exact Hnbs|]. split; [exact Hnn | exact CSTR2].
+ rewrite nth_error_lupd_neq in Hli by congruence. exact (LVo i li Hli NE).
- unfold cur_st, ts2, ts_lvl_obj; cbn [t_levels t_depth t_objs t_objbs t_obj]. rewrite nth_error_lupd_eq by exact Hd. cbn [tl_st l2]. rewrite Hst. cbn. split; reflexivity. }
split; [| split; [exact PBKa | split; [exact LENK | split; [exact DEPK | split; [exact BK2' |]]]]].
2:{ intros w wv nm nn' Enbs Hw Hwv. rewrite Hnbs in Enbs. injection Enbs as _ Enn. subst nn'. destruct CSTR2 as (Lks & _).
destruct CASES as [(_ & _ & _ & _ & JX) | (_ & _ & _ & _ & JX)].
- exists (w + (key_w (Z.of_nat (length ks) + 1) + wv)). split; [exact (JX w wv Hw Hwv) | unfold key_w; lia].
- destruct (JX w wv Hw Hwv) as (w' & E' & L'). exists w'. split; [exact E' | unfold key_w; lia]. }
split; [| exact REST2]. unfold PE_CORE_A, ts2, ts_lvl_obj; cbn [t_levels t_depth t_co t_x t_pb t_pbs]. split; [rewrite lupd_length; exact LEN32|]. split; [exact D32|]. split; [exact CO|]. split; [exact CHOFF|].
split; [exact TOK|]. split; [exact (PBOK_pbuf _ _ _ PBKa)|]. split; [exact Hpb|]. split; [| exact FR2].
eapply tstack_lupd_srec; [exact TSK1 | exact Hl | reflexivity].
- right. split; [reflexivity|]. exists REM.
split; [split; [exact LEN32|]; split; [exact D32|]; split; [exact CO|]; split; [exact CHOFF|]; split; [exact TOK|]; split; [exact (PBOK_pbuf _ _ _ PBKa)|]; split; [exact Hpb|]; split; [exact TSK1 | exact FR2]|].
apply PE_REST_A_base in REST1 as (BASE1 & _ & _ & _).
split; [| split].
+ eapply (PE_BASE_A_callGx HIx GA GA_presx) with (LBc := LBk); [exact STC | exact BASE1 | exact VM2 | exact HPR2 | exact LG2 | exact LB0R | | exact ST2 | exact ERR2].
eapply (heapA_perm A4L HIx); [exact HP2 | | apply Permutation_refl | apply Permutation_refl].
apply (Permutation_trans (l' := (tl_cbs l ++ t_objbs ts ++ LBk) ++ REM)).
* rewrite <- !app_assoc. apply Permutation_app_head. apply Permutation_app_head. apply Permutation_app_comm.
* apply Permutation_app_tail. apply Permutation_sym. exact PERM0.
+ intros i li Hli.
destruct (PeanoNat.Nat.eq_dec i (t_depth ts)) as [-> | NE].
* rewrite Hl in Hli. injection Hli as <-. apply lvl_cur_weakA.
split; [exact ST26|]. split; [exact SS26|]. split; [rewrite Hcs; cbn [jopt]; split; [exact Hc | exact J2]|].
rewrite Nat.ltb_irrefl, Nat.eqb_refl. exists CObj, true. split; [rewrite Hst; apply lvl_mode_ovadd|]. split; [rewrite Hcs; exact I|].
cbn [name_ok]. split; [exact Hn0|]. exists nn, ks. split; [exact Hnbs|]. split; [exact Hnn | exact CSTR2].
* apply lvl_cur_weakA. exact (LVo i li Hli NE).
+ exact (BKF B2 HB2 HD2).
Qed.
End PeSCallOaA.
End RC__1.
End Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QIsM Qa8x QW22 Qc5u QAzu Q6vt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QJjn QRUw.Mq0 QRUw QkMG. Import QG8z Qdyh.Mq0 Qdyh.Mq3 QIsM.Mq2 Qa8x.Mq2.
Import QbFI. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqj QsKa.Mqd Qiiq QsKa.Mqf Q4v2 QSHS Ql4f.Mq4 Q1Y6.Mq4 QsKa.Mqh QrQv.Mq4 QEUF.Mq2 QW22.Mq8 QdGy.Mq9 QYZ0.Mq8.
Import Qc5u QAzu.Mq0 Q6vt.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section PeSEatwsB.
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

Ltac reopen_std INVx TSx ts0 PF q LB0 tk mxd depth l Hl bse Hbse mX :=
pose proof INVx as [CORE2 REST2];
destruct CORE2 as (_ & _ & _ & _ & TOK & _ & _ & TSK & FR);
pose proof REST2 as (HP & _); clear REST2;
try unfold TSx in TOK, TSK; try unfold ts_pbs, ts_lvl in TOK, TSK; try unfold ts0 in TOK, TSK;
cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_tk pf_mxd pf_fl] in TOK, TSK;
unfold tok_cells_g in TOK; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK;
unfold pe_frameA in FR; destruct FR as (SLOTS & _ & _ & _ & _); unfold pe_slotsA in SLOTS; cbn zeta in SLOTS;
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in SLOTS;
assert (INtk : In (tk, 72) (pe_blocksA PF q LB0 TSx)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity);
assert (INq : In (q, 32 * mxd) (pe_blocksA PF q LB0 TSx)) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity);
pose proof (tok_shadowA HIx _ _ _ _ _ _ _ _ HP INtk) as SHT;
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI;
pose proof (wmono_refl asegs mX) as WM;
pose proof (TSK depth l Hl) as Ld; rewrite <- Hbse in Ld; unfold srec_cells in Ld;
pose proof (stack_shadowA HIx _ _ _ _ _ _ _ q mxd (Z.of_nat depth) 0 HP INq ltac:(lia) ltac:(lia)) as SHQ4;
replace (q / 8 + 4 * Z.of_nat depth + 0 + A_SB) with (bse / 8 + 2147450880) in SHQ4 by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia);
pose proof (munch_refl [(bse, bse + 32)] mX) as MU;
unfold shA in *; a4l; unfold SB2, SB4, SB7, SB8 in *;
clear TSK INtk INq.

Lemma eatws_pop_B :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP : Z)
(gp t0 a1 a2 a5 a6 a7 s3 s6 s7 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv -> PBOK m ts kP ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_eatws ->
(forall m' gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md A B
(ts_lvl ts (TL (tl_ss l) (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) cb nb pj sv errv ->
PBOK m' (ts_lvl ts (TL (tl_ss l) (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) kP ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa APE_REDO (t_co ts) gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F fc m')) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa 0x95654 (t_co ts) gp t0 (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) a1 a2 (Z_to_bv 64 (q / 8 + 4 * Z.of_nat (t_depth ts) + A_SB)) (Z_to_bv 64 0) a5 a6 a7 s3 (Z_to_bv 64 q) s6 s7 (Z_to_bv 64 (Z.of_nat (t_depth ts))) s9 s11 t3 t4 t5 t6 F fc m).
Proof.
intros until fc. intros STC INV PBK Hl Hst Kredo. pose proof INV as INV0. pe_openA STC INV.
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
unfold APE_BREAK, APE_REDO, APE_OUT, APE_ERRMEM, APE_JTAB in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
stash Himg_t. stash Himg_q. clear PB REST TSK HP LV OBJ HPR BUD GAP SAVED FSH FF STR ERR SBin.
reenterA asegs A4L HIx asegs_wx HP.
replace (q + 32 * Z.of_nat depth) with bse by lia.
step.
step. if_true.
step.
asan_chkB.
asan_rechkMB 1.
norm_sx32.
stepz.
step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, Lc : rw_cells asegs mc bse _ |- _ =>
evt_done5; subst bse;
destruct (PE_INV_A_lvl_write HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m mc md A B ts0
cb nb pj sv errv l (tl_ss l) (tl_ss l) c0 hn0 c0 STC INV0 Hl MUc WMc MIc TOKc Lc Hmode
(Qa8x.Mq2.lvl_mode_ws_pop (tl_st l) (tl_ss l) c0 hn0 ltac:(rewrite Hst; reflexivity) SS26 Hmode) SS26 SS26 (or_introl eq_refl)
ltac:(rewrite Hst; exact (lvl_mode_ws_ss_noadd (tl_st l) (tl_ss l) c0 hn0 ltac:(rewrite Hst; reflexivity) Hmode))) as [INV3 PBK3];
eapply (Kredo mc); [exact INV3 | exact (PBK3 kP PBK)]
end end.
Qed.

Lemma eatws_slash_B :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (nB : nat)
(gp t0 a1 a2 a5 a6 a7 s3 s6 s7 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv -> BOK pf pa ts B (S nB) ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_eatws ->
t_co ts < pf_len pf ->

(forall m' md' A' B' pbs' errv' gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B'
(ts_pbs (ts_lvl ts (TL ST_comment_start (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) pbs') cb nb pj sv errv' ->
PBOK m' (ts_pbs (ts_lvl ts (TL ST_comment_start (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) pbs') 1 ->
BOK pf pa (ts_pbs (ts_lvl ts (TL ST_comment_start (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) pbs') B' nB ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msA asegs pf pa APE_BREAK (t_co ts) gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' (Z_to_bv 64 2) s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' m')) ->

(forall m' md' A' B' errv' x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' ts cb nb pj sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msX asegs pf pa APE_ERR3 x1' gp' t0' t1' t2' (Z_to_bv 64 16) a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' m')) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa 0x980a8 (t_co ts) gp t0 (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) a1 a2 (Z_to_bv 64 (q / 8 + 4 * Z.of_nat (t_depth ts) + A_SB)) (Z_to_bv 64 0) a5 a6 a7 s3 (Z_to_bv 64 q) s6 s7 (Z_to_bv 64 (Z.of_nat (t_depth ts))) s9 s11 t3 t4 t5 t6 F fc m).
Proof.
intros until fc. intros STC BSL INV BK Hl Hst Hco Kbreak Kerr16. pose proof INV as INV0. pe_openA STC INV.
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
unfold APE_BREAK, APE_REDO, APE_OUT, APE_ERRMEM, APE_STBRK, APE_ERR3, APE_JTAB in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
stash Himg_t. stash Himg_q. stash Kbreak. stash Kerr16. clear PB REST TSK HP LV OBJ HPR BUD GAP SAVED FSH FF STR ERR SBin SHQ SHQ4 Ld MU.
reenterA asegs A4L HIx asegs_wx HP.
step.
asan_chkB.
step. step.
eapply (pe_pbreset HIx GA GA_pres (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo _ md A B ts0 cb nb pj sv errv);
[exact STC | exact INV0 | rewrite unsigned_lit by lia; reflexivity |].
intros m2 a1' a2' a3' a4' INV2 PBK2 _.
cbn [pf_spf] in *. unfold A_TP in *.
clear TOK SLOTS SHT MI WM INV0 INtk INq.
reopen_std INV2 ts0 ts0 (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 tk mxd depth l Hl bse Hbse m2.
lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) => replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
asan_rechkB.
step.
step.
step. step.
evt_done5.
eapply (pe_memappend_c HIx GA GA_pres MAPP (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m2 md A B ts0 cb nb pj sv errv T);
[exact STC | exact BSL | exact INV2 | exact PBK2 | exact BK | exact Hco | rewrite unsigned_lit by lia; reflexivity |].
intros m3 md3 A3 B3 pbs3 errv3 r w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 F3 fc3 INV3 OUT3 FS3 FRM3.
cbn [pf_spf] in *. unfold A_TP in *.
clear TOK SLOTS SHT MI WM Ld SHQ4 MU HP INV2 PBK2 BK.
set (ts3 := ts_pbs ts0 pbs3) in *.
reopen_std INV3 ts3 ts0 (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 tk mxd depth l Hl bse Hbse m3.
reenterA asegs A4L HIx asegs_wx HP.
destruct OUT3 as [(-> & PBK3 & BK3) | [-> Epbs3]].
- step.
if_true.
assert (BLO : 0 < bse < 2^63 /\ q <= bse) by (subst bse; lia).
step. asan_rechkMB 3.
asan_rechkMB 2.
step. step.
norm_sx32.
step. step.
ub_bse q bse (Z.of_nat depth).
step. step. ub_lvl q bse (Z.of_nat depth). step. ub_if_lit.
do 4 step. ub_lvl q bse (Z.of_nat depth). step. ub_if_lit.
step. if_truex.
step. ub_land Hb8. step. ub_if_lit.
clear SHT.
asan_chkMB 1.
step. step.
stepz.

assert (Hl3 : nth_error (t_levels ts3) (t_depth ts3) = Some l) by exact Hl.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m3 mc, WMc : wmono asegs m3 mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, Lc : rw_cells asegs mc bse _ |- _ =>
evt_done5; rewrite Hbse in MUc, Lc;
destruct (PE_INV_A_lvl_write HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m3 mc md3 A3 B3 ts3
cb nb pj sv errv3 l ST_comment_start (tl_ss l) c0 hn0 c0 STC INV3 Hl3 MUc WMc MIc TOKc Lc Hmode
ltac:(rewrite <- Hmode; apply QIsM.Mq2.lvl_mode_ws_same; [rewrite Hst; reflexivity | reflexivity]) ltac:(unfold ST_comment_start; lia) SS26 (or_introl eq_refl)
ltac:(rewrite Hst; reflexivity)) as [INV4 PBK4];
unstash Kbreak; eapply (Kbreak mc md3 A3 B3 pbs3 errv3);
[exact INV4 | exact (PBK4 1 PBK3)
| exact (BOK_lvl_restate _ _ ts3 B3 nB l ST_comment_start (tl_ss l) Hl3 (lvl_closed_keep l ST_comment_start _ _ _ _ _ eq_refl) (BOK_weaken _ _ _ _ _ nB (Nat.le_succ_diag_r nB) BK3))
| exact FS3 | exact FRM3]
end end.
- replace (Z_to_bv 64 (2^64 - 1)) with (Z_to_bv 64 (-1)) by (apply bv_eq; vm_compute; reflexivity).
step.
if_false.
step.
step.
asan_rechkB.
step.
evt_done5.
unstash Kerr16. eapply (Kerr16 m3 md3 A3 B3 errv3); [| exact FS3 | exact FRM3].
unfold ts3 in INV3. rewrite Epbs3 in INV3. exact INV3.
Qed.

Lemma eatws_eof_B :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet)
(gp t0 a1 a2 a5 a6 a7 s3 s6 s7 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
t_co ts = pf_len pf ->

(forall m' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md A B (ts_set_x ts (t_co ts) (tx_err (t_x ts) (Z_to_bv 64 0))) cb nb pj sv errv ->
AJ5 A4L HIx A T md
(pe_msO asegs pf pa APE_OUT gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F fc m')) ->

(forall m' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md A B ts cb nb pj sv errv ->
AJ5 A4L HIx A T md
(pe_msO asegs pf pa APE_ERR2 gp' t0' t1' t2' (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F fc m')) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa 0x9914c (pf_len pf - 1) gp t0 (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) a1 a2 (Z_to_bv 64 (q / 8 + 4 * Z.of_nat (t_depth ts) + A_SB)) (Z_to_bv 64 0) a5 a6 a7 s3 (Z_to_bv 64 q) s6 s7 (Z_to_bv 64 (Z.of_nat (t_depth ts))) s9 s11 t3 t4 t5 t6 F fc m).
Proof.
intros until fc. intros STC INV Heof Kout Kcont. pose proof INV as INV0.
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
unfold pe_msA, pe_msO in *.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
set (ts0 := TST depth levels len pb pbs (TS isd stpos (Z_to_bv 64 len) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * mxd) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t.
blk_factsA A4L HIx HP q (32 * mxd) Hqal Hqlo Hqhi Himg_q.
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
unfold APE_OUT, APE_ERR2 in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
stash Himg_t. stash Himg_q. clear PB TSK REST LV.
reenterA asegs A4L HIx asegs_wx HP.

lazymatch goal with |- evt _ _ (MS ?R ?FF _ ?fcc None ?mm ?rom) =>
assert (TAILC : forall a0v a1v, evt asegs (AJ5e A4L HIx A T md) (MS (bvmap_set 11 a1v (bvmap_set 10 a0v R)) FF (Z_to_bv 64 0x991bc) fcc None mm rom)) end.
{ intros a0v a1v.
step.
asan_rechkB.
step. step.
evt_done5. eapply (Kcont m). exact INV0. }
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
asan_rechkB.
step.
stepz.
step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _ |- _ =>
evt_done5;
destruct (PE_INV_A_tokw1 HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m mc md A B ts0
cb nb pj sv errv len (tx_err (t_x ts0) (Z_to_bv 64 0)) STC INV0 MUc WMc MIc TOKc ltac:(cbn [pf_len]; lia) eq_refl) as [INVe _];
eapply (Kout mc); exact INVe
end end.
* step.
if_truex. apply (TAILC _ _).
+ step.
if_truex. apply (TAILC _ _).
- if_truex. apply (TAILC _ _).
Qed.

Ltac frameA_now mc :=
unfold pe_frameA, pe_slotsA, pe_savedA_cells, ff_cellsA, ffsh_cells, FSH0; cbn [map pf_tk pf_spf pf_lenr pa_F pa_sp0 pa_oldloc pa_newloc]; unfold shA, A_SB;
split; [| split; [| split; [| split]]];
match goal with H : rw_cells asegs mc ?a _ |- rw_cells asegs mc ?a _ => exact H end.

Lemma eatws_loop_B :
forall (n : nat) (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel) (b : Z)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet)
(gp t0 a1 a2 a6 s3 s6 s7 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> pf_fl pf = 0 ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
PBOKat m ts b ->
CSTR_OK pf payload ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_eatws ->
t_co ts < pf_len pf -> nth_error payload (Z.to_nat (t_co ts)) = Some cb ->
(pf_len pf - t_co ts <= Z.of_nat n) ->

(forall m' co' cb' t0' a1' a5' a7' t3',
t_co ts <= co' < pf_len pf -> nth_error payload (Z.to_nat co') = Some cb' -> is_ws (bv_unsigned cb') = false ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md A B (ts_set_co ts co') cb' nb pj sv errv ->
PBOKat m' (ts_set_co ts co') b ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa 0x95654 co' gp t0' (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) a1' a2 (Z_to_bv 64 (q / 8 + 4 * Z.of_nat (t_depth ts) + A_SB)) (Z_to_bv 64 0) a5' a6 a7' s3 (Z_to_bv 64 q) s6 s7 (Z_to_bv 64 (Z.of_nat (t_depth ts))) s9 s11 t3' t4 t5 t6 F fc m')) ->

(forall m' co' cb' t0' a1' a5' a7' t3',
t_co ts <= co' < pf_len pf -> nth_error payload (Z.to_nat co') = Some cb' -> bv_unsigned cb' = 47 ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md A B (ts_set_co ts co') cb' nb pj sv errv ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa 0x980a8 co' gp t0' (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) a1' a2 (Z_to_bv 64 (q / 8 + 4 * Z.of_nat (t_depth ts) + A_SB)) (Z_to_bv 64 0) a5' a6 a7' s3 (Z_to_bv 64 q) s6 s7 (Z_to_bv 64 (Z.of_nat (t_depth ts))) s9 s11 t3' t4 t5 t6 F fc m')) ->

(forall m' cb' t0' a1' a5' a7' t3',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md A B (ts_set_co ts (pf_len pf)) cb' nb pj sv errv ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa 0x9914c (pf_len pf - 1) gp t0' (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) a1' a2 (Z_to_bv 64 (q / 8 + 4 * Z.of_nat (t_depth ts) + A_SB)) (Z_to_bv 64 0) a5' a6 a7' s3 (Z_to_bv 64 q) s6 s7 (Z_to_bv 64 (Z.of_nat (t_depth ts))) s9 s11 t3' t4 t5 t6 F fc m')) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa 0x94b6c (t_co ts) gp t0 (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) a1 a2 (Z_to_bv 64 (q / 8 + 4 * Z.of_nat (t_depth ts) + A_SB)) (Z_to_bv 64 0) (Z_to_bv 64 (pf_sb pf + t_co ts)) a6 (Z_to_bv 64 (bv_unsigned cb)) s3 (Z_to_bv 64 q) s6 s7 (Z_to_bv 64 (Z.of_nat (t_depth ts))) s9 s11 t3 t4 t5 t6 F fc m).
Proof.
induction n as [|n IH]; intros until fc; intros STC FL0 INV PBK CSTR Hl Hst Hco Hc Hn Kpop Ksl Keof.
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
unfold ts_set_co in Kpop, Ksl, Keof.
cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in Kpop, Ksl, Keof.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
pose proof FR as FR0. unfold pe_frameA in FR. destruct FR as (SLOTS & GAP & SAVED & FF & FSH). unfold pe_msA in *.
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
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8, A_SB in *.
pose proof (munch_refl [(tk, tk + 72); (Ff + 64, Ff + 65)] m) as MU.
assert (HW : Forall (pe_wtfA (PEF tk oldl newl len lenr sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl)) [(tk, tk + 72); (Ff + 64, Ff + 65)]).
{ apply Forall_cons; [left; cbn [fst snd pf_tk]; lia |]. apply Forall_cons; [| apply Forall_nil]. right; right; left. cbn [fst snd pa_F]. lia. }
clear LV OBJ HPR.
assert (SBpos : 0 < sb) by (exact (pe_sb_pos HIx GA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV0 ltac:(cbn [pf_len]; lia))).
stash PB. stash TSK.
reenterA asegs A4L HIx asegs_wx HP.
step.
rewrite (unsigned_lit (bv_unsigned cb)) by lia. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. change (2 ^ 8) with 256. rewrite (Z.mod_small (bv_unsigned cb) 256) by lia.
step. step.
destruct (Z_lt_dec 47 (bv_unsigned cb)) as [GT | LE].
{ if_truex. evt_done5.
eapply (Kpop m co cb); [lia | exact Hc | | exact INV0 | exact PBK].
unfold is_ws. rewrite !(proj2 (Z.eqb_neq _ _)) by lia. reflexivity. }
if_falsex.

step. step. norm_w32. step. step. step. rewrite (ws_word cb) by lia.
destruct (is_ws (bv_unsigned cb)) eqn:WS.
2:{
step. if_true.
step. step.
destruct (Z.eq_dec (bv_unsigned cb) 47) as [E47 | N47].
- if_falsex.
step. asan_rechkB.
pose proof (tok_flags_byteA mxd 0 m tk pb (Z.of_nat depth) q (TS isd stpos (Z_to_bv 64 co) err ucs high quote) TOK) as RDF.
step. step.
rewrite ?zxb_zero. clear RDF.
step.
step.
if_false.
step.
evt_done5.
eapply (Ksl m co cb); [lia | exact Hc | exact E47 | exact INV0].
- if_truex. evt_done5.
eapply (Kpop m co cb); [lia | exact Hc | exact WS | exact INV0 | exact PBK]. }

step.
if_false.
assert (Hnz : bv_unsigned cb <> 0) by (intros E0; rewrite E0 in WS; discriminate WS).
destruct (peek_cases (PEF tk oldl newl len lenr sb spf pmd mxd 0) payload co cb LENR CSTR (proj1 RR) ltac:(cbn [pf_len pf_mxd]; lia) ltac:(cbn [pf_len pf_mxd]; lia) Hc Hnz)
as [[Elenr Heof] | [Hne Hmore]]; cbn [pf_len pf_lenr pf_mxd] in *.
{
subst lenr.
step. step.
step. if_truex.
step. asan_rechkB.
step.
norm_sx32.
step.
norm_w32.
step. if_truex.
step. asan_rechkB.
stepz.
step.
rewrite Heof. if_false. step.
replace (sb + co) with (sb + (len - 1)) by lia.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _ |- _ =>
assert (FRc : pe_frameA asegs mc (PEF tk oldl newl len len sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) cb nb pj sv) by (frameA_now mc);
evt_done5;
destruct (PE_INV_A_tokw HIx GA GA_outside (PEF tk oldl newl len len sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m mc md A B ts0
cb nb pj sv errv _ (co + 1) (TS isd stpos (Z_to_bv 64 (co + 1)) err ucs high quote) cb nb STC INV0 MUc WMc MIc HW TOKc FRc
ltac:(cbn [pf_len]; lia) eq_refl) as [INV1 _];
rewrite Heof in INV1; eapply (Keof mc cb); exact INV1
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

stash Hv. stash GAP. stash SAVED. stash FSH. stash DSt. stash DSF. stash SHPF.
stash IH. stash Kpop. stash Ksl. stash Keof. stash INV0. stash REST. stash FR0. stash PBK. stash SBc. stash SBhi. stash LE1. stash Hc'. stash Hc. stash STR. stash HW.
step. step.
step. if_truex.
step. asan_rechkB.
step.
norm_sx32.
step.
norm_w32.
step. if_truex.
step. asan_rechkB.
stepz.
stash DFt. stash DSPt. clear SEP4c SEP4t SEP4i SEP8c SEP8t SEP8i SHT4.
step.
if_truex.
step. asan_rechkB.
clear SHT8.
lazymatch goal with TOKc : rw_cells asegs ?mc tk _ |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (tok_flags_byteA mxd 0 mc tk pb (Z.of_nat depth) q (TS isd stpos (Z_to_bv 64 (co + 1)) err ucs high quote) TOKc) as RDF end.
step. step.
rewrite ?zxb_zero. clear RDF.
step. step.
step.
if_true.
step. step.
sh_norm.

lazymatch goal with |- evt _ _ (MS ?R ?FF _ ?fcc None ?mm ?rom) =>
assert (JOIN : forall a7x t0x, evt asegs (AJ5e A4L HIx A T md) (MS (bvmap_set 17 a7x (bvmap_set 5 t0x R)) FF (Z_to_bv 64 0x94c3c) fcc None mm rom)) end.
2:{ unstash Hv. destruct Hv as [-> | [Hv8 Hvlt]].
- step. rewrite ?sxb_zero. step. if_false. apply JOIN.
- step. rewrite (sxb_small v) by lia. step. if_truex.
step.
unstash SBhi. rewrite (unsigned_lit (sb + co + 1)) by lia. rewrite (land7_mod8 (sb + co + 1)) by lia.
pose proof (Z.mod_pos_bound (sb + co + 1) 8 ltac:(lia)) as R8. remember ((sb + co + 1) mod 8) as r8 eqn:Er8 in *.
step.
if_truex. apply JOIN. }
intros a7x t0x. clear SHP.

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
unstash REST. unstash HW. unstash INV0. unstash FR0. unstash PBK.
replace (sb + co + 2) with (sb + (co + 1) + 1) by lia. replace (sb + co + 1) with (sb + (co + 1)) by lia.
unstash Kpop. unstash Ksl. unstash Keof. unstash IH.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, FFc : rw_cells asegs mc Ff _ |- _ =>
assert (FRc : pe_frameA asegs mc (PEF tk oldl newl len lenr sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) c' nb pj sv)
by (eapply (pe_frameA_scan HIx) with (ts := ts0); [exact STC | exact (proj1 REST) | exact FR0 | exact MUc | exact WMc | exact FFc]);
evt_done5;
destruct (PE_INV_A_tokw HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m mc md A B ts0
cb nb pj sv errv _ (co + 1) (TS isd stpos (Z_to_bv 64 (co + 1)) err ucs high quote) c' nb STC INV0 MUc WMc MIc HW TOKc FRc
ltac:(cbn [pf_len]; lia) eq_refl) as [INV1 PBK1];
eapply (IH (PEF tk oldl newl len lenr sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo mc md A B
(TST depth levels (co + 1) pb pbs (TS isd stpos (Z_to_bv 64 (co + 1)) err ucs high quote) obj objs objbs) l b c' nb pj sv errv T);
[ exact STC | reflexivity | exact INV1 | exact (PBK1 b PBK) | exact CSTR | exact Hl | exact Hst
| cbn [t_co pf_len]; lia | exact Hc' | cbn [t_co pf_len]; lia
| cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_sb pf_len pf_tk pf_lenr pa_F ts_set_co];
intros; eapply Kpop; [cbn [pf_len] in *; lia | eassumption | assumption | eassumption | eassumption]
| cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_sb pf_len pf_tk pf_lenr pa_F ts_set_co];
intros; eapply Ksl; [cbn [pf_len] in *; lia | eassumption | assumption | eassumption]
| cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_sb pf_len pf_tk pf_lenr pa_F ts_set_co];
intros; eapply Keof; eassumption ]
end end.
Qed.

Lemma seg_eatws_B :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP : Z) (nB : nat)
(gp t0 a5 a7 s3 s6 s7 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa -> pf_fl pf = 0 ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv -> PBOK m ts kP -> BOK pf pa ts B (S nB) ->
CSTR_OK pf payload ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_eatws ->
t_co ts < pf_len pf -> nth_error payload (Z.to_nat (t_co ts)) = Some cb ->

(forall m' co' cb' gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6',
t_co ts <= co' < pf_len pf -> nth_error payload (Z.to_nat co') = Some cb' -> is_ws (bv_unsigned cb') = false ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md A B
(ts_lvl (ts_set_co ts co') (TL (tl_ss l) (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) cb' nb pj sv errv ->
PBOK m' (ts_lvl (ts_set_co ts co') (TL (tl_ss l) (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) kP ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa APE_REDO co' gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F fc m')) ->

(forall m' md' A' B' pbs' errv' co' cb' gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc',
t_co ts <= co' < pf_len pf -> nth_error payload (Z.to_nat co') = Some cb' -> bv_unsigned cb' = 47 ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B'
(ts_pbs (ts_lvl (ts_set_co ts co') (TL ST_comment_start (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) pbs') cb' nb pj sv errv' ->
PBOK m' (ts_pbs (ts_lvl (ts_set_co ts co') (TL ST_comment_start (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) pbs') 1 ->
BOK pf pa (ts_pbs (ts_lvl (ts_set_co ts co') (TL ST_comment_start (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) pbs') B' nB ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msA asegs pf pa APE_BREAK co' gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' (Z_to_bv 64 2) s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' m')) ->

(forall m' md' A' B' errv' co' cb' x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc',
t_co ts <= co' < pf_len pf ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' (ts_set_co ts co') cb' nb pj sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msX asegs pf pa APE_ERR3 x1' gp' t0' t1' t2' (Z_to_bv 64 16) a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' m')) ->

(forall m' cb' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md A B
(ts_set_x ts (pf_len pf) (TS (ts_isd (t_x ts)) (ts_stpos (t_x ts)) (Z_to_bv 64 (pf_len pf)) (Z_to_bv 64 0) (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))) cb' nb pj sv errv ->
AJ5 A4L HIx A T md
(pe_msO asegs pf pa APE_OUT gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F fc m')) ->

(forall m' cb' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md A B (ts_set_co ts (pf_len pf)) cb' nb pj sv errv ->
AJ5 A4L HIx A T md
(pe_msO asegs pf pa APE_ERR2 gp' t0' t1' t2' (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F fc m')) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa (pe_jtA ST_eatws) (t_co ts) gp t0 (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) (Z_to_bv 64 (tl_st l)) (Z_to_bv 64 0) (Z_to_bv 64 (q / 8 + 4 * Z.of_nat (t_depth ts) + A_SB)) (Z_to_bv 64 0) a5 (Z_to_bv 64 APE_JTAB) a7 s3 (Z_to_bv 64 q) s6 s7 (Z_to_bv 64 (Z.of_nat (t_depth ts))) s9 s11 t3 t4 t5 t6 F fc m).
Proof.
intros until fc. intros STC BSL FL0 INV PBK BK CSTR Hl Hst Hco Hc Kredo Kbreak Kerr16 Kout Kcont. pose proof INV as INV0.
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR).
destruct INV as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof (proj1 REST) as HP.
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
unfold pe_frameA in FR. destruct FR as (SLOTS & _ & _ & FF & _).
unfold pe_slotsA in SLOTS. cbn zeta in SLOTS. unfold ff_cellsA in FF.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in SLOTS, FF.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
pose proof (bv_unsigned_in_range 8 cb) as CBR; unfold bv_modulus in CBR; cbn in CBR.
unfold pe_msA. cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pa_sp0 pa_F]. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
clear PB TSK REST TOK.
reenterA asegs A4L HIx asegs_wx HP. rewrite Hst. unfold ST_eatws. cbn [pe_jtA].
step. step.
change (zxb cb) with (Z_to_bv 64 (bv_unsigned cb)).
step.
step.
evt_done5.
eapply (eatws_loop_B (Z.to_nat (len - co)) (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m md A B ts0 l (co + kP)
cb nb pj sv errv T);
[exact STC | exact FL0 | exact INV0 | exact PBK | exact CSTR | exact Hl | exact Hst | exact Hco | exact Hc | cbn [pf_len t_co ts0]; lia | | |].
-
intros m' co' cb' t0' a1' a5' a7' t3' Hr Hc' Hws INV' PBK'.
eapply (eatws_pop_B (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m' md A B (ts_set_co ts0 co') l cb' nb pj sv errv T kP);
[exact STC | exact INV' | unfold PBOK; eapply PBOKat_weaken; [| exact PBK']; cbn [t_co ts_set_co ts0] in *; lia | exact Hl | exact Hst |].
intros m''. do 21 intro. intros INV'' PBK''. eapply (Kredo m'' co' cb'); [exact Hr | exact Hc' | exact Hws | exact INV'' | exact PBK''].
-
intros m' co' cb' t0' a1' a5' a7' t3' Hr Hc' H47 INV'.
eapply (eatws_slash_B (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m' md A B (ts_set_co ts0 co') l cb' nb pj sv errv T nB);
[exact STC | exact BSL | exact INV' | exact (BOK_set_co _ _ ts0 B (S nB) co' ltac:(cbn [t_co ts0] in *; lia) BK) | exact Hl | exact Hst | cbn [t_co ts_set_co pf_len] in *; lia | |].
+ intros until fc'. intros INV'' PBK'' BK'' FS'' FRM''. eapply (Kbreak _ _ _ _ _ _ co' cb'); [exact Hr | exact Hc' | exact H47 | exact INV'' | exact PBK'' | exact BK'' | exact FS'' | exact FRM''].
+ intros until fc'. intros INV'' FS'' FRM''. eapply (Kerr16 _ _ _ _ _ co' cb'); [exact Hr | exact INV'' | exact FS'' | exact FRM''].
-
intros m' cb' t0' a1' a5' a7' t3' INV'.
eapply (eatws_eof_B (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m' md A B (ts_set_co ts0 len) cb' nb pj sv errv T);
[exact STC | exact INV' | reflexivity | |].
+ intros m''. intros. eapply (Kout m'' cb'). eassumption.
+ intros m''. intros. eapply (Kcont m'' cb'). eassumption.
Qed.
End PeSEatwsB.
End RC__1.
End Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2EX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq5.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QJjn QRUw.Mq0 QRUw QkMG. Import QG8z Qdyh.Mq2 QLbz Q2Sr.
Import QbFI. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QsKa.Mqd Qiiq QSHS Ql4f.Mq4 Q1Y6.Mq4 QArX.Mq0 QrQv.Mq3 QYZ0.Mq6 QrQv.Mq4 QEUF.Mq2 QdGy.Mqc.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import QlKV.Mq2. Import Q2EX.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Lemma PBS_set_co : forall ts co', PBS (ts_set_co ts co') = PBS ts.
Proof. intros [d lv co pb pbs x o os obs] co'. reflexivity. Qed.
Lemma NAO_set_co : forall ts co', NAO ts -> NAO (ts_set_co ts co').
Proof. intros [d lv co pb pbs x o os obs] co' H. exact H. Qed.

Lemma PBJ_set_co : forall m m' ts k, (forall b, PBOKat m ts b -> PBOKat m' (ts_set_co ts (t_co ts + 1)) b) ->
PBJ m ts (k + 1) (t_co ts + 1) -> PBJ m' (ts_set_co ts (t_co ts + 1)) k (t_co (ts_set_co ts (t_co ts + 1))).
Proof.
intros m m' ts k PBT (g & P & Hg & J). exists g. split; [exact (PBT _ P)|]. split; [unfold ts_set_co; cbn [t_co]; lia|].
unfold ts_set_co at 2; cbn [t_co]. eapply (JL_same ts); [reflexivity | reflexivity | intros _; split; reflexivity | exact J].
Qed.
Section PeSMasterB.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_outside : forall m m' W, GA m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= hl_img_lo A4H \/ hl_img_hi A4H <= fst iv) W -> GA m'.
Variables (pf : pe_fix) (pa : pe_fixA) (q : Z) (LBc LM : list blk) (FRS : list frame) (payload : list byte)
(me : word -> option byte) (lo : Z) (sv : pe_saved) (T : TSet) (F0 : bvmap 5 word) (utf8rep : list byte).
Hypothesis STC : PE_STATIC_A HIx pf pa lo.
Hypothesis CSTR : CSTR_OK pf payload.
Hypothesis UTF : bytes_at asegs me UTF8REP_ADDR_A utf8rep.

Notation KOUTx := (KOUT_S HIx GA pf pa q LBc LM FRS payload me lo sv T F0).
Notation KERR2x := (KERR2_S HIx GA pf pa q LBc LM FRS payload me lo sv T F0).
Notation KBRKx := (KBRK_S HIx GA pf pa q LBc LM FRS payload me lo sv T F0).
Notation KALLx := (KALL_S HIx GA pf pa q LBc LM FRS payload me lo sv T F0).
Notation CASEx := (CASE_S HIx GA pf pa q LBc LM FRS payload me lo sv T F0 utf8rep).

Hypothesis KO : KOUTx.
Hypothesis KE : KERR2x.
Hypothesis HC : forall st, 0 <= st <= 26 -> CASEx st.
Hypothesis FL0 : pf_fl pf = 0.

Local Ltac tdsame TD := first [ exact TD
| lazymatch type of TD with tdepth_ok ?tsd => eapply (tdepth_ok_same tsd); [ | | | exact TD]; unfold ts_set_co, ts_set_err; cbn [t_levels t_depth t_objs pf_mxd]; reflexivity end ].

Theorem pe_master_S : forall n, KALLx n.
Proof.
induction n as [|n IH].
- split; [| split; [| split]]; intros until fc; intros M; exfalso; lia.
- pose proof IH as IHall. destruct IH as (IHL & IHR & IHB & IHA).
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR).
assert (KB : KBRKx (S n)).
{
intros ts m md A B cb nb pj errv gp t0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc M INV Hco Hcb NN SP TD PBK BK NA FS FRM.
eapply (seg_break_A HIx GA GA_outside); [exact STC | exact INV | exact Hco | |].
* intros m' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' Hz INV'.
eapply KO; [apply (PE_INV_A_W HIx GA); exact INV' | tdsame TD | | exact FS | exact FRM].
eapply (JOUT_of_PBJ (pf_len pf) m ts (ts_set_co ts (t_co ts + 1))); [exact PBK | lia | reflexivity | reflexivity | intros _; split; reflexivity].
* intros m' gp' t0' a0' a1' a3' a4' a5' a6' a7' s3' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' Hnz INV' PBT'.
eapply (IHL (ts_set_co ts (t_co ts + 1))); [| exact INV' | exact NN | | | | | | apply NAO_set_co; exact NA | exact FS | exact FRM].
{ unfold mbrk, mloop, mbase, ts_set_co in *. cbn [t_co pf_mxd]. lia. }
{ revert SP. unfold SPOK, ts_set_co, cur_st. destruct ts as [dp9 lv9 co9 pb9 pbs9 x9 ob9 os9 obs9]; cbn [t_levels t_depth t_x t_co pf_mxd]. intros SP Hz. specialize (SP Hz). unfold SPV in *. cbn [ts_stpos pf_mxd] in *. lia. }
{ tdsame TD. }
{ unfold ts_set_co; cbn [t_co pf_mxd]. intros NE. pose proof INV as [(_ & _ & CO & _) _].
destruct (peek_cases pf payload (t_co ts) cb LENR CSTR (proj1 RR) ltac:(lia) ltac:(lia) Hcb Hnz) as [[E _] | [_ LT]]; [exfalso; exact (NE E) | exact LT]. }
{ rewrite PBS_set_co. exact (PBJ_set_co m m' ts (PBS ts) PBT' PBK). }
{ eapply BOK_weaken; [| apply BOK_set_co; [| exact BK]; lia]. unfold bloop, bbrk, bx, bxb, mbrk, mloop, mbase, cur_st, cur_ss, ts_set_co. cbn [t_co t_levels t_depth pf_mxd]. lia. } }
split; [| split; [| split; [exact KB | exact KB]]].
+
intros ts m md A B cb nb pj errv gp t0 a0 a1 a3 a4 a5 a6 a7 s3 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc M INV NN SP TD CLT PBK BK NA FS FRM.
eapply (seg_loop_B HIx GA GA_outside); [exact STC | exact FL0 | exact INV | exact CLT | |].
*
intros m' c nb' gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' Hco Hc INV' PBT'.
pose proof INV' as [(LEN32 & D32 & CO & _) REST']. pose proof REST' as (HP' & LV' & _).
destruct (nth_error (t_levels ts) (t_depth ts)) as [l|] eqn:Hl; [| exfalso; apply nth_error_None in Hl; lia].
pose proof (LV' _ _ Hl) as (ST26 & SS26 & _).
eapply (seg_redo0_A HIx GA); [exact STC | exact INV' | exact Hl |]. intros a5''.
eapply (HC (tl_st l) ST26 n ts l); [exact STC | exact INV' | exact Hl | reflexivity | exact Hco | exact Hc | intros E; exfalso; exact (NN E) | exact SP | exact TD
| destruct PBK as (g & P & Hg & J); exists g; split; [exact (PBT' _ P) | split; [exact Hg | exact J]]
| eapply BOK_weaken; [| exact BK]; unfold bloop, bredo, mloop, mredo; pose proof (rank_le (cur_st ts) (cur_ss ts)); lia
| apply OBJW_of_NAO; exact NA | exact UTF | exact CSTR | exact FS | exact FRM
| unfold mloop, mredo in *; pose proof (rank_le (cur_st ts) (cur_ss ts)); lia | exact IHall | exact KO | exact KE].
*
intros m' e gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' INV'.
eapply KO; [apply (PE_INV_A_W HIx GA); exact INV' | tdsame TD | | exact FS | exact FRM].
eapply (JOUT_of_PBJ (pf_len pf) m ts (Qdyh.Mq2.ts_set_err ts e)); [exact PBK | pose proof INV as [(_ & _ & CO9 & _) _]; lia | reflexivity | reflexivity | intros _; split; reflexivity].
+
intros ts m md A B cb nb pj errv gp t0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc M INV Hco Hcb NUM SP TD PBK BK OW FS FRM.
pose proof INV as [(LEN32 & D32 & CO & _) REST]. pose proof REST as (HP & LV & _).
destruct (nth_error (t_levels ts) (t_depth ts)) as [l|] eqn:Hl; [| exfalso; apply nth_error_None in Hl; lia].
pose proof (LV _ _ Hl) as (ST26 & SS26 & _).
eapply (seg_redo_A HIx GA); [exact STC | exact INV | exact Hl |]. intros a5'.
eapply (HC (tl_st l) ST26 n ts l); [exact STC | exact INV | exact Hl | reflexivity | exact Hco | exact Hcb | exact NUM | exact SP | exact TD
| exact PBK | exact BK | exact OW | exact UTF | exact CSTR | exact FS | exact FRM | lia | exact IHall | exact KO | exact KE].
Qed.
End PeSMasterB.
End RC__1.
End Mq5.

Module Mq6.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QJjn QRUw.Mq0 QRUw QRUw.Mq2 QmZZ. Import QPZI.Mq4. Import QkMG. Import QG8z Qdyh.Mq0.
Import QbFI. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqj QsKa.Mqd Qiiq QsKa.Mqf Q4v2 QlKV.Mqf QlKV.Mqh QSHS Ql4f.Mq4 QsKa.Mqh QrQv.Mq4 QEUF.Mq2 QdGy.Mqe Qeia.Mq7.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section WithIface.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_outside : forall m m' W, GA m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= hl_img_lo A4H \/ hl_img_hi A4H <= fst iv) W -> GA m'.
Hypothesis GA_pres : forall LB SP m m', heap_pres A4H LB SP m m' -> GA m -> GA m'.

Definition PE_WINX (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (p : Z) (s : option jshape) (BS : list blk) (rc : Z)
(errv : word) (FRX : Prop) : Prop :=
(length (t_levels ts) = Z.to_nat (pf_mxd pf) /\ (t_depth ts < Z.to_nat (pf_mxd pf))%nat /\
0 <= t_co ts <= pf_len pf /\ ts_choff (t_x ts) = Z_to_bv 64 (t_co ts) /\
rw_cells asegs m (pf_tk pf) (tok_cells_g (pf_mxd pf) (pf_fl pf) (t_pb ts) (Z.of_nat (t_depth ts)) q (t_x ts)) /\
pbuf asegs m (t_pbs ts) (t_pb ts) /\ t_pb ts <> 0 /\
tstack asegs m q (t_levels ts) /\
FRX) /\
PE_BASE_A HIx GA pf pa LB0 LM FRS payload me lo m md A B (pe_blocksA pf q LB0 (tsF ts BS)) errv /\
(forall i li, nth_error (t_levels ts) i = Some li -> i <> t_depth ts -> lvl_cur asegs A4F m (t_depth ts) i li) /\
(exists l, nth_error (t_levels ts) (t_depth ts) = Some l /\ lvl_bare l) /\
t_objbs ts = [] /\
put_pre A4H A4F s m BS p rc.

Lemma PE_WIN_of_WINX : forall pf pa q LB0 LM FRS payload me lo m md A B ts p s BS rc cb nb pj sv errv,
PE_WINX pf pa q LB0 LM FRS payload me lo m md A B ts p s BS rc errv (pe_frameA asegs m pf pa cb nb pj sv) ->
PE_WIN HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts p s BS rc cb nb pj sv errv.
Proof. intros until errv. intros H. exact H. Qed.

Lemma PE_WINX_open : forall pf pa q LB0 LM FRS payload me lo m md A B ts errv l (FRX : Prop),
PE_INV_AX HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts errv FRX ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_name l = 0 -> tl_nbs l = [] -> t_objbs ts = [] ->
PE_WINX pf pa q LB0 LM FRS payload me lo m md A B (ts_lvl ts (TL (tl_st l) (tl_ss l) (tl_cur l) None [] 0 [])) (tl_cur l) (tl_cs l) (tl_cbs l) 1 errv FRX.
Proof.
intros pf pa q LB0 LM FRS payload me lo m md A B ts errv l FRX [CORE REST] Hl Hn Hnbs Eobj.
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
apply PE_REST_A_base in REST as (BASE & LV & OBJ & BUD).
set (lw := TL (tl_st l) (tl_ss l) (tl_cur l) None [] 0 []).
assert (Hd : (t_depth ts < length (t_levels ts))%nat) by (apply nth_error_Some; rewrite Hl; discriminate).
pose proof (LV _ _ Hl) as (R1 & R2 & JO & _).
split; [| split; [| split; [| split; [| split]]]].
- unfold ts_lvl; cbn [t_levels t_depth t_co t_x t_pb t_pbs]. split; [rewrite lupd_length; exact LEN32|]. split; [exact D32|]. split; [exact CO|]. split; [exact CHOFF|].
split; [exact TOK|]. split; [exact PB|]. split; [exact Hpb|]. split; [| exact FR].
eapply tstack_lupd_srec; [exact TSK | exact Hl |]. unfold srec_cells, lw; cbn [tl_st tl_ss tl_cur tl_name]. rewrite Hn. reflexivity.
- destruct BASE as (HP & BASE'). split; [| exact BASE'].
eapply (heapA_perm A4L HIx); [exact HP | | apply Permutation_refl | apply Permutation_refl].
eapply Permutation_trans; [apply (pe_blocksA_cur_perm2 pf q LB0 ts l Hl)|]. apply Permutation_sym.
eapply Permutation_trans; [apply (pe_blocksA_lvl_obj_perm pf q LB0 ts l lw 0 None (tl_cbs l) Hl)|].
unfold lvl_blocks, lw; cbn [tl_cbs tl_nbs app]. rewrite Hnbs, Eobj, app_nil_r. cbn [app]. apply Permutation_refl.
- unfold ts_lvl; cbn [t_levels t_depth]. intros i li Hli Hne. rewrite nth_error_lupd_neq in Hli by congruence. exact (LV i li Hli).
- exists lw. split; [unfold ts_lvl; cbn [t_levels t_depth]; apply nth_error_lupd_eq; exact Hd|].
unfold lvl_bare, lw; cbn [tl_st tl_ss tl_cs tl_cbs tl_name tl_nbs]. repeat split; try reflexivity; lia.
- exact Eobj.
- unfold put_pre. destruct (tl_cs l) as [s'|]; cbn [jopt] in JO; [| exact JO]. destruct JO as [Hp J]. split; [exact Hp|]. split; [lia | exact J].
Qed.

Lemma PE_WINX_write : forall pf pa q LB0 LM FRS payload me lo m mc md A B ts p s BS rc errv W l' (FRX FRX' : Prop),
PE_STATIC_A HIx pf pa lo ->
PE_WINX pf pa q LB0 LM FRS payload me lo m md A B ts p s BS rc errv FRX ->
munch W m mc -> wmono asegs m mc -> mem_inv asegs mc -> Forall (pe_wtqA pf pa q) W ->
rw_cells asegs mc (pf_tk pf) (tok_cells_g (pf_mxd pf) (pf_fl pf) (t_pb ts) (Z.of_nat (t_depth ts)) q (t_x ts)) ->
tstack asegs mc q (lupd (t_levels ts) (t_depth ts) l') ->
FRX' ->
lvl_bare l' ->
PE_WINX pf pa q LB0 LM FRS payload me lo mc md A B (ts_lvl ts l') p s BS rc errv FRX'
/\ (forall b, PBOKat m ts b -> PBOKat mc (ts_lvl ts l') b).
Proof.
intros pf pa q LB0 LM FRS payload me lo m mc md A B ts p s BS rc errv W l' FRX FRX' STC (CORE & BASE & LVo & (l & Hl & BARE) & Eobj & PP) MU WM MI HW TOKc TSKc FRc BARE'.
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
assert (Hd : (t_depth ts < length (t_levels ts))%nat) by (apply nth_error_Some; rewrite Hl; discriminate).
destruct (PE_BASE_A_private_write HIx GA GA_outside pf pa q LB0 LM FRS payload me lo m mc md A B (tsF ts BS) errv W STC BASE MU WM MI (pe_wtqA_private _ _ _ _ _ HW)) as [BASEc AG].
unfold tsF in AG; cbn [t_objbs t_levels] in AG.
assert (Eb : lvl_blocks l' = lvl_blocks l).
{ destruct BARE as (_ & _ & _ & C1 & _ & C2). destruct BARE' as (_ & _ & _ & C1' & _ & C2'). unfold lvl_blocks. rewrite C1, C2, C1', C2'. reflexivity. }
split.
2:{ intros b PBK. eapply PBOKat_same with (ts := ts); [reflexivity | reflexivity |].
eapply PBOKat_agree; [exact PBK | | apply incl_refl].
eapply (agree_wtqA HIx) with (ts := tsF ts BS); [exact STC | exact (proj1 BASE) | exact MU | exact WM | exact HW |].
intros a n Hin. assert (HinL : In (a, n) (pe_blocksA pf q LB0 (tsF ts BS) ++ LM)) by (unfold pe_blocksA, tstate_blocks, tsF; cbn [t_pbs]; apply in_or_app; left; apply in_or_app; left; apply in_or_app; left; exact Hin).
split; [exact HinL|].
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ (proj1 BASE)) as ND. unfold pe_blocksA in ND. rewrite <- app_assoc in ND. split.
+ intros ->. refine (nodup_app_ne _ _ _ _ _ _ ND _ _ eq_refl); [unfold tstate_blocks, tsF; cbn [t_pbs]; apply in_or_app; left; exact Hin | left; reflexivity].
+ intros ->. refine (nodup_app_ne _ _ _ _ _ _ ND _ _ eq_refl); [unfold tstate_blocks, tsF; cbn [t_pbs]; apply in_or_app; left; exact Hin | right; left; reflexivity]. }
split; [| split; [| split; [| split; [| split]]]].
- unfold ts_lvl; cbn [t_levels t_depth t_co t_x t_pb t_pbs]. split; [rewrite lupd_length; exact LEN32|]. split; [exact D32|]. split; [exact CO|]. split; [exact CHOFF|].
split; [exact TOKc|]. split; [| split; [exact Hpb | split; [exact TSKc | exact FRc]]].
eapply (pbuf_wtqA HIx) with (ts := tsF ts BS); [exact STC | exact (proj1 BASE) | exact PB | exact MU | exact WM | exact HW].
- rewrite (pe_blocksA_tsF_lvl pf q LB0 ts BS l l' Hl Eb). exact BASEc.
- unfold ts_lvl; cbn [t_levels t_depth]. intros i li Hli Hne. rewrite nth_error_lupd_neq in Hli by congruence.
eapply (lvl_cur_agree asegs A4F); [exact (LVo i li Hli Hne) | exact AG |].
intros b Hb. apply in_or_app; right. apply in_concat. exists (lvl_blocks li). split; [| exact Hb]. apply in_map. eapply nth_error_In; exact Hli.
- exists l'. split; [unfold ts_lvl; cbn [t_levels t_depth]; apply nth_error_lupd_eq; exact Hd | exact BARE'].
- exact Eobj.
- unfold put_pre in *. destruct s as [s'|]; [| exact PP]. destruct PP as (Hp & Hrc & J). split; [exact Hp|]. split; [exact Hrc|].
eapply jval_agree; [exact J | exact AG | intros b Hb; apply in_or_app; left; exact Hb].
Qed.

Lemma PE_WINX_write_x : forall pf pa q LB0 LM FRS payload me lo m mc md A B ts p s BS rc errv W l' x' (FRX FRX' : Prop),
PE_STATIC_A HIx pf pa lo ->
PE_WINX pf pa q LB0 LM FRS payload me lo m md A B ts p s BS rc errv FRX ->
munch W m mc -> wmono asegs m mc -> mem_inv asegs mc -> Forall (pe_wtqA pf pa q) W ->
rw_cells asegs mc (pf_tk pf) (tok_cells_g (pf_mxd pf) (pf_fl pf) (t_pb ts) (Z.of_nat (t_depth ts)) q x') -> ts_choff x' = Z_to_bv 64 (t_co ts) ->
tstack asegs mc q (lupd (t_levels ts) (t_depth ts) l') ->
FRX' ->
lvl_bare l' ->
PE_WINX pf pa q LB0 LM FRS payload me lo mc md A B (ts_set_x (ts_lvl ts l') (t_co ts) x') p s BS rc errv FRX'
/\ (forall b, PBOKat m ts b -> PBOKat mc (ts_set_x (ts_lvl ts l') (t_co ts) x') b).
Proof.
intros pf pa q LB0 LM FRS payload me lo m mc md A B ts p s BS rc errv W l' x' FRX FRX' STC (CORE & BASE & LVo & (l & Hl & BARE) & Eobj & PP) MU WM MI HW TOKc Hch TSKc FRc BARE'.
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
assert (Hd : (t_depth ts < length (t_levels ts))%nat) by (apply nth_error_Some; rewrite Hl; discriminate).
destruct (PE_BASE_A_private_write HIx GA GA_outside pf pa q LB0 LM FRS payload me lo m mc md A B (tsF ts BS) errv W STC BASE MU WM MI (pe_wtqA_private _ _ _ _ _ HW)) as [BASEc AG].
unfold tsF in AG; cbn [t_objbs t_levels] in AG.
assert (Eb : lvl_blocks l' = lvl_blocks l).
{ destruct BARE as (_ & _ & _ & C1 & _ & C2). destruct BARE' as (_ & _ & _ & C1' & _ & C2'). unfold lvl_blocks. rewrite C1, C2, C1', C2'. reflexivity. }
split.
2:{ intros b PBK. eapply PBOKat_same with (ts := ts); [reflexivity | reflexivity |].
eapply PBOKat_agree; [exact PBK | | apply incl_refl].
eapply (agree_wtqA HIx) with (ts := tsF ts BS); [exact STC | exact (proj1 BASE) | exact MU | exact WM | exact HW |].
intros a n Hin. assert (HinL : In (a, n) (pe_blocksA pf q LB0 (tsF ts BS) ++ LM)) by (unfold pe_blocksA, tstate_blocks, tsF; cbn [t_pbs]; apply in_or_app; left; apply in_or_app; left; apply in_or_app; left; exact Hin).
split; [exact HinL|].
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ (proj1 BASE)) as ND. unfold pe_blocksA in ND. rewrite <- app_assoc in ND. split.
+ intros ->. refine (nodup_app_ne _ _ _ _ _ _ ND _ _ eq_refl); [unfold tstate_blocks, tsF; cbn [t_pbs]; apply in_or_app; left; exact Hin | left; reflexivity].
+ intros ->. refine (nodup_app_ne _ _ _ _ _ _ ND _ _ eq_refl); [unfold tstate_blocks, tsF; cbn [t_pbs]; apply in_or_app; left; exact Hin | right; left; reflexivity]. }
split; [| split; [| split; [| split; [| split]]]].
- unfold ts_set_x, ts_lvl; cbn [t_levels t_depth t_co t_x t_pb t_pbs]. split; [rewrite lupd_length; exact LEN32|]. split; [exact D32|]. split; [exact CO|]. split; [exact Hch|].
split; [exact TOKc|]. split; [| split; [exact Hpb | split; [exact TSKc | exact FRc]]].
eapply (pbuf_wtqA HIx) with (ts := tsF ts BS); [exact STC | exact (proj1 BASE) | exact PB | exact MU | exact WM | exact HW].
- replace (pe_blocksA pf q LB0 (tsF (ts_set_x (ts_lvl ts l') (t_co ts) x') BS)) with (pe_blocksA pf q LB0 (tsF (ts_lvl ts l') BS)) by reflexivity.
rewrite (pe_blocksA_tsF_lvl pf q LB0 ts BS l l' Hl Eb). exact BASEc.
- unfold ts_set_x, ts_lvl; cbn [t_levels t_depth]. intros i li Hli Hne. rewrite nth_error_lupd_neq in Hli by congruence.
eapply (lvl_cur_agree asegs A4F); [exact (LVo i li Hli Hne) | exact AG |].
intros b Hb. apply in_or_app; right. apply in_concat. exists (lvl_blocks li). split; [| exact Hb]. apply in_map. eapply nth_error_In; exact Hli.
- exists l'. split; [unfold ts_set_x, ts_lvl; cbn [t_levels t_depth]; apply nth_error_lupd_eq; exact Hd | exact BARE'].
- exact Eobj.
- unfold put_pre in *. destruct s as [s'|]; [| exact PP]. destruct PP as (Hp & Hrc & J). split; [exact Hp|]. split; [exact Hrc|].
eapply jval_agree; [exact J | exact AG | intros b Hb; apply in_or_app; left; exact Hb].
Qed.

Lemma PE_WINX_callG2 : forall pf pa q LB0 LM FRS payload me lo m1 m2 md md2 A A2 B B2 ts p s BS rc p2 s2 BS2 rc2 errv errv2 (FRX FRX' : Prop),
PE_STATIC_A HIx pf pa lo ->
PE_WINX pf pa q LB0 LM FRS payload me lo m1 md A B ts p s BS rc errv FRX ->
model_vm_only (cfg_model md) (cfg_model md2) ->
heap_pres A4H (pe_blocksA pf q LB0 ts ++ LM ++ fr_ivs A4L ((pa_F pa, 2) :: FRS)) (pf_spf pf) m1 m2 ->
HEAPA A4L HIx A2 (pe_blocksA pf q LB0 (tsF ts BS2)) LM ((pa_F pa, 2) :: FRS) B2 m2 md2 ->
stk asegs m2 lo (pf_spf pf) -> rw_cells asegs m2 A_ERRNO [C4 errv2] ->
put_pre A4H A4F s2 m2 BS2 p2 rc2 ->
FRX' ->
PE_WINX pf pa q LB0 LM FRS payload me lo m2 md2 A2 B2 ts p2 s2 BS2 rc2 errv2 FRX'.
Proof.
intros pf pa q LB0 LM FRS payload me lo m1 m2 md md2 A A2 B B2 ts p s BS rc p2 s2 BS2 rc2 errv errv2 FRX FRX' STC (CORE & BASE & LVo & CUR & Eobj & PP) VM HPR HP2 ST2 ERR2 PP2 FR2.
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR).
set (RB := pe_blocksA pf q LB0 ts) in *.
assert (INtk : In (pf_tk pf, 72) RB) by (unfold RB, pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * pf_mxd pf) RB) by (unfold RB, pe_blocksA; apply in_or_app; right; right; left; reflexivity).
assert (LB0R : incl LB0 RB) by (unfold RB, pe_blocksA; intros b Hb; apply in_or_app; right; right; right; exact Hb).
assert (AG : agree_on asegs RB m1 m2) by (eapply (agree_of_heap_pres asegs A4H); [exact HPR | reflexivity | intros b Hb; apply in_or_app; left; exact Hb]).
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR) in TOK; [| eapply client_range_block; [apply in_or_app; left; exact INtk | lia | unfold tok_cells_g; cbn; lia]]. cbn [hl_segs hla_base A4L A4H] in TOK.
apply (tstack_pres_g A4H _ _ _ _ _ _ HPR (in_or_app _ _ _ (or_introl INq))) in TSK; [| exact LEN32]. cbn [hl_segs hla_base A4L A4H] in TSK.
split; [| split; [| split; [| split; [exact CUR | split; [exact Eobj | exact PP2]]]]].
- split; [exact LEN32|]. split; [exact D32|]. split; [exact CO|]. split; [exact CHOFF|]. split; [exact TOK|]. split; [| split; [exact Hpb | split; [exact TSK | exact FR2]]].
eapply pbuf_agree; [exact PB | exact AG |]. unfold RB, pe_blocksA, tstate_blocks. intros b Hb. apply in_or_app; left. apply in_or_app; left. exact Hb.
- eapply (PE_BASE_A_callG HIx GA GA_pres pf pa LB0 LM FRS payload me lo m1 m2 md md2 A A2 B B2 _ _ errv errv2 RB); [exact STC | exact BASE | exact VM | exact HPR | exact LB0R | exact HP2 | exact ST2 | exact ERR2].
- intros i li Hli Hne. eapply (lvl_cur_agree asegs A4F); [exact (LVo i li Hli Hne) | exact AG |].
intros b Hb. unfold RB, pe_blocksA, tstate_blocks. apply in_or_app; left. apply in_or_app; right. apply in_or_app; right. apply in_concat. exists (lvl_blocks li). split; [| exact Hb]. apply in_map. eapply nth_error_In; exact Hli.
Qed.

Lemma pe_uw_atX : forall pf pa lo m nb pj sv v2 ra2 ffc shc,
PE_STATIC_A HIx pf pa lo -> pe_frameAX m pf pa nb pj sv ffc shc ->
pe_s0 sv = Z_to_bv 64 v2 -> pe_ra sv = Z_to_bv 64 ra2 ->
(v2 < alloc_ceiling \/ v2 mod 8 <> 0 \/ v2 <= pa_sp0 pa \/ hiA_top A4L HIx - 16 <= v2) -> 0 <= v2 < 2^64 ->
uw_at (hiA_top A4L HIx) m (pf_spf pf) (pa_sp0 pa) (UWfp ra2 v2).
Proof.
intros pf pa lo m nb pj sv v2 ra2 ffc shc STC (_ & _ & SV & _) S0V RAV HV HR.
pose proof STC as (LO & LOS & GEO & HT & SP0 & _). pose proof GEO as (Gspf & Gsp0 & Gle & _).
cbn [uw_at]. split; [lia|]. split; [clear - Gsp0; Z.div_mod_to_equations; lia|]. split; [lia|]. split; [| split; [exact HV | exact HR]].
unfold pe_savedA_cells in SV. destruct SV as [[_ SVB] _].
cbn [cells_bytes cbytes app] in SVB. rewrite <- ?app_assoc in SVB.
do 11 (apply bytes_at_app in SVB as [_ SVB]; rewrite length_le8 in SVB).
rewrite S0V, RAV in SVB. eapply bytes_at_ext; [| reflexivity].
match type of SVB with bytes_at _ _ ?a _ => replace a with (pa_sp0 pa - 16) in SVB by lia end. exact SVB.
Qed.

End WithIface.
End RC__1.
End Mq6.

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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qdyh.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qdyh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qdyh.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QIsM.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4v2.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1Ey.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1Ey. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Ql4f.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql4f.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1Y6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1Y6.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QrQv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QrQv.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEUF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEUF. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QW22.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QW22.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdGy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdGy.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYZ0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYZ0.Mq3.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section PeSEatwsA.
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

Ltac reopen_std INVx TSx ts0 PF q LB0 tk mxd depth l Hl bse Hbse mX :=
pose proof INVx as [CORE2 REST2];
destruct CORE2 as (_ & _ & _ & _ & TOK & _ & _ & TSK & FR);
pose proof REST2 as (HP & _); clear REST2;
try unfold TSx in TOK, TSK; try unfold ts_pbs, ts_lvl in TOK, TSK; try unfold ts0 in TOK, TSK;
cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_tk pf_mxd pf_fl] in TOK, TSK;
unfold tok_cells_g in TOK; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK;
unfold pe_frameA in FR; destruct FR as (SLOTS & _ & _ & _ & _); unfold pe_slotsA in SLOTS; cbn zeta in SLOTS;
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in SLOTS;
assert (INtk : In (tk, 72) (pe_blocksA PF q LB0 TSx)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity);
assert (INq : In (q, 32 * mxd) (pe_blocksA PF q LB0 TSx)) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity);
pose proof (tok_shadowA HIx _ _ _ _ _ _ _ _ HP INtk) as SHT;
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI;
pose proof (wmono_refl asegs mX) as WM;
pose proof (TSK depth l Hl) as Ld; rewrite <- Hbse in Ld; unfold srec_cells in Ld;
pose proof (stack_shadowA HIx _ _ _ _ _ _ _ q mxd (Z.of_nat depth) 0 HP INq ltac:(lia) ltac:(lia)) as SHQ4;
replace (q / 8 + 4 * Z.of_nat depth + 0 + A_SB) with (bse / 8 + 2147450880) in SHQ4 by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia);
pose proof (munch_refl [(bse, bse + 32)] mX) as MU;
unfold shA in *; a4l; unfold SB2, SB4, SB7, SB8 in *;
clear TSK INtk INq.

Lemma eatws_pop_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP : Z)
(gp t0 t1 t2 a1 a3 a4 a5 a6 a7 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv -> PBOK m ts kP ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_eatws ->
(forall m' a0' a1' a2' a3',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md A B
(ts_lvl ts (TL (tl_ss l) (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) cb nb pj sv errv ->
PBOK m' (ts_lvl ts (TL (tl_ss l) (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) kP ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa APE_REDO (t_co ts) gp t0 t1 t2 a0' a1' a2' a3' a4 a5 a6 a7
(Z_to_bv 64 (Z.of_nat (t_depth ts))) (Z_to_bv 64 (pf_tk pf + 56)) (Z_to_bv 64 (pa_F pa + 64)) F fc m')) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa 0x94d04 (t_co ts) gp t0 t1 t2
(Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) a1
(Z_to_bv 64 (q / 8 + 4 * Z.of_nat (t_depth ts) + A_SB)) a3 a4 a5 a6 a7
(Z_to_bv 64 (Z.of_nat (t_depth ts))) (Z_to_bv 64 q) (Z_to_bv 64 (pa_F pa + 64)) F fc m).
Proof.
intros until fc. intros STC INV PBK Hl Hst Kredo. pose proof INV as INV0. pe_openA STC INV.
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
unfold APE_BREAK, APE_REDO, APE_OUT, APE_ERRMEM, APE_ERRST, APE_JTAB in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
stash Himg_t. stash Himg_q. clear PB REST TSK HP LV OBJ HPR BUD GAP SAVED FSH FF STR ERR SBin.
reenterA asegs A4L HIx asegs_wx HP.
replace (q + 32 * Z.of_nat depth) with bse by lia.
step. step.
asan_chkA.
asan_rechkM 1.
norm_sx32.
stepz.
step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, Lc : rw_cells asegs mc bse _ |- _ =>
evt_done5; subst bse;
destruct (PE_INV_A_lvl_write HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m mc md A B ts0
cb nb pj sv errv l (tl_ss l) (tl_ss l) c0 hn0 c0 STC INV0 Hl MUc WMc MIc TOKc Lc Hmode
(Qa8x.Mq2.lvl_mode_ws_pop (tl_st l) (tl_ss l) c0 hn0 ltac:(rewrite Hst; reflexivity) SS26 Hmode) SS26 SS26 (or_introl eq_refl)
ltac:(rewrite Hst; exact (lvl_mode_ws_ss_noadd (tl_st l) (tl_ss l) c0 hn0 ltac:(rewrite Hst; reflexivity) Hmode))) as [INV3 PBK3];
eapply (Kredo mc); [exact INV3 | exact (PBK3 kP PBK)]
end end.
Qed.

Lemma eatws_slash_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (nB : nat)
(gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv -> BOK pf pa ts B (S nB) ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_eatws ->
t_co ts < pf_len pf ->

(forall m' md' A' B' pbs' errv' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' F' fc',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B'
(ts_pbs (ts_lvl ts (TL ST_comment_start (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) pbs') cb nb pj sv errv' ->
PBOK m' (ts_pbs (ts_lvl ts (TL ST_comment_start (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) pbs') 1 ->
BOK pf pa (ts_pbs (ts_lvl ts (TL ST_comment_start (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) pbs') B' nB ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msA asegs pf pa APE_BREAK (t_co ts) gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5'
(Z_to_bv 64 (pf_tk pf + 56)) (Z_to_bv 64 (pa_F pa + 64)) F' fc' m')) ->

(forall m' md' A' B' errv' x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s5' t3' t4' t5' t6' F' fc',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' ts cb nb pj sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(Q1Y6.Mq2.pe_msE pf pa APE_ERR2 x1' gp' t0' t1' t2' (Z_to_bv 64 16) a1' a2' a3' a4' a5' a6' a7'
(Z_to_bv 64 (pf_tk pf / 8 + SB2)) (Z_to_bv 64 (pf_tk pf + 20)) s5' (Z_to_bv 64 (pf_tk pf + 36)) (Z_to_bv 64 (pf_tk pf + 32)) (Z_to_bv 64 (pa_F pa))
(Z_to_bv 64 (pf_tk pf + 56)) (Z_to_bv 64 (pf_sb pf + t_co ts)) t3' t4' t5' t6' F' fc' m')) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa 0x96e40 (t_co ts) gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 (Z_to_bv 64 (pf_tk pf + 56)) (Z_to_bv 64 (pa_F pa + 64)) F fc m).
Proof.
intros until fc. intros STC BSL INV BK Hl Hst Hco Kbreak Kerr16. pose proof INV as INV0. pe_openA STC INV.
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
unfold APE_BREAK, APE_REDO, APE_OUT, APE_ERRMEM, APE_ERRST, APE_ERR2, APE_JTAB in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
stash Himg_t. stash Himg_q. stash Kbreak. stash Kerr16. clear PB REST TSK HP LV OBJ HPR BUD GAP SAVED FSH FF STR ERR SBin SHQ SHQ4 Ld MU.
reenterA asegs A4L HIx asegs_wx HP.
step.
asan_chkA.
step. step.
eapply (pe_pbreset HIx GA GA_pres (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo _ md A B ts0 cb nb pj sv errv);
[exact STC | exact INV0 | rewrite unsigned_lit by lia; reflexivity |].
intros m2 a1' a2' a3' a4' INV2 PBK2 _.
cbn [pf_spf] in *. unfold A_TP in *.
clear TOK SLOTS SHT MI WM INV0 INtk INq.
reopen_std INV2 ts0 ts0 (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 tk mxd depth l Hl bse Hbse m2.
lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) => replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
asan_rechkA.
step.
step.
step. step.
evt_done5.
eapply (pe_memappend_c HIx GA GA_pres MAPP (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m2 md A B ts0 cb nb pj sv errv T);
[exact STC | exact BSL | exact INV2 | exact PBK2 | exact BK | exact Hco | rewrite unsigned_lit by lia; reflexivity |].
intros m3 md3 A3 B3 pbs3 errv3 r w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 F3 fc3 INV3 OUT3 FS3 FRM3.
cbn [pf_spf] in *. unfold A_TP in *.
clear TOK SLOTS SHT MI WM Ld SHQ4 MU HP INV2 PBK2 BK.
set (ts3 := ts_pbs ts0 pbs3) in *.
reopen_std INV3 ts3 ts0 (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 tk mxd depth l Hl bse Hbse m3.
reenterA asegs A4L HIx asegs_wx HP.
destruct OUT3 as [(-> & PBK3 & BK3) | [-> Epbs3]].
- step. step.
if_true.
step.
asan_rechkM 4.
asan_rechkM 2.
step.
norm_sx32.
step.
rewrite (unsigned_lit (Z.of_nat depth)) by lia.
rewrite Z.shiftl_mul_pow2 by lia.
change (2 ^ 5) with 32.
step.
replace (q + Z.of_nat depth * 32) with bse by lia.
clear SHT.
asan_chkA.
step. step.
stepz.

assert (Hl3 : nth_error (t_levels ts3) (t_depth ts3) = Some l) by exact Hl.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m3 mc, WMc : wmono asegs m3 mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, Lc : rw_cells asegs mc bse _ |- _ =>
evt_done5; rewrite Hbse in MUc, Lc;
destruct (PE_INV_A_lvl_write HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m3 mc md3 A3 B3 ts3
cb nb pj sv errv3 l ST_comment_start (tl_ss l) c0 hn0 c0 STC INV3 Hl3 MUc WMc MIc TOKc Lc Hmode
ltac:(rewrite <- Hmode; apply QIsM.Mq2.lvl_mode_ws_same; [rewrite Hst; reflexivity | reflexivity]) ltac:(unfold ST_comment_start; lia) SS26 (or_introl eq_refl)
ltac:(rewrite Hst; reflexivity)) as [INV4 PBK4];
unstash Kbreak; eapply (Kbreak mc md3 A3 B3 pbs3 errv3);
[exact INV4 | exact (PBK4 1 PBK3)
| exact (BOK_lvl_restate _ _ ts3 B3 nB l ST_comment_start (tl_ss l) Hl3 (lvl_closed_keep l ST_comment_start _ _ _ _ _ eq_refl) (BOK_weaken _ _ _ _ _ nB (Nat.le_succ_diag_r nB) BK3))
| exact FS3 | exact FRM3]
end end.
- replace (Z_to_bv 64 (2^64 - 1)) with (Z_to_bv 64 (-1)) by (apply bv_eq; vm_compute; reflexivity).
step. step.
if_false.
step.
step.
asan_rechkA.
step.
evt_done5.
unstash Kerr16. eapply (Kerr16 m3 md3 A3 B3 errv3); [| exact FS3 | exact FRM3].
unfold ts3 in INV3. rewrite Epbs3 in INV3. exact INV3.
Qed.

Lemma eatws_eof_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet)
(gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
t_co ts = pf_len pf ->
(forall m' (e : word) x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' s11' t4' t6',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md A B (ts_set_x ts (t_co ts) (tx_err (t_x ts) e)) cb nb pj sv errv ->
AJ5 A4L HIx A T md
(pe_msO asegs pf pa APE_OUT x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' (Z_to_bv 64 (pf_tk pf + 56)) s11' t4' t6' F fc m')) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa 0x97d24 (pf_len pf - 1) gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (Z.of_nat (t_depth ts))) (Z_to_bv 64 q) (Z_to_bv 64 (pa_F pa + 64)) F fc m).
Proof.
intros until fc. intros STC INV Heof Kout. pose proof INV as INV0.
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
unfold pe_msA, pe_msO in *.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
set (ts0 := TST depth levels len pb pbs (TS isd stpos (Z_to_bv 64 len) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * mxd) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t.
blk_factsA A4L HIx HP q (32 * mxd) Hqal Hqlo Hqhi Himg_q.
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
unfold APE_OUT in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
stash Himg_t. stash Himg_q. clear PB TSK REST LV.
reenterA asegs A4L HIx asegs_wx HP.

lazymatch goal with |- evt _ _ (MS ?R ?FF _ ?fcc None ?mm ?rom) =>
assert (TAILC : forall a0v a1v, evt asegs (AJ5e A4L HIx A T md) (MS (bvmap_set 11 a1v (bvmap_set 10 a0v R)) FF (Z_to_bv 64 0x97d88) fcc None mm rom)) end.
{ intros a0v a1v.
step.
asan_rechkA.
step. step.
stepz.
step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _ |- _ =>
evt_done5;
destruct (PE_INV_A_tokw1 HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m mc md A B ts0
cb nb pj sv errv len (tx_err (t_x ts0) (Z_to_bv 64 1)) STC INV0 MUc WMc MIc TOKc ltac:(cbn [pf_len]; lia) eq_refl) as [INVe _];
eapply (Kout mc (Z_to_bv 64 1)); exact INVe
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
asan_rechkA.
stepz.
step.
step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _ |- _ =>
evt_done5;
destruct (PE_INV_A_tokw1 HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m mc md A B ts0
cb nb pj sv errv len (tx_err (t_x ts0) (Z_to_bv 64 0)) STC INV0 MUc WMc MIc TOKc ltac:(cbn [pf_len]; lia) eq_refl) as [INVe _];
eapply (Kout mc (Z_to_bv 64 0)); exact INVe
end end.
* step.
if_truex. apply (TAILC _ _).
+ step.
if_truex. apply (TAILC _ _).
- if_truex. apply (TAILC _ _).
Qed.

Ltac frameA_now mc :=
unfold pe_frameA, pe_slotsA, pe_savedA_cells, ff_cellsA, ffsh_cells, FSH0; cbn [map pf_tk pf_spf pf_lenr pa_F pa_sp0 pa_oldloc pa_newloc]; unfold shA, A_SB;
split; [| split; [| split; [| split]]];
match goal with H : rw_cells asegs mc ?a _ |- rw_cells asegs mc ?a _ => exact H end.

Lemma eatws_loop_A :
forall (n : nat) (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel) (b : Z)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet)
(gp t0 t1 t2 a3 a5 a6 a7 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> pf_fl pf = 0 ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
PBOKat m ts b ->
CSTR_OK pf payload ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_eatws ->
t_co ts < pf_len pf -> nth_error payload (Z.to_nat (t_co ts)) = Some cb ->
(pf_len pf - t_co ts <= Z.of_nat n) ->

(forall m' co' cb' a1' a3' a4' a5',
t_co ts <= co' < pf_len pf -> nth_error payload (Z.to_nat co') = Some cb' -> is_ws (bv_unsigned cb') = false ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md A B (ts_set_co ts co') cb' nb pj sv errv ->
PBOKat m' (ts_set_co ts co') b ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa 0x94d04 co' gp t0 t1 t2 (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) a1'
(Z_to_bv 64 (q / 8 + 4 * Z.of_nat (t_depth ts) + A_SB)) a3' a4' a5' a6 a7
(Z_to_bv 64 (Z.of_nat (t_depth ts))) (Z_to_bv 64 q) (Z_to_bv 64 (pa_F pa + 64)) F fc m')) ->

(forall m' co' cb' a1' a3' a4' a5',
t_co ts <= co' < pf_len pf -> nth_error payload (Z.to_nat co') = Some cb' -> bv_unsigned cb' = 47 ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md A B (ts_set_co ts co') cb' nb pj sv errv ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa 0x96e40 co' gp t0 t1 t2 (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) a1'
(Z_to_bv 64 (q / 8 + 4 * Z.of_nat (t_depth ts) + A_SB)) a3' a4' a5' a6 a7
(Z_to_bv 64 (Z.of_nat (t_depth ts))) (Z_to_bv 64 (pf_tk pf + 56)) (Z_to_bv 64 (pa_F pa + 64)) F fc m')) ->

(forall m' cb' a1' a3' a4' a5',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md A B (ts_set_co ts (pf_len pf)) cb' nb pj sv errv ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa 0x97d24 (pf_len pf - 1) gp t0 t1 t2 (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) a1'
(Z_to_bv 64 (q / 8 + 4 * Z.of_nat (t_depth ts) + A_SB)) a3' a4' a5' a6 a7
(Z_to_bv 64 (Z.of_nat (t_depth ts))) (Z_to_bv 64 q) (Z_to_bv 64 (pa_F pa + 64)) F fc m')) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa 0x9411c (t_co ts) gp t0 t1 t2 (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) (Z_to_bv 64 (pf_sb pf + t_co ts + 1))
(Z_to_bv 64 (q / 8 + 4 * Z.of_nat (t_depth ts) + A_SB)) a3 (Z_to_bv 64 (bv_unsigned cb)) a5 a6 a7
(Z_to_bv 64 (Z.of_nat (t_depth ts))) (Z_to_bv 64 q) (Z_to_bv 64 (pa_F pa + 64)) F fc m).
Proof.
induction n as [|n IH]; intros until fc; intros STC FL0 INV PBK CSTR Hl Hst Hco Hc Hn Kpop Ksl Keof.
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
unfold ts_set_co in Kpop, Ksl, Keof.
cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in Kpop, Ksl, Keof.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
pose proof FR as FR0. unfold pe_frameA in FR. destruct FR as (SLOTS & GAP & SAVED & FF & FSH). unfold pe_msA in *.
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
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8, A_SB in *.
pose proof (munch_refl [(tk, tk + 72); (Ff + 64, Ff + 65)] m) as MU.
assert (HW : Forall (pe_wtfA (PEF tk oldl newl len lenr sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl)) [(tk, tk + 72); (Ff + 64, Ff + 65)]).
{ apply Forall_cons; [left; cbn [fst snd pf_tk]; lia |]. apply Forall_cons; [| apply Forall_nil]. right; right; left. cbn [fst snd pa_F]. lia. }
clear LV OBJ HPR.
stash PB. stash TSK.
reenterA asegs A4L HIx asegs_wx HP.
step.
rewrite (unsigned_lit (bv_unsigned cb)) by lia. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. change (2 ^ 8) with 256. rewrite (Z.mod_small (bv_unsigned cb) 256) by lia.
step. step.
destruct (Z_lt_dec 47 (bv_unsigned cb)) as [GT | LE].
{ if_truex. evt_done5.
eapply (Kpop m co cb); [lia | exact Hc | | exact INV0 | exact PBK].
unfold is_ws. rewrite !(proj2 (Z.eqb_neq _ _)) by lia. reflexivity. }
if_falsex.

step. step. norm_w32. step. step. step. rewrite (ws_word cb) by lia.
destruct (is_ws (bv_unsigned cb)) eqn:WS.
2:{
step. if_true. step. step.
destruct (Z.eq_dec (bv_unsigned cb) 47) as [E47 | N47].
- if_falsex.
asan_rechkA.
pose proof (tok_flags_byteA mxd 0 m tk pb (Z.of_nat depth) q (TS isd stpos (Z_to_bv 64 co) err ucs high quote) TOK) as RDF.
step.
rewrite ?zxb_zero. clear RDF.
step. step.
step.
if_false.
step.
evt_done5.
eapply (Ksl m co cb); [lia | exact Hc | exact E47 | exact INV0].
- if_truex. evt_done5.
eapply (Kpop m co cb); [lia | exact Hc | exact WS | exact INV0 | exact PBK]. }

step.
if_false.
assert (Hnz : bv_unsigned cb <> 0) by (intros E0; rewrite E0 in WS; discriminate WS).
destruct (peek_cases (PEF tk oldl newl len lenr sb spf pmd mxd 0) payload co cb LENR CSTR (proj1 RR) ltac:(cbn [pf_len pf_mxd]; lia) ltac:(cbn [pf_len pf_mxd]; lia) Hc Hnz)
as [[Elenr Heof] | [Hne Hmore]]; cbn [pf_len pf_lenr pf_mxd] in *.
{
subst lenr.
asan_rechkA.
step.
norm_sx32.
step.
norm_w32.
step.
step.
rewrite Heof. if_false. step.
replace (sb + co) with (sb + (len - 1)) by lia.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _ |- _ =>
assert (FRc : pe_frameA asegs mc (PEF tk oldl newl len len sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) cb nb pj sv) by (frameA_now mc);
evt_done5;
destruct (PE_INV_A_tokw HIx GA GA_outside (PEF tk oldl newl len len sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m mc md A B ts0
cb nb pj sv errv _ (co + 1) (TS isd stpos (Z_to_bv 64 (co + 1)) err ucs high quote) cb nb STC INV0 MUc WMc MIc HW TOKc FRc
ltac:(cbn [pf_len]; lia) eq_refl) as [INV1 _];
rewrite Heof in INV1; eapply (Keof mc cb); exact INV1
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

stash Hv. stash SLOTS. stash GAP. stash SAVED. stash FSH. stash DSt. stash DSF. stash SHPF.
stash IH. stash Kpop. stash Ksl. stash Keof. stash INV0. stash REST. stash FR0. stash PBK. stash SBc. stash SBhi. stash LE1. stash Hc'. stash Hc. stash STR. stash HW.
asan_rechkA.
step.
norm_sx32.
step.
norm_w32.
step.
stash DFt. stash DSPt. clear SEP4c SEP4t SEP4i SEP8c SEP8t SEP8i SHT4.
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
assert (JOIN : forall a4x a5x, evt asegs (AJ5e A4L HIx A T md) (MS (bvmap_set 14 a4x (bvmap_set 15 a5x R)) FF (Z_to_bv 64 0x941b8) fcc None mm rom)) end.
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
step.
unstash REST. unstash HW. unstash INV0. unstash FR0. unstash PBK.
replace (sb + co + 2) with (sb + (co + 1) + 1) by lia. replace (sb + co + 1) with (sb + (co + 1)) by lia.
unstash Kpop. unstash Ksl. unstash Keof. unstash IH.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, FFc : rw_cells asegs mc Ff _ |- _ =>
assert (FRc : pe_frameA asegs mc (PEF tk oldl newl len lenr sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) c' nb pj sv)
by (eapply (pe_frameA_scan HIx) with (ts := ts0); [exact STC | exact (proj1 REST) | exact FR0 | exact MUc | exact WMc | exact FFc]);
evt_done5;
destruct (PE_INV_A_tokw HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m mc md A B ts0
cb nb pj sv errv _ (co + 1) (TS isd stpos (Z_to_bv 64 (co + 1)) err ucs high quote) c' nb STC INV0 MUc WMc MIc HW TOKc FRc
ltac:(cbn [pf_len]; lia) eq_refl) as [INV1 PBK1];
eapply (IH (PEF tk oldl newl len lenr sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo mc md A B
(TST depth levels (co + 1) pb pbs (TS isd stpos (Z_to_bv 64 (co + 1)) err ucs high quote) obj objs objbs) l b c' nb pj sv errv T);
[ exact STC | reflexivity | exact INV1 | exact (PBK1 b PBK) | exact CSTR | exact Hl | exact Hst
| cbn [t_co pf_len]; lia | exact Hc' | cbn [t_co pf_len]; lia
| cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_sb pf_len pf_tk pf_lenr pa_F ts_set_co];
intros; eapply Kpop; [cbn [pf_len] in *; lia | eassumption | assumption | eassumption | eassumption]
| cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_sb pf_len pf_tk pf_lenr pa_F ts_set_co];
intros; eapply Ksl; [cbn [pf_len] in *; lia | eassumption | assumption | eassumption]
| cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_sb pf_len pf_tk pf_lenr pa_F ts_set_co];
intros; eapply Keof; eassumption ]
end end.
Qed.

Lemma seg_eatws_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP : Z) (nB : nat)
(gp t0 t1 t2 a3 a5 a6 a7 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa -> pf_fl pf = 0 ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv -> PBOK m ts kP -> BOK pf pa ts B (S nB) ->
CSTR_OK pf payload ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_eatws ->
t_co ts < pf_len pf -> nth_error payload (Z.to_nat (t_co ts)) = Some cb ->

(forall m' co' cb' a0' a1' a2' a3' a4' a5',
t_co ts <= co' < pf_len pf -> nth_error payload (Z.to_nat co') = Some cb' -> is_ws (bv_unsigned cb') = false ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md A B
(ts_lvl (ts_set_co ts co') (TL (tl_ss l) (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) cb' nb pj sv errv ->
PBOK m' (ts_lvl (ts_set_co ts co') (TL (tl_ss l) (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) kP ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa APE_REDO co' gp t0 t1 t2 a0' a1' a2' a3' a4' a5' a6 a7
(Z_to_bv 64 (Z.of_nat (t_depth ts))) (Z_to_bv 64 (pf_tk pf + 56)) (Z_to_bv 64 (pa_F pa + 64)) F fc m')) ->

(forall m' md' A' B' pbs' errv' co' cb' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' F' fc',
t_co ts <= co' < pf_len pf -> nth_error payload (Z.to_nat co') = Some cb' -> bv_unsigned cb' = 47 ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B'
(ts_pbs (ts_lvl (ts_set_co ts co') (TL ST_comment_start (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) pbs') cb' nb pj sv errv' ->
PBOK m' (ts_pbs (ts_lvl (ts_set_co ts co') (TL ST_comment_start (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) pbs') 1 ->
BOK pf pa (ts_pbs (ts_lvl (ts_set_co ts co') (TL ST_comment_start (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) pbs') B' nB ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msA asegs pf pa APE_BREAK co' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5'
(Z_to_bv 64 (pf_tk pf + 56)) (Z_to_bv 64 (pa_F pa + 64)) F' fc' m')) ->

(forall m' md' A' B' errv' co' cb' x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s5' t3' t4' t5' t6' F' fc',
t_co ts <= co' < pf_len pf ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' (ts_set_co ts co') cb' nb pj sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(Q1Y6.Mq2.pe_msE pf pa APE_ERR2 x1' gp' t0' t1' t2' (Z_to_bv 64 16) a1' a2' a3' a4' a5' a6' a7'
(Z_to_bv 64 (pf_tk pf / 8 + SB2)) (Z_to_bv 64 (pf_tk pf + 20)) s5' (Z_to_bv 64 (pf_tk pf + 36)) (Z_to_bv 64 (pf_tk pf + 32)) (Z_to_bv 64 (pa_F pa))
(Z_to_bv 64 (pf_tk pf + 56)) (Z_to_bv 64 (pf_sb pf + co')) t3' t4' t5' t6' F' fc' m')) ->

(forall m' (e : word) cb' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' s11' t4' t6',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md A B
(ts_set_x ts (pf_len pf) (TS (ts_isd (t_x ts)) (ts_stpos (t_x ts)) (Z_to_bv 64 (pf_len pf)) e (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))) cb' nb pj sv errv ->
AJ5 A4L HIx A T md
(pe_msO asegs pf pa APE_OUT x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' (Z_to_bv 64 (pf_tk pf + 56)) s11' t4' t6' F fc m')) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa (pe_jtA ST_eatws) (t_co ts) gp t0 t1 t2
(Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) (Z_to_bv 64 (tl_st l))
(Z_to_bv 64 (q / 8 + 4 * Z.of_nat (t_depth ts) + A_SB)) a3 (Z_to_bv 64 APE_JTAB) a5 a6 a7
(Z_to_bv 64 (Z.of_nat (t_depth ts))) (Z_to_bv 64 q) (Z_to_bv 64 (pa_F pa + 64)) F fc m).
Proof.
intros until fc. intros STC BSL FL0 INV PBK BK CSTR Hl Hst Hco Hc Kredo Kbreak Kerr16 Kout. pose proof INV as INV0.
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR).
destruct INV as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof (proj1 REST) as HP.
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
unfold pe_frameA in FR. destruct FR as (SLOTS & _ & _ & FF & _).
unfold pe_slotsA in SLOTS. cbn zeta in SLOTS. unfold ff_cellsA in FF.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in SLOTS, FF.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
pose proof (bv_unsigned_in_range 8 cb) as CBR; unfold bv_modulus in CBR; cbn in CBR.
unfold pe_msA. cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pa_sp0 pa_F]. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
clear PB TSK REST TOK.
reenterA asegs A4L HIx asegs_wx HP. rewrite Hst. unfold ST_eatws. cbn [pe_jtA].
step.
change (zxb cb) with (Z_to_bv 64 (bv_unsigned cb)).
step.
step.
evt_done5.
eapply (eatws_loop_A (Z.to_nat (len - co)) (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m md A B ts0 l (co + kP)
cb nb pj sv errv T);
[exact STC | exact FL0 | exact INV0 | exact PBK | exact CSTR | exact Hl | exact Hst | exact Hco | exact Hc | cbn [pf_len t_co ts0]; lia | | |].
-
intros m' co' cb' a1' a3' a4' a5' Hr Hc' Hws INV' PBK'.
eapply (eatws_pop_A (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m' md A B (ts_set_co ts0 co') l cb' nb pj sv errv T kP);
[exact STC | exact INV' | unfold PBOK; eapply PBOKat_weaken; [| exact PBK']; cbn [t_co ts_set_co ts0] in *; lia | exact Hl | exact Hst |].
intros m'' a0'' a1'' a2'' a3'' INV'' PBK''. eapply (Kredo m'' co' cb'); [exact Hr | exact Hc' | exact Hws | exact INV'' | exact PBK''].
-
intros m' co' cb' a1' a3' a4' a5' Hr Hc' H47 INV'.
eapply (eatws_slash_A (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m' md A B (ts_set_co ts0 co') l cb' nb pj sv errv T nB);
[exact STC | exact BSL | exact INV' | exact (BOK_set_co _ _ ts0 B (S nB) co' ltac:(cbn [t_co ts0] in *; lia) BK) | exact Hl | exact Hst | cbn [t_co ts_set_co pf_len] in *; lia | |].
+ intros until fc'. intros INV'' PBK'' BK'' FS'' FRM''. eapply (Kbreak _ _ _ _ _ _ co' cb'); [exact Hr | exact Hc' | exact H47 | exact INV'' | exact PBK'' | exact BK'' | exact FS'' | exact FRM''].
+ intros until fc'. intros INV'' FS'' FRM''. eapply (Kerr16 _ _ _ _ _ co' cb'); [exact Hr | exact INV'' | exact FS'' | exact FRM''].
-
intros m' cb' a1' a3' a4' a5' INV'.
eapply (eatws_eof_A (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m' md A B (ts_set_co ts0 len) cb' nb pj sv errv T);
[exact STC | exact INV' | reflexivity |].
intros m'' e. intros. eapply (Kout m'' e cb'). eassumption.
Qed.
End PeSEatwsA.
End RC__1.
