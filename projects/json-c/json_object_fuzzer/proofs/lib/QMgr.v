(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup Lib.GwApply QWxq_c1 QRjH QHnV QCcH QfLs Q0Ek Qtgi QjDH Qsw7 QJjn QRUw QPZI QkMG QG8z QIsM Q7UD Qhd4 Qwm6 QlKV QsKa Qiiq Q4v2 QugP Q1Ey Ql4f QrQv QEUF QW22 QdGy Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QJjn QRUw.Mq0 QRUw QRUw.Mq2. Import QPZI.Mq4. Import QkMG. Import QG8z QIsM.Mq2.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa QsKa.Mq4 Qiiq.Mq0 QsKa.Mq6 Q4v2.Mq0 QugP.Mq1 QlKV.Mq5 Q1Ey Ql4f.Mq1 QsKa.Mq8 QrQv.Mq2 QEUF QW22.Mq3 QdGy.Mq2.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section PeSCallKA.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_pres : forall LB SP m m', heap_pres A4H LB SP m m' -> GA m -> GA m'.
Hypothesis MAPP : memappend_A_stmt2 HIx.

Lemma pe_memappend_pk :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (co0 k0 xn : Z)
(ra gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
PBOKat m ts (co0 + k0) -> k0 <= 0 -> 0 <= co0 -> 0 <= xn -> co0 + xn <= t_co ts + 1 -> co0 + xn <= pf_len pf -> 0 < pf_len pf ->
forall kB : nat, BOK pf pa ts B kB -> bv_unsigned ra mod 2 = 0 ->
(forall m2 md2 A2 B2 pbs2 errv2 r (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : word) F2 fc2,
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m2 md2 A2 B2 (ts_pbs ts pbs2) cb nb pj sv errv2 ->
(r = xn /\ PBOKat m2 (ts_pbs ts pbs2) (co0 + k0 + xn) /\ BOK pf pa (ts_pbs ts pbs2) B2 kB) \/ (r = 2^64 - 1 /\ pbs2 = t_pbs ts) ->
fsaved F F2 -> (frm0 fc -> frm0 fc2) ->
AJ5 A4L HIx A2 T md2
(MS (mkR ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) w0 w1 w2 s0 s1 (Z_to_bv 64 r) w3 w4 w5 w6 w7 w8 w9
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 w10 w11 w12 w13) F2 (ret_pc ra) fc2 None m2 (seg_rom asegs))) ->
AJ5 A4L HIx A T md
(MS (mkR ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2 s0 s1 (Z_to_bv 64 (t_pb ts)) (Z_to_bv 64 (pf_sb pf + co0)) (Z_to_bv 64 xn) a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x9a0ac) fc None m (seg_rom asegs)).
Proof.
intros until fc. intros STC BSL INV PBK K0 Hco0 Hxn Hle1 Hle2 Hlen0 kB BK RA K.
pose proof STC as (_ & _ & _ & _ & _ & LEN & SB0 & _).
pose proof INV as [(_ & _ & CO & _) REST]. pose proof REST as (HP & _ & _ & _ & _ & STR & PLEN & SBin & _).
destruct SBin as [L0 | PL]; [exfalso; lia|].
pose proof (bytes_at_sub A4H m (pf_sb pf) payload (Z.to_nat co0) (Z.to_nat xn) STR ltac:(lia)) as SRC. cbn [hl_segs hla_base A4L A4H] in SRC. rewrite Z2Nat.id in SRC by lia.
eapply (pe_memappend_g HIx GA GA_pres MAPP pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv T (pf_sb pf + co0) xn (co0 + k0) (firstn (Z.to_nat xn) (skipn (Z.to_nat co0) payload)));
[exact STC | exact BSL | exact INV | exact PBK | lia | lia | exact BK | exact RA | exact SRC
| rewrite length_firstn, length_skipn; lia | lia | | | exact K].
- destruct PL as [([b0 n0] & Hb & Hb1 & Hb2) | (Fh & kh & HFh & HF1 & HF2 & _)]; cbn [blk_addr blk_size fst snd] in *.
+ left. exists b0, n0. split; [apply in_or_app; right; right; right; exact Hb | lia].
+ right. first [left | idtac]. exists Fh, kh. split; [right; exact HFh | lia].
- intros Hn0. destruct PL as [([b0 n0] & Hb & Hb1 & Hb2) | (Fh & kh & HFh & HF1 & HF2 & UPS)]; cbn [blk_addr blk_size fst snd] in *.
+ eapply (unpoisoned_of_blk HIx); [exact HP | unfold pe_blocksA; apply in_or_app; right; right; right; exact Hb | lia | lia | exact Hn0].
+ eapply unpoisoned_sub2; [exact UPS | lia | lia | exact Hn0].
Qed.
End PeSCallKA.
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

Section PeSNeeduA.
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

Lemma seg_needu_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP : Z) (nB : nat)
(gp t0 t1 t2 a3 a5 a6 a7 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv -> PBOK m ts kP -> kP + 3 <= 1 -> BOK pf pa ts B (S nB) ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_esc_need_u ->
t_co ts < pf_len pf ->
bytes_at asegs me UTF8REP_ADDR_A Qa8x.Mq3.utf8rep ->

(forall m' a1' a2' a3',
bv_unsigned cb = 117 ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md A B
(ts_lvl ts (TL ST_escape_unicode (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) cb nb pj sv errv ->
PBOK m' (ts_lvl ts (TL ST_escape_unicode (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) kP ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa APE_ADV (t_co ts) gp t0 t1 t2 (Z_to_bv 64 125) a1' a2' a3' (Z_to_bv 64 APE_JTAB) a5 a6 a7
(Z_to_bv 64 (Z.of_nat (t_depth ts))) (Z_to_bv 64 (pf_tk pf + 56)) (Z_to_bv 64 (pa_F pa + 64)) F fc m')) ->

(forall m' md' A' B' pbs' errv' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' F' fc',
bv_unsigned cb <> 117 ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B'
(ts_lvl (ts_set_x (ts_pbs ts pbs') (t_co ts) (TS (ts_isd (t_x ts)) (Z_to_bv 64 0) (ts_choff (t_x ts)) (ts_err (t_x ts)) (Z_to_bv 64 0) (Z_to_bv 64 0) (ts_quote (t_x ts))))
(TL ST_string_escape (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) cb nb pj sv errv' ->
PBOK m' (ts_lvl (ts_set_x (ts_pbs ts pbs') (t_co ts) (TS (ts_isd (t_x ts)) (Z_to_bv 64 0) (ts_choff (t_x ts)) (ts_err (t_x ts)) (Z_to_bv 64 0) (Z_to_bv 64 0) (ts_quote (t_x ts))))
(TL ST_string_escape (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) (kP + 3) ->
BOK pf pa (ts_lvl (ts_set_x (ts_pbs ts pbs') (t_co ts) (TS (ts_isd (t_x ts)) (Z_to_bv 64 0) (ts_choff (t_x ts)) (ts_err (t_x ts)) (Z_to_bv 64 0) (Z_to_bv 64 0) (ts_quote (t_x ts))))
(TL ST_string_escape (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) B' nB ->
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
(pe_msA asegs pf pa (pe_jtA ST_esc_need_u) (t_co ts) gp t0 t1 t2
(Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) (Z_to_bv 64 (tl_st l))
(Z_to_bv 64 (q / 8 + 4 * Z.of_nat (t_depth ts) + A_SB)) a3 (Z_to_bv 64 APE_JTAB) a5 a6 a7
(Z_to_bv 64 (Z.of_nat (t_depth ts))) (Z_to_bv 64 q) (Z_to_bv 64 (pa_F pa + 64)) F fc m).
Proof.
intros until fc. intros STC BSL INV PBK HkP BK Hl Hst Hco UTF Kadv Kredo Kerr16. pose proof INV as INV0. pe_openA STC INV.
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
reenterA asegs A4L HIx asegs_wx HP. rewrite Hst. unfold ST_esc_need_u. cbn [pe_jtA].
replace (q + 32 * Z.of_nat depth) with bse by lia.
step.
change (zxb cb) with (Z_to_bv 64 (bv_unsigned cb)).
step.
destruct (Z.eq_dec (bv_unsigned cb) 117) as [C92 | N92].
- clear SRC FF SHT.
step.
if_falsex.
step.
asan_rechkA.
step.
step.
stepz.
step.
step. step.
asan_rechkA.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, Lc : rw_cells asegs mc bse _ |- _ =>
evt_done5; rewrite Hbse in MUc, Lc;
destruct (PE_INV_A_lvl_write HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m mc md A B ts0
cb nb pj sv errv l ST_escape_unicode (tl_ss l) c0 hn0 c0 STC INV0 Hl MUc WMc MIc TOKc Lc Hmode
ltac:(rewrite <- Hmode; apply Qa8x.Mq3.lvl_mode_esc_same; [rewrite Hst; reflexivity | reflexivity | exact SS26]) ltac:(unfold ST_escape_unicode; lia) SS26 (or_introl eq_refl)
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
asan_chkA.
step.
stepz.
step.

assert (Hl3 : nth_error (t_levels ts3) (t_depth ts3) = Some l) by exact Hl.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mcF _) =>
lazymatch goal with MUc : munch _ ?mb mcF, WMc : wmono asegs ?mb mcF, MIc : mem_inv asegs mcF, TOKc : rw_cells asegs mcF tk _, Lc : rw_cells asegs mcF bse _ |- _ =>
evt_done5; rewrite Hbse in MUc, Lc;
destruct (PE_INV_A_lvl_write HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo mb mcF md2 A2 B2 ts3
cb nb pj sv errv2 l ST_string_escape (tl_ss l) c0 hn0 c0 STC INV3 Hl3 MUc WMc MIc TOKc Lc Hmode
ltac:(rewrite <- Hmode; apply Qa8x.Mq3.lvl_mode_esc_same; [rewrite Hst; reflexivity | reflexivity | exact SS26]) ltac:(unfold ST_string_escape; lia) SS26 (or_introl eq_refl)
ltac:(rewrite Hst; reflexivity)) as [INV4 PBK4];
unstash Kredo; eapply (Kredo mcF md2 A2 B2 pbs2 errv2 _ _ _ _ _ _ _ _ _ _ _ _ _ F2 fc2 N92);
[ exact INV4
| apply PBK4; unfold PBOK; cbn [t_co ts3 ts_set_x]; apply PBT3; replace (co + (kP + 3)) with (co + kP + 3) by lia; exact PBK2
| exact (BOK_lvl_restate _ _ ts3 B2 nB l ST_string_escape (tl_ss l) Hl3 (lvl_closed_keep l ST_string_escape _ _ _ _ _ eq_refl)
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
End PeSNeeduA.
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
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqj QsKa.Mqd Qiiq QsKa.Mqf Q4v2 QugP QlKV.Mqf QSHS Ql4f.Mq4 QsKa.Mqh QrQv.Mq4 QEUF.Mq2 QW22.Mq8 QdGy.Mq9.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section PeSCallKA.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_pres : forall LB SP m m', heap_pres A4H LB SP m m' -> GA m -> GA m'.
Hypothesis MAPP : memappend_A_stmt2 HIx.

Lemma pe_memappend_pk :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (co0 k0 xn : Z)
(ra gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
PBOKat m ts (co0 + k0) -> k0 <= 0 -> 0 <= co0 -> 0 <= xn -> co0 + xn <= t_co ts + 1 -> co0 + xn <= pf_len pf -> 0 < pf_len pf ->
forall kB : nat, BOK pf pa ts B kB -> bv_unsigned ra mod 2 = 0 ->
(forall m2 md2 A2 B2 pbs2 errv2 r (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : word) F2 fc2,
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m2 md2 A2 B2 (ts_pbs ts pbs2) cb nb pj sv errv2 ->
(r = xn /\ PBOKat m2 (ts_pbs ts pbs2) (co0 + k0 + xn) /\ BOK pf pa (ts_pbs ts pbs2) B2 kB) \/ (r = 2^64 - 1 /\ pbs2 = t_pbs ts) ->
fsaved F F2 -> (frm0 fc -> frm0 fc2) ->
AJ5 A4L HIx A2 T md2
(MS (mkR ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) w0 w1 w2 s0 s1 (Z_to_bv 64 r) w3 w4 w5 w6 w7 w8 w9
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 w10 w11 w12 w13) F2 (ret_pc ra) fc2 None m2 (seg_rom asegs))) ->
AJ5 A4L HIx A T md
(MS (mkR ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2 s0 s1 (Z_to_bv 64 (t_pb ts)) (Z_to_bv 64 (pf_sb pf + co0)) (Z_to_bv 64 xn) a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x9b4fc) fc None m (seg_rom asegs)).
Proof.
intros until fc. intros STC BSL INV PBK K0 Hco0 Hxn Hle1 Hle2 Hlen0 kB BK RA K.
pose proof STC as (_ & _ & _ & _ & _ & LEN & SB0 & _).
pose proof INV as [(_ & _ & CO & _) REST]. pose proof REST as (HP & _ & _ & _ & _ & STR & PLEN & SBin & _).
destruct SBin as [L0 | PL]; [exfalso; lia|].
pose proof (bytes_at_sub A4H m (pf_sb pf) payload (Z.to_nat co0) (Z.to_nat xn) STR ltac:(lia)) as SRC. cbn [hl_segs hla_base A4L A4H] in SRC. rewrite Z2Nat.id in SRC by lia.
eapply (pe_memappend_g HIx GA GA_pres MAPP pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv T (pf_sb pf + co0) xn (co0 + k0) (firstn (Z.to_nat xn) (skipn (Z.to_nat co0) payload)));
[exact STC | exact BSL | exact INV | exact PBK | lia | lia | exact BK | exact RA | exact SRC
| rewrite length_firstn, length_skipn; lia | lia | | | exact K].
- destruct PL as [([b0 n0] & Hb & Hb1 & Hb2) | (Fh & kh & HFh & HF1 & HF2 & _)]; cbn [blk_addr blk_size fst snd] in *.
+ left. exists b0, n0. split; [apply in_or_app; right; right; right; exact Hb | lia].
+ right. first [left | idtac]. exists Fh, kh. split; [right; exact HFh | lia].
- intros Hn0. destruct PL as [([b0 n0] & Hb & Hb1 & Hb2) | (Fh & kh & HFh & HF1 & HF2 & UPS)]; cbn [blk_addr blk_size fst snd] in *.
+ eapply (unpoisoned_of_blk HIx); [exact HP | unfold pe_blocksA; apply in_or_app; right; right; right; exact Hb | lia | lia | exact Hn0].
+ eapply unpoisoned_sub2; [exact UPS | lia | lia | exact Hn0].
Qed.
End PeSCallKA.
End RC__1.
End Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QgoP Qw5U.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QJjn QRUw.Mq0 QRUw QkMG. Import QG8z.
Import QgoP.
Import QbFI. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqj QsKa.Mq9 QsKa.Mqd Qiiq QsKa.Mqf Q4v2 QSHS Ql4f.Mq4 Q1Y6.Mq4 QsKa.Mqh QrQv.Mq4 QEUF.Mq2 QdGy.Mq9 Qw5U.Mq7.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition APE_ERRLIT : Z := 0x98434.

Section PeSLitA.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_pres : forall LB SP m m', heap_pres A4H LB SP m m' -> GA m -> GA m'.

Lemma blk_granA : forall A LB LM FR B m md a n i,
HEAPA A4L HIx A LB LM FR B m md -> In (a, n) LB -> 0 <= i -> 8 * i + 8 <= n ->
ro_cells asegs m (a / 8 + i + A_SB) [C1 (Z_to_bv 8 0)].
Proof.
intros A LB LM FR B m md a n i HP Hin Hi Hn.
pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ _ _ HP Hin) as SH. unfold shad in SH. cbn [hl_sb A4L] in SH.
pose proof (shadow_granule0 asegs m (a / 8 + A_SB) n i Hi Hn SH) as G.
replace (a / 8 + A_SB + i) with (a / 8 + i + A_SB) in G by lia. exact G.
Qed.

Lemma PE_INV_A_stackw : forall pf pa q LB0 LM FRS payload me lo m m2 md A B ts cb nb pj sv errv,
PE_STATIC_A HIx pf pa lo ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
munch [(lo, pf_spf pf)] m m2 -> wmono asegs m m2 -> mem_inv asegs m2 -> stk asegs m2 lo (pf_spf pf) ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m2 md A B ts cb nb pj sv errv
/\ agree_on asegs (pe_blocksA pf q LB0 ts) m m2.
Proof.
intros until errv. intros STC INV MU WM MI2 ST2.
destruct ts as [depth levels co pbx pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs] in *.
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
pose proof INV as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof REST as (HP & LV & OBJ & ST & ERR & STR & PLEN & SBin & HPR & MDV & G & BUD).
cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs] in *.
set (ts := TST depth levels co pbx pbs x obj objs objbs) in *.
set (RB := pe_blocksA pf q LB0 ts) in *.
pose proof alloc_ceiling_range as ACR.
assert (HPRc : heap_pres A4H (RB ++ LM ++ fr_ivs A4L ((pa_F pa, 2) :: FRS)) (pf_spf pf) m m2).
{ eapply (heap_pres_of_munch A4H); [exact MU | exact WM |].
eapply (client_outsideF HIx); [exact HP | | lia |].
- intros b Hb. rewrite app_assoc in Hb. apply in_app_or in Hb as [Hb | Hb]; [left; exact Hb | right; exact Hb].
- apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_nil]. }
assert (HP2 : HEAPA A4L HIx A RB LM ((pa_F pa, 2) :: FRS) B m2 md).
{ eapply (heapA_client_frame A4L HIx); [exact HP | | exact WM | exact MI2]. eapply (frame_writes_okF A4L HIx); [exact HP | exact MU |].
apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_nil]. }
assert (INq2 : In (q, 32 * pf_mxd pf) RB) by (unfold RB, pe_blocksA; apply in_or_app; right; right; left; reflexivity).
assert (INtk2 : In (pf_tk pf, 72) RB) by (unfold RB, pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (AG : agree_on asegs RB m m2) by (eapply (agree_of_heap_pres asegs A4H); [exact HPRc | reflexivity | intros b Hb; apply in_or_app; left; exact Hb]).
assert (FR2 : pe_frameA asegs m2 pf pa cb nb pj sv).
{ eapply pe_frameA_pres; [exact HPRc | lia | exact GEO | | | exact FR].
- apply in_or_app; right. apply in_or_app; right. change 248 with (fr_size 2 - 8). apply fr_ivs_frame. left; reflexivity.
- apply in_or_app; right. apply in_or_app; right. rewrite <- fr_shadow_len_2. change (shA (pa_F pa)) with (shad A4L (pa_F pa)). apply fr_ivs_shadow. left; reflexivity. }
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPRc) in TOK; [| eapply client_range_block; [apply in_or_app; left; exact INtk2 | lia | unfold tok_cells_g; cbn; lia]]. cbn [hl_segs hla_base A4L A4H] in TOK.
apply (tstack_pres_g A4H _ _ _ _ _ _ HPRc (in_or_app _ _ _ (or_introl INq2))) in TSK; [| exact LEN32]. cbn [hl_segs hla_base A4L A4H] in TSK.
assert (ERR2 : rw_cells asegs m2 A_ERRNO [C4 errv]).
{ eapply rw_cells_transport; [exact ERR | exact MU | exact WM |]. cbn [cells_size csize Z.of_nat disjoint_from fst snd]. unfold A_ERRNO, A_TP. repeat split; try lia. }
assert (REST2 : PE_REST_A HIx GA pf pa q LB0 LM FRS payload me lo m2 md A B ts errv).
{ eapply (PE_REST_A_call_pb HIx GA GA_pres) with (ts := ts) (LBc := RB) (co2 := co) (pb2 := pbx) (pbs2 := pbs) (x2 := x);
[exact STC | exact REST | apply model_vm_only_refl | exact HPRc | | exact HP2 | exact ST2 | exact ERR2 | exact BUD].
unfold RB, pe_blocksA, tstate_blocks, ts; cbn [t_pbs t_objbs t_levels]. intros b Hb. apply in_app_or in Hb as [Hb | Hb].
- apply in_or_app; left. apply in_or_app; right. apply in_or_app; left. exact Hb.
- apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; apply in_or_app; right; apply in_or_app; right; exact Hb | apply in_or_app; right; right; right; exact Hb]. }
split; [| exact AG].
split; [| exact REST2]. unfold PE_CORE_A, ts; cbn [t_levels t_depth t_co t_x t_pb t_pbs]. split; [exact LEN32|]. split; [exact D32|]. split; [exact CO|]. split; [exact CHOFF|].
split; [exact TOK|]. split; [| split; [exact Hpb | split; [exact TSK | exact FR2]]].
eapply (pbuf_agree asegs); [exact PB | exact AG |]. unfold RB, pe_blocksA, tstate_blocks, ts; cbn [t_pbs]. intros b Hb. apply in_or_app; left. apply in_or_app; left. exact Hb.
Qed.

Lemma pe_istrn_c :
forall (entry : Z) (model : list byte -> list byte -> Z -> option (nat * Z)),
istrn_spec_U entry model ->
(forall ls pre post n, exists j v, model (ls ++ [b0]) (pre ++ [Z_to_bv 8 0] ++ post) n = Some (j, v) /\ -300 <= v <= 300) ->
(forall la lb n j v, model la lb n = Some (j, v) -> (j <= Z.to_nat n)%nat /\ (j <= length la)%nat /\ (j <= length lb)%nat /\ (0 < n -> (1 <= j)%nat)) ->
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (Q : machine_state -> Prop)
(xa n buf cap : Z) (ls : list byte)
(ra gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
t_pbs ts = [(t_pb ts, PB_SZ); (buf, cap)] ->
0 < n <= 64 ->
0x10000 <= xa -> xa + Z.of_nat (length ls) + 1 <= 0x3c000 ->
bytes_at asegs m xa (ls ++ [b0]) ->
(forall k', 0 < k' <= n -> k' <= Z.of_nat (length ls) + 1 -> src_globA xa k') ->
bv_unsigned ra mod 2 = 0 ->
(forall m2 (v : Z) (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
-300 <= v <= 300 ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m2 md A B ts cb nb pj sv errv ->
agree_on asegs (pe_blocksA pf q LB0 ts) m m2 ->
evt asegs Q (MS (mkR ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0' t1' t2' s0 s1 (Z_to_bv 64 v) a1' a2' a3' a4' a5' a6' a7'
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m2 (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2 s0 s1 (Z_to_bv 64 xa) (Z_to_bv 64 buf) (Z_to_bv 64 n) a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 entry) fc None m (seg_rom asegs)).
Proof.
intros entry model SPEC TOT NREAD. intros until fc. intros STC INV Epbs Hn Hxa Hxb LIT SRC RA K.
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
pose proof INV as [CORE REST].
destruct CORE as (_ & _ & _ & _ & _ & PB & _ & _ & _).
pose proof REST as (HP & _ & _ & ST & _).
destruct PB as (buf' & bpos & cap' & pre & post & Epbs' & Lpre & CORE1).
rewrite Epbs in Epbs'. injection Epbs' as <- <-.
destruct CORE1 as (Hbp & Hcap & Hlen & _ & BUFC).
pose proof (rw_cells_bytes_at' _ _ _ _ BUFC) as BUFB. cbn [cells_bytes cbytes] in BUFB. rewrite app_nil_r in BUFB.
destruct (TOT ls pre post n) as (k & v & MOD & Hv).
destruct (NREAD _ _ _ _ _ MOD) as (Hk1 & Hk2 & Hk3 & Hk4). specialize (Hk4 ltac:(lia)).
rewrite length_app in Hk2. cbn [length] in Hk2.
assert (INbuf : In (buf, cap) (pe_blocksA pf q LB0 ts)).
{ unfold pe_blocksA, tstate_blocks. rewrite Epbs. apply in_or_app; left. cbn [app]. right; left; reflexivity. }
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ buf cap HP (in_or_app _ LM _ (or_introl INbuf))) as (Hc0 & _ & Hb0 & Hbhi & _).
pose proof alloc_ceiling_range as ACR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
assert (SPF1 : lo <= pf_spf pf - 4096 /\ pf_spf pf mod 16 = 0) by (clear - LOS Gspf; split; [lia | Z.div_mod_to_equations; lia]).
destruct SPF1 as (SPF1 & SPF2).
eapply (SPEC ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2 s0 s1 (Z_to_bv 64 xa) (Z_to_bv 64 buf) (Z_to_bv 64 n) a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m xa buf n lo (ls ++ [b0]) (pre ++ [Z_to_bv 8 0] ++ post) k v Q);
rewrite ?unsigned_lit by lia.
- exact MOD.
- eapply (unpoisoned_of_glob HIx); [exact HP | apply SRC; rewrite ?length_app in *; cbn [length] in *; lia | lia].
- eapply (unpoisoned_of_blk HIx); [exact HP | exact INbuf | lia | lia | lia].
- exact (asan_rt_ok_of_HEAPA HIx _ _ _ _ _ _ _ HP).
- lia.
- rewrite length_app; cbn [length]; lia.
- lia.
- lia.
- left. rewrite length_app; cbn [length]; lia.
- left. lia.
- reflexivity.
- reflexivity.
- reflexivity.
- exact Hn.
- exact LIT.
- exact BUFB.
- exact ST.
- exact LO.
- exact SPF1.
- exact SPF2.
- exact MI.
- exact RA.
- intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 MU WM MI2 _ _ ST2.
destruct (PE_INV_A_stackw pf pa q LB0 LM FRS payload me lo m m2 md A B ts cb nb pj sv errv STC INV MU WM MI2 ST2) as [INV2 AG].
eapply (K m2 v); [exact Hv | exact INV2 | exact AG].
Qed.

Definition pe_istrncmp_c (SPEC : istrncmp_spec_U) := pe_istrn_c A_ISTRNCMP istrncmp_model SPEC istrncmp_total istrncmp_nread.
Definition pe_istrncasecmp_c (SPEC : istrncasecmp_spec_U) := pe_istrn_c A_ISTRNCASECMP istrncasecmp_model SPEC istrncasecmp_total istrncasecmp_nread.

Hypothesis GA_outside : forall m m' W, GA m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= hl_img_lo A4H \/ hl_img_hi A4H <= fst iv) W -> GA m'.

Lemma PE_INV_A_framew : forall pf pa q LB0 LM FRS payload me lo m mc md A B ts cb nb pj sv errv W cb' nb' pj',
PE_STATIC_A HIx pf pa lo ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
munch W m mc -> wmono asegs m mc -> mem_inv asegs mc -> Forall (pe_wtfA pf pa) W ->
rw_cells asegs mc (pf_tk pf) (tok_cells_g (pf_mxd pf) (pf_fl pf) (t_pb ts) (Z.of_nat (t_depth ts)) q (t_x ts)) ->
pe_frameA asegs mc pf pa cb' nb' pj' sv ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo mc md A B ts cb' nb' pj' sv errv
/\ (forall b, PBOKat m ts b -> PBOKat mc ts b).
Proof.
intros pf pa q LB0 LM FRS payload me lo m mc md A B ts cb nb pj sv errv W cb' nb' pj' STC [CORE REST] MU WM MI HW TOKc FRc.
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
split.
- split.
+ unfold PE_CORE_A. split; [exact LEN32|]. split; [exact D32|]. split; [exact CO|]. split; [exact CHOFF|].
split; [exact TOKc|]. split; [| split; [exact Hpb | split; [| exact FRc]]].
* eapply (pbuf_wtfA HIx) with (ts := ts); [exact STC | exact (proj1 REST) | exact PB | exact MU | exact WM | exact HW].
* eapply (tstack_wtfA HIx) with (ts := ts); [exact STC | exact (proj1 REST) | exact TSK | exact LEN32 | exact MU | exact WM | exact HW].
+ eapply (PE_REST_A_private_write HIx GA GA_outside) with (ts := ts); [exact STC | exact REST | exact MU | exact WM | exact MI | apply pe_wtfA_private; exact HW].
- intros b PBK.
eapply PBOKat_agree; [exact PBK | | apply incl_refl].
eapply (agree_wtqA HIx); [exact STC | exact (proj1 REST) | exact MU | exact WM | apply pe_wtfA_wtqA; exact HW |].
intros a n Hin. assert (HinL : In (a, n) (pe_blocksA pf q LB0 ts ++ LM)) by (unfold pe_blocksA, tstate_blocks; apply in_or_app; left; apply in_or_app; left; apply in_or_app; left; exact Hin).
split; [exact HinL|].
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ (proj1 REST)) as ND. unfold pe_blocksA in ND. rewrite <- app_assoc in ND. split.
+ intros ->. refine (nodup_app_ne _ _ _ _ _ _ ND _ _ eq_refl); [unfold tstate_blocks; apply in_or_app; left; exact Hin | left; reflexivity].
+ intros ->. refine (nodup_app_ne _ _ _ _ _ _ ND _ _ eq_refl); [unfold tstate_blocks; apply in_or_app; left; exact Hin | right; left; reflexivity].
Qed.
End PeSLitA.
End RC__1.
End Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc5u QAzu.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

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

Section PeSNeeduA.
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

Lemma seg_needu_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP : Z) (nB : nat)
(gp t0 a5 a7 s3 s6 s7 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv -> PBOK m ts kP -> kP + 3 <= 1 -> BOK pf pa ts B (S nB) ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_esc_need_u ->
t_co ts < pf_len pf ->
bytes_at asegs me UTF8REP_ADDR_A Qa8x.Mq3.utf8rep ->

(forall m' a1' a4',
bv_unsigned cb = 117 ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md A B
(ts_lvl ts (TL ST_escape_unicode (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) cb nb pj sv errv ->
PBOK m' (ts_lvl ts (TL ST_escape_unicode (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) kP ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa APE_BREAK (t_co ts) gp t0 (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) a1' (Z_to_bv 64 0) (Z_to_bv 64 (q / 8 + 4 * Z.of_nat (t_depth ts) + A_SB)) a4' a5 (Z_to_bv 64 APE_JTAB) a7 s3 (Z_to_bv 64 2) s6 s7 (Z_to_bv 64 (Z.of_nat (t_depth ts))) s9 s11 t3 t4 t5 t6 F fc m')) ->

(forall m' md' A' B' pbs' errv' gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc',
bv_unsigned cb <> 117 ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B'
(ts_lvl (ts_set_x (ts_pbs ts pbs') (t_co ts) (TS (ts_isd (t_x ts)) (Z_to_bv 64 0) (ts_choff (t_x ts)) (ts_err (t_x ts)) (Z_to_bv 64 0) (Z_to_bv 64 0) (ts_quote (t_x ts))))
(TL ST_string_escape (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) cb nb pj sv errv' ->
PBOK m' (ts_lvl (ts_set_x (ts_pbs ts pbs') (t_co ts) (TS (ts_isd (t_x ts)) (Z_to_bv 64 0) (ts_choff (t_x ts)) (ts_err (t_x ts)) (Z_to_bv 64 0) (Z_to_bv 64 0) (ts_quote (t_x ts))))
(TL ST_string_escape (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) (kP + 3) ->
BOK pf pa (ts_lvl (ts_set_x (ts_pbs ts pbs') (t_co ts) (TS (ts_isd (t_x ts)) (Z_to_bv 64 0) (ts_choff (t_x ts)) (ts_err (t_x ts)) (Z_to_bv 64 0) (Z_to_bv 64 0) (ts_quote (t_x ts))))
(TL ST_string_escape (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) B' nB ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msA asegs pf pa APE_REDO (t_co ts) gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' m')) ->

(forall m' md' A' B' errv' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' ts cb nb pj sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msO asegs pf pa APE_ERRMEM gp' t0' t1' t2' (Z_to_bv 64 (pf_tk pf + 36)) a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' m')) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa (pe_jtA ST_esc_need_u) (t_co ts) gp t0 (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) (Z_to_bv 64 (tl_st l)) (Z_to_bv 64 0) (Z_to_bv 64 (q / 8 + 4 * Z.of_nat (t_depth ts) + A_SB)) (Z_to_bv 64 0) a5 (Z_to_bv 64 APE_JTAB) a7 s3 (Z_to_bv 64 q) s6 s7 (Z_to_bv 64 (Z.of_nat (t_depth ts))) s9 s11 t3 t4 t5 t6 F fc m).
Proof.
intros until fc. intros STC BSL INV PBK HkP BK Hl Hst Hco UTF Kadv Kredo Kerr16. pose proof INV as INV0. pe_openA STC INV.
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
reenterA asegs A4L HIx asegs_wx HP. rewrite Hst. unfold ST_esc_need_u. cbn [pe_jtA].
replace (q + 32 * Z.of_nat depth) with bse by lia.
step. step.
change (zxb cb) with (Z_to_bv 64 (bv_unsigned cb)).
step.
destruct (Z.eq_dec (bv_unsigned cb) 117) as [C92 | N92].
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
cb nb pj sv errv l ST_escape_unicode (tl_ss l) c0 hn0 c0 STC INV0 Hl MUc WMc MIc TOKc Lc Hmode
ltac:(rewrite <- Hmode; apply Qa8x.Mq3.lvl_mode_esc_same; [rewrite Hst; reflexivity | reflexivity | exact SS26]) ltac:(unfold ST_escape_unicode; lia) SS26 (or_introl eq_refl)
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
asan_chkB.
step. step.
stepz.
step.

assert (Hl3 : nth_error (t_levels ts3) (t_depth ts3) = Some l) by exact Hl.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mcF _) =>
lazymatch goal with MUc : munch _ ?mb mcF, WMc : wmono asegs ?mb mcF, MIc : mem_inv asegs mcF, TOKc : rw_cells asegs mcF tk _, Lc : rw_cells asegs mcF bse _ |- _ =>
evt_done5; rewrite Hbse in MUc, Lc;
destruct (PE_INV_A_lvl_write HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo mb mcF md2 A2 B2 ts3
cb nb pj sv errv2 l ST_string_escape (tl_ss l) c0 hn0 c0 STC INV3 Hl3 MUc WMc MIc TOKc Lc Hmode
ltac:(rewrite <- Hmode; apply Qa8x.Mq3.lvl_mode_esc_same; [rewrite Hst; reflexivity | reflexivity | exact SS26]) ltac:(unfold ST_string_escape; lia) SS26 (or_introl eq_refl)
ltac:(rewrite Hst; reflexivity)) as [INV4 PBK4];
unstash Kredo; eapply (Kredo mcF md2 A2 B2 pbs2 errv2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F2 fc2 N92);
[ exact INV4
| apply PBK4; unfold PBOK; cbn [t_co ts3 ts_set_x]; apply PBT3; replace (co + (kP + 3)) with (co + kP + 3) by lia; exact PBK2
| exact (BOK_lvl_restate _ _ ts3 B2 nB l ST_string_escape (tl_ss l) Hl3 (lvl_closed_keep l ST_string_escape _ _ _ _ _ eq_refl)
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
End PeSNeeduA.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QG8z.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QgoP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QgoP.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7UD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7UD. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qhd4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qhd4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqa. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdGy.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qw5U.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qw5U.Mq2.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition APE_ERRLIT : Z := 0x9845c.

Section PeSLitA.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_pres : forall LB SP m m', heap_pres A4H LB SP m m' -> GA m -> GA m'.

Lemma blk_granA : forall A LB LM FR B m md a n i,
HEAPA A4L HIx A LB LM FR B m md -> In (a, n) LB -> 0 <= i -> 8 * i + 8 <= n ->
ro_cells asegs m (a / 8 + i + A_SB) [C1 (Z_to_bv 8 0)].
Proof.
intros A LB LM FR B m md a n i HP Hin Hi Hn.
pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ _ _ HP Hin) as SH. unfold shad in SH. cbn [hl_sb A4L] in SH.
pose proof (shadow_granule0 asegs m (a / 8 + A_SB) n i Hi Hn SH) as G.
replace (a / 8 + A_SB + i) with (a / 8 + i + A_SB) in G by lia. exact G.
Qed.

Lemma PE_INV_A_stackw : forall pf pa q LB0 LM FRS payload me lo m m2 md A B ts cb nb pj sv errv,
PE_STATIC_A HIx pf pa lo ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
munch [(lo, pf_spf pf)] m m2 -> wmono asegs m m2 -> mem_inv asegs m2 -> stk asegs m2 lo (pf_spf pf) ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m2 md A B ts cb nb pj sv errv
/\ agree_on asegs (pe_blocksA pf q LB0 ts) m m2.
Proof.
intros until errv. intros STC INV MU WM MI2 ST2.
destruct ts as [depth levels co pbx pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs] in *.
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
pose proof INV as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof REST as (HP & LV & OBJ & ST & ERR & STR & PLEN & SBin & HPR & MDV & G & BUD).
cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs] in *.
set (ts := TST depth levels co pbx pbs x obj objs objbs) in *.
set (RB := pe_blocksA pf q LB0 ts) in *.
pose proof alloc_ceiling_range as ACR.
assert (HPRc : heap_pres A4H (RB ++ LM ++ fr_ivs A4L ((pa_F pa, 2) :: FRS)) (pf_spf pf) m m2).
{ eapply (heap_pres_of_munch A4H); [exact MU | exact WM |].
eapply (client_outsideF HIx); [exact HP | | lia |].
- intros b Hb. rewrite app_assoc in Hb. apply in_app_or in Hb as [Hb | Hb]; [left; exact Hb | right; exact Hb].
- apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_nil]. }
assert (HP2 : HEAPA A4L HIx A RB LM ((pa_F pa, 2) :: FRS) B m2 md).
{ eapply (heapA_client_frame A4L HIx); [exact HP | | exact WM | exact MI2]. eapply (frame_writes_okF A4L HIx); [exact HP | exact MU |].
apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_nil]. }
assert (INq2 : In (q, 32 * pf_mxd pf) RB) by (unfold RB, pe_blocksA; apply in_or_app; right; right; left; reflexivity).
assert (INtk2 : In (pf_tk pf, 72) RB) by (unfold RB, pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (AG : agree_on asegs RB m m2) by (eapply (agree_of_heap_pres asegs A4H); [exact HPRc | reflexivity | intros b Hb; apply in_or_app; left; exact Hb]).
assert (FR2 : pe_frameA asegs m2 pf pa cb nb pj sv).
{ eapply pe_frameA_pres; [exact HPRc | lia | exact GEO | | | exact FR].
- apply in_or_app; right. apply in_or_app; right. change 248 with (fr_size 2 - 8). apply fr_ivs_frame. left; reflexivity.
- apply in_or_app; right. apply in_or_app; right. rewrite <- fr_shadow_len_2. change (shA (pa_F pa)) with (shad A4L (pa_F pa)). apply fr_ivs_shadow. left; reflexivity. }
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPRc) in TOK; [| eapply client_range_block; [apply in_or_app; left; exact INtk2 | lia | unfold tok_cells_g; cbn; lia]]. cbn [hl_segs hla_base A4L A4H] in TOK.
apply (tstack_pres_g A4H _ _ _ _ _ _ HPRc (in_or_app _ _ _ (or_introl INq2))) in TSK; [| exact LEN32]. cbn [hl_segs hla_base A4L A4H] in TSK.
assert (ERR2 : rw_cells asegs m2 A_ERRNO [C4 errv]).
{ eapply rw_cells_transport; [exact ERR | exact MU | exact WM |]. cbn [cells_size csize Z.of_nat disjoint_from fst snd]. unfold A_ERRNO, A_TP. repeat split; try lia. }
assert (REST2 : PE_REST_A HIx GA pf pa q LB0 LM FRS payload me lo m2 md A B ts errv).
{ eapply (PE_REST_A_call_pb HIx GA GA_pres) with (ts := ts) (LBc := RB) (co2 := co) (pb2 := pbx) (pbs2 := pbs) (x2 := x);
[exact STC | exact REST | apply model_vm_only_refl | exact HPRc | | exact HP2 | exact ST2 | exact ERR2 | exact BUD].
unfold RB, pe_blocksA, tstate_blocks, ts; cbn [t_pbs t_objbs t_levels]. intros b Hb. apply in_app_or in Hb as [Hb | Hb].
- apply in_or_app; left. apply in_or_app; right. apply in_or_app; left. exact Hb.
- apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; apply in_or_app; right; apply in_or_app; right; exact Hb | apply in_or_app; right; right; right; exact Hb]. }
split; [| exact AG].
split; [| exact REST2]. unfold PE_CORE_A, ts; cbn [t_levels t_depth t_co t_x t_pb t_pbs]. split; [exact LEN32|]. split; [exact D32|]. split; [exact CO|]. split; [exact CHOFF|].
split; [exact TOK|]. split; [| split; [exact Hpb | split; [exact TSK | exact FR2]]].
eapply (pbuf_agree asegs); [exact PB | exact AG |]. unfold RB, pe_blocksA, tstate_blocks, ts; cbn [t_pbs]. intros b Hb. apply in_or_app; left. apply in_or_app; left. exact Hb.
Qed.

Lemma pe_istrn_c :
forall (entry : Z) (model : list byte -> list byte -> Z -> option (nat * Z)),
istrn_spec_U entry model ->
(forall ls pre post n, exists j v, model (ls ++ [b0]) (pre ++ [Z_to_bv 8 0] ++ post) n = Some (j, v) /\ -300 <= v <= 300) ->
(forall la lb n j v, model la lb n = Some (j, v) -> (j <= Z.to_nat n)%nat /\ (j <= length la)%nat /\ (j <= length lb)%nat /\ (0 < n -> (1 <= j)%nat)) ->
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (Q : machine_state -> Prop)
(xa n buf cap : Z) (ls : list byte)
(ra gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
t_pbs ts = [(t_pb ts, PB_SZ); (buf, cap)] ->
0 < n <= 64 ->
0x10000 <= xa -> xa + Z.of_nat (length ls) + 1 <= 0x3c000 ->
bytes_at asegs m xa (ls ++ [b0]) ->
(forall k', 0 < k' <= n -> k' <= Z.of_nat (length ls) + 1 -> src_globA xa k') ->
bv_unsigned ra mod 2 = 0 ->
(forall m2 (v : Z) (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
-300 <= v <= 300 ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m2 md A B ts cb nb pj sv errv ->
agree_on asegs (pe_blocksA pf q LB0 ts) m m2 ->
evt asegs Q (MS (mkR ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0' t1' t2' s0 s1 (Z_to_bv 64 v) a1' a2' a3' a4' a5' a6' a7'
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m2 (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2 s0 s1 (Z_to_bv 64 xa) (Z_to_bv 64 buf) (Z_to_bv 64 n) a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 entry) fc None m (seg_rom asegs)).
Proof.
intros entry model SPEC TOT NREAD. intros until fc. intros STC INV Epbs Hn Hxa Hxb LIT SRC RA K.
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
pose proof INV as [CORE REST].
destruct CORE as (_ & _ & _ & _ & _ & PB & _ & _ & _).
pose proof REST as (HP & _ & _ & ST & _).
destruct PB as (buf' & bpos & cap' & pre & post & Epbs' & Lpre & CORE1).
rewrite Epbs in Epbs'. injection Epbs' as <- <-.
destruct CORE1 as (Hbp & Hcap & Hlen & _ & BUFC).
pose proof (rw_cells_bytes_at' _ _ _ _ BUFC) as BUFB. cbn [cells_bytes cbytes] in BUFB. rewrite app_nil_r in BUFB.
destruct (TOT ls pre post n) as (k & v & MOD & Hv).
destruct (NREAD _ _ _ _ _ MOD) as (Hk1 & Hk2 & Hk3 & Hk4). specialize (Hk4 ltac:(lia)).
rewrite length_app in Hk2. cbn [length] in Hk2.
assert (INbuf : In (buf, cap) (pe_blocksA pf q LB0 ts)).
{ unfold pe_blocksA, tstate_blocks. rewrite Epbs. apply in_or_app; left. cbn [app]. right; left; reflexivity. }
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ buf cap HP (in_or_app _ LM _ (or_introl INbuf))) as (Hc0 & _ & Hb0 & Hbhi & _).
pose proof alloc_ceiling_range as ACR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
assert (SPF1 : lo <= pf_spf pf - 4096 /\ pf_spf pf mod 16 = 0) by (clear - LOS Gspf; split; [lia | Z.div_mod_to_equations; lia]).
destruct SPF1 as (SPF1 & SPF2).
eapply (SPEC ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2 s0 s1 (Z_to_bv 64 xa) (Z_to_bv 64 buf) (Z_to_bv 64 n) a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m xa buf n lo (ls ++ [b0]) (pre ++ [Z_to_bv 8 0] ++ post) k v Q);
rewrite ?unsigned_lit by lia.
- exact MOD.
- eapply (unpoisoned_of_glob HIx); [exact HP | apply SRC; rewrite ?length_app in *; cbn [length] in *; lia | lia].
- eapply (unpoisoned_of_blk HIx); [exact HP | exact INbuf | lia | lia | lia].
- exact (asan_rt_ok_of_HEAPA HIx _ _ _ _ _ _ _ HP).
- lia.
- rewrite length_app; cbn [length]; lia.
- lia.
- lia.
- left. rewrite length_app; cbn [length]; lia.
- left. lia.
- reflexivity.
- reflexivity.
- reflexivity.
- exact Hn.
- exact LIT.
- exact BUFB.
- exact ST.
- exact LO.
- exact SPF1.
- exact SPF2.
- exact MI.
- exact RA.
- intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 MU WM MI2 _ _ ST2.
destruct (PE_INV_A_stackw pf pa q LB0 LM FRS payload me lo m m2 md A B ts cb nb pj sv errv STC INV MU WM MI2 ST2) as [INV2 AG].
eapply (K m2 v); [exact Hv | exact INV2 | exact AG].
Qed.

Definition pe_istrncmp_c (SPEC : istrncmp_spec_U) := pe_istrn_c A_ISTRNCMP istrncmp_model SPEC istrncmp_total istrncmp_nread.
Definition pe_istrncasecmp_c (SPEC : istrncasecmp_spec_U) := pe_istrn_c A_ISTRNCASECMP istrncasecmp_model SPEC istrncasecmp_total istrncasecmp_nread.

Hypothesis GA_outside : forall m m' W, GA m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= hl_img_lo A4H \/ hl_img_hi A4H <= fst iv) W -> GA m'.

Lemma PE_INV_A_framew : forall pf pa q LB0 LM FRS payload me lo m mc md A B ts cb nb pj sv errv W cb' nb' pj',
PE_STATIC_A HIx pf pa lo ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
munch W m mc -> wmono asegs m mc -> mem_inv asegs mc -> Forall (pe_wtfA pf pa) W ->
rw_cells asegs mc (pf_tk pf) (tok_cells_g (pf_mxd pf) (pf_fl pf) (t_pb ts) (Z.of_nat (t_depth ts)) q (t_x ts)) ->
pe_frameA asegs mc pf pa cb' nb' pj' sv ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo mc md A B ts cb' nb' pj' sv errv
/\ (forall b, PBOKat m ts b -> PBOKat mc ts b).
Proof.
intros pf pa q LB0 LM FRS payload me lo m mc md A B ts cb nb pj sv errv W cb' nb' pj' STC [CORE REST] MU WM MI HW TOKc FRc.
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
split.
- split.
+ unfold PE_CORE_A. split; [exact LEN32|]. split; [exact D32|]. split; [exact CO|]. split; [exact CHOFF|].
split; [exact TOKc|]. split; [| split; [exact Hpb | split; [| exact FRc]]].
* eapply (pbuf_wtfA HIx) with (ts := ts); [exact STC | exact (proj1 REST) | exact PB | exact MU | exact WM | exact HW].
* eapply (tstack_wtfA HIx) with (ts := ts); [exact STC | exact (proj1 REST) | exact TSK | exact LEN32 | exact MU | exact WM | exact HW].
+ eapply (PE_REST_A_private_write HIx GA GA_outside) with (ts := ts); [exact STC | exact REST | exact MU | exact WM | exact MI | apply pe_wtfA_private; exact HW].
- intros b PBK.
eapply PBOKat_agree; [exact PBK | | apply incl_refl].
eapply (agree_wtqA HIx); [exact STC | exact (proj1 REST) | exact MU | exact WM | apply pe_wtfA_wtqA; exact HW |].
intros a n Hin. assert (HinL : In (a, n) (pe_blocksA pf q LB0 ts ++ LM)) by (unfold pe_blocksA, tstate_blocks; apply in_or_app; left; apply in_or_app; left; apply in_or_app; left; exact Hin).
split; [exact HinL|].
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ (proj1 REST)) as ND. unfold pe_blocksA in ND. rewrite <- app_assoc in ND. split.
+ intros ->. refine (nodup_app_ne _ _ _ _ _ _ ND _ _ eq_refl); [unfold tstate_blocks; apply in_or_app; left; exact Hin | left; reflexivity].
+ intros ->. refine (nodup_app_ne _ _ _ _ _ _ ND _ _ eq_refl); [unfold tstate_blocks; apply in_or_app; left; exact Hin | right; left; reflexivity].
Qed.
End PeSLitA.
End RC__1.
