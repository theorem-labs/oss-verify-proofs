(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup Lib.GwApply QWxq_c1 QRjH QHnV QCcH QfLs Q0Ek Qtgi QjDH Qsw7 QJjn QRUw QmZZ QPZI QkMG Qu4M QG8z Qdyh QLbz Q2Sr Qa8x Q7UD Qhd4 Qwm6 QlKV QsKa Qiiq Q4v2 Qoif Q1Ey Ql4f Q1Y6 QGdd QcmL QrQv QEUF QJZd QW22 QnDr Qmgs QdGy QWrz QV7s QQ2r QtyQ Q8H8 QFrL QQPy Qz87 Q84s QI6Z QFZX Q63E Q6oO Qvmy Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QJjn QRUw.Mq0 QRUw QmZZ. Import QPZI.Mq4. Import QkMG. Import Qu4M.Mq0 QG8z Qdyh.Mq0 Qdyh.Mq2 QLbz Q2Sr Qdyh.Mq3 Qa8x.Mq3 QLbz.Mq0.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa QsKa.Mq4 Qiiq.Mq0 QsKa.Mq6 Q4v2.Mq0 QlKV.Mq5 QlKV.Mq7 QsKa.Mq5 Qoif.Mq0 QlKV.Mq4 Q1Ey Ql4f.Mq1 Q1Y6.Mq2 QGdd QcmL.Mq0 QrQv.Mq2 QEUF QJZd.Mq8 QW22.Mq3 QnDr.Mq2 Qmgs QdGy.Mq5 QWrz.Mq1 QV7s QQ2r.Mq2 QtyQ.Mq2 QtyQ.Mq3 Q8H8.Mq0 QQ2r.Mq4 QFrL.Mq1 QQPy.Mq0 Qz87.Mq2 QJZd.Mq5 Q84s.Mq0 QI6Z.Mq2 Qiiq.Mq5 QJZd.Mq0.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Q2qa.Mq0.sf_vocab ::= Q2qa.Mq0.mkr__sf_vocab_5. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import QsKa.Mq0 QFZX.Mq4 QFZX.Mq3 Q63E.Mq6.
Import Q6oO.Mq0 Q63E.Mq7.
Import Qvmy.Mq0 QW22.Mq0 QV7s.Mq1.
Import QlKV.Mq2 QEUF.Mq1 QnDr.Mq3.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Lemma lhg_outside : forall m m' W, lh_globA m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= hl_img_lo A4H \/ hl_img_hi A4H <= fst iv) W -> lh_globA m'.
Proof.
intros m m' W G MU WM HW. eapply lh_globA_frame; [exact G | exact MU | exact WM |].
eapply Forall_impl; [| exact HW]. intros [a b] H. cbn [fst snd hl_img_lo hl_img_hi A4H] in *. unfold GHASHA, GSEEDA. lia.
Qed.
Lemma lhg_loc : forall m m', lh_globA m -> munch [(LOCCELL_A, LOCCELL_A + 8)] m m' -> wmono asegs m m' -> lh_globA m'.
Proof.
intros m m' G MU WM. eapply lh_globA_frame; [exact G | exact MU | exact WM |].
apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. unfold GHASHA, GSEEDA, LOCCELL_A, A_TP. lia.
Qed.

Section ATokParse.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).

Hypothesis MAPP : memappend_A_stmt2 HIx.
Hypothesis SHRINK : jo_array_shrink_A2J HIx.
Hypothesis AADD : jo_array_add_A2J HIx.
Hypothesis PUT : put_stmt_A HIx.
Hypothesis NEWARR : jo_new_array_A3 HIx.
Hypothesis NEWOBJ : jo_new_object_A3_stmt HIx.
Variable HD : Z.
Hypothesis HD_le : 64 + 96 + 4096 + 128 + HD <= 12288.
Hypothesis OADD : jo_object_add_A HIx HD.
Hypothesis USE : uselocale_A_stmt.
Hypothesis ERRNOL : errno_location_A_stmt.
Hypothesis DUP : duplocale_A_stmt HIx.
Hypothesis NEWL : newlocale_A_stmt HIx.
Hypothesis FREEL : freelocale_A_stmt HIx.
Hypothesis NEWDBL : jo_new_double_A_stmt HIx.
Hypothesis NEWBOOL : jo_new_boolean_A_stmt HIx.
Hypothesis NEWSTR : jo_new_string_len_A_stmt HIx.
Hypothesis PARSEI : parse_i64_A_stmt HIx 0xa39f8.
Hypothesis PARSEU : parse_i64_A_stmt HIx 0xa3c68.
Hypothesis STRTOD : strtod_A_stmt HIx.
Hypothesis NEWINT : jo_new_int_A_stmt HIx 0x9c330.
Hypothesis NEWUINT : jo_new_int_A_stmt HIx 0x9c9d4.
Hypothesis NEWDBLS : new_double_s_A_stmt HIx.

Definition tokparse_costB (n : Z) : Z := toknew_costB + (Z.of_nat (pe_A0 (n + 1)) + PhiPB (n + 1) 32 + K_free * 4 + K_exit) + 512 * 34.
Definition tokparse_costD (n : Z) : Z := Z.of_nat (pe_A0 (n + 1)) + 1 + M2D.
Lemma tokparse_A_main :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LBc LM : list blk) (FRS : list frame) (B : bud) (sb lo : Z) (str0 slack : list byte) (errv : word) (u : uwd),
jo_preA HIx A LBc LM FRS B m md sp tp ra lo (32 + 416 + 12288 + 4096) errv ->
bv_unsigned sp mod 32 = 0 -> Z.of_nat (length LM) < 8 ->
cstring_argA FRS m sb str0 slack -> Z.of_nat (length str0) < 2^25 ->
rw_cells asegs m LOCCELL_A [C8 (Z_to_bv 64 GLOBLOC_A)] -> rw_cells asegs m LOCALE_LOCK_A [C4 (Z_to_bv 64 0)] -> lh_globA m ->
bytes_at asegs m UTF8REP_ADDR_A Qa8x.Mq3.utf8rep ->
uw_at (hiA_top A4L HIx) m (bv_unsigned sp) (bv_unsigned s0) u -> uw_ok A4L (hl_calloc A4H) (Z_to_bv 64 0x92b10) u ->
Z.of_nat (length FRS) + 2 < 4096 ->
tokparse_costB (Z.of_nat (length str0)) <= bB B -> uw_cost u + tokparse_costD (Z.of_nat (length str0)) <= bD B ->
frm0 fc -> a0 = Z_to_bv 64 sb ->
(forall ms' md' m' (A' : ASA A4L HIx) (B' : bud) (gp' : word) (r : Z) (errv' : word) (RBS LK : list blk),
ret_statew A4H ra sp gp' tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' ->
model_vm_only (cfg_model md) (cfg_model md') ->
stk asegs m' lo (bv_unsigned sp) ->
rw_cells asegs m' A_ERRNO [C4 errv'] ->
rw_cells asegs m' LOCCELL_A [C8 (Z_to_bv 64 GLOBLOC_A)] -> rw_cells asegs m' LOCALE_LOCK_A [C4 (Z_to_bv 64 0)] -> lh_globA m' ->
bytes_at asegs m' UTF8REP_ADDR_A Qa8x.Mq3.utf8rep ->
heap_presx A4H QcmL.Mq0.xlocA (LBc ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m' ->
jo_chargeA (tokparse_costB (Z.of_nat (length str0))) (uw_cost u + tokparse_costD (Z.of_nat (length str0))) B B' ->
HEAPAx A' (RBS ++ LK ++ LBc) LM FRS B' m' md' ->
((r = 0 /\ RBS = []) \/
(r <> 0 /\ exists s, jval asegs A4F s m' RBS r 1 /\ sdepth s <= 32 /\ exists w, jtx s RBS = Some (w, []) /\ w <= 26 * (Z.of_nat (length str0) + 1) + 64)) ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x93040) fc None m (seg_rom asegs)).
Proof.
intros until u. intros PRE SP32 LMN CSTR LEN LOC LCK G UTF UW UWK FRN BB BD FRM A0 K. subst a0.
destruct PRE as (HP & ST & LO & LOS & SPA & HT & ERR & TP & RA).
destruct CSTR as (STR & NONUL & PAD & ALOC & UNP). destruct ALOC as (Fr & kf & INF & HF1 & HF2).
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP INF) as (Hkf & HFal & HF0 & HFc & _).
pose proof alloc_ceiling_range as ACR. pose proof (hiA_top_le A4L HIx) as HT47.
unfold tokparse_costB, tokparse_costD in BB, BD.
word_range sp SPR. assert (M2D0 : 0 <= M2D) by (unfold M2D; lia).
pose proof (bytes_at_bound _ _ _ _ STR) as SB0. rewrite length_app in SB0. cbn [length] in SB0.

assert (TRK : forall mx, munch [(bv_unsigned sp + -32, bv_unsigned sp)] m mx -> wmono asegs m mx ->
bytes_at asegs mx sb (str0 ++ Z_to_bv 8 0 :: slack) /\ rw_cells asegs mx LOCCELL_A [C8 (Z_to_bv 64 GLOBLOC_A)] /\
rw_cells asegs mx LOCALE_LOCK_A [C4 (Z_to_bv 64 0)] /\ lh_globA mx /\ bytes_at asegs mx UTF8REP_ADDR_A Qa8x.Mq3.utf8rep /\
unpoisoned asegs mx A_SB sb (Z.of_nat (length str0) + 1)).
{ intros mx MUx WMx.
split. { eapply bytes_at_transport; [exact STR | exact MUx |]. cbn [disjoint_from]. rewrite length_app. cbn [length]. lia. }
split. { eapply rw_cells_transport; [exact LOC | exact MUx | exact WMx |]. unfold LOCCELL_A, A_TP. cbn [disjoint_from cells_size csize Nat.add]. lia. }
split. { eapply rw_cells_transport; [exact LCK | exact MUx | exact WMx |]. unfold LOCALE_LOCK_A. cbn [disjoint_from cells_size csize Nat.add]. lia. }
split. { eapply lhg_outside; [exact G | exact MUx | exact WMx |]. apply Forall_cons; [| apply Forall_nil]. cbn [fst snd hl_img_lo hl_img_hi A4H]. lia. }
split. { eapply bytes_at_transport; [exact UTF | exact MUx |]. unfold UTF8REP_ADDR_A. cbn [disjoint_from length Qa8x.Mq3.utf8rep]. lia. }
eapply unpoisoned_transport; [exact UNP | exact MUx |]. intros a k Ha Hk. cbn [disjoint_from]. split; [| exact I]. left.
assert (HH : shadow_span_hi A_SB sb (Z.of_nat (length str0) + 1) <= 2^45).
{ unfold shadow_span_hi, A_SB. assert (E1 : (sb + (Z.of_nat (length str0) + 1) - 1) / 8 <= 2^44) by (apply Z.div_le_upper_bound; lia).
pose proof (Z.mul_div_le ((sb + (Z.of_nat (length str0) + 1) - 1) / 8 + 2147450880) 8 ltac:(lia)). lia. }
lia. }
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL].
pose proof (heap_pres_refl A4H (LBc ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m) as HPR.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU.
stash TRK. stash K.
a4l. reenterA asegs A4L HIx asegs_wx HP. subst tp.
carve_frame 32%nat ST.
do 5 step.
step. step. step.
step. step. step.
evt_done5.
eapply (json_tokener_new_A_cps HIx PUT) with (u := u) (lo := lo);
[ heap_nowA A4L HIx HP MU WM MI
| rewrite ?unsigned_lit by lia; eapply (uw_at_mono _ _ _ _ _ _ _ _ UW MU); [apply Forall_cons; [cbn; lia | apply Forall_nil] | lia]
| exact UWK | .. ]; a4l_goal; rewrite ?unsigned_lit by lia; try first [reflexivity | lia].
all: try eassumption.
1: (unfold put_stk_A; lia).
1: (unfold toknew_costB, pbnew_costB, PhiPB, K_free, K_exit in *; lia).
intros ms2 md2 A2 (m2 & r & errv2 & B2 & RS2 & VM2 & ST2 & HPR2 & ERR2 & BB2 & BD2 & OUT2).
destruct RS2 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F2 & fc2 & -> & FS2 & FRM2).
a4l. rewrite ?unsigned_lit in ST2 by lia. rewrite ?unsigned_lit in HPR2 by lia.
extend_presA A4L HIx HPR MU WM HP HPR2.
replace (ret_pc (Z_to_bv 64 602220)) with (Z_to_bv 64 602220) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
unstash TRK. destruct (TRK m1 MU WM) as (STR1 & LOC1 & LCK1 & G1 & UTF1 & UNP1). clear TRK.

apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia].
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in LOC1; [| right; left; cbn; intros z Hz; cbn [hl_client_static A4H]; unfold a4_client_static, LOCCELL_A, A_TP in *; lia].
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in LCK1; [| right; left; cbn; intros z Hz; cbn [hl_client_static A4H]; unfold a4_client_static, LOCALE_LOCK_A in *; lia].
pose proof (lh_globA_client _ _ _ _ HPR2 G1) as G2.
assert (UTF2 : bytes_at asegs m2 UTF8REP_ADDR_A Qa8x.Mq3.utf8rep).
{ eapply (heap_pres_bytes_at A4H); [exact HPR2 | exact UTF1 |]. right; left. intros z Hz. unfold UTF8REP_ADDR_A in Hz. cbn in Hz. cbn [hl_client_static A4H]. unfold a4_client_static. lia. }
assert (INFI : In (Fr, fr_size kf - 8) (LBc ++ LM ++ fr_ivs A4L FRS)) by (apply in_or_app; right; apply in_or_app; right; apply fr_ivs_frame; exact INF).
assert (STR2 : bytes_at asegs m2 sb (str0 ++ Z_to_bv 8 0 :: slack)).
{ eapply (heap_pres_bytes_at A4H); [exact HPR2 | exact STR1 |]. eapply client_range_block; [exact INFI | exact HF1 |]. rewrite length_app. cbn [length]. lia. }
assert (UNP2 : unpoisoned asegs m2 A_SB sb (Z.of_nat (length str0) + 1)).
{ eapply (unpoisoned_pres_frame HIx A LBc LM FRS B m md LBc _ m1 m2 Fr kf); [exact HP | exact INF | exact HF1 | lia | exact UNP1 | exact HPR2]. }
assert (UW2 : uw_at (hiA_top A4L HIx) m2 (bv_unsigned sp) (bv_unsigned s0) u).
{ eapply uw_at_heap_pres; [eapply (uw_at_mono _ _ _ _ _ _ _ _ UW MU); [apply Forall_cons; [cbn; lia | apply Forall_nil] | lia] | exact HPR2 | lia]. }
cbn [uw_cost] in BD2.
destruct OUT2 as [(-> & HP2) | (Hr & BS & TF & HP2)].
-
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI2. a4l.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m2) as MU2. pose proof (wmono_refl asegs m2) as WM2.
reenterA asegs A4L HIx asegs_wx HP2.
step. if_true. do 6 step.
evt_done5. unstash K. eapply (K _ _ _ _ B2 _ 0 errv2 [] []).
+ apply ret_statew_intro; [exact FS2 | exact FRM2].
+ exact VM2.
+ release_frame FR ST2 (bv_unsigned sp). exact ST2.
+ exact ERR2.
+ exact LOC1.
+ exact LCK1.
+ exact G2.
+ exact UTF2.
+ apply heap_pres_presx. exact HPR.
+ unfold jo_chargeA, tokparse_costB, tokparse_costD. unfold toknew_costB, pbnew_costB, PhiPB, K_free, K_exit in *. split; lia.
+ exact HP2.
+ left. split; reflexivity.
-
destruct TF as (stk0 & pb & PBS & EBS & TOK & PBF & Hpb & TSK).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI2. a4l.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m2) as MU2. pose proof (wmono_refl asegs m2) as WM2.
assert (INtk : In (r, 72) ((BS ++ LBc) ++ LM)) by (apply in_or_app; left; apply in_or_app; left; rewrite EBS; left; reflexivity).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ r 72 HP2 INtk) as (_ & Htal & Htlo & Hthi & _).
stash TOK. stash PBF. stash TSK. stash STR2. stash LOC1. stash LCK1. stash UTF2.
reenterA asegs A4L HIx asegs_wx HP2.
step. if_falsex. step. step. step. step.
evt_done5. unstash TOK. unstash PBF. unstash TSK. unstash STR2. unstash LOC1. unstash LCK1. unstash UTF2.
destruct PBF as (buf & post & EPBS & PCORE).
set (len := Z.of_nat (length str0) + 1).
replace (str0 ++ Z_to_bv 8 0 :: slack) with ((str0 ++ [Z_to_bv 8 0]) ++ slack) in STR2 by (rewrite <- app_assoc; reflexivity).
apply bytes_at_app in STR2 as [S1 S2]. rewrite length_app in S2. cbn [length] in S2. replace (sb + Z.of_nat (length str0 + 1)) with (sb + len) in S2 by (unfold len; lia).
assert (LBS : length BS = 4%nat) by (rewrite EBS, EPBS; reflexivity).
set (bslv := bB B2 - (Z.of_nat (pe_A0 len) + PhiPB len 32 + K_free * 4 + K_exit)).
set (dslv := bD B2 - Z.of_nat (pe_A0 len) - M2D).
eapply (json_tokener_parse_ex_A_cps HIx lh_globA lhg_outside lh_globA_client (fun _ _ _ _ _ H _ => H) (fun _ H => H) lhg_loc
MAPP SHRINK AADD PUT NEWARR NEWOBJ HD HD_le OADD USE ERRNOL DUP NEWL FREEL NEWDBL NEWBOOL NEWSTR PARSEI PARSEU STRTOD NEWINT NEWUINT NEWDBLS)
with (TBS := BS) (LBc := LBc) (LM := LM) (FRS := FRS) (B := B2) (tk := r) (sb := sb) (len := len) (lenr := 2^64 - 1) (lo := lo) (bsl := bslv) (dsl := dslv)
(sp0 := bv_unsigned sp + -32) (payload := str0 ++ [Z_to_bv 8 0]) (slack := slack) (errv := errv2) (mxd := 32) (q := stk0) (pb := pb) (pbs := PBS).
1: heap_nowA A4L HIx HP2 MU2 WM2 MI2.
1: exact EBS.
1: lia.
1: exact TOK.
1: (exists buf, 0, 32, [], post; split; [exact EPBS | split; [reflexivity | exact PCORE]]).
1: exact Hpb.
1: exact TSK.
1: (exists buf, 0, 32, [], post; split; [cbn [ts_init t_pbs]; exact EPBS | split; [reflexivity | split; [exact PCORE | lia]]]).
1: (rewrite EPBS; reflexivity).
1: exact S1.
1: (rewrite length_app; cbn [length]; unfold len; lia).
1: (unfold len; lia).
1: { split.
- right; right. exists Fr, kf. split; [exact INF|]. split; [exact HF1|]. split; [unfold len; lia | exact UNP2].
- right. split; [reflexivity|]. split; [unfold len; lia|].
split. { exists str0. split; [reflexivity|]. intros Hin. rewrite Forall_forall in NONUL. apply (NONUL _ Hin). reflexivity. }
split; [exact S2|]. split; [unfold len; replace (sb + (Z.of_nat (length str0) + 1)) with (sb + Z.of_nat (length str0) + 1) by lia; exact PAD|].
right. exists Fr, kf. split; [exact INF|]. split; [exact HF1 | unfold len; lia]. }
1: lia.
1: (unfold len; lia).
1: exact LOC1.
1: exact LCK1.
1: exact G2.
1: exact UTF2.
1: reflexivity.
1: eassumption.
1: exact LO.
1: (unfold PE_STK_A; lia).
1: (replace (bv_unsigned sp + -32) with (bv_unsigned sp + (-1) * 32) by lia; rewrite Z.mod_add by lia; exact SP32).
1: lia.
1: lia.
1: exact ERR2.
1: reflexivity.
1: exact (FRM2 FRM).
1: reflexivity.
1: reflexivity.
1: (apply bv_eq; vm_compute; reflexivity).
1: reflexivity.
1: reflexivity.
1-7: (cbn [uw_ok uw_key]; rewrite ?unsigned_lit by lia; unfold a4_straces, PE_RA2; cbn [hl_straces hl_malloc hl_free hl_strdup A4L A4H hla_base]; repeat first [left; reflexivity | right]).
1: exact LMN.
1: exact FRN.
1: (fold len in BD; cbn [uw_cost] in *; lia).
1: (unfold bslv; rewrite LBS; unfold K_free; lia).
1: (unfold dslv; lia).
1: (unfold bslv; unfold toknew_costB, pbnew_costB in *; fold len in BB; unfold K_free, K_exit in *; lia).
1: (unfold dslv; fold len in BD; lia).
intros ms3 md3 A3 (m3 & gp3 & r3 & errv3 & RBS & TBS & LK & B3 & RS3 & VM3 & ST3 & ERR3 & LOC3 & HPRX3 & HP3 & TOKR3 & RES3 & G3 & BB3 & BD3).
cbn [pe_ra pe_s0 pe_s1 pe_s2 pe_s3 pe_s4 pe_s5 pe_s6 pe_s7 pe_s8 pe_s9 pe_s10 pe_s11 pa_sp0 pa_bslack pa_dslack pf_tk pf_mxd pf_fl pf_len] in *.
destruct RS3 as (v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & F3 & fc3 & -> & FS3 & FRM3).
replace (ret_pc (Z_to_bv 64 PE_RA2)) with (Z_to_bv 64 PE_RA2) by (symmetry; apply ret_pc_even; [unfold PE_RA2; lia | reflexivity]).

eapply (heap_presx_rw_cells A4H) in FR; [| exact HPRX3 | left; cbn; lia].
eapply (heap_presx_rw_cells A4H) in LCK1; [| exact HPRX3 | right; left; cbn; intros z Hz; split; [cbn [hl_client_static A4H]; unfold a4_client_static, LOCALE_LOCK_A in *; lia | unfold QcmL.Mq0.xlocA, a4_volatile, LOCALE_LOCK_A, LOCCELL_A, A_TP in *; lia]].
assert (UTF3 : bytes_at asegs m3 UTF8REP_ADDR_A Qa8x.Mq3.utf8rep).
{ eapply (heap_presx_bytes_at A4H); [exact HPRX3 | exact UTF2 |]. right; left. intros z Hz. unfold UTF8REP_ADDR_A in Hz. cbn in Hz.
split; [cbn [hl_client_static A4H]; unfold a4_client_static; lia | unfold QcmL.Mq0.xlocA, a4_volatile, LOCCELL_A, A_TP; lia]. }

pose proof TOKR3 as (stk3 & pb3 & dep3 & PBS3 & lvs3 & x3 & ETBS3 & LEN3 & DEP3 & TOK3 & _).
destruct x3 as [isd3 stp3 cho3 err3 ucs3 hi3 qu3].
assert (INtk3 : In (r, 72) (RBS ++ TBS ++ LK ++ LBc)) by (apply in_or_app; right; apply in_or_app; left; rewrite ETBS3; left; reflexivity).
assert (SHT3 : ro_cells asegs m3 (r / 8 + A_SB)
[C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]).
{ pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ r 72 HP3 INtk3) as SH. unfold shad in SH. apply shadow_ro_cells in SH.
let cs := eval cbv in (shadow_cells 72) in change (shadow_cells 72) with cs in SH. exact SH. }
unfold tok_cells_g in TOK3. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK3.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP3) as MI3.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m3) as MU3. pose proof (wmono_refl asegs m3) as WM3.
unfold A_SB, PE_RA2 in *. a4l.
reenterA asegs A4L HIx asegs_wx HP3.
step. asan_chkA.
step.

assert (FREE : forall (m4 : word -> option byte) (md4 : config) (A4 : ASA A4L HIx) (B4 : bud) (F4 : bvmap 5 word) (fc4 : bv 32) (RBS4 : list blk) (r4 : Z) (errv4 : word)
(x1 gpx y0 y1 y2 b0 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 : word),
HEAPAx A4 (RBS4 ++ TBS ++ LK ++ LBc) LM FRS B4 m4 md4 ->
((r4 = 0 /\ RBS4 = []) \/
(r4 <> 0 /\ exists s, jval asegs A4F s m4 RBS4 r4 1 /\ sdepth s <= 32 /\ exists w, jtx s RBS4 = Some (w, []) /\ w <= 26 * (Z.of_nat (length str0) + 1) + 64)) ->
tokrep_g asegs A4F 32 0 m4 TBS r ->
heap_presx A4H QcmL.Mq0.xlocA (LBc ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m4 ->
model_vm_only (cfg_model md) (cfg_model md4) -> fsaved F F4 -> (frm0 fc -> frm0 fc4) ->
rw_cells asegs m4 LOCCELL_A [C8 (Z_to_bv 64 GLOBLOC_A)] -> rw_cells asegs m4 LOCALE_LOCK_A [C4 (Z_to_bv 64 0)] -> lh_globA m4 ->
bytes_at asegs m4 UTF8REP_ADDR_A Qa8x.Mq3.utf8rep ->
stk asegs m4 lo (bv_unsigned sp + -32) -> rw_cells asegs m4 (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra] -> rw_cells asegs m4 A_ERRNO [C4 errv4] ->
bB B - tokparse_costB (Z.of_nat (length str0)) + tokfree_costB TBS <= bB B4 ->
bD B - (uw_cost u + tokparse_costD (Z.of_nat (length str0))) + 1 <= bD B4 ->
AJ5 A4L HIx A4 T md4
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -32)) gpx (Z_to_bv 64 6434400) y0 y1 y2 (Z_to_bv 64 r) (Z_to_bv 64 r4) b0 b1 b2 b3 b4 b5 b6 b7
(Z_to_bv 64 2147450880) s3 s4 s5 s6 s7 s8 s9 s10 s11 y3 y4 y5 y6)
F4 (Z_to_bv 64 0x930b0) fc4 None m4 (seg_rom asegs))).
{ clear - K HD_le PUT ACR HT47 SPR LO LOS SPA HT RA Htlo Hthi Hr BB BD.
intros m4 md4 A4 B4 F4 fc4 RBS4 r4 errv4 x1 gpx y0 y1 y2 b0 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 HP4 RES4 TOKR4 PX4 VM4 FS4 FRM4 LOC4 LCK4 G4 UTF4 ST4 FR4 ERR4 BB4 BD4.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP4) as MI4.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m4) as MU4. pose proof (wmono_refl asegs m4) as WM4.
a4l. reenterA asegs A4L HIx asegs_wx HP4.
step. step.
evt_done5. unstash K.
eapply (json_tokener_free_A_cps HIx PUT) with (BS := TBS) (LB := RBS4 ++ LK ++ LBc) (tk := r) (lo := lo) (u := UWpaid);
[ eapply (heapA_perm A4L HIx); [heap_nowA A4L HIx HP4 MU4 WM4 MI4 | apply Permutation_app_swap_app | apply Permutation_refl | apply Permutation_refl]
| apply tokrep_g32; exact TOKR4 | exact Hr | apply uw_at_paid | cbn; exact I | .. ]; a4l_goal; rewrite ?unsigned_lit by lia; try first [reflexivity | eassumption | lia].
1: (unfold put_stk_A; lia).
1: (unfold tokparse_costB in BB4; unfold tokfree_costB in *; lia).
1: (cbn [uw_cost]; unfold tokparse_costD in BD4; lia).
intros ms5 md5 A5 (m5 & rv5 & B5 & RS5 & VM5 & ST5 & HPR5 & ERR5 & BB5 & BD5 & HP5).
destruct RS5 as (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & F5 & fc5 & -> & FS5 & FRM5).
a4l. rewrite ?unsigned_lit in ST5 by lia. rewrite ?unsigned_lit in HPR5 by lia.
replace (ret_pc (Z_to_bv 64 602296)) with (Z_to_bv 64 602296) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR5) in FR4; [| left; cbn; lia]. a4l.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP5) as MI5.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m5) as MU5. pose proof (wmono_refl asegs m5) as WM5.
reenterA asegs A4L HIx asegs_wx HP5.
do 7 step.
evt_done5. eapply (K _ _ _ _ B5 _ r4 errv4 RBS4 LK).
+ apply ret_statew_intro; [eapply fsaved_trans; [exact FS4 | exact FS5] | intros Hf; exact (FRM5 (FRM4 Hf))].
+ eapply model_vm_only_trans; [exact VM4 | exact VM5].
+ release_frame FR4 ST5 (bv_unsigned sp). exact ST5.
+ exact ERR5.
+ eapply (heap_pres_rw_cells A4H); [exact HPR5 | exact LOC4 |]. right; left. cbn. intros z Hz. cbn [hl_client_static A4H]. unfold a4_client_static, LOCCELL_A, A_TP in *. lia.
+ eapply (heap_pres_rw_cells A4H); [exact HPR5 | exact LCK4 |]. right; left. cbn. intros z Hz. cbn [hl_client_static A4H]. unfold a4_client_static, LOCALE_LOCK_A in *. lia.
+ exact (lh_globA_client _ _ _ _ HPR5 G4).
+ eapply (heap_pres_bytes_at A4H); [exact HPR5 | exact UTF4 |]. right; left. intros z Hz. unfold UTF8REP_ADDR_A in Hz. cbn in Hz. cbn [hl_client_static A4H]. unfold a4_client_static. lia.
+ eapply heap_presx_trans; [exact PX4|]. apply heap_pres_presx. eapply heap_pres_weaken; [exact HPR5 | lia |].
intros b Hb. apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; apply in_or_app; right; apply in_or_app; right; exact Hb | apply in_or_app; right; exact Hb].
+ unfold jo_chargeA. unfold tokfree_costB in *. cbn [uw_cost] in BD5. split; lia.
+ exact HP5.
+ destruct RES4 as [L | (NZ & s & J & D)]; [left; exact L | right]. split; [exact NZ|]. exists s. split; [| exact D].
eapply (jval_agree asegs A4F); [exact J | eapply (agree_of_heap_pres asegs A4H); [exact HPR5 | reflexivity | intros b Hb; apply in_or_app; left; apply in_or_app; left; exact Hb] | apply incl_refl]. }

assert (PX3 : heap_presx A4H QcmL.Mq0.xlocA (LBc ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m3).
{ eapply heap_presx_trans; [apply heap_pres_presx; exact HPR|]. eapply heap_presx_weaken; [exact HPRX3 | lia | intros b Hb; exact Hb | intros a Xa; exact Xa]. }
assert (VM03 : model_vm_only (cfg_model md) (cfg_model md3)) by (eapply model_vm_only_trans; [exact VM2 | exact VM3]).
assert (FS03 : fsaved F F3) by (eapply fsaved_trans; [exact FS2 | exact FS3]).
assert (BB03 : bB B - tokparse_costB (Z.of_nat (length str0)) + tokfree_costB TBS + 512 * Z.of_nat (length RBS) <= bB B3).
{ unfold tokparse_costB, tokfree_costB. fold len. unfold bslv in BB3. rewrite length_app, Nat2Z.inj_add in BB3. unfold toknew_costB, pbnew_costB, K_free in *. lia. }
assert (BD03 : bD B - (uw_cost u + tokparse_costD (Z.of_nat (length str0))) + 1 <= bD B3).
{ unfold tokparse_costD. fold len. unfold dslv in BD3. lia. }
step. match goal with |- context [if ?c then Z_to_bv 64 602284 else _] => destruct c end.
+
step. evt_done5.
eapply (FREE m3 md3 A3 B3 F3 fc3 RBS r3 errv3);
[ heap_nowA A4L HIx HP3 MU3 WM3 MI3 | exact RES3 | exact TOKR3 | exact PX3 | exact VM03 | exact FS03 | intros Hf; exact (FRM3 (FRM2 Hf)) | exact LOC3 | exact LCK1 | exact G3 | exact UTF3
| eassumption | eassumption | eassumption | pose proof (Zle_0_nat (length RBS)); lia | exact BD03 ].
+
destruct RES3 as [[-> ->] | (NZ3 & s3v & J3 & D3)].
* step. if_true. step. step. evt_done5.
eapply (FREE m3 md3 A3 B3 F3 fc3 [] 0 errv3);
[ heap_nowA A4L HIx HP3 MU3 WM3 MI3 | left; split; reflexivity | exact TOKR3 | exact PX3 | exact VM03 | exact FS03 | intros Hf; exact (FRM3 (FRM2 Hf)) | exact LOC3 | exact LCK1 | exact G3 | exact UTF3
| eassumption | eassumption | eassumption | cbn [length Z.of_nat] in BB03; lia | exact BD03 ].
* assert (RR : 0 < r3 /\ r3 + 48 <= alloc_ceiling).
{ pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP3) as ND. rewrite !map_app in ND. apply List.NoDup_app_remove_r in ND. apply List.NoDup_app_remove_r in ND.
destruct (QmZZ.jval_hdr asegs A4F s3v m3 RBS r3 1 J3 ND) as (n & tojs & pb0 & udel & ud & rest & INp & Hn & H48 & _).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ r3 n HP3 ltac:(apply in_or_app; left; apply in_or_app; left; exact INp)) as (_ & _ & Hlo & Hhi & _). lia. }
step. if_falsex. step. evt_done5.
eapply PUT with (s := Some s3v) (BS := RBS) (p := r3) (rc := 1) (lo := lo) (LB := TBS ++ LK ++ LBc);
[ heap_nowA A4L HIx HP3 MU3 WM3 MI3 | cbn [QPIU.Mqi.put_pre]; split; [exact NZ3 | split; [lia | exact J3]] | reflexivity | .. ];
a4l_goal; rewrite ?unsigned_lit by lia; try first [reflexivity | eassumption | lia].
1: (unfold put_stk_A; lia).
1: (unfold put_costA; change (1 =? 1) with true; cbv iota; unfold tokparse_costB, tokfree_costB in BB03; pose proof (Zle_0_nat (length TBS)); unfold toknew_costB, pbnew_costB, PhiPB, K_free, K_exit in *; lia).
intros ms4 md4 A4 (m4 & rv4 & B4 & RS4 & VM4 & ST4 & HPR4 & ERR4 & BB4 & BD4 & OUT4).
destruct RS4 as (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & F4 & fc4 & -> & FS4 & FRM4).
a4l. rewrite ?unsigned_lit in ST4 by lia. rewrite ?unsigned_lit in HPR4 by lia.
replace (ret_pc (Z_to_bv 64 602276)) with (Z_to_bv 64 602276) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
assert (HP4 : HEAPAx A4 (TBS ++ LK ++ LBc) LM FRS B4 m4 md4) by (destruct OUT4 as [[_ H] | (s' & _ & RC & _)]; [exact H | lia]).
clear OUT4.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP4) as MI4.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m4) as MU4. pose proof (wmono_refl asegs m4) as WM4.
reenterA asegs A4L HIx asegs_wx HP4.
step. step. evt_done5.
assert (AG4 : agree_on asegs TBS m3 m4).
{ eapply (agree_of_heap_pres asegs A4H); [exact HPR4 | reflexivity |]. intros b Hb. apply in_or_app; left. apply in_or_app; left. exact Hb. }
eapply (FREE m4 md4 A4 B4 F4 fc4 [] 0 errv3).
-- heap_nowA A4L HIx HP4 MU4 WM4 MI4.
-- left. split; reflexivity.
-- eapply tokrep_g_agree; [exact TOKR3 | exact AG4].
-- eapply heap_presx_trans; [exact PX3|]. apply heap_pres_presx. eapply heap_pres_weaken; [exact HPR4 | lia |].
intros b Hb. apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; apply in_or_app; right; apply in_or_app; right; exact Hb | apply in_or_app; right; exact Hb].
-- eapply model_vm_only_trans; [exact VM03 | exact VM4].
-- eapply fsaved_trans; [exact FS03 | exact FS4].
-- intros Hf. exact (FRM4 (FRM3 (FRM2 Hf))).
-- eapply (heap_pres_rw_cells A4H); [exact HPR4 | exact LOC3 |]. right; left. cbn. intros z Hz. cbn [hl_client_static A4H]. unfold a4_client_static, LOCCELL_A, A_TP in *. lia.
-- eapply (heap_pres_rw_cells A4H); [exact HPR4 | exact LCK1 |]. right; left. cbn. intros z Hz. cbn [hl_client_static A4H]. unfold a4_client_static, LOCALE_LOCK_A in *. lia.
-- exact (lh_globA_client _ _ _ _ HPR4 G3).
-- eapply (heap_pres_bytes_at A4H); [exact HPR4 | exact UTF3 |]. right; left. intros z Hz. unfold UTF8REP_ADDR_A in Hz. cbn in Hz. cbn [hl_client_static A4H]. unfold a4_client_static. lia.
-- eassumption.
-- eapply (heap_pres_rw_cells A4H) in FR; [| exact HPR4 | left; cbn; lia]. a4l. exact FR.
-- eassumption.
-- unfold put_costA in BB4. change (1 =? 1) with true in BB4. cbv iota in BB4. lia.
-- lia.
Qed.

Theorem json_tokener_parse_A_cps : jo_tokparse_A_stmt HIx 0x93040 (32 + 416 + 12288 + 4096) 0x92b10 tokparse_costB tokparse_costD.
Proof.
unfold jo_tokparse_A_stmt. intros until u. intros PRE SP32 LMN CSTR LEN (LOC & LCK & G & UTF) UW UWK FRN BB BD FRM A0 K.
eapply (tokparse_A_main ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m md T A LBc LM FRS B sb lo str0 slack errv u);
[exact PRE | exact SP32 | exact LMN | exact CSTR | exact LEN | exact LOC | exact LCK | exact G | exact UTF | exact UW | exact UWK | exact FRN | exact BB | exact BD | exact FRM | exact A0 |].
intros ms' md' m' A' B' gp' r errv' RBS LK RS VM ST ERR LOC' LCK' G' UTF' PX CH HP RES.
eapply (K ms' md' m' A' B' gp' r errv' RBS LK); [exact RS | exact VM | exact ST | exact ERR | split; [exact LOC' | split; [exact LCK' | split; [exact G' | exact UTF']]] | exact PX | exact CH | exact HP | exact RES].
Qed.
End ATokParse.

Lemma tokparse_cost_le : forall n, 0 <= n <= 20 -> 0 <= tokparse_costB n <= 322639 /\ 0 <= tokparse_costD n <= 257424 + 2^27.
Proof.
intros n Hn. unfold tokparse_costB, tokparse_costD, pe_A0, pe_N0, toknew_costB, QJZd.Mq5.pbnew_costB, PhiPB, K_free, K_exit, M2D.
assert (H : (16 * Z.max 0 (n + 1) + 11008) * (n + 1) <= (16 * 21 + 11008) * 21) by nia.
split; lia.
Qed.

End RC__1.
End Mq0.
From LinuxProcessSemantics.LinuxProcessSem Require Fs.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.SepCache Qfw3_c1 Qc3B Q5Rg QKQo Q8tj QSL3 Qvbw QYIF QnCn QR2u QrIB QXUB Qw5U Q9O6 Qawr Q30W Q2Do QJlD QB6X QSHS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.

Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun QWxq_c1.Mq0 Qfw3_c1.Mq2 Qc3B Q5Rg.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 QmZZ Qsw7 QJjn QKQo Q8tj QRUw.Mq2.
Import QSL3.
Import Qvbw QYIF.
Import QnCn.Mq0 QR2u.

Import Q7UD QXUB.Mq0 Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QsKa.Mq4 QlKV.Mqa QsKa.Mq7 QsKa.Mq0 QJZd.Mq0 QsKa.Mq8 Qw5U.Mq0 QsKa.Mq3 QsKa.Mq2 QlKV.Mq7 QsKa.Mq5 QlKV.Mq5 QlKV.Mq2 QsKa Q9O6.Mq1 Qiiq.Mq0.

Import Qvmy.Mq0 Qawr.Mq0 Q30W.Mq0 Q2Do.Mq0.

Import Qu4M.Mq0.
Import Qwm6.Mq2.
Import QB6X QSHS.Mq1 Qoif.Mq2.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Q2qa.Mq0.sf_vocab ::= Q2qa.Mq0.mkr__sf_vocab_5. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Lemma unpoisoned_of_fshadow1 : forall m Fr (shb : list byte) (g0 g1 : nat),
bytes_at asegs m (Fr / 8 + A_SB) shb -> length shb = 16%nat -> Fr mod 128 = 0 -> 0 <= Fr ->
(g0 < g1)%nat -> (g1 <= 16)%nat ->
forallb (fun b => bv_unsigned b =? 0) (firstn (g1 - g0) (skipn g0 shb)) = true ->
unpoisoned asegs m A_SB (Fr + 8 * Z.of_nat g0) (8 * Z.of_nat (g1 - g0)).
Proof.
intros m Fr shb g0 g1 SH L AL F0 Hg Hg1 Z0.
assert (GZ : forall g : nat, (g0 <= g < g1)%nat -> bytes_at asegs m (Fr / 8 + A_SB + Z.of_nat g) [Z_to_bv 8 0]).
{ intros g Hgg. pose proof (Ql4f.Mq0.bytes_at_sub asegs m _ shb g 1 SH ltac:(lia)) as X.
assert (E : firstn 1 (skipn g shb) = [Z_to_bv 8 0]); [| rewrite E in X; exact X].
rewrite forallb_forall in Z0.
destruct (nth_error shb g) as [b|] eqn:Hb; [| apply nth_error_None in Hb; lia].
assert (Hin : In b (firstn (g1 - g0) (skipn g0 shb))).
{ apply (nth_error_In _ (g - g0)). rewrite nth_error_firstn. destruct (Nat.ltb_spec (g - g0) (g1 - g0)); [| lia]. rewrite nth_error_skipn. replace (g0 + (g - g0))%nat with g by lia. exact Hb. }
specialize (Z0 b Hin). apply Z.eqb_eq in Z0.
pose proof (@nth_error_split _ shb g b Hb) as (l1 & l2 & E & Hl1). rewrite E. rewrite <- Hl1, skipn_app, skipn_all, Nat.sub_diag. cbn. f_equal. apply bv_eq. rewrite Z0. reflexivity. }
assert (E1 : (Fr + 8 * Z.of_nat g0) / 8 = Fr / 8 + Z.of_nat g0) by (Z.div_mod_to_equations; lia).
assert (E2 : (Fr + 8 * Z.of_nat g0 + 8 * Z.of_nat (g1 - g0) - 1) / 8 = Fr / 8 + Z.of_nat g1 - 1) by (Z.div_mod_to_equations; lia).
unfold unpoisoned. split; [lia|]. split; [| split].
- intros g Hgr. rewrite E1, E2 in Hgr. replace (g + A_SB) with (Fr / 8 + A_SB + Z.of_nat (Z.to_nat (g - Fr / 8))) by lia. apply GZ. lia.
- exists 0. split; [| left; reflexivity]. rewrite E2. replace (Fr / 8 + Z.of_nat g1 - 1 + A_SB) with (Fr / 8 + A_SB + Z.of_nat (g1 - 1)) by lia. apply GZ. lia.
- intros w Hw. rewrite E1, E2 in Hw.
assert (EW : exists j : nat, (j < 2)%nat /\ w * 8 = Fr / 8 + A_SB + Z.of_nat (8 * j)).
{ exists (Z.to_nat (w - (Fr / 8 + A_SB) / 8)). unfold A_SB in *. split; Z.div_mod_to_equations; lia. }
destruct EW as (j & Hj & ->). exists (firstn 8 (skipn (8 * j) shb)). split.
+ rewrite firstn_length_le; [reflexivity | rewrite length_skipn; lia].
+ apply Ql4f.Mq0.bytes_at_sub; [exact SH | lia].
Qed.
Section MDcArr.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Notation wz := (Z_to_bv 64).
Notation jroot_repA := (jroot_rep A4H A4F).
Notation presxD := (QYIF.heap_presxD A4H).
Hypothesis SHALLOW : shallow_A_stmt HIx.
Hypothesis PUT : put_stmt_A HIx.

Lemma presxD_own : forall D0 D' L0 L' SP SP' m m',
presxD D' L' SP' m m' -> SP' <= SP -> (forall b, In b L0 -> In b L') ->
(forall a, D' <= a < D' + 8 -> ~ client_addr A4H L0 SP a) -> presxD D0 L0 SP m m'.
Proof.
intros D0 D' L0 L' SP SP' m m' H HS HL N a Ha Hc _. apply (H a Ha).
- destruct Hc as [Hc | [Hc | (b & Hb & Hr)]]; [left; lia | right; left; exact Hc | right; right; exists b; split; [apply HL; exact Hb | exact Hr]].
- intros Hd. apply (N a Hd). exact (client_addrx_addr A4H _ _ _ _ Hc).
Qed.

Lemma presxD_agree_blocks : forall D0 L0 SP m m' BSx,
presxD D0 L0 SP m m' -> (forall b, In b BSx -> In b L0) -> (forall a k, In (a, k) BSx -> D0 + 8 <= a \/ a + k <= D0) -> agree_on asegs BSx m m'.
Proof.
intros D0 L0 SP m m' BSx H HL N a Ha (b & Hb & Hr). apply (H a Ha).
- right; right. exists b. split; [apply HL; exact Hb | exact Hr].
- destruct b as [ba bn]. cbn [blk_addr blk_size fst snd] in Hr. pose proof (N _ _ Hb). lia.
Qed.

Lemma arr_nowD : forall A LBa LMx FRS' B mc mdc m BSx px tojs pb a AL ps,
HEAPAx A LBa LMx FRS' B mc mdc -> agree_on asegs BSx m mc -> incl BSx LBa -> In (px, 48) BSx -> incl AL BSx ->
rw_cells asegs m px (jhdr_cells JT_ARRAY 1 tojs pb 0 0 ++ [C8 (wz a)]) -> alist asegs A4F m AL a ps ->
exists arr size,
rw_cells asegs mc px (jhdr_cells JT_ARRAY 1 tojs pb 0 0 ++ [C8 (wz a)]) /\ 0 < px /\ px + 48 <= alloc_ceiling /\ px mod 8 = 0 /\
ro_cells asegs mc (px / 8 + A_SB) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] /\
px / 8 + A_SB + 6 <= alloc_ceiling /\
alist asegs A4F mc [(a, AL_SZ); (arr, 8 * size)] a ps /\ al_blkA a arr size /\
ro_cells asegs mc (a / 8 + A_SB) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] /\
bytes_at asegs mc (arr / 8 + A_SB) (shadow_bytes (8 * size)) /\ 0 <= size /\ arr / 8 + A_SB + size <= alloc_ceiling /\
Z.of_nat (length ps) <= size /\ AL = [(a, AL_SZ); (arr, 8 * size)].
Proof.
intros A LBa LMx FRS' B mc mdc m BSx px tojs pb a AL ps HP AG INC INp INAL HDR HAL.
pose proof alloc_ceiling_range as ACR.
destruct (alist_open asegs A4F m AL a ps HAL) as (arr & size & junk & EAL & OP).
exists arr, size.
assert (INpA : In (px, 48) LBa) by (apply INC; exact INp).
assert (INaA : In (a, 32) LBa) by (apply INC, INAL; rewrite EAL; left; reflexivity).
assert (INrA : In (arr, 8 * size) LBa) by (apply INC, INAL; rewrite EAL; right; left; reflexivity).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ px 48 HP ltac:(apply in_or_app; left; exact INpA)) as (_ & Hpal & Hplo & Hphi & _).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ a 32 HP ltac:(apply in_or_app; left; exact INaA)) as (_ & Haal & Halo & Hahi & _).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ arr (8 * size) HP ltac:(apply in_or_app; left; exact INrA)) as (Hrn & Hral & Hrlo & Hrhi & _).
split.
{ eapply rw_cells_agree; [exact HDR | exact AG |]. exists px, 48. split; [exact INp|]. unfold jhdr_cells. cbn. lia. }
split; [exact Hplo|]. split; [exact Hphi|]. split; [clear - Hpal; Z.div_mod_to_equations; lia|].
split.
{ pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ px 48 HP INpA) as SH. unfold shad in SH. apply shadow_ro_cells in SH.
cbn [hl_sb hl_segs hla_base A4L A4H] in SH. exact SH. }
split; [unfold A_SB; clear - Hphi ACR Hplo; Z.div_mod_to_equations; lia|].
split.
{ rewrite EAL in HAL. eapply (alist_agree asegs A4F); [exact HAL | exact AG |]. intros b Hb. apply INAL. rewrite EAL. exact Hb. }
split.
{ unfold al_blkA. split; [exact Halo|]. split; [clear - Haal; Z.div_mod_to_equations; lia|]. split; [exact Hahi|]. split; [exact Hrlo|]. split; [clear - Hral; Z.div_mod_to_equations; lia | exact Hrhi]. }
split.
{ pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ a 32 HP INaA) as SH. unfold shad in SH. apply shadow_ro_cells in SH.
cbn [hl_sb hl_segs hla_base A4L A4H] in SH. exact SH. }
split.
{ pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ arr (8 * size) HP INrA) as SH. unfold shad in SH.
cbn [hl_sb hl_segs hla_base A4L A4H] in SH. exact SH. }
destruct OP as (_ & _ & _ & Hlen & Hsz).
split; [lia|]. split; [unfold A_SB; clear - Hrhi ACR Hrlo Hrn; Z.div_mod_to_equations; lia|]. split; [exact Hlen | exact EAL].
Qed.

Variables (ra sp gp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : config) (LB BS LM : list blk) (FRS : list frame) (B0 : bud) (lo p D w : Z) (r : jroot) (T : TSet).
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOS : lo <= bv_unsigned sp - dc_stkA (rdepth r).
Hypothesis SPA : bv_unsigned sp mod 32 = 0.
Hypothesis HT : bv_unsigned sp <= hiA_top A4L HIx.
Hypothesis RA : bv_unsigned ra mod 2 = 0.
Hypothesis FRM0 : frm0 fc.
Hypothesis DLOC : arg_locA FRS D 8.
Hypothesis DAL : D mod 8 = 0.
Hypothesis NN : r <> JRnull.
Hypothesis JR0 : jroot_repA r m0 BS p.
Hypothesis Kont : forall ms' md' m' rv (A' : ASA A4L HIx) (B' : bud),
jo_post_frameDA D ra sp gp (wz A_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 (BS ++ LB) (LM ++ fr_ivs A4L FRS) lo rv m' ms' md' ->
lh_globA m' -> jroot_repA r m' BS p -> dc_resA HIx r BS LB LM FRS D w B0 m' md' rv A' B' ->
AJ5 A4L HIx A' T md' ms'.
Local Notation fk1_HEAPA := (Qoif.Mq2.fk1_HEAPA HIx) (only parsing).
Local Notation fk1_pres := (Qoif.Mq2.fk1_pres HIx) (only parsing).
Local Notation ASP := (Qoif.Mq2.ASP sp) (only parsing).
Local Notation dc_save := (Qoif.Mq2.dc_save ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) (only parsing).
Local Notation dc_inv := (Qoif.Mq2.dc_inv ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 md0 LB BS LM FRS lo D) (only parsing).
Local Notation dc_dst := (Qoif.Mq2.dc_dst D) (only parsing).
Local Notation dc_dfacts := (Qoif.Mq2.dc_dfacts HIx ra sp LM FRS D DLOC DAL) (only parsing).
Local Notation dc_dst_munch := (Qoif.Mq2.dc_dst_munch HIx ra sp LM FRS lo D LO DLOC DAL) (only parsing).
Local Notation dc_dsh_range := (Qoif.Mq2.dc_dsh_range HIx ra sp LM FRS D DLOC) (only parsing).
Local Notation dc_dst_pres := (Qoif.Mq2.dc_dst_pres HIx ra sp LM FRS D DLOC) (only parsing).
Local Notation dc_epi := (Qoif.Mq2.dc_epi HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB BS LM FRS B0 lo p D w r T LO LOS HT DLOC NN JR0 Kont) (only parsing).
Local Notation dc_scr := (Qoif.Mq2.dc_scr p D) (only parsing).
Local Notation dc_tail0 := (Qoif.Mq2.dc_tail0 HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB BS LM FRS B0 lo p D w r T LO LOS HT DLOC DAL NN JR0 Kont) (only parsing).

Lemma da_src_agree : forall Ax LBx Bx mx mdx Fr mc mdc, HEAPAx Ax LBx LM ((Fr, 1) :: FRS) Bx mx mdx -> incl BS LBx -> dc_inv mc mdc -> agree_on asegs BS m0 mc.
Proof.
intros Ax LBx Bx mx mdx Fr mc mdc HP Hi (_ & PX & _).
destruct (dc_dfacts _ _ _ _ _ _ HP) as (_ & _ & _ & _ & DBLK & _).
eapply presxD_agree_blocks; [exact PX | intros b Hb; apply in_or_app; left; apply in_or_app; left; exact Hb |].
intros a0 k0 Hin. pose proof (DBLK a0 k0 ltac:(apply in_or_app; left; apply Hi; exact Hin)). lia.
Qed.
Lemma da_src_now : forall Ax LBx Bx mx mdx Fr mc mdc, HEAPAx Ax LBx LM ((Fr, 1) :: FRS) Bx mx mdx -> incl BS LBx -> dc_inv mc mdc -> jroot_repA r mc BS p.
Proof.
intros Ax LBx Bx mx mdx Fr mc mdc HP Hi INV.
exact (QrIB.Mq0.jroot_rep_agree A4H A4F _ _ _ _ _ _ JR0 (da_src_agree _ _ _ _ _ _ _ _ HP Hi INV) (incl_refl _)).
Qed.

Notation own_W Fr := [(lo, bv_unsigned sp + -104); (Fr, Fr + 120); (Fr / 8 + 2147450880, Fr / 8 + 2147450880 + 16); (6434236, 6434240)].
Lemma dc_inv_own : forall Ax LBx Bx mx mdx Fr mc',
HEAPAx Ax LBx LM ((Fr, 1) :: FRS) Bx mx mdx -> incl (BS ++ LB) LBx ->
munch (own_W Fr) mx mc' -> wmono asegs mx mc' ->
dc_inv mx mdx -> stk asegs mc' lo ASP -> dc_save mc' -> dc_inv mc' mdx.
Proof.
intros Ax LBx Bx mx mdx Fr mc' HP Hi MU WM (VM & PX & _ & _ & G) ST SV.
pose proof LOS as LOSu. unfold dc_stkA, DC_F, DC_C in LOSu.
assert (RD0 : 0 <= rdepth r) by (destruct r; cbn [rdepth]; try lia; apply sdepth_nonneg).
pose proof (fk1_pres _ _ _ _ _ _ _ _ lo (bv_unsigned sp + -104) _ HP LO ltac:(lia) MU WM) as HPR.
split; [exact VM|]. split; [| split; [exact ST | split; [exact SV | eapply lh_globA_client; [exact HPR | exact G]]]].
eapply (QrIB.Mq0.presxD_trans A4H); [exact PX |]. apply (QrIB.Mq0.pres_presxD A4H). eapply heap_pres_weaken; [exact HPR | lia |].
intros b Hb. apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; apply Hi; exact Hb | apply in_or_app; right; exact Hb].
Qed.

Lemma da_own_outside : forall Ax LBx Bx mx mdx Fr x,
HEAPAx Ax LBx LM ((Fr, 1) :: FRS) Bx mx mdx -> incl (BS ++ LB) LBx -> 0 <= x < 2^64 -> Fr <= x < Fr + 120 ->
~ client_addr A4H ((BS ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) x.
Proof.
intros Ax LBx Bx mx mdx Fr x HP Hi Ha Hr Hc.
pose proof LOS as LOSu. unfold dc_stkA, DC_F, DC_C in LOSu.
assert (RD0 : 0 <= rdepth r) by (destruct r; cbn [rdepth]; try lia; apply sdepth_nonneg).
assert (INF : In (Fr, 1) ((Fr, 1) :: FRS)) by (left; reflexivity).
destruct (own_frame_fresh HIx Fr 1 LBx (BS ++ LB) LM FRS Bx Ax _ mdx HP Hi) as [OFF OFS].
assert (Ho : outside [(Fr, Fr + 120)] x).
{ eapply (Q1Ey.client_outsideF HIx Ax LBx LM ((Fr, 1) :: FRS) Bx ((BS ++ LB) ++ LM ++ fr_ivs A4L FRS) _ mdx [(Fr, Fr + 120)] (bv_unsigned sp) HP); [| lia | | exact Ha | exact Hc].
- intros b Hb. apply in_app_or in Hb as [Hb | Hb]; [left; apply in_or_app; left; apply Hi; exact Hb |].
apply in_app_or in Hb as [Hb | Hb]; [left; apply in_or_app; right; exact Hb | right; cbn [fr_ivs flat_map app]; right; right; exact Hb].
- apply Forall_cons; [| apply Forall_nil]. right; right; right. exists Fr, 1. split; [exact INF|]. split; [exact OFF|]. split; [exact OFS|]. left. cbn [fst snd]. rewrite fr_size_1. lia. }
cbn [outside] in Ho. lia.
Qed.

Lemma dc_dst_presxD : forall Ax LBx Bx mx mdx Fr D' L0 SP mc m' q,
HEAPAx Ax LBx LM ((Fr, 1) :: FRS) Bx mx mdx -> Fr <= D' -> D' + 8 <= Fr + 120 -> dc_dst mc q ->
presxD D' (L0 ++ LM ++ fr_ivs A4L ((Fr, 1) :: FRS)) SP mc m' -> dc_dst m' q.
Proof.
intros Ax LBx Bx mx mdx Fr D' L0 SP mc m' q HP HD1 HD2 [DC DSH] PX.
destruct (dc_dfacts _ _ _ _ _ _ HP) as (D1 & D2 & D3 & D4 & _ & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13).
destruct DLOC as (Fd & kd & HFd & H1 & H2).
assert (IND : In (Fd, kd) ((Fr, 1) :: FRS)) by (right; exact HFd).
split.
- eapply (QrIB.Mq0.presxD_rw_cells A4H); [exact PX | exact DC | | cbn [cells_size csize Nat.add]; lia].
eapply client_rangex_block; [apply in_or_app; right; apply in_or_app; right; apply fr_ivs_frame; exact IND | cbn; lia | cbn; lia].
- destruct DSH as [Hwf Hb]. split; [exact Hwf|].
eapply (QrIB.Mq0.presxD_bytes_at A4H); [exact PX | exact Hb | cbn [cells_bytes cbytes app length]; exact (dc_dsh_range _ _ _ _ _ _ (hl_volatile A4H) L0 SP HP) |].
cbn [cells_bytes cbytes app length]. clear - D8 D9 D10 HD1 HD2. lia.
Qed.

Variable kids : list (option jshape).
Hypothesis Er : r = JRtree (Sarr kids).
Hypothesis FRN : Z.of_nat (length FRS) + (1 + rdepth r) < 4096.
Hypothesis IH : forall s', In (Some s') kids -> DCOPY HIx (JRtree s').
Variables (pb a : Z) (PBS AL : list blk) (ps : list Z) (KBS : list (list blk)) (ws : list Z).
Hypothesis EBS : BS = ((p, 48) :: AL ++ concat KBS) ++ PBS.
Hypothesis OPB0 : opt_pbuf asegs m0 PBS pb.
Hypothesis HDR0 : rw_cells asegs m0 p (jhdr_cells JT_ARRAY 1 (fn_arr_to_json_string A4F) pb 0 0 ++ [C8 (wz a)]).
Hypothesis HAL0 : alist asegs A4F m0 AL a ps.
Hypothesis L1 : length ps = length kids.
Hypothesis L2 : length KBS = length kids.
Hypothesis KIDS0 : akids asegs A4F m0 kids ps KBS.
Hypothesis LW : length ws = length kids.
Hypothesis EW : w = 24 + arr_wsum ws.
Hypothesis NNW : Forall (fun x => 0 <= x) ws.
Hypothesis KW1 : forall i s bs, nth_error kids i = Some (Some s) -> nth_error KBS i = Some bs -> exists Yi Ri, jtx s (bs ++ Yi) = Some (nth i ws 0, Ri).
Hypothesis KW2 : forall i, nth_error kids i = Some None -> nth i ws 0 = NULL_W.
Hypothesis WLT : w < 2^28.
Hypothesis BBW : DC_KB * w <= bB B0.
Hypothesis BDW : w <= bD B0.

Definition da_own (mc : word -> option byte) (Fr : Z) (v2 : word) (b8 : Z) : Prop :=
exists (j24 j16 jf1 jf2 : list byte) (w1 w2 : word),
rw_cells asegs mc ASP (dc_scr Fr (wz 0) (CB 8 j24) j16) /\
rw_cells asegs mc Fr [C8 (wz 1102416563); C8 w1; C8 w2; CB 40 jf1; C8 v2; CB 48 jf2] /\
rw_cells asegs mc (Fr / 8 + 2147450880) [C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242);
C1 (Z_to_bv 8 b8); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].

Lemma dc_arr_fail :
forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x19 x21 x22 x23 x24 x26 x27 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
(mc : word -> option byte) (mdc : config) (A : ASA A4L HIx) (Bc : bud) (Fr v2 q : Z) (VBS CBS REM : list blk),
dc_inv mc mdc -> fsaved F F1 -> frm0 fc1 ->
HEAPAx A (BS ++ CBS ++ VBS ++ REM ++ LB) LM ((Fr, 1) :: FRS) Bc mc mdc ->
da_own mc Fr (wz v2) 0 -> fresA mc VBS v2 -> jroot_repA r mc BS p ->
dc_dst mc q -> fresA mc CBS q ->
bD B0 - w <= bD Bc -> bB B0 - DC_KB * w + 512 * (Z.of_nat (length CBS) + Z.of_nat (length VBS)) <= bB Bc ->
AJ5 A4L HIx A T mdc
(MS (mkR x1 (wz ASP) gp (wz A_TP) t0 t1 t2 sp (wz ASP) a0 a1 a2 a3 a4 a5 a6 a7
(wz (Fr / 8 + 2147450880)) x19 (wz 2147450880) x21 x22 x23 x24 (wz (Fr + 64)) x26 x27 t3 t4 t5 t6)
F1 (wz 0x9fcc8) fc1 None mc (seg_rom asegs)).
Proof.
intros until REM. intros INV FS FRM1 HP (j24 & j16 & jf1 & jf2 & w1 & w2 & SCR & FF & FSH) FRV JRc DD FRC BDc BBc.
pose proof INV as (VMi & PRESi & STi & SAVEi & Gi). unfold dc_save in SAVEi.
pose proof LOS as LOSu. unfold dc_stkA, DC_F, DC_C in LOSu. unfold ASP, dc_scr in *.
assert (RD0 : 0 <= rdepth r) by (destruct r; cbn [rdepth]; try lia; apply sdepth_nonneg).
pose proof alloc_ceiling_range as ACR.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
destruct (dc_dfacts _ _ _ _ _ _ HP) as (D1 & D2 & D3 & D4 & DBLK & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13).
set (sh := Fr / 8 + 2147450880) in *.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. change (hl_segs A4L) with asegs in MI.
destruct (heapA_errno A4L HIx _ _ _ _ _ _ _ HP) as (errs & ERRs).
pose proof (wmono_refl asegs mc) as WM. pose proof (munch_refl [(lo, bv_unsigned sp + -104); (Fr, Fr + 120); (sh, sh + 16); (6434236, 6434240)] mc) as MU.

assert (PP : exists so, QPZI.Mq4.put_pre A4H A4F so mc VBS v2 1).
{ destruct FRV as [[-> ->] | (Hv & s & JV)]; [exists None; split; reflexivity | exists (Some s); split; [exact Hv | split; [lia | exact JV]]]. }
destruct PP as (so & PP).
assert (HPp : HEAPAx A (VBS ++ (BS ++ CBS ++ REM ++ LB)) LM ((Fr, 1) :: FRS) Bc mc mdc).
{ eapply (heapA_perm A4L HIx); [exact HP | perm | apply Permutation_refl | apply Permutation_refl]. }
assert (V2R : 0 <= v2 < 2^64).
{ destruct FRV as [[-> _] | (Hv & s & JV)]; [lia|]. destruct (jval_root_in asegs A4F _ _ _ _ _ JV) as (n & Hin & Hn).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ v2 n HPp ltac:(apply in_or_app; left; apply in_or_app; left; exact Hin)) as (_ & _ & Hlo & Hhi & _). unfold alloc_ceiling, sp_window_lo, stack_max_size in Hhi. lia. }
stash PRESi. stash Gi. stash FRC. stash JRc. stash DD.
unfold A_TP. a4l.
reenterA asegs A4L HIx asegs_wx HP.
step. step.

assert (PC : put_costA so 1 VBS <= bB Bc).
{ unfold put_costA. destruct so; [change (1 =? 1) with true; cbv iota|]; unfold DC_KB in *; lia. }
evt_done5.
eapply PUT with (LB := BS ++ CBS ++ REM ++ LB) (LM := LM) (FRS := (Fr, 1) :: FRS) (B := Bc) (lo := lo) (errv := errs) (s := so) (BS := VBS) (p := v2) (rc := 1);
[ exact HPp | exact PP | reflexivity | rewrite unsigned_lit by lia; exact STi | exact LO | rewrite unsigned_lit by lia; unfold put_stk_A; lia
| rewrite unsigned_lit by lia; clear - SPA; Z.div_mod_to_equations; lia | rewrite unsigned_lit by lia; lia | exact ERRs | reflexivity | reflexivity | exact PC | ].
intros ms2 md2 A2 (m2 & rr & B2 & RS2 & VM2 & ST2 & HPR2 & ERR2 & BB2 & BD2 & OUT2).
destruct RS2 as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & F2 & fc2 & -> & FS2 & FRM2).

destruct OUT2 as [[_ HP2] | (s' & _ & Habs & _)]; [| exfalso; lia].
rewrite ?(unsigned_lit (bv_unsigned sp + -192)) in ST2 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -192)) in HPR2 by lia.
change (hl_segs A4L) with asegs in *.
assert (HPRX : forall A0 cs0, rw_cells asegs mc A0 cs0 ->
client_range A4H ((BS ++ CBS ++ REM ++ LB) ++ LM ++ fr_ivs A4L ((Fr, 1) :: FRS)) (bv_unsigned sp + -192) A0 (Z.of_nat (cells_size cs0)) -> rw_cells asegs m2 A0 cs0).
{ intros A0 cs0 H1 H2. exact (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2 H1 H2). }
apply HPRX in SCR; [| left; lia]. apply HPRX in SAVEi; [| left; lia].
apply HPRX in FF; [| eapply client_range_block; [apply in_or_app; right; apply in_or_app; right; left; reflexivity | cbn [fr_base fst]; lia | cbn [cells_size csize Nat.add fr_base fr_class fst snd]; rewrite fr_size_1; lia]].
apply HPRX in FSH; [| eapply client_range_block; [apply in_or_app; right; apply in_or_app; right; right; left; reflexivity | unfold shad; cbn [fr_base fst hl_sb A4L]; unfold A_SB; fold sh; lia
| unfold shad; cbn [cells_size csize Nat.add fr_base fr_class fst snd hl_sb A4L]; rewrite fr_shadow_len_1; unfold A_SB; fold sh; lia]].
unstash DD. pose proof (dc_dst_pres _ _ _ _ _ _ _ _ _ _ _ HP2 DD HPR2) as DD2. clear DD HPRX. stash DD2.
clear MU WM MI.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI2. change (hl_segs A4L) with asegs in MI2.
pose proof (wmono_refl asegs m2) as WM2. pose proof (munch_refl [(lo, bv_unsigned sp + -104); (Fr, Fr + 120); (sh, sh + 16); (6434236, 6434240)] m2) as MU2.
replace (ret_pc (wz 654544)) with (wz 654544) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
stash SAVEi.
reenterA asegs A4L HIx asegs_wx HP2.
step. stepz. step. step. step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) => rename mq into mX end.
pose proof (fk1_HEAPA _ _ _ _ _ _ _ _ lo (bv_unsigned sp + -104) _ HP2 LO ltac:(lia) MU2 WM2 MI2) as HPY.
pose proof (fk1_pres _ _ _ _ _ _ _ _ lo (bv_unsigned sp + -104) _ HP2 LO ltac:(lia) MU2 WM2) as HPR2X.
unstash SAVEi. apply (rw_cells_transport asegs [(lo, bv_unsigned sp + -104); (Fr, Fr + 120); (sh, sh + 16); (6434236, 6434240)] _ mX) in SAVEi; [| exact MU2 | exact WM2 | cbn [disjoint_from]; simpl_sizes; lia].
unstash DD2. pose proof (dc_dst_munch _ _ _ _ _ _ _ _ _ HP2 DD2 MU2 WM2) as [DCX DSHX].
assert (HPRcX : heap_pres A4H ((BS ++ CBS ++ REM ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) mc mX).
{ eapply heap_pres_trans; [eapply heap_pres_weaken; [exact HPR2 | lia |] | eapply heap_pres_weaken; [exact HPR2X | lia | intros b Hb; exact Hb]].
intros b Hb. apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; exact Hb | apply in_or_app; right].
apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; exact Hb | apply in_or_app; right; cbn [fr_ivs flat_map app]; right; right; exact Hb]. }
assert (AGX : forall BSx, incl BSx (BS ++ CBS ++ REM ++ LB) -> agree_on asegs BSx mc mX).
{ intros BSx Hi. eapply (agree_of_heap_pres asegs A4H); [exact HPRcX | reflexivity | intros b Hb; apply in_or_app; left; apply Hi; exact Hb]. }
unstash JRc. unstash PRESi. unstash Gi. unstash FRC.
evt_done5.
replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 (2^64 - 1)) by (apply bv_eq; vm_compute; reflexivity).
eapply (dc_epi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F2 fc2 mX md2 A2 B2 (BS ++ CBS ++ REM ++ LB) Fr (2^64 - 1)).
- split; [eapply model_vm_only_trans; [exact VMi | exact VM2] |].
split; [eapply (QrIB.Mq0.presxD_trans A4H); [exact PRESi |]; apply (QrIB.Mq0.pres_presxD A4H); eapply heap_pres_weaken; [exact HPRcX | lia |] |].
{ intros b Hb. apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left | apply in_or_app; right; exact Hb].
apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; exact Hb | apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; exact Hb]. }
split; [exact ST2 |].
split; [unfold dc_save; exact SAVEi |]. eapply lh_globA_client; [exact HPRcX | exact Gi].
- eapply fsaved_trans; [exact FS | exact FS2].
- apply FRM2. exact FRM1.
- exact HPY.
- exact SCR.
- reflexivity.
- exact FF.
- reflexivity.
- exact FSH.
- eapply (QrIB.Mq0.jroot_rep_agree A4H A4F); [exact JRc | apply (AGX BS); apply incl_appl; apply incl_refl | apply incl_refl].
- split; [lia|]. right. split; [reflexivity|]. exists q, CBS, REM. split; [reflexivity|]. split; [exact DCX|].
split; [eapply fresA_agree; [exact FRC | apply (AGX CBS); apply incl_appr; apply incl_appl; apply incl_refl | apply incl_refl] |].
assert (VL : put_costA so 1 VBS <= 512 * Z.of_nat (length VBS)) by (unfold put_costA; destruct so; [change (1 =? 1) with true; cbv iota; lia | destruct PP as [_ ->]; cbn; lia]).
lia.
Qed.

Lemma dc_arr_add :
forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x19 x21 x22 x23 x24 x26 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
(mc : word -> option byte) (mdc : config) (A : ASA A4L HIx) (Bc : bud) (Fr v q : Z) (kids' : list (option jshape)) (vs : option jshape) (VBS CBS REM : list blk),
dc_inv mc mdc -> fsaved F F1 -> frm0 fc1 ->
HEAPAx A (BS ++ CBS ++ VBS ++ REM ++ LB) LM ((Fr, 1) :: FRS) Bc mc mdc ->
da_own mc Fr (wz v) 0 -> jroot_repA r mc BS p ->
q <> 0 -> dc_dst mc q -> jval asegs A4F (Sarr kids') mc CBS q 1 -> jopt asegs A4F vs mc VBS v ->
Z.of_nat (length kids') + 1 < 2^28 ->
bD B0 - w <= bD Bc ->
bB B0 - DC_KB * w + 512 * (Z.of_nat (length CBS) + Z.of_nat (length VBS)) + arr_add_costA (arr_capA CBS) (Z.of_nat (length kids')) <= bB Bc ->
(forall (y1 u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 : word) (F2 : bvmap 5 word) (fc2 : bv 32)
(m2 : word -> option byte) (md2 : config) (A2 : ASA A4L HIx) (B2 : bud) (CBS' : list blk),
dc_inv m2 md2 -> fsaved F F2 -> frm0 fc2 ->
HEAPAx A2 (BS ++ CBS' ++ REM ++ LB) LM ((Fr, 1) :: FRS) B2 m2 md2 ->
da_own m2 Fr (wz v) 0 -> jroot_repA r m2 BS p ->
dc_dst m2 q -> jval asegs A4F (Sarr (kids' ++ [vs])) m2 CBS' q 1 ->
Z.of_nat (length CBS') = Z.of_nat (length CBS) + Z.of_nat (length VBS) ->
arr_grownA (arr_capA CBS) (Z.of_nat (length kids')) (arr_capA CBS') ->
bB Bc - arr_add_costA (arr_capA CBS) (Z.of_nat (length kids')) <= bB B2 -> bD Bc <= bD B2 ->
(forall wq wv, jtx (Sarr kids') CBS = Some (wq, []) -> jtx_opt vs VBS = Some (wv, []) -> jtx (Sarr (kids' ++ [vs])) CBS' = Some (wq + (2 + wv), [])) ->
AJ5 A4L HIx A2 T md2
(MS (mkR y1 (wz ASP) gp (wz A_TP) u0 u1 u2 sp (wz ASP) (wz 0) b1 b2 b3 b4 b5 b6 b7
(wz (Fr / 8 + 2147450880)) x19 (wz 2147450880) x21 x22 x23 x24 (wz (Fr + 64)) x26 (wz (D / 8 + 2147450880)) u3 u4 u5 u6)
F2 (wz 0x9fb9c) fc2 None m2 (seg_rom asegs))) ->
AJ5 A4L HIx A T mdc
(MS (mkR x1 (wz ASP) gp (wz A_TP) t0 t1 t2 sp (wz ASP) a0 a1 a2 a3 a4 a5 a6 a7
(wz (Fr / 8 + 2147450880)) x19 (wz 2147450880) x21 x22 x23 x24 (wz (Fr + 64)) x26 (wz (D / 8 + 2147450880)) t3 t4 t5 t6)
F1 (wz 0x9fb70) fc1 None mc (seg_rom asegs)).
Proof.
intros until REM. intros INV FS FRM1 HP OWN JRc Hq DD JQ JOB Hlen28 BDc BBc KADD.
pose proof OWN as (j24 & j16 & jf1 & jf2 & w1 & w2 & SCR & FF & FSH).
pose proof INV as (VMi & PRESi & STi & SAVEi & Gi). unfold dc_save in SAVEi.
pose proof LOS as LOSu. unfold dc_stkA, DC_F, DC_C in LOSu. unfold ASP, dc_scr in *.
assert (RD0 : 0 <= rdepth r) by (destruct r; cbn [rdepth]; try lia; apply sdepth_nonneg).
pose proof alloc_ceiling_range as ACR.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
destruct (dc_dfacts _ _ _ _ _ _ HP) as (D1 & D2 & D3 & D4 & DBLK & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13).
pose proof DD as [DC DSH]. pose proof (rw_cells_bound asegs mc D _ DC) as DR. cbn [cells_size csize Nat.add] in DR.
set (sh := Fr / 8 + 2147450880) in *.

pose proof (arr_capA_jval _ _ _ _ _ JQ) as (a_ & arr_ & rest_ & EABS & Hcap1 & Hcap2 & Hcap3).
destruct (sarr_open asegs A4F _ _ _ _ _ JQ) as (pbq & PBSq & qa & ALq & psq & KBSq & ECBS & OPBq & HDRq & HALq & Lq1 & Lq2 & KIDSq).
pose proof HALq as (qarr & cap & ajunk & EALq & Hlenq & Hszq & _). subst ALq.
assert (Ecap : cap = arr_capA CBS /\ a_ = qa /\ arr_ = qarr) by (rewrite EABS in ECBS; cbn [app] in ECBS; injection ECBS; intros; lia).
destruct Ecap as (Ecap & -> & ->). rewrite <- Ecap in *. clear EABS rest_ Hcap1 Hcap2 Hcap3.
set (LBR := (q, 48) :: concat KBSq ++ PBSq ++ VBS ++ BS ++ REM ++ LB).
assert (HPa : HEAPAx A ((qa, 32) :: (qarr, 8 * cap) :: LBR) LM ((Fr, 1) :: FRS) Bc mc mdc).
{ eapply (heapA_perm A4L HIx); [exact HP | rewrite ECBS; unfold LBR; perm | apply Permutation_refl | apply Permutation_refl]. }

assert (INq : In (q, 48) LBR) by (left; reflexivity).
assert (HiK : incl (concat KBSq) LBR) by (intros b Hb; right; apply in_or_app; left; exact Hb).
assert (HiP : incl PBSq LBR) by (intros b Hb; right; apply in_or_app; right; apply in_or_app; left; exact Hb).
assert (HiV : incl VBS LBR) by (intros b Hb; right; apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; exact Hb).
assert (HiB : incl BS LBR) by (intros b Hb; right; apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; exact Hb).
assert (Hv : 0 <= v /\ v + 1 <= alloc_ceiling).
{ destruct vs as [s'|]; cbn in JOB.
- destruct JOB as [Hv0 J]. destruct (jval_root_in asegs A4F _ _ _ _ _ J) as (n & Hin & Hn).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ v n HPa ltac:(apply in_or_app; left; right; right; apply HiV; exact Hin)) as (_ & _ & Hlo & Hhi & _). lia.
- destruct JOB as [-> _]. unfold alloc_ceiling, sp_window_lo, stack_max_size. lia. }
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hv.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. change (hl_segs A4L) with asegs in MI.
destruct (heapA_errno A4L HIx _ _ _ _ _ _ _ HP) as (errs & ERRs).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ q 48 HPa ltac:(apply in_or_app; left; right; right; exact INq)) as (_ & Hqal & Hqlo & Hqhi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hqhi.
pose proof (blk_gran0A HIx _ _ _ _ _ _ _ q 48 5 HPa ltac:(right; right; exact INq) ltac:(lia) ltac:(lia)) as SHq5.
replace (q / 8 + 2147450880 + 5) with (q / 8 + 2147450885) in SHq5 by lia.
unfold jhdr_cells in HDRq. cbn [app] in HDRq.
pose proof (wmono_refl asegs mc) as WM. pose proof (munch_refl [(lo, bv_unsigned sp + -104); (Fr, Fr + 120); (sh, sh + 16); (6434236, 6434240)] mc) as MU.
stash PRESi. stash Gi. stash JRc. stash JQ. stash JOB. stash OPBq. stash KIDSq. stash HALq. stash KADD. stash OWN. stash INV. stash DD.
unfold A_TP. a4l.
reenterA asegs A4L HIx asegs_wx HP.
step. step. step. asan_chkA.
step. step. step.

unstash HALq.
assert (BBadd : cap <= Z.of_nat (length psq) + 1 -> al_add_costB cap <= bB Bc).
{ intros Hge. unfold al_add_costB, arr_add_costA in *. rewrite Lq1 in Hge. destruct (Z.ltb_spec (Z.of_nat (length kids') + 1) cap); [lia|]. unfold DC_KB in *. lia. }
evt_done5.
eapply (array_list_add_A_cps HIx (wz 654232) (wz (bv_unsigned sp + -192)) gp sp (wz (bv_unsigned sp + -192)) (wz sh) x19 (wz 2147450880) x21 x22 x23 x24 (wz (Fr + 64)) x26 (wz (D / 8 + 2147450880))
F1 fc1 mc mdc LBR LM ((Fr, 1) :: FRS) Bc lo qa qarr cap v psq T);
[ exact HPa | exact HALq | rewrite Lq1; lia | lia
| rewrite unsigned_lit by lia; exact STi | exact LO | rewrite unsigned_lit by lia; lia
| rewrite unsigned_lit by lia; clear - SPA; Z.div_mod_to_equations; lia | rewrite unsigned_lit by lia; lia
| exact ERRs | reflexivity | reflexivity | reflexivity | exact BBadd | exact (proj2 (heapA_budget A4L HIx _ _ _ _ _ _ _ HP)) | ].
intros ms' md' A' (m' & rr & errv' & arr' & size' & B' & RS & VM' & ST' & HPR' & ERR' & BD' & HP' & OUT).
destruct RS as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & F2 & fc2 & -> & FS2 & FRM2).
rewrite ?(unsigned_lit (bv_unsigned sp + -192)) in ST', HPR' by lia.
change (hl_segs A4L) with asegs in *.
assert (AG : agree_on asegs LBR mc m') by (eapply (agree_of_heap_pres asegs A4H); [exact HPR' | reflexivity | intros b Hb; apply in_or_app; left; exact Hb]).
assert (HPRX : forall A0 cs0, rw_cells asegs mc A0 cs0 ->
client_range A4H (LBR ++ LM ++ fr_ivs A4L ((Fr, 1) :: FRS)) (bv_unsigned sp + -192) A0 (Z.of_nat (cells_size cs0)) -> rw_cells asegs m' A0 cs0).
{ intros A0 cs0 H1 H2. exact (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR' H1 H2). }
apply HPRX in SCR; [| left; lia]. apply HPRX in SAVEi; [| left; lia].
apply HPRX in FF; [| eapply client_range_block; [apply in_or_app; right; apply in_or_app; right; left; reflexivity | cbn [fr_base fst]; lia | cbn [cells_size csize Nat.add fr_base fr_class fst snd]; rewrite fr_size_1; lia]].
apply HPRX in FSH; [| eapply client_range_block; [apply in_or_app; right; apply in_or_app; right; right; left; reflexivity | unfold shad; cbn [fr_base fst hl_sb A4L]; unfold A_SB; fold sh; lia
| unfold shad; cbn [cells_size csize Nat.add fr_base fr_class fst snd hl_sb A4L]; rewrite fr_shadow_len_1; unfold A_SB; fold sh; lia]].
apply HPRX in HDRq; [| eapply client_range_block; [apply in_or_app; left; exact INq | lia | cbn [cells_size csize Nat.add]; lia]].
unstash DD. pose proof (dc_dst_pres _ _ _ _ _ _ _ _ _ _ _ HP DD HPR') as DD'. clear HPRX.
unstash JRc. pose proof (QrIB.Mq0.jroot_rep_agree A4H A4F _ _ _ _ _ _ JRc AG HiB) as JRc'.
unstash PRESi. unstash Gi.
assert (INV' : dc_inv m' md').
{ split; [eapply model_vm_only_trans; [exact VMi | exact VM'] |].
split; [eapply (QrIB.Mq0.presxD_trans A4H); [exact PRESi |]; apply (QrIB.Mq0.pres_presxD A4H); eapply heap_pres_weaken; [exact HPR' | lia |] |].
{ intros b Hb. apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left | apply in_or_app; right].
- apply in_app_or in Hb as [Hb | Hb]; [apply HiB; exact Hb |]. unfold LBR. right. apply in_or_app; right. apply in_or_app; right. apply in_or_app; right. apply in_or_app; right. apply in_or_app; right. exact Hb.
- apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; exact Hb | apply in_or_app; right; cbn [fr_ivs flat_map app]; right; right; exact Hb]. }
split; [exact ST' |]. split; [unfold dc_save; exact SAVEi |]. eapply lh_globA_client; [exact HPR' | exact Gi]. }
assert (OWN' : da_own m' Fr (wz v) 0) by (exists j24, j16, jf1, jf2, w1, w2; split; [exact SCR | split; [exact FF | exact FSH]]).
unstash OPBq. unstash KIDSq. unstash JOB.
pose proof (opt_pbuf_agree _ _ _ _ _ _ OPBq AG HiP) as OPBq'.
pose proof (akids_agree _ _ _ _ _ _ _ _ KIDSq AG HiK) as KIDSq'.
pose proof (jopt_agree _ _ _ _ _ _ _ _ JOB AG HiV) as JOB'.

destruct OUT as [(-> & -> & -> & Hgr & BBf & AL') | (-> & AL' & CASES)].
-
assert (JQ' : jval asegs A4F (Sarr kids') m' CBS q 1).
{ eapply (sarr_close asegs A4F) with (AL := [(qa, 32); (qarr, 8 * cap)]) (KBS := KBSq) (PBS := PBSq) (pb := pbq) (a := qa) (ps := psq);
[exact ECBS | exact OPBq' | unfold jhdr_cells; cbn [app]; exact HDRq | exact AL' | exact Lq1 | exact Lq2 | exact KIDSq']. }
assert (HPf : HEAPAx A' (BS ++ CBS ++ VBS ++ REM ++ LB) LM ((Fr, 1) :: FRS) B' m' md').
{ eapply (heapA_perm A4L HIx); [exact HP' | rewrite ECBS; unfold LBR; perm | apply Permutation_refl | apply Permutation_refl]. }
replace (ret_pc (wz 654232)) with (wz 654232) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
reenterA asegs A4L HIx asegs_wx HPf.
step. if_lit.
evt_done5.
eapply dc_arr_fail with (v2 := v) (q := q) (VBS := VBS) (CBS := CBS) (REM := REM);
[ exact INV' | eapply fsaved_trans; [exact FS | exact FS2] | apply FRM2; exact FRM1 | exact HPf | exact OWN'
| destruct vs as [s'|]; [right; destruct JOB' as [Hv0 J]; split; [exact Hv0 | exists s'; exact J] | left; exact JOB']
| exact JRc' | exact DD' | right; split; [exact Hq | exists (Sarr kids'); exact JQ'] | lia | ].
unfold al_add_costB, arr_add_costA in *. rewrite Lq1 in Hgr. destruct (Z.ltb_spec (Z.of_nat (length kids') + 1) cap); lia.

-
set (CBS' := ((q, 48) :: [(qa, 32); (arr', 8 * size')] ++ concat (KBSq ++ [VBS])) ++ PBSq).
assert (JQ' : jval asegs A4F (Sarr (kids' ++ [vs])) m' CBS' q 1).
{ eapply (sarr_close asegs A4F) with (ps := psq ++ [v]); [reflexivity | exact OPBq' | unfold jhdr_cells; cbn [app]; exact HDRq | exact AL' | | |].
- rewrite !length_app. cbn [length]. lia.
- rewrite !length_app. cbn [length]. lia.
- apply akids_app; [exact KIDSq' | apply akids_one; exact JOB']. }
assert (HPs : HEAPAx A' (BS ++ CBS' ++ REM ++ LB) LM ((Fr, 1) :: FRS) B' m' md').
{ unfold CBS'. rewrite concat_app. cbn [concat]. rewrite app_nil_r.
eapply (heapA_perm A4L HIx); [exact HP' | unfold LBR; perm | apply Permutation_refl | apply Permutation_refl]. }
replace (ret_pc (wz 654232)) with (wz 654232) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
reenterA asegs A4L HIx asegs_wx HPs.
step. if_lit.
evt_done5. unstash KADD.
eapply (KADD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F2 fc2 m' md' A' B' CBS');
[ exact INV' | eapply fsaved_trans; [exact FS | exact FS2] | apply FRM2; exact FRM1 | exact HPs | exact OWN' | exact JRc' | exact DD' | exact JQ' | | | | exact BD' | ].
+ unfold CBS'. rewrite ECBS. rewrite concat_app. cbn [concat]. rewrite app_nil_r. rewrite ?length_app. cbn [length]. rewrite ?length_app. cbn [length]. clear. Zify.zify. unfold blk in *. lia.
+ unfold arr_grownA, arr_capA, CBS'. cbn [app nth snd]. rewrite ?Lq1 in CASES.
destruct CASES as [(-> & -> & Hlt & _) | (-> & Hge & _)]; [left | right]; Z.div_mod_to_equations; lia.
+ unfold al_add_costB, arr_add_costA in *. rewrite ?Lq1 in CASES.
destruct (Z.ltb_spec (Z.of_nat (length kids') + 1) cap); destruct CASES as [(_ & _ & Hlt & BBx) | (_ & Hge & BBx)]; lia.
+ intros wq wv Hw Hwv. unstash KIDSq. rewrite ECBS in Hw.
exact (arr_add_jtx asegs A4F mc kids' psq KBSq PBSq (q, 48) (qa, 32) (qarr, 8 * cap) (arr', 8 * size') vs VBS wq wv KIDSq Hw Hwv).
Qed.

Definition da_copy (mc : word -> option byte) (Bc : bud) (ii : nat) (q : Z) (CBS : list blk) (acc : Z) : Prop :=
exists (kids' : list (option jshape)) (wq : Z),
q <> 0 /\ dc_dst mc q /\ jval asegs A4F (Sarr kids') mc CBS q 1 /\ length kids' = ii /\ okmax kids' <= okmax kids /\
jtx (Sarr kids') CBS = Some (wq, []) /\ wq <= acc /\
arr_inv (arr_capA CBS) (Z.of_nat ii) /\
bD B0 - acc <= bD Bc /\ bB B0 - DC_KB * acc + 512 * Z.of_nat (length CBS) + PhiA (arr_capA CBS) (Z.of_nat ii) <= bB Bc.

Lemma da_copy_own : forall Ax LBx Bx mx mdx Fr mc' Bc ii q CBS acc,
HEAPAx Ax LBx LM ((Fr, 1) :: FRS) Bx mx mdx -> incl CBS LBx ->
munch (own_W Fr) mx mc' -> wmono asegs mx mc' ->
da_copy mx Bc ii q CBS acc -> da_copy mc' Bc ii q CBS acc.
Proof.
intros Ax LBx Bx mx mdx Fr mc' Bc ii q CBS acc HP Hi MU WM (kids' & wq & Hq & DD & JQ & REST).
pose proof LOS as LOSu. unfold dc_stkA, DC_F, DC_C in LOSu.
assert (RD0 : 0 <= rdepth r) by (destruct r; cbn [rdepth]; try lia; apply sdepth_nonneg).
pose proof (fk1_pres _ _ _ _ _ _ _ _ lo (bv_unsigned sp + -104) _ HP LO ltac:(lia) MU WM) as HPR.
exists kids', wq. split; [exact Hq|]. split; [exact (dc_dst_munch _ _ _ _ _ _ _ _ _ HP DD MU WM) |]. split; [| exact REST].
eapply (jval_agree asegs A4F); [exact JQ | | exact Hi].
eapply (agree_of_heap_pres asegs A4H); [exact HPR | reflexivity | intros b Hb; apply in_or_app; left; exact Hb].
Qed.

Lemma dc_arr_next :
forall (ii : nat) (y1 u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 x21 u3 u4 u5 u6 : word) (F2 : bvmap 5 word) (fc2 : bv 32)
(m2 : word -> option byte) (md2 : config) (A2 : ASA A4L HIx) (B2 : bud) (Fr q acc : Z) (v2 : word) (CBS REM : list blk),
(S ii <= length kids)%nat ->
dc_inv m2 md2 -> fsaved F F2 -> frm0 fc2 ->
HEAPAx A2 (BS ++ CBS ++ REM ++ LB) LM ((Fr, 1) :: FRS) B2 m2 md2 ->
da_own m2 Fr v2 0 ->
da_copy m2 B2 (S ii) q CBS acc -> acc + arr_wsum (skipn (S ii) ws) = w ->
((S ii < length kids)%nat ->
forall (mc : word -> option byte),
dc_inv mc md2 -> HEAPAx A2 (BS ++ CBS ++ REM ++ LB) LM ((Fr, 1) :: FRS) B2 mc md2 ->
da_own mc Fr v2 248 -> da_copy mc B2 (S ii) q CBS acc ->
AJ5 A4L HIx A2 T md2
(MS (mkR y1 (wz ASP) gp (wz A_TP) u0 u1 u2 sp (wz ASP) (wz 0) b1 b2 b3 b4 b5 b6 b7
(wz (Fr / 8 + 2147450880)) (wz (-8)) (wz 2147450880) x21 (wz ((p + 40) / 8 + 2147450880)) (wz (p + 40))
(wz (Z.of_nat (length kids))) (wz (Fr + 64)) (wz (Z.of_nat (S ii))) (wz (D / 8 + 2147450880)) u3 u4 u5 u6)
F2 (wz 0x9fb1c) fc2 None mc (seg_rom asegs))) ->
AJ5 A4L HIx A2 T md2
(MS (mkR y1 (wz ASP) gp (wz A_TP) u0 u1 u2 sp (wz ASP) (wz 0) b1 b2 b3 b4 b5 b6 b7
(wz (Fr / 8 + 2147450880)) (wz (-8)) (wz 2147450880) x21 (wz ((p + 40) / 8 + 2147450880)) (wz (p + 40))
(wz (Z.of_nat (length kids))) (wz (Fr + 64)) (wz (Z.of_nat ii)) (wz (D / 8 + 2147450880)) u3 u4 u5 u6)
F2 (wz 0x9fb9c) fc2 None m2 (seg_rom asegs)).
Proof.
intros until REM. intros Hii INV FS FRM2 HP OWN COPY ACC KLOOP.
pose proof OWN as (j24 & j16 & jf1 & jf2 & w1 & w2 & SCR & FF & FSH).
pose proof INV as (VMi & PRESi & STi & SAVEi & Gi). unfold dc_save in SAVEi.
pose proof LOS as LOSu. unfold dc_stkA, DC_F, DC_C in LOSu. unfold ASP, dc_scr in *.
assert (RD0 : 0 <= rdepth r) by (destruct r; cbn [rdepth]; try lia; apply sdepth_nonneg).
pose proof alloc_ceiling_range as ACR.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
destruct (dc_dfacts _ _ _ _ _ _ HP) as (D1 & D2 & D3 & D4 & DBLK & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13).
set (sh := Fr / 8 + 2147450880) in *.

assert (HiB : incl BS (BS ++ CBS ++ REM ++ LB)) by (apply incl_appl; apply incl_refl).
pose proof (da_src_agree _ _ _ _ _ _ _ _ HP HiB INV) as AG0.
destruct (arr_nowD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HP AG0 HiB ltac:(rewrite EBS; left; reflexivity) ltac:(rewrite EBS; intros b Hb; right; apply in_or_app; left; apply in_or_app; left; exact Hb) HDR0 HAL0)
as (sarr & ssize & HDRc & _ & _ & _ & _ & _ & _ & ALB & _ & _ & Hsz0 & SHrb & Hlen & _).
assert (LEN : Z.of_nat (length kids) < 2^61).
{ rewrite <- L1. destruct ALB as (_ & _ & _ & Hr0 & _ & Hrh). clear - Hlen Hrh Hr0 ACR. lia. }
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. change (hl_segs A4L) with asegs in MI.
pose proof (wmono_refl asegs m2) as WM. pose proof (munch_refl [(lo, bv_unsigned sp + -104); (Fr, Fr + 120); (sh, sh + 16); (6434236, 6434240)] m2) as MU.
stash PRESi. stash Gi. stash COPY. stash KLOOP. stash OWN. stash INV. stash HDRc. stash AG0.
unfold A_TP. a4l.
reenterA asegs A4L HIx asegs_wx HP.
step. stepz. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) => rename mq into mX end.
lazymatch goal with MUc : munch _ m2 mX, WMc : wmono asegs m2 mX, MIc : mem_inv asegs mX |- _ =>
pose proof (fk1_HEAPA _ _ _ _ _ _ _ _ lo (bv_unsigned sp + -104) _ HP LO ltac:(lia) MUc WMc MIc) as HPX;
unstash INV; pose proof (dc_inv_own _ _ _ _ _ _ _ HP ltac:(intros b Hb; apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; exact Hb | apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; exact Hb]) MUc WMc INV STi SAVEi) as INVX;
unstash COPY; pose proof (da_copy_own _ _ _ _ _ _ _ _ _ _ _ _ HP ltac:(apply incl_appr; apply incl_appl; apply incl_refl) MUc WMc COPY) as COPYX
end.
assert (OWNX : da_own mX Fr v2 248) by (exists j24, j16, jf1, jf2, w1, w2; split; [exact SCR | split; [exact FF | exact FSH]]).
destruct (Nat.eq_dec (S ii) (length kids)) as [Eend | Nend].
-
replace (Z.of_nat ii + 1) with (Z.of_nat (length kids)) by lia.
rewrite bv_eqb_refl. cbn [negb]. cbv iota.
pose proof (da_src_agree _ _ _ _ _ _ _ _ HPX HiB INVX) as AGX.
destruct (arr_nowD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HPX AGX HiB ltac:(rewrite EBS; left; reflexivity) ltac:(rewrite EBS; intros b Hb; right; apply in_or_app; left; apply in_or_app; left; exact Hb) HDR0 HAL0)
as (sarr' & ssize' & HDRX & _).
destruct (proj1 (rw_cells_app asegs mX _ _ _) HDRX) as [HDRX1 _].
destruct COPYX as (kids' & wq & Hq & DDX & JQX & LK & OK & JTX & WQ & AINV & BDX & BBX).
pose proof (PhiA_nonneg _ _ AINV) as PHI.
evt_done5.
eapply (dc_tail0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F2 fc2 mX md2 A2 B2 Fr (wz 0) (CB 8 j24) j16 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (JRtree (Sarr kids')) q 48 JT_ARRAY (fn_arr_to_json_string A4F) pb CBS REM);
[ exact INVX | exact FS | exact FRM2 | exact HPX | exact SCR | reflexivity | exact FF | reflexivity | exact FSH
| exact (da_src_now _ _ _ _ _ _ _ _ HPX HiB INVX) | rewrite EBS; left; reflexivity | lia | exact HDRX1
| rewrite Er; exists (Sarr kids'); split; [reflexivity | rewrite !sdepth_Sarr; lia]
| cbn [dc_cwA]; exists wq; split; [exact JTX |]; rewrite Eend, skipn_all2 in ACC by lia; cbn [arr_wsum] in ACC; lia
| exact Hq | exact DDX | split; [exact Hq | exact JQX]
| rewrite Eend, skipn_all2 in ACC by lia; cbn [arr_wsum] in ACC; lia
| rewrite Eend, skipn_all2 in ACC by lia; cbn [arr_wsum] in ACC; unfold DC_KB in *; lia ].
-
assert (NE : Z.of_nat (length kids) <> Z.of_nat ii + 1) by lia.
if_truex.
replace (Z.of_nat ii + 1) with (Z.of_nat (S ii)) by lia.
evt_done5. unstash KLOOP.
exact (KLOOP ltac:(lia) mX INVX HPX OWNX COPYX).
Qed.

Lemma dc_arr_loop :
forall (n ii : nat) (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x21 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
(mc : word -> option byte) (mdc : config) (A : ASA A4L HIx) (Bc : bud) (Fr q acc : Z) (v2 : word) (CBS REM : list blk),
n = (length kids - ii)%nat -> (ii < length kids)%nat ->
dc_inv mc mdc -> fsaved F F1 -> frm0 fc1 ->
HEAPAx A (BS ++ CBS ++ REM ++ LB) LM ((Fr, 1) :: FRS) Bc mc mdc ->
da_own mc Fr v2 248 -> da_copy mc Bc ii q CBS acc -> acc + arr_wsum (skipn ii ws) = w ->
AJ5 A4L HIx A T mdc
(MS (mkR x1 (wz ASP) gp (wz A_TP) t0 t1 t2 sp (wz ASP) a0 a1 a2 a3 a4 a5 a6 a7
(wz (Fr / 8 + 2147450880)) (wz (-8)) (wz 2147450880) x21 (wz ((p + 40) / 8 + 2147450880)) (wz (p + 40))
(wz (Z.of_nat (length kids))) (wz (Fr + 64)) (wz (Z.of_nat ii)) (wz (D / 8 + 2147450880)) t3 t4 t5 t6)
F1 (wz 0x9fb1c) fc1 None mc (seg_rom asegs)).
Proof.
induction n as [|n IHn]; intros until REM; intros Hn Hii INV FS FRM1 HP OWN COPY ACC; [lia|].
pose proof OWN as (j24 & j16 & jf1 & jf2 & w1 & w2 & SCR & FF & FSH).
pose proof INV as (VMi & PRESi & STi & SAVEi & Gi). unfold dc_save in SAVEi.
pose proof COPY as (kids' & wq & Hq & DD & JQ & LK & OK & JTX & WQ & AINV & BDc & BBc).
pose proof LOS as LOSu. unfold dc_stkA, DC_F, DC_C in LOSu. unfold ASP, dc_scr in *.
assert (RD0 : 0 <= rdepth r) by (destruct r; cbn [rdepth]; try lia; apply sdepth_nonneg).
pose proof alloc_ceiling_range as ACR.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
destruct (dc_dfacts _ _ _ _ _ _ HP) as (D1 & D2 & D3 & D4 & DBLK & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13).
pose proof DD as [DC DSH]. pose proof (rw_cells_bound asegs mc D _ DC) as DR. cbn [cells_size csize Nat.add] in DR.
set (sh := Fr / 8 + 2147450880) in *.

assert (HiB : incl BS (BS ++ CBS ++ REM ++ LB)) by (apply incl_appl; apply incl_refl).
assert (INp : In (p, 48) BS) by (rewrite EBS; left; reflexivity).
pose proof (da_src_agree _ _ _ _ _ _ _ _ HP HiB INV) as AG0.
destruct (arr_nowD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HP AG0 HiB INp ltac:(rewrite EBS; intros b Hb; right; apply in_or_app; left; apply in_or_app; left; exact Hb) HDR0 HAL0)
as (sarr & ssize & HDRc & Hp0 & Hp48 & Hp8 & SHp1 & SHpb & AL1 & ALB & SHa1 & SHr1 & Hsz0 & SHrb & Hlen & EAL).
assert (LEN : Z.of_nat (length kids) < 2^61).
{ rewrite <- L1. destruct ALB as (_ & _ & _ & Hr0 & _ & Hrh). clear - Hlen Hrh Hr0 ACR. lia. }
destruct (akids_nth asegs A4F m0 kids ps KBS ii (al_nth ps (Z.of_nat ii)) KIDS0 ltac:(rewrite <- (Nat2Z.id ii) at 1; apply al_nth_in; lia)) as (k & bs & Hk & Hbs & JO0).
pose proof (nth_error_In kids ii Hk) as KIN.
assert (BSI : incl bs BS).
{ intros b Hb. rewrite EBS. apply in_or_app; left. right. apply in_or_app; right. rewrite (QJlD.concat_nth_split KBS ii bs Hbs). apply in_or_app; right. apply in_or_app; left. exact Hb. }
pose proof (jopt_agree _ _ _ _ _ _ _ _ JO0 AG0 BSI) as JOc.
pose proof (blk_gran0A HIx _ _ _ _ _ _ _ p 48 5 HP ltac:(apply HiB; exact INp) ltac:(lia) ltac:(lia)) as SHp5.
replace (p / 8 + 2147450880 + 5) with ((p + 40) / 8 + 2147450880) in SHp5 by (clear - Hp8; Z.div_mod_to_equations; lia).
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ p 48 HP ltac:(left; reflexivity) ltac:(apply in_or_app; left; apply HiB; exact INp)) as DFp. rewrite fr_size_1 in DFp.
pose proof (heapA_blk_appmem A4L HIx _ _ _ _ _ _ _ p 48 HP ltac:(apply in_or_app; left; apply HiB; exact INp)) as APPp. cbn [hl_sb A4L] in APPp. unfold A_SB in APPp.
change ((2 ^ 47 - 1) / 8 + 2147450880 + 1) with 17594333495296 in APPp.
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP ltac:(left; reflexivity)) as (_ & _ & _ & _ & HFimg & _). rewrite fr_size_1 in HFimg. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in HFimg.
set (psh := (p + 40) / 8 + 2147450880) in *.
assert (PSH : 2147450880 <= psh < 17594333495296 /\ (psh + 1 <= sh \/ sh + 16 <= psh)) by (unfold psh, sh; clear - Hp0 Hp48 Hp8 ACR DFp D6 D7; Z.div_mod_to_equations; lia).
unfold jhdr_cells in HDRc. cbn [app] in HDRc.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. change (hl_segs A4L) with asegs in MI.
destruct (heapA_sb_cells A4L HIx _ _ _ _ _ _ _ HP) as (SB1 & SB2 & _ & _).
apply ro_C8_of_bytes_at in SB1. apply ro_C8_of_bytes_at in SB2.
pose proof (wmono_refl asegs mc) as WM. pose proof (munch_refl [(lo, bv_unsigned sp + -104); (Fr, Fr + 120); (sh, sh + 16); (6434236, 6434240)] mc) as MU.
stash PRESi. stash Gi. stash COPY. stash OWN. stash INV. stash JQ. stash JOc. stash JO0. stash AL1. stash SHa1. stash SHr1. stash SHp1. stash AG0. stash DD. stash IHn.
clear DC DSH.
unfold A_TP. a4l.
reenterA asegs A4L HIx asegs_wx HP.
stepz. stepz.
asan_rechkA.
step. step. step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) => rename mq into mg end.
assert (HiBL : incl (BS ++ LB) (BS ++ CBS ++ REM ++ LB)).
{ intros b Hb. apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; exact Hb | apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; exact Hb]. }
pose proof (fk1_HEAPA _ _ _ _ _ _ _ _ lo (bv_unsigned sp + -104) _ HP LO ltac:(lia) MU WM MI) as HPg.
unstash INV. pose proof (dc_inv_own _ _ _ _ _ _ _ HP HiBL MU WM INV STi SAVEi) as INVg.
pose proof (da_src_agree _ _ _ _ _ _ _ _ HPg HiB INVg) as AGg.
clear AL1 SHa1 SHr1 SHp1 ALB Hsz0 SHrb Hlen EAL.
destruct (arr_nowD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HPg AGg HiB INp ltac:(rewrite EBS; intros b Hb; right; apply in_or_app; left; apply in_or_app; left; exact Hb) HDR0 HAL0)
as (sarr' & ssize' & _ & _ & _ & _ & _ & _ & AL1 & ALB & SHa1 & SHr1 & Hsz0 & SHrb & Hlen & EAL).
eapply evt_cut.
{ eapply array_list_get_idx_A with (lo := lo) (sbcell := 981752) (a := a) (arr := sarr') (size := ssize') (ps := ps) (i := Z.of_nat ii).
- unfold small_pre, A_GOT_SB, A_SB. rewrite ?unsigned_lit by lia.
split; [assumption|]. split; [eassumption|]. split; [lia|]. split; [exact LO|]. split; [eassumption|]. split; [eassumption|]. lia.
- exact AL1.
- reflexivity.
- reflexivity.
- lia.
- exact ALB.
- exact SHa1.
- exact SHr1. }
intros ms' (g1 & g2 & g3 & g4 & m' & -> & MUg & WMg & MIg & STg).
rewrite ?unsigned_lit in MUg, STg by lia.
rewrite (proj2 (Z.ltb_lt (Z.of_nat ii) (Z.of_nat (length ps)))) by lia.
clear AL1 SHa1 SHr1 ALB Hsz0 SHrb Hlen EAL AGg.

lazymatch type of MUg with munch _ ?mq _ =>
transport_after_call asegs mq m' MUg WMg; try match goal with H : mem_inv asegs mq |- _ => clear H end; clear MUg WMg end.
replace (ret_pc (wz 654136)) with (wz 654136) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
unstash JOc.
destruct k as [sk|].
-
destruct JOc as [Hpk JVk].
destruct (jval_root_in asegs A4F _ _ _ _ _ JVk) as (nk & INk & Hnk).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ _ nk HP ltac:(apply in_or_app; left; apply HiB; apply BSI; exact INk)) as (_ & Hpkal & Hpklo & Hpkhi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hpkhi.
set (pk := al_nth ps (Z.of_nat ii)) in *.
clear JVk.
step. if_falsex.
step. step. step. step. step. step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) => rename mq into mk end.
pose proof (fk1_HEAPA _ _ _ _ _ _ _ _ lo (bv_unsigned sp + -104) _ HP LO ltac:(lia) MU WM MIg) as HPc.
pose proof (dc_inv_own _ _ _ _ _ _ _ HP HiBL MU WM INV STg SAVEi) as INVc.
pose proof (da_src_agree _ _ _ _ _ _ _ _ HPc HiB INVc) as AGc.
unstash JO0. pose proof (jopt_agree _ _ _ _ _ _ _ _ JO0 AGc BSI) as [_ JVk].
unstash COPY. pose proof (da_copy_own _ _ _ _ _ _ _ _ _ _ _ _ HP ltac:(apply incl_appr; apply incl_appl; apply incl_refl) MU WM COPY) as COPYc. clear COPY.
destruct (heapA_errno A4L HIx _ _ _ _ _ _ _ HPc) as (errs & ERRs).

destruct (KW1 ii sk bs Hk Hbs) as (Yi & Ri & JTk). set (wk := nth ii ws 0) in *.
pose proof (arr_wsum_skipn ws ii wk ltac:(apply nth_error_nth_len; lia)) as WS1. fold wk in WS1.
pose proof (arr_wsum_skipn_nonneg ws (S ii) NNW) as WS2.
pose proof (jtx_nonneg _ _ _ _ JTk) as WK0.
pose proof (PhiA_nonneg _ _ AINV) as PHI.

set (K1 := concat (firstn ii KBS)). set (K2 := concat (skipn (S ii) KBS)).
assert (EBSk : BS = ((p, 48) :: AL ++ K1 ++ bs ++ K2) ++ PBS) by (rewrite EBS, (QJlD.concat_nth_split KBS ii bs Hbs); reflexivity).
set (LBk := ((p, 48) :: AL ++ K1 ++ K2) ++ PBS ++ CBS ++ REM ++ LB).
assert (HPk : HEAPAx A (bs ++ LBk) LM ((Fr, 1) :: FRS) Bc mk mdc).
{ eapply (heapA_perm A4L HIx); [exact HPc | rewrite EBSk; unfold LBk; perm | apply Permutation_refl | apply Permutation_refl]. }

lazymatch type of FF with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?rest) =>
change (c0 :: c1 :: c2 :: c3 :: c4 :: rest) with ([c0; c1; c2; c3] ++ ([c4] ++ rest)) in FF end.
destruct (proj1 (rw_cells_app asegs mk _ _ _) FF) as [FFa FFx]. cbn [cells_size csize Nat.add] in FFx.
destruct (proj1 (rw_cells_app asegs mk _ _ _) FFx) as [FFj FFb]. cbn [cells_size csize Nat.add] in FFb.
replace (Fr + Z.of_nat 64) with (Fr + 64) in FFj, FFb by lia. replace (Fr + 64 + Z.of_nat 8) with (Fr + 72) in FFb by lia.
clear FF FFx.
assert (UNP : unpoisoned asegs mk A_SB (Fr + 64) 8).
{ pose proof (unpoisoned_of_fshadow1 mk Fr _ 8 9 (proj2 (proj1 FSH)) eq_refl D6 ltac:(lia) ltac:(lia) ltac:(lia) eq_refl) as U.
change (8 * Z.of_nat 8) with 64 in U. change (8 * Z.of_nat (9 - 8)) with 8 in U. exact U. }

assert (DEPk : sdepth sk + 1 <= rdepth r).
{ rewrite Er. cbn [rdepth]. rewrite sdepth_Sarr. pose proof (odep_le_okmax kids (Some sk) KIN) as X. cbn [odep] in X. lia. }
assert (WKLT : wk < 2^28) by (pose proof (jtx_nonneg _ _ _ _ JTX) as WQ0; clear - WLT WS1 WS2 ACC WQ WQ0; lia).
evt_done5.
eapply (IH sk KIN) with (A := A) (LB := LBk) (BS := bs) (LM := LM) (FRS := (Fr, 1) :: FRS) (B := Bc) (lo := lo) (p := pk) (D := Fr + 64) (w := wk) (errv := errs);
[ exact HPk | split; [exact Hpk | exact JVk] | discriminate | exact (proj2 (proj2 (proj2 (proj2 INVc)))) | exact FFj
| exists Fr, 1; split; [left; reflexivity | rewrite fr_size_1; lia]
| exact UNP | clear - D6; Z.div_mod_to_equations; lia
| rewrite unsigned_lit by lia; exact STg | exact LO
| rewrite unsigned_lit by lia; unfold dc_stkA, DC_F, DC_C; cbn [rdepth]; lia
| rewrite unsigned_lit by lia; clear - SPA; Z.div_mod_to_equations; lia
| rewrite unsigned_lit by lia; lia
| exact ERRs | reflexivity | rewrite unsigned_lit by lia; reflexivity | exact FRM1
| cbn [length rdepth]; lia
| exists Yi, Ri; exact JTk
| exact WKLT
| unfold DC_KB in *; lia | lia | reflexivity | reflexivity | reflexivity | ].

intros msr mdr mr rvr Ar Br (RSr & VMr & STr & PXr & (errr & ERRr)) Gr JRr (BDr & OUTr).
destruct RSr as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & F2 & fc2 & -> & FS2 & FRM2).
rewrite ?(unsigned_lit (bv_unsigned sp + -192)) in STr, PXr by lia.
change (hl_segs A4L) with asegs in *.
replace (ret_pc (wz 654164)) with (wz 654164) by (symmetry; apply ret_pc_even; [lia | reflexivity]).

assert (PXR : forall A0 cs0, rw_cells asegs mk A0 cs0 ->
client_rangex A4H (hl_volatile A4H) ((bs ++ LBk) ++ LM ++ fr_ivs A4L ((Fr, 1) :: FRS)) (bv_unsigned sp + -192) A0 (Z.of_nat (cells_size cs0)) ->
(A0 + Z.of_nat (cells_size cs0) <= Fr + 64 \/ Fr + 64 + 8 <= A0) -> rw_cells asegs mr A0 cs0).
{ intros A0 cs0 H1 H2 H3. exact (QrIB.Mq0.presxD_rw_cells A4H _ _ _ _ _ _ _ PXr H1 H2 H3). }
apply PXR in SCR; [| left; lia | cbn [cells_size csize Nat.add]; lia].
apply PXR in SAVEi; [| left; lia | cbn [cells_size csize Nat.add]; lia].
apply PXR in FFa; [| eapply client_rangex_block; [apply in_or_app; right; apply in_or_app; right; left; reflexivity | cbn [fr_base fst]; lia | cbn [cells_size csize Nat.add fr_base fr_class fst snd]; rewrite fr_size_1; lia]
| cbn [cells_size csize Nat.add]; lia].
apply PXR in FFb; [| eapply client_rangex_block; [apply in_or_app; right; apply in_or_app; right; left; reflexivity | cbn [fr_base fst]; lia | cbn [cells_size csize Nat.add fr_base fr_class fst snd]; rewrite fr_size_1; lia]
| cbn [cells_size csize Nat.add]; lia].
apply PXR in FSH; [| eapply client_rangex_block; [apply in_or_app; right; apply in_or_app; right; right; left; reflexivity | unfold shad; cbn [fr_base fst hl_sb A4L]; unfold A_SB; fold sh; lia
| unfold shad; cbn [cells_size csize Nat.add fr_base fr_class fst snd hl_sb A4L]; rewrite fr_shadow_len_1; unfold A_SB; fold sh; lia]
| cbn [cells_size csize Nat.add]; lia].
clear PXR.

assert (INVr : dc_inv mr mdr).
{ destruct INVc as (VMc & PXc & _ & _ & _).
split; [eapply model_vm_only_trans; [exact VMc | exact VMr] |].
split; [eapply (QrIB.Mq0.presxD_trans A4H); [exact PXc |] | split; [exact STr | split; [unfold dc_save; exact SAVEi | exact Gr]]].
eapply presxD_own with (D' := Fr + 64); [exact PXr | lia | |].
- intros b Hb. apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left | apply in_or_app; right].
+ apply (Permutation_in b (l := BS ++ CBS ++ REM ++ LB)); [rewrite EBSk; unfold LBk; perm | apply HiBL; exact Hb].
+ apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; exact Hb | apply in_or_app; right; cbn [fr_ivs flat_map app]; right; right; exact Hb].
- intros x Hx. eapply da_own_outside; [exact HPc | exact HiBL | unfold alloc_ceiling, sp_window_lo, stack_max_size in D8; lia | lia]. }
destruct COPYc as (kidsc & wqc & Hqc & DDk & JQk & LKc & OKc & JTXc & WQc & AINVc & BDk & BBk).
pose proof (dc_dst_presxD _ _ _ _ _ Fr (Fr + 64) (bs ++ LBk) (bv_unsigned sp + -192) mk mr q HPc ltac:(lia) ltac:(lia) DDk PXr) as DDr.

assert (AGr : forall BSx, incl BSx (BS ++ CBS ++ REM ++ LB) -> agree_on asegs BSx mk mr).
{ intros BSx Hi. eapply presxD_agree_blocks; [exact PXr | |].
- intros b Hb. apply in_or_app; left. apply (Permutation_in b (l := BS ++ CBS ++ REM ++ LB)); [rewrite EBSk; unfold LBk; perm | apply Hi; exact Hb].
- intros a0' k0' Hin. pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ Fr 1 a0' k0' HPc ltac:(left; reflexivity) ltac:(apply in_or_app; left; apply Hi; exact Hin)) as DF.
rewrite fr_size_1 in DF. lia. }
pose proof (jval_agree asegs A4F _ _ _ _ _ _ _ JQk (AGr CBS ltac:(apply incl_appr; apply incl_appl; apply incl_refl)) (incl_refl _)) as JQr.
clear JVk FFj UNP.
destruct OUTr as [(-> & d & qk & KCBS & KREM & COk & CWk & Hqk & DCk & JRk & BBr & HPr) | (-> & qk & KCBS & KREM & DCk & FRk & BBr & HPr)].
+
destruct COk as (sk' & -> & DEPk'). cbn [dc_cwA] in CWk. destruct CWk as (wk' & JTk' & WK').
assert (HPa : HEAPAx Ar (BS ++ CBS ++ KCBS ++ (KREM ++ REM) ++ LB) LM ((Fr, 1) :: FRS) Br mr mdr).
{ eapply (heapA_perm A4L HIx); [exact HPr | rewrite EBSk; unfold LBk; perm | apply Permutation_refl | apply Permutation_refl]. }
assert (OWNr : da_own mr Fr (wz qk) 0).
{ exists j24, j16, jf1, jf2, w1, w2. split; [exact SCR | split; [| exact FSH]].
lazymatch goal with |- rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?rest) =>
change (c0 :: c1 :: c2 :: c3 :: c4 :: rest) with ([c0; c1; c2; c3] ++ ([c4] ++ rest)) end.
apply (proj2 (rw_cells_app asegs mr _ _ _)). split; [exact FFa |]. cbn [cells_size csize Nat.add].
apply (proj2 (rw_cells_app asegs mr _ _ _)). cbn [cells_size csize Nat.add].
replace (Fr + Z.of_nat 64) with (Fr + 64) by lia. replace (Fr + 64 + Z.of_nat 8) with (Fr + 72) by lia. split; [exact DCk | exact FFb]. }
assert (HiBa : incl BS (BS ++ CBS ++ KCBS ++ (KREM ++ REM) ++ LB)) by (apply incl_appl; apply incl_refl).
pose proof (da_src_now _ _ _ _ _ _ _ _ HPa HiBa INVr) as JRsrc.
clear SCR FFa FFb FSH SAVEi.
pose proof DDr as [_ DSHr].
stash INVr. stash OWNr. stash JRsrc. stash JQr. stash JRk. stash DDr.
try clear MU WM. try clear MIg.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HPa) as MIr. change (hl_segs A4L) with asegs in MIr.
pose proof (wmono_refl asegs mr) as WMr. pose proof (munch_refl [(lo, bv_unsigned sp + -104); (Fr, Fr + 120); (sh, sh + 16); (6434236, 6434240)] mr) as MUr.
reenterA asegs A4L HIx asegs_wx HPa.
step. if_lit.
step. rewrite ?zxb_zero. step. if_lit.
evt_done5. unstash INVr. unstash OWNr. unstash JRsrc. unstash JQr. unstash JRk. unstash DDr.
assert (LEN28 : Z.of_nat (length kids) + 1 < 2^28).
{ pose proof (arr_wsum_len ws NNW) as X. rewrite LW in X. clear - X EW WLT. lia. }
assert (CAPk : arr_add_costA (arr_capA CBS) (Z.of_nat ii) <= PhiA (arr_capA CBS) (Z.of_nat ii) + 1280).
{ clear - AINVc. unfold arr_add_costA, PhiA, arr_inv in *. destruct (Z.ltb_spec (Z.of_nat ii + 1) (arr_capA CBS)); lia. }
eapply dc_arr_add with (v := qk) (q := q) (kids' := kidsc) (vs := Some sk') (VBS := KCBS) (CBS := CBS) (REM := KREM ++ REM);
[ exact INVr | eapply fsaved_trans; [exact FS | exact FS2] | apply FRM2; exact FRM1 | exact HPa | exact OWNr | exact JRsrc
| exact Hqc | exact DDr | exact JQr | exact JRk | rewrite LKc; lia | lia
| rewrite LKc; unfold DC_KB in *; lia | ].
intros z1 u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F3 fc3 m3 md3 A3 B3 CBS' INV3 FS3 FRM3 HP3 OWN3 JR3 DD3 JQ3 LEN3 GROW3 BB3 BD3 JTX3.
rewrite LKc in GROW3, BB3.
destruct (potential_step_arr_add _ _ _ AINVc GROW3) as [POT AINV3].
eapply (dc_arr_next ii) with (q := q) (acc := acc + (2 + wk)) (CBS := CBS') (REM := KREM ++ REM);
[ lia | exact INV3 | exact FS3 | exact FRM3 | exact HP3 | exact OWN3 | | lia | ].
* exists (kidsc ++ [Some sk']), (wqc + (2 + wk')).
split; [exact Hqc|]. split; [exact DD3|]. split; [exact JQ3|].
split; [rewrite length_app, LKc; cbn [length]; lia|].
split; [rewrite okmax_app, okmax_single; cbn [odep]; pose proof (odep_le_okmax kids (Some sk) KIN) as X; cbn [odep] in X; lia|].
split; [exact (JTX3 wqc wk' JTXc JTk')|].
split; [lia|].
split; [replace (Z.of_nat (S ii)) with (Z.of_nat ii + 1) by lia; exact AINV3|].
split; [lia|].
replace (Z.of_nat (S ii)) with (Z.of_nat ii + 1) by lia. unfold Qiiq.Mq0.RA, K_arr, DC_KB in *. lia.
* intros Hlt mc' INV' HP' OWN' COPY'. unstash IHn.
eapply (IHn (S ii)) with (q := q) (acc := acc + (2 + wk)) (CBS := CBS') (REM := KREM ++ REM);
[ lia | lia | exact INV' | exact FS3 | exact FRM3 | exact HP' | exact OWN' | exact COPY' | lia ].
+
assert (HPa : HEAPAx Ar (BS ++ CBS ++ KCBS ++ (KREM ++ REM) ++ LB) LM ((Fr, 1) :: FRS) Br mr mdr).
{ eapply (heapA_perm A4L HIx); [exact HPr | rewrite EBSk; unfold LBk; perm | apply Permutation_refl | apply Permutation_refl]. }
assert (OWNr : da_own mr Fr (wz qk) 0).
{ exists j24, j16, jf1, jf2, w1, w2. split; [exact SCR | split; [| exact FSH]].
lazymatch goal with |- rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?rest) =>
change (c0 :: c1 :: c2 :: c3 :: c4 :: rest) with ([c0; c1; c2; c3] ++ ([c4] ++ rest)) end.
apply (proj2 (rw_cells_app asegs mr _ _ _)). split; [exact FFa |]. cbn [cells_size csize Nat.add].
apply (proj2 (rw_cells_app asegs mr _ _ _)). cbn [cells_size csize Nat.add].
replace (Fr + Z.of_nat 64) with (Fr + 64) by lia. replace (Fr + 64 + Z.of_nat 8) with (Fr + 72) by lia. split; [exact DCk | exact FFb]. }
assert (HiBa : incl BS (BS ++ CBS ++ KCBS ++ (KREM ++ REM) ++ LB)) by (apply incl_appl; apply incl_refl).
pose proof (da_src_now _ _ _ _ _ _ _ _ HPa HiBa INVr) as JRsrc.
clear SCR FFa FFb FSH SAVEi.
stash INVr. stash OWNr. stash JRsrc. stash JQr. stash FRk. stash DDr.
try clear MU WM. try clear MIg.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HPa) as MIr. change (hl_segs A4L) with asegs in MIr.
pose proof (wmono_refl asegs mr) as WMr. pose proof (munch_refl [(lo, bv_unsigned sp + -104); (Fr, Fr + 120); (sh, sh + 16); (6434236, 6434240)] mr) as MUr.
reenterA asegs A4L HIx asegs_wx HPa.
step. if_lit.
evt_done5. unstash INVr. unstash OWNr. unstash JRsrc. unstash JQr. unstash FRk. unstash DDr.
eapply dc_arr_fail with (v2 := qk) (q := q) (VBS := KCBS) (CBS := CBS) (REM := KREM ++ REM);
[ exact INVr | eapply fsaved_trans; [exact FS | exact FS2] | apply FRM2; exact FRM1 | exact HPa | exact OWNr | exact FRk | exact JRsrc | exact DDr
| right; split; [exact Hqc | exists (Sarr kidsc); exact JQr] | lia | unfold DC_KB in *; lia ].
-
destruct JOc as [Epk Ebs].
rewrite Epk.
step. if_lit.
stepz.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) => rename mq into mk end.
lazymatch goal with MUc : munch _ mc mk, WMc : wmono asegs mc mk, MIc : mem_inv asegs mk |- _ =>
pose proof (fk1_HEAPA _ _ _ _ _ _ _ _ lo (bv_unsigned sp + -104) _ HP LO ltac:(lia) MUc WMc MIc) as HPc;
pose proof (dc_inv_own _ _ _ _ _ _ _ HP HiBL MUc WMc INV STg SAVEi) as INVc;
unstash COPY; pose proof (da_copy_own _ _ _ _ _ _ _ _ _ _ _ _ HP ltac:(apply incl_appr; apply incl_appl; apply incl_refl) MUc WMc COPY) as COPYc; clear COPY
end.
destruct COPYc as (kidsc & wqc & Hqc & DDk & JQk & LKc & OKc & JTXc & WQc & AINVc & BDk & BBk).
pose proof DDk as [_ DSHk].
step. rewrite ?zxb_zero. step. if_lit.
assert (OWNc : da_own mk Fr (wz 0) 0) by (exists j24, j16, jf1, jf2, w1, w2; split; [exact SCR | split; [exact FF | exact FSH]]).
pose proof (KW2 ii Hk) as WKN.
pose proof (arr_wsum_skipn ws ii (nth ii ws 0) ltac:(apply nth_error_nth_len; lia)) as WS1. rewrite WKN in WS1.
pose proof (arr_wsum_skipn_nonneg ws (S ii) NNW) as WS2.
pose proof (PhiA_nonneg _ _ AINVc) as PHI.
assert (LEN28 : Z.of_nat (length kids) + 1 < 2^28).
{ pose proof (arr_wsum_len ws NNW) as X. rewrite LW in X. clear - X EW WLT. lia. }
assert (CAPk : arr_add_costA (arr_capA CBS) (Z.of_nat ii) <= PhiA (arr_capA CBS) (Z.of_nat ii) + 1280).
{ clear - AINVc. unfold arr_add_costA, PhiA, arr_inv in *. destruct (Z.ltb_spec (Z.of_nat ii + 1) (arr_capA CBS)); lia. }
evt_done5.
eapply dc_arr_add with (v := 0) (q := q) (kids' := kidsc) (vs := None) (VBS := []) (CBS := CBS) (REM := REM);
[ exact INVc | exact FS | exact FRM1 | exact HPc | exact OWNc | exact (da_src_now _ _ _ _ _ _ _ _ HPc HiB INVc)
| exact Hqc | exact DDk | exact JQk | split; reflexivity | rewrite LKc; lia | unfold NULL_W in *; lia
| rewrite LKc; cbn [length]; unfold DC_KB, NULL_W in *; lia | ].
intros z1 u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F3 fc3 m3 md3 A3 B3 CBS' INV3 FS3 FRM3 HP3 OWN3 JR3 DD3 JQ3 LEN3 GROW3 BB3 BD3 JTX3.
rewrite LKc in GROW3, BB3.
destruct (potential_step_arr_add _ _ _ AINVc GROW3) as [POT AINV3].
eapply (dc_arr_next ii) with (q := q) (acc := acc + (2 + NULL_W)) (CBS := CBS') (REM := REM);
[ lia | exact INV3 | exact FS3 | exact FRM3 | exact HP3 | exact OWN3 | | unfold NULL_W in *; lia | ].
+ exists (kidsc ++ [None]), (wqc + (2 + NULL_W)).
split; [exact Hqc|]. split; [exact DD3|]. split; [exact JQ3|].
split; [rewrite length_app, LKc; cbn [length]; lia|].
split; [rewrite okmax_app, okmax_single; cbn [odep]; pose proof (okmax_nonneg kids); lia|].
split; [exact (JTX3 wqc NULL_W JTXc eq_refl)|].
split; [lia|].
split; [replace (Z.of_nat (S ii)) with (Z.of_nat ii + 1) by lia; exact AINV3|].
split; [unfold NULL_W in *; lia|].
replace (Z.of_nat (S ii)) with (Z.of_nat ii + 1) by lia. cbn [length] in LEN3. unfold Qiiq.Mq0.RA, K_arr, DC_KB, NULL_W in *. lia.
+ intros Hlt mc' INV' HP' OWN' COPY'. unstash IHn.
eapply (IHn (S ii)) with (q := q) (acc := acc + (2 + NULL_W)) (CBS := CBS') (REM := REM);
[ lia | lia | exact INV' | exact FS3 | exact FRM3 | exact HP' | exact OWN' | exact COPY' | unfold NULL_W in *; lia ].
Qed.

Lemma dc_arr :
forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x19 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
(mc : word -> option byte) (mdc : config) (A : ASA A4L HIx) (Bc : bud) (Fr q : Z) (v2 : word) (CBS : list blk),
dc_inv mc mdc -> fsaved F F1 -> frm0 fc1 ->
HEAPAx A (BS ++ CBS ++ LB) LM ((Fr, 1) :: FRS) Bc mc mdc ->
da_own mc Fr v2 248 ->
q <> 0 -> dc_dst mc q -> jval asegs A4F (Sarr []) mc CBS q 1 -> length CBS = 3%nat -> arr_capA CBS = 32 ->
bD B0 - 1 <= bD Bc -> bB B0 - ((16 * 48 + 512) + (2048 + 128 * 32)) <= bB Bc ->
AJ5 A4L HIx A T mdc
(MS (mkR x1 (wz ASP) gp (wz A_TP) t0 t1 t2 sp (wz ASP) a0 a1 a2 a3 a4 a5 a6 a7
(wz (Fr / 8 + 2147450880)) x19 (wz 2147450880) (wz Fr) (wz Fr) (wz p) s8 s9 s10 s11 t3 t4 t5 t6)
F1 (wz 0x9fadc) fc1 None mc (seg_rom asegs)).
Proof.
intros until CBS. intros INV FS FRM1 HP0 OWN Hq DD JQ LCBS CAPQ BDc BBc.
assert (HP : HEAPAx A (BS ++ CBS ++ [] ++ LB) LM ((Fr, 1) :: FRS) Bc mc mdc) by exact HP0.
pose proof OWN as (j24 & j16 & jf1 & jf2 & w1 & w2 & SCR & FF & FSH).
pose proof INV as (VMi & PRESi & STi & SAVEi & Gi). unfold dc_save in SAVEi.
pose proof LOS as LOSu. unfold dc_stkA, DC_F, DC_C in LOSu. unfold ASP, dc_scr in *.
assert (RD0 : 0 <= rdepth r) by (destruct r; cbn [rdepth]; try lia; apply sdepth_nonneg).
pose proof alloc_ceiling_range as ACR.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
destruct (dc_dfacts _ _ _ _ _ _ HP) as (D1 & D2 & D3 & D4 & DBLK & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13).
pose proof DD as [DC DSH]. pose proof (rw_cells_bound asegs mc D _ DC) as DR. cbn [cells_size csize Nat.add] in DR.
set (sh := Fr / 8 + 2147450880) in *.

assert (JTXQ : jtx (Sarr []) CBS = Some (24, [])).
{ destruct (arr_capA_jval _ _ _ _ _ JQ) as (a_ & arr_ & rest_ & EABS & _). rewrite EABS in LCBS |- *. destruct rest_; [| cbn in LCBS; lia]. reflexivity. }
pose proof (arr_wsum_nonneg ws NNW) as WS0.

assert (HiB : incl BS (BS ++ CBS ++ [] ++ LB)) by (apply incl_appl; apply incl_refl).
assert (INp : In (p, 48) BS) by (rewrite EBS; left; reflexivity).
pose proof (da_src_agree _ _ _ _ _ _ _ _ HP HiB INV) as AG0.
destruct (arr_nowD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HP AG0 HiB INp ltac:(rewrite EBS; intros b Hb; right; apply in_or_app; left; apply in_or_app; left; exact Hb) HDR0 HAL0)
as (sarr & ssize & HDRc & Hp0 & Hp48 & Hp8 & SHp1 & SHpb & AL1 & ALB & SHa1 & SHr1 & Hsz0 & SHrb & Hlen & EAL).
assert (LEN : Z.of_nat (length kids) < 2^61).
{ rewrite <- L1. destruct ALB as (_ & _ & _ & Hr0 & _ & Hrh). clear - Hlen Hrh Hr0 ACR. lia. }
pose proof (blk_gran0A HIx _ _ _ _ _ _ _ p 48 5 HP ltac:(apply HiB; exact INp) ltac:(lia) ltac:(lia)) as SHp5.
replace (p / 8 + 2147450880 + 5) with (p / 8 + 2147450885) in SHp5 by lia.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hp48.
assert (COPY0 : da_copy mc Bc 0 q CBS 24).
{ exists [], 24. split; [exact Hq|]. split; [exact DD|]. split; [exact JQ|]. split; [reflexivity|].
split; [cbn [okmax]; apply okmax_nonneg|]. split; [exact JTXQ|]. split; [lia|].
rewrite CAPQ. split; [exact arr_inv_new|]. split; [lia|]. rewrite LCBS. unfold PhiA, DC_KB in *. cbn [Z.of_nat]. lia. }
unfold jhdr_cells in HDRc. cbn [app] in HDRc.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. change (hl_segs A4L) with asegs in MI.
destruct (heapA_sb_cells A4L HIx _ _ _ _ _ _ _ HP) as (SB1 & SB2 & _ & _).
apply ro_C8_of_bytes_at in SB1. apply ro_C8_of_bytes_at in SB2.
pose proof (wmono_refl asegs mc) as WM. pose proof (munch_refl [(lo, bv_unsigned sp + -104); (Fr, Fr + 120); (sh, sh + 16); (6434236, 6434240)] mc) as MU.
stash PRESi. stash Gi. stash COPY0. stash OWN. stash INV. stash JQ. stash AG0. stash DD.
clear DC DSH.
unfold A_TP. a4l.
reenterA asegs A4L HIx asegs_wx HP.
step. asan_chkA.
step. step.

eapply evt_cut.
{ eapply array_list_length_A with (lo := lo) (sbcell := 981752) (a := a) (arr := sarr) (size := ssize) (ps := ps).
- unfold small_pre, A_GOT_SB, A_SB. rewrite ?unsigned_lit by lia.
split; [assumption|]. split; [eassumption|]. split; [lia|]. split; [exact LO|]. split; [eassumption|]. split; [eassumption|]. lia.
- exact AL1.
- reflexivity.
- exact ALB.
- exact SHa1. }
intros ms' (g1 & g2 & m' & -> & MUg & WMg & MIg & STg).
rewrite ?unsigned_lit in MUg, STg by lia.
clear AL1 SHa1 SHr1 ALB Hsz0 SHrb Hlen EAL.
lazymatch type of MUg with munch _ ?mq _ =>
transport_after_call asegs mq m' MUg WMg; try match goal with H : mem_inv asegs mq |- _ => clear H end; clear MUg WMg end.
replace (ret_pc (wz 654072)) with (wz 654072) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
assert (HiBL : incl (BS ++ LB) (BS ++ CBS ++ [] ++ LB)).
{ intros b Hb. apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; exact Hb | apply in_or_app; right; apply in_or_app; right; exact Hb]. }
pose proof (fk1_HEAPA _ _ _ _ _ _ _ _ lo (bv_unsigned sp + -104) _ HP LO ltac:(lia) MU WM MIg) as HPg.
unstash INV. pose proof (dc_inv_own _ _ _ _ _ _ _ HP HiBL MU WM INV STg SAVEi) as INVg.
unstash COPY0. pose proof (da_copy_own _ _ _ _ _ _ _ _ _ _ _ _ HP ltac:(apply incl_appr; apply incl_appl; apply incl_refl) MU WM COPY0) as COPYg. clear COPY0.
assert (OWNg : da_own m' Fr v2 248) by (exists j24, j16, jf1, jf2, w1, w2; split; [exact SCR | split; [exact FF | exact FSH]]).
rewrite L1.
destruct (Nat.eq_dec (length kids) 0) as [E0 | N0].
-
rewrite E0. step. if_lit.
destruct COPYg as (kidsc & wqc & _ & DDg & JQg & LKc & _ & JTXg & WQg & _).
destruct kidsc; [| cbn in LKc; lia].
pose proof (da_src_agree _ _ _ _ _ _ _ _ HPg HiB INVg) as AGg.
destruct (arr_nowD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HPg AGg HiB INp ltac:(rewrite EBS; intros b Hb; right; apply in_or_app; left; apply in_or_app; left; exact Hb) HDR0 HAL0)
as (sarr' & ssize' & HDRg & _).
destruct (proj1 (rw_cells_app asegs m' _ _ _) HDRg) as [HDRg1 _].
evt_done5.
eapply (dc_tail0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F1 fc1 m' mdc A Bc Fr (wz 0) (CB 8 j24) j16 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (JRtree (Sarr [])) q 48 JT_ARRAY (fn_arr_to_json_string A4F) pb CBS []);
[ exact INVg | exact FS | exact FRM1 | exact HPg | exact SCR | reflexivity | exact FF | reflexivity | exact FSH
| exact (da_src_now _ _ _ _ _ _ _ _ HPg HiB INVg) | exact INp | lia | exact HDRg1
| rewrite Er; exists (Sarr []); split; [reflexivity | rewrite !sdepth_Sarr; cbn [okmax]; pose proof (okmax_nonneg kids); lia]
| cbn [dc_cwA]; exists wqc; split; [exact JTXg | lia]
| exact Hq | exact DDg | split; [exact Hq | exact JQg]
| lia | rewrite LCBS; unfold DC_KB in *; cbn [Z.of_nat]; lia ].
-
step. if_falsex.
do 8 step. sh_norm.
replace (p / 8 + 2147450885) with ((p + 40) / 8 + 2147450880) by (clear - Hp8; Z.div_mod_to_equations; lia).
evt_done5.
eapply (dc_arr_loop (length kids) 0) with (q := q) (acc := 24) (CBS := CBS) (REM := []);
[ lia | lia | exact INVg | exact FS | exact FRM1 | exact HPg | exact OWNg | exact COPYg | rewrite EW; reflexivity ].
Qed.
End MDcArr.
End RC__1.
End Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI QRBl QgHv Q228 QfHY QiVi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import QCcH Q0Ek QjDH.Mq0.
Import QbFI. Import QRBl. Import Qhd4. Import Qwm6.Mq4 QgHv Q9O6.Mq5 QlKV.Mqg Q228.Mq9 Qz87.Mq3 Q228.Mqb Q228.Mqf QtyQ QfHY.Mq8 QiVi.Mq5 QfHY.Mq5 Q63E.Mqi.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac QlEo_c1.solve_load ::= QXup.mkr__solve_load_3. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Section All.
Variable HIx : heap_iface_A A4L.
Hypothesis OBL_REALLOC_NF : realloc_nf_stmt HIx.
Variable PFRT : (word -> option byte) -> Prop.
Variable PFLO : Z.
Hypothesis OBL_PFRT : forall A LB LM FRS B m md, HEAPA A4L HIx A LB LM FRS B m md -> PFRT m.
Hypothesis OBL_PFLO : PFLO <= alloc_ceiling.
Hypothesis SNP_LD : isnprintf_ld_stmt PFRT PFLO.
Hypothesis SNP_LU : isnprintf_lu_stmt PFRT PFLO.
Hypothesis SNP_U : isnprintf_u00cc_stmt PFRT PFLO.

Theorem servalA : SERVALA HIx.
Proof.
pose proof (json_escape_str_A HIx OBL_REALLOC_NF PFRT PFLO OBL_PFRT OBL_PFLO SNP_U) as ESC.
unfold SERVALA. induction s as [|u| |h|kids IHk|kids IHk] using jshape_ind2.
- exact (ser_boolA HIx OBL_REALLOC_NF).
- destruct u; [exact (ser_udA HIx OBL_REALLOC_NF) | exact (ser_dblA HIx OBL_REALLOC_NF)].
- exact (ser_intA HIx OBL_REALLOC_NF PFRT PFLO OBL_PFRT OBL_PFLO SNP_LD SNP_LU).
- destruct h; [exact (ser_str_heapA HIx OBL_REALLOC_NF ESC) | exact (ser_str_inlineA HIx OBL_REALLOC_NF ESC)].
- exact (ser_objA HIx OBL_REALLOC_NF ESC kids IHk).
- exact (ser_arrA HIx OBL_REALLOC_NF kids IHk).
Qed.
End All.
End RC__1.
End Mq2.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.

Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun QWxq_c1.Mq0 Qfw3_c1.Mq2 Qc3B Q5Rg.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 QmZZ Qsw7 QJjn QKQo Q8tj QRUw.Mq2.
Import QSL3.
Import Qvbw QYIF.
Import QnCn.Mq0 QR2u.

Import QbFI QXUB. Import QRBl. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QsKa.Mqd QlKV.Mqj QsKa.Mqg QsKa.Mq9 QJZd.Mq9 QsKa.Mqh Qw5U.Mq5 QsKa.Mqc QsKa.Mqb QlKV.Mqh QsKa.Mqe QlKV.Mqf. Import QlKV.Mq2 QsKa Q9O6.Mq1. Import Qiiq.

Import Qvmy Qawr Q30W.Mq4 Q2Do.Mq4.

Import Qu4M.Mq0.
Import Qwm6.Mq2.
Import QB6X.Mq0 Qoif.Mq6. Import QSHS.Mq1.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Q2qa.Mq0.sf_vocab ::= Q2qa.Mq0.mkr__sf_vocab_5. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Lemma unpoisoned_of_fshadow1 : forall m Fr (shb : list byte) (g0 g1 : nat),
bytes_at asegs m (Fr / 8 + A_SB) shb -> length shb = 16%nat -> Fr mod 128 = 0 -> 0 <= Fr ->
(g0 < g1)%nat -> (g1 <= 16)%nat ->
forallb (fun b => bv_unsigned b =? 0) (firstn (g1 - g0) (skipn g0 shb)) = true ->
unpoisoned asegs m A_SB (Fr + 8 * Z.of_nat g0) (8 * Z.of_nat (g1 - g0)).
Proof.
intros m Fr shb g0 g1 SH L AL F0 Hg Hg1 Z0.
assert (GZ : forall g : nat, (g0 <= g < g1)%nat -> bytes_at asegs m (Fr / 8 + A_SB + Z.of_nat g) [Z_to_bv 8 0]).
{ intros g Hgg. pose proof (Ql4f.Mq3.bytes_at_sub asegs m _ shb g 1 SH ltac:(lia)) as X.
assert (E : firstn 1 (skipn g shb) = [Z_to_bv 8 0]); [| rewrite E in X; exact X].
rewrite forallb_forall in Z0.
destruct (nth_error shb g) as [b|] eqn:Hb; [| apply nth_error_None in Hb; lia].
assert (Hin : In b (firstn (g1 - g0) (skipn g0 shb))).
{ apply (nth_error_In _ (g - g0)). rewrite nth_error_firstn. destruct (Nat.ltb_spec (g - g0) (g1 - g0)); [| lia]. rewrite nth_error_skipn. replace (g0 + (g - g0))%nat with g by lia. exact Hb. }
specialize (Z0 b Hin). apply Z.eqb_eq in Z0.
pose proof (@nth_error_split _ shb g b Hb) as (l1 & l2 & E & Hl1). rewrite E. rewrite <- Hl1, skipn_app, skipn_all, Nat.sub_diag. cbn. f_equal. apply bv_eq. rewrite Z0. reflexivity. }
assert (E1 : (Fr + 8 * Z.of_nat g0) / 8 = Fr / 8 + Z.of_nat g0) by (Z.div_mod_to_equations; lia).
assert (E2 : (Fr + 8 * Z.of_nat g0 + 8 * Z.of_nat (g1 - g0) - 1) / 8 = Fr / 8 + Z.of_nat g1 - 1) by (Z.div_mod_to_equations; lia).
unfold unpoisoned. split; [lia|]. split; [| split].
- intros g Hgr. rewrite E1, E2 in Hgr. replace (g + A_SB) with (Fr / 8 + A_SB + Z.of_nat (Z.to_nat (g - Fr / 8))) by lia. apply GZ. lia.
- exists 0. split; [| left; reflexivity]. rewrite E2. replace (Fr / 8 + Z.of_nat g1 - 1 + A_SB) with (Fr / 8 + A_SB + Z.of_nat (g1 - 1)) by lia. apply GZ. lia.
- intros w Hw. rewrite E1, E2 in Hw.
assert (EW : exists j : nat, (j < 2)%nat /\ w * 8 = Fr / 8 + A_SB + Z.of_nat (8 * j)).
{ exists (Z.to_nat (w - (Fr / 8 + A_SB) / 8)). unfold A_SB in *. split; Z.div_mod_to_equations; lia. }
destruct EW as (j & Hj & ->). exists (firstn 8 (skipn (8 * j) shb)). split.
+ rewrite firstn_length_le; [reflexivity | rewrite length_skipn; lia].
+ apply Ql4f.Mq3.bytes_at_sub; [exact SH | lia].
Qed.
Section MDcArr.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Notation wz := (Z_to_bv 64).
Notation jroot_repA := (jroot_rep A4H A4F).
Notation presxD := (QYIF.heap_presxD A4H).
Hypothesis SHALLOW : shallow_A_stmt HIx.
Hypothesis PUT : put_stmt_A HIx.

Lemma presxD_own : forall D0 D' L0 L' SP SP' m m',
presxD D' L' SP' m m' -> SP' <= SP -> (forall b, In b L0 -> In b L') ->
(forall a, D' <= a < D' + 8 -> ~ client_addr A4H L0 SP a) -> presxD D0 L0 SP m m'.
Proof.
intros D0 D' L0 L' SP SP' m m' H HS HL N a Ha Hc _. apply (H a Ha).
- destruct Hc as [Hc | [Hc | (b & Hb & Hr)]]; [left; lia | right; left; exact Hc | right; right; exists b; split; [apply HL; exact Hb | exact Hr]].
- intros Hd. apply (N a Hd). exact (client_addrx_addr A4H _ _ _ _ Hc).
Qed.

Lemma presxD_agree_blocks : forall D0 L0 SP m m' BSx,
presxD D0 L0 SP m m' -> (forall b, In b BSx -> In b L0) -> (forall a k, In (a, k) BSx -> D0 + 8 <= a \/ a + k <= D0) -> agree_on asegs BSx m m'.
Proof.
intros D0 L0 SP m m' BSx H HL N a Ha (b & Hb & Hr). apply (H a Ha).
- right; right. exists b. split; [apply HL; exact Hb | exact Hr].
- destruct b as [ba bn]. cbn [blk_addr blk_size fst snd] in Hr. pose proof (N _ _ Hb). lia.
Qed.

Lemma arr_nowD : forall A LBa LMx FRS' B mc mdc m BSx px tojs pb a AL ps,
HEAPAx A LBa LMx FRS' B mc mdc -> agree_on asegs BSx m mc -> incl BSx LBa -> In (px, 48) BSx -> incl AL BSx ->
rw_cells asegs m px (jhdr_cells JT_ARRAY 1 tojs pb 0 0 ++ [C8 (wz a)]) -> alist asegs A4F m AL a ps ->
exists arr size,
rw_cells asegs mc px (jhdr_cells JT_ARRAY 1 tojs pb 0 0 ++ [C8 (wz a)]) /\ 0 < px /\ px + 48 <= alloc_ceiling /\ px mod 8 = 0 /\
ro_cells asegs mc (px / 8 + A_SB) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] /\
px / 8 + A_SB + 6 <= alloc_ceiling /\
alist asegs A4F mc [(a, AL_SZ); (arr, 8 * size)] a ps /\ al_blkA a arr size /\
ro_cells asegs mc (a / 8 + A_SB) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] /\
bytes_at asegs mc (arr / 8 + A_SB) (shadow_bytes (8 * size)) /\ 0 <= size /\ arr / 8 + A_SB + size <= alloc_ceiling /\
Z.of_nat (length ps) <= size /\ AL = [(a, AL_SZ); (arr, 8 * size)].
Proof.
intros A LBa LMx FRS' B mc mdc m BSx px tojs pb a AL ps HP AG INC INp INAL HDR HAL.
pose proof alloc_ceiling_range as ACR.
destruct (alist_open asegs A4F m AL a ps HAL) as (arr & size & junk & EAL & OP).
exists arr, size.
assert (INpA : In (px, 48) LBa) by (apply INC; exact INp).
assert (INaA : In (a, 32) LBa) by (apply INC, INAL; rewrite EAL; left; reflexivity).
assert (INrA : In (arr, 8 * size) LBa) by (apply INC, INAL; rewrite EAL; right; left; reflexivity).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ px 48 HP ltac:(apply in_or_app; left; exact INpA)) as (_ & Hpal & Hplo & Hphi & _).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ a 32 HP ltac:(apply in_or_app; left; exact INaA)) as (_ & Haal & Halo & Hahi & _).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ arr (8 * size) HP ltac:(apply in_or_app; left; exact INrA)) as (Hrn & Hral & Hrlo & Hrhi & _).
split.
{ eapply rw_cells_agree; [exact HDR | exact AG |]. exists px, 48. split; [exact INp|]. unfold jhdr_cells. cbn. lia. }
split; [exact Hplo|]. split; [exact Hphi|]. split; [clear - Hpal; Z.div_mod_to_equations; lia|].
split.
{ pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ px 48 HP INpA) as SH. unfold shad in SH. apply shadow_ro_cells in SH.
cbn [hl_sb hl_segs hla_base A4L A4H] in SH. exact SH. }
split; [unfold A_SB; clear - Hphi ACR Hplo; Z.div_mod_to_equations; lia|].
split.
{ rewrite EAL in HAL. eapply (alist_agree asegs A4F); [exact HAL | exact AG |]. intros b Hb. apply INAL. rewrite EAL. exact Hb. }
split.
{ unfold al_blkA. split; [exact Halo|]. split; [clear - Haal; Z.div_mod_to_equations; lia|]. split; [exact Hahi|]. split; [exact Hrlo|]. split; [clear - Hral; Z.div_mod_to_equations; lia | exact Hrhi]. }
split.
{ pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ a 32 HP INaA) as SH. unfold shad in SH. apply shadow_ro_cells in SH.
cbn [hl_sb hl_segs hla_base A4L A4H] in SH. exact SH. }
split.
{ pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ arr (8 * size) HP INrA) as SH. unfold shad in SH.
cbn [hl_sb hl_segs hla_base A4L A4H] in SH. exact SH. }
destruct OP as (_ & _ & _ & Hlen & Hsz).
split; [lia|]. split; [unfold A_SB; clear - Hrhi ACR Hrlo Hrn; Z.div_mod_to_equations; lia|]. split; [exact Hlen | exact EAL].
Qed.

Variables (ra sp gp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : config) (LB BS LM : list blk) (FRS : list frame) (B0 : bud) (lo p D w : Z) (r : jroot) (T : TSet).
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOS : lo <= bv_unsigned sp - dc_stkA (rdepth r).
Hypothesis SPA : bv_unsigned sp mod 32 = 0.
Hypothesis HT : bv_unsigned sp <= hiA_top A4L HIx.
Hypothesis RA : bv_unsigned ra mod 2 = 0.
Hypothesis FRM0 : frm0 fc.
Hypothesis DLOC : arg_locA FRS D 8.
Hypothesis DAL : D mod 8 = 0.
Hypothesis NN : r <> JRnull.
Hypothesis JR0 : jroot_repA r m0 BS p.
Hypothesis Kont : forall ms' md' m' rv (A' : ASA A4L HIx) (B' : bud),
jo_post_frameDA D ra sp gp (wz A_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 (BS ++ LB) (LM ++ fr_ivs A4L FRS) lo rv m' ms' md' ->
lh_globA m' -> jroot_repA r m' BS p -> dc_resA HIx r BS LB LM FRS D w B0 m' md' rv A' B' ->
AJ5 A4L HIx A' T md' ms'.
Local Notation fk1_HEAPA := (Qoif.Mq6.fk1_HEAPA HIx) (only parsing).
Local Notation fk1_pres := (Qoif.Mq6.fk1_pres HIx) (only parsing).
Local Notation ASP := (Qoif.Mq6.ASP sp) (only parsing).
Local Notation dc_save := (Qoif.Mq6.dc_save ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) (only parsing).
Local Notation dc_inv := (Qoif.Mq6.dc_inv ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 md0 LB BS LM FRS lo D) (only parsing).
Local Notation dc_dst := (Qoif.Mq6.dc_dst D) (only parsing).
Local Notation dc_dfacts := (Qoif.Mq6.dc_dfacts HIx ra sp LM FRS D DLOC DAL) (only parsing).
Local Notation dc_dst_munch := (Qoif.Mq6.dc_dst_munch HIx ra sp LM FRS lo D LO DLOC DAL) (only parsing).
Local Notation dc_dsh_range := (Qoif.Mq6.dc_dsh_range HIx ra sp LM FRS D DLOC) (only parsing).
Local Notation dc_dst_pres := (Qoif.Mq6.dc_dst_pres HIx ra sp LM FRS D DLOC) (only parsing).
Local Notation dc_epi := (Qoif.Mq6.dc_epi HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB BS LM FRS B0 lo p D w r T LO LOS HT DLOC NN JR0 Kont) (only parsing).
Local Notation dc_scr := (Qoif.Mq6.dc_scr p) (only parsing).
Local Notation dc_tail0 := (Qoif.Mq6.dc_tail0 HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB BS LM FRS B0 lo p D w r T LO LOS SPA HT RA DLOC DAL NN JR0 Kont) (only parsing).

Lemma da_src_agree : forall Ax LBx Bx mx mdx Fr mc mdc, HEAPAx Ax LBx LM ((Fr, 1) :: FRS) Bx mx mdx -> incl BS LBx -> dc_inv mc mdc -> agree_on asegs BS m0 mc.
Proof.
intros Ax LBx Bx mx mdx Fr mc mdc HP Hi (_ & PX & _).
destruct (dc_dfacts _ _ _ _ _ _ HP) as (_ & _ & _ & _ & DBLK & _).
eapply presxD_agree_blocks; [exact PX | intros b Hb; apply in_or_app; left; apply in_or_app; left; exact Hb |].
intros a0 k0 Hin. pose proof (DBLK a0 k0 ltac:(apply in_or_app; left; apply Hi; exact Hin)). lia.
Qed.
Lemma da_src_now : forall Ax LBx Bx mx mdx Fr mc mdc, HEAPAx Ax LBx LM ((Fr, 1) :: FRS) Bx mx mdx -> incl BS LBx -> dc_inv mc mdc -> jroot_repA r mc BS p.
Proof.
intros Ax LBx Bx mx mdx Fr mc mdc HP Hi INV.
exact (QrIB.Mq0.jroot_rep_agree A4H A4F _ _ _ _ _ _ JR0 (da_src_agree _ _ _ _ _ _ _ _ HP Hi INV) (incl_refl _)).
Qed.

Notation own_W Fr := [(lo, bv_unsigned sp + -104); (Fr, Fr + 120); (Fr / 8 + 2147450880, Fr / 8 + 2147450880 + 16); (6444156, 6444160)].
Lemma dc_inv_own : forall Ax LBx Bx mx mdx Fr mc',
HEAPAx Ax LBx LM ((Fr, 1) :: FRS) Bx mx mdx -> incl (BS ++ LB) LBx ->
munch (own_W Fr) mx mc' -> wmono asegs mx mc' ->
dc_inv mx mdx -> stk asegs mc' lo ASP -> dc_save mc' -> dc_inv mc' mdx.
Proof.
intros Ax LBx Bx mx mdx Fr mc' HP Hi MU WM (VM & PX & _ & _ & G) ST SV.
pose proof LOS as LOSu. unfold dc_stkA, DC_F, DC_C in LOSu.
assert (RD0 : 0 <= rdepth r) by (destruct r; cbn [rdepth]; try lia; apply sdepth_nonneg).
pose proof (fk1_pres _ _ _ _ _ _ _ _ lo (bv_unsigned sp + -104) _ HP LO ltac:(lia) MU WM) as HPR.
split; [exact VM|]. split; [| split; [exact ST | split; [exact SV | eapply lh_globA_client; [exact HPR | exact G]]]].
eapply (QrIB.Mq0.presxD_trans A4H); [exact PX |]. apply (QrIB.Mq0.pres_presxD A4H). eapply heap_pres_weaken; [exact HPR | lia |].
intros b Hb. apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; apply Hi; exact Hb | apply in_or_app; right; exact Hb].
Qed.

Lemma da_own_outside : forall Ax LBx Bx mx mdx Fr x,
HEAPAx Ax LBx LM ((Fr, 1) :: FRS) Bx mx mdx -> incl (BS ++ LB) LBx -> 0 <= x < 2^64 -> Fr <= x < Fr + 120 ->
~ client_addr A4H ((BS ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) x.
Proof.
intros Ax LBx Bx mx mdx Fr x HP Hi Ha Hr Hc.
pose proof LOS as LOSu. unfold dc_stkA, DC_F, DC_C in LOSu.
assert (RD0 : 0 <= rdepth r) by (destruct r; cbn [rdepth]; try lia; apply sdepth_nonneg).
assert (INF : In (Fr, 1) ((Fr, 1) :: FRS)) by (left; reflexivity).
destruct (own_frame_fresh HIx Fr 1 LBx (BS ++ LB) LM FRS Bx Ax _ mdx HP Hi) as [OFF OFS].
assert (Ho : outside [(Fr, Fr + 120)] x).
{ eapply (QSHS.client_outsideF HIx Ax LBx LM ((Fr, 1) :: FRS) Bx ((BS ++ LB) ++ LM ++ fr_ivs A4L FRS) _ mdx [(Fr, Fr + 120)] (bv_unsigned sp) HP); [| lia | | exact Ha | exact Hc].
- intros b Hb. apply in_app_or in Hb as [Hb | Hb]; [left; apply in_or_app; left; apply Hi; exact Hb |].
apply in_app_or in Hb as [Hb | Hb]; [left; apply in_or_app; right; exact Hb | right; cbn [fr_ivs flat_map app]; right; right; exact Hb].
- apply Forall_cons; [| apply Forall_nil]. right; right; right. exists Fr, 1. split; [exact INF|]. split; [exact OFF|]. split; [exact OFS|]. left. cbn [fst snd]. rewrite fr_size_1. lia. }
cbn [outside] in Ho. lia.
Qed.

Lemma dc_dst_presxD : forall Ax LBx Bx mx mdx Fr D' L0 SP mc m' q,
HEAPAx Ax LBx LM ((Fr, 1) :: FRS) Bx mx mdx -> Fr <= D' -> D' + 8 <= Fr + 120 -> dc_dst mc q ->
presxD D' (L0 ++ LM ++ fr_ivs A4L ((Fr, 1) :: FRS)) SP mc m' -> dc_dst m' q.
Proof.
intros Ax LBx Bx mx mdx Fr D' L0 SP mc m' q HP HD1 HD2 [DC DSH] PX.
destruct (dc_dfacts _ _ _ _ _ _ HP) as (D1 & D2 & D3 & D4 & _ & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13).
destruct DLOC as (Fd & kd & HFd & H1 & H2).
assert (IND : In (Fd, kd) ((Fr, 1) :: FRS)) by (right; exact HFd).
split.
- eapply (QrIB.Mq0.presxD_rw_cells A4H); [exact PX | exact DC | | cbn [cells_size csize Nat.add]; lia].
eapply client_rangex_block; [apply in_or_app; right; apply in_or_app; right; apply fr_ivs_frame; exact IND | cbn; lia | cbn; lia].
- destruct DSH as [Hwf Hb]. split; [exact Hwf|].
eapply (QrIB.Mq0.presxD_bytes_at A4H); [exact PX | exact Hb | cbn [cells_bytes cbytes app length]; exact (dc_dsh_range _ _ _ _ _ _ (hl_volatile A4H) L0 SP HP) |].
cbn [cells_bytes cbytes app length]. clear - D8 D9 D10 HD1 HD2. lia.
Qed.

Variable kids : list (option jshape).
Hypothesis Er : r = JRtree (Sarr kids).
Hypothesis FRN : Z.of_nat (length FRS) + (1 + rdepth r) < 4096.
Hypothesis IH : forall s', In (Some s') kids -> DCOPY HIx (JRtree s').
Variables (pb a : Z) (PBS AL : list blk) (ps : list Z) (KBS : list (list blk)) (ws : list Z).
Hypothesis EBS : BS = ((p, 48) :: AL ++ concat KBS) ++ PBS.
Hypothesis OPB0 : opt_pbuf asegs m0 PBS pb.
Hypothesis HDR0 : rw_cells asegs m0 p (jhdr_cells JT_ARRAY 1 (fn_arr_to_json_string A4F) pb 0 0 ++ [C8 (wz a)]).
Hypothesis HAL0 : alist asegs A4F m0 AL a ps.
Hypothesis L1 : length ps = length kids.
Hypothesis L2 : length KBS = length kids.
Hypothesis KIDS0 : akids asegs A4F m0 kids ps KBS.
Hypothesis LW : length ws = length kids.
Hypothesis EW : w = 24 + arr_wsum ws.
Hypothesis NNW : Forall (fun x => 0 <= x) ws.
Hypothesis KW1 : forall i s bs, nth_error kids i = Some (Some s) -> nth_error KBS i = Some bs -> exists Yi Ri, jtx s (bs ++ Yi) = Some (nth i ws 0, Ri).
Hypothesis KW2 : forall i, nth_error kids i = Some None -> nth i ws 0 = NULL_W.
Hypothesis WLT : w < 2^28.
Hypothesis BBW : DC_KB * w <= bB B0.
Hypothesis BDW : w <= bD B0.

Lemma PhiA_nonneg : forall cap len, arr_inv cap len -> 0 <= PhiA cap len.
Proof. intros cap len (H32 & Hl & Hc). unfold PhiA. lia. Qed.

Definition da_own (mc : word -> option byte) (Fr : Z) (v2 : word) (b8 : Z) : Prop :=
exists (j24 j16 jf1 jf2 : list byte) (w1 w2 : word),
rw_cells asegs mc ASP (dc_scr Fr (wz 0) j24 (C8 (wz 0)) j16) /\
rw_cells asegs mc Fr [C8 (wz 1102416563); C8 w1; C8 w2; CB 40 jf1; C8 v2; CB 48 jf2] /\
rw_cells asegs mc (Fr / 8 + 2147450880) [C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242);
C1 (Z_to_bv 8 b8); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].

Lemma dc_arr_fail :
forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x19 x20 x21 x22 x23 x24 x26 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
(mc : word -> option byte) (mdc : config) (A : ASA A4L HIx) (Bc : bud) (Fr v2 q : Z) (VBS CBS REM : list blk),
dc_inv mc mdc -> fsaved F F1 -> frm0 fc1 ->
HEAPAx A (BS ++ CBS ++ VBS ++ REM ++ LB) LM ((Fr, 1) :: FRS) Bc mc mdc ->
da_own mc Fr (wz v2) 0 -> fresA mc VBS v2 -> jroot_repA r mc BS p ->
dc_dst mc q -> fresA mc CBS q ->
bD B0 - w <= bD Bc -> bB B0 - DC_KB * w + 512 * (Z.of_nat (length CBS) + Z.of_nat (length VBS)) <= bB Bc ->
AJ5 A4L HIx A T mdc
(MS (mkR x1 (wz ASP) gp (wz A_TP) t0 t1 t2 sp (wz ASP) a0 a1 a2 a3 a4 a5 a6 a7
(wz Fr) x19 x20 x21 x22 x23 x24 (wz (Fr + 64)) x26 (wz (Fr / 8 + 2147450880)) t3 t4 t5 t6)
F1 (wz 0xa1a98) fc1 None mc (seg_rom asegs)).
Proof.
intros until REM. intros INV FS FRM1 HP (j24 & j16 & jf1 & jf2 & w1 & w2 & SCR & FF & FSH) FRV JRc DD FRC BDc BBc.
pose proof INV as (VMi & PRESi & STi & SAVEi & Gi). unfold dc_save in SAVEi.
pose proof LOS as LOSu. unfold dc_stkA, DC_F, DC_C in LOSu. unfold ASP, dc_scr in *.
assert (RD0 : 0 <= rdepth r) by (destruct r; cbn [rdepth]; try lia; apply sdepth_nonneg).
pose proof alloc_ceiling_range as ACR.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
destruct (dc_dfacts _ _ _ _ _ _ HP) as (D1 & D2 & D3 & D4 & DBLK & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13).
set (sh := Fr / 8 + 2147450880) in *.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. change (hl_segs A4L) with asegs in MI.
destruct (heapA_errno A4L HIx _ _ _ _ _ _ _ HP) as (errs & ERRs).
pose proof (wmono_refl asegs mc) as WM. pose proof (munch_refl [(lo, bv_unsigned sp + -104); (Fr, Fr + 120); (sh, sh + 16); (6444156, 6444160)] mc) as MU.

assert (PP : exists so, QPZI.Mq4.put_pre A4H A4F so mc VBS v2 1).
{ destruct FRV as [[-> ->] | (Hv & s & JV)]; [exists None; split; reflexivity | exists (Some s); split; [exact Hv | split; [lia | exact JV]]]. }
destruct PP as (so & PP).
assert (HPp : HEAPAx A (VBS ++ (BS ++ CBS ++ REM ++ LB)) LM ((Fr, 1) :: FRS) Bc mc mdc).
{ eapply (heapA_perm A4L HIx); [exact HP | perm | apply Permutation_refl | apply Permutation_refl]. }
assert (V2R : 0 <= v2 < 2^64).
{ destruct FRV as [[-> _] | (Hv & s & JV)]; [lia|]. destruct (jval_root_in asegs A4F _ _ _ _ _ JV) as (n & Hin & Hn).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ v2 n HPp ltac:(apply in_or_app; left; apply in_or_app; left; exact Hin)) as (_ & _ & Hlo & Hhi & _). unfold alloc_ceiling, sp_window_lo, stack_max_size in Hhi. lia. }
stash PRESi. stash Gi. stash FRC. stash JRc. stash DD.
unfold A_TP. a4l.
reenterA asegs A4L HIx asegs_wx HP.
step. step.

assert (PC : put_costA so 1 VBS <= bB Bc).
{ unfold put_costA. destruct so; [change (1 =? 1) with true; cbv iota|]; unfold DC_KB in *; lia. }
evt_done5.
eapply PUT with (LB := BS ++ CBS ++ REM ++ LB) (LM := LM) (FRS := (Fr, 1) :: FRS) (B := Bc) (lo := lo) (errv := errs) (s := so) (BS := VBS) (p := v2) (rc := 1);
[ exact HPp | exact PP | reflexivity | rewrite unsigned_lit by lia; exact STi | exact LO | rewrite unsigned_lit by lia; unfold put_stk_A; lia
| rewrite unsigned_lit by lia; clear - SPA; Z.div_mod_to_equations; lia | rewrite unsigned_lit by lia; lia | exact ERRs | reflexivity | reflexivity | exact PC | ].
intros ms2 md2 A2 (m2 & rr & B2 & RS2 & VM2 & ST2 & HPR2 & ERR2 & BB2 & BD2 & OUT2).
destruct RS2 as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & F2 & fc2 & -> & FS2 & FRM2).

destruct OUT2 as [[_ HP2] | (s' & _ & Habs & _)]; [| exfalso; lia].
rewrite ?(unsigned_lit (bv_unsigned sp + -192)) in ST2 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -192)) in HPR2 by lia.
change (hl_segs A4L) with asegs in *.
assert (HPRX : forall A0 cs0, rw_cells asegs mc A0 cs0 ->
client_range A4H ((BS ++ CBS ++ REM ++ LB) ++ LM ++ fr_ivs A4L ((Fr, 1) :: FRS)) (bv_unsigned sp + -192) A0 (Z.of_nat (cells_size cs0)) -> rw_cells asegs m2 A0 cs0).
{ intros A0 cs0 H1 H2. exact (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2 H1 H2). }
apply HPRX in SCR; [| left; lia]. apply HPRX in SAVEi; [| left; lia].
apply HPRX in FF; [| eapply client_range_block; [apply in_or_app; right; apply in_or_app; right; left; reflexivity | cbn [fr_base fst]; lia | cbn [cells_size csize Nat.add fr_base fr_class fst snd]; rewrite fr_size_1; lia]].
apply HPRX in FSH; [| eapply client_range_block; [apply in_or_app; right; apply in_or_app; right; right; left; reflexivity | unfold shad; cbn [fr_base fst hl_sb A4L]; unfold A_SB; fold sh; lia
| unfold shad; cbn [cells_size csize Nat.add fr_base fr_class fst snd hl_sb A4L]; rewrite fr_shadow_len_1; unfold A_SB; fold sh; lia]].
unstash DD. pose proof (dc_dst_pres _ _ _ _ _ _ _ _ _ _ _ HP2 DD HPR2) as DD2. clear DD HPRX. stash DD2.
clear MU WM MI.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI2. change (hl_segs A4L) with asegs in MI2.
pose proof (wmono_refl asegs m2) as WM2. pose proof (munch_refl [(lo, bv_unsigned sp + -104); (Fr, Fr + 120); (sh, sh + 16); (6444156, 6444160)] m2) as MU2.
replace (ret_pc (wz 662176)) with (wz 662176) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
stash SAVEi.
reenterA asegs A4L HIx asegs_wx HP2.
step. stepz. step. step. step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) => rename mq into mX end.
pose proof (fk1_HEAPA _ _ _ _ _ _ _ _ lo (bv_unsigned sp + -104) _ HP2 LO ltac:(lia) MU2 WM2 MI2) as HPY.
pose proof (fk1_pres _ _ _ _ _ _ _ _ lo (bv_unsigned sp + -104) _ HP2 LO ltac:(lia) MU2 WM2) as HPR2X.
unstash SAVEi. apply (rw_cells_transport asegs [(lo, bv_unsigned sp + -104); (Fr, Fr + 120); (sh, sh + 16); (6444156, 6444160)] _ mX) in SAVEi; [| exact MU2 | exact WM2 | cbn [disjoint_from]; simpl_sizes; lia].
unstash DD2. pose proof (dc_dst_munch _ _ _ _ _ _ _ _ _ HP2 DD2 MU2 WM2) as [DCX DSHX].
assert (HPRcX : heap_pres A4H ((BS ++ CBS ++ REM ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) mc mX).
{ eapply heap_pres_trans; [eapply heap_pres_weaken; [exact HPR2 | lia |] | eapply heap_pres_weaken; [exact HPR2X | lia | intros b Hb; exact Hb]].
intros b Hb. apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; exact Hb | apply in_or_app; right].
apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; exact Hb | apply in_or_app; right; cbn [fr_ivs flat_map app]; right; right; exact Hb]. }
assert (AGX : forall BSx, incl BSx (BS ++ CBS ++ REM ++ LB) -> agree_on asegs BSx mc mX).
{ intros BSx Hi. eapply (agree_of_heap_pres asegs A4H); [exact HPRcX | reflexivity | intros b Hb; apply in_or_app; left; apply Hi; exact Hb]. }
unstash JRc. unstash PRESi. unstash Gi. unstash FRC.
evt_done5.
replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 (2^64 - 1)) by (apply bv_eq; vm_compute; reflexivity).
eapply (dc_epi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F2 fc2 mX md2 A2 B2 (BS ++ CBS ++ REM ++ LB) Fr (2^64 - 1)).
- split; [eapply model_vm_only_trans; [exact VMi | exact VM2] |].
split; [eapply (QrIB.Mq0.presxD_trans A4H); [exact PRESi |]; apply (QrIB.Mq0.pres_presxD A4H); eapply heap_pres_weaken; [exact HPRcX | lia |] |].
{ intros b Hb. apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left | apply in_or_app; right; exact Hb].
apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; exact Hb | apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; exact Hb]. }
split; [exact ST2 |].
split; [unfold dc_save; exact SAVEi |]. eapply lh_globA_client; [exact HPRcX | exact Gi].
- eapply fsaved_trans; [exact FS | exact FS2].
- apply FRM2. exact FRM1.
- exact HPY.
- exact SCR.
- reflexivity.
- exact FF.
- reflexivity.
- exact FSH.
- eapply (QrIB.Mq0.jroot_rep_agree A4H A4F); [exact JRc | apply (AGX BS); apply incl_appl; apply incl_refl | apply incl_refl].
- split; [lia|]. right. split; [reflexivity|]. exists q, CBS, REM. split; [reflexivity|]. split; [exact DCX|].
split; [eapply fresA_agree; [exact FRC | apply (AGX CBS); apply incl_appr; apply incl_appl; apply incl_refl | apply incl_refl] |].
assert (VL : put_costA so 1 VBS <= 512 * Z.of_nat (length VBS)) by (unfold put_costA; destruct so; [change (1 =? 1) with true; cbv iota; lia | destruct PP as [_ ->]; cbn; lia]).
lia.
Qed.

Lemma dc_arr_add :
forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x21 x23 x24 x26 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
(mc : word -> option byte) (mdc : config) (A : ASA A4L HIx) (Bc : bud) (Fr v q : Z) (kids' : list (option jshape)) (vs : option jshape) (VBS CBS REM : list blk),
dc_inv mc mdc -> fsaved F F1 -> frm0 fc1 ->
HEAPAx A (BS ++ CBS ++ VBS ++ REM ++ LB) LM ((Fr, 1) :: FRS) Bc mc mdc ->
da_own mc Fr (wz v) 0 -> jroot_repA r mc BS p ->
q <> 0 -> dc_dst mc q -> jval asegs A4F (Sarr kids') mc CBS q 1 -> jopt asegs A4F vs mc VBS v ->
Z.of_nat (length kids') + 1 < 2^28 ->
bD B0 - w <= bD Bc ->
bB B0 - DC_KB * w + 512 * (Z.of_nat (length CBS) + Z.of_nat (length VBS)) + arr_add_costA (arr_capA CBS) (Z.of_nat (length kids')) <= bB Bc ->
(forall (y1 u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 : word) (F2 : bvmap 5 word) (fc2 : bv 32)
(m2 : word -> option byte) (md2 : config) (A2 : ASA A4L HIx) (B2 : bud) (CBS' : list blk),
dc_inv m2 md2 -> fsaved F F2 -> frm0 fc2 ->
HEAPAx A2 (BS ++ CBS' ++ REM ++ LB) LM ((Fr, 1) :: FRS) B2 m2 md2 ->
da_own m2 Fr (wz v) 0 -> jroot_repA r m2 BS p ->
dc_dst m2 q -> jval asegs A4F (Sarr (kids' ++ [vs])) m2 CBS' q 1 ->
Z.of_nat (length CBS') = Z.of_nat (length CBS) + Z.of_nat (length VBS) ->
arr_grownA (arr_capA CBS) (Z.of_nat (length kids')) (arr_capA CBS') ->
bB Bc - arr_add_costA (arr_capA CBS) (Z.of_nat (length kids')) <= bB B2 -> bD Bc <= bD B2 ->
(forall wq wv, jtx (Sarr kids') CBS = Some (wq, []) -> jtx_opt vs VBS = Some (wv, []) -> jtx (Sarr (kids' ++ [vs])) CBS' = Some (wq + (2 + wv), [])) ->
AJ5 A4L HIx A2 T md2
(MS (mkR y1 (wz ASP) gp (wz A_TP) u0 u1 u2 sp (wz ASP) (wz 0) b1 b2 b3 b4 b5 b6 b7
(wz Fr) (wz (D / 8 + 2147450880)) (wz D) x21 (wz 2147450880) x23 x24 (wz (Fr + 64)) x26 (wz (Fr / 8 + 2147450880)) u3 u4 u5 u6)
F2 (wz 0xa1974) fc2 None m2 (seg_rom asegs))) ->
AJ5 A4L HIx A T mdc
(MS (mkR x1 (wz ASP) gp (wz A_TP) t0 t1 t2 sp (wz ASP) a0 a1 a2 a3 a4 a5 a6 a7
(wz Fr) (wz (D / 8 + 2147450880)) (wz D) x21 (wz 2147450880) x23 x24 (wz (Fr + 64)) x26 (wz (Fr / 8 + 2147450880)) t3 t4 t5 t6)
F1 (wz 0xa1938) fc1 None mc (seg_rom asegs)).
Proof.
intros until REM. intros INV FS FRM1 HP OWN JRc Hq DD JQ JOB Hlen28 BDc BBc KADD.
pose proof OWN as (j24 & j16 & jf1 & jf2 & w1 & w2 & SCR & FF & FSH).
pose proof INV as (VMi & PRESi & STi & SAVEi & Gi). unfold dc_save in SAVEi.
pose proof LOS as LOSu. unfold dc_stkA, DC_F, DC_C in LOSu. unfold ASP, dc_scr in *.
assert (RD0 : 0 <= rdepth r) by (destruct r; cbn [rdepth]; try lia; apply sdepth_nonneg).
pose proof alloc_ceiling_range as ACR.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
destruct (dc_dfacts _ _ _ _ _ _ HP) as (D1 & D2 & D3 & D4 & DBLK & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13).
pose proof DD as [DC DSH]. pose proof (rw_cells_bound asegs mc D _ DC) as DR. cbn [cells_size csize Nat.add] in DR.
set (sh := Fr / 8 + 2147450880) in *.

pose proof (arr_capA_jval _ _ _ _ _ JQ) as (a_ & arr_ & rest_ & EABS & Hcap1 & Hcap2 & Hcap3).
destruct (sarr_open asegs A4F _ _ _ _ _ JQ) as (pbq & PBSq & qa & ALq & psq & KBSq & ECBS & OPBq & HDRq & HALq & Lq1 & Lq2 & KIDSq).
pose proof HALq as (qarr & cap & ajunk & EALq & Hlenq & Hszq & _). subst ALq.
assert (Ecap : cap = arr_capA CBS /\ a_ = qa /\ arr_ = qarr) by (rewrite EABS in ECBS; cbn [app] in ECBS; injection ECBS; intros; lia).
destruct Ecap as (Ecap & -> & ->). rewrite <- Ecap in *. clear EABS rest_ Hcap1 Hcap2 Hcap3.
set (LBR := (q, 48) :: concat KBSq ++ PBSq ++ VBS ++ BS ++ REM ++ LB).
assert (HPa : HEAPAx A ((qa, 32) :: (qarr, 8 * cap) :: LBR) LM ((Fr, 1) :: FRS) Bc mc mdc).
{ eapply (heapA_perm A4L HIx); [exact HP | rewrite ECBS; unfold LBR; perm | apply Permutation_refl | apply Permutation_refl]. }

assert (INq : In (q, 48) LBR) by (left; reflexivity).
assert (HiK : incl (concat KBSq) LBR) by (intros b Hb; right; apply in_or_app; left; exact Hb).
assert (HiP : incl PBSq LBR) by (intros b Hb; right; apply in_or_app; right; apply in_or_app; left; exact Hb).
assert (HiV : incl VBS LBR) by (intros b Hb; right; apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; exact Hb).
assert (HiB : incl BS LBR) by (intros b Hb; right; apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; exact Hb).
assert (Hv : 0 <= v /\ v + 1 <= alloc_ceiling).
{ destruct vs as [s'|]; cbn in JOB.
- destruct JOB as [Hv0 J]. destruct (jval_root_in asegs A4F _ _ _ _ _ J) as (n & Hin & Hn).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ v n HPa ltac:(apply in_or_app; left; right; right; apply HiV; exact Hin)) as (_ & _ & Hlo & Hhi & _). lia.
- destruct JOB as [-> _]. unfold alloc_ceiling, sp_window_lo, stack_max_size. lia. }
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hv.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. change (hl_segs A4L) with asegs in MI.
destruct (heapA_errno A4L HIx _ _ _ _ _ _ _ HP) as (errs & ERRs).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ q 48 HPa ltac:(apply in_or_app; left; right; right; exact INq)) as (_ & Hqal & Hqlo & Hqhi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hqhi.
pose proof (blk_gran0A HIx _ _ _ _ _ _ _ q 48 5 HPa ltac:(right; right; exact INq) ltac:(lia) ltac:(lia)) as SHq5.
replace (q / 8 + 2147450880 + 5) with (q / 8 + 2147450885) in SHq5 by lia.
unfold jhdr_cells in HDRq. cbn [app] in HDRq.
pose proof (wmono_refl asegs mc) as WM. pose proof (munch_refl [(lo, bv_unsigned sp + -104); (Fr, Fr + 120); (sh, sh + 16); (6444156, 6444160)] mc) as MU.
stash PRESi. stash Gi. stash JRc. stash JQ. stash JOB. stash OPBq. stash KIDSq. stash HALq. stash KADD. stash OWN. stash INV. stash DD.
unfold A_TP. a4l.
reenterA asegs A4L HIx asegs_wx HP.
step. rewrite ?zxb_zero. step. if_false.
step. step. if_falsex.
step. step. ub_resolve.
step. asan_chkA.
step. step. step.

unstash HALq.
assert (BBadd : cap <= Z.of_nat (length psq) + 1 -> al_add_costB cap <= bB Bc).
{ intros Hge. unfold al_add_costB, arr_add_costA in *. rewrite Lq1 in Hge. destruct (Z.ltb_spec (Z.of_nat (length kids') + 1) cap); [lia|]. unfold DC_KB in *. lia. }
evt_done5.
eapply (array_list_add_A_cps HIx (wz 661872) (wz (bv_unsigned sp + -192)) gp sp (wz (bv_unsigned sp + -192)) (wz Fr) (wz (D / 8 + 2147450880)) (wz D) x21 (wz 2147450880) x23 x24 (wz (Fr + 64)) x26 (wz sh)
F1 fc1 mc mdc LBR LM ((Fr, 1) :: FRS) Bc lo qa qarr cap v psq T);
[ exact HPa | exact HALq | rewrite Lq1; lia | lia
| rewrite unsigned_lit by lia; exact STi | exact LO | rewrite unsigned_lit by lia; lia
| rewrite unsigned_lit by lia; clear - SPA; Z.div_mod_to_equations; lia | rewrite unsigned_lit by lia; lia
| exact ERRs | reflexivity | reflexivity | reflexivity | exact BBadd | exact (proj2 (heapA_budget A4L HIx _ _ _ _ _ _ _ HP)) | ].
intros ms' md' A' (m' & rr & errv' & arr' & size' & B' & RS & VM' & ST' & HPR' & ERR' & BD' & HP' & OUT).
destruct RS as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & F2 & fc2 & -> & FS2 & FRM2).
rewrite ?(unsigned_lit (bv_unsigned sp + -192)) in ST', HPR' by lia.
change (hl_segs A4L) with asegs in *.
assert (AG : agree_on asegs LBR mc m') by (eapply (agree_of_heap_pres asegs A4H); [exact HPR' | reflexivity | intros b Hb; apply in_or_app; left; exact Hb]).
assert (HPRX : forall A0 cs0, rw_cells asegs mc A0 cs0 ->
client_range A4H (LBR ++ LM ++ fr_ivs A4L ((Fr, 1) :: FRS)) (bv_unsigned sp + -192) A0 (Z.of_nat (cells_size cs0)) -> rw_cells asegs m' A0 cs0).
{ intros A0 cs0 H1 H2. exact (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR' H1 H2). }
apply HPRX in SCR; [| left; lia]. apply HPRX in SAVEi; [| left; lia].
apply HPRX in FF; [| eapply client_range_block; [apply in_or_app; right; apply in_or_app; right; left; reflexivity | cbn [fr_base fst]; lia | cbn [cells_size csize Nat.add fr_base fr_class fst snd]; rewrite fr_size_1; lia]].
apply HPRX in FSH; [| eapply client_range_block; [apply in_or_app; right; apply in_or_app; right; right; left; reflexivity | unfold shad; cbn [fr_base fst hl_sb A4L]; unfold A_SB; fold sh; lia
| unfold shad; cbn [cells_size csize Nat.add fr_base fr_class fst snd hl_sb A4L]; rewrite fr_shadow_len_1; unfold A_SB; fold sh; lia]].
apply HPRX in HDRq; [| eapply client_range_block; [apply in_or_app; left; exact INq | lia | cbn [cells_size csize Nat.add]; lia]].
unstash DD. pose proof (dc_dst_pres _ _ _ _ _ _ _ _ _ _ _ HP DD HPR') as DD'. clear HPRX.
unstash JRc. pose proof (QrIB.Mq0.jroot_rep_agree A4H A4F _ _ _ _ _ _ JRc AG HiB) as JRc'.
unstash PRESi. unstash Gi.
assert (INV' : dc_inv m' md').
{ split; [eapply model_vm_only_trans; [exact VMi | exact VM'] |].
split; [eapply (QrIB.Mq0.presxD_trans A4H); [exact PRESi |]; apply (QrIB.Mq0.pres_presxD A4H); eapply heap_pres_weaken; [exact HPR' | lia |] |].
{ intros b Hb. apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left | apply in_or_app; right].
- apply in_app_or in Hb as [Hb | Hb]; [apply HiB; exact Hb |]. unfold LBR. right. apply in_or_app; right. apply in_or_app; right. apply in_or_app; right. apply in_or_app; right. apply in_or_app; right. exact Hb.
- apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; exact Hb | apply in_or_app; right; cbn [fr_ivs flat_map app]; right; right; exact Hb]. }
split; [exact ST' |]. split; [unfold dc_save; exact SAVEi |]. eapply lh_globA_client; [exact HPR' | exact Gi]. }
assert (OWN' : da_own m' Fr (wz v) 0) by (exists j24, j16, jf1, jf2, w1, w2; split; [exact SCR | split; [exact FF | exact FSH]]).
unstash OPBq. unstash KIDSq. unstash JOB.
pose proof (opt_pbuf_agree _ _ _ _ _ _ OPBq AG HiP) as OPBq'.
pose proof (akids_agree _ _ _ _ _ _ _ _ KIDSq AG HiK) as KIDSq'.
pose proof (jopt_agree _ _ _ _ _ _ _ _ JOB AG HiV) as JOB'.

destruct OUT as [(-> & -> & -> & Hgr & BBf & AL') | (-> & AL' & CASES)].
-
assert (JQ' : jval asegs A4F (Sarr kids') m' CBS q 1).
{ eapply (sarr_close asegs A4F) with (AL := [(qa, 32); (qarr, 8 * cap)]) (KBS := KBSq) (PBS := PBSq) (pb := pbq) (a := qa) (ps := psq);
[exact ECBS | exact OPBq' | unfold jhdr_cells; cbn [app]; exact HDRq | exact AL' | exact Lq1 | exact Lq2 | exact KIDSq']. }
assert (HPf : HEAPAx A' (BS ++ CBS ++ VBS ++ REM ++ LB) LM ((Fr, 1) :: FRS) B' m' md').
{ eapply (heapA_perm A4L HIx); [exact HP' | rewrite ECBS; unfold LBR; perm | apply Permutation_refl | apply Permutation_refl]. }
replace (ret_pc (wz 661872)) with (wz 661872) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
reenterA asegs A4L HIx asegs_wx HPf.
step. if_lit.
evt_done5.
eapply dc_arr_fail with (v2 := v) (q := q) (VBS := VBS) (CBS := CBS) (REM := REM);
[ exact INV' | eapply fsaved_trans; [exact FS | exact FS2] | apply FRM2; exact FRM1 | exact HPf | exact OWN'
| destruct vs as [s'|]; [right; destruct JOB' as [Hv0 J]; split; [exact Hv0 | exists s'; exact J] | left; exact JOB']
| exact JRc' | exact DD' | right; split; [exact Hq | exists (Sarr kids'); exact JQ'] | lia | ].
unfold al_add_costB, arr_add_costA in *. rewrite Lq1 in Hgr. destruct (Z.ltb_spec (Z.of_nat (length kids') + 1) cap); lia.

-
set (CBS' := ((q, 48) :: [(qa, 32); (arr', 8 * size')] ++ concat (KBSq ++ [VBS])) ++ PBSq).
assert (JQ' : jval asegs A4F (Sarr (kids' ++ [vs])) m' CBS' q 1).
{ eapply (sarr_close asegs A4F) with (ps := psq ++ [v]); [reflexivity | exact OPBq' | unfold jhdr_cells; cbn [app]; exact HDRq | exact AL' | | |].
- rewrite !length_app. cbn [length]. lia.
- rewrite !length_app. cbn [length]. lia.
- apply akids_app; [exact KIDSq' | apply akids_one; exact JOB']. }
assert (HPs : HEAPAx A' (BS ++ CBS' ++ REM ++ LB) LM ((Fr, 1) :: FRS) B' m' md').
{ unfold CBS'. rewrite concat_app. cbn [concat]. rewrite app_nil_r.
eapply (heapA_perm A4L HIx); [exact HP' | unfold LBR; perm | apply Permutation_refl | apply Permutation_refl]. }
replace (ret_pc (wz 661872)) with (wz 661872) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
reenterA asegs A4L HIx asegs_wx HPs.
step. if_lit.
evt_done5. unstash KADD.
eapply (KADD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F2 fc2 m' md' A' B' CBS');
[ exact INV' | eapply fsaved_trans; [exact FS | exact FS2] | apply FRM2; exact FRM1 | exact HPs | exact OWN' | exact JRc' | exact DD' | exact JQ' | | | | exact BD' | ].
+ unfold CBS'. rewrite ECBS. rewrite concat_app. cbn [concat]. rewrite app_nil_r. rewrite ?length_app. cbn [length]. rewrite ?length_app. cbn [length]. clear. Zify.zify. unfold blk in *. lia.
+ unfold arr_grownA, arr_capA, CBS'. cbn [app nth snd]. rewrite ?Lq1 in CASES.
destruct CASES as [(-> & -> & Hlt & _) | (-> & Hge & _)]; [left | right]; Z.div_mod_to_equations; lia.
+ unfold al_add_costB, arr_add_costA in *. rewrite ?Lq1 in CASES.
destruct (Z.ltb_spec (Z.of_nat (length kids') + 1) cap); destruct CASES as [(_ & _ & Hlt & BBx) | (_ & Hge & BBx)]; lia.
+ intros wq wv Hw Hwv. unstash KIDSq. rewrite ECBS in Hw.
exact (arr_add_jtx asegs A4F mc kids' psq KBSq PBSq (q, 48) (qa, 32) (qarr, 8 * cap) (arr', 8 * size') vs VBS wq wv KIDSq Hw Hwv).
Qed.

Definition da_copy (mc : word -> option byte) (Bc : bud) (ii : nat) (q : Z) (CBS : list blk) (acc : Z) : Prop :=
exists (kids' : list (option jshape)) (wq : Z),
q <> 0 /\ dc_dst mc q /\ jval asegs A4F (Sarr kids') mc CBS q 1 /\ length kids' = ii /\ okmax kids' <= okmax kids /\
jtx (Sarr kids') CBS = Some (wq, []) /\ wq <= acc /\
arr_inv (arr_capA CBS) (Z.of_nat ii) /\
bD B0 - acc <= bD Bc /\ bB B0 - DC_KB * acc + 512 * Z.of_nat (length CBS) + PhiA (arr_capA CBS) (Z.of_nat ii) <= bB Bc.

Lemma da_copy_own : forall Ax LBx Bx mx mdx Fr mc' Bc ii q CBS acc,
HEAPAx Ax LBx LM ((Fr, 1) :: FRS) Bx mx mdx -> incl CBS LBx ->
munch (own_W Fr) mx mc' -> wmono asegs mx mc' ->
da_copy mx Bc ii q CBS acc -> da_copy mc' Bc ii q CBS acc.
Proof.
intros Ax LBx Bx mx mdx Fr mc' Bc ii q CBS acc HP Hi MU WM (kids' & wq & Hq & DD & JQ & REST).
pose proof LOS as LOSu. unfold dc_stkA, DC_F, DC_C in LOSu.
assert (RD0 : 0 <= rdepth r) by (destruct r; cbn [rdepth]; try lia; apply sdepth_nonneg).
pose proof (fk1_pres _ _ _ _ _ _ _ _ lo (bv_unsigned sp + -104) _ HP LO ltac:(lia) MU WM) as HPR.
exists kids', wq. split; [exact Hq|]. split; [exact (dc_dst_munch _ _ _ _ _ _ _ _ _ HP DD MU WM) |]. split; [| exact REST].
eapply (jval_agree asegs A4F); [exact JQ | | exact Hi].
eapply (agree_of_heap_pres asegs A4H); [exact HPR | reflexivity | intros b Hb; apply in_or_app; left; exact Hb].
Qed.

Lemma dc_arr_next :
forall (ii : nat) (y1 u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 : word) (F2 : bvmap 5 word) (fc2 : bv 32)
(m2 : word -> option byte) (md2 : config) (A2 : ASA A4L HIx) (B2 : bud) (Fr q acc : Z) (v2 : word) (CBS REM : list blk),
(S ii <= length kids)%nat ->
dc_inv m2 md2 -> fsaved F F2 -> frm0 fc2 ->
HEAPAx A2 (BS ++ CBS ++ REM ++ LB) LM ((Fr, 1) :: FRS) B2 m2 md2 ->
da_own m2 Fr v2 0 ->
da_copy m2 B2 (S ii) q CBS acc -> acc + arr_wsum (skipn (S ii) ws) = w ->
((S ii < length kids)%nat ->
forall (mc : word -> option byte),
dc_inv mc md2 -> HEAPAx A2 (BS ++ CBS ++ REM ++ LB) LM ((Fr, 1) :: FRS) B2 mc md2 ->
da_own mc Fr v2 248 -> da_copy mc B2 (S ii) q CBS acc ->
AJ5 A4L HIx A2 T md2
(MS (mkR y1 (wz ASP) gp (wz A_TP) u0 u1 u2 sp (wz ASP) (wz (2^64 - 8)) b1 b2 b3 b4 b5 b6 b7
(wz Fr) (wz (D / 8 + 2147450880)) (wz D) (wz ((p + 40) / 8 + 2147450880)) (wz 2147450880) (wz (p + 40))
(wz (Z.of_nat (length kids))) (wz (Fr + 64)) (wz (Z.of_nat (S ii))) (wz (Fr / 8 + 2147450880)) u3 u4 u5 u6)
F2 (wz 0xa18e4) fc2 None mc (seg_rom asegs))) ->
AJ5 A4L HIx A2 T md2
(MS (mkR y1 (wz ASP) gp (wz A_TP) u0 u1 u2 sp (wz ASP) (wz 0) b1 b2 b3 b4 b5 b6 b7
(wz Fr) (wz (D / 8 + 2147450880)) (wz D) (wz ((p + 40) / 8 + 2147450880)) (wz 2147450880) (wz (p + 40))
(wz (Z.of_nat (length kids))) (wz (Fr + 64)) (wz (Z.of_nat ii)) (wz (Fr / 8 + 2147450880)) u3 u4 u5 u6)
F2 (wz 0xa1974) fc2 None m2 (seg_rom asegs)).
Proof.
intros until REM. intros Hii INV FS FRM2 HP OWN COPY ACC KLOOP.
pose proof OWN as (j24 & j16 & jf1 & jf2 & w1 & w2 & SCR & FF & FSH).
pose proof INV as (VMi & PRESi & STi & SAVEi & Gi). unfold dc_save in SAVEi.
pose proof LOS as LOSu. unfold dc_stkA, DC_F, DC_C in LOSu. unfold ASP, dc_scr in *.
assert (RD0 : 0 <= rdepth r) by (destruct r; cbn [rdepth]; try lia; apply sdepth_nonneg).
pose proof alloc_ceiling_range as ACR.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
destruct (dc_dfacts _ _ _ _ _ _ HP) as (D1 & D2 & D3 & D4 & DBLK & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13).
set (sh := Fr / 8 + 2147450880) in *.

assert (HiB : incl BS (BS ++ CBS ++ REM ++ LB)) by (apply incl_appl; apply incl_refl).
pose proof (da_src_agree _ _ _ _ _ _ _ _ HP HiB INV) as AG0.
destruct (arr_nowD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HP AG0 HiB ltac:(rewrite EBS; left; reflexivity) ltac:(rewrite EBS; intros b Hb; right; apply in_or_app; left; apply in_or_app; left; exact Hb) HDR0 HAL0)
as (sarr & ssize & HDRc & _ & _ & _ & _ & _ & _ & ALB & _ & _ & Hsz0 & SHrb & Hlen & _).
assert (LEN : Z.of_nat (length kids) < 2^61).
{ rewrite <- L1. destruct ALB as (_ & _ & _ & Hr0 & _ & Hrh). clear - Hlen Hrh Hr0 ACR. lia. }
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. change (hl_segs A4L) with asegs in MI.
pose proof (wmono_refl asegs m2) as WM. pose proof (munch_refl [(lo, bv_unsigned sp + -104); (Fr, Fr + 120); (sh, sh + 16); (6444156, 6444160)] m2) as MU.
stash PRESi. stash Gi. stash COPY. stash KLOOP. stash OWN. stash INV. stash HDRc. stash AG0.
unfold A_TP. a4l.
reenterA asegs A4L HIx asegs_wx HP.
step. step. stepz. step.
try replace (Z_to_bv 64 (-8)) with (Z_to_bv 64 (2^64 - 8)) by (apply bv_eq; vm_compute; reflexivity).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) => rename mq into mX end.
lazymatch goal with MUc : munch _ m2 mX, WMc : wmono asegs m2 mX, MIc : mem_inv asegs mX |- _ =>
pose proof (fk1_HEAPA _ _ _ _ _ _ _ _ lo (bv_unsigned sp + -104) _ HP LO ltac:(lia) MUc WMc MIc) as HPX;
unstash INV; pose proof (dc_inv_own _ _ _ _ _ _ _ HP ltac:(intros b Hb; apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; exact Hb | apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; exact Hb]) MUc WMc INV STi SAVEi) as INVX;
unstash COPY; pose proof (da_copy_own _ _ _ _ _ _ _ _ _ _ _ _ HP ltac:(apply incl_appr; apply incl_appl; apply incl_refl) MUc WMc COPY) as COPYX
end.
assert (OWNX : da_own mX Fr v2 248) by (exists j24, j16, jf1, jf2, w1, w2; split; [exact SCR | split; [exact FF | exact FSH]]).
destruct (Nat.eq_dec (S ii) (length kids)) as [Eend | Nend].
-
replace (Z.of_nat ii + 1) with (Z.of_nat (length kids)) by lia.
rewrite bv_eqb_refl. cbn [negb]. cbv iota.
pose proof (da_src_agree _ _ _ _ _ _ _ _ HPX HiB INVX) as AGX.
destruct (arr_nowD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HPX AGX HiB ltac:(rewrite EBS; left; reflexivity) ltac:(rewrite EBS; intros b Hb; right; apply in_or_app; left; apply in_or_app; left; exact Hb) HDR0 HAL0)
as (sarr' & ssize' & HDRX & _).
destruct (proj1 (rw_cells_app asegs mX _ _ _) HDRX) as [HDRX1 _].
destruct COPYX as (kids' & wq & Hq & DDX & JQX & LK & OK & JTX & WQ & AINV & BDX & BBX).
pose proof (PhiA_nonneg _ _ AINV) as PHI.
evt_done5.
eapply (dc_tail0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F2 fc2 mX md2 A2 B2 Fr (wz 0) j24 (C8 (wz 0)) j16 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (JRtree (Sarr kids')) q 48 JT_ARRAY (fn_arr_to_json_string A4F) pb CBS REM);
[ exact INVX | exact FS | exact FRM2 | exact HPX | exact SCR | reflexivity | exact FF | reflexivity | exact FSH
| exact (da_src_now _ _ _ _ _ _ _ _ HPX HiB INVX) | rewrite EBS; left; reflexivity | lia | exact HDRX1
| rewrite Er; exists (Sarr kids'); split; [reflexivity | rewrite !sdepth_Sarr; lia]
| cbn [dc_cwA]; exists wq; split; [exact JTX |]; rewrite Eend, skipn_all2 in ACC by lia; cbn [arr_wsum] in ACC; lia
| exact Hq | exact DDX | split; [exact Hq | exact JQX]
| rewrite Eend, skipn_all2 in ACC by lia; cbn [arr_wsum] in ACC; lia
| rewrite Eend, skipn_all2 in ACC by lia; cbn [arr_wsum] in ACC; unfold DC_KB in *; lia ].
-
assert (NE : Z.of_nat (length kids) <> Z.of_nat ii + 1) by lia.
if_truex.
replace (Z.of_nat ii + 1) with (Z.of_nat (S ii)) by lia.
evt_done5. unstash KLOOP.
exact (KLOOP ltac:(lia) mX INVX HPX OWNX COPYX).
Qed.

Lemma dc_arr_loop :
forall (n ii : nat) (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
(mc : word -> option byte) (mdc : config) (A : ASA A4L HIx) (Bc : bud) (Fr q acc : Z) (v2 : word) (CBS REM : list blk),
n = (length kids - ii)%nat -> (ii < length kids)%nat ->
dc_inv mc mdc -> fsaved F F1 -> frm0 fc1 ->
HEAPAx A (BS ++ CBS ++ REM ++ LB) LM ((Fr, 1) :: FRS) Bc mc mdc ->
da_own mc Fr v2 248 -> da_copy mc Bc ii q CBS acc -> acc + arr_wsum (skipn ii ws) = w ->
AJ5 A4L HIx A T mdc
(MS (mkR x1 (wz ASP) gp (wz A_TP) t0 t1 t2 sp (wz ASP) a0 a1 a2 a3 a4 a5 a6 a7
(wz Fr) (wz (D / 8 + 2147450880)) (wz D) (wz ((p + 40) / 8 + 2147450880)) (wz 2147450880) (wz (p + 40))
(wz (Z.of_nat (length kids))) (wz (Fr + 64)) (wz (Z.of_nat ii)) (wz (Fr / 8 + 2147450880)) t3 t4 t5 t6)
F1 (wz 0xa18e4) fc1 None mc (seg_rom asegs)).
Proof.
induction n as [|n IHn]; intros until REM; intros Hn Hii INV FS FRM1 HP OWN COPY ACC; [lia|].
pose proof OWN as (j24 & j16 & jf1 & jf2 & w1 & w2 & SCR & FF & FSH).
pose proof INV as (VMi & PRESi & STi & SAVEi & Gi). unfold dc_save in SAVEi.
pose proof COPY as (kids' & wq & Hq & DD & JQ & LK & OK & JTX & WQ & AINV & BDc & BBc).
pose proof LOS as LOSu. unfold dc_stkA, DC_F, DC_C in LOSu. unfold ASP, dc_scr in *.
assert (RD0 : 0 <= rdepth r) by (destruct r; cbn [rdepth]; try lia; apply sdepth_nonneg).
pose proof alloc_ceiling_range as ACR.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
destruct (dc_dfacts _ _ _ _ _ _ HP) as (D1 & D2 & D3 & D4 & DBLK & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13).
pose proof DD as [DC DSH]. pose proof (rw_cells_bound asegs mc D _ DC) as DR. cbn [cells_size csize Nat.add] in DR.
set (sh := Fr / 8 + 2147450880) in *.

assert (HiB : incl BS (BS ++ CBS ++ REM ++ LB)) by (apply incl_appl; apply incl_refl).
assert (INp : In (p, 48) BS) by (rewrite EBS; left; reflexivity).
pose proof (da_src_agree _ _ _ _ _ _ _ _ HP HiB INV) as AG0.
destruct (arr_nowD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HP AG0 HiB INp ltac:(rewrite EBS; intros b Hb; right; apply in_or_app; left; apply in_or_app; left; exact Hb) HDR0 HAL0)
as (sarr & ssize & HDRc & Hp0 & Hp48 & Hp8 & SHp1 & SHpb & AL1 & ALB & SHa1 & SHr1 & Hsz0 & SHrb & Hlen & EAL).
assert (LEN : Z.of_nat (length kids) < 2^61).
{ rewrite <- L1. destruct ALB as (_ & _ & _ & Hr0 & _ & Hrh). clear - Hlen Hrh Hr0 ACR. lia. }
destruct (akids_nth asegs A4F m0 kids ps KBS ii (al_nth ps (Z.of_nat ii)) KIDS0 ltac:(rewrite <- (Nat2Z.id ii) at 1; apply al_nth_in; lia)) as (k & bs & Hk & Hbs & JO0).
pose proof (nth_error_In kids ii Hk) as KIN.
assert (BSI : incl bs BS).
{ intros b Hb. rewrite EBS. apply in_or_app; left. right. apply in_or_app; right. rewrite (QJlD.concat_nth_split KBS ii bs Hbs). apply in_or_app; right. apply in_or_app; left. exact Hb. }
pose proof (jopt_agree _ _ _ _ _ _ _ _ JO0 AG0 BSI) as JOc.
pose proof (blk_gran0A HIx _ _ _ _ _ _ _ p 48 5 HP ltac:(apply HiB; exact INp) ltac:(lia) ltac:(lia)) as SHp5.
replace (p / 8 + 2147450880 + 5) with ((p + 40) / 8 + 2147450880) in SHp5 by (clear - Hp8; Z.div_mod_to_equations; lia).
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ p 48 HP ltac:(left; reflexivity) ltac:(apply in_or_app; left; apply HiB; exact INp)) as DFp. rewrite fr_size_1 in DFp.
pose proof (heapA_blk_appmem A4L HIx _ _ _ _ _ _ _ p 48 HP ltac:(apply in_or_app; left; apply HiB; exact INp)) as APPp. cbn [hl_sb A4L] in APPp. unfold A_SB in APPp.
change ((2 ^ 47 - 1) / 8 + 2147450880 + 1) with 17594333495296 in APPp.
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP ltac:(left; reflexivity)) as (_ & _ & _ & _ & HFimg & _). rewrite fr_size_1 in HFimg. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in HFimg.
set (psh := (p + 40) / 8 + 2147450880) in *.
assert (PSH : 2147450880 <= psh < 17594333495296 /\ (psh + 1 <= sh \/ sh + 16 <= psh)) by (unfold psh, sh; clear - Hp0 Hp48 Hp8 ACR DFp D6 D7; Z.div_mod_to_equations; lia).
unfold jhdr_cells in HDRc. cbn [app] in HDRc.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. change (hl_segs A4L) with asegs in MI.
destruct (heapA_sb_cells A4L HIx _ _ _ _ _ _ _ HP) as (SB1 & SB2 & _ & _).
apply ro_C8_of_bytes_at in SB1. apply ro_C8_of_bytes_at in SB2.
pose proof (wmono_refl asegs mc) as WM. pose proof (munch_refl [(lo, bv_unsigned sp + -104); (Fr, Fr + 120); (sh, sh + 16); (6444156, 6444160)] mc) as MU.
stash PRESi. stash Gi. stash COPY. stash OWN. stash INV. stash JQ. stash JOc. stash JO0. stash AL1. stash SHa1. stash SHr1. stash SHp1. stash AG0. stash DD. stash IHn.
clear DC DSH.
unfold A_TP. a4l.
reenterA asegs A4L HIx asegs_wx HP.
stepz. stepz.
asan_rechkA.
step. step. step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) => rename mq into mg end.
assert (HiBL : incl (BS ++ LB) (BS ++ CBS ++ REM ++ LB)).
{ intros b Hb. apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; exact Hb | apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; exact Hb]. }
pose proof (fk1_HEAPA _ _ _ _ _ _ _ _ lo (bv_unsigned sp + -104) _ HP LO ltac:(lia) MU WM MI) as HPg.
unstash INV. pose proof (dc_inv_own _ _ _ _ _ _ _ HP HiBL MU WM INV STi SAVEi) as INVg.
pose proof (da_src_agree _ _ _ _ _ _ _ _ HPg HiB INVg) as AGg.
clear AL1 SHa1 SHr1 SHp1 ALB Hsz0 SHrb Hlen EAL.
destruct (arr_nowD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HPg AGg HiB INp ltac:(rewrite EBS; intros b Hb; right; apply in_or_app; left; apply in_or_app; left; exact Hb) HDR0 HAL0)
as (sarr' & ssize' & _ & _ & _ & _ & _ & _ & AL1 & ALB & SHa1 & SHr1 & Hsz0 & SHrb & Hlen & EAL).
eapply evt_cut.
{ eapply array_list_get_idx_A with (lo := lo) (sbcell := 991672) (a := a) (arr := sarr') (size := ssize') (ps := ps) (i := Z.of_nat ii).
- unfold small_pre, A_GOT_SB, A_SB. rewrite ?unsigned_lit by lia.
split; [assumption|]. split; [eassumption|]. split; [lia|]. split; [exact LO|]. split; [eassumption|]. split; [eassumption|]. lia.
- exact AL1.
- reflexivity.
- reflexivity.
- lia.
- exact ALB.
- exact SHa1.
- exact SHr1. }
intros ms' (g1 & g2 & g3 & g4 & g5 & m' & -> & MUg & WMg & MIg & STg).
rewrite ?unsigned_lit in MUg, STg by lia.
rewrite (proj2 (Z.ltb_lt (Z.of_nat ii) (Z.of_nat (length ps)))) by lia.
clear AL1 SHa1 SHr1 ALB Hsz0 SHrb Hlen EAL AGg.

lazymatch type of MUg with munch _ ?mq _ =>
transport_after_call asegs mq m' MUg WMg; try match goal with H : mem_inv asegs mq |- _ => clear H end; clear MUg WMg end.
replace (ret_pc (wz 661760)) with (wz 661760) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
unstash JOc.
destruct k as [sk|].
-
destruct JOc as [Hpk JVk].
destruct (jval_root_in asegs A4F _ _ _ _ _ JVk) as (nk & INk & Hnk).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ _ nk HP ltac:(apply in_or_app; left; apply HiB; apply BSI; exact INk)) as (_ & Hpkal & Hpklo & Hpkhi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hpkhi.
set (pk := al_nth ps (Z.of_nat ii)) in *.
clear JVk.
step. if_falsex.
step. step. step. step. step. step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) => rename mq into mk end.
pose proof (fk1_HEAPA _ _ _ _ _ _ _ _ lo (bv_unsigned sp + -104) _ HP LO ltac:(lia) MU WM MIg) as HPc.
pose proof (dc_inv_own _ _ _ _ _ _ _ HP HiBL MU WM INV STg SAVEi) as INVc.
pose proof (da_src_agree _ _ _ _ _ _ _ _ HPc HiB INVc) as AGc.
unstash JO0. pose proof (jopt_agree _ _ _ _ _ _ _ _ JO0 AGc BSI) as [_ JVk].
unstash COPY. pose proof (da_copy_own _ _ _ _ _ _ _ _ _ _ _ _ HP ltac:(apply incl_appr; apply incl_appl; apply incl_refl) MU WM COPY) as COPYc. clear COPY.
destruct (heapA_errno A4L HIx _ _ _ _ _ _ _ HPc) as (errs & ERRs).

destruct (KW1 ii sk bs Hk Hbs) as (Yi & Ri & JTk). set (wk := nth ii ws 0) in *.
pose proof (arr_wsum_skipn ws ii wk ltac:(apply nth_error_nth_len; lia)) as WS1. fold wk in WS1.
pose proof (arr_wsum_skipn_nonneg ws (S ii) NNW) as WS2.
pose proof (jtx_nonneg _ _ _ _ JTk) as WK0.
pose proof (PhiA_nonneg _ _ AINV) as PHI.

set (K1 := concat (firstn ii KBS)). set (K2 := concat (skipn (S ii) KBS)).
assert (EBSk : BS = ((p, 48) :: AL ++ K1 ++ bs ++ K2) ++ PBS) by (rewrite EBS, (QJlD.concat_nth_split KBS ii bs Hbs); reflexivity).
set (LBk := ((p, 48) :: AL ++ K1 ++ K2) ++ PBS ++ CBS ++ REM ++ LB).
assert (HPk : HEAPAx A (bs ++ LBk) LM ((Fr, 1) :: FRS) Bc mk mdc).
{ eapply (heapA_perm A4L HIx); [exact HPc | rewrite EBSk; unfold LBk; perm | apply Permutation_refl | apply Permutation_refl]. }

lazymatch type of FF with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?rest) =>
change (c0 :: c1 :: c2 :: c3 :: c4 :: rest) with ([c0; c1; c2; c3] ++ ([c4] ++ rest)) in FF end.
destruct (proj1 (rw_cells_app asegs mk _ _ _) FF) as [FFa FFx]. cbn [cells_size csize Nat.add] in FFx.
destruct (proj1 (rw_cells_app asegs mk _ _ _) FFx) as [FFj FFb]. cbn [cells_size csize Nat.add] in FFb.
replace (Fr + Z.of_nat 64) with (Fr + 64) in FFj, FFb by lia. replace (Fr + 64 + Z.of_nat 8) with (Fr + 72) in FFb by lia.
clear FF FFx.
assert (UNP : unpoisoned asegs mk A_SB (Fr + 64) 8).
{ pose proof (unpoisoned_of_fshadow1 mk Fr _ 8 9 (proj2 (proj1 FSH)) eq_refl D6 ltac:(lia) ltac:(lia) ltac:(lia) eq_refl) as U.
change (8 * Z.of_nat 8) with 64 in U. change (8 * Z.of_nat (9 - 8)) with 8 in U. exact U. }

assert (DEPk : sdepth sk + 1 <= rdepth r).
{ rewrite Er. cbn [rdepth]. rewrite sdepth_Sarr. pose proof (odep_le_okmax kids (Some sk) KIN) as X. cbn [odep] in X. lia. }
assert (WKLT : wk < 2^28) by (pose proof (jtx_nonneg _ _ _ _ JTX) as WQ0; clear - WLT WS1 WS2 ACC WQ WQ0; lia).
evt_done5.
eapply (IH sk KIN) with (A := A) (LB := LBk) (BS := bs) (LM := LM) (FRS := (Fr, 1) :: FRS) (B := Bc) (lo := lo) (p := pk) (D := Fr + 64) (w := wk) (errv := errs);
[ exact HPk | split; [exact Hpk | exact JVk] | discriminate | exact (proj2 (proj2 (proj2 (proj2 INVc)))) | exact FFj
| exists Fr, 1; split; [left; reflexivity | rewrite fr_size_1; lia]
| exact UNP | clear - D6; Z.div_mod_to_equations; lia
| rewrite unsigned_lit by lia; exact STg | exact LO
| rewrite unsigned_lit by lia; unfold dc_stkA, DC_F, DC_C; cbn [rdepth]; lia
| rewrite unsigned_lit by lia; clear - SPA; Z.div_mod_to_equations; lia
| rewrite unsigned_lit by lia; lia
| exact ERRs | reflexivity | rewrite unsigned_lit by lia; reflexivity | exact FRM1
| cbn [length rdepth]; lia
| exists Yi, Ri; exact JTk
| exact WKLT
| unfold DC_KB in *; lia | lia | reflexivity | reflexivity | reflexivity | ].

intros msr mdr mr rvr Ar Br (RSr & VMr & STr & PXr & (errr & ERRr)) Gr JRr (BDr & OUTr).
destruct RSr as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & F2 & fc2 & -> & FS2 & FRM2).
rewrite ?(unsigned_lit (bv_unsigned sp + -192)) in STr, PXr by lia.
change (hl_segs A4L) with asegs in *.
replace (ret_pc (wz 661788)) with (wz 661788) by (symmetry; apply ret_pc_even; [lia | reflexivity]).

assert (PXR : forall A0 cs0, rw_cells asegs mk A0 cs0 ->
client_rangex A4H (hl_volatile A4H) ((bs ++ LBk) ++ LM ++ fr_ivs A4L ((Fr, 1) :: FRS)) (bv_unsigned sp + -192) A0 (Z.of_nat (cells_size cs0)) ->
(A0 + Z.of_nat (cells_size cs0) <= Fr + 64 \/ Fr + 64 + 8 <= A0) -> rw_cells asegs mr A0 cs0).
{ intros A0 cs0 H1 H2 H3. exact (QrIB.Mq0.presxD_rw_cells A4H _ _ _ _ _ _ _ PXr H1 H2 H3). }
apply PXR in SCR; [| left; lia | cbn [cells_size csize Nat.add]; lia].
apply PXR in SAVEi; [| left; lia | cbn [cells_size csize Nat.add]; lia].
apply PXR in FFa; [| eapply client_rangex_block; [apply in_or_app; right; apply in_or_app; right; left; reflexivity | cbn [fr_base fst]; lia | cbn [cells_size csize Nat.add fr_base fr_class fst snd]; rewrite fr_size_1; lia]
| cbn [cells_size csize Nat.add]; lia].
apply PXR in FFb; [| eapply client_rangex_block; [apply in_or_app; right; apply in_or_app; right; left; reflexivity | cbn [fr_base fst]; lia | cbn [cells_size csize Nat.add fr_base fr_class fst snd]; rewrite fr_size_1; lia]
| cbn [cells_size csize Nat.add]; lia].
apply PXR in FSH; [| eapply client_rangex_block; [apply in_or_app; right; apply in_or_app; right; right; left; reflexivity | unfold shad; cbn [fr_base fst hl_sb A4L]; unfold A_SB; fold sh; lia
| unfold shad; cbn [cells_size csize Nat.add fr_base fr_class fst snd hl_sb A4L]; rewrite fr_shadow_len_1; unfold A_SB; fold sh; lia]
| cbn [cells_size csize Nat.add]; lia].
clear PXR.

assert (INVr : dc_inv mr mdr).
{ destruct INVc as (VMc & PXc & _ & _ & _).
split; [eapply model_vm_only_trans; [exact VMc | exact VMr] |].
split; [eapply (QrIB.Mq0.presxD_trans A4H); [exact PXc |] | split; [exact STr | split; [unfold dc_save; exact SAVEi | exact Gr]]].
eapply presxD_own with (D' := Fr + 64); [exact PXr | lia | |].
- intros b Hb. apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left | apply in_or_app; right].
+ apply (Permutation_in b (l := BS ++ CBS ++ REM ++ LB)); [rewrite EBSk; unfold LBk; perm | apply HiBL; exact Hb].
+ apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; exact Hb | apply in_or_app; right; cbn [fr_ivs flat_map app]; right; right; exact Hb].
- intros x Hx. eapply da_own_outside; [exact HPc | exact HiBL | unfold alloc_ceiling, sp_window_lo, stack_max_size in D8; lia | lia]. }
destruct COPYc as (kidsc & wqc & Hqc & DDk & JQk & LKc & OKc & JTXc & WQc & AINVc & BDk & BBk).
pose proof (dc_dst_presxD _ _ _ _ _ Fr (Fr + 64) (bs ++ LBk) (bv_unsigned sp + -192) mk mr q HPc ltac:(lia) ltac:(lia) DDk PXr) as DDr.

assert (AGr : forall BSx, incl BSx (BS ++ CBS ++ REM ++ LB) -> agree_on asegs BSx mk mr).
{ intros BSx Hi. eapply presxD_agree_blocks; [exact PXr | |].
- intros b Hb. apply in_or_app; left. apply (Permutation_in b (l := BS ++ CBS ++ REM ++ LB)); [rewrite EBSk; unfold LBk; perm | apply Hi; exact Hb].
- intros a0' k0' Hin. pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ Fr 1 a0' k0' HPc ltac:(left; reflexivity) ltac:(apply in_or_app; left; apply Hi; exact Hin)) as DF.
rewrite fr_size_1 in DF. lia. }
pose proof (jval_agree asegs A4F _ _ _ _ _ _ _ JQk (AGr CBS ltac:(apply incl_appr; apply incl_appl; apply incl_refl)) (incl_refl _)) as JQr.
clear JVk FFj UNP.
destruct OUTr as [(-> & d & qk & KCBS & KREM & COk & CWk & Hqk & DCk & JRk & BBr & HPr) | (-> & qk & KCBS & KREM & DCk & FRk & BBr & HPr)].
+
destruct COk as (sk' & -> & DEPk'). cbn [dc_cwA] in CWk. destruct CWk as (wk' & JTk' & WK').
assert (HPa : HEAPAx Ar (BS ++ CBS ++ KCBS ++ (KREM ++ REM) ++ LB) LM ((Fr, 1) :: FRS) Br mr mdr).
{ eapply (heapA_perm A4L HIx); [exact HPr | rewrite EBSk; unfold LBk; perm | apply Permutation_refl | apply Permutation_refl]. }
assert (OWNr : da_own mr Fr (wz qk) 0).
{ exists j24, j16, jf1, jf2, w1, w2. split; [exact SCR | split; [| exact FSH]].
lazymatch goal with |- rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?rest) =>
change (c0 :: c1 :: c2 :: c3 :: c4 :: rest) with ([c0; c1; c2; c3] ++ ([c4] ++ rest)) end.
apply (proj2 (rw_cells_app asegs mr _ _ _)). split; [exact FFa |]. cbn [cells_size csize Nat.add].
apply (proj2 (rw_cells_app asegs mr _ _ _)). cbn [cells_size csize Nat.add].
replace (Fr + Z.of_nat 64) with (Fr + 64) by lia. replace (Fr + 64 + Z.of_nat 8) with (Fr + 72) by lia. split; [exact DCk | exact FFb]. }
assert (HiBa : incl BS (BS ++ CBS ++ KCBS ++ (KREM ++ REM) ++ LB)) by (apply incl_appl; apply incl_refl).
pose proof (da_src_now _ _ _ _ _ _ _ _ HPa HiBa INVr) as JRsrc.
clear FFa FFb FSH SAVEi.
pose proof DDr as [_ DSHr].
stash INVr. stash OWNr. stash JRsrc. stash JQr. stash JRk. stash DDr.
try clear MU WM. try clear MIg.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HPa) as MIr. change (hl_segs A4L) with asegs in MIr.
pose proof (wmono_refl asegs mr) as WMr. pose proof (munch_refl [(lo, bv_unsigned sp + -104); (Fr, Fr + 120); (sh, sh + 16); (6444156, 6444160)] mr) as MUr.
reenterA asegs A4L HIx asegs_wx HPa.
step. if_lit.
step. step. if_lit.
evt_done5. unstash INVr. unstash OWNr. unstash JRsrc. unstash JQr. unstash JRk. unstash DDr.
assert (LEN28 : Z.of_nat (length kids) + 1 < 2^28).
{ pose proof (arr_wsum_len ws NNW) as X. rewrite LW in X. clear - X EW WLT. lia. }
assert (CAPk : arr_add_costA (arr_capA CBS) (Z.of_nat ii) <= PhiA (arr_capA CBS) (Z.of_nat ii) + 1280).
{ clear - AINVc. unfold arr_add_costA, PhiA, arr_inv in *. destruct (Z.ltb_spec (Z.of_nat ii + 1) (arr_capA CBS)); lia. }
eapply dc_arr_add with (v := qk) (q := q) (kids' := kidsc) (vs := Some sk') (VBS := KCBS) (CBS := CBS) (REM := KREM ++ REM);
[ exact INVr | eapply fsaved_trans; [exact FS | exact FS2] | apply FRM2; exact FRM1 | exact HPa | exact OWNr | exact JRsrc
| exact Hqc | exact DDr | exact JQr | exact JRk | rewrite LKc; lia | lia
| rewrite LKc; unfold DC_KB in *; lia | ].
intros z1 u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F3 fc3 m3 md3 A3 B3 CBS' INV3 FS3 FRM3 HP3 OWN3 JR3 DD3 JQ3 LEN3 GROW3 BB3 BD3 JTX3.
rewrite LKc in GROW3, BB3.
destruct (potential_step_arr_add _ _ _ AINVc GROW3) as [POT AINV3].
eapply (dc_arr_next ii) with (q := q) (acc := acc + (2 + wk)) (CBS := CBS') (REM := KREM ++ REM);
[ lia | exact INV3 | exact FS3 | exact FRM3 | exact HP3 | exact OWN3 | | lia | ].
* exists (kidsc ++ [Some sk']), (wqc + (2 + wk')).
split; [exact Hqc|]. split; [exact DD3|]. split; [exact JQ3|].
split; [rewrite length_app, LKc; cbn [length]; lia|].
split; [rewrite okmax_app, okmax_single; cbn [odep]; pose proof (odep_le_okmax kids (Some sk) KIN) as X; cbn [odep] in X; lia|].
split; [exact (JTX3 wqc wk' JTXc JTk')|].
split; [lia|].
split; [replace (Z.of_nat (S ii)) with (Z.of_nat ii + 1) by lia; exact AINV3|].
split; [lia|].
replace (Z.of_nat (S ii)) with (Z.of_nat ii + 1) by lia. unfold Qiiq.Mq0.RA, K_arr, DC_KB in *. lia.
* intros Hlt mc' INV' HP' OWN' COPY'. unstash IHn.
eapply (IHn (S ii)) with (q := q) (acc := acc + (2 + wk)) (CBS := CBS') (REM := KREM ++ REM);
[ lia | lia | exact INV' | exact FS3 | exact FRM3 | exact HP' | exact OWN' | exact COPY' | lia ].
+
assert (HPa : HEAPAx Ar (BS ++ CBS ++ KCBS ++ (KREM ++ REM) ++ LB) LM ((Fr, 1) :: FRS) Br mr mdr).
{ eapply (heapA_perm A4L HIx); [exact HPr | rewrite EBSk; unfold LBk; perm | apply Permutation_refl | apply Permutation_refl]. }
assert (OWNr : da_own mr Fr (wz qk) 0).
{ exists j24, j16, jf1, jf2, w1, w2. split; [exact SCR | split; [| exact FSH]].
lazymatch goal with |- rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?rest) =>
change (c0 :: c1 :: c2 :: c3 :: c4 :: rest) with ([c0; c1; c2; c3] ++ ([c4] ++ rest)) end.
apply (proj2 (rw_cells_app asegs mr _ _ _)). split; [exact FFa |]. cbn [cells_size csize Nat.add].
apply (proj2 (rw_cells_app asegs mr _ _ _)). cbn [cells_size csize Nat.add].
replace (Fr + Z.of_nat 64) with (Fr + 64) by lia. replace (Fr + 64 + Z.of_nat 8) with (Fr + 72) by lia. split; [exact DCk | exact FFb]. }
assert (HiBa : incl BS (BS ++ CBS ++ KCBS ++ (KREM ++ REM) ++ LB)) by (apply incl_appl; apply incl_refl).
pose proof (da_src_now _ _ _ _ _ _ _ _ HPa HiBa INVr) as JRsrc.
clear SCR FFa FFb FSH SAVEi.
stash INVr. stash OWNr. stash JRsrc. stash JQr. stash FRk. stash DDr.
try clear MU WM. try clear MIg.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HPa) as MIr. change (hl_segs A4L) with asegs in MIr.
pose proof (wmono_refl asegs mr) as WMr. pose proof (munch_refl [(lo, bv_unsigned sp + -104); (Fr, Fr + 120); (sh, sh + 16); (6444156, 6444160)] mr) as MUr.
reenterA asegs A4L HIx asegs_wx HPa.
step. if_lit.
evt_done5. unstash INVr. unstash OWNr. unstash JRsrc. unstash JQr. unstash FRk. unstash DDr.
eapply dc_arr_fail with (v2 := qk) (q := q) (VBS := KCBS) (CBS := CBS) (REM := KREM ++ REM);
[ exact INVr | eapply fsaved_trans; [exact FS | exact FS2] | apply FRM2; exact FRM1 | exact HPa | exact OWNr | exact FRk | exact JRsrc | exact DDr
| right; split; [exact Hqc | exists (Sarr kidsc); exact JQr] | lia | unfold DC_KB in *; lia ].
-
destruct JOc as [Epk Ebs].
rewrite Epk.
step. if_lit.
stepz.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) => rename mq into mk end.
lazymatch goal with MUc : munch _ mc mk, WMc : wmono asegs mc mk, MIc : mem_inv asegs mk |- _ =>
pose proof (fk1_HEAPA _ _ _ _ _ _ _ _ lo (bv_unsigned sp + -104) _ HP LO ltac:(lia) MUc WMc MIc) as HPc;
pose proof (dc_inv_own _ _ _ _ _ _ _ HP HiBL MUc WMc INV STg SAVEi) as INVc;
unstash COPY; pose proof (da_copy_own _ _ _ _ _ _ _ _ _ _ _ _ HP ltac:(apply incl_appr; apply incl_appl; apply incl_refl) MUc WMc COPY) as COPYc; clear COPY
end.
destruct COPYc as (kidsc & wqc & Hqc & DDk & JQk & LKc & OKc & JTXc & WQc & AINVc & BDk & BBk).
pose proof DDk as [_ DSHk].
step. step. if_lit.
assert (OWNc : da_own mk Fr (wz 0) 0) by (exists j24, j16, jf1, jf2, w1, w2; split; [exact SCR | split; [exact FF | exact FSH]]).
pose proof (KW2 ii Hk) as WKN.
pose proof (arr_wsum_skipn ws ii (nth ii ws 0) ltac:(apply nth_error_nth_len; lia)) as WS1. rewrite WKN in WS1.
pose proof (arr_wsum_skipn_nonneg ws (S ii) NNW) as WS2.
pose proof (PhiA_nonneg _ _ AINVc) as PHI.
assert (LEN28 : Z.of_nat (length kids) + 1 < 2^28).
{ pose proof (arr_wsum_len ws NNW) as X. rewrite LW in X. clear - X EW WLT. lia. }
assert (CAPk : arr_add_costA (arr_capA CBS) (Z.of_nat ii) <= PhiA (arr_capA CBS) (Z.of_nat ii) + 1280).
{ clear - AINVc. unfold arr_add_costA, PhiA, arr_inv in *. destruct (Z.ltb_spec (Z.of_nat ii + 1) (arr_capA CBS)); lia. }
evt_done5.
eapply dc_arr_add with (v := 0) (q := q) (kids' := kidsc) (vs := None) (VBS := []) (CBS := CBS) (REM := REM);
[ exact INVc | exact FS | exact FRM1 | exact HPc | exact OWNc | exact (da_src_now _ _ _ _ _ _ _ _ HPc HiB INVc)
| exact Hqc | exact DDk | exact JQk | split; reflexivity | rewrite LKc; lia | unfold NULL_W in *; lia
| rewrite LKc; cbn [length]; unfold DC_KB, NULL_W in *; lia | ].
intros z1 u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F3 fc3 m3 md3 A3 B3 CBS' INV3 FS3 FRM3 HP3 OWN3 JR3 DD3 JQ3 LEN3 GROW3 BB3 BD3 JTX3.
rewrite LKc in GROW3, BB3.
destruct (potential_step_arr_add _ _ _ AINVc GROW3) as [POT AINV3].
eapply (dc_arr_next ii) with (q := q) (acc := acc + (2 + NULL_W)) (CBS := CBS') (REM := REM);
[ lia | exact INV3 | exact FS3 | exact FRM3 | exact HP3 | exact OWN3 | | unfold NULL_W in *; lia | ].
+ exists (kidsc ++ [None]), (wqc + (2 + NULL_W)).
split; [exact Hqc|]. split; [exact DD3|]. split; [exact JQ3|].
split; [rewrite length_app, LKc; cbn [length]; lia|].
split; [rewrite okmax_app, okmax_single; cbn [odep]; pose proof (okmax_nonneg kids); lia|].
split; [exact (JTX3 wqc NULL_W JTXc eq_refl)|].
split; [lia|].
split; [replace (Z.of_nat (S ii)) with (Z.of_nat ii + 1) by lia; exact AINV3|].
split; [unfold NULL_W in *; lia|].
replace (Z.of_nat (S ii)) with (Z.of_nat ii + 1) by lia. cbn [length] in LEN3. unfold Qiiq.Mq0.RA, K_arr, DC_KB, NULL_W in *. lia.
+ intros Hlt mc' INV' HP' OWN' COPY'. unstash IHn.
eapply (IHn (S ii)) with (q := q) (acc := acc + (2 + NULL_W)) (CBS := CBS') (REM := REM);
[ lia | lia | exact INV' | exact FS3 | exact FRM3 | exact HP' | exact OWN' | exact COPY' | unfold NULL_W in *; lia ].
Qed.

Lemma dc_arr :
forall (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x21 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
(mc : word -> option byte) (mdc : config) (A : ASA A4L HIx) (Bc : bud) (Fr q : Z) (v2 : word) (CBS : list blk)
(j24 j8 j16 jf1 jf2 : list byte) (w1 w2 : word),
dc_inv mc mdc -> fsaved F F1 -> frm0 fc1 ->
HEAPAx A (BS ++ CBS ++ LB) LM ((Fr, 1) :: FRS) Bc mc mdc ->

rw_cells asegs mc ASP (dc_scr Fr (wz 0) j24 (CB 8 j8) j16) ->
rw_cells asegs mc Fr [C8 (wz 1102416563); C8 w1; C8 w2; CB 40 jf1; C8 v2; CB 48 jf2] ->
rw_cells asegs mc (Fr / 8 + 2147450880) [C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242);
C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
q <> 0 -> dc_dst mc q -> jval asegs A4F (Sarr []) mc CBS q 1 -> length CBS = 3%nat -> arr_capA CBS = 32 ->
bD B0 - 1 <= bD Bc -> bB B0 - ((16 * 48 + 512) + (2048 + 128 * 32)) <= bB Bc ->
AJ5 A4L HIx A T mdc
(MS (mkR x1 (wz ASP) gp (wz A_TP) t0 t1 t2 sp (wz ASP) (wz p) a1 a2 a3 a4 a5 a6 a7
(wz Fr) (wz Fr) (wz D) x21 (wz 2147450880) (wz p) s8 s9 s10 (wz (Fr / 8 + 2147450880)) t3 t4 t5 t6)
F1 (wz 0xa18a8) fc1 None mc (seg_rom asegs)).
Proof.
intros until w2. intros INV FS FRM1 HP0 SCR FF FSH Hq DD JQ LCBS CAPQ BDc BBc.
assert (HP : HEAPAx A (BS ++ CBS ++ [] ++ LB) LM ((Fr, 1) :: FRS) Bc mc mdc) by exact HP0.
pose proof INV as (VMi & PRESi & STi & SAVEi & Gi). unfold dc_save in SAVEi.
pose proof LOS as LOSu. unfold dc_stkA, DC_F, DC_C in LOSu. unfold ASP, dc_scr in *.
assert (RD0 : 0 <= rdepth r) by (destruct r; cbn [rdepth]; try lia; apply sdepth_nonneg).
pose proof alloc_ceiling_range as ACR.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
destruct (dc_dfacts _ _ _ _ _ _ HP) as (D1 & D2 & D3 & D4 & DBLK & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13).
pose proof DD as [DC DSH]. pose proof (rw_cells_bound asegs mc D _ DC) as DR. cbn [cells_size csize Nat.add] in DR.
set (sh := Fr / 8 + 2147450880) in *.

assert (JTXQ : jtx (Sarr []) CBS = Some (24, [])).
{ destruct (arr_capA_jval _ _ _ _ _ JQ) as (a_ & arr_ & rest_ & EABS & _). rewrite EABS in LCBS |- *. destruct rest_; [| cbn in LCBS; lia]. reflexivity. }
pose proof (arr_wsum_nonneg ws NNW) as WS0.

assert (HiB : incl BS (BS ++ CBS ++ [] ++ LB)) by (apply incl_appl; apply incl_refl).
assert (INp : In (p, 48) BS) by (rewrite EBS; left; reflexivity).
pose proof (da_src_agree _ _ _ _ _ _ _ _ HP HiB INV) as AG0.
destruct (arr_nowD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HP AG0 HiB INp ltac:(rewrite EBS; intros b Hb; right; apply in_or_app; left; apply in_or_app; left; exact Hb) HDR0 HAL0)
as (sarr & ssize & HDRc & Hp0 & Hp48 & Hp8 & SHp1 & SHpb & AL1 & ALB & SHa1 & SHr1 & Hsz0 & SHrb & Hlen & EAL).
assert (LEN : Z.of_nat (length kids) < 2^61).
{ rewrite <- L1. destruct ALB as (_ & _ & _ & Hr0 & _ & Hrh). clear - Hlen Hrh Hr0 ACR. lia. }
pose proof (blk_gran0A HIx _ _ _ _ _ _ _ p 48 5 HP ltac:(apply HiB; exact INp) ltac:(lia) ltac:(lia)) as SHp5.
replace (p / 8 + 2147450880 + 5) with (p / 8 + 2147450885) in SHp5 by lia.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hp48.
assert (COPY0 : da_copy mc Bc 0 q CBS 24).
{ exists [], 24. split; [exact Hq|]. split; [exact DD|]. split; [exact JQ|]. split; [reflexivity|].
split; [cbn [okmax]; apply okmax_nonneg|]. split; [exact JTXQ|]. split; [lia|].
rewrite CAPQ. split; [exact arr_inv_new|]. split; [lia|]. rewrite LCBS. unfold PhiA, DC_KB in *. cbn [Z.of_nat]. lia. }
unfold jhdr_cells in HDRc. cbn [app] in HDRc.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. change (hl_segs A4L) with asegs in MI.
destruct (heapA_sb_cells A4L HIx _ _ _ _ _ _ _ HP) as (SB1 & SB2 & _ & _).
apply ro_C8_of_bytes_at in SB1. apply ro_C8_of_bytes_at in SB2.
pose proof (wmono_refl asegs mc) as WM. pose proof (munch_refl [(lo, bv_unsigned sp + -104); (Fr, Fr + 120); (sh, sh + 16); (6444156, 6444160)] mc) as MU.
stash PRESi. stash Gi. stash COPY0. stash INV. stash JQ. stash AG0. stash DD.
clear DC DSH.
unfold A_TP. a4l.
reenterA asegs A4L HIx asegs_wx HP.
step. asan_chkA.
step. step.

eapply evt_cut.
{ eapply array_list_length_A with (lo := lo) (sbcell := 991672) (a := a) (arr := sarr) (size := ssize) (ps := ps).
- unfold small_pre, A_GOT_SB, A_SB. rewrite ?unsigned_lit by lia.
split; [assumption|]. split; [eassumption|]. split; [lia|]. split; [exact LO|]. split; [eassumption|]. split; [eassumption|]. lia.
- exact AL1.
- reflexivity.
- exact ALB.
- exact SHa1. }
intros ms' (g1 & g2 & m' & -> & MUg & WMg & MIg & STg).
rewrite ?unsigned_lit in MUg, STg by lia.
clear AL1 SHa1 SHr1 ALB Hsz0 SHrb Hlen EAL.
lazymatch type of MUg with munch _ ?mq _ =>
transport_after_call asegs mq m' MUg WMg; try match goal with H : mem_inv asegs mq |- _ => clear H end; clear MUg WMg end.
replace (ret_pc (wz 661700)) with (wz 661700) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
assert (HiBL : incl (BS ++ LB) (BS ++ CBS ++ [] ++ LB)).
{ intros b Hb. apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; exact Hb | apply in_or_app; right; apply in_or_app; right; exact Hb]. }
pose proof (fk1_HEAPA _ _ _ _ _ _ _ _ lo (bv_unsigned sp + -104) _ HP LO ltac:(lia) MU WM MIg) as HPg.
unstash INV. pose proof (dc_inv_own _ _ _ _ _ _ _ HP HiBL MU WM INV STg SAVEi) as INVg.
unstash COPY0. pose proof (da_copy_own _ _ _ _ _ _ _ _ _ _ _ _ HP ltac:(apply incl_appr; apply incl_appl; apply incl_refl) MU WM COPY0) as COPYg.
rewrite L1.
destruct (Nat.eq_dec (length kids) 0) as [E0 | N0].
-
rewrite E0. step. if_lit.
destruct COPYg as (kidsc & wqc & _ & DDg & JQg & LKc & _ & JTXg & WQg & _).
destruct kidsc; [| cbn in LKc; lia].
pose proof (da_src_agree _ _ _ _ _ _ _ _ HPg HiB INVg) as AGg.
destruct (arr_nowD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HPg AGg HiB INp ltac:(rewrite EBS; intros b Hb; right; apply in_or_app; left; apply in_or_app; left; exact Hb) HDR0 HAL0)
as (sarr' & ssize' & HDRg & _).
destruct (proj1 (rw_cells_app asegs m' _ _ _) HDRg) as [HDRg1 _].
evt_done5.
eapply (dc_tail0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F1 fc1 m' mdc A Bc Fr (wz 0) j24 (CB 8 j8) j16 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (JRtree (Sarr [])) q 48 JT_ARRAY (fn_arr_to_json_string A4F) pb CBS []);
[ exact INVg | exact FS | exact FRM1 | exact HPg | exact SCR | reflexivity | exact FF | reflexivity | exact FSH
| exact (da_src_now _ _ _ _ _ _ _ _ HPg HiB INVg) | exact INp | lia | exact HDRg1
| rewrite Er; exists (Sarr []); split; [reflexivity | rewrite !sdepth_Sarr; cbn [okmax]; pose proof (okmax_nonneg kids); lia]
| cbn [dc_cwA]; exists wqc; split; [exact JTXg | lia]
| exact Hq | exact DDg | split; [exact Hq | exact JQg]
| lia | rewrite LCBS; unfold DC_KB in *; cbn [Z.of_nat]; lia ].
-
step. if_falsex.
step. step. step.
step. rewrite (unsigned_lit D) by lia. rewrite (ub_land7 D DAL).
stepz.
step. step. sh_norm.
replace (p / 8 + 2147450885) with ((p + 40) / 8 + 2147450880) by (clear - Hp8; Z.div_mod_to_equations; lia).
clear HPg INVg COPYg.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => lazymatch goal with MIX : mem_inv asegs mX, STX : stk asegs mX _ _ |- _ =>
pose proof (fk1_HEAPA _ _ _ _ _ _ _ _ lo (bv_unsigned sp + -104) _ HP LO ltac:(lia) MU WM MIX) as HPg;
pose proof (dc_inv_own _ _ _ _ _ _ _ HP HiBL MU WM INV STX SAVEi) as INVg;
pose proof (da_copy_own _ _ _ _ _ _ _ _ _ _ _ _ HP ltac:(apply incl_appr; apply incl_appl; apply incl_refl) MU WM COPY0) as COPYg; clear COPY0;
assert (OWNg : da_own mX Fr v2 248) by (exists j24, j16, jf1, jf2, w1, w2; split; [exact SCR | split; [exact FF | exact FSH]])
end end.
evt_done5.
eapply (dc_arr_loop (length kids) 0) with (q := q) (acc := 24) (CBS := CBS) (REM := []);
[ lia | lia | exact INVg | exact FS | exact FRM1 | exact HPg | exact OWNg | exact COPYg | rewrite EW; reflexivity ].
Qed.
End MDcArr.
End RC__1.
End Mq3.

From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QjDH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDH.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7UD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7UD. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qhd4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qhd4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QgHv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QgHv.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9O6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9O6.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mq6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q228.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q228.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qz87.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qz87.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q228.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q228.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q228.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q228.Mq7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QtyQ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QtyQ.Mq6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfHY.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfHY.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QiVi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QiVi.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfHY.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfHY.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q63E.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q63E.Mq8.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac QlEo_c1.solve_load ::= QXup.mkr__solve_load_3. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Section All.
Variable HIx : heap_iface_A A4L.
Hypothesis OBL_REALLOC_NF : realloc_nf_stmt HIx.
Variable PFRT : (word -> option byte) -> Prop.
Variable PFLO : Z.
Hypothesis OBL_PFRT : forall A LB LM FRS B m md, HEAPA A4L HIx A LB LM FRS B m md -> PFRT m.
Hypothesis OBL_PFLO : PFLO <= alloc_ceiling.
Hypothesis SNP_LD : isnprintf_ld_stmt PFRT PFLO.
Hypothesis SNP_LU : isnprintf_lu_stmt PFRT PFLO.
Hypothesis SNP_U : isnprintf_u00cc_stmt PFRT PFLO.

Theorem servalA : SERVALA HIx.
Proof.
pose proof (json_escape_str_A HIx OBL_REALLOC_NF PFRT PFLO OBL_PFRT OBL_PFLO SNP_U) as ESC.
unfold SERVALA. induction s as [|u| |h|kids IHk|kids IHk] using jshape_ind2.
- exact (ser_boolA HIx OBL_REALLOC_NF).
- destruct u; [exact (ser_udA HIx OBL_REALLOC_NF) | exact (ser_dblA HIx OBL_REALLOC_NF)].
- exact (ser_intA HIx OBL_REALLOC_NF PFRT PFLO OBL_PFRT OBL_PFLO SNP_LD SNP_LU).
- destruct h; [exact (ser_str_heapA HIx OBL_REALLOC_NF ESC) | exact (ser_str_inlineA HIx OBL_REALLOC_NF ESC)].
- exact (ser_objA HIx OBL_REALLOC_NF ESC kids IHk).
- exact (ser_arrA HIx OBL_REALLOC_NF kids IHk).
Qed.
End All.
End RC__1.
