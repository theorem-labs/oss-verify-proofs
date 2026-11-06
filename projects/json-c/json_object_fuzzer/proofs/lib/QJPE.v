(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup Lib.GwApply QWxq_c1 Lib.SepCache Qfw3_c1 QRjH QHnV QCcH QfLs Q0Ek QjDH QTEu Qsw7 QJjn QRUw Q7UD QXUB Qhd4 Qwm6 QlKV Q4v2 QgHv Q1Y6 QsKa QpNt Qw5U Q9O6 QL3k Ql4f Q228 QJZd QfS1_c1 Q1Ey QsjA Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun Qfw3_c1.Mq2.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0. Import QTEu. Import Qsw7 QJjn QRUw QRUw.Mq0.
Import Q7UD QXUB.Mq0 Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa Q4v2.Mq0 QgHv.Mq0 Q1Y6.Mq1 QsKa.Mq6 QsKa.Mq7 QpNt.Mq4 QsKa.Mq8 Qw5U.Mq0 QlKV.Mq2 QsKa Q9O6.Mq2 QL3k.Mq1 Ql4f.Mq2 Qwm6.Mq1 Q228.Mq5 QJZd.Mq6 QfS1_c1.Mq0.

Import QWxq_c1 QsjA.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Notation wz := (Z_to_bv 64) (only parsing).
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section Ser.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Hypothesis OBL_REALLOC_NF : realloc_nf_stmt HIx.

Lemma ser_dblA_0 : ser_specA_al HIx 0 ASER_DBL (Sdouble false).
Proof.
unfold ser_specA_al, ser_specA. intros until errv. intros D32 HP PB JN INCL JTX CAP TXT NEED FL Hlv Hlvd FRSN ST LO LOS SPA HT ERR JHX TP' RA FRM A0 A1 A2 A3 K.
destruct JN as (bits & EREST & SPEC & NODE). pose proof NODE as NODE0. stash NODE0. unfold jhdr_cells in NODE. cbn [app] in NODE.
subst a0 a1 a2 a3 tp REST.
cbn [app jtx] in JTX. injection JTX as <- _.
unfold ASER_DBL, ser_budgetA, ASER_LEVEL, ASER_LEAF in *. cbn [sdepth Z.mul Z.add] in LOS.
word_range sp SPR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
pose proof alloc_ceiling_range as ACR.
pose proof (hiA_top_le A4L HIx) as HTLE.
destruct (heapA_sb_cells A4L HIx _ _ _ _ _ _ _ HP) as (SB1 & SB2 & SB3 & SB4).
apply ro_C8_of_bytes_at in SB1. apply ro_C8_of_bytes_at in SB2. apply ro_C8_of_bytes_at in SB3.
assert (UARC : ro_cells asegs m (hl_uar_cell A4L) [C4 (Z_to_bv 64 1)]) by (split; [cbn; split; exact I | cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact SB4]).
clear SB4.
assert (INp0 : In (p, 48) LB) by (apply INCL; left; reflexivity).
assert (INp : In (p, 48) ((pb, PB_SZ) :: (buf, cap) :: LB)) by (right; right; exact INp0).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ p 48 HP ltac:(apply in_or_app; left; exact INp)) as (_ & Hpal & Hplo & Hphi & _).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ pb PB_SZ HP ltac:(apply in_or_app; left; left; reflexivity)) as (_ & Hal & Hlo & Hhi & _).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ buf cap HP ltac:(apply in_or_app; left; right; left; reflexivity)) as (_ & Hbal & Hblo & Hbhi & _).
unfold_consts.
shadow_inA A4L HIx HP INp SHp.
pose proof PB as (Hbp & Hcap & Hlen & PBS & PBUF).
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp + -128, bv_unsigned sp)] m) as MU.
a4l. reenterA asegs A4L HIx asegs_wx HP.
step. step. step.
carve_frame 128%nat ST.
step. stepz. do 13 step.
step. step.
rewrite (unsigned_lit (bv_unsigned sp + -128)) by lia. change 18446744073709551584 with (2^64 - 2^5). rewrite OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.land_align_down by lia. change (2^5) with 32.
replace (bv_unsigned sp + -128 - (bv_unsigned sp + -128) mod 32) with (bv_unsigned sp + -128) by (clear - D32; Z.div_mod_to_equations; lia).
do 11 step.
norm_sx32. step. if_false. step. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
match goal with H : mem_inv asegs m1 |- _ => rename H into MI1 end.
evt_done5.
eapply (stack_malloc_full HIx) with (k := 2) (bytes := 192) (lo := lo) (LB := (pb, PB_SZ) :: (buf, cap) :: LB) (LM := LM) (FR := FRS) (B := B);
[ heap_nowA A4L HIx HP MU WM MI1 | lia | .. ].
all: rewrite ?unsigned_lit by lia.
1: rewrite fr_size_2; lia.
1: reflexivity.
1: lia.
1: exact ST.
1: exact LO.
1: cbn [hl_stack_A A4L]; lia.
1: clear - D32; Z.div_mod_to_equations; lia.
1: lia.
1: reflexivity.
1: reflexivity.
intros ms1 m1' md1 A1 Fr RS1 VM1 ST1 HPR1 FRNZ (jff & FF1) SHB1 HP1. open_ret RS1.
destruct (heapA_errno A4L HIx _ _ _ _ _ _ _ HP1) as (errv1 & ERR1). unfold A_ERRNO, A_TP in ERR1. cbn [hl_tp A4L A4H hla_base] in ERR1.
rewrite ?unsigned_lit in ST1, HPR1 by lia.
clear ERR.
assert (INF : In (Fr, 2) ((Fr, 2) :: FRS)) by (left; reflexivity).
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP1 INF) as (_ & HFal & HF0 & HFc & HFimg & _ & HFshw & _).
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP1 INF) as HFapp.
pose proof (frame_above_img HIx _ _ _ _ _ _ _ _ _ HP1 INF) as HFhi. cbn [hl_img_hi A4H] in HFhi.
rewrite fr_size_2 in HFal, HFc, HFimg, HFapp. change (fr_shadow_len 2) with 32 in HFshw. cbn [hl_img_lo hl_img_hi hla_base hl_sb A4L A4H] in HFimg, HFapp. unfold A_SB in HFapp.
change ((2 ^ 47 - 1) / 8 + 2147450880 + 1) with 17594333495296 in HFapp.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR1) in FR; [| left; cbn; lia].
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR1) in NODE; [| eapply client_range_block; [apply in_or_app; left; exact INp | lia | cbn; lia]].
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR1) in PBS; [| eapply client_range_block; [apply in_or_app; left; left; reflexivity | cbn; lia | cbn; lia]].
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR1) in PBUF; [| eapply client_range_block; [apply in_or_app; left; right; left; reflexivity | cbn; lia | cbn; lia]].
clear SB1 SB2 SB3 UARC SHp.
shadow_inA A4L HIx HP1 INp SHp.
assert (INpX : In (p, 48) (((pb, PB_SZ) :: (buf, cap) :: LB) ++ LM)) by (apply in_or_app; left; exact INp).
assert (INpbX : In (pb, PB_SZ) (((pb, PB_SZ) :: (buf, cap) :: LB) ++ LM)) by (apply in_or_app; left; left; reflexivity).
assert (INbufX : In (buf, cap) (((pb, PB_SZ) :: (buf, cap) :: LB) ++ LM)) by (apply in_or_app; left; right; left; reflexivity).
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP1 INF INpX) as DFp. rewrite fr_size_2 in DFp.
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP1 INF INpbX) as DFpb. rewrite fr_size_2 in DFpb.
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP1 INF INbufX) as DFbuf. rewrite fr_size_2 in DFbuf.
pose proof (heapA_blk_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP1 INpX) as APp. cbn [hl_sb A4L] in APp. unfold A_SB in APp.
pose proof (heapA_blk_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP1 INpbX) as APpb. cbn [hl_sb A4L] in APpb. unfold A_SB in APpb.
pose proof (heapA_blk_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP1 INbufX) as APbuf. cbn [hl_sb A4L] in APbuf. unfold A_SB in APbuf.
assert (FSH1 : rw_cells asegs m1' (shad A4L Fr) [CB 32 (repeat (Z_to_bv 8 0) 32)]).
{ split; [split; [cbn; split; [reflexivity | exact I] | cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact SHB1] | exact HFshw]. }
clear SHB1.
rewrite fr_size_2 in FF1. change (Z.to_nat (256 - 8)) with 248%nat in FF1.
unfold shad in FSH1. a4l.
set (sh := Fr / 8 + 2147450880) in *.
assert (SHR : 2147450880 <= sh /\ sh + 32 <= 17594333495296) by (unfold sh; clear - HF0 HFc ACR; Z.div_mod_to_equations; lia).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP1) as MI1'. change (hl_segs A4L) with asegs in MI1'. clear MI1.

assert (SUB0 : forall b, In b (LB ++ LM ++ fr_ivs A4L FRS) -> In b (((pb, PB_SZ) :: (buf, cap) :: LB) ++ LM) \/ In b (fr_ivs A4L FRS)).
{ intros b Hb. apply in_app_or in Hb as [Hb|Hb]; [left; apply in_or_app; left; right; right; exact Hb|]. apply in_app_or in Hb as [Hb|Hb]; [left; apply in_or_app; right; exact Hb | right; exact Hb]. }
assert (SUB1 : forall b, In b (LB ++ LM ++ fr_ivs A4L FRS) -> In b (((pb, PB_SZ) :: (buf, cap) :: LB) ++ LM) \/ In b (fr_ivs A4L ((Fr, 2) :: FRS))).
{ intros b Hb. destruct (SUB0 b Hb) as [H|H]; [left; exact H | right; cbn [fr_ivs flat_map app]; right; right; exact H]. }
destruct (own_frame_fresh HIx Fr 2 ((pb, PB_SZ) :: (buf, cap) :: LB) LB LM FRS B A1 m1' md1 HP1 ltac:(intros b Hb; right; right; exact Hb)) as [OFF OFS].
assert (HPR01 : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m1').
{ eapply heap_pres_trans.
- eapply (pres_private HIx _ _ _ _ _ _ _ _ _ _ (bv_unsigned sp) HP MU WM SUB0 ltac:(lia)). apply Forall_cons; [| apply Forall_nil]. left. cbn [fst snd]. lia.
- eapply heap_pres_weaken; [exact HPR1 | lia |]. intros b Hb. apply in_app_or in Hb as [Hb|Hb]; [apply in_or_app; left; right; right; exact Hb | apply in_or_app; right; exact Hb]. }
clear MU WM. pose proof (wmono_refl asegs m1') as WM. pose proof (munch_refl [(lo, bv_unsigned sp); (Fr, Fr + 248); (sh, sh + 32)] m1') as MU.
reenterA asegs A4L HIx asegs_wx HP1.
step. step. step. if_truex.
step. step. step. step.
rewrite (unsigned_lit Fr) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
step. step. step. step.
stepz. stepz. stepz. step. step.
fold sh.
do 4 stepz. step. step.
do 19 stepz.

step; sh_norm;
repeat match goal with
| |- context [ (?p + ?j) / 8 ] => is_Zlit j; rewrite (div8_add p j) by lia; let k := eval vm_compute in (Z.div j 8) in change (j / 8) with k
end.
do 12 stepz.
step; sh_norm;
repeat match goal with
| |- context [ (?p + ?j) / 8 ] => is_Zlit j; rewrite (div8_add p j) by lia; let k := eval vm_compute in (Z.div j 8) in change (j / 8) with k
end.
step. stepz. step. first [ if_false | if_true ]. rewrite ?sxb_zero, ?zxb_zero.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
match goal with H : mem_inv asegs m2 |- _ => rename H into MI2 end.
match goal with H : stk asegs m2 lo _ |- _ => rename H into ST2 end.
assert (HPc : HEAPAx A1 ((pb, PB_SZ) :: (buf, cap) :: LB) LM ((Fr, 2) :: FRS) B m2 md1).
{ eapply (heapA_client_frame A4L HIx); [exact HP1 | | exact WM | exact MI2].
eapply (frame_writes_okF A4L HIx _ _ _ _ _ _ _ _ _ HP1 MU).
apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]].
- left. cbn [fst snd]. lia.
- right; right; right. exists Fr, 2. split; [exact INF|]. left. cbn [fst snd]. rewrite fr_size_2. lia.
- right; right; right. exists Fr, 2. split; [exact INF|]. right. unfold shad. cbn [fst snd hl_sb A4L]. change (fr_shadow_len 2) with 32. unfold A_SB. fold sh. lia. }
assert (HPR02 : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m2).
{ eapply heap_pres_trans; [exact HPR01|].
eapply (pres_private HIx _ _ _ _ _ _ _ _ _ _ (bv_unsigned sp) HP1 MU WM SUB1 ltac:(lia)).
apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]].
+ left. cbn [fst snd]. lia.
+ right; right; right. exists Fr, 2. split; [exact INF|]. split; [exact OFF|]. split; [exact OFS|]. left. cbn [fst snd]. rewrite fr_size_2. lia.
+ right; right; right. exists Fr, 2. split; [exact INF|]. split; [exact OFF|]. split; [exact OFS|]. right. unfold shad. cbn [fst snd hl_sb A4L]. change (fr_shadow_len 2) with 32. unfold A_SB. fold sh. lia. }
eapply (rw_cells_split_CB asegs _ _ [_; _; _] 224 _ [] [8%nat; 128%nat; 88%nat]) in FF1; [| reflexivity].
cbn [app mk_CB_cells] in FF1.
apply (proj1 (rw_cells_app asegs _ _ [_; _; _] _)) in FR. destruct FR as [LOC SAV]. cbn [cells_size csize Nat.add] in SAV.
change (Z.of_nat 24) with 24 in SAV. replace (bv_unsigned sp + -128 + 24) with (bv_unsigned sp + -104) in SAV by lia.
fold_mkR. subst sh.
evt_done5.
unstash NODE0.
eapply (dbl_armsA HIx OBL_REALLOC_NF ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB LM FRS B pb lo bpos cap T (bv_unsigned sp + -128) 0 Fr
ltac:(lia) ltac:(lia) ltac:(clear - D32; Z.div_mod_to_equations; lia) LO ltac:(unfold ADBL_STACK; lia) HT CAP TXT NEED K p rc pb0 fl bits INp0 NODE0 SPEC)
with (bufb := firstn 128 (skipn 8 (skipn 8 (skipn 8 (skipn 8 jff))))); [ | apply fsaved_refl | exact FRM ].
lazymatch type of LOC with rw_cells _ _ _ ?locc => lazymatch type of FF1 with rw_cells _ _ _ [_; _; _; CB 8 ?j8; CB 128 ?bufb; CB 88 ?jr] => lazymatch type of FSH1 with rw_cells _ _ _ ?shc =>
lazymatch shc with context [CB 8 ?t8] => exists locc, j8, jr, t8 end end end end.
split; [reflexivity|].
exists buf, cap, bpos, content, errv1, B.
split; [exact HPc|].
split; [split; [lia|]; split; [lia|]; split; [exact Hlen|]; split; [exact PBS | exact PBUF]|].
split. { unfold dblCH. constructor; [exact LOC|]. constructor; [exact SAV|]. constructor; [exact FF1|]. constructor; [exact FSH1 | constructor]. }
split.
{ unfold dblCH. constructor; [left; cbn [fst]; lia|].
constructor; [left; cbn [fst]; lia|].
constructor; [right; right; exists (Fr, fr_size 2 - 8); split; [apply in_or_app; right; apply in_or_app; right; apply fr_ivs_frame; exact INF | unfold dblFF; cbn [blk_addr blk_size fst snd cells_size csize Nat.add]; rewrite fr_size_2; lia]|].
constructor; [right; right; exists (shad A4L Fr, fr_shadow_len 2); split; [apply in_or_app; right; apply in_or_app; right; apply fr_ivs_shadow; exact INF | unfold shad, dblSH; cbn [blk_addr blk_size fst snd cells_size csize Nat.add hl_sb A4L]; change (fr_shadow_len 2) with 32; unfold A_SB; lia]|].
constructor. }
split; [intros b Hb; cbn [fr_ivs flat_map app]; right; right; exact Hb|].
split; [exact ERR1|]. split; [exact ST2|].
split; [exact HPR02|].
split; [exact VM1|].
split; [lia|]. split; [unfold ser_capb; lia|]. split; lia.
Qed.
End Ser.
End RC__1.
End Mq0.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.SepCache.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qfw3_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfw3_c1.Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QjDH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDH.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTEu.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTEu. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbFI. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXUB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXUB.  From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qhd4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qhd4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqj. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4v2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4v2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QgHv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QgHv. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1Y6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1Y6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mqf. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mqg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpNt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpNt.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mqh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qw5U.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qw5U.Mq5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9O6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9O6.Mq5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QL3k.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QL3k.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Ql4f.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql4f. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q228.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q228.Mqd. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJZd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJZd.Mqf. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfS1_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfS1_c1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSHS.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsjA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsjA.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Notation wz := (Z_to_bv 64) (only parsing).
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section Ser.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Hypothesis OBL_REALLOC_NF : realloc_nf_stmt HIx.

Lemma ser_dblA_0 : ser_specA_al HIx 0 ASER_DBL (Sdouble false).
Proof.
unfold ser_specA_al, ser_specA. intros until errv. intros D32 HP PB JN INCL JTX CAP TXT NEED FL Hlv Hlvd FRSN ST LO LOS SPA HT ERR JHX TP' RA FRM A0 A1 A2 A3 K.
destruct JN as (bits & EREST & SPEC & NODE). pose proof NODE as NODE0. stash NODE0. unfold jhdr_cells in NODE. cbn [app] in NODE.
subst a0 a1 a2 a3 tp REST.
cbn [app jtx] in JTX. injection JTX as <- _.
unfold ASER_DBL, ser_budgetA, ASER_LEVEL, ASER_LEAF in *. cbn [sdepth Z.mul Z.add] in LOS.
word_range sp SPR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
pose proof alloc_ceiling_range as ACR.
pose proof (hiA_top_le A4L HIx) as HTLE.
destruct (heapA_sb_cells A4L HIx _ _ _ _ _ _ _ HP) as (SB1 & SB2 & SB3 & SB4).
apply ro_C8_of_bytes_at in SB1. apply ro_C8_of_bytes_at in SB2. apply ro_C8_of_bytes_at in SB3.
assert (UARC : ro_cells asegs m (hl_uar_cell A4L) [C4 (Z_to_bv 64 1)]) by (split; [cbn; split; exact I | cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact SB4]).
clear SB4.
assert (INp0 : In (p, 48) LB) by (apply INCL; left; reflexivity).
assert (INp : In (p, 48) ((pb, PB_SZ) :: (buf, cap) :: LB)) by (right; right; exact INp0).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ p 48 HP ltac:(apply in_or_app; left; exact INp)) as (_ & Hpal & Hplo & Hphi & _).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ pb PB_SZ HP ltac:(apply in_or_app; left; left; reflexivity)) as (_ & Hal & Hlo & Hhi & _).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ buf cap HP ltac:(apply in_or_app; left; right; left; reflexivity)) as (_ & Hbal & Hblo & Hbhi & _).
unfold_consts.
shadow_inA A4L HIx HP INp SHp.
pose proof PB as (Hbp & Hcap & Hlen & PBS & PBUF).
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp + -128, bv_unsigned sp)] m) as MU.
a4l. reenterA asegs A4L HIx asegs_wx HP.
step. step. step.
carve_frame 128%nat ST.
step. stepz. do 13 step.
step. step.
rewrite (unsigned_lit (bv_unsigned sp + -128)) by lia. change 18446744073709551584 with (2^64 - 2^5). rewrite OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.land_align_down by lia. change (2^5) with 32.
replace (bv_unsigned sp + -128 - (bv_unsigned sp + -128) mod 32) with (bv_unsigned sp + -128) by (clear - D32; Z.div_mod_to_equations; lia).
do 11 step.
norm_sx32. step. if_false. step. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
match goal with H : mem_inv asegs m1 |- _ => rename H into MI1 end.
evt_done5.
eapply (stack_malloc_full HIx) with (k := 2) (bytes := 192) (lo := lo) (LB := (pb, PB_SZ) :: (buf, cap) :: LB) (LM := LM) (FR := FRS) (B := B);
[ heap_nowA A4L HIx HP MU WM MI1 | lia | .. ].
all: rewrite ?unsigned_lit by lia.
1: rewrite fr_size_2; lia.
1: reflexivity.
1: lia.
1: exact ST.
1: exact LO.
1: cbn [hl_stack_A A4L]; lia.
1: clear - D32; Z.div_mod_to_equations; lia.
1: lia.
1: reflexivity.
1: reflexivity.
intros ms1 m1' md1 A1 Fr RS1 VM1 ST1 HPR1 FRNZ (jff & FF1) SHB1 HP1. open_ret RS1.
destruct (heapA_errno A4L HIx _ _ _ _ _ _ _ HP1) as (errv1 & ERR1). unfold A_ERRNO, A_TP in ERR1. cbn [hl_tp A4L A4H hla_base] in ERR1.
rewrite ?unsigned_lit in ST1, HPR1 by lia.
clear ERR.
assert (INF : In (Fr, 2) ((Fr, 2) :: FRS)) by (left; reflexivity).
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP1 INF) as (_ & HFal & HF0 & HFc & HFimg & _ & HFshw & _).
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP1 INF) as HFapp.
pose proof (frame_above_img HIx _ _ _ _ _ _ _ _ _ HP1 INF) as HFhi. cbn [hl_img_hi A4H] in HFhi.
rewrite fr_size_2 in HFal, HFc, HFimg, HFapp. change (fr_shadow_len 2) with 32 in HFshw. cbn [hl_img_lo hl_img_hi hla_base hl_sb A4L A4H] in HFimg, HFapp. unfold A_SB in HFapp.
change ((2 ^ 47 - 1) / 8 + 2147450880 + 1) with 17594333495296 in HFapp.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR1) in FR; [| left; cbn; lia].
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR1) in NODE; [| eapply client_range_block; [apply in_or_app; left; exact INp | lia | cbn; lia]].
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR1) in PBS; [| eapply client_range_block; [apply in_or_app; left; left; reflexivity | cbn; lia | cbn; lia]].
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR1) in PBUF; [| eapply client_range_block; [apply in_or_app; left; right; left; reflexivity | cbn; lia | cbn; lia]].
clear SB1 SB2 SB3 UARC SHp.
shadow_inA A4L HIx HP1 INp SHp.
assert (INpX : In (p, 48) (((pb, PB_SZ) :: (buf, cap) :: LB) ++ LM)) by (apply in_or_app; left; exact INp).
assert (INpbX : In (pb, PB_SZ) (((pb, PB_SZ) :: (buf, cap) :: LB) ++ LM)) by (apply in_or_app; left; left; reflexivity).
assert (INbufX : In (buf, cap) (((pb, PB_SZ) :: (buf, cap) :: LB) ++ LM)) by (apply in_or_app; left; right; left; reflexivity).
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP1 INF INpX) as DFp. rewrite fr_size_2 in DFp.
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP1 INF INpbX) as DFpb. rewrite fr_size_2 in DFpb.
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP1 INF INbufX) as DFbuf. rewrite fr_size_2 in DFbuf.
pose proof (heapA_blk_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP1 INpX) as APp. cbn [hl_sb A4L] in APp. unfold A_SB in APp.
pose proof (heapA_blk_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP1 INpbX) as APpb. cbn [hl_sb A4L] in APpb. unfold A_SB in APpb.
pose proof (heapA_blk_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP1 INbufX) as APbuf. cbn [hl_sb A4L] in APbuf. unfold A_SB in APbuf.
assert (FSH1 : rw_cells asegs m1' (shad A4L Fr) [CB 32 (repeat (Z_to_bv 8 0) 32)]).
{ split; [split; [cbn; split; [reflexivity | exact I] | cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact SHB1] | exact HFshw]. }
clear SHB1.
rewrite fr_size_2 in FF1. change (Z.to_nat (256 - 8)) with 248%nat in FF1.
unfold shad in FSH1. a4l.
set (sh := Fr / 8 + 2147450880) in *.
assert (SHR : 2147450880 <= sh /\ sh + 32 <= 17594333495296) by (unfold sh; clear - HF0 HFc ACR; Z.div_mod_to_equations; lia).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP1) as MI1'. change (hl_segs A4L) with asegs in MI1'. clear MI1.

assert (SUB0 : forall b, In b (LB ++ LM ++ fr_ivs A4L FRS) -> In b (((pb, PB_SZ) :: (buf, cap) :: LB) ++ LM) \/ In b (fr_ivs A4L FRS)).
{ intros b Hb. apply in_app_or in Hb as [Hb|Hb]; [left; apply in_or_app; left; right; right; exact Hb|]. apply in_app_or in Hb as [Hb|Hb]; [left; apply in_or_app; right; exact Hb | right; exact Hb]. }
assert (SUB1 : forall b, In b (LB ++ LM ++ fr_ivs A4L FRS) -> In b (((pb, PB_SZ) :: (buf, cap) :: LB) ++ LM) \/ In b (fr_ivs A4L ((Fr, 2) :: FRS))).
{ intros b Hb. destruct (SUB0 b Hb) as [H|H]; [left; exact H | right; cbn [fr_ivs flat_map app]; right; right; exact H]. }
destruct (own_frame_fresh HIx Fr 2 ((pb, PB_SZ) :: (buf, cap) :: LB) LB LM FRS B A1 m1' md1 HP1 ltac:(intros b Hb; right; right; exact Hb)) as [OFF OFS].
assert (HPR01 : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m1').
{ eapply heap_pres_trans.
- eapply (pres_private HIx _ _ _ _ _ _ _ _ _ _ (bv_unsigned sp) HP MU WM SUB0 ltac:(lia)). apply Forall_cons; [| apply Forall_nil]. left. cbn [fst snd]. lia.
- eapply heap_pres_weaken; [exact HPR1 | lia |]. intros b Hb. apply in_app_or in Hb as [Hb|Hb]; [apply in_or_app; left; right; right; exact Hb | apply in_or_app; right; exact Hb]. }
clear MU WM. pose proof (wmono_refl asegs m1') as WM. pose proof (munch_refl [(lo, bv_unsigned sp); (Fr, Fr + 248); (sh, sh + 32)] m1') as MU.
reenterA asegs A4L HIx asegs_wx HP1.
step. step. step. if_truex.
stepz.
step. step. step. step.
rewrite (unsigned_lit Fr) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
step. step. step.
stepz. stepz. stepz. step. step.
fold sh.
do 4 stepz. step.
do 20 stepz.
step. if_falsex.
step. step. ubsan_align Hpal.
step.

step; sh_norm;
repeat match goal with
| |- context [ (?p + ?j) / 8 ] => is_Zlit j; rewrite (div8_add p j) by lia; let k := eval vm_compute in (Z.div j 8) in change (j / 8) with k
end.
step; sh_norm;
repeat match goal with
| |- context [ (?p + ?j) / 8 ] => is_Zlit j; rewrite (div8_add p j) by lia; let k := eval vm_compute in (Z.div j 8) in change (j / 8) with k
end.
step. step. first [ if_false | if_true ]. rewrite ?sxb_zero, ?zxb_zero.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
match goal with H : mem_inv asegs m2 |- _ => rename H into MI2 end.
match goal with H : stk asegs m2 lo _ |- _ => rename H into ST2 end.
assert (HPc : HEAPAx A1 ((pb, PB_SZ) :: (buf, cap) :: LB) LM ((Fr, 2) :: FRS) B m2 md1).
{ eapply (heapA_client_frame A4L HIx); [exact HP1 | | exact WM | exact MI2].
eapply (frame_writes_okF A4L HIx _ _ _ _ _ _ _ _ _ HP1 MU).
apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]].
- left. cbn [fst snd]. lia.
- right; right; right. exists Fr, 2. split; [exact INF|]. left. cbn [fst snd]. rewrite fr_size_2. lia.
- right; right; right. exists Fr, 2. split; [exact INF|]. right. unfold shad. cbn [fst snd hl_sb A4L]. change (fr_shadow_len 2) with 32. unfold A_SB. fold sh. lia. }
assert (HPR02 : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m2).
{ eapply heap_pres_trans; [exact HPR01|].
eapply (pres_private HIx _ _ _ _ _ _ _ _ _ _ (bv_unsigned sp) HP1 MU WM SUB1 ltac:(lia)).
apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]].
+ left. cbn [fst snd]. lia.
+ right; right; right. exists Fr, 2. split; [exact INF|]. split; [exact OFF|]. split; [exact OFS|]. left. cbn [fst snd]. rewrite fr_size_2. lia.
+ right; right; right. exists Fr, 2. split; [exact INF|]. split; [exact OFF|]. split; [exact OFS|]. right. unfold shad. cbn [fst snd hl_sb A4L]. change (fr_shadow_len 2) with 32. unfold A_SB. fold sh. lia. }
eapply (rw_cells_split_CB asegs _ _ [_; _; _] 224 _ [] [8%nat; 128%nat; 88%nat]) in FF1; [| reflexivity].
cbn [app mk_CB_cells] in FF1.
apply (proj1 (rw_cells_app asegs _ _ [_; _; _] _)) in FR. destruct FR as [LOC SAV]. cbn [cells_size csize Nat.add] in SAV.
change (Z.of_nat 24) with 24 in SAV. replace (bv_unsigned sp + -128 + 24) with (bv_unsigned sp + -104) in SAV by lia.
fold_mkR. subst sh.
evt_done5.
unstash NODE0.
eapply (dbl_armsA HIx OBL_REALLOC_NF ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB LM FRS B pb lo bpos cap T (bv_unsigned sp + -128) 0 Fr
ltac:(lia) ltac:(lia) ltac:(clear - D32; Z.div_mod_to_equations; lia) LO ltac:(unfold ADBL_STACK; lia) HT CAP TXT NEED K p rc pb0 fl bits INp0 NODE0 SPEC)
with (bufb := firstn 128 (skipn 8 (skipn 8 (skipn 8 (skipn 8 jff))))); [ | apply fsaved_refl | exact FRM ].
lazymatch type of LOC with rw_cells _ _ _ ?locc => lazymatch type of FF1 with rw_cells _ _ _ [_; _; _; CB 8 ?j8; CB 128 ?bufb; CB 88 ?jr] => lazymatch type of FSH1 with rw_cells _ _ _ ?shc =>
lazymatch shc with context [CB 8 ?t8] => exists locc, j8, jr, t8 end end end end.
split; [reflexivity|].
exists buf, cap, bpos, content, errv1, B.
split; [exact HPc|].
split; [split; [lia|]; split; [lia|]; split; [exact Hlen|]; split; [exact PBS | exact PBUF]|].
split. { unfold dblCH. constructor; [exact LOC|]. constructor; [exact SAV|]. constructor; [exact FF1|]. constructor; [exact FSH1 | constructor]. }
split.
{ unfold dblCH. constructor; [left; cbn [fst]; lia|].
constructor; [left; cbn [fst]; lia|].
constructor; [right; right; exists (Fr, fr_size 2 - 8); split; [apply in_or_app; right; apply in_or_app; right; apply fr_ivs_frame; exact INF | unfold dblFF; cbn [blk_addr blk_size fst snd cells_size csize Nat.add]; rewrite fr_size_2; lia]|].
constructor; [right; right; exists (shad A4L Fr, fr_shadow_len 2); split; [apply in_or_app; right; apply in_or_app; right; apply fr_ivs_shadow; exact INF | unfold shad, dblSH; cbn [blk_addr blk_size fst snd cells_size csize Nat.add hl_sb A4L]; change (fr_shadow_len 2) with 32; unfold A_SB; lia]|].
constructor. }
split; [intros b Hb; cbn [fr_ivs flat_map app]; right; right; exact Hb|].
split; [exact ERR1|]. split; [exact ST2|].
split; [exact HPR02|].
split; [exact VM1|].
split; [lia|]. split; [unfold ser_capb; lia|]. split; lia.
Qed.
End Ser.
End RC__1.
