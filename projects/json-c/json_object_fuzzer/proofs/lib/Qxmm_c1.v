(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup Lib.GwApply Lib.SepCache QWxq_c1 Qfw3_c1 Qc3B Q5Rg QZDE QRjH QHnV QCcH QfLs Q0Ek QjDH QmZZ Qsw7 QJjn QKQo Q8tj QRUw QSL3 Qvbw QYIF QnCn QR2u QrIB Q7UD QXUB Qhd4 Qwm6 QlKV QsKa QJZd Qw5U Q9O6 Qiiq Q1Ey Qvmy Qawr Q30W Q2Do Ql4f QJlD Qu4M QUr4 Q3jZ Qmd7 Q22i Qg1M QkXq Q1Y6 QvPk Qoif Qkxa QjKS QnPO QB6X QSHS Qeia QRcT QkDD QgwQ QPZI Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

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
Import QUr4.
Import Q3jZ Qmd7 Q22i.
Import Qg1M.
Import Q30W.Mq3 QkXq.Mq2 Q1Y6.Mq0 Q30W.Mq1 QvPk Qoif.Mq0.

Import Qwm6.Mq2.
Import QB6X QSHS.Mq1 Qeia.Mq4 Qoif.Mq2 QRcT.Mq1.
Import Qeia.Mq3 QkDD.Mq0 QgwQ.Mq0.
Import QPZI.Mq4.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Q2qa.Mq0.sf_vocab ::= Q2qa.Mq0.mkr__sf_vocab_5. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Section MDcWrap.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Notation wz := (Z_to_bv 64).
Notation jroot_repA := (jroot_rep A4H A4F).
Hypothesis SHALLOW : shallow_A_stmt HIx.
Hypothesis PUT : put_stmt_A HIx.
Hypothesis OBL_STRDUP_NF : strdup_nf_stmt A4L HIx.
Hypothesis LF : lf_test_spec.
Hypothesis OBL_AMEMSET : amemset_spec_A HIx.
Hypothesis OBL_ISTRCMP : istrcmp_spec_U.
Variable HD : Z.
Hypothesis HD_ge : 96 + 4096 <= HD.
Hypothesis HD_le : 96 + 4096 + 128 + HD <= DC_C.
Hypothesis HASH : lh_char_hash_A_stmt HIx (fun a b : config => model_vm_only (cfg_model a) (cfg_model b)) HD.
Let DCA := (dcopy_A HIx SHALLOW PUT OBL_STRDUP_NF LF OBL_AMEMSET OBL_ISTRCMP HD HD_ge HD_le HASH).

Theorem deep_copy_A : jo_deep_copy_A_stmt HIx DC_A SH_A (32 + (DC_F + DC_C)) DC_F (fun w => DC_KB * w) (fun w => w).
Proof.
unfold jo_deep_copy_A_stmt. intros until errv. intros PRE SPA32 G JR DC DLOC DU DAL FRN RW WLT BBW BDW FRM A0 A1 A2 K.
destruct PRE as (HP & ST & LO & LOS & SPA & HT & ERR & TP & RA). subst a0 a1 a2 tp.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
unfold A_ERRNO, A_TP in ERR. change (6434400 - 164) with 6434236 in ERR.
assert (RD0 : 0 <= rdepth r) by (destruct r; cbn [rdepth]; try lia; apply sdepth_nonneg).
pose proof LOS as LOSu. unfold dc_stkA, DC_F, DC_C in LOSu.
pose proof alloc_ceiling_range as ACR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. change (hl_segs A4L) with asegs in MI.
destruct (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL]. a4l.
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (6434236, 6434240)] m) as MU.
assert (W0 : 0 <= w) by (destruct r as [|s|?|]; cbn [root_wA] in RW; [exact RW | destruct RW as (w0 & Y & R & J & LE); pose proof (QSHS.Mq1.jtx_ge8 _ _ _ _ J); lia | lia | destruct RW as (L & (len & _ & _ & AB) & WL); lia]).
stash K. stash DC. stash DU. stash G.
reenterA asegs A4L HIx asegs_wx HP.
carve_frame 32%nat ST.
step. stepz. stepz. stepz. stepz.
step. step. step. step.
idtac.
assert (NULLD : r = JRnull \/ r <> JRnull) by (destruct r; [left; reflexivity | right; discriminate | right; discriminate | right; discriminate]).
destruct NULLD as [Er | NN].
{
subst r. destruct JR as [Ep EB]. rewrite Ep. step. if_lit.
step. step. step. step.
try (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end).
pose proof (errno_shadowA HIx _ _ _ _ _ _ _ HP) as ESH0. a4l. change ((6434400 - 164) / 8 + 2147450880) with 2148255159 in ESH0.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (ESH : ro_cells asegs mc 2148255159 [C1 (Z_to_bv 8 0)]) by (eapply (ro_cells_transport asegs); [exact ESH0 | exact MU | cbn [disjoint_from cells_size csize Nat.add]; clear - SPR LOSu LO ACR RD0; lia]) end.
clear ESH0.
step. step. step. rewrite ?sxb_zero, ?zxb_zero. step. if_false.
step. stepz. step.
step. step. step. step. step.
release_frame FR ST (bv_unsigned sp).
step.
evt_done5. unstash K. unstash DC. unstash G.
replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 (2^64 - 1)) by (apply bv_eq; vm_compute; reflexivity).
lazymatch goal with |- context [MS _ _ _ _ _ ?mf _] =>
assert (HPRf : heap_pres A4H ((BS ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m mf);
[ eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MU | exact WM |];
eapply (client_outsideA A4L HIx); [exact HP | intros b Hb; exact Hb | clia | ];
apply Forall_cons; [left; cbn [fst snd]; clear - LO LOSu RD0 SPR; lia|];
apply Forall_cons; [right; right; cbn [fst snd]; intros x Hx; simpl hl_scratch; unfold A_TP; clear - Hx; lia | apply Forall_nil]
| eapply (K _ md mf (2^64 - 1) A B) ] end.
- split; [apply ret_statew_same|]. split; [apply model_vm_only_refl|]. split; [exact ST|]. split; [| eexists; eassumption].
apply (QrIB.Mq0.pres_presxD A4H). eapply heap_pres_weaken; [exact HPRf | lia | intros b Hb; rewrite EB; cbn [app]; exact Hb].
- unfold jo_chargeA. clear - W0 BBW. unfold DC_KB in *. cbn [bB bD]. lia.
- eapply lh_globA_client; [exact HPRf | exact G].
- cbn [jroot_rep]. split; [exact Ep | exact EB].
- right. split; [reflexivity|]. exists []. cbn [app]. split.
+ eapply (heap_pres_rw_cells A4H); [exact HPRf | exact DC |].
destruct DLOC as (Fd & kd & HFd & HD1 & HD2).
eapply client_range_block; [apply in_or_app; right; apply in_or_app; right; apply fr_ivs_frame; exact HFd | cbn; lia | cbn; lia].
+ eapply (heapA_client_frame A4L HIx); [exact HP | eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP MU) | exact WM | assumption].
apply Forall_cons; [left; cbn [fst snd]; clear - LO LOSu RD0 SPR HT; lia|].
apply Forall_cons; [right; right; cbn [fst snd]; intros x Hx; simpl hl_scratch; unfold A_TP; clear - Hx; lia | apply Forall_nil]. }

assert (Hp : p <> 0) by (destruct r as [|s|tojsx|]; [exfalso; exact (NN eq_refl) | exact (proj1 JR) | exact (proj1 JR) | exact (proj1 JR)]).
assert (WX : exists w0, dc_wtA r m BS p w0 /\ 1 <= w0 <= w).
{ destruct r as [|s|tojsx|]; [exfalso; exact (NN eq_refl) | | |]; cbn [root_wA] in RW; cbn [dc_wtA].
- destruct RW as (w0 & Y & R & J & LE). pose proof (QSHS.Mq1.jtx_ge8 _ _ _ _ J). exists w0. split; [exists Y, R; exact J | lia].
- exists w. split; [exact RW | lia].
- destruct RW as (L & SL & WL). exists w. split; [exists L; split; [exact SL | exact WL] |]. lia. }
destruct WX as (w0 & WT0 & W0R).
idtac.

assert (PB : exists np, In (p, np) BS /\ 48 <= np).
{ destruct r as [|s|tojsx|]; [exfalso; exact (NN eq_refl) | | |].
- destruct JR as [_ J]. pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND0.
assert (ND : List.NoDup (map blk_addr BS)) by (pose proof ND0 as X; rewrite !map_app in X; apply NoDup_app_remove_r in X; apply NoDup_app_remove_r in X; exact X).
destruct (jval_hdr asegs A4F s m BS p 1 J ND) as (n & tojs & pb & udel & ud & rest & INp & SZ & N48 & _). exists n. split; [exact INp | exact N48].
- destruct JR as (_ & _ & pb & PBS & bits & EBS & _). exists 48. split; [rewrite EBS; left; reflexivity | lia].
- destruct JR as (_ & pb & PBS & DBS & cap & len & str & EBS & _ & Hcap & _). exists (48 + cap). split; [rewrite EBS; left; reflexivity | lia]. }
destruct PB as (np & INp & Hnp).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ p np HP ltac:(apply in_or_app; left; apply in_or_app; left; exact INp)) as (_ & Hpal & Hplo & Hphi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hphi.
destruct DLOC as (Fd & kd & HFd & HD1 & HD2).
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP HFd) as (Hkd & HFdal & HFd0 & HFdc & HFimg & _). cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in HFimg.
pose proof (fr_size_pos kd ltac:(lia)) as FSP.
unstash DU. pose proof (unpoisoned8_cell asegs _ A_SB D DU DAL) as DSH0. unfold A_SB in DSH0.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (DSH : ro_cells asegs mc (D / 8 + 2147450880) [C1 (Z_to_bv 8 0)]) by (eapply (ro_cells_transport asegs); [exact DSH0 | exact MU | cbn [disjoint_from cells_size csize Nat.add]; clear - SPR LOSu LO ACR RD0 HD1 HD2 HFd0 HFdc FSP; Z.div_mod_to_equations; lia]);
unstash DC; assert (DCc : rw_cells asegs mc D [C8 (wz 0)]) by (eapply (rw_cells_transport asegs); [exact DC | exact MU | exact WM | cbn [disjoint_from cells_size csize Nat.add]; clear - SPR LOSu LO ACR RD0 HD1 HD2 HFd0 HFdc HFimg FSP; lia])
end.
clear DSH0. stash DC.
step. if_falsex. step. if_falsex.
asan_chk0.
step. step. if_lit.
step. step. unfold SH_A. if_lit.
step. step. step. step. step. step.
idtac.

assert (HP1 : HEAPAx A (BS ++ LB) LM FRS B m1 md).
{ eapply (heapA_client_frame A4L HIx); [exact HP | eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP MU) | exact WM | exact MI].
apply Forall_cons; [left; cbn [fst snd]; clear - LO LOSu RD0 SPR HT; lia|].
apply Forall_cons; [right; right; cbn [fst snd]; intros x Hx; simpl hl_scratch; unfold A_TP; clear - Hx; lia | apply Forall_nil]. }
assert (HPR1 : heap_pres A4H ((BS ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m1).
{ eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | intros b Hb; exact Hb | clia | ].
apply Forall_cons; [left; cbn [fst snd]; clear - LO LOSu RD0 SPR; lia|].
apply Forall_cons; [right; right; cbn [fst snd]; intros x Hx; simpl hl_scratch; unfold A_TP; clear - Hx; lia | apply Forall_nil]. }
unstash G. unstash K.
assert (JR1 : jroot_repA r m1 BS p).
{ eapply (QrIB.Mq0.jroot_rep_agree A4H A4F); [exact JR | | apply incl_refl].
eapply (agree_of_heap_pres asegs A4H); [exact HPR1 | reflexivity | intros b Hb; apply in_or_app; left; apply in_or_app; left; exact Hb]. }
assert (WT1 : dc_wtA r m1 BS p w0).
{ destruct r as [|s|tojsx|]; [exfalso; exact (NN eq_refl) | exact WT0 | exact WT0 |]. cbn [dc_wtA] in WT0 |- *.
destruct WT0 as (L & (len & BY & RL & AB) & WL). exists L. split; [| exact WL]. exists len. split; [| split; [exact RL | exact AB]].
eapply (heap_pres_bytes_at A4H); [exact HPR1 | exact BY |].
eapply client_range_block; [apply in_or_app; left; apply in_or_app; left; exact INp | cbn; lia | rewrite length_le8; cbn; lia]. }
evt_done5.
eapply (DCA r NN) with (m := m1) (md := md) (T := T) (A := A) (LB := LB) (BS := BS) (LM := LM) (FRS := FRS) (B := B) (lo := lo) (p := p) (D := D) (w := w0) (errv := errv);
[ exact HP1 | exact JR1 | exact NN | eapply lh_globA_client; [exact HPR1 | exact G] | exact DCc | exists Fd, kd; split; [exact HFd | split; [exact HD1 | exact HD2]]
| eapply (QsKa.Mq6.unpoisoned_pres_frame HIx); [exact HP | exact HFd | exact HD1 | exact HD2 | exact DU | exact HPR1] | exact DAL
| rewrite ?unsigned_lit by lia; exact ST | exact LO | rewrite ?unsigned_lit by lia; clear - LOSu; unfold dc_stkA, DC_F, DC_C; lia
| rewrite ?unsigned_lit by lia; clear - SPA32 SPR LOSu LO ACR RD0; Z.div_mod_to_equations; lia | rewrite ?unsigned_lit by lia; clear - HT; lia
| exact ERR | reflexivity | rewrite ?unsigned_lit by lia; reflexivity | exact FRM | exact FRN | exact WT1 | clear - W0R WLT; lia
| clear - W0R BBW; unfold DC_KB in *; lia | clear - W0R BDW; lia | reflexivity | reflexivity | reflexivity | ].
idtac.
intros msr mdr mr rvr Ar Br (RSr & VMr & STr & PXr & (errr & ERRr)) Gr JRr (BDr & OUTr).
destruct RSr as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & F2 & fc2 & -> & FS2 & FRM2).
rewrite ?(unsigned_lit (bv_unsigned sp + -32)) in STr, PXr by lia.
change (hl_segs A4L) with asegs in *.
replace (ret_pc (wz 653112)) with (wz 653112) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP HFd) as HFa. cbn [hl_sb A4L] in HFa. unfold A_SB in HFa.
change ((2 ^ 47 - 1) / 8 + 2147450880 + 1) with 17594333495296 in HFa.

assert (FRr : rw_cells asegs mr (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra]).
{ eapply (QrIB.Mq0.presxD_rw_cells A4H); [exact PXr | exact FR | left; cbn; lia | cbn [cells_size csize Nat.add]; clear - HD1 HD2 HFdc LO LOSu RD0; lia]. }
assert (DSHr : ro_cells asegs mr (D / 8 + 2147450880) [C1 (Z_to_bv 8 0)]).
{ destruct DSH as [Hwf Hb]. split; [exact Hwf|].
eapply (QrIB.Mq0.presxD_bytes_at A4H); [exact PXr | exact Hb | |].
- cbn [cells_bytes cbytes app length].
eapply client_rangex_block; [apply in_or_app; right; apply in_or_app; right; apply fr_ivs_shadow; exact HFd | |].
+ unfold shad. cbn [hl_sb A4L]. unfold A_SB. clear - HD1. Z.div_mod_to_equations. lia.
+ unfold shad. cbn [hl_sb A4L]. unfold A_SB, fr_shadow_len.
assert (HF8 : Fd mod 64 = 0).
{ apply Z.mod_divide; [lia|]. apply (Z.divide_trans _ (fr_size kd)); [| apply Z.mod_divide; [lia | exact HFdal]]. exists (2 ^ kd). unfold fr_size. lia. }
unfold fr_size in HD2. clear - HD1 HD2 HF8 Hkd. assert (KK : kd = 0 \/ kd = 1 \/ kd = 2 \/ kd = 3) by lia. destruct KK as [-> | [-> | [-> | ->]]]; cbn in *; Z.div_mod_to_equations; lia.
- cbn [cells_bytes cbytes app length]. clear - HD1 HD2 HFa HFd0 FSP. Z.div_mod_to_equations. lia. }
clear FR DSH. a4l.
destruct OUTr as [(-> & d & q & CBS & REM & CO & CW & Hq & DCr & JD & BBr & HPr) | (-> & q & CBS & REM & DCr & FRq & BBr & HPr)].
-
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HPr) as MIr. change (hl_segs A4L) with asegs in MIr.
pose proof (wmono_refl asegs mr) as WMr. pose proof (munch_refl (@nil (Z * Z)) mr) as MUr.
reenterA asegs A4L HIx asegs_wx HPr.
step. step. step. if_lit.
step. step. step. step. step.
release_frame FRr STr (bv_unsigned sp).
step.
evt_done5.
eapply (K _ mdr mr 0 Ar Br).
+ split; [apply ret_statew_intro; [exact FS2 | exact FRM2] |]. split; [exact VMr|]. split; [exact STr|]. split; [| exists errr; exact ERRr].
change (QYIF.heap_presxD A4H D (LB ++ (LM ++ fr_ivs A4L FRS)) (bv_unsigned sp) m mr).
eapply (QrIB.Mq0.presxD_trans A4H).
* apply (QrIB.Mq0.pres_presxD A4H). eapply heap_pres_weaken; [exact HPR1 | lia | intros b Hb].
apply in_app_or in Hb. apply in_or_app. destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; exact Hb | right; exact Hb].
* eapply (QrIB.Mq0.presxD_weaken A4H); [exact PXr | lia | intros b Hb].
apply in_app_or in Hb. apply in_or_app. destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; exact Hb | right; exact Hb].
+ unfold jo_chargeA. cbn [bB bD]. clear - BBr BDr W0R. unfold DC_KB in *. split; lia.
+ exact Gr.
+ exact JRr.
+ left. split; [reflexivity|]. exists d, q, CBS, REM. split; [| split; [exact Hq | split; [exact DCr | split; [exact JD | exact HPr]]]].
split; [exact CO|]. destruct d as [|s'|?|]; try exact I. cbn [dc_cwA] in CW. destruct CW as (w' & J' & LE'). exists w'. split; [exact J' | clear - LE' W0R; lia].
-
idtac.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HPr) as MIr. change (hl_segs A4L) with asegs in MIr.
pose proof (wmono_refl asegs mr) as WMr. pose proof (munch_refl (@nil (Z * Z)) mr) as MUr.
assert (HPp : HEAPAx Ar (CBS ++ (BS ++ REM ++ LB)) LM FRS Br mr mdr).
{ eapply (heapA_perm A4L HIx); [exact HPr | clear; unfold blk; perm | apply Permutation_refl | apply Permutation_refl]. }
stash K.
reenterA asegs A4L HIx asegs_wx HPr.
step. step. step. if_lit.
step. rewrite ?zxb_zero. step. if_false.
step. step.
evt_done5.
destruct FRq as [[-> ->] | (Hq & sq & JQ)].
+
eapply (PUT _ _ gp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F2 fc2 mr mdr T Ar (BS ++ REM ++ LB) LM FRS Br lo errr None [] 0 1);
[ exact HPp | cbn [put_pre]; split; reflexivity | reflexivity | rewrite unsigned_lit by lia; exact STr | exact LO | rewrite unsigned_lit by lia; unfold put_stk_A; clear - LOSu RD0; lia
| rewrite unsigned_lit by lia; clear - SPA32 SPR LOSu LO ACR RD0; Z.div_mod_to_equations; lia | rewrite unsigned_lit by lia; clear - HT; lia | exact ERRr | reflexivity | reflexivity
| cbn [put_costA]; clear - BBr BBW W0R; unfold DC_KB in *; lia | ].
idtac.
intros ms2 md2 A2 (m2 & rr & B2 & RS2 & VM2 & ST2 & HPR2 & ERR2 & BB2 & BD2 & OUT2).
destruct RS2 as (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & F3 & fc3 & -> & FS3 & FRM3).
destruct OUT2 as [[_ HP2] | (s' & Hs' & _)]; [| discriminate].
rewrite ?(unsigned_lit (bv_unsigned sp + -32)) in ST2, HPR2 by lia. change (hl_segs A4L) with asegs in *.
replace (ret_pc (wz 653140)) with (wz 653140) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in FRr; [| left; cbn; lia].
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in DCr; [| eapply client_range_block; [apply in_or_app; right; apply in_or_app; right; apply fr_ivs_frame; exact HFd | cbn; lia | cbn; lia]].
assert (DSH2 : ro_cells asegs m2 (D / 8 + 2147450880) [C1 (Z_to_bv 8 0)]).
{ destruct DSHr as [Hwf Hb]. split; [exact Hwf|]. eapply (heap_pres_bytes_at A4H); [exact HPR2 | exact Hb |]. cbn [cells_bytes cbytes app length].
eapply client_range_block; [apply in_or_app; right; apply in_or_app; right; apply fr_ivs_shadow; exact HFd | |].
- unfold shad. cbn [hl_sb A4L]. unfold A_SB. clear - HD1. Z.div_mod_to_equations. lia.
- unfold shad. cbn [hl_sb A4L]. unfold A_SB, fr_shadow_len.
assert (HF8 : Fd mod 64 = 0).
{ apply Z.mod_divide; [lia|]. apply (Z.divide_trans _ (fr_size kd)); [| apply Z.mod_divide; [lia | exact HFdal]]. exists (2 ^ kd). unfold fr_size. lia. }
unfold fr_size in HD2. clear - HD1 HD2 HF8 Hkd. assert (KK : kd = 0 \/ kd = 1 \/ kd = 2 \/ kd = 3) by lia. destruct KK as [-> | [-> | [-> | ->]]]; cbn in *; Z.div_mod_to_equations; lia.    }
clear DSHr.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI2. change (hl_segs A4L) with asegs in MI2.
pose proof (wmono_refl asegs m2) as WM2. pose proof (munch_refl [(D, D + 8)] m2) as MU2.
change (hl_segs A4H) with asegs in *. pose proof ERR2 as ERRk. stash ERRk.
reenterA asegs A4L HIx asegs_wx HP2.
step. rewrite ?zxb_zero. step. if_false.
stepz. step.
step. step. step. step. step. step.
release_frame FRr ST2 (bv_unsigned sp).
step.
evt_done5. unstash K. unstash ERRk.
replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 (2^64 - 1)) by (apply bv_eq; vm_compute; reflexivity).
lazymatch goal with |- context [MS _ _ _ _ _ ?mf _] =>
lazymatch goal with MUc : munch _ m2 mf, WMc : wmono asegs m2 mf, MIc : mem_inv asegs mf |- _ =>
rename mf into mF; rename MUc into MUF; rename WMc into WMF; rename MIc into MIF end end.
assert (HPf : HEAPAx A2 (BS ++ REM ++ LB) LM FRS B2 mF md2).
{ eapply (heapA_client_frame A4L HIx); [exact HP2 | eapply (frame_writes_okF A4L HIx _ _ _ _ _ _ _ _ _ HP2 MUF) | exact WMF | exact MIF].
apply Forall_cons; [| apply Forall_nil]. right; right; right. exists Fd, kd. split; [exact HFd|]. left. cbn [fst snd]. clear - HD1 HD2. lia. }
assert (AGf : agree_on asegs BS m2 mF).
{ eapply (agree_of_munch asegs); [exact MUF | exact WMF |]. intros ba bk Hb. cbn [fst snd].
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ ba bk HP2 HFd ltac:(apply in_or_app; left; apply in_or_app; left; exact Hb)) as DJ.
split; [clear - DJ HD1 HD2; lia | exact I]. }
eapply (K _ md2 mF (2^64 - 1) A2 B2).
* split; [apply ret_statew_intro; [eapply fsaved_trans; [exact FS2 | exact FS3] | intros H0; exact (FRM3 (FRM2 H0))] |].
split; [eapply model_vm_only_trans; [exact VMr | exact VM2] |]. split; [assumption |].
split; [| exists errr; eapply (rw_cells_transport asegs _ m2 mF); [exact ERRk | exact MUF | exact WMF | cbn [disjoint_from cells_size csize Nat.add]; unfold A_ERRNO, A_TP; clear - HD1 HD2 HFimg FSP; lia]].
change (QYIF.heap_presxD A4H D (LB ++ (LM ++ fr_ivs A4L FRS)) (bv_unsigned sp) m mF).
eapply (QrIB.Mq0.presxD_trans A4H); [| eapply (QrIB.Mq0.presxD_trans A4H); [| eapply (QrIB.Mq0.presxD_trans A4H)]].
-- apply (QrIB.Mq0.pres_presxD A4H). eapply heap_pres_weaken; [exact HPR1 | lia | intros b Hb].
apply in_app_or in Hb. apply in_or_app. destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; exact Hb | right; exact Hb].
-- eapply (QrIB.Mq0.presxD_weaken A4H); [exact PXr | lia | intros b Hb].
apply in_app_or in Hb. apply in_or_app. destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; exact Hb | right; exact Hb].
-- apply (QrIB.Mq0.pres_presxD A4H). eapply heap_pres_weaken; [exact HPR2 | lia | intros b Hb].
apply in_app_or in Hb. apply in_or_app. destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; apply in_or_app; right; exact Hb | right; exact Hb].
-- eapply (QrIB.Mq0.presxD_of_munch A4H); [exact MUF | exact WMF |]. intros a Ha Hc Hd. cbn [outside fst snd]. clear - Hd. lia.
* unfold jo_chargeA. cbn [bB bD put_costA] in *. try (change (1 =? 1) with true in BB2; cbn in BB2). clear - BBr BDr BB2 BD2 W0R. unfold DC_KB in *. split; lia.
* eapply lh_globA_frame; [eapply lh_globA_client; [exact HPR2 | exact Gr] | exact MUF | exact WMF |].
apply Forall_cons; [cbn [fst snd]; unfold GHASHA, GSEEDA; clear - HD1 HD2 HFimg FSP; lia | apply Forall_nil].
* eapply (QrIB.Mq0.jroot_rep_agree A4H A4F); [exact JRr | | apply incl_refl].
eapply agree_on_trans; [| exact AGf]. eapply (agree_of_heap_pres asegs A4H); [exact HPR2 | reflexivity | intros b Hb; apply in_or_app; left; apply in_or_app; left; exact Hb].
* right. split; [reflexivity|]. exists REM. split; [assumption | exact HPf].
+
eapply (PUT _ _ gp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F2 fc2 mr mdr T Ar (BS ++ REM ++ LB) LM FRS Br lo errr (Some sq) CBS q 1);
[ exact HPp | cbn [put_pre]; split; [exact Hq | split; [lia | exact JQ]] | reflexivity | rewrite unsigned_lit by lia; exact STr | exact LO | rewrite unsigned_lit by lia; unfold put_stk_A; clear - LOSu RD0; lia
| rewrite unsigned_lit by lia; clear - SPA32 SPR LOSu LO ACR RD0; Z.div_mod_to_equations; lia | rewrite unsigned_lit by lia; clear - HT; lia | exact ERRr | reflexivity | reflexivity
| cbn [put_costA]; change (1 =? 1) with true; cbn [bB]; clear - BBr BBW W0R; unfold DC_KB in *; lia | ].
intros ms2 md2 A2 (m2 & rr & B2 & RS2 & VM2 & ST2 & HPR2 & ERR2 & BB2 & BD2 & OUT2).
destruct RS2 as (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & F3 & fc3 & -> & FS3 & FRM3).
destruct OUT2 as [[_ HP2] | (s' & _ & Habs & _)]; [| exfalso; clear - Habs; lia].
rewrite ?(unsigned_lit (bv_unsigned sp + -32)) in ST2, HPR2 by lia. change (hl_segs A4L) with asegs in *.
replace (ret_pc (wz 653140)) with (wz 653140) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in FRr; [| left; cbn; lia].
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in DCr; [| eapply client_range_block; [apply in_or_app; right; apply in_or_app; right; apply fr_ivs_frame; exact HFd | cbn; lia | cbn; lia]].
assert (DSH2 : ro_cells asegs m2 (D / 8 + 2147450880) [C1 (Z_to_bv 8 0)]).
{ destruct DSHr as [Hwf Hb]. split; [exact Hwf|]. eapply (heap_pres_bytes_at A4H); [exact HPR2 | exact Hb |]. cbn [cells_bytes cbytes app length].
eapply client_range_block; [apply in_or_app; right; apply in_or_app; right; apply fr_ivs_shadow; exact HFd | |].
- unfold shad. cbn [hl_sb A4L]. unfold A_SB. clear - HD1. Z.div_mod_to_equations. lia.
- unfold shad. cbn [hl_sb A4L]. unfold A_SB, fr_shadow_len.
assert (HF8 : Fd mod 64 = 0).
{ apply Z.mod_divide; [lia|]. apply (Z.divide_trans _ (fr_size kd)); [| apply Z.mod_divide; [lia | exact HFdal]]. exists (2 ^ kd). unfold fr_size. lia. }
unfold fr_size in HD2. clear - HD1 HD2 HF8 Hkd. assert (KK : kd = 0 \/ kd = 1 \/ kd = 2 \/ kd = 3) by lia. destruct KK as [-> | [-> | [-> | ->]]]; cbn in *; Z.div_mod_to_equations; lia.    }
clear DSHr.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI2. change (hl_segs A4L) with asegs in MI2.
pose proof (wmono_refl asegs m2) as WM2. pose proof (munch_refl [(D, D + 8)] m2) as MU2.
change (hl_segs A4H) with asegs in *. pose proof ERR2 as ERRk. stash ERRk.
reenterA asegs A4L HIx asegs_wx HP2.
step. rewrite ?zxb_zero. step. if_false.
stepz. step.
step. step. step. step. step. step.
release_frame FRr ST2 (bv_unsigned sp).
step.
evt_done5. unstash K. unstash ERRk.
replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 (2^64 - 1)) by (apply bv_eq; vm_compute; reflexivity).
lazymatch goal with |- context [MS _ _ _ _ _ ?mf _] =>
lazymatch goal with MUc : munch _ m2 mf, WMc : wmono asegs m2 mf, MIc : mem_inv asegs mf |- _ =>
rename mf into mF; rename MUc into MUF; rename WMc into WMF; rename MIc into MIF end end.
assert (HPf : HEAPAx A2 (BS ++ REM ++ LB) LM FRS B2 mF md2).
{ eapply (heapA_client_frame A4L HIx); [exact HP2 | eapply (frame_writes_okF A4L HIx _ _ _ _ _ _ _ _ _ HP2 MUF) | exact WMF | exact MIF].
apply Forall_cons; [| apply Forall_nil]. right; right; right. exists Fd, kd. split; [exact HFd|]. left. cbn [fst snd]. clear - HD1 HD2. lia. }
assert (AGf : agree_on asegs BS m2 mF).
{ eapply (agree_of_munch asegs); [exact MUF | exact WMF |]. intros ba bk Hb. cbn [fst snd].
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ ba bk HP2 HFd ltac:(apply in_or_app; left; apply in_or_app; left; exact Hb)) as DJ.
split; [clear - DJ HD1 HD2; lia | exact I]. }
eapply (K _ md2 mF (2^64 - 1) A2 B2).
* split; [apply ret_statew_intro; [eapply fsaved_trans; [exact FS2 | exact FS3] | intros H0; exact (FRM3 (FRM2 H0))] |].
split; [eapply model_vm_only_trans; [exact VMr | exact VM2] |]. split; [assumption |].
split; [| exists errr; eapply (rw_cells_transport asegs _ m2 mF); [exact ERRk | exact MUF | exact WMF | cbn [disjoint_from cells_size csize Nat.add]; unfold A_ERRNO, A_TP; clear - HD1 HD2 HFimg FSP; lia]].
change (QYIF.heap_presxD A4H D (LB ++ (LM ++ fr_ivs A4L FRS)) (bv_unsigned sp) m mF).
eapply (QrIB.Mq0.presxD_trans A4H); [| eapply (QrIB.Mq0.presxD_trans A4H); [| eapply (QrIB.Mq0.presxD_trans A4H)]].
-- apply (QrIB.Mq0.pres_presxD A4H). eapply heap_pres_weaken; [exact HPR1 | lia | intros b Hb].
apply in_app_or in Hb. apply in_or_app. destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; exact Hb | right; exact Hb].
-- eapply (QrIB.Mq0.presxD_weaken A4H); [exact PXr | lia | intros b Hb].
apply in_app_or in Hb. apply in_or_app. destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; exact Hb | right; exact Hb].
-- apply (QrIB.Mq0.pres_presxD A4H). eapply heap_pres_weaken; [exact HPR2 | lia | intros b Hb].
apply in_app_or in Hb. apply in_or_app. destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; apply in_or_app; right; exact Hb | right; exact Hb].
-- eapply (QrIB.Mq0.presxD_of_munch A4H); [exact MUF | exact WMF |]. intros a Ha Hc Hd. cbn [outside fst snd]. clear - Hd. lia.
* unfold jo_chargeA. cbn [bB bD put_costA] in *. try (change (1 =? 1) with true in BB2; cbn in BB2). clear - BBr BDr BB2 BD2 W0R. unfold DC_KB in *. split; lia.
* eapply lh_globA_frame; [eapply lh_globA_client; [exact HPR2 | exact Gr] | exact MUF | exact WMF |].
apply Forall_cons; [cbn [fst snd]; unfold GHASHA, GSEEDA; clear - HD1 HD2 HFimg FSP; lia | apply Forall_nil].
* eapply (QrIB.Mq0.jroot_rep_agree A4H A4F); [exact JRr | | apply incl_refl].
eapply agree_on_trans; [| exact AGf]. eapply (agree_of_heap_pres asegs A4H); [exact HPR2 | reflexivity | intros b Hb; apply in_or_app; left; apply in_or_app; left; exact Hb].
* right. split; [reflexivity|]. exists REM. split; [assumption | exact HPf].
Qed.
End MDcWrap.
End RC__1.
End Mq0.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem Require Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.SepCache.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qfw3_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfw3_c1.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc3B.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc3B. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZDE. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QjDH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDH.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmZZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmZZ. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKQo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKQo. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q8tj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q8tj. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw.Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSL3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSL3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qvbw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qvbw. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYIF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYIF.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnCn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnCn.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QR2u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QR2u.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QrIB.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbFI. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXUB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXUB. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRBl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRBl. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qhd4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qhd4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mqd. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqj. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mqg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mq9. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJZd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJZd.Mq9. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mqh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qw5U.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qw5U.Mq5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mqc. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mqb. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mqe. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqf. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9O6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9O6.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qiiq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qiiq.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSHS. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJlD.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qu4M.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qu4M.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QB6X.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QB6X.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qoif.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qoif.Mq6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSHS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSHS.Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPZI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPZI.Mq4.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Q2qa.Mq0.sf_vocab ::= Q2qa.Mq0.mkr__sf_vocab_5. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Section MDcWrap.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Notation wz := (Z_to_bv 64).
Notation jroot_repA := (jroot_rep A4H A4F).
Hypothesis SHALLOW : shallow_A_stmt HIx.
Hypothesis PUT : put_stmt_A HIx.
Hypothesis DCA : forall r : jroot, r <> JRnull -> DCOPY HIx r.

Theorem deep_copy_A : jo_deep_copy_A_stmt HIx DC_A SH_A (32 + (DC_F + DC_C)) DC_F (fun w => DC_KB * w) (fun w => w).
Proof.
unfold jo_deep_copy_A_stmt. intros until errv. intros PRE SPA32 G JR DC DLOC DU DAL FRN RW WLT BBW BDW FRM A0 A1 A2 K.
destruct PRE as (HP & ST & LO & LOS & SPA & HT & ERR & TP & RA). subst a0 a1 a2 tp.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
unfold A_ERRNO, A_TP in ERR. change (6444320 - 164) with 6444156 in ERR.
assert (RD0 : 0 <= rdepth r) by (destruct r; cbn [rdepth]; try lia; apply sdepth_nonneg).
pose proof LOS as LOSu. unfold dc_stkA, DC_F, DC_C in LOSu.
pose proof alloc_ceiling_range as ACR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. change (hl_segs A4L) with asegs in MI.
destruct (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL]. a4l.
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (6444156, 6444160)] m) as MU.
assert (W0 : 0 <= w) by (destruct r as [|s|?|]; cbn [root_wA] in RW; [exact RW | destruct RW as (w0 & Y & R & J & LE); pose proof (QSHS.Mq1.jtx_ge8 _ _ _ _ J); lia | lia | destruct RW as (L & (len & _ & _ & AB) & WL); lia]).
pose proof (rw_cells_bound asegs m D _ DC) as DRng. cbn [cells_size csize Nat.add] in DRng.
stash K. stash DC. stash DU. stash G.
reenterA asegs A4L HIx asegs_wx HP.
carve_frame 32%nat ST.
bstep. bstepz. bstepz. bstepz. bstepz.
bstep. bstep. bstep. bstep.
idtac.
assert (NULLD : r = JRnull \/ r <> JRnull) by (destruct r; [left; reflexivity | right; discriminate | right; discriminate | right; discriminate]).
destruct NULLD as [Er | NN].
{
subst r. destruct JR as [Ep EB]. rewrite Ep. bstep. if_lit.
bstep. bstep. bstep. bstep.
try (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end).
pose proof (errno_shadowA HIx _ _ _ _ _ _ _ HP) as ESH0. a4l. change ((6444320 - 164) / 8 + 2147450880) with 2148256399 in ESH0.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (ESH : ro_cells asegs mc 2148256399 [C1 (Z_to_bv 8 0)]) by (eapply (ro_cells_transport asegs); [exact ESH0 | exact MU | cbn [disjoint_from cells_size csize Nat.add]; clear - SPR LOSu LO ACR RD0; lia]) end.
clear ESH0.
bstep. bstep. bstep. rewrite ?sxb_zero, ?zxb_zero. bstep. if_false.
bstep. bstepz. bstep.
bstep. bstep. bstep. bstep. bstep.
release_frame FR ST (bv_unsigned sp).
bstep.
evt_done5. unstash K. unstash DC. unstash G.
replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 (2^64 - 1)) by (apply bv_eq; vm_compute; reflexivity).
lazymatch goal with |- context [MS _ _ _ _ _ ?mf _] =>
assert (HPRf : heap_pres A4H ((BS ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m mf);
[ eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MU | exact WM |];
eapply (client_outsideA A4L HIx); [exact HP | intros b Hb; exact Hb | clia | ];
apply Forall_cons; [left; cbn [fst snd]; clear - LO LOSu RD0 SPR; lia|];
apply Forall_cons; [right; right; cbn [fst snd]; intros x Hx; simpl hl_scratch; unfold A_TP; clear - Hx; lia | apply Forall_nil]
| eapply (K _ md mf (2^64 - 1) A B) ] end.
- split; [apply ret_statew_same|]. split; [apply model_vm_only_refl|]. split; [exact ST|]. split; [| eexists; eassumption].
apply (QrIB.Mq0.pres_presxD A4H). eapply heap_pres_weaken; [exact HPRf | lia | intros b Hb; rewrite EB; cbn [app]; exact Hb].
- unfold jo_chargeA. clear - W0 BBW. unfold DC_KB in *. cbn [bB bD]. lia.
- eapply lh_globA_client; [exact HPRf | exact G].
- cbn [jroot_rep]. split; [exact Ep | exact EB].
- right. split; [reflexivity|]. exists []. cbn [app]. split.
+ eapply (heap_pres_rw_cells A4H); [exact HPRf | exact DC |].
destruct DLOC as (Fd & kd & HFd & HD1 & HD2).
eapply client_range_block; [apply in_or_app; right; apply in_or_app; right; apply fr_ivs_frame; exact HFd | cbn; lia | cbn; lia].
+ eapply (heapA_client_frame A4L HIx); [exact HP | eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP MU) | exact WM | assumption].
apply Forall_cons; [left; cbn [fst snd]; clear - LO LOSu RD0 SPR HT; lia|].
apply Forall_cons; [right; right; cbn [fst snd]; intros x Hx; simpl hl_scratch; unfold A_TP; clear - Hx; lia | apply Forall_nil]. }

assert (Hp : p <> 0) by (destruct r as [|s|tojsx|]; [exfalso; exact (NN eq_refl) | exact (proj1 JR) | exact (proj1 JR) | exact (proj1 JR)]).
assert (WX : exists w0, dc_wtA r m BS p w0 /\ 1 <= w0 <= w).
{ destruct r as [|s|tojsx|]; [exfalso; exact (NN eq_refl) | | |]; cbn [root_wA] in RW; cbn [dc_wtA].
- destruct RW as (w0 & Y & R & J & LE). pose proof (QSHS.Mq1.jtx_ge8 _ _ _ _ J). exists w0. split; [exists Y, R; exact J | lia].
- exists w. split; [exact RW | lia].
- destruct RW as (L & SL & WL). exists w. split; [exists L; split; [exact SL | exact WL] |]. lia. }
destruct WX as (w0 & WT0 & W0R).
idtac.

assert (PB : exists np, In (p, np) BS /\ 48 <= np).
{ destruct r as [|s|tojsx|]; [exfalso; exact (NN eq_refl) | | |].
- destruct JR as [_ J]. pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND0.
assert (ND : List.NoDup (map blk_addr BS)) by (pose proof ND0 as X; rewrite !map_app in X; apply NoDup_app_remove_r in X; apply NoDup_app_remove_r in X; exact X).
destruct (jval_hdr asegs A4F s m BS p 1 J ND) as (n & tojs & pb & udel & ud & rest & INp & SZ & N48 & _). exists n. split; [exact INp | exact N48].
- destruct JR as (_ & _ & pb & PBS & bits & EBS & _). exists 48. split; [rewrite EBS; left; reflexivity | lia].
- destruct JR as (_ & pb & PBS & DBS & cap & len & str & EBS & _ & Hcap & _). exists (48 + cap). split; [rewrite EBS; left; reflexivity | lia]. }
destruct PB as (np & INp & Hnp).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ p np HP ltac:(apply in_or_app; left; apply in_or_app; left; exact INp)) as (_ & Hpal & Hplo & Hphi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hphi.
destruct DLOC as (Fd & kd & HFd & HD1 & HD2).
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP HFd) as (Hkd & HFdal & HFd0 & HFdc & HFimg & _). cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in HFimg.
pose proof (fr_size_pos kd ltac:(lia)) as FSP.
unstash DU. pose proof (unpoisoned8_cell asegs _ A_SB D DU DAL) as DSH0. unfold A_SB in DSH0.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (DSH : ro_cells asegs mc (D / 8 + 2147450880) [C1 (Z_to_bv 8 0)]) by (eapply (ro_cells_transport asegs); [exact DSH0 | exact MU | cbn [disjoint_from cells_size csize Nat.add]; clear - SPR LOSu LO ACR RD0 HD1 HD2 HFd0 HFdc FSP; Z.div_mod_to_equations; lia]);
unstash DC; assert (DCc : rw_cells asegs mc D [C8 (wz 0)]) by (eapply (rw_cells_transport asegs); [exact DC | exact MU | exact WM | cbn [disjoint_from cells_size csize Nat.add]; clear - SPR LOSu LO ACR RD0 HD1 HD2 HFd0 HFdc HFimg FSP; lia])
end.
clear DSH0. stash DC.
bstep. if_falsex. bstep. if_falsex.
ub_skip.
asan_chk0.
bstep. bstep. if_lit.
bstep. bstep. unfold SH_A. if_lit.
bstep. bstep. bstep. bstep. bstep. bstep.
idtac.

assert (HP1 : HEAPAx A (BS ++ LB) LM FRS B m1 md).
{ eapply (heapA_client_frame A4L HIx); [exact HP | eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP MU) | exact WM | exact MI].
apply Forall_cons; [left; cbn [fst snd]; clear - LO LOSu RD0 SPR HT; lia|].
apply Forall_cons; [right; right; cbn [fst snd]; intros x Hx; simpl hl_scratch; unfold A_TP; clear - Hx; lia | apply Forall_nil]. }
assert (HPR1 : heap_pres A4H ((BS ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m1).
{ eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | intros b Hb; exact Hb | clia | ].
apply Forall_cons; [left; cbn [fst snd]; clear - LO LOSu RD0 SPR; lia|].
apply Forall_cons; [right; right; cbn [fst snd]; intros x Hx; simpl hl_scratch; unfold A_TP; clear - Hx; lia | apply Forall_nil]. }
unstash G. unstash K.
assert (JR1 : jroot_repA r m1 BS p).
{ eapply (QrIB.Mq0.jroot_rep_agree A4H A4F); [exact JR | | apply incl_refl].
eapply (agree_of_heap_pres asegs A4H); [exact HPR1 | reflexivity | intros b Hb; apply in_or_app; left; apply in_or_app; left; exact Hb]. }
assert (WT1 : dc_wtA r m1 BS p w0).
{ destruct r as [|s|tojsx|]; [exfalso; exact (NN eq_refl) | exact WT0 | exact WT0 |]. cbn [dc_wtA] in WT0 |- *.
destruct WT0 as (L & (len & BY & RL & AB) & WL). exists L. split; [| exact WL]. exists len. split; [| split; [exact RL | exact AB]].
eapply (heap_pres_bytes_at A4H); [exact HPR1 | exact BY |].
eapply client_range_block; [apply in_or_app; left; apply in_or_app; left; exact INp | cbn; lia | rewrite length_le8; cbn; lia]. }
evt_done5.
eapply (DCA r NN) with (m := m1) (md := md) (T := T) (A := A) (LB := LB) (BS := BS) (LM := LM) (FRS := FRS) (B := B) (lo := lo) (p := p) (D := D) (w := w0) (errv := errv);
[ exact HP1 | exact JR1 | exact NN | eapply lh_globA_client; [exact HPR1 | exact G] | exact DCc | exists Fd, kd; split; [exact HFd | split; [exact HD1 | exact HD2]]
| eapply (QsKa.Mqf.unpoisoned_pres_frame HIx); [exact HP | exact HFd | exact HD1 | exact HD2 | exact DU | exact HPR1] | exact DAL
| rewrite ?unsigned_lit by lia; exact ST | exact LO | rewrite ?unsigned_lit by lia; clear - LOSu; unfold dc_stkA, DC_F, DC_C; lia
| rewrite ?unsigned_lit by lia; clear - SPA32 SPR LOSu LO ACR RD0; Z.div_mod_to_equations; lia | rewrite ?unsigned_lit by lia; clear - HT; lia
| exact ERR | reflexivity | rewrite ?unsigned_lit by lia; reflexivity | exact FRM | exact FRN | exact WT1 | clear - W0R WLT; lia
| clear - W0R BBW; unfold DC_KB in *; lia | clear - W0R BDW; lia | reflexivity | reflexivity | reflexivity | ].
idtac.
intros msr mdr mr rvr Ar Br (RSr & VMr & STr & PXr & (errr & ERRr)) Gr JRr (BDr & OUTr).
destruct RSr as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & F2 & fc2 & -> & FS2 & FRM2).
rewrite ?(unsigned_lit (bv_unsigned sp + -32)) in STr, PXr by lia.
change (hl_segs A4L) with asegs in *.
replace (ret_pc (wz 660880)) with (wz 660880) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP HFd) as HFa. cbn [hl_sb A4L] in HFa. unfold A_SB in HFa.
change ((2 ^ 47 - 1) / 8 + 2147450880 + 1) with 17594333495296 in HFa.

assert (FRr : rw_cells asegs mr (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra]).
{ eapply (QrIB.Mq0.presxD_rw_cells A4H); [exact PXr | exact FR | left; cbn; lia | cbn [cells_size csize Nat.add]; clear - HD1 HD2 HFdc LO LOSu RD0; lia]. }
assert (DSHr : ro_cells asegs mr (D / 8 + 2147450880) [C1 (Z_to_bv 8 0)]).
{ destruct DSH as [Hwf Hb]. split; [exact Hwf|].
eapply (QrIB.Mq0.presxD_bytes_at A4H); [exact PXr | exact Hb | |].
- cbn [cells_bytes cbytes app length].
eapply client_rangex_block; [apply in_or_app; right; apply in_or_app; right; apply fr_ivs_shadow; exact HFd | |].
+ unfold shad. cbn [hl_sb A4L]. unfold A_SB. clear - HD1. Z.div_mod_to_equations. lia.
+ unfold shad. cbn [hl_sb A4L]. unfold A_SB, fr_shadow_len.
assert (HF8 : Fd mod 64 = 0).
{ apply Z.mod_divide; [lia|]. apply (Z.divide_trans _ (fr_size kd)); [| apply Z.mod_divide; [lia | exact HFdal]]. exists (2 ^ kd). unfold fr_size. lia. }
unfold fr_size in HD2. clear - HD1 HD2 HF8 Hkd. assert (KK : kd = 0 \/ kd = 1 \/ kd = 2 \/ kd = 3) by lia. destruct KK as [-> | [-> | [-> | ->]]]; cbn in *; Z.div_mod_to_equations; lia.
- cbn [cells_bytes cbytes app length]. clear - HD1 HD2 HFa HFd0 FSP. Z.div_mod_to_equations. lia. }
clear FR DSH. a4l.
destruct OUTr as [(-> & d & q & CBS & REM & CO & CW & Hq & DCr & JD & BBr & HPr) | (-> & q & CBS & REM & DCr & FRq & BBr & HPr)].
-
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HPr) as MIr. change (hl_segs A4L) with asegs in MIr.
pose proof (wmono_refl asegs mr) as WMr. pose proof (munch_refl (@nil (Z * Z)) mr) as MUr.
reenterA asegs A4L HIx asegs_wx HPr.
bstep. bstep. bstep. if_lit.
bstep. bstep. bstep. bstep. bstep.
release_frame FRr STr (bv_unsigned sp).
bstep.
evt_done5.
eapply (K _ mdr mr 0 Ar Br).
+ split; [apply ret_statew_intro; [exact FS2 | exact FRM2] |]. split; [exact VMr|]. split; [exact STr|]. split; [| exists errr; exact ERRr].
change (QYIF.heap_presxD A4H D (LB ++ (LM ++ fr_ivs A4L FRS)) (bv_unsigned sp) m mr).
eapply (QrIB.Mq0.presxD_trans A4H).
* apply (QrIB.Mq0.pres_presxD A4H). eapply heap_pres_weaken; [exact HPR1 | lia | intros b Hb].
apply in_app_or in Hb. apply in_or_app. destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; exact Hb | right; exact Hb].
* eapply (QrIB.Mq0.presxD_weaken A4H); [exact PXr | lia | intros b Hb].
apply in_app_or in Hb. apply in_or_app. destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; exact Hb | right; exact Hb].
+ unfold jo_chargeA. cbn [bB bD]. clear - BBr BDr W0R. unfold DC_KB in *. split; lia.
+ exact Gr.
+ exact JRr.
+ left. split; [reflexivity|]. exists d, q, CBS, REM. split; [| split; [exact Hq | split; [exact DCr | split; [exact JD | exact HPr]]]].
split; [exact CO|]. destruct d as [|s'|?|]; try exact I. cbn [dc_cwA] in CW. destruct CW as (w' & J' & LE'). exists w'. split; [exact J' | clear - LE' W0R; lia].
-
idtac.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HPr) as MIr. change (hl_segs A4L) with asegs in MIr.
pose proof (wmono_refl asegs mr) as WMr. pose proof (munch_refl (@nil (Z * Z)) mr) as MUr.
assert (HPp : HEAPAx Ar (CBS ++ (BS ++ REM ++ LB)) LM FRS Br mr mdr).
{ eapply (heapA_perm A4L HIx); [exact HPr | clear; unfold blk; perm | apply Permutation_refl | apply Permutation_refl]. }
stash K.
reenterA asegs A4L HIx asegs_wx HPr.
bstep. bstep. bstep. if_lit.
bstep. rewrite ?zxb_zero. bstep. if_false.
bstep. bstep.
evt_done5.
destruct FRq as [[-> ->] | (Hq & sq & JQ)].
+
eapply (PUT _ _ gp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F2 fc2 mr mdr T Ar (BS ++ REM ++ LB) LM FRS Br lo errr None [] 0 1);
[ exact HPp | cbn [put_pre]; split; reflexivity | reflexivity | rewrite unsigned_lit by lia; exact STr | exact LO | rewrite unsigned_lit by lia; unfold put_stk_A; clear - LOSu RD0; lia
| rewrite unsigned_lit by lia; clear - SPA32 SPR LOSu LO ACR RD0; Z.div_mod_to_equations; lia | rewrite unsigned_lit by lia; clear - HT; lia | exact ERRr | reflexivity | reflexivity
| cbn [put_costA]; clear - BBr BBW W0R; unfold DC_KB in *; lia | ].
idtac.
intros ms2 md2 A2 (m2 & rr & B2 & RS2 & VM2 & ST2 & HPR2 & ERR2 & BB2 & BD2 & OUT2).
destruct RS2 as (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & F3 & fc3 & -> & FS3 & FRM3).
destruct OUT2 as [[_ HP2] | (s' & Hs' & _)]; [| discriminate].
rewrite ?(unsigned_lit (bv_unsigned sp + -32)) in ST2, HPR2 by lia. change (hl_segs A4L) with asegs in *.
replace (ret_pc (wz 660908)) with (wz 660908) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in FRr; [| left; cbn; lia].
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in DCr; [| eapply client_range_block; [apply in_or_app; right; apply in_or_app; right; apply fr_ivs_frame; exact HFd | cbn; lia | cbn; lia]].
assert (DSH2 : ro_cells asegs m2 (D / 8 + 2147450880) [C1 (Z_to_bv 8 0)]).
{ destruct DSHr as [Hwf Hb]. split; [exact Hwf|]. eapply (heap_pres_bytes_at A4H); [exact HPR2 | exact Hb |]. cbn [cells_bytes cbytes app length].
eapply client_range_block; [apply in_or_app; right; apply in_or_app; right; apply fr_ivs_shadow; exact HFd | |].
- unfold shad. cbn [hl_sb A4L]. unfold A_SB. clear - HD1. Z.div_mod_to_equations. lia.
- unfold shad. cbn [hl_sb A4L]. unfold A_SB, fr_shadow_len.
assert (HF8 : Fd mod 64 = 0).
{ apply Z.mod_divide; [lia|]. apply (Z.divide_trans _ (fr_size kd)); [| apply Z.mod_divide; [lia | exact HFdal]]. exists (2 ^ kd). unfold fr_size. lia. }
unfold fr_size in HD2. clear - HD1 HD2 HF8 Hkd. assert (KK : kd = 0 \/ kd = 1 \/ kd = 2 \/ kd = 3) by lia. destruct KK as [-> | [-> | [-> | ->]]]; cbn in *; Z.div_mod_to_equations; lia.    }
clear DSHr.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI2. change (hl_segs A4L) with asegs in MI2.
pose proof (wmono_refl asegs m2) as WM2. pose proof (munch_refl [(D, D + 8)] m2) as MU2.
change (hl_segs A4H) with asegs in *. pose proof ERR2 as ERRk. stash ERRk.
reenterA asegs A4L HIx asegs_wx HP2.
bstep. rewrite ?zxb_zero. bstep. if_false.
bstepz. bstep.
bstep. bstep. bstep. bstep. bstep. bstep.
release_frame FRr ST2 (bv_unsigned sp).
bstep.
evt_done5. unstash K. unstash ERRk.
replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 (2^64 - 1)) by (apply bv_eq; vm_compute; reflexivity).
lazymatch goal with |- context [MS _ _ _ _ _ ?mf _] =>
lazymatch goal with MUc : munch _ m2 mf, WMc : wmono asegs m2 mf, MIc : mem_inv asegs mf |- _ =>
rename mf into mF; rename MUc into MUF; rename WMc into WMF; rename MIc into MIF end end.
assert (HPf : HEAPAx A2 (BS ++ REM ++ LB) LM FRS B2 mF md2).
{ eapply (heapA_client_frame A4L HIx); [exact HP2 | eapply (frame_writes_okF A4L HIx _ _ _ _ _ _ _ _ _ HP2 MUF) | exact WMF | exact MIF].
apply Forall_cons; [| apply Forall_nil]. right; right; right. exists Fd, kd. split; [exact HFd|]. left. cbn [fst snd]. clear - HD1 HD2. lia. }
assert (AGf : agree_on asegs BS m2 mF).
{ eapply (agree_of_munch asegs); [exact MUF | exact WMF |]. intros ba bk Hb. cbn [fst snd].
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ ba bk HP2 HFd ltac:(apply in_or_app; left; apply in_or_app; left; exact Hb)) as DJ.
split; [clear - DJ HD1 HD2; lia | exact I]. }
eapply (K _ md2 mF (2^64 - 1) A2 B2).
* split; [apply ret_statew_intro; [eapply fsaved_trans; [exact FS2 | exact FS3] | intros H0; exact (FRM3 (FRM2 H0))] |].
split; [eapply model_vm_only_trans; [exact VMr | exact VM2] |]. split; [assumption |].
split; [| exists errr; eapply (rw_cells_transport asegs _ m2 mF); [exact ERRk | exact MUF | exact WMF | cbn [disjoint_from cells_size csize Nat.add]; unfold A_ERRNO, A_TP; clear - HD1 HD2 HFimg FSP; lia]].
change (QYIF.heap_presxD A4H D (LB ++ (LM ++ fr_ivs A4L FRS)) (bv_unsigned sp) m mF).
eapply (QrIB.Mq0.presxD_trans A4H); [| eapply (QrIB.Mq0.presxD_trans A4H); [| eapply (QrIB.Mq0.presxD_trans A4H)]].
-- apply (QrIB.Mq0.pres_presxD A4H). eapply heap_pres_weaken; [exact HPR1 | lia | intros b Hb].
apply in_app_or in Hb. apply in_or_app. destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; exact Hb | right; exact Hb].
-- eapply (QrIB.Mq0.presxD_weaken A4H); [exact PXr | lia | intros b Hb].
apply in_app_or in Hb. apply in_or_app. destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; exact Hb | right; exact Hb].
-- apply (QrIB.Mq0.pres_presxD A4H). eapply heap_pres_weaken; [exact HPR2 | lia | intros b Hb].
apply in_app_or in Hb. apply in_or_app. destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; apply in_or_app; right; exact Hb | right; exact Hb].
-- eapply (QrIB.Mq0.presxD_of_munch A4H); [exact MUF | exact WMF |]. intros a Ha Hc Hd. cbn [outside fst snd]. clear - Hd. lia.
* unfold jo_chargeA. cbn [bB bD put_costA] in *. try (change (1 =? 1) with true in BB2; cbn in BB2). clear - BBr BDr BB2 BD2 W0R. unfold DC_KB in *. split; lia.
* eapply lh_globA_frame; [eapply lh_globA_client; [exact HPR2 | exact Gr] | exact MUF | exact WMF |].
apply Forall_cons; [cbn [fst snd]; unfold GHASHA, GSEEDA; clear - HD1 HD2 HFimg FSP; lia | apply Forall_nil].
* eapply (QrIB.Mq0.jroot_rep_agree A4H A4F); [exact JRr | | apply incl_refl].
eapply agree_on_trans; [| exact AGf]. eapply (agree_of_heap_pres asegs A4H); [exact HPR2 | reflexivity | intros b Hb; apply in_or_app; left; apply in_or_app; left; exact Hb].
* right. split; [reflexivity|]. exists REM. split; [assumption | exact HPf].
+
eapply (PUT _ _ gp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F2 fc2 mr mdr T Ar (BS ++ REM ++ LB) LM FRS Br lo errr (Some sq) CBS q 1);
[ exact HPp | cbn [put_pre]; split; [exact Hq | split; [lia | exact JQ]] | reflexivity | rewrite unsigned_lit by lia; exact STr | exact LO | rewrite unsigned_lit by lia; unfold put_stk_A; clear - LOSu RD0; lia
| rewrite unsigned_lit by lia; clear - SPA32 SPR LOSu LO ACR RD0; Z.div_mod_to_equations; lia | rewrite unsigned_lit by lia; clear - HT; lia | exact ERRr | reflexivity | reflexivity
| cbn [put_costA]; change (1 =? 1) with true; cbn [bB]; clear - BBr BBW W0R; unfold DC_KB in *; lia | ].
intros ms2 md2 A2 (m2 & rr & B2 & RS2 & VM2 & ST2 & HPR2 & ERR2 & BB2 & BD2 & OUT2).
destruct RS2 as (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & F3 & fc3 & -> & FS3 & FRM3).
destruct OUT2 as [[_ HP2] | (s' & _ & Habs & _)]; [| exfalso; clear - Habs; lia].
rewrite ?(unsigned_lit (bv_unsigned sp + -32)) in ST2, HPR2 by lia. change (hl_segs A4L) with asegs in *.
replace (ret_pc (wz 660908)) with (wz 660908) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in FRr; [| left; cbn; lia].
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in DCr; [| eapply client_range_block; [apply in_or_app; right; apply in_or_app; right; apply fr_ivs_frame; exact HFd | cbn; lia | cbn; lia]].
assert (DSH2 : ro_cells asegs m2 (D / 8 + 2147450880) [C1 (Z_to_bv 8 0)]).
{ destruct DSHr as [Hwf Hb]. split; [exact Hwf|]. eapply (heap_pres_bytes_at A4H); [exact HPR2 | exact Hb |]. cbn [cells_bytes cbytes app length].
eapply client_range_block; [apply in_or_app; right; apply in_or_app; right; apply fr_ivs_shadow; exact HFd | |].
- unfold shad. cbn [hl_sb A4L]. unfold A_SB. clear - HD1. Z.div_mod_to_equations. lia.
- unfold shad. cbn [hl_sb A4L]. unfold A_SB, fr_shadow_len.
assert (HF8 : Fd mod 64 = 0).
{ apply Z.mod_divide; [lia|]. apply (Z.divide_trans _ (fr_size kd)); [| apply Z.mod_divide; [lia | exact HFdal]]. exists (2 ^ kd). unfold fr_size. lia. }
unfold fr_size in HD2. clear - HD1 HD2 HF8 Hkd. assert (KK : kd = 0 \/ kd = 1 \/ kd = 2 \/ kd = 3) by lia. destruct KK as [-> | [-> | [-> | ->]]]; cbn in *; Z.div_mod_to_equations; lia.    }
clear DSHr.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI2. change (hl_segs A4L) with asegs in MI2.
pose proof (wmono_refl asegs m2) as WM2. pose proof (munch_refl [(D, D + 8)] m2) as MU2.
change (hl_segs A4H) with asegs in *. pose proof ERR2 as ERRk. stash ERRk.
reenterA asegs A4L HIx asegs_wx HP2.
bstep. rewrite ?zxb_zero. bstep. if_false.
bstepz. bstep.
bstep. bstep. bstep. bstep. bstep. bstep.
release_frame FRr ST2 (bv_unsigned sp).
bstep.
evt_done5. unstash K. unstash ERRk.
replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 (2^64 - 1)) by (apply bv_eq; vm_compute; reflexivity).
lazymatch goal with |- context [MS _ _ _ _ _ ?mf _] =>
lazymatch goal with MUc : munch _ m2 mf, WMc : wmono asegs m2 mf, MIc : mem_inv asegs mf |- _ =>
rename mf into mF; rename MUc into MUF; rename WMc into WMF; rename MIc into MIF end end.
assert (HPf : HEAPAx A2 (BS ++ REM ++ LB) LM FRS B2 mF md2).
{ eapply (heapA_client_frame A4L HIx); [exact HP2 | eapply (frame_writes_okF A4L HIx _ _ _ _ _ _ _ _ _ HP2 MUF) | exact WMF | exact MIF].
apply Forall_cons; [| apply Forall_nil]. right; right; right. exists Fd, kd. split; [exact HFd|]. left. cbn [fst snd]. clear - HD1 HD2. lia. }
assert (AGf : agree_on asegs BS m2 mF).
{ eapply (agree_of_munch asegs); [exact MUF | exact WMF |]. intros ba bk Hb. cbn [fst snd].
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ ba bk HP2 HFd ltac:(apply in_or_app; left; apply in_or_app; left; exact Hb)) as DJ.
split; [clear - DJ HD1 HD2; lia | exact I]. }
eapply (K _ md2 mF (2^64 - 1) A2 B2).
* split; [apply ret_statew_intro; [eapply fsaved_trans; [exact FS2 | exact FS3] | intros H0; exact (FRM3 (FRM2 H0))] |].
split; [eapply model_vm_only_trans; [exact VMr | exact VM2] |]. split; [assumption |].
split; [| exists errr; eapply (rw_cells_transport asegs _ m2 mF); [exact ERRk | exact MUF | exact WMF | cbn [disjoint_from cells_size csize Nat.add]; unfold A_ERRNO, A_TP; clear - HD1 HD2 HFimg FSP; lia]].
change (QYIF.heap_presxD A4H D (LB ++ (LM ++ fr_ivs A4L FRS)) (bv_unsigned sp) m mF).
eapply (QrIB.Mq0.presxD_trans A4H); [| eapply (QrIB.Mq0.presxD_trans A4H); [| eapply (QrIB.Mq0.presxD_trans A4H)]].
-- apply (QrIB.Mq0.pres_presxD A4H). eapply heap_pres_weaken; [exact HPR1 | lia | intros b Hb].
apply in_app_or in Hb. apply in_or_app. destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; exact Hb | right; exact Hb].
-- eapply (QrIB.Mq0.presxD_weaken A4H); [exact PXr | lia | intros b Hb].
apply in_app_or in Hb. apply in_or_app. destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; exact Hb | right; exact Hb].
-- apply (QrIB.Mq0.pres_presxD A4H). eapply heap_pres_weaken; [exact HPR2 | lia | intros b Hb].
apply in_app_or in Hb. apply in_or_app. destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; apply in_or_app; right; exact Hb | right; exact Hb].
-- eapply (QrIB.Mq0.presxD_of_munch A4H); [exact MUF | exact WMF |]. intros a Ha Hc Hd. cbn [outside fst snd]. clear - Hd. lia.
* unfold jo_chargeA. cbn [bB bD put_costA] in *. try (change (1 =? 1) with true in BB2; cbn in BB2). clear - BBr BDr BB2 BD2 W0R. unfold DC_KB in *. split; lia.
* eapply lh_globA_frame; [eapply lh_globA_client; [exact HPR2 | exact Gr] | exact MUF | exact WMF |].
apply Forall_cons; [cbn [fst snd]; unfold GHASHA, GSEEDA; clear - HD1 HD2 HFimg FSP; lia | apply Forall_nil].
* eapply (QrIB.Mq0.jroot_rep_agree A4H A4F); [exact JRr | | apply incl_refl].
eapply agree_on_trans; [| exact AGf]. eapply (agree_of_heap_pres asegs A4H); [exact HPR2 | reflexivity | intros b Hb; apply in_or_app; left; apply in_or_app; left; exact Hb].
* right. split; [reflexivity|]. exists REM. split; [assumption | exact HPf].
Qed.
End MDcWrap.
End RC__1.
