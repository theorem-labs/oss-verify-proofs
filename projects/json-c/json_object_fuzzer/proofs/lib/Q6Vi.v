(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup QEQM Lib.GwApply Qc3B QZDE Lib.SepCache Qfw3_c1 QRjH QHnV QCcH QfLs Q0Ek QjDH QmZZ QC8c Qsw7 QJjn Q6WR QrPc QYIF QvXs Qc8V QBGG QN7A Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup.
Import QEQM.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qc3B QZDE OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.Bytes OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun Qfw3_c1.Mq2.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 QmZZ.
Import QC8c.Mq0.
Import Qsw7 QJjn.
Import Q6WR Q6WR.Mq0 QrPc.
Import QYIF.
Import QvXs.
Import Qc8V.
Import QBGG.
Import QN7A.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section GetIntP.
Variable HIx : heap_iface S4L.
Notation HEAPx := (HEAP S4L HIx).
Hypothesis HT62 : hi_top S4L HIx < 2^62.

Definition gi_c1 := Eval vm_compute in match image_bytes rsegs 0x13480 8 with Some bs => bs | None => [] end.
Definition gi_c2 := Eval vm_compute in match image_bytes rsegs 0x13438 8 with Some bs => bs | None => [] end.
#[using="Type"] Lemma gi_ro : forall m, mem_inv rsegs m -> ro_cells rsegs m 0x13480 [CB 8 gi_c1] /\ ro_cells rsegs m 0x13438 [CB 8 gi_c2].
Proof.
intros m MI. split.
- change 8%nat with (length gi_c1). apply ro_cells_image; [exact MI | vm_compute; reflexivity | lia | ]. change (Z.of_nat (length gi_c1)) with 8%Z. lia.
- change 8%nat with (length gi_c2). apply ro_cells_image; [exact MI | vm_compute; reflexivity | lia | ]. change (Z.of_nat (length gi_c2)) with 8%Z. lia.
Qed.

#[using="HT62"] Theorem get_int_P : jo_get_num_stmt S4L HIx S4F 0x24618 448.
Proof.
unfold jo_get_num_stmt. intros until errv. intros (HP & ST & LO & LOS & SPA & HT & ERR & TP & RA) JO FRM A0 K.
cbn [hl_segs hl_tp S4L] in *.
unfold_consts. word_range sp SPR. subst a0 tp.
change (482928 - 164) with 482764 in ERR.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (wmono_refl rsegs m) as WM.
destruct (gi_ro m MI) as [RO1 RO2].
pose proof (heap_canary S4L HIx _ _ _ _ HP) as (g & CAN1 & CAN2 & _). cbn [hl_got_guard hl_guard hl_segs S4L] in CAN1, CAN2.
carve_frame 32%nat ST.
pose proof (munch_refl [(lo, bv_unsigned sp); (482764, 482768)] m) as MU.

assert (EXIT : forall (m1 : word -> option byte) (md1 : Model) (F1 : bvmap 5 word) (fc1 : bv 32)
(xra xt0 xt1 xt2 xs0 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word) (j8 : list byte) (jw e1 : word),
rw_cells rsegs m1 (bv_unsigned sp + -32) [CB 8 j8; C8 jw; C8 s0; C8 ra] ->
stk rsegs m1 lo (bv_unsigned sp + -32) ->
fsaved F F1 -> (frm0 fc -> frm0 fc1) ->
model_ok md1 -> model_vm_only md md1 -> heap_pres S4L LB (bv_unsigned sp) m m1 ->
rw_cells rsegs m1 482764 [C4 e1] -> mem_inv rsegs m1 ->
jopt rsegs S4F s m1 BS p -> HEAPx A (BS ++ LB) m1 md1 ->
realizes rsegs (mkCfg (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -32)) gp (Z_to_bv 64 482928) xt0 xt1 xt2 xs0 s1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
F1 (Z_to_bv 64 0x246d8) fc1 None m1 (seg_rom rsegs)) md1) T).
{ intros m1 md1 F1 fc1 xra xt0 xt1 xt2 xs0 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 j8 jw e1 FR1 ST1 FS1 FRM1 MOK1 VM1 HPR1 ERR1 MI1 JO1 HP1.
clear ST MI WM MU FR RO1 RO2 CAN1 CAN2.
pose proof (munch_refl [] m1) as MU. pose proof (wmono_refl rsegs m1) as WM.
apply rz_evt; [exact MOK1|].
step. step. step. step.
release_frame FR1 ST1 (bv_unsigned sp).
step. fold_mkR.
lazymatch goal with |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ ?a0v _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
apply evt_RZ_done; eapply (K _ md1 m1 (bv_unsigned a0v)) end.
- split; [| split; [exact VM1 | split; [exact ST1 | split; [exact HPR1 | exists e1; exact ERR1]]]].
rewrite Z_to_bv_bv_unsigned. apply ret_statew_intro; [exact FS1 | exact FRM1].
- exact JO1.
- exact HP1. }

assert (XHPR : forall mX, munch [(lo, bv_unsigned sp); (482764, 482768)] m mX -> wmono rsegs m mX -> heap_pres S4L LB (bv_unsigned sp) m mX).
{ intros mX MUX WMX. eapply (heap_pres_of_munch S4L LB (bv_unsigned sp)); [exact MUX | exact WMX |].
eapply (client_outside S4L HIx); [exact HP | intros b Hb; apply in_or_app; right; exact Hb | clia |].
apply Forall_cons; [cbn [fst snd]; left; clia |]. apply Forall_cons; [cbn [fst snd]; right; right; intros; cbn; lia | apply Forall_nil]. }
assert (XHP : forall mX, munch [(lo, bv_unsigned sp); (482764, 482768)] m mX -> wmono rsegs m mX -> mem_inv rsegs mX -> HEAPx A (BS ++ LB) mX md).
{ intros mX MUX WMX MIX. eapply (heap_frame S4L HIx); [exact HP | | exact WMX | exact MIX].
eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HP MUX). solve_frameW. }
assert (XJO : forall mX, munch [(lo, bv_unsigned sp); (482764, 482768)] m mX -> wmono rsegs m mX -> jopt rsegs S4F s mX BS p).
{ intros mX MUX WMX. destruct s as [sh|]; [| exact JO]. destruct JO as [Hp J]. split; [exact Hp|].
eapply jval_agree; [exact J | | apply incl_refl]. eapply agree_of_munch; [exact MUX | exact WMX |].
intros a k Hin. pose proof (heap_blk S4L HIx _ _ _ _ a k HP ltac:(apply in_or_app; left; exact Hin)) as (Hk & _ & _ & Hhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ a k HP ltac:(apply in_or_app; left; exact Hin)) as Himg. cbn [hl_img_lo hl_img_hi S4L] in Himg.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hhi. cbn. lia. }
apply rz_evt; [exact MOK|].
step. step. step. step. stepz. step. step. step. step. stepz.
step.
destruct s as [sh|].
2:{  destruct JO as [Hp _]. rewrite Hp in *. if_truex. step.
exit_now EXIT XHPR XJO XHP MOK. }
destruct JO as [Hp J].
pose proof (heap_blk_nodup S4L HIx _ _ _ _ HP) as ND.
destruct (jval_hdr rsegs S4F sh m BS p 1 J (nodup_app_l' _ _ ND)) as (n & tojs & pb & udel & ud & rest & INp & SZ & N48 & HDR & CLOSE).
pose proof (heap_blk S4L HIx _ _ _ _ p n HP ltac:(in_sub INp)) as (_ & Hpal & Hplo & Hphi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ p n HP ltac:(in_sub INp)) as Hpimg. cbn [hl_img_lo hl_img_hi S4L] in Hpimg.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hphi.
if_falsex.
unfold jhdr_cells in HDR, SZ. cbn [app hl_segs S4L] in HDR, SZ.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
apply (rw_cells_transport rsegs [(lo, bv_unsigned sp); (482764, 482768)] m mX) in HDR; [| exact MU | exact WM | cbn [disjoint_from]; rewrite SZ; clia] end.
pose proof (jtype_range sh) as JR.
step. rewrite sx32_small by lia. step. step. step.
destruct sh as [|u| |h|kids|kids]; cbn [jtype] in *; unfold JT_BOOLEAN, JT_DOUBLE, JT_INT, JT_STRING, JT_OBJECT, JT_ARRAY in *; if_lit.
-  step. step. if_lit.
destruct J as (pb_ & PBS & REST & EBS & OPB & (b & junk_ & ER & CELLS)). cbn [hl_segs S4L] in CELLS. unfold jhdr_cells in CELLS. cbn [app] in CELLS.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
apply (rw_cells_transport rsegs [(lo, bv_unsigned sp); (482764, 482768)] m mX) in CELLS; [| exact MU | exact WM | cbn [disjoint_from]; cbn; clia] end.
step. step.
exit_now EXIT XHPR XJO XHP MOK.
-  step. step. if_lit. step. step. if_lit.
destruct J as (pb_ & PBS & REST & EBS & OPB & J). cbn [hl_segs S4L] in J.
assert (CELLS : exists tojs' udel' ud' bits, rw_cells rsegs m p (jhdr_cells 2 1 tojs' pb_ udel' ud' ++ [C8 bits])).
{ destruct u; [destruct J as (bits & ud_ & udn & uds & _ & _ & C & _) | destruct J as (bits & _ & _ & C)]; do 4 eexists; exact C. }
clear J. destruct CELLS as (tojs' & udel' & ud' & bits & CELLS). unfold jhdr_cells in CELLS. cbn [app] in CELLS.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
apply (rw_cells_transport rsegs [(lo, bv_unsigned sp); (482764, 482768)] m mX) in CELLS; [| exact MU | exact WM | cbn [disjoint_from]; cbn; clia] end.

step. step. step. step. step.
if_cases Hc1.
+  step. step. step. step.
if_cases Hc2.
*  step. step. step. step. step. exit_now EXIT XHPR XJO XHP MOK.
*  step. step. step. step. step. step. step.
if_cases Hc3.
--  step. step. exit_now EXIT XHPR XJO XHP MOK.
--  step. step. step. step. step. exit_now EXIT XHPR XJO XHP MOK.
+  step. step. step. step. exit_now EXIT XHPR XJO XHP MOK.
-  step. step. if_lit. step. step. if_lit.
destruct J as (pb_ & PBS & REST & EBS & OPB & (cty & v & junk_ & ER & Hcty & CELLS)). cbn [hl_segs S4L] in CELLS. unfold jhdr_cells in CELLS. cbn [app] in CELLS.
pose proof (heap_blk S4L HIx _ _ _ _ p 56 HP ltac:(rewrite EBS, ER; cbn; left; reflexivity)) as (_ & _ & _ & Hphi56 & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hphi56.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
apply (rw_cells_transport rsegs [(lo, bv_unsigned sp); (482764, 482768)] m mX) in CELLS; [| exact MU | exact WM | cbn [disjoint_from]; cbn; clia] end.
step. rewrite sx32_small by lia. step. step.
destruct Hcty as [-> | ->]; if_lit.
+  step. step. step.
if_cases Hc5.
* step. step. step. if_cases Hc6.
-- step. step. exit_now EXIT XHPR XJO XHP MOK.
-- step. step. step. step. step. exit_now EXIT XHPR XJO XHP MOK.
* step. step. step. exit_now EXIT XHPR XJO XHP MOK.
+  step. step. step.
if_cases Hc7.
* step. step. step. step. step. exit_now EXIT XHPR XJO XHP MOK.
* step. step. step. step. if_cases Hc8.
-- step. step. exit_now EXIT XHPR XJO XHP MOK.
-- step. step. step. step. step. exit_now EXIT XHPR XJO XHP MOK.
-
step. step. if_lit.
pose proof J as J0. destruct J as (pb_ & PBS & REST & EBS & OPB & J). cbn [hl_segs S4L] in J, OPB.

assert (TXT : exists (TX TB TBN len : Z) (str0 rest0 : list byte) (lencell : list cell),
In (TB, TBN) BS /\ TB <= TX /\ TX + Z.of_nat (length str0) + 1 <= TB + TBN /\ ~ In (Z_to_bv 8 0) str0 /\
bytes_at rsegs m TX (str0 ++ [Z_to_bv 8 0]) /\
rw_cells rsegs m (p + 40) (C8 (Z_to_bv 64 len) :: lencell) /\ -2^31 < len < 2^31 /\
((0 <= len /\ TX = p + 48) \/ (len < 0 /\ lencell = [C8 (Z_to_bv 64 TX)])) /\
(exists pn, In (p, pn) BS /\ 56 <= pn)).
{ destruct h.
- destruct J as (len & pd & pdn & str & junk2 & ER & Hlen & Hstr & Hpdn & C1 & C2).
destruct (first_nul_split2 str junk2) as (str0 & rest0 & E0 & NIN & L0).
exists pd, pd, pdn, len, str0, rest0, [C8 (Z_to_bv 64 pd)].
split; [rewrite EBS, ER; cbn; right; left; reflexivity|]. split; [lia|]. split; [lia|]. split; [exact NIN|].
split. { apply rw_cells_bytes_at in C2. cbn [cells_bytes cbytes app] in C2. rewrite app_nil_r in C2.
eapply bytes_at_cstr_prefix2; [exact C2 | exact E0]. }
split. { unfold jhdr_cells in C1. cbn [app] in C1. apply rw_cells_app with (cs1 := [_;_;_;_;_;_]) in C1 as [_ C1]. cbn [cells_size csize Nat.add] in C1. change (p + Z.of_nat 40) with (p + 40) in C1. exact C1. }
split; [lia|]. split; [right; split; [lia | reflexivity]|]. exists 56. split; [rewrite EBS, ER; cbn; left; reflexivity | lia].
- destruct J as (len & str & junkS & ER & Hlen & Hstr & C1).
destruct (first_nul_split2 str junkS) as (str0 & rest0 & E0 & NIN & L0).
exists (p + 48), p, (str_objsize len), len, str0, rest0, [CB (Z.to_nat (str_objsize len - 48)) (str ++ [Z_to_bv 8 0] ++ junkS)].
split; [rewrite EBS, ER; cbn; left; reflexivity|]. split; [lia|]. split; [unfold str_objsize; lia|]. split; [exact NIN|].
unfold jhdr_cells in C1. cbn [app] in C1. apply rw_cells_app with (cs1 := [_;_;_;_;_;_]) in C1 as [_ C1]. cbn [cells_size csize Nat.add] in C1. change (p + Z.of_nat 40) with (p + 40) in C1.
split. { pose proof C1 as C2. apply rw_cells_app with (cs1 := [_]) in C2 as [_ C2]. cbn [cells_size csize Nat.add] in C2.
apply rw_cells_bytes_at in C2. cbn [cells_bytes cbytes app] in C2. rewrite app_nil_r in C2.
change (p + 40 + Z.of_nat 8) with (p + 40 + 8) in C2. replace (p + 40 + 8) with (p + 48) in C2 by lia. eapply bytes_at_cstr_prefix2; [exact C2 | exact E0]. }
split; [exact C1|]. split; [lia|]. split; [left; split; [lia | reflexivity]|]. exists (str_objsize len). split; [rewrite EBS, ER; cbn; left; reflexivity | unfold str_objsize; lia]. }
clear J. destruct TXT as (TX & TB & TBN & len & str0 & rest0 & lencell & INT & TLO & THI & NIN & BY & LENC & Hlen & ALT & (pn & INpn & Hpn)).
pose proof (heap_blk S4L HIx _ _ _ _ p pn HP ltac:(apply in_or_app; left; exact INpn)) as (_ & _ & _ & Hphi56 & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hphi56.
pose proof (heap_blk S4L HIx _ _ _ _ TB TBN HP ltac:(apply in_or_app; left; exact INT)) as (_ & Htal & Htlo & Hthi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ TB TBN HP ltac:(apply in_or_app; left; exact INT)) as Htimg. cbn [hl_img_lo hl_img_hi S4L] in Htimg.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hthi.
apply rw_cells_app with (cs1 := [_]) in LENC as [LEN1 LEN2]. cbn [cells_size csize Nat.add] in LEN2. change (p + 40 + Z.of_nat 8) with (p + 40 + 8) in LEN2. replace (p + 40 + 8) with (p + 48) in LEN2 by lia.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
apply (rw_cells_transport rsegs [(lo, bv_unsigned sp); (482764, 482768)] m mX) in LEN1; [| exact MU | exact WM | cbn [disjoint_from]; cbn; clia];
apply (bytes_at_transport rsegs [(lo, bv_unsigned sp); (482764, 482768)] m mX) in BY; [| exact MU | cbn [disjoint_from]; rewrite length_app; cbn [length]; clia] end.

eassert (GOAL : evt rsegs (RZ rsegs md T) _).
2:{ destruct ALT as [[Hl ETX] | [Hl ->]].
- clear LEN2. step. step. step. step. if_truex. rewrite <- ETX. exact GOAL.
- lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
apply (rw_cells_transport rsegs [(lo, bv_unsigned sp); (482764, 482768)] m mX) in LEN2; [| exact MU | exact WM | cbn [disjoint_from]; cbn; clia] end.
step. step. step. step. if_falsex. step. exact GOAL. }

step. step. step.
apply rw_cells_app with (cs1 := [_]) in FR as [FRa FRb]. cbn [cells_size csize Nat.add] in FRb.
apply rw_cells_app with (cs1 := [_]) in FRb as [FRr FRc]. cbn [cells_size csize Nat.add] in FRc.
change (bv_unsigned sp + -32 + Z.of_nat 8) with (bv_unsigned sp + -32 + 8) in FRr, FRc.
change (bv_unsigned sp + -32 + 8 + Z.of_nat 8) with (bv_unsigned sp + -32 + 8 + 8) in FRc.
replace (bv_unsigned sp + -32 + 8 + 8) with (bv_unsigned sp + -16) in FRc by lia.
replace (bv_unsigned sp + -32 + 8) with (bv_unsigned sp + -24) in FRr by lia.
fold_mkR.
pose proof (json_parse_int64_spec strtoll_spec) as PU. unfold parse_i64_stmt in PU.
lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
eapply evt_cut; [ eapply PU with (SP := bv_unsigned sp + -32) (A := TX) (R := bv_unsigned sp + -24) (lo := lo) (str := str0) (g := g)
| unfold parse_i64_post, parse_i64_W; post_call segs mm ] end.
all: clear PU.
{ rewrite unsigned_lit by lia. reflexivity. } { reflexivity. } { reflexivity. }
{ exact BY. } { exact NIN. } { lia. } { lia. }
{ exact FRr. } { lia. } { lia. } { eassumption. } { reflexivity. }
{ unfold GOT_GUARD, GUARD. exact CAN1. } { unfold GUARD. exact CAN2. } { eassumption. }
{ clia. } { lia. } { lia. } { vm_compute; reflexivity. } { assumption. }
cbv beta. change (0x75e70 - 164) with 482764 in *.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
match goal with H : mem_inv rsegs m5 |- _ => rename H into MI5 end.
match goal with H : stk rsegs m5 lo _ |- _ => rename H into ST5 end.
match goal with H : rw_cells rsegs m5 (bv_unsigned sp + -24) [C8 ?v] |- _ => rename H into FRr5 end.
match goal with H : rw_cells rsegs m5 482764 [C4 ?e] |- _ => rename H into ERR5 end.
match goal with H : ?rv = 0 \/ ?rv = 1 |- _ => rename H into HRV end.

lazymatch type of FRr5 with rw_cells _ _ _ [C8 ?vv] =>
lazymatch type of FRa with rw_cells _ _ _ [CB 8 ?jj] =>
assert (FR5 : rw_cells rsegs m5 (bv_unsigned sp + -32) [CB 8 jj; C8 vv; C8 s0; C8 ra]) end end.
{ apply (proj2 (rw_cells_app rsegs m5 _ [CB 8 _] _)). split; [exact FRa|]. cbn [cells_size csize Nat.add].
apply (proj2 (rw_cells_app rsegs m5 _ [C8 _] _)). split.
- change (bv_unsigned sp + -32 + Z.of_nat 8) with (bv_unsigned sp + -32 + 8). replace (bv_unsigned sp + -32 + 8) with (bv_unsigned sp + -24) by lia. exact FRr5.
- cbn [cells_size csize Nat.add]. change (bv_unsigned sp + -32 + Z.of_nat 8 + Z.of_nat 8) with (bv_unsigned sp + -32 + 8 + 8).
replace (bv_unsigned sp + -32 + 8 + 8) with (bv_unsigned sp + -16) by lia. exact FRc. }
clear FRa FRc.
step. destruct HRV as [-> | ->]; if_lit.
+  step. step. step. step. step.
clear FRr5.
if_cases Hc7.
* step. step. step. if_cases Hc8.
-- step. step.
apply evt_RZ_done; eapply EXIT;
[ exact FR5 | exact ST5 | apply fsaved_refl | intros Hf; exact Hf | exact MOK | apply model_vm_only_refl
| apply XHPR; assumption | eassumption | exact MI5 | apply XJO; assumption | apply XHP; assumption ].
-- step. step. step. step. step.
apply evt_RZ_done; eapply EXIT;
[ eassumption | eassumption | apply fsaved_refl | intros Hf; exact Hf | exact MOK | apply model_vm_only_refl
| apply XHPR; assumption | eassumption | assumption | apply XJO; assumption | apply XHP; assumption ].
* step. step. step.
apply evt_RZ_done; eapply EXIT;
[ eassumption | eassumption | apply fsaved_refl | intros Hf; exact Hf | exact MOK | apply model_vm_only_refl
| apply XHPR; assumption | eassumption | assumption | apply XJO; assumption | apply XHP; assumption ].
+  step. clear FRr5.
apply evt_RZ_done; eapply EXIT;
[ exact FR5 | exact ST5 | apply fsaved_refl | intros Hf; exact Hf | exact MOK | apply model_vm_only_refl
| apply XHPR; assumption | exact ERR5 | exact MI5 | apply XJO; assumption | apply XHP; assumption ].
-  step. step. if_lit. step. step. if_lit. exit_now EXIT XHPR XJO XHP MOK.
-  step. step. if_lit. step. step. if_lit. exit_now EXIT XHPR XJO XHP MOK.
Qed.
End GetIntP.

End RC__1.
End Mq0.
From Stdlib Require Permutation.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QIsM QgLo QKQo QEE7 QrIB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup.
Import QEQM.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 QmZZ.
Import QC8c.Mq0 QIsM.
Import QgLo.
Import Qsw7 QJjn QKQo.
Import Q6WR Q6WR.Mq0 QrPc.
Import QYIF.
Import QBGG.
Import QEE7.Mq1 QN7A QrIB.Mq0.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Ltac if_lit :=
lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
let v := eval vm_compute in c in change (if c then a else b) with (if v then a else b); cbv iota
end. Ltac mkr__if_lit_0 := lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
let v := eval vm_compute in c in change (if c then a else b) with (if v then a else b); cbv iota
end.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma jval_sstr_xstr : forall L fn h m BS p rc,
jval (hl_segs L) fn (Sstr h) m BS p rc -> xstr L fn m BS p rc.
Proof.
intros L fn h m BS p rc J. cbn [jval] in J.
destruct J as (pb & PBS & REST & EBS & OPB & J). destruct h.
- destruct J as (len & pd & pdn & str & junk2 & ER & Hlen & Hstr & Hpdn & C1 & C2). subst REST BS.
exists pb, PBS, [(pd, pdn)], 8, len, str. split; [reflexivity|]. split; [exact OPB|]. split; [lia|]. split; [lia|]. split; [lia|].
right. split; [lia|]. exists pd, pdn, (@nil byte), junk2. split; [reflexivity|]. split; [lia|]. split; [| exact C2].
pose proof C1 as C0. destruct C0 as [[_ B0] W0]. pose proof (bytes_at_bound _ _ _ _ B0) as BB.
unfold jhdr_cells in BB |- *. cbn [cells_bytes cbytes app length] in BB. rewrite ?length_app, ?length_le8, ?length_le4 in BB. cbn in BB.
change ([C4 (Z_to_bv 64 JT_STRING); C4 (Z_to_bv 64 rc); C8 (Z_to_bv 64 (fn_str_to_json_string fn)); C8 (Z_to_bv 64 pb); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ++ [C8 (Z_to_bv 64 len); C8 (Z_to_bv 64 pd); CB (Z.to_nat (8 - 8)) []])
with (([C4 (Z_to_bv 64 JT_STRING); C4 (Z_to_bv 64 rc); C8 (Z_to_bv 64 (fn_str_to_json_string fn)); C8 (Z_to_bv 64 pb); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ++ [C8 (Z_to_bv 64 len); C8 (Z_to_bv 64 pd)]) ++ [CB 0 []]).
apply rw_cells_app. split; [exact C1|]. cbn [cells_size csize Nat.add app]. change (Z.of_nat 56) with 56 in *. change (Z.of_nat 0) with 0.
split; [split; [cbn; auto | cbn [cells_bytes cbytes app]; apply bytes_at_nil; lia] | ]. unfold wr_at. cbn [cells_size csize Nat.add]. change (Z.of_nat 0) with 0. match goal with |- ?g => idtac g end. split; [lia|]. split; [lia|]. intros i Hi. lia.
- destruct J as (len & str & junk & ER & Hlen & Hstr & C1). subst REST BS.
exists pb, PBS, (@nil blk), (str_objsize len - 48), len, str. cbn [app].
split; [unfold str_objsize; f_equal; f_equal; lia|]. split; [exact OPB|]. split; [unfold str_objsize; lia|]. split; [lia|]. split; [lia|].
left. split; [lia|]. split; [reflexivity|]. split; [unfold str_objsize; lia|]. exists junk. exact C1.
Qed.

#[using="Type"] Lemma neg_word_negval : forall z, -2^63 <= z < 2^63 -> Z_to_bv 64 (0 - bv_unsigned (Z_to_bv 64 z)) = Z_to_bv 64 (- z).
Proof.
intros z Hz. rewrite Z_to_bv_unsigned. rewrite <- (Z_to_bv_mod64 (0 - _)), <- (Z_to_bv_mod64 (- z)). f_equal.
change (bv_wrap 64 z) with (z mod 2^64).
destruct (Z.lt_ge_cases z 0).
- rewrite <- (Z.mod_unique z (2^64) (-1) (z + 2^64)) by lia.
rewrite <- (Z.mod_unique (0 - (z + 2^64)) (2^64) (-1) (-z)) by lia.
rewrite <- (Z.mod_unique (- z) (2^64) 0 (-z)) by lia. reflexivity.
- rewrite (Z.mod_small z) by lia. f_equal; lia.
Qed.

#[using="Type"] Lemma rw_cells_CB_word : forall segs m A k bs,
rw_cells segs m A [CB k bs] -> (8 <= k)%nat ->
rw_cells segs m A [C8 (le_bytes_to_word (firstn 8 bs)); CB (k - 8) (skipn 8 bs)].
Proof.
intros segs m A k bs H Hk.
assert (L : length bs = k) by (destruct H as [[[Hwf _] _] _]; exact Hwf).
apply (rw_cells_recast segs m A [CB k bs]); [exact H | | |].
- cbn. split; [exact I|]. split; [rewrite length_skipn; lia | exact I].
- cbn [cells_bytes cbytes app]. rewrite le8_lbw8 by (rewrite length_firstn; lia). rewrite ?app_nil_r. apply firstn_skipn.
- cbn. lia.
Qed.

#[using="Type"] Lemma rw_cells_eqA : forall segs m A A' cs, rw_cells segs m A cs -> A = A' -> rw_cells segs m A' cs.
Proof. intros segs m A A' cs H <-. exact H. Qed.
End RC__1.
Ltac hdr_join HD LEN REST :=
apply (proj2 (rw_cells_app _ _ _ [_;_;_;_;_;_] _)); split; [first [exact HD | unfold JT_STRING; exact HD | unfold JT_STRING in HD; exact HD] |];
cbn [cells_size csize Nat.add];
apply (proj2 (rw_cells_app _ _ _ [_] _)); split; [eapply rw_cells_eqA; [exact LEN | lia] |];
cbn [cells_size csize Nat.add]; eapply rw_cells_eqA; [exact REST | lia].
Section RC__2. Context {RC__ : Q6q3.RunConsts}.

Section SetStrPS.
Variable HIx : heap_iface S4L.
Notation HEAPx := (HEAP S4L HIx).
Notation wz := (Z_to_bv 64).

#[using="Type"] Lemma jroot_str_cases : forall r m BS p,
jroot_rep S4L S4F r m BS p -> r <> JRnull -> List.NoDup (map blk_addr BS) ->
p <> 0 /\
( (xstr S4L S4F m BS p 1 /\ set_string_root r = JRstrx)
\/ (set_string_root r = r /\
exists n ty tojs pb udel ud rest,
In (p, n) BS /\ Z.of_nat (cells_size (jhdr_cells ty 1 tojs pb udel ud ++ rest)) = n /\ 48 <= n /\ 0 <= ty <= 6 /\ ty <> JT_STRING /\
rw_cells rsegs m p (jhdr_cells ty 1 tojs pb udel ud ++ rest)) ).
Proof.
intros r m BS p RR NN ND.
assert (Hp : p <> 0) by (destruct r; [exfalso; exact (NN eq_refl) | exact (proj1 RR) ..]). split; [exact Hp|].
destruct r as [|s|tojs|]; [exfalso; exact (NN eq_refl)| | |].
- destruct RR as [_ J].
assert (SPLIT : (exists h, s = Sstr h) \/ jtype s <> JT_STRING).
{ destruct s as [|u| |h|kids|kids]; cbn [jtype]; unfold JT_BOOLEAN, JT_DOUBLE, JT_INT, JT_STRING, JT_OBJECT, JT_ARRAY;
first [left; eexists; reflexivity | right; lia]. }
destruct SPLIT as [[h ->] | NS]; [left; split; [eapply (jval_sstr_xstr S4L); exact J | reflexivity]|].
right. split; [destruct s as [|u| |h|kids|kids]; try reflexivity; cbn [jtype] in NS; exfalso; exact (NS eq_refl)|].
destruct (jval_hdr rsegs S4F s m BS p 1 J ND) as (n & tojs & pb & udel & ud & rest & INp & SZ & N48 & HDR & _).
exists n, (jtype s), tojs, pb, udel, ud, rest. split; [exact INp|]. split; [exact SZ|]. split; [exact N48|].
split; [apply jtype_range|]. split; [exact NS| exact HDR].
- right. split; [reflexivity|]. destruct RR as (_ & Htojs & pb & PBS & bits & EBS & OPB & HDR).
exists 48, JT_DOUBLE, tojs, pb, 0, 0, [C8 bits]. split; [rewrite EBS; left; reflexivity|]. split; [reflexivity|]. split; [lia|].
split; [unfold JT_DOUBLE; lia|]. split; [unfold JT_DOUBLE, JT_STRING; lia|]. exact HDR.
- left. split; [exact (proj2 RR) | reflexivity].
Qed.

Section BodyC.
Variables (ra sp gp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : Model) (LB : list blk) (lo p S : Z) (sb : list byte) (r : jroot) (T : TSet).
Let usp := bv_unsigned sp.
Let n := Z.of_nat (length sb).
Hypothesis SPR : 0 <= bv_unsigned sp < 2^64.
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOS : lo <= bv_unsigned sp - (64 + 8256).
Hypothesis SPA : bv_unsigned sp mod 16 = 0.
Hypothesis HT : bv_unsigned sp <= hi_top S4L HIx.
Hypothesis RA : bv_unsigned ra mod 2 = 0.
Hypothesis SPS : bv_unsigned sp <= S.
Hypothesis SHI : S + n < 2^63.
Hypothesis LSB : n < 2^31 - 2.
Hypothesis K : set_string_post S4L HIx S4F ra sp gp (wz 0x75e70) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB lo p r T.

#[using="sb usp n SPR LOS K"] Lemma sc_exit : forall (m1 : word -> option byte) (md1 : Model)
(xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xt3 xt4 xt5 xt6 : word) (e1 : word),
rw_cells rsegs m1 (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
stk rsegs m1 lo (bv_unsigned sp + -48) -> model_ok md1 -> model_vm_only md0 md1 -> heap_pres S4L LB (bv_unsigned sp) m0 m1 ->
rw_cells rsegs m1 482764 [C4 e1] -> mem_inv rsegs m1 ->
(exists A' BS', jroot_rep S4L S4F (set_string_root r) m1 BS' p /\ HEAPx A' (BS' ++ LB) m1 md1) ->
realizes rsegs (mkCfg (MS (mkR xra (wz (bv_unsigned sp + -48)) gp (wz 0x75e70) xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
F (wz 0x2541c) fc None m1 (seg_rom rsegs)) md1) T.
Proof.
intros until e1. intros FR1 ST1 MOK1 VM1 HPR1 ERR1 MI1 ROOT.
pose proof (munch_refl [] m1) as MU. pose proof (wmono_refl rsegs m1) as WM. unfold_consts.
apply rz_evt; [exact MOK1|].
do 6 step.
release_frame FR1 ST1 (bv_unsigned sp).
step. step.
apply evt_RZ_done. rewrite <- (Z_to_bv_bv_unsigned xa0). eapply (K _ md1 m1 (bv_unsigned xa0)).
- split; [| split; [exact VM1 | split; [exact ST1 | split; [exact HPR1 | exists e1; exact ERR1]]]].
rewrite Z_to_bv_bv_unsigned. apply ret_statew_intro; [apply fsaved_refl | intros Hf; exact Hf].
- exact ROOT.
Qed.

#[using="usp SPR LO LOS SPS SHI LSB K"] Lemma sc_tail : forall (m1 : word -> option byte) (md1 : Model)
(xra xt0 xt1 xt2 xa0 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xt3 xt4 xt5 xt6 : word) (e1 : word)
(A1 : AS S4L HIx) (BS1 : list blk) (D : Z) (k : nat) (junk : list byte) (newlen lenw : word) (bD szD pn : Z),
rw_cells rsegs m1 (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
stk rsegs m1 lo (bv_unsigned sp + -48) -> model_vm_only md0 md1 -> heap_pres S4L LB (bv_unsigned sp) m0 m1 ->
rw_cells rsegs m1 482764 [C4 e1] ->
HEAPx A1 (BS1 ++ LB) m1 md1 ->
bytes_at rsegs m1 S sb ->
rw_cells rsegs m1 D [CB k junk] -> n + 1 <= Z.of_nat k -> In (bD, szD) BS1 -> bD <= D -> D + Z.of_nat k <= bD + szD ->
rw_cells rsegs m1 (p + 40) [C8 lenw] -> In (p, pn) BS1 -> 48 <= pn ->
(p + 48 <= D \/ D + Z.of_nat k <= p) ->
set_string_root r = JRstrx ->
(forall m2, munch [(D, D + Z.of_nat k); (p + 40, p + 48)] m1 m2 -> wmono rsegs m1 m2 -> mem_inv rsegs m2 ->
rw_cells rsegs m2 D [CB k (sb ++ [Z_to_bv 8 0] ++ skipn (Z.to_nat (n + 1)) junk)] ->
rw_cells rsegs m2 (p + 40) [C8 newlen] ->
exists BS', Permutation BS1 BS' /\ jroot_rep S4L S4F JRstrx m2 BS' p) ->
realizes rsegs (mkCfg (MS (mkR xra (wz (bv_unsigned sp + -48)) gp (wz 0x75e70) xt0 xt1 xt2 (wz p) (wz D) xa0 (wz S) (wz n) xa3 xa4 xa5 xa6 xa7
xs2 xs3 newlen s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
F (wz 0x25400) fc None m1 (seg_rom rsegs)) md1) T.
Proof.
intros until pn. intros FR1 ST1 VM1 HPR1 ERR1 HP1 SB1 DST Hk INd HbD HDk LEN INp Hpn SEP SR FIN.
unfold_consts.
pose proof (heap_model_ok _ _ _ _ _ _ HP1) as MOK1.
pose proof (heap_mem_inv _ _ _ _ _ _ HP1) as MI. cbn [hl_segs S4L] in MI.
pose proof (heap_blk S4L HIx _ _ _ _ bD szD HP1 ltac:(apply in_or_app; left; exact INd)) as (_ & _ & HdLO & HdHI & _).
pose proof (heap_blk S4L HIx _ _ _ _ p pn HP1 ltac:(apply in_or_app; left; exact INp)) as (_ & _ & HpLO & HpHI & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in HdHI, HpHI.
pose proof (heap_blk_img S4L HIx _ _ _ _ bD szD HP1 ltac:(apply in_or_app; left; exact INd)) as HdIMG. cbn [hl_img_lo hl_img_hi S4L] in HdIMG.
pose proof (heap_blk_img S4L HIx _ _ _ _ p pn HP1 ltac:(apply in_or_app; left; exact INp)) as HpIMG. cbn [hl_img_lo hl_img_hi S4L] in HpIMG.
pose proof (heap_blk_nodup S4L HIx _ _ _ _ HP1) as ND.
assert (LJ : length junk = k) by (destruct DST as [[[Hwf _] _] _]; exact Hwf).

destruct (rw_cells_CB_cut rsegs _ _ _ _ (Z.to_nat n) DST ltac:(lia)) as [DATA REST1].
destruct (rw_cells_CB_cut rsegs _ _ _ _ 1%nat REST1 ltac:(lia)) as [NUL REST2]. clear DST REST1.
replace (D + Z.of_nat (Z.to_nat n)) with (D + n) in NUL, REST2 by lia.
replace (D + n + Z.of_nat 1) with (D + n + 1) in REST2 by lia.
pose proof (munch_refl [(D, D + Z.of_nat k); (p + 40, p + 48)] m1) as MU. pose proof (wmono_refl rsegs m1) as WM.
apply rz_evt; [exact MOK1|].
step. step. step.
call memcpy_specZ; [lia | lia | lia | lia | lia | exact SB1 | subst n; rewrite Nat2Z.id; reflexivity | exact DATA | lia | exact MI |].
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => rename mX into m2 end.
match goal with H : rw_cells rsegs m2 D [CB _ sb] |- _ => rename H into DATA2 end.
assert (Hn0 : 0 <= n) by (subst n; lia).
step.
set (ez := D + n) in *. stepz. subst ez.
stepz.
step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => rename mX into m3 end.
match goal with H : mem_inv rsegs m3 |- _ => rename H into MI3 | _ => idtac end.

assert (HP3 : HEAPx A1 (BS1 ++ LB) m3 md1).
{ eapply (heap_frame S4L HIx); [exact HP1 | | exact WM | assumption].
eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HP1 MU).
apply Forall_cons; [cbn [fst snd]; right; left; exists bD, szD; split; [apply in_or_app; left; exact INd | lia]|].
apply Forall_cons; [cbn [fst snd]; right; left; exists p, pn; split; [apply in_or_app; left; exact INp | lia]| apply Forall_nil]. }
assert (HPR3 : heap_pres S4L LB (bv_unsigned sp) m0 m3).
{ eapply heap_pres_trans; [exact HPR1|].
eapply (heap_pres_of_munch S4L LB (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outside S4L HIx); [exact HP1 | intros b Hb; apply in_or_app; right; exact Hb | clia |].
apply Forall_cons; [cbn [fst snd]; right; left; exists bD, szD; split; [apply in_or_app; left; exact INd | split; [| lia]];
eapply (nodup_prefix_suffix BS1 LB); [exact ND | exact INd] |].
apply Forall_cons; [cbn [fst snd]; right; left; exists p, pn; split; [apply in_or_app; left; exact INp | split; [| lia]];
eapply (nodup_prefix_suffix BS1 LB); [exact ND | exact INp] | apply Forall_nil]. }
destruct (FIN m3 MU WM ltac:(assumption)) as (BS' & PERM & ROOT').
{
lazymatch goal with H : rw_cells rsegs m3 (D + n) ?c |- _ =>
apply (rw_cells_recast rsegs _ _ _ [CB 1 [Z_to_bv 8 0]]) in H; [| cbn; auto | reflexivity | reflexivity] end.
lazymatch goal with H1 : rw_cells rsegs m3 D [CB _ sb], H2 : rw_cells rsegs m3 (D + n) [CB 1 _], H3 : rw_cells rsegs m3 (D + n + 1) _ |- _ =>
pose proof (rw_cells_CB_join rsegs _ _ _ _ _ _ H1 ltac:(replace (D + Z.of_nat (Z.to_nat n)) with (D + n) by lia; exact H2)) as J1;
pose proof (rw_cells_CB_join rsegs _ _ _ _ _ _ J1 ltac:(replace (D + Z.of_nat (Z.to_nat n + 1)) with (D + n + 1) by lia; exact H3)) as J2 end.
rewrite <- app_assoc in J2. replace (Z.to_nat n + 1 + (k - Z.to_nat n - 1))%nat with k in J2 by lia.
rewrite skipn_skipn in J2. replace (1 + Z.to_nat n)%nat with (Z.to_nat (n + 1)) in J2 by lia. exact J2. }
{ assumption. }
apply evt_RZ_done. eapply sc_exit; [eassumption | eassumption | exact MOK1 | exact VM1 | exact HPR3 | eassumption | assumption |].
exists A1, BS'. rewrite SR. split; [exact ROOT'|]. eapply (heap_perm S4L HIx); [exact HP3|]. apply Permutation_app_tail. exact PERM.
Qed.

#[using="usp SPR LO LOS SPS SHI LSB K"] Lemma sc_grow2 : forall (m1 : word -> option byte) (md1 : Model)
(xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word) (e1 : word)
(A1 : AS S4L HIx) (PBS : list blk) (q cap pb : Z) (junk0 junk : list byte) (lenw x : word),
rw_cells rsegs m1 (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
stk rsegs m1 lo (bv_unsigned sp + -48) -> model_vm_only md0 md1 -> heap_pres S4L LB (bv_unsigned sp) m0 m1 ->
rw_cells rsegs m1 482764 [C4 e1] ->
HEAPx A1 (((q, n + 1) :: (p, 48 + cap) :: PBS) ++ LB) m1 md1 ->
bytes_at rsegs m1 S sb ->
rw_cells rsegs m1 q [CB (Z.to_nat (n + 1)) junk0] ->
rw_cells rsegs m1 p (jhdr_cells JT_STRING 1 (fn_str_to_json_string S4F) pb 0 0 ++ [C8 lenw; C8 x; CB (Z.to_nat (cap - 8)) junk]) ->
opt_pbuf rsegs m1 PBS pb -> 8 <= cap -> 1 <= n ->
set_string_root r = JRstrx ->
realizes rsegs (mkCfg (MS (mkR xra (wz (bv_unsigned sp + -48)) gp (wz 0x75e70) xt0 xt1 xt2 (wz p) (wz q) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
(wz (p + 48)) (wz S) (wz n) s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
F (wz 0x253c4) fc None m1 (seg_rom rsegs)) md1) T.
Proof.
intros until x. intros FR1 ST1 VM1 HPR1 ERR1 HP1 SB1 QB HDR OPB Hcap Hn SR.
unfold_consts.
pose proof (heap_model_ok _ _ _ _ _ _ HP1) as MOK1.
pose proof (heap_mem_inv _ _ _ _ _ _ HP1) as MI. cbn [hl_segs S4L] in MI.
pose proof (heap_blk S4L HIx _ _ _ _ q (n + 1) HP1 ltac:(left; reflexivity)) as (_ & _ & HqLO & HqHI & _).
pose proof (heap_blk S4L HIx _ _ _ _ p (48 + cap) HP1 ltac:(right; left; reflexivity)) as (_ & _ & HpLO & HpHI & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in HqHI, HpHI.
pose proof (heap_blk_img S4L HIx _ _ _ _ q (n + 1) HP1 ltac:(left; reflexivity)) as HqIMG. cbn [hl_img_lo hl_img_hi S4L] in HqIMG.
pose proof (heap_blk_img S4L HIx _ _ _ _ p (48 + cap) HP1 ltac:(right; left; reflexivity)) as HpIMG. cbn [hl_img_lo hl_img_hi S4L] in HpIMG.
pose proof (blk_ne_01 S4L HIx _ _ _ _ _ _ _ _ HP1) as Hqp.
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ q (n + 1) p (48 + cap) HP1 ltac:(left; reflexivity) ltac:(right; left; reflexivity) Hqp) as DISJ.
unfold jhdr_cells in HDR. cbn [app hl_segs S4L] in HDR.
pose proof (munch_refl [(p + 48, p + 56)] m1) as MU. pose proof (wmono_refl rsegs m1) as WM.
apply rz_evt; [exact MOK1|].
stepz.
step. step. step. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => rename mX into m2 end.
match goal with H : mem_inv rsegs m2 |- _ => rename H into MI2 | _ => idtac end.
assert (HP2 : HEAPx A1 (((q, n + 1) :: (p, 48 + cap) :: PBS) ++ LB) m2 md1).
{ eapply (heap_frame S4L HIx); [exact HP1 | | exact WM | assumption].
eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HP1 MU).
apply Forall_cons; [cbn [fst snd]; right; left; exists p, (48 + cap); split; [right; left; reflexivity | lia]| apply Forall_nil]. }
assert (HPR2 : heap_pres S4L LB (bv_unsigned sp) m0 m2).
{ eapply heap_pres_trans; [exact HPR1|].
eapply (heap_pres_of_munch S4L LB (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outside S4L HIx); [exact HP1 | intros b Hb; apply in_or_app; right; exact Hb | clia |].
apply Forall_cons; [cbn [fst snd]; right; left; exists p, (48 + cap); split; [right; left; reflexivity | split; [| lia]];
eapply (nodup_prefix_suffix ((q, n + 1) :: (p, 48 + cap) :: PBS) LB p (48 + cap));
[exact (heap_blk_nodup S4L HIx _ _ _ _ HP1) | right; left; reflexivity]
| apply Forall_nil]. }

lazymatch goal with H : rw_cells rsegs m2 p ?cs |- _ => rename H into HDR2 end.
apply rw_cells_app with (cs1 := [_;_;_;_;_;_]) in HDR2 as [HD2 LEN2]. cbn [cells_size csize Nat.add] in LEN2. change (p + Z.of_nat 40) with (p + 40) in LEN2.
apply rw_cells_app with (cs1 := [_]) in LEN2 as [LEN2 PD2]. cbn [cells_size csize Nat.add] in PD2. change (p + 40 + Z.of_nat 8) with (p + 40 + 8) in PD2.
replace (p + 40 + 8) with (p + 48) in PD2 by lia.
apply evt_RZ_done.
eapply (sc_tail m2 md1) with (A1 := A1) (BS1 := (q, n + 1) :: (p, 48 + cap) :: PBS) (k := Z.to_nat (n + 1)) (bD := q) (szD := n + 1) (pn := 48 + cap);
[ eassumption | eassumption | exact VM1 | exact HPR2 | eassumption | exact HP2 | eassumption | eassumption | lia | left; reflexivity | lia | lia
| exact LEN2 | right; left; reflexivity | lia | lia | exact SR |].
intros m3 MU3 WM3 MI3 DST3 LEN3.
exists ((p, 48 + cap) :: [(q, n + 1)] ++ PBS). split; [cbn [app]; apply perm_swap|].
split; [lia|].
exists pb, PBS, [(q, n + 1)], cap, (- n), sb. split; [reflexivity|]. split.
{ eapply opt_pbuf_agree; [exact OPB | | apply incl_refl].
eapply agree_on_trans.
- eapply agree_of_munch; [exact MU | exact WM |]. intros a k' Hin.
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ p (48 + cap) a k' HP1 ltac:(right; left; reflexivity) ltac:(right; right; apply in_or_app; left; exact Hin)) as D1.
pose proof (heap_blk S4L HIx _ _ _ _ a k' HP1 ltac:(right; right; apply in_or_app; left; exact Hin)) as (Hk' & _).
assert (p <> a). { intros <-. exact (nodup_prefix_suffix [(q, n + 1); (p, 48 + cap)] (PBS ++ LB) p (48 + cap) k' (heap_blk_nodup S4L HIx _ _ _ _ HP1) ltac:(right; left; reflexivity) ltac:(apply in_or_app; left; exact Hin)). }
cbn. split; [lia | exact I].
- eapply agree_of_munch; [exact MU3 | exact WM3 |]. intros a k' Hin.
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ p (48 + cap) a k' HP1 ltac:(right; left; reflexivity) ltac:(right; right; apply in_or_app; left; exact Hin)) as D1.
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ q (n + 1) a k' HP1 ltac:(left; reflexivity) ltac:(right; right; apply in_or_app; left; exact Hin)) as D2.
pose proof (heap_blk S4L HIx _ _ _ _ a k' HP1 ltac:(right; right; apply in_or_app; left; exact Hin)) as (Hk' & _).
pose proof (heap_blk_nodup S4L HIx _ _ _ _ HP1) as ND1.
assert (p <> a). { intros <-. exact (nodup_prefix_suffix [(q, n + 1); (p, 48 + cap)] (PBS ++ LB) p (48 + cap) k' ND1 ltac:(right; left; reflexivity) ltac:(apply in_or_app; left; exact Hin)). }
assert (q <> a). { intros <-. exact (nodup_prefix_suffix [(q, n + 1); (p, 48 + cap)] (PBS ++ LB) q (n + 1) k' ND1 ltac:(left; reflexivity) ltac:(apply in_or_app; left; exact Hin)). }
cbn. split; [lia|]. split; [lia | exact I]. }
split; [lia|]. split; [lia|]. split; [lia|].
right. split; [lia|]. exists q, (n + 1), junk, (skipn (Z.to_nat (n + 1)) junk0). split; [reflexivity|]. split; [lia|]. split.
- unfold jhdr_cells. cbn [app].
lazymatch type of MU3 with munch ?W _ _ =>
apply (rw_cells_transport rsegs W m2 m3) in HD2; [| exact MU3 | exact WM3 | cbn [disjoint_from]; cbn; lia];
apply (rw_cells_transport rsegs W m2 m3) in PD2; [| exact MU3 | exact WM3 | cbn [disjoint_from]; cbn [cells_size csize Nat.add]; lia] end.
rewrite unsigned_lit in LEN3 by lia. replace (0 - n) with (- n) in LEN3 by lia.
hdr_join HD2 LEN3 PD2.
- exact DST3.
Qed.

#[using="usp SPR LO LOS SPA HT SPS SHI LSB K"] Lemma sc_grow : forall (m1 : word -> option byte) (md1 : Model)
(xra xt0 xt1 xt2 xs1 xa0 xa3 xa4 xa5 xa6 xa7 xs3 xs4 xt3 xt4 xt5 xt6 : word) (e1 : word)
(A1 : AS S4L HIx) (PBS DBS : list blk) (cap pb len0 : Z) (junk : list byte) (x : word),
rw_cells rsegs m1 (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
stk rsegs m1 lo (bv_unsigned sp + -48) -> model_vm_only md0 md1 -> heap_pres S4L LB (bv_unsigned sp) m0 m1 ->
rw_cells rsegs m1 482764 [C4 e1] ->
HEAPx A1 (((p, 48 + cap) :: DBS ++ PBS) ++ LB) m1 md1 ->
bytes_at rsegs m1 S sb ->
rw_cells rsegs m1 p (jhdr_cells JT_STRING 1 (fn_str_to_json_string S4F) pb 0 0 ++ [C8 (wz len0); C8 x; CB (Z.to_nat (cap - 8)) junk]) ->
opt_pbuf rsegs m1 PBS pb -> 8 <= cap -> 1 <= n ->
xstr S4L S4F m1 ((p, 48 + cap) :: DBS ++ PBS) p 1 ->
-2^63 <= len0 < 2^63 ->
((0 <= len0 /\ DBS = []) \/ (len0 < 0 /\ exists pd pdn, DBS = [(pd, pdn)] /\ x = wz pd)) ->
set_string_root r = JRstrx ->
realizes rsegs (mkCfg (MS (mkR xra (wz (bv_unsigned sp + -48)) gp (wz 0x75e70) xt0 xt1 xt2 (wz p) xs1 xa0 (wz S) (wz n) xa3 xa4 xa5 xa6 xa7
(wz (p + 48)) xs3 xs4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
F (wz 0x2539c) fc None m1 (seg_rom rsegs)) md1) T.
Proof.
intros until x. intros FR1 ST1 VM1 HPR1 ERR1 HP1 SB1 HDR OPB Hcap Hn ROOT LEN0R FLAG SR.
unfold_consts.
pose proof (heap_model_ok _ _ _ _ _ _ HP1) as MOK1.
pose proof (heap_mem_inv _ _ _ _ _ _ HP1) as MI. cbn [hl_segs S4L] in MI.
pose proof (heap_blk S4L HIx _ _ _ _ p (48 + cap) HP1 ltac:(left; reflexivity)) as (_ & _ & HpLO & HpHI & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in HpHI.
pose proof (bytes_at_bound _ _ _ _ SB1) as SBB. fold n in SBB.
unfold jhdr_cells in HDR. cbn [app hl_segs S4L] in HDR.
pose proof (munch_refl [] m1) as MU. pose proof (wmono_refl rsegs m1) as WM.
apply rz_evt; [exact MOK1|].
step. step. step. step.

alloc_call (hi_malloc S4L HIx) S4L HIx HP1 MU WM MI.
intros ms2 m2 md2 A2 q e2 RS VM2 ST2 HPR2 ERR2 OUT2. open_ret RS. cbn [hl_segs hl_tp S4L] in *.
rewrite ?(unsigned_lit (bv_unsigned sp + -48)) in ST2 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -48)) in HPR2 by lia.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in FR1; [| left; cbn; lia]. cbn [hl_segs S4L] in FR1.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in HDR; [| eapply client_range_block; [left; reflexivity | lia | cbn; lia]]. cbn [hl_segs S4L] in HDR.
apply (heap_pres_bytes_at S4L _ _ _ _ _ _ HPR2) in SB1; [| left; cbn; lia]. cbn [hl_segs S4L] in SB1.
assert (AG2 : agree_on rsegs ((p, 48 + cap) :: DBS ++ PBS) m1 m2).
{ eapply (agree_of_heap_pres rsegs S4L); [exact HPR2 | reflexivity | intros b Hb; apply in_or_app; left; exact Hb]. }
assert (HPR02 : heap_pres S4L LB (bv_unsigned sp) m0 m2).
{ eapply heap_pres_trans; [exact HPR1|]. eapply heap_pres_weaken; [exact HPR2 | lia | intros b Hb; apply in_or_app; right; exact Hb]. }
pose proof (model_vm_only_trans _ _ _ VM1 VM2) as VM02.
clear MU WM MI.
destruct OUT2 as [(-> & _ & HP2) | (Hq & [junk0 QB] & HP2)].
-
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2.
pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI. cbn [hl_segs S4L] in MI.
pose proof (munch_refl [] m2) as MU. pose proof (wmono_refl rsegs m2) as WM.
reenter MOK2. step. if_lit.
apply evt_RZ_done. eapply sc_exit; [exact FR1 | exact ST2 | exact MOK2 | exact VM02 | exact HPR02 | exact ERR2 | exact MI |].
exists A2, ((p, 48 + cap) :: DBS ++ PBS). rewrite SR. split; [| exact HP2]. split; [lia|].
eapply (xstr_agree S4L); [exact ROOT | exact AG2 | apply incl_refl].
-
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2.
pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI. cbn [hl_segs S4L] in MI.
pose proof (heap_blk S4L HIx _ _ _ _ q (n + 1) HP2 ltac:(left; reflexivity)) as (_ & _ & HqLO & HqHI & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in HqHI.
pose proof (heap_blk_nodup S4L HIx _ _ _ _ HP2) as ND2.
pose proof (munch_refl [] m2) as MU. pose proof (wmono_refl rsegs m2) as WM.
reenter MOK2. step. if_falsex. step. step. step.
destruct FLAG as [(Hl0 & ->) | (Hl0 & pd & pdn & -> & ->)].
+
if_truex. cbn [app] in HP2, OPB, AG2.
apply evt_RZ_done. eapply sc_grow2; [exact FR1 | exact ST2 | exact VM02 | exact HPR02 | exact ERR2 | exact HP2 | exact SB1 | exact QB
| unfold jhdr_cells; cbn [app]; exact HDR | | exact Hcap | exact Hn | exact SR].
eapply opt_pbuf_agree; [exact OPB | exact AG2 | intros b Hb; right; exact Hb].
+
if_falsex. cbn [app] in HP2, AG2, ND2.
assert (Hqpd : q <> pd). { intros Eq. cbn in ND2. inversion ND2 as [|x_ l_ Hni Hnd]; subst x_ l_. apply Hni. cbn. right; left. symmetry; exact Eq. }
assert (Hppd : p <> pd). { intros Epd. cbn in ND2. inversion ND2 as [|x_ l_ Hni Hnd]; subst x_ l_. inversion Hnd as [|x2 l2 Hni2 Hnd2]; subst x2 l2. apply Hni2. cbn. left. symmetry; exact Epd. }
step. step.
alloc_call (hi_free S4L HIx) S4L HIx HP2 MU WM MI.
{ right. exists pdn. cbn. right; right; left; reflexivity. }
intros ms3 m3 md3 A3 r3 RS3 VM3 ST3 HPR3 ERR3 HP3. open_ret RS3. cbn [hl_segs hl_tp S4L] in *.
rewrite ?(unsigned_lit (bv_unsigned sp + -48)) in ST3 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -48)) in HPR3 by lia.
rewrite (lb_remove_other pd) in HPR3, HP3 by (cbn; lia). rewrite (lb_remove_other pd) in HPR3, HP3 by (cbn; lia). rewrite lb_remove_head in HPR3, HP3.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR3) in FR1; [| left; cbn; lia]. cbn [hl_segs S4L] in FR1.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR3) in HDR; [| eapply client_range_block; [right; left; reflexivity | lia | cbn; lia]]. cbn [hl_segs S4L] in HDR.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR3) in QB; [| eapply client_range_block; [left; reflexivity | lia | cbn; lia]]. cbn [hl_segs S4L] in QB.
apply (heap_pres_bytes_at S4L _ _ _ _ _ _ HPR3) in SB1; [| left; cbn; lia]. cbn [hl_segs S4L] in SB1.
pose proof (heap_model_ok _ _ _ _ _ _ HP3) as MOK3.
reenter MOK3.
apply evt_RZ_done. eapply sc_grow2; [exact FR1 | exact ST3 | exact (model_vm_only_trans _ _ _ VM02 VM3) | | exact ERR3 | exact HP3 | exact SB1 | exact QB
| unfold jhdr_cells; cbn [app]; exact HDR | | exact Hcap | exact Hn | exact SR].
* eapply heap_pres_trans; [exact HPR02|]. eapply heap_pres_weaken; [exact HPR3 | lia | intros b Hb; right; right; apply in_or_app; right; exact Hb].
* eapply opt_pbuf_agree; [exact OPB | | apply incl_refl]. eapply agree_on_trans.
-- eapply agree_on_incl; [exact AG2 | intros b Hb; right; right; exact Hb].
-- eapply (agree_of_heap_pres rsegs S4L); [exact HPR3 | reflexivity | intros b Hb; right; right; apply in_or_app; left; exact Hb].
Qed.

#[using="usp SPR LO LOS SPA HT SPS SHI LSB K"] Lemma sc_main : forall (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (A : AS S4L HIx) (BS : list blk) (errv : word),
HEAPx A (BS ++ LB) m0 md0 -> stk rsegs m0 lo (bv_unsigned sp) -> rw_cells rsegs m0 482764 [C4 errv] ->
jroot_rep S4L S4F r m0 BS p ->
bytes_at rsegs m0 S sb ->
realizes rsegs (mkCfg (MS (mkR ra sp gp (wz 0x75e70) t0 t1 t2 s0 s1 (wz p) (wz S) (wz n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x25344) fc None m0 (seg_rom rsegs)) md0) T.
Proof.
intros until errv. intros HP ST ERR RR SB.
unfold_consts.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (wmono_refl rsegs m0) as WM.
pose proof (heap_blk_nodup S4L HIx _ _ _ _ HP) as ND.
pose proof (bytes_at_bound _ _ _ _ SB) as SBB. fold n in SBB.
pose proof ST as ST0. carve_frame 48%nat ST.
pose proof (munch_refl [(bv_unsigned sp + -48, bv_unsigned sp)] m0) as MU.
stash SB.
apply rz_evt; [exact MOK|].
step.
destruct (jroot_null_dec r) as [Er | NN].
{
rewrite Er in RR. destruct RR as [Ep EB]. rewrite Ep. if_lit. step.
apply evt_RZ_done. eapply (K _ md0 m0 0).
- split; [| split; [apply model_vm_only_refl | split; [exact ST0 | split; [apply heap_pres_refl | exists errv; exact ERR]]]].
apply ret_statew_intro; [apply fsaved_refl | intros Hf; exact Hf].
- exists A, (@nil blk). rewrite Er. split; [split; [exact Ep | reflexivity] | rewrite EB in HP; exact HP]. }
destruct (jroot_str_cases r m0 BS p RR NN (nodup_app_l' _ _ ND)) as (Hp & CASES).
assert (PB : exists pn, In (p, pn) BS).
{ destruct CASES as [((pb & PBS & DBS & cap & len0 & str & EBS & _) & _) | (_ & n0 & ty & tojs & pb & udel & ud & rest & INp & _)];
[exists (48 + cap); rewrite EBS; left; reflexivity | exists n0; exact INp]. }
destruct PB as (pn & INp).
pose proof (heap_blk S4L HIx _ _ _ _ p pn HP ltac:(apply in_or_app; left; exact INp)) as (Hpn0 & Hpal & Hplo & Hphi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ p pn HP ltac:(apply in_or_app; left; exact INp)) as Hpimg. cbn [hl_img_lo hl_img_hi S4L] in Hpimg.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hphi.
if_falsex.
step. stepz. stepz. stepz. stepz. stepz. stepz.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => rename mX into m2 end.
match goal with H : mem_inv rsegs m2 |- _ => rename H into MI2 end.
unstash SB.

assert (XHP : HEAPx A (BS ++ LB) m2 md0).
{ eapply (heap_frame S4L HIx); [exact HP | | exact WM | exact MI2].
eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HP MU). apply Forall_cons; [cbn [fst snd]; left; clia | apply Forall_nil]. }
assert (XHPR : heap_pres S4L LB (bv_unsigned sp) m0 m2).
{ eapply (heap_pres_of_munch S4L LB (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outside S4L HIx); [exact HP | intros b Hb; apply in_or_app; right; exact Hb | clia |].
apply Forall_cons; [cbn [fst snd]; left; clia | apply Forall_nil]. }
assert (XAG : agree_on rsegs BS m0 m2).
{ eapply agree_of_munch; [exact MU | exact WM |].
intros a k Hin. pose proof (heap_blk S4L HIx _ _ _ _ a k HP ltac:(apply in_or_app; left; exact Hin)) as (Hk & _ & _ & Hhi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hhi. cbn. lia. }
assert (SB2 : bytes_at rsegs m2 S sb).
{ eapply (bytes_at_transport rsegs); [exact SB | exact MU | cbn [disjoint_from]; lia]. }
step. step. step. step. step. if_falsex.
destruct CASES as [(X & SR) | (SR & n0 & ty & tojs & pb & udel & ud & rest & INp' & SZ & N48 & TY & NS & HDR)].
2:{
rewrite (nodup_addr_size BS p pn n0 (nodup_app_l' _ _ ND) INp INp') in *.
unfold jhdr_cells in HDR, SZ. cbn [app hl_segs S4L] in HDR, SZ.
apply (rw_cells_agree rsegs BS m0 m2) in HDR; [| exact XAG | exists p, n0; split; [exact INp' | cbn [cells_size csize Nat.add app] in SZ |- *; rewrite <- SZ; lia]].
unfold JT_STRING in NS. step. rewrite sx32_small by lia. step. step. if_truex.
apply evt_RZ_done. eapply sc_exit; [eassumption | eassumption | exact MOK | apply model_vm_only_refl | exact XHPR | eassumption | exact MI2 |].
exists A, BS. rewrite SR. split; [| exact XHP]. eapply (jroot_rep_agree S4L); [exact RR | exact XAG | apply incl_refl]. }

pose proof (xstr_agree S4L S4F _ _ _ _ _ _ X XAG (incl_refl _)) as X2.
destruct X as (pb & PBS & DBS & cap & len0 & str & EBS & OPB & Hcap & Hlen0 & Hstr & ALT).
rewrite (nodup_addr_size BS p pn (48 + cap) (nodup_app_l' _ _ ND) INp ltac:(rewrite EBS; left; reflexivity)) in *.
assert (OPB2 : opt_pbuf rsegs m2 PBS pb).
{ eapply opt_pbuf_agree; [exact OPB | exact XAG | rewrite EBS; intros b Hb; right; apply in_or_app; right; exact Hb]. }
assert (HDRX : exists tl, rw_cells rsegs m0 p (jhdr_cells JT_STRING 1 (fn_str_to_json_string S4F) pb 0 0 ++ C8 (wz len0) :: tl)
/\ Z.of_nat (cells_size (jhdr_cells JT_STRING 1 (fn_str_to_json_string S4F) pb 0 0 ++ C8 (wz len0) :: tl)) = 48 + cap).
{ destruct ALT as [(_ & _ & _ & jk & H) | (_ & pd & pdn & jk & jk2 & _ & _ & H & _)]; eexists; (split; [exact H|]);
unfold jhdr_cells; rewrite cells_size_app; cbn [cells_size csize Nat.add app]; lia. }
destruct HDRX as (tl & HDR & SZ). unfold jhdr_cells in HDR, SZ. cbn [app hl_segs S4L] in HDR, SZ.
apply (rw_cells_agree rsegs BS m0 m2) in HDR; [| exact XAG | exists p, (48 + cap); split; [rewrite EBS; left; reflexivity | rewrite SZ; lia]].
step. rewrite sx32_small by (unfold JT_STRING; lia). step. step. unfold JT_STRING. if_lit.
step. step.
clear HDR.
destruct ALT as [(Hl0 & EDBS & Hfit & jk & CELLS) | (Hl0 & pd & pdn & jk & jk2 & EDBS & Hpdn & CELLS & PD)].
-
subst DBS. cbn [app] in EBS.
if_falsex.
step. step. step. step.
unfold jhdr_cells in CELLS. cbn [app hl_segs S4L] in CELLS.
apply (rw_cells_agree rsegs BS m0 m2) in CELLS; [| exact XAG | exists p, (48 + cap); split; [rewrite EBS; left; reflexivity | cbn [cells_size csize Nat.add app]; lia]].
apply rw_cells_app with (cs1 := [_;_;_;_;_;_]) in CELLS as [HD LEN]. cbn [cells_size csize Nat.add] in LEN. change (p + Z.of_nat 40) with (p + 40) in LEN.
apply rw_cells_app with (cs1 := [_]) in LEN as [LEN DATA]. cbn [cells_size csize Nat.add] in DATA. change (p + 40 + Z.of_nat 8) with (p + 40 + 8) in DATA.
replace (p + 40 + 8) with (p + 48) in DATA by lia.
destruct (Z.lt_ge_cases len0 n) as [GROW | FIT].
+
if_falsex.
pose proof (rw_cells_CB_word rsegs _ _ _ _ DATA ltac:(lia)) as DATA'.
assert (HDRG : rw_cells rsegs m2 p (jhdr_cells JT_STRING 1 (fn_str_to_json_string S4F) pb 0 0 ++
[C8 (wz len0); C8 (le_bytes_to_word (firstn 8 (str ++ [Z_to_bv 8 0] ++ jk))); CB (Z.to_nat (cap - 8)) (skipn 8 (str ++ [Z_to_bv 8 0] ++ jk))])).
{ unfold jhdr_cells. cbn [app]. replace (Z.to_nat (cap - 8)) with (Z.to_nat cap - 8)%nat by lia. hdr_join HD LEN DATA'. }
apply evt_RZ_done. eapply sc_grow with (A1 := A) (PBS := PBS) (DBS := []) (cap := cap) (pb := pb);
[ eassumption | eassumption | apply model_vm_only_refl | exact XHPR | eassumption | rewrite EBS in XHP; exact XHP | exact SB2 | exact HDRG
| exact OPB2 | exact Hcap | lia | rewrite EBS in X2; exact X2 | lia | left; split; [lia | reflexivity] | exact SR ].
+
if_truex.
step. if_lit. step. step.
apply evt_RZ_done.
eapply sc_tail with (A1 := A) (BS1 := BS) (D := p + 48) (k := Z.to_nat cap) (junk := str ++ [Z_to_bv 8 0] ++ jk) (lenw := wz len0) (bD := p) (szD := 48 + cap) (pn := 48 + cap);
[ eassumption | eassumption | apply model_vm_only_refl | exact XHPR | eassumption | exact XHP | exact SB2 | exact DATA | lia
| rewrite EBS; left; reflexivity | lia | lia | exact LEN | rewrite EBS; left; reflexivity | lia | left; lia | exact SR |].
intros m3 MU3 WM3 MI3 DST3 LEN3.
exists BS. split; [apply Permutation_refl|]. split; [exact Hp|].
exists pb, PBS, (@nil blk), cap, n, sb. split; [exact EBS|]. split.
{ eapply opt_pbuf_agree; [exact OPB2 | | apply incl_refl]. eapply agree_of_munch; [exact MU3 | exact WM3 |].
intros a k' Hin.
assert (Hpa : p <> a).
{ intros <-. pose proof (nodup_app_l' _ _ ND) as NDB. rewrite EBS in NDB. cbn in NDB. inversion NDB as [|x_ l_ Hni Hnd]; subst x_ l_. apply Hni. exact (in_map blk_addr _ _ Hin). }
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ p (48 + cap) a k' HP ltac:(rewrite EBS; left; reflexivity) ltac:(rewrite EBS; right; apply in_or_app; left; exact Hin) Hpa) as D1.
pose proof (heap_blk S4L HIx _ _ _ _ a k' HP ltac:(rewrite EBS; right; apply in_or_app; left; exact Hin)) as (Hk' & _).
cbn. split; [lia|]. split; [lia | exact I]. }
split; [lia|]. split; [lia|]. split; [lia|].
left. split; [lia|]. split; [reflexivity|]. split; [lia|]. exists (skipn (Z.to_nat (n + 1)) (str ++ [Z_to_bv 8 0] ++ jk)).
unfold jhdr_cells. cbn [app].
lazymatch type of MU3 with munch ?W _ _ =>
apply (rw_cells_transport rsegs W m2 m3) in HD; [| exact MU3 | exact WM3 | cbn [disjoint_from]; cbn; lia] end.
hdr_join HD LEN3 DST3.
-
subst DBS. cbn [app] in EBS.
if_truex.
unfold jhdr_cells in CELLS. cbn [app hl_segs S4L] in CELLS.
apply (rw_cells_agree rsegs BS m0 m2) in CELLS; [| exact XAG | exists p, (48 + cap); split; [rewrite EBS; left; reflexivity | cbn [cells_size csize Nat.add app]; lia]].
pose proof (heap_blk S4L HIx _ _ _ _ pd pdn HP ltac:(rewrite EBS; right; left; reflexivity)) as (Hpdn0 & Hpdal & Hpdlo & Hpdhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ pd pdn HP ltac:(rewrite EBS; right; left; reflexivity)) as Hpdimg. cbn [hl_img_lo hl_img_hi S4L] in Hpdimg.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hpdhi.
assert (Hppd : p <> pd).
{ intros E. pose proof (nodup_app_l' _ _ ND) as NDB. rewrite EBS in NDB. cbn in NDB. inversion NDB as [|x_ l_ Hni Hnd]; subst x_ l_. apply Hni. left. symmetry. exact E. }
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ p (48 + cap) pd pdn HP ltac:(rewrite EBS; left; reflexivity) ltac:(rewrite EBS; right; left; reflexivity) Hppd) as DPD.
apply (rw_cells_agree rsegs BS m0 m2) in PD; [| exact XAG | exists pd, pdn; split; [rewrite EBS; right; left; reflexivity | cbn; lia]].
step.
destruct (Z.eq_dec n 0) as [N0 | N1].
+
if_truex.
step. step. step. step.
pose proof (munch_refl [] m2) as MU2. pose proof (wmono_refl rsegs m2) as WM2.
alloc_call (hi_free S4L HIx) S4L HIx XHP MU2 WM2 MI2.
{ right. exists pdn. rewrite EBS. cbn. right; left; reflexivity. }
intros ms3 m3 md3 A3 r3 RS3 VM3 ST3 HPR3 ERR3 HP3. open_ret RS3. cbn [hl_segs hl_tp S4L] in *.
rewrite ?(unsigned_lit (bv_unsigned sp + -48)) in ST3 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -48)) in HPR3 by lia.
rewrite EBS in HPR3, HP3. cbn [app] in HPR3, HP3.
rewrite (lb_remove_other pd) in HPR3, HP3 by (cbn; lia). rewrite lb_remove_head in HPR3, HP3.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR3) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR3) in CELLS; [| eapply client_range_block; [left; reflexivity | lia | cbn; lia]]. cbn [hl_segs S4L] in CELLS.
apply (heap_pres_bytes_at S4L _ _ _ _ _ _ HPR3) in SB2; [| left; cbn; lia]. cbn [hl_segs S4L] in SB2.
assert (OPB3 : opt_pbuf rsegs m3 PBS pb).
{ eapply opt_pbuf_agree; [exact OPB2 | | apply incl_refl].
eapply (agree_of_heap_pres rsegs S4L); [exact HPR3 | reflexivity | intros b Hb; right; apply in_or_app; left; exact Hb]. }
pose proof (heap_model_ok _ _ _ _ _ _ HP3) as MOK3.
pose proof (heap_mem_inv _ _ _ _ _ _ HP3) as MI3. cbn [hl_segs S4L] in MI3.
pose proof (munch_refl [(p + 40, p + 48)] m3) as MU3. pose proof (wmono_refl rsegs m3) as WM3.
clear MU2 WM2.
reenter MOK3.
step. step. step. stepz. step.
step. step. step. step. if_truex. step. if_lit. step. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => rename mX into m4 end.
match goal with H : mem_inv rsegs m4 |- _ => rename H into MI4 end.
lazymatch goal with H : rw_cells rsegs m4 p ?cs |- _ => rename H into CELLS4 end.
assert (HP4 : HEAPx A3 (((p, 48 + cap) :: PBS) ++ LB) m4 md3).
{ eapply (heap_frame S4L HIx); [exact HP3 | | exact WM3 | exact MI4].
eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HP3 MU3).
apply Forall_cons; [cbn [fst snd]; right; left; exists p, (48 + cap); split; [left; reflexivity | lia]| apply Forall_nil]. }
assert (HPR4 : heap_pres S4L LB (bv_unsigned sp) m0 m4).
{ eapply heap_pres_trans; [exact XHPR|]. eapply heap_pres_trans.
- eapply heap_pres_weaken; [exact HPR3 | lia | intros b Hb; right; apply in_or_app; right; exact Hb].
- eapply (heap_pres_of_munch S4L LB (bv_unsigned sp)); [exact MU3 | exact WM3 |].
eapply (client_outside S4L HIx); [exact HP3 | intros b Hb; right; apply in_or_app; right; exact Hb | clia |].
apply Forall_cons; [cbn [fst snd]; right; left; exists p, (48 + cap); split; [left; reflexivity | split; [| lia]];
eapply (nodup_prefix_suffix ((p, 48 + cap) :: PBS) LB p (48 + cap)); [exact (heap_blk_nodup S4L HIx _ _ _ _ HP3) | left; reflexivity]
| apply Forall_nil]. }
apply rw_cells_app with (cs1 := [_;_;_;_;_;_]) in CELLS4 as [HD LEN]. cbn [cells_size csize Nat.add] in LEN. change (p + Z.of_nat 40) with (p + 40) in LEN.
apply rw_cells_app with (cs1 := [_]) in LEN as [LEN DATA]. cbn [cells_size csize Nat.add] in DATA. change (p + 40 + Z.of_nat 8) with (p + 40 + 8) in DATA.
replace (p + 40 + 8) with (p + 48) in DATA by lia.
apply (rw_cells_recast rsegs _ _ _ [CB (Z.to_nat cap) (le8 (wz pd) ++ jk)]) in DATA;
[| split; [| exact I]; cbn [cell_wf]; rewrite length_app, length_le8; destruct DATA as [[[_ [Hw _]] _] _]; cbn [cell_wf] in Hw; lia
| cbn [cells_bytes cbytes app]; rewrite <- app_assoc; reflexivity | cbn; lia].
apply evt_RZ_done.
eapply sc_tail with (A1 := A3) (BS1 := (p, 48 + cap) :: PBS) (D := p + 48) (k := Z.to_nat cap) (junk := le8 (wz pd) ++ jk) (bD := p) (szD := 48 + cap) (pn := 48 + cap);
[ eassumption | eassumption | exact VM3 | exact HPR4 | eassumption | exact HP4 | exact SB2 | exact DATA | lia
| left; reflexivity | lia | lia | exact LEN | left; reflexivity | lia | left; lia | exact SR |].
intros m5 MU5 WM5 MI5 DST5 LEN5.
exists ((p, 48 + cap) :: PBS). split; [apply Permutation_refl|]. split; [exact Hp|].
exists pb, PBS, (@nil blk), cap, 0, (@nil byte). split; [reflexivity|]. split.
{ eapply opt_pbuf_agree; [exact OPB3 | | apply incl_refl].
eapply agree_on_trans; (eapply agree_of_munch; [eassumption | eassumption |]); intros a k' Hin;
(assert (Hpa : p <> a) by (intros <-; exact (nodup_prefix_suffix [(p, 48 + cap)] (PBS ++ LB) p (48 + cap) k' (heap_blk_nodup S4L HIx _ _ _ _ HP3) ltac:(left; reflexivity) ltac:(apply in_or_app; left; exact Hin))));
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ p (48 + cap) a k' HP3 ltac:(left; reflexivity) ltac:(right; apply in_or_app; left; exact Hin) Hpa) as D1;
pose proof (heap_blk S4L HIx _ _ _ _ a k' HP3 ltac:(right; apply in_or_app; left; exact Hin)) as (Hk' & _); cbn; [split; [lia | exact I] | split; [lia|]; split; [lia | exact I]]. }
split; [lia|]. split; [lia|]. split; [cbn; lia|].
left. split; [lia|]. split; [reflexivity|]. split; [lia|]. exists (skipn (Z.to_nat (n + 1)) (le8 (wz pd) ++ jk)).
unfold jhdr_cells. cbn [app].
lazymatch type of MU5 with munch ?W _ _ =>
apply (rw_cells_transport rsegs W m4 m5) in HD; [| exact MU5 | exact WM5 | cbn [disjoint_from]; cbn; lia] end.
assert (Esb : sb = []) by (destruct sb; [reflexivity | exfalso; subst n; cbn [length] in N0; lia]).
rewrite Esb in DST5. cbn [app] in DST5 |- *. rewrite N0 in LEN5.
hdr_join HD LEN5 DST5.
+
if_falsex.

step. step. step. rewrite neg_word_negval by lia. step. step.
apply rw_cells_app with (cs1 := [_;_;_;_;_;_]) in CELLS as [HD LEN]. cbn [cells_size csize Nat.add] in LEN. change (p + Z.of_nat 40) with (p + 40) in LEN.
apply rw_cells_app with (cs1 := [_]) in LEN as [LEN PDC]. cbn [cells_size csize Nat.add] in PDC. change (p + 40 + Z.of_nat 8) with (p + 40 + 8) in PDC.
replace (p + 40 + 8) with (p + 48) in PDC by lia.
destruct (Z.lt_ge_cases (- len0) n) as [GROW | FIT].
*
if_truex.
apply evt_RZ_done. eapply sc_grow with (A1 := A) (PBS := PBS) (DBS := [(pd, pdn)]) (cap := cap) (pb := pb);
[ eassumption | eassumption | apply model_vm_only_refl | exact XHPR | eassumption | rewrite EBS in XHP; exact XHP | exact SB2
| unfold jhdr_cells; cbn [app]; hdr_join HD LEN PDC
| exact OPB2 | exact Hcap | lia | rewrite EBS in X2; exact X2 | lia | right; split; [lia | exists pd, pdn; split; reflexivity] | exact SR ].
*
if_falsex.
step. if_lit. step.
apply evt_RZ_done.
eapply sc_tail with (A1 := A) (BS1 := BS) (D := pd) (k := Z.to_nat pdn) (junk := str ++ [Z_to_bv 8 0] ++ jk2) (lenw := wz len0) (bD := pd) (szD := pdn) (pn := 48 + cap);
[ eassumption | eassumption | apply model_vm_only_refl | exact XHPR | eassumption | exact XHP | exact SB2 | exact PD | lia
| rewrite EBS; right; left; reflexivity | lia | lia | exact LEN | rewrite EBS; left; reflexivity | lia | lia | exact SR |].
intros m3 MU3 WM3 MI3 DST3 LEN3.
exists BS. split; [apply Permutation_refl|]. split; [exact Hp|].
exists pb, PBS, [(pd, pdn)], cap, (- n), sb. split; [exact EBS|]. split.
{ eapply opt_pbuf_agree; [exact OPB2 | | apply incl_refl]. eapply agree_of_munch; [exact MU3 | exact WM3 |].
intros a k' Hin.
pose proof (nodup_app_l' _ _ ND) as NDB. rewrite EBS in NDB.
assert (Hpa : p <> a).
{ intros <-. cbn in NDB. inversion NDB as [|x_ l_ Hni Hnd]; subst x_ l_. apply Hni. right. exact (in_map blk_addr _ _ Hin). }
assert (Hpda : pd <> a).
{ intros <-. cbn in NDB. inversion NDB as [|x_ l_ Hni Hnd]; subst x_ l_. inversion Hnd as [|x2_ l2_ Hni2 Hnd2]; subst x2_ l2_. apply Hni2. exact (in_map blk_addr _ _ Hin). }
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ p (48 + cap) a k' HP ltac:(rewrite EBS; left; reflexivity) ltac:(rewrite EBS; right; right; apply in_or_app; left; exact Hin) Hpa) as D1.
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ pd pdn a k' HP ltac:(rewrite EBS; right; left; reflexivity) ltac:(rewrite EBS; right; right; apply in_or_app; left; exact Hin) Hpda) as D2.
pose proof (heap_blk S4L HIx _ _ _ _ a k' HP ltac:(rewrite EBS; right; right; apply in_or_app; left; exact Hin)) as (Hk' & _).
cbn. split; [(clear - Hpdn FIT D2; lia)|]. split; [(clear - Hcap D1; lia) | exact I]. }
split; [lia|]. split; [lia|]. split; [lia|].
right. split; [lia|]. exists pd, pdn, jk, (skipn (Z.to_nat (n + 1)) (str ++ [Z_to_bv 8 0] ++ jk2)). split; [reflexivity|]. split; [lia|]. split; [| exact DST3].
unfold jhdr_cells. cbn [app].
lazymatch type of MU3 with munch ?W _ _ =>
apply (rw_cells_transport rsegs W m2 m3) in HD; [| exact MU3 | exact WM3 | cbn [disjoint_from]; cbn; (clear - Hcap Hpdn0 DPD; lia)];
apply (rw_cells_transport rsegs W m2 m3) in PDC; [| exact MU3 | exact WM3 | cbn [disjoint_from]; cbn [cells_size csize Nat.add]; (clear - Hcap Hl0 Hpdn DPD; lia)] end.
rewrite unsigned_lit in LEN3 by lia. replace (0 - n) with (- n) in LEN3 by lia.
hdr_join HD LEN3 PDC.
Qed.
End BodyC.

#[using="Type"] Theorem set_string_len_P : jo_set_string_len_stmt S4L HIx S4F 0x25460 (64 + 8256).
Proof.
unfold jo_set_string_len_stmt, buffer_arg. intros until errv.
intros (HP & ST & LO & LOS & SPA & HT & ERR & TP & RA) RR (SB & SPS & SHI) LSB -> -> -> K.
cbn [hl_segs hl_tp S4L] in *. subst tp. change (0x75e70 - 164) with 482764 in ERR.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
apply rz_evt; [exact MOK|]. step. apply evt_RZ_done.
eapply sc_main with (lo := lo) (LB := LB) (r := r) (A := A) (BS := BS) (errv := errv).
all: first [eassumption | exact SPR | exact K | lia].
Qed.

#[using="Type"] Theorem set_string_P : jo_set_string_stmt S4L HIx S4F 0x25304 (64 + 8256).
Proof.
unfold jo_set_string_stmt, cstring_arg. intros until errv.
intros (HP & ST & LO & LOS & SPA & HT & ERR & TP & RA) RR (SB & NZ & PAD & SPS & SHI) LSB -> -> K.
cbn [hl_segs hl_tp S4L] in *. subst tp. change (0x75e70 - 164) with 482764 in ERR.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. unfold_consts.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (wmono_refl rsegs m) as WM.
pose proof (bytes_at_bound _ _ _ _ SB) as SBB. rewrite length_app in SBB. cbn [length] in SBB.
assert (NONUL : ~ In (Z_to_bv 8 0) sb) by (intros Hin; exact (proj1 (Forall_forall _ _) NZ _ Hin eq_refl)).
pose proof ST as ST0. carve_frame 32%nat ST.
pose proof (munch_refl [(bv_unsigned sp + -32, bv_unsigned sp)] m) as MU.
apply rz_evt; [exact MOK|].
step. stepz. stepz. stepz. step. step. step. step.
rewrite <- (unsigned_lit S) in SB by lia.
assert (PADZ : (- (bv_unsigned (wz S) + Z.of_nat (length sb) + 1)) mod 8 <= Z.of_nat (length slack)) by (rewrite unsigned_lit by lia; exact PAD).
call strlen_spec; [exact SB | exact NONUL | exact PADZ | assumption |].
rewrite (unsigned_lit S) in * by lia.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => rename mX into m2 end.
match goal with H : mem_inv rsegs m2 |- _ => rename H into MI2 end.
match goal with H : bytes_at rsegs m2 S _ |- _ => rename H into SB2 end.
step. step. step. step. step. step.
lazymatch goal with H : rw_cells rsegs m2 (bv_unsigned sp + -32) _ |- _ => release_frame H ST (bv_unsigned sp) end.
step. step. fold_mkR.
assert (XHP : HEAPx A (BS ++ LB) m2 md).
{ eapply (heap_frame S4L HIx); [exact HP | | exact WM | exact MI2].
eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HP MU). apply Forall_cons; [cbn [fst snd]; left; clia | apply Forall_nil]. }
assert (XHPR : heap_pres S4L LB (bv_unsigned sp) m m2).
{ eapply (heap_pres_of_munch S4L LB (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outside S4L HIx); [exact HP | intros b Hb; apply in_or_app; right; exact Hb | clia |].
apply Forall_cons; [cbn [fst snd]; left; clia | apply Forall_nil]. }
assert (XAG : agree_on rsegs BS m m2).
{ eapply agree_of_munch; [exact MU | exact WM |].
intros a k Hin. pose proof (heap_blk S4L HIx _ _ _ _ a k HP ltac:(apply in_or_app; left; exact Hin)) as (Hk & _ & _ & Hhi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hhi. cbn. lia. }
apply bytes_at_app in SB2 as [SB2 _].
apply evt_RZ_done.
eapply sc_main with (m0 := m2) (lo := lo) (LB := LB) (r := r) (A := A) (BS := BS).
all: try first [exact SPR | exact XHP | exact SB2 | eapply (jroot_rep_agree S4L S4F); [exact RR | exact XAG | apply incl_refl]].
all: try (unfold set_string_post; intros ms' md' m' rv (RS' & VM' & ST' & HPR' & ERR') ROOT'; eapply K; [| exact ROOT'];
split; [exact RS' | split; [exact VM' | split; [exact ST' | split; [eapply heap_pres_trans; [exact XHPR | exact HPR'] | exact ERR']]]]).
all: first [eassumption | lia].
Qed.
End SetStrPS.

End RC__2.
End Mq1.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEQM.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QjDH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDH.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmZZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmZZ.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QC8c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QC8c.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKQo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKQo.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPZI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPZI.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qu4M.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qu4M.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qihm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qihm. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QtMn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QtMn. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QIsM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QIsM.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSL3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSL3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QhI1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QhI1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QunB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QunB.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qvbw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qvbw. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYIF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYIF.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QrIB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QrIB.Mq0.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section ShallowP2.
Variable HIx : heap_iface S4L.
Notation HEAPx := (HEAP S4L HIx).
Notation wz := (Z_to_bv 64).
Notation lh_glob4 := (lh_glob rsegs S4F GHASH4 GGOT4 GVDSO4 vdso_ok4).

Variables (ra sp gp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : Model) (LB BS : list blk) (lo p D : Z) (r : jroot) (T : TSet).
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOS : lo <= bv_unsigned sp - SH_STK_P.
Hypothesis SPA : bv_unsigned sp mod 16 = 0.
Hypothesis HT : bv_unsigned sp <= hi_top S4L HIx.
Hypothesis RA : bv_unsigned ra mod 2 = 0.
Hypothesis SPD : bv_unsigned sp <= D.
Hypothesis DHI : D + 8 <= hi_top S4L HIx.
Hypothesis DAL : D mod 8 = 0.
Hypothesis NN : r <> JRnull.
Hypothesis JR0 : jroot_rep S4L S4F r m0 BS p.
Hypothesis Kont : forall ms' md' m' rv,
jf_postD S4L D ra sp gp (wz 0x75e70) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 (BS ++ LB) lo rv m' ms' md' ->
jc_glob_P m' -> jroot_rep S4L S4F r m' BS p -> shallow_res S4L HIx S4F r BS LB D m' md' rv ->
realizes rsegs (mkCfg ms' md') T.

Notation sh_inv := (sh_inv ra sp s0 s1 s2 s3 s4 s5 F m0 md0 LB BS lo D).
Notation sh_regs := (sh_regs sp gp s6 s7 s8 s9 s10 s11 p D).

Ltac sh_hyps := try first [ exact Kont | exact JR0 | exact NN | exact DAL | exact DHI | exact SPD | exact RA | exact HT | exact SPA | exact LOS | exact LO ].

#[using="LO LOS SPA HT SPD DHI DAL NN JR0 Kont"] Lemma sh_object :
forall (x1 t0 t1 t2 a0 a2 a3 a5 a6 a7 x18 x19 x20 x21 t3 t4 t5 t6 : word)
(mc : word -> option byte) (mdc : Model) (A : AS S4L HIx) (np tojs pb udel ud : Z) (dold errc : word),
sh_inv mc mdc -> HEAPx A (BS ++ LB) mc mdc -> In (p, np) BS -> 48 <= np ->
rw_cells rsegs mc D [C8 dold] -> rw_cells rsegs mc (0x75e70 - 164) [C4 errc] ->
rw_cells rsegs mc p (jhdr_cells JT_OBJECT 1 tojs pb udel ud) ->
(forall m' q t TBS, rw_cells rsegs m' q (jhdr_cells JT_OBJECT 1 tojs 0 0 0 ++ [C8 (wz t)]) ->
lhtab2 rsegs S4F m' TBS t [] -> scopy S4L S4F r m' ((q, 48) :: TBS) q) ->
realizes rsegs (mkCfg (MS (sh_regs x1 t0 t1 t2 a0 a2 a3 a5 a6 a7 x18 x19 x20 x21 t3 t4 t5 t6)
F (wz 0x25694) fc None mc (seg_rom rsegs)) mdc) T.
Proof.
intros until errc. intros INV HP INp Hnp DC ERR SRC SCB. pose proof INV as (VM & PRES & ST & FR & G).
unfold QrIB.Mq0.sh_frame in FR. unfold QrIB.Mq0.sh_regs. unfold SH_STK_P in LOS. unfold_consts. word_range sp SPR.
change (0x75e70 - 164) with 482764 in ERR.
assert (INp1 : In (p, np) (BS ++ LB)) by (apply in_or_app; left; exact INp).
pose proof (heap_blk S4L HIx _ _ _ _ p np HP INp1) as (_ & Hpal & Hplo & Hphi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ p np HP INp1) as Hpimg. cbn [hl_img_lo hl_img_hi S4L] in Hpimg.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hphi.
unfold jhdr_cells in SRC.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (wmono_refl rsegs mc) as WM.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)] mc) as MU.
stash G. stash SCB.
apply rz_evt; [exact MOK|].
step. step.

alloc_call (hi_malloc S4L HIx) S4L HIx HP MU WM MI.
intros ms2 m2 md2 A2 q e2 RS VM2 ST2 HPR2 ERR2 OUT2. open_ret RS. cbn [hl_segs S4L] in *.
rewrite ?(unsigned_lit (bv_unsigned sp + -64)) in ST2 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -64)) in HPR2 by lia.
extend_presD S4L HIx PRES MU WM HP. extend_presD_call PRES HPR2.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in DC; [| left; cbn; lia]. cbn [hl_segs S4L] in DC.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in SRC; [| eapply client_range_block; [exact INp1 | lia | cbn; lia]]. cbn [hl_segs S4L] in SRC.
unstash G. pose proof (jc_glob_P_pres _ _ _ _ HPR2 (jc_glob_P_munch _ _ _ G MU WM ltac:(repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd]; lia))) as G2. clear G.
clear MU WM MI ST.
destruct OUT2 as [(-> & _ & HP2) | (Hq & [junk0 BLK] & HP2)].
-
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2.
pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI. cbn [hl_segs S4L] in MI.
pose proof (munch_refl [] m2) as MU. pose proof (wmono_refl rsegs m2) as WM.
reenter MOK2.
step. if_true.
apply evt_RZ_done. apply (proj1 (rw_cells_app rsegs m2 p [_; _] _)) in SRC as X. destruct X as [_ SRC8]. cbn [cells_size csize Nat.add app] in SRC8.
apply (proj1 (rw_cells_app rsegs m2 (p + 8) [_] _)) in SRC8 as [SRC8 _].
eapply (sh_join HIx) with (ty := JT_OBJECT) (tojs := tojs); sh_hyps;
[ split; [eapply model_vm_only_trans; [exact VM | exact VM2] | split; [exact PRES | split; [exact ST2 | split; [exact FR | exact G2]]]]
| apply fsv8_refl | intros Hf; exact Hf | exact DC | exact ERR2 | exact SRC8 | left; split; [reflexivity | exists A2; exact HP2] ].
-
change (Z.to_nat 48) with 48%nat in BLK.
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2.
pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI. cbn [hl_segs S4L] in MI.
pose proof (heap_blk S4L HIx _ _ _ _ q 48 HP2 ltac:(left; reflexivity)) as (_ & Hqal & Hqlo & Hqhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ q 48 HP2 ltac:(left; reflexivity)) as Hqimg. cbn [hl_img_lo hl_img_hi S4L] in Hqimg.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hqhi.
assert (Hqp : q <> p) by (intros ->; exact (fresh_not_in S4L HIx _ _ _ _ _ _ np HP2 INp1)).
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ q 48 p np HP2 ltac:(left; reflexivity) ltac:(right; exact INp1) Hqp) as Hdqp.
pose proof (munch_refl [(q, q + 48)] m2) as MU. pose proof (wmono_refl rsegs m2) as WM.
stash G2.
reenter MOK2.
step. if_falsex.
do 5 step. stepz. stepz. stepz. stepz. stepz.
do 4 step. step.
unstash G2.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
assert (G3 : jc_glob_P mx) by
(eapply jc_glob_P_outside; [exact G2 | exact MU | exact WM |]; repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd]; lia);
assert (HP3 : HEAPx A2 ((q, 48) :: BS ++ LB) mx md2) by heap_now S4L HIx HP2 MU WM MI
end.
extend_presD S4L HIx PRES MU WM HP2.
apply (proj1 (rw_cells_app rsegs _ p [_; _] _)) in SRC as X. destruct X as [_ SRC8]. cbn [cells_size csize Nat.add app] in SRC8.
apply (proj1 (rw_cells_app rsegs _ (p + 8) [_] _)) in SRC8 as [SRC8 _].
apply evt_RZ_done.
eapply (lh_kchar_table_new_cps HIx) with (LB := (q, 48) :: BS ++ LB) (lo := lo);
[ exact HP3 | exact G3 | .. ]; try alloc_side.
intros ms3 md3 (m3 & A3 & t & e3 & RS3 & VM3 & ST3 & HPR3 & ERR3 & G4 & OUT3).
destruct RS3 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F3 & fc3 & -> & FS3 & FRM3).
cbn [hl_segs S4L] in *.
rewrite ?(unsigned_lit (bv_unsigned sp + -64)) in ST3 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -64)) in HPR3 by lia.
extend_presD_call PRES HPR3.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR3) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR3) in DC; [| left; cbn; lia]. cbn [hl_segs S4L] in DC.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR3) in SRC8; [| eapply client_range_block; [right; exact INp1 | lia | cbn; lia]]. cbn [hl_segs S4L] in SRC8.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR3) in BLK; [| eapply client_range_block; [left; reflexivity | lia | cbn; lia]]. cbn [hl_segs S4L] in BLK.
change lh_glob4 with jc_glob_P in G4.
clear MU WM MI G2 G3.
destruct OUT3 as [(-> & HP4) | (Ht & TBS & TAB & HP4)].
+
pose proof (heap_model_ok _ _ _ _ _ _ HP4) as MOK4.
pose proof (heap_mem_inv _ _ _ _ _ _ HP4) as MI. cbn [hl_segs S4L] in MI.
pose proof (munch_refl [(q, q + 48)] m3) as MU. pose proof (wmono_refl rsegs m3) as WM.
stash G4.
reenter MOK4.

step. step. stepz. step. if_false. step. step. step. step.
unstash G4.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
assert (HP5 : HEAPx A3 ((q, 48) :: BS ++ LB) mx md3) by heap_now S4L HIx HP4 MU WM MI;
assert (G5 : jc_glob_P mx) by
(eapply jc_glob_P_outside; [exact G4 | exact MU | exact WM |]; repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd]; lia)
end.
extend_presD S4L HIx PRES MU WM HP4.
apply evt_RZ_done.
eapply (printbuf_free_cps HIx) with (LB := (q, 48) :: BS ++ LB) (BS := []) (p := 0) (lo := lo);
[ cbn [app]; exact HP5 | left; split; reflexivity | .. ]; try alloc_side.
intros ms5 md5 (m5 & A5 & r5 & RS5 & VM5 & ST5 & HPR5 & ERR5 & HP6).
destruct RS5 as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & F5 & fc5 & -> & FS5 & FRM5).
cbn [hl_segs S4L] in *.
rewrite ?(unsigned_lit (bv_unsigned sp + -64)) in ST5 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -64)) in HPR5 by lia.
extend_presD_call PRES HPR5.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR5) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR5) in DC; [| left; cbn; lia]. cbn [hl_segs S4L] in DC.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR5) in SRC8; [| eapply client_range_block; [right; exact INp1 | lia | cbn; lia]]. cbn [hl_segs S4L] in SRC8.
pose proof (jc_glob_P_pres _ _ _ _ HPR5 G5) as G6.
clear MU WM MI BLK HP5 G5.
pose proof (heap_model_ok _ _ _ _ _ _ HP6) as MOK6.
pose proof (heap_mem_inv _ _ _ _ _ _ HP6) as MI. cbn [hl_segs S4L] in MI.
pose proof (munch_refl [] m5) as MU. pose proof (wmono_refl rsegs m5) as WM.
stash G6.
reenter MOK6.
step. step.

alloc_call (hi_free S4L HIx) S4L HIx HP6 MU WM MI.
{ right. exists 48. left. reflexivity. }
intros ms7 m7 md7 A7 r7 RS7 VM7 ST7 HPR7 ERR7 HP7. open_ret RS7. cbn [hl_segs S4L] in *.
rewrite lb_remove_head in HPR7, HP7.
rewrite ?(unsigned_lit (bv_unsigned sp + -64)) in ST7 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -64)) in HPR7 by lia.
extend_presD_call PRES HPR7.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR7) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR7) in DC; [| left; cbn; lia]. cbn [hl_segs S4L] in DC.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR7) in SRC8; [| eapply client_range_block; [exact INp1 | lia | cbn; lia]]. cbn [hl_segs S4L] in SRC8.
unstash G6. pose proof (jc_glob_P_pres _ _ _ _ HPR7 G6) as G7. clear G6.
clear MU WM MI.
pose proof (heap_model_ok _ _ _ _ _ _ HP7) as MOK7.
pose proof (heap_mem_inv _ _ _ _ _ _ HP7) as MI. cbn [hl_segs S4L] in MI.
change (482928 - 164) with 482764 in ERR7.
pose proof (munch_refl [(482764, 482768)] m7) as MU. pose proof (wmono_refl rsegs m7) as WM.
stash G7.
reenter MOK7.
do 4 step. step. step. step. stepz. step.
unstash G7. unstash SCB.
apply evt_RZ_done.
lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ =>
assert (HP8 : HEAPx A7 (BS ++ LB) mx md7) by heap_now S4L HIx HP7 MU WM MI;
assert (G8 : jc_glob_P mx) by
(eapply jc_glob_P_munch; [exact G7 | exact MU | exact WM |]; repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd]; lia)
end.
extend_presD S4L HIx PRES MU WM HP7.
eapply (sh_join HIx) with (ty := JT_OBJECT) (tojs := tojs); sh_hyps;
[ split; [| split; [exact PRES | split; [exact ST7 | split; [exact FR | exact G8]]]]
| | | exact DC | exact ERR7 | exact SRC8 | left; split; [reflexivity | exists A7; exact HP8] ].
* eapply model_vm_only_trans; [exact VM|]. eapply model_vm_only_trans; [exact VM2|]. eapply model_vm_only_trans; [exact VM3|].
eapply model_vm_only_trans; [exact VM5 | exact VM7].
* apply fsv8_of_fsaved. eapply fsaved_trans; [exact FS3 | exact FS5].
* intros Hf. apply FRM5. apply FRM3. exact Hf.
+
pose proof TAB as (tbl & size & es & svs & Hkvs & EBS2 & OPEN).
destruct es as [|e0 es']; [| cbn in Hkvs; discriminate]. subst TBS. unfold lh_blocks in HP4. cbn [map app] in HP4.
pose proof (proj1 OPEN) as THDR. unfold lh_hdrf in THDR.
pose proof (rw_cells_bound rsegs m3 t _ THDR) as R2B. cbn [cells_size csize Nat.add] in R2B. clear THDR.
pose proof (heap_model_ok _ _ _ _ _ _ HP4) as MOK4.
pose proof (heap_mem_inv _ _ _ _ _ _ HP4) as MI. cbn [hl_segs S4L] in MI.
pose proof (heap_blk_img S4L HIx _ _ _ _ t 56 HP4 ltac:(left; reflexivity)) as Himg_t. cbn [hl_img_lo hl_img_hi S4L] in Himg_t.
pose proof (heap_blk_img S4L HIx _ _ _ _ tbl (40 * size) HP4 ltac:(right; left; reflexivity)) as Himg_tbl. cbn [hl_img_lo hl_img_hi S4L] in Himg_tbl.
pose proof (heap_blk S4L HIx _ _ _ _ t 56 HP4 ltac:(left; reflexivity)) as (_ & Htal & Htlo & Hthi & _).
pose proof (heap_blk S4L HIx _ _ _ _ tbl (40 * size) HP4 ltac:(right; left; reflexivity)) as (_ & Hbal & Hblo & Hbhi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hthi, Hbhi.
assert (Htq : t <> q) by (intros ->; exact (fresh_not_in S4L HIx _ _ _ _ _ _ 48 HP4 ltac:(right; left; reflexivity))).
assert (Hbq : tbl <> q).
{ intros ->. pose proof (heap_blk_nodup S4L HIx _ _ _ _ HP4) as ND. cbn in ND.
inversion ND as [|x l Hni Hnd]; subst. inversion Hnd as [|x' l' Hni' Hnd']; subst. apply Hni'. left. reflexivity. }
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ t 56 q 48 HP4 ltac:(left; reflexivity) ltac:(right; right; left; reflexivity) Htq) as Hdj1.
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ tbl (40 * size) q 48 HP4 ltac:(right; left; reflexivity) ltac:(right; right; left; reflexivity) Hbq) as Hdj2.
stash TAB. clear OPEN. stash G4.
pose proof (munch_refl [(q, q + 48)] m3) as MU. pose proof (wmono_refl rsegs m3) as WM.
reenter MOK4.
step. step. step. step. if_truex.
unstash TAB. unstash G4. unstash SCB.
apply evt_RZ_done.
jhdr_split BLK.
apply (proj1 (rw_cells_app rsegs _ q [_; _; _] _)) in BLK as X. destruct X as [QH QT]. cbn [cells_size csize Nat.add app] in QT.
lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ =>
assert (HP5 : HEAPx A3 ((t, 56) :: (tbl, 40 * size) :: (q, 48) :: BS ++ LB) mx md3) by heap_now S4L HIx HP4 MU WM MI;
assert (G5 : jc_glob_P mx) by
(eapply jc_glob_P_outside; [exact G4 | exact MU | exact WM |]; repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd]; (clear - Hqimg; lia))
end.
extend_presD S4L HIx PRES MU WM HP4.
eapply (sh_join HIx) with (ty := JT_OBJECT) (tojs := tojs); sh_hyps;
[ split; [| split; [exact PRES | split; [exact ST3 | split; [exact FR | exact G5]]]]
| apply fsv8_of_fsaved; exact FS3 | exact FRM3 | exact DC | exact ERR3 | exact SRC8 | ].
{ eapply model_vm_only_trans; [exact VM|]. eapply model_vm_only_trans; [exact VM2 | exact VM3]. }
right. split; [exact Hq|]. exists A3, [(q, 48); (t, 56); (tbl, 40 * size)], 48, (fn_obj_to_json_string S4F).
split; [eapply (heap_perm S4L HIx); [exact HP5 | perm] |].
split; [left; reflexivity|]. split; [lia|]. split; [exact QH|].
intros m' QH' MU' WM'. eapply (SCB m' q t).
* unfold jhdr_cells. cbn [app].
apply (proj2 (rw_cells_app rsegs m' q [_; _; _] _)). split; [exact QH'|]. cbn [cells_size csize Nat.add app].
eapply (rw_cells_transport rsegs); [exact QT | exact MU' | exact WM' |]. cbn. lia.
* eapply (lhtab2_agree rsegs S4F); [exact TAB | | apply incl_refl].
eapply agree_on_trans.
-- eapply (agree_of_munch rsegs); [exact MU | exact WM |].
intros b k Hb. cbn in Hb. cbn. destruct Hb as [Hb | [Hb | Hb]]; [injection Hb as <- <- | injection Hb as <- <- | destruct Hb]; lia.
-- eapply (agree_of_munch rsegs); [exact MU' | exact WM' |].
intros b k Hb. cbn in Hb. cbn. destruct Hb as [Hb | [Hb | Hb]]; [injection Hb as <- <- | injection Hb as <- <- | destruct Hb]; (clear - LO LOS SPD Hthi Hdj1 Hbhi Hdj2; lia).
Qed.

#[using="LO LOS SPA HT SPD DHI DAL NN JR0 Kont"] Lemma sh_array :
forall (x1 t0 t1 t2 a0 a2 a3 a5 a6 a7 x18 x19 x20 x21 t3 t4 t5 t6 : word)
(mc : word -> option byte) (mdc : Model) (A : AS S4L HIx) (np tojs pb udel ud : Z) (dold errc : word),
sh_inv mc mdc -> HEAPx A (BS ++ LB) mc mdc -> In (p, np) BS -> 48 <= np ->
rw_cells rsegs mc D [C8 dold] -> rw_cells rsegs mc (0x75e70 - 164) [C4 errc] ->
rw_cells rsegs mc p (jhdr_cells JT_ARRAY 1 tojs pb udel ud) ->
(forall m' q a ABS, rw_cells rsegs m' q (jhdr_cells JT_ARRAY 1 tojs 0 0 0 ++ [C8 (wz a)]) ->
alist rsegs S4F m' ABS a [] -> scopy S4L S4F r m' ((q, 48) :: ABS) q) ->
realizes rsegs (mkCfg (MS (sh_regs x1 t0 t1 t2 a0 a2 a3 a5 a6 a7 x18 x19 x20 x21 t3 t4 t5 t6)
F (wz 0x255e0) fc None mc (seg_rom rsegs)) mdc) T.
Proof.
intros until errc. intros INV HP INp Hnp DC ERR SRC SCB. pose proof INV as (VM & PRES & ST & FR & G).
unfold QrIB.Mq0.sh_frame in FR. unfold QrIB.Mq0.sh_regs. unfold SH_STK_P in LOS. unfold_consts. word_range sp SPR.
change (0x75e70 - 164) with 482764 in ERR.
assert (INp1 : In (p, np) (BS ++ LB)) by (apply in_or_app; left; exact INp).
pose proof (heap_blk S4L HIx _ _ _ _ p np HP INp1) as (_ & Hpal & Hplo & Hphi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ p np HP INp1) as Hpimg. cbn [hl_img_lo hl_img_hi S4L] in Hpimg.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hphi.
unfold jhdr_cells in SRC.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (wmono_refl rsegs mc) as WM.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)] mc) as MU.
stash G. stash SCB.
apply rz_evt; [exact MOK|].
step. step.

alloc_call (hi_malloc S4L HIx) S4L HIx HP MU WM MI.
intros ms2 m2 md2 A2 q e2 RS VM2 ST2 HPR2 ERR2 OUT2. open_ret RS. cbn [hl_segs S4L] in *.
rewrite ?(unsigned_lit (bv_unsigned sp + -64)) in ST2 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -64)) in HPR2 by lia.
extend_presD S4L HIx PRES MU WM HP. extend_presD_call PRES HPR2.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in DC; [| left; cbn; lia]. cbn [hl_segs S4L] in DC.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in SRC; [| eapply client_range_block; [exact INp1 | lia | cbn; lia]]. cbn [hl_segs S4L] in SRC.
unstash G. pose proof (jc_glob_P_pres _ _ _ _ HPR2 (jc_glob_P_munch _ _ _ G MU WM ltac:(repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd]; lia))) as G2. clear G.
clear MU WM MI ST.
apply (proj1 (rw_cells_app rsegs _ p [_; _] _)) in SRC as X. destruct X as [_ SRC8]. cbn [cells_size csize Nat.add app] in SRC8.
apply (proj1 (rw_cells_app rsegs _ (p + 8) [_] _)) in SRC8 as [SRC8 _]. clear SRC.
destruct OUT2 as [(-> & _ & HP2) | (Hq & [junk0 BLK] & HP2)].
-
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2.
pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI. cbn [hl_segs S4L] in MI.
pose proof (munch_refl [] m2) as MU. pose proof (wmono_refl rsegs m2) as WM.
reenter MOK2.
step. if_true.
apply evt_RZ_done.
eapply (sh_join HIx) with (ty := JT_ARRAY) (tojs := tojs); sh_hyps;
[ split; [eapply model_vm_only_trans; [exact VM | exact VM2] | split; [exact PRES | split; [exact ST2 | split; [exact FR | exact G2]]]]
| apply fsv8_refl | intros Hf; exact Hf | exact DC | exact ERR2 | exact SRC8 | left; split; [reflexivity | exists A2; exact HP2] ].
-
change (Z.to_nat 48) with 48%nat in BLK.
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2.
pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI. cbn [hl_segs S4L] in MI.
pose proof (heap_blk S4L HIx _ _ _ _ q 48 HP2 ltac:(left; reflexivity)) as (_ & Hqal & Hqlo & Hqhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ q 48 HP2 ltac:(left; reflexivity)) as Hqimg. cbn [hl_img_lo hl_img_hi S4L] in Hqimg.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hqhi.
assert (Hqp : q <> p) by (intros ->; exact (fresh_not_in S4L HIx _ _ _ _ _ _ np HP2 INp1)).
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ q 48 p np HP2 ltac:(left; reflexivity) ltac:(right; exact INp1) Hqp) as Hdqp.
pose proof (munch_refl [(q, q + 48)] m2) as MU. pose proof (wmono_refl rsegs m2) as WM.
stash G2.
reenter MOK2.
step. if_falsex.
do 5 step. stepz. stepz. stepz. stepz. stepz.
do 5 step. step.
unstash G2.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
assert (G3 : jc_glob_P mx) by
(eapply jc_glob_P_outside; [exact G2 | exact MU | exact WM |]; repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd]; lia);
assert (HP3 : HEAPx A2 ((q, 48) :: BS ++ LB) mx md2) by heap_now S4L HIx HP2 MU WM MI
end.
extend_presD S4L HIx PRES MU WM HP2.
apply evt_RZ_done.
eapply (array_list_new2_cps HIx) with (LB := (q, 48) :: BS ++ LB) (lo := lo) (isz := 32);
[ exact HP3 | .. ]; try alloc_side.
intros ms3 md3 (m3 & A3 & al & e3 & RS3 & VM3 & ST3 & HPR3 & ERR3 & OUT3).
destruct RS3 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F3 & fc3 & -> & FS3 & FRM3).
cbn [hl_segs S4L] in *.
rewrite ?(unsigned_lit (bv_unsigned sp + -64)) in ST3 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -64)) in HPR3 by lia.
extend_presD_call PRES HPR3.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR3) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR3) in DC; [| left; cbn; lia]. cbn [hl_segs S4L] in DC.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR3) in SRC8; [| eapply client_range_block; [right; exact INp1 | lia | cbn; lia]]. cbn [hl_segs S4L] in SRC8.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR3) in BLK; [| eapply client_range_block; [left; reflexivity | lia | cbn; lia]]. cbn [hl_segs S4L] in BLK.
pose proof (jc_glob_P_pres _ _ _ _ HPR3 G3) as G4.
clear MU WM MI G2 G3.
destruct OUT3 as [(-> & HP4) | (Hal & ABS & AL & HP4)].
+
pose proof (heap_model_ok _ _ _ _ _ _ HP4) as MOK4.
pose proof (heap_mem_inv _ _ _ _ _ _ HP4) as MI. cbn [hl_segs S4L] in MI.
pose proof (munch_refl [(q, q + 48)] m3) as MU. pose proof (wmono_refl rsegs m3) as WM.
stash G4.
reenter MOK4.
step. step. stepz. step. if_false. step.
unstash G4.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
assert (HP5 : HEAPx A3 ((q, 48) :: BS ++ LB) mx md3) by heap_now S4L HIx HP4 MU WM MI;
assert (G5 : jc_glob_P mx) by
(eapply jc_glob_P_outside; [exact G4 | exact MU | exact WM |]; repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd]; lia)
end.
extend_presD S4L HIx PRES MU WM HP4.
clear BLK MU WM.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
pose proof (munch_refl [] mx) as MU; pose proof (wmono_refl rsegs mx) as WM end.

alloc_call (hi_free S4L HIx) S4L HIx HP5 MU WM MI.
{ right. exists 48. left. reflexivity. }
intros ms7 m7 md7 A7 r7 RS7 VM7 ST7 HPR7 ERR7 HP7. open_ret RS7. cbn [hl_segs S4L] in *.
rewrite lb_remove_head in HPR7, HP7.
rewrite ?(unsigned_lit (bv_unsigned sp + -64)) in ST7 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -64)) in HPR7 by lia.
extend_presD_call PRES HPR7.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR7) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR7) in DC; [| left; cbn; lia]. cbn [hl_segs S4L] in DC.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR7) in SRC8; [| eapply client_range_block; [exact INp1 | lia | cbn; lia]]. cbn [hl_segs S4L] in SRC8.
pose proof (jc_glob_P_pres _ _ _ _ HPR7 G5) as G7.
clear MU WM MI HP5 G5.
pose proof (heap_model_ok _ _ _ _ _ _ HP7) as MOK7.
pose proof (heap_mem_inv _ _ _ _ _ _ HP7) as MI. cbn [hl_segs S4L] in MI.
pose proof (munch_refl [] m7) as MU. pose proof (wmono_refl rsegs m7) as WM.
reenter MOK7.
step. step. step.
unstash SCB.
apply evt_RZ_done.
eapply (sh_join HIx) with (ty := JT_ARRAY) (tojs := tojs); sh_hyps;
[ split; [| split; [exact PRES | split; [exact ST7 | split; [exact FR | exact G7]]]]
| apply fsv8_of_fsaved; exact FS3 | exact FRM3 | exact DC | exact ERR7 | exact SRC8 | left; split; [reflexivity | exists A7; exact HP7] ].
eapply model_vm_only_trans; [exact VM|]. eapply model_vm_only_trans; [exact VM2|]. eapply model_vm_only_trans; [exact VM3 | exact VM7].
+
pose proof AL as (arr & size & ajunk & EBS & Hlen & Hsz & AHDR & AARR). subst ABS. cbn [app] in HP4.
pose proof (rw_cells_bound rsegs m3 al _ AHDR) as R2B. cbn [cells_size csize Nat.add] in R2B.
pose proof (heap_model_ok _ _ _ _ _ _ HP4) as MOK4.
pose proof (heap_mem_inv _ _ _ _ _ _ HP4) as MI. cbn [hl_segs S4L] in MI.
pose proof (heap_blk_img S4L HIx _ _ _ _ al 32 HP4 ltac:(left; reflexivity)) as Himg_al. cbn [hl_img_lo hl_img_hi S4L] in Himg_al.
pose proof (heap_blk_img S4L HIx _ _ _ _ arr (8 * size) HP4 ltac:(right; left; reflexivity)) as Himg_arr. cbn [hl_img_lo hl_img_hi S4L] in Himg_arr.
pose proof (heap_blk S4L HIx _ _ _ _ al 32 HP4 ltac:(left; reflexivity)) as (_ & Halal & Hallo & Halhi & _).
pose proof (heap_blk S4L HIx _ _ _ _ arr (8 * size) HP4 ltac:(right; left; reflexivity)) as (_ & Haal & Halo & Hahi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Halhi, Hahi.
assert (Halq : al <> q) by (intros ->; exact (fresh_not_in S4L HIx _ _ _ _ _ _ 48 HP4 ltac:(right; left; reflexivity))).
assert (Harrq : arr <> q).
{ intros ->. pose proof (heap_blk_nodup S4L HIx _ _ _ _ HP4) as ND. cbn in ND.
inversion ND as [|x l Hni Hnd]; subst. inversion Hnd as [|x' l' Hni' Hnd']; subst. apply Hni'. left. reflexivity. }
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ al 32 q 48 HP4 ltac:(left; reflexivity) ltac:(right; right; left; reflexivity) Halq) as Hdj1.
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ arr (8 * size) q 48 HP4 ltac:(right; left; reflexivity) ltac:(right; right; left; reflexivity) Harrq) as Hdj2.
clear AHDR AARR. stash AL. stash G4.
pose proof (munch_refl [(q, q + 48)] m3) as MU. pose proof (wmono_refl rsegs m3) as WM.
reenter MOK4.
step. step. step. step. if_truex.
unstash AL. unstash G4. unstash SCB.
apply evt_RZ_done.
jhdr_split BLK.
apply (proj1 (rw_cells_app rsegs _ q [_; _; _] _)) in BLK as X. destruct X as [QH QT]. cbn [cells_size csize Nat.add app] in QT.
lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ =>
assert (HP5 : HEAPx A3 ((al, 32) :: (arr, 8 * size) :: (q, 48) :: BS ++ LB) mx md3) by heap_now S4L HIx HP4 MU WM MI;
assert (G5 : jc_glob_P mx) by
(eapply jc_glob_P_outside; [exact G4 | exact MU | exact WM |]; repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd]; (clear - Hqimg; lia))
end.
extend_presD S4L HIx PRES MU WM HP4.
eapply (sh_join HIx) with (ty := JT_ARRAY) (tojs := tojs); sh_hyps;
[ split; [| split; [exact PRES | split; [exact ST3 | split; [exact FR | exact G5]]]]
| apply fsv8_of_fsaved; exact FS3 | exact FRM3 | exact DC | exact ERR3 | exact SRC8 | ].
{ eapply model_vm_only_trans; [exact VM|]. eapply model_vm_only_trans; [exact VM2 | exact VM3]. }
right. split; [exact Hq|]. exists A3, [(q, 48); (al, 32); (arr, 8 * size)], 48, (fn_arr_to_json_string S4F).
split; [eapply (heap_perm S4L HIx); [exact HP5 | perm] |].
split; [left; reflexivity|]. split; [lia|]. split; [exact QH|].
intros m' QH' MU' WM'. eapply (SCB m' q al).
* unfold jhdr_cells. cbn [app].
apply (proj2 (rw_cells_app rsegs m' q [_; _; _] _)). split; [exact QH'|]. cbn [cells_size csize Nat.add app].
eapply (rw_cells_transport rsegs); [exact QT | exact MU' | exact WM' |]. cbn. lia.
* eapply (alist_agree rsegs S4F); [exact AL | | apply incl_refl].
eapply agree_on_trans.
-- eapply (agree_of_munch rsegs); [exact MU | exact WM |].
intros b k Hb. cbn in Hb. cbn. destruct Hb as [Hb | [Hb | Hb]]; [injection Hb as <- <- | injection Hb as <- <- | destruct Hb]; lia.
-- eapply (agree_of_munch rsegs); [exact MU' | exact WM' |].
intros b k Hb. cbn in Hb. cbn. destruct Hb as [Hb | [Hb | Hb]]; [injection Hb as <- <- | injection Hb as <- <- | destruct Hb]; (clear - LO LOS SPD Halhi Hdj1 Hahi Hdj2; lia).
Qed.

End ShallowP2.

End RC__1.
