(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB.Top Require TopUbTac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qc3B.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc3B. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZDE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZDE. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.Bytes. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Lib.SepCache.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qfw3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfw3.Mq2.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QjDH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDH.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QmZZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmZZ.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UC8c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UC8c.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6WR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6WR. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6WR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6WR.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QrPc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QrPc.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QYIF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYIF.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UvXs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UvXs.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uc8V.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uc8V.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QBGG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBGG.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q7T7.
Import ListNotations. Unset Keyed Unification. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Ltac if_lit :=
lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
let v := eval vm_compute in c in change (if c then a else b) with (if v then a else b); cbv iota
end. Ltac mkr__if_lit_0 := lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
let v := eval vm_compute in c in change (if c then a else b) with (if v then a else b); cbv iota
end.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Ltac bstep := TopUbTac.ub_skip; step. Ltac bstepz := TopUbTac.ub_skip; stepz.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma first_nul_split2 : forall (pre post : list byte),
exists str rest, pre ++ Z_to_bv 8 0 :: post = str ++ Z_to_bv 8 0 :: rest /\ ~ In (Z_to_bv 8 0) str /\ (length str <= length pre)%nat.
Proof.
induction pre as [|b pre IH]; intros post.
- exists [], post. split; [reflexivity|]. split; [intros H; exact H | cbn; lia].
- destruct (Z.eq_dec (bv_unsigned b) 0) as [E|NE].
+ exists [], (pre ++ Z_to_bv 8 0 :: post). split; [| split; [intros H; exact H | cbn; lia]].
change (b :: (pre ++ Z_to_bv 8 0 :: post) = Z_to_bv 8 0 :: (pre ++ Z_to_bv 8 0 :: post)). f_equal. apply bv_eq. rewrite E. reflexivity.
+ destruct (IH post) as (str & rest & E2 & Hn & Hl). exists (b :: str), rest.
split; [change (b :: (pre ++ Z_to_bv 8 0 :: post) = b :: (str ++ Z_to_bv 8 0 :: rest)); rewrite E2; reflexivity|].
split; [| cbn; lia]. intros [H|H]; [| exact (Hn H)]. apply NE. rewrite H. reflexivity.
Qed.

#[using="Type"] Lemma bytes_at_cstr_prefix2 : forall segs m A (str str0 rest0 tail : list byte),
bytes_at segs m A (str ++ [Z_to_bv 8 0] ++ tail) -> str ++ Z_to_bv 8 0 :: tail = str0 ++ Z_to_bv 8 0 :: rest0 ->
bytes_at segs m A (str0 ++ [Z_to_bv 8 0]).
Proof.
intros segs m A str str0 rest0 tail B E.
change (str ++ [Z_to_bv 8 0] ++ tail) with (str ++ ([Z_to_bv 8 0] ++ tail)) in B. cbn [app] in B. rewrite E in B.
replace (str0 ++ Z_to_bv 8 0 :: rest0) with ((str0 ++ [Z_to_bv 8 0]) ++ rest0) in B by (rewrite <- app_assoc; reflexivity).
apply bytes_at_app in B as [B _]. exact B.
Qed.

#[using="Type"] Lemma le8_lbw8 : forall bs : list byte, length bs = 8%nat -> le8 (le_bytes_to_word bs) = bs.
Proof.
intros bs Hl. unfold le8, word_to_le_bytes, le_bytes_to_word.
rewrite Z_to_bv_unsigned.
assert (R : 0 <= bytes_le_to_Z bs < 2^64).
{ rewrite bytes_le_to_Z_le_val. pose proof (le_val_range _ (bytes_ok_map bs)) as H. rewrite length_map, Hl in H. cbn in H. lia. }
change (bv_wrap 64 ?z) with (z mod 2^64). rewrite Z.mod_small by lia.
rewrite <- Hl. apply Z_to_le_bytes_to_Z.
Qed.

#[using="Type"] Lemma rw_cells_junk16 : forall segs m A (j : list byte) rest,
rw_cells segs m A (CB 16 j :: rest) ->
rw_cells segs m A (CB 8 (firstn 8 j) :: C8 (le_bytes_to_word (skipn 8 j)) :: rest).
Proof.
intros segs m A j rest H.
assert (L : length j = 16%nat) by (destruct H as [[[Hwf _] _] _]; exact Hwf).
apply (rw_cells_recast_prefix segs m A [CB 16 j] [CB 8 (firstn 8 j); C8 (le_bytes_to_word (skipn 8 j))] rest); [exact H | | |].
- cbn. split; [rewrite length_firstn; lia | exact (conj I I)].
- cbn [cells_bytes cbytes app]. rewrite le8_lbw8 by (rewrite length_skipn; lia). rewrite ?app_nil_r. rewrite firstn_skipn. reflexivity.
- reflexivity.
Qed.
End RC__1.

Ltac fs_tail := intros k Hk; cbn [FSAVED In] in Hk; repeat (destruct Hk as [<- | Hk]); [..| destruct Hk]; rewrite ?freg_get_other by (vm_compute; reflexivity); reflexivity.
Ltac exit_now EXIT XHPR XJO XHP MOK :=
apply evt_RZ_done; eapply EXIT;
[ eassumption | eassumption | first [apply fsaved_refl | fs_tail] | intros _; assumption | exact MOK | apply model_vm_only_refl
| apply XHPR; assumption | eassumption | assumption | apply XJO; assumption | apply XHP; assumption ].
Lemma bword_eqb0 : forall b : bool, bv_eqb (bword b) (Z_to_bv 64 0) = negb b.
Proof. intros []; vm_compute; reflexivity. Qed.
Ltac fp_lit :=
repeat match goal with
| |- context [Q7T7.wkey ?c] => TopUbTac.ub_closed c; let v := eval vm_compute in (Q7T7.wkey c) in change (Q7T7.wkey c) with v
| H : context [Q7T7.wkey ?c] |- _ => TopUbTac.ub_closed c; let v := eval vm_compute in (Q7T7.wkey c) in change (Q7T7.wkey c) with v in H
end.
Ltac fp_side := first [assumption | vm_compute; reflexivity].
Ltac fp_hyp H :=
rewrite ?bword_eqb0, ?Bool.negb_involutive in H;
lazymatch type of H with negb _ = true => apply Bool.negb_true_iff in H | _ => idtac end;
first [rewrite Q7T7.flt_d_key in H by fp_side | rewrite Q7T7.fle_d_key in H by fp_side];
first [apply Z.ltb_ge in H | apply Z.ltb_lt in H | apply Z.leb_gt in H | apply Z.leb_le in H];
fp_lit.
Ltac fp_chk :=
lazymatch goal with
| |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
replace c with false; [cbv iota | symmetry; rewrite bword_eqb0; apply Bool.negb_false_iff;
rewrite Q7T7.flt_d_key by fp_side; apply Z.ltb_lt; fp_lit; lia]
end.
Section RC__2. Context {RC__ : Q6q3.RunConsts}.

Section GetNumP.
Variable HIx : heap_iface S4L.
Notation HEAPx := (HEAP S4L HIx).
Hypothesis HT62 : hi_top S4L HIx < 2^62.

Definition gi64_c1 := Eval vm_compute in match image_bytes rsegs 0x133f8 8 with Some bs => bs | None => [] end.
Definition gi64_c2 := Eval vm_compute in match image_bytes rsegs 0x13470 8 with Some bs => bs | None => [] end.
#[using="Type"] Lemma gi64_ro : forall m, mem_inv rsegs m -> ro_cells rsegs m 0x133f8 [CB 8 gi64_c1] /\ ro_cells rsegs m 0x13470 [CB 8 gi64_c2].
Proof.
intros m MI. split.
- change 8%nat with (length gi64_c1). apply ro_cells_image; [exact MI | vm_compute; reflexivity | lia | ]. change (Z.of_nat (length gi64_c1)) with 8%Z. lia.
- change 8%nat with (length gi64_c2). apply ro_cells_image; [exact MI | vm_compute; reflexivity | lia | ]. change (Z.of_nat (length gi64_c2)) with 8%Z. lia.
Qed.
Definition gi64_c3 := Eval vm_compute in match image_bytes rsegs 0x13490 8 with Some bs => bs | None => [] end.
#[using="Type"] Lemma gi64_ro3 : forall m, mem_inv rsegs m -> ro_cells rsegs m 0x13490 [CB 8 gi64_c3].
Proof.
intros m MI. change 8%nat with (length gi64_c3). apply ro_cells_image; [exact MI | vm_compute; reflexivity | lia | ]. change (Z.of_nat (length gi64_c3)) with 8%Z. lia.
Qed.

#[using="HT62"] Theorem get_int64_P : jo_get_num_stmt S4L HIx S4F 0x25a5c 448.
Proof.
unfold jo_get_num_stmt. intros until errv. intros (HP & ST & LO & LOS & SPA & HT & ERR & TP & RA) JO FRM A0 K.
cbn [hl_segs hl_tp S4L] in *.
unfold_consts. word_range sp SPR. subst a0 tp.
change (490496 - 164) with 490332 in ERR.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (wmono_refl rsegs m) as WM.
destruct (gi64_ro m MI) as [RO1 RO2]. pose proof (gi64_ro3 m MI) as RO3.
pose proof (heap_canary S4L HIx _ _ _ _ HP) as (g & CAN1 & CAN2 & _). cbn [hl_got_guard hl_guard hl_segs S4L] in CAN1, CAN2.
carve_frame 32%nat ST.
pose proof (munch_refl [(lo, bv_unsigned sp); (490332, 490336)] m) as MU.

assert (EXIT : forall (m1 : word -> option byte) (md1 : Model) (F1 : bvmap 5 word) (fc1 : bv 32)
(xra xt0 xt1 xt2 xs0 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word) (j8 : list byte) (jw e1 : word),
rw_cells rsegs m1 (bv_unsigned sp + -32) [CB 8 j8; C8 jw; C8 s0; C8 ra] ->
stk rsegs m1 lo (bv_unsigned sp + -32) ->
fsaved F F1 -> (frm0 fc -> frm0 fc1) ->
model_ok md1 -> model_vm_only md md1 -> heap_pres S4L LB (bv_unsigned sp) m m1 ->
rw_cells rsegs m1 490332 [C4 e1] -> mem_inv rsegs m1 ->
jopt rsegs S4F s m1 BS p -> HEAPx A (BS ++ LB) m1 md1 ->
realizes rsegs (mkCfg (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -32)) gp (Z_to_bv 64 490496) xt0 xt1 xt2 xs0 s1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
F1 (Z_to_bv 64 0x25ba0) fc1 None m1 (seg_rom rsegs)) md1) T).
{ intros m1 md1 F1 fc1 xra xt0 xt1 xt2 xs0 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 j8 jw e1 FR1 ST1 FS1 FRM1 MOK1 VM1 HPR1 ERR1 MI1 JO1 HP1.
clear ST MI WM MU FR RO1 RO2 CAN1 CAN2.
pose proof (munch_refl [] m1) as MU. pose proof (wmono_refl rsegs m1) as WM.
apply rz_evt; [exact MOK1|].
bstep. bstep. bstep. bstep.
release_frame FR1 ST1 (bv_unsigned sp).
bstep.
apply evt_RZ_done. eapply (K _ md1 m1 (bv_unsigned xa1)).
- split; [| split; [exact VM1 | split; [exact ST1 | split; [exact HPR1 | exists e1; exact ERR1]]]].
rewrite Z_to_bv_bv_unsigned. apply ret_statew_intro; [exact FS1 | exact FRM1].
- exact JO1.
- exact HP1. }

assert (XHPR : forall mX, munch [(lo, bv_unsigned sp); (490332, 490336)] m mX -> wmono rsegs m mX -> heap_pres S4L LB (bv_unsigned sp) m mX).
{ intros mX MUX WMX. eapply (heap_pres_of_munch S4L LB (bv_unsigned sp)); [exact MUX | exact WMX |].
eapply (client_outside S4L HIx); [exact HP | intros b Hb; apply in_or_app; right; exact Hb | clia |].
apply Forall_cons; [cbn [fst snd]; left; clia |]. apply Forall_cons; [cbn [fst snd]; right; right; intros; cbn; lia | apply Forall_nil]. }
assert (XHP : forall mX, munch [(lo, bv_unsigned sp); (490332, 490336)] m mX -> wmono rsegs m mX -> mem_inv rsegs mX -> HEAPx A (BS ++ LB) mX md).
{ intros mX MUX WMX MIX. eapply (heap_frame S4L HIx); [exact HP | | exact WMX | exact MIX].
eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HP MUX). solve_frameW. }
assert (XJO : forall mX, munch [(lo, bv_unsigned sp); (490332, 490336)] m mX -> wmono rsegs m mX -> jopt rsegs S4F s mX BS p).
{ intros mX MUX WMX. destruct s as [sh|]; [| exact JO]. destruct JO as [Hp J]. split; [exact Hp|].
eapply jval_agree; [exact J | | apply incl_refl]. eapply agree_of_munch; [exact MUX | exact WMX |].
intros a k Hin. pose proof (heap_blk S4L HIx _ _ _ _ a k HP ltac:(apply in_or_app; left; exact Hin)) as (Hk & _ & _ & Hhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ a k HP ltac:(apply in_or_app; left; exact Hin)) as Himg. cbn [hl_img_lo hl_img_hi S4L] in Himg.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hhi. cbn. lia. }
apply rz_evt; [exact MOK|].
bstep. bstep. bstep. bstep. bstep. bstep. bstep. bstep. bstepz.
apply rw_cells_junk16 in FR.
bstep.
destruct s as [sh|].
2:{  destruct JO as [Hp _]. rewrite Hp in *. if_truex. bstep. bstep.
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
apply (rw_cells_transport rsegs [(lo, bv_unsigned sp); (490332, 490336)] m mX) in HDR; [| exact MU | exact WM | cbn [disjoint_from]; rewrite SZ; clia] end.
pose proof (jtype_range sh) as JR.
bstep. rewrite sx32_small by lia. bstep. bstep.
destruct sh as [|u| |h|kids|kids]; cbn [jtype] in *; unfold JT_BOOLEAN, JT_DOUBLE, JT_INT, JT_STRING, JT_OBJECT, JT_ARRAY in *; if_lit.
-  bstep. bstep. if_lit.
destruct J as (pb_ & PBS & REST & EBS & OPB & (b & junk_ & ER & CELLS)). cbn [hl_segs S4L] in CELLS. unfold jhdr_cells in CELLS. cbn [app] in CELLS.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
apply (rw_cells_transport rsegs [(lo, bv_unsigned sp); (490332, 490336)] m mX) in CELLS; [| exact MU | exact WM | cbn [disjoint_from]; cbn; clia] end.
bstep. bstep.
exit_now EXIT XHPR XJO XHP MOK.
-  bstep. bstep. if_lit. bstep. bstep. if_lit.
destruct J as (pb_ & PBS & REST & EBS & OPB & J). cbn [hl_segs S4L] in J.
assert (CELLS : exists tojs' udel' ud' bits, rw_cells rsegs m p (jhdr_cells 2 1 tojs' pb_ udel' ud' ++ [C8 bits])).
{ destruct u; [destruct J as (bits & ud_ & udn & uds & _ & _ & C & _) | destruct J as (bits & _ & _ & C)]; do 4 eexists; exact C. }
clear J. destruct CELLS as (tojs' & udel' & ud' & bits & CELLS). unfold jhdr_cells in CELLS. cbn [app] in CELLS.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
apply (rw_cells_transport rsegs [(lo, bv_unsigned sp); (490332, 490336)] m mX) in CELLS; [| exact MU | exact WM | cbn [disjoint_from]; cbn; clia] end.

bstep. bstep. bstep. bstep. bstep.
if_cases Hc1.
+  bstep. bstep. bstep. bstep. bstep.
exit_now EXIT XHPR XJO XHP MOK.
+  bstep. bstep. bstep. bstep.
if_cases Hc2.
*  bstep. bstep. bstep. bstep. bstep. bstep. bstep.
if_cases Hc3.
--  pose proof (Q7T7.nan_test_false bits Hc3) as NX. fp_hyp Hc1. fp_hyp Hc2. step. step. step. step. fp_chk. step. step. fp_chk. step. exit_now EXIT XHPR XJO XHP MOK.
--  bstep. bstep. bstep. bstep. bstep. exit_now EXIT XHPR XJO XHP MOK.
*  bstep. bstep. bstep. bstep. bstep. bstep. exit_now EXIT XHPR XJO XHP MOK.
-  bstep. bstep. if_lit. bstep. bstep. if_lit.
destruct J as (pb_ & PBS & REST & EBS & OPB & (cty & v & junk_ & ER & Hcty & CELLS)). cbn [hl_segs S4L] in CELLS. unfold jhdr_cells in CELLS. cbn [app] in CELLS.
pose proof (heap_blk S4L HIx _ _ _ _ p 56 HP ltac:(rewrite EBS, ER; cbn; left; reflexivity)) as (_ & _ & _ & Hphi56 & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hphi56.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
apply (rw_cells_transport rsegs [(lo, bv_unsigned sp); (490332, 490336)] m mX) in CELLS; [| exact MU | exact WM | cbn [disjoint_from]; cbn; clia] end.
bstep. rewrite sx32_small by lia. bstep. bstep.
destruct Hcty as [-> | ->]; if_lit.
+  bstep. if_lit. bstep. bstep. exit_now EXIT XHPR XJO XHP MOK.
+  bstep. bstep.
if_cases Hc4.
* exit_now EXIT XHPR XJO XHP MOK.
* bstep. bstep. bstep. bstep. bstep. exit_now EXIT XHPR XJO XHP MOK.
-
bstep. bstep. if_lit.
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
apply (rw_cells_transport rsegs [(lo, bv_unsigned sp); (490332, 490336)] m mX) in LEN1; [| exact MU | exact WM | cbn [disjoint_from]; cbn; clia];
apply (bytes_at_transport rsegs [(lo, bv_unsigned sp); (490332, 490336)] m mX) in BY; [| exact MU | cbn [disjoint_from]; rewrite length_app; cbn [length]; clia] end.

eassert (GOAL : evt rsegs (RZ rsegs md T) _).
2:{ destruct ALT as [[Hl ETX] | [Hl ->]].
- clear LEN2. bstep. bstep. bstep. if_truex. rewrite <- ETX. exact GOAL.
- lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
apply (rw_cells_transport rsegs [(lo, bv_unsigned sp); (490332, 490336)] m mX) in LEN2; [| exact MU | exact WM | cbn [disjoint_from]; cbn; clia] end.
bstep. bstep. bstep. if_falsex. bstep. exact GOAL. }

bstep. bstep.
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
{ exact FRr. } { lia. } { lia. } { Z.div_mod_to_equations; lia. } { eassumption. } { reflexivity. }
{ unfold GOT_GUARD, GUARD. exact CAN1. } { unfold GUARD. exact CAN2. } { eassumption. }
{ clia. } { lia. } { lia. } { vm_compute; reflexivity. } { assumption. }
cbv beta. change (0x77c00 - 164) with 490332 in *.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
match goal with H : mem_inv rsegs m5 |- _ => rename H into MI5 end.
match goal with H : stk rsegs m5 lo _ |- _ => rename H into ST5 end.
match goal with H : rw_cells rsegs m5 (bv_unsigned sp + -24) [C8 ?v] |- _ => rename H into FRr5 end.
match goal with H : rw_cells rsegs m5 490332 [C4 ?e] |- _ => rename H into ERR5 end.

bstep. bstep. bstep. bstep. bstep.

lazymatch type of FRr5 with rw_cells _ _ _ [C8 ?vv] =>
lazymatch type of FRa with rw_cells _ _ _ [CB 8 ?jj] =>
assert (FR5 : rw_cells rsegs m5 (bv_unsigned sp + -32) [CB 8 jj; C8 vv; C8 s0; C8 ra]) end end.
{ apply (proj2 (rw_cells_app rsegs m5 _ [CB 8 _] _)). split; [exact FRa|]. cbn [cells_size csize Nat.add].
apply (proj2 (rw_cells_app rsegs m5 _ [C8 _] _)). split.
- change (bv_unsigned sp + -32 + Z.of_nat 8) with (bv_unsigned sp + -32 + 8). replace (bv_unsigned sp + -32 + 8) with (bv_unsigned sp + -24) by lia. exact FRr5.
- cbn [cells_size csize Nat.add]. change (bv_unsigned sp + -32 + Z.of_nat 8 + Z.of_nat 8) with (bv_unsigned sp + -32 + 8 + 8).
replace (bv_unsigned sp + -32 + 8 + 8) with (bv_unsigned sp + -16) by lia. exact FRc. }
clear FRa FRr5 FRc.
apply evt_RZ_done. eapply EXIT;
[ exact FR5 | exact ST5 | apply fsaved_refl | intros Hf; exact Hf | exact MOK | apply model_vm_only_refl
| apply XHPR; assumption | exact ERR5 | exact MI5 | apply XJO; assumption | apply XHP; assumption ].
-  bstep. bstep. if_lit. bstep. bstep. if_lit. exit_now EXIT XHPR XJO XHP MOK.
-  bstep. bstep. if_lit. bstep. bstep. if_lit. exit_now EXIT XHPR XJO XHP MOK.
Qed.
Definition gu64_c1 := Eval vm_compute in match image_bytes rsegs 0x133d8 8 with Some bs => bs | None => [] end.
#[using="Type"] Lemma gu64_ro : forall m, mem_inv rsegs m -> ro_cells rsegs m 0x133d8 [CB 8 gu64_c1] /\ True.
Proof.
intros m MI. split; [| exact I].
change 8%nat with (length gu64_c1). apply ro_cells_image; [exact MI | vm_compute; reflexivity | lia | ]. change (Z.of_nat (length gu64_c1)) with 8%Z. lia.
Qed.
Definition gu64_c2 := Eval vm_compute in match image_bytes rsegs 0x13390 8 with Some bs => bs | None => [] end.
#[using="Type"] Lemma gu64_ro2 : forall m, mem_inv rsegs m -> ro_cells rsegs m 0x13390 [CB 8 gu64_c2].
Proof.
intros m MI. change 8%nat with (length gu64_c2). apply ro_cells_image; [exact MI | vm_compute; reflexivity | lia | ]. change (Z.of_nat (length gu64_c2)) with 8%Z. lia.
Qed.

#[using="HT62"] Theorem get_uint64_P : jo_get_num_stmt S4L HIx S4F 0x25bc4 448.
Proof.
unfold jo_get_num_stmt. intros until errv. intros (HP & ST & LO & LOS & SPA & HT & ERR & TP & RA) JO FRM A0 K.
cbn [hl_segs hl_tp S4L] in *.
unfold_consts. word_range sp SPR. subst a0 tp.
change (490496 - 164) with 490332 in ERR.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (wmono_refl rsegs m) as WM.
destruct (gu64_ro m MI) as [RO1 _]. pose proof (gu64_ro2 m MI) as RO3.
pose proof (heap_canary S4L HIx _ _ _ _ HP) as (g & CAN1 & CAN2 & _). cbn [hl_got_guard hl_guard hl_segs S4L] in CAN1, CAN2.
carve_frame 32%nat ST.
pose proof (munch_refl [(lo, bv_unsigned sp); (490332, 490336)] m) as MU.

assert (EXIT : forall (m1 : word -> option byte) (md1 : Model) (F1 : bvmap 5 word) (fc1 : bv 32)
(xra xt0 xt1 xt2 xs0 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word) (j8 : list byte) (jw e1 : word),
rw_cells rsegs m1 (bv_unsigned sp + -32) [CB 8 j8; C8 jw; C8 s0; C8 ra] ->
stk rsegs m1 lo (bv_unsigned sp + -32) ->
fsaved F F1 -> (frm0 fc -> frm0 fc1) ->
model_ok md1 -> model_vm_only md md1 -> heap_pres S4L LB (bv_unsigned sp) m m1 ->
rw_cells rsegs m1 490332 [C4 e1] -> mem_inv rsegs m1 ->
jopt rsegs S4F s m1 BS p -> HEAPx A (BS ++ LB) m1 md1 ->
realizes rsegs (mkCfg (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -32)) gp (Z_to_bv 64 490496) xt0 xt1 xt2 xs0 s1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
F1 (Z_to_bv 64 0x25ce4) fc1 None m1 (seg_rom rsegs)) md1) T).
{ intros m1 md1 F1 fc1 xra xt0 xt1 xt2 xs0 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 j8 jw e1 FR1 ST1 FS1 FRM1 MOK1 VM1 HPR1 ERR1 MI1 JO1 HP1.
clear ST MI WM MU FR RO1 CAN1 CAN2.
pose proof (munch_refl [] m1) as MU. pose proof (wmono_refl rsegs m1) as WM.
apply rz_evt; [exact MOK1|].
bstep. bstep. bstep. bstep.
release_frame FR1 ST1 (bv_unsigned sp).
bstep.
apply evt_RZ_done. eapply (K _ md1 m1 (bv_unsigned xa1)).
- split; [| split; [exact VM1 | split; [exact ST1 | split; [exact HPR1 | exists e1; exact ERR1]]]].
rewrite Z_to_bv_bv_unsigned. apply ret_statew_intro; [exact FS1 | exact FRM1].
- exact JO1.
- exact HP1. }

assert (XHPR : forall mX, munch [(lo, bv_unsigned sp); (490332, 490336)] m mX -> wmono rsegs m mX -> heap_pres S4L LB (bv_unsigned sp) m mX).
{ intros mX MUX WMX. eapply (heap_pres_of_munch S4L LB (bv_unsigned sp)); [exact MUX | exact WMX |].
eapply (client_outside S4L HIx); [exact HP | intros b Hb; apply in_or_app; right; exact Hb | clia |].
apply Forall_cons; [cbn [fst snd]; left; clia |]. apply Forall_cons; [cbn [fst snd]; right; right; intros; cbn; lia | apply Forall_nil]. }
assert (XHP : forall mX, munch [(lo, bv_unsigned sp); (490332, 490336)] m mX -> wmono rsegs m mX -> mem_inv rsegs mX -> HEAPx A (BS ++ LB) mX md).
{ intros mX MUX WMX MIX. eapply (heap_frame S4L HIx); [exact HP | | exact WMX | exact MIX].
eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HP MUX). solve_frameW. }
assert (XJO : forall mX, munch [(lo, bv_unsigned sp); (490332, 490336)] m mX -> wmono rsegs m mX -> jopt rsegs S4F s mX BS p).
{ intros mX MUX WMX. destruct s as [sh|]; [| exact JO]. destruct JO as [Hp J]. split; [exact Hp|].
eapply jval_agree; [exact J | | apply incl_refl]. eapply agree_of_munch; [exact MUX | exact WMX |].
intros a k Hin. pose proof (heap_blk S4L HIx _ _ _ _ a k HP ltac:(apply in_or_app; left; exact Hin)) as (Hk & _ & _ & Hhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ a k HP ltac:(apply in_or_app; left; exact Hin)) as Himg. cbn [hl_img_lo hl_img_hi S4L] in Himg.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hhi. cbn. lia. }
apply rz_evt; [exact MOK|].
bstep. bstep. bstep. bstep. bstep. bstep. bstep. bstep. bstepz.
apply rw_cells_junk16 in FR.
bstep.
destruct s as [sh|].
2:{  destruct JO as [Hp _]. rewrite Hp in *. if_truex. bstep. bstep.
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
apply (rw_cells_transport rsegs [(lo, bv_unsigned sp); (490332, 490336)] m mX) in HDR; [| exact MU | exact WM | cbn [disjoint_from]; rewrite SZ; clia] end.
pose proof (jtype_range sh) as JR.
bstep. rewrite sx32_small by lia. bstep. bstep.
destruct sh as [|u| |h|kids|kids]; cbn [jtype] in *; unfold JT_BOOLEAN, JT_DOUBLE, JT_INT, JT_STRING, JT_OBJECT, JT_ARRAY in *; if_lit.
-  bstep. bstep. if_lit.
destruct J as (pb_ & PBS & REST & EBS & OPB & (b & junk_ & ER & CELLS)). cbn [hl_segs S4L] in CELLS. unfold jhdr_cells in CELLS. cbn [app] in CELLS.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
apply (rw_cells_transport rsegs [(lo, bv_unsigned sp); (490332, 490336)] m mX) in CELLS; [| exact MU | exact WM | cbn [disjoint_from]; cbn; clia] end.
bstep. bstep.
exit_now EXIT XHPR XJO XHP MOK.
-  bstep. bstep. if_lit. bstep. bstep. if_lit.
destruct J as (pb_ & PBS & REST & EBS & OPB & J). cbn [hl_segs S4L] in J.
assert (CELLS : exists tojs' udel' ud' bits, rw_cells rsegs m p (jhdr_cells 2 1 tojs' pb_ udel' ud' ++ [C8 bits])).
{ destruct u; [destruct J as (bits & ud_ & udn & uds & _ & _ & C & _) | destruct J as (bits & _ & _ & C)]; do 4 eexists; exact C. }
clear J. destruct CELLS as (tojs' & udel' & ud' & bits & CELLS). unfold jhdr_cells in CELLS. cbn [app] in CELLS.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
apply (rw_cells_transport rsegs [(lo, bv_unsigned sp); (490332, 490336)] m mX) in CELLS; [| exact MU | exact WM | cbn [disjoint_from]; cbn; clia] end.

bstep. bstep. bstep. bstep. bstep.
if_cases Hc1.
+  bstep. bstep. bstep. bstep.
exit_now EXIT XHPR XJO XHP MOK.
+  bstep. bstep. bstep.
if_cases Hc2.
*  bstep. bstep. bstep. bstep. exit_now EXIT XHPR XJO XHP MOK.
*  bstep. bstep. bstep. bstep. bstep. bstep. bstep.
if_cases Hc3.
--  pose proof (Q7T7.nan_test_false bits Hc3) as NX. fp_hyp Hc1. fp_hyp Hc2. step. step. step. step. fp_chk. step. step. fp_chk. step. step. exit_now EXIT XHPR XJO XHP MOK.
--  bstep. bstep. bstep. bstep. exit_now EXIT XHPR XJO XHP MOK.
-  bstep. bstep. if_lit. bstep. bstep. if_lit.
destruct J as (pb_ & PBS & REST & EBS & OPB & (cty & v & junk_ & ER & Hcty & CELLS)). cbn [hl_segs S4L] in CELLS. unfold jhdr_cells in CELLS. cbn [app] in CELLS.
pose proof (heap_blk S4L HIx _ _ _ _ p 56 HP ltac:(rewrite EBS, ER; cbn; left; reflexivity)) as (_ & _ & _ & Hphi56 & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hphi56.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
apply (rw_cells_transport rsegs [(lo, bv_unsigned sp); (490332, 490336)] m mX) in CELLS; [| exact MU | exact WM | cbn [disjoint_from]; cbn; clia] end.
bstep. rewrite sx32_small by lia. bstep. bstep.
destruct Hcty as [-> | ->]; if_lit.
+  bstep. if_lit. bstep. bstep.
if_cases Hc4.
* exit_now EXIT XHPR XJO XHP MOK.
* bstep. bstep. bstep. bstep. exit_now EXIT XHPR XJO XHP MOK.
+  bstep. exit_now EXIT XHPR XJO XHP MOK.
-
bstep. bstep. if_lit.
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
apply (rw_cells_transport rsegs [(lo, bv_unsigned sp); (490332, 490336)] m mX) in LEN1; [| exact MU | exact WM | cbn [disjoint_from]; cbn; clia];
apply (bytes_at_transport rsegs [(lo, bv_unsigned sp); (490332, 490336)] m mX) in BY; [| exact MU | cbn [disjoint_from]; rewrite length_app; cbn [length]; clia] end.

eassert (GOAL : evt rsegs (RZ rsegs md T) _).
2:{ destruct ALT as [[Hl ETX] | [Hl ->]].
- clear LEN2. bstep. bstep. bstep. if_truex. rewrite <- ETX. exact GOAL.
- lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
apply (rw_cells_transport rsegs [(lo, bv_unsigned sp); (490332, 490336)] m mX) in LEN2; [| exact MU | exact WM | cbn [disjoint_from]; cbn; clia] end.
bstep. bstep. bstep. if_falsex. bstep. exact GOAL. }

bstep. bstep.
apply rw_cells_app with (cs1 := [_]) in FR as [FRa FRb]. cbn [cells_size csize Nat.add] in FRb.
apply rw_cells_app with (cs1 := [_]) in FRb as [FRr FRc]. cbn [cells_size csize Nat.add] in FRc.
change (bv_unsigned sp + -32 + Z.of_nat 8) with (bv_unsigned sp + -32 + 8) in FRr, FRc.
change (bv_unsigned sp + -32 + 8 + Z.of_nat 8) with (bv_unsigned sp + -32 + 8 + 8) in FRc.
replace (bv_unsigned sp + -32 + 8 + 8) with (bv_unsigned sp + -16) in FRc by lia.
replace (bv_unsigned sp + -32 + 8) with (bv_unsigned sp + -24) in FRr by lia.
fold_mkR.
pose proof (json_parse_uint64_spec strtoull_spec) as PU. unfold parse_i64_stmt in PU.
lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
eapply evt_cut; [ eapply PU with (SP := bv_unsigned sp + -32) (A := TX) (R := bv_unsigned sp + -24) (lo := lo) (str := str0) (g := g)
| unfold parse_i64_post, parse_i64_W; post_call segs mm ] end.
all: clear PU.
{ rewrite unsigned_lit by lia. reflexivity. } { reflexivity. } { reflexivity. }
{ exact BY. } { exact NIN. } { lia. } { lia. }
{ exact FRr. } { lia. } { lia. } { Z.div_mod_to_equations; lia. } { eassumption. } { reflexivity. }
{ unfold GOT_GUARD, GUARD. exact CAN1. } { unfold GUARD. exact CAN2. } { eassumption. }
{ clia. } { lia. } { lia. } { vm_compute; reflexivity. } { assumption. }
cbv beta. change (0x77c00 - 164) with 490332 in *.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
match goal with H : mem_inv rsegs m5 |- _ => rename H into MI5 end.
match goal with H : stk rsegs m5 lo _ |- _ => rename H into ST5 end.
match goal with H : rw_cells rsegs m5 (bv_unsigned sp + -24) [C8 ?v] |- _ => rename H into FRr5 end.
match goal with H : rw_cells rsegs m5 490332 [C4 ?e] |- _ => rename H into ERR5 end.

bstep. bstep. bstep. bstep. bstep.

lazymatch type of FRr5 with rw_cells _ _ _ [C8 ?vv] =>
lazymatch type of FRa with rw_cells _ _ _ [CB 8 ?jj] =>
assert (FR5 : rw_cells rsegs m5 (bv_unsigned sp + -32) [CB 8 jj; C8 vv; C8 s0; C8 ra]) end end.
{ apply (proj2 (rw_cells_app rsegs m5 _ [CB 8 _] _)). split; [exact FRa|]. cbn [cells_size csize Nat.add].
apply (proj2 (rw_cells_app rsegs m5 _ [C8 _] _)). split.
- change (bv_unsigned sp + -32 + Z.of_nat 8) with (bv_unsigned sp + -32 + 8). replace (bv_unsigned sp + -32 + 8) with (bv_unsigned sp + -24) by lia. exact FRr5.
- cbn [cells_size csize Nat.add]. change (bv_unsigned sp + -32 + Z.of_nat 8 + Z.of_nat 8) with (bv_unsigned sp + -32 + 8 + 8).
replace (bv_unsigned sp + -32 + 8 + 8) with (bv_unsigned sp + -16) by lia. exact FRc. }
clear FRa FRr5 FRc.
apply evt_RZ_done. eapply EXIT;
[ exact FR5 | exact ST5 | apply fsaved_refl | intros Hf; exact Hf | exact MOK | apply model_vm_only_refl
| apply XHPR; assumption | exact ERR5 | exact MI5 | apply XJO; assumption | apply XHP; assumption ].
-  bstep. bstep. if_lit. bstep. bstep. if_lit. exit_now EXIT XHPR XJO XHP MOK.
-  bstep. bstep. if_lit. bstep. bstep. if_lit. exit_now EXIT XHPR XJO XHP MOK.
Qed.
End GetNumP.

End RC__2.
