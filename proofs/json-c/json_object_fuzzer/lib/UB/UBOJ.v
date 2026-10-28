(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB.Top Require TopUbTac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qc3B.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc3B. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qfw3.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QKQo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKQo.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6WR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6WR.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QrPc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QrPc.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qvbw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qvbw. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QYIF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYIF.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qx2n.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qx2n.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uy2A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uy2A. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UvMd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UvMd. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UdFq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UdFq.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QBGG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBGG.
Import ListNotations. Unset Keyed Unification. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr.
Open Scope Z_scope.

Ltac if_lit :=
lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
let v := eval vm_compute in c in change (if c then a else b) with (if v then a else b); cbv iota
end. Ltac mkr__if_lit_0 := lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
let v := eval vm_compute in c in change (if c then a else b) with (if v then a else b); cbv iota
end.

Ltac solve_FS1 :=
let k := fresh "k" in let Hk := fresh "Hk" in let NE := fresh "NE" in
intros k Hk NE; cbn [FSAVED In] in Hk;
repeat (destruct Hk as [<- | Hk]); [..| destruct Hk];
first [ exfalso; apply NE; reflexivity
| repeat (rewrite freg_get_other by (vm_compute; reflexivity)); reflexivity ].
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Ltac bstep := TopUbTac.ub_skip; step. Ltac bstepz := TopUbTac.ub_skip; stepz.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma first_nul_split' : forall (pre post : list byte),
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

#[using="Type"] Lemma bytes_at_cstr_prefix : forall segs m A (str str0 rest0 tail : list byte),
bytes_at segs m A (str ++ [Z_to_bv 8 0] ++ tail) -> str ++ Z_to_bv 8 0 :: tail = str0 ++ Z_to_bv 8 0 :: rest0 ->
bytes_at segs m A (str0 ++ [Z_to_bv 8 0]).
Proof.
intros segs m A str str0 rest0 tail B E.
change (str ++ [Z_to_bv 8 0] ++ tail) with (str ++ ([Z_to_bv 8 0] ++ tail)) in B. cbn [app] in B. rewrite E in B.
replace (str0 ++ Z_to_bv 8 0 :: rest0) with ((str0 ++ [Z_to_bv 8 0]) ++ rest0) in B by (rewrite <- app_assoc; reflexivity).
apply bytes_at_app in B as [B _]. exact B.
Qed.

#[using="Type"] Lemma lb_remove_zero' : forall L (HIx : heap_iface L) A LB m md, HEAP L HIx A LB m md -> lb_remove 0 LB = LB.
Proof.
intros L HIx A LB m md HP.
assert (H : forall b, In b LB -> blk_addr b <> 0).
{ intros [a n] Hin. cbn. pose proof (heap_blk L HIx _ _ _ _ a n HP Hin) as (_ & _ & Hlo & _). lia. }
clear HP. induction LB as [|[a n] LB IH]; [reflexivity|]. cbn.
destruct (Z.eqb_spec a 0) as [E|NE]; [exfalso; exact (H (a, n) ltac:(left; reflexivity) E)|].
f_equal. apply IH. intros b Hb. apply H. right. exact Hb.
Qed.

#[using="Type"] Lemma map_unsigned_bytes' : forall bs : list byte, map (Z_to_bv 8) (map bv_unsigned bs) = bs.
Proof. induction bs as [|b bs IH]; [reflexivity|]. cbn. rewrite IH. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

Section JoGetDoubleP.
Variable HIx : heap_iface S4L.
Notation HEAPx := (HEAP S4L HIx).
Hypothesis HT62 : hi_top S4L HIx < 2^62.

Hypothesis SCANH : scan_strtod_h_total_stmt.
Hypothesis STRTOD : rstrtod_total_stmt.

Definition GD_ENTRY_P : Z := 0x26220.
Definition GD_LCONV_P : Z := 0x65798.
Definition GD_DP_P : Z := 0x10eaf.
Definition GD_STK : Z := 64 + 8928.

#[using="HT62 SCANH STRTOD"] Theorem jo_get_double_P : jo_get_double_stmt S4L HIx S4F GD_ENTRY_P GD_STK GD_LCONV_P GD_DP_P.
Proof.
unfold jo_get_double_stmt, GD_ENTRY_P, GD_STK, GD_LCONV_P, GD_DP_P.
intros until errv. intros (HP & ST & LO & LOS & SPA & HT & ERR & TP & RA) JO FRM A0 LC DP K.
cbn [hl_segs hl_tp S4L] in *.
unfold_consts. word_range sp SPR. subst a0 tp.
assert (FRMfp : Qc3B.frm0 fc) by exact FRM. change (490496 - 164) with 490332 in ERR.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (wmono_refl rsegs m) as WM.

carve_frame 64%nat ST.
pose proof (munch_refl [(lo, bv_unsigned sp); (490332, 490336)] m) as MU.
assert (EXIT : forall (m1 : word -> option byte) (md1 : Model) (A1 : AS S4L HIx) (F1 : bvmap 5 word) (fc1 : bv 32)
(xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xt3 xt4 xt5 xt6 : word) (ej : word) (e1 : word),
rw_cells rsegs m1 (bv_unsigned sp + -64) [C8 ej; C8 (reg_get F 8); C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
stk rsegs m1 lo (bv_unsigned sp + -64) ->
(forall k, In k FSAVED -> k <> 8 -> reg_get F1 (Z_to_bv 5 k) = reg_get F (Z_to_bv 5 k)) ->
(frm0 fc -> frm0 fc1) ->
model_ok md1 -> model_vm_only md md1 -> heap_pres S4L LB (bv_unsigned sp) m m1 ->
rw_cells rsegs m1 490332 [C4 e1] -> mem_inv rsegs m1 ->
jopt rsegs S4F s m1 BS p -> HEAPx A1 (BS ++ LB) m1 md1 ->
realizes rsegs (mkCfg (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -64)) gp (Z_to_bv 64 490496) xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
F1 (Z_to_bv 64 0x26398) fc1 None m1 (seg_rom rsegs)) md1) T).
{ intros m1 md1 A1 F1 fc1 xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xt3 xt4 xt5 xt6 ej e1 FR1 ST1 FS1 FRM1 MOK1 VM1 HPR1 ERR1 MI1 JO1 HP1.
clear ST MI WM MU FR.
pose proof (munch_refl [] m1) as MU. pose proof (wmono_refl rsegs m1) as WM.
apply rz_evt; [exact MOK1|].
bstep. bstep. bstep. bstep. bstep. bstep. bstep. bstep. bstep.
release_frame FR1 ST1 (bv_unsigned sp).
apply evt_RZ_done. eapply (K _ md1 m1 (bv_unsigned xa0)).
- split; [| split; [exact VM1 | split; [exact ST1 | split; [exact HPR1 | exists e1; exact ERR1]]]].
rewrite Z_to_bv_bv_unsigned.
apply ret_statew_intro; [| exact FRM1].
intros k Hk. destruct (Z.eq_dec k 8) as [-> | NE].
+ rewrite freg_get_same by (vm_compute; reflexivity). reflexivity.
+ rewrite freg_get_other. { apply FS1; [exact Hk | exact NE]. }
cbn [FSAVED In] in Hk.
repeat (destruct Hk as [<- | Hk]); [..| destruct Hk]; first [vm_compute; reflexivity | exfalso; apply NE; reflexivity].
- exact JO1.
- exists A1. exact HP1. }

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
bstep. bstep.
destruct s as [sh|].
2:{  destruct JO as [Hp _]. rewrite Hp in *. if_truex. step.
apply evt_RZ_done. eapply EXIT; [eassumption | eassumption | | intros Hf; exact Hf | exact MOK | apply model_vm_only_refl | apply XHPR; assumption | exact ERR | exact MI | apply XJO; assumption | apply XHP; assumption].
solve_FS1. }
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
bstep. bstep. bstep. step.
apply evt_RZ_done. eapply EXIT; [eassumption | eassumption | solve_FS1 | intros _; assumption | exact MOK | apply model_vm_only_refl
| apply XHPR; assumption | eassumption | assumption | apply XJO; assumption | apply XHP; assumption].
-  bstep. bstep. if_lit. bstep. bstep. if_lit.
destruct J as (pb_ & PBS & REST & EBS & OPB & J). cbn [hl_segs S4L] in J.
assert (CELLS : exists tojs' udel' ud' bits, rw_cells rsegs m p (jhdr_cells 2 1 tojs' pb_ udel' ud' ++ [C8 bits])).
{ destruct u; [destruct J as (bits & ud_ & udn & uds & _ & _ & C & _) | destruct J as (bits & _ & _ & C)]; do 4 eexists; exact C. }
clear J. destruct CELLS as (tojs' & udel' & ud' & bits & CELLS). unfold jhdr_cells in CELLS. cbn [app] in CELLS.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
apply (rw_cells_transport rsegs [(lo, bv_unsigned sp); (490332, 490336)] m mX) in CELLS; [| exact MU | exact WM | cbn [disjoint_from]; cbn; clia] end.
bstep. bstep. step.
apply evt_RZ_done. eapply EXIT; [eassumption | eassumption | solve_FS1 | intros _; assumption | exact MOK | apply model_vm_only_refl
| apply XHPR; assumption | eassumption | assumption | apply XJO; assumption | apply XHP; assumption].
-  bstep. bstep. if_lit.
destruct J as (pb_ & PBS & REST & EBS & OPB & (cty & v & junk_ & ER & Hcty & CELLS)). cbn [hl_segs S4L] in CELLS. unfold jhdr_cells in CELLS. cbn [app] in CELLS.
pose proof (heap_blk S4L HIx _ _ _ _ p 56 HP ltac:(rewrite EBS, ER; cbn; left; reflexivity)) as (_ & _ & _ & Hphi56 & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hphi56.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
apply (rw_cells_transport rsegs [(lo, bv_unsigned sp); (490332, 490336)] m mX) in CELLS; [| exact MU | exact WM | cbn [disjoint_from]; cbn; clia] end.
bstep. rewrite sx32_small by lia. bstep. bstep.
destruct Hcty as [-> | ->]; if_lit.
+ bstep. if_lit. bstep. bstep. bstep. step.
apply evt_RZ_done. eapply EXIT; [eassumption | eassumption | solve_FS1 | intros _; assumption | exact MOK | apply model_vm_only_refl
| apply XHPR; assumption | eassumption | assumption | apply XJO; assumption | apply XHP; assumption].
+ bstep. bstep. bstep. step.
apply evt_RZ_done. eapply EXIT; [eassumption | eassumption | solve_FS1 | intros _; assumption | exact MOK | apply model_vm_only_refl
| apply XHPR; assumption | eassumption | assumption | apply XJO; assumption | apply XHP; assumption].
-
bstep. bstep. try if_lit. bstep. bstep. try if_lit.
pose proof J as J0. destruct J as (pb_ & PBS & REST & EBS & OPB & J). cbn [hl_segs S4L] in J, OPB.

assert (TXT : exists (TX TB TBN len : Z) (str0 rest0 : list byte) (lencell : list cell),
In (TB, TBN) BS /\ TB <= TX /\ TX + Z.of_nat (length str0) + 1 <= TB + TBN /\ ~ In (Z_to_bv 8 0) str0 /\
Z.of_nat (length str0) < 2^31 /\
bytes_at rsegs m TX (str0 ++ [Z_to_bv 8 0]) /\
rw_cells rsegs m (p + 40) (C8 (Z_to_bv 64 len) :: lencell) /\ -2^31 < len < 2^31 /\
((0 <= len /\ TX = p + 48) \/ (len < 0 /\ lencell = [C8 (Z_to_bv 64 TX)])) /\
(exists pn, In (p, pn) BS /\ 56 <= pn)).
{ destruct h.
- destruct J as (len & pd & pdn & str & junk2 & ER & Hlen & Hstr & Hpdn & C1 & C2).
destruct (first_nul_split' str junk2) as (str0 & rest0 & E0 & NIN & L0).
exists pd, pd, pdn, len, str0, rest0, [C8 (Z_to_bv 64 pd)].
split; [rewrite EBS, ER; cbn; right; left; reflexivity|]. split; [lia|]. split; [lia|]. split; [exact NIN|]. split; [lia|].
split. { apply rw_cells_bytes_at in C2. cbn [cells_bytes cbytes app] in C2. rewrite app_nil_r in C2.
eapply bytes_at_cstr_prefix; [exact C2 | exact E0]. }
split. { unfold jhdr_cells in C1. cbn [app] in C1. apply rw_cells_app with (cs1 := [_;_;_;_;_;_]) in C1 as [_ C1]. cbn [cells_size csize Nat.add] in C1. change (p + Z.of_nat 40) with (p + 40) in C1. exact C1. }
split; [lia|]. split; [right; split; [lia | reflexivity]|]. exists 56. split; [rewrite EBS, ER; cbn; left; reflexivity | lia].
- destruct J as (len & str & junkS & ER & Hlen & Hstr & C1).
destruct (first_nul_split' str junkS) as (str0 & rest0 & E0 & NIN & L0).
exists (p + 48), p, (str_objsize len), len, str0, rest0, [CB (Z.to_nat (str_objsize len - 48)) (str ++ [Z_to_bv 8 0] ++ junkS)].
split; [rewrite EBS, ER; cbn; left; reflexivity|]. split; [lia|]. split; [unfold str_objsize; lia|]. split; [exact NIN|]. split; [lia|].
unfold jhdr_cells in C1. cbn [app] in C1. apply rw_cells_app with (cs1 := [_;_;_;_;_;_]) in C1 as [_ C1]. cbn [cells_size csize Nat.add] in C1. change (p + Z.of_nat 40) with (p + 40) in C1.
split. { pose proof C1 as C2. apply rw_cells_app with (cs1 := [_]) in C2 as [_ C2]. cbn [cells_size csize Nat.add] in C2.
apply rw_cells_bytes_at in C2. cbn [cells_bytes cbytes app] in C2. rewrite app_nil_r in C2.
change (p + 40 + Z.of_nat 8) with (p + 40 + 8) in C2. replace (p + 40 + 8) with (p + 48) in C2 by lia. eapply bytes_at_cstr_prefix; [exact C2 | exact E0]. }
split; [exact C1|]. split; [lia|]. split; [left; split; [lia | reflexivity]|]. exists (str_objsize len). split; [rewrite EBS, ER; cbn; left; reflexivity | unfold str_objsize; lia]. }
clear J. destruct TXT as (TX & TB & TBN & len & str0 & rest0 & lencell & INT & TLO & THI & NIN & LS0 & BY & LENC & Hlen & ALT & (pn & INpn & Hpn)).
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

bstep. bstep. bstep. bstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (bytes_at_read rsegs mX 415640 _ 0 8 LC ltac:(lia) ltac:(rewrite length_le8; lia)) as RD1;
pose proof (bytes_at_read rsegs mX 69295 _ 0 1 DP ltac:(lia) ltac:(cbn; lia)) as RD2 end.
change (Z.to_nat 0) with 0%nat in RD1, RD2. rewrite skipn_O in RD1, RD2.
rewrite firstn_all2 in RD1 by (rewrite length_le8; lia). cbn [firstn] in RD2.
replace (415640 + 0) with 415640 in RD1 by lia. replace (69295 + 0) with 69295 in RD2 by lia.
bstep. bstep. try if_lit. bstep. bstep. bstep. try if_lit.

bstep. bstep. bstep. bstep. bstep. bstep. bstepz. bstep. bstep. bstep.

set (txtZ := map bv_unsigned str0 ++ [0]).
assert (FA : Forall (fun c => 0 <= c < 256) (map bv_unsigned str0)).
{ apply Forall_map. apply Forall_forall. intros b _. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R. lia. }
destruct (SCANH (map bv_unsigned str0) FA) as (bits & used & SCAN & U0).
assert (LTX : zlength txtZ = Z.of_nat (length str0) + 1) by (unfold zlength, txtZ; rewrite length_app, length_map; cbn [length]; lia).
assert (LPRE : zlength (map bv_unsigned str0) = Z.of_nat (length str0)) by (unfold zlength; rewrite length_map; reflexivity).
pose proof (heap_canary S4L HIx _ _ _ _ HP) as (g & CAN1 & CAN2 & _). cbn [hl_got_guard hl_guard hl_segs S4L] in CAN1, CAN2.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
apply (bytes_at_transport rsegs [(lo, bv_unsigned sp); (490332, 490336)] m mX) in CAN1; [| exact MU | cbn [disjoint_from]; rewrite length_le8; clia];
apply (bytes_at_transport rsegs [(lo, bv_unsigned sp); (490332, 490336)] m mX) in CAN2; [| exact MU | cbn [disjoint_from]; rewrite length_le8; clia] end.
lazymatch goal with H : rw_cells rsegs ?mX (bv_unsigned sp + -64) _ |- _ =>
apply rw_cells_app with (cs1 := [_]) in H as [PEC FR2]; cbn [cells_size csize Nat.add] in FR2;
change (bv_unsigned sp + -64 + Z.of_nat 8) with (bv_unsigned sp + -64 + 8) in FR2; replace (bv_unsigned sp + -64 + 8) with (bv_unsigned sp + -56) in FR2 by lia end.
fold_mkR.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => rename mX into mS end.
eapply evt_cut.
{ eapply STRTOD with (T := TX) (PE := bv_unsigned sp + -64) (txt := txtZ) (pre := map bv_unsigned str0) (post := []) (lo := lo) (bits := bits) (used := used) (canary := g).
- unfold txtZ. rewrite map_app. cbn [map]. rewrite map_unsigned_bytes'. exact BY.
- unfold txtZ. apply Forall_app. split; [exact FA | constructor; [lia | constructor]].
- reflexivity.
- rewrite LPRE. lia.
- rewrite LTX. lia.
- exact PEC.
- exact SCAN.
- rewrite unsigned_lit by lia. eassumption.
- rewrite unsigned_lit by lia. unfold RSTRTOD_DEPTH. lia.
- unfold RGLOBALS_TOP. clia.
- rewrite unsigned_lit by lia. lia.
- lia.
- rewrite unsigned_lit by lia. left. rewrite LTX. unfold RIMG_LO, RGLOBALS_TOP. split; [lia | clia].
- lia.
- rewrite unsigned_lit by lia. lia.
- lia.
- right. rewrite LTX. clia.
- apply ssp_cells_of_canary; [exact CAN1 | exact CAN2].
- unfold RERRNO. eassumption.
- assumption.
- exact FRM.
- reflexivity.
- reflexivity.
- apply bv_eq. rewrite !unsigned_lit by lia. reflexivity. }
cbv beta delta [rstrtod_post]. rewrite !(unsigned_lit (bv_unsigned sp + -64)) by lia. unfold RERRNO.
post_call rsegs mS.
rename PC0 into FKEEP. rename PC into FRMS. rename PC2 into STS. rename PC3 into PEC2. rename PC4 into TXT2. rename PC6 into ERRS. clear PC5 PC1. rename MI0 into MI.
lazymatch goal with |- evt _ _ (MS _ ?Fs _ ?fcs _ ?mX _) => rename mX into m5; rename Fs into F5; rename fcs into fc5 end.

assert (AG5 : agree_on rsegs BS m m5).
{ eapply agree_of_munch; [exact MU | exact WM |].
intros a k Hin. pose proof (heap_blk S4L HIx _ _ _ _ a k HP ltac:(apply in_or_app; left; exact Hin)) as (Hk & _ & _ & Hhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ a k HP ltac:(apply in_or_app; left; exact Hin)) as Himg. cbn [hl_img_lo hl_img_hi S4L] in Himg.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hhi. cbn. lia. }

assert (KFREE : forall (retpc : Z) (F2 : bvmap 5 word) (fc2 : bv 32) (mc : word -> option byte) (Ac : AS S4L HIx) (mdc : Model) (ec : word)
(ms3 : machine_state) (m3 : word -> option byte) (md3 : Model) (A3 : AS S4L HIx) (r3 : word),
(retpc = 0x26310 \/ retpc = 0x26394) -> Qc3B.frm0 fc2 ->
(forall k, In k FSAVED -> k <> 8 -> reg_get F2 (Z_to_bv 5 k) = reg_get F (Z_to_bv 5 k)) ->
rw_cells rsegs mc (bv_unsigned sp + -56) [C8 (reg_get F 8); C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
(exists ej, rw_cells rsegs mc (bv_unsigned sp + -64) [C8 ej]) ->
model_vm_only md mdc -> heap_pres S4L LB (bv_unsigned sp) m mc -> agree_on rsegs BS m mc -> HEAPx Ac (BS ++ LB) mc mdc ->
ret_state S4L (Z_to_bv 64 retpc) (Z_to_bv 64 (bv_unsigned sp + -64)) gp (Z_to_bv 64 490496) (Z_to_bv 64 TX) (Z_to_bv 64 0) (Z_to_bv 64 490332) s3 (Z_to_bv 64 69295) s5 s6 s7 s8 s9 s10 s11 F2 fc2 r3 m3 ms3 ->
model_vm_only mdc md3 -> stk rsegs m3 lo (bv_unsigned sp + -64) ->
heap_pres S4L (lb_remove 0 (BS ++ LB)) (bv_unsigned sp + -64) mc m3 ->
rw_cells rsegs m3 490332 [C4 ec] -> HEAPx A3 (lb_remove 0 (BS ++ LB)) m3 md3 ->
realizes rsegs (mkCfg ms3 md3) T).
{ intros retpc F2 fc2 mc Ac mdc ec ms3 m3 md3 A3 r3 Hret FRM2 FS2 FRc PEc VMc HPRc AGc HPc RS3 VM3 ST3 HPR3 ERR3 HP3.
clear MU WM MI FKEEP STS PEC2 TXT2 ERRS AG5 RD1 RD2 CAN1 CAN2 LEN1 LEN2 BY.
rewrite (lb_remove_zero' S4L HIx _ _ _ _ HPc) in HPR3, HP3.
open_ret RS3. cbn [hl_segs hl_tp S4L] in *.
destruct PEc as [ej PEc].
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR3) in FRc; [| left; cbn; lia]. cbn [hl_segs S4L] in FRc.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR3) in PEc; [| left; cbn; lia]. cbn [hl_segs S4L] in PEc.
assert (FR3 : rw_cells rsegs m3 (bv_unsigned sp + -64) [C8 ej; C8 (reg_get F 8); C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
{ apply (proj2 (rw_cells_app rsegs m3 _ [C8 ej] _)). split; [exact PEc|]. cbn [cells_size csize Nat.add].
change (bv_unsigned sp + -64 + Z.of_nat 8) with (bv_unsigned sp + -64 + 8). replace (bv_unsigned sp + -64 + 8) with (bv_unsigned sp + -56) by lia. exact FRc. }
clear FRc PEc.
pose proof (heap_model_ok _ _ _ _ _ _ HP3) as MOK3.
pose proof (heap_mem_inv _ _ _ _ _ _ HP3) as MI3. cbn [hl_segs S4L] in MI3.
assert (HPRm3 : heap_pres S4L LB (bv_unsigned sp) m m3).
{ eapply heap_pres_trans; [exact HPRc|]. eapply heap_pres_weaken; [exact HPR3 | lia | intros b Hb; apply in_or_app; right; exact Hb]. }
assert (JO3 : jopt rsegs S4F (Some (Sstr h)) m3 BS p).
{ split; [exact Hp|]. eapply jval_agree; [exact J0 | | apply incl_refl]. eapply agree_on_trans; [exact AGc|].
eapply (agree_of_heap_pres rsegs S4L); [exact HPR3 | reflexivity | intros b Hb; apply in_or_app; left; exact Hb]. }
pose proof (munch_refl [(lo, bv_unsigned sp); (490332, 490336)] m3) as MU. pose proof (wmono_refl rsegs m3) as WM.
destruct Hret as [-> | ->]; reenter MOK3.
-
bstep. bstepz. bstep. bstep.
apply evt_RZ_done. eapply EXIT; [eassumption | eassumption | | intros _; assumption | exact MOK3 | eapply model_vm_only_trans; [exact VMc | exact VM3] | | eassumption | assumption | | ].
{ intros k Hk NE. rewrite freg_get_other; [apply FS2; [exact Hk | exact NE]|].
cbn [FSAVED In] in Hk. repeat (destruct Hk as [<- | Hk]); [..| destruct Hk]; vm_compute; reflexivity. }
{ eapply heap_pres_trans; [exact HPRm3|]. eapply (heap_pres_of_munch S4L LB (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outside S4L HIx); [exact HP3 | intros b Hb; apply in_or_app; right; exact Hb | clia |].
apply Forall_cons; [cbn [fst snd]; left; clia |]. apply Forall_cons; [cbn [fst snd]; right; right; intros; cbn; lia | apply Forall_nil]. }
{ destruct JO3 as [_ J3]. split; [exact Hp|]. eapply jval_agree; [exact J3 | | apply incl_refl]. eapply agree_of_munch; [exact MU | exact WM |].
intros a k Hin. pose proof (heap_blk S4L HIx _ _ _ _ a k HP3 ltac:(apply in_or_app; left; exact Hin)) as (Hk & _ & _ & Hhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ a k HP3 ltac:(apply in_or_app; left; exact Hin)) as Himg. cbn [hl_img_lo hl_img_hi S4L] in Himg.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hhi. cbn. lia. }
{ eapply (heap_frame S4L HIx); [exact HP3 | | exact WM | assumption].
eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HP3 MU). solve_frameW. }
-
bstep.
apply evt_RZ_done. eapply EXIT; [eassumption | eassumption | | intros _; assumption | exact MOK3 | eapply model_vm_only_trans; [exact VMc | exact VM3] | | eassumption | assumption | | ].
{ intros k Hk NE. rewrite freg_get_other; [apply FS2; [exact Hk | exact NE]|].
cbn [FSAVED In] in Hk. repeat (destruct Hk as [<- | Hk]); [..| destruct Hk]; vm_compute; reflexivity. }
{ eapply heap_pres_trans; [exact HPRm3|]. eapply (heap_pres_of_munch S4L LB (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outside S4L HIx); [exact HP3 | intros b Hb; apply in_or_app; right; exact Hb | clia |].
apply Forall_cons; [cbn [fst snd]; left; clia |]. apply Forall_cons; [cbn [fst snd]; right; right; intros; cbn; lia | apply Forall_nil]. }
{ destruct JO3 as [_ J3]. split; [exact Hp|]. eapply jval_agree; [exact J3 | | apply incl_refl]. eapply agree_of_munch; [exact MU | exact WM |].
intros a k Hin. pose proof (heap_blk S4L HIx _ _ _ _ a k HP3 ltac:(apply in_or_app; left; exact Hin)) as (Hk & _ & _ & Hhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ a k HP3 ltac:(apply in_or_app; left; exact Hin)) as Himg. cbn [hl_img_lo hl_img_hi S4L] in Himg.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hhi. cbn. lia. }
{ eapply (heap_frame S4L HIx); [exact HP3 | | exact WM | assumption].
eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HP3 MU). solve_frameW. } }

assert (HP5 : HEAPx A (BS ++ LB) m5 md) by (heap_now S4L HIx HP MU WM MI).
assert (HPR5 : heap_pres S4L LB (bv_unsigned sp) m m5) by (apply XHPR; assumption).
assert (FS5 : forall G : bvmap 5 word, (forall k : reg, bv_eqb (Z_to_bv 5 8) k = false -> bv_eqb (Z_to_bv 5 10) k = false -> reg_get G k = reg_get F5 k) ->
forall k, In k FSAVED -> k <> 8 -> reg_get G (Z_to_bv 5 k) = reg_get F (Z_to_bv 5 k)).
{ intros G HG k Hk NE. cbn [FSAVED In] in Hk.
repeat (destruct Hk as [<- | Hk]); [..| destruct Hk]; first [exfalso; apply NE; reflexivity | idtac];
(rewrite HG by (vm_compute; reflexivity)); (rewrite FKEEP by (vm_compute; lia));
rewrite !freg_get_other by (vm_compute; reflexivity); reflexivity. }

bstep. bstep.
destruct (Z.eq_dec used 0) as [U0' | UN0].
+
rewrite U0' in *. replace (TX + 0) with TX by lia. if_truex. bstep. bstep.
alloc_call (hi_free S4L HIx) S4L HIx HP MU WM MI.
{ left. reflexivity. }
intros ms3 m3 md3 A3 r3 RS3 VM3 ST3 HPR3 ERR3 HP3.
lazymatch type of RS3 with ret_state _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?F2 ?fc2 _ _ _ =>
eapply (KFREE 0x26310 F2 fc2 m5 _ md) end; [left; reflexivity | assumption | apply FS5; intros; rewrite ?freg_get_other by assumption; reflexivity
| exact FR2 | eexists; exact PEC2 | apply model_vm_only_refl | exact HPR5 | exact AG5 | exact HP5
| exact RS3 | exact VM3 | exact ST3 | exact HPR3 | exact ERR3 | exact HP3].
+ if_falsex.
assert (HL : (Z.to_nat used < length (map (Z_to_bv 8) txtZ))%nat) by (rewrite length_map; unfold txtZ; rewrite length_app, length_map; cbn [length]; unfold zlength in POST; rewrite length_map in POST; lia).
destruct (nth_error (map (Z_to_bv 8) txtZ) (Z.to_nat used)) as [bu|] eqn:Hbu; [| exfalso; apply nth_error_None in Hbu; lia].
pose proof (bv_unsigned_in_range 8 bu) as BUR. unfold bv_modulus in BUR. cbn in BUR.
pose proof (u8ro_read rsegs m5 TX _ used bu _ TXT2 Hbu ltac:(lia) eq_refl) as RDU.
bstep. clear RDU. bstep.
match goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => destruct c end.
*
bstep. bstep. bstep.
match goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => destruct c end.
-- bstep. bstep. bstep.
alloc_call (hi_free S4L HIx) S4L HIx HP MU WM MI.
{ left. reflexivity. }
intros ms3 m3 md3 A3 r3 RS3 VM3 ST3 HPR3 ERR3 HP3.
lazymatch type of RS3 with ret_state _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?F2 ?fc2 _ _ _ =>
eapply (KFREE 0x26394 F2 fc2 m5 _ md) end; [right; reflexivity | assumption | apply FS5; intros; rewrite ?freg_get_other by assumption; reflexivity
| exact FR2 | eexists; exact PEC2 | apply model_vm_only_refl | exact HPR5 | exact AG5 | exact HP5
| exact RS3 | exact VM3 | exact ST3 | exact HPR3 | exact ERR3 | exact HP3].
-- bstep. bstep. bstep.
match goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => destruct c end.
++ bstep. bstep. bstep.
alloc_call (hi_free S4L HIx) S4L HIx HP MU WM MI.
{ left. reflexivity. }
intros ms3 m3 md3 A3 r3 RS3 VM3 ST3 HPR3 ERR3 HP3.
lazymatch type of RS3 with ret_state _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?F2 ?fc2 _ _ _ =>
eapply (KFREE 0x26394 F2 fc2 m5 _ md) end; [right; reflexivity | assumption | apply FS5; intros; rewrite ?freg_get_other by assumption; reflexivity
| exact FR2 | eexists; exact PEC2 | apply model_vm_only_refl | exact HPR5 | exact AG5 | exact HP5
| exact RS3 | exact VM3 | exact ST3 | exact HPR3 | exact ERR3 | exact HP3].
++ bstep. bstep. bstep. bstep.
alloc_call (hi_free S4L HIx) S4L HIx HP MU WM MI.
{ left. reflexivity. }
intros ms3 m3 md3 A3 r3 RS3 VM3 ST3 HPR3 ERR3 HP3.
lazymatch type of RS3 with ret_state _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?F2 ?fc2 _ _ _ =>
eapply (KFREE 0x26394 F2 fc2 m5 _ md) end; [right; reflexivity | assumption | apply FS5; intros; rewrite ?freg_get_other by assumption; reflexivity
| exact FR2 | eexists; exact PEC2 | apply model_vm_only_refl | exact HPR5 | exact AG5 | exact HP5
| exact RS3 | exact VM3 | exact ST3 | exact HPR3 | exact ERR3 | exact HP3].
*
bstep. bstep.
alloc_call (hi_free S4L HIx) S4L HIx HP MU WM MI.
{ left. reflexivity. }
intros ms3 m3 md3 A3 r3 RS3 VM3 ST3 HPR3 ERR3 HP3.
lazymatch type of RS3 with ret_state _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?F2 ?fc2 _ _ _ =>
eapply (KFREE 0x26310 F2 fc2 m5 _ md) end; [left; reflexivity | assumption | apply FS5; intros; rewrite ?freg_get_other by assumption; reflexivity
| exact FR2 | eexists; exact PEC2 | apply model_vm_only_refl | exact HPR5 | exact AG5 | exact HP5
| exact RS3 | exact VM3 | exact ST3 | exact HPR3 | exact ERR3 | exact HP3].
-  bstep. bstep. try if_lit. bstep. bstep. try if_lit.
bstep. bstep. bstep. bstep. bstep. bstepz. bstep. step.
apply evt_RZ_done. eapply EXIT; [eassumption | eassumption | solve_FS1 | intros _; assumption | exact MOK | apply model_vm_only_refl
| apply XHPR; assumption | eassumption | assumption | apply XJO; assumption | apply XHP; assumption].
-  bstep. bstep. try if_lit. bstep. bstep. try if_lit.
bstep. bstep. bstep. bstep. bstep. bstepz. bstep. step.
apply evt_RZ_done. eapply EXIT; [eassumption | eassumption | solve_FS1 | intros _; assumption | exact MOK | apply model_vm_only_refl
| apply XHPR; assumption | eassumption | assumption | apply XJO; assumption | apply XHP; assumption].
Qed.
End JoGetDoubleP.

End RC__1.
