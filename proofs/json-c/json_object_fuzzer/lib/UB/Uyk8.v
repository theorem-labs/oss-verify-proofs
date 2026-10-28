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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKQo. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q8tj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q8tj.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UPZI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UPZI.Mq4.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UzWc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UzWc.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6WR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6WR. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6WR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6WR.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QrPc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QrPc.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QeuE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QeuE. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UIX4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UIX4. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uxk8.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uxk8. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UiEN.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UiEN. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UNPb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UNPb. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UKci.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UKci. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UrWh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UrWh.
Import ListNotations. Unset Keyed Unification. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section Put.
Variable HIx : heap_iface S4L.
Hypothesis DEL : lh_delete_tail_stmt2 HIx.
Hypothesis MEMMOVE : memmove_stmt.

#[using="DEL MEMMOVE"] Theorem json_object_put_cps : put_stmt_P HIx.
Proof.
unfold put_stmt_P, put_stmt. intros until rc. intros HP PRE A0 ST LO LOS SPA HT ERR TP RA K.
cbn [hl_segs hl_tp S4L] in *. unfold put_stk_P in LOS. unfold put_entry_P.
unfold_consts. word_range sp SPW.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (wmono_refl rsegs m) as WM. pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp)] m) as MU.
apply rz_evt; [exact MOK|]. subst a0 tp.
destruct s as [c|].
- destruct PRE as (Hp & Hrc & J).
pose proof (heap_blk_nodup S4L HIx _ _ _ _ HP) as ND.
destruct (jval_hdr rsegs S4F c m BS p rc J (nodup_app_l _ _ ND)) as (n & tojs_ & pb_ & udel_ & ud_ & rest_ & INp & _ & N48 & _ & _). clear tojs_ pb_ udel_ ud_ rest_.
pose proof (heap_blk S4L HIx _ _ _ _ p n HP ltac:(in_sub INp)) as (_ & Hpal & Hplo & Hphi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hphi.
carve_frame 96%nat ST.
do 12 step. step. if_falsex. step. step. step.
match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
assert (J1 : jval rsegs S4F c m1 BS p rc).
{ eapply jval_agree; [exact J | | apply incl_refl]. eapply agree_of_munch; [exact MU | exact WM |].
intros a k Hin. pose proof (heap_blk S4L HIx _ _ _ _ a k HP ltac:(in_sub Hin)) as (Hk & _ & _ & Hahi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hahi. cbn. lia. }
assert (HPR1 : heap_pres S4L LB (bv_unsigned sp) m m1).
{ eapply (heap_pres_of_munch S4L LB (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outside S4L HIx); [exact HP | intros b Hb; in_sub Hb | clia |].
apply Forall_cons; [cbn [fst snd]; left; clia | apply Forall_nil]. }
apply evt_RZ_done.
eapply (maybe_free_cps HIx) with (s := c) (BS := BS) (LB := LB) (x := p) (rc := rc) (lo := lo);
[ heap_now S4L HIx HP MU WM MI | exact Hp | exact Hrc | exact J1 | .. ]; try alloc_side.
intros ms2 md2 (m2 & A2 & r & RS2 & VM2 & ST2 & HPR2 & ERR2 & OUT2).
destruct RS2 as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & F2 & fc2 & -> & FS2 & FRM2).
cbn [hl_segs hl_tp S4L] in *.
rewrite ?(unsigned_lit (bv_unsigned sp + -96)) in ST2 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -96)) in HPR2 by lia.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
assert (HPR12 : heap_pres S4L LB (bv_unsigned sp) m m2).
{ eapply heap_pres_trans; [exact HPR1 | eapply heap_pres_weaken; [exact HPR2 | lia | intros b Hb; exact Hb]]. }
clear MU WM MI J J1.
destruct OUT2 as [(-> & Hrc2 & J2 & HP2) | [(-> & -> & HP2) | (-> & -> & ZM & HP2)]].
+
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2. pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI. cbn [hl_segs S4L] in MI.
pose proof (wmono_refl rsegs m2) as WM. pose proof (munch_refl [] m2) as MU.
reenter MOK2. step. step. if_truex.
do 12 step. release_frame FR ST2 (bv_unsigned sp). step.
apply evt_RZ_done. apply K. unfold put_post. exists m2, A2, (Z_to_bv 64 0).
split; [apply ret_statew_intro; [exact FS2 | exact FRM2] |]. split; [exact VM2|]. split; [exact ST2|]. split; [exact HPR12|]. split; [exact ERR2|].
right. exists c. split; [reflexivity|]. split; [lia|]. split; [exact J2 | exact HP2].
+
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2. pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI. cbn [hl_segs S4L] in MI.
pose proof (wmono_refl rsegs m2) as WM. pose proof (munch_refl [] m2) as MU.
reenter MOK2. step. step. if_truex.
do 12 step. release_frame FR ST2 (bv_unsigned sp). step.
apply evt_RZ_done. apply K. unfold put_post. exists m2, A2, (Z_to_bv 64 1).
split; [apply ret_statew_intro; [exact FS2 | exact FRM2] |]. split; [exact VM2|]. split; [exact ST2|]. split; [exact HPR12|]. split; [exact ERR2|].
left. split; [right; reflexivity | exact HP2].
+
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2. pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI. cbn [hl_segs S4L] in MI.
pose proof (wmono_refl rsegs m2) as WM. pose proof (munch_refl [] m2) as MU.
destruct (zomb_zhead HIx sp gp s10 s11 lo errv c m2 p BS ZM (desc_all HIx sp gp s10 s11 lo errv LO ltac:(lia) SPA HT DEL MEMMOVE c)) as (isobj & ck & ZH & HS).
reenter MOK2. step. step. if_false. step. step. step. step. step.
replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 18446744073709551615) by (apply bv_eq; vm_compute; reflexivity).
apply evt_RZ_done.
stash FR.
eapply HS; [exact HP2 | exact ZH | exact ST2 | exact ERR2 |].
intros ms3 md3 (m3 & A3 & F3 & fc3 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w18 & w19 & w20 & -> & FS3 & FRM3 & VM3 & HP3 & ST3 & HPR3 & ERR3).
unstash FR.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR3) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
pose proof (heap_model_ok _ _ _ _ _ _ HP3) as MOK3. pose proof (heap_mem_inv _ _ _ _ _ _ HP3) as MI3. cbn [hl_segs S4L] in MI3.
clear WM MU. pose proof (wmono_refl rsegs m3) as WM. pose proof (munch_refl [] m3) as MU.
apply rz_evt; [exact MOK3|].
step. step. if_true. step.
do 12 step. release_frame FR ST3 (bv_unsigned sp). step.
apply evt_RZ_done. apply K. unfold put_post. exists m3, A3, (Z_to_bv 64 1).
split; [apply ret_statew_intro; [eapply fsaved_trans; [exact FS2 | exact FS3] | intros Hf; exact (FRM3 (FRM2 Hf))] |].
split; [eapply model_vm_only_trans; [exact VM2 | exact VM3]|]. split; [exact ST3|].
split; [eapply heap_pres_trans; [exact HPR12 | eapply heap_pres_weaken; [exact HPR3 | lia | intros b Hb; exact Hb]]|].
split; [exact ERR3|]. left. split; [right; reflexivity | exact HP3].
-
destruct PRE as [-> ->]. cbn [app] in HP.
carve_frame 96%nat ST.
do 12 step. step. if_true.
match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
assert (HP1 : HEAP S4L HIx A LB m1 md).
{ eapply (heap_frame S4L HIx); [exact HP | | exact WM | exact MI].
eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HP MU).
apply Forall_cons; [cbn [fst snd]; left; split; [clia | pose proof (hi_top_hi S4L HIx); lia] | apply Forall_nil]. }
assert (HPR1 : heap_pres S4L LB (bv_unsigned sp) m m1).
{ eapply (heap_pres_of_munch S4L LB (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outside S4L HIx); [exact HP | intros b Hb; exact Hb | clia |].
apply Forall_cons; [cbn [fst snd]; left; clia | apply Forall_nil]. }
do 12 step. release_frame FR ST (bv_unsigned sp). step.
apply evt_RZ_done. apply K. unfold put_post. exists m1, A, (Z_to_bv 64 0).
split; [apply ret_statew_same|]. split; [apply model_vm_only_refl|]. split; [exact ST|]. split; [exact HPR1|]. split; [exact ERR|].
left. split; [left; reflexivity | exact HP1].
Qed.
End Put.
End RC__1.

From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Ul9N.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ul9N.Mq0.
Section RC__2. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Theorem json_object_put_P : forall HIx : heap_iface S4L, put_stmt_P HIx.
Proof. intros HIx. exact (json_object_put_cps HIx (lh_delete_tail_cps2 HIx) memmove_spec). Qed.

End RC__2.
