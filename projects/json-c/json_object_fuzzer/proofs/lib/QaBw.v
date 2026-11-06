(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwApply. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QzgB.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc3B.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc3B.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfYR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfYR. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfcC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfcC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Ql2m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql2m.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7wb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7wb. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCqH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCqH.
Import ListNotations. Unset Keyed Unification. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms_in H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_in_4 H. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap e ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_1 e. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap_in e H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.

Module GwI.
Definition segs := tt.
End GwI.

Lemma znth_In' : forall (l : list Z) i, 0 <= i < zlength l -> In (znth l i) l.
Proof. first [GwInst.gw_exact (@QzgB.znth_In') | autorewrite with gw_eqs; GwInst.gw_exact (@QzgB.znth_In')]. Qed.

Lemma znth_app_mid : forall (pre post : list Z), znth (pre ++ 0 :: post)%Z (Z.of_nat (length pre)) = 0%Z.
Proof. first [GwInst.gw_exact (@QzgB.znth_app_mid) | autorewrite with gw_eqs; GwInst.gw_exact (@QzgB.znth_app_mid)]. Qed.

Local Definition gwt_X : unit := Q6nq.gwt_nil.
Lemma znth_app_pre : ltac2:(Q6nq.tyx '(@QzgB.znth_app_pre) [] '(@nil Z) 'gwt_X).
Proof. first [GwInst.gw_exact (@QzgB.znth_app_pre) | autorewrite with gw_eqs; GwInst.gw_exact (@QzgB.znth_app_pre)]. Qed.

Section Model.
Variables (txt : list Z) (p : Z).
Hypothesis BYT : Forall (fun c => 0 <= c < 256)%Z txt.
Hypothesis Hp : (0 <= p < zlength txt)%Z.
Hypothesis Hnul : znth txt p = 0%Z.
Hypothesis Hnum : forall i, (0 <= i < p)%Z -> is_numch (znth txt i) = true.

#[using="Hnum"] Lemma numch_facts : forall i, (0 <= i < p)%Z -> let c := znth txt i in (43 <= c <= 57 \/ c = 69 \/ c = 101)%Z.
Proof. first [GwApply.gw_by_name GwI.segs (@QzgB.numch_facts) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QzgB.numch_facts)]. Qed.

Definition okch (c : Z) : Prop := (43 <= c <= 57 \/ c = 69 \/ c = 101 \/ c = 0 \/ c = -1)%Z.
Lemma gw_eq_okch : @okch = ltac:(GwInst.gw_term (@QzgB.okch) (@okch)). Proof. unfold okch, QzgB.okch; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_okch : gw_eqs.

#[using="Type"] Lemma fs_ws_loop_step : ltac2:(Q6nq.ty1 'GwI.segs '(@QzgB.fs_ws_loop_step) [[@gw_eq_okch__3; @gw_eq_okch__2; @gw_eq_okch]] '(@nil Z) 'gwt_X).
Proof. first [GwApply.gw_by_name GwI.segs (@QzgB.fs_ws_loop_step) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QzgB.fs_ws_loop_step)]. Qed.
#[using="Type"] Lemma okch_cases : ltac2:(Q6nq.ty1 'GwI.segs '(@QzgB.okch_cases) [[@gw_eq_okch]] '([105; 110]%Z : list Z) 'gwt_X).
Proof. rewrite ?gw_eq_okch; first [GwApply.gw_by_name GwI.segs (@QzgB.okch_cases) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QzgB.okch_cases)]. Qed.
#[using="Type"] Lemma fs_inf_nil : forall c f, (Z.lor c 32 =? 105) = false -> fs_inf_loop 9 (0%Z, c, f) = Some (0%Z, c, f).
Proof. first [GwApply.gw_by_name GwI.segs (@QzgB.fs_inf_nil) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QzgB.fs_inf_nil)]. Qed.
#[using="Type"] Lemma fs_nan_nil : forall c f, (Z.lor c 32 =? 110) = false -> fs_nan_loop 4 (0%Z, c, f) = Some (0%Z, c, f).
Proof. first [GwApply.gw_by_name GwI.segs (@QzgB.fs_nan_nil) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QzgB.fs_nan_nil)]. Qed.

#[using="Type"] Lemma dfK_dn_f : forall sg f rp a z e2 x f' y, dfK_dn 53 (-1074) sg f rp a z e2 x = Some (f', y) -> f' = f.
Proof. first [GwApply.gw_by_name GwI.segs (@QzgB.dfK_dn_f) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QzgB.dfK_dn_f)]. Qed.
#[using="Type"] Lemma dfK_up_f : forall sg f rp a z e2 x f' y, dfK_up 53 (-1074) sg f rp a z e2 x = Some (f', y) -> f' = f.
Proof. first [GwApply.gw_by_name GwI.segs (@QzgB.dfK_up_f) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QzgB.dfK_up_f)]. Qed.
#[using="Type"] Lemma dfK_al_f : forall sg f rp z x f' y, dfK_al 53 (-1074) sg f rp z x = Some (f', y) -> f' = f.
Proof. first [GwApply.gw_by_name GwI.segs (@QzgB.dfK_al_f) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QzgB.dfK_al_f)]. Qed.
#[using="Type"] Lemma dfK_tz_f : forall sg f rp k x f' y, dfK_tz 53 (-1074) sg f rp k x = Some (f', y) -> f' = f.
Proof. first [GwApply.gw_by_name GwI.segs (@QzgB.dfK_tz_f) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QzgB.dfK_tz_f)]. Qed.
#[using="Type"] Lemma dfK_mid_f : forall sg f rp lnz k x f' y, dfK_mid 53 (-1074) sg f rp lnz k x = Some (f', y) -> f' = f.
Proof. first [GwApply.gw_by_name GwI.segs (@QzgB.dfK_mid_f) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QzgB.dfK_mid_f)]. Qed.
#[using="Type"] Lemma dfK_pad_f : forall sg f lrp lnz j k x f' y, dfK_pad 53 (-1074) sg f lrp lnz j k x = Some (f', y) -> f' = f.
Proof. first [GwApply.gw_by_name GwI.segs (@QzgB.dfK_pad_f) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QzgB.dfK_pad_f)]. Qed.
#[using="Type"] Lemma dfK_rng_f : forall sg f lrp dc lnz j k x f' y, dfK_rng 53 (-1074) sg f lrp dc lnz j k x = Some (f', y) -> f' = f.
Proof. first [GwApply.gw_by_name GwI.segs (@QzgB.dfK_rng_f) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QzgB.dfK_rng_f)]. Qed.

#[using="Type"] Lemma dfK_rng_f' : forall {sg f lrp dc lnz j k x f2 y}, dfK_rng 53 (-1074) sg f lrp dc lnz j k x = Some (f2, y) -> f = f2.
Proof. first [GwApply.gw_by_name GwI.segs (@QzgB.dfK_rng_f') | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QzgB.dfK_rng_f')]. Qed.

Definition JF (k c : Z) (f : shfile) : Prop :=
(sh_buf f = txt /\ sh_cnt0 f = 0 /\ 0 <= sh_rpos f /\ -1 <= c /\
(sh_shlim_neg f = false -> k <= sh_rpos f) /\
(sh_stdio f = false -> sh_shlim_neg f = false /\ sh_rpos f <= p + 1 /\ (c <> 0 -> sh_rpos f <= p) /\ 0 <= c) /\
(sh_stdio f = true -> sh_n f = p /\ sh_rpos f <= p /\ (sh_shlim_neg f = true -> sh_rpos f = p)))%Z.
Lemma gw_eq_JF : @JF = ltac:(GwInst.gw_term (@QzgB.JF) (@JF)). Proof. unfold JF, QzgB.JF; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_JF : gw_eqs.

Definition JR (f : shfile) : Prop := (0 <= sh_cnt0 f <= sh_rpos f /\ sh_rpos f <= p)%Z.
Lemma gw_eq_JR : @JR = ltac:(GwInst.gw_term (@QzgB.JR) (@JR)). Proof. unfold JR, QzgB.JR; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_JR : gw_eqs.

#[using="BYT Hp Hnul"] Lemma JF_getc : forall k c f, JF k c f -> c <> 0%Z -> JF (k + 1) (fst (sh_getc f)) (snd (sh_getc f)).
Proof. rewrite ?gw_eq_JF; first [GwApply.gw_by_name GwI.segs (@QzgB.JF_getc) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QzgB.JF_getc)]. Qed.
#[using="Type"] Lemma JF_unget_any : ltac2:(Q6nq.ty1 'GwI.segs '(@QzgB.JF_unget_any) [[@gw_eq_JF]; [@gw_eq_JR]; [@gw_eq_okch__3; @gw_eq_okch__2; @gw_eq_okch]] '(@nil Z) 'gwt_X).
Proof. rewrite ?gw_eq_JF, ?gw_eq_JR; first [GwApply.gw_by_name GwI.segs (@QzgB.JF_unget_any) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QzgB.JF_unget_any)]. Qed.
#[using="Type"] Lemma JR_lim0 : forall f, JR f -> JR (sh_lim0 f).
Proof. rewrite ?gw_eq_JR; first [GwApply.gw_by_name GwI.segs (@QzgB.JR_lim0) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QzgB.JR_lim0)]. Qed.
#[using="Type"] Lemma JF_weak : forall k k' c f, JF k c f -> (k' <= k)%Z -> JF k' c f.
Proof. rewrite ?gw_eq_JF; first [GwApply.gw_by_name GwI.segs (@QzgB.JF_weak) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QzgB.JF_weak)]. Qed.
#[using="Type"] Lemma JF_neg_JR : forall k c f, JF k c f -> (c < 0)%Z -> JR f.
Proof. rewrite ?gw_eq_JF, ?gw_eq_JR; first [GwApply.gw_by_name GwI.segs (@QzgB.JF_neg_JR) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QzgB.JF_neg_JR)]. Qed.
#[using="Hp Hnul Hnum"] Lemma JF_okch : forall k c f, JF k c f -> c <> 0%Z -> okch (fst (sh_getc f)).
Proof. rewrite ?gw_eq_okch, ?gw_eq_JF; first [GwApply.gw_by_name GwI.segs (@QzgB.JF_okch) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QzgB.JF_okch)]. Qed.

#[using="BYT Hp Hnul"] Lemma df_lz_J : ltac2:(Q6nq.ty1 'GwI.segs '(@QzgB.df_lz_J) [[@gw_eq_JF]; [@gw_eq_okch__3; @gw_eq_okch__2; @gw_eq_okch]; [@gw_eq_JR__3; @gw_eq_JR__2; @gw_eq_JR]] '(@nil Z) 'gwt_X).
Proof. rewrite ?gw_eq_JF; first [GwApply.gw_by_name GwI.segs (@QzgB.df_lz_J) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QzgB.df_lz_J)]. Qed.
#[using="BYT Hp Hnul"] Lemma df_rz_J : ltac2:(Q6nq.ty1 'GwI.segs '(@QzgB.df_rz_J) [[@gw_eq_JF]; [@gw_eq_okch__3; @gw_eq_okch__2; @gw_eq_okch]; [@gw_eq_JR__3; @gw_eq_JR__2; @gw_eq_JR]] '(@nil Z) 'gwt_X).
Proof. rewrite ?gw_eq_JF; first [GwApply.gw_by_name GwI.segs (@QzgB.df_rz_J) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QzgB.df_rz_J)]. Qed.
#[using="BYT Hp Hnul"] Lemma df_dig_J : ltac2:(Q6nq.ty1 'GwI.segs '(@QzgB.df_dig_J) [[@gw_eq_JF]; [@gw_eq_okch__3; @gw_eq_okch__2; @gw_eq_okch]; [@gw_eq_JR__3; @gw_eq_JR__2; @gw_eq_JR]] '(@nil Z) 'gwt_X).
Proof. rewrite ?gw_eq_JF; first [GwApply.gw_by_name GwI.segs (@QzgB.df_dig_J) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QzgB.df_dig_J)]. Qed.
#[using="BYT Hp Hnul"] Lemma scanexp_l1_J : ltac2:(Q6nq.ty1 'GwI.segs '(@QzgB.scanexp_l1_J) [[@gw_eq_JF]; [@gw_eq_okch__3; @gw_eq_okch__2; @gw_eq_okch]; [@gw_eq_JR__3; @gw_eq_JR__2; @gw_eq_JR]] '(@nil Z) 'gwt_X).
Proof. rewrite ?gw_eq_JF; first [GwApply.gw_by_name GwI.segs (@QzgB.scanexp_l1_J) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QzgB.scanexp_l1_J)]. Qed.
#[using="BYT Hp Hnul"] Lemma scanexp_l2_J : ltac2:(Q6nq.ty1 'GwI.segs '(@QzgB.scanexp_l2_J) [[@gw_eq_JF]; [@gw_eq_okch__3; @gw_eq_okch__2; @gw_eq_okch]; [@gw_eq_JR__3; @gw_eq_JR__2; @gw_eq_JR]] '(@nil Z) 'gwt_X).
Proof. rewrite ?gw_eq_JF; first [GwApply.gw_by_name GwI.segs (@QzgB.scanexp_l2_J) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QzgB.scanexp_l2_J)]. Qed.
#[using="BYT Hp Hnul"] Lemma scanexp_l3_J : ltac2:(Q6nq.ty1 'GwI.segs '(@QzgB.scanexp_l3_J) [[@gw_eq_JF]; [@gw_eq_okch__3; @gw_eq_okch__2; @gw_eq_okch]; [@gw_eq_JR__3; @gw_eq_JR__2; @gw_eq_JR]] '(@nil Z) 'gwt_X).
Proof. rewrite ?gw_eq_JF; first [GwApply.gw_by_name GwI.segs (@QzgB.scanexp_l3_J) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QzgB.scanexp_l3_J)]. Qed.

#[using="BYT Hp Hnul"] Lemma scanexp_J : ltac2:(Q6nq.ty1 'GwI.segs '(@QzgB.scanexp_J) [[@gw_eq_JF]; [@gw_eq_JR]; [@gw_eq_okch__3; @gw_eq_okch__2; @gw_eq_okch]] '(@nil Z) 'gwt_X).
Proof. rewrite ?gw_eq_JF, ?gw_eq_JR; first [GwApply.gw_by_name GwI.segs (@QzgB.scanexp_J) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QzgB.scanexp_J)]. Qed.

#[using="BYT Hp Hnul"] Lemma decfloat_J : ltac2:(Q6nq.ty1 'GwI.segs '(@QzgB.decfloat_J) [[@gw_eq_JF]; [@gw_eq_JR]; [@gw_eq_okch__3; @gw_eq_okch__2; @gw_eq_okch]] '([(-1074)]%Z : list Z) 'gwt_X).
Proof. rewrite ?gw_eq_JF, ?gw_eq_JR; first [GwApply.gw_by_name GwI.segs (@QzgB.decfloat_J) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QzgB.decfloat_J)]. Qed.

#[using="BYT Hp Hnul Hnum"] Lemma floatscan_JR : forall n f pk f' y, floatscan (S n) f 1 pk = Some (f', y) -> JF 0 1 f -> JR f'.
Proof. rewrite ?gw_eq_JF, ?gw_eq_JR; first [GwApply.gw_by_name GwI.segs (@QzgB.floatscan_JR) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QzgB.floatscan_JR)]. Qed.

#[using="Type"] Lemma strlen_loop_first0 : ltac2:(Q6nq.ty1 'GwI.segs '(@QzgB.strlen_loop_first0) [[@gw_eq_okch__3; @gw_eq_okch__2; @gw_eq_okch]; [@gw_eq_JF__3; @gw_eq_JF__2; @gw_eq_JF]; [@gw_eq_JR__3; @gw_eq_JR__2; @gw_eq_JR]] '(@nil Z) 'gwt_X).
Proof. first [GwApply.gw_by_name GwI.segs (@QzgB.strlen_loop_first0) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QzgB.strlen_loop_first0)]. Qed.

Definition ssf0 : shfile := mkSh txt 0 0 p true false.
Lemma gw_eq_ssf0 : @ssf0 = ltac:(GwInst.gw_term (@QzgB.ssf0) (@ssf0)). Proof. unfold ssf0, QzgB.ssf0; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_ssf0 : gw_eqs.

#[using="Hp"] Lemma ss_JF0 : JF 0 1 ssf0.
Proof. rewrite ?gw_eq_JF, ?gw_eq_ssf0; first [GwApply.gw_by_name GwI.segs (@QzgB.ss_JF0) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QzgB.ss_JF0)]. Qed.

#[using="BYT Hp Hnul Hnum"] Lemma ss_peek : ltac2:(Q6nq.ty1 'GwI.segs '(@QzgB.ss_peek) [[@gw_eq_okch]; [@gw_eq_ssf0]; [@gw_eq_JF__3; @gw_eq_JF__2; @gw_eq_JF]; [@gw_eq_JR__3; @gw_eq_JR__2; @gw_eq_JR]] '(@nil Z) 'gwt_X).
Proof. rewrite ?gw_eq_okch, ?gw_eq_ssf0; first [GwApply.gw_by_name GwI.segs (@QzgB.ss_peek) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QzgB.ss_peek)]. Qed.

#[using="BYT Hp Hnul Hnum"] Lemma ss_model : ltac2:(Q6nq.ty1 'GwI.segs '(@QzgB.ss_model) [[@gw_eq_JR]; [@gw_eq_ssf0]; [@gw_eq_okch__3; @gw_eq_okch__2; @gw_eq_okch]; [@gw_eq_JF__3; @gw_eq_JF__2; @gw_eq_JF]] '(@nil Z) 'gwt_X).
Proof. rewrite ?gw_eq_JR, ?gw_eq_ssf0; first [GwApply.gw_by_name GwI.segs (@QzgB.ss_model) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QzgB.ss_model)]. Qed.

End Model.
Lemma gw_eq_okch__2 : @okch = ltac:(GwInst.gw_term (@QzgB.okch) (@okch)). Proof. unfold okch, QzgB.okch; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_okch__2 : gw_eqs.
Lemma gw_eq_JF__2 : @JF = ltac:(GwInst.gw_term (@QzgB.JF) (@JF)). Proof. unfold JF, QzgB.JF; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_JF__2 : gw_eqs.
Lemma gw_eq_JR__2 : @JR = ltac:(GwInst.gw_term (@QzgB.JR) (@JR)). Proof. unfold JR, QzgB.JR; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_JR__2 : gw_eqs.
Lemma gw_eq_ssf0__2 : @ssf0 = ltac:(GwInst.gw_term (@QzgB.ssf0) (@ssf0)). Proof. unfold ssf0, QzgB.ssf0; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_ssf0__2 : gw_eqs.
