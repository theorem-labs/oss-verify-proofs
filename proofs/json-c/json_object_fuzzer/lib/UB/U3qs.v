(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwEq GwApply. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZxv.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QQRC.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qc3B.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc3B.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QfYR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfYR. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QfcC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfcC.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Lib.SepCache.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QnDM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnDM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QDUx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDUx. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q9Ay.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9Ay.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U4l4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U4l4. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UzHs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UzHs. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UuJ9.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UuJ9. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UnKY.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UnKY. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UqYW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UqYW.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
Import ListNotations. Unset Keyed Unification.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module GwI.
Definition segs := rsegs.
Definition base := 0x5b640%Z.
Definition w_71 := 0x0000a517%Z.
Definition w_72 := 0x27453903%Z.
Definition w_98 := 0x85df50ef%Z.
Definition hi_71 := (Z_to_bv 20 10).
Definition lo_72 := (Z_to_bv 12 628).
Definition joff_98 := (Z_to_bv 21 2054236).
Definition got_ssp := got_ssp.
Definition STRING_READ := STRING_READ.
Definition ssp_guard := ssp_guard.
Definition e_197bc := 0x51024%Z.
Definition e_memcpy := 0x5f438%Z.
Definition e_memchr := 0x5f33c%Z.
Lemma CODE : CodeAt.code_at rsegs 0x5b640 (QQRC.Mq3.shgetc_code 0x0000a517%Z 0x27453903%Z 0x85df50ef%Z).  Proof. StepGen.code_at_vm. Qed.
Lemma BASE4 : (0x5b640 mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma BASER : (0 <= 0x5b640 /\ 0x5b640 + 544 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.
End GwI.

Definition RFJ (T : Z) (txt : list Z) (p : Z) (w : bool) (J : rfj) (kmin c : Z) (f : shfile) : Prop :=
sh_ok T txt f /\ (-1 <= c < 256)%Z /\ (0 <= sh_cnt0 f <= sh_rpos f)%Z /\
(sh_shlim_neg f = false -> sh_cnt0 f + kmin <= sh_rpos f)%Z /\
(sh_stdio f = false -> sh_shlim_neg f = false /\ sh_rpos f <= p + 1 /\ (c <> 0%Z -> sh_rpos f <= p))%Z /\
(sh_stdio f = true -> sh_n f = p /\ sh_rpos f <= p /\ (sh_shlim_neg f = true -> sh_rpos f = p) /\
(w = false -> sh_rpos f = 0 /\ sh_cnt0 f = 0 /\ sh_shlim_neg f = false) /\ (J = ssJ /\ False))%Z.
Lemma gw_eq_RFJ : @RFJ = ltac:(GwInst.gw_term (@QZxv.Mql.RFJ STRING_READ) (@RFJ)). Proof. unfold RFJ, QZxv.Mql.RFJ; ltac2:(GwEq.gw_rw [[@gw_eq_ssJ__3; @gw_eq_ssJ__2; @gw_eq_ssJ]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_RFJ : gw_eqs.

Section RF.
Variables (T : Z) (txt : list Z) (p : Z) (J : rfj).
Hypothesis BYT : Forall (fun c => 0 <= c < 256) txt.
Hypothesis Hp : 0 <= p < zlength txt.
Hypothesis Hnul : znth txt p = 0.
Hypothesis T0 : 0 < T.
Hypothesis T1 : T + 2^41 <= 2^63.

Notation RFI := (RFJ T txt p true J).

#[using="Type"] Lemma RFI_ok : forall kmin c f, RFI kmin c f -> sh_ok T txt f.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_RFI__3; @gw_eq_RFI__2; @gw_eq_RFI]]); first [GwApply.gw_by_name GwI.segs (@QZxv.Mql.RFI_ok) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QZxv.Mql.RFI_ok)]. Qed.

#[using="Hp"] Lemma RFI_rpos : forall kmin c f, RFI kmin c f -> 0 <= sh_rpos f <= p + 1.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_RFI__3; @gw_eq_RFI__2; @gw_eq_RFI]]); first [GwApply.gw_by_name GwI.segs (@QZxv.Mql.RFI_rpos) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QZxv.Mql.RFI_rpos)]. Qed.

Local Definition gwt_X : unit := (Q6nq.gwt_def (@QQRC.Mq3.ssp_cells) (@UxDK.ssp_cells) (Q6nq.gwt_def (@QZxv.Mql.ssp_cells) (@UxDK.ssp_cells) (Q6nq.gwt_def (@QQRC.Mq3.ssJ) (@UxDK.ssJ) (Q6nq.gwt_def (@QZxv.Mql.ssJ) (@UxDK.ssJ) (Q6nq.gwt_def (@QROt.Mq2.shgetc_post) (@UnKY.shgetc_post) (Q6nq.gwt_def (@QZxv.Mql.shgetc_post) (@UnKY.shgetc_post) (Q6nq.gwt_def (@Q8l1.Mq3.rtext) (@Uoo0.rtext) (Q6nq.gwt_def (@QQRC.Mq3.rf_rend) (@UxDK.rf_rend) (Q6nq.gwt_def (@QQRC.Mq3.rf_cells) (@UxDK.rf_cells) (Q6nq.gwt_def (@QQRC.Mq3.SHGETC) (@UxDK.SHGETC) (Q6nq.gwt_def (@QZxv.Mql.SHGETC) (@UxDK.SHGETC) (Q6nq.gwt_def (@QQRC.Mq3.RFI) (@UxDK.RFI) (Q6nq.gwt_def (@QZxv.Mql.RFI) (@UxDK.RFI) Q6nq.gwt_nil))))))))))))).
#[using="Hp"] Lemma rf_getc_fast : ltac2:(Q6nq.ty1 'GwI.segs '(@QZxv.Mql.rf_getc_fast) [[@gw_eq_RFI__3; @gw_eq_RFI__2; @gw_eq_RFI]; [@gw_eq_rf_rend__3; @gw_eq_rf_rend__2; @gw_eq_rf_rend]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]] '(@nil Z) 'gwt_X).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_RFI__3; @gw_eq_RFI__2; @gw_eq_RFI]; [@gw_eq_rf_rend__3; @gw_eq_rf_rend__2; @gw_eq_rf_rend]]); first [GwApply.gw_by_name GwI.segs (@QZxv.Mql.rf_getc_fast) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QZxv.Mql.rf_getc_fast)]. Qed.

#[using="Hp"] Lemma rf_getc_fast_lt : ltac2:(Q6nq.ty1 'GwI.segs '(@QZxv.Mql.rf_getc_fast_lt) [[@gw_eq_RFI__3; @gw_eq_RFI__2; @gw_eq_RFI]; [@gw_eq_rf_rend__3; @gw_eq_rf_rend__2; @gw_eq_rf_rend]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]] '(@nil Z) 'gwt_X).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_RFI__3; @gw_eq_RFI__2; @gw_eq_RFI]; [@gw_eq_rf_rend__3; @gw_eq_rf_rend__2; @gw_eq_rf_rend]]); first [GwApply.gw_by_name GwI.segs (@QZxv.Mql.rf_getc_fast_lt) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QZxv.Mql.rf_getc_fast_lt)]. Qed.

#[using="Hp T1"] Lemma rf_getc_slow : ltac2:(Q6nq.ty1 'GwI.segs '(@QZxv.Mql.rf_getc_slow) [[@gw_eq_RFI__3; @gw_eq_RFI__2; @gw_eq_RFI]; [@gw_eq_rf_rend__3; @gw_eq_rf_rend__2; @gw_eq_rf_rend]; [@gw_eq_ssJ__3; @gw_eq_ssJ__2; @gw_eq_ssJ]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]] '(@nil Z) 'gwt_X).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_RFI__3; @gw_eq_RFI__2; @gw_eq_RFI]; [@gw_eq_rf_rend__3; @gw_eq_rf_rend__2; @gw_eq_rf_rend]; [@gw_eq_ssJ__3; @gw_eq_ssJ__2; @gw_eq_ssJ]]); first [GwApply.gw_by_name GwI.segs (@QZxv.Mql.rf_getc_slow) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QZxv.Mql.rf_getc_slow)]. Qed.

#[using="BYT Hp Hnul"] Lemma RFI_getc : forall kmin c f, RFI kmin c f -> c <> 0 -> RFI (kmin + 1) (fst (sh_getc f)) (snd (sh_getc f)).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_RFI__3; @gw_eq_RFI__2; @gw_eq_RFI]]); first [GwApply.gw_by_name GwI.segs (@QZxv.Mql.RFI_getc) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QZxv.Mql.RFI_getc)]. Qed.

#[using="Hp"] Lemma RFI_unget : forall kmin c f, RFI kmin c f -> 1 <= kmin -> RFI (kmin - 1) c (sh_unget f).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_RFI__3; @gw_eq_RFI__2; @gw_eq_RFI]]); first [GwApply.gw_by_name GwI.segs (@QZxv.Mql.RFI_unget) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QZxv.Mql.RFI_unget)]. Qed.

#[using="Type"] Lemma rf_unget_shlim : forall f, (if sh_shlim_neg f then M64 else 0) = (if sh_shlim_neg (sh_unget f) then M64 else 0).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_M64__3; @gw_eq_M64__2; @gw_eq_M64]]); first [GwApply.gw_by_name GwI.segs (@QZxv.Mql.rf_unget_shlim) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QZxv.Mql.rf_unget_shlim)]. Qed.
#[using="Type"] Lemma rf_unget_eq : ltac2:(Q6nq.ty1 'GwI.segs '(@QZxv.Mql.rf_unget_eq) [[@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]] '(@nil Z) 'gwt_X).
Proof. first [GwApply.gw_by_name GwI.segs (@QZxv.Mql.rf_unget_eq) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QZxv.Mql.rf_unget_eq)]. Qed.
#[using="Type"] Lemma rf_unget_nop : forall f, sh_shlim_neg f = true -> sh_unget f = f.
Proof. first [GwApply.gw_by_name GwI.segs (@QZxv.Mql.rf_unget_nop) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QZxv.Mql.rf_unget_nop)]. Qed.
End RF.

Open Scope bv_scope.

Lemma shgetc_callJ : ltac2:(Q6nq.ty1 'GwI.segs '(@QZxv.Mql.shgetc_callJ) [[@gw_eq_SHGETC__3; @gw_eq_SHGETC__2; @gw_eq_SHGETC]; [@gw_eq_rf_cells__3; @gw_eq_rf_cells__2; @gw_eq_rf_cells]; [@gw_eq_rf_rend__3; @gw_eq_rf_rend__2; @gw_eq_rf_rend]; [@gw_eq_rtext__3; @gw_eq_rtext__2; @gw_eq_rtext]; [@gw_eq_shgetc_post__3; @gw_eq_shgetc_post__2; @gw_eq_shgetc_post]; [@gw_eq_ssp_cells__3; @gw_eq_ssp_cells__2; @gw_eq_ssp_cells]; [@gw_eq_RFJ]] '([(-160); 232; 4096]%Z : list Z) '(Q6nq.gwt_zc ssp_guard (Q6nq.gwt_zc got_ssp (Q6nq.gwt_zc SHGETC (Q6nq.gwt_pat (@ssp_guard) (@ssp_guard) (Q6nq.gwt_hdr GwI.ssp_guard (@ssp_guard) (Q6nq.gwt_pat (@got_ssp) (@got_ssp) (Q6nq.gwt_hdr GwI.got_ssp (@got_ssp) gwt_X)))))))).
Proof. rewrite ?gw_eq_RFJ; ltac2:(GwEq.gw_rw [[@gw_eq_SHGETC__3; @gw_eq_SHGETC__2; @gw_eq_SHGETC]; [@gw_eq_rf_cells__3; @gw_eq_rf_cells__2; @gw_eq_rf_cells]; [@gw_eq_rf_rend__3; @gw_eq_rf_rend__2; @gw_eq_rf_rend]; [@gw_eq_rtext__3; @gw_eq_rtext__2; @gw_eq_rtext]; [@gw_eq_shgetc_post__3; @gw_eq_shgetc_post__2; @gw_eq_shgetc_post]; [@gw_eq_ssp_cells__3; @gw_eq_ssp_cells__2; @gw_eq_ssp_cells]]); first [GwApply.gw_by_name GwI.segs (@QZxv.Mql.shgetc_callJ) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QZxv.Mql.shgetc_callJ)]. Qed.
