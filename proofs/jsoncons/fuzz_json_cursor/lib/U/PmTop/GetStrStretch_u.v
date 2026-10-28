(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10PlanKit_u PmLibDefs_u PmLibSpecs_u PmLayout_u PmCurSpecs_u PmFloatCSpecs_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutCert Require Import Pm10CutKit_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutL5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop Require Import TopKit_u TopKit2_u TopSpecs_u ReadKit_u ChunkKit_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutGen Require Cut_getstr_str_csrc_u Cut_getstr_key_csrc_u Cut_getstr_null_csrc_u Cut_getstr_bool_csrc_u Cut_getstr_i64_csrc_u Cut_getstr_u64_csrc_u Cut_getstr_dbl_csrc_u Cut_getstr_bobj_csrc_u Cut_getstr_eobj_csrc_u Cut_getstr_barr_csrc_u Cut_getstr_earr_csrc_u.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module GST.
Definition R_STR : Z := 0x43020.    Definition R_CSTR : Z := 0x430d8.   Definition R_U64 : Z := 0x42f8c.    Definition R_I64 : Z := 0x43040.
Definition R_WD : Z := 0x43004.     Definition R_CONV : Z := 0x430b0.   Definition FLD : Z := 0x42ff4.      Definition WD_CALL : Z := 0x42ff8.
Definition RET : Z := 0x4312c.
End GST.

Module GSS.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).
Module Gstr := Cut_getstr_str_csrc_u.
Module Gkey := Cut_getstr_key_csrc_u.
Module Gnull := Cut_getstr_null_csrc_u.
Module Gbool := Cut_getstr_bool_csrc_u.
Module Gi64 := Cut_getstr_i64_csrc_u.
Module Gu64 := Cut_getstr_u64_csrc_u.
Module Gdbl := Cut_getstr_dbl_csrc_u.
Module Gbobj := Cut_getstr_bobj_csrc_u.
Module Geobj := Cut_getstr_eobj_csrc_u.
Module Gbarr := Cut_getstr_barr_csrc_u.
Module Gearr := Cut_getstr_earr_csrc_u.
Lemma ret_gs : CL.is_ret_at RSEGS GST.RET. Proof. CL.solve_is_ret. Qed.
Lemma nth_gl : forall (gl : list Z) j z, nth_error gl j = Some z -> (j < length gl)%nat.
Proof. intros gl j z H. apply nth_error_Some. rewrite H. discriminate. Qed.

Definition KOG : list nat := [3; 4; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.

Definition KEG (sp1 o : Z) (a : Z) : Prop := ~ (sp1 - 64 <= a < sp1) /\ ~ (o <= a < o + 24).

Section S.
Context {SCFG_P : ScfgP}.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.

Lemma s_g_str : forall (fx : FPState) R M model K sp1 rav o Ev v n,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx ->
  getr R 2%bv = Z_to_bv 64 sp1 -> CK.spok sp1 -> getr R 1%bv = Z_to_bv 64 rav -> L5.ra_ok rav -> getr R 10%bv = Z_to_bv 64 o -> getr R 11%bv = Z_to_bv 64 Ev ->
  2 ^ 40 <= o <= 2 ^ 47 - 24 -> 2 ^ 12 <= Ev <= 2 ^ 47 - 40 -> (o + 24 <= sp1 - 48 \/ sp1 <= o) -> (Ev + 40 <= sp1 - 48 \/ sp1 <= Ev) -> (Ev + 40 <= o \/ o + 24 <= Ev) ->
  0 <= v < 2 ^ 64 -> 0 <= n < 2 ^ 64 ->
  L5.defined M (sp1 - 48) 48 -> L5.defined M o 24 -> L5.u64_at RSEGS M Ev 1 -> L5.defined M (Ev + 8) 16 -> L5.u64_at RSEGS M (Ev + 24) v -> L5.u64_at RSEGS M (Ev + 32) n ->
  PML.img_ro M ->
  (forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 48) -> getr R' 1%bv = Z_to_bv 64 GST.R_STR ->
      getr R' 10%bv = Z_to_bv 64 o -> getr R' 11%bv = Z_to_bv 64 v -> getr R' 12%bv = Z_to_bv 64 n -> getr R' 8%bv = Z_to_bv 64 o -> TK.keepsR KOG R R' ->
      L5.u64_at RSEGS M' (sp1 - 8) rav -> L5.u64_at RSEGS M' (sp1 - 16) (bv_unsigned (getr R 8%bv)) -> L5.u64_at RSEGS M' (sp1 - 24) (bv_unsigned (getr R 9%bv)) -> TK.samem (KEG sp1 o) M M' -> mem_grows M M' -> srealizes RSEGS SCFG (@PML.cfg fx' R' PMCS.PC_STRINIT2 M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R PMCS.PC_GET_STRING M model) K.
Proof.
  intros fx R M model K sp1 rav o Ev v n Hh Hl Hfp H2 [Hsp Hal] H1 Hra H10 H11 Ho HEv D1 D2 D3 Hv Hn DF DO F0 D8 V24 V32 RO Kc.
  change PMCS.PC_GET_STRING with (CC.cp_pc Gstr.cp0).
  assert (Hrav : 0 <= rav < 2 ^ 64) by (destruct Hra; lia).
  pose proof (bv_unsigned_in_range _ (getr R 8%bv)) as G8. pose proof (bv_unsigned_in_range _ (getr R 9%bv)) as G9. change (bv_modulus 64) with (2 ^ 64) in G8, G9.
  set (gl := [0; v; n]).
  ck_open FPM Gstr.cp0 (Gstr.plans 0%nat _ eq_refl) 0 gl (fun _ : nat => @nil byte) (@nil (nat * Z)) sp1 R M fx model K Hh Hl Hfp H2 ck_no_pins.
  - ck_reg E (10%bv : reg) H10. ck_reg E (11%bv : reg) H11. ck_gh E 1%nat v. ck_gh E 2%nat n.
    unfold know_ok, Gstr.cp0. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + e_unk. + e_wr. + e_range. + e_unk. + e_wr. + e_range.
    + ck_kw64 Ev 1 F0. + e_unk. + ck_kw64 (Ev + 24) v V24. + ck_kw64 (Ev + 32) n V32. + tk_kimg RO. + e_disj. + e_disj. + e_disj.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    assert (GH : forall j z, nth_error gl j = Some z -> ev E' (64 + j) = Z_to_bv 64 z).
    { intros j z Hj. pose proof (nth_gl gl j z Hj) as Hj8. change (length gl) with 3%nat in Hj8. change (CC.cp_nx Gstr.cp0) with 67%nat in Hag.
      rewrite <- (proj1 Hag (64 + j)%nat) by lia. exact (CK.hvB_gh_w _ _ _ _ j z Hj). }
    ck_reg E (10%bv : reg) H10. ck_reg E (11%bv : reg) H11. ck_reg E (1%bv : reg) H1. ck_gh E 1%nat v. ck_gh E 2%nat n.
    ck_leaf Hag E'.
    assert (FRM : TK.samem (KEG sp1 o) M M') by (apply (TK.frame_samem _ _ _ _ _ _ _ HLF); intros a Ha (Hk1 & Hk2); cbn [CC.cp_F]; tk_outside).
    pose proof (CC.lf_grows _ _ _ _ _ _ _ HLF) as MG.
    ck_leaf_k k Hnth; [|ck_leaf_end k Hnth].
    apply (Kc fx' R' M' Hfp'); [tk_lin HLF (2%bv : reg) | unfold GST.R_STR; tk_lin HLF (1%bv : reg) | tk_lin HLF (10%bv : reg)
      | tk_reg HLF (11%bv : reg); exact (GH 1%nat _ eq_refl) | tk_reg HLF (12%bv : reg); exact (GH 2%nat _ eq_refl) | tk_lin HLF (8%bv : reg) | ck_keeps HLF Hag64 KOG
      | | | | exact FRM | exact MG]; [ck_cell64 HLF (EVar 2) (-8) (EVar 33); ck_atom | ck_saved HLF Hag64 (-16) 40%nat (8%bv : reg) | ck_saved HLF Hag64 (-24) 41%nat (9%bv : reg)].
Qed.

Lemma s_g_key : forall (fx : FPState) R M model K sp1 rav o Ev v n,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx ->
  getr R 2%bv = Z_to_bv 64 sp1 -> CK.spok sp1 -> getr R 1%bv = Z_to_bv 64 rav -> L5.ra_ok rav -> getr R 10%bv = Z_to_bv 64 o -> getr R 11%bv = Z_to_bv 64 Ev ->
  2 ^ 40 <= o <= 2 ^ 47 - 24 -> 2 ^ 12 <= Ev <= 2 ^ 47 - 40 -> (o + 24 <= sp1 - 48 \/ sp1 <= o) -> (Ev + 40 <= sp1 - 48 \/ sp1 <= Ev) -> (Ev + 40 <= o \/ o + 24 <= Ev) ->
  0 <= v < 2 ^ 64 -> 0 <= n < 2 ^ 64 ->
  L5.defined M (sp1 - 48) 48 -> L5.defined M o 24 -> L5.u64_at RSEGS M Ev 4097 -> L5.defined M (Ev + 8) 16 -> L5.u64_at RSEGS M (Ev + 24) v -> L5.u64_at RSEGS M (Ev + 32) n ->
  PML.img_ro M ->
  (forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 48) -> getr R' 1%bv = Z_to_bv 64 GST.R_STR ->
      getr R' 10%bv = Z_to_bv 64 o -> getr R' 11%bv = Z_to_bv 64 v -> getr R' 12%bv = Z_to_bv 64 n -> getr R' 8%bv = Z_to_bv 64 o -> TK.keepsR KOG R R' ->
      L5.u64_at RSEGS M' (sp1 - 8) rav -> L5.u64_at RSEGS M' (sp1 - 16) (bv_unsigned (getr R 8%bv)) -> L5.u64_at RSEGS M' (sp1 - 24) (bv_unsigned (getr R 9%bv)) -> TK.samem (KEG sp1 o) M M' -> mem_grows M M' -> srealizes RSEGS SCFG (@PML.cfg fx' R' PMCS.PC_STRINIT2 M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R PMCS.PC_GET_STRING M model) K.
Proof.
  intros fx R M model K sp1 rav o Ev v n Hh Hl Hfp H2 [Hsp Hal] H1 Hra H10 H11 Ho HEv D1 D2 D3 Hv Hn DF DO F0 D8 V24 V32 RO Kc.
  change PMCS.PC_GET_STRING with (CC.cp_pc Gkey.cp0).
  assert (Hrav : 0 <= rav < 2 ^ 64) by (destruct Hra; lia).
  pose proof (bv_unsigned_in_range _ (getr R 8%bv)) as G8. pose proof (bv_unsigned_in_range _ (getr R 9%bv)) as G9. change (bv_modulus 64) with (2 ^ 64) in G8, G9.
  set (gl := [0; v; n]).
  ck_open FPM Gkey.cp0 (Gkey.plans 0%nat _ eq_refl) 0 gl (fun _ : nat => @nil byte) (@nil (nat * Z)) sp1 R M fx model K Hh Hl Hfp H2 ck_no_pins.
  - ck_reg E (10%bv : reg) H10. ck_reg E (11%bv : reg) H11. ck_gh E 1%nat v. ck_gh E 2%nat n.
    unfold know_ok, Gkey.cp0. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + e_unk. + e_wr. + e_range. + e_unk. + e_wr. + e_range.
    + ck_kw64 Ev 4097 F0. + e_unk. + ck_kw64 (Ev + 24) v V24. + ck_kw64 (Ev + 32) n V32. + tk_kimg RO. + e_disj. + e_disj. + e_disj.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    assert (GH : forall j z, nth_error gl j = Some z -> ev E' (64 + j) = Z_to_bv 64 z).
    { intros j z Hj. pose proof (nth_gl gl j z Hj) as Hj8. change (length gl) with 3%nat in Hj8. change (CC.cp_nx Gkey.cp0) with 67%nat in Hag.
      rewrite <- (proj1 Hag (64 + j)%nat) by lia. exact (CK.hvB_gh_w _ _ _ _ j z Hj). }
    ck_reg E (10%bv : reg) H10. ck_reg E (11%bv : reg) H11. ck_reg E (1%bv : reg) H1. ck_gh E 1%nat v. ck_gh E 2%nat n.
    ck_leaf Hag E'.
    assert (FRM : TK.samem (KEG sp1 o) M M') by (apply (TK.frame_samem _ _ _ _ _ _ _ HLF); intros a Ha (Hk1 & Hk2); cbn [CC.cp_F]; tk_outside).
    pose proof (CC.lf_grows _ _ _ _ _ _ _ HLF) as MG.
    ck_leaf_k k Hnth; [|ck_leaf_end k Hnth].
    apply (Kc fx' R' M' Hfp'); [tk_lin HLF (2%bv : reg) | unfold GST.R_STR; tk_lin HLF (1%bv : reg) | tk_lin HLF (10%bv : reg)
      | tk_reg HLF (11%bv : reg); exact (GH 1%nat _ eq_refl) | tk_reg HLF (12%bv : reg); exact (GH 2%nat _ eq_refl) | tk_lin HLF (8%bv : reg) | ck_keeps HLF Hag64 KOG
      | | | | exact FRM | exact MG]; [ck_cell64 HLF (EVar 2) (-8) (EVar 33); ck_atom | ck_saved HLF Hag64 (-16) 40%nat (8%bv : reg) | ck_saved HLF Hag64 (-24) 41%nat (9%bv : reg)].
Qed.

Lemma s_g_null : forall (fx : FPState) R M model K sp1 rav o Ev v n,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx ->
  getr R 2%bv = Z_to_bv 64 sp1 -> CK.spok sp1 -> getr R 1%bv = Z_to_bv 64 rav -> L5.ra_ok rav -> getr R 10%bv = Z_to_bv 64 o -> getr R 11%bv = Z_to_bv 64 Ev ->
  2 ^ 40 <= o <= 2 ^ 47 - 24 -> 2 ^ 12 <= Ev <= 2 ^ 47 - 40 -> (o + 24 <= sp1 - 48 \/ sp1 <= o) -> (Ev + 40 <= sp1 - 48 \/ sp1 <= Ev) -> (Ev + 40 <= o \/ o + 24 <= Ev) ->
  0 <= v < 2 ^ 64 -> 0 <= n < 2 ^ 64 ->
  L5.defined M (sp1 - 48) 48 -> L5.defined M o 24 -> L5.u64_at RSEGS M Ev 4 -> L5.defined M (Ev + 8) 16 -> L5.u64_at RSEGS M (Ev + 24) v -> L5.u64_at RSEGS M (Ev + 32) n ->
  PML.img_ro M ->
  (forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 48) -> getr R' 1%bv = Z_to_bv 64 GST.R_CSTR ->
      getr R' 10%bv = Z_to_bv 64 o -> getr R' 11%bv = Z_to_bv 64 PMCS.STR_NULL -> getr R' 8%bv = Z_to_bv 64 o -> TK.keepsR KOG R R' ->
      L5.u64_at RSEGS M' (sp1 - 8) rav -> L5.u64_at RSEGS M' (sp1 - 16) (bv_unsigned (getr R 8%bv)) -> L5.u64_at RSEGS M' (sp1 - 24) (bv_unsigned (getr R 9%bv)) -> TK.samem (KEG sp1 o) M M' -> mem_grows M M' -> srealizes RSEGS SCFG (@PML.cfg fx' R' PMCS.PC_CSTR_CTOR M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R PMCS.PC_GET_STRING M model) K.
Proof.
  intros fx R M model K sp1 rav o Ev v n Hh Hl Hfp H2 [Hsp Hal] H1 Hra H10 H11 Ho HEv D1 D2 D3 Hv Hn DF DO F0 D8 V24 V32 RO Kc.
  change PMCS.PC_GET_STRING with (CC.cp_pc Gnull.cp0).
  assert (Hrav : 0 <= rav < 2 ^ 64) by (destruct Hra; lia).
  pose proof (bv_unsigned_in_range _ (getr R 8%bv)) as G8. pose proof (bv_unsigned_in_range _ (getr R 9%bv)) as G9. change (bv_modulus 64) with (2 ^ 64) in G8, G9.
  set (gl := [0; v; n]).
  ck_open FPM Gnull.cp0 (Gnull.plans 0%nat _ eq_refl) 0 gl (fun _ : nat => @nil byte) (@nil (nat * Z)) sp1 R M fx model K Hh Hl Hfp H2 ck_no_pins.
  - ck_reg E (10%bv : reg) H10. ck_reg E (11%bv : reg) H11. ck_gh E 1%nat v. ck_gh E 2%nat n.
    unfold know_ok, Gnull.cp0. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + e_unk. + e_wr. + e_range. + e_unk. + e_wr. + e_range.
    + ck_kw64 Ev 4 F0. + e_unk. + ck_kw64 (Ev + 24) v V24. + ck_kw64 (Ev + 32) n V32. + tk_kimg RO. + e_disj. + e_disj. + e_disj.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    assert (GH : forall j z, nth_error gl j = Some z -> ev E' (64 + j) = Z_to_bv 64 z).
    { intros j z Hj. pose proof (nth_gl gl j z Hj) as Hj8. change (length gl) with 3%nat in Hj8. change (CC.cp_nx Gnull.cp0) with 67%nat in Hag.
      rewrite <- (proj1 Hag (64 + j)%nat) by lia. exact (CK.hvB_gh_w _ _ _ _ j z Hj). }
    ck_reg E (10%bv : reg) H10. ck_reg E (11%bv : reg) H11. ck_reg E (1%bv : reg) H1. ck_gh E 1%nat v. ck_gh E 2%nat n.
    ck_leaf Hag E'.
    assert (FRM : TK.samem (KEG sp1 o) M M') by (apply (TK.frame_samem _ _ _ _ _ _ _ HLF); intros a Ha (Hk1 & Hk2); cbn [CC.cp_F]; tk_outside).
    pose proof (CC.lf_grows _ _ _ _ _ _ _ HLF) as MG.
    ck_leaf_k k Hnth; [|ck_leaf_end k Hnth].
    apply (Kc fx' R' M' Hfp'); [tk_lin HLF (2%bv : reg) | unfold GST.R_CSTR; tk_lin HLF (1%bv : reg) | tk_lin HLF (10%bv : reg)
      | unfold PMCS.STR_NULL; tk_lin HLF (11%bv : reg) | tk_lin HLF (8%bv : reg) | ck_keeps HLF Hag64 KOG
      | | | | exact FRM | exact MG]; [ck_cell64 HLF (EVar 2) (-8) (EVar 33); ck_atom | ck_saved HLF Hag64 (-16) 40%nat (8%bv : reg) | ck_saved HLF Hag64 (-24) 41%nat (9%bv : reg)].
Qed.

Lemma s_g_bool : forall (fx : FPState) R M model K sp1 rav o Ev v n,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx ->
  getr R 2%bv = Z_to_bv 64 sp1 -> CK.spok sp1 -> getr R 1%bv = Z_to_bv 64 rav -> L5.ra_ok rav -> getr R 10%bv = Z_to_bv 64 o -> getr R 11%bv = Z_to_bv 64 Ev ->
  2 ^ 40 <= o <= 2 ^ 47 - 24 -> 2 ^ 12 <= Ev <= 2 ^ 47 - 40 -> (o + 24 <= sp1 - 48 \/ sp1 <= o) -> (Ev + 40 <= sp1 - 48 \/ sp1 <= Ev) -> (Ev + 40 <= o \/ o + 24 <= Ev) ->
  0 <= v < 2 ^ 64 -> 0 <= n < 2 ^ 64 -> v mod 256 <= 1 ->
  L5.defined M (sp1 - 48) 48 -> L5.defined M o 24 -> L5.u64_at RSEGS M Ev 8 -> L5.defined M (Ev + 8) 16 -> L5.u64_at RSEGS M (Ev + 24) v -> L5.u64_at RSEGS M (Ev + 32) n ->
  PML.img_ro M ->
  (forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 48) -> getr R' 1%bv = Z_to_bv 64 GST.R_CSTR ->
      getr R' 10%bv = Z_to_bv 64 o -> getr R' 11%bv = Z_to_bv 64 (if Z.eqb (v mod 256) 0 then PMCS.STR_FALSE else PMCS.STR_TRUE) -> getr R' 8%bv = Z_to_bv 64 o ->
      TK.keepsR KOG R R' -> L5.u64_at RSEGS M' (sp1 - 8) rav -> L5.u64_at RSEGS M' (sp1 - 16) (bv_unsigned (getr R 8%bv)) -> L5.u64_at RSEGS M' (sp1 - 24) (bv_unsigned (getr R 9%bv)) -> TK.samem (KEG sp1 o) M M' -> mem_grows M M' -> srealizes RSEGS SCFG (@PML.cfg fx' R' PMCS.PC_CSTR_CTOR M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R PMCS.PC_GET_STRING M model) K.
Proof.
  intros fx R M model K sp1 rav o Ev v n Hh Hl Hfp H2 [Hsp Hal] H1 Hra H10 H11 Ho HEv D1 D2 D3 Hv Hn VB1 DF DO F0 D8 V24 V32 RO Kc.
  change PMCS.PC_GET_STRING with (CC.cp_pc Gbool.cp0).
  assert (Hrav : 0 <= rav < 2 ^ 64) by (destruct Hra; lia).
  pose proof (bv_unsigned_in_range _ (getr R 8%bv)) as G8. pose proof (bv_unsigned_in_range _ (getr R 9%bv)) as G9. change (bv_modulus 64) with (2 ^ 64) in G8, G9.
  set (gl := [0; v; n]).
  ck_open FPM Gbool.cp0 (Gbool.plans 0%nat _ eq_refl) 0 gl (fun _ : nat => @nil byte) (@nil (nat * Z)) sp1 R M fx model K Hh Hl Hfp H2 ck_no_pins.
  - ck_reg E (10%bv : reg) H10. ck_reg E (11%bv : reg) H11. ck_gh E 1%nat v. ck_gh E 2%nat n.
    unfold know_ok, Gbool.cp0. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + e_unk. + e_wr. + e_range. + e_unk. + e_wr. + e_range.
    + ck_kw64 Ev 8 F0. + e_unk. + ck_kw64 (Ev + 24) v V24. + ck_kw64 (Ev + 32) n V32. + tk_kimg RO. + e_disj. + e_disj. + e_disj.
    + cbn [kentry_ok edenot]. rewrite <- (Z_to_bv_bv_unsigned _ (ev E 65)). rw_atoms. rewrite (RK.ext_u8_mod v Hv), Z_to_bv_unsigned. unfold bv_wrap.
      change (bv_modulus 64) with (2 ^ 64). pose proof (Z.mod_pos_bound v 256 ltac:(lia)). rewrite (Z.mod_small (v mod 256)) by lia. lia.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    assert (GH : forall j z, nth_error gl j = Some z -> ev E' (64 + j) = Z_to_bv 64 z).
    { intros j z Hj. pose proof (nth_gl gl j z Hj) as Hj8. change (length gl) with 3%nat in Hj8. change (CC.cp_nx Gbool.cp0) with 67%nat in Hag.
      rewrite <- (proj1 Hag (64 + j)%nat) by lia. exact (CK.hvB_gh_w _ _ _ _ j z Hj). }
    ck_reg E (10%bv : reg) H10. ck_reg E (11%bv : reg) H11. ck_reg E (1%bv : reg) H1. ck_gh E 1%nat v. ck_gh E 2%nat n.
    ck_leaf Hag E'.
    assert (FRM : TK.samem (KEG sp1 o) M M') by (apply (TK.frame_samem _ _ _ _ _ _ _ HLF); intros a Ha (Hk1 & Hk2); cbn [CC.cp_F]; tk_outside).
    pose proof (CC.lf_grows _ _ _ _ _ _ _ HLF) as MG.
    destruct k as [|k]; [injection Hnth as <- | destruct k as [|k]; [injection Hnth as <- | destruct k; discriminate Hnth]].
    +
      ck_probes HLF PF. destruct PF as (PF & _). ck_w2z PF. rewrite (RK.ext_u8_mod v Hv) in PF. apply RK.w_inj in PF; [|pose proof (Z.mod_pos_bound v 256 ltac:(lia)); lia | lia].
      apply (Kc fx' R' M' Hfp'); [tk_lin HLF (2%bv : reg) | unfold GST.R_CSTR; tk_lin HLF (1%bv : reg) | tk_lin HLF (10%bv : reg)
        | rewrite PF; cbn -[Z_to_bv]; unfold PMCS.STR_FALSE; tk_lin HLF (11%bv : reg) | tk_lin HLF (8%bv : reg) | ck_keeps HLF Hag64 KOG
        | | | | exact FRM | exact MG]; [ck_cell64 HLF (EVar 2) (-8) (EVar 33); ck_atom | ck_saved HLF Hag64 (-16) 40%nat (8%bv : reg) | ck_saved HLF Hag64 (-24) 41%nat (9%bv : reg)].
    +
      ck_probes HLF PF. destruct PF as (PF & _). ck_w2z PF. rewrite (RK.ext_u8_mod v Hv) in PF. apply RK.w_neq in PF.
      apply (Kc fx' R' M' Hfp'); [tk_lin HLF (2%bv : reg) | unfold GST.R_CSTR; tk_lin HLF (1%bv : reg) | tk_lin HLF (10%bv : reg)
        | rewrite (proj2 (Z.eqb_neq _ _) PF); unfold PMCS.STR_TRUE; tk_lin HLF (11%bv : reg) | tk_lin HLF (8%bv : reg) | ck_keeps HLF Hag64 KOG
        | | | | exact FRM | exact MG]; [ck_cell64 HLF (EVar 2) (-8) (EVar 33); ck_atom | ck_saved HLF Hag64 (-16) 40%nat (8%bv : reg) | ck_saved HLF Hag64 (-24) 41%nat (9%bv : reg)].
Qed.

Lemma s_g_i64 : forall (fx : FPState) R M model K sp1 rav o Ev v n,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx ->
  getr R 2%bv = Z_to_bv 64 sp1 -> CK.spok sp1 -> getr R 1%bv = Z_to_bv 64 rav -> L5.ra_ok rav -> getr R 10%bv = Z_to_bv 64 o -> getr R 11%bv = Z_to_bv 64 Ev ->
  2 ^ 40 <= o <= 2 ^ 47 - 24 -> 2 ^ 12 <= Ev <= 2 ^ 47 - 40 -> (o + 24 <= sp1 - 48 \/ sp1 <= o) -> (Ev + 40 <= sp1 - 48 \/ sp1 <= Ev) -> (Ev + 40 <= o \/ o + 24 <= Ev) ->
  0 <= v < 2 ^ 64 -> 0 <= n < 2 ^ 64 ->
  L5.defined M (sp1 - 48) 48 -> L5.defined M o 24 -> L5.u64_at RSEGS M Ev 16 -> L5.defined M (Ev + 8) 16 -> L5.u64_at RSEGS M (Ev + 24) v -> L5.u64_at RSEGS M (Ev + 32) n ->
  PML.img_ro M ->
  (forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 48) -> getr R' 1%bv = Z_to_bv 64 GST.R_I64 ->
      getr R' 10%bv = Z_to_bv 64 v -> getr R' 11%bv = Z_to_bv 64 o -> getr R' 8%bv = Z_to_bv 64 o -> TK.keepsR KOG R R' ->
      L5.u64_at RSEGS M' (sp1 - 8) rav -> L5.u64_at RSEGS M' (sp1 - 16) (bv_unsigned (getr R 8%bv)) -> L5.u64_at RSEGS M' (sp1 - 24) (bv_unsigned (getr R 9%bv)) -> L5.u64_at RSEGS M' o 0 -> L5.u64_at RSEGS M' (o + 8) 0 -> L5.u64_at RSEGS M' (o + 16) 0 -> TK.samem (KEG sp1 o) M M' -> mem_grows M M' -> srealizes RSEGS SCFG (@PML.cfg fx' R' PMFC.PC_FROM_INT_I64 M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R PMCS.PC_GET_STRING M model) K.
Proof.
  intros fx R M model K sp1 rav o Ev v n Hh Hl Hfp H2 [Hsp Hal] H1 Hra H10 H11 Ho HEv D1 D2 D3 Hv Hn DF DO F0 D8 V24 V32 RO Kc.
  change PMCS.PC_GET_STRING with (CC.cp_pc Gi64.cp0).
  assert (Hrav : 0 <= rav < 2 ^ 64) by (destruct Hra; lia).
  pose proof (bv_unsigned_in_range _ (getr R 8%bv)) as G8. pose proof (bv_unsigned_in_range _ (getr R 9%bv)) as G9. change (bv_modulus 64) with (2 ^ 64) in G8, G9.
  set (gl := [0; v; n]).
  ck_open FPM Gi64.cp0 (Gi64.plans 0%nat _ eq_refl) 0 gl (fun _ : nat => @nil byte) (@nil (nat * Z)) sp1 R M fx model K Hh Hl Hfp H2 ck_no_pins.
  - ck_reg E (10%bv : reg) H10. ck_reg E (11%bv : reg) H11. ck_gh E 1%nat v. ck_gh E 2%nat n.
    unfold know_ok, Gi64.cp0. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + e_unk. + e_wr. + e_range. + e_unk. + e_wr. + e_range.
    + ck_kw64 Ev 16 F0. + e_unk. + ck_kw64 (Ev + 24) v V24. + ck_kw64 (Ev + 32) n V32. + tk_kimg RO. + e_disj. + e_disj. + e_disj.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    assert (GH : forall j z, nth_error gl j = Some z -> ev E' (64 + j) = Z_to_bv 64 z).
    { intros j z Hj. pose proof (nth_gl gl j z Hj) as Hj8. change (length gl) with 3%nat in Hj8. change (CC.cp_nx Gi64.cp0) with 67%nat in Hag.
      rewrite <- (proj1 Hag (64 + j)%nat) by lia. exact (CK.hvB_gh_w _ _ _ _ j z Hj). }
    ck_reg E (10%bv : reg) H10. ck_reg E (11%bv : reg) H11. ck_reg E (1%bv : reg) H1. ck_gh E 1%nat v. ck_gh E 2%nat n.
    ck_leaf Hag E'.
    assert (FRM : TK.samem (KEG sp1 o) M M') by (apply (TK.frame_samem _ _ _ _ _ _ _ HLF); intros a Ha (Hk1 & Hk2); cbn [CC.cp_F]; tk_outside).
    pose proof (CC.lf_grows _ _ _ _ _ _ _ HLF) as MG.
    ck_leaf_k k Hnth; [|ck_leaf_end k Hnth].
    apply (Kc fx' R' M' Hfp'); [tk_lin HLF (2%bv : reg) | unfold GST.R_I64; tk_lin HLF (1%bv : reg) | tk_reg HLF (10%bv : reg); exact (GH 1%nat _ eq_refl) | tk_lin HLF (11%bv : reg)
      | tk_lin HLF (8%bv : reg) | ck_keeps HLF Hag64 KOG | | | | | | | exact FRM | exact MG].
    * ck_cell64 HLF (EVar 2) (-8) (EVar 33); ck_atom.
    * ck_saved HLF Hag64 (-16) 40%nat (8%bv : reg).
    * ck_saved HLF Hag64 (-24) 41%nat (9%bv : reg).
    * replace o with (o + 0) by lia; ck_cell64 HLF (EVar 42) 0 (ELit 0); reflexivity.
    * ck_cell64 HLF (EVar 42) 8 (ELit 0); reflexivity.
    * ck_cell64 HLF (EVar 42) 16 (ELit 0); reflexivity.
Qed.

Lemma s_g_u64 : forall (fx : FPState) R M model K sp1 rav o Ev v n,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx ->
  getr R 2%bv = Z_to_bv 64 sp1 -> CK.spok sp1 -> getr R 1%bv = Z_to_bv 64 rav -> L5.ra_ok rav -> getr R 10%bv = Z_to_bv 64 o -> getr R 11%bv = Z_to_bv 64 Ev ->
  2 ^ 40 <= o <= 2 ^ 47 - 24 -> 2 ^ 12 <= Ev <= 2 ^ 47 - 40 -> (o + 24 <= sp1 - 48 \/ sp1 <= o) -> (Ev + 40 <= sp1 - 48 \/ sp1 <= Ev) -> (Ev + 40 <= o \/ o + 24 <= Ev) ->
  0 <= v < 2 ^ 64 -> 0 <= n < 2 ^ 64 ->
  L5.defined M (sp1 - 48) 48 -> L5.defined M o 24 -> L5.u64_at RSEGS M Ev 32 -> L5.defined M (Ev + 8) 16 -> L5.u64_at RSEGS M (Ev + 24) v -> L5.u64_at RSEGS M (Ev + 32) n ->
  PML.img_ro M ->
  (forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 48) -> getr R' 1%bv = Z_to_bv 64 GST.R_U64 ->
      getr R' 10%bv = Z_to_bv 64 v -> getr R' 11%bv = Z_to_bv 64 o -> getr R' 8%bv = Z_to_bv 64 o -> TK.keepsR KOG R R' ->
      L5.u64_at RSEGS M' (sp1 - 8) rav -> L5.u64_at RSEGS M' (sp1 - 16) (bv_unsigned (getr R 8%bv)) -> L5.u64_at RSEGS M' (sp1 - 24) (bv_unsigned (getr R 9%bv)) -> L5.u64_at RSEGS M' o 0 -> L5.u64_at RSEGS M' (o + 8) 0 -> L5.u64_at RSEGS M' (o + 16) 0 -> TK.samem (KEG sp1 o) M M' -> mem_grows M M' -> srealizes RSEGS SCFG (@PML.cfg fx' R' PMFC.PC_FROM_INT_U64 M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R PMCS.PC_GET_STRING M model) K.
Proof.
  intros fx R M model K sp1 rav o Ev v n Hh Hl Hfp H2 [Hsp Hal] H1 Hra H10 H11 Ho HEv D1 D2 D3 Hv Hn DF DO F0 D8 V24 V32 RO Kc.
  change PMCS.PC_GET_STRING with (CC.cp_pc Gu64.cp0).
  assert (Hrav : 0 <= rav < 2 ^ 64) by (destruct Hra; lia).
  pose proof (bv_unsigned_in_range _ (getr R 8%bv)) as G8. pose proof (bv_unsigned_in_range _ (getr R 9%bv)) as G9. change (bv_modulus 64) with (2 ^ 64) in G8, G9.
  set (gl := [0; v; n]).
  ck_open FPM Gu64.cp0 (Gu64.plans 0%nat _ eq_refl) 0 gl (fun _ : nat => @nil byte) (@nil (nat * Z)) sp1 R M fx model K Hh Hl Hfp H2 ck_no_pins.
  - ck_reg E (10%bv : reg) H10. ck_reg E (11%bv : reg) H11. ck_gh E 1%nat v. ck_gh E 2%nat n.
    unfold know_ok, Gu64.cp0. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + e_unk. + e_wr. + e_range. + e_unk. + e_wr. + e_range.
    + ck_kw64 Ev 32 F0. + e_unk. + ck_kw64 (Ev + 24) v V24. + ck_kw64 (Ev + 32) n V32. + tk_kimg RO. + e_disj. + e_disj. + e_disj.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    assert (GH : forall j z, nth_error gl j = Some z -> ev E' (64 + j) = Z_to_bv 64 z).
    { intros j z Hj. pose proof (nth_gl gl j z Hj) as Hj8. change (length gl) with 3%nat in Hj8. change (CC.cp_nx Gu64.cp0) with 67%nat in Hag.
      rewrite <- (proj1 Hag (64 + j)%nat) by lia. exact (CK.hvB_gh_w _ _ _ _ j z Hj). }
    ck_reg E (10%bv : reg) H10. ck_reg E (11%bv : reg) H11. ck_reg E (1%bv : reg) H1. ck_gh E 1%nat v. ck_gh E 2%nat n.
    ck_leaf Hag E'.
    assert (FRM : TK.samem (KEG sp1 o) M M') by (apply (TK.frame_samem _ _ _ _ _ _ _ HLF); intros a Ha (Hk1 & Hk2); cbn [CC.cp_F]; tk_outside).
    pose proof (CC.lf_grows _ _ _ _ _ _ _ HLF) as MG.
    ck_leaf_k k Hnth; [|ck_leaf_end k Hnth].
    apply (Kc fx' R' M' Hfp'); [tk_lin HLF (2%bv : reg) | unfold GST.R_U64; tk_lin HLF (1%bv : reg) | tk_reg HLF (10%bv : reg); exact (GH 1%nat _ eq_refl) | tk_lin HLF (11%bv : reg)
      | tk_lin HLF (8%bv : reg) | ck_keeps HLF Hag64 KOG | | | | | | | exact FRM | exact MG].
    * ck_cell64 HLF (EVar 2) (-8) (EVar 33); ck_atom.
    * ck_saved HLF Hag64 (-16) 40%nat (8%bv : reg).
    * ck_saved HLF Hag64 (-24) 41%nat (9%bv : reg).
    * replace o with (o + 0) by lia; ck_cell64 HLF (EVar 42) 0 (ELit 0); reflexivity.
    * ck_cell64 HLF (EVar 42) 8 (ELit 0); reflexivity.
    * ck_cell64 HLF (EVar 42) 16 (ELit 0); reflexivity.
Qed.

Lemma s_g_dbl : forall (fx : FPState) R M model K sp1 rav o Ev v n,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx ->
  getr R 2%bv = Z_to_bv 64 sp1 -> CK.spok sp1 -> getr R 1%bv = Z_to_bv 64 rav -> L5.ra_ok rav -> getr R 10%bv = Z_to_bv 64 o -> getr R 11%bv = Z_to_bv 64 Ev ->
  2 ^ 40 <= o <= 2 ^ 47 - 24 -> 2 ^ 12 <= Ev <= 2 ^ 47 - 40 -> (o + 24 <= sp1 - 48 \/ sp1 <= o) -> (Ev + 40 <= sp1 - 48 \/ sp1 <= Ev) -> (Ev + 40 <= o \/ o + 24 <= Ev) ->
  0 <= v < 2 ^ 64 -> 0 <= n < 2 ^ 64 -> L5.defined M (sp1 - 64) 16 -> (o + 24 <= sp1 - 64 \/ sp1 <= o) -> (Ev + 40 <= sp1 - 64 \/ sp1 <= Ev) ->
  L5.defined M (sp1 - 48) 48 -> L5.defined M o 24 -> L5.u64_at RSEGS M Ev 128 -> L5.defined M (Ev + 8) 16 -> L5.u64_at RSEGS M (Ev + 24) v -> L5.u64_at RSEGS M (Ev + 32) n ->
  PML.img_ro M ->
  (forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 48) -> getr R' 8%bv = Z_to_bv 64 o -> getr R' 9%bv = Z_to_bv 64 Ev ->
      TK.keepsR KOG R R' -> L5.u64_at RSEGS M' (sp1 - 8) rav -> L5.u64_at RSEGS M' (sp1 - 16) (bv_unsigned (getr R 8%bv)) -> L5.u64_at RSEGS M' (sp1 - 24) (bv_unsigned (getr R 9%bv)) -> L5.u64_at RSEGS M' o 0 -> L5.u64_at RSEGS M' (o + 8) 0 -> L5.u64_at RSEGS M' (o + 16) 0 ->
      L5.u8_at RSEGS M' (sp1 - 40) 0 -> L5.u32_at RSEGS M' (sp1 - 36) 0 -> L5.u8_at RSEGS M' (sp1 - 32) 46 ->
      TK.samem (KEG sp1 o) M M' -> mem_grows M M' -> srealizes RSEGS SCFG (@PML.cfg fx' R' GST.FLD M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R PMCS.PC_GET_STRING M model) K.
Proof.
  intros fx R M model K sp1 rav o Ev v n Hh Hl Hfp H2 [Hsp Hal] H1 Hra H10 H11 Ho HEv D1 D2 D3 Hv Hn DS OS ES DF DO F0 D8 V24 V32 RO Kc.
  change PMCS.PC_GET_STRING with (CC.cp_pc Gdbl.cp0).
  assert (Hrav : 0 <= rav < 2 ^ 64) by (destruct Hra; lia).
  pose proof (bv_unsigned_in_range _ (getr R 8%bv)) as G8. pose proof (bv_unsigned_in_range _ (getr R 9%bv)) as G9. change (bv_modulus 64) with (2 ^ 64) in G8, G9.
  set (gl := [0; v; n]).
  ck_open FPM Gdbl.cp0 (Gdbl.plans 0%nat _ eq_refl) 0 gl (fun _ : nat => @nil byte) (@nil (nat * Z)) sp1 R M fx model K Hh Hl Hfp H2 ck_no_pins.
  - ck_reg E (10%bv : reg) H10. ck_reg E (11%bv : reg) H11. ck_gh E 1%nat v. ck_gh E 2%nat n.
    unfold know_ok, Gdbl.cp0. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + e_unk. + e_wr. + e_range. + e_unk. + e_wr. + e_range.
    + ck_kw64 Ev 128 F0. + e_unk. + ck_kw64 (Ev + 24) v V24. + ck_kw64 (Ev + 32) n V32. + tk_kimg RO. + e_disj. + e_disj. + e_disj.
    + e_unk. + e_wr. + e_disj. + e_disj.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    assert (GH : forall j z, nth_error gl j = Some z -> ev E' (64 + j) = Z_to_bv 64 z).
    { intros j z Hj. pose proof (nth_gl gl j z Hj) as Hj8. change (length gl) with 3%nat in Hj8. change (CC.cp_nx Gdbl.cp0) with 67%nat in Hag.
      rewrite <- (proj1 Hag (64 + j)%nat) by lia. exact (CK.hvB_gh_w _ _ _ _ j z Hj). }
    ck_reg E (10%bv : reg) H10. ck_reg E (11%bv : reg) H11. ck_reg E (1%bv : reg) H1. ck_gh E 1%nat v. ck_gh E 2%nat n.
    ck_leaf Hag E'.
    assert (FRM : TK.samem (KEG sp1 o) M M') by (apply (TK.frame_samem _ _ _ _ _ _ _ HLF); intros a Ha (Hk1 & Hk2); cbn [CC.cp_F]; tk_outside).
    pose proof (CC.lf_grows _ _ _ _ _ _ _ HLF) as MG.
    ck_leaf_k k Hnth; [|ck_leaf_end k Hnth].
    apply (Kc fx' R' M' Hfp'); [tk_lin HLF (2%bv : reg) | tk_lin HLF (8%bv : reg) | tk_lin HLF (9%bv : reg) | ck_keeps HLF Hag64 KOG | | | | | | | | | | exact FRM | exact MG].
    * ck_cell64 HLF (EVar 2) (-8) (EVar 33); ck_atom.
    * ck_saved HLF Hag64 (-16) 40%nat (8%bv : reg).
    * ck_saved HLF Hag64 (-24) 41%nat (9%bv : reg).
    * replace o with (o + 0) by lia; ck_cell64 HLF (EVar 42) 0 (ELit 0); reflexivity.
    * ck_cell64 HLF (EVar 42) 8 (ELit 0); reflexivity.
    * ck_cell64 HLF (EVar 42) 16 (ELit 0); reflexivity.
    * ck_cell8 HLF (EVar 2) (-40) (ELit 0); reflexivity.
    * ck_cell32 HLF (EVar 2) (-36) (ELit 0); reflexivity.
    * ck_cell8 HLF (EVar 2) (-32) (ELit 46); reflexivity.
Qed.

Lemma s_g_bobj : forall (fx : FPState) R M model K sp1 rav o Ev v n,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx ->
  getr R 2%bv = Z_to_bv 64 sp1 -> CK.spok sp1 -> getr R 1%bv = Z_to_bv 64 rav -> L5.ra_ok rav -> getr R 10%bv = Z_to_bv 64 o -> getr R 11%bv = Z_to_bv 64 Ev ->
  2 ^ 40 <= o <= 2 ^ 47 - 24 -> 2 ^ 12 <= Ev <= 2 ^ 47 - 40 -> (o + 24 <= sp1 - 48 \/ sp1 <= o) -> (Ev + 40 <= sp1 - 48 \/ sp1 <= Ev) -> (Ev + 40 <= o \/ o + 24 <= Ev) ->
  0 <= v < 2 ^ 64 -> 0 <= n < 2 ^ 64 ->
  L5.defined M (sp1 - 48) 48 -> L5.defined M o 24 -> L5.u64_at RSEGS M Ev 256 -> L5.defined M (Ev + 8) 16 -> L5.u64_at RSEGS M (Ev + 24) v -> L5.u64_at RSEGS M (Ev + 32) n ->
  PML.img_ro M ->
  (forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 48) -> getr R' 1%bv = Z_to_bv 64 GST.R_CONV ->
      getr R' 10%bv = getr R 13%bv -> getr R' 11%bv = Z_to_bv 64 11 -> getr R' 8%bv = Z_to_bv 64 o -> TK.keepsR KOG R R' ->
      L5.u64_at RSEGS M' (sp1 - 8) rav -> L5.u64_at RSEGS M' (sp1 - 16) (bv_unsigned (getr R 8%bv)) -> L5.u64_at RSEGS M' (sp1 - 24) (bv_unsigned (getr R 9%bv)) -> TK.samem (KEG sp1 o) M M' -> mem_grows M M' -> srealizes RSEGS SCFG (@PML.cfg fx' R' PMS.PC_CONV_EC M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R PMCS.PC_GET_STRING M model) K.
Proof.
  intros fx R M model K sp1 rav o Ev v n Hh Hl Hfp H2 [Hsp Hal] H1 Hra H10 H11 Ho HEv D1 D2 D3 Hv Hn DF DO F0 D8 V24 V32 RO Kc.
  change PMCS.PC_GET_STRING with (CC.cp_pc Gbobj.cp0).
  assert (Hrav : 0 <= rav < 2 ^ 64) by (destruct Hra; lia).
  pose proof (bv_unsigned_in_range _ (getr R 8%bv)) as G8. pose proof (bv_unsigned_in_range _ (getr R 9%bv)) as G9. change (bv_modulus 64) with (2 ^ 64) in G8, G9.
  set (gl := [0; v; n]).
  ck_open FPM Gbobj.cp0 (Gbobj.plans 0%nat _ eq_refl) 0 gl (fun _ : nat => @nil byte) (@nil (nat * Z)) sp1 R M fx model K Hh Hl Hfp H2 ck_no_pins.
  - ck_reg E (10%bv : reg) H10. ck_reg E (11%bv : reg) H11. ck_gh E 1%nat v. ck_gh E 2%nat n.
    unfold know_ok, Gbobj.cp0. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + e_unk. + e_wr. + e_range. + e_unk. + e_wr. + e_range.
    + ck_kw64 Ev 256 F0. + e_unk. + ck_kw64 (Ev + 24) v V24. + ck_kw64 (Ev + 32) n V32. + tk_kimg RO. + e_disj. + e_disj. + e_disj.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    assert (GH : forall j z, nth_error gl j = Some z -> ev E' (64 + j) = Z_to_bv 64 z).
    { intros j z Hj. pose proof (nth_gl gl j z Hj) as Hj8. change (length gl) with 3%nat in Hj8. change (CC.cp_nx Gbobj.cp0) with 67%nat in Hag.
      rewrite <- (proj1 Hag (64 + j)%nat) by lia. exact (CK.hvB_gh_w _ _ _ _ j z Hj). }
    ck_reg E (10%bv : reg) H10. ck_reg E (11%bv : reg) H11. ck_reg E (1%bv : reg) H1. ck_gh E 1%nat v. ck_gh E 2%nat n.
    ck_leaf Hag E'.
    assert (FRM : TK.samem (KEG sp1 o) M M') by (apply (TK.frame_samem _ _ _ _ _ _ _ HLF); intros a Ha (Hk1 & Hk2); cbn [CC.cp_F]; tk_outside).
    pose proof (CC.lf_grows _ _ _ _ _ _ _ HLF) as MG.
    ck_leaf_k k Hnth; [|ck_leaf_end k Hnth].
    apply (Kc fx' R' M' Hfp'); [tk_lin HLF (2%bv : reg) | unfold GST.R_CONV; tk_lin HLF (1%bv : reg) | ck_keep HLF Hag64 (10%bv : reg) (13%bv : reg) | tk_lin HLF (11%bv : reg)
      | tk_lin HLF (8%bv : reg) | ck_keeps HLF Hag64 KOG | | | | exact FRM | exact MG]; [ck_cell64 HLF (EVar 2) (-8) (EVar 33); ck_atom | ck_saved HLF Hag64 (-16) 40%nat (8%bv : reg) | ck_saved HLF Hag64 (-24) 41%nat (9%bv : reg)].
Qed.

Lemma s_g_eobj : forall (fx : FPState) R M model K sp1 rav o Ev v n,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx ->
  getr R 2%bv = Z_to_bv 64 sp1 -> CK.spok sp1 -> getr R 1%bv = Z_to_bv 64 rav -> L5.ra_ok rav -> getr R 10%bv = Z_to_bv 64 o -> getr R 11%bv = Z_to_bv 64 Ev ->
  2 ^ 40 <= o <= 2 ^ 47 - 24 -> 2 ^ 12 <= Ev <= 2 ^ 47 - 40 -> (o + 24 <= sp1 - 48 \/ sp1 <= o) -> (Ev + 40 <= sp1 - 48 \/ sp1 <= Ev) -> (Ev + 40 <= o \/ o + 24 <= Ev) ->
  0 <= v < 2 ^ 64 -> 0 <= n < 2 ^ 64 ->
  L5.defined M (sp1 - 48) 48 -> L5.defined M o 24 -> L5.u64_at RSEGS M Ev 512 -> L5.defined M (Ev + 8) 16 -> L5.u64_at RSEGS M (Ev + 24) v -> L5.u64_at RSEGS M (Ev + 32) n ->
  PML.img_ro M ->
  (forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 48) -> getr R' 1%bv = Z_to_bv 64 GST.R_CONV ->
      getr R' 10%bv = getr R 13%bv -> getr R' 11%bv = Z_to_bv 64 11 -> getr R' 8%bv = Z_to_bv 64 o -> TK.keepsR KOG R R' ->
      L5.u64_at RSEGS M' (sp1 - 8) rav -> L5.u64_at RSEGS M' (sp1 - 16) (bv_unsigned (getr R 8%bv)) -> L5.u64_at RSEGS M' (sp1 - 24) (bv_unsigned (getr R 9%bv)) -> TK.samem (KEG sp1 o) M M' -> mem_grows M M' -> srealizes RSEGS SCFG (@PML.cfg fx' R' PMS.PC_CONV_EC M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R PMCS.PC_GET_STRING M model) K.
Proof.
  intros fx R M model K sp1 rav o Ev v n Hh Hl Hfp H2 [Hsp Hal] H1 Hra H10 H11 Ho HEv D1 D2 D3 Hv Hn DF DO F0 D8 V24 V32 RO Kc.
  change PMCS.PC_GET_STRING with (CC.cp_pc Geobj.cp0).
  assert (Hrav : 0 <= rav < 2 ^ 64) by (destruct Hra; lia).
  pose proof (bv_unsigned_in_range _ (getr R 8%bv)) as G8. pose proof (bv_unsigned_in_range _ (getr R 9%bv)) as G9. change (bv_modulus 64) with (2 ^ 64) in G8, G9.
  set (gl := [0; v; n]).
  ck_open FPM Geobj.cp0 (Geobj.plans 0%nat _ eq_refl) 0 gl (fun _ : nat => @nil byte) (@nil (nat * Z)) sp1 R M fx model K Hh Hl Hfp H2 ck_no_pins.
  - ck_reg E (10%bv : reg) H10. ck_reg E (11%bv : reg) H11. ck_gh E 1%nat v. ck_gh E 2%nat n.
    unfold know_ok, Geobj.cp0. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + e_unk. + e_wr. + e_range. + e_unk. + e_wr. + e_range.
    + ck_kw64 Ev 512 F0. + e_unk. + ck_kw64 (Ev + 24) v V24. + ck_kw64 (Ev + 32) n V32. + tk_kimg RO. + e_disj. + e_disj. + e_disj.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    assert (GH : forall j z, nth_error gl j = Some z -> ev E' (64 + j) = Z_to_bv 64 z).
    { intros j z Hj. pose proof (nth_gl gl j z Hj) as Hj8. change (length gl) with 3%nat in Hj8. change (CC.cp_nx Geobj.cp0) with 67%nat in Hag.
      rewrite <- (proj1 Hag (64 + j)%nat) by lia. exact (CK.hvB_gh_w _ _ _ _ j z Hj). }
    ck_reg E (10%bv : reg) H10. ck_reg E (11%bv : reg) H11. ck_reg E (1%bv : reg) H1. ck_gh E 1%nat v. ck_gh E 2%nat n.
    ck_leaf Hag E'.
    assert (FRM : TK.samem (KEG sp1 o) M M') by (apply (TK.frame_samem _ _ _ _ _ _ _ HLF); intros a Ha (Hk1 & Hk2); cbn [CC.cp_F]; tk_outside).
    pose proof (CC.lf_grows _ _ _ _ _ _ _ HLF) as MG.
    ck_leaf_k k Hnth; [|ck_leaf_end k Hnth].
    apply (Kc fx' R' M' Hfp'); [tk_lin HLF (2%bv : reg) | unfold GST.R_CONV; tk_lin HLF (1%bv : reg) | ck_keep HLF Hag64 (10%bv : reg) (13%bv : reg) | tk_lin HLF (11%bv : reg)
      | tk_lin HLF (8%bv : reg) | ck_keeps HLF Hag64 KOG | | | | exact FRM | exact MG]; [ck_cell64 HLF (EVar 2) (-8) (EVar 33); ck_atom | ck_saved HLF Hag64 (-16) 40%nat (8%bv : reg) | ck_saved HLF Hag64 (-24) 41%nat (9%bv : reg)].
Qed.

Lemma s_g_barr : forall (fx : FPState) R M model K sp1 rav o Ev v n,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx ->
  getr R 2%bv = Z_to_bv 64 sp1 -> CK.spok sp1 -> getr R 1%bv = Z_to_bv 64 rav -> L5.ra_ok rav -> getr R 10%bv = Z_to_bv 64 o -> getr R 11%bv = Z_to_bv 64 Ev ->
  2 ^ 40 <= o <= 2 ^ 47 - 24 -> 2 ^ 12 <= Ev <= 2 ^ 47 - 40 -> (o + 24 <= sp1 - 48 \/ sp1 <= o) -> (Ev + 40 <= sp1 - 48 \/ sp1 <= Ev) -> (Ev + 40 <= o \/ o + 24 <= Ev) ->
  0 <= v < 2 ^ 64 -> 0 <= n < 2 ^ 64 ->
  L5.defined M (sp1 - 48) 48 -> L5.defined M o 24 -> L5.u64_at RSEGS M Ev 1024 -> L5.defined M (Ev + 8) 16 -> L5.u64_at RSEGS M (Ev + 24) v -> L5.u64_at RSEGS M (Ev + 32) n ->
  PML.img_ro M ->
  (forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 48) -> getr R' 1%bv = Z_to_bv 64 GST.R_CONV ->
      getr R' 10%bv = getr R 13%bv -> getr R' 11%bv = Z_to_bv 64 11 -> getr R' 8%bv = Z_to_bv 64 o -> TK.keepsR KOG R R' ->
      L5.u64_at RSEGS M' (sp1 - 8) rav -> L5.u64_at RSEGS M' (sp1 - 16) (bv_unsigned (getr R 8%bv)) -> L5.u64_at RSEGS M' (sp1 - 24) (bv_unsigned (getr R 9%bv)) -> TK.samem (KEG sp1 o) M M' -> mem_grows M M' -> srealizes RSEGS SCFG (@PML.cfg fx' R' PMS.PC_CONV_EC M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R PMCS.PC_GET_STRING M model) K.
Proof.
  intros fx R M model K sp1 rav o Ev v n Hh Hl Hfp H2 [Hsp Hal] H1 Hra H10 H11 Ho HEv D1 D2 D3 Hv Hn DF DO F0 D8 V24 V32 RO Kc.
  change PMCS.PC_GET_STRING with (CC.cp_pc Gbarr.cp0).
  assert (Hrav : 0 <= rav < 2 ^ 64) by (destruct Hra; lia).
  pose proof (bv_unsigned_in_range _ (getr R 8%bv)) as G8. pose proof (bv_unsigned_in_range _ (getr R 9%bv)) as G9. change (bv_modulus 64) with (2 ^ 64) in G8, G9.
  set (gl := [0; v; n]).
  ck_open FPM Gbarr.cp0 (Gbarr.plans 0%nat _ eq_refl) 0 gl (fun _ : nat => @nil byte) (@nil (nat * Z)) sp1 R M fx model K Hh Hl Hfp H2 ck_no_pins.
  - ck_reg E (10%bv : reg) H10. ck_reg E (11%bv : reg) H11. ck_gh E 1%nat v. ck_gh E 2%nat n.
    unfold know_ok, Gbarr.cp0. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + e_unk. + e_wr. + e_range. + e_unk. + e_wr. + e_range.
    + ck_kw64 Ev 1024 F0. + e_unk. + ck_kw64 (Ev + 24) v V24. + ck_kw64 (Ev + 32) n V32. + tk_kimg RO. + e_disj. + e_disj. + e_disj.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    assert (GH : forall j z, nth_error gl j = Some z -> ev E' (64 + j) = Z_to_bv 64 z).
    { intros j z Hj. pose proof (nth_gl gl j z Hj) as Hj8. change (length gl) with 3%nat in Hj8. change (CC.cp_nx Gbarr.cp0) with 67%nat in Hag.
      rewrite <- (proj1 Hag (64 + j)%nat) by lia. exact (CK.hvB_gh_w _ _ _ _ j z Hj). }
    ck_reg E (10%bv : reg) H10. ck_reg E (11%bv : reg) H11. ck_reg E (1%bv : reg) H1. ck_gh E 1%nat v. ck_gh E 2%nat n.
    ck_leaf Hag E'.
    assert (FRM : TK.samem (KEG sp1 o) M M') by (apply (TK.frame_samem _ _ _ _ _ _ _ HLF); intros a Ha (Hk1 & Hk2); cbn [CC.cp_F]; tk_outside).
    pose proof (CC.lf_grows _ _ _ _ _ _ _ HLF) as MG.
    ck_leaf_k k Hnth; [|ck_leaf_end k Hnth].
    apply (Kc fx' R' M' Hfp'); [tk_lin HLF (2%bv : reg) | unfold GST.R_CONV; tk_lin HLF (1%bv : reg) | ck_keep HLF Hag64 (10%bv : reg) (13%bv : reg) | tk_lin HLF (11%bv : reg)
      | tk_lin HLF (8%bv : reg) | ck_keeps HLF Hag64 KOG | | | | exact FRM | exact MG]; [ck_cell64 HLF (EVar 2) (-8) (EVar 33); ck_atom | ck_saved HLF Hag64 (-16) 40%nat (8%bv : reg) | ck_saved HLF Hag64 (-24) 41%nat (9%bv : reg)].
Qed.

Lemma s_g_earr : forall (fx : FPState) R M model K sp1 rav o Ev v n,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx ->
  getr R 2%bv = Z_to_bv 64 sp1 -> CK.spok sp1 -> getr R 1%bv = Z_to_bv 64 rav -> L5.ra_ok rav -> getr R 10%bv = Z_to_bv 64 o -> getr R 11%bv = Z_to_bv 64 Ev ->
  2 ^ 40 <= o <= 2 ^ 47 - 24 -> 2 ^ 12 <= Ev <= 2 ^ 47 - 40 -> (o + 24 <= sp1 - 48 \/ sp1 <= o) -> (Ev + 40 <= sp1 - 48 \/ sp1 <= Ev) -> (Ev + 40 <= o \/ o + 24 <= Ev) ->
  0 <= v < 2 ^ 64 -> 0 <= n < 2 ^ 64 ->
  L5.defined M (sp1 - 48) 48 -> L5.defined M o 24 -> L5.u64_at RSEGS M Ev 2048 -> L5.defined M (Ev + 8) 16 -> L5.u64_at RSEGS M (Ev + 24) v -> L5.u64_at RSEGS M (Ev + 32) n ->
  PML.img_ro M ->
  (forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 48) -> getr R' 1%bv = Z_to_bv 64 GST.R_CONV ->
      getr R' 10%bv = getr R 13%bv -> getr R' 11%bv = Z_to_bv 64 11 -> getr R' 8%bv = Z_to_bv 64 o -> TK.keepsR KOG R R' ->
      L5.u64_at RSEGS M' (sp1 - 8) rav -> L5.u64_at RSEGS M' (sp1 - 16) (bv_unsigned (getr R 8%bv)) -> L5.u64_at RSEGS M' (sp1 - 24) (bv_unsigned (getr R 9%bv)) -> TK.samem (KEG sp1 o) M M' -> mem_grows M M' -> srealizes RSEGS SCFG (@PML.cfg fx' R' PMS.PC_CONV_EC M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R PMCS.PC_GET_STRING M model) K.
Proof.
  intros fx R M model K sp1 rav o Ev v n Hh Hl Hfp H2 [Hsp Hal] H1 Hra H10 H11 Ho HEv D1 D2 D3 Hv Hn DF DO F0 D8 V24 V32 RO Kc.
  change PMCS.PC_GET_STRING with (CC.cp_pc Gearr.cp0).
  assert (Hrav : 0 <= rav < 2 ^ 64) by (destruct Hra; lia).
  pose proof (bv_unsigned_in_range _ (getr R 8%bv)) as G8. pose proof (bv_unsigned_in_range _ (getr R 9%bv)) as G9. change (bv_modulus 64) with (2 ^ 64) in G8, G9.
  set (gl := [0; v; n]).
  ck_open FPM Gearr.cp0 (Gearr.plans 0%nat _ eq_refl) 0 gl (fun _ : nat => @nil byte) (@nil (nat * Z)) sp1 R M fx model K Hh Hl Hfp H2 ck_no_pins.
  - ck_reg E (10%bv : reg) H10. ck_reg E (11%bv : reg) H11. ck_gh E 1%nat v. ck_gh E 2%nat n.
    unfold know_ok, Gearr.cp0. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + e_unk. + e_wr. + e_range. + e_unk. + e_wr. + e_range.
    + ck_kw64 Ev 2048 F0. + e_unk. + ck_kw64 (Ev + 24) v V24. + ck_kw64 (Ev + 32) n V32. + tk_kimg RO. + e_disj. + e_disj. + e_disj.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    assert (GH : forall j z, nth_error gl j = Some z -> ev E' (64 + j) = Z_to_bv 64 z).
    { intros j z Hj. pose proof (nth_gl gl j z Hj) as Hj8. change (length gl) with 3%nat in Hj8. change (CC.cp_nx Gearr.cp0) with 67%nat in Hag.
      rewrite <- (proj1 Hag (64 + j)%nat) by lia. exact (CK.hvB_gh_w _ _ _ _ j z Hj). }
    ck_reg E (10%bv : reg) H10. ck_reg E (11%bv : reg) H11. ck_reg E (1%bv : reg) H1. ck_gh E 1%nat v. ck_gh E 2%nat n.
    ck_leaf Hag E'.
    assert (FRM : TK.samem (KEG sp1 o) M M') by (apply (TK.frame_samem _ _ _ _ _ _ _ HLF); intros a Ha (Hk1 & Hk2); cbn [CC.cp_F]; tk_outside).
    pose proof (CC.lf_grows _ _ _ _ _ _ _ HLF) as MG.
    ck_leaf_k k Hnth; [|ck_leaf_end k Hnth].
    apply (Kc fx' R' M' Hfp'); [tk_lin HLF (2%bv : reg) | unfold GST.R_CONV; tk_lin HLF (1%bv : reg) | ck_keep HLF Hag64 (10%bv : reg) (13%bv : reg) | tk_lin HLF (11%bv : reg)
      | tk_lin HLF (8%bv : reg) | ck_keeps HLF Hag64 KOG | | | | exact FRM | exact MG]; [ck_cell64 HLF (EVar 2) (-8) (EVar 33); ck_atom | ck_saved HLF Hag64 (-16) 40%nat (8%bv : reg) | ck_saved HLF Hag64 (-24) 41%nat (9%bv : reg)].
Qed.

Lemma s_g_rstr : forall (fx : FPState) R M model K sp1 rav s0v s1v,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp1 - 48) -> CK.spok sp1 -> L5.ra_ok rav ->
  0 <= s0v < 2 ^ 64 -> 0 <= s1v < 2 ^ 64 -> L5.u64_at RSEGS M (sp1 - 8) rav -> L5.u64_at RSEGS M (sp1 - 16) s0v -> L5.u64_at RSEGS M (sp1 - 24) s1v ->
  (forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 sp1 -> getr R' 8%bv = Z_to_bv 64 s0v -> getr R' 9%bv = Z_to_bv 64 s1v ->
      TK.keepsR KOG R R' -> TK.samem (fun _ => True) M M' -> mem_grows M M' -> srealizes RSEGS SCFG (@PML.cfg fx' R' rav M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R GST.R_STR M model) K.
Proof.
  intros fx R M model K sp1 rav s0v s1v Hh Hl Hfp H2 [Hsp Hal] Hra Hs0 Hs1 F1 F2 F3 Kret.
  change GST.R_STR with (CC.cp_pc Gstr.cp1).
  assert (Hrav : 0 <= rav < 2 ^ 64) by (destruct Hra; lia).
  set (gl := [rav; s0v; s1v]).
  ck_open FPM Gstr.cp1 (Gstr.plans 1%nat _ eq_refl) (-48) gl (fun _ : nat => @nil byte) (@nil (nat * Z)) sp1 R M fx model K Hh Hl Hfp H2 ck_no_pins.
  - ck_gh E 0%nat rav. ck_gh E 1%nat s0v. ck_gh E 2%nat s1v.
    unfold know_ok, Gstr.cp1. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + ck_kw64 (sp1 - 8) rav F1. + ck_kw64 (sp1 - 16) s0v F2. + ck_kw64 (sp1 - 24) s1v F3.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    assert (GH : forall j z, nth_error gl j = Some z -> ev E' (64 + j) = Z_to_bv 64 z).
    { intros j z Hj. pose proof (nth_gl gl j z Hj) as Hj8. change (length gl) with 3%nat in Hj8. change (CC.cp_nx Gstr.cp1) with 67%nat in Hag.
      rewrite <- (proj1 Hag (64 + j)%nat) by lia. exact (CK.hvB_gh_w _ _ _ _ j z Hj). }
    ck_leaf Hag E'.
    assert (FRM : TK.samem (fun _ => True) M M') by (apply (TK.frame_samem _ _ _ _ _ _ _ HLF); intros a Ha _; cbn [CC.cp_F]; tk_outside).
    pose proof (CC.lf_grows _ _ _ _ _ _ _ HLF) as MG.
    ck_leaf_k k Hnth; [|ck_leaf_end k Hnth].
    assert (R1 : getr R' 1%bv = Z_to_bv 64 rav) by (tk_reg HLF (1%bv : reg); exact (GH 0%nat _ eq_refl)).
    apply (CK.ret_leaf fx' R' _ M' model K rav ret_gs Hh Hl R1 Hra).
    apply (Kret fx' R' M' Hfp'); [tk_lin HLF (2%bv : reg) | tk_reg HLF (8%bv : reg); exact (GH 1%nat _ eq_refl) | tk_reg HLF (9%bv : reg); exact (GH 2%nat _ eq_refl)
      | ck_keeps HLF Hag64 KOG | exact FRM | exact MG].
Qed.

Lemma s_g_rkey : forall (fx : FPState) R M model K sp1 rav s0v s1v,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp1 - 48) -> CK.spok sp1 -> L5.ra_ok rav ->
  0 <= s0v < 2 ^ 64 -> 0 <= s1v < 2 ^ 64 -> L5.u64_at RSEGS M (sp1 - 8) rav -> L5.u64_at RSEGS M (sp1 - 16) s0v -> L5.u64_at RSEGS M (sp1 - 24) s1v ->
  (forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 sp1 -> getr R' 8%bv = Z_to_bv 64 s0v -> getr R' 9%bv = Z_to_bv 64 s1v ->
      TK.keepsR KOG R R' -> TK.samem (fun _ => True) M M' -> mem_grows M M' -> srealizes RSEGS SCFG (@PML.cfg fx' R' rav M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R GST.R_STR M model) K.
Proof.
  intros fx R M model K sp1 rav s0v s1v Hh Hl Hfp H2 [Hsp Hal] Hra Hs0 Hs1 F1 F2 F3 Kret.
  change GST.R_STR with (CC.cp_pc Gkey.cp1).
  assert (Hrav : 0 <= rav < 2 ^ 64) by (destruct Hra; lia).
  set (gl := [rav; s0v; s1v]).
  ck_open FPM Gkey.cp1 (Gkey.plans 1%nat _ eq_refl) (-48) gl (fun _ : nat => @nil byte) (@nil (nat * Z)) sp1 R M fx model K Hh Hl Hfp H2 ck_no_pins.
  - ck_gh E 0%nat rav. ck_gh E 1%nat s0v. ck_gh E 2%nat s1v.
    unfold know_ok, Gkey.cp1. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + ck_kw64 (sp1 - 8) rav F1. + ck_kw64 (sp1 - 16) s0v F2. + ck_kw64 (sp1 - 24) s1v F3.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    assert (GH : forall j z, nth_error gl j = Some z -> ev E' (64 + j) = Z_to_bv 64 z).
    { intros j z Hj. pose proof (nth_gl gl j z Hj) as Hj8. change (length gl) with 3%nat in Hj8. change (CC.cp_nx Gkey.cp1) with 67%nat in Hag.
      rewrite <- (proj1 Hag (64 + j)%nat) by lia. exact (CK.hvB_gh_w _ _ _ _ j z Hj). }
    ck_leaf Hag E'.
    assert (FRM : TK.samem (fun _ => True) M M') by (apply (TK.frame_samem _ _ _ _ _ _ _ HLF); intros a Ha _; cbn [CC.cp_F]; tk_outside).
    pose proof (CC.lf_grows _ _ _ _ _ _ _ HLF) as MG.
    ck_leaf_k k Hnth; [|ck_leaf_end k Hnth].
    assert (R1 : getr R' 1%bv = Z_to_bv 64 rav) by (tk_reg HLF (1%bv : reg); exact (GH 0%nat _ eq_refl)).
    apply (CK.ret_leaf fx' R' _ M' model K rav ret_gs Hh Hl R1 Hra).
    apply (Kret fx' R' M' Hfp'); [tk_lin HLF (2%bv : reg) | tk_reg HLF (8%bv : reg); exact (GH 1%nat _ eq_refl) | tk_reg HLF (9%bv : reg); exact (GH 2%nat _ eq_refl)
      | ck_keeps HLF Hag64 KOG | exact FRM | exact MG].
Qed.

Lemma s_g_rnull : forall (fx : FPState) R M model K sp1 rav s0v s1v,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp1 - 48) -> CK.spok sp1 -> L5.ra_ok rav ->
  0 <= s0v < 2 ^ 64 -> 0 <= s1v < 2 ^ 64 -> L5.u64_at RSEGS M (sp1 - 8) rav -> L5.u64_at RSEGS M (sp1 - 16) s0v -> L5.u64_at RSEGS M (sp1 - 24) s1v ->
  (forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 sp1 -> getr R' 8%bv = Z_to_bv 64 s0v -> getr R' 9%bv = Z_to_bv 64 s1v ->
      TK.keepsR KOG R R' -> TK.samem (fun _ => True) M M' -> mem_grows M M' -> srealizes RSEGS SCFG (@PML.cfg fx' R' rav M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R GST.R_CSTR M model) K.
Proof.
  intros fx R M model K sp1 rav s0v s1v Hh Hl Hfp H2 [Hsp Hal] Hra Hs0 Hs1 F1 F2 F3 Kret.
  change GST.R_CSTR with (CC.cp_pc Gnull.cp1).
  assert (Hrav : 0 <= rav < 2 ^ 64) by (destruct Hra; lia).
  set (gl := [rav; s0v; s1v]).
  ck_open FPM Gnull.cp1 (Gnull.plans 1%nat _ eq_refl) (-48) gl (fun _ : nat => @nil byte) (@nil (nat * Z)) sp1 R M fx model K Hh Hl Hfp H2 ck_no_pins.
  - ck_gh E 0%nat rav. ck_gh E 1%nat s0v. ck_gh E 2%nat s1v.
    unfold know_ok, Gnull.cp1. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + ck_kw64 (sp1 - 8) rav F1. + ck_kw64 (sp1 - 16) s0v F2. + ck_kw64 (sp1 - 24) s1v F3.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    assert (GH : forall j z, nth_error gl j = Some z -> ev E' (64 + j) = Z_to_bv 64 z).
    { intros j z Hj. pose proof (nth_gl gl j z Hj) as Hj8. change (length gl) with 3%nat in Hj8. change (CC.cp_nx Gnull.cp1) with 67%nat in Hag.
      rewrite <- (proj1 Hag (64 + j)%nat) by lia. exact (CK.hvB_gh_w _ _ _ _ j z Hj). }
    ck_leaf Hag E'.
    assert (FRM : TK.samem (fun _ => True) M M') by (apply (TK.frame_samem _ _ _ _ _ _ _ HLF); intros a Ha _; cbn [CC.cp_F]; tk_outside).
    pose proof (CC.lf_grows _ _ _ _ _ _ _ HLF) as MG.
    ck_leaf_k k Hnth; [|ck_leaf_end k Hnth].
    assert (R1 : getr R' 1%bv = Z_to_bv 64 rav) by (tk_reg HLF (1%bv : reg); exact (GH 0%nat _ eq_refl)).
    apply (CK.ret_leaf fx' R' _ M' model K rav ret_gs Hh Hl R1 Hra).
    apply (Kret fx' R' M' Hfp'); [tk_lin HLF (2%bv : reg) | tk_reg HLF (8%bv : reg); exact (GH 1%nat _ eq_refl) | tk_reg HLF (9%bv : reg); exact (GH 2%nat _ eq_refl)
      | ck_keeps HLF Hag64 KOG | exact FRM | exact MG].
Qed.

Lemma s_g_rbool : forall (fx : FPState) R M model K sp1 rav s0v s1v,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp1 - 48) -> CK.spok sp1 -> L5.ra_ok rav ->
  0 <= s0v < 2 ^ 64 -> 0 <= s1v < 2 ^ 64 -> L5.u64_at RSEGS M (sp1 - 8) rav -> L5.u64_at RSEGS M (sp1 - 16) s0v -> L5.u64_at RSEGS M (sp1 - 24) s1v ->
  (forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 sp1 -> getr R' 8%bv = Z_to_bv 64 s0v -> getr R' 9%bv = Z_to_bv 64 s1v ->
      TK.keepsR KOG R R' -> TK.samem (fun _ => True) M M' -> mem_grows M M' -> srealizes RSEGS SCFG (@PML.cfg fx' R' rav M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R GST.R_CSTR M model) K.
Proof.
  intros fx R M model K sp1 rav s0v s1v Hh Hl Hfp H2 [Hsp Hal] Hra Hs0 Hs1 F1 F2 F3 Kret.
  change GST.R_CSTR with (CC.cp_pc Gbool.cp1).
  assert (Hrav : 0 <= rav < 2 ^ 64) by (destruct Hra; lia).
  set (gl := [rav; s0v; s1v]).
  ck_open FPM Gbool.cp1 (Gbool.plans 1%nat _ eq_refl) (-48) gl (fun _ : nat => @nil byte) (@nil (nat * Z)) sp1 R M fx model K Hh Hl Hfp H2 ck_no_pins.
  - ck_gh E 0%nat rav. ck_gh E 1%nat s0v. ck_gh E 2%nat s1v.
    unfold know_ok, Gbool.cp1. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + ck_kw64 (sp1 - 8) rav F1. + ck_kw64 (sp1 - 16) s0v F2. + ck_kw64 (sp1 - 24) s1v F3.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    assert (GH : forall j z, nth_error gl j = Some z -> ev E' (64 + j) = Z_to_bv 64 z).
    { intros j z Hj. pose proof (nth_gl gl j z Hj) as Hj8. change (length gl) with 3%nat in Hj8. change (CC.cp_nx Gbool.cp1) with 67%nat in Hag.
      rewrite <- (proj1 Hag (64 + j)%nat) by lia. exact (CK.hvB_gh_w _ _ _ _ j z Hj). }
    ck_leaf Hag E'.
    assert (FRM : TK.samem (fun _ => True) M M') by (apply (TK.frame_samem _ _ _ _ _ _ _ HLF); intros a Ha _; cbn [CC.cp_F]; tk_outside).
    pose proof (CC.lf_grows _ _ _ _ _ _ _ HLF) as MG.
    ck_leaf_k k Hnth; [|ck_leaf_end k Hnth].
    assert (R1 : getr R' 1%bv = Z_to_bv 64 rav) by (tk_reg HLF (1%bv : reg); exact (GH 0%nat _ eq_refl)).
    apply (CK.ret_leaf fx' R' _ M' model K rav ret_gs Hh Hl R1 Hra).
    apply (Kret fx' R' M' Hfp'); [tk_lin HLF (2%bv : reg) | tk_reg HLF (8%bv : reg); exact (GH 1%nat _ eq_refl) | tk_reg HLF (9%bv : reg); exact (GH 2%nat _ eq_refl)
      | ck_keeps HLF Hag64 KOG | exact FRM | exact MG].
Qed.

Lemma s_g_ri64 : forall (fx : FPState) R M model K sp1 rav s0v s1v,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp1 - 48) -> CK.spok sp1 -> L5.ra_ok rav ->
  0 <= s0v < 2 ^ 64 -> 0 <= s1v < 2 ^ 64 -> L5.u64_at RSEGS M (sp1 - 8) rav -> L5.u64_at RSEGS M (sp1 - 16) s0v -> L5.u64_at RSEGS M (sp1 - 24) s1v ->
  (forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 sp1 -> getr R' 8%bv = Z_to_bv 64 s0v -> getr R' 9%bv = Z_to_bv 64 s1v ->
      TK.keepsR KOG R R' -> TK.samem (fun _ => True) M M' -> mem_grows M M' -> srealizes RSEGS SCFG (@PML.cfg fx' R' rav M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R GST.R_I64 M model) K.
Proof.
  intros fx R M model K sp1 rav s0v s1v Hh Hl Hfp H2 [Hsp Hal] Hra Hs0 Hs1 F1 F2 F3 Kret.
  change GST.R_I64 with (CC.cp_pc Gi64.cp1).
  assert (Hrav : 0 <= rav < 2 ^ 64) by (destruct Hra; lia).
  set (gl := [rav; s0v; s1v]).
  ck_open FPM Gi64.cp1 (Gi64.plans 1%nat _ eq_refl) (-48) gl (fun _ : nat => @nil byte) (@nil (nat * Z)) sp1 R M fx model K Hh Hl Hfp H2 ck_no_pins.
  - ck_gh E 0%nat rav. ck_gh E 1%nat s0v. ck_gh E 2%nat s1v.
    unfold know_ok, Gi64.cp1. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + ck_kw64 (sp1 - 8) rav F1. + ck_kw64 (sp1 - 16) s0v F2. + ck_kw64 (sp1 - 24) s1v F3.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    assert (GH : forall j z, nth_error gl j = Some z -> ev E' (64 + j) = Z_to_bv 64 z).
    { intros j z Hj. pose proof (nth_gl gl j z Hj) as Hj8. change (length gl) with 3%nat in Hj8. change (CC.cp_nx Gi64.cp1) with 67%nat in Hag.
      rewrite <- (proj1 Hag (64 + j)%nat) by lia. exact (CK.hvB_gh_w _ _ _ _ j z Hj). }
    ck_leaf Hag E'.
    assert (FRM : TK.samem (fun _ => True) M M') by (apply (TK.frame_samem _ _ _ _ _ _ _ HLF); intros a Ha _; cbn [CC.cp_F]; tk_outside).
    pose proof (CC.lf_grows _ _ _ _ _ _ _ HLF) as MG.
    ck_leaf_k k Hnth; [|ck_leaf_end k Hnth].
    assert (R1 : getr R' 1%bv = Z_to_bv 64 rav) by (tk_reg HLF (1%bv : reg); exact (GH 0%nat _ eq_refl)).
    apply (CK.ret_leaf fx' R' _ M' model K rav ret_gs Hh Hl R1 Hra).
    apply (Kret fx' R' M' Hfp'); [tk_lin HLF (2%bv : reg) | tk_reg HLF (8%bv : reg); exact (GH 1%nat _ eq_refl) | tk_reg HLF (9%bv : reg); exact (GH 2%nat _ eq_refl)
      | ck_keeps HLF Hag64 KOG | exact FRM | exact MG].
Qed.

Lemma s_g_ru64 : forall (fx : FPState) R M model K sp1 rav s0v s1v,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp1 - 48) -> CK.spok sp1 -> L5.ra_ok rav ->
  0 <= s0v < 2 ^ 64 -> 0 <= s1v < 2 ^ 64 -> L5.u64_at RSEGS M (sp1 - 8) rav -> L5.u64_at RSEGS M (sp1 - 16) s0v -> L5.u64_at RSEGS M (sp1 - 24) s1v ->
  (forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 sp1 -> getr R' 8%bv = Z_to_bv 64 s0v -> getr R' 9%bv = Z_to_bv 64 s1v ->
      TK.keepsR KOG R R' -> TK.samem (fun _ => True) M M' -> mem_grows M M' -> srealizes RSEGS SCFG (@PML.cfg fx' R' rav M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R GST.R_U64 M model) K.
Proof.
  intros fx R M model K sp1 rav s0v s1v Hh Hl Hfp H2 [Hsp Hal] Hra Hs0 Hs1 F1 F2 F3 Kret.
  change GST.R_U64 with (CC.cp_pc Gu64.cp1).
  assert (Hrav : 0 <= rav < 2 ^ 64) by (destruct Hra; lia).
  set (gl := [rav; s0v; s1v]).
  ck_open FPM Gu64.cp1 (Gu64.plans 1%nat _ eq_refl) (-48) gl (fun _ : nat => @nil byte) (@nil (nat * Z)) sp1 R M fx model K Hh Hl Hfp H2 ck_no_pins.
  - ck_gh E 0%nat rav. ck_gh E 1%nat s0v. ck_gh E 2%nat s1v.
    unfold know_ok, Gu64.cp1. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + ck_kw64 (sp1 - 8) rav F1. + ck_kw64 (sp1 - 16) s0v F2. + ck_kw64 (sp1 - 24) s1v F3.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    assert (GH : forall j z, nth_error gl j = Some z -> ev E' (64 + j) = Z_to_bv 64 z).
    { intros j z Hj. pose proof (nth_gl gl j z Hj) as Hj8. change (length gl) with 3%nat in Hj8. change (CC.cp_nx Gu64.cp1) with 67%nat in Hag.
      rewrite <- (proj1 Hag (64 + j)%nat) by lia. exact (CK.hvB_gh_w _ _ _ _ j z Hj). }
    ck_leaf Hag E'.
    assert (FRM : TK.samem (fun _ => True) M M') by (apply (TK.frame_samem _ _ _ _ _ _ _ HLF); intros a Ha _; cbn [CC.cp_F]; tk_outside).
    pose proof (CC.lf_grows _ _ _ _ _ _ _ HLF) as MG.
    ck_leaf_k k Hnth; [|ck_leaf_end k Hnth].
    assert (R1 : getr R' 1%bv = Z_to_bv 64 rav) by (tk_reg HLF (1%bv : reg); exact (GH 0%nat _ eq_refl)).
    apply (CK.ret_leaf fx' R' _ M' model K rav ret_gs Hh Hl R1 Hra).
    apply (Kret fx' R' M' Hfp'); [tk_lin HLF (2%bv : reg) | tk_reg HLF (8%bv : reg); exact (GH 1%nat _ eq_refl) | tk_reg HLF (9%bv : reg); exact (GH 2%nat _ eq_refl)
      | ck_keeps HLF Hag64 KOG | exact FRM | exact MG].
Qed.

Lemma s_g_rdbl : forall (fx : FPState) R M model K sp1 rav s0v s1v,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp1 - 48) -> CK.spok sp1 -> L5.ra_ok rav ->
  0 <= s0v < 2 ^ 64 -> 0 <= s1v < 2 ^ 64 -> L5.u64_at RSEGS M (sp1 - 8) rav -> L5.u64_at RSEGS M (sp1 - 16) s0v -> L5.u64_at RSEGS M (sp1 - 24) s1v ->
  (forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 sp1 -> getr R' 8%bv = Z_to_bv 64 s0v -> getr R' 9%bv = Z_to_bv 64 s1v ->
      TK.keepsR KOG R R' -> TK.samem (fun _ => True) M M' -> mem_grows M M' -> srealizes RSEGS SCFG (@PML.cfg fx' R' rav M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R GST.R_WD M model) K.
Proof.
  intros fx R M model K sp1 rav s0v s1v Hh Hl Hfp H2 [Hsp Hal] Hra Hs0 Hs1 F1 F2 F3 Kret.
  change GST.R_WD with (CC.cp_pc Gdbl.cp2).
  assert (Hrav : 0 <= rav < 2 ^ 64) by (destruct Hra; lia).
  set (gl := [rav; s0v; s1v]).
  ck_open FPM Gdbl.cp2 (Gdbl.plans 2%nat _ eq_refl) (-48) gl (fun _ : nat => @nil byte) (@nil (nat * Z)) sp1 R M fx model K Hh Hl Hfp H2 ck_no_pins.
  - ck_gh E 0%nat rav. ck_gh E 1%nat s0v. ck_gh E 2%nat s1v.
    unfold know_ok, Gdbl.cp2. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + ck_kw64 (sp1 - 8) rav F1. + ck_kw64 (sp1 - 16) s0v F2. + ck_kw64 (sp1 - 24) s1v F3.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    assert (GH : forall j z, nth_error gl j = Some z -> ev E' (64 + j) = Z_to_bv 64 z).
    { intros j z Hj. pose proof (nth_gl gl j z Hj) as Hj8. change (length gl) with 3%nat in Hj8. change (CC.cp_nx Gdbl.cp2) with 67%nat in Hag.
      rewrite <- (proj1 Hag (64 + j)%nat) by lia. exact (CK.hvB_gh_w _ _ _ _ j z Hj). }
    ck_leaf Hag E'.
    assert (FRM : TK.samem (fun _ => True) M M') by (apply (TK.frame_samem _ _ _ _ _ _ _ HLF); intros a Ha _; cbn [CC.cp_F]; tk_outside).
    pose proof (CC.lf_grows _ _ _ _ _ _ _ HLF) as MG.
    ck_leaf_k k Hnth; [|ck_leaf_end k Hnth].
    assert (R1 : getr R' 1%bv = Z_to_bv 64 rav) by (tk_reg HLF (1%bv : reg); exact (GH 0%nat _ eq_refl)).
    apply (CK.ret_leaf fx' R' _ M' model K rav ret_gs Hh Hl R1 Hra).
    apply (Kret fx' R' M' Hfp'); [tk_lin HLF (2%bv : reg) | tk_reg HLF (8%bv : reg); exact (GH 1%nat _ eq_refl) | tk_reg HLF (9%bv : reg); exact (GH 2%nat _ eq_refl)
      | ck_keeps HLF Hag64 KOG | exact FRM | exact MG].
Qed.

Lemma s_g_rbobj : forall (fx : FPState) R M model K sp1 rav s0v s1v o,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp1 - 48) -> CK.spok sp1 -> L5.ra_ok rav -> getr R 8%bv = Z_to_bv 64 o ->
  0 <= s0v < 2 ^ 64 -> 0 <= s1v < 2 ^ 64 -> L5.u64_at RSEGS M (sp1 - 8) rav -> L5.u64_at RSEGS M (sp1 - 16) s0v -> L5.u64_at RSEGS M (sp1 - 24) s1v ->
  2 ^ 40 <= o <= 2 ^ 47 - 24 -> (o + 24 <= sp1 - 48 \/ sp1 <= o) -> L5.defined M o 24 ->
  (forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 sp1 -> getr R' 8%bv = Z_to_bv 64 s0v -> getr R' 9%bv = Z_to_bv 64 s1v ->
      TK.keepsR KOG R R' -> L5.u64_at RSEGS M' o 0 -> L5.u64_at RSEGS M' (o + 8) 0 -> L5.u64_at RSEGS M' (o + 16) 0 ->
      TK.samem (fun a => ~ (o <= a < o + 24)) M M' -> mem_grows M M' -> srealizes RSEGS SCFG (@PML.cfg fx' R' rav M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R GST.R_CONV M model) K.
Proof.
  intros fx R M model K sp1 rav s0v s1v o Hh Hl Hfp H2 [Hsp Hal] Hra H8 Hs0 Hs1 F1 F2 F3 Ho D1 DO Kret.
  change GST.R_CONV with (CC.cp_pc Gbobj.cp1).
  assert (Hrav : 0 <= rav < 2 ^ 64) by (destruct Hra; lia).
  set (gl := [rav; s0v; s1v]).
  ck_open FPM Gbobj.cp1 (Gbobj.plans 1%nat _ eq_refl) (-48) gl (fun _ : nat => @nil byte) (@nil (nat * Z)) sp1 R M fx model K Hh Hl Hfp H2 ck_no_pins.
  - ck_reg E (8%bv : reg) H8. ck_gh E 0%nat rav. ck_gh E 1%nat s0v. ck_gh E 2%nat s1v.
    unfold know_ok, Gbobj.cp1. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + ck_kw64 (sp1 - 8) rav F1. + ck_kw64 (sp1 - 16) s0v F2. + ck_kw64 (sp1 - 24) s1v F3. + e_range. + e_unk. + e_wr. + e_disj.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    assert (GH : forall j z, nth_error gl j = Some z -> ev E' (64 + j) = Z_to_bv 64 z).
    { intros j z Hj. pose proof (nth_gl gl j z Hj) as Hj8. change (length gl) with 3%nat in Hj8. change (CC.cp_nx Gbobj.cp1) with 67%nat in Hag.
      rewrite <- (proj1 Hag (64 + j)%nat) by lia. exact (CK.hvB_gh_w _ _ _ _ j z Hj). }
    ck_reg E (8%bv : reg) H8.
    ck_leaf Hag E'.
    assert (FRM : TK.samem (fun a => ~ (o <= a < o + 24)) M M') by (apply (TK.frame_samem _ _ _ _ _ _ _ HLF); intros a Ha Hk; cbn [CC.cp_F]; tk_outside).
    pose proof (CC.lf_grows _ _ _ _ _ _ _ HLF) as MG.
    ck_leaf_k k Hnth; [|ck_leaf_end k Hnth].
    assert (R1 : getr R' 1%bv = Z_to_bv 64 rav) by (tk_reg HLF (1%bv : reg); exact (GH 0%nat _ eq_refl)).
    apply (CK.ret_leaf fx' R' _ M' model K rav ret_gs Hh Hl R1 Hra).
    apply (Kret fx' R' M' Hfp'); [tk_lin HLF (2%bv : reg) | tk_reg HLF (8%bv : reg); exact (GH 1%nat _ eq_refl) | tk_reg HLF (9%bv : reg); exact (GH 2%nat _ eq_refl)
      | ck_keeps HLF Hag64 KOG | | | | exact FRM | exact MG].
    * replace o with (o + 0) by lia. ck_cell64 HLF (EVar 40) 0 (ELit 0). reflexivity.
    * ck_cell64 HLF (EVar 40) 8 (ELit 0). reflexivity.
    * ck_cell64 HLF (EVar 40) 16 (ELit 0). reflexivity.
Qed.

Lemma s_g_reobj : forall (fx : FPState) R M model K sp1 rav s0v s1v o,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp1 - 48) -> CK.spok sp1 -> L5.ra_ok rav -> getr R 8%bv = Z_to_bv 64 o ->
  0 <= s0v < 2 ^ 64 -> 0 <= s1v < 2 ^ 64 -> L5.u64_at RSEGS M (sp1 - 8) rav -> L5.u64_at RSEGS M (sp1 - 16) s0v -> L5.u64_at RSEGS M (sp1 - 24) s1v ->
  2 ^ 40 <= o <= 2 ^ 47 - 24 -> (o + 24 <= sp1 - 48 \/ sp1 <= o) -> L5.defined M o 24 ->
  (forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 sp1 -> getr R' 8%bv = Z_to_bv 64 s0v -> getr R' 9%bv = Z_to_bv 64 s1v ->
      TK.keepsR KOG R R' -> L5.u64_at RSEGS M' o 0 -> L5.u64_at RSEGS M' (o + 8) 0 -> L5.u64_at RSEGS M' (o + 16) 0 ->
      TK.samem (fun a => ~ (o <= a < o + 24)) M M' -> mem_grows M M' -> srealizes RSEGS SCFG (@PML.cfg fx' R' rav M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R GST.R_CONV M model) K.
Proof.
  intros fx R M model K sp1 rav s0v s1v o Hh Hl Hfp H2 [Hsp Hal] Hra H8 Hs0 Hs1 F1 F2 F3 Ho D1 DO Kret.
  change GST.R_CONV with (CC.cp_pc Geobj.cp1).
  assert (Hrav : 0 <= rav < 2 ^ 64) by (destruct Hra; lia).
  set (gl := [rav; s0v; s1v]).
  ck_open FPM Geobj.cp1 (Geobj.plans 1%nat _ eq_refl) (-48) gl (fun _ : nat => @nil byte) (@nil (nat * Z)) sp1 R M fx model K Hh Hl Hfp H2 ck_no_pins.
  - ck_reg E (8%bv : reg) H8. ck_gh E 0%nat rav. ck_gh E 1%nat s0v. ck_gh E 2%nat s1v.
    unfold know_ok, Geobj.cp1. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + ck_kw64 (sp1 - 8) rav F1. + ck_kw64 (sp1 - 16) s0v F2. + ck_kw64 (sp1 - 24) s1v F3. + e_range. + e_unk. + e_wr. + e_disj.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    assert (GH : forall j z, nth_error gl j = Some z -> ev E' (64 + j) = Z_to_bv 64 z).
    { intros j z Hj. pose proof (nth_gl gl j z Hj) as Hj8. change (length gl) with 3%nat in Hj8. change (CC.cp_nx Geobj.cp1) with 67%nat in Hag.
      rewrite <- (proj1 Hag (64 + j)%nat) by lia. exact (CK.hvB_gh_w _ _ _ _ j z Hj). }
    ck_reg E (8%bv : reg) H8.
    ck_leaf Hag E'.
    assert (FRM : TK.samem (fun a => ~ (o <= a < o + 24)) M M') by (apply (TK.frame_samem _ _ _ _ _ _ _ HLF); intros a Ha Hk; cbn [CC.cp_F]; tk_outside).
    pose proof (CC.lf_grows _ _ _ _ _ _ _ HLF) as MG.
    ck_leaf_k k Hnth; [|ck_leaf_end k Hnth].
    assert (R1 : getr R' 1%bv = Z_to_bv 64 rav) by (tk_reg HLF (1%bv : reg); exact (GH 0%nat _ eq_refl)).
    apply (CK.ret_leaf fx' R' _ M' model K rav ret_gs Hh Hl R1 Hra).
    apply (Kret fx' R' M' Hfp'); [tk_lin HLF (2%bv : reg) | tk_reg HLF (8%bv : reg); exact (GH 1%nat _ eq_refl) | tk_reg HLF (9%bv : reg); exact (GH 2%nat _ eq_refl)
      | ck_keeps HLF Hag64 KOG | | | | exact FRM | exact MG].
    * replace o with (o + 0) by lia. ck_cell64 HLF (EVar 40) 0 (ELit 0). reflexivity.
    * ck_cell64 HLF (EVar 40) 8 (ELit 0). reflexivity.
    * ck_cell64 HLF (EVar 40) 16 (ELit 0). reflexivity.
Qed.

Lemma s_g_rbarr : forall (fx : FPState) R M model K sp1 rav s0v s1v o,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp1 - 48) -> CK.spok sp1 -> L5.ra_ok rav -> getr R 8%bv = Z_to_bv 64 o ->
  0 <= s0v < 2 ^ 64 -> 0 <= s1v < 2 ^ 64 -> L5.u64_at RSEGS M (sp1 - 8) rav -> L5.u64_at RSEGS M (sp1 - 16) s0v -> L5.u64_at RSEGS M (sp1 - 24) s1v ->
  2 ^ 40 <= o <= 2 ^ 47 - 24 -> (o + 24 <= sp1 - 48 \/ sp1 <= o) -> L5.defined M o 24 ->
  (forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 sp1 -> getr R' 8%bv = Z_to_bv 64 s0v -> getr R' 9%bv = Z_to_bv 64 s1v ->
      TK.keepsR KOG R R' -> L5.u64_at RSEGS M' o 0 -> L5.u64_at RSEGS M' (o + 8) 0 -> L5.u64_at RSEGS M' (o + 16) 0 ->
      TK.samem (fun a => ~ (o <= a < o + 24)) M M' -> mem_grows M M' -> srealizes RSEGS SCFG (@PML.cfg fx' R' rav M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R GST.R_CONV M model) K.
Proof.
  intros fx R M model K sp1 rav s0v s1v o Hh Hl Hfp H2 [Hsp Hal] Hra H8 Hs0 Hs1 F1 F2 F3 Ho D1 DO Kret.
  change GST.R_CONV with (CC.cp_pc Gbarr.cp1).
  assert (Hrav : 0 <= rav < 2 ^ 64) by (destruct Hra; lia).
  set (gl := [rav; s0v; s1v]).
  ck_open FPM Gbarr.cp1 (Gbarr.plans 1%nat _ eq_refl) (-48) gl (fun _ : nat => @nil byte) (@nil (nat * Z)) sp1 R M fx model K Hh Hl Hfp H2 ck_no_pins.
  - ck_reg E (8%bv : reg) H8. ck_gh E 0%nat rav. ck_gh E 1%nat s0v. ck_gh E 2%nat s1v.
    unfold know_ok, Gbarr.cp1. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + ck_kw64 (sp1 - 8) rav F1. + ck_kw64 (sp1 - 16) s0v F2. + ck_kw64 (sp1 - 24) s1v F3. + e_range. + e_unk. + e_wr. + e_disj.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    assert (GH : forall j z, nth_error gl j = Some z -> ev E' (64 + j) = Z_to_bv 64 z).
    { intros j z Hj. pose proof (nth_gl gl j z Hj) as Hj8. change (length gl) with 3%nat in Hj8. change (CC.cp_nx Gbarr.cp1) with 67%nat in Hag.
      rewrite <- (proj1 Hag (64 + j)%nat) by lia. exact (CK.hvB_gh_w _ _ _ _ j z Hj). }
    ck_reg E (8%bv : reg) H8.
    ck_leaf Hag E'.
    assert (FRM : TK.samem (fun a => ~ (o <= a < o + 24)) M M') by (apply (TK.frame_samem _ _ _ _ _ _ _ HLF); intros a Ha Hk; cbn [CC.cp_F]; tk_outside).
    pose proof (CC.lf_grows _ _ _ _ _ _ _ HLF) as MG.
    ck_leaf_k k Hnth; [|ck_leaf_end k Hnth].
    assert (R1 : getr R' 1%bv = Z_to_bv 64 rav) by (tk_reg HLF (1%bv : reg); exact (GH 0%nat _ eq_refl)).
    apply (CK.ret_leaf fx' R' _ M' model K rav ret_gs Hh Hl R1 Hra).
    apply (Kret fx' R' M' Hfp'); [tk_lin HLF (2%bv : reg) | tk_reg HLF (8%bv : reg); exact (GH 1%nat _ eq_refl) | tk_reg HLF (9%bv : reg); exact (GH 2%nat _ eq_refl)
      | ck_keeps HLF Hag64 KOG | | | | exact FRM | exact MG].
    * replace o with (o + 0) by lia. ck_cell64 HLF (EVar 40) 0 (ELit 0). reflexivity.
    * ck_cell64 HLF (EVar 40) 8 (ELit 0). reflexivity.
    * ck_cell64 HLF (EVar 40) 16 (ELit 0). reflexivity.
Qed.

Lemma s_g_rearr : forall (fx : FPState) R M model K sp1 rav s0v s1v o,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp1 - 48) -> CK.spok sp1 -> L5.ra_ok rav -> getr R 8%bv = Z_to_bv 64 o ->
  0 <= s0v < 2 ^ 64 -> 0 <= s1v < 2 ^ 64 -> L5.u64_at RSEGS M (sp1 - 8) rav -> L5.u64_at RSEGS M (sp1 - 16) s0v -> L5.u64_at RSEGS M (sp1 - 24) s1v ->
  2 ^ 40 <= o <= 2 ^ 47 - 24 -> (o + 24 <= sp1 - 48 \/ sp1 <= o) -> L5.defined M o 24 ->
  (forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 sp1 -> getr R' 8%bv = Z_to_bv 64 s0v -> getr R' 9%bv = Z_to_bv 64 s1v ->
      TK.keepsR KOG R R' -> L5.u64_at RSEGS M' o 0 -> L5.u64_at RSEGS M' (o + 8) 0 -> L5.u64_at RSEGS M' (o + 16) 0 ->
      TK.samem (fun a => ~ (o <= a < o + 24)) M M' -> mem_grows M M' -> srealizes RSEGS SCFG (@PML.cfg fx' R' rav M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R GST.R_CONV M model) K.
Proof.
  intros fx R M model K sp1 rav s0v s1v o Hh Hl Hfp H2 [Hsp Hal] Hra H8 Hs0 Hs1 F1 F2 F3 Ho D1 DO Kret.
  change GST.R_CONV with (CC.cp_pc Gearr.cp1).
  assert (Hrav : 0 <= rav < 2 ^ 64) by (destruct Hra; lia).
  set (gl := [rav; s0v; s1v]).
  ck_open FPM Gearr.cp1 (Gearr.plans 1%nat _ eq_refl) (-48) gl (fun _ : nat => @nil byte) (@nil (nat * Z)) sp1 R M fx model K Hh Hl Hfp H2 ck_no_pins.
  - ck_reg E (8%bv : reg) H8. ck_gh E 0%nat rav. ck_gh E 1%nat s0v. ck_gh E 2%nat s1v.
    unfold know_ok, Gearr.cp1. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + ck_kw64 (sp1 - 8) rav F1. + ck_kw64 (sp1 - 16) s0v F2. + ck_kw64 (sp1 - 24) s1v F3. + e_range. + e_unk. + e_wr. + e_disj.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    assert (GH : forall j z, nth_error gl j = Some z -> ev E' (64 + j) = Z_to_bv 64 z).
    { intros j z Hj. pose proof (nth_gl gl j z Hj) as Hj8. change (length gl) with 3%nat in Hj8. change (CC.cp_nx Gearr.cp1) with 67%nat in Hag.
      rewrite <- (proj1 Hag (64 + j)%nat) by lia. exact (CK.hvB_gh_w _ _ _ _ j z Hj). }
    ck_reg E (8%bv : reg) H8.
    ck_leaf Hag E'.
    assert (FRM : TK.samem (fun a => ~ (o <= a < o + 24)) M M') by (apply (TK.frame_samem _ _ _ _ _ _ _ HLF); intros a Ha Hk; cbn [CC.cp_F]; tk_outside).
    pose proof (CC.lf_grows _ _ _ _ _ _ _ HLF) as MG.
    ck_leaf_k k Hnth; [|ck_leaf_end k Hnth].
    assert (R1 : getr R' 1%bv = Z_to_bv 64 rav) by (tk_reg HLF (1%bv : reg); exact (GH 0%nat _ eq_refl)).
    apply (CK.ret_leaf fx' R' _ M' model K rav ret_gs Hh Hl R1 Hra).
    apply (Kret fx' R' M' Hfp'); [tk_lin HLF (2%bv : reg) | tk_reg HLF (8%bv : reg); exact (GH 1%nat _ eq_refl) | tk_reg HLF (9%bv : reg); exact (GH 2%nat _ eq_refl)
      | ck_keeps HLF Hag64 KOG | | | | exact FRM | exact MG].
    * replace o with (o + 0) by lia. ck_cell64 HLF (EVar 40) 0 (ELit 0). reflexivity.
    * ck_cell64 HLF (EVar 40) 8 (ELit 0). reflexivity.
    * ck_cell64 HLF (EVar 40) 16 (ELit 0). reflexivity.
Qed.

Lemma s_g_wdcall : forall (fx : FPState) R M model K sp1 o,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp1 - 48) -> CK.spok sp1 -> getr R 8%bv = Z_to_bv 64 o -> 0 <= o < 2 ^ 64 ->
  (forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 48) -> getr R' 1%bv = Z_to_bv 64 GST.R_WD -> getr R' 10%bv = Z_to_bv 64 (sp1 - 40) ->
      getr R' 11%bv = Z_to_bv 64 o -> TK.keepsR CK.CSR R R' -> TK.samem (fun _ => True) M M' -> mem_grows M M' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' PMFC.PC_WRITE_DOUBLE M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R GST.WD_CALL M model) K.
Proof.
  intros fx R M model K sp1 o Hh Hl Hfp H2 [Hsp Hal] H8 Ho Kc.
  change GST.WD_CALL with (CC.cp_pc Gdbl.cp1).
  ck_open FPM Gdbl.cp1 (Gdbl.plans 1%nat _ eq_refl) (-48) (@nil Z) (fun _ : nat => @nil byte) (@nil (nat * Z)) sp1 R M fx model K Hh Hl Hfp H2 ck_no_pins.
  - unfold know_ok, Gdbl.cp1. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    ck_reg E (8%bv : reg) H8.
    ck_leaf Hag E'.
    assert (FRM : TK.samem (fun _ => True) M M') by (apply (TK.frame_samem _ _ _ _ _ _ _ HLF); intros a Ha _; cbn [CC.cp_F]; tk_outside).
    pose proof (CC.lf_grows _ _ _ _ _ _ _ HLF) as MG.
    ck_leaf_k k Hnth; [|ck_leaf_end k Hnth].
    apply (Kc fx' R' M' Hfp'); [tk_lin HLF (2%bv : reg) | unfold GST.R_WD; tk_lin HLF (1%bv : reg) | tk_lin HLF (10%bv : reg) | tk_lin HLF (11%bv : reg) | ck_keeps HLF Hag64 CK.CSR
      | exact FRM | exact MG].
Qed.

End S.
End GSS.
