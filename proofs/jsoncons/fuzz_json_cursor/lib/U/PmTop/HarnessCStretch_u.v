(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10PlanKit_u PmLibDefs_u PmLibSpecs_u PmLayout_u PmCurSpecs_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutCert Require Import Pm10CutKit_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutL5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop Require Import TopKit_u TopKit2_u TopSpecs_u ReadKit_u ChunkKit_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutGen Require Cut_hnc_csrc_u Cut_hnb_s2l_csrc_u Cut_hnb_s2s_csrc_u Cut_hnb_sbl_csrc_u Cut_hnb_sbs_csrc_u Cut_hnb_sl_csrc_u Cut_hnb_ss_csrc_u Cut_hnb_g11_csrc_u.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module HCT.
Definition R_STRINIT : Z := 0x39710.   Definition R_ISS : Z := 0x39720.      Definition R_SYSCAT : Z := 0x39728.   Definition R_CCTOR : Z := 0x3973c.
Definition R_GET : Z := 0x39788.       Definition R_RN : Z := 0x397a0.       Definition R_OPDEL_S2 : Z := 0x397bc. Definition R_PDTOR : Z := 0x397e8.
Definition R_SDTOR : Z := 0x397f0.     Definition R_OPDEL_SB : Z := 0x39840. Definition R_LOCDTOR : Z := 0x39858. Definition R_ISTRDTOR : Z := 0x39864.
Definition R_IOSBDTOR : Z := 0x3986c.  Definition R_OPDEL_S : Z := 0x39888.  Definition BR_S2 : Z := 0x397a8.     Definition BR_SB : Z := 0x3982c.
Definition BR_S : Z := 0x39874.        Definition RET : Z := 0x398a0.
Definition VT_ISS0 : Z := 792064.      Definition VT_SBUF0 : Z := 791824.    Definition VT_IOS0 : Z := 792104.     Definition VTT_ISS : Z := 792120.
Definition VT_SBUF1 : Z := 791696.
End HCT.

Module HCS.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).
Module G := Cut_hnc_csrc_u.
Module Gs2l := Cut_hnb_s2l_csrc_u.   Module Gs2s := Cut_hnb_s2s_csrc_u.   Module Gsbl := Cut_hnb_sbl_csrc_u.   Module Gsbs := Cut_hnb_sbs_csrc_u.
Module Gsl := Cut_hnb_sl_csrc_u.     Module Gss := Cut_hnb_ss_csrc_u.     Module Gg11 := Cut_hnb_g11_csrc_u.
Lemma ret_h : CL.is_ret_at RSEGS HCT.RET. Proof. CL.solve_is_ret. Qed.
Lemma nth_gl : forall (gl : list Z) j z, nth_error gl j = Some z -> (j < length gl)%nat.
Proof. intros gl j z H. apply nth_error_Some. rewrite H. discriminate. Qed.

Definition KOH : list nat := [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.

Definition KEX (sp1 : Z) (a : Z) : Prop := ~ (sp1 - 1008 <= a < sp1 - 1000) /\ ~ (sp1 - 360 <= a < sp1 - 352).
Lemma and1_lit : forall x, 0 <= x < 2 ^ 64 -> alu64 ALU_AND (Z_to_bv 64 x) (Z_to_bv 64 1) = Z_to_bv 64 (Z.land x 1).
Proof. intros x Hx. apply RK.w_of_u. apply TK.and1_val. apply u64_of_Z. exact Hx. Qed.
Lemma bit_of_byte : forall w, 0 <= w < 2 ^ 64 -> alu64 ALU_AND (ext_val false 0 1 (Z_to_bv 64 w)) (Z_to_bv 64 1) = Z_to_bv 64 (Z.land (w mod 256) 1).
Proof. intros w Hw. rewrite (RK.ext_u8_mod w Hw). apply and1_lit. pose proof (Z.mod_pos_bound w 256 ltac:(lia)). lia. Qed.

Section S.
Context {SCFG_P : ScfgP}.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.

Lemma s_h_entry : forall (fx : FPState) R M model K sp1 rav,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx ->
  getr R 2%bv = Z_to_bv 64 sp1 -> getr R 1%bv = Z_to_bv 64 rav -> 0 <= rav < 2 ^ 64 -> CK.spok sp1 -> L5.defined M (sp1 - 1040) 1040 ->
  (forall (fx' : FPState) R' M', PML.fp_ok fx' ->
      getr R' 2%bv = Z_to_bv 64 (sp1 - 1040) -> getr R' 1%bv = Z_to_bv 64 HCT.R_STRINIT -> getr R' 10%bv = Z_to_bv 64 (sp1 - 56) ->
      getr R' 11%bv = getr R 10%bv -> getr R' 12%bv = getr R 11%bv -> TK.keepsR CK.CSR R R' ->
      L5.u64_at RSEGS M' (sp1 - 8) rav -> L5.u64_at RSEGS M' (sp1 - 16) (bv_unsigned (getr R 8%bv)) -> L5.u64_at RSEGS M' (sp1 - 24) (bv_unsigned (getr R 9%bv)) ->
      L5.u64_at RSEGS M' (sp1 - 32) (bv_unsigned (getr R 18%bv)) ->
      TK.samem (fun a => ~ (sp1 - 1040 <= a < sp1)) M M' -> mem_grows M M' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' PML.PC_STRINIT M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R PML.PC_LIB M model) K.
Proof.
  intros fx R M model K sp1 rav Hh Hl Hfp H2 H1 Hra [Hsp Hal] Hdef Hcont.
  set (E := Env (reg_ev R (fun _ => Z_to_bv 64 0)) (fun _ => [])).
  assert (U2 : bv_unsigned (ev E 2) = sp1) by (unfold E; rewrite (CL5.ev_reg R _ _ 2%bv), H2; apply u64_of_Z; lia).
  change PML.PC_LIB with (CC.cp_pc G.cp0).
  apply (TK.stretch_cps FPM G.cp0 fx E R M model K (G.plans 0%nat _ eq_refl) Hh Hl Hfp).
  - exact (regs_ok_id R _ _).
  - unfold know_ok, G.cp0. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + e_unk. + e_wr.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    destruct k as [|k]; [|destruct k; discriminate Hnth]. injection Hnth as <-.
    assert (Hag32 : env_agree 32 E E') by exact Hag.
    assert (U2' : bv_unsigned (ev E' 2) = sp1) by (rewrite <- (proj1 Hag32 2%nat) by lia; exact U2).
    apply (Hcont fx' R' M' Hfp').
    + tk_lin HLF (2%bv : reg).
    + unfold HCT.R_STRINIT. tk_lin HLF (1%bv : reg).
    + tk_lin HLF (10%bv : reg).
    + tk_reg HLF (11%bv : reg). rewrite <- (proj1 Hag32 10%nat) by lia. exact (CL5.ev_reg R _ _ 10%bv).
    + tk_reg HLF (12%bv : reg). rewrite <- (proj1 Hag32 11%nat) by lia. exact (CL5.ev_reg R _ _ 11%bv).
    + intros r Hr. exact (TK.keeps_id_sound _ _ R _ _ E' R' M M' CK.CSR r HLF eq_refl Hag32 Hr).
    + eapply (CL5.kword64_elim RSEGS E' M'); [apply (CC.lf_cells _ _ _ _ _ _ _ HLF (KWord (SA (EVar 2) (-8)) 8 (EVar 1))); cbn; tauto | ev_start |].
      cbn [edenot]. rewrite <- (proj1 Hag32 1%nat) by lia. unfold E. rewrite (CL5.ev_reg R _ _ 1%bv), H1. apply u64_of_Z. exact Hra.
    + eapply (CL5.kword64_elim RSEGS E' M'); [apply (CC.lf_cells _ _ _ _ _ _ _ HLF (KWord (SA (EVar 2) (-16)) 8 (EVar 8))); cbn; tauto | ev_start |].
      cbn [edenot]. rewrite <- (proj1 Hag32 8%nat) by lia. unfold E. rewrite (CL5.ev_reg R _ _ 8%bv). reflexivity.
    + eapply (CL5.kword64_elim RSEGS E' M'); [apply (CC.lf_cells _ _ _ _ _ _ _ HLF (KWord (SA (EVar 2) (-24)) 8 (EVar 9))); cbn; tauto | ev_start |].
      cbn [edenot]. rewrite <- (proj1 Hag32 9%nat) by lia. unfold E. rewrite (CL5.ev_reg R _ _ 9%bv). reflexivity.
    + eapply (CL5.kword64_elim RSEGS E' M'); [apply (CC.lf_cells _ _ _ _ _ _ _ HLF (KWord (SA (EVar 2) (-32)) 8 (EVar 18))); cbn; tauto | ev_start |].
      cbn [edenot]. rewrite <- (proj1 Hag32 18%nat) by lia. unfold E. rewrite (CL5.ev_reg R _ _ 18%bv). reflexivity.
    + apply (TK.frame_samem _ _ _ _ _ _ _ HLF). intros a Ha Hk. cbn [CC.cp_F G.cp0]. tk_outside.
    + exact (CC.lf_grows _ _ _ _ _ _ _ HLF).
Qed.

Ltac h_simple cp plans sp1 R M fx model K Hh Hl Hfp H2 :=
  ck_open FPM cp plans (-1040) (@nil Z) (fun _ : nat => @nil byte) (@nil (nat * Z)) sp1 R M fx model K Hh Hl Hfp H2 ck_no_pins.

Lemma s_h_rstrinit : forall (fx : FPState) R M model K sp1,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp1 - 1040) -> CK.spok sp1 ->
  (forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 1040) -> getr R' 1%bv = Z_to_bv 64 HCT.R_ISS -> getr R' 10%bv = Z_to_bv 64 (sp1 - 328) ->
      getr R' 11%bv = Z_to_bv 64 (sp1 - 56) -> getr R' 12%bv = Z_to_bv 64 8 -> TK.keepsR CK.CSR R R' -> TK.samem (fun _ => True) M M' -> mem_grows M M' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' PML.PC_ISS_CTOR M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R HCT.R_STRINIT M model) K.
Proof.
  intros fx R M model K sp1 Hh Hl Hfp H2 [Hsp Hal] Hcont. change HCT.R_STRINIT with (CC.cp_pc G.cp1).
  h_simple G.cp1 (G.plans 1%nat _ eq_refl) sp1 R M fx model K Hh Hl Hfp H2.
  - unfold know_ok, G.cp1. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil]. + e_range. + e_align Hal.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'. ck_leaf Hag E'.
    assert (FRM : TK.samem (fun _ => True) M M') by (apply (TK.frame_samem _ _ _ _ _ _ _ HLF); intros a Ha _; cbn [CC.cp_F]; tk_outside).
    ck_leaf_k k Hnth; [|ck_leaf_end k Hnth].
    apply (Hcont fx' R' M' Hfp'); [tk_lin HLF (2%bv : reg) | unfold HCT.R_ISS; tk_lin HLF (1%bv : reg) | tk_lin HLF (10%bv : reg) | tk_lin HLF (11%bv : reg) | tk_lin HLF (12%bv : reg)
      | ck_keeps HLF Hag64 CK.CSR | exact FRM | exact (CC.lf_grows _ _ _ _ _ _ _ HLF)].
Qed.

Lemma s_h_riss : forall (fx : FPState) R M model K sp1,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp1 - 1040) -> CK.spok sp1 -> L5.defined M (sp1 - 344) 4 ->
  (forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 1040) -> getr R' 1%bv = Z_to_bv 64 HCT.R_SYSCAT -> TK.keepsR CK.CSR R R' ->
      L5.u32_at RSEGS M' (sp1 - 344) 0 -> TK.samem (fun a => ~ (sp1 - 344 <= a < sp1 - 340)) M M' -> mem_grows M M' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' PML.PC_SYSTEM_CATEGORY M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R HCT.R_ISS M model) K.
Proof.
  intros fx R M model K sp1 Hh Hl Hfp H2 [Hsp Hal] D1 Hcont. change HCT.R_ISS with (CC.cp_pc G.cp2).
  h_simple G.cp2 (G.plans 2%nat _ eq_refl) sp1 R M fx model K Hh Hl Hfp H2.
  - unfold know_ok, G.cp2. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil]. + e_range. + e_align Hal. + e_unk. + e_wr.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'. ck_leaf Hag E'.
    assert (FRM : TK.samem (fun a => ~ (sp1 - 344 <= a < sp1 - 340)) M M') by (apply (TK.frame_samem _ _ _ _ _ _ _ HLF); intros a Ha Hk; cbn [CC.cp_F]; tk_outside).
    ck_leaf_k k Hnth; [|ck_leaf_end k Hnth].
    apply (Hcont fx' R' M' Hfp'); [tk_lin HLF (2%bv : reg) | unfold HCT.R_SYSCAT; tk_lin HLF (1%bv : reg) | ck_keeps HLF Hag64 CK.CSR | | exact FRM | exact (CC.lf_grows _ _ _ _ _ _ _ HLF)].
    ck_cell32 HLF (EVar 2) (-344) (ELit 0). reflexivity.
Qed.

Lemma s_h_rsyscat : forall (fx : FPState) R M model K sp1 cat,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp1 - 1040) -> CK.spok sp1 -> getr R 10%bv = Z_to_bv 64 cat -> 0 <= cat < 2 ^ 64 ->
  L5.defined M (sp1 - 336) 8 ->
  (forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 1040) -> getr R' 1%bv = Z_to_bv 64 HCT.R_CCTOR -> getr R' 10%bv = Z_to_bv 64 (sp1 - 1008) ->
      getr R' 11%bv = Z_to_bv 64 (sp1 - 328) -> getr R' 12%bv = Z_to_bv 64 (sp1 - 344) -> TK.keepsR CK.CSR R R' ->
      L5.u64_at RSEGS M' (sp1 - 336) cat -> TK.samem (fun a => ~ (sp1 - 336 <= a < sp1 - 328)) M M' -> mem_grows M M' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' PMCS.PC_CURSOR_CTOR M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R HCT.R_SYSCAT M model) K.
Proof.
  intros fx R M model K sp1 cat Hh Hl Hfp H2 [Hsp Hal] H10 Hcat D1 Hcont. change HCT.R_SYSCAT with (CC.cp_pc G.cp3).
  h_simple G.cp3 (G.plans 3%nat _ eq_refl) sp1 R M fx model K Hh Hl Hfp H2.
  - unfold know_ok, G.cp3. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil]. + e_range. + e_align Hal. + e_unk. + e_wr.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'. ck_reg E (10%bv : reg) H10. ck_leaf Hag E'.
    assert (FRM : TK.samem (fun a => ~ (sp1 - 336 <= a < sp1 - 328)) M M') by (apply (TK.frame_samem _ _ _ _ _ _ _ HLF); intros a Ha Hk; cbn [CC.cp_F]; tk_outside).
    ck_leaf_k k Hnth; [|ck_leaf_end k Hnth].
    apply (Hcont fx' R' M' Hfp'); [tk_lin HLF (2%bv : reg) | unfold HCT.R_CCTOR; tk_lin HLF (1%bv : reg) | tk_lin HLF (10%bv : reg) | tk_lin HLF (11%bv : reg) | tk_lin HLF (12%bv : reg)
      | ck_keeps HLF Hag64 CK.CSR | | exact FRM | exact (CC.lf_grows _ _ _ _ _ _ _ HLF)].
    ck_cell64 HLF (EVar 2) (-336) (EVar 42). ck_atom.
Qed.

Lemma s_h_rpdtor : forall (fx : FPState) R M model K sp1,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp1 - 1040) -> CK.spok sp1 ->
  (forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 1040) -> getr R' 1%bv = Z_to_bv 64 HCT.R_SDTOR -> getr R' 10%bv = Z_to_bv 64 (sp1 - 1000) ->
      TK.keepsR CK.CSR R R' -> TK.samem (fun _ => True) M M' -> mem_grows M M' -> srealizes RSEGS SCFG (@PML.cfg fx' R' PML.PC_SOURCE_DTOR M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R HCT.R_PDTOR M model) K.
Proof.
  intros fx R M model K sp1 Hh Hl Hfp H2 [Hsp Hal] Hcont. change HCT.R_PDTOR with (CC.cp_pc G.cp8).
  h_simple G.cp8 (G.plans 8%nat _ eq_refl) sp1 R M fx model K Hh Hl Hfp H2.
  - unfold know_ok, G.cp8. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil]. + e_range. + e_align Hal.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'. ck_leaf Hag E'.
    assert (FRM : TK.samem (fun _ => True) M M') by (apply (TK.frame_samem _ _ _ _ _ _ _ HLF); intros a Ha _; cbn [CC.cp_F]; tk_outside).
    ck_leaf_k k Hnth; [|ck_leaf_end k Hnth].
    apply (Hcont fx' R' M' Hfp'); [tk_lin HLF (2%bv : reg) | unfold HCT.R_SDTOR; tk_lin HLF (1%bv : reg) | tk_lin HLF (10%bv : reg) | ck_keeps HLF Hag64 CK.CSR | exact FRM
      | exact (CC.lf_grows _ _ _ _ _ _ _ HLF)].
Qed.

Lemma s_h_ropdel_sb : forall (fx : FPState) R M model K sp1,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp1 - 1040) -> CK.spok sp1 -> PML.img_ro M -> L5.defined M (sp1 - 312) 8 ->
  (forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 1040) -> getr R' 1%bv = Z_to_bv 64 HCT.R_LOCDTOR -> getr R' 10%bv = Z_to_bv 64 (sp1 - 304) ->
      TK.keepsR CK.CSR R R' -> L5.u64_at RSEGS M' (sp1 - 312) HCT.VT_SBUF1 -> TK.samem (fun a => ~ (sp1 - 312 <= a < sp1 - 304)) M M' -> mem_grows M M' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' PML.PC_LOCALE_DTOR M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R HCT.R_OPDEL_SB M model) K.
Proof.
  intros fx R M model K sp1 Hh Hl Hfp H2 [Hsp Hal] RO D1 Hcont. change HCT.R_OPDEL_SB with (CC.cp_pc G.cp10).
  h_simple G.cp10 (G.plans 10%nat _ eq_refl) sp1 R M fx model K Hh Hl Hfp H2.
  - unfold know_ok, G.cp10. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil]. + e_range. + e_align Hal. + tk_kimg RO. + e_unk. + e_wr.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'. ck_leaf Hag E'.
    assert (FRM : TK.samem (fun a => ~ (sp1 - 312 <= a < sp1 - 304)) M M') by (apply (TK.frame_samem _ _ _ _ _ _ _ HLF); intros a Ha Hk; cbn [CC.cp_F]; tk_outside).
    ck_leaf_k k Hnth; [|ck_leaf_end k Hnth].
    apply (Hcont fx' R' M' Hfp'); [tk_lin HLF (2%bv : reg) | unfold HCT.R_LOCDTOR; tk_lin HLF (1%bv : reg) | tk_lin HLF (10%bv : reg) | ck_keeps HLF Hag64 CK.CSR | | exact FRM
      | exact (CC.lf_grows _ _ _ _ _ _ _ HLF)].
    unfold HCT.VT_SBUF1. ck_cell64 HLF (EVar 2) (-312) (ELit 791696). reflexivity.
Qed.

Lemma s_h_rlocdtor : forall (fx : FPState) R M model K sp1,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp1 - 1040) -> CK.spok sp1 ->
  (forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 1040) -> getr R' 1%bv = Z_to_bv 64 HCT.R_ISTRDTOR -> getr R' 10%bv = Z_to_bv 64 (sp1 - 328) ->
      TK.keepsR CK.CSR R R' -> TK.samem (fun _ => True) M M' -> mem_grows M M' -> srealizes RSEGS SCFG (@PML.cfg fx' R' PML.PC_ISTREAM_DTOR M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R HCT.R_LOCDTOR M model) K.
Proof.
  intros fx R M model K sp1 Hh Hl Hfp H2 [Hsp Hal] Hcont. change HCT.R_LOCDTOR with (CC.cp_pc G.cp11).
  h_simple G.cp11 (G.plans 11%nat _ eq_refl) sp1 R M fx model K Hh Hl Hfp H2.
  - unfold know_ok, G.cp11. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil]. + e_range. + e_align Hal.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'. ck_leaf Hag E'.
    assert (FRM : TK.samem (fun _ => True) M M') by (apply (TK.frame_samem _ _ _ _ _ _ _ HLF); intros a Ha _; cbn [CC.cp_F]; tk_outside).
    ck_leaf_k k Hnth; [|ck_leaf_end k Hnth].
    apply (Hcont fx' R' M' Hfp'); [tk_lin HLF (2%bv : reg) | unfold HCT.R_ISTRDTOR; tk_lin HLF (1%bv : reg) | tk_lin HLF (10%bv : reg) | ck_keeps HLF Hag64 CK.CSR | exact FRM
      | exact (CC.lf_grows _ _ _ _ _ _ _ HLF)].
Qed.

Lemma s_h_ristrdtor : forall (fx : FPState) R M model K sp1,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp1 - 1040) -> CK.spok sp1 ->
  (forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 1040) -> getr R' 1%bv = Z_to_bv 64 HCT.R_IOSBDTOR -> getr R' 10%bv = Z_to_bv 64 (sp1 - 208) ->
      TK.keepsR CK.CSR R R' -> TK.samem (fun _ => True) M M' -> mem_grows M M' -> srealizes RSEGS SCFG (@PML.cfg fx' R' PML.PC_IOSB_DTOR M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R HCT.R_ISTRDTOR M model) K.
Proof.
  intros fx R M model K sp1 Hh Hl Hfp H2 [Hsp Hal] Hcont. change HCT.R_ISTRDTOR with (CC.cp_pc G.cp12).
  h_simple G.cp12 (G.plans 12%nat _ eq_refl) sp1 R M fx model K Hh Hl Hfp H2.
  - unfold know_ok, G.cp12. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil]. + e_range. + e_align Hal.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'. ck_leaf Hag E'.
    assert (FRM : TK.samem (fun _ => True) M M') by (apply (TK.frame_samem _ _ _ _ _ _ _ HLF); intros a Ha _; cbn [CC.cp_F]; tk_outside).
    ck_leaf_k k Hnth; [|ck_leaf_end k Hnth].
    apply (Hcont fx' R' M' Hfp'); [tk_lin HLF (2%bv : reg) | unfold HCT.R_IOSBDTOR; tk_lin HLF (1%bv : reg) | tk_lin HLF (10%bv : reg) | ck_keeps HLF Hag64 CK.CSR | exact FRM
      | exact (CC.lf_grows _ _ _ _ _ _ _ HLF)].
Qed.

Lemma pr_s32_eq : forall c, 0 <= c < 2 ^ 31 -> ext_val true 0 4 (Z_to_bv 64 c) = Z_to_bv 64 0 -> c = 0.
Proof. intros c Hc H. rewrite (RK.ext_s32 c Hc) in H. apply RK.w_inj in H; lia. Qed.
Lemma pr_s32_ne : forall c, 0 <= c < 2 ^ 31 -> ext_val true 0 4 (Z_to_bv 64 c) <> Z_to_bv 64 0 -> c <> 0.
Proof. intros c Hc H. rewrite (RK.ext_s32 c Hc) in H. exact (RK.w_neq _ _ H). Qed.
Lemma pr_u8_eq : forall c, 0 <= c <= 1 -> Z_to_bv 64 c = Z_to_bv 64 0 -> c = 0.
Proof. intros c Hc H. apply RK.w_inj in H; lia. Qed.
Lemma pr_u8_ne : forall c, 0 <= c <= 1 -> Z_to_bv 64 c <> Z_to_bv 64 0 -> c <> 0.
Proof. intros c Hc H. exact (RK.w_neq _ _ H). Qed.
Lemma pr_b1_eq : forall c, 0 <= c <= 1 -> Z_to_bv 64 c = Z_to_bv 64 0 -> Z.land c 1 = 0.
Proof. intros c Hc H. rewrite (pr_u8_eq c Hc H). reflexivity. Qed.
Lemma pr_b1_ne : forall c, 0 <= c <= 1 -> Z_to_bv 64 c <> Z_to_bv 64 0 -> Z.land c 1 <> 0.
Proof. intros c Hc H. assert (X : c = 1) by (pose proof (pr_u8_ne c Hc H); lia). rewrite X. discriminate. Qed.
Lemma keeps_csr : forall R R' : bvmap 5 word, TK.keepsR KOH R R' -> getr R' 8%bv = getr R 8%bv -> getr R' 9%bv = getr R 9%bv -> getr R' 18%bv = getr R 18%bv ->
  TK.keepsR CK.CSR R R'.
Proof.
  intros R R' HK H8 H9 H18 r Hr. unfold CK.CSR in Hr. cbn [In] in Hr.
  destruct (Nat.eq_dec (ridx r) 8) as [E|E]; [rewrite <- (ridx_inj 8%bv r ltac:(rewrite E; vm_compute; reflexivity)); exact H8|].
  destruct (Nat.eq_dec (ridx r) 9) as [E'|E']; [rewrite <- (ridx_inj 9%bv r ltac:(rewrite E'; vm_compute; reflexivity)); exact H9|].
  destruct (Nat.eq_dec (ridx r) 18) as [E''|E'']; [rewrite <- (ridx_inj 18%bv r ltac:(rewrite E''; vm_compute; reflexivity)); exact H18|].
  apply HK. unfold KOH. cbn [In]. lia.
Qed.

Ltac h_test_know Hal sp1 pd dn ec F460 F352 F336 :=
  unfold know_ok; cbn [CC.cp_know]; repeat (apply Forall_cons); [.. | apply Forall_nil];
  [ e_range | e_align Hal | ck_kw8 (sp1 - 476) pd F460 | ck_kw8 (sp1 - 368) dn F352 | ck_kw32 (sp1 - 344) ec F336 | e_unk | e_wr | e_unk | e_wr | e_range | e_range ].

Lemma s_h_test_cctor : forall (fx : FPState) R M model K sp1 pd dn ec,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp1 - 1040) -> CK.spok sp1 ->
  0 <= pd <= 1 -> 0 <= dn <= 1 -> 0 <= ec < 2 ^ 31 ->
  L5.u8_at RSEGS M (sp1 - 476) pd -> L5.u8_at RSEGS M (sp1 - 368) dn -> L5.u32_at RSEGS M (sp1 - 344) ec -> L5.defined M (sp1 - 1008) 8 -> L5.defined M (sp1 - 360) 8 ->
  (pd = 0 -> Z.land dn 1 = 0 -> ec = 0 -> forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 1040) -> getr R' 1%bv = Z_to_bv 64 HCT.R_GET ->
      getr R' 10%bv = Z_to_bv 64 (sp1 - 1032) -> getr R' 11%bv = Z_to_bv 64 (sp1 - 408) -> getr R' 12%bv = Z_to_bv 64 0 -> getr R' 13%bv = Z_to_bv 64 (sp1 - 344) ->
      getr R' 8%bv = Z_to_bv 64 (sp1 - 416) -> getr R' 9%bv = Z_to_bv 64 (sp1 - 408) -> getr R' 18%bv = Z_to_bv 64 2 -> TK.keepsR KOH R R' -> TK.samem (KEX sp1) M M' -> mem_grows M M' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' PMCS.PC_GET_STRING M' model) K) ->
  (pd <> 0 \/ Z.land dn 1 <> 0 \/ ec <> 0 -> forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 1040) -> getr R' 1%bv = Z_to_bv 64 HCT.R_PDTOR ->
      getr R' 10%bv = Z_to_bv 64 (sp1 - 688) -> TK.keepsR KOH R R' -> L5.u64_at RSEGS M' (sp1 - 1008) PMCS.VT_CURSOR -> L5.u64_at RSEGS M' (sp1 - 360) PMCS.VT_CURSOR_SER ->
      TK.samem (KEX sp1) M M' -> mem_grows M M' -> srealizes RSEGS SCFG (@PML.cfg fx' R' PML.PC_PARSER_DTOR M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R HCT.R_CCTOR M model) K.
Proof.
  intros fx R M model K sp1 pd dn ec Hh Hl Hfp H2 [Hsp Hal] Hpd Hdn Hec F460 F352 F336 D992 D344 Kget Kexit.
  change HCT.R_CCTOR with (CC.cp_pc G.cp4).
  set (gl := [0; 0; 0; pd; dn; ec]).
  ck_open FPM G.cp4 (G.plans 4%nat _ eq_refl) (-1040) gl (fun _ : nat => @nil byte) (@nil (nat * Z)) sp1 R M fx model K Hh Hl Hfp H2 ck_no_pins.
  - ck_gh E 3%nat pd. ck_gh E 4%nat dn. ck_gh E 5%nat ec. unfold G.cp4. h_test_know Hal sp1 pd dn ec F460 F352 F336.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    ck_gh E 3%nat pd. ck_gh E 4%nat dn. ck_gh E 5%nat ec. ck_leaf Hag E'.
    assert (FRM : TK.samem (KEX sp1) M M') by (apply (TK.frame_samem _ _ _ _ _ _ _ HLF); intros a Ha (Hk1 & Hk2); cbn [CC.cp_F]; tk_outside).
    pose proof (CC.lf_grows _ _ _ _ _ _ _ HLF) as MG.
    destruct k as [|k]; [injection Hnth as <- | destruct k as [|k]; [injection Hnth as <- | destruct k as [|k]; [injection Hnth as <- | destruct k as [|k]; [injection Hnth as <- | destruct k; discriminate Hnth]]]].
    + ck_probes HLF PF. destruct PF as (Pec & Pdn & Ppd & _). ck_w2z Pec. ck_w2z Pdn. ck_w2z Ppd.
      apply (Kget (pr_u8_eq pd Hpd Ppd) (pr_b1_eq dn Hdn Pdn) (pr_s32_eq ec Hec Pec) fx' R' M' Hfp');
        [tk_lin HLF (2%bv : reg) | unfold HCT.R_GET; tk_lin HLF (1%bv : reg) | tk_lin HLF (10%bv : reg) | tk_lin HLF (11%bv : reg) | tk_lin HLF (12%bv : reg) | tk_lin HLF (13%bv : reg)
        | tk_lin HLF (8%bv : reg) | tk_lin HLF (9%bv : reg) | tk_lin HLF (18%bv : reg) | ck_keeps HLF Hag64 KOH | exact FRM | exact MG].
    + ck_probes HLF PF. destruct PF as (P & _). ck_w2z P.
      apply (Kexit (or_intror (or_intror (pr_s32_ne ec Hec P))) fx' R' M' Hfp');
        [tk_lin HLF (2%bv : reg) | unfold HCT.R_PDTOR; tk_lin HLF (1%bv : reg) | tk_lin HLF (10%bv : reg) | ck_keeps HLF Hag64 KOH
        | unfold PMCS.VT_CURSOR; ck_cell64 HLF (EVar 2) (-1008) (ELit 776480); reflexivity | unfold PMCS.VT_CURSOR_SER; ck_cell64 HLF (EVar 2) (-360) (ELit 776696); reflexivity
        | exact FRM | exact MG].
    + ck_probes HLF PF. destruct PF as (P & _). ck_w2z P.
      apply (Kexit (or_intror (or_introl (pr_b1_ne dn Hdn P))) fx' R' M' Hfp');
        [tk_lin HLF (2%bv : reg) | unfold HCT.R_PDTOR; tk_lin HLF (1%bv : reg) | tk_lin HLF (10%bv : reg) | ck_keeps HLF Hag64 KOH
        | unfold PMCS.VT_CURSOR; ck_cell64 HLF (EVar 2) (-1008) (ELit 776480); reflexivity | unfold PMCS.VT_CURSOR_SER; ck_cell64 HLF (EVar 2) (-360) (ELit 776696); reflexivity
        | exact FRM | exact MG].
    + ck_probes HLF PF. destruct PF as (P & _). ck_w2z P.
      apply (Kexit (or_introl (pr_u8_ne pd Hpd P)) fx' R' M' Hfp');
        [tk_lin HLF (2%bv : reg) | unfold HCT.R_PDTOR; tk_lin HLF (1%bv : reg) | tk_lin HLF (10%bv : reg) | ck_keeps HLF Hag64 KOH
        | unfold PMCS.VT_CURSOR; ck_cell64 HLF (EVar 2) (-1008) (ELit 776480); reflexivity | unfold PMCS.VT_CURSOR_SER; ck_cell64 HLF (EVar 2) (-360) (ELit 776696); reflexivity
        | exact FRM | exact MG].
Qed.

Lemma s_h_test_opdel : forall (fx : FPState) R M model K sp1 pd dn ec,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp1 - 1040) -> CK.spok sp1 -> getr R 18%bv = Z_to_bv 64 2 ->
  0 <= pd <= 1 -> 0 <= dn <= 1 -> 0 <= ec < 2 ^ 31 ->
  L5.u8_at RSEGS M (sp1 - 476) pd -> L5.u8_at RSEGS M (sp1 - 368) dn -> L5.u32_at RSEGS M (sp1 - 344) ec -> L5.defined M (sp1 - 1008) 8 -> L5.defined M (sp1 - 360) 8 ->
  (pd = 0 -> Z.land dn 1 = 0 -> ec = 0 -> forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 1040) -> getr R' 1%bv = Z_to_bv 64 HCT.R_GET ->
      getr R' 10%bv = Z_to_bv 64 (sp1 - 1032) -> getr R' 11%bv = getr R 9%bv -> getr R' 12%bv = Z_to_bv 64 0 -> getr R' 13%bv = Z_to_bv 64 (sp1 - 344) ->
      TK.keepsR CK.CSR R R' -> TK.samem (KEX sp1) M M' -> mem_grows M M' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' PMCS.PC_GET_STRING M' model) K) ->
  (pd <> 0 \/ Z.land dn 1 <> 0 \/ ec <> 0 -> forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 1040) -> getr R' 1%bv = Z_to_bv 64 HCT.R_PDTOR ->
      getr R' 10%bv = Z_to_bv 64 (sp1 - 688) -> TK.keepsR KOH R R' -> L5.u64_at RSEGS M' (sp1 - 1008) PMCS.VT_CURSOR -> L5.u64_at RSEGS M' (sp1 - 360) PMCS.VT_CURSOR_SER ->
      TK.samem (KEX sp1) M M' -> mem_grows M M' -> srealizes RSEGS SCFG (@PML.cfg fx' R' PML.PC_PARSER_DTOR M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R HCT.R_OPDEL_S2 M model) K.
Proof.
  intros fx R M model K sp1 pd dn ec Hh Hl Hfp H2 [Hsp Hal] H18 Hpd Hdn Hec F460 F352 F336 D992 D344 Kget Kexit.
  change HCT.R_OPDEL_S2 with (CC.cp_pc G.cp7).
  set (gl := [0; 0; 0; pd; dn; ec]).
  ck_open FPM G.cp7 (G.plans 7%nat _ eq_refl) (-1040) gl (fun _ : nat => @nil byte) [(18%nat, 2)] sp1 R M fx model K Hh Hl Hfp H2 ck_pins.
  - ck_gh E 3%nat pd. ck_gh E 4%nat dn. ck_gh E 5%nat ec. unfold G.cp7. h_test_know Hal sp1 pd dn ec F460 F352 F336.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    ck_gh E 3%nat pd. ck_gh E 4%nat dn. ck_gh E 5%nat ec. ck_leaf Hag E'.
    assert (FRM : TK.samem (KEX sp1) M M') by (apply (TK.frame_samem _ _ _ _ _ _ _ HLF); intros a Ha (Hk1 & Hk2); cbn [CC.cp_F]; tk_outside).
    pose proof (CC.lf_grows _ _ _ _ _ _ _ HLF) as MG.
    destruct k as [|k]; [injection Hnth as <- | destruct k as [|k]; [injection Hnth as <- | destruct k as [|k]; [injection Hnth as <- | destruct k as [|k]; [injection Hnth as <- | destruct k; discriminate Hnth]]]].
    + ck_probes HLF PF. destruct PF as (Pec & Pdn & Ppd & _). ck_w2z Pec. ck_w2z Pdn. ck_w2z Ppd.
      apply (Kget (pr_u8_eq pd Hpd Ppd) (pr_b1_eq dn Hdn Pdn) (pr_s32_eq ec Hec Pec) fx' R' M' Hfp');
        [tk_lin HLF (2%bv : reg) | unfold HCT.R_GET; tk_lin HLF (1%bv : reg) | tk_lin HLF (10%bv : reg) | ck_keep HLF Hag64 (11%bv : reg) (9%bv : reg) | tk_lin HLF (12%bv : reg)
        | tk_lin HLF (13%bv : reg) | apply keeps_csr; [ck_keeps HLF Hag64 KOH | ck_keep HLF Hag64 (8%bv : reg) (8%bv : reg) | ck_keep HLF Hag64 (9%bv : reg) (9%bv : reg)
          | rewrite H18; tk_lin HLF (18%bv : reg)] | exact FRM | exact MG].
    + ck_probes HLF PF. destruct PF as (P & _). ck_w2z P.
      apply (Kexit (or_intror (or_intror (pr_s32_ne ec Hec P))) fx' R' M' Hfp');
        [tk_lin HLF (2%bv : reg) | unfold HCT.R_PDTOR; tk_lin HLF (1%bv : reg) | tk_lin HLF (10%bv : reg) | ck_keeps HLF Hag64 KOH
        | unfold PMCS.VT_CURSOR; ck_cell64 HLF (EVar 2) (-1008) (ELit 776480); reflexivity | unfold PMCS.VT_CURSOR_SER; ck_cell64 HLF (EVar 2) (-360) (ELit 776696); reflexivity
        | exact FRM | exact MG].
    + ck_probes HLF PF. destruct PF as (P & _). ck_w2z P.
      apply (Kexit (or_intror (or_introl (pr_b1_ne dn Hdn P))) fx' R' M' Hfp');
        [tk_lin HLF (2%bv : reg) | unfold HCT.R_PDTOR; tk_lin HLF (1%bv : reg) | tk_lin HLF (10%bv : reg) | ck_keeps HLF Hag64 KOH
        | unfold PMCS.VT_CURSOR; ck_cell64 HLF (EVar 2) (-1008) (ELit 776480); reflexivity | unfold PMCS.VT_CURSOR_SER; ck_cell64 HLF (EVar 2) (-360) (ELit 776696); reflexivity
        | exact FRM | exact MG].
    + ck_probes HLF PF. destruct PF as (P & _). ck_w2z P.
      apply (Kexit (or_introl (pr_u8_ne pd Hpd P)) fx' R' M' Hfp');
        [tk_lin HLF (2%bv : reg) | unfold HCT.R_PDTOR; tk_lin HLF (1%bv : reg) | tk_lin HLF (10%bv : reg) | ck_keeps HLF Hag64 KOH
        | unfold PMCS.VT_CURSOR; ck_cell64 HLF (EVar 2) (-1008) (ELit 776480); reflexivity | unfold PMCS.VT_CURSOR_SER; ck_cell64 HLF (EVar 2) (-360) (ELit 776696); reflexivity
        | exact FRM | exact MG].
Qed.

Lemma s_h_s2s : forall (fx : FPState) R M model K sp1 pd dn ec,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp1 - 1040) -> CK.spok sp1 -> getr R 10%bv = Z_to_bv 64 0 -> getr R 18%bv = Z_to_bv 64 2 ->
  0 <= pd <= 1 -> 0 <= dn <= 1 -> 0 <= ec < 2 ^ 31 ->
  L5.u8_at RSEGS M (sp1 - 476) pd -> L5.u8_at RSEGS M (sp1 - 368) dn -> L5.u32_at RSEGS M (sp1 - 344) ec -> L5.defined M (sp1 - 1008) 8 -> L5.defined M (sp1 - 360) 8 ->
  (pd = 0 -> Z.land dn 1 = 0 -> ec = 0 -> forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 1040) -> getr R' 1%bv = Z_to_bv 64 HCT.R_GET ->
      getr R' 10%bv = Z_to_bv 64 (sp1 - 1032) -> getr R' 11%bv = getr R 9%bv -> getr R' 12%bv = Z_to_bv 64 0 -> getr R' 13%bv = Z_to_bv 64 (sp1 - 344) ->
      TK.keepsR CK.CSR R R' -> TK.samem (KEX sp1) M M' -> mem_grows M M' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' PMCS.PC_GET_STRING M' model) K) ->
  (pd <> 0 \/ Z.land dn 1 <> 0 \/ ec <> 0 -> forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 1040) -> getr R' 1%bv = Z_to_bv 64 HCT.R_PDTOR ->
      getr R' 10%bv = Z_to_bv 64 (sp1 - 688) -> TK.keepsR KOH R R' -> L5.u64_at RSEGS M' (sp1 - 1008) PMCS.VT_CURSOR -> L5.u64_at RSEGS M' (sp1 - 360) PMCS.VT_CURSOR_SER ->
      TK.samem (KEX sp1) M M' -> mem_grows M M' -> srealizes RSEGS SCFG (@PML.cfg fx' R' PML.PC_PARSER_DTOR M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R HCT.BR_S2 M model) K.
Proof.
  intros fx R M model K sp1 pd dn ec Hh Hl Hfp H2 [Hsp Hal] H10 H18 Hpd Hdn Hec F460 F352 F336 D992 D344 Kget Kexit.
  change HCT.BR_S2 with (CC.cp_pc Gs2s.cp0).
  set (gl := [0; 0; 0; pd; dn; ec]).
  ck_open FPM Gs2s.cp0 (Gs2s.plans 0%nat _ eq_refl) (-1040) gl (fun _ : nat => @nil byte) [(10%nat, 0); (18%nat, 2)] sp1 R M fx model K Hh Hl Hfp H2 ck_pins.
  - ck_gh E 3%nat pd. ck_gh E 4%nat dn. ck_gh E 5%nat ec. unfold Gs2s.cp0. h_test_know Hal sp1 pd dn ec F460 F352 F336.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    ck_gh E 3%nat pd. ck_gh E 4%nat dn. ck_gh E 5%nat ec. ck_leaf Hag E'.
    assert (FRM : TK.samem (KEX sp1) M M') by (apply (TK.frame_samem _ _ _ _ _ _ _ HLF); intros a Ha (Hk1 & Hk2); cbn [CC.cp_F]; tk_outside).
    pose proof (CC.lf_grows _ _ _ _ _ _ _ HLF) as MG.
    destruct k as [|k]; [injection Hnth as <- | destruct k as [|k]; [injection Hnth as <- | destruct k as [|k]; [injection Hnth as <- | destruct k as [|k]; [injection Hnth as <- | destruct k; discriminate Hnth]]]].
    + ck_probes HLF PF. destruct PF as (Pec & Pdn & Ppd & _). ck_w2z Pec. ck_w2z Pdn. ck_w2z Ppd.
      apply (Kget (pr_u8_eq pd Hpd Ppd) (pr_b1_eq dn Hdn Pdn) (pr_s32_eq ec Hec Pec) fx' R' M' Hfp');
        [tk_lin HLF (2%bv : reg) | unfold HCT.R_GET; tk_lin HLF (1%bv : reg) | tk_lin HLF (10%bv : reg) | ck_keep HLF Hag64 (11%bv : reg) (9%bv : reg) | tk_lin HLF (12%bv : reg)
        | tk_lin HLF (13%bv : reg) | apply keeps_csr; [ck_keeps HLF Hag64 KOH | ck_keep HLF Hag64 (8%bv : reg) (8%bv : reg) | ck_keep HLF Hag64 (9%bv : reg) (9%bv : reg)
          | rewrite H18; tk_lin HLF (18%bv : reg)] | exact FRM | exact MG].
    + ck_probes HLF PF. destruct PF as (P & _). ck_w2z P.
      apply (Kexit (or_intror (or_intror (pr_s32_ne ec Hec P))) fx' R' M' Hfp');
        [tk_lin HLF (2%bv : reg) | unfold HCT.R_PDTOR; tk_lin HLF (1%bv : reg) | tk_lin HLF (10%bv : reg) | ck_keeps HLF Hag64 KOH
        | unfold PMCS.VT_CURSOR; ck_cell64 HLF (EVar 2) (-1008) (ELit 776480); reflexivity | unfold PMCS.VT_CURSOR_SER; ck_cell64 HLF (EVar 2) (-360) (ELit 776696); reflexivity
        | exact FRM | exact MG].
    + ck_probes HLF PF. destruct PF as (P & _). ck_w2z P.
      apply (Kexit (or_intror (or_introl (pr_b1_ne dn Hdn P))) fx' R' M' Hfp');
        [tk_lin HLF (2%bv : reg) | unfold HCT.R_PDTOR; tk_lin HLF (1%bv : reg) | tk_lin HLF (10%bv : reg) | ck_keeps HLF Hag64 KOH
        | unfold PMCS.VT_CURSOR; ck_cell64 HLF (EVar 2) (-1008) (ELit 776480); reflexivity | unfold PMCS.VT_CURSOR_SER; ck_cell64 HLF (EVar 2) (-360) (ELit 776696); reflexivity
        | exact FRM | exact MG].
    + ck_probes HLF PF. destruct PF as (P & _). ck_w2z P.
      apply (Kexit (or_introl (pr_u8_ne pd Hpd P)) fx' R' M' Hfp');
        [tk_lin HLF (2%bv : reg) | unfold HCT.R_PDTOR; tk_lin HLF (1%bv : reg) | tk_lin HLF (10%bv : reg) | ck_keeps HLF Hag64 KOH
        | unfold PMCS.VT_CURSOR; ck_cell64 HLF (EVar 2) (-1008) (ELit 776480); reflexivity | unfold PMCS.VT_CURSOR_SER; ck_cell64 HLF (EVar 2) (-360) (ELit 776696); reflexivity
        | exact FRM | exact MG].
Qed.

Ltac h_gh gl Hag E' G cp :=
  let j := fresh "j" in let z := fresh "z" in let Hj := fresh "Hj" in let Hj8 := fresh "Hj8" in
  assert (GH : forall j z, nth_error gl j = Some z -> ev E' (64 + j) = Z_to_bv 64 z)
    by (intros j z Hj; pose proof (nth_gl gl j z Hj) as Hj8; rewrite <- (proj1 Hag (64 + j)%nat) by (vm_compute in Hag |- *; vm_compute in Hj8; lia); exact (CK.hvB_gh_w _ _ _ _ j z Hj)).

Lemma s_h_rget : forall (fx : FPState) R M model K sp1 w p,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp1 - 1040) -> CK.spok sp1 -> 0 <= w < 2 ^ 64 -> 0 <= p < 2 ^ 64 ->
  L5.u64_at RSEGS M (sp1 - 1032) w -> L5.u64_at RSEGS M (sp1 - 1016) p -> L5.u32_at RSEGS M (sp1 - 344) 0 ->
  (forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 1040) -> getr R' 1%bv = Z_to_bv 64 HCT.R_RN -> getr R' 10%bv = Z_to_bv 64 (sp1 - 1008) ->
      getr R' 11%bv = getr R 8%bv -> getr R' 12%bv = Z_to_bv 64 (sp1 - 344) -> TK.keepsR CK.CSR R R' -> TK.samem (fun _ => True) M M' -> mem_grows M M' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' PMCS.PC_READ_NEXT_C M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R HCT.R_GET M model) K.
Proof.
  intros fx R M model K sp1 w p Hh Hl Hfp H2 [Hsp Hal] Hw Hp F1 F2 F3 Hcont. change HCT.R_GET with (CC.cp_pc G.cp5).
  set (gl := [w; p]).
  ck_open FPM G.cp5 (G.plans 5%nat _ eq_refl) (-1040) gl (fun _ : nat => @nil byte) (@nil (nat * Z)) sp1 R M fx model K Hh Hl Hfp H2 ck_no_pins.
  - ck_gh E 0%nat w. ck_gh E 1%nat p. unfold know_ok, G.cp5. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + ck_kw64 (sp1 - 1032) w F1. + ck_kw64 (sp1 - 1016) p F2. + ck_kw32 (sp1 - 344) 0 F3.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'. ck_leaf Hag E'.
    assert (FRM : TK.samem (fun _ => True) M M') by (apply (TK.frame_samem _ _ _ _ _ _ _ HLF); intros a Ha _; cbn [CC.cp_F]; tk_outside).
    ck_leaf_k k Hnth; [|ck_leaf_end k Hnth].
    apply (Hcont fx' R' M' Hfp'); [tk_lin HLF (2%bv : reg) | unfold HCT.R_RN; tk_lin HLF (1%bv : reg) | tk_lin HLF (10%bv : reg) | ck_keep HLF Hag64 (11%bv : reg) (8%bv : reg)
      | tk_lin HLF (12%bv : reg) | ck_keeps HLF Hag64 CK.CSR | exact FRM | exact (CC.lf_grows _ _ _ _ _ _ _ HLF)].
Qed.

Lemma s_h_rrn : forall (fx : FPState) R M model K sp1 w p pd dn ec,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp1 - 1040) -> CK.spok sp1 -> 0 <= w < 2 ^ 64 -> 0 <= p < 2 ^ 64 ->
  0 <= pd < 256 -> 0 <= dn < 256 -> 0 <= ec < 2 ^ 32 ->
  L5.u64_at RSEGS M (sp1 - 1032) w -> L5.u64_at RSEGS M (sp1 - 1016) p -> L5.u8_at RSEGS M (sp1 - 476) pd -> L5.u8_at RSEGS M (sp1 - 368) dn -> L5.u32_at RSEGS M (sp1 - 344) ec ->
  L5.defined M (sp1 - 1008) 8 -> L5.defined M (sp1 - 360) 8 ->
  (forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 1040) -> getr R' 10%bv = Z_to_bv 64 (Z.land (w mod 256) 1) -> TK.keepsR CK.CSR R R' ->
      TK.samem (KEX sp1) M M' -> mem_grows M M' -> srealizes RSEGS SCFG (@PML.cfg fx' R' HCT.BR_S2 M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R HCT.R_RN M model) K.
Proof.
  intros fx R M model K sp1 w p pd dn ec Hh Hl Hfp H2 [Hsp Hal] Hw Hp Hpd Hdn Hec F1 F2 F460 F352 F336 D992 D344 Hcont. change HCT.R_RN with (CC.cp_pc G.cp6).
  set (gl := [w; p; 0; pd; dn; ec]).
  ck_open FPM G.cp6 (G.plans 6%nat _ eq_refl) (-1040) gl (fun _ : nat => @nil byte) (@nil (nat * Z)) sp1 R M fx model K Hh Hl Hfp H2 ck_no_pins.
  - ck_gh E 0%nat w. ck_gh E 1%nat p. ck_gh E 3%nat pd. ck_gh E 4%nat dn. ck_gh E 5%nat ec. unfold know_ok, G.cp6. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + ck_kw64 (sp1 - 1032) w F1. + ck_kw64 (sp1 - 1016) p F2. + ck_kw8 (sp1 - 476) pd F460. + ck_kw8 (sp1 - 368) dn F352. + ck_kw32 (sp1 - 344) ec F336.
    + e_unk. + e_wr. + e_unk. + e_wr.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'. ck_gh E 0%nat w. ck_leaf Hag E'.
    assert (FRM : TK.samem (KEX sp1) M M') by (apply (TK.frame_samem _ _ _ _ _ _ _ HLF); intros a Ha (Hk1 & Hk2); cbn [CC.cp_F]; tk_outside).
    ck_leaf_k k Hnth; [|ck_leaf_end k Hnth].
    apply (Hcont fx' R' M' Hfp'); [tk_lin HLF (2%bv : reg) | | ck_keeps HLF Hag64 CK.CSR | exact FRM | exact (CC.lf_grows _ _ _ _ _ _ _ HLF)].
    tk_reg HLF (10%bv : reg). match goal with U : bv_unsigned (ev E' 64) = w |- _ => rewrite (RK.w_of_u _ _ U) end. exact (bit_of_byte w Hw).
Qed.

Lemma s_h_g11 : forall (fx : FPState) R M model K sp1 w p,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp1 - 1040) -> CK.spok sp1 -> 0 <= w < 2 ^ 64 -> 0 <= p < 2 ^ 64 ->
  L5.u64_at RSEGS M (sp1 - 1032) w -> L5.u64_at RSEGS M (sp1 - 1016) p -> L5.u32_at RSEGS M (sp1 - 344) 11 ->
  (forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 1040) -> getr R' 10%bv = Z_to_bv 64 (Z.land (w mod 256) 1) -> TK.keepsR CK.CSR R R' ->
      TK.samem (fun _ => True) M M' -> mem_grows M M' -> srealizes RSEGS SCFG (@PML.cfg fx' R' HCT.BR_S2 M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R HCT.R_GET M model) K.
Proof.
  intros fx R M model K sp1 w p Hh Hl Hfp H2 [Hsp Hal] Hw Hp F1 F2 F3 Hcont. change HCT.R_GET with (CC.cp_pc Gg11.cp0).
  set (gl := [w; p]).
  ck_open FPM Gg11.cp0 (Gg11.plans 0%nat _ eq_refl) (-1040) gl (fun _ : nat => @nil byte) (@nil (nat * Z)) sp1 R M fx model K Hh Hl Hfp H2 ck_no_pins.
  - ck_gh E 0%nat w. ck_gh E 1%nat p. unfold know_ok, Gg11.cp0. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + ck_kw64 (sp1 - 1032) w F1. + ck_kw64 (sp1 - 1016) p F2. + ck_kw32 (sp1 - 344) 11 F3.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'. ck_gh E 0%nat w. ck_leaf Hag E'.
    assert (FRM : TK.samem (fun _ => True) M M') by (apply (TK.frame_samem _ _ _ _ _ _ _ HLF); intros a Ha _; cbn [CC.cp_F]; tk_outside).
    ck_leaf_k k Hnth; [|ck_leaf_end k Hnth].
    apply (Hcont fx' R' M' Hfp'); [tk_lin HLF (2%bv : reg) | | ck_keeps HLF Hag64 CK.CSR | exact FRM | exact (CC.lf_grows _ _ _ _ _ _ _ HLF)].
    tk_reg HLF (10%bv : reg). match goal with U : bv_unsigned (ev E' 64) = w |- _ => rewrite (RK.w_of_u _ _ U) end. exact (bit_of_byte w Hw).
Qed.

Lemma s_h_rsdtor : forall (fx : FPState) R M model K sp1 w p,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp1 - 1040) -> CK.spok sp1 -> 0 <= w < 2 ^ 64 -> 0 <= p < 2 ^ 64 ->
  PML.img_ro M -> L5.defined M (sp1 - 328) 8 -> L5.defined M (sp1 - 312) 8 -> L5.defined M (sp1 - 208) 8 -> L5.u64_at RSEGS M (sp1 - 248) w -> L5.u64_at RSEGS M (sp1 - 232) p ->
  (forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 1040) -> getr R' 11%bv = Z_to_bv 64 (Z.land (w mod 256) 1) ->
      getr R' 8%bv = Z_to_bv 64 HCT.VTT_ISS -> getr R' 9%bv = getr R 9%bv -> TK.keepsR KOH R R' ->
      L5.u64_at RSEGS M' (sp1 - 328) HCT.VT_ISS0 -> L5.u64_at RSEGS M' (sp1 - 312) HCT.VT_SBUF0 -> L5.u64_at RSEGS M' (sp1 - 208) HCT.VT_IOS0 ->
      TK.samem (fun a => ~ (sp1 - 328 <= a < sp1 - 320) /\ ~ (sp1 - 312 <= a < sp1 - 304) /\ ~ (sp1 - 208 <= a < sp1 - 200)) M M' -> mem_grows M M' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' HCT.BR_SB M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R HCT.R_SDTOR M model) K.
Proof.
  intros fx R M model K sp1 w p Hh Hl Hfp H2 [Hsp Hal] Hw Hp RO D1 D2 D3 F1 F2 Hcont. change HCT.R_SDTOR with (CC.cp_pc G.cp9).
  set (gl := [w; p]).
  ck_open FPM G.cp9 (G.plans 9%nat _ eq_refl) (-1040) gl (fun _ : nat => @nil byte) (@nil (nat * Z)) sp1 R M fx model K Hh Hl Hfp H2 ck_no_pins.
  - ck_gh E 0%nat w. ck_gh E 1%nat p. unfold know_ok, G.cp9. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + tk_kimg RO. + e_unk. + e_wr. + e_unk. + e_wr. + e_unk. + e_wr. + ck_kw64 (sp1 - 248) w F1. + ck_kw64 (sp1 - 232) p F2.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'. ck_gh E 0%nat w. ck_leaf Hag E'.
    assert (FRM : TK.samem (fun a => ~ (sp1 - 328 <= a < sp1 - 320) /\ ~ (sp1 - 312 <= a < sp1 - 304) /\ ~ (sp1 - 208 <= a < sp1 - 200)) M M')
      by (apply (TK.frame_samem _ _ _ _ _ _ _ HLF); intros a Ha (Hk1 & Hk2 & Hk3); cbn [CC.cp_F]; tk_outside).
    ck_leaf_k k Hnth; [|ck_leaf_end k Hnth].
    apply (Hcont fx' R' M' Hfp'); [tk_lin HLF (2%bv : reg) | | unfold HCT.VTT_ISS; tk_lin HLF (8%bv : reg) | ck_keep HLF Hag64 (9%bv : reg) (9%bv : reg) | ck_keeps HLF Hag64 KOH
      | unfold HCT.VT_ISS0; ck_cell64 HLF (EVar 2) (-328) (ELit 792064); reflexivity | unfold HCT.VT_SBUF0; ck_cell64 HLF (EVar 2) (-312) (ELit 791824); reflexivity
      | unfold HCT.VT_IOS0; ck_cell64 HLF (EVar 2) (-208) (ELit 792104); reflexivity | exact FRM | exact (CC.lf_grows _ _ _ _ _ _ _ HLF)].
    tk_reg HLF (11%bv : reg). match goal with U : bv_unsigned (ev E' 64) = w |- _ => rewrite (RK.w_of_u _ _ U) end. exact (bit_of_byte w Hw).
Qed.

Lemma s_h_riosbdtor : forall (fx : FPState) R M model K sp1 w p rav s0v s1v s2v,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp1 - 1040) -> CK.spok sp1 -> 0 <= w < 2 ^ 64 -> 0 <= p < 2 ^ 64 ->
  0 <= rav < 2 ^ 64 -> 0 <= s0v < 2 ^ 64 -> 0 <= s1v < 2 ^ 64 -> 0 <= s2v < 2 ^ 64 ->
  L5.u64_at RSEGS M (sp1 - 56) w -> L5.u64_at RSEGS M (sp1 - 40) p -> L5.u64_at RSEGS M (sp1 - 8) rav -> L5.u64_at RSEGS M (sp1 - 16) s0v -> L5.u64_at RSEGS M (sp1 - 24) s1v ->
  L5.u64_at RSEGS M (sp1 - 32) s2v ->
  (forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 1040) -> getr R' 10%bv = Z_to_bv 64 (Z.land (w mod 256) 1) -> TK.keepsR CK.CSR R R' ->
      TK.samem (fun _ => True) M M' -> mem_grows M M' -> srealizes RSEGS SCFG (@PML.cfg fx' R' HCT.BR_S M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R HCT.R_IOSBDTOR M model) K.
Proof.
  intros fx R M model K sp1 w p rav s0v s1v s2v Hh Hl Hfp H2 [Hsp Hal] Hw Hp Hr Hs0 Hs1 Hs2 F1 F2 F3 F4 F5 F6 Hcont. change HCT.R_IOSBDTOR with (CC.cp_pc G.cp13).
  set (gl := [w; p; rav; s0v; s1v; s2v]).
  ck_open FPM G.cp13 (G.plans 13%nat _ eq_refl) (-1040) gl (fun _ : nat => @nil byte) (@nil (nat * Z)) sp1 R M fx model K Hh Hl Hfp H2 ck_no_pins.
  - ck_gh E 0%nat w. ck_gh E 1%nat p. ck_gh E 2%nat rav. ck_gh E 3%nat s0v. ck_gh E 4%nat s1v. ck_gh E 5%nat s2v.
    unfold know_ok, G.cp13. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + ck_kw64 (sp1 - 56) w F1. + ck_kw64 (sp1 - 40) p F2. + ck_kw64 (sp1 - 8) rav F3. + ck_kw64 (sp1 - 16) s0v F4. + ck_kw64 (sp1 - 24) s1v F5.
    + ck_kw64 (sp1 - 32) s2v F6.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'. ck_gh E 0%nat w. ck_leaf Hag E'.
    assert (FRM : TK.samem (fun _ => True) M M') by (apply (TK.frame_samem _ _ _ _ _ _ _ HLF); intros a Ha _; cbn [CC.cp_F]; tk_outside).
    ck_leaf_k k Hnth; [|ck_leaf_end k Hnth].
    apply (Hcont fx' R' M' Hfp'); [tk_lin HLF (2%bv : reg) | | ck_keeps HLF Hag64 CK.CSR | exact FRM | exact (CC.lf_grows _ _ _ _ _ _ _ HLF)].
    tk_reg HLF (10%bv : reg). match goal with U : bv_unsigned (ev E' 64) = w |- _ => rewrite (RK.w_of_u _ _ U) end. exact (bit_of_byte w Hw).
Qed.

Lemma s_h_s2l : forall (fx : FPState) R M model K sp1 w p,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp1 - 1040) -> CK.spok sp1 -> getr R 10%bv = Z_to_bv 64 1 ->
  0 <= w < 2 ^ 64 -> 0 <= p < 2 ^ 64 -> L5.u64_at RSEGS M (sp1 - 1032) w -> L5.u64_at RSEGS M (sp1 - 1016) p ->
  (forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 1040) -> getr R' 1%bv = Z_to_bv 64 HCT.R_OPDEL_S2 -> getr R' 10%bv = Z_to_bv 64 p ->
      TK.keepsR CK.CSR R R' -> TK.samem (fun _ => True) M M' -> mem_grows M M' -> srealizes RSEGS SCFG (@PML.cfg fx' R' PML.PC_OPDEL_SIZED M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R HCT.BR_S2 M model) K.
Proof.
  intros fx R M model K sp1 w p Hh Hl Hfp H2 [Hsp Hal] HB Hw Hp F1 F2 Hcont. change HCT.BR_S2 with (CC.cp_pc Gs2l.cp0).
  set (gl := [w; p]).
  ck_open FPM Gs2l.cp0 (Gs2l.plans 0%nat _ eq_refl) (-1040) gl (fun _ : nat => @nil byte) [(10%nat, 1)] sp1 R M fx model K Hh Hl Hfp H2 ck_pins.
  - ck_gh E 0%nat w. ck_gh E 1%nat p. unfold know_ok, Gs2l.cp0. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + ck_kw64 (sp1 - 1032) w F1. + ck_kw64 (sp1 - 1016) p F2.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'. ck_gh E 1%nat p. ck_leaf Hag E'.
    assert (FRM : TK.samem (fun _ => True) M M') by (apply (TK.frame_samem _ _ _ _ _ _ _ HLF); intros a Ha _; cbn [CC.cp_F]; tk_outside).
    ck_leaf_k k Hnth; [|ck_leaf_end k Hnth].
    apply (Hcont fx' R' M' Hfp'); [tk_lin HLF (2%bv : reg) | unfold HCT.R_OPDEL_S2; tk_lin HLF (1%bv : reg) | tk_reg HLF (10%bv : reg); match goal with U : bv_unsigned (ev E' 65) = p |- _ => exact (RK.w_of_u _ _ U) end
      | ck_keeps HLF Hag64 CK.CSR | exact FRM | exact (CC.lf_grows _ _ _ _ _ _ _ HLF)].
Qed.

Lemma s_h_sbl : forall (fx : FPState) R M model K sp1 w p,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp1 - 1040) -> CK.spok sp1 -> getr R 11%bv = Z_to_bv 64 1 ->
  0 <= w < 2 ^ 64 -> 0 <= p < 2 ^ 64 -> L5.u64_at RSEGS M (sp1 - 248) w -> L5.u64_at RSEGS M (sp1 - 232) p ->
  (forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 1040) -> getr R' 1%bv = Z_to_bv 64 HCT.R_OPDEL_SB -> getr R' 10%bv = Z_to_bv 64 p ->
      TK.keepsR CK.CSR R R' -> TK.samem (fun _ => True) M M' -> mem_grows M M' -> srealizes RSEGS SCFG (@PML.cfg fx' R' PML.PC_OPDEL_SIZED M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R HCT.BR_SB M model) K.
Proof.
  intros fx R M model K sp1 w p Hh Hl Hfp H2 [Hsp Hal] HB Hw Hp F1 F2 Hcont. change HCT.BR_SB with (CC.cp_pc Gsbl.cp0).
  set (gl := [w; p]).
  ck_open FPM Gsbl.cp0 (Gsbl.plans 0%nat _ eq_refl) (-1040) gl (fun _ : nat => @nil byte) [(11%nat, 1)] sp1 R M fx model K Hh Hl Hfp H2 ck_pins.
  - ck_gh E 0%nat w. ck_gh E 1%nat p. unfold know_ok, Gsbl.cp0. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + ck_kw64 (sp1 - 248) w F1. + ck_kw64 (sp1 - 232) p F2.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'. ck_gh E 1%nat p. ck_leaf Hag E'.
    assert (FRM : TK.samem (fun _ => True) M M') by (apply (TK.frame_samem _ _ _ _ _ _ _ HLF); intros a Ha _; cbn [CC.cp_F]; tk_outside).
    ck_leaf_k k Hnth; [|ck_leaf_end k Hnth].
    apply (Hcont fx' R' M' Hfp'); [tk_lin HLF (2%bv : reg) | unfold HCT.R_OPDEL_SB; tk_lin HLF (1%bv : reg) | tk_reg HLF (10%bv : reg); match goal with U : bv_unsigned (ev E' 65) = p |- _ => exact (RK.w_of_u _ _ U) end
      | ck_keeps HLF Hag64 CK.CSR | exact FRM | exact (CC.lf_grows _ _ _ _ _ _ _ HLF)].
Qed.

Lemma s_h_sl : forall (fx : FPState) R M model K sp1 w p,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp1 - 1040) -> CK.spok sp1 -> getr R 10%bv = Z_to_bv 64 1 ->
  0 <= w < 2 ^ 64 -> 0 <= p < 2 ^ 64 -> L5.u64_at RSEGS M (sp1 - 56) w -> L5.u64_at RSEGS M (sp1 - 40) p ->
  (forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 1040) -> getr R' 1%bv = Z_to_bv 64 HCT.R_OPDEL_S -> getr R' 10%bv = Z_to_bv 64 p ->
      TK.keepsR CK.CSR R R' -> TK.samem (fun _ => True) M M' -> mem_grows M M' -> srealizes RSEGS SCFG (@PML.cfg fx' R' PML.PC_OPDEL_SIZED M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R HCT.BR_S M model) K.
Proof.
  intros fx R M model K sp1 w p Hh Hl Hfp H2 [Hsp Hal] HB Hw Hp F1 F2 Hcont. change HCT.BR_S with (CC.cp_pc Gsl.cp0).
  set (gl := [w; p]).
  ck_open FPM Gsl.cp0 (Gsl.plans 0%nat _ eq_refl) (-1040) gl (fun _ : nat => @nil byte) [(10%nat, 1)] sp1 R M fx model K Hh Hl Hfp H2 ck_pins.
  - ck_gh E 0%nat w. ck_gh E 1%nat p. unfold know_ok, Gsl.cp0. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + ck_kw64 (sp1 - 56) w F1. + ck_kw64 (sp1 - 40) p F2.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'. ck_gh E 1%nat p. ck_leaf Hag E'.
    assert (FRM : TK.samem (fun _ => True) M M') by (apply (TK.frame_samem _ _ _ _ _ _ _ HLF); intros a Ha _; cbn [CC.cp_F]; tk_outside).
    ck_leaf_k k Hnth; [|ck_leaf_end k Hnth].
    apply (Hcont fx' R' M' Hfp'); [tk_lin HLF (2%bv : reg) | unfold HCT.R_OPDEL_S; tk_lin HLF (1%bv : reg) | tk_reg HLF (10%bv : reg); match goal with U : bv_unsigned (ev E' 65) = p |- _ => exact (RK.w_of_u _ _ U) end
      | ck_keeps HLF Hag64 CK.CSR | exact FRM | exact (CC.lf_grows _ _ _ _ _ _ _ HLF)].
Qed.

Lemma s_h_sbs : forall (fx : FPState) R M model K sp1,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp1 - 1040) -> CK.spok sp1 -> getr R 11%bv = Z_to_bv 64 0 ->
  PML.img_ro M -> L5.defined M (sp1 - 312) 8 ->
  (forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 1040) -> getr R' 1%bv = Z_to_bv 64 HCT.R_LOCDTOR -> getr R' 10%bv = Z_to_bv 64 (sp1 - 304) ->
      TK.keepsR CK.CSR R R' -> L5.u64_at RSEGS M' (sp1 - 312) HCT.VT_SBUF1 -> TK.samem (fun a => ~ (sp1 - 312 <= a < sp1 - 304)) M M' -> mem_grows M M' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' PML.PC_LOCALE_DTOR M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R HCT.BR_SB M model) K.
Proof.
  intros fx R M model K sp1 Hh Hl Hfp H2 [Hsp Hal] HB RO D1 Hcont. change HCT.BR_SB with (CC.cp_pc Gsbs.cp0).
  ck_open FPM Gsbs.cp0 (Gsbs.plans 0%nat _ eq_refl) (-1040) (@nil Z) (fun _ : nat => @nil byte) [(11%nat, 0)] sp1 R M fx model K Hh Hl Hfp H2 ck_pins.
  - unfold know_ok, Gsbs.cp0. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil]. + e_range. + e_align Hal. + tk_kimg RO. + e_unk. + e_wr.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'. ck_leaf Hag E'.
    assert (FRM : TK.samem (fun a => ~ (sp1 - 312 <= a < sp1 - 304)) M M') by (apply (TK.frame_samem _ _ _ _ _ _ _ HLF); intros a Ha Hk; cbn [CC.cp_F]; tk_outside).
    ck_leaf_k k Hnth; [|ck_leaf_end k Hnth].
    apply (Hcont fx' R' M' Hfp'); [tk_lin HLF (2%bv : reg) | unfold HCT.R_LOCDTOR; tk_lin HLF (1%bv : reg) | tk_lin HLF (10%bv : reg) | ck_keeps HLF Hag64 CK.CSR | | exact FRM
      | exact (CC.lf_grows _ _ _ _ _ _ _ HLF)].
    unfold HCT.VT_SBUF1. ck_cell64 HLF (EVar 2) (-312) (ELit 791696). reflexivity.
Qed.

Lemma s_h_ss : forall (fx : FPState) R M model K sp1 rav s0v s1v s2v,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp1 - 1040) -> CK.spok sp1 -> getr R 10%bv = Z_to_bv 64 0 -> L5.ra_ok rav ->
  0 <= s0v < 2 ^ 64 -> 0 <= s1v < 2 ^ 64 -> 0 <= s2v < 2 ^ 64 -> L5.u64_at RSEGS M (sp1 - 8) rav -> L5.u64_at RSEGS M (sp1 - 16) s0v -> L5.u64_at RSEGS M (sp1 - 24) s1v ->
  L5.u64_at RSEGS M (sp1 - 32) s2v ->
  (forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 sp1 -> getr R' 8%bv = Z_to_bv 64 s0v -> getr R' 9%bv = Z_to_bv 64 s1v -> getr R' 18%bv = Z_to_bv 64 s2v ->
      getr R' 10%bv = Z_to_bv 64 0 ->
      TK.keepsR KOH R R' -> TK.samem (fun _ => True) M M' -> mem_grows M M' -> srealizes RSEGS SCFG (@PML.cfg fx' R' rav M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R HCT.BR_S M model) K.
Proof.
  intros fx R M model K sp1 rav s0v s1v s2v Hh Hl Hfp H2 [Hsp Hal] HB Hra Hs0 Hs1 Hs2 F1 F2 F3 F4 Kret. change HCT.BR_S with (CC.cp_pc Gss.cp0).
  assert (Hrav : 0 <= rav < 2 ^ 64) by (destruct Hra; lia).
  set (gl := [rav; s0v; s1v; s2v]).
  ck_open FPM Gss.cp0 (Gss.plans 0%nat _ eq_refl) (-1040) gl (fun _ : nat => @nil byte) [(10%nat, 0)] sp1 R M fx model K Hh Hl Hfp H2 ck_pins.
  - ck_gh E 0%nat rav. ck_gh E 1%nat s0v. ck_gh E 2%nat s1v. ck_gh E 3%nat s2v.
    unfold know_ok, Gss.cp0. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + ck_kw64 (sp1 - 8) rav F1. + ck_kw64 (sp1 - 16) s0v F2. + ck_kw64 (sp1 - 24) s1v F3. + ck_kw64 (sp1 - 32) s2v F4.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'. ck_gh E 0%nat rav. ck_gh E 1%nat s0v. ck_gh E 2%nat s1v. ck_gh E 3%nat s2v. ck_leaf Hag E'.
    assert (FRM : TK.samem (fun _ => True) M M') by (apply (TK.frame_samem _ _ _ _ _ _ _ HLF); intros a Ha _; cbn [CC.cp_F]; tk_outside).
    ck_leaf_k k Hnth; [|ck_leaf_end k Hnth].
    assert (R1 : getr R' 1%bv = Z_to_bv 64 rav) by (tk_reg HLF (1%bv : reg); match goal with U : bv_unsigned (ev E' 64) = rav |- _ => exact (RK.w_of_u _ _ U) end).
    apply (CK.ret_leaf fx' R' _ M' model K rav ret_h Hh Hl R1 Hra).
    apply (Kret fx' R' M' Hfp'); [tk_lin HLF (2%bv : reg) | tk_reg HLF (8%bv : reg); match goal with U : bv_unsigned (ev E' 65) = s0v |- _ => exact (RK.w_of_u _ _ U) end
      | tk_reg HLF (9%bv : reg); match goal with U : bv_unsigned (ev E' 66) = s1v |- _ => exact (RK.w_of_u _ _ U) end
      | tk_reg HLF (18%bv : reg); match goal with U : bv_unsigned (ev E' 67) = s2v |- _ => exact (RK.w_of_u _ _ U) end | tk_lin HLF (10%bv : reg) | ck_keeps HLF Hag64 KOH
      | exact FRM | exact (CC.lf_grows _ _ _ _ _ _ _ HLF)].
Qed.

Lemma s_h_ropdel_s : forall (fx : FPState) R M model K sp1 rav s0v s1v s2v,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp1 - 1040) -> CK.spok sp1 -> L5.ra_ok rav ->
  0 <= s0v < 2 ^ 64 -> 0 <= s1v < 2 ^ 64 -> 0 <= s2v < 2 ^ 64 -> L5.u64_at RSEGS M (sp1 - 8) rav -> L5.u64_at RSEGS M (sp1 - 16) s0v -> L5.u64_at RSEGS M (sp1 - 24) s1v ->
  L5.u64_at RSEGS M (sp1 - 32) s2v ->
  (forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 sp1 -> getr R' 8%bv = Z_to_bv 64 s0v -> getr R' 9%bv = Z_to_bv 64 s1v -> getr R' 18%bv = Z_to_bv 64 s2v ->
      getr R' 10%bv = Z_to_bv 64 0 ->
      TK.keepsR KOH R R' -> TK.samem (fun _ => True) M M' -> mem_grows M M' -> srealizes RSEGS SCFG (@PML.cfg fx' R' rav M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R HCT.R_OPDEL_S M model) K.
Proof.
  intros fx R M model K sp1 rav s0v s1v s2v Hh Hl Hfp H2 [Hsp Hal] Hra Hs0 Hs1 Hs2 F1 F2 F3 F4 Kret. change HCT.R_OPDEL_S with (CC.cp_pc G.cp14).
  assert (Hrav : 0 <= rav < 2 ^ 64) by (destruct Hra; lia).
  set (gl := [rav; s0v; s1v; s2v]).
  ck_open FPM G.cp14 (G.plans 14%nat _ eq_refl) (-1040) gl (fun _ : nat => @nil byte) (@nil (nat * Z)) sp1 R M fx model K Hh Hl Hfp H2 ck_no_pins.
  - ck_gh E 0%nat rav. ck_gh E 1%nat s0v. ck_gh E 2%nat s1v. ck_gh E 3%nat s2v.
    unfold know_ok, G.cp14. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + ck_kw64 (sp1 - 8) rav F1. + ck_kw64 (sp1 - 16) s0v F2. + ck_kw64 (sp1 - 24) s1v F3. + ck_kw64 (sp1 - 32) s2v F4.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'. ck_gh E 0%nat rav. ck_gh E 1%nat s0v. ck_gh E 2%nat s1v. ck_gh E 3%nat s2v. ck_leaf Hag E'.
    assert (FRM : TK.samem (fun _ => True) M M') by (apply (TK.frame_samem _ _ _ _ _ _ _ HLF); intros a Ha _; cbn [CC.cp_F]; tk_outside).
    ck_leaf_k k Hnth; [|ck_leaf_end k Hnth].
    assert (R1 : getr R' 1%bv = Z_to_bv 64 rav) by (tk_reg HLF (1%bv : reg); match goal with U : bv_unsigned (ev E' 64) = rav |- _ => exact (RK.w_of_u _ _ U) end).
    apply (CK.ret_leaf fx' R' _ M' model K rav ret_h Hh Hl R1 Hra).
    apply (Kret fx' R' M' Hfp'); [tk_lin HLF (2%bv : reg) | tk_reg HLF (8%bv : reg); match goal with U : bv_unsigned (ev E' 65) = s0v |- _ => exact (RK.w_of_u _ _ U) end
      | tk_reg HLF (9%bv : reg); match goal with U : bv_unsigned (ev E' 66) = s1v |- _ => exact (RK.w_of_u _ _ U) end
      | tk_reg HLF (18%bv : reg); match goal with U : bv_unsigned (ev E' 67) = s2v |- _ => exact (RK.w_of_u _ _ U) end | tk_lin HLF (10%bv : reg) | ck_keeps HLF Hag64 KOH
      | exact FRM | exact (CC.lf_grows _ _ _ _ _ _ _ HLF)].
Qed.
End S.
End HCS.
