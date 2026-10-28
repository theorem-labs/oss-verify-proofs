(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.openssl.hashtable.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import PropExec ShapeAlg AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanNodesIO AsanInit.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import CertRefl CxRel CxPlan CxPlanSound CxGlue CxBatch CxOfAps CxReblob.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import HBPlanImage HBAtable HBArg HBCheckG HBChain HBHop HBBatch HBFam2 HBParity HBSel BVT012Se BNTeS0 BNTeDgn BNTeThmgn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import CAP. Import CXS.
Open Scope Z_scope.
Definition BASE_ (_ : unit) : acs := vt012se.
Abbreviation BASE := (BASE_ tt).
Definition NB : nat := Eval vm_compute in nxt BASE.
Definition lnums_ (_ : unit) : list cellq := [(9, 12, 0, 0); (8, 11, 1, 7); (33, 36, 0, 0); (32, 35, 1, 7); (45, 48, 0, 0); (44, 47, 1, 7); (57, 80, 0, 0); (56, 79, 1, 7); (241, 368, 0, 0); (240, 367, 1, 7); (497, 511, 0, 0); (496, 511, 1, 7); (512, 736, 0, 0); (512, 735, 1, 7); (737, 992, 0, 0); (736, 991, 1, 7); (993, 1504, 0, 0); (992, 1503, 1, 7); (4033, 6016, 0, 0); (4032, 6015, 1, 7)].
Abbreviation lnums := (lnums_ tt).
Definition DL_ (_ : unit) : list (nat * nat * Z * Z * Z) := [(235%nat, 236%nat, 4096, 17594333433856, 140600040943616)].
Abbreviation DL := (DL_ tt).
Lemma HNB : nxt BASE = NB. Proof. vm_compute. reflexivity. Qed.
Lemma HNB0 : (NX0 <= NB)%nat. Proof. vm_compute. repeat constructor. Qed.
Lemma NB_spw : CAP.expr_vars_lt NB e_spw = true. Proof. vm_compute. reflexivity. Qed.
Lemma Hfresh : fresh_ok NB BASE = true. Proof. vm_compute. reflexivity. Qed.
Lemma Hsub : forallb (fun K => kn_mem K BASE) (kn NTe_cs) = true. Proof. change ((let b := BASE in forallb (fun K => kn_mem K b) (kn NTe_cs)) = true). vm_cast_no_check (eq_refl true). Qed.
Lemma Hbump : node_bump (set_kn BASE (kn NTe_cs)) BNTeDgn.N0 = Some NTe_cs. Proof. vm_compute. reflexivity. Qed.
Lemma Hext : forall b, sig_ok NB (s_ext 1130%nat 1131%nat 1132%nat 1133%nat 1134%nat 1135%nat 1136%nat b) = true. Proof. intros []; vm_compute; reflexivity. Qed.
Lemma Hvars : forallb (expr_vars_lt NB) [e_cl; e_n; e_cm; e_b1s; EVar LV] = true. Proof. vm_compute. reflexivity. Qed.
Lemma HKN : (kn_mem (KRange (EVar LV) 6 65535) BASE && kn_mem (KRange e_cl 0 32767) BASE && kn_mem (KRange e_n 0 65529) BASE && blob_mem BASE)%bool = true. Proof. vm_compute. reflexivity. Qed.
Lemma Hshapes : shapeB = shapeB_of 1130 false /\ sC2s = sC2s_can /\ sXs = sXs_of false. Proof. repeat split; vm_compute; reflexivity. Qed.
Lemma CHK : chk 1130%nat 1131%nat 1132%nat 1133%nat 1134%nat 1135%nat 1136%nat BASE NB BNTeDgn.N0 a0s leaves lnums DL 65 96 = true. Proof. vm_compute. reflexivity. Qed.
Lemma CHK1 : chk 1130%nat 1131%nat 1132%nat 1133%nat 1134%nat 1135%nat 1136%nat BASE NB BNTeDgn.N0 a0s leaves lnums DL 257 288 = true. Proof. vm_compute. reflexivity. Qed.
Lemma CHK2 : chk 1130%nat 1131%nat 1132%nat 1133%nat 1134%nat 1135%nat 1136%nat BASE NB BNTeDgn.N0 a0s leaves lnums DL 353 384 = true. Proof. vm_compute. reflexivity. Qed.
Lemma CHK3 : chk 1130%nat 1131%nat 1132%nat 1133%nat 1134%nat 1135%nat 1136%nat BASE NB BNTeDgn.N0 a0s leaves lnums DL 449 640 = true. Proof. vm_compute. reflexivity. Qed.
Lemma CHK4 : chk 1130%nat 1131%nat 1132%nat 1133%nat 1134%nat 1135%nat 1136%nat BASE NB BNTeDgn.N0 a0s leaves lnums DL 1921 2944 = true. Proof. vm_compute. reflexivity. Qed.
Lemma CHK5 : chk 1130%nat 1131%nat 1132%nat 1133%nat 1134%nat 1135%nat 1136%nat BASE NB BNTeDgn.N0 a0s leaves lnums DL 3969 12032 = true. Proof. vm_compute. reflexivity. Qed.
Lemma CHK6 : chk 1130%nat 1131%nat 1132%nat 1133%nat 1134%nat 1135%nat 1136%nat BASE NB BNTeDgn.N0 a0s leaves lnums DL 32257 48128 = true. Proof. vm_compute. reflexivity. Qed.
Section D.
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variable brk0 : word.
  Variables argv envp : list (list byte).
  Variable fs : Fs.Fs.
  Variables uid hw : word.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Let c := content_of argv fs.
  #[local] Notation SV := (SINVm HAPH sp rdraw brk0 argv envp uid hw c).
  #[local] Notation argH := (argH0 HAPH sp rdraw argv envp uid hw).
  Hypothesis H_FE : fx_hole SV argH (bv_unsigned sp) fs TFE TFEE.
  Theorem drive : forall (PHIb : env -> Prop) E R FULL model,
    cs_ok HASEGS HAT AsanInit.LIMIT (SVG PHIb SV) argH (bv_unsigned sp) fs E BASE R FULL model -> 65 <= nb_of E <= 96 ->
    crz HASEGS (cfg_of HASEGS R (pc BASE) FULL model) (TGT false (calls_of E) (cnt_of E) (m_fs model)).
  Proof.
    exact (grp_drive sp rdraw argv envp uid hw fs SV (SINVm_agree HAPH sp rdraw brk0 argv envp uid hw c) 1130%nat 1131%nat 1132%nat 1133%nat 1134%nat 1135%nat 1136%nat BASE NTe_cs NB BNTeDgn.N0
             HNB HNB0 NB_spw Hfresh Hsub Hbump Hext Hvars HKN a0s leaves lnums shapeB sC2s sXs false Hshapes DL 65 96
             (BNTeThmgn.grp_sound sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FE) CHK).
  Qed.
  Theorem drive1 : forall (PHIb : env -> Prop) E R FULL model,
    cs_ok HASEGS HAT AsanInit.LIMIT (SVG PHIb SV) argH (bv_unsigned sp) fs E BASE R FULL model -> 257 <= nb_of E <= 288 ->
    crz HASEGS (cfg_of HASEGS R (pc BASE) FULL model) (TGT false (calls_of E) (cnt_of E) (m_fs model)).
  Proof.
    exact (grp_drive sp rdraw argv envp uid hw fs SV (SINVm_agree HAPH sp rdraw brk0 argv envp uid hw c) 1130%nat 1131%nat 1132%nat 1133%nat 1134%nat 1135%nat 1136%nat BASE NTe_cs NB BNTeDgn.N0
             HNB HNB0 NB_spw Hfresh Hsub Hbump Hext Hvars HKN a0s leaves lnums shapeB sC2s sXs false Hshapes DL 257 288
             (BNTeThmgn.grp_sound sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FE) CHK1).
  Qed.
  Theorem drive2 : forall (PHIb : env -> Prop) E R FULL model,
    cs_ok HASEGS HAT AsanInit.LIMIT (SVG PHIb SV) argH (bv_unsigned sp) fs E BASE R FULL model -> 353 <= nb_of E <= 384 ->
    crz HASEGS (cfg_of HASEGS R (pc BASE) FULL model) (TGT false (calls_of E) (cnt_of E) (m_fs model)).
  Proof.
    exact (grp_drive sp rdraw argv envp uid hw fs SV (SINVm_agree HAPH sp rdraw brk0 argv envp uid hw c) 1130%nat 1131%nat 1132%nat 1133%nat 1134%nat 1135%nat 1136%nat BASE NTe_cs NB BNTeDgn.N0
             HNB HNB0 NB_spw Hfresh Hsub Hbump Hext Hvars HKN a0s leaves lnums shapeB sC2s sXs false Hshapes DL 353 384
             (BNTeThmgn.grp_sound sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FE) CHK2).
  Qed.
  Theorem drive3 : forall (PHIb : env -> Prop) E R FULL model,
    cs_ok HASEGS HAT AsanInit.LIMIT (SVG PHIb SV) argH (bv_unsigned sp) fs E BASE R FULL model -> 449 <= nb_of E <= 640 ->
    crz HASEGS (cfg_of HASEGS R (pc BASE) FULL model) (TGT false (calls_of E) (cnt_of E) (m_fs model)).
  Proof.
    exact (grp_drive sp rdraw argv envp uid hw fs SV (SINVm_agree HAPH sp rdraw brk0 argv envp uid hw c) 1130%nat 1131%nat 1132%nat 1133%nat 1134%nat 1135%nat 1136%nat BASE NTe_cs NB BNTeDgn.N0
             HNB HNB0 NB_spw Hfresh Hsub Hbump Hext Hvars HKN a0s leaves lnums shapeB sC2s sXs false Hshapes DL 449 640
             (BNTeThmgn.grp_sound sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FE) CHK3).
  Qed.
  Theorem drive4 : forall (PHIb : env -> Prop) E R FULL model,
    cs_ok HASEGS HAT AsanInit.LIMIT (SVG PHIb SV) argH (bv_unsigned sp) fs E BASE R FULL model -> 1921 <= nb_of E <= 2944 ->
    crz HASEGS (cfg_of HASEGS R (pc BASE) FULL model) (TGT false (calls_of E) (cnt_of E) (m_fs model)).
  Proof.
    exact (grp_drive sp rdraw argv envp uid hw fs SV (SINVm_agree HAPH sp rdraw brk0 argv envp uid hw c) 1130%nat 1131%nat 1132%nat 1133%nat 1134%nat 1135%nat 1136%nat BASE NTe_cs NB BNTeDgn.N0
             HNB HNB0 NB_spw Hfresh Hsub Hbump Hext Hvars HKN a0s leaves lnums shapeB sC2s sXs false Hshapes DL 1921 2944
             (BNTeThmgn.grp_sound sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FE) CHK4).
  Qed.
  Theorem drive5 : forall (PHIb : env -> Prop) E R FULL model,
    cs_ok HASEGS HAT AsanInit.LIMIT (SVG PHIb SV) argH (bv_unsigned sp) fs E BASE R FULL model -> 3969 <= nb_of E <= 12032 ->
    crz HASEGS (cfg_of HASEGS R (pc BASE) FULL model) (TGT false (calls_of E) (cnt_of E) (m_fs model)).
  Proof.
    exact (grp_drive sp rdraw argv envp uid hw fs SV (SINVm_agree HAPH sp rdraw brk0 argv envp uid hw c) 1130%nat 1131%nat 1132%nat 1133%nat 1134%nat 1135%nat 1136%nat BASE NTe_cs NB BNTeDgn.N0
             HNB HNB0 NB_spw Hfresh Hsub Hbump Hext Hvars HKN a0s leaves lnums shapeB sC2s sXs false Hshapes DL 3969 12032
             (BNTeThmgn.grp_sound sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FE) CHK5).
  Qed.
  Theorem drive6 : forall (PHIb : env -> Prop) E R FULL model,
    cs_ok HASEGS HAT AsanInit.LIMIT (SVG PHIb SV) argH (bv_unsigned sp) fs E BASE R FULL model -> 32257 <= nb_of E <= 48128 ->
    crz HASEGS (cfg_of HASEGS R (pc BASE) FULL model) (TGT false (calls_of E) (cnt_of E) (m_fs model)).
  Proof.
    exact (grp_drive sp rdraw argv envp uid hw fs SV (SINVm_agree HAPH sp rdraw brk0 argv envp uid hw c) 1130%nat 1131%nat 1132%nat 1133%nat 1134%nat 1135%nat 1136%nat BASE NTe_cs NB BNTeDgn.N0
             HNB HNB0 NB_spw Hfresh Hsub Hbump Hext Hvars HKN a0s leaves lnums shapeB sC2s sXs false Hshapes DL 32257 48128
             (BNTeThmgn.grp_sound sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FE) CHK6).
  Qed.
End D.
