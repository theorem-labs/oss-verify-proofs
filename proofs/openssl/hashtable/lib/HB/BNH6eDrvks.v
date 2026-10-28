(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.openssl.hashtable.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import PropExec ShapeAlg AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanNodesIO AsanInit.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import CertRefl CxRel CxPlan CxPlanSound CxGlue CxBatch CxOfAps CxReblob.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import HBPlanImage HBAtable HBArg HBCheckG HBChain HBHop HBBatch HBFam2 HBParity HBSelK BVG6T3Se BNH6eS0 BNH6eDks BNH6eThmks.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import CAP. Import CXS.
Open Scope Z_scope.
Definition BASE_ (_ : unit) : acs := vg6t3se.
Abbreviation BASE := (BASE_ tt).
Definition NB : nat := Eval vm_compute in nxt BASE.
Definition lnums_ (_ : unit) : list cellt := [(258047, 260607, 1, 7, (0, 511)); (260608, 522751, 1, 7, (0, 511)); (522752, 524287, 1, 7, (0, 511)); (258048, 260607, 0, 0, (1, 511)); (260608, 522751, 0, 0, (1, 511)); (522752, 524287, 0, 0, (1, 511)); (258048, 260608, 0, 0, (0, 0)); (261120, 522752, 0, 0, (0, 0)); (523264, 523776, 0, 0, (0, 0))].
Abbreviation lnums := (lnums_ tt).
Lemma HL : 32774 <= 2097152 /\ 2097152 <= 4194303 /\ 4194303 < 4194304 + 8192 /\ 2 ^ 17 <= 4194304 <= 2 ^ 40 /\ 4194297 = 4194303 - 6. Proof. lia. Qed.
Definition DL_ (_ : unit) : list (nat * nat * Z * Z * Z) := [(235%nat, 236%nat, 4096, 17594333433856, 140600040943616)].
Abbreviation DL := (DL_ tt).
Lemma HNB : nxt BASE = NB. Proof. vm_compute. reflexivity. Qed.
Lemma HNB0 : (NX0 <= NB)%nat. Proof. vm_compute. repeat constructor. Qed.
Lemma NB_spw : CAP.expr_vars_lt NB e_spw = true. Proof. vm_compute. reflexivity. Qed.
Lemma Hfresh : fresh_ok NB BASE = true. Proof. vm_compute. reflexivity. Qed.
Lemma Hsub : forallb (fun K => kn_mem K BASE) (kn NH6e_cs) = true. Proof. change ((let b := BASE in forallb (fun K => kn_mem K b) (kn NH6e_cs)) = true). vm_cast_no_check (eq_refl true). Qed.
Lemma Hbump : node_bump (set_kn BASE (kn NH6e_cs)) BNH6eDks.N0 = Some NH6e_cs. Proof. vm_compute. reflexivity. Qed.
Lemma Hext : forall b tz, sig_ok NB (s_ext 1130%nat 1131%nat 1132%nat 1133%nat 1134%nat 1135%nat 1136%nat 1137%nat 1138%nat b tz) = true. Proof. intros [] []; vm_compute; reflexivity. Qed.      (* [comment removed for export] *)
Lemma Hvars : forallb (expr_vars_lt NB) [e_cl; e_n; e_cm; e_b1s; EVar LV] = true. Proof. vm_compute. reflexivity. Qed.
Lemma HKN : (kn_mem (KRange (EVar LV) 2097152 4194303) BASE && kn_mem (KRange e_cl 0 32767) BASE && kn_mem (KRange e_n 0 4194297) BASE)%bool = true. Proof. vm_compute. reflexivity. Qed.
Lemma Hshapes : shapeB = shapeB_of 1130 false /\ sC2s = sC2s_can /\ sXs = sXs_of false. Proof. repeat split; vm_compute; reflexivity. Qed.
Lemma CHK : chk 1130%nat 1131%nat 1132%nat 1133%nat 1134%nat 1135%nat 1136%nat 1137%nat 1138%nat 2097152 4194303 4194297 4194304 BASE NB BNH6eDks.N0 a0s leaves lnums DL 2064379 4194297 = true. Proof. vm_compute. reflexivity. Qed.
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
    cs_ok HASEGS HAT AsanInit.LIMIT (SVG PHIb SV) argH (bv_unsigned sp) fs E BASE R FULL model -> 2064379 <= nb_of E <= 4194297 ->
    crz HASEGS (cfg_of HASEGS R (pc BASE) FULL model) (TGT false (calls_of E) (cnt_of E) (m_fs model)).
  Proof.
    exact (grp_drive sp rdraw argv envp uid hw fs SV (SINVm_agree HAPH sp rdraw brk0 argv envp uid hw c) 1130%nat 1131%nat 1132%nat 1133%nat 1134%nat 1135%nat 1136%nat 1137%nat 1138%nat 2097152 4194303 4194297 4194304 HL BASE NH6e_cs NB BNH6eDks.N0
             HNB HNB0 NB_spw Hfresh Hsub Hbump Hext Hvars HKN a0s leaves lnums shapeB sC2s sXs false Hshapes DL 2064379 4194297
             (BNH6eThmks.grp_sound sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FE) CHK).
  Qed.
End D.
