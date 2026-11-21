(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the state invariants take the launch record [LaunchX], and the argument area is read from it; the hop's variable bound is the renumbered one). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.openssl.hashtable.images Require Import AsanUbsan.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import PropExec ShapeAlg AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanInit CertRefl.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import CxRel CxPlan CxPlanSound CxGlue CxReblob CxOpt CxOptGen CxOptK CxRefront CxfL9 CxfFast HBPlanImage HBAtable HBArg HBCheckG HBChain HBHop HBUsageDefs HBParity
  HBVtHop BVT012Lit BFIEndA0se7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import CAP. Import CXS.
Open Scope Z_scope.
Definition htg_a0e_ (_ : unit) : htgt := (t012, t012_sig_a0e, t012_F_a0e).
Abbreviation htg_a0e := (htg_a0e_ tt).
Lemma htok_a0e : ht_ok t012_NX htg_a0e = true. Proof. vm_compute. reflexivity. Qed.
Lemma nxge_a0e : (NX0 <= t012_NX)%nat. Proof. apply Nat.leb_le. vm_compute. reflexivity. Qed.
Lemma nxspw_a0e : CAP.expr_vars_lt t012_NX e_spw = true. Proof. vm_compute. reflexivity. Qed.
Lemma chk_a0e : CAP.check HASEGS vt_IT HAT t012_NX AsanInit.LIMIT (hag_XN t012_NX) (hag_XE t012_NX) hag_XB (HS_tg [(950%nat, htg_a0e)]) 0 true false true 400000 3000 None fienda0se7 vhpl_a0e = COk (SHole 950).
Proof. apply CXFF.check_l_intro. ltac2:(cert_refl_vm constr:(COk (SHole 950))). Qed.
Section M.
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variable brk0 : word.
  Variables argv envp : list (list byte).
  Variable fs : Fs.Fs.
  Variables uid hw : word.
  Context {L : LaunchX}.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Let c := content_of argv fs.
  #[local] Notation SV := (SINVm HAPH sp rdraw brk0 argv envp uid hw L c).
  #[local] Notation argH := (argH0 sp rdraw argv envp (lx_kb L) (lx_execfn L)).
  #[local] Notation ISP := (bv_unsigned sp).
  Variable PHI : env -> Prop.
  Hypothesis PHI_agree : forall E E', env_agree NX0 E E' -> PHI E -> PHI E'.
  Variable T : env -> Fs.Fs -> TSet.
  Hypothesis T_agree : t_agree T.
  Hypothesis T_nil : forall E fs0, T E fs0 [].
  (* [comment removed for export] *)
  Hypothesis Htmpl : forall PHIb : env -> Prop, piece (SVG PHIb SV) argH ISP fs (with_facts t012 [par_even]) T.
  Theorem vtail_a0e : piece (SVG PHI SV) argH ISP fs fienda0se7 T.
  Proof.
    exact (vt_hop sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit PHI PHI_agree T T_agree T_nil t012_NX nxge_a0e nxspw_a0e
             t012 fienda0se7 t012_sig_a0e t012_F_a0e vt_IT vt_IT_ok vhpl_a0e 950%nat htok_a0e Htmpl chk_a0e).
  Qed.
End M.
