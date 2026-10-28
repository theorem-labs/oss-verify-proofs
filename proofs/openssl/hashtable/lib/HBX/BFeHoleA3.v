(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63 PrimString.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.openssl.hashtable.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.FX Require Import W64 ITrie FxInstr FxState FxMem FxExec FxRel FxImage FxHandoff.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import PropExec ShapeAlg AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanInit.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import CxRel CxPlan CxPlanSound CxReblob HBPlanImage HBAtable HBChain BC3A3Lit BFEEndA3.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.Br Require Import BrEnv BrRev BrClass BrRevS BrDress BrTrans BrGen BrHole.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib.HBX Require Import BFePcsX BFeDataA3.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma IM_eq : mk_fimage HASEGS = Some IM.
Proof. vm_cast_no_check (eq_refl (Some IM)). Qed.
Lemma code_eq : build_code HASEGS fe_pcs = Some code.
Proof. vm_cast_no_check (eq_refl (Some code)). Qed.

Lemma fe_tr_check :
  tr_check IM HAT APC.NX0 TT 1000 shapes [] [] START d bs F' VT
           (AX2.s_pc (CAP.a_ss END)) (AX2.s_regs (CAP.a_ss END)) (CAP.kn END) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma fe_side : side_chk HAT TT (CAP.kn START) d = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma fe_run : fx_run IM code BP 20 (dress (state_of d) bs) = (F', RS, CNT).
Proof. vm_cast_no_check (eq_refl (F', RS, CNT)). Qed.
Lemma fe_end : tr_state START (AX2.s_pc (CAP.a_ss END)) (AX2.s_regs (CAP.a_ss END)) (CAP.kn END) (CAP.nxt END) = END.
Proof. vm_cast_no_check (eq_refl END). Qed.

Section FeHole.
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variable brk0 : word.
  Variables argv envp : list (list byte).
  Variable fs : Fs.Fs.
  Variables uid hw : word.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Let c := content_of argv fs.
  #[local] Notation SV := (SINVm HAPH sp rdraw brk0 argv envp uid hw c).
  #[local] Notation argH := (argH0 HAPH sp rdraw argv envp uid hw).
  #[local] Notation ISP := (bv_unsigned sp).

  Theorem fe_hole_a3 : HBChain.fx_hole SV argH ISP fs c3a3_hs20 feenda3.
  Proof.
    pose proof (fx_hole_chk CxRel.cfg0 HASEGS IM code (build_code_ok HASEGS fe_pcs code code_eq)
                  (mk_fimage_ok HASEGS IM IM_eq) (mk_fimage_wr_ok HASEGS IM IM_eq)
                  HAT AsanInit.LIMIT SV argH ISP fs hat_in_hull hat_hull_ok
                  (argH0_high HAPH sp rdraw argv envp uid hw Hsp Hva) APC.NX0 eq_refl
                  (argH0_agree HAPH sp rdraw argv envp uid hw)
                  (SINVm_agree HAPH sp rdraw brk0 argv envp uid hw c)
                  (SINVm_frame HAPH sp rdraw brk0 argv envp uid hw c)
                  TT 1000%uint63 shapes [] [] START d bs BP 20 F' RS CNT VT END
                  fe_tr_check fe_side ltac:(lia) fe_run fe_end) as Hh.
    exact Hh.
  Qed.
End FeHole.
Check fe_hole_a3.
(* [comment removed for export] *)
