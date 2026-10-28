(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63 PrimString.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.openssl.hashtable.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.FX Require Import W64 ITrie FxInstr FxState FxMem FxExec FxRel FxImage FxHandoff
  FxDrive FxDrive3 FxDrive3D FxDrive3O.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import PropExec ShapeAlg AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanInit.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import CxRel CxPlan CxPlanSound CxReblob HBPlanImage HBAtable HBChain BC7A3Lit HBParity BFIaEndA3o.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.Br Require Import BrEnv BrRev BrClass BrRevS BrDress BrTrans BrGen BrHole Br3Root Br3Leaf Br3Know Br3Trans
  Br3X Br3RespDefs Br3Resp.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib.HBX Require Import BFIPcs BFI8DataA3ao BFI8EndA3ao BFI8AuxA3ao.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma IM_eq : mk_fimage HASEGS = Some IM.
Proof. vm_cast_no_check (eq_refl (Some IM)). Qed.   (* [comment removed for export] *)
Lemma code_eq : build_code HASEGS fi_pcs = Some code.
Proof. vm_cast_no_check (eq_refl (Some code)). Qed.

(* [comment removed for export] *)
Lemma START_eq : resp_cs RTs START0 = START.
Proof. vm_cast_no_check (eq_refl START). Qed.
Lemma END_eq : resp_cs RTe END0 = END.
Proof. vm_cast_no_check (eq_refl END). Qed.
Lemma fi_resp_check : resp_chk RTs RTe START0 END0 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma fi_end_back : CAP.set_kn (resp_cs RTe END0) (CAP.kn END0) = END0.
Proof. vm_cast_no_check (eq_refl END0). Qed.

(* [comment removed for export] *)
Definition HK : hooksel := HK7 96 16 16.
Lemma fi_trans_check :
  trans3x_chk HASEGS IM code HAT AsanInit.LIMIT APC.NX0 TT NTAG shapes [] classes START d bs L3 W RBYTES RC shp xask BP 20 1000000 END aux XF XA HK = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Section FIHole.
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

  Theorem fi_hole_a3ao : HBChain.fx_hole SV argH ISP fs START0 END0.
  Proof.
    pose proof (fx_hole3x_chk CxRel.cfg0 HASEGS IM code (build_code_ok HASEGS fi_pcs code code_eq) eq_refl
                  (mk_fimage_ok HASEGS IM IM_eq) (mk_fimage_wr_ok HASEGS IM IM_eq)
                  HAT AsanInit.LIMIT SV argH ISP fs hat_in_hull hat_hull_ok
                  (argH0_high HAPH sp rdraw argv envp uid hw Hsp Hva) APC.NX0 eq_refl
                  (argH0_agree HAPH sp rdraw argv envp uid hw)
                  (SINVm_agree HAPH sp rdraw brk0 argv envp uid hw c)
                  (SINVm_frame HAPH sp rdraw brk0 argv envp uid hw c)
                  TT NTAG shapes [] classes START d bs L3 W RBYTES RC shp xask BP 20%nat 1000000%nat END aux XF XA HK
                  fi_trans_check ltac:(lia)) as Hh.
    rewrite <- START_eq, <- END_eq in Hh.
    exact (fx_hole_resp CxRel.cfg0 HASEGS HAT AsanInit.LIMIT SV argH ISP fs
             (SINVm_frame HAPH sp rdraw brk0 argv envp uid hw c) RTs RTe START0 END0 fi_resp_check fi_end_back Hh).
  Qed.
End FIHole.
Check fi_hole_a3ao.
(* [comment removed for export] *)
