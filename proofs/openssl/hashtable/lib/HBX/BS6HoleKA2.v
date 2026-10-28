(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63 PrimString.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.openssl.hashtable.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.FX Require Import W64 ITrie FxInstr FxState FxMem FxExec FxRel FxImage FxHandoff
  FxDrive FxDrive3 FxDrive3D FxDrive3O.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import PropExec ShapeAlg AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanInit.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import CxRel CxPlan CxPlanSound CxReblob HBPlanImage HBAtable HBChain BC2A2Lit BS6EndA2K.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.Br Require Import BrEnv BrRev BrClass BrRevS BrDress BrTrans BrGen BrHole Br3Root Br3Leaf Br3Know Br3Trans.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib.HBX Require Import BS6Pcs BS6DataA2 BS6AuxKA2.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma IM_eq : mk_fimage HASEGS = Some IM.
Proof. vm_cast_no_check (eq_refl (Some IM)). Qed.
Lemma code_eq : build_code HASEGS s6_pcs = Some code.
Proof. vm_cast_no_check (eq_refl (Some code)). Qed.

(* [comment removed for export] *)
Definition HK : hooksel := HK7 96 16 16.
Lemma s6_trans_check :
  trans3h_chk HK HASEGS IM code HAT AsanInit.LIMIT APC.NX0 TT NTAG shapes [] classes START d bs L3 W RBYTES RC shp xask BP 20 64 END aux = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Section S6Hole.
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

  Theorem s6_hole_ka2 : HBChain.fx_hole SV argH ISP fs c2a2_hs10 s6enda2k.
  Proof.
    pose proof (fx_hole3h_chk CxRel.cfg0 HASEGS IM code (build_code_ok HASEGS s6_pcs code code_eq) eq_refl
                  (mk_fimage_ok HASEGS IM IM_eq) (mk_fimage_wr_ok HASEGS IM IM_eq)
                  HAT AsanInit.LIMIT SV argH ISP fs hat_in_hull hat_hull_ok
                  (argH0_high HAPH sp rdraw argv envp uid hw Hsp Hva) APC.NX0 eq_refl
                  (argH0_agree HAPH sp rdraw argv envp uid hw)
                  (SINVm_agree HAPH sp rdraw brk0 argv envp uid hw c)
                  (SINVm_frame HAPH sp rdraw brk0 argv envp uid hw c)
                  HK TT NTAG shapes [] classes START d bs L3 W RBYTES RC shp xask BP 20%nat 64%nat END aux
                  s6_trans_check ltac:(lia)) as Hh.
    exact Hh.
  Qed.
End S6Hole.
Check s6_hole_ka2.
(* [comment removed for export] *)
