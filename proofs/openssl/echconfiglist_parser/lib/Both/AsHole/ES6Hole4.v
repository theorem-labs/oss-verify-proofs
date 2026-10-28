(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63 PrimString.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.openssl.echconfiglist_parser.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Common.FX Require Import W64 ITrie FxInstr FxState FxMem FxExec FxRel FxImage FxHandoff
  FxDrive FxDrive3 FxDrive3D FxDrive3O.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import PropExec ShapeAlg Scfg AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanInit.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.AsCert Require Import AsImages AsPlanImages EAsStartupHSA.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.AsHole Require Import ES6End4.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Common.Br Require Import CXI BrEnv BrRev BrClass BrRevS BrDress BrTrans BrGen BrHole Br3Root Br3Leaf Br3Know Br3Trans.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.AsHole Require Import ES6Pcs ES6Img ES6Start ES6Data4 ES6Aux4.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition HK : hooksel := HK7 96 16 16.
Lemma s6_trans_check :
  trans3h_chk HK ASEGS IM code ASAN_H AsanInit.LIMIT APC.NX0 TT NTAG shapes [] classes START d bs L3 W RBYTES RC shp xask BP 20 64 END aux = true.
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
  #[local] Notation SV := (SINV0 APH sp rdraw brk0 argv envp uid hw).
  #[local] Notation argH := (argH0 APH sp rdraw argv envp uid hw).
  #[local] Notation ISP := (bv_unsigned sp).

  (* [comment removed for export] *)
  Lemma argH0_highI : forall E (a : word), argH E a = true -> APC.CEIL <= bv_unsigned a /\ ISP <= bv_unsigned a.
  Proof.
    intros E x Hx. split; [exact (argH0_high APH sp rdraw argv envp uid hw Hsp Hva E x Hx)|].
    unfold argH0 in Hx. apply andb_prop in Hx as [Hx _]. unfold argB0 in Hx.
    apply orb_prop in Hx as [Hx|Hx]; apply andb_prop in Hx as [Hx _]; apply Z.leb_le in Hx; lia.
  Qed.

  Theorem s6_hole_4 :
    BrHole.fx_hole the_scfg ASEGS ASAN_H AsanInit.LIMIT SV argH ISP fs s6start4 es6end4.
  Proof.
    pose proof (fx_hole3h_chk the_scfg ASEGS IM code (build_code_ok ASEGS s6_pcs code code_eq) eq_refl
                  (mk_fimage_ok ASEGS IM IM_eq) (mk_fimage_wr_ok ASEGS IM IM_eq)
                  ASAN_H AsanInit.LIMIT SV argH ISP fs asan_in_hull asan_hull_ok
                  argH0_highI APC.NX0 eq_refl
                  (argH0_agree APH sp rdraw argv envp uid hw)
                  (SINV0_agree APH sp rdraw brk0 argv envp uid hw)
                  (SINV0_frame APH sp rdraw brk0 argv envp uid hw)
                  HK TT NTAG shapes [] classes START d bs L3 W RBYTES RC shp xask BP 20%nat 64%nat END aux
                  s6_trans_check ltac:(lia)) as Hh.
    exact Hh.
  Qed.
End S6Hole.
Check s6_hole_4.
