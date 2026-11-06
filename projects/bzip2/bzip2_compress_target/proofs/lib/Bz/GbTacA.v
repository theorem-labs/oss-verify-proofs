(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzDefs BzModel BzTac BzTac2 BzInv BzTables BzContracts.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK DecCutFA DecTacFA A0F_decV A0F_decRet.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import AsanKit.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutFA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decV OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decRet.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require GbKitA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Ltac mkR_setf R n :=
  let p := eval vm_compute in (bv_key (Z_to_bv 5 n)) in
  eval cbv beta iota delta [tset mkR] in (fun wq : word => tset p wq R).

(* [comment removed for export] *)
Ltac til_joinA rq skip HD STRM FRL FRH ST MU WM MI MUL WML :=
  lazymatch goal with |- evt ?sg ?Q (MS ?R ?F ?pc ?fc ?rv ?m ?ro) =>
  lazymatch type of HD with rw_cells _ _ ?Sa ?csH =>
  lazymatch type of STRM with rw_cells _ _ ?strm (?c0 :: ?c1 :: ?c2 :: C4 ?tih0 :: ?rest) =>
  lazymatch type of FRL with rw_cells _ _ ?Pl ?csL =>
  lazymatch type of FRH with rw_cells _ _ ?Ph ?csHi =>
  lazymatch type of ST with stk _ _ ?lo ?base =>
  lazymatch type of MU with munch ?W ?ma _ =>
  lazymatch type of MUL with munch ?WL ?m0 _ =>
  let Rf := mkR_setf R rq in
  let J := constr:(forall (wq tq : word) (m2 : word -> option byte),
             rw_cells sg m2 Sa csH -> rw_cells sg m2 strm (c0 :: c1 :: c2 :: C4 tq :: rest) ->
             rw_cells sg m2 Pl csL -> rw_cells sg m2 Ph csHi ->
             stk sg m2 lo base -> munch W ma m2 -> wmono sg ma m2 -> mem_inv sg m2 ->
             munch WL m0 m2 -> wmono sg m0 m2 ->
             evt sg Q (MS (Rf wq) F (Z_to_bv 64 skip) fc rv m2 ro)) in
  let JN := fresh "JN" in
  enough J as JN;
  [ | clear HD STRM FRL FRH ST MU WM MI MUL WML; try clear m;
      intros ?wq ?tq ?m HD STRM FRL FRH ST MU WM MI MUL WML; cbv beta ]
  end end end end end end end end.
Ltac til_useA JN :=
  eapply JN;
  [ match goal with H : rw_cells _ _ (b_s _) _ |- _ => exact H end
  | match goal with H : rw_cells _ _ (b_strm _) _ |- _ => exact H end
  | match goal with H : rw_cells _ _ (a_P _) _ |- _ => exact H end
  | match goal with H : rw_cells _ _ (a_P _ + 496)%Z _ |- _ => exact H end
  | match goal with H : stk _ _ _ _ |- _ => exact H end
  | match goal with H : munch _ (a_m0 _) _ |- _ => exact H end
  | match goal with H : wmono _ (a_m0 _) _ |- _ => exact H end
  | match goal with H : mem_inv _ _ |- _ => exact H end
  | match goal with H : munch _ _ _ |- munch ?W _ _ => match type of H with munch W _ _ => exact H end end
  | match goal with H : wmono _ ?a _ |- wmono _ ?a _ => exact H end ].

Ltac gbF_close DP MUL WML :=
  lazymatch goal with AOK : act_ok _ _, DM0 : dmem _ _ _ _ _ _ _ |- dmem _ ?cx _ _ _ ?mm _ =>
    eapply (GbKitA.gbF_dmem_close _ _ AOK _ (GbKitA.di_in_imgA_ok AIHI0 DI_A0 eq_refl) _ _ _ _ _ _ _ _ DM0 DP MUL WML);
    [ dvF_cbn; dmodel_cbn; match goal with H : rw_cells _ mm (b_s cx) _ |- _ => exact_cells H end
    | dvF_cbn; dmodel_cbn; match goal with H : rw_cells _ mm (b_strm cx) _ |- _ => exact_cells H end
    | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity ]
  end.
Ltac cut_sideG MUL WML DP :=
  lazymatch goal with
  | |- dmem _ _ _ _ _ _ _ => gbF_close DP MUL WML
  | |- aframe _ _ => match goal with AOK : act_ok _ _, AF : aframe _ _ |- _ => exact (aframe_gb_tr _ _ _ _ AOK AF MUL WML) end
  | |- _ => cut_sideF DP
  end.
(* [comment removed for export] *)
Ltac gbA_exit HK MUL WML DP MD FU n :=
  erewrite (drun_bits' _ _ _ _ _ _ _ n) in MD by first [reflexivity | cbn; lia];
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_eq; [ | eapply (HK _ _ _ _ _ _ _ mm MD) ]; only 1: unify_memF;
    [ | eapply fuel_ok_gbst_bits; [exact FU | cbn; lia] | try cut_sideG MUL WML DP .. ];
    [ dvF_cbn; dmodel_cbn; st_eq | try (cbn [length]; unset_Z; lia) .. ] end.
(* [comment removed for export] *)
Ltac gbA_ret HRET MUL WML DP MD NB n :=
  erewrite (drun_eof' _ _ _ _ _ _ _ n) in MD by first [reflexivity | cbn; lia];
  rewrite MD;
  (eapply evt_eq; [ | eapply (HRET _ _ _ (JK _ _ _ _ _ _ _ _ _ _ _ _ _ _)) ]; only 1: unify_memF; try cut_sideG MUL WML DP; only 1: (dvF_cbn; dmodel_cbn; st_eq)); [exact NB | apply dpost14_ne; dmodel_cbn; cbv; discriminate].
