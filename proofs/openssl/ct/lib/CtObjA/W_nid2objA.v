(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac ZBridge RzCPS ITree Arr. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Malloc Prog Prelim BnBase BnModel BnTree ApBase ApState ApObjTab ApObj.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface RT_client_kit D_defs D_cs I_lkit GDesc.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnW Require Import BnTac BnMem BnTacX.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnP Require Import BnKit BnKit2.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnAsan Require Import AsKit AsLoop.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import RT_iface2 LibKitA ARun BnHeapA ImplA ImplAX BnIfaceA AsStruct RtCallA UnwindA AsStruct2 AsByte.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtFrameA Require Import AFrameKit AFrameCall AFrameTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require Import ApCells.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require ApObjRep.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApRepDefs ApRep ApIface ApFrame ApObjRep Fr_OBJ_nid2obj.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtObjA Require Import ObjLookupStmtA ObjTabA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApUTacB.
Ltac stepA := step. Ltac step := ub; stepA. Ltac zstepA := zstep. Ltac zstep := ub; zstepA.
Import ListNotations.
Open Scope Z_scope.

Ltac cell_of_bytes bs ::=
  lazymatch bs with
  | le8 ?v => constr:(C8 v)
  | le4 ?v => constr:(C4 v)
  | le2 ?v => constr:(C2 v)
  | [?b] => constr:(C1 b)
  | le1 (zxb ?b) => constr:(C1 b)
  | le1 (Z_to_bv 64 ?z) => constr:(C1 (Z_to_bv 8 z))
  | Z_to_le_bytes 8 ?z => constr:(C8 (Z_to_bv 64 z))
  | Z_to_le_bytes 4 ?z => constr:(C4 (Z_to_bv 64 z))
  | Z_to_le_bytes 1 ?z => constr:(C1 (Z_to_bv 8 z))
  end.

Section WithRT.
Context {AR : ARun}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation FR := (@ar_FR AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

Theorem OBJ_nid2obj_walkA : OBJ_nid2obj_stmtA.
Proof.
  unfold OBJ_nid2obj_stmtA. intros until lnlen. intros HEAP ST CEIL LO TOP AL16 MI TP FLEN CRED NID SOK ->.
  unfold N2O_STACK_A, RT_STACK, OBJ_NID2OBJ_A in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3.
  unfold NUM_NID in NID.
  change (wz OBJ_NID2OBJ_A) with (wz ON2O_ENTRY) || idtac.
  eapply (on2o_pro_cps _) with (lo := lo) (OW := OW) (LB := LB);
    [exact HEAP | exact ST | exact CEIL | unfold ON2O_FRAME, RT_STACK; clear - LO; lia | exact TOP | exact AL16 | exact MI | exact TP | exact FLEN | exact CRED |].
  intros Σ1 m3 f spa g jk gjk ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' j0 j8 jf24 jf32 jf48 jf64 jf104 jst
         HEAP3 FRESH GEO CR1 EL1 ST3 MI3 AGF FRL FRH FRF FRS SPA32 SPAL SPAH GSZ SAVJ.
  assert (ESPA : bv_unsigned (Z_to_bv 64 spa) = spa) by (apply unsigned_lit; unfold BnHeapA.ACEIL in *; clear - C1 C3 CEIL LO SPAL SPAH SPR; lia).
  pose proof GEO as (G1 & G2 & G3 & G4 & G5). change (fs_size 2) with 256 in G3, G5. unfold SEGTOP_A in G4. cbn [ar_SP0 push amb] in G3.
  clear FRF FRS.
  (* [comment removed for export] *)
  assert (ACCO : acc ctasegs m3 (A_NID_OBJS_VA + 40 * n) 40).
  { eapply (af_lib_acc_lit RT AF Σ1 m3 A_NIDOBJS_G); [exact (@AH_art (push AR f 2) _ _ _ _ HEAP3)| exact A_NIDOBJS_G_memb| unfold A_NID_OBJS_VA; cbn; clear - NID; lia| unfold A_NID_OBJS_VA; cbn; clear - NID; lia]. }
  assert (OBAL : (A_NID_OBJS_VA + 40 * n) mod 8 = 0) by (unfold A_NID_OBJS_VA; clear - NID; Z.div_mod_to_equations; lia).
  pose proof (static_obj_nid_cellA m3 n lnlen (obj_table_okA_heap (push AR f 2) _ _ _ _ HEAP3 MI3) SOK) as RON.
  unfold A_NID_OBJS_VA in *.
  assert (OFFW : offshW ([] : list (Z * Z))) by exact I.
  pose proof (munch_refl ([] : list (Z * Z)) m3) as MU. pose proof (wmono_refl ctasegs m3) as WM.
  apply cps_from_evt'. unfold ON2O_BODY, MallocRep.wz.
  step. if_cases Ka; zify_cond Ka; [exfalso; rewrite <- ?unsigned_lit_land in Ka; rewrite ?unsigned_lit in Ka by (clear - NID; lia); clear - Ka NID; lia|]. try clear Ka.
  step. step. if_cases Kb; zify_cond Kb; [exfalso; rewrite <- ?unsigned_lit_land in Kb; rewrite ?unsigned_lit in Kb by (clear - NID; lia); clear - Kb NID; lia|]. try clear Kb.
  do 5 step. setreg 10%Z (Z_to_bv 64 (5457152 + 40 * n)) ltac:(rewrite ?unsigned_lit by (clear - NID; lia); f_equal; clear; lia).  (* [comment removed for export] *)
  step. setreg 10%Z (Z_to_bv 64 (5457152 + 40 * n + 16)) ltac:(rewrite ?unsigned_lit by (clear - NID; lia); reflexivity).
  do 2 step. shl_with ACCO OBAL. chk0.
  step. setreg 10%Z (Z_to_bv 64 n) ltac:(rewrite (sx32_small n) by (clear - NID; lia); reflexivity).
  step. if_cases Kc; zify_cond Kc; [exfalso; rewrite <- ?unsigned_lit_land in Kc; rewrite ?unsigned_lit in Kc by (clear - NID; lia); clear - Kc NID; lia|]. try clear Kc.
  do 5 step. setreg 10%Z (Z_to_bv 64 (5457152 + 40 * n)) ltac:(rewrite ?unsigned_lit by (clear - NID; lia); f_equal; clear; lia).
  step. apply evt_done. unfold MallocRep.wz.
  eapply (on2o_epi_cps _) with (lo := lo) (LB := LB) (gj := gjk) (hrest := []);
    [exact HEAP3 | intros b Hb; apply FRESH; apply in_or_app; right; exact Hb | exact ST3 | exact CEIL | clear - LO SPAL; lia | exact TOP | clear - SPAL; lia | clear - SPAH; lia
    | exact GSZ | exact SAVJ | exact MI3 | exact FRL | exact FRH | reflexivity |].
  intros Σ' m' x11' HEAP' CR' EL' ST' MI' AG'.
  apply cps_post. intros c Hc. exists Σ'. split; [| rewrite EL', EL1; reflexivity].
  eapply ASTA_conseq; [exact Hc|]. intros ms0 <-. unfold lk_postA, MallocRep.wz.
  do 14 eexists. exists F', fc', m'. split; [reflexivity|].
  split; [exact MI'|]. split; [exact ST'|].
  split; [| split; [exact HEAP'| split; [rewrite EL', EL1; reflexivity| clear - CR' CR1; lia]]].
  eapply agree_on_trans; [exact AGF|]. eapply agree_on_mono; [exact AG'|]. intros a [Ha|[Ha|Hb]]; [left; clear - Ha SPAH; lia| right; left; exact Ha| right; right; exact Hb].
Qed.

End WithRT.
