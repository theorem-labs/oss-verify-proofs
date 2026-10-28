(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem RzCPS. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Monad Stdio Prog BnBase BnModel BnTree ApBase ApState ApLogic ApInv ApErr ApParse ApPrim.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface RT_client_kit D_defs D_cs I_lkit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnP Require Import BnKit BnKit2.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnW Require Import BnTac BnMem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnAsan Require Import AsKit AsLoop.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import R_unwind_chain.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import RT_iface2 LibKitA ARun BnHeapA BnRepDefs BnRepA ImplA ImplAX BnIfaceA AsStruct RtCallA UnwindA EdgesA UnwindX.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtFrameA Require Import AFrameKit AFrameCall AFrameTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require Import ApCells.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require W_get_object W_get_object_walk W_check_tlen.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApUTacB.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import I_strcpyA ApATac ApATacX ApBImg ApWalkTac ApRepDefs ApRep ApIface ApFrame W_akit W_get_objectA W_check_tlenA
     W_item_d2i_stmtA W_item_d2i_imgA W_c2i_stmtA W_frkitA Fr_asn1_check_tlen Fr_asn1_d2i_ex_primitive W_item_d2i_exA W_item_d2i_tailA W_item_d2i_octA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require W_get_object_walkA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac step := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.
Local Ltac zstep := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
Local Ltac alia := unfold BnHeapA.ACEIL, SEGTOP_A, SHHI, SHLO, STACK_WIN, USTACK_TOP in *; lia.
(* [comment removed for export] *)
Local Ltac plia := unfold BnHeapA.ACEIL, SEGTOP_A, SHHI, SHLO, STACK_WIN, USTACK_TOP, RT_STACK in *; cbn [ar_FR ar_RT ar_SP0 ar_PMc push amb] in *; lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Ltac zc H := rewrite ?bv_lts_zero_r, ?bv_lts_zero_l in H; unfold bv_eqb, bv_ltu, bv_lts, bv_leu in H; fold_lit_ux_in H; try zsimp_in H; zify_bool H.




Local Definition hidden (P : Prop) : Prop := P.
Local Ltac hide H := lazymatch type of H with ?T => change T with (hidden T) in H end.
Local Ltac freeze H := lazymatch type of H with ?T => change T with (frozen T) in H end.
Notation tlc_in := CtRepP.W_check_tlen.tlc_in.


Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation FR := (@ar_FR AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

(* [comment removed for export] *)
Definition exprim_specA : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (st : ap_st bptr) (OW LB : list block) (E : ap_env) (bo : Z * Z)
         (lo : Z) (K : list block) (ras : list Z) (D : Z) (d : list Z) (op totlen utype e OPP PV TLC : Z) (j31 : list byte),
    let g := get_object d op totlen in
    ap_preA Σ st m OW LB E bo sp lo EXPRIM_STACK_A (EXPRIM_COST_A (go_len g)) EXPRIM_FRAMES_A -> tp = wz TP_A ->
    uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx ADEP_ENTRY (bv_unsigned ra :: ras) -> ras <> nil ->   (* [comment removed for export] *)
    d2i_entryA e utype ->
    (forall b, In b K -> In b OW) -> (forall b, In b K -> ~ In (blk_id b) (es_ids st ++ env_ids E)) ->
    payload_okA m LB D d -> 0 <= op -> 0 < totlen -> op + totlen <= zlength d ->
    go_err g = None -> go_tag g = utype -> go_cls g = 0 -> Z.land (go_ret g) 32 = 0 ->
    cellA_in LB OPP 8 -> cellA_in LB PV 8 -> cellA_in LB TLC 32 -> OPP mod 8 = 0 -> PV mod 8 = 0 -> TLC mod 8 = 0 ->
    (OPP + 8 <= PV \/ PV + 8 <= OPP) -> (OPP + 8 <= TLC \/ TLC + 32 <= OPP) -> (PV + 8 <= TLC \/ TLC + 32 <= PV) ->
    (OPP + 8 <= D \/ D + zlength d <= OPP) -> (PV + 8 <= D \/ D + zlength d <= PV) -> (TLC + 32 <= D \/ D + zlength d <= TLC) ->
    rw_cells ctasegs m OPP [C8 (wz (D + op))] -> rw_cells ctasegs m PV [C8 (wz 0)] -> rw_cells ctasegs m TLC (tlc_in j31) ->
    a0 = wz PV -> a1 = wz OPP -> a2 = wz totlen -> a3 = wz (item_ofA utype) -> a4 = wz (-1) -> a5 = wz 0 -> a6 = wz 0 -> a7 = wz TLC ->
    implAp (d2i_prim d op totlen utype st) Σ
           (exprim_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB E bo lo m K OPP PV TLC utype (go_len g))
           (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz ADEP_ENTRY) fc None m (seg_rom ctasegs)).

Section Walk.
  Hypothesis STRCPY : strcpy_icontract RT.
  Hypothesis HCT : forall AR' : ARun, strcpy_icontract (@ar_RT AR') -> @check_tlen_specA AR' UK.
  Hypothesis HTF : forall AR' : ARun, @type_free_null_specA AR'.

  Theorem exprim_walkA : exprim_specA.
  Proof.
    intros until j31. cbv zeta.
    intros PRE0 -> UW CTX NE ENT KOW KIDS PAY OP0 TL0 OPT EG ETAG ECLS ERET COPP CPV CTLC ALO ALV ALT DOV DOT DVT DOD DVD DTD HOPP HPV HTLC -> -> -> -> -> -> -> ->.
    pose proof PRE0 as (HEAP & AS & IDS & DC & ST & CEIL & LOSP & TOP & AL16 & MI & CRED & FRM).
    assert (EF : EXPRIM_FRAMES_A = 7 /\ GETOBJ_ERR_COST_A = 13 /\ 66320 <= CHECK_TLEN_STACK_A).
    { split; [reflexivity|]. split; [reflexivity|]. unfold CHECK_TLEN_STACK_A, ACTL_FRAME, GETOBJ_STACK_A, ERR_SET_ERROR_STACK, ERR_VSET_ERROR_STACK, RT_STACK; clear; lia. }
    pose proof (get_object_bounds d op totlen ltac:(destruct PAY as (_ & DF & _); eapply Forall_impl; [| exact DF]; cbv beta; intros; lia) TL0) as GB.
    cbv zeta in GB. rewrite EG in GB. destruct GB as (GB1 & GB2 & GB3).
    pose proof (mcost_nonneg (go_len (get_object d op totlen)) ltac:(clear - GB2; lia)) as MC0.
    unfold MallocRep.wz. intros X Φ Dl SAFE LINK.
    eapply (adep_pro_cps _) with (lo := lo) (OW := OW) (LB := LB);
      [exact HEAP| exact ST| exact CEIL| unfold EXPRIM_STACK_A, ADEP_FRAME, RT_STACK in *; clear - LOSP EF; lia| exact TOP| exact AL16| exact MI| reflexivity
      | cbn [length]; clear - FRM EF; lia| unfold EXPRIM_COST_A in CRED; clear - CRED EF MC0; lia|].
    intros Σ1 m3 f spa g junk gj ra' t0' t1' t2' a7' t3' t4' t5' t6' F' fc' j0 j8 j16 j24 j32 j48 j64 j72 j80 j96 j104 j112 j120 j128 j136 j144 jf24 jf32 jf40 jf64 jf65 jf80 jf112 jst
           HEAP3 FRESH GEO CR1 EL1 ST3 MI3 AGF FRL FRH FRF FRS SPA32 SPAL SPAH GSZ SAVJ.
    eapply (@implAp_elim (push AR f 2) _ (d2i_prim d op totlen utype st)); [| exact SAFE| exact LINK| exact EL1].
    eapply (exprim_frontA STRCPY HCT);
      [exact PRE0| exact ENT| exact UW| exact CTX| exact KOW| exact KIDS| exact PAY| exact OP0| exact TL0| exact OPT| exact EG| exact ETAG| exact ECLS| exact ERET| exact COPP| exact CPV| exact CTLC
      | exact ALO| exact ALV| exact ALT| exact DOT| exact DVT| exact DTD| exact HOPP| exact HPV| exact HTLC| exact HEAP3| exact FRESH| exact GEO| exact CR1| exact ST3| exact MI3| exact AGF
      | exact SPA32| exact SPAL| exact SPAH| exact GSZ| | | exact FRL| exact FRH| exact FRF| exact FRS].
    - intros qc qfc Σ4 OW4 m9 jt4 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 F4 fc4 UI AF.
      (* [comment removed for export] *)
      exfalso. destruct ENT as [_ EU]. rewrite EU in UI. unfold V_ASN1_OCTET_STRING, V_ASN1_INTEGER, V_ASN1_ENUMERATED in UI. clear - UI. lia.
    - intros qc qfc Σ4 OW4 m9 jt4 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 F4 fc4 UO AF.
      eapply exprim_oct_armA;
        [exact PRE0| exact ENT| exact UW| exact CTX| exact PAY| exact OP0| exact TL0| exact OPT| exact EG| exact ETAG| exact ECLS| exact ERET| exact COPP| exact CPV| exact CTLC
        | exact ALO| exact ALV| exact ALT| exact DOV| exact DVD| exact FRESH| exact GEO| exact SPA32| exact SPAL| exact SPAH| exact GSZ| exact SAVJ| exact UO| exact AF].
  Qed.

  (* [comment removed for export] *)
  Goal True. idtac "Assumptions of exprim_walkA:". Print Assumptions exprim_walkA. exact I. Qed.
End Walk.
End WithRT.
