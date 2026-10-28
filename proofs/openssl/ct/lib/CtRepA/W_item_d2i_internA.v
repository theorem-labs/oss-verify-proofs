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
     W_item_d2i_stmtA W_item_d2i_imgA W_c2i_stmtA W_frkitA Fr_asn1_check_tlen Fr_asn1_d2i_ex_primitive W_item_d2i_exA W_item_d2i_tailA W_item_d2i_exprimA.
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



Definition INTERN_A : Z := 0x240274.
Definition EMBED_A : Z := 0x2405d4.
Definition ITEM_EX_FREE_A : Z := 0x24412c.
Definition INTERN_RA : Z := 0x2402b4.        (* [comment removed for export] *)
Definition ITEM_EX_FREE_RA : Z := 0x2402c8.
(* [comment removed for export] *)
Definition INTERN_STACK_A : Z := 64 + EXPRIM_STACK_A.
(* [comment removed for export] *)
Definition ITEM_EX_FREE_STACK_A : Z := 176.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition item_ex_free_null_specA : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo PVAL IT w PB PBn : Z) (shb : shb_cells ctasegs A_GOT_SHB A_SHB_CELL m -> Prop) (POST : machine_state -> Prop),
    stk ctasegs m lo (bv_unsigned sp) -> SHHI <= lo -> lo <= bv_unsigned sp - ITEM_EX_FREE_STACK_A -> bv_unsigned sp + 16 <= USTACK_TOP -> mem_inv ctasegs m ->
    shb_cells ctasegs A_GOT_SHB A_SHB_CELL m ->
    acc ctasegs m PB PBn -> PB <= PVAL -> PVAL + 8 <= PB + PBn -> 0 < PB -> PB + PBn <= lo -> (PB + PBn <= SHLO \/ SHHI <= PB) -> PVAL mod 8 = 0 ->
    rw_cells ctasegs m PVAL [C8 (Z_to_bv 64 0)] ->
    item_cellsA m IT w -> 0 < IT -> IT + 56 <= SHLO -> IT mod 8 = 0 -> bv_unsigned (sx32 (Z_to_bv 64 w)) <> 1 ->
    a0 = wz PVAL -> a1 = wz IT ->
    (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
       munch [(bv_unsigned sp - ITEM_EX_FREE_STACK_A, bv_unsigned sp)]%Z m m' -> wmono ctasegs m m' -> mem_inv ctasegs m' -> stk ctasegs m' lo (bv_unsigned sp) ->
       evt ctasegs POST
         (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom ctasegs))) ->
    evt ctasegs POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz ITEM_EX_FREE_A) fc None m (seg_rom ctasegs)).

Lemma item_ofA_al8 : forall e u, d2i_entryA e u -> item_ofA u mod 8 = 0.
Proof. intros e u [_ ->]; reflexivity. Qed.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Notation E_intern_embed := (E_asn1_item_ex_d2i_intern_242bd4 : uk_call 0x240274 0x2402b4 0x2405d4).  (* [comment removed for export] *)
Local Notation E_embed_tail := (E_asn1_item_embed_d2i_24340c : uk_tail 0x2405d4 0x24187c).                  (* [comment removed for export] *)


Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation FR := (@ar_FR AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

(* [comment removed for export] *)
Definition intern_specA : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (st : ap_st bptr) (OW LB : list block) (E : ap_env) (bo : Z * Z)
         (lo : Z) (K : list block) (ras : list Z) (D : Z) (d : list Z) (op totlen utype e OPP PV TLC : Z) (j31 : list byte),
    let g := get_object d op totlen in
    ap_preA Σ st m OW LB E bo sp lo INTERN_STACK_A (EXPRIM_COST_A (go_len g)) EXPRIM_FRAMES_A -> tp = wz TP_A ->
    uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx INTERN_A (bv_unsigned ra :: ras) -> ras <> nil ->   (* [comment removed for export] *)
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
               F (wz INTERN_A) fc None m (seg_rom ctasegs)).

Section Walk.
  Hypothesis HEX : exprim_specA.
  Hypothesis HEF : item_ex_free_null_specA.

  Theorem intern_walkA : intern_specA.
  Proof.
    intros until j31. cbv zeta.
    intros PRE0 -> UW CTX NE ENT KOW KIDS PAY OP0 TL0 OPT EG ETAG ECLS ERET COPP CPV CTLC ALO ALV ALT DOV DOT DVT DOD DVD DTD HOPP HPV HTLC -> -> -> -> -> -> -> ->.
    pose proof PRE0 as (HEAP & AS & IDS & DC & ST & CEIL & LOSP & TOP & AL16 & MI & CRED & FRM).
    pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, STACK_WIN, SHHI, USTACK_TOP in C1, C2, C3.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    assert (LO0 : 0 <= lo) by (clear - ST; destruct ST as [H _]; exact H).
    assert (ESS : 66320 <= CHECK_TLEN_STACK_A) by (unfold CHECK_TLEN_STACK_A, ACTL_FRAME, GETOBJ_STACK_A, ERR_SET_ERROR_STACK, ERR_VSET_ERROR_STACK, RT_STACK; clear; lia).
    unfold INTERN_STACK_A, EXPRIM_STACK_A, ADEP_FRAME in LOSP.
    destruct CPV as (bv & Hbv & BV1 & BV2). destruct COPP as (bq & Hbq & BQ1 & BQ2). destruct CTLC as (bt & Hbt & BT1 & BT2).
    pose proof (AH_range_gen _ _ _ _ bv HEAP (in_or_app _ _ _ (or_intror Hbv))) as (BV3 & _ & _ & BV4 & BV5).
    pose proof (AH_range_gen _ _ _ _ bq HEAP (in_or_app _ _ _ (or_intror Hbq))) as (BQ3 & _ & _ & BQ4 & BQ5).
    pose proof (AH_range_gen _ _ _ _ bt HEAP (in_or_app _ _ _ (or_intror Hbt))) as (BT3 & _ & _ & BT4 & BT5).
    pose proof (AH_offsh _ _ _ _ bv HEAP (in_or_app _ _ _ (or_intror Hbv))) as ROV. unfold SHLO, SHHI in ROV.
    destruct (@item_cellsA_of AR _ _ _ _ e utype HEAP ENT) as (IT0 & IT8 & IT8L & IT16 & IT32 & ACCIT). pose proof (item_ofA_range utype) as ITR.
    pose proof (utype_casesA _ _ ENT) as UT. pose proof PAY as (_ & DF & D0 & D63 & D26 & _).
    assert (EPV : bv_unsigned (Z_to_bv 64 PV) = PV) by (apply unsigned_lit; clear - BV1 BV2 BV3 BV4 C3; unfold BnHeapA.ACEIL in *; lia).
    unfold INTERN_A, MallocRep.wz in *. unfold CtRepP.W_check_tlen.tlc_in in HTLC.
    pose proof (proj2 (AH_acc _ _ _ _ bv HEAP (in_or_app _ _ _ (or_intror Hbv)))) as ACCV.
    assert (OFFW : offshW [(bv_unsigned sp - 304, bv_unsigned sp)]%Z) by (cbn [offshW]; unfold SHLO, SHHI; clear - C2 CEIL LOSP ESS; unfold BnHeapA.ACEIL in *; lia).
    pose proof (munch_refl [(bv_unsigned sp - 304, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctasegs m) as WM.
    hide BV5. hide BQ5. hide BT5. hide DOV. hide DOT. hide DVT. hide DOD. hide DVD. hide DTD. hide UT. hide ROV.
    freeze HOPP. freeze HTLC.
    assert (ITAL8 : al8 (item_ofA utype)) by (clear; unfold al8, item_ofA, ITEM_OCTET_A, ITEM_INTEGER_A, ITEM_ENUM_A; destruct (utype =? _); [reflexivity|]; destruct (utype =? _); reflexivity). (* [comment removed for export] *)
    apply implAp_from_evt.
    (* [comment removed for export] *)
    carve_frame 64%nat ST. do 7 step.
    step. if_cases KP; zc KP; [exfalso; rewrite ?EPV in KP; clear - KP BV3 BV1; lia|]. clear KP.
    step. step. if_cases KI; zc KI; [exfalso; rewrite ?unsigned_lit in KI by (clear - ITR; lia); clear - KI ITR; lia|]. clear KI.
    step. step. step. step. step. step.
    (* [comment removed for export] *)
    carve_frame 240%nat ST. do 15 step.
    do 9 step. if_cases KP2; zc KP2; [exfalso; rewrite ?EPV in KP2; clear - KP2 BV3 BV1; lia|]. clear KP2.
    step. step. if_cases KI2; zc KI2; [exfalso; rewrite ?unsigned_lit in KI2 by (clear - ITR; lia); clear - KI2 ITR; lia|]. clear KI2.
    step. step. if_cases KL; zc KL.
    { exfalso. rewrite (proj2 (Z.ltb_lt 0 totlen)) in KL by (clear - TL0; lia). rewrite (proj2 (Z.ltb_lt totlen _)) in KL by (clear - TL0 OPT D26 OP0; lia). discriminate KL. }
    try clear KL. try clear KL0. try clear KL1.
    (* [comment removed for export] *)
    step. step.
    step. step. step. if_true.
    (* [comment removed for export] *)
    step. step. step. if_true.
    (* [comment removed for export] *)
    step.
    step. step. step. if_false.
    step. step. step. zstep.
    match goal with H : mem_inv ctasegs ?mx |- evt _ _ (MS _ _ _ _ _ ?mx _) => pose proof (jt_embed_d2iA mx H) as JT end.
    step. clear JT. rewrite (sx32_small 1891992) by (clear; lia). step. setreg 12 (Z_to_bv 64 0x240890) ltac:(reflexivity). step. step. step.
    (* [comment removed for export] *)
    step. step. if_true.
    do 7 step. do 13 step. step. release_frame FR0 ST (bv_unsigned sp + -64). step.
    name_mem m1.
    match goal with H : munch _ m m1 |- _ => rename H into MU1 end. match goal with H : wmono ctasegs m m1 |- _ => rename H into WM1 end.
    match goal with H : mem_inv ctasegs m1 |- _ => rename H into MI1 end.
    apply evt_done. fold ADEP_ENTRY.
    (* [comment removed for export] *)
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; clear - SPR CEIL LOSP LO0 ESS; lia).
    pose proof (agree_on_of_munch_nw _ _ _ MU1) as AG1.
    assert (HEAP1 : AHEAP Σ OW LB m1).
    { eapply (AH_frame Σ OW LB m m1 _ HEAP MU1 WM1). constructor; [left; cbn [fst snd]; clear - CEIL LOSP TOP ESS; unfold USTACK_TOP in *; lia| constructor]. }
    assert (AGL1 : agree_on (lib_addr OW) m m1).
    { eapply agree_on_mono; [exact AG1|]. intros a [HS|(b & Hb & Hr)]; cbn [outside fst snd].
      - pose proof (LIBW_S_A a HS) as HA. unfold LIBW_A in HA. cbn [rin_ivs fst snd] in HA. clear - HA C1 CEIL LOSP ESS. unfold BnHeapA.ACEIL in *. lia.
      - pose proof (AH_range_gen _ _ _ _ b HEAP (in_or_app _ _ _ (or_introl Hb))) as (_ & _ & _ & R3 & _). clear - Hr R3 CEIL LOSP ESS. lia. }
    assert (AGC1 : agree_on (aclient_addr LB (bv_unsigned sp)) m m1).
    { eapply agree_on_mono; [exact AG1|]. intros a [H1|[H1|(b & Hb & Hr)]]; cbn [outside fst snd].
      - clear - H1. lia.
      - assert (a < 12365824) by (destruct H1 as [(l & h & Hin & Hlh) _]; unfold CLIENT_STATIC in Hin; cbn [In] in Hin; clear - Hin Hlh; destruct Hin as [E0|[E0|[E0|[]]]]; injection E0 as <- <-; lia).
        clear - H C1 CEIL LOSP ESS. unfold BnHeapA.ACEIL in *. lia.
      - pose proof (AH_range_gen _ _ _ _ b HEAP (in_or_app _ _ _ (or_intror Hb))) as (_ & _ & _ & R3 & _). clear - Hr R3 CEIL LOSP ESS. lia. }
    pose proof AS as (_ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & OD)).
    assert (PRE1 : ap_preA Σ st m1 OW LB E bo (Z_to_bv 64 (bv_unsigned sp + -64)) lo EXPRIM_STACK_A (EXPRIM_COST_A (go_len (get_object d op totlen))) EXPRIM_FRAMES_A).
    { unfold ap_preA. rewrite ESP. split; [exact HEAP1|]. split; [exact (ap_state_agree _ _ _ _ _ _ AS AGL1)|]. split; [exact IDS|]. split; [exact (data_cells_agree _ _ _ _ DC AGL1 OD)|].
      split; [exact ST|]. split; [exact CEIL|]. split; [unfold EXPRIM_STACK_A, ADEP_FRAME; clear - LOSP; lia|]. split; [clear - TOP; lia|].
      split; [clear - AL16; unfold al16 in *; Z.div_mod_to_equations; lia|]. split; [exact MI1|]. split; [exact CRED| exact FRM]. }
    unfold frozen in HOPP, HTLC.
    apply (rw_cells_agree _ _ _ _ _ AG1) in HOPP; [| intros a Ha; cbn in Ha; cbn [outside fst snd]; clear - Ha BQ1 BQ2 BQ4 CEIL LOSP ESS; lia].
    apply (rw_cells_agree _ _ _ _ _ AG1) in HTLC; [| intros a Ha; cbn in Ha; cbn [outside fst snd]; clear - Ha BT1 BT2 BT4 CEIL LOSP ESS; lia].
    assert (PAY1 : payload_okA m1 LB D d).
    { eapply payload_okA_agreeA; [exact PAY|]. eapply agree_on_mono; [exact AGC1|]. intros a Ha. right; right. exact Ha. }
    unfold hidden in DOV, DOT, DVT, DOD, DVD, DTD.
    eapply implAp_post.
    { eapply HEX with (K := K) (e := e) (j31 := j31); [exact PRE1| reflexivity
        | rewrite ESP; uw_call_mu_tac m 64 UW MU1 FR; [intros a Ha; cbn [outside fst snd]; lia | clear; lia | uchk_open; clear - AL16; Z.div_mod_to_equations; lia | clear - TOP; unfold USTACK_TOP in *; lia]
        | rewrite unsigned_lit by (clear; lia); exact (uk_ctx_tail _ _ _ E_embed_tail (uk_ctx_call _ _ _ _ E_intern_embed CTX))
        | apply cons_ne| exact ENT| exact KOW| exact KIDS| exact PAY1| exact OP0| exact TL0| exact OPT| exact EG| exact ETAG| exact ECLS| exact ERET
        | exists bq; split; [exact Hbq| split; [exact BQ1| exact BQ2]]| exists bv; split; [exact Hbv| split; [exact BV1| exact BV2]]| exists bt; split; [exact Hbt| split; [exact BT1| exact BT2]]
        | exact ALO| exact ALV| exact ALT| exact DOV| exact DOT| exact DVT| exact DOD| exact DVD| exact DTD| exact HOPP| exact HPV| exact HTLC
        | reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity]. }
    cbv beta. intros [res st'] Σ' ms' PO. unfold exprim_postA in PO. cbn [fst snd] in PO. unfold MallocRep.wz in PO. rewrite ?ESP in PO.
    destruct PO as (u0 & u1 & u2 & a0' & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & F' & fc' & m' & OW' & ov & -> & PRE' & AXP' & CRED' & KEPT' & HOPP' & RES').
    unfold INTERN_RA. rewrite (ret_pc_even 0x2402b4) by (clear; lia).
    pose proof PRE' as (HEAP' & AS' & IDS' & DC' & ST' & _ & _ & _ & _ & MI' & _ & _).
    (* [comment removed for export] *)
    apply (rw_cells_agree _ _ _ _ _ AXP') in FR.
    2:{ intros a Ha. cbn [cells_size csize Nat.add] in Ha. rewrite ?Nat2Z.inj_add in Ha. cbn in Ha. split; [| left; clear - Ha TOP; unfold USTACK_TOP in *; lia].
        unfold LIBW_A. cbn [rin_ivs fst snd app]. clear - Ha BQ2 BQ4 BV2 BV4 BT2 BT4 C1 CEIL LOSP ESS. unfold BnHeapA.ACEIL in *. lia. }
    rewrite ESP in ST'. clear ST MI1 SHB1_ SHB2_.
    assert (AGF : agree_on (aclient_addr (OW ++ LB) (bv_unsigned sp)) m m1).
    { intros a Hr Ha. destruct Ha as [H1|[H1|(b & Hb & Hrg)]]; [apply (AGC1 a Hr); left; exact H1| apply (AGC1 a Hr); right; left; exact H1|].
      apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [apply (AGL1 a Hr); right; exists b; split; [exact Hb| exact Hrg]| apply (AGC1 a Hr); right; right; exists b; split; [exact Hb| exact Hrg]]. }
    assert (AXP1 : ax_pres LB (bv_unsigned sp) ([(OPP, OPP + 8); (PV, PV + 8); (TLC, TLC + 32)] ++ LIBW_A) m m').
    { eapply ax_pres_trans; [| eapply ax_pres_lower; [exact AXP'| clear; lia]]. unfold ax_pres. eapply agree_on_mono; [exact AGC1|]. intros a [_ Ha]. exact Ha. }
    assert (KEPT1 : blocks_kept K st' OW' m m') by (eapply (blocks_kept_pre K st' OW OW' LB); [exact KOW| exact AGF| exact KEPT']).
    clear AG1 AGL1 AGC1 MU1 WM1 HEAP1 PRE1 PAY1 HOPP HTLC HPV.
    pose proof (munch_refl [(bv_unsigned sp - 304, bv_unsigned sp)]%Z m') as MU. pose proof (wmono_refl ctasegs m') as WM.
    freeze HOPP'.
    apply implAp_from_evt. step. destruct res as [x|].
    - (* [comment removed for export] *)
      destruct RES' as (-> & A & ty & HPV' & SR & TY & IDX). freeze HPV'.
      step. if_true. step. do 5 step. step. release_frame FR ST' (bv_unsigned sp). step.
      apply evt_done. apply implAp_ret. unfold exprim_postA. cbn [fst snd]. unfold frozen in HOPP', HPV'.
      do 17 eexists. exists m', OW', ov. split; [reflexivity|].
      split.
      { unfold ap_preA. split; [exact HEAP'|]. split; [exact AS'|]. split; [exact IDS'|]. split; [exact DC'|]. split; [exact ST'|]. split; [exact CEIL|]. split; [clear - LOSP ESS; lia|].
        split; [exact TOP|]. split; [exact AL16|]. split; [exact MI'|]. pose proof PRE' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CR0 & _).
        split; [clear - CR0; lia| clear - FRM; unfold EXPRIM_FRAMES_A in *; lia]. }
      split; [exact AXP1|]. split; [exact CRED'|]. split; [exact KEPT1|]. split; [exact HOPP'|].
      split; [reflexivity|]. exists A, ty. split; [exact HPV'|]. split; [exact SR|]. split; [exact TY| exact IDX].
    - (* [comment removed for export] *)
      destruct RES' as (-> & HPV'). freeze HPV'.
      step. if_false. step. step. step.
      unfold frozen in HPV'.
      destruct (@item_cellsA_of AR _ _ _ _ e utype HEAP' ENT) as (JT0 & JT8 & JT8L & JT16 & JT32 & ACCIT').
      unfold ITEM_EX_FREE_A in HEF.
      eapply (HEF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo PV (item_ofA utype) utype (blk_addr bv) (blk_size bv) (fun _ => True)); rewrite ?ESP;
        [exact ST'| unfold SHHI; clear - C2 CEIL; unfold BnHeapA.ACEIL in *; lia| unfold ITEM_EX_FREE_STACK_A; clear - LOSP ESS; lia| clear - TOP; unfold USTACK_TOP in *; lia| exact MI'
        | exact (AH_shbA _ _ _ _ HEAP')
        | exact (proj2 (AH_acc _ _ _ _ bv HEAP' (in_or_app _ _ _ (or_intror Hbv))))| exact BV1| exact BV2| exact BV3| clear - BV4 CEIL; lia
        | pose proof ROV as X; unfold hidden in X; unfold SHLO, SHHI; exact X| exact ALV| exact HPV'
        | split; [exact JT0| split; [exact JT8| split; [exact JT8L| split; [exact JT16| split; [exact JT32| exact ACCIT']]]]]
        | clear - ITR; lia| unfold SHLO; clear - ITR; lia| exact (item_ofA_al8 _ _ ENT)| pose proof UT as X; unfold hidden in X; rewrite (sx32_small utype) by (clear - X; lia); rewrite unsigned_lit by (clear - X; lia); clear - X; lia
        | reflexivity| reflexivity|].
      intros t0'' t1'' t2'' b0 b1 b2 b3 b4 b5 b6 b7 t3'' t4'' t5'' t6'' m'' MU'' WM'' MI'' ST''. rewrite ?ESP in MU'', ST''. unfold ITEM_EX_FREE_STACK_A in MU''.
      unfold ITEM_EX_FREE_RA. rewrite (ret_pc_even 0x2402c8) by (clear; lia).
      (* [comment removed for export] *)
      pose proof (agree_on_of_munch_nw _ _ _ MU'') as AG''. unfold ITEM_EX_FREE_STACK_A in AG''.
      apply (rw_cells_agree _ _ _ _ _ AG'') in FR; [| intros a Ha; cbn in Ha; cbn [outside fst snd]; clear - Ha; lia].
      unfold frozen in HOPP'.
      apply (rw_cells_agree _ _ _ _ _ AG'') in HOPP'; [| intros a Ha; cbn in Ha; cbn [outside fst snd]; clear - Ha BQ1 BQ2 BQ4 CEIL LOSP ESS; lia].
      apply (rw_cells_agree _ _ _ _ _ AG'') in HPV'; [| intros a Ha; cbn in Ha; cbn [outside fst snd]; clear - Ha BV1 BV2 BV4 CEIL LOSP ESS; lia].
      assert (HEAP'' : AHEAP Σ' OW' LB m'').
      { eapply (AH_frame Σ' OW' LB m' m'' _ HEAP' MU'' WM''). constructor; [left; cbn [fst snd]; clear - CEIL LOSP TOP ESS; unfold USTACK_TOP in *; lia| constructor]. }
      assert (AGL'' : agree_on (lib_addr OW') m' m'').
      { eapply agree_on_mono; [exact AG''|]. intros a [HS|(b & Hb & Hr)]; cbn [outside fst snd].
        - pose proof (LIBW_S_A a HS) as HA. unfold LIBW_A in HA. cbn [rin_ivs fst snd] in HA. clear - HA C1 CEIL LOSP ESS. unfold BnHeapA.ACEIL in *. lia.
        - pose proof (AH_range_gen _ _ _ _ b HEAP' (in_or_app _ _ _ (or_introl Hb))) as (_ & _ & _ & R3 & _). clear - Hr R3 CEIL LOSP ESS. lia. }
      pose proof AS' as (_ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & OD')).
      clear MU WM. pose proof (munch_refl [(bv_unsigned sp - 304, bv_unsigned sp)]%Z m'') as MU. pose proof (wmono_refl ctasegs m'') as WM.
      freeze HOPP'. freeze HPV'.
      step. step. do 5 step. step. release_frame FR ST'' (bv_unsigned sp). step.
      apply evt_done. apply implAp_ret. unfold exprim_postA. cbn [fst snd]. unfold frozen in HOPP', HPV'.
      do 17 eexists. exists m'', OW', ov. split; [reflexivity|].
      split.
      { unfold ap_preA. split; [exact HEAP''|]. split; [exact (ap_state_agree _ _ _ _ _ _ AS' AGL'')|]. split; [exact IDS'|]. split; [exact (data_cells_agree _ _ _ _ DC' AGL'' OD')|].
        split; [exact ST''|]. split; [exact CEIL|]. split; [clear - LOSP ESS; lia|].
        split; [exact TOP|]. split; [exact AL16|]. split; [exact MI''|]. pose proof PRE' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CR0 & _).
        split; [clear - CR0; lia| clear - FRM; unfold EXPRIM_FRAMES_A in *; lia]. }
      split.
      { eapply ax_pres_trans; [exact AXP1|]. unfold ax_pres. eapply agree_on_mono; [exact AG''|]. intros a [_ Ha]; cbn [outside fst snd]. destruct Ha as [H1|[H1|(b & Hb & Hr)]].
        - clear - H1. lia.
        - assert (a < 12365824) by (destruct H1 as [(l & h & Hin & Hlh) _]; unfold CLIENT_STATIC in Hin; cbn [In] in Hin; clear - Hin Hlh; destruct Hin as [E0|[E0|[E0|[]]]]; injection E0 as <- <-; lia).
          clear - H C1 CEIL LOSP ESS. unfold BnHeapA.ACEIL in *. lia.
        - pose proof (AH_range_gen _ _ _ _ b HEAP (in_or_app _ _ _ (or_intror Hb))) as (_ & _ & _ & R3 & _). clear - Hr R3 CEIL LOSP ESS. lia. }
      split; [exact CRED'|]. split; [exact (blocks_kept_lib _ _ _ _ _ _ KEPT1 AGL'')|]. split; [exact HOPP'|].
      split; [reflexivity| exact HPV'].
  Qed.
End Walk.
End WithRT.
