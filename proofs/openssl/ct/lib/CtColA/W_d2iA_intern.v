(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem RzCPS. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Monad Stdio Prog LibProg ProgG CtSizes CtWire CtModel BnBase BnModel BnTree ApBase ApState ApLogic ApInv ApErr ApParse ApPrim ApBridge.
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
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import I_strcpyA ApATac ApATacX ApBImg ApWalkTac ApRepDefs ApRep ApIface ApFrame W_akit W_get_objectA W_check_tlenA W_item_d2i_stmtA W_item_d2i_imgA W_c2i_stmtA W_frkitA Fr_asn1_check_tlen Fr_asn1_d2i_ex_primitive W_item_d2i_exA W_item_d2i_tailA W_item_d2i_exprimA W_item_d2i_internA W_item_freeA W_err_newA W_err_set_debugA W_err_vsetA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require W_get_object_walkA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctP Require SctStmt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctA Require Import SctRepA SctStmtA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtColA Require Import ColDefsA ColBudgetA ExoBudgetA W_d2iA_stmt W_ctlA_defs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac step := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.
Local Ltac zstep := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
Local Ltac alia := unfold BnHeapA.ACEIL, SEGTOP_A, SHHI, SHLO, STACK_WIN, USTACK_TOP in *; lia.
Local Ltac plia := unfold BnHeapA.ACEIL, SEGTOP_A, SHHI, SHLO, STACK_WIN, USTACK_TOP, RT_STACK in *; cbn [ar_FR ar_RT ar_SP0 ar_PMc push amb] in *; lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Ltac zc H := rewrite ?bv_lts_zero_r, ?bv_lts_zero_l in H; unfold bv_eqb, bv_ltu, bv_lts, bv_leu in H; fold_lit_ux_in H; try zsimp_in H; zify_bool H.

Local Definition hidden (P : Prop) : Prop := P.
Local Ltac hide H := lazymatch type of H with ?T => change T with (hidden T) in H end.
Local Ltac freeze H := lazymatch type of H with ?T => change T with (frozen T) in H end.

(* [comment removed for export] *)
Definition INTERN_OCT_STACK_A : Z := 64 + EXO_STACK_A.
(* [comment removed for export] *)
Definition INTERN_OCT_COST_A (n : Z) : Z := EXO_COST_A n + GETOBJ_ERR_COST_A.
(* [comment removed for export] *)
Definition A_ASN1_ITEM_EMBED_D2I_FN_A : Z := 0x72bc0.

(* [comment removed for export] *)
Local Notation E_intern_embed := (E_asn1_item_ex_d2i_intern_242bd4 : uk_call 0x240274 0x2402b4 0x2405d4).  (* [comment removed for export] *)
Local Notation E_embed_tail := (E_asn1_item_embed_d2i_24340c : uk_tail 0x2405d4 0x24187c).                  (* [comment removed for export] *)
Local Notation E_embed_new := (E_asn1_item_embed_d2i_243070 : uk_call 0x2405d4 0x240724 0x1fd52c).        (* [comment removed for export] *)
Local Notation E_embed_dbg := (E_asn1_item_embed_d2i_243088 : uk_call 0x2405d4 0x24073c 0x1fd844).        (* [comment removed for export] *)
Local Notation E_embed_err := (E_asn1_item_embed_d2i_243098 : uk_call 0x2405d4 0x24074c 0x1fdab8).        (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma octet_repA_agree : forall m m' L adr os,
  octet_repA m L adr os -> agree_on (fun a => in_block L a) m m' -> octet_repA m' L adr os.
Proof.
  intros m m' L adr os (IN & AL & HC & L1 & L2 & L3 & DAT) AG.
  split; [exact IN|]. split; [exact AL|]. split.
  { eapply rw_cells_agree; [exact AG| exact HC|]. intros a Ha. exists (os_blk os, adr (os_blk os), ASN1_STRING_SIZE). split; [exact IN|].
    cbn [blk_addr blk_size fst snd]. unfold asn1_string_cells in Ha. cbn [cells_size csize Nat.add] in Ha. unfold ASN1_STRING_SIZE. lia. }
  split; [exact L1|]. split; [exact L2|]. split; [exact L3|].
  destruct (os_data os) as [[dp n]|]; [| exact DAT]. destruct DAT as (NE & IN2 & LE & BY). split; [exact NE|]. split; [exact IN2|]. split; [exact LE|].
  eapply bytes_at_agree; [exact AG| exact BY|]. intros a Ha. exists (dp, adr dp, n). split; [exact IN2|]. cbn [blk_addr blk_size fst snd].
  unfold to_bytes in Ha. rewrite length_map in Ha. unfold zlength in L1. lia.
Qed.

Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation FR := (@ar_FR AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

Section Walk.
  Hypothesis STRCPY : strcpy_icontract RT.
  Hypothesis HEXPRIM : exprim_oct_specA EXO_STACK_A EXO_COST_A EXO_FRAMES_A.

  Local Ltac ecu := unfold GETOBJ_ERR_COST_A, ERR_NEW_COST, ERR_SET_DEBUG_COST, ERR_SET_ERROR_COST, ERR_VSET_ERROR_COST, ERR_NEW_FRAMES, ERR_SET_DEBUG_FRAMES,
                           ERR_SET_ERROR_FRAMES, ERR_VSET_ERROR_FRAMES, ERR_NEW_STACK, ERR_SET_DEBUG_STACK, ERR_SET_ERROR_STACK, ERR_VSET_ERROR_STACK, RT_STACK in *.

  Theorem intern_oct_walkA : intern_oct_specA INTERN_OCT_STACK_A INTERN_OCT_COST_A EXO_FRAMES_A.
  Proof.
    intros until j31.
    intros PRE0 -> UW CTX NE KOW KIDS ADR CELLS -> -> -> -> -> -> -> ->.
    pose proof CELLS as (PAY & COPP & CPV & CTLC & ALO & ALV & ALT & DOV & DOT & DVT & DOD & DVD & DTD & HOPP & HPV & HTLC).
    pose proof PRE0 as (HEAP & AS & IDS & DC & ST & CEIL & LOSP & TOP & AL16 & MI & CRED & FRM).
    pose proof (AH_ceil _ _ _ _ HEAP) as (CE1 & CE2 & CE3). unfold SEGTOP_A, STACK_WIN, SHHI, USTACK_TOP in CE1, CE2, CE3.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    assert (LO0 : 0 <= lo) by (clear - ST; destruct ST as [H _]; exact H).
    pose proof exo_budgets as (EXS & EXF & EXC).
    assert (ESS : INTERN_OCT_STACK_A = 67744 /\ EXO_FRAMES_A = 7 /\ GETOBJ_ERR_COST_A = 13) by (unfold INTERN_OCT_STACK_A; rewrite EXS, EXF; repeat split; reflexivity).
    destruct ESS as (ESS & EF7 & EC13). rewrite ESS in LOSP. rewrite EF7 in FRM. unfold INTERN_OCT_COST_A in CRED. rewrite EC13 in CRED.
    pose proof (proj1 (D2I_OCTET_COST_A_bound (zlength d) ltac:(destruct PAY as (_ & _ & _ & _ & D26 & _); unfold zlength in *; clear - D26; lia))) as CST0 || idtac.
    assert (EXC0 : 0 <= EXO_COST_A (zlength d)) by (rewrite EXC; unfold zlength; clear; lia).
    destruct CPV as (bpv & Hbv & BV1 & BV2). destruct COPP as (bq & Hbq & BQ1 & BQ2). destruct CTLC as (bt & Hbt & BT1 & BT2).
    pose proof (AH_range_gen _ _ _ _ bpv HEAP (in_or_app _ _ _ (or_intror Hbv))) as (BV3 & _ & _ & BV4 & BV5).
    pose proof (AH_range_gen _ _ _ _ bq HEAP (in_or_app _ _ _ (or_intror Hbq))) as (BQ3 & _ & _ & BQ4 & BQ5).
    pose proof (AH_range_gen _ _ _ _ bt HEAP (in_or_app _ _ _ (or_intror Hbt))) as (BT3 & _ & _ & BT4 & BT5).
    pose proof (AH_offsh _ _ _ _ bpv HEAP (in_or_app _ _ _ (or_intror Hbv))) as ROV. unfold SHLO, SHHI in ROV.
    destruct (item_cellsA_octet _ _ _ _ HEAP) as (IT0 & IT8 & IT8L & IT16 & IT32 & ACCIT).
    pose proof PAY as (_ & DF & D0 & D63 & D26 & _).
    assert (EPV : bv_unsigned (Z_to_bv 64 PV) = PV) by (apply unsigned_lit; clear - BV1 BV2 BV3 BV4 CE3; unfold BnHeapA.ACEIL in *; lia).
    assert (ITR : 0x547620 <= ITEM_OCTET_A /\ ITEM_OCTET_A + 56 <= 0x547720) by (unfold ITEM_OCTET_A; clear; lia).
    assert (ITV : ITEM_OCTET_A = 5535264) by reflexivity.
    unfold INTERN_A, MallocRep.wz in *. unfold CtRepP.W_check_tlen.tlc_in in HTLC.
    pose proof (proj2 (AH_acc _ _ _ _ bpv HEAP (in_or_app _ _ _ (or_intror Hbv)))) as ACCV.
    assert (OFFW : offshW [(bv_unsigned sp - 288, bv_unsigned sp)]%Z) by (cbn [offshW]; unfold SHLO, SHHI; clear - CE2 CEIL LOSP; unfold BnHeapA.ACEIL in *; lia).
    pose proof (munch_refl [(bv_unsigned sp - 288, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctasegs m) as WM.
    (* [comment removed for export] *)
    assert (NONE_TAIL : forall (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (F' : bvmap 5 word) (fc' : bv 32)
        (Σ' : rts RT) (st' : ap_st bptr) (m' : mem) (OW' : list block) (bo' : Z * Z) (adr' : bptr -> Z) (ov : word) (jt : list (bv 8)),
      ap_preA Σ' st' m' OW' LB E bo' (Z_to_bv 64 (bv_unsigned sp + -64)) lo 0 0 0 ->
      ax_pres LB (bv_unsigned sp) ([(OPP, OPP + 8); (PV, PV + 8); (TLC, TLC + 32)] ++ LIBW_A) m m' ->
      rt_credit RT Σ - (EXO_COST_A (zlength d) + 13) <= rt_credit RT Σ' ->
      blocks_kept K st' OW' m m' ->
      (forall b, In b LB -> adr' (blk_id b) = adr (blk_id b)) ->
      rw_cells ctasegs m' OPP [C8 ov] -> rw_cells ctasegs m' TLC [CB 32 jt] -> rw_cells ctasegs m' PV [C8 (Z_to_bv 64 0)] ->
      rw_cells ctasegs m' (bv_unsigned sp + -64) [C8 (Z_to_bv 64 0); C8 t3; C8 t4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      implAp (ARet (@None (octet bptr), st')) Σ' (exprim_oct_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB E lo m K (INTERN_OCT_COST_A (zlength d)) adr OPP PV TLC)
        (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp (Z_to_bv 64 TP_A) x5 x6 x7 sp (Z_to_bv 64 ITEM_OCTET_A) (Z_to_bv 64 0) x11 x12 x13 x14 x15 x16 x17
                 (Z_to_bv 64 PV) s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F' (Z_to_bv 64 0x2402b4) fc' None m' (seg_rom ctasegs))).
    { intros until jt. intros PRE' AXP1 CRED' KEPT1 ADR' HOPP' HTLC' HPV' FR.
      pose proof PRE' as (HEAP' & AS' & IDS' & DC' & ST' & _ & _ & _ & _ & MI' & _ & _).
      assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; clear - SPR CEIL LOSP LO0; lia).
      rewrite ESP in ST'.
      pose proof (munch_refl [(bv_unsigned sp - 288, bv_unsigned sp)]%Z m') as MU'. pose proof (wmono_refl ctasegs m') as WM'.
      freeze HOPP'. freeze HTLC'. freeze HPV'.
      apply implAp_from_evt.
      step. step. if_false. step. step. step.
      unfold frozen in HPV'.
      destruct (item_cellsA_octet _ _ _ _ HEAP') as (JT0 & JT8 & JT8L & JT16 & JT32 & ACCIT').
      pose proof item_ex_free_null_walkA as HEF. unfold item_ex_free_null_specA, ITEM_EX_FREE_A in HEF.
      eapply (HEF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo PV ITEM_OCTET_A 4 (blk_addr bpv) (blk_size bpv) (fun _ => True)); rewrite ?ESP;
        [exact ST'| unfold SHHI; clear - CE2 CEIL; unfold BnHeapA.ACEIL in *; lia| unfold W_freeStmtB.ITEM_EX_FREE_STACK_A, ITEM_EX_FREE_STACK_A; clear - LOSP; lia| clear - TOP; unfold USTACK_TOP in *; lia| exact MI'
        | exact (AH_shbA _ _ _ _ HEAP')
        | exact (proj2 (AH_acc _ _ _ _ bpv HEAP' (in_or_app _ _ _ (or_intror Hbv))))| exact BV1| exact BV2| exact BV3| clear - BV4 CEIL; lia
        | pose proof ROV as X; unfold SHLO, SHHI; exact X| exact ALV| exact HPV'
        | split; [exact JT0| split; [exact JT8| split; [exact JT8L| split; [exact JT16| split; [exact JT32| exact ACCIT']]]]]
        | clear - ITR; lia| unfold SHLO; clear - ITR; lia| unfold ITEM_OCTET_A; reflexivity| rewrite (sx32_small 4) by (clear; lia); rewrite unsigned_lit by (clear; lia); clear; lia
        | reflexivity| reflexivity|].
      intros t0'' t1'' t2'' b0 b1 b2 b3 b4 b5 b6 b7 t3'' t4'' t5'' t6'' m'' MU'' WM'' MI'' ST''. rewrite ?ESP in MU'', ST''. unfold W_freeStmtB.ITEM_EX_FREE_STACK_A, ITEM_EX_FREE_STACK_A in MU''.
      unfold ITEM_EX_FREE_RA. rewrite (ret_pc_even 0x2402c8) by (clear; lia).
      (* [comment removed for export] *)
      pose proof (agree_on_of_munch_nw _ _ _ MU'') as AG''.
      apply (rw_cells_agree _ _ _ _ _ AG'') in FR; [| intros a Ha; cbn in Ha; cbn [outside fst snd]; clear - Ha; lia].
      unfold frozen in HOPP', HTLC'.
      apply (rw_cells_agree _ _ _ _ _ AG'') in HOPP'; [| intros a Ha; cbn in Ha; cbn [outside fst snd]; clear - Ha BQ1 BQ2 BQ4 CEIL LOSP; lia].
      apply (rw_cells_agree _ _ _ _ _ AG'') in HPV'; [| intros a Ha; cbn in Ha; cbn [outside fst snd]; clear - Ha BV1 BV2 BV4 CEIL LOSP; lia].
      apply (rw_cells_agree _ _ _ _ _ AG'') in HTLC'; [| intros a Ha; cbn in Ha; cbn [outside fst snd]; clear - Ha BT1 BT2 BT4 CEIL LOSP; lia].
      assert (HEAP'' : AHEAP Σ' OW' LB m'').
      { eapply (AH_frame Σ' OW' LB m' m'' _ HEAP' MU'' WM''). constructor; [left; cbn [fst snd]; clear - CEIL LOSP TOP; unfold USTACK_TOP in *; lia| constructor]. }
      assert (AGL'' : agree_on (lib_addr OW') m' m'').
      { eapply agree_on_mono; [exact AG''|]. intros a [HS|(b & Hb & Hr)]; cbn [outside fst snd].
        - pose proof (LIBW_S_A a HS) as HA. unfold LIBW_A in HA. cbn [rin_ivs fst snd] in HA. clear - HA CE1 CEIL LOSP. unfold BnHeapA.ACEIL in *. lia.
        - pose proof (AH_range_gen _ _ _ _ b HEAP' (in_or_app _ _ _ (or_introl Hb))) as (_ & _ & _ & R3 & _). clear - Hr R3 CEIL LOSP. lia. }
      pose proof AS' as (_ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & OD')).
      clear MU' WM'. pose proof (munch_refl [(bv_unsigned sp - 288, bv_unsigned sp)]%Z m'') as MU'. pose proof (wmono_refl ctasegs m'') as WM'.
      freeze HOPP'. freeze HPV'. freeze HTLC'.
      step. step. do 5 step. step. release_frame FR ST'' (bv_unsigned sp). step.
      apply evt_done. apply implAp_ret. unfold exprim_oct_postA. cbn [fst snd]. unfold frozen in HOPP', HPV', HTLC'.
      do 16 eexists. exists m'', OW', bo', adr', (@nil block), ov, jt. split; [reflexivity|].
      split.
      { unfold ap_preA. cbn [app]. split; [exact HEAP''|]. split; [exact (ap_state_agree _ _ _ _ _ _ AS' AGL'')|]. split; [exact IDS'|]. split; [exact (data_cells_agree _ _ _ _ DC' AGL'' OD')|].
        split; [exact ST''|]. split; [exact CEIL|]. split; [clear - LOSP; lia|].
        split; [exact TOP|]. split; [exact AL16|]. split; [exact MI''|]. pose proof PRE' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CR0 & _).
        split; [clear - CR0; lia| clear - FRM; lia]. }
      split.
      { eapply ax_pres_trans; [exact AXP1|]. unfold ax_pres. eapply agree_on_mono; [exact AG''|]. intros a [_ Ha]; cbn [outside fst snd]. destruct Ha as [H1|[H1|(b & Hb & Hr)]].
        - clear - H1. lia.
        - assert (a < 12365824) by (destruct H1 as [(l & h & Hin & Hlh) _]; unfold CLIENT_STATIC in Hin; cbn [In] in Hin; clear - Hin Hlh; destruct Hin as [E0|[E0|[E0|[]]]]; injection E0 as <- <-; lia).
          clear - H CE1 CEIL LOSP. unfold BnHeapA.ACEIL in *. lia.
        - pose proof (AH_range_gen _ _ _ _ b HEAP (in_or_app _ _ _ (or_intror Hb))) as (_ & _ & _ & R3 & _). clear - Hr R3 CEIL LOSP. lia. }
      split; [unfold INTERN_OCT_COST_A; rewrite EC13; exact CRED'|]. split; [exact (blocks_kept_lib _ _ _ _ _ _ KEPT1 AGL'')|]. split; [exact ADR'|].
      split; [intros b Hb; destruct Hb|]. split; [constructor|]. split; [exact HOPP'|]. split; [exact HTLC'|]. split; [reflexivity| exact HPV']. }
    hide BV5. hide BQ5. hide BT5. hide DOV. hide DOT. hide DVT. hide DOD. hide DVD. hide DTD. hide ROV.
    freeze HOPP. freeze HTLC.
    apply implAp_from_evt.
    (* [comment removed for export] *)
    carve_frame 64%nat ST. do 7 step.
    step. if_cases KP; zc KP; [exfalso; rewrite ?EPV in KP; clear - KP BV3 BV1; lia|]. clear KP.
    step. step. if_cases KI; zc KI; [exfalso; rewrite ?unsigned_lit in KI by (clear - ITR; lia); clear - KI ITR; lia|]. clear KI.
    step. step. step. step. step. step.
    (* [comment removed for export] *)
    carve_frame 224%nat ST. do 15 step.
    do 9 step. if_cases KP2; zc KP2; [exfalso; rewrite ?EPV in KP2; clear - KP2 BV3 BV1; lia|]. clear KP2.
    step. step. if_cases KI2; zc KI2; [exfalso; rewrite ?unsigned_lit in KI2 by (clear - ITR; lia); clear - KI2 ITR; lia|]. clear KI2.
    step. step. if_cases KL; zc KL.
    - (* [comment removed for export] *)
      assert (DN : zlength d = 0).
      { revert KL. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by (clear; lia). rewrite Z.mod_small by (clear - D26; unfold zlength in *; lia).
        clear - D26. unfold zlength in *. intros KL. apply andb_false_iff in KL. destruct KL as [KL|KL]; apply Z.ltb_ge in KL; lia. }
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m0 end.
      match goal with H : munch _ m m0 |- _ => rename H into MU0 end. match goal with H : wmono ctasegs m m0 |- _ => rename H into WM0 end.
      match goal with H : stk ctasegs m0 lo _ |- _ => rename H into ST0 end. match goal with H : mem_inv ctasegs m0 |- _ => rename H into MI0 end.
      match goal with H : rw_cells ctasegs m0 (bv_unsigned sp + -64) _ |- _ => rename H into FRI end.
      match goal with H : rw_cells ctasegs m0 (bv_unsigned sp + -288) _ |- _ => rename H into FRE end.
      apply evt_done. rewrite d2i_octet_split. rewrite (proj2 (Z.leb_le (zlength d) 0)) by (clear - DN; lia). cbv iota.
      (* [comment removed for export] *)
      assert (ESPe : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -288)) = bv_unsigned sp + -288) by (apply unsigned_lit; clear - SPR CEIL LOSP LO0; lia).
      assert (ESPi : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; clear - SPR CEIL LOSP LO0; lia).
      pose proof (agree_on_of_munch_nw _ _ _ MU0) as AG0.
      assert (HEAP0 : AHEAP Σ OW LB m0).
      { eapply (AH_frame Σ OW LB m m0 _ HEAP MU0 WM0). constructor; [left; cbn [fst snd]; clear - CEIL LOSP TOP; unfold USTACK_TOP in *; lia| constructor]. }
      assert (AGL0 : agree_on (lib_addr OW) m m0).
      { eapply agree_on_mono; [exact AG0|]. intros a [HS|(b & Hb & Hr)]; cbn [outside fst snd].
        - pose proof (LIBW_S_A a HS) as HA. unfold LIBW_A in HA. cbn [rin_ivs fst snd] in HA. clear - HA CE1 CEIL LOSP. unfold BnHeapA.ACEIL in *. lia.
        - pose proof (AH_range_gen _ _ _ _ b HEAP (in_or_app _ _ _ (or_introl Hb))) as (_ & _ & _ & R3 & _). clear - Hr R3 CEIL LOSP. lia. }
      assert (AGC0 : agree_on (aclient_addr LB (bv_unsigned sp)) m m0).
      { eapply agree_on_mono; [exact AG0|]. intros a [H1|[H1|(b & Hb & Hr)]]; cbn [outside fst snd].
        - clear - H1. lia.
        - pose proof (client_static_lowA a H1) as Ha. unfold SEGTOP_A in Ha. clear - Ha CE1 CEIL LOSP. unfold BnHeapA.ACEIL in *. lia.
        - pose proof (AH_range_gen _ _ _ _ b HEAP (in_or_app _ _ _ (or_intror Hb))) as (_ & _ & _ & R3 & _). clear - Hr R3 CEIL LOSP. lia. }
      assert (AGF0 : agree_on (aclient_addr (OW ++ LB) (bv_unsigned sp)) m m0).
      { intros a Hr Ha. destruct Ha as [H1|[H1|(b & Hb & Hrg)]]; [apply (AGC0 a Hr); left; exact H1| apply (AGC0 a Hr); right; left; exact H1|].
        apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [apply (AGL0 a Hr); right; exists b; split; [exact Hb| exact Hrg]| apply (AGC0 a Hr); right; right; exists b; split; [exact Hb| exact Hrg]]. }
      pose proof AS as (_ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & OD)).
      assert (PREe : ap_preA Σ st m0 OW LB E bo (Z_to_bv 64 (bv_unsigned sp + -288)) lo 0 0 0).
      { unfold ap_preA. rewrite ESPe. split; [exact HEAP0|]. split; [exact (ap_state_agree _ _ _ _ _ _ AS AGL0)|]. split; [exact IDS|]. split; [exact (data_cells_agree _ _ _ _ DC AGL0 OD)|].
        split; [exact ST0|]. split; [exact CEIL|]. split; [clear - LOSP; lia|]. split; [clear - TOP; lia|].
        split; [clear - AL16; unfold al16 in *; Z.div_mod_to_equations; lia|]. split; [exact MI0|]. split; [clear - CRED; lia| clear - FRM; lia]. }
      assert (UW1 : uw_chain USTACK_TOP m0 (bv_unsigned sp + -64) (bv_unsigned sp) (bv_unsigned ra :: ras)).
      { uw_call_mu_tac m 64 UW MU0 FRI; [intros a Ha; cbn [outside fst snd]; lia | clear; lia | uchk_open; clear - AL16; Z.div_mod_to_equations; lia | clear - TOP; unfold USTACK_TOP in *; lia]. }
      assert (UWe : uw_chain USTACK_TOP m0 (bv_unsigned sp + -288) (bv_unsigned sp + -64) (0x2402b4 :: bv_unsigned ra :: ras)).
      { pose proof (munch_refl ([] : list (Z * Z)) m0) as MUr. pose proof FRE as FRE'.
        replace (bv_unsigned sp + -288) with (bv_unsigned sp + -64 + - (224)) in FRE' by (clear; lia).
        uw_call_mu_tac m0 224 UW1 MUr FRE'; [intros a Ha; exact I | clear; lia | uchk_open; clear - AL16; Z.div_mod_to_equations; lia | clear - TOP; unfold USTACK_TOP in *; lia]. }
      unfold hidden in BV5, BQ5, BT5. unfold frozen in HOPP, HTLC.
      apply (rw_cells_agree _ _ _ _ _ AG0) in HOPP; [| intros a Ha; cbn in Ha; cbn [outside fst snd]; clear - Ha BQ1 BQ2 BQ4 CEIL LOSP; lia].
      apply (rw_cells_agree _ _ _ _ _ AG0) in HTLC; [| intros a Ha; cbn in Ha; cbn [outside fst snd]; clear - Ha BT1 BT2 BT4 CEIL LOSP; lia].
      (* [comment removed for export] *)
      assert (KEEP : forall mA mB, ax_pres LB (bv_unsigned sp + -288) LIBW_A mA mB ->
                (forall A0 cs, rw_cells ctasegs mA A0 cs -> bv_unsigned sp + -288 <= A0 -> A0 + Z.of_nat (cells_size cs) <= USTACK_TOP -> rw_cells ctasegs mB A0 cs)
                /\ (forall (b : block) A0 cs, In b LB -> rw_cells ctasegs mA A0 cs -> blk_addr b <= A0 -> A0 + Z.of_nat (cells_size cs) <= blk_addr b + blk_size b -> rw_cells ctasegs mB A0 cs)
                /\ (uw_chain USTACK_TOP mA (bv_unsigned sp + -288) (bv_unsigned sp + -64) (0x2402b4 :: bv_unsigned ra :: ras) ->
                    uw_chain USTACK_TOP mB (bv_unsigned sp + -288) (bv_unsigned sp + -64) (0x2402b4 :: bv_unsigned ra :: ras))).
      { intros mA mB AX. split; [| split].
        - intros A0 cs HC H1 H2. eapply rw_cells_agree; [exact AX| exact HC|]. intros a Ha. split; [| left; clear - Ha H1 H2; lia].
          unfold LIBW_A. cbn [rin_ivs fst snd app]. clear - Ha H1 CE1 CEIL LOSP. unfold BnHeapA.ACEIL in *. lia.
        - intros b A0 cs Hb HC H1 H2. pose proof (AH_range_gen _ _ _ _ b HEAP (in_or_app _ _ _ (or_intror Hb))) as (_ & _ & _ & R4 & R5).
          eapply rw_cells_agree; [exact AX| exact HC|]. intros a Ha. split; [unfold LIBW_A; cbn [rin_ivs fst snd app]; clear - Ha H1 H2 R5; lia|].
          right; right. exists b. split; [exact Hb| clear - Ha H1 H2; lia].
        - intros UWx. apply (uw_chain_axpres _ _ _ _ _ _ _ AX) in UWx; [exact UWx| clear; lia| unfold SEGTOP_A; clear - CE1 CEIL LOSP; unfold BnHeapA.ACEIL in *; lia]. }
      destruct (lit_okA_auto A_TASN_DEC_C_A 23 ltac:(vm_compute; reflexivity)) as (fs' & fk & LF).
      destruct (lit_okA_auto A_ASN1_ITEM_EMBED_D2I_FN_A 20 ltac:(vm_compute; reflexivity)) as (ns & nk & LN).
      change 23 with (rs_flen RS_td_small) in LF. change 20 with (rs_fnlen RS_td_small) in LN.
      unfold err_raise.
      eapply implAp_abind with (Q1 := fun r3 ΣC ms3 => exists (o0 o1 o2 o10 o11 o12 o13 o14 o15 o16 o17 o18 o19 o20 o21 o22 o23 o24 o25 o26 o27 o3 o4 o5 o6 : word) (F3 : bvmap 5 word) (fc3 : bv 32) mC OW3,
          ms3 = MS (mkR (Z_to_bv 64 0x24074c) (Z_to_bv 64 (bv_unsigned sp + -288)) gp (Z_to_bv 64 TP_A) o0 o1 o2 (Z_to_bv 64 (bv_unsigned sp + -64)) (Z_to_bv 64 ITEM_OCTET_A)
                        o10 o11 o12 o13 o14 o15 o16 o17 o18 o19 o20 o21 o22 o23 o24 o25 o26 o27 o3 o4 o5 o6)
                   F3 (Z_to_bv 64 0x24074c) fc3 None mC (seg_rom ctasegs)
          /\ ap_preA ΣC (snd r3) mC OW3 LB E bo (Z_to_bv 64 (bv_unsigned sp + -288)) lo 0 0 0
          /\ ax_pres LB (bv_unsigned sp + -288) LIBW_A m0 mC
          /\ rt_credit RT Σ - GETOBJ_ERR_COST_A <= rt_credit RT ΣC
          /\ blocks_kept K (snd r3) OW3 m0 mC).
      + (* [comment removed for export] *)
        eapply implAp_abind.
        { apply implAp_from_evt. step. apply evt_done.
          pose proof (ERR_new_walkA bo) as W1. unfold ap_stmtA in W1.
          eapply W1; [eapply ap_preA_restockA; [exact PREe| rewrite ESPe; ecu; clear - LOSP; lia| ecu; clear - CRED EXC0; lia| ecu; clear; lia| ecu; clear - FRM; lia]
                    | reflexivity| rewrite ESPe, ESPi; exact UWe| rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_embed_new (uk_ctx_call _ _ _ _ E_intern_embed CTX))| apply cons_ne
                    | reflexivity| exact KOW| exact KIDS]. }
        intros r1 ΣA ms1 PO1. cbv beta in PO1.
        destruct PO1 as (q0 & q1 & q2 & q10 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q3 & q4 & q5 & q6 & F1 & fc1 & mA & OW1 & bo1 & -> & PREa & AXa & CRa & BKa & EBO1). subst bo1.
        rewrite ESPe in AXa. destruct (KEEP _ _ AXa) as (KS1 & KB1 & KU1). pose proof (KU1 UWe) as UWa.
        apply KS1 in FRE; [| clear; lia| cbn [cells_size csize Nat.add]; rewrite ?Nat2Z.inj_add; cbn; clear - TOP; unfold USTACK_TOP in *; lia].
        apply KS1 in FRI; [| clear; lia| cbn; clear - TOP; unfold USTACK_TOP in *; lia].
        apply (KB1 bq) in HOPP; [| exact Hbq| exact BQ1| cbn; exact BQ2]. apply (KB1 bpv) in HPV; [| exact Hbv| exact BV1| cbn; exact BV2]. apply (KB1 bt) in HTLC; [| exact Hbt| exact BT1| cbn; exact BT2].
        pose proof BKa as (KOWa & KIDa & _).
        assert (KIDSa : forall b, In b K -> ~ In (blk_id b) (es_ids (snd r1) ++ env_ids E)).
        { intros b Hb Hin. apply in_app_iff in Hin. destruct Hin as [Hin|Hin]; [exact (KIDa b Hb Hin)| apply (KIDS b Hb); apply in_app_iff; right; exact Hin]. }
        rewrite (ret_pc_even (0x240720 + 4)) by (clear; lia). change (0x240720 + 4) with 0x240724.
        pose proof PREa as (_ & _ & _ & _ & STa & _ & _ & _ & _ & MIa & CREDa & _). rewrite ESPe in STa. cbn [ar_RT push amb] in CRa, CREDa.
        pose proof (munch_refl (@nil (Z * Z)) mA) as MUa. pose proof (wmono_refl ctasegs mA) as WMa.
        (* [comment removed for export] *)
        eapply implAp_abind.
        { apply implAp_from_evt. do 6 step. apply evt_done.
          change (Z_to_bv 64 0x72b80) with (Z_to_bv 64 A_TASN_DEC_C_A). change (Z_to_bv 64 0x72bc0) with (Z_to_bv 64 A_ASN1_ITEM_EMBED_D2I_FN_A).
          pose proof (ERR_set_debug_walkA STRCPY RS_td_small A_TASN_DEC_C_A A_ASN1_ITEM_EMBED_D2I_FN_A bo _ _ _ _ LF LN) as W2. unfold ap_stmtA in W2.
          eapply W2; [eapply ap_preA_restockA; [exact PREa| rewrite ESPe; ecu; clear - LOSP; lia| ecu; clear - CRED CRa EXC0; lia| ecu; clear; lia| ecu; clear - FRM; lia]
                    | reflexivity| rewrite ESPe, ESPi; exact UWa| rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_embed_dbg (uk_ctx_call _ _ _ _ E_intern_embed CTX))| apply cons_ne
                    | unfold MallocRep.wz; cbn [rs_line RS_td_small]; repeat split; reflexivity| exact KOWa| exact KIDSa]. }
        intros r2 ΣB ms2 PO2. cbv beta in PO2.
        destruct PO2 as (p0 & p1' & p2' & p10 & p11 & p12 & p13 & p14 & p15 & p16 & p17 & p3 & p4 & p5 & p6 & F2 & fc2 & mB & OW2 & bo2 & -> & PREb & AXb & CRb & BKb & EBO2). subst bo2.
        rewrite ESPe in AXb. destruct (KEEP _ _ AXb) as (KS2 & KB2 & KU2). pose proof (KU2 UWa) as UWb.
        apply KS2 in FRE; [| clear; lia| cbn [cells_size csize Nat.add]; rewrite ?Nat2Z.inj_add; cbn; clear - TOP; unfold USTACK_TOP in *; lia].
        apply KS2 in FRI; [| clear; lia| cbn; clear - TOP; unfold USTACK_TOP in *; lia].
        apply (KB2 bq) in HOPP; [| exact Hbq| exact BQ1| cbn; exact BQ2]. apply (KB2 bpv) in HPV; [| exact Hbv| exact BV1| cbn; exact BV2]. apply (KB2 bt) in HTLC; [| exact Hbt| exact BT1| cbn; exact BT2].
        pose proof (blocks_kept_transA K _ _ _ _ m0 mA mB BKa BKb) as BKab. pose proof BKab as (KOWb & KIDb & _).
        assert (KIDSb : forall b, In b K -> ~ In (blk_id b) (es_ids (snd r2) ++ env_ids E)).
        { intros b Hb Hin. apply in_app_iff in Hin. destruct Hin as [Hin|Hin]; [exact (KIDb b Hb Hin)| apply (KIDS b Hb); apply in_app_iff; right; exact Hin]. }
        rewrite (ret_pc_even 0x24073c) by (clear; lia).
        pose proof PREb as (_ & _ & _ & _ & STb & _ & _ & _ & _ & MIb & CREDb & _). rewrite ESPe in STb. cbn [ar_RT push amb] in CRb, CREDb.
        pose proof (munch_refl (@nil (Z * Z)) mB) as MUb. pose proof (wmono_refl ctasegs mB) as WMb.
        (* [comment removed for export] *)
        apply implAp_from_evt. do 4 step. apply evt_done.
        pose proof (ERR_set_error_closedA AR UK BE RS_td_small 13 224 bo) as W3. unfold ERR_set_error_specA, ap_stmtA in W3.
        eapply implAp_mono.
        { eapply W3; [eapply ap_preA_restockA; [exact PREb| rewrite ESPe; ecu; clear - LOSP; lia| ecu; clear - CRED CRa CRb EXC0; lia| ecu; clear; lia| ecu; clear - FRM; lia]
                    | reflexivity| rewrite ESPe, ESPi; exact UWb| rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_embed_err (uk_ctx_call _ _ _ _ E_intern_embed CTX))| apply cons_ne
                    | unfold ERR_LIB_SYS, MallocRep.wz; repeat split; first [reflexivity| (clear; lia)]| exact KOWb| exact KIDSb]. }
        intros r3 ΣC ms3 PO3. cbv beta in PO3.
        destruct PO3 as (o0 & o1 & o2 & o10 & o11 & o12 & o13 & o14 & o15 & o16 & o17 & o3 & o4 & o5 & o6 & F3 & fc3 & mC & OW3 & bo3 & -> & PREc & AXc & CRc & BKc & EBO3). subst bo3.
        rewrite ESPe in AXc. cbn [ar_RT push amb] in CRc. rewrite (ret_pc_even 0x24074c) by (clear; lia).
        eexists o0, o1, o2, o10, o11, o12, o13, o14, o15, o16, o17, _, _, _, _, _, _, _, _, _, _, o3, o4, o5, o6, F3, fc3, mC, OW3.
        split; [reflexivity|]. split; [exact PREc|]. split; [eapply ax_pres_trans; [exact AXa| eapply ax_pres_trans; [exact AXb| exact AXc]]|].
        split; [rewrite EC13; ecu; clear - CRa CRb CRc; lia| exact (blocks_kept_transA K _ _ _ _ m0 mB mC BKab BKc)].
      + (* [comment removed for export] *)
        intros r3 ΣC ms3 PO3. cbv beta in PO3. cbv beta.
        destruct PO3 as (o0 & o1 & o2 & o10 & o11 & o12 & o13 & o14 & o15 & o16 & o17 & o18 & o19 & o20 & o21 & o22 & o23 & o24 & o25 & o26 & o27 & o3 & o4 & o5 & o6 & F3 & fc3 & mC & OW3 & -> & PREc & AXc & CRc & BKc).
        destruct (KEEP _ _ AXc) as (KS3 & KB3 & _).
        apply KS3 in FRE; [| clear; lia| cbn [cells_size csize Nat.add]; rewrite ?Nat2Z.inj_add; cbn; clear - TOP; unfold USTACK_TOP in *; lia].
        apply KS3 in FRI; [| clear; lia| cbn; clear - TOP; unfold USTACK_TOP in *; lia].
        apply (KB3 bq) in HOPP; [| exact Hbq| exact BQ1| cbn; exact BQ2]. apply (KB3 bpv) in HPV; [| exact Hbv| exact BV1| cbn; exact BV2]. apply (KB3 bt) in HTLC; [| exact Hbt| exact BT1| cbn; exact BT2].
        pose proof PREc as (HEAPc & ASc & IDSc & DCc & STc & _ & _ & _ & _ & MIc & CREDc & FRMc). rewrite ESPe in STc.
        pose proof (munch_refl (@nil (Z * Z)) mC) as MUc. pose proof (wmono_refl ctasegs mC) as WMc.
        apply implAp_from_evt. unfold MallocRep.wz.
        step. do 13 step. step. release_frame FRE STc (bv_unsigned sp + -64). step.
        apply evt_done.
        apply rw_cells_CB_ofA in HTLC. cbn [cells_size csize Nat.add] in HTLC.
        eapply NONE_TAIL; [| | | exact BKc' || idtac| intros b Hb; reflexivity| exact HOPP| exact HTLC| exact HPV| exact FRI].
        * unfold ap_preA. rewrite ESPi. split; [exact HEAPc|]. split; [exact ASc|]. split; [exact IDSc|]. split; [exact DCc|].
          split; [match goal with H : stk ctasegs mC lo _ |- _ => exact H end|]. split; [exact CEIL|]. split; [clear - LOSP; lia|]. split; [clear - TOP; lia|].
          split; [clear - AL16; unfold al16 in *; Z.div_mod_to_equations; lia|]. split; [exact MIc|]. split; [exact CREDc| exact FRMc].
        * eapply ax_pres_trans.
          -- unfold ax_pres. eapply agree_on_mono; [exact AGC0|]. intros a [_ Ha]. exact Ha.
          -- eapply ax_pres_weaken; [exact AXc| clear; lia| intros b Hb; exact Hb| intros a Ha; cbn [rin_ivs app]; right; right; right; exact Ha].
        * rewrite EC13 in CRc. clear - CRc EXC0. lia.
        * exact (blocks_kept_pre K (snd r3) OW OW3 LB (bv_unsigned sp) m m0 mC KOW AGF0 BKc).
    - (* [comment removed for export] *)
      assert (TL0 : 0 < zlength d).
      { match goal with H : 0 < Z.land (zlength d) _ |- _ => revert H end. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by (clear; lia).
        rewrite Z.mod_small by (clear - D26; unfold zlength in *; lia). clear. intros H. exact H. }
      try clear KL. try clear KL0. try clear KL1.
      (* [comment removed for export] *)
      step. step. step.
      step. step. if_true.
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
      do 7 step. do 13 step. step.
      match goal with FR0 : rw_cells ctasegs ?mx (bv_unsigned sp + -288) _, ST : stk ctasegs ?mx lo _ |- evt _ _ (MS _ _ _ _ _ ?mx _) => release_frame FR0 ST (bv_unsigned sp + -64) end. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
      match goal with H : munch _ m m1 |- _ => rename H into MU1 end. match goal with H : wmono ctasegs m m1 |- _ => rename H into WM1 end.
      match goal with H : mem_inv ctasegs m1 |- _ => rename H into MI1 end. match goal with H : stk ctasegs m1 lo _ |- _ => rename H into ST1 end.
      match goal with H : rw_cells ctasegs m1 (bv_unsigned sp + -64) _ |- _ => rename H into FR end.
      apply evt_done. fold ADEP_ENTRY. rewrite d2i_octet_split. rewrite (proj2 (Z.leb_gt (zlength d) 0)) by exact TL0. cbv iota.
      (* [comment removed for export] *)
      assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; clear - SPR CEIL LOSP LO0; lia).
      pose proof (agree_on_of_munch_nw _ _ _ MU1) as AG1.
      assert (HEAP1 : AHEAP Σ OW LB m1).
      { eapply (AH_frame Σ OW LB m m1 _ HEAP MU1 WM1). constructor; [left; cbn [fst snd]; clear - CEIL LOSP TOP; unfold USTACK_TOP in *; lia| constructor]. }
      assert (AGL1 : agree_on (lib_addr OW) m m1).
      { eapply agree_on_mono; [exact AG1|]. intros a [HS|(b & Hb & Hr)]; cbn [outside fst snd].
        - pose proof (LIBW_S_A a HS) as HA. unfold LIBW_A in HA. cbn [rin_ivs fst snd] in HA. clear - HA CE1 CEIL LOSP. unfold BnHeapA.ACEIL in *. lia.
        - pose proof (AH_range_gen _ _ _ _ b HEAP (in_or_app _ _ _ (or_introl Hb))) as (_ & _ & _ & R3 & _). clear - Hr R3 CEIL LOSP. lia. }
      assert (AGC1 : agree_on (aclient_addr LB (bv_unsigned sp)) m m1).
      { eapply agree_on_mono; [exact AG1|]. intros a [H1|[H1|(b & Hb & Hr)]]; cbn [outside fst snd].
        - clear - H1. lia.
        - pose proof (client_static_lowA a H1) as Ha. unfold SEGTOP_A in Ha. clear - Ha CE1 CEIL LOSP. unfold BnHeapA.ACEIL in *. lia.
        - pose proof (AH_range_gen _ _ _ _ b HEAP (in_or_app _ _ _ (or_intror Hb))) as (_ & _ & _ & R3 & _). clear - Hr R3 CEIL LOSP. lia. }
      pose proof AS as (_ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & OD)).
      assert (PRE1 : ap_preA Σ st m1 OW LB E bo (Z_to_bv 64 (bv_unsigned sp + -64)) lo EXO_STACK_A (EXO_COST_A (zlength d)) EXO_FRAMES_A).
      { unfold ap_preA. rewrite ESP. split; [exact HEAP1|]. split; [exact (ap_state_agree _ _ _ _ _ _ AS AGL1)|]. split; [exact IDS|]. split; [exact (data_cells_agree _ _ _ _ DC AGL1 OD)|].
        split; [exact ST1|]. split; [exact CEIL|]. split; [rewrite EXS; clear - LOSP; lia|]. split; [clear - TOP; lia|].
        split; [clear - AL16; unfold al16 in *; Z.div_mod_to_equations; lia|]. split; [exact MI1|]. split; [clear - CRED EXC0; lia| rewrite EF7; exact FRM]. }
      unfold frozen in HOPP, HTLC.
      apply (rw_cells_agree _ _ _ _ _ AG1) in HOPP; [| intros a Ha; cbn in Ha; cbn [outside fst snd]; clear - Ha BQ1 BQ2 BQ4 CEIL LOSP; lia].
      apply (rw_cells_agree _ _ _ _ _ AG1) in HTLC; [| intros a Ha; cbn in Ha; cbn [outside fst snd]; clear - Ha BT1 BT2 BT4 CEIL LOSP; lia].
      first [apply (rw_cells_agree _ _ _ _ _ AG1) in HPV; [| intros a Ha; cbn in Ha; cbn [outside fst snd]; clear - Ha BV1 BV2 BV4 CEIL LOSP; lia] | idtac].
      assert (PAY1 : payload_okA m1 LB D d).
      { eapply payload_okA_agreeA; [exact PAY|]. eapply agree_on_mono; [exact AGC1|]. intros a Ha. right; right. exact Ha. }
      unfold hidden in DOV, DOT, DVT, DOD, DVD, DTD.
      pose proof HEXPRIM as HEX. unfold exprim_oct_specA in HEX.
      eapply implAp_post.
      { eapply HEX with (K := K) (j31 := j31); [exact PRE1| reflexivity
          | rewrite ESP; uw_call_mu_tac m 64 UW MU1 FR; [intros a Ha; cbn [outside fst snd]; lia | clear; lia | uchk_open; clear - AL16; Z.div_mod_to_equations; lia | clear - TOP; unfold USTACK_TOP in *; lia]
          | rewrite unsigned_lit by (clear; lia); exact (uk_ctx_tail _ _ _ E_embed_tail (uk_ctx_call _ _ _ _ E_intern_embed CTX))
          | apply cons_ne| exact KOW| exact KIDS| exact ADR
          | split; [exact PAY1|]; split; [exists bq; split; [exact Hbq| split; [exact BQ1| exact BQ2]]|]; split; [exists bpv; split; [exact Hbv| split; [exact BV1| exact BV2]]|];
            split; [exists bt; split; [exact Hbt| split; [exact BT1| exact BT2]]|]; split; [exact ALO|]; split; [exact ALV|]; split; [exact ALT|];
            split; [exact DOV|]; split; [exact DOT|]; split; [exact DVT|]; split; [exact DOD|]; split; [exact DVD|]; split; [exact DTD|];
            split; [exact HOPP|]; split; [exact HPV| exact HTLC]
          | exact TL0
          | reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity]. }
      cbv beta. intros [res st'] Σ' ms' PO. unfold exprim_oct_postA in PO. cbn [fst snd] in PO. unfold MallocRep.wz in PO. rewrite ?ESP in PO.
      destruct PO as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & F' & fc' & m' & OW' & bo' & adr' & NEW & ov & jt & -> & PRE' & AXP' & CRED' & KEPT' & ADR' & FRESH' & LBOK' & HOPP' & HTLC' & RES').
      rewrite (ret_pc_even 0x2402b4) by (clear; lia).
      pose proof PRE' as (HEAP' & AS' & IDS' & DC' & ST' & _ & _ & _ & _ & MI' & CR0' & FRM'). rewrite ESP in ST'.
      (* [comment removed for export] *)
      apply (rw_cells_agree _ _ _ _ _ AXP') in FR.
      2:{ intros a Ha. cbn [cells_size csize Nat.add] in Ha. rewrite ?Nat2Z.inj_add in Ha. cbn in Ha. split; [| left; clear - Ha TOP; unfold USTACK_TOP in *; lia].
          unfold LIBW_A. cbn [rin_ivs fst snd app]. clear - Ha BQ2 BQ4 BV2 BV4 BT2 BT4 CE1 CEIL LOSP. unfold BnHeapA.ACEIL in *. lia. }
      assert (AGF : agree_on (aclient_addr (OW ++ LB) (bv_unsigned sp)) m m1).
      { intros a Hr Ha. destruct Ha as [H1|[H1|(b & Hb & Hrg)]]; [apply (AGC1 a Hr); left; exact H1| apply (AGC1 a Hr); right; left; exact H1|].
        apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [apply (AGL1 a Hr); right; exists b; split; [exact Hb| exact Hrg]| apply (AGC1 a Hr); right; right; exists b; split; [exact Hb| exact Hrg]]. }
      assert (AXP1 : ax_pres LB (bv_unsigned sp) ([(OPP, OPP + 8); (PV, PV + 8); (TLC, TLC + 32)] ++ LIBW_A) m m').
      { eapply ax_pres_trans; [| eapply ax_pres_lower; [exact AXP'| clear; lia]]. unfold ax_pres. eapply agree_on_mono; [exact AGC1|]. intros a [_ Ha]. exact Ha. }
      assert (KEPT1 : blocks_kept K st' OW' m m') by (eapply (blocks_kept_pre K st' OW OW' LB); [exact KOW| exact AGF| exact KEPT']).
      destruct res as [os|].
      + (* [comment removed for export] *)
        destruct RES' as (ENEW & OREP & HPV'). freeze HPV'. freeze HOPP'. freeze HTLC'.
        pose proof (munch_refl [(bv_unsigned sp - 288, bv_unsigned sp)]%Z m') as MU'. pose proof (wmono_refl ctasegs m') as WM'.
        apply implAp_from_evt. step. step. if_true. step. do 5 step. step. release_frame FR ST' (bv_unsigned sp). step.
        apply evt_done. apply implAp_ret. unfold exprim_oct_postA. cbn [fst snd]. unfold frozen in HOPP', HPV', HTLC'.
        do 16 eexists. exists m', OW', bo', adr', NEW, ov, jt. split; [reflexivity|].
        split.
        { unfold ap_preA. split; [exact HEAP'|]. split; [exact AS'|]. split; [exact IDS'|]. split; [exact DC'|].
          split; [match goal with H : stk ctasegs m' lo (bv_unsigned sp) |- _ => exact H end|]. split; [exact CEIL|]. split; [clear - LOSP; lia|].
          split; [exact TOP|]. split; [exact AL16|]. split; [exact MI'|]. split; [clear - CR0'; lia| clear - FRM; lia]. }
        split; [exact AXP1|]. split; [unfold INTERN_OCT_COST_A; rewrite EC13; clear - CRED' EXC0; lia|]. split; [exact KEPT1|]. split; [exact ADR'|].
        split; [exact FRESH'|]. split; [exact LBOK'|]. split; [exact HOPP'|]. split; [exact HTLC'|]. split; [exact ENEW|]. split; [exact OREP| exact HPV'].
      + (* [comment removed for export] *)
        destruct RES' as (-> & HPV'). cbn [app] in PRE'.
        eapply NONE_TAIL; [| exact AXP1| clear - CRED' EXC0; lia| exact KEPT1| exact ADR'| exact HOPP'| exact HTLC'| exact HPV'| exact FR].
        unfold ap_preA. rewrite ESP. split; [exact HEAP'|]. split; [exact AS'|]. split; [exact IDS'|]. split; [exact DC'|].
        split; [exact ST'|]. split; [exact CEIL|]. split; [clear - LOSP; lia|]. split; [clear - TOP; lia|].
        split; [clear - AL16; unfold al16 in *; Z.div_mod_to_equations; lia|]. split; [exact MI'|]. split; [clear - CR0'; lia| exact FRM'].
  Qed.
End Walk.
End WithRT.
