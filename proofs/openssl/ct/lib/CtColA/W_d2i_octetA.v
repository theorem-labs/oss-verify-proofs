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
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import I_strcpyA ApATac ApATacX ApBImg ApWalkTac ApRepDefs ApRep ApIface ApFrame W_akit W_get_objectA W_check_tlenA W_item_d2i_stmtA W_item_d2i_imgA W_c2i_stmtA W_frkitA Fr_asn1_check_tlen Fr_asn1_d2i_ex_primitive W_item_d2i_exA W_item_d2i_tailA W_item_d2i_exprimA W_item_d2i_internA Fr_ASN1_item_d2i_ex.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require W_get_object_walkA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctP Require SctStmt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctA Require Import SctRepA SctStmtA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtColA Require Import ColDefsA ColBudgetA ExoBudgetA W_d2iA_stmt W_ctlA_defs W_d2iA_intern.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHarA Require Import HarKitA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeA Require Import BTacX.                (* [comment removed for export] *)
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
Definition D2I_OCT_STACK_A : Z := 32 + AIDE_FRAME + INTERN_OCT_STACK_A.
Definition D2I_OCT_COST_A (n : Z) : Z := 1 + INTERN_OCT_COST_A n.
Definition D2I_OCT_FRAMES_A : Z := 1 + EXO_FRAMES_A.

Lemma d2i_oct_budgets : D2I_OCT_STACK_A <= D2I_OCTET_STACK_A /\ D2I_OCT_FRAMES_A <= D2I_OCTET_FRAMES_A /\ (forall n, 0 <= n -> 0 <= D2I_OCT_COST_A n <= D2I_OCTET_COST_A n).
Proof.
  pose proof exo_within_d2i_octet as (S1 & S2 & S3). pose proof exo_budgets as (E1 & E2 & E3).
  unfold D2I_OCT_STACK_A, D2I_OCT_FRAMES_A, D2I_OCT_COST_A, INTERN_OCT_STACK_A, INTERN_OCT_COST_A, AIDE_FRAME, GETOBJ_ERR_COST_A, ERR_NEW_COST, ERR_SET_DEBUG_COST, ERR_SET_ERROR_COST, ERR_VSET_ERROR_COST.
  split; [clear - S1; lia|]. split; [clear - S2; lia|]. intros n Hn. specialize (S3 n Hn). rewrite E3 in *. clear - S3 Hn. lia.
Qed.

Definition ITEM_D2I_A : Z := 0x2405ac.
Definition AIDE_INTERN_RA : Z := 0x24048c.
(* [comment removed for export] *)
Local Notation E_oct_tail := (E_d2i_ASN1_OCTET_STRING_249f64 : uk_tail 0x246e0c 0x2405ac).   (* [comment removed for export] *)
Local Notation E_itemd2i_tail := (E_ASN1_item_d2i_242f00 : uk_tail 0x2405ac 0x240320).     (* [comment removed for export] *)
Local Notation E_aide_intern := (E_ASN1_item_d2i_ex_242dac : uk_call 0x240320 0x24048c 0x240274).  (* [comment removed for export] *)

Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation FR := (@ar_FR AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

(* [comment removed for export] *)
Lemma aide_lbokA_pop : forall f' k b, @lbokA (push AR f' k) b -> @lbokA AR b.
Proof.
  intros f' k b [H1 H2]. split; [exact H1|]. intros (f'' & k' & Hin & R). apply H2. exists f'', k'. split; [cbn [ar_FR push amb]; right; exact Hin| exact R].
Qed.

(* [comment removed for export] *)
Lemma aide_lbokA_off : forall f' k Σ OW L m b, @BnHeapA.AHEAP (push AR f' k) Σ OW L m -> In b (OW ++ L) -> @lbokA (push AR f' k) b -> off_fr f' k b.
Proof.
  intros f' k Σ OW L m b HEAP Hb [_ NPB]. destruct (@AH_fr_blk (push AR f' k) Σ OW L m f' k b HEAP ltac:(left; reflexivity) Hb) as [IN|OFF]; [| exact OFF].
  exfalso. apply NPB. exists f', k. split; [left; reflexivity| exact IN].
Qed.

Section Walk.
  Hypothesis STRCPY : strcpy_icontract RT.
  Hypothesis HEXPRIM : forall AR' : ARun, strcpy_icontract (@ar_RT AR') -> @exprim_oct_specA AR' UK EXO_STACK_A EXO_COST_A EXO_FRAMES_A.

  (* [comment removed for export] *)
  Lemma aide_oct_walkA : forall (ra sp gp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m mc : mem) (Σ : rts RT) (st : ap_st bptr) (OW LB : list block) (E : ap_env) (bo : Z * Z)
      (lo : Z) (K : list block) (adr : bptr -> Z) (D : Z) (d : list Z) (OPP OCT : Z) (ras : list Z),
    ap_preA Σ st m OW LB E bo sp lo D2I_OCT_STACK_A (D2I_OCT_COST_A (zlength d)) D2I_OCT_FRAMES_A ->
    uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx AIDE_ENTRY (bv_unsigned ra :: ras) -> ras <> nil ->
    (forall b, In b K -> In b OW) -> (forall b, In b K -> ~ In (blk_id b) (es_ids st ++ env_ids E)) ->
    payload_okA m LB D d -> (forall b, In b LB -> adr (blk_id b) = blk_addr b) ->
    cellA_in LB OPP 8 -> OPP mod 8 = 0 -> (d = [] \/ OPP + 8 <= D \/ D + zlength d <= OPP) -> rw_cells ctasegs m OPP [C8 (wz D)] ->
    cellA_in LB OCT 8 -> OCT mod 8 = 0 -> (d = [] \/ OCT + 8 <= D \/ D + zlength d <= OCT) -> rw_cells ctasegs m OCT [C8 (wz 0)] ->
    (OPP + 8 <= OCT \/ OCT + 8 <= OPP) ->
    munch [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m mc -> wmono ctasegs m mc -> mem_inv ctasegs mc -> stk ctasegs mc lo (bv_unsigned sp) ->
    implAp (d2i_octet d (zlength d) st) Σ
           (d2i_octet_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB E lo m K (D2I_OCT_COST_A (zlength d)) adr OPP OCT)
           (MS (mkR ra sp gp (wz TP_A) t0 t1 t2 s0 s1 (wz OCT) (wz OPP) (wz (zlength d)) (wz ITEM_OCTET_A) (wz 0) (wz 0) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz AIDE_ENTRY) fc None mc (seg_rom ctasegs)).
  Proof.
    intros until ras. intros PRE0 UW CTX NE KOW KIDS PAY ADR COPP ALO DOD HOPP COCT ALV DVD HPV DOV MUc WMc MIc STc.
    pose proof PRE0 as (HEAP & AS & IDS & DC & ST & CEIL & LOSP & TOP & AL16 & MI & CRED & FRM).
    pose proof (AH_ceil _ _ _ _ HEAP) as (CE1 & CE2 & CE3). unfold SEGTOP_A, STACK_WIN, SHHI, USTACK_TOP in CE1, CE2, CE3.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    assert (LO0 : 0 <= lo) by (clear - ST; destruct ST as [H _]; exact H).
    pose proof exo_budgets as (EXS & EXF & EXC).
    assert (EF : D2I_OCT_FRAMES_A = 8 /\ INTERN_OCT_STACK_A = 67744 /\ D2I_OCT_STACK_A = 67920 /\ GETOBJ_ERR_COST_A = 13).
    { unfold D2I_OCT_FRAMES_A, D2I_OCT_STACK_A, INTERN_OCT_STACK_A, AIDE_FRAME. rewrite EXS, EXF. repeat split; reflexivity. }
    destruct EF as (EF8 & EIS & EDS & EC13). rewrite EF8 in FRM. rewrite EDS in LOSP.
    assert (EXC0 : 0 <= EXO_COST_A (zlength d)) by (rewrite EXC; unfold zlength; clear; lia).
    unfold D2I_OCT_COST_A, INTERN_OCT_COST_A in CRED. rewrite EC13 in CRED.
    destruct COPP as (bq & Hbq & BQ1 & BQ2). pose proof (AH_range_gen _ _ _ _ bq HEAP (in_or_app _ _ _ (or_intror Hbq))) as (BQ3 & _ & _ & BQ4 & BQ5).
    destruct COCT as (bv & Hbv & BV1 & BV2). pose proof (AH_range_gen _ _ _ _ bv HEAP (in_or_app _ _ _ (or_intror Hbv))) as (BV3 & _ & _ & BV4 & BV5).
    pose proof PAY as (HB & DF & D0 & D63 & D26 & HBL).
    assert (EOCT : bv_unsigned (Z_to_bv 64 OCT) = OCT) by (apply unsigned_lit; clear - BV1 BV2 BV3 BV4 CE3; unfold BnHeapA.ACEIL in *; lia).
    (* [comment removed for export] *)
    pose proof (agree_on_of_munch_nw _ _ _ MUc) as AGc.
    assert (HEAPc : AHEAP Σ OW LB mc).
    { eapply (AH_frame Σ OW LB m mc _ HEAP MUc WMc). constructor; [left; cbn [fst snd]; clear - CEIL LOSP TOP; unfold USTACK_TOP in *; lia| constructor]. }
    assert (AGLc : agree_on (lib_addr OW) m mc).
    { eapply agree_on_mono; [exact AGc|]. intros a [HS|(b & Hb & Hr)]; cbn [outside fst snd].
      - pose proof (LIBW_S_A a HS) as HA. unfold LIBW_A in HA. cbn [rin_ivs fst snd] in HA. clear - HA CE1 CEIL LOSP. unfold BnHeapA.ACEIL in *. lia.
      - pose proof (AH_range_gen _ _ _ _ b HEAP (in_or_app _ _ _ (or_introl Hb))) as (_ & _ & _ & R3 & _). clear - Hr R3 CEIL LOSP. lia. }
    assert (AGCc : agree_on (aclient_addr LB (bv_unsigned sp)) m mc).
    { eapply agree_on_mono; [exact AGc|]. intros a [H1|[H1|(b & Hb & Hr)]]; cbn [outside fst snd].
      - clear - H1. lia.
      - pose proof (client_static_lowA a H1) as Ha. unfold SEGTOP_A in Ha. clear - Ha CE1 CEIL LOSP. unfold BnHeapA.ACEIL in *. lia.
      - pose proof (AH_range_gen _ _ _ _ b HEAP (in_or_app _ _ _ (or_intror Hb))) as (_ & _ & _ & R3 & _). clear - Hr R3 CEIL LOSP. lia. }
    assert (AGF0 : agree_on (aclient_addr (OW ++ LB) (bv_unsigned sp)) m mc).
    { intros a Hr Ha. destruct Ha as [H1|[H1|(b & Hb & Hrg)]]; [apply (AGCc a Hr); left; exact H1| apply (AGCc a Hr); right; left; exact H1|].
      apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [apply (AGLc a Hr); right; exists b; split; [exact Hb| exact Hrg]| apply (AGCc a Hr); right; right; exists b; split; [exact Hb| exact Hrg]]. }
    pose proof AS as (_ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & OD)).
    assert (PREc : ap_preA Σ st mc OW LB E bo sp lo D2I_OCT_STACK_A (1 + (EXO_COST_A (zlength d) + 13)) D2I_OCT_FRAMES_A).
    { unfold ap_preA. split; [exact HEAPc|]. split; [exact (ap_state_agree _ _ _ _ _ _ AS AGLc)|]. split; [exact IDS|]. split; [exact (data_cells_agree _ _ _ _ DC AGLc OD)|].
      split; [exact STc|]. split; [exact CEIL|]. split; [rewrite EDS; exact LOSP|]. split; [exact TOP|]. split; [exact AL16|]. split; [exact MIc|]. split; [exact CRED| rewrite EF8; exact FRM]. }
    apply (rw_cells_agree _ _ _ _ _ AGc) in HOPP; [| intros a Ha; cbn in Ha; cbn [outside fst snd]; clear - Ha BQ1 BQ2 BQ4 CEIL LOSP; lia].
    apply (rw_cells_agree _ _ _ _ _ AGc) in HPV; [| intros a Ha; cbn in Ha; cbn [outside fst snd]; clear - Ha BV1 BV2 BV4 CEIL LOSP; lia].
    assert (HB' : d = [] \/ exists bd, In bd LB /\ blk_addr bd <= D /\ D + zlength d <= blk_addr bd + blk_size bd /\ bytes_at ctasegs mc D (to_bytes d)).
    { destruct HBL as [E0|(bd & Hbd & BD1 & BD2)]; [left; exact E0| right]. exists bd. split; [exact Hbd|]. split; [exact BD1|]. split; [exact BD2|].
      apply (bytes_at_agree _ _ _ _ _ AGCc) in HB; [exact HB|]. intros a Ha. right; right. exists bd. split; [exact Hbd| unfold to_bytes in Ha; rewrite length_map in Ha; unfold zlength in BD2; clear - Ha BD1 BD2; lia]. }
    (* [comment removed for export] *)
    unfold MallocRep.wz. intros X Φ Dl SAFE LINK.
    eapply (aide_pro_cps _) with (lo := lo) (OW := OW) (LB := LB);
      [exact HEAPc| exact STc| exact CEIL| unfold AIDE_FRAME, RT_STACK; rewrite EDS in *; clear - LOSP; lia| exact TOP| exact AL16| exact MIc| reflexivity
      | cbn [length]; rewrite EF8 in *; clear - FRM; lia| clear - CRED EXC0; lia|].
    intros Σ1 m3 f spa g junk gj ra' t0' t1' t2' a3' a4' a5' a6' t3' t4' t5' t6' F' fc' j0 j8 jf24 jf32 jf64 jf104
           HEAP3 FRESH GEO CR1 EL1 ST3 MI3 AGF FRL FRH FRF FRS SPA32 SPAL SPAH GSZ SAVJ.
    eapply (@implAp_elim (push AR f 1) _ (d2i_octet d (zlength d) st)); [| exact SAFE| exact LINK| exact EL1].
    pose proof GEO as (G1 & G2 & G3 & G4 & G5). change (fs_size 1) with 128 in G3, G5. unfold SEGTOP_A in G4.
    assert (ESPA : bv_unsigned (Z_to_bv 64 spa) = spa) by (apply unsigned_lit; clear - LO0 CEIL LOSP SPAL SPAH SPR; lia).
    assert (F8 : f mod 8 = 0) by (clear - G2; Z.div_mod_to_equations; lia).
    assert (SHR : 2147450880 <= shad f /\ shad f + 16 <= 17594333495296).
    { unfold shad, SHB. pose proof (Z.div_pos f 8 ltac:(clear - G1; lia) ltac:(clear; lia)).
      assert (f / 8 + 16 <= 2 ^ 44) by (assert (f / 8 < 2 ^ 44 - 16); [apply Z.div_lt_upper_bound; clear - G3 CE3; plia | clear - H0; lia]). clear - H H0. lia. }
    assert (FSH : f + 120 <= shad f \/ shad f + 16 <= f) by (pose proof G5 as G5c; clear - G5c SHR; unfold shad, SHB in *; destruct G5c as [G5c|G5c]; [left | right]; Z.div_mod_to_equations; lia).
    assert (OFFLB : forall b, In b LB -> off_fr f 1 b) by (intros b Hb; apply FRESH; apply in_or_app; right; exact Hb).
    (* [comment removed for export] *)
    destruct (bptr_fresh (map blk_id (OW ++ LB))) as [qt Hqt].
    assert (HEAPt : @BnHeapA.AHEAP (push AR f 1) Σ1 OW ((qt, f + 32, 32) :: LB) m3).
    { apply (@frame_obj_open (push AR f 1) Σ1 OW LB m3 f 1%nat qt (f + 32) 32 (or_introl eq_refl) HEAP3); [clear; lia| change (fs_size 1) with 128; clear; lia| clear; lia| | exact Hqt|].
      - eapply (acc_of_shadow_cells m3 (shad f) _ 4 (f + 32) 32 FRS); [clear - F8; Z.div_mod_to_equations; lia| clear - G1; lia| clear; lia| unfold shad; clear - F8; Z.div_mod_to_equations; lia| cbn; clear; lia| reflexivity].
      - intros b Hb. pose proof (OFFLB b Hb) as O. unfold off_fr in O. change (fs_size 1) with 128 in O. unfold blk_apart. cbn [blk_addr blk_size fst snd]. clear - O. lia. }
    destruct (bptr_fresh (map blk_id (OW ++ (qt, f + 32, 32) :: LB))) as [qv Hqv].
    assert (HEAPv : @BnHeapA.AHEAP (push AR f 1) Σ1 OW ((qv, f + 96, 8) :: (qt, f + 32, 32) :: LB) m3).
    { apply (@frame_obj_open (push AR f 1) Σ1 OW _ m3 f 1%nat qv (f + 96) 8 (or_introl eq_refl) HEAPt); [clear; lia| change (fs_size 1) with 128; clear; lia| clear; lia| | exact Hqv|].
      - eapply (acc_of_shadow_cells m3 (shad f) _ 12 (f + 96) 8 FRS); [clear - F8; Z.div_mod_to_equations; lia| clear - G1; lia| clear; lia| unfold shad; clear - F8; Z.div_mod_to_equations; lia| cbn; clear; lia| reflexivity].
      - intros b [<-|Hb]; [unfold blk_apart; cbn [blk_addr blk_size fst snd]; clear; lia|].
        pose proof (OFFLB b Hb) as O. unfold off_fr in O. change (fs_size 1) with 128 in O. unfold blk_apart. cbn [blk_addr blk_size fst snd]. clear - O. lia. }
    clear HEAPt.
    assert (INL : forall b, In b LB -> In b ((qv, f + 96, 8) :: (qt, f + 32, 32) :: LB)) by (intros b Hb; right; right; exact Hb).
    (* [comment removed for export] *)
    apply (rw_cells_agree _ _ _ _ _ AGF) in HOPP; [| intros a Ha; cbn in Ha; right; right; exists bq; split; [apply in_or_app; right; exact Hbq| clear - Ha BQ1 BQ2; lia]].
    apply (rw_cells_agree _ _ _ _ _ AGF) in HPV; [| intros a Ha; cbn in Ha; right; right; exists bv; split; [apply in_or_app; right; exact Hbv| clear - Ha BV1 BV2; lia]].
    pose proof (munch_refl [(f + 32, f + 64)]%Z m3) as MU. pose proof (wmono_refl ctasegs m3) as WM.
    pose proof (pro_closeA Σ st mc OW LB E bo sp lo _ _ _ f 1%nat Σ1 m3 spa 128 PREc HEAP3 ST3 MI3 AGF CR1 SPA32
                  ltac:(clear - SPAL; lia) ltac:(clear - SPAH; lia) ltac:(clear; lia) ltac:(rewrite EDS; clear; lia)
                  ltac:(clear - EXC0; lia) ltac:(rewrite EF8; clear; lia)) as PRE3.
    freeze HOPP. freeze HPV. freeze FRS. hide BQ5. hide BV5. hide G5.
    unfold AIDE_BODY, MallocRep.wz. apply implAp_from_evt.
    step. if_cases KO; zc KO; [| exfalso; revert KO; rewrite ?EOCT; clear - BV3 BV1; lia]. clear KO.
    sbstep.
    step. step. step. step. step. step. step. step. step. step.
    name_mem m4.
    match goal with H : munch _ m3 m4 |- _ => rename H into MU4 end. match goal with H : wmono ctasegs m3 m4 |- _ => rename H into WM4 end.
    match goal with H : stk ctasegs m4 lo _ |- _ => rename H into ST4 end. match goal with H : mem_inv ctasegs m4 |- _ => rename H into MI4 end.
    apply evt_done. fold INTERN_A.
    (* [comment removed for export] *)
    pose proof (agree_on_of_munch_nw _ _ _ MU4) as AG4.
    assert (HEAP4 : @BnHeapA.AHEAP (push AR f 1) Σ1 OW ((qv, f + 96, 8) :: (qt, f + 32, 32) :: LB) m4).
    { eapply (@AH_frame (push AR f 1)); [exact HEAPv| exact MU4| exact WM4|]. constructor; [| constructor].
      right; right. exists (qt, f + 32, 32). split; [apply in_or_app; right; right; left; reflexivity| cbn [blk_addr blk_size fst snd]; clear; lia]. }
    assert (AGL4 : agree_on (lib_addr OW) m3 m4).
    { eapply agree_on_mono; [exact AG4|]. intros a [HS|(b & Hb & Hr)]; cbn [outside fst snd].
      - pose proof (LIBW_S_A a HS) as HA. unfold LIBW_A in HA. cbn [rin_ivs fst snd] in HA. clear - HA G4. lia.
      - pose proof (FRESH b (in_or_app _ _ _ (or_introl Hb))) as O. unfold off_fr in O. change (fs_size 1) with 128 in O. clear - Hr O. lia. }
    assert (PRE4 : @ap_preA (push AR f 1) Σ1 st m4 OW ((qv, f + 96, 8) :: (qt, f + 32, 32) :: LB) E bo (Z_to_bv 64 spa) lo INTERN_OCT_STACK_A (INTERN_OCT_COST_A (zlength d)) EXO_FRAMES_A).
    { eapply (@ap_preA_weaken (push AR f 1)); [eapply (@ap_preA_memA (push AR f 1)); [exact PRE3| exact HEAP4| exact AGL4| rewrite ESPA; exact ST4| exact MI4]| | |].
      - rewrite EDS, EIS. clear; lia.
      - unfold INTERN_OCT_COST_A. rewrite EC13. clear - EXC0; lia.
      - rewrite EF8, EXF. clear; lia. }
    unfold frozen in HOPP, HPV.
    apply (rw_cells_agree _ _ _ _ _ AG4) in HOPP; [| intros a Ha; cbn in Ha; cbn [outside fst snd]; pose proof (OFFLB bq Hbq) as O; unfold off_fr in O; change (fs_size 1) with 128 in O; clear - Ha O BQ1 BQ2; lia].
    apply (rw_cells_agree _ _ _ _ _ AG4) in HPV; [| intros a Ha; cbn in Ha; cbn [outside fst snd]; pose proof (OFFLB bv Hbv) as O; unfold off_fr in O; change (fs_size 1) with 128 in O; clear - Ha O BV1 BV2; lia].
    assert (PAY4 : payload_okA m4 ((qv, f + 96, 8) :: (qt, f + 32, 32) :: LB) D d).
    { split; [| split; [exact DF|]; split; [exact D0|]; split; [exact D63|]; split; [exact D26|]].
      - destruct HB' as [->|(bd & Hbd & BD1 & BD2 & HBc)]; [cbn [to_bytes map]; apply bytes_at_nil; clear - D0 D63; unfold zlength in *; cbn in *; lia|].
        apply (bytes_at_agree _ _ _ _ _ AGF) in HBc; [| intros a Ha; right; right; exists bd; split; [apply in_or_app; right; exact Hbd| unfold to_bytes in Ha; rewrite length_map in Ha; unfold zlength in BD2; clear - Ha BD1 BD2; lia]].
        apply (bytes_at_agree _ _ _ _ _ AG4) in HBc; [exact HBc|]. intros a Ha. cbn [outside fst snd]. pose proof (OFFLB bd Hbd) as O. unfold off_fr in O. change (fs_size 1) with 128 in O.
        unfold to_bytes in Ha. rewrite length_map in Ha. unfold zlength in BD2. clear - Ha O BD1 BD2. lia.
      - destruct HB' as [E0|(bd & Hbd & BD1 & BD2 & _)]; [left; exact E0| right]. exists bd. split; [exact (INL bd Hbd)| split; [exact BD1| exact BD2]]. }
    (* [comment removed for export] *)
    lazymatch type of FRF with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: nil) =>
      change (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: c8 :: nil) with ([c0; c1; c2; c3] ++ [c4; c5] ++ [c6] ++ [c7] ++ [c8]) in FRF end.
    apply rw_cells_app in FRF as [_ FRF]. apply rw_cells_app in FRF as [HTLC FRF]. apply rw_cells_app in FRF as [_ FRF]. apply rw_cells_app in FRF as [HPT _].
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add app length] in HTLC, HPT.
    replace (f + Z.of_nat 32) with (f + 32) in HTLC by (clear; lia).
    pose proof BQ5 as BQ5'. unfold hidden in BQ5'. pose proof BV5 as BV5'. unfold hidden in BV5'.
    (* [comment removed for export] *)
    set (adr1 := fun p : bptr => if bptr_eqb p qv then f + 96 else if bptr_eqb p qt then f + 32 else adr p).
    assert (NQV : forall b, In b LB -> blk_id b <> qv) by (intros b Hb E0; apply Hqv; rewrite <- E0; rewrite map_app; apply in_or_app; right; right; apply in_map; exact Hb).
    assert (NQT : forall b, In b LB -> blk_id b <> qt) by (intros b Hb E0; apply Hqt; rewrite <- E0; rewrite map_app; apply in_or_app; right; apply in_map; exact Hb).
    assert (NVT : qv <> qt) by (intros E0; apply Hqv; rewrite E0; rewrite map_app; apply in_or_app; right; left; reflexivity).
    assert (ADR1 : forall b, In b ((qv, f + 96, 8) :: (qt, f + 32, 32) :: LB) -> adr1 (blk_id b) = blk_addr b).
    { intros b [<-|[<-|Hb]]; unfold adr1; cbn [blk_id blk_addr fst snd].
      - rewrite bptr_eqb_refl. reflexivity.
      - rewrite (bptr_eqb_neq qt qv ltac:(intros E0; apply NVT; symmetry; exact E0)), bptr_eqb_refl. reflexivity.
      - rewrite (bptr_eqb_neq _ _ (NQV b Hb)), (bptr_eqb_neq _ _ (NQT b Hb)). exact (ADR b Hb). }
    pose proof (@intern_oct_walkA (push AR f 1) UK BE STRCPY (HEXPRIM (push AR f 1) STRCPY)) as HIN. unfold intern_oct_specA in HIN.
    eapply implAp_post.
    { eapply HIN with (K := K) (adr := adr1) (OPP := OPP) (PV := OCT) (TLC := f + 32) (j31 := drop 1 jf32); rewrite ?ESPA;
        [exact PRE4| reflexivity
        | eapply (uw_call m m4 spa (bv_unsigned sp) 16 [] (bv_unsigned ra) (bv_unsigned s0) ras);
          [ exact UW
          | eapply agree_on_trans; [eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MUc)|]; intros a Ha; cbn [outside fst snd]; clear - Ha; lia
            | eapply agree_on_trans; [eapply agree_on_mono; [exact AGF|]; intros a Ha; left; exact Ha
              | eapply agree_on_mono; [exact AG4|]; intros a Ha; cbn [outside fst snd]; clear - Ha G3 CEIL LOSP SPAL; plia]]
          | reflexivity | clear - SPAH; lia | uchk_open; clear - AL16; Z.div_mod_to_equations; lia | clear - TOP; unfold USTACK_TOP in *; lia
          | apply bv_unsigned_in_range | rewrite !Z_to_bv_bv_unsigned; cbn [app]; exact FRH ]
        | rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_aide_intern CTX)
        | apply cons_ne| exact KOW| exact KIDS| exact ADR1
        | | reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity].
      (* [comment removed for export] *)
      split; [exact PAY4|].
      split; [exists bq; split; [exact (INL bq Hbq)| split; [exact BQ1| exact BQ2]]|].
      split; [exists bv; split; [exact (INL bv Hbv)| split; [exact BV1| exact BV2]]|].
      split; [exists (qt, f + 32, 32); split; [right; left; reflexivity| cbn; clear; lia]|].
      split; [exact ALO|]. split; [exact ALV|]. split; [clear - F8; unfold al8 in *; Z.div_mod_to_equations; lia|].
      split; [exact DOV|].
      split; [pose proof (OFFLB bq Hbq) as O; unfold off_fr in O; change (fs_size 1) with 128 in O; clear - O BQ1 BQ2; lia|].
      split; [pose proof (OFFLB bv Hbv) as O; unfold off_fr in O; change (fs_size 1) with 128 in O; clear - O BV1 BV2; lia|].
      split; [exact DOD|]. split; [exact DVD|].
      split; [destruct HB' as [E0|(bd & Hbd & BD1 & BD2 & _)]; [left; exact E0| right]; pose proof (OFFLB bd Hbd) as O; unfold off_fr in O; change (fs_size 1) with 128 in O; clear - O BD1 BD2; lia|].
      split; [exact HOPP|]. split; [exact HPV| exact HTLC]. }
    cbv beta. intros [res st'] Σ' ms' PO. unfold exprim_oct_postA in PO. cbn [fst snd] in PO. unfold MallocRep.wz in PO. rewrite ?ESPA in PO.
    destruct PO as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & F5 & fc5 & m5 & OW5 & bo5 & adr5 & NEW & ov & jt & -> & PRE5 & AXP5 & CRED5 & KEPT5 & ADR5 & FRESH5 & LBOK5 & HOPP5 & HTLC5 & RES5).
    unfold AIDE_INTERN_RA. rewrite (ret_pc_even 0x24048c) by (clear; lia).
    pose proof PRE5 as (HEAP5 & AS5 & IDS5 & DC5 & ST5 & _ & _ & _ & _ & MI5 & CR50 & _). cbn [ar_RT push amb] in CR50, CRED5. rewrite ESPA in ST5.
    (* [comment removed for export] *)
    assert (AXS : forall A0 cs, rw_cells ctasegs m4 A0 cs -> spa <= A0 -> A0 + Z.of_nat (cells_size cs) <= USTACK_TOP -> rw_cells ctasegs m5 A0 cs).
    { intros A0 cs HC H1 H2. eapply rw_cells_agree; [exact AXP5| exact HC|].
      intros a Ha. split; [| left; clear - Ha H1 H2; lia]. unfold LIBW_A. cbn [rin_ivs fst snd app]. clear - Ha H1 H2 BQ2 BQ4 BV2 BV4 G3 CE1 CEIL LOSP SPAL. plia. }
    apply AXS in FRL; [| clear; lia| cbn [cells_size csize Nat.add]; rewrite ?Nat2Z.inj_add; clear - GSZ SPAH TOP; unfold USTACK_TOP in *; lia].
    apply AXS in FRH; [| clear - SPAH; lia| cbn; clear - TOP; unfold USTACK_TOP in *; lia]. clear AXS.
    (* [comment removed for export] *)
    assert (OFFN : forall b, In b NEW -> off_fr f 1 b).
    { intros b Hb. eapply (aide_lbokA_off f 1%nat Σ' OW5 _ m5 b HEAP5); [apply in_or_app; right; apply in_or_app; left; exact Hb| exact (proj1 (Forall_forall _ _) LBOK5 b Hb)]. }
    assert (HEAPP : @BnHeapA.AHEAP (push AR f 1) Σ' OW5 ((qv, f + 96, 8) :: (qt, f + 32, 32) :: (NEW ++ LB)) m5).
    { eapply AHEAP_permLB; [exact HEAP5|]. symmetry. eapply Permutation_trans; [apply perm_skip; apply Permutation_middle| apply Permutation_middle]. }
    assert (HEAPk : @BnHeapA.AHEAP (push AR f 1) Σ' OW5 (NEW ++ LB) m5).
    { eapply (@frame_obj_close (push AR f 1)); [left; reflexivity| |].
      - eapply (@frame_obj_close (push AR f 1)); [left; reflexivity| exact HEAPP|]. unfold in_fr. cbn [blk_addr blk_size fst snd]. change (fs_size 1) with 128. clear; lia.
      - unfold in_fr. cbn [blk_addr blk_size fst snd]. change (fs_size 1) with 128. clear; lia. }
    assert (OFFNL : forall b, In b (NEW ++ LB) -> off_fr f 1 b) by (intros b Hb; apply in_app_iff in Hb; destruct Hb as [Hb|Hb]; [exact (OFFN b Hb)| exact (OFFLB b Hb)]).
    (* [comment removed for export] *)
    pose proof (proj2 (@AH_acc (push AR f 1) _ _ _ _ bv HEAP5 ltac:(apply in_or_app; right; apply in_or_app; right; right; right; exact Hbv))) as ACCV.
    pose proof (@AH_offsh (push AR f 1) _ _ _ _ bv HEAP5 ltac:(apply in_or_app; right; apply in_or_app; right; right; right; exact Hbv)) as ROV.
    pose proof G5 as G5'. unfold hidden in G5'.
    assert (OFFW : offshW ([] : list (Z * Z))) by exact I.
    pose proof (munch_refl ([] : list (Z * Z)) m5) as MU5. pose proof (wmono_refl ctasegs m5) as WM5.
    freeze HOPP5.
    assert (EXITK : forall (rv : word) (x11 : word),
      match res with Some os => rv = Z_to_bv 64 (adr5 (os_blk os)) | None => rv = Z_to_bv 64 0 end ->
      @implAp (push AR f 1) _ (ARet (res, st')) Σ' (d2i_octet_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB E lo m K (D2I_OCT_COST_A (zlength d)) adr OPP OCT)
        (MS (mkR (Z_to_bv 64 2360460) (Z_to_bv 64 spa) gp (Z_to_bv 64 TP_A) u0 u1 u2 sp (Z_to_bv 64 spa) rv x11 v2 v3 v4 v5 v6 v7
                 (Z_to_bv 64 f) (Z_to_bv 64 0) (Z_to_bv 64 OCT) (Z_to_bv 64 0) (Z_to_bv 64 ITEM_OCTET_A) (Z_to_bv 64 (zlength d)) (Z_to_bv 64 OPP) (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) (Z_to_bv 64 SHB) u3 u4 u5 u6)
            F5 (Z_to_bv 64 AIDE_EXIT) fc5 None m5 (seg_rom ctasegs))).
    { intros rv x11 RV.
      unfold AIDE_EXIT. intros X2 Φ2 D2 SAFE2 LINK2.
      eapply (@aide_epi_cps AR _) with (lo := lo) (LB := NEW ++ LB) (gj := gj) (hrest := []);
        [exact HEAPk| exact OFFNL| exact ST5| exact CEIL| clear - CEIL LOSP SPAL; lia| exact TOP| clear - SPAL; lia| clear - SPAH; lia
        | exact GSZ| exact SAVJ| exact MI5| exact FRL| exact FRH| reflexivity|].
      intros Σ'' m'' x11' HEAP'' CR'' EL'' ST'' MI'' AG''.
      eapply (@implAp_elim (push AR f 1) _ (ARet (res, st'))); [| exact SAFE2| exact LINK2| exact EL''].
      apply implAp_ret.
      (* [comment removed for export] *)
      assert (AGL : agree_on (lib_addr OW5) m5 m'') by (eapply agree_on_mono; [exact AG''|]; intros a Ha; exact (lib_addr_aclient OW5 (NEW ++ LB) spa a Ha)).
      pose proof AS5 as (_ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & OD5)).
      unfold d2i_octet_postA. cbn [fst snd]. unfold frozen in HOPP5.
      do 16 eexists. exists m'', OW5, bo5, adr5, NEW, ov, (match res with Some os => Z_to_bv 64 (adr5 (os_blk os)) | None => Z_to_bv 64 0 end).
      split; [destruct res as [os|]; rewrite RV; reflexivity|].
      split.
      { unfold ap_preA. split; [exact HEAP''|]. split; [eapply ap_state_rt; [exact AS5| exact AG'']|]. split; [exact IDS5|].
        split; [eapply data_cells_rt; [exact AS5| exact DC5| exact AG'']|]. split; [exact ST''|]. split; [exact CEIL|]. split; [clear - LOSP; lia|].
        split; [exact TOP|]. split; [exact AL16|]. split; [exact MI''|].
        split; [pose proof (af_credit_nonneg RT (@ar_AF AR) Σ'' m'' (AH_art _ _ _ _ HEAP'')) as CNN; clear - CNN; lia| clear - FRM; lia]. }
      split.
      { unfold ax_pres.
        eapply agree_on_trans; [eapply agree_on_mono; [exact AGCc|]; intros a [_ Ha]; exact Ha|].
        eapply agree_on_trans; [eapply agree_on_mono; [exact AGF|]; intros a [_ Ha]; eapply acl_sub; [| | exact Ha]; [intros b Hb; apply in_or_app; right; exact Hb| clear; lia]|].
        eapply agree_on_trans; [eapply agree_on_mono; [exact AG4|]|].
        { intros a [_ Ha]. cbn [outside fst snd]. destruct Ha as [H1|[H1|(b & Hb & Hr)]].
          - clear - H1 G3 CEIL LOSP SPAL. plia.
          - pose proof (client_static_lowA a H1) as Hs. unfold SEGTOP_A in Hs. clear - Hs G4. lia.
          - pose proof (OFFLB b Hb) as O. unfold off_fr in O. change (fs_size 1) with 128 in O. clear - Hr O. lia. }
        eapply agree_on_trans; [eapply agree_on_mono; [exact AXP5|]|].
        { intros a [HX Ha]. cbn [rin_ivs fst snd] in HX. split.
          - unfold LIBW_A in *. cbn [rin_ivs fst snd app] in *. destruct Ha as [H1|[H1|(b & Hb & Hr)]].
            + clear - HX H1 G3 CEIL LOSP SPAL. plia.
            + pose proof (client_static_lowA a H1) as Hs. unfold SEGTOP_A in Hs. clear - HX Hs G4. lia.
            + pose proof (OFFLB b Hb) as O. unfold off_fr in O. change (fs_size 1) with 128 in O. clear - HX Hr O. lia.
          - eapply acl_sub; [| | exact Ha]; [exact INL| clear - SPAH; lia]. }
        eapply agree_on_mono; [exact AG''|]. intros a [_ Ha]. eapply acl_sub; [| | exact Ha]; [intros b Hb; apply in_or_app; right; apply in_or_app; right; exact Hb| clear - SPAH; lia]. }
      split; [unfold D2I_OCT_COST_A, INTERN_OCT_COST_A in *; rewrite EC13 in *; clear - CR1 CRED5 CR''; lia|].
      split.
      { eapply (blocks_kept_post K st' OW5 (NEW ++ LB)); [| exact AG'']. eapply (blocks_kept_pre K st' OW OW5 LB (bv_unsigned sp) m m4); [exact KOW| | exact KEPT5].
        eapply agree_on_trans; [exact AGF0|]. eapply agree_on_trans; [exact AGF|].
        intros a Hr Ha. apply (AG4 a Hr). cbn [outside fst snd]. destruct Ha as [H1|[H1|(b & Hb & Hrg)]].
        - clear - H1 G3 CEIL LOSP SPAL. plia.
        - pose proof (client_static_lowA a H1) as Hs. unfold SEGTOP_A in Hs. clear - Hs G4. lia.
        - pose proof (FRESH b Hb) as O. unfold off_fr in O. change (fs_size 1) with 128 in O. clear - Hrg O. lia. }
      split; [intros b Hb; rewrite (ADR5 b (INL b Hb)); unfold adr1; rewrite (bptr_eqb_neq _ _ (NQV b Hb)), (bptr_eqb_neq _ _ (NQT b Hb)); reflexivity|].
      split; [intros b Hb Hin; apply (FRESH5 b Hb); rewrite map_app in Hin |- *; apply in_app_iff in Hin; apply in_or_app; destruct Hin as [Hin|Hin]; [left; exact Hin| right; right; right; exact Hin]|].
      split; [eapply Forall_impl; [| exact LBOK5]; intros b Hb; exact (aide_lbokA_pop _ _ _ Hb)|].
      split; [eapply rw_cells_agree; [exact AG''| exact HOPP5| intros a Ha; cbn in Ha; right; right; exists bq; split; [apply in_or_app; right; apply in_or_app; right; exact Hbq| clear - Ha BQ1 BQ2; lia]]|].
      destruct res as [os|].
      - destruct RES5 as (ENEW & OREP & HPV5). split; [| split; [exact ENEW| split; [| reflexivity]]].
        + eapply rw_cells_agree; [exact AG''| exact HPV5| intros a Ha; cbn in Ha; right; right; exists bv; split; [apply in_or_app; right; apply in_or_app; right; exact Hbv| clear - Ha BV1 BV2; lia]].
        + eapply octet_repA_agree.
          * destruct OREP as (IN & AL & HC & L1 & L2 & L3 & DAT).
            assert (DROP : forall b, In b (OW5 ++ NEW ++ (qv, f + 96, 8) :: (qt, f + 32, 32) :: LB) -> In (blk_id b) (map blk_id NEW) -> In b (OW5 ++ NEW ++ LB)).
            { intros b Hb Hid. apply in_app_iff in Hb. apply in_or_app. destruct Hb as [Hb|Hb]; [left; exact Hb| right].
              apply in_app_iff in Hb. apply in_or_app. destruct Hb as [Hb|[<-|[<-|Hb]]]; [left; exact Hb| exfalso| exfalso| right; exact Hb].
              - apply in_map_iff in Hid. destruct Hid as (b' & E0 & Hb'). apply (FRESH5 b' Hb'). rewrite E0. cbn [blk_id fst]. rewrite map_app. apply in_or_app. right. left. reflexivity.
              - apply in_map_iff in Hid. destruct Hid as (b' & E0 & Hb'). apply (FRESH5 b' Hb'). rewrite E0. cbn [blk_id fst]. rewrite map_app. apply in_or_app. right. right. left. reflexivity. }
            split; [apply DROP; [exact IN| rewrite ENEW; unfold CtSctP.SctStmt.oct_blocks; cbn; left; reflexivity]|].
            split; [exact AL|]. split; [exact HC|]. split; [exact L1|]. split; [exact L2|]. split; [exact L3|].
            destruct (os_data os) as [[dp n]|] eqn:EOD; [| exact DAT]. destruct DAT as (NE' & IN2 & LE & BY). split; [exact NE'|]. split; [| split; [exact LE| exact BY]].
            apply DROP; [exact IN2| rewrite ENEW; unfold CtSctP.SctStmt.oct_blocks; rewrite EOD; cbn; right; left; reflexivity].
          * eapply agree_on_mono; [exact AG''|]. intros a (b & Hb & Hr). right; right. exists b. split; [| exact Hr].
            apply in_app_iff in Hb. apply in_or_app. destruct Hb as [Hb|Hb]; [left; exact Hb| right; exact Hb].
      - destruct RES5 as (ENEW & HPV5). split; [| exact ENEW].
        eapply rw_cells_agree; [exact AG''| exact HPV5| intros a Ha; cbn in Ha; right; right; exists bv; split; [apply in_or_app; right; apply in_or_app; right; exact Hbv| clear - Ha BV1 BV2; lia]]. }
    apply implAp_from_evt. step. destruct res as [os|].
    - destruct RES5 as (ENEW & OREP & HPV5).
      if_false. step. step. apply evt_done. apply (EXITK (Z_to_bv 64 (adr5 (os_blk os)))). reflexivity.
    - destruct RES5 as (-> & HPV0). if_true. step. apply evt_done. apply (EXITK (Z_to_bv 64 0)). reflexivity.
  Qed.

  Local Ltac tramp_tail spv :=
    do 3 step;
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      match goal with FR : rw_cells ctasegs mx _ _, ST : stk ctasegs mx _ _ |- _ => release_frame FR ST (bv_unsigned spv) end end;
    step.

  (* [comment removed for export] *)
  Theorem d2i_octet_walkA : d2i_octet_specA D2I_OCTET_STACK_A D2I_OCTET_COST_A D2I_OCTET_FRAMES_A.
  Proof.
    unfold d2i_octet_specA. intros until OCT.
    intros PRE0 -> UW CTX NE KOW KIDS PAY ADR COPP ALO DOD HOPP COCT ALV DVD HPV DOV -> -> ->.
    pose proof PRE0 as (HEAP & AS & IDS & DC & ST & CEIL & LOSP & TOP & AL16 & MI & CRED & FRM).
    pose proof (AH_ceil _ _ _ _ HEAP) as (CE1 & CE2 & CE3). unfold SEGTOP_A, STACK_WIN, SHHI, USTACK_TOP in CE1, CE2, CE3.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof d2i_oct_budgets as (BS & BF & BC). pose proof exo_budgets as (EXS & EXF & EXC).
    assert (EDS : D2I_OCT_STACK_A = 67920) by (unfold D2I_OCT_STACK_A, INTERN_OCT_STACK_A, AIDE_FRAME; rewrite EXS; reflexivity).
    assert (PRE0' : ap_preA Σ st m OW LB E bo sp lo D2I_OCT_STACK_A (D2I_OCT_COST_A (zlength d)) D2I_OCT_FRAMES_A).
    { eapply ap_preA_weaken; [exact PRE0| exact BS| apply BC; unfold zlength; clear; lia| split; [unfold D2I_OCT_FRAMES_A; rewrite EXF; clear; lia| exact BF]]. }
    pose proof PRE0' as (_ & _ & _ & _ & _ & _ & LOSP' & _). rewrite EDS in LOSP'.
    pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctasegs m) as WM.
    freeze HOPP. freeze HPV. unfold MallocRep.wz.
    apply implAp_from_evt. unfold D2I_ASN1_OCTET_STRING_A.
    carve_frame 16%nat ST. do 4 step. step. zstep. tramp_tail sp.
    unfold ITEM_D2I_A. carve_frame 16%nat ST. do 4 step. step. step. tramp_tail sp.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      match goal with MU' : munch _ ?m0 mx, WM' : wmono ctasegs ?m0 mx, MI' : mem_inv ctasegs mx, ST' : stk ctasegs mx _ _ |- _ =>
        apply evt_done; unfold frozen in HOPP, HPV;
        eapply (implAp_mono _ _ _ _ _ (aide_oct_walkA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m0 mx _ _ _ _ _ _ _ _ _ _ _ _ _ _
                  PRE0' UW (uk_ctx_tail _ _ _ E_itemd2i_tail (uk_ctx_tail _ _ _ E_oct_tail CTX)) NE KOW KIDS PAY ADR COPP ALO DOD HOPP COCT ALV DVD HPV DOV MU' WM' MI' ST'));
        intros r Σ' ms' PO; unfold d2i_octet_postA in PO |- *;
        destruct PO as (y0 & y1 & y2 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & y3 & y4 & y5 & y6 & F2 & fc2 & m2 & OW2 & bo2 & adr2 & NEW & ov & cv & E1 & PRE2 & AXP2 & CRED2 & REST);
        do 16 eexists; exists m2, OW2, bo2, adr2, NEW, ov, cv; split; [exact E1|]; split; [exact PRE2|]; split; [exact AXP2|]; split; [| exact REST];
        pose proof (BC (zlength d) ltac:(unfold zlength; clear; lia)) as BCd; clear - CRED2 BCd; lia
      end end.
  Qed.
End Walk.
End WithRT.
