(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
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
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import RT_iface2 LibKitA ARun BnHeapA BnRepDefs BnRepA ImplA ImplAX BnIfaceA AsStruct RtCallA UnwindA EdgesA UnwindX UnwindRecA W_cryptoA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtFrameA Require Import AFrameKit AFrameCall AFrameTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require Import ApCells.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require W_get_object W_get_object_walk W_check_tlen.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import I_strcpyA ApATac ApATacX ApBImg ApWalkTac ApRepDefs ApRep ApIface ApFrame W_akit W_get_objectA W_check_tlenA W_item_d2i_stmtA W_item_d2i_imgA W_c2i_stmtA W_frkitA Fr_asn1_check_tlen Fr_asn1_d2i_ex_primitive.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require W_get_object_walkA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import W_item_d2i_exA W_item_d2i_tailA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctP Require SctStmt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctA Require Import SctRepA SctStmtA O2iKitA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtColA Require Import ColBudgetA ColDefsA CtlStmtA W_bufmemA W_collectA W_d2iA_stmt W_d2iA_exprim_ctx.
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
Import CtRepP.W_get_object(land_32_cases, go_ret_cases, go_cls_cases, go_tag_range).
Import CtRepP.W_get_object_walk(signed_small, zxb_lit).
Notation go_ret_prim := CtRepP.W_check_tlen.go_ret_prim.
Notation tlc_in := CtRepP.W_check_tlen.tlc_in.
Notation payload_readA := CtRepA.W_get_object_walkA.payload_readA.

Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges} {UR : UnwindRec ASN1_COLLECT_A ASN1_COLLECT_REC_RA 6}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation FR := (@ar_FR AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

(* [comment removed for export] *)
Section Body.
  (* [comment removed for export] *)
  Hypothesis STRCPY : strcpy_icontract RT.
  Hypothesis HCTL : forall AR' : ARun, strcpy_icontract (@ar_RT AR') -> @check_tlen_gen_specA AR' UK.

  (* [comment removed for export] *)
  Variables (STK : Z) (CST : Z -> Z) (FRMb : Z).
  Variables (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word).
  Variables (m : mem) (Σ : rts RT) (st : ap_st bptr) (OW LB : list block) (E : ap_env) (bo : Z * Z) (lo : Z) (K : list block).
  Variables (adr : bptr -> Z) (D : Z) (d : list Z) (OPP PV TLC : Z) (j31 : list byte).
  Variables (f spa : Z) (g : nat) (junk gj : list byte) (Σ1 : rts RT) (m3 : mem).
  Let len := zlength d.
  Let gr := get_object d 0 len.

  (* [comment removed for export] *)
  Hypothesis PRE0 : ap_preA Σ st m OW LB E bo sp lo STK (CST len) FRMb.
  Variable ras : list Z.
  Hypothesis UW : uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras.
  Hypothesis CTX : uk_ctx ADEP_ENTRY (bv_unsigned ra :: ras).
  Hypothesis NE : ras <> nil.
  Hypothesis KOW : forall b, In b K -> In b OW.
  Hypothesis KIDS : forall b, In b K -> ~ In (blk_id b) (es_ids st ++ env_ids E).
  Hypothesis ADR : forall b, In b LB -> adr (blk_id b) = blk_addr b.
  Hypothesis CELLS : d2i_cells_okA m LB D d OPP PV TLC j31.
  Hypothesis LEN1 : 0 < len.

  (* [comment removed for export] *)
  Hypothesis HEAP3 : @BnHeapA.AHEAP (push AR f 2) Σ1 OW LB m3.
  Hypothesis FRESH : forall b, In b (OW ++ LB) -> off_fr f 2 b.
  Hypothesis GEO : @fr_geo (push AR f 2) f 2.
  Hypothesis CR1 : rt_credit RT Σ1 = rt_credit RT Σ - 1.
  Hypothesis ST3 : stk ctasegs m3 lo spa.
  Hypothesis MI3 : mem_inv ctasegs m3.
  Hypothesis AGF : agree_on (aclient_addr (OW ++ LB) (bv_unsigned sp)) m m3.
  Hypothesis SPA32 : spa mod 32 = 0.
  Hypothesis SPAL : bv_unsigned sp - 272 <= spa.
  Hypothesis SPAH : spa <= bv_unsigned sp - 256.
  Hypothesis GSZ : Z.of_nat g = bv_unsigned sp - spa - 168.
  Hypothesis SAVJ : junk = gj ++ cells_bytes [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1].
  (* [comment removed for export] *)
  Hypothesis STKB : ADEP_FRAME + CHECK_TLEN_STACK_A + 6 * 176 <= STK.
  Hypothesis FRMBb : 1 + CHECK_TLEN_FRAMES_A <= FRMb.
(* [comment removed for export] *)

  Local Ltac ctx := pose proof (exo_ctx STK CST FRMb sp m Σ st OW LB E bo lo D d OPP PV TLC j31 f spa PRE0 CELLS LEN1 FRESH GEO SPAL SPAH STKB)
                      as (DF & D0 & D63 & D26 & CL1 & CL2 & CL3 & CEIL & LO0 & LO & ESS & TOP & SPR & DLEN & ESPA & G1 & G2 & G3 & G4 & Ef & G5 & FSH & SHR1 & SHR2
                          & (bd & Hbd & BD1 & BD2 & BD3 & BD4 & BD5 & OD) & (bq & Hbq & BQ1 & BQ2 & BQ3 & BQ4 & BQ5 & OQ)
                          & (bv & Hbv & BV1 & BV2 & BV3 & BV4 & BV5 & OV) & (bt & Hbt & BT1 & BT2 & BT3 & BT4 & BT5 & OT));
                    unfold off_fr in OD, OQ, OV, OT; change (fs_size 2) with 256 in OD, OQ, OV, OT; cbn [blk_addr blk_size fst snd] in OD, OQ, OV, OT.
  Local Notation POST := (exprim_oct_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB E lo m K (CST len) adr OPP PV TLC).
  Local Notation linv := (exo_inv STK CST FRMb sp LB E lo K D d OPP PV TLC f spa Σ1).

  (* [comment removed for export] *)
  Lemma exo_lbokA_pop : forall f' k b, @lbokA (push AR f' k) b -> @lbokA AR b.
  Proof.
    intros f' k b [H1 H2]. split; [exact H1|]. intros (f'' & k' & Hin & R). apply H2. exists f'', k'. split; [cbn [ar_FR push amb]; right; exact Hin| exact R].
  Qed.

  (* [comment removed for export] *)
  Lemma exo_KH : forall qfc qb, @kit_hyps (push AR f 2) sp (exo_pbs f qfc qb ++ LB) lo d D (exo_XP OPP PV TLC f) (spa - bv_unsigned sp) (STK - ADEP_FRAME).
  Proof.
    intros qfc qb. ctx. pose proof PRE0 as (_ & _ & _ & _ & _ & _ & LOSP & _ & AL16 & _). pose proof CELLS as (PAY & COPP & CPV & CTLC & ALO & ALV & ALT & DOV & DOT & DVT & DOD & DVD & DTD & _).
    pose proof PAY as (_ & _ & _ & _ & _ & HB). pose proof STKB as STKu. unfold ADEP_FRAME in STKu.
    unfold kit_hyps. split; [exact DF|]. split; [unfold BnHeapA.ACEIL; cbn [ar_SP0 push amb]; exact CEIL|]. split; [exact LO0|].
    split; [unfold ADEP_FRAME; clear - LOSP SPAL; lia|]. split; [unfold ADEP_FRAME; clear - STKu ESS; lia|]. split; [clear - SPAH; lia|].
    split; [exact TOP|]. split; [exact AL16|]. split; [clear - SPA32 AL16; Z.div_mod_to_equations; lia|].
    split.
    { unfold exo_XP, exo_pbs. constructor; [cbn [fst snd]; exists bq; split; [apply in_or_app; right; exact Hbq| clear - BQ1 BQ2; lia]|].
      constructor; [cbn [fst snd]; exists bv; split; [apply in_or_app; right; exact Hbv| clear - BV1 BV2; lia]|].
      constructor; [cbn [fst snd]; exists bt; split; [apply in_or_app; right; exact Hbt| clear - BT1 BT2; lia]|].
      constructor; [cbn [fst snd]; exists (qfc, f + 64, 1); split; [apply in_or_app; left; left; reflexivity| cbn; clear; lia]|].
      constructor; [cbn [fst snd]; exists (qb, f + 80, 32); split; [apply in_or_app; left; right; left; reflexivity| cbn; clear; lia]| constructor]. }
    split.
    { unfold exo_XP. constructor; [cbn [fst snd]; exact DOD|]. constructor; [cbn [fst snd]; exact DVD|]. constructor; [cbn [fst snd]; exact DTD|].
      assert (OP : d = [] \/ exists b, In b LB /\ blk_addr b <= D /\ D + zlength d <= blk_addr b + blk_size b) by exact HB.
      constructor; [cbn [fst snd]| constructor; [cbn [fst snd]| constructor]];
        (destruct OP as [E0|(b & Hb & H1 & H2)]; [left; exact E0| right]; pose proof (FRESH b (in_or_app _ _ _ (or_intror Hb))) as O;
         unfold off_fr in O; change (fs_size 2) with 256 in O; clear - O H1 H2; lia). }
    split; [| clear - D0; lia]. destruct HB as [E0|(b & Hb & H1 & H2)]; [left; exact E0| right]. destruct b as [[pb PA] psz]. exists pb, PA, psz.
    split; [apply in_or_app; right; exact Hb|]. cbn [blk_addr blk_size fst snd] in H1, H2. split; [exact H1| exact H2].
  Qed.

  (* [comment removed for export] *)
  Lemma exo_close_pbs : forall qfc qb ΣX OWX NEW mX,
    @BnHeapA.AHEAP (push AR f 2) ΣX OWX (NEW ++ (exo_pbs f qfc qb ++ LB)) mX -> @BnHeapA.AHEAP (push AR f 2) ΣX OWX (NEW ++ LB) mX.
  Proof.
    intros qfc qb ΣX OWX NEW mX H. unfold exo_pbs in H.
    assert (CL : forall b L, in_fr f 2 b -> @BnHeapA.AHEAP (push AR f 2) ΣX OWX (NEW ++ b :: L) mX -> @BnHeapA.AHEAP (push AR f 2) ΣX OWX (NEW ++ L) mX).
    { intros b L IB HH. eapply (@frame_obj_close (push AR f 2)) with (f := f) (k := 2%nat) (b := b); [left; reflexivity| | exact IB].
      eapply AHEAP_permLB; [exact HH|]. symmetry. apply Permutation_middle. }
    apply (CL (qb, f + 80, 32)); [unfold in_fr; cbn [blk_addr blk_size fst snd]; change (fs_size 2) with 256; clear; lia|].
    apply (CL (qfc, f + 64, 1)); [unfold in_fr; cbn [blk_addr blk_size fst snd]; change (fs_size 2) with 256; clear; lia|].
    exact H.
  Qed.

  (* [comment removed for export] *)
  Lemma exo_exit : forall qfc qb mr ΣX stX mX OWX boX NEW CX (res : option (CtModel.octet bptr)) (adr' : bptr -> Z) (ov : word) (jt : list (bv 8))
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x23 x24 x26 x27 x28 x29 x30 x31 : word) (FX : bvmap 5 word) (fcX : bv 32)
      (j0 j8 j16 j24 j32 j40 j48 j64 j72 j80 j96 j104 j112 j120 j128 j136 j144 : list (bv 8)),
    agree_on (aclient_addr (OW ++ LB) (bv_unsigned sp)) m mr ->
    linv qfc qb mr ΣX stX mX OWX boX NEW CX -> 0 <= CX ->
    (forall b, In b LB -> adr' (blk_id b) = adr (blk_id b)) ->
    (forall b, In b NEW -> off_fr f 2 b) ->
    rw_cells ctasegs mX OPP [C8 ov] -> rw_cells ctasegs mX TLC [CB 32 jt] ->
    match res with
    | None => NEW = [] /\ rw_cells ctasegs mX PV [C8 (wz 0)]
    | Some os => NEW = oct_blocks adr' os /\ octet_repA mX (OWX ++ NEW ++ LB) adr' os /\ rw_cells ctasegs mX PV [C8 (wz (adr' (CtModel.os_blk os)))]
    end ->
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    rw_cells ctasegs mX spa [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48; C8 (Z_to_bv 64 OPP); CB 8 j64; CB 8 j72; CB 8 j80; C8 (Z_to_bv 64 f);
                             CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; CB g junk] ->
    rw_cells ctasegs mX (bv_unsigned sp + -16) [C8 s0; C8 ra] ->
    @implAp (push AR f 2) _ (ARet (res, stX)) ΣX POST
      (MS (mkR x1 (Z_to_bv 64 spa) gp (wz TP_A) x5 x6 x7 sp (Z_to_bv 64 spa) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 f) (Z_to_bv 64 f) x20 x21 (Z_to_bv 64 (shad f)) x23 x24 (Z_to_bv 64 match res with Some _ => 1 | None => 0 end) x26 x27 x28 x29 x30 x31)
          FX (wz ADEP_EXIT) fcX None mX (seg_rom ctasegs)).      (* [comment removed for export] *)
  Proof.
    intros until j144. intros AGFr LI HCX ADR' OFN HOPPk HTLCk RESk FRL FRH. ctx. clear AGF.
    pose proof PRE0 as (HEAP & AS & IDS & DC & ST & CEIL' & LOSP & TOP' & AL16 & MI & CRED & FRM).
    pose proof LI as (PREX & AXX & KO & KI & KP & HBX & CR & LBOK). pose proof PREX as (HEAPX & ASX & IDSX & DCX & STX & _ & _ & _ & _ & MIX & CREDX & _).
    replace (bv_unsigned sp + (spa - bv_unsigned sp)) with spa in STX by (clear; lia).
    rewrite ESPA in STX. replace (bv_unsigned sp + (spa - bv_unsigned sp)) with spa in ASX by (clear; lia). replace (bv_unsigned sp + (spa - bv_unsigned sp)) with spa in DCX by (clear; lia).
    cbn [ar_RT ar_FR push amb] in CR, CREDX.
    pose proof (exo_close_pbs qfc qb ΣX OWX NEW mX HEAPX) as HEAPc.
    assert (OFFL : forall b, In b (NEW ++ LB) -> off_fr f 2 b).
    { intros b Hb. apply in_app_or in Hb as [Hb|Hb]; [exact (OFN b Hb)| apply FRESH; apply in_or_app; right; exact Hb]. }
    (* [comment removed for export] *)
    unfold MallocRep.wz. intros X2 Φ2 D2 SAFE2 LINK2.
    apply (rw_cells_cb_first _ _ _ 8) in FRL. cbn [cb_first csize cbytes] in FRL.
    eapply (@adep_epi_cps AR _) with (lo := lo) (LB := NEW ++ LB) (gj := gj) (hrest := []);
      [exact HEAPc | exact OFFL | exact STX | exact CEIL | clear - CEIL LO SPAL ESS; lia | exact TOP | clear - SPAL; lia | clear - SPAH; lia
      | exact GSZ | exact SAVJ | exact MIX | exact FRL | exact FRH | reflexivity |].
    intros Σ' m' HEAP' CR' EL' ST' MI' AG'.
    eapply (@implAp_elim (push AR f 2) _ (ARet (res, stX))); [| exact SAFE2 | exact LINK2 | exact EL'].
    apply implAp_ret.
    (* [comment removed for export] *)
    assert (AGB : forall b A n, In b LB -> blk_addr b <= A -> A + n <= blk_addr b + blk_size b -> agree_on (fun a => A <= a < A + n) mX m').
    { intros b A n Hb H1 H2. eapply agree_on_mono; [exact AG'|]. intros a Ha. right; right. exists b. split; [apply in_or_app; right; apply in_or_app; right; exact Hb| clear - Ha H1 H2; lia]. }
    unfold exprim_oct_postA. cbn [fst snd].
    do 16 eexists. exists m', OWX, boX, adr', NEW, ov, jt. split; [reflexivity|].
    split.
    { unfold ap_preA. split; [exact HEAP'|]. split; [eapply ap_state_rt; [exact ASX | exact AG']|]. split; [exact IDSX|].
      split; [eapply data_cells_rt; [exact ASX | exact DCX | exact AG']|]. split; [exact ST'|]. split; [exact CEIL'|]. split; [clear - LOSP LO ESS; lia|].
      split; [exact TOP'|]. split; [exact AL16|]. split; [exact MI'|].
      split; [pose proof (af_credit_nonneg RT (@ar_AF AR) Σ' m' (AH_art _ _ _ _ HEAP')) as CNN; clear - CNN; lia|]. clear - FRM. lia. }
    split.
    { eapply ax_pres_trans; [eapply (ax_pres_of_aclient OW LB); [exact AGFr | clear; lia]|].
      eapply ax_pres_trans.
      - unfold ax_pres. eapply agree_on_mono; [exact AXX|]. intros a [HXa Ha]. split.
        + unfold exo_XP. intros HIN. apply HXa. cbn [app rin_ivs fst snd] in HIN |- *.
          assert (FRNG : ~ (f + 64 <= a < f + 112)).
          { destruct Ha as [Ha|[Ha|(b & Hb & Hr)]]; [clear - Ha G3 CEIL LO ESS; lia| |].
            * destruct Ha as [(l & h & Hin & Hlh) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin. destruct Hin as [E0|[E0|[E0|[]]]]; injection E0 as <- <-; clear - Hlh G4; lia.
            * pose proof (FRESH b (in_or_app _ _ _ (or_intror Hb))) as O. unfold off_fr in O. change (fs_size 2) with 256 in O.
              destruct b as [[bq' bA] bn]; cbn [blk_addr blk_size fst snd] in Hr, O. clear - Hr O. lia. }
          destruct HIN as [HIN|[HIN|[HIN|[HIN|[HIN|HIN]]]]];
            [left; exact HIN| right; left; exact HIN| right; right; left; exact HIN| exfalso; clear - HIN FRNG; lia| exfalso; clear - HIN FRNG; lia| right; right; right; exact HIN].
        + destruct Ha as [Ha|[Ha|(b & Hb & Hr)]]; [left; clear - Ha SPAH; lia| right; left; exact Ha| right; right; exists b; split; [apply in_or_app; right; exact Hb| exact Hr]].
      - eapply (ax_pres_of_aclient (OWX ++ NEW) LB); [rewrite <- app_assoc; exact AG' | clear - SPAH; lia]. }
    split; [cbn [ar_RT ar_FR push amb] in CR' |- *; unfold len in CR |- *; clear - CR CR1 CR' HCX; lia|].
    split.
    { eapply (blocks_kept_post K stX OWX (NEW ++ LB)); [| exact AG']. eapply (blocks_kept_pre K stX OW OWX LB); [exact KOW | exact AGFr |].
      split; [exact KO|]. split; [intros b Hb Hin; apply (KI b Hb); apply in_app_iff; left; exact Hin| exact KP]. }
    split; [exact ADR'|].
    split.
    { pose proof (oinv_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ (exo_KH qfc qb) _ _ _ _ _ _ _ LI) as (_ & _ & _ & FRSH & _).
      intros b Hb Hin. apply (FRSH b Hb). rewrite map_app in Hin |- *. apply in_app_iff in Hin. apply in_or_app. destruct Hin as [Hin|Hin]; [left; exact Hin| right].
      rewrite map_app. apply in_or_app. right. exact Hin. }
    split; [eapply Forall_impl; [| exact LBOK]; intros b Hb; exact (exo_lbokA_pop _ _ _ Hb)|].
    split; [eapply rw_cells_agree; [exact (AGB bq OPP 8 Hbq BQ1 BQ2)| exact HOPPk| intros a Ha; cbn in Ha; cbv beta; clear - Ha; lia]|].
    split; [eapply rw_cells_agree; [exact (AGB bt TLC 32 Hbt BT1 BT2)| exact HTLCk| intros a Ha; cbn in Ha; cbv beta; clear - Ha; lia]|].
    destruct res as [os|].
    - destruct RESk as (EN & REP & HPVk). split; [exact EN|]. split.
      + destruct REP as (RIN & RAL & RC & RL & RF & R31 & RD). split; [exact RIN|]. split; [exact RAL|]. split; [| split; [exact RL| split; [exact RF| split; [exact R31|]]]].
        * eapply rw_cells_agree; [exact AG'| exact RC|]. intros a Ha. right; right. exists (CtModel.os_blk os, adr' (CtModel.os_blk os), ASN1_STRING_SIZE). split; [exact RIN|].
          unfold asn1_string_cells in Ha. cbn in Ha. cbn [blk_addr blk_size fst snd]. unfold ASN1_STRING_SIZE. clear - Ha. lia.
        * destruct (CtModel.os_data os) as [[dp n]|]; [| exact RD]. destruct RD as (RD1 & RD2 & RD3 & RB). split; [exact RD1|]. split; [exact RD2|]. split; [exact RD3|].
          eapply bytes_at_agree; [exact AG'| exact RB|]. intros a Ha. right; right. exists (dp, adr' dp, n). split; [exact RD2|].
          cbn [blk_addr blk_size fst snd]. unfold to_bytes in Ha. rewrite length_map in Ha. unfold zlength in RL. clear - Ha RL RD3. lia.
      + eapply rw_cells_agree; [exact (AGB bv PV 8 Hbv BV1 BV2)| exact HPVk| intros a Ha; cbn in Ha; cbv beta; clear - Ha; lia].
    - destruct RESk as (EN & HPVk). split; [exact EN|].
      eapply rw_cells_agree; [exact (AGB bv PV 8 Hbv BV1 BV2)| exact HPVk| intros a Ha; cbn in Ha; cbv beta; clear - Ha; lia].
  Qed.
End Body.
End WithRT.
