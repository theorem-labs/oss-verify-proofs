(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim Malloc Prog LibProg CtSizes CtWire CtModel ApBase ApState ApErr ApBridge.
From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem SFModel.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface Malloc_ifaceP.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require Import RMallocRep RMallocTree RMalloc_iface RAligned_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import STree Monad ProgG.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Layout Lib_iface Lib_kit Printf_lib F_memcpy.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtBnU Require Import BnKit BnHeap BnRep W_crypto.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXU Require Import HxpInit HxpFacts.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApCells ApRepDefs ApRep ApWalkTac ApErrKit ApIface W_err_new W_err_set_debug W_err_set_error W_get_object_walk W_asn1_string W_item_d2i_img W_obj_free.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtParseU Require Import PzDefs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctU Require Import SctDefs W_sct_list_free SctRep W_sct_leaves W_sk_leaves SctStmt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtEncU Require Import EncPure EncStmt EncKit W_sct_complete W_asn1_enc_leaves W_asn1_i2d W_asn1_i2d2 W_i2o_sct W_i2o_list W_i2d_segs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope am_scope.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].
Ltac xmu H MU WM := apply (fun H0 => rw_cells_transport _ _ _ _ _ _ H0 MU WM) in H; [| cbn [cells_size csize]; rewrite ?Nat.add_0_r, ?Z2Nat.id by lia; cbn; lia].

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.

  Section Act.
  (* [comment removed for export] *)
  Variables (sp gp : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (st : ap_st bptr) (OW LB : list block) (E : ap_env) (bo : Z * Z).
  Variables (lo B : Z) (canary : word) (K : list block) (adr : bptr -> Z) (k : skr bptr) (DER : Z).
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis GLO : 3493888 <= lo.
  Hypothesis LOB : lo <= bv_unsigned sp - I2D_SCT_LIST_STACK.
  Hypothesis SPB : bv_unsigned sp <= B.
  Hypothesis B63 : B < 2 ^ 63.
  Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
  Hypothesis DERlo : bv_unsigned sp <= DER.
  Hypothesis DERhi : DER + 8 <= B.
  Hypothesis SKLB : forall b, In b (sk_blocks adr k) -> In b LB.
  Variables (B0T : Type) (kont : option bptr -> @AM bptr B0T) (QQ : B0T * ap_st bptr -> PState -> machine_state -> Prop).
  Variables (ra0 e8 e9 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 : word).
  Hypothesis KN : forall st' s' ms',
    i2d_post ra0 sp gp e8 e9 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 F s OW LB E lo B canary m K adr k DER (None, st') s' ms' ->
    implM ctusegs (interp (ap_embed (kont None st'))) s' QQ ms'.
  Hypothesis KS : forall d st' s' ms',
    i2d_post ra0 sp gp e8 e9 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 F s OW LB E lo B canary m K adr k DER (Some d, st') s' ms' ->
    implM ctusegs (interp (ap_embed (kont (Some d) st'))) s' QQ ms'.

  Local Notation EINV := (einv sp m s LB E lo B canary K (XC DER)).
  Local Notation FRAME1 := (frame1 ra0 e8 e9 e18 e19 e20).
  Local Notation FRAME2 := (frame2 sp DER e9 e19 e20 e21 e22 e23 e24).
  Local Notation FRAME3 := (frame3 sp adr k e20 e21 e22 e23 e24).
  Local Notation GK := (Gk B0T kont).
  (* [comment removed for export] *)
  Let k_facts' := @k_facts CE__ RN__ sp m s LB E lo B canary K DER.
  Let k_call' := @k_call CE__ RN__ sp m s LB E lo B canary K DER CEIL GLO SPB B63.
  Let k_munch' := @k_munch CE__ RN__ sp m s LB E lo B canary K DER CEIL GLO SPB DERlo DERhi.
  Let k_exit' := @k_exit CE__ RN__ sp m s LB E lo B canary K DER CEIL GLO SPB B63 SP16.
  Let k_ap_pre' := @k_ap_pre CE__ RN__ sp m s LB E lo B canary K DER CEIL GLO SPB B63.
  Let k_after' := @k_after CE__ RN__ sp m s LB E lo B canary K DER CEIL GLO SPB B63 DERlo DERhi.
  Let k_alloc' := @k_alloc CE__ RN__ sp m s LB E lo B canary K DER.
  Let k_heap' := @k_heap CE__ RN__ sp m s LB E lo B canary K DER.
  Let item_facts' := @item_facts CE__ RN__ sp m s LB E lo B canary K adr k DER CEIL.
  Let sk_keep' := @sk_keep CE__ RN__ sp m s LB E lo B canary K adr k DER CEIL LOB DERlo.
  Let raise_B_seq' := @raise_B_seq CE__ RN__ HM HF sp gp m s LB E lo B canary K DER CEIL GLO SPB B63 DERlo DERhi.
  Let len_loop' := @len_loop CE__ RN__ HM HF sp gp F m s OW LB E lo B canary K adr k DER CEIL GLO LOB SPB B63 SP16 DERlo DERhi B0T kont QQ ra0 e8 e9 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 KN.
  Let write_loop' := @write_loop CE__ RN__ sp gp m s LB E lo B canary K adr k DER CEIL GLO LOB SPB B63 SP16 DERlo DERhi ra0 e8 e9 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27.

  Lemma SPR' : 0 <= bv_unsigned sp < 2 ^ 64.
  Proof. pose proof (bv_unsigned_in_range 64 sp) as H. unfold bv_modulus in H. cbn in H. exact H. Qed.
  Lemma OWN0 : forall NEW lo' hi', lo <= lo' -> hi' <= bv_unsigned sp -> Forall (own_iv sp lo (XC DER) NEW) [(lo', hi')]%Z.
  Proof. intros. constructor; [left; cbn; lia| constructor]. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma ret_none_tail : forall sX stX mX OWX (errvX : word) boX (FX : bvmap 5 word) (fcX : bv 32)
      (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x28 x29 x30 x31 : word) j1 j2,
    EINV (bv_unsigned sp + -160) sX stX mX OWX errvX boX [] ->
    rw_cells ctusegs mX (bv_unsigned sp + -64) (FRAME1 j1 0) -> rw_cells ctusegs mX (bv_unsigned sp + -160) (FRAME2 j2 0) ->
    rw_cells ctusegs mX DER [C8 (Z_to_bv 64 0)] -> sk_rep mX LB adr k -> frm0 fcX -> (forall rr : reg, bv_unsigned rr <> 10 -> reg_get FX rr = reg_get F rr) ->
    implM ctusegs (interp (ap_embed (kont None stX))) sX QQ
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -160)) gp (wz RATP) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
               x18 x19 (Z_to_bv 64 (-1)) x21 x22 x23 e24 e25 e26 e27 x28 x29 x30 x31)
          FX (Z_to_bv 64 RAISE_RET_B) fcX None mX (seg_rom ctusegs)).
  Proof using KN k_call' k_exit' k_munch' sk_keep'.
    intros until j2. intros EI FR1 FR2 HDER SK FRM FE. pose proof SPR' as SPR.
    unfold I2D_SCT_LIST_STACK, ERR_SET_ERROR_STACK in LOB. unfold RAISE_RET_B.
    pose proof (k_call' _ _ _ _ _ _ _ _ EI) as (_ & _ & _ & ST & _ & _ & _ & MI & _).
    unfold implM. iprefix.
    pose proof (munch_refl [(lo, bv_unsigned sp)]%Z mX) as MU. pose proof (wmono_refl ctusegs mX) as WM.
    unfold frame2 in FR2. unfold frame1 in FR1.
    (* [comment removed for export] *)
    zstep. do 10 zstep. zstep. release_frame FR2 ST (bv_unsigned sp + -64). zstep.
    zstep. zstep. btaken. zstep. do 6 zstep. zstep. release_frame FR1 ST (bv_unsigned sp). zstep.
    ihere. to_implM.
    lazymatch goal with |- implM _ _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
    assert (EI5 : EINV (bv_unsigned sp) sX stX m5 OWX errvX boX []).
    { eapply k_munch'; [exact EI| exact MU| exact WM| assumption| exact ST| lia| apply OWN0; lia]. }
    assert (SK5 : sk_rep m5 LB adr k) by (eapply sk_keep'; [exact EI| exact SK| exact MU| exact WM| apply OWN0; lia]).
    destruct (k_exit' _ _ _ _ _ _ _ EI5) as (PRE5 & LX5 & BK5 & SO5 & FA5 & FRESH5). cbn [app] in PRE5.
    apply KN. unfold i2d_post. cbn [fst snd].
    do 15 eexists. exists FX, fcX, m5, OWX, errvX, boX, []. cbn [app].
    split; [reflexivity|]. split; [exact FRM|]. split; [exact FE|].
    split; [exact PRE5|]. split; [exact LX5|]. split; [exact SO5|]. split; [exact FA5|]. split; [exact BK5|].
    split; [intros b Hb; destruct Hb|]. split; [exact SK5|]. split; [reflexivity| exact HDER].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma k_alloc_but : forall q sX stX mX OWX errvX boX NEW sY mY (errvY : word) pn A n,
    EINV q sX stX mX OWX errvX boX NEW ->
    rheap_pres_but (OWX ++ NEW ++ LB) q (DER, DER + 8) mX mY ->
    RHEAP sY ((pn, A, n) :: OWX ++ NEW ++ LB) mY ->
    mem_inv ctusegs mY -> stk ctusegs mY lo q -> rw_cells ctusegs mY LX_ERRNO [C4 errvY] -> rauxv_ok mY B ->
    ps_fa sY = ps_fa sX -> ps_so sY = ps_so sX ->
    EINV q sY stX mY OWX errvY boX ((pn, A, n) :: NEW).
  Proof using CEIL DERlo GLO.
    intros until n. intros OI HPB HEAPY MI ST ERR AUX FA' SO'. pose proof SPR' as SPR.
    pose proof (k_facts' _ _ _ _ _ _ _ _ OI) as (_ & _ & BND & _).
    destruct OI as ((HEAP & AS & IDS & DC & AUX0 & LOQ0 & ST0 & ERR0 & SSP & MI0) & LX & KO & KI & KP & SO & FA).
    pose proof (ap_state_es _ _ _ _ _ AS) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & OD).
    unfold LX_ERRNO, RATP in ERR. change (3355176 - 164) with 3355012 in ERR.
    (* [comment removed for export] *)
    assert (HP : rheap_pres (OWX ++ NEW ++ LB) (2 ^ 64) mX mY).
    { intros a Ha Hc. apply HPB; [exact Ha| |].
      - destruct Hc as [Hc|[Hc|Hc]]; [lia| right; left; exact Hc| right; right; exact Hc].
      - destruct Hc as [Hc|[Hc|(b & Hb & Hr)]]; [lia| cbn [fst snd]; lia|].
        destruct b as [[pb Ab] nb]. cbn [blk_addr blk_size fst snd] in Hr. pose proof (BND pb Ab nb Hb). cbn [fst snd]. lia. }
    assert (HEAPY' : RHEAP sY (OWX ++ ((pn, A, n) :: NEW) ++ LB) mY) by (eapply RHEAP_perm; [exact HEAPY| apply Permutation_middle]).
    split; [| split; [| split; [exact KO| split; [exact KI| split; [| split; [rewrite SO'; exact SO| rewrite FA'; exact FA]]]]]].
    - split; [exact HEAPY'|].
      split; [eapply ap_state_heap_pres_app; [exact AS| exact HP]|].
      split; [exact IDS|].
      split. { eapply data_cells_heap_pres; [exact DC| exact HP|]. intros i p kk Hd. apply in_app_iff. left. exact (proj1 (optb_ok_nth OWX _ i p kk OD Hd)). }
      split; [exact AUX|]. split; [exact LOQ0|]. split; [exact ST|]. split; [exact ERR|].
      split; [rewrite (ssp_canary_0 _ _ _ _ HEAP SSP); eapply RHEAP_ssp; exact HEAPY'| exact MI].
    - eapply lx_pres_trans; [exact LX|]. intros a Ha [Hx Hc]. apply HPB; [exact Ha| |].
      + destruct Hc as [Hc|[(b & Hb & Hr)|Hc]]; [left; lia| right; right; exists b; split; [apply in_app_iff; right; apply in_app_iff; right; exact Hb| exact Hr]| right; left; exact Hc].
      + intros Hin. apply Hx. cbn [rin_ivs app XC fst snd]. left. exact Hin.
    - eapply kept_trans; [exact KP|]. eapply kept_of_heap_pres; [exact HP|]. intros b Hb. apply in_app_iff. left. apply KO. exact Hb.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma after_der : forall sX stX mX OWX (errvX : word) boX (FX : bvmap 5 word) (fcX : bv 32)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) j1 (pr po pd : bptr) (ADR n3 A AD len2 : Z),
    EINV (bv_unsigned sp + -64) sX stX mX OWX errvX boX [(pr, ADR, n3); (po, A, ASN1_STRING_SIZE); (pd, AD, len2)] -> 0 < n3 ->
    rw_cells ctusegs mX (bv_unsigned sp + -64) (FRAME1 j1 AD) -> rw_cells ctusegs mX DER [C8 (wz ADR)] ->
    rw_cells ctusegs mX A (asn1_string_cells len2 V_ASN1_OCTET_STRING AD 0) ->
    sk_rep mX LB adr k -> frm0 fcX -> (forall rr : reg, bv_unsigned rr <> 10 -> reg_get FX rr = reg_get F rr) ->
    implM ctusegs (interp (LFree pd (LFree po (ap_embed (kont (Some pr) stX))))) sX QQ
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp (wz RATP) x5 x6 x7 sp (Z_to_bv 64 (-1)) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 DER) (Z_to_bv 64 A) (Z_to_bv 64 len2) e21 e22 e23 e24 e25 e26 e27 x28 x29 x30 x31)
          FX (Z_to_bv 64 0x19d470) fcX None mX (seg_rom ctusegs)).
  Proof using HF KS LOB bo k_call' k_exit' k_munch'.
    intros until len2. intros EI N3 FR1 HDER HS SK FRM FE. pose proof SPR' as SPR.
    unfold I2D_SCT_LIST_STACK, ERR_SET_ERROR_STACK in LOB.
    pose proof (k_call' _ _ _ _ _ _ _ _ EI) as (HEAP & AUX & _ & ST & _ & _ & ERR & MI & CS & _).
    pose proof (k_facts' _ _ _ _ _ _ _ _ EI) as (_ & ND & BND & FRESH & _).
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; lia).
    rewrite !map_app in ND. pose proof (NoDup_app_split _ _ ND) as (N23 & _ & _). pose proof (NoDup_app_split _ _ N23) as (_ & _ & NN).
    cbn [map blk_id fst snd] in NN. apply NoDup_cons_iff in NN. destruct NN as [N1 NN]. apply NoDup_cons_iff in NN. destruct NN as [N2 _]. cbn [In] in N1, N2.
    assert (NE : po <> pd) by (intros E0; apply N2; left; symmetry; exact E0).
    assert (NE1 : pr <> pd /\ pr <> po) by (split; intros E0; apply N1; [right; left| left]; symmetry; exact E0).
    unfold implM. iprefix.
    pose proof (munch_refl (@nil (Z * Z)) mX) as MU. pose proof (wmono_refl ctusegs mX) as WM.
    (* [comment removed for export] *)
    zstep. zstep. zstep. ihere. to_implM.
    eapply ASN1_pfree_walk with (lo := lo) (B := B) (errv := errvX) (L := OWX ++ [(pr, ADR, n3); (po, A, ASN1_STRING_SIZE); (pd, AD, len2)] ++ LB)
                                 (pblk := po) (pdata := pd) (A := A) (D := AD) (alloc := len2) (len := len2) (ty := V_ASN1_OCTET_STRING); rewrite ?ESP;
      [ exact HF| right; left; reflexivity| exact HEAP| exact AUX| lia| exact ST| exact CEIL| unfold GLOBALS_TOP; lia
      | unfold ASN1_STRING_FREE_STACK, CRYPTO_FREE_STACK, RFREE_STACK; lia| exact ERR| exact MI| reflexivity| exact CS
      | apply in_app_iff; right; apply in_app_iff; left; right; left; reflexivity
      | apply in_app_iff; right; apply in_app_iff; left; right; right; left; reflexivity
      | exact NE| exact HS| reflexivity|].
    intros sG msG PO. unfold vfree_post in PO. rewrite ?ESP in PO.
    destruct PO as (g0 & g1 & g2 & g10 & g11 & g12 & g13 & g14 & g15 & g16 & g17 & g3 & g4 & g5 & g6 & mG
                    & -> & MIG & STG & ERRG & AUXG & HPG & FAG & SOG & HEAPG & _).
    replace (ret_pc (Z_to_bv 64 0x19d47c)) with (Z_to_bv 64 0x19d47c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    (* [comment removed for export] *)
    assert (FRpo : ~ In po (map blk_id (OWX ++ LB))) by (eapply (FRESH po A ASN1_STRING_SIZE); right; left; reflexivity).
    assert (FRpd : ~ In pd (map blk_id (OWX ++ LB))) by (eapply (FRESH pd AD len2); right; right; left; reflexivity).
    rewrite map_app in FRpo, FRpd.
    assert (E1 : lb_remove pd [(pr, ADR, n3); (po, A, ASN1_STRING_SIZE); (pd, AD, len2)] = [(pr, ADR, n3); (po, A, ASN1_STRING_SIZE)]).
    { rewrite !lb_remove_cons. cbn [blk_id fst snd]. rewrite (bptr_eqb_neq pr pd), (bptr_eqb_neq po pd), bptr_eqb_refl by tauto. reflexivity. }
    assert (E2 : lb_remove po [(pr, ADR, n3); (po, A, ASN1_STRING_SIZE)] = [(pr, ADR, n3)]).
    { rewrite !lb_remove_cons. cbn [blk_id fst snd]. rewrite (bptr_eqb_neq pr po), bptr_eqb_refl by tauto. reflexivity. }
    assert (LEQ : lb_remove po (lb_remove pd (OWX ++ [(pr, ADR, n3); (po, A, ASN1_STRING_SIZE); (pd, AD, len2)] ++ LB)) = OWX ++ [(pr, ADR, n3)] ++ LB).
    { rewrite !lb_remove_app, E1. rewrite (lb_remove_notin pd OWX), (lb_remove_notin pd LB) by (intros Hin; apply FRpd; apply in_app_iff; tauto).
      rewrite E2. rewrite (lb_remove_notin po OWX), (lb_remove_notin po LB) by (intros Hin; apply FRpo; apply in_app_iff; tauto).
      reflexivity. }
    rewrite LEQ in HPG, HEAPG.
    assert (EIG : EINV (bv_unsigned sp + -64) sG stX mG OWX errvX boX [(pr, ADR, n3)]).
    { eapply (k_heap' _ _ _ _ _ _ _ _ sG mG errvX _ _ [(pr, ADR, n3)]); [exact EI| exact HPG| | exact HEAPG| apply Permutation_refl| exact MIG| exact STG| exact ERRG| exact AUXG| exact FAG| exact SOG].
      intros b Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; exact Hb| right; apply in_app_iff; right; exact Hb]. }
    pose proof (agree_of_heap_pres _ _ _ _ HPG) as AGG.
    apply (rw_cells_agree _ _ _ _ _ AGG) in FR1; [| intros a Ha; left; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ AGG) in HDER; [| intros a Ha; left; cbn in Ha; lia].
    assert (SKG : sk_rep mG LB adr k).
    { eapply sk_rep_agree; [exact AGG| | exact SK]. intros [[qb Ab] nb] a Hb Ha. cbn [blk_addr blk_size fst snd] in Ha.
      pose proof (sk_allblocks_in _ _ _ _ _ SK Hb) as HbL. right. right. exists (qb, Ab, nb). split; [| cbn; lia].
      apply in_app_iff. right. apply in_app_iff. right. exact HbL. }
    clear MU WM MI ST HEAP AUX ERR CS AGG HPG EI SK.
    (* [comment removed for export] *)
    unfold implM. iprefix.
    pose proof (munch_refl (@nil (Z * Z)) mG) as MU. pose proof (wmono_refl ctusegs mG) as WM.
    zstep. unfold frame1 in FR1.
    eapply evt_cut. { eapply i2d_epilogue with (lo := lo); [exact STG| exact MIG| lia| lia| exact FR1]. }
    cbv beta. intros ms2 [-> ST2]. ihere. to_implM.
    assert (EI5 : EINV (bv_unsigned sp) sG stX mG OWX errvX boX [(pr, ADR, n3)]).
    { eapply k_munch'; [exact EIG| apply munch_refl| apply wmono_refl| exact MIG| exact ST2| lia| constructor]. }
    destruct (k_exit' _ _ _ _ _ _ _ EI5) as (PRE5 & LX5 & BK5 & SO5 & FA5 & FRESH5). cbn [app] in PRE5.
    apply KS. unfold i2d_post. cbn [fst snd].
    do 15 eexists. exists FX, fcX, mG, OWX, errvX, boX, [(pr, ADR, n3)]. cbn [app].
    split; [reflexivity|]. split; [exact FRM|]. split; [exact FE|].
    split; [exact PRE5|]. split; [exact LX5|]. split; [exact SO5|]. split; [exact FA5|]. split; [exact BK5|].
    split; [intros b Hb; apply FRESH5; exact Hb|]. split; [exact SKG|]. exists ADR, n3. split; [reflexivity|]. split; [exact N3| exact HDER].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma after_oct : forall sX stX mX OWX (errvX : word) boX (FX : bvmap 5 word) (fcX : bv 32)
      (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31 : word) j1 (po pd : bptr) (A AD len2 : Z) bs,
    EINV (bv_unsigned sp + -64) sX stX mX OWX errvX boX [(po, A, ASN1_STRING_SIZE); (pd, AD, len2)] -> 2 <= len2 <= 65535 ->
    rw_cells ctusegs mX (bv_unsigned sp + -64) (FRAME1 j1 AD) -> rw_cells ctusegs mX DER [C8 (Z_to_bv 64 0)] -> DER mod 8 = 0 ->
    rw_cells ctusegs mX A (asn1_string_cells 0 V_ASN1_OCTET_STRING 0 0) -> rw_cells ctusegs mX AD [CB (Z.to_nat len2) bs] ->
    sk_rep mX LB adr k -> frm0 fcX -> (forall rr : reg, bv_unsigned rr <> 10 -> reg_get FX rr = reg_get F rr) ->
    implM ctusegs (interp (ap_embed (abind (amalloc (der_hl len2 + len2))
                                       (fun der => abind (afree pd) (fun _ => abind (afree po) (fun _ => kont (Some der)))) stX))) sX QQ
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp (wz RATP) x5 x6 x7 sp (Z_to_bv 64 (-1)) (Z_to_bv 64 A) x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 DER) x19 (Z_to_bv 64 len2) e21 e22 e23 e24 e25 e26 e27 x28 x29 x30 x31)
          FX (Z_to_bv 64 I2D_RET2) fcX None mX (seg_rom ctusegs)).
  Proof using HF HM KS bo k_call' k_exit' k_munch' sk_keep'.
    intros until bs. intros EI L2 FR1 HDER DER8 HS HD SK FRM FE. pose proof SPR' as SPR.
    unfold I2D_SCT_LIST_STACK, ERR_SET_ERROR_STACK in LOB.
    pose proof (k_call' _ _ _ _ _ _ _ _ EI) as (HEAP & AUX & _ & ST & _ & _ & ERR & MI & CS & _ & _ & IMG & _).
    pose proof (k_facts' _ _ _ _ _ _ _ _ EI) as (_ & ND & BND & FRESH & DJL & DJO & DJN).
    pose proof (BND po A ASN1_STRING_SIZE ltac:(apply in_app_iff; right; apply in_app_iff; left; left; reflexivity)) as (A0 & _ & AC & _ & A16).
    pose proof (BND pd AD len2 ltac:(apply in_app_iff; right; apply in_app_iff; left; right; left; reflexivity)) as (AD0 & _ & ADC & _).
    rewrite !map_app in ND. pose proof (NoDup_app_split _ _ ND) as (N23 & _ & _). pose proof (NoDup_app_split _ _ N23) as (_ & _ & NN).
    cbn [map blk_id fst snd] in NN. apply NoDup_cons_iff in NN. destruct NN as [N1 _]. cbn [In] in N1.
    assert (NE : po <> pd) by (intros E0; apply N1; left; symmetry; exact E0).
    pose proof (DJN _ _ _ _ _ _ ltac:(left; reflexivity) ltac:(right; left; reflexivity) NE) as DJAD. unfold ASN1_STRING_SIZE in DJAD, AC.
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; lia).
    unfold implM. iprefix. unfold frame1 in FR1.
    eapply evt_cut.
    { eapply i2d_set0_seg with (lo := lo) (A := A) (AD := AD) (len2 := len2); rewrite ?ESP;
        [exact ST| exact MI| unfold GLOBALS_TOP; lia| lia| lia| lia| unfold ASN1_STRING_SIZE; lia| lia| lia| lia| exact HS| exact FR1]. }
    cbv beta. intros ms1 PO. rewrite ?ESP in PO. unfold ASN1_STRING_SIZE in PO.
    destruct PO as (u5 & u6 & u7 & u14 & u15 & u16 & u17 & u28 & u29 & u30 & u31 & m1 & -> & MU1 & WM1 & MI1 & ST1 & HS1 & FR1').
    xmu HDER MU1 WM1. xmu HD MU1 WM1.
    assert (EI1 : EINV (bv_unsigned sp + -64) sX stX m1 OWX errvX boX [(po, A, ASN1_STRING_SIZE); (pd, AD, len2)]).
    { eapply k_munch'; [exact EI| exact MU1| exact WM1| exact MI1| exact ST1| lia|].
      constructor; [left; cbn; lia| constructor; [| constructor]]. right. right. exists po, A, ASN1_STRING_SIZE. cbn [fst snd]. unfold ASN1_STRING_SIZE. split; [left; reflexivity| lia]. }
    assert (SK1 : sk_rep m1 LB adr k).
    { eapply sk_keep'; [exact EI| exact SK| exact MU1| exact WM1|].
      constructor; [left; cbn; lia| constructor; [| constructor]]. right. right. exists po, A, ASN1_STRING_SIZE. cbn [fst snd]. unfold ASN1_STRING_SIZE. split; [left; reflexivity| lia]. }
    pose proof (k_call' _ _ _ _ _ _ _ _ EI1) as (HEAP1 & AUX1 & _ & _ & _ & _ & ERR1 & _ & CS1 & _ & _ & IMG1 & _).
    clear MU1 WM1 MI ST HEAP AUX ERR CS IMG EI SK HS FR1. rename FR1' into FR1.
    (* [comment removed for export] *)
    ihere. cbn [abind apbind amalloc afree aret ap_embed fst snd]. to_implM.
    eapply (asn1_item_flags_i2d_walk HM) with (lo := lo) (B := B) (errv := errvX) (L := OWX ++ [(po, A, ASN1_STRING_SIZE); (pd, AD, len2)] ++ LB)
             (poct := po) (pdata := pd) (A := A) (len := len2) (D := AD) (DER := DER) (src := bs) (a2 := wz 0) (a3 := wz 0); rewrite ?ESP;
      [ exact HEAP1| exact AUX1| lia| exact B63| exact ST1| rewrite <- Zplus_mod_idemp_l, SP16; reflexivity| exact CEIL| unfold GLOBALS_TOP; lia
      | unfold ASN1_ITEM_FLAGS_I2D_STACK, CRYPTO_MALLOC_STACK, RMALLOC_STACK; lia| exact ERR1| exact MI1| reflexivity| exact CS1| exact IMG1
      | apply in_app_iff; right; apply in_app_iff; left; left; reflexivity
      | apply in_app_iff; right; apply in_app_iff; left; right; left; reflexivity
      | exact NE| exact HS1| exact HD| lia| lia| lia| exact HDER| exact DER8| reflexivity| reflexivity| reflexivity|].
    intros pr sD msD PO. unfold flags_post in PO. rewrite ?ESP in PO.
    destruct PO as (d0 & d1 & d2 & d11 & d12 & d13 & d14 & d15 & d16 & d17 & d3 & d4 & d5 & d6 & mD & ADR & errvD
                    & -> & MID & STD & ERRD & AUXD & HPD & FAD & SOD & BRD & HEAPD & HDERD & HSD & _).
    replace (ret_pc (Z_to_bv 64 0x19d470)) with (Z_to_bv 64 0x19d470) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof BRD as (BD0 & BD16 & _ & BDC & BDI). pose proof (der_hl_range len2 ltac:(lia)) as HLR.
    assert (EID : EINV (bv_unsigned sp + -64) sD stX mD OWX errvD boX [(pr, ADR, der_hl len2 + len2); (po, A, ASN1_STRING_SIZE); (pd, AD, len2)]).
    { eapply k_alloc_but; [exact EI1| exact HPD| exact HEAPD| exact MID| exact STD| exact ERRD| exact AUXD| exact FAD| exact SOD]. }
    (* [comment removed for export] *)
    assert (AGD : agree_on (fun a => (bv_unsigned sp + -64 <= a /\ ~ (DER <= a < DER + 8)) \/ in_block LB a) m1 mD).
    { hnf. intros a Ha Hc. apply HPD; [exact Ha| | ].
      - destruct Hc as [[Hc _]|(b & Hb & Hr)]; [left; exact Hc| right; right; exists b; split; [apply in_app_iff; right; apply in_app_iff; right; exact Hb| exact Hr]].
      - destruct Hc as [[_ Hc]|(b & Hb & Hr)]; [exact Hc|]. destruct b as [[qb Ab] nb]. cbn [blk_addr blk_size fst snd] in Hr.
        pose proof (BND qb Ab nb ltac:(apply in_app_iff; right; apply in_app_iff; right; exact Hb)). cbn [fst snd]. lia. }
    apply (rw_cells_agree _ _ _ _ _ AGD) in FR1; [| intros a Ha; left; cbn in Ha; lia].
    assert (SKD : sk_rep mD LB adr k).
    { eapply sk_rep_agree; [exact AGD| | exact SK1]. intros [[qb Ab] nb] a Hb Ha. cbn [blk_addr blk_size fst snd] in Ha.
      right. exists (qb, Ab, nb). split; [exact (sk_allblocks_in _ _ _ _ _ SK1 Hb)| cbn; lia]. }
    cbn [abind apbind afree aret ap_embed fst snd].
    eapply after_der; [exact EID| lia| exact FR1| exact HDERD| exact HSD| exact SKD| exact FRM| exact FE].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma from_ret1 : forall sX stX mX OWX (errvX : word) boX (FX : bvmap 5 word) (fcX : bv 32)
      (x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x19 x20 x28 x29 x30 x31 : word) j1 (pd : bptr) (AD len2 : Z) bs,
    EINV (bv_unsigned sp + -64) sX stX mX OWX errvX boX [(pd, AD, len2)] -> 2 <= len2 <= 65535 ->
    rw_cells ctusegs mX (bv_unsigned sp + -64) (FRAME1 j1 AD) -> rw_cells ctusegs mX DER [C8 (Z_to_bv 64 0)] -> DER mod 8 = 0 ->
    rw_cells ctusegs mX AD [CB (Z.to_nat len2) bs] ->
    sk_rep mX LB adr k -> frm0 fcX -> (forall rr : reg, bv_unsigned rr <> 10 -> reg_get FX rr = reg_get F rr) ->
    implM ctusegs (interp (ap_embed (abind (amalloc SZ_ASN1_STRING) (fun oct =>
                                      abind (amalloc (der_hl len2 + len2)) (fun der =>
                                      abind (afree pd) (fun _ => abind (afree oct) (fun _ => kont (Some der))))) stX))) sX QQ
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp (wz RATP) x5 x6 x7 sp x9 (Z_to_bv 64 len2) x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 DER) x19 x20 e21 e22 e23 e24 e25 e26 e27 x28 x29 x30 x31)
          FX (Z_to_bv 64 I2D_RET1) fcX None mX (seg_rom ctusegs)).
  Proof using HF HM KS bo k_call' k_exit' k_munch' sk_keep'.
    intros until bs. intros EI L2 FR1 HDER DER8 HD SK FRM FE. pose proof SPR' as SPR.
    unfold I2D_SCT_LIST_STACK, ERR_SET_ERROR_STACK in LOB.
    pose proof (k_call' _ _ _ _ _ _ _ _ EI) as (_ & _ & _ & ST & _ & _ & _ & MI & _).
    pose proof (k_facts' _ _ _ _ _ _ _ _ EI) as (_ & _ & BND & _).
    pose proof (BND pd AD len2 ltac:(apply in_app_iff; right; apply in_app_iff; left; left; reflexivity)) as (AD0 & _ & ADC & _).
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; lia).
    unfold implM. iprefix. unfold frame1 in FR1.
    eapply i2d_call_new_seg with (lo := lo); rewrite ?ESP; [exact ST| exact MI| unfold GLOBALS_TOP; lia| lia| lia| lia|].
    intros m1 MU1 WM1 MI1 ST1. rewrite ?ESP in *.
    xmu FR1 MU1 WM1. xmu HDER MU1 WM1. xmu HD MU1 WM1.
    assert (EI1 : EINV (bv_unsigned sp + -64) sX stX m1 OWX errvX boX [(pd, AD, len2)]).
    { eapply k_munch'; [exact EI| exact MU1| exact WM1| exact MI1| exact ST1| lia| apply OWN0; lia]. }
    assert (SK1 : sk_rep m1 LB adr k) by (eapply sk_keep'; [exact EI| exact SK| exact MU1| exact WM1| apply OWN0; lia]).
    pose proof (k_call' _ _ _ _ _ _ _ _ EI1) as (HEAP1 & AUX1 & _ & _ & _ & _ & ERR1 & _ & CS1 & _).
    clear MU1 WM1 MI ST EI SK.
    (* [comment removed for export] *)
    ihere. cbn [abind apbind amalloc afree aret ap_embed fst snd]. to_implM.
    eapply (ASN1_STRING_type_new_walk HM) with (lo := lo) (B := B) (errv := errvX) (L := OWX ++ [(pd, AD, len2)] ++ LB) (ty := V_ASN1_OCTET_STRING); rewrite ?ESP;
      [ exact HEAP1| exact AUX1| lia| exact ST1| exact CEIL| unfold GLOBALS_TOP; lia
      | unfold ASN1_STRING_TYPE_NEW_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RMALLOC_STACK; lia| exact ERR1| exact MI1| reflexivity| exact CS1
      | reflexivity| unfold V_ASN1_OCTET_STRING; lia| reflexivity|].
    intros po sL msL PO. unfold calloc_post in PO. rewrite ?ESP in PO.
    destruct PO as (u0 & u1 & u2 & u11 & u12 & u13 & u14 & u15 & u16 & u17 & u3 & u4 & u5 & u6 & mL & A & errvL
                    & -> & MIL & STL & ERRL & AUXL & HPL & FAL & SOL & BRL & HEAPL & HSL).
    replace (ret_pc (Z_to_bv 64 I2D_RET2)) with (Z_to_bv 64 I2D_RET2) by (symmetry; apply ret_pc_even; [unfold I2D_RET2; lia| reflexivity]). unfold MallocRep.wz.
    assert (EIL : EINV (bv_unsigned sp + -64) sL stX mL OWX errvL boX [(po, A, 24); (pd, AD, len2)]).
    { eapply k_alloc'; [exact EI1| exact HPL| exact HEAPL| exact MIL| exact STL| exact ERRL| exact AUXL| exact FAL| exact SOL]. }
    pose proof (agree_of_heap_pres _ _ _ _ HPL) as AGL.
    apply (rw_cells_agree _ _ _ _ _ AGL) in FR1; [| intros a Ha; left; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ AGL) in HDER; [| intros a Ha; left; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ AGL) in HD.
    2:{ intros a Ha. right. right. exists (pd, AD, len2). split; [apply in_app_iff; right; apply in_app_iff; left; left; reflexivity|].
        cbn [cells_size csize] in Ha. rewrite Nat.add_0_r, Z2Nat.id in Ha by lia. cbn. lia. }
    assert (SKL : sk_rep mL LB adr k).
    { eapply sk_rep_agree; [exact AGL| | exact SK1]. intros [[qb Ab] nb] a Hb Ha. cbn [blk_addr blk_size fst snd] in Ha.
      right. right. exists (qb, Ab, nb). split; [apply in_app_iff; right; apply in_app_iff; right; exact (sk_allblocks_in _ _ _ _ _ SK1 Hb)| cbn; lia]. }
    cbn [abind apbind afree aret ap_embed fst snd].
    eapply after_oct; [exact EIL| lia| exact FR1| exact HDER| exact DER8| exact HSL| exact HD| exact SKL| exact FRM| exact FE].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma sk_facts : forall q sC stC mC OWC errvC boC NEW,
    EINV q sC stC mC OWC errvC boC NEW -> sk_rep mC LB adr k ->
    (0 < adr (sk_blk k) /\ adr (sk_blk k) + STACK_SIZE <= lo) /\ ro_cells ctusegs mC (adr (sk_blk k)) [C4 (wz (sk_num k))] /\ 0 <= sk_num k < 2^23
    /\ Forall (sct_ok adr) (sk_items k) /\ adr (sk_blk k) mod 8 = 0.
  Proof using CEIL.
    intros until NEW. intros EI SK. pose proof (k_facts' _ _ _ _ _ _ _ _ EI) as (HEAP & _).
    clear k_facts' k_call' k_munch' k_exit' k_ap_pre' k_after' k_alloc' k_heap' item_facts' sk_keep' raise_B_seq' len_loop' write_loop'.
    pose proof SK as (HIN & (sorted & SR & HC) & HD & HFI & ND).
    pose proof (blk_bounds _ _ _ _ _ _ HEAP ltac:(apply in_app_iff; right; apply in_app_iff; right; exact HIN)) as (B1 & B2 & B3 & B4 & B5). unfold STACK_SIZE in *.
    split; [lia|].
    unfold sk_cells in HC.
    lazymatch type of HC with rw_cells _ _ _ (?c0 :: ?rest) => pose proof (proj1 (proj1 (rw_cells_app mC _ [c0] rest) HC)) as X0 end.
    split; [exact (proj1 X0)|].
    split. { unfold sk_num in *. destruct (sk_data k) as [[q0 na]|]; [destruct HD as (_ & H1 & H2 & _); unfold zlength in *; lia| rewrite HD; unfold zlength; cbn [length Z.of_nat]; lia]. }
    split; [| lia].
    apply Forall_forall. intros x Hx. eapply sct_ok_of_rep; [exact HEAP|]. eapply sct_rep_mono; [| exact (proj1 (Forall_forall _ _) HFI x Hx)].
    intros b Hb. apply in_app_iff. right. apply in_app_iff. right. exact Hb.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma some_path : forall sC stC mC OWC (errvC : word) boC (FC : bvmap 5 word) (fcC : bv 32)
      (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) j1 j2 len2,
    EINV (bv_unsigned sp + -160) sC stC mC OWC errvC boC [] ->
    len2 = 2 + i2o_sum (sk_items k) -> len2 <= 65535 -> Forall (fun x => sct_complete x = true) (sk_items k) ->
    rw_cells ctusegs mC (bv_unsigned sp + -64) (FRAME1 j1 0) -> rw_cells ctusegs mC (bv_unsigned sp + -160) (FRAME2 j2 0) ->
    rw_cells ctusegs mC DER [C8 (Z_to_bv 64 0)] -> DER mod 8 = 0 -> sk_rep mC LB adr k -> frm0 fcC -> (forall rr : reg, bv_unsigned rr <> 10 -> reg_get FC rr = reg_get F rr) ->
    implM ctusegs (interp (ap_embed (GK (Some len2) stC))) sC QQ
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -160)) gp (wz RATP) x5 x6 x7 (Z_to_bv 64 (bv_unsigned sp + -64)) (Z_to_bv 64 (bv_unsigned sp + -56))
               (Z_to_bv 64 len2) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (adr (sk_blk k))) (Z_to_bv 64 0) e20 e21 e22 e23 e24 e25 e26 e27 x28 x29 x30 x31)
          FC (Z_to_bv 64 0x19d2a8) fcC None mC (seg_rom ctusegs)).
  Proof using HF HM KS bo k_call' k_exit' k_munch' sk_keep' write_loop'.
    intros until len2. intros EI LEN2 L2B CALL FR1 FR2 HDER DER8 SK FRM FE. pose proof SPR' as SPR.
    unfold I2D_SCT_LIST_STACK, ERR_SET_ERROR_STACK in LOB.
    pose proof (sk_facts _ _ _ _ _ _ _ _ EI SK) as (SAR & _ & NR & OKALL & SA8).
    pose proof (i2o_sum_ge0 sp adr (sk_items k) OKALL) as SUM0.
    pose proof (k_call' _ _ _ _ _ _ _ _ EI) as (HEAP & AUX & _ & ST & _ & _ & ERR & MI & CS & _).
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -160)) = bv_unsigned sp + -160) by (apply unsigned_lit; lia).
    unfold Gk. replace (MAX_SCT_LIST_SIZE <? len2) with false by (symmetry; apply Z.ltb_ge; unfold MAX_SCT_LIST_SIZE; lia).
    unfold implM. iprefix. unfold frame2 in FR2. unfold frame1 in FR1.
    pose proof (munch_refl (@nil (Z * Z)) mC) as MU. pose proof (wmono_refl ctusegs mC) as WM.
    (* [comment removed for export] *)
    zstep. zstep. sfalse. zstep. zstep. zstep. zstep.
    ihere. cbn [abind apbind amalloc afree aret ap_embed fst snd]. to_implM.
    eapply (CRYPTO_malloc_walk HM) with (B := B) (lo := lo) (errv := errvC) (n := len2) (L := OWC ++ [] ++ LB); rewrite ?ESP;
      [ exact HEAP| exact AUX| lia| exact ST| exact CEIL| unfold GLOBALS_TOP; lia| unfold CRYPTO_MALLOC_STACK, RMALLOC_STACK; lia
      | exact ERR| exact MI| reflexivity| exact CS| reflexivity| lia| reflexivity|].
    intros pd sL msL PO. unfold calloc_post in PO. rewrite ?ESP in PO.
    destruct PO as (u0 & u1 & u2 & u11 & u12 & u13 & u14 & u15 & u16 & u17 & u3 & u4 & u5 & u6 & mL & AD & errvL
                    & -> & MIL & STL & ERRL & AUXL & HPL & FAL & SOL & BRL & HEAPL & (junk & BLK)).
    replace (ret_pc (Z_to_bv 64 0x19d2c0)) with (Z_to_bv 64 0x19d2c0) by (symmetry; apply ret_pc_even; [lia| reflexivity]). unfold MallocRep.wz.
    pose proof BRL as (AD0 & AD16 & _ & ADC & ADI).
    assert (EIL : EINV (bv_unsigned sp + -160) sL stC mL OWC errvL boC [(pd, AD, len2)]).
    { eapply k_alloc'; [exact EI| exact HPL| exact HEAPL| exact MIL| exact STL| exact ERRL| exact AUXL| exact FAL| exact SOL]. }
    pose proof (agree_of_heap_pres _ _ _ _ HPL) as AGL.
    apply (rw_cells_agree _ _ _ _ _ AGL) in FR1; [| intros a Ha; left; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ AGL) in FR2; [| intros a Ha; left; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ AGL) in HDER; [| intros a Ha; left; cbn in Ha; lia].
    assert (SKL : sk_rep mL LB adr k).
    { eapply sk_rep_agree; [exact AGL| | exact SK]. intros [[qb Ab] nb] a Hb Ha. cbn [blk_addr blk_size fst snd] in Ha.
      right. right. exists (qb, Ab, nb). split; [apply in_app_iff; right; apply in_app_iff; right; exact (sk_allblocks_in _ _ _ _ _ SK Hb)| cbn; lia]. }
    pose proof (sk_facts _ _ _ _ _ _ _ _ EIL SKL) as (_ & RNUM & _).
    clear MU WM HEAP AUX ST ERR MI CS AGL HPL EI SK.
    (* [comment removed for export] *)
    unfold implM. iprefix.
    eapply evt_cut.
    { eapply write_entry_seg with (lo := lo) (SA := adr (sk_blk k)) (n := sk_num k) (AD := AD); rewrite ?ESP;
        [exact STL| exact MIL| unfold GLOBALS_TOP; lia| lia| lia| lia| exact (proj2 SAR)| exact SA8| exact RNUM| lia| lia| lia| exact FR1| exact FR2]. }
    cbv beta. intros ms1 PO.
    destruct PO as (v5 & v6 & v7 & v11 & v12 & v13 & v14 & v15 & v16 & v17 & v28 & v29 & v30 & v31 & m1 & -> & MU1 & WM1 & MI1 & ST1 & FR1' & FR2').
    clear FR1 FR2. rename FR1' into FR1. rename FR2' into FR2.
    xmu HDER MU1 WM1. xmu BLK MU1 WM1.
    assert (EI1 : EINV (bv_unsigned sp + -160) sL stC m1 OWC errvL boC [(pd, AD, len2)]).
    { eapply k_munch'; [exact EIL| exact MU1| exact WM1| exact MI1| exact ST1| lia| apply OWN0; lia]. }
    assert (SK1 : sk_rep m1 LB adr k) by (eapply sk_keep'; [exact EIL| exact SKL| exact MU1| exact WM1| apply OWN0; lia]).
    clear MU1 WM1 MIL STL EIL SKL RNUM.
    pose proof (munch_refl [(lo, bv_unsigned sp + -64); (AD, AD + len2)]%Z m1) as MU. pose proof (wmono_refl ctusegs m1) as WM.
    unfold SKNUM_RET.
    (* [comment removed for export] *)
    assert (CASES : sk_items k = [] \/ exists y t, sk_items k = y :: t) by (clear; destruct (sk_items k) as [|y t]; [left; reflexivity| right; exists y, t; reflexivity]).
    zstep. unfold sk_num. destruct CASES as [EIT|(y & t & EIT)]; rewrite EIT.
    - (* [comment removed for export] *)
      change (zlength (@nil (sctr bptr))) with 0. btaken.
      rewrite EIT in LEN2. cbn [i2o_sum] in LEN2.
      (* [comment removed for export] *)
      zstep. replace (Z_to_bv 64 2) with (Z_to_bv 64 len2) by (rewrite LEN2; reflexivity).
      eapply evt_cut.
      { eapply outer_tail_seg with (lo := lo) (AD := AD) (len2 := len2); rewrite ?ESP;
          [exact ST1| exact MI1| unfold GLOBALS_TOP; lia| lia| lia| exact SP16| lia| lia| lia| exact FR1| exact FR2| exact BLK]. }
      cbv beta. intros ms2 PO. destruct PO as (w11 & w12 & w13 & m2 & bs2 & -> & MU2 & WM2 & MI2 & ST2 & FR1' & HB2).
      xmu HDER MU2 WM2.
      assert (EI2 : EINV (bv_unsigned sp + -64) sL stC m2 OWC errvL boC [(pd, AD, len2)]).
      { eapply k_munch'; [exact EI1| exact MU2| exact WM2| exact MI2| exact ST2| lia|].
        constructor; [left; cbn; lia| constructor; [| constructor]]. right. right. exists pd, AD, len2. cbn [fst snd]. split; [left; reflexivity| lia]. }
      assert (SK2 : sk_rep m2 LB adr k).
      { eapply sk_keep'; [exact EI1| exact SK1| exact MU2| exact WM2|].
        constructor; [left; cbn; lia| constructor; [| constructor]]. right. right. exists pd, AD, len2. cbn [fst snd]. split; [left; reflexivity| lia]. }
      ihere. to_implM.
      eapply from_ret1; [exact EI2| lia| exact FR1'| exact HDER| exact DER8| exact HB2| exact SK2| exact FRM| exact FE].
    - (* [comment removed for export] *)
      assert (T1 : 1 <= zlength (y :: t) < 2^23) by (split; [unfold zlength; cbn [length]; lia| rewrite <- EIT; unfold sk_num in NR; lia]).
      sfalse.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep.
      replace len2 with (2 + (len2 - 2)) in BLK by lia.
      pose proof (cb_split2 m1 AD 2 (len2 - 2) junk BLK ltac:(lia) ltac:(lia)) as [HBP HBJ]. clear BLK.
      eapply evt_cut.
      { eapply (write_loop' (y :: t) [] 2 m1 m1) with (pd := pd) (len2 := len2); unfold INNER_HEAD; rewrite ?ESP;
          [ rewrite EIT; reflexivity| discriminate| first [exact OKALL| rewrite EIT; exact OKALL]| first [exact CALL| rewrite EIT; exact CALL]
          | cbn [i2o_sum]; lia| first [exact LEN2| rewrite EIT; exact LEN2]| lia| apply munch_refl| apply wmono_refl| exact EI1| left; reflexivity
          | exact FR1| exact FR2| exact HDER| exact SK1| exact HBP| exact HBJ]. }
      cbv beta. intros ms2 PO. unfold wl_post in PO.
      destruct PO as (w1 & w5 & w6 & w7 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w23 & w24 & w28 & w29 & w30 & w31 & m2 & bs2
                       & -> & MU2 & WM2 & MI2 & EI2 & FR1' & FR2' & HDER2 & SK2 & HB2).
      clear FR1 FR2 HDER SK1 EI1 HBP HBJ MU WM.
      pose proof (k_call' _ _ _ _ _ _ _ _ EI2) as (_ & _ & _ & ST2 & _).
      pose proof (munch_refl (@nil (Z * Z)) m2) as MU. pose proof (wmono_refl ctusegs m2) as WM.
      unfold INNER_EXIT, frame2 in *. unfold frame1 in FR1'.
      (* [comment removed for export] *)
      zstep. replace (len2 ≫ 16) with 0 by (rewrite Z.shiftr_div_pow2 by lia; symmetry; apply Z.div_small; lia). zstep. btaken.
      eapply evt_cut.
      { eapply outer_tail_seg with (lo := lo) (AD := AD) (len2 := len2); rewrite ?ESP;
          [exact ST2| exact MI2| unfold GLOBALS_TOP; lia| lia| lia| exact SP16| lia| lia| lia| exact FR1'| exact FR2'| exact HB2]. }
      cbv beta. intros ms3 PO. destruct PO as (z11 & z12 & z13 & m3 & bs3 & -> & MU3 & WM3 & MI3 & ST3 & FR1 & HB3).
      xmu HDER2 MU3 WM3.
      assert (EI3 : EINV (bv_unsigned sp + -64) sL stC m3 OWC errvL boC [(pd, AD, len2)]).
      { eapply k_munch'; [exact EI2| exact MU3| exact WM3| exact MI3| exact ST3| lia|].
        constructor; [left; cbn; lia| constructor; [| constructor]]. right. right. exists pd, AD, len2. cbn [fst snd]. split; [left; reflexivity| lia]. }
      assert (SK3 : sk_rep m3 LB adr k).
      { eapply sk_keep'; [exact EI2| exact SK2| exact MU3| exact WM3|].
        constructor; [left; cbn; lia| constructor; [| constructor]]. right. right. exists pd, AD, len2. cbn [fst snd]. split; [left; reflexivity| lia]. }
      ihere. to_implM.
      eapply from_ret1; [exact EI3| lia| exact FR1| exact HDER2| exact DER8| exact HB3| exact SK3| exact FRM| exact FE].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma inner_exit : forall stC sC OWC (errvC : word) boC (FC : bvmap 5 word) (fcC : bv 32),
    DER mod 8 = 0 -> frm0 fcC -> (forall rr : reg, bv_unsigned rr <> 10 -> reg_get FC rr = reg_get F rr) ->
    len_done sp gp m s LB E lo B canary K adr k DER B0T kont QQ ra0 e8 e9 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 stC sC OWC errvC boC FC fcC (2 + i2o_sum (sk_items k)).
  Proof using KN KS bo k_call' k_exit' k_munch' raise_B_seq' sk_keep' write_loop'.
    intros until fcC. intros DER8 FRM FE. unfold len_done. intros until j3. intros EI FR1 FR2 FR3 HDER SK CALL. pose proof SPR' as SPR.
    unfold I2D_SCT_LIST_STACK, ERR_SET_ERROR_STACK in LOB.
    pose proof (sk_facts _ _ _ _ _ _ _ _ EI SK) as (SAR & _ & NR & OKALL & _).
    pose proof (i2o_sum_ge0 sp adr (sk_items k) OKALL) as SUM0.
    pose proof (k_call' _ _ _ _ _ _ _ _ EI) as (_ & _ & _ & ST & _ & _ & _ & MI & _).
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -256)) = bv_unsigned sp + -256) by (apply unsigned_lit; lia).
    set (tot := 2 + i2o_sum (sk_items k)) in *. assert (TB : 2 <= tot <= 2 + 196702 * 2^23) by (unfold tot, sk_num in *; lia).
    unfold implM. iprefix. unfold frame3 in FR3. unfold INNER_EXIT.
    pose proof (munch_refl (@nil (Z * Z)) mD) as MU. pose proof (wmono_refl ctusegs mD) as WM.
    destruct (Z.leb_spec tot 65535) as [LE|GT].
    - (* [comment removed for export] *)
      zstep. replace (tot ≫ 16) with 0 by (rewrite Z.shiftr_div_pow2 by lia; symmetry; apply Z.div_small; lia). zstep. btaken. zstep. btaken.
      eapply evt_cut. { eapply i2o_list_epilogue with (lo := lo); rewrite ?ESP; [exact ST| exact MI| lia| lia| exact FR3]. }
      cbv beta. intros ms2 [-> ST2]. rewrite ?ESP in *. rewrite (unsigned_lit tot), (swrap32_small tot) by lia.
      replace (bv_unsigned sp + -256 + 96) with (bv_unsigned sp + -160) in * by lia.
      replace (ret_pc (Z_to_bv 64 0x19d2a8)) with (Z_to_bv 64 0x19d2a8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      ihere. to_implM.
      assert (EI2 : EINV (bv_unsigned sp + -160) sC stC mD OWC errvC boC []).
      { eapply k_munch'; [exact EI| apply munch_refl| apply wmono_refl| exact MI| exact ST2| lia| constructor]. }
      eapply some_path; [exact EI2| reflexivity| lia| exact CALL| exact FR1| exact FR2| exact HDER| exact DER8| exact SK| exact FRM| exact FE].
    - (* [comment removed for export] *)
      zstep. rewrite Z.shiftr_div_pow2 by lia. zstep. sfalse. zstep. zstep. btaken.
      rewrite <- (Z_to_bv_mod64 (-1)). change ((-1) mod 2 ^ 64) with 18446744073709551615.
      eapply evt_cut. { eapply i2o_list_epilogue with (lo := lo); rewrite ?ESP; [exact ST| exact MI| lia| lia| exact FR3]. }
      cbv beta. intros ms2 [-> ST2]. rewrite ?ESP in *. rewrite (unsigned_lit 18446744073709551615), (swrap32_high 18446744073709551615) by lia.
      change (18446744073709551615 - 2 ^ 64) with (-1).
      replace (bv_unsigned sp + -256 + 96) with (bv_unsigned sp + -160) in * by lia.
      replace (ret_pc (Z_to_bv 64 0x19d2a8)) with (Z_to_bv 64 0x19d2a8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      zstep. zstep. btaken.
      ihere. to_implM.
      assert (EI2 : EINV (bv_unsigned sp + -160) sC stC mD OWC errvC boC []).
      { eapply k_munch'; [exact EI| apply munch_refl| apply wmono_refl| exact MI| exact ST2| lia| constructor]. }
      unfold Gk. replace (MAX_SCT_LIST_SIZE <? tot) with true by (symmetry; apply Z.ltb_lt; unfold MAX_SCT_LIST_SIZE; lia).
      eapply implM_apbind.
      { eapply raise_B_seq'; [exact EI2| rewrite <- Zplus_mod_idemp_l, SP16; reflexivity| unfold ERR_SET_ERROR_STACK; lia| exact FRM]. }
      intros [u2 st2] s2 ms2 RP. unfold rpost in RP. cbn [fst snd] in RP.
      destruct RP as (w1 & w5 & w6 & w7 & w10 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w28 & w29 & w30 & w31 & F2' & fc2 & m4 & OW2 & errv2 & bo2 & -> & EI4 & LX4 & FRM4 & FE4).
      cbn [app] in LX4. pose proof (agree_of_lx_pres _ _ _ _ _ LX4) as AG4.
      assert (CL4 : forall a, bv_unsigned sp + -160 <= a -> a < 2^64 -> lx_client LB (bv_unsigned sp + -160) LIBW_AP a).
      { intros a Ha Hb. split; [unfold LIBW_AP; cbn [rin_ivs fst snd]; lia| left; exact Ha]. }
      apply (rw_cells_agree _ _ _ _ _ AG4) in FR1; [| intros a Ha; apply CL4; cbn in Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ AG4) in FR2; [| intros a Ha; apply CL4; cbn in Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ AG4) in HDER; [| intros a Ha; apply CL4; cbn in Ha; lia].
      pose proof (k_facts' _ _ _ _ _ _ _ _ EI2) as (HEAP3 & _).
      assert (SK4 : sk_rep m4 LB adr k).
      { eapply sk_rep_agree; [exact AG4| | exact SK]. intros [[qb Ab] nb] a Hb Ha. cbn [blk_addr blk_size fst snd] in Ha.
        pose proof (sk_allblocks_in _ _ _ _ _ SK Hb) as HbL.
        pose proof (blk_bounds _ _ _ _ _ _ HEAP3 ltac:(apply in_app_iff; right; apply in_app_iff; right; exact HbL)) as (B1 & B2 & B3' & B4 & B5).
        split; [unfold LIBW_AP; cbn [rin_ivs fst snd]; lia|]. right. left. exists (qb, Ab, nb). split; [exact HbL| cbn; lia]. }
      replace (ret_pc (Z_to_bv 64 RAISE_RET_B)) with (Z_to_bv 64 RAISE_RET_B) by (symmetry; apply ret_pc_even; [unfold RAISE_RET_B; lia| reflexivity]).
      cbv beta.
      eapply ret_none_tail; [exact EI4| exact FR1| exact FR2| exact HDER| exact SK4| exact FRM4|].
      intros rr Hr. rewrite (FE4 rr Hr). apply (FE rr Hr).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma capstone_act : forall (tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (errv : word),
    ap_pre s st m OW LB E bo sp lo B errv canary I2D_SCT_LIST_STACK -> tp = wz RATP -> frm0 fc ->
    (forall b, In b K -> In b OW) -> (forall b, In b K -> ~ In (blk_id b) (es_ids st ++ env_ids E)) ->
    sk_rep m LB adr k -> rw_cells ctusegs m DER [C8 (wz 0)] -> DER mod 8 = 0 -> a0 = wz (adr (sk_blk k)) -> a1 = wz DER ->
    implM ctusegs (interp (ap_embed (i2d_sct_list_cps k kont st))) s QQ
      (MS (mkR ra0 sp gp tp t0 t1 t2 e8 e9 a0 a1 a2 a3 a4 a5 a6 a7 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 t3 t4 t5 t6)
          F (wz I2D_SCT_LIST) fc None m (seg_rom ctusegs)).
  Proof using KS k_call' k_exit' k_munch' len_loop' raise_B_seq' sk_keep' write_loop'.
    intros until errv. intros PRE -> FRM KO KI SK HDER DER8 -> ->. pose proof SPR' as SPR.
    pose proof LOB as LOB0. unfold I2D_SCT_LIST_STACK, ERR_SET_ERROR_STACK in LOB.
    destruct (einv_entry sp m s LB E lo B canary K (XC DER) st OW bo errv I2D_SCT_LIST_STACK PRE ltac:(unfold I2D_SCT_LIST_STACK, ERR_SET_ERROR_STACK; lia) KO KI) as (EI & _ & _).
    pose proof (k_call' _ _ _ _ _ _ _ _ EI) as (_ & _ & _ & ST & _ & _ & _ & MI & _).
    pose proof (sk_facts _ _ _ _ _ _ _ _ EI SK) as (SAR & RNUM & NR & OKALL & SA8).
    pose proof (i2o_sum_ge0 sp adr (sk_items k) OKALL) as SUM0.
    unfold MallocRep.wz in *. unfold implM. iprefix.
    eapply evt_cut.
    { eapply i2d_entry_seg with (lo := lo) (SA := adr (sk_blk k)) (n := sk_num k) (DER := DER);
        [exact ST| exact MI| unfold GLOBALS_TOP; lia| lia| exact SP16| lia| exact (proj2 SAR)| exact SA8| exact RNUM| lia| reflexivity| reflexivity]. }
    cbv beta. intros ms1 PO.
    destruct PO as (v5 & v6 & v7 & v11 & v12 & v13 & v14 & v15 & v16 & v17 & v28 & v29 & v30 & v31 & m1 & j1 & j2 & j3 & -> & MU1 & WM1 & MI1 & ST1 & FR1 & FR2 & FR3).
    xmu HDER MU1 WM1.
    assert (EI1 : EINV (bv_unsigned sp + -256) s st m1 OW errv bo []).
    { eapply k_munch'; [exact EI| exact MU1| exact WM1| exact MI1| exact ST1| lia| apply OWN0; lia]. }
    assert (SK1 : sk_rep m1 LB adr k) by (eapply sk_keep'; [exact EI| exact SK| exact MU1| exact WM1| apply OWN0; lia]).
    pose proof (sk_facts _ _ _ _ _ _ _ _ EI1 SK1) as (_ & RNUM1 & _).
    clear MU1 WM1 MI ST EI SK RNUM.
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -256)) = bv_unsigned sp + -256) by (apply unsigned_lit; lia).
    pose proof (munch_refl (@nil (Z * Z)) m1) as MU. pose proof (wmono_refl ctusegs m1) as WM.
    unfold SKNUM_RET.
    assert (CASES : sk_items k = [] \/ exists y t, sk_items k = y :: t) by (clear; destruct (sk_items k) as [|y t]; [left; reflexivity| right; exists y, t; reflexivity]).
    (* [comment removed for export] *)
    zstep. unfold sk_num. destruct CASES as [EIT|(y & t & EIT)]; rewrite EIT.
    - (* [comment removed for export] *)
      change (zlength (@nil (sctr bptr))) with 0. btaken.
      (* [comment removed for export] *)
      zstep. zstep. btaken.
      eapply evt_cut. { eapply i2o_list_epilogue with (lo := lo); rewrite ?ESP; [exact ST1| exact MI1| lia| lia| exact FR3]. }
      cbv beta. intros ms2 [-> ST2]. rewrite ?ESP in *. rewrite (unsigned_lit 2), (swrap32_small 2) by lia.
      replace (bv_unsigned sp + -256 + 96) with (bv_unsigned sp + -160) in * by lia.
      replace (ret_pc (Z_to_bv 64 0x19d2a8)) with (Z_to_bv 64 0x19d2a8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      ihere. to_implM.
      assert (EI2 : EINV (bv_unsigned sp + -160) s st m1 OW errv bo []).
      { eapply k_munch'; [exact EI1| apply munch_refl| apply wmono_refl| exact MI1| exact ST2| lia| constructor]. }
      unfold i2d_sct_list_cps. rewrite EIT.
      lazymatch goal with |- implM _ _ _ _ ?ms => change (implM ctusegs (interp (ap_embed (GK (Some 2) st))) s QQ ms) end.
      eapply some_path; [exact EI2| rewrite EIT; reflexivity| lia| rewrite EIT; constructor| exact FR1| exact FR2| exact HDER| exact DER8| exact SK1| exact FRM| intros rr Hr; reflexivity].
    - (* [comment removed for export] *)
      assert (T1 : 1 <= zlength (y :: t) < 2^23) by (split; [unfold zlength; cbn [length]; lia| rewrite <- EIT; unfold sk_num in NR; lia]).
      sfalse.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep.
      ihere. to_implM. unfold i2d_sct_list_cps.
      eapply (len_loop' (sk_items k) [] 2); unfold INNER_HEAD; rewrite ?ESP;
        [ reflexivity| first [exact OKALL| rewrite EIT; exact OKALL]| rewrite EIT; discriminate| lia| unfold sk_num in NR; lia| constructor
        | exact EI1| exact FR1| exact FR2| exact FR3| exact HDER| exact SK1| exact FRM| intros rr Hr; reflexivity
        | apply inner_exit; [exact DER8| exact FRM| intros rr Hr; reflexivity]].
  Qed.

  End Act.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem i2d_sct_list_ok : i2d_sct_list_spec.
  Proof using HF HM.
    unfold i2d_sct_list_spec. intros until DER. intros PRE TP FRM KO KI SK DERlo DERhi HDER DER8 A0 A1 KN KS.
    pose proof PRE as (_ & _ & _ & _ & _ & SPB & B63 & _ & CEIL & GLO & LOB & _ & _ & _ & SP16). unfold GLOBALS_TOP in GLO.
    eapply capstone_act with (DER := DER) (k := k) (adr := adr) (K := K) (lo := lo) (B := B); eassumption.
  Qed.
End Proofs.
End WithCeiling0.
