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
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem RzCPS. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Monad Stdio Prog BnBase BnModel BnTree ApBase ApState ApLogic ApInv ApErr ApParse ApPrim.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface RT_client_kit D_defs D_cs I_lkit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnP Require Import BnKit BnKit2.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnW Require Import BnTac BnMem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnAsan Require Import AsKit AsLoop.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import R_unwind_chain.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import RT_iface2 LibKitA ARun BnHeapA BnRepDefs BnRepA ImplA ImplAX BnIfaceA AsStruct RtCallA W_cryptoA UnwindA EdgesA UnwindX.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtFrameA Require Import AFrameKit AFrameCall AFrameTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require Import ApCells.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require W_get_object W_get_object_walk W_check_tlen.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApUTacB.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import I_strcpyA ApATac ApATacX ApBImg ApWalkTac ApRepDefs ApRep ApIface ApFrame W_akit W_get_objectA W_check_tlenA
     W_item_d2i_stmtA W_item_d2i_imgA W_c2i_stmtA W_frkitA Fr_asn1_check_tlen Fr_asn1_d2i_ex_primitive W_item_d2i_exA W_item_d2i_tailA W_err_set_debugA W_asn1_stringA W_prefix_create W_bio_push.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require ApErrKit ApErrKit2.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import PzBitsA.   (* [comment removed for export] *)
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


(* [comment removed for export] *)
Lemma slice_bytesA : forall (m : mem) D d p len,
  bytes_at ctasegs m D (to_bytes d) -> 0 <= p -> 0 <= len -> p + len <= zlength d ->
  bytes_at ctasegs m (D + p) (firstn (Z.to_nat len) (skipn (Z.to_nat p) (to_bytes d))) /\ Z.of_nat (length (firstn (Z.to_nat len) (skipn (Z.to_nat p) (to_bytes d)))) = len.
Proof.
  intros m D d p len HB Hp Hl Hpl. unfold zlength in Hpl. split.
  - replace (D + p) with (D + Z.of_nat (Z.to_nat p)) by lia. apply bytes_at_firstn. apply bytes_at_skipn; [exact HB| unfold to_bytes; rewrite length_map; lia].
  - unfold to_bytes. rewrite length_firstn, length_skipn, length_map. lia.
Qed.
(* [comment removed for export] *)
Local Notation E_ex_tnew := (E_asn1_d2i_ex_primitive_244f68 : uk_call 0x24187c 0x2424f0 0x224b04).    (* [comment removed for export] *)
Local Notation E_ex_set1 := (E_asn1_d2i_ex_primitive_244fb4 : uk_call 0x24187c 0x242540 0x2249e8).    (* [comment removed for export] *)


Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation FR := (@ar_FR AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

Section Body.

  (* [comment removed for export] *)
  Variables (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word).
  Variables (m : mem) (Σ : rts RT) (st : ap_st bptr) (OW LB : list block) (E : ap_env) (bo : Z * Z) (lo : Z) (K : list block).
  Variables (D : Z) (d : list Z) (op totlen utype e OPP PV TLC : Z) (j31 : list byte).
  Variables (f spa : Z) (g : nat) (junk gj : list byte) (Σ1 : rts RT) (m3 : mem).
  Local Notation gr := (get_object d op totlen).
  Local Notation plen := (go_len (get_object d op totlen)).
  Local Notation cont := (go_p (get_object d op totlen)).

  (* [comment removed for export] *)
  Hypothesis PRE0 : ap_preA Σ st m OW LB E bo sp lo EXPRIM_STACK_A (EXPRIM_COST_A plen) EXPRIM_FRAMES_A.
  Hypothesis ENT : d2i_entryA e utype.
  (* [comment removed for export] *)
  Variable ras : list Z.
  Hypothesis UW : uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras.
  Hypothesis CTX : uk_ctx ADEP_ENTRY (bv_unsigned ra :: ras).
  Hypothesis KOW : forall b, In b K -> In b OW.
  Hypothesis KIDS : forall b, In b K -> ~ In (blk_id b) (es_ids st ++ env_ids E).
  Hypothesis PAY : payload_okA m LB D d.
  Hypothesis OP0 : 0 <= op.
  Hypothesis TL0 : 0 < totlen.
  Hypothesis OPT : op + totlen <= zlength d.
  Hypothesis EG : go_err gr = None.
  Hypothesis ETAG : go_tag gr = utype.
  Hypothesis ECLS : go_cls gr = 0.
  Hypothesis ERET : Z.land (go_ret gr) 32 = 0.
  Hypothesis COPP : cellA_in LB OPP 8.
  Hypothesis CPV : cellA_in LB PV 8.
  Hypothesis CTLC : cellA_in LB TLC 32.
  Hypothesis ALO : OPP mod 8 = 0.
  Hypothesis ALV : PV mod 8 = 0.
  Hypothesis ALT : TLC mod 8 = 0.
  Hypothesis DOV : OPP + 8 <= PV \/ PV + 8 <= OPP.
  Hypothesis DOT : OPP + 8 <= TLC \/ TLC + 32 <= OPP.
  Hypothesis DVT : PV + 8 <= TLC \/ TLC + 32 <= PV.
  Hypothesis DOD : OPP + 8 <= D \/ D + zlength d <= OPP.
  Hypothesis DVD : PV + 8 <= D \/ D + zlength d <= PV.
  Hypothesis DTD : TLC + 32 <= D \/ D + zlength d <= TLC.
  Hypothesis HOPP : rw_cells ctasegs m OPP [C8 (wz (D + op))].
  Hypothesis HPV : rw_cells ctasegs m PV [C8 (wz 0)].
  Hypothesis HTLC : rw_cells ctasegs m TLC (tlc_in j31).

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

  Local Ltac ctx := pose proof (ex_ctx sp m Σ st OW LB E bo lo D d op totlen utype e OPP PV TLC f spa g PRE0 ENT PAY OP0 TL0 OPT EG ETAG ECLS ERET COPP CPV CTLC FRESH GEO SPAL SPAH)
                      as (DF & D0 & D63 & D26 & CL1 & CL2 & CL3 & CEIL & LO0 & LO & ESS & TOP & SPR & DLEN & ESPA & G1 & G2 & G3 & G4 & Ef & G5 & FSH & SHR1 & SHR2 & GB1 & GB2 & GB3 & UTR
                                             & (bd & Hbd & BD1 & BD2 & BD3 & BD4 & BD5 & OD) & (bq & Hbq & BQ1 & BQ2 & BQ3 & BQ4 & BQ5 & OQ)
                                             & (bv & Hbv & BV1 & BV2 & BV3 & BV4 & BV5 & OV) & (bt & Hbt & BT1 & BT2 & BT3 & BT4 & BT5 & OT));
                    unfold off_fr in OD, OQ, OV, OT; change (fs_size 2) with 256 in OD, OQ, OV, OT; cbn [blk_addr blk_size fst snd] in OD, OQ, OV, OT;
                    hide BD5; hide BQ5; hide BV5; hide BT5; hide OD; hide OQ; hide OV; hide OT; hide G5.
  Local Ltac hide_disj := hide DOV; hide DOT; hide DVT; hide DOD; hide DVD; hide DTD.
  Local Notation POST := (@exprim_postA AR ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB E bo lo m K OPP PV TLC utype plen).
  Local Notation XIV := ([(OPP, OPP + 8); (PV, PV + 8); (TLC, TLC + 32)] ++ LIBW_A).
  Local Notation AFACTS := (ex_arm_facts ra sp s0 m Σ st LB E bo lo K D d op totlen utype OPP PV TLC f spa g junk).


  (* [comment removed for export] *)
  Lemma exprim_oct_armA : forall qc qfc Σ4 OW4 m9 jt4 (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (F' : bvmap 5 word) (fc' : bv 32)
      (j0 j8 j16 j64 j72 j80 j104 j120 j128 j136 j144 : list byte),
    utype = V_ASN1_OCTET_STRING ->
    AFACTS qc qfc Σ4 OW4 m9 jt4 j0 j8 j16 j64 j72 j80 j104 j120 j128 j136 j144 ->
    @implAp (push AR f 2) _ (abind (amalloc SZ_ASN1_STRING) (fun blk =>
                               if plen =? 0 then aret (Some (mkStr blk None))
                               else abind (amalloc plen) (fun dp => aret (Some (mkStr blk (Some (dp, plen)))))) st) Σ4 POST
      (ex_arm_ms sp gp d op totlen utype f spa EX_OCT_ARM x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 F' fc' m9).
  Proof.
    intros until j144. intros UO AF. hide_disj. ctx.
    pose proof PRE0 as (HEAP & AS & IDS & DC & ST & CEIL' & LOSP & TOP' & AL16 & MI & CRED & FRM).
    destruct AF as (HEAP9 & PRE9 & CRA & CRB & KEPT9 & AXF & FRLA & F96 & F104 & F110 & F111 & F112 & F120 & FRLB & FRH & HCONT & HFC & HOPP9 & HPV9 & HTLC9 & PAY9).
    pose proof PRE9 as (_ & AS9 & IDS9 & DC9 & ST9 & CEIL9 & _ & TOP9 & AL9 & MI9 & _ & _). rewrite ?ESPA in ST9, TOP9, AL9.
    unfold ex_arm_ms, EX_OCT_ARM, ex_lowB, MallocRep.wz in *. clear HTLC9. pose proof PAY9 as (HB & _).
    assert (OFFLB : forall b, In b LB -> off_fr f 2 b) by (intros b Hb; apply FRESH; apply in_or_app; right; exact Hb).
    assert (EC : GETOBJ_ERR_COST_A = 13) by reflexivity.
    assert (ESK : ASN1_STRING_TYPE_NEW_STACK + 208 <= CHECK_TLEN_STACK_A /\ ASN1_STRING_SET_STACK + 208 <= CHECK_TLEN_STACK_A /\ mcost 24 = 0).
    { unfold ASN1_STRING_TYPE_NEW_STACK, ASN1_STRING_SET_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, CHECK_TLEN_STACK_A, ACTL_FRAME, GETOBJ_STACK_A, ERR_SET_ERROR_STACK, ERR_VSET_ERROR_STACK. split; [clear; lia|]. split; [clear; lia| reflexivity]. }
    pose proof (mcost_nonneg plen ltac:(clear - GB2; lia)) as MC0.
    assert (INL : forall b, In b LB -> In b (ex_pbs f qc qfc ++ LB)) by (intros b Hb; apply in_or_app; right; exact Hb).
    assert (CSR : forall a, client_static a -> 5958600 <= a < 12365008). (* [comment removed for export] *)
    { intros a [(l & h & Hin & Hlh) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin. clear - Hin Hlh. destruct Hin as [E0|[E0|[E0|[]]]]; injection E0 as <- <-; lia. }
    assert (EPV : bv_unsigned (Z_to_bv 64 PV) = PV) by (apply unsigned_lit; clear - BV1 BV2 BV3 BV4 CL3; unfold BnHeapA.ACEIL in *; lia).
    pose proof (AH_offsh _ _ _ _ bv HEAP (in_or_app _ _ _ (or_intror Hbv))) as ROV. unfold SHLO, SHHI in ROV.
    pose proof (proj2 (@AH_acc (push AR f 2) _ _ _ _ bv HEAP9 ltac:(apply in_or_app; right; apply INL; exact Hbv))) as ACCV.
    assert (PL31 : plen < 2 ^ 26) by (clear - GB1 GB2 GB3 OPT D26 OP0; lia).
    (* [comment removed for export] *)
    pose proof (munch_refl [(spa, spa + 96)]%Z m9) as MU. pose proof (wmono_refl ctasegs m9) as WM.
    assert (OFFW : offshW [(spa, spa + 96)]%Z) by (cbn [offshW]; unfold SHLO, SHHI; clear - CL2 CEIL LO ESS SPAL; lia).
    freeze HOPP9. freeze HFC. freeze HCONT. freeze HB. hide ROV.
    apply implAp_from_evt.
    step. step. rewrite (unsigned_lit plen) by (clear - GB2 PL31; lia). rewrite Z.add_0_r, (bk_swrap32_small plen) by (clear - GB2 PL31; lia). if_false.
    step. step. if_cases K30; zc K30; [clear K30| exfalso; clear - K30 UO; unfold V_ASN1_OCTET_STRING in UO; lia].
    step. step. if_cases K28; zc K28; [clear K28| exfalso; clear - K28 UO; unfold V_ASN1_OCTET_STRING in UO; lia].
    lazymatch goal with |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv ?mm ?ro) =>
      let pt := eval vm_compute in (bv_key (Z_to_bv 5 10)) in
      eapply (evt_cut segs (fun ms => exists vt : word, ms = MS (tset pt vt R) F (Z_to_bv 64 0x2424a8) fc rv mm ro)) end.
    { step. step. if_cases K14; zc K14.
      - step. step. if_cases K12; zc K12; [apply evt_done; eexists; map_cbv_set; reflexivity|].
        step. step. if_cases K23; zc K23; [| exfalso; clear - K23 UO; unfold V_ASN1_OCTET_STRING in UO; lia]. apply evt_done; eexists; map_cbv_set; reflexivity.
      - step. step. if_cases K24; zc K24; [| exfalso; clear - K24 UO; unfold V_ASN1_OCTET_STRING in UO; lia].
        step. step. if_cases K12; zc K12; [apply evt_done; eexists; map_cbv_set; reflexivity|].
        step. step. if_cases K23; zc K23; [| exfalso; clear - K23 UO; unfold V_ASN1_OCTET_STRING in UO; lia]. apply evt_done; eexists; map_cbv_set; reflexivity. }
    intros ms1 (vt & ->). map_cbv_set.
    (* [comment removed for export] *)
    rewrite ?EPV. step. rewrite ?EPV. step. step.
    step. rewrite ?EPV. step. step. step. if_true.
    (* [comment removed for export] *)
    step. name_mem ma.
    match goal with H : munch _ m9 ma |- _ => rename H into MUa end. match goal with H : wmono ctasegs m9 ma |- _ => rename H into WMa end.
    match goal with H : stk ctasegs ma lo _ |- _ => rename H into STa end. match goal with H : mem_inv ctasegs ma |- _ => rename H into MIa end.
    step. apply evt_done.
    assert (HEAPa : @BnHeapA.AHEAP (push AR f 2) Σ4 OW4 (ex_pbs f qc qfc ++ LB) ma).
    { eapply (@AH_frame (push AR f 2)); [exact HEAP9| exact MUa| exact WMa|]. constructor; [left; cbn [fst snd]; clear - CEIL9 LO SPAL ESS TOP9 SPAH TOP; plia| constructor]. }
    pose proof (agree_on_of_munch_nw _ _ _ MUa) as AGa. clear MUa WMa.
    assert (AGLa : agree_on (lib_addr OW4) m9 ma).
    { eapply agree_on_mono; [exact AGa|]. intros a [HS|(b & Hb & Hr)]; cbn [outside fst snd].
      - pose proof (LIBW_S_A a HS) as HA. unfold LIBW_A in HA. cbn [rin_ivs fst snd] in HA. clear - HA CL1 CEIL LO ESS SPAL. lia.
      - pose proof (@AH_range_gen (push AR f 2) _ _ _ _ b HEAP9 (in_or_app _ _ _ (or_introl Hb))) as (_ & _ & _ & R3 & _). clear - Hr R3 CEIL9 LO ESS SPAL. plia. }
    pose proof (ap_state_agree _ _ _ _ _ _ AS9 AGLa) as ASa. pose proof ASa as (_ & (CSa & RSa & _) & _).
    unfold abind, amalloc. cbn [apbind].
    (* [comment removed for export] *)
    assert (AXa : ax_pres LB (bv_unsigned sp) XIV m ma).
    { eapply ax_pres_trans; [exact AXF|]. unfold ax_pres. eapply agree_on_mono; [exact AGa|]. intros a [_ Ha]. cbn [outside fst snd]. destruct Ha as [H1|[H1|(b & Hb & Hr)]].
      + clear - H1 SPAH. lia.
      + pose proof (CSR a H1) as HA. clear - HA CL1 CEIL LO ESS SPAL. lia.
      + pose proof (AH_range_gen _ _ _ _ b HEAP (in_or_app _ _ _ (or_intror Hb))) as (_ & _ & _ & R3 & _). clear - Hr R3 CEIL LO ESS SPAL. lia. }
    eapply (@ASN1_STRING_type_new_walkA (push AR f 2) UK BE) with (lo := lo) (ty := utype); rewrite ?ESPA;
      [exact HEAPa| exact STa| exact CEIL9| clear - LO SPAL ESK; lia| exact TOP9| exact AL9| exact MIa| reflexivity| exact CSa| reflexivity| clear - UTR; lia
      | uw_call_axX_tac m 16 UW AXa FRH; [clear; lia
          | intros a Ha; apply rin_ivs_app in Ha as [Ha|Ha]; [cbn [rin_ivs fst snd app] in Ha; clear - Ha BQ2 BQ4 BV2 BV4 BT2 BT4 CEIL LO ESS; lia
              | pose proof (libw_below a Ha) as Hb; unfold SEGTOP_A in Hb; clear - Hb CL1 CEIL LO ESS; lia]
          | clear - SPAH; lia | uchk_open; clear - AL16; Z.div_mod_to_equations; lia | clear - TOP; unfold USTACK_TOP in *; lia]
      | rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_ex_tnew CTX) |].
    intros p Σb msb NIp POb.
    destruct POb as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & Fb & fcb & mb & A & -> & MIb & STb & AGb & CRb & BRA & HEAPb & ACCA & CELLb).
    cbn [apbind fst snd]. unfold MallocRep.wz in *. rewrite ?ESPA in *. rewrite (ret_pc_even 0x2424f0) by (clear; lia). cbn [ar_RT push amb] in CRb.
    pose proof BRA as (BA0 & BA16 & _ & BAC & BAS). change (@BnHeapA.ACEIL (push AR f 2)) with (@BnHeapA.ACEIL AR) in BAC.
    assert (NIp4 : ~ In p (map blk_id OW4)) by (intros X; apply NIp; rewrite map_app; apply in_or_app; left; exact X).
    (* [comment removed for export] *)
    assert (AGS : forall A0 cs, rw_cells ctasegs ma A0 cs -> spa <= A0 -> A0 + Z.of_nat (cells_size cs) <= USTACK_TOP -> rw_cells ctasegs mb A0 cs).
    { intros A0 cs HC H1 H2. eapply rw_cells_agree; [exact AGb| exact HC|]. intros a Ha. left. clear - Ha H1 H2. lia. }
    apply AGS in FRLA; [| clear; lia| cbn; clear - SPAH TOP; unfold USTACK_TOP in *; lia]. apply AGS in F96; [| clear; lia| cbn; clear - SPAH TOP; unfold USTACK_TOP in *; lia].
    apply AGS in F104; [| clear; lia| cbn; clear - SPAH TOP; unfold USTACK_TOP in *; lia]. apply AGS in F110; [| clear; lia| cbn; clear - SPAH TOP; unfold USTACK_TOP in *; lia].
    apply AGS in F111; [| clear; lia| cbn; clear - SPAH TOP; unfold USTACK_TOP in *; lia]. apply AGS in F112; [| clear; lia| cbn; clear - SPAH TOP; unfold USTACK_TOP in *; lia].
    apply AGS in F120; [| clear; lia| cbn; clear - SPAH TOP; unfold USTACK_TOP in *; lia].
    apply AGS in FRLB; [| clear; lia| cbn [cells_size csize Nat.add]; rewrite ?Nat2Z.inj_add; clear - GSZ SPAH TOP; unfold USTACK_TOP in *; lia].
    apply AGS in FRH; [| clear - SPAH; lia| cbn; clear - TOP; unfold USTACK_TOP in *; lia]. clear AGS.
    unfold frozen in HOPP9, HFC, HCONT, HB.
    apply (rw_cells_agree _ _ _ _ _ AGa) in HOPP9; [| intros a Ha; cbn in Ha; cbn [outside fst snd]; clear - Ha BQ1 BQ2 BQ4 CEIL LO ESS SPAL; lia].
    apply (rw_cells_agree _ _ _ _ _ AGb) in HOPP9; [| intros a Ha; cbn in Ha; right; right; exists bq; split; [apply in_or_app; right; apply INL; exact Hbq| clear - Ha BQ1 BQ2; lia]].
    apply (rw_cells_agree _ _ _ _ _ AGb) in HPV9; [| intros a Ha; cbn in Ha; right; right; exists bv; split; [apply in_or_app; right; apply INL; exact Hbv| clear - Ha BV1 BV2; lia]].
    apply (rw_cells_agree _ _ _ _ _ AGa) in HFC; [| intros a Ha; cbn in Ha; cbn [outside fst snd]; clear - Ha G3 CEIL LO ESS SPAL; plia].
    apply (rw_cells_agree _ _ _ _ _ AGb) in HFC; [| intros a Ha; cbn in Ha; right; right; exists (qfc, f + 64, 1); split; [apply in_or_app; right; apply in_or_app; left; right; left; reflexivity| cbn; clear - Ha; lia]].
    apply (rw_cells_agree _ _ _ _ _ AGa) in HCONT; [| intros a Ha; cbn in Ha; cbn [outside fst snd]; clear - Ha G3 CEIL LO ESS SPAL; plia].
    apply (rw_cells_agree _ _ _ _ _ AGb) in HCONT; [| intros a Ha; cbn in Ha; right; right; exists (qc, f + 32, 8); split; [apply in_or_app; right; apply in_or_app; left; left; reflexivity| cbn; clear - Ha; lia]].
    rewrite <- DLEN in BD2.
    apply (bytes_at_agree _ _ _ _ _ AGa) in HB; [| intros a Ha; cbn [outside fst snd]; clear - Ha BD1 BD2 BD4 CEIL LO ESS SPAL; lia].
    apply (bytes_at_agree _ _ _ _ _ AGb) in HB; [| intros a Ha; right; right; exists bd; split; [apply in_or_app; right; apply INL; exact Hbd| clear - Ha BD1 BD2; lia]].
    rewrite DLEN in BD2.
    assert (AGL9b : agree_on (lib_addr OW4) m9 mb).
    { eapply agree_on_trans; [exact AGLa|]. eapply agree_on_mono; [exact AGb|]. intros a Ha. exact (lib_addr_aclient OW4 _ spa a Ha). }
    assert (AXb : ax_pres LB (bv_unsigned sp) XIV m mb).
    { eapply ax_pres_trans; [exact AXF|]. unfold ax_pres. eapply agree_on_trans.
      - eapply agree_on_mono; [exact AGa|]. intros a [_ Ha]. cbn [outside fst snd]. destruct Ha as [H1|[H1|(b & Hb & Hr)]].
        + clear - H1 SPAH. lia.
        + pose proof (CSR a H1) as HA. clear - HA CL1 CEIL LO ESS SPAL. lia.
        + pose proof (AH_range_gen _ _ _ _ b HEAP (in_or_app _ _ _ (or_intror Hb))) as (_ & _ & _ & R3 & _). clear - Hr R3 CEIL LO ESS SPAL. lia.
      - eapply agree_on_mono; [exact AGb|]. intros a [_ Ha]. eapply acl_sub; [| | exact Ha]; [intros b Hb; apply in_or_app; right; exact (INL b Hb)| clear - SPAH; lia]. }
    pose proof (ap_state_rt _ _ _ _ _ _ _ _ ASa AGb) as ASb. pose proof ASa as (_ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & ODa)).
    pose proof (data_cells_rt _ _ _ _ _ _ _ _ ASa (data_cells_agree _ _ _ _ DC9 AGLa ODa) AGb) as DCb.
    clear AGa AGb AXF HEAPa HEAP9.
    (* [comment removed for export] *)
    assert (HEAPb' : @BnHeapA.AHEAP (push AR f 2) Σb ((p, A, 24) :: OW4) ((qfc, f + 64, 1) :: LB) mb).
    { eapply (@frame_obj_close (push AR f 2)); [left; reflexivity| exact HEAPb|]. unfold in_fr. cbn [blk_addr blk_size fst snd]. change (fs_size 2) with 256. clear; lia. }
    clear HEAPb.
    assert (DJL : forall b, In b LB -> blk_addr b + blk_size b <= A \/ A + 24 <= blk_addr b).
    { intros b Hb. destruct b as [[q B] nb]. cbn [blk_addr blk_size fst snd].
      assert (NE : blk_id (q, B, nb) <> blk_id (p, A, 24)) by (cbn; intros ->; apply NIp; rewrite map_app; apply in_or_app; right; change p with (blk_id (p, B, nb)); apply in_map; apply INL; exact Hb).
      pose proof (@AH_disjoint_gen (push AR f 2) _ _ _ _ (q, B, nb) (p, A, 24) HEAPb' ltac:(apply in_or_app; right; right; exact Hb) ltac:(apply in_or_app; left; left; reflexivity) NE) as DJb.
      cbn [blk_addr blk_size fst snd] in DJb. exact DJb. }
    pose proof (@AH_ow_off_fr (push AR f 2) _ _ _ _ f 2%nat (p, A, 24) HEAPb' (or_introl eq_refl) (or_introl eq_refl)) as OA.
    unfold off_fr in OA. change (fs_size 2) with 256 in OA. cbn [blk_addr blk_size fst snd] in OA.
    pose proof (@AH_offsh (push AR f 2) _ _ _ _ (p, A, 24) HEAPb' ltac:(apply in_or_app; left; left; reflexivity)) as ROA. cbn [blk_addr blk_size fst snd] in ROA. unfold SHLO, SHHI in ROA.
    assert (EA : bv_unsigned (Z_to_bv 64 A) = A) by (apply unsigned_lit; clear - BA0 BAC CL3; lia).
    pose proof (proj2 (@AH_acc (push AR f 2) _ _ _ _ bv HEAPb' ltac:(apply in_or_app; right; right; exact Hbv))) as ACCV2. clear ACCV.
    (* [comment removed for export] *)
    pose proof (munch_refl [(PV, PV + 8)]%Z mb) as MU. pose proof (wmono_refl ctasegs mb) as WM.
    unfold hidden in ROV. assert (OFFW2 : offshW [(PV, PV + 8)]%Z) by (cbn [offshW]; unfold SHLO, SHHI; clear - ROV BV1 BV2; lia). hide ROV.
    freeze HOPP9. freeze HFC. freeze HB. freeze CELLb. freeze HCONT. hide BAS. hide DJL. hide OA. hide ROA.
    apply implAp_from_evt.
    step. if_cases KA0; zc KA0; [exfalso; rewrite ?EA in KA0; clear - KA0 BA0; lia|]. clear KA0.
    step. step. rewrite ?EPV. ab_shload 8. rewrite ?EPV. step. rewrite ?zxb_z8, ?sxb_z8. if_false. rewrite ?EPV. step. rewrite ?EPV. step. (* [comment removed for export] *)
    (* [comment removed for export] *)
    unfold frozen in HFC, HCONT. pose proof OV as OV'. unfold hidden in OV'.
    match goal with H : munch _ mb ?mx |- _ => apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ H)) in HFC; [| intros a Ha; cbn in Ha; cbn [outside fst snd]; clear - Ha OV' BV1 BV2; lia] end.
    match goal with H : munch _ mb ?mx |- _ => apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ H)) in HCONT; [| intros a Ha; cbn in Ha; cbn [outside fst snd]; clear - Ha OV' BV1 BV2; lia] end.
    step. step. change (zxb (Z_to_bv 8 0)) with (Z_to_bv 64 0). step. rewrite ?(unsigned_lit (D + cont)) by (clear - D0 D63 GB1 GB2 GB3 OP0 OPT; lia). step. if_true.
    step. step. step. step. name_mem mc.
    match goal with H : munch _ mb mc |- _ => rename H into MUc end. match goal with H : wmono ctasegs mb mc |- _ => rename H into WMc end.
    match goal with H : stk ctasegs mc lo _ |- _ => rename H into STc end. match goal with H : mem_inv ctasegs mc |- _ => rename H into MIc end.
    apply evt_done.
    (* [comment removed for export] *)
    unfold frozen in HOPP9, HFC, HB, CELLb. unfold hidden in DJL, OA, ROA, BAS. pose proof DOV as DOV'. unfold hidden in DOV'. pose proof DVD as DVD'. unfold hidden in DVD'.
    pose proof (agree_on_of_munch_nw _ _ _ MUc) as AGc.
    apply (rw_cells_agree _ _ _ _ _ AGc) in HOPP9; [| intros a Ha; cbn in Ha; cbn [outside fst snd]; clear - Ha DOV'; lia].
    apply (rw_cells_agree _ _ _ _ _ AGc) in CELLb; [| intros a Ha; unfold asn1_string_cells in Ha; cbn in Ha; cbn [outside fst snd]; pose proof (DJL bv Hbv) as X; clear - Ha X BV1 BV2; lia].
    rewrite <- DLEN in BD2.
    apply (bytes_at_agree _ _ _ _ _ AGc) in HB; [| intros a Ha; cbn [outside fst snd]; clear - Ha DVD' DLEN BD2; lia].
    rewrite DLEN in BD2.
    assert (HEAPc : @BnHeapA.AHEAP (push AR f 2) Σb ((p, A, 24) :: OW4) ((qfc, f + 64, 1) :: LB) mc).
    { eapply (@AH_frame (push AR f 2)); [exact HEAPb'| exact MUc| exact WMc|]. constructor; [| constructor].
      right; right. exists bv. split; [apply in_or_app; right; right; exact Hbv| cbn [fst snd]; clear - BV1 BV2; lia]. }
    assert (AGLbc : agree_on (lib_addr OW4) mb mc).
    { eapply agree_on_mono; [exact AGc|]. intros a [HS|(b & Hb & Hr)]; cbn [outside fst snd].
      - pose proof (LIBW_S_A a HS) as HA. unfold LIBW_A in HA. cbn [rin_ivs fst snd] in HA. pose proof BV5 as X; unfold hidden in X; unfold SEGTOP_A in X. clear - HA X BV1 BV2. lia.
      - destruct b as [[q B] nb]. cbn [blk_addr blk_size fst snd] in Hr.
        pose proof (@AH_nodup (push AR f 2) _ _ _ _ HEAPb') as ND.
        pose proof (ids_disj ((p, A, 24) :: OW4) ((qfc, f + 64, 1) :: LB) q B nb ND (or_intror Hb) bv (or_intror Hbv)) as NE.
        pose proof (@AH_disjoint_gen (push AR f 2) _ _ _ _ bv (q, B, nb) HEAPb' ltac:(apply in_or_app; right; right; exact Hbv) ltac:(apply in_or_app; left; right; exact Hb) NE) as DJb.
        cbn [blk_addr blk_size fst snd] in DJb. clear - Hr DJb BV1 BV2. lia. }
    pose proof (ap_state_agree _ _ _ _ _ _ ASb AGLbc) as ASc. pose proof ASc as (_ & (CSc & RSc & _) & _).
    pose proof (data_cells_agree _ _ _ _ DCb AGLbc ODa) as DCc.
    assert (KEPTc : blocks_kept K st OW4 m mc) by (exact (blocks_kept_lib _ _ _ _ _ _ (blocks_kept_lib _ _ _ _ _ _ KEPT9 AGL9b) AGLbc)).
    assert (AXc : ax_pres LB (bv_unsigned sp) XIV m mc).
    { eapply ax_pres_trans; [exact AXb|]. unfold ax_pres. eapply agree_on_mono; [exact AGc|]. intros a [HX _]. unfold LIBW_A in HX. cbn [rin_ivs fst snd app] in HX. cbn [outside fst snd]. clear - HX. lia. }
    pose proof (ids_in_introA _ _ _ _ _ AS9) as IDS_IN.
    assert (NBD : blk_id bd <> p) by (intros X; apply NIp; rewrite <- X, map_app; apply in_or_app; right; apply in_map; apply INL; exact Hbd).
    destruct (slice_bytesA mc D d cont plen HB ltac:(clear - GB1 OP0; lia) GB2 ltac:(clear - GB3 OPT; lia)) as [SRC SLEN].
    clear AGc MUc WMc AGLa ASa ASb DCb HEAPb' ACCV2 OFFW OFFW2.
    assert (CRbb : mcost plen <= rt_credit RT Σb) by (clear - CRA CRb EC ESK; lia).
    destruct (Z.eq_dec plen 0) as [PZ|PNZ].
    + (* [comment removed for export] *)
      rewrite (proj2 (Z.eqb_eq _ _) PZ). unfold aret. cbv beta iota.
      eapply implAp_step_same.
      { eapply (@ASN1_STRING_set1_data_zero_cpsA (push AR f 2) UK BE) with (lo := lo) (A := A) (ty := utype) (pblk := p); rewrite ?ESPA;
          [exact HEAPc| exact STc| exact CEIL9| clear - LO SPAL ESK; lia| exact TOP9| exact AL9| exact MIc| reflexivity| exact CSc
          | left; reflexivity| exact CELLb| clear - UTR; lia| clear - UO; unfold V_ASN1_OCTET_STRING in UO; lia| reflexivity| rewrite PZ; reflexivity
          | uw_call_axX_tac m 16 UW AXc FRH; [clear; lia
          | intros a Ha; apply rin_ivs_app in Ha as [Ha|Ha]; [cbn [rin_ivs fst snd app] in Ha; clear - Ha BQ2 BQ4 BV2 BV4 BT2 BT4 CEIL LO ESS; lia
              | pose proof (libw_below a Ha) as Hb; unfold SEGTOP_A in Hb; clear - Hb CL1 CEIL LO ESS; lia]
          | clear - SPAH; lia | uchk_open; clear - AL16; Z.div_mod_to_equations; lia | clear - TOP; unfold USTACK_TOP in *; lia]
          | rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_ex_set1 CTX)]. }
      intros msd POd. destruct POd as (w0 & w1 & w2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & w3 & w4 & w5 & w6 & Fd & fcd & md & -> & MId & STd & APX & HEAPd & CELLd).
      unfold MallocRep.wz in *. rewrite ?ESPA in *. rewrite (ret_pc_even 0x242540) by (clear; lia). unfold ASN1_STRING_SIZE in APX.
      (* [comment removed for export] *)
      assert (AGd : forall a, aclient_addr LB spa a \/ (f + 64 <= a < f + 65) -> md (wa a) = mc (wa a) -> True) by (intros; exact I). clear AGd.
      assert (AXS : forall A0 cs, rw_cells ctasegs mc A0 cs -> spa <= A0 -> A0 + Z.of_nat (cells_size cs) <= USTACK_TOP -> rw_cells ctasegs md A0 cs).
      { intros A0 cs HC H1 H2. eapply rw_cells_agree; [exact APX| exact HC|]. intros a Ha. split; [left; clear - Ha H1 H2; lia| cbn [outside fst snd]; clear - Ha H1 BAC CEIL LO ESS SPAL; lia]. }
      apply AXS in FRLA; [| clear; lia| cbn; clear - SPAH TOP; unfold USTACK_TOP in *; lia]. apply AXS in F96; [| clear; lia| cbn; clear - SPAH TOP; unfold USTACK_TOP in *; lia].
      apply AXS in F104; [| clear; lia| cbn; clear - SPAH TOP; unfold USTACK_TOP in *; lia]. apply AXS in F110; [| clear; lia| cbn; clear - SPAH TOP; unfold USTACK_TOP in *; lia].
      apply AXS in F111; [| clear; lia| cbn; clear - SPAH TOP; unfold USTACK_TOP in *; lia]. apply AXS in F112; [| clear; lia| cbn; clear - SPAH TOP; unfold USTACK_TOP in *; lia].
      apply AXS in F120; [| clear; lia| cbn; clear - SPAH TOP; unfold USTACK_TOP in *; lia].
      apply AXS in FRLB; [| clear; lia| cbn [cells_size csize Nat.add]; rewrite ?Nat2Z.inj_add; clear - GSZ SPAH TOP; unfold USTACK_TOP in *; lia].
      apply AXS in FRH; [| clear - SPAH; lia| cbn; clear - TOP; unfold USTACK_TOP in *; lia]. clear AXS.
      apply (rw_cells_agree _ _ _ _ _ APX) in HOPP9; [| intros a Ha; cbn in Ha; split; [right; right; exists bq; split; [apply in_or_app; right; right; exact Hbq| clear - Ha BQ1 BQ2; lia]| cbn [outside fst snd]; pose proof (DJL bq Hbq) as X; clear - Ha X BQ1 BQ2; lia]].
      apply (rw_cells_agree _ _ _ _ _ APX) in HPV9; [| intros a Ha; cbn in Ha; split; [right; right; exists bv; split; [apply in_or_app; right; right; exact Hbv| clear - Ha BV1 BV2; lia]| cbn [outside fst snd]; pose proof (DJL bv Hbv) as X; clear - Ha X BV1 BV2; lia]].
      apply (rw_cells_agree _ _ _ _ _ APX) in HFC; [| intros a Ha; cbn in Ha; split; [right; right; exists (qfc, f + 64, 1); split; [apply in_or_app; right; left; reflexivity| cbn; clear - Ha; lia]| cbn [outside fst snd]; clear - Ha OA; lia]].
      assert (AGL4 : agree_on (lib_addr OW4) mc md).
      { eapply agree_on_mono; [exact APX|]. intros a HL. split; [eapply acl_sub; [| | exact (lib_addr_aclient OW4 LB spa a HL)]; [intros b Hb; apply in_or_app; apply in_app_or in Hb; destruct Hb as [Hb|Hb]; [left; right; exact Hb| right; right; exact Hb]| clear; lia]|].
        cbn [outside fst snd]. destruct HL as [HS|(b & Hb & Hr)].
        - pose proof (LIBW_S_A a HS) as HA. unfold LIBW_A in HA. cbn [rin_ivs fst snd] in HA. clear - HA BAS. lia.
        - destruct b as [[q B] nb]. cbn [blk_addr blk_size fst snd] in Hr.
          assert (NE : blk_id (q, B, nb) <> blk_id (p, A, 24)) by (cbn; intros ->; apply NIp4; change p with (blk_id (p, B, nb)); apply in_map; exact Hb).
          pose proof (@AH_disjoint_gen (push AR f 2) _ _ _ _ (q, B, nb) (p, A, 24) HEAPc ltac:(apply in_or_app; left; right; exact Hb) ltac:(apply in_or_app; left; left; reflexivity) NE) as DJb.
          cbn [blk_addr blk_size fst snd] in DJb. clear - Hr DJb. lia. }
      pose proof (munch_refl ([] : list (Z * Z)) md) as MU. pose proof (wmono_refl ctasegs md) as WM.
      apply implAp_from_evt. step. if_true. apply evt_done. fold EX_OK_TAIL. clear MU WM.
      (* [comment removed for export] *)
      pose proof (ap_state_agree _ _ _ _ _ _ ASc AGL4) as ASd. pose proof ASd as (_ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & ODd)).
      assert (ASd' : ap_state st md ((p, A, 24) :: OW4) E bo) by (apply ap_state_cons_fresh; [exact ASd| exact NIp4| exact BA0| clear - BAC CL3; lia| exact BA16]).
      assert (DCd' : data_cells md ((p, A, 24) :: OW4) st) by (apply data_cells_cons_fresh; [exact (data_cells_agree _ _ _ _ DCc AGL4 ODd)| exact ODd| exact NIp4]).
      assert (KEPTd : blocks_kept K st ((p, A, 24) :: OW4) m md) by (apply blocks_kept_cons; exact (blocks_kept_lib _ _ _ _ _ _ KEPTc AGL4)).
      assert (AXd : ax_pres LB (bv_unsigned sp) XIV m md).
      { eapply ax_pres_trans; [exact AXc|]. unfold ax_pres. eapply agree_on_mono; [exact APX|]. intros a [_ Ha]. split; [eapply acl_sub; [| | exact Ha]; [intros b Hb; apply in_or_app; right; right; exact Hb| clear - SPAH; lia]|].
        cbn [outside fst snd]. destruct Ha as [H1|[H1|(b & Hb & Hr)]]; [clear - H1 BAC CEIL LO ESS SPAL; lia| pose proof (CSR a H1) as HA; clear - HA BAS; lia| pose proof (DJL b Hb) as X; clear - Hr X; lia]. }
      assert (CRd : rt_credit RT Σ - EXPRIM_SPENT_A plen <= rt_credit RT Σb) by (unfold EXPRIM_SPENT_A; clear - CRB CRb ESK MC0; lia).
      assert (SRd : str_repA md ((p, A, 24) :: OW4) (mkStr p None) A utype).
      { unfold str_repA. cbn [str_blk str_data]. rewrite CtRepP.ApErrKit.badr_cons, bptr_eqb_refl.
        split; [reflexivity|]. split; [exact BA0|]. split; [left; reflexivity| exact CELLd]. }
      assert (IDX : forall q, In q (str_ids (mkStr p (@None (bptr * Z)))) -> ~ In q (map blk_id K ++ es_ids st ++ env_ids E)).
      { intros q Hq. unfold str_ids in Hq. cbn [str_blk str_data app] in Hq. destruct Hq as [<-|[]].
        intros Hin. apply in_app_iff in Hin. destruct Hin as [Hin|Hin].
        { apply in_map_iff in Hin. destruct Hin as (b & Hb1 & Hb2). apply NIp4. rewrite <- Hb1. apply in_map. exact (proj1 KEPT9 b Hb2). }
        apply NIp4. exact (IDS_IN _ Hin). }
      apply (rw_cells_cb_first md spa _ 3) in FRLA. cbn [cb_first csize cbytes] in FRLA.
      eapply exprim_oktailA;
        [exact PRE0| exact ENT| exact PAY| exact OP0| exact TL0| exact OPT| exact EG| exact ETAG| exact ECLS| exact ERET| exact COPP| exact CPV| exact CTLC| exact ALO| exact ALV| exact ALT| exact DOV| exact FRESH| exact GEO| exact SPA32| exact SPAL| exact SPAH| exact GSZ| exact SAVJ
        | exact HEAPd| exact ASd'| exact IDS9| exact DCd'| exact STd| exact MId| exact AXd| exact CRd| exact KEPTd
        | exact HOPP9| exact HPV9| exact SRd| left; reflexivity| exact IDX
        | exact FRLA| exact F96| exact F104| exact F110| exact F111| exact F112| exact F120| exact FRLB| exact FRH| exact HFC].
    + (* [comment removed for export] *)
      assert (PPOS : 0 < plen) by (clear - PNZ GB2; lia).
      rewrite (proj2 (Z.eqb_neq _ _) PNZ). unfold abind, amalloc. cbn [apbind].
      eapply (@ASN1_STRING_set1_data_walkA (push AR f 2) UK BE) with (lo := lo) (pblk := p) (bsrc := bd) (A := A) (ty := utype) (P := D + cont) (n := plen)
                                                             (src := firstn (Z.to_nat plen) (skipn (Z.to_nat cont) (to_bytes d))); rewrite ?ESPA;
        [exact HEAPc| exact STc| exact CEIL9| clear - LO SPAL ESK; lia| exact TOP9| exact AL9| exact MIc| reflexivity| exact CSc| exact RSc
        | left; reflexivity| exact CELLb| clear - UTR; lia| clear - UO; unfold V_ASN1_OCTET_STRING in UO; lia
        | apply in_or_app; right; right; exact Hbd| exact NBD| clear - BD1 GB1 OP0; lia| clear - BD2 GB3 OPT; lia| exact SRC| exact SLEN
        | reflexivity| reflexivity| reflexivity| clear - PPOS PL31; lia| cbn [ar_RT push amb]; exact CRbb
        | uw_call_axX_tac m 16 UW AXc FRH; [clear; lia
          | intros a Ha; apply rin_ivs_app in Ha as [Ha|Ha]; [cbn [rin_ivs fst snd app] in Ha; clear - Ha BQ2 BQ4 BV2 BV4 BT2 BT4 CEIL LO ESS; lia
              | pose proof (libw_below a Ha) as Hb; unfold SEGTOP_A in Hb; clear - Hb CL1 CEIL LO ESS; lia]
          | clear - SPAH; lia | uchk_open; clear - AL16; Z.div_mod_to_equations; lia | clear - TOP; unfold USTACK_TOP in *; lia]
        | rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_ex_set1 CTX) |].
      intros p2 Σd msd NIp2 POd.
      destruct POd as (w0 & w1 & w2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & w3 & w4 & w5 & w6 & Fd & fcd & md & C & -> & MId & STd & APX & CRd & BRC & HEAPd & ACCC & (DSTd & CELLd & HBd)).
      cbn [apbind fst snd]. unfold MallocRep.wz in *. rewrite ?ESPA in *. rewrite (ret_pc_even 0x242540) by (clear; lia). unfold ASN1_STRING_SIZE in APX, HEAPd. cbn [ar_RT push amb] in CRd.
      pose proof BRC as (BC0 & BC16 & _ & BCC & BCS). change (@BnHeapA.ACEIL (push AR f 2)) with (@BnHeapA.ACEIL AR) in BCC.
      assert (NIp24 : ~ In p2 (map blk_id OW4)) by (intros X; apply NIp2; rewrite map_app; apply in_or_app; left; right; exact X).
      assert (NPP : p <> p2) by (intros X; apply NIp2; rewrite <- X, map_app; apply in_or_app; left; left; reflexivity).
      pose proof (@AH_disjoint_gen (push AR f 2) _ _ _ _ (p2, C, plen) (p, A, 24) HEAPd (or_introl eq_refl) (or_intror (or_introl eq_refl)) ltac:(cbn; clear - NPP; congruence)) as DJ2.
      cbn [blk_addr blk_size fst snd] in DJ2.
      (* [comment removed for export] *)
      assert (AXS : forall A0 cs, rw_cells ctasegs mc A0 cs -> spa <= A0 -> A0 + Z.of_nat (cells_size cs) <= USTACK_TOP -> rw_cells ctasegs md A0 cs).
      { intros A0 cs HC H1 H2. eapply rw_cells_agree; [exact APX| exact HC|]. intros a Ha. split; [left; clear - Ha H1 H2; lia| clear - Ha H1 BAC CEIL LO ESS SPAL; lia]. }
      apply AXS in FRLA; [| clear; lia| cbn; clear - SPAH TOP; unfold USTACK_TOP in *; lia]. apply AXS in F96; [| clear; lia| cbn; clear - SPAH TOP; unfold USTACK_TOP in *; lia].
      apply AXS in F104; [| clear; lia| cbn; clear - SPAH TOP; unfold USTACK_TOP in *; lia]. apply AXS in F110; [| clear; lia| cbn; clear - SPAH TOP; unfold USTACK_TOP in *; lia].
      apply AXS in F111; [| clear; lia| cbn; clear - SPAH TOP; unfold USTACK_TOP in *; lia]. apply AXS in F112; [| clear; lia| cbn; clear - SPAH TOP; unfold USTACK_TOP in *; lia].
      apply AXS in F120; [| clear; lia| cbn; clear - SPAH TOP; unfold USTACK_TOP in *; lia].
      apply AXS in FRLB; [| clear; lia| cbn [cells_size csize Nat.add]; rewrite ?Nat2Z.inj_add; clear - GSZ SPAH TOP; unfold USTACK_TOP in *; lia].
      apply AXS in FRH; [| clear - SPAH; lia| cbn; clear - TOP; unfold USTACK_TOP in *; lia]. clear AXS.
      apply (rw_cells_agree _ _ _ _ _ APX) in HOPP9; [| intros a Ha; cbn in Ha; split; [right; right; exists bq; split; [apply in_or_app; right; right; exact Hbq| clear - Ha BQ1 BQ2; lia]| pose proof (DJL bq Hbq) as X; clear - Ha X BQ1 BQ2; lia]].
      apply (rw_cells_agree _ _ _ _ _ APX) in HPV9; [| intros a Ha; cbn in Ha; split; [right; right; exists bv; split; [apply in_or_app; right; right; exact Hbv| clear - Ha BV1 BV2; lia]| pose proof (DJL bv Hbv) as X; clear - Ha X BV1 BV2; lia]].
      apply (rw_cells_agree _ _ _ _ _ APX) in HFC; [| intros a Ha; cbn in Ha; split; [right; right; exists (qfc, f + 64, 1); split; [apply in_or_app; right; left; reflexivity| cbn; clear - Ha; lia]| clear - Ha OA; lia]].
      assert (AGL4 : agree_on (lib_addr OW4) mc md).
      { eapply agree_on_mono; [exact APX|]. intros a HL. split; [eapply acl_sub; [| | exact (lib_addr_aclient OW4 LB spa a HL)]; [intros b Hb; apply in_or_app; apply in_app_or in Hb; destruct Hb as [Hb|Hb]; [left; right; exact Hb| right; right; exact Hb]| clear; lia]|].
        destruct HL as [HS|(b & Hb & Hr)].
        - pose proof (LIBW_S_A a HS) as HA. unfold LIBW_A in HA. cbn [rin_ivs fst snd] in HA. clear - HA BAS. lia.
        - destruct b as [[q B] nb]. cbn [blk_addr blk_size fst snd] in Hr.
          assert (NE : blk_id (q, B, nb) <> blk_id (p, A, 24)) by (cbn; intros ->; apply NIp4; change p with (blk_id (p, B, nb)); apply in_map; exact Hb).
          pose proof (@AH_disjoint_gen (push AR f 2) _ _ _ _ (q, B, nb) (p, A, 24) HEAPc ltac:(apply in_or_app; left; right; exact Hb) ltac:(apply in_or_app; left; left; reflexivity) NE) as DJb.
          cbn [blk_addr blk_size fst snd] in DJb. clear - Hr DJb. lia. }
      pose proof (munch_refl ([] : list (Z * Z)) md) as MU. pose proof (wmono_refl ctasegs md) as WM.
      apply implAp_from_evt. step. if_true. apply evt_done. fold EX_OK_TAIL. clear MU WM.
      (* [comment removed for export] *)
      pose proof (ap_state_agree _ _ _ _ _ _ ASc AGL4) as ASd. pose proof ASd as (_ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & ODd)).
      assert (ASd' : ap_state st md ((p, A, 24) :: OW4) E bo) by (apply ap_state_cons_fresh; [exact ASd| exact NIp4| exact BA0| clear - BAC CL3; lia| exact BA16]).
      pose proof ASd' as (_ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & ODd')).
      assert (ASd'' : ap_state st md ((p2, C, plen) :: (p, A, 24) :: OW4) E bo).
      { apply ap_state_cons_fresh; [exact ASd'| cbn; intros [X|X]; [exact (NPP X)| exact (NIp24 X)]| exact BC0| clear - BCC CL3; lia| exact BC16]. }
      assert (DCd'' : data_cells md ((p2, C, plen) :: (p, A, 24) :: OW4) st).
      { apply data_cells_cons_fresh; [| exact ODd'| cbn; intros [X|X]; [exact (NPP X)| exact (NIp24 X)]].
        apply data_cells_cons_fresh; [exact (data_cells_agree _ _ _ _ DCc AGL4 ODd)| exact ODd| exact NIp4]. }
      assert (KEPTd : blocks_kept K st ((p2, C, plen) :: (p, A, 24) :: OW4) m md) by (apply blocks_kept_cons; apply blocks_kept_cons; exact (blocks_kept_lib _ _ _ _ _ _ KEPTc AGL4)).
      assert (AXd : ax_pres LB (bv_unsigned sp) XIV m md).
      { eapply ax_pres_trans; [exact AXc|]. unfold ax_pres. eapply agree_on_mono; [exact APX|]. intros a [_ Ha]. split; [eapply acl_sub; [| | exact Ha]; [intros b Hb; apply in_or_app; right; right; exact Hb| clear - SPAH; lia]|].
        destruct Ha as [H1|[H1|(b & Hb & Hr)]]; [clear - H1 BAC CEIL LO ESS SPAL; lia| pose proof (CSR a H1) as HA; clear - HA BAS; lia| pose proof (DJL b Hb) as X; clear - Hr X; lia]. }
      assert (CRd' : rt_credit RT Σ - EXPRIM_SPENT_A plen <= rt_credit RT Σd) by (unfold EXPRIM_SPENT_A; clear - CRB CRb CRd ESK MC0; lia).
      assert (SRd : str_repA md ((p2, C, plen) :: (p, A, 24) :: OW4) (mkStr p (Some (p2, plen))) A utype).
      { unfold str_repA. cbn [str_blk str_data].
        assert (EBA : badr ((p2, C, plen) :: (p, A, 24) :: OW4) p = A).
        { rewrite CtRepP.ApErrKit.badr_cons. replace (bptr_eqb p2 p) with false by (symmetry; apply bptr_eqb_neq; intros X; exact (NPP (eq_sym X))). rewrite CtRepP.ApErrKit.badr_cons, bptr_eqb_refl. reflexivity. }
        assert (EBD : badr ((p2, C, plen) :: (p, A, 24) :: OW4) p2 = C) by (rewrite CtRepP.ApErrKit.badr_cons, bptr_eqb_refl; reflexivity).
        rewrite EBA, EBD.
        split; [reflexivity|]. split; [exact BA0|]. split; [right; left; reflexivity|].
        split; [clear - PPOS PL31; lia|]. split; [exact NPP|]. split; [left; reflexivity|]. split; [exact BC0|].
        split; [exact CELLd|]. exists (firstn (Z.to_nat plen) (skipn (Z.to_nat cont) (to_bytes d))). exact DSTd. }
      assert (IDX : forall q, In q (str_ids (mkStr p (Some (p2, plen)))) -> ~ In q (map blk_id K ++ es_ids st ++ env_ids E)).
      { intros q Hq. unfold str_ids in Hq. cbn [str_blk str_data app] in Hq.
        assert (Hq' : q = p \/ q = p2) by (destruct Hq as [Hq|[Hq|[]]]; [left| right]; symmetry; exact Hq). clear Hq.
        intros Hin. apply in_app_iff in Hin. destruct Hin as [Hin|Hin].
        { apply in_map_iff in Hin. destruct Hin as (b & Hb1 & Hb2). pose proof (proj1 KEPT9 b Hb2) as HbO.
          destruct Hq' as [-> | ->]; [apply NIp4| apply NIp24]; rewrite <- Hb1; apply in_map; exact HbO. }
        destruct Hq' as [-> | ->]; [apply NIp4| apply NIp24]; exact (IDS_IN _ Hin). }
      apply (rw_cells_cb_first md spa _ 3) in FRLA. cbn [cb_first csize cbytes] in FRLA.
      eapply exprim_oktailA;
        [exact PRE0| exact ENT| exact PAY| exact OP0| exact TL0| exact OPT| exact EG| exact ETAG| exact ECLS| exact ERET| exact COPP| exact CPV| exact CTLC| exact ALO| exact ALV| exact ALT| exact DOV| exact FRESH| exact GEO| exact SPA32| exact SPAL| exact SPAH| exact GSZ| exact SAVJ
        | exact HEAPd| exact ASd''| exact IDS9| exact DCd''| exact STd| exact MId| exact AXd| exact CRd'| exact KEPTd
        | exact HOPP9| exact HPV9| exact SRd| left; reflexivity| exact IDX
        | exact FRLA| exact F96| exact F104| exact F110| exact F111| exact F112| exact F120| exact FRLB| exact FRH| exact HFC].
  Qed.
End Body.
End WithRT.
