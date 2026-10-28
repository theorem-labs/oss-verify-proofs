(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim Malloc Prog LibProg CtSizes CtWire CtModel ApBase ApState ApErr ApParse ApBridge.
From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import STree Monad ProgG Stdio.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Layout Lib_iface Lib_kit Startup_B.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtBnU Require Import BnKit BnHeap BnRep W_crypto.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXU Require Import HxpInit HxpFacts.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApCells ApRepDefs ApRep ApWalkTac ApErrKit ApErrKit2 ApErrKit3 ApIface W_err_new W_err_set_debug W_err_set_error W_c2i_int W_get_object W_get_object_walk W_check_tlen W_prefix_create W_asn1_string W_item_d2i_stmt W_item_d2i_img W_item_d2i_front W_item_d2i_tail ApUTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtParseU Require Import PzDefs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtEncU Require Import W_asn1_enc_leaves.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctU Require Import SctStmt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtColU Require Import ColKit ColDefs W_bufmem W_check_tlen_gen W_collect W_d2i_octet_A W_d2i_octet_B W_d2i_octet_C.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope am_scope.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].
Local Ltac step := ub; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.
Local Ltac zstep := ub; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
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
Ltac zc H := rewrite ?bv_lts_zero_r, ?bv_lts_zero_l in H; unfold bv_eqb, bv_ltu, bv_lts, bv_leu in H; fold_lit_ux_in H; try zsimp_in H; zify_bool H.


(* [comment removed for export] *)
Ltac assert_join10 J pc :=
  let r1 := reg_val 1%Z in let r2 := reg_val 2%Z in let r3 := reg_val 3%Z in let r4 := reg_val 4%Z in let r5 := reg_val 5%Z in
  let r6 := reg_val 6%Z in let r7 := reg_val 7%Z in let r8 := reg_val 8%Z in let r9 := reg_val 9%Z in let r11 := reg_val 11%Z in
  let r12 := reg_val 12%Z in let r13 := reg_val 13%Z in let r14 := reg_val 14%Z in let r15 := reg_val 15%Z in let r16 := reg_val 16%Z in
  let r17 := reg_val 17%Z in let r18 := reg_val 18%Z in let r19 := reg_val 19%Z in let r20 := reg_val 20%Z in let r21 := reg_val 21%Z in
  let r22 := reg_val 22%Z in let r23 := reg_val 23%Z in let r24 := reg_val 24%Z in let r25 := reg_val 25%Z in let r26 := reg_val 26%Z in
  let r27 := reg_val 27%Z in let r28 := reg_val 28%Z in let r29 := reg_val 29%Z in let r30 := reg_val 30%Z in let r31 := reg_val 31%Z in
  lazymatch goal with |- evt ?sg ?P (MS _ ?FF _ ?fcc None ?mm ?rom) =>
    assert (J : forall w10 : word,
      evt sg P (MS (mkR r1 r2 r3 r4 r5 r6 r7 r8 r9 w10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29 r30 r31) FF (Z_to_bv 64 pc) fcc None mm rom))
  end.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.
  Hypothesis HGO : ASN1_get_object_spec.

  Section Act.
  (* [comment removed for export] *)
  Variables (sp : word) (m : mem) (s : PState) (LB : list block) (E : ap_env) (lo B : Z) (canary : word) (K : list block).
  Variables (d : list Z) (D : Z).
  Variables (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word).
  Variables (st : ap_st bptr) (OW : list block) (bo : Z * Z) (errv : word) (adr : bptr -> Z) (OPP OCT : Z).
  Hypothesis DF : Forall (fun b => 0 <= b < 256) d.
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis GLO : 3493888 <= lo.
  Hypothesis SPB : bv_unsigned sp <= B.
  Hypothesis B63 : B < 2 ^ 63.
  Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
  Hypothesis PBX : d = [] \/ exists pb PA psz, In (pb, PA, psz) LB /\ PA <= D /\ D + zlength d <= PA + psz.
  Hypothesis D1 : 0 < D.
  Hypothesis D63 : D + zlength d < 2 ^ 63.
  Hypothesis D30 : zlength d < 2 ^ 30.
  Hypothesis OPPlo : bv_unsigned sp <= OPP.
  Hypothesis OPPhi : OPP + 8 <= B.
  Hypothesis OCTlo : bv_unsigned sp <= OCT.
  Hypothesis OCThi : OCT + 8 <= B.
  Hypothesis DJXP : OPP + 8 <= OCT \/ OCT + 8 <= OPP.
  Hypothesis ADR : forall b, In b LB -> adr (blk_id b) = blk_addr b.

  Local Notation XPO := (XPO OPP OCT).
  Local Notation oinvK OFS STK := (oinv sp m s LB E lo B canary K d D XPO OFS STK).
  Local Notation SP := (bv_unsigned sp) (only parsing).
  Local Notation XPokK := (XPok sp B OPP OCT OPPlo OPPhi OCTlo OCThi).
  Local Notation xsaved := (xsaved sp s3 s4 s5 s6 s7 s8 s9 s10 OCT).
  Local Notation iframe := (iframe sp s2 s3 OCT).
  Local Notation dframe_hi := (dframe_hi ra s0 s1).

  Local Notation PRIM_STK := (W_d2i_octet_B.PRIM_STK).

  (* [comment removed for export] *)
  Definition CONS_STK : Z := COLLECT_STACK + 720.

  Lemma cons_stk_facts : PRIM_STK <= CONS_STK /\ GROW_STACK <= CONS_STK /\ CRYPTO_FREE_STACK <= CONS_STK.
  Proof.
    clear. unfold W_d2i_octet_B.PRIM_STK, CONS_STK, COLLECT_STACK, COLLECT_FRAME, CHECK_TLEN_STACK, GETOBJ_STACK, ERR_SET_ERROR_STACK, GROW_STACK,
      ASN1_STRING_TYPE_NEW_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, CRYPTO_FREE_STACK, RMALLOC_STACK, RFREE_STACK. std_lia__.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma dx_cons : forall (STK : Z) (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s7x : word) (FA : bvmap 5 word) (fcA : bv 32)
      sA stA mA OWA errvA boA (ov cw : word) (vb : byte) (j5 j4 j16 j31 j0 : list byte),
    let g := get_object d 0 (zlength d) in
    go_err g = None -> go_tag g = V_ASN1_OCTET_STRING -> go_cls g = 0 -> Z.land (go_ret g) 32 <> 0 -> 0 < zlength d ->
    lo <= SP + -320 - STK -> CONS_STK <= STK ->
    oinvK (-320) STK sA stA mA OWA errvA boA [] -> frm0 fcA -> (forall k : reg, bv_unsigned k <> 10 -> reg_get FA k = reg_get F k) ->
    rw_cells ctusegs mA OPP [C8 ov] -> rw_cells ctusegs mA OCT [C8 (Z_to_bv 64 0)] ->
    rw_cells ctusegs mA (SP + -312) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
    rw_cells ctusegs mA (SP + -280) [C8 (Z_to_bv 64 (D + go_p g))] ->
    rw_cells ctusegs mA (SP + -272) [CB 5 j5] -> rw_cells ctusegs mA (SP + -267) [C1 (Z_to_bv 8 0)] ->
    rw_cells ctusegs mA (SP + -266) [C1 (Z_to_bv 8 (Z.land (go_ret g) 1)); C1 (Z_to_bv 8 (Z.land (go_ret g) 32)); C8 (Z_to_bv 64 (tlen_plen g 0 (zlength d)))] ->
    rw_cells ctusegs mA (SP + -256) [CB 4 j4] -> rw_cells ctusegs mA (SP + -252) [C4 (Z_to_bv 64 4)] -> rw_cells ctusegs mA (SP + -248) [CB 16 j16] ->
    rw_cells ctusegs mA (SP + -232) [C8 cw] -> rw_cells ctusegs mA (SP + -224) xsaved -> rw_cells ctusegs mA (SP + -128) iframe ->
    rw_cells ctusegs mA (SP + -64) [C8 (Z_to_bv 64 0)] -> rw_cells ctusegs mA (SP + -56) [C1 vb; CB 31 j31] -> rw_cells ctusegs mA (SP + -24) dframe_hi ->
    rw_cells ctusegs mA (SP + -320) [CB 8 j0] -> OCT mod 8 = 0 ->
    implM ctusegs (interp (ap_embed ((' (b, r) <- collect (ct_fuel d) d buf0 (go_p g) (if Z.testbit (go_ret g) 0 then zlength d - go_p g else go_len g) (Z.testbit (go_ret g) 0) 0 ;;
                                      match r with
                                      | None => afree_opt (option_map fst (bm_data b)) ;;; aret None
                                      | Some _ =>
                                          let l := bm_len b in
                                          b2 <- buf_grow_clean b (l + 1) ;;
                                          blk <- amalloc SZ_ASN1_STRING ;;
                                          aret (Some (mkOct blk (bm_data b2) l (firstn (Z.to_nat l) (bm_bytes b2))))
                                      end) stA))) sA
          (d2i_octet_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F s OW LB E lo B canary m K adr OPP OCT)
          (MS (mkR x1 (Z_to_bv 64 (SP + -320)) gp (wz RATP) t0 t1 t2 (Z_to_bv 64 (SP + -128)) (Z_to_bv 64 OPP) (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7
                   (Z_to_bv 64 OCT) (Z_to_bv 64 ITEM_OCTET) (Z_to_bv 64 (SP + -56)) (Z_to_bv 64 0) (Z_to_bv 64 (zlength d)) s7x (Z_to_bv 64 0) (Z_to_bv 64 (-1)) s10 s11 t3 t4 t5 t6)
              FA (Z_to_bv 64 EXPRIM_AFTER_TLEN) fcA None mA (seg_rom ctusegs)).
  Proof using B63 CEIL D1 D30 D63 DF DJXP GLO HF HGO HM OCThi OCTlo OPPhi OPPlo PBX SP16 SPB.
    intros until j0. cbv zeta. intros EG ETAG ECLS ERET LEN0 LO STKG OI FRMA FEA HOPP HOCT FBUF FPP FJ5 FFC FPIC FJ4 FUT FJ16 FCW FSV FI FD0 FTLC FDH FJ0 OCT8.
    set (g := get_object d 0 (zlength d)) in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof cons_stk_facts as (STKP & STKW & STKF).
    unfold W_d2i_octet_B.PRIM_STK, ASN1_STRING_TYPE_NEW_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RMALLOC_STACK in STKP.
    assert (STK0 : 0 <= STK) by lia. assert (OFS0 : -320 <= 0) by lia. assert (OFS16 : (-320) mod 16 = 0) by reflexivity.
    assert (ESP : bv_unsigned (Z_to_bv 64 (SP + -320)) = SP + -320) by (apply unsigned_lit; lia).
    pose proof (oinv_facts sp m s LB E lo B canary K d D XPO (-320) STK _ _ _ _ _ _ _ OI) as (HEAPA & NDA & BND & FRESH & DJL & DJO).
    pose proof (oinv_call sp m s LB E lo B canary K d D XPO (-320) STK GLO LO STK0 OFS0 SPB B63 _ _ _ _ _ _ _ OI) as (_ & AUXA & _ & STA & _ & _ & ERRA & MIA & CSA & ASA).
    unfold LX_ERRNO, RATP in ERRA. change (3355176 - 164) with 3355012 in ERRA.
    assert (DLEN : Z.of_nat (length (to_bytes d)) = zlength d) by apply zlength_to_bytes.
    destruct PBX as [E0|(pb & PA & psz & HPB & PA1 & PA2)]; [exfalso; rewrite E0 in LEN0; unfold zlength in LEN0; cbn in LEN0; lia|].
    pose proof (BND pb PA psz ltac:(apply in_app_iff; right; apply in_app_iff; right; exact HPB)) as (BB0 & BB1 & BB2 & BB3 & BB4).
    pose proof (get_object_bounds d 0 (zlength d) ltac:(eapply Forall_impl; [| exact DF]; cbv beta; intros; lia) LEN0) as GB. cbv zeta in GB. fold g in GB. rewrite EG in GB.
    destruct GB as (GB1 & GB2 & GB3).
    pose proof (go_ret_cases d 0 (zlength d)) as RC. cbv zeta in RC. fold g in RC.
    pose proof (ret_bits (go_ret g) RC) as (R1 & R32 & R129 & R128 & R11 & RTB).
    assert (E32 : Z.land (go_ret g) 32 = 32) by (destruct R32 as [X|X]; [exfalso; exact (ERET X)| exact X]).
    rewrite E32 in FPIC.
    set (inf := Z.testbit (go_ret g) 0) in *.
    set (plen := if inf then zlength d - go_p g else go_len g) in *.
    assert (EPL : tlen_plen g 0 (zlength d) = plen) by (unfold tlen_plen; subst plen inf; rewrite Z.sub_0_r; reflexivity).
    rewrite EPL in FPIC.
    assert (PL0 : 0 <= plen /\ go_p g + plen <= zlength d) by (subst plen; destruct inf; lia).
    assert (IV1 : Z.land (Z.land (go_ret g) 1) 1 = (if inf then 1 else 0)).
    { rewrite R11. subst inf. destruct (Z.testbit (go_ret g) 0) eqn:TB.
      - apply (proj1 RTB). first [exact TB| reflexivity].
      - destruct R1 as [E1|E1]; [exact E1|]. exfalso. pose proof (proj2 RTB E1) as X. first [discriminate X| rewrite X in TB; discriminate TB]. }
    assert (IVR : 0 <= Z.land (go_ret g) 1 < 2 ^ 64) by lia.
    unfold W_d2i_octet_A.xsaved, W_d2i_octet_A.iframe, W_d2i_octet_A.dframe_hi, EXPRIM_AFTER_TLEN, RA_INTERN, RA_D2IEX, ITEM_OCTET, V_ASN1_OCTET_STRING, MallocRep.wz in *.
    pose proof (munch_refl [(SP - 320, SP)]%Z mA) as MU. pose proof (wmono_refl ctusegs mA) as WM.
    rename MIA into MI.
    unfold implM. iprefix.
    (* [comment removed for export] *)
    step. step. if_false. step. if_true.
    step. rewrite (sx32_small 4) by lia. step. step.
    step. if_cases KU; zc KU; [| exfalso; lia]. clear KU.
    step. step. if_true.
    step. change (zxb (Z_to_bv 8 32)) with (Z_to_bv 64 32). step. if_false.
    step. step. if_false. step. step. step. step. if_true.
    step. step. setreg 13%Z (Z_to_bv 64 (Z.land (go_ret g) 1)) ltac:(rewrite zxb_lit by lia; reflexivity).
    step. step. step. step. step. step.
    name_mem m0.
    match goal with H : stk ctusegs m0 lo _ |- _ => rename H into ST0 end.
    assert (OI0 : oinvK (-320) STK sA stA m0 OWA errvA boA []).
    { eapply (oinv_munch sp m s LB E lo B canary K d D XPO (-320) STK CEIL GLO LO STK0 OFS0 SPB B63 SP16 OFS16 XPokK PBX);
        [exact OI| exact MU| exact WM| exact MI| exact ST0| exact ERRA|]. constructor; [left; cbn; lia| constructor]. }
    ihere. to_implM. eapply implM_abind.
    { eapply (asn1_collect_walk HM HF HGO sp m s LB E lo B canary K d D XPO DF CEIL GLO SPB B63 SP16 XPokK PBX D1 D63 D30 (ct_fuel d) (-320) STK)
        with (b := buf0) (A0 := 0) (NEW1 := []) (BUF := SP + -312) (PP := SP + -280);
        [exact LO| exact OFS0| exact OFS16| unfold CONS_STK in STKG; lia| exact OI0| exact FRMA
        | lia| lia| clear - SP16; Z.div_mod_to_equations; lia| lia| lia| clear - SP16; Z.div_mod_to_equations; lia| lia| exact FBUF| | exact FPP| lia| lia| lia| lia| exact IVR| exact IV1| cbn; lia].
      unfold buf_inv, buf0. cbn [bm_len bm_data bm_bytes]. split; [lia|]. split; [reflexivity|]. split; [constructor|]. split; reflexivity. }
    intros r1 s1' ms1 PO1. unfold coll_post in PO1.
    destruct PO1 as (w0 & w1 & w2 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w3 & w4 & w5 & w6 & F2 & fc2 & m2 & OW2 & errv2 & bo2 & A2
                     & -> & FRM2 & FE2 & OI2 & HBUF2 & BI2 & HPP2 & LX2 & BND2).
    replace (ret_pc (Z_to_bv 64 0x11246c)) with (Z_to_bv 64 0x11246c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    destruct r1 as [[b1 ro] st1]. cbn [fst snd] in *. rewrite app_nil_r in OI2.
    (* [comment removed for export] *)
    pose proof (agree_of_lx_pres _ _ _ _ _ LX2) as AG2. cbn [app] in AG2.
    assert (CL2 : forall a, ((SP + -272 <= a < SP) \/ (SP + -320 <= a < SP + -312) \/ (OPP <= a < OPP + 8) \/ (OCT <= a < OCT + 8)) -> lx_client LB (SP + -320) ([(SP + -312, SP + -312 + 32); (SP + -280, SP + -280 + 8)] ++ LIBW_AP) a).
    { intros a Ha. split; [unfold LIBW_AP; cbn [rin_ivs fst snd app]; lia| left; lia]. }
    apply (rw_cells_agree _ _ _ _ _ AG2) in FJ5; [| intros a Ha; apply CL2; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ AG2) in FFC; [| intros a Ha; apply CL2; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ AG2) in FPIC; [| intros a Ha; apply CL2; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ AG2) in FJ4; [| intros a Ha; apply CL2; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ AG2) in FUT; [| intros a Ha; apply CL2; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ AG2) in FJ16; [| intros a Ha; apply CL2; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ AG2) in FCW; [| intros a Ha; apply CL2; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ AG2) in FSV; [| intros a Ha; apply CL2; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ AG2) in FI; [| intros a Ha; apply CL2; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ AG2) in FD0; [| intros a Ha; apply CL2; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ AG2) in FTLC; [| intros a Ha; apply CL2; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ AG2) in FJ0; [| intros a Ha; apply CL2; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ AG2) in FDH; [| intros a Ha; apply CL2; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ AG2) in HOPP; [| intros a Ha; apply CL2; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ AG2) in HOCT; [| intros a Ha; apply CL2; cbn in Ha; lia].
    clear AG2 CL2 MU WM MI ST0 ERRA.
    pose proof (oinv_facts sp m s LB E lo B canary K d D XPO (-320) STK _ _ _ _ _ _ _ OI2) as (HEAPB & NDB & BNDB & FRESHB & DJLB & DJOB).
    pose proof (oinv_call sp m s LB E lo B canary K d D XPO (-320) STK GLO LO STK0 OFS0 SPB B63 _ _ _ _ _ _ _ OI2) as (_ & AUXB & _ & STB & _ & _ & ERRB & MIB & CSB & ASB).
    unfold LX_ERRNO, RATP in ERRB. change (3355176 - 164) with 3355012 in ERRB.
    pose proof BI2 as (BL0 & BLEN & BRNG & BI4).
    unfold buf_cells, MallocRep.wz in HBUF2.
    pose proof (munch_refl [(SP - 320, SP)]%Z m2) as MU. pose proof (wmono_refl ctusegs m2) as WM.
    destruct ro as [p'|].
    - (* [comment removed for export] *)
      destruct BND2 as [BP1 BP2].
      unfold implM. iprefix. step. if_false. step. step. step. step.
      name_mem m3.
      match goal with H : stk ctusegs m3 lo _ |- _ => rename H into ST3 end. match goal with H : mem_inv ctusegs m3 |- _ => rename H into MI3 end.
      assert (OI3 : oinvK (-320) STK s1' st1 m3 OW2 errv2 bo2 (buf_blk b1 A2)).
      { eapply (oinv_munch sp m s LB E lo B canary K d D XPO (-320) STK CEIL GLO LO STK0 OFS0 SPB B63 SP16 OFS16 XPokK PBX);
          [exact OI2| exact MU| exact WM| exact MI3| exact ST3| exact ERRB|]. constructor; [left; cbn; lia| constructor]. }
      (* [comment removed for export] *)
      assert (AFTER : forall r2 s2' ms2 bytes,
        grow_post sp m s LB E lo B canary K d D XPO (-320) STK (Z_to_bv 64 0x112484) gp (Z_to_bv 64 (SP + -128)) (Z_to_bv 64 OPP)
                  (Z_to_bv 64 OCT) (Z_to_bv 64 2960328) (Z_to_bv 64 (SP + -56)) (Z_to_bv 64 (bm_len b1)) (Z_to_bv 64 (zlength d)) s7x (Z_to_bv 64 0) (Z_to_bv 64 (-1)) s10 s11
                  F2 fc2 st1 OW2 bo2 m3 [] b1 (bm_len b1 + 1) (SP + -312) bytes r2 s2' ms2 ->
        firstn (Z.to_nat (bm_len b1)) bytes = to_bytes (bm_bytes b1) ->
        implM ctusegs (interp (ap_embed ((blk <- amalloc SZ_ASN1_STRING ;;
                                          aret (Some (mkOct blk (bm_data (fst r2)) (bm_len b1) (firstn (Z.to_nat (bm_len b1)) (bm_bytes (fst r2)))))) (snd r2)))) s2'
              (d2i_octet_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F s OW LB E lo B canary m K adr OPP OCT) ms2).
      { intros r2 s2' ms2 bytes POG FBY. unfold grow_post in POG.
        destruct POG as (v0 & v1 & v2 & v11 & v12 & v13 & v14 & v15 & v16 & v17 & v3 & v4 & v5 & v6 & mG & errvG & q & A & n & rest
                         & -> & ER2 & ER1 & OIG & HBUFG & HAG & LEN & N4 & A0' & AC & LXG).
        rewrite ER1, ER2. cbn [bm_data bm_bytes fst snd].
        replace (ret_pc (Z_to_bv 64 0x112484)) with (Z_to_bv 64 0x112484) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        rewrite FBY in HAG.
        rewrite firstn_all2 by (pose proof (zlength_to_bytes (bm_bytes b1)) as ZL; rewrite <- BLEN in ZL; unfold zlength in ZL |- *; rewrite <- ZL; unfold to_bytes; rewrite length_map; lia).
        (* [comment removed for export] *)
        pose proof (agree_of_lx_pres _ _ _ _ _ LXG) as AGG. cbn [app] in AGG.
        assert (CLG : forall a, ((SP + -280 <= a < SP) \/ (SP + -320 <= a < SP + -312) \/ (OPP <= a < OPP + 8) \/ (OCT <= a < OCT + 8)) -> lx_client LB (SP + -320) ([(SP + -312, SP + -312 + 32)] ++ LIBW_AP) a).
        { intros a Ha. split; [unfold LIBW_AP; cbn [rin_ivs fst snd app]; lia| left; lia]. }
        apply (rw_cells_agree _ _ _ _ _ AGG) in HPP2; [| intros a Ha; apply CLG; cbn in Ha; lia].
        apply (rw_cells_agree _ _ _ _ _ AGG) in FJ5; [| intros a Ha; apply CLG; cbn in Ha; lia].
        apply (rw_cells_agree _ _ _ _ _ AGG) in FFC; [| intros a Ha; apply CLG; cbn in Ha; lia].
        apply (rw_cells_agree _ _ _ _ _ AGG) in FPIC; [| intros a Ha; apply CLG; cbn in Ha; lia].
        apply (rw_cells_agree _ _ _ _ _ AGG) in FJ4; [| intros a Ha; apply CLG; cbn in Ha; lia].
        apply (rw_cells_agree _ _ _ _ _ AGG) in FUT; [| intros a Ha; apply CLG; cbn in Ha; lia].
        apply (rw_cells_agree _ _ _ _ _ AGG) in FJ16; [| intros a Ha; apply CLG; cbn in Ha; lia].
        apply (rw_cells_agree _ _ _ _ _ AGG) in FCW; [| intros a Ha; apply CLG; cbn in Ha; lia].
        apply (rw_cells_agree _ _ _ _ _ AGG) in FSV; [| intros a Ha; apply CLG; cbn in Ha; lia].
        apply (rw_cells_agree _ _ _ _ _ AGG) in FI; [| intros a Ha; apply CLG; cbn in Ha; lia].
        apply (rw_cells_agree _ _ _ _ _ AGG) in FD0; [| intros a Ha; apply CLG; cbn in Ha; lia].
        apply (rw_cells_agree _ _ _ _ _ AGG) in FTLC; [| intros a Ha; apply CLG; cbn in Ha; lia].
        apply (rw_cells_agree _ _ _ _ _ AGG) in FJ0; [| intros a Ha; apply CLG; cbn in Ha; lia].
        apply (rw_cells_agree _ _ _ _ _ AGG) in FDH; [| intros a Ha; apply CLG; cbn in Ha; lia].
        apply (rw_cells_agree _ _ _ _ _ AGG) in HOPP; [| intros a Ha; apply CLG; cbn in Ha; lia].
        apply (rw_cells_agree _ _ _ _ _ AGG) in HOCT; [| intros a Ha; apply CLG; cbn in Ha; lia].
        clear AGG CLG.
        pose proof (oinv_call sp m s LB E lo B canary K d D XPO (-320) STK GLO LO STK0 OFS0 SPB B63 _ _ _ _ _ _ _ OIG) as (_ & _ & _ & STG & _ & _ & ERRG & MIG & _).
        unfold LX_ERRNO, RATP in ERRG. change (3355176 - 164) with 3355012 in ERRG.
        pose proof (oinv_facts sp m s LB E lo B canary K d D XPO (-320) STK _ _ _ _ _ _ _ OIG) as (HEAPG & NDG & BNDG & FRESHG & DJLG & DJOG).
        pose proof (BNDG q A n ltac:(apply in_app_iff; right; left; reflexivity)) as (GA0 & _ & GAC & GAI & GA16).
        (* [comment removed for export] *)
        cut_hd HAG HA1 (A + bm_len b1). rename HAG into HA2.
        replace (Z.to_nat (n - bm_len b1)) with (1 + Z.to_nat (n - bm_len b1 - 1))%nat in HA2 by lia.
        apply cb_split in HA2. cut_hd HA2 HAZ (A + bm_len b1 + 1). rename HA2 into HA3.
        destruct (cb_byte _ _ _ HAZ) as [bz HAZ']. clear HAZ.
        clear MU WM. pose proof (munch_refl [(SP - 320, SP); (A + bm_len b1, A + bm_len b1 + 1)]%Z mG) as MU. pose proof (wmono_refl ctusegs mG) as WM.
        unfold MallocRep.wz in HBUFG. rename MIG into MI.
        unfold implM. iprefix.
        step. if_cases KA; zc KA; [exfalso; revert KA; rewrite ?unsigned_lit by lia; lia|]. clear KA.
        step. step.
        remember (A + bm_len b1) as AZ eqn:EAZ.
        setreg 10%Z (Z_to_bv 64 AZ) ltac:(rewrite EAZ; reflexivity).
        step. subst AZ. step. step. step.
        name_mem m4.
        match goal with H : stk ctusegs m4 lo _ |- _ => rename H into ST4 end. match goal with H : mem_inv ctusegs m4 |- _ => rename H into MI4 end.
        assert (OI4 : oinvK (-320) STK s2' st1 m4 OW2 errvG bo2 [(q, A, n)]).
        { eapply (oinv_munch sp m s LB E lo B canary K d D XPO (-320) STK CEIL GLO LO STK0 OFS0 SPB B63 SP16 OFS16 XPokK PBX);
            [exact OIG| exact MU| exact WM| exact MI4| exact ST4| exact ERRG|]. constructor; [left; cbn; lia|]. constructor; [| constructor]. right. right. exists q, A, n. split; [left; reflexivity| cbn; lia]. }
        ihere. to_implM.
        try rewrite le1_lit in HAZ'.
        join2 HA1 HAZ'. join2 HA1 HA3.
        eapply (dx_cons_c2i HM sp m s LB E lo B canary K d D ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F OW adr OPP OCT CEIL GLO SPB B63 SP16 PBX D1 D63 OPPlo OPPhi OCTlo OCThi DJXP STK)
          with (p2 := p') (bys := bm_bytes b1);
          [exact LO| unfold W_d2i_octet_B.PRIM_STK, ASN1_STRING_TYPE_NEW_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RMALLOC_STACK; lia| exact OI4| exact FRM2| intros k Hk; rewrite (FE2 k Hk); exact (FEA k Hk)| exact HOPP| exact HOCT| lia| lia| lia| exact BLEN| exact BRNG| lia| exact HA1
          | exact HBUFG| exact HPP2| exact FJ5| exact FFC| exact FPIC| exact FJ4| exact FUT| exact FJ16| exact FCW| exact FSV| exact FI| exact FD0| exact FTLC| exact FDH| exact FJ0| exact OCT8]. }
      ihere. to_implM.
      destruct (bm_data b1) as [[q0 n0]|] eqn:EBD.
      + destruct BI4 as (C1' & C2 & C3 & C4' & C5 & rest & HC). apply cb_join in HC.
        replace (Z.to_nat (bm_len b1) + Z.to_nat (n0 - bm_len b1))%nat with (Z.to_nat n0) in HC by lia.
        eapply implM_abind.
        { eapply (BUF_MEM_grow_clean_walk HM HF sp m s LB E lo B canary K d D XPO CEIL GLO SPB B63 SP16 XPokK PBX (-320) STK) with (b := b1) (A0 := A2) (NEW1 := [])
            (bytes := to_bytes (bm_bytes b1) ++ rest);
            [exact LO| exact OFS0| exact OFS16| lia| unfold buf_blk in OI3 |- *; rewrite EBD in OI3 |- *; rewrite app_nil_r; exact OI3| exact FRM2
            | lia| lia| clear - SP16; Z.div_mod_to_equations; lia| unfold buf_cells, MallocRep.wz; exact HBUF2| unfold bm_max; rewrite EBD; lia| lia| lia| rewrite EBD; split; [lia| exact HC]]. }
        intros r2 s2' ms2 PO2. eapply AFTER; [exact PO2|].
        rewrite firstn_app. pose proof (cb_len _ _ _ _ HC) as LL. rewrite length_app in LL.
        replace (Z.to_nat (bm_len b1) - length (to_bytes (bm_bytes b1)))%nat with 0%nat by (pose proof (zlength_to_bytes (bm_bytes b1)); unfold zlength in *; lia).
        cbn [firstn]. rewrite app_nil_r. apply firstn_all2. pose proof (zlength_to_bytes (bm_bytes b1)). unfold zlength in *. lia.
      + destruct BI4 as [EA0 EL0].
        eapply implM_abind.
        { eapply (BUF_MEM_grow_clean_walk HM HF sp m s LB E lo B canary K d D XPO CEIL GLO SPB B63 SP16 XPokK PBX (-320) STK) with (b := b1) (A0 := A2) (NEW1 := [])
            (bytes := []);
            [exact LO| exact OFS0| exact OFS16| lia| unfold buf_blk in OI3 |- *; rewrite EBD in OI3 |- *; rewrite app_nil_r; exact OI3| exact FRM2
            | lia| lia| clear - SP16; Z.div_mod_to_equations; lia| unfold buf_cells, MallocRep.wz; exact HBUF2| unfold bm_max; rewrite EBD; lia| lia| lia| rewrite EBD; exact EA0]. }
        intros r2 s2' ms2 PO2. eapply AFTER; [exact PO2|].
        rewrite EL0. cbn [Z.to_nat firstn]. symmetry. rewrite BLEN in EL0. destruct (bm_bytes b1); [reflexivity| unfold zlength in EL0; cbn in EL0; lia].
    - (* [comment removed for export] *)
      unfold implM. iprefix. step. if_true.
      step. step. step. change (zxb (Z_to_bv 8 1)) with (Z_to_bv 64 1). step. if_false.
      step. step. step. step. step.
      name_mem m3.
      match goal with H : stk ctusegs m3 lo _ |- _ => rename H into ST3 end. match goal with H : mem_inv ctusegs m3 |- _ => rename H into MI3 end.
      assert (OI3 : oinvK (-320) STK s1' st1 m3 OW2 errv2 bo2 (buf_blk b1 A2)).
      { eapply (oinv_munch sp m s LB E lo B canary K d D XPO (-320) STK CEIL GLO LO STK0 OFS0 SPB B63 SP16 OFS16 XPokK PBX);
          [exact OI2| exact MU| exact WM| exact MI3| exact ST3| exact ERRB|]. constructor; [left; cbn; lia| constructor]. }
      pose proof (oinv_call sp m s LB E lo B canary K d D XPO (-320) STK GLO LO STK0 OFS0 SPB B63 _ _ _ _ _ _ _ OI3) as (HEAP3 & AUX3 & _ & _ & _ & _ & ERR3 & _ & CS3 & AS3).
      unfold buf_blk in OI3, HEAP3.
      (* [comment removed for export] *)
      assert (TAILF : forall (y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word) mF sF OWF (errvF : word),
        oinvK (-320) STK sF st1 mF OWF errvF bo2 [] ->
        agree_on (fun a => SP + -320 <= a \/ in_block LB a) m3 mF \/ (munch [(SP - 320 - 16, SP - 320)]%Z m3 mF /\ wmono ctusegs m3 mF) ->
        evt ctusegs (d2i_octet_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F s OW LB E lo B canary m K adr OPP OCT (None, st1) sF)
          (MS (mkR (Z_to_bv 64 EXPRIM_RET) (Z_to_bv 64 (SP + -320)) gp (Z_to_bv 64 RATP) y5 y6 y7 (Z_to_bv 64 (SP + -128)) (Z_to_bv 64 OPP) y10 y11 y12 y13 y14 y15 y16 y17
                   (Z_to_bv 64 OCT) (Z_to_bv 64 2960328) (Z_to_bv 64 (SP + -56)) (Z_to_bv 64 0) (Z_to_bv 64 (zlength d)) s7x (Z_to_bv 64 0) (Z_to_bv 64 (-1)) s10 s11 y28 y29 y30 y31)
              F2 (Z_to_bv 64 EXPRIM_RET) fc2 None mF (seg_rom ctusegs))).
      { intros until errvF. intros OIF AGF.
        assert (XP : forall A0 cs, rw_cells ctusegs m3 A0 cs -> (SP + -320 <= A0) -> rw_cells ctusegs mF A0 cs).
        { intros A0 cs H HA0. destruct AGF as [AG|[MUF WMF]].
          - eapply rw_cells_agree; [exact AG| exact H| intros a Ha; left; lia].
          - eapply rw_cells_transport; [exact H| exact MUF| exact WMF| cbn; lia]. }
        apply XP in HBUF2; [| lia]. apply XP in HPP2; [| lia]. apply XP in FJ5; [| lia]. apply XP in FFC; [| lia]. apply XP in FPIC; [| lia].
        apply XP in FJ4; [| lia]. apply XP in FUT; [| lia]. apply XP in FJ16; [| lia]. apply XP in FCW; [| lia]. apply XP in FSV; [| lia].
        apply XP in FI; [| lia]. apply XP in FD0; [| lia]. apply XP in FTLC; [| lia]. apply XP in FDH; [| lia]. apply XP in HOPP; [| lia]. apply XP in HOCT; [| lia]. apply XP in FJ0; [| lia].
        destruct (fb_pack sp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HBUF2 HPP2 FJ5 FFC FPIC FJ4 FUT FJ16 FCW FJ0) as (jb & jm & FB).
        destruct (fb_blob sp _ _ _ _ _ _ FB) as [jlo FLO].
        destruct (fd_pack sp _ _ _ _ FD0 FTLC) as (jd & FD).
        unfold EXPRIM_RET.
        eapply (dx_fail_tail sp m s LB E lo B canary K d D ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F OW adr OPP OCT CEIL GLO SPB B63 SP16 PBX OPPlo OPPhi OCTlo OCThi STK);
          [exact LO| exact STK0| exact OIF| exact FRM2| intros k Hk; rewrite (FE2 k Hk); exact (FEA k Hk)| exact HOPP| exact HOCT| exact OCT8| exact FLO| exact FSV| exact FI| exact FD| exact FDH]. }
      destruct (bm_data b1) as [[q0 n0]|] eqn:EBD.
      + (* [comment removed for export] *)
        destruct BI4 as (C1' & C2 & C3 & C4' & C5 & rest & HC).
        ihere. cbn [abind apbind afree_opt afree option_map aret ap_embed fst snd]. to_implM.
        eapply (CRYPTO_free_walk HF) with (B := B) (lo := lo) (errv := errv2) (A := A2) (n := n0) (L := OW2 ++ [(q0, A2, n0)] ++ LB);
          [exact HEAP3| apply in_app_iff; right; left; reflexivity| exact AUX3| rewrite ESP; lia| rewrite ESP; exact ST3| exact CEIL| unfold GLOBALS_TOP; lia
          | rewrite ESP; unfold CRYPTO_FREE_STACK, RFREE_STACK; unfold CONS_STK, COLLECT_STACK, COLLECT_FRAME, CHECK_TLEN_STACK, GETOBJ_STACK, ERR_SET_ERROR_STACK in STKG; lia
          | exact ERR3| exact MI3| reflexivity| exact CS3| reflexivity|].
        intros sF msF POF. unfold cfree_post in POF. rewrite ?ESP in POF.
        destruct POF as (z0 & z1 & z2 & z10 & z11 & z12 & z13 & z14 & z15 & z16 & z17 & z3 & z4 & z5 & z6 & mF & -> & MIF & STF & ERRF & AUXF & HPF & FAF & SOF & HEAPF).
        replace (ret_pc (Z_to_bv 64 0x1125b8)) with (Z_to_bv 64 0x1125b8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        pose proof (oinv_facts sp m s LB E lo B canary K d D XPO (-320) STK _ _ _ _ _ _ _ OI3) as (_ & ND3 & _).
        pose proof (lb_remove_mid OW2 (q0, A2, n0) [] LB ND3) as LREM. cbn [blk_id fst snd app] in LREM. rewrite LREM in HEAPF, HPF.
        apply implM_ret. unfold EXPRIM_RET in TAILF. eapply TAILF.
        * eapply (oinv_heap sp m s LB E lo B canary K d D XPO (-320) STK CEIL GLO LO STK0 OFS0 SPB B63 PBX) with (L1 := OW2 ++ LB);
            [exact OI3| eapply rheap_pres_weaken; [exact HPF| lia| intros b Hb; exact Hb]| intros b [Hb|Hb]; apply in_app_iff; [left| right]; exact Hb
            | exact HEAPF| apply Permutation_refl| exact MIF| exact STF| exact ERRF| exact AUXF| exact FAF| exact SOF].
        * left. eapply agree_on_mono; [exact (agree_of_heap_pres _ _ _ _ HPF)|]. intros a Ha. destruct Ha as [Ha|Ha]; [left; exact Ha| right; right].
          destruct Ha as (b & Hb & Hin). exists b. split; [apply in_app_iff; right; exact Hb| exact Hin].
      + (* [comment removed for export] *)
        destruct BI4 as [EA0 EL0]. subst A2.
        ihere. cbn [abind apbind afree_opt afree option_map aret ap_embed fst snd]. to_implM. apply implM_ret.
        eapply evt_cut.
        { eapply CRYPTO_free_null_spec with (lo := lo); [rewrite ESP; exact ST3| unfold GLOBALS_TOP; lia| rewrite ESP; lia| exact MI3| exact CS3| reflexivity]. }
        cbv beta. intros msF (z0 & z1 & z2 & z10 & z11 & z12 & z13 & z14 & z15 & z16 & z17 & z3 & z4 & z5 & z6 & mF & -> & MUF & WMF & MIF & STF). rewrite ?ESP in *.
        replace (ret_pc (Z_to_bv 64 0x1125b8)) with (Z_to_bv 64 0x1125b8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        unfold EXPRIM_RET in TAILF. eapply TAILF.
        * eapply (oinv_munch sp m s LB E lo B canary K d D XPO (-320) STK CEIL GLO LO STK0 OFS0 SPB B63 SP16 OFS16 XPokK PBX);
            [exact OI3| exact MUF| exact WMF| exact MIF| exact STF| eapply rw_cells_transport; [exact ERR3| exact MUF| exact WMF| cbn; lia]|]. constructor; [left; cbn; lia| constructor].
        * right. split; [| exact WMF]. eapply munch_weaken; [| exact MUF]. intros x; cbn; lia.
  Qed.

  End Act.
End Proofs.
End WithCeiling0.
