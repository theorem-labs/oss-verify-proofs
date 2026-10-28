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
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtColU Require Import ColKit ColDefs W_bufmem W_check_tlen_gen W_collect W_d2i_octet_A W_d2i_octet_B.
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
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma dx_cons_c2i : forall (STK : Z) (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 x22 x23 x24 x25 : word) (FA : bvmap 5 word) (fcA : bv 32)
      sA stA mA OWA errvA boA (ov cw : word) (vb bi bc : byte) (pl : word) (j5 j4 j16 j31 j0 : list byte)
      (q : bptr) (A n l : Z) (bys : list Z) (rest : list byte) (p2 : Z),
    lo <= SP + -320 - STK -> PRIM_STK <= STK ->
    oinvK (-320) STK sA stA mA OWA errvA boA [(q, A, n)] -> frm0 fcA -> (forall k : reg, bv_unsigned k <> 10 -> reg_get FA k = reg_get F k) ->
    rw_cells ctusegs mA OPP [C8 ov] -> rw_cells ctusegs mA OCT [C8 (Z_to_bv 64 0)] ->
    0 <= l -> l + 1 <= n -> n < 2 ^ 31 -> l = zlength bys -> Forall (fun b => 0 <= b < 256) bys -> 0 <= p2 <= zlength d ->
    rw_cells ctusegs mA A [CB (Z.to_nat l) (to_bytes bys); C1 (Z_to_bv 8 0); CB (Z.to_nat (n - l - 1)) rest] ->
    rw_cells ctusegs mA (SP + -312) [C8 (Z_to_bv 64 (l + 1)); C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 0)] ->
    rw_cells ctusegs mA (SP + -280) [C8 (Z_to_bv 64 (D + p2))] ->
    rw_cells ctusegs mA (SP + -272) [CB 5 j5] -> rw_cells ctusegs mA (SP + -267) [C1 (Z_to_bv 8 1)] ->
    rw_cells ctusegs mA (SP + -266) [C1 bi; C1 bc; C8 pl] ->
    rw_cells ctusegs mA (SP + -256) [CB 4 j4] -> rw_cells ctusegs mA (SP + -252) [C4 (Z_to_bv 64 4)] -> rw_cells ctusegs mA (SP + -248) [CB 16 j16] ->
    rw_cells ctusegs mA (SP + -232) [C8 cw] -> rw_cells ctusegs mA (SP + -224) xsaved -> rw_cells ctusegs mA (SP + -128) iframe ->
    rw_cells ctusegs mA (SP + -64) [C8 (Z_to_bv 64 0)] -> rw_cells ctusegs mA (SP + -56) [C1 vb; CB 31 j31] -> rw_cells ctusegs mA (SP + -24) dframe_hi ->
    rw_cells ctusegs mA (SP + -320) [CB 8 j0] -> OCT mod 8 = 0 ->
    implM ctusegs (interp (ap_embed ((blk <- amalloc SZ_ASN1_STRING ;; aret (Some (mkOct blk (Some (q, n)) l bys))) stA))) sA
          (d2i_octet_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F s OW LB E lo B canary m K adr OPP OCT)
          (MS (mkR x1 (Z_to_bv 64 (SP + -320)) gp (wz RATP) t0 t1 t2 (Z_to_bv 64 (SP + -128)) (Z_to_bv 64 OPP) a0 a1 a2 a3 a4 a5 a6 a7
                   (Z_to_bv 64 OCT) (Z_to_bv 64 ITEM_OCTET) (Z_to_bv 64 A) (Z_to_bv 64 l) x22 x23 x24 x25 (Z_to_bv 64 0) s11 t3 t4 t5 t6)
              FA (Z_to_bv 64 EXPRIM_C2I) fcA None mA (seg_rom ctusegs)).
  Proof using B63 CEIL D1 D63 DJXP GLO HM OCThi OCTlo OPPhi OPPlo PBX SP16 SPB.
    intros until p2. intros LO STKG OI FRMA FEA HOPP HOCT L0 LN N31 LBY RBY P2 HA FBUF FPP FJ5 FFC FPIC FJ4 FUT FJ16 FCW FSV FI FD0 FTLC FDH FJ0 OCT8.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    unfold W_d2i_octet_B.PRIM_STK, ASN1_STRING_TYPE_NEW_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RMALLOC_STACK in STKG.
    assert (STK0 : 0 <= STK) by lia. assert (OFS0 : -320 <= 0) by lia. assert (OFS16 : (-320) mod 16 = 0) by reflexivity.
    assert (ESP : bv_unsigned (Z_to_bv 64 (SP + -320)) = SP + -320) by (apply unsigned_lit; lia).
    pose proof (oinv_facts sp m s LB E lo B canary K d D XPO (-320) STK _ _ _ _ _ _ _ OI) as (HEAPA & NDA & BND & FRESH & DJL & DJO).
    pose proof (oinv_call sp m s LB E lo B canary K d D XPO (-320) STK GLO LO STK0 OFS0 SPB B63 _ _ _ _ _ _ _ OI) as (_ & AUXA & _ & STA & _ & _ & ERRA & MIA & CSA & ASA).
    unfold LX_ERRNO, RATP in ERRA. change (3355176 - 164) with 3355012 in ERRA.
    pose proof ASA as (_ & IMG & _).
    pose proof (item_cells_octet mA IMG) as (IT0 & IT8 & IT8L & IT16 & IT32). unfold ITEM_OCTET in IT0, IT8, IT8L, IT16, IT32.
    change (2960328 + 8) with 2960336 in IT8. change (2960328 + 8) with 2960336 in IT8L. change (2960328 + 16) with 2960344 in IT16. change (2960328 + 32) with 2960360 in IT32.
    pose proof (BND q A n ltac:(apply in_app_iff; right; left; reflexivity)) as (BA0 & _ & BAC & BAI & _).
    assert (DLEN : Z.of_nat (length (to_bytes d)) = zlength d) by apply zlength_to_bytes.
    unfold W_d2i_octet_A.xsaved, W_d2i_octet_A.iframe, W_d2i_octet_A.dframe_hi, EXPRIM_C2I, RA_INTERN, RA_D2IEX, ITEM_OCTET, MallocRep.wz in *.
    pose proof (munch_refl [(SP - 320, SP)]%Z mA) as MU. pose proof (wmono_refl ctusegs mA) as WM.
    rename MIA into MI.
    unfold implM. iprefix.
    (* [comment removed for export] *)
    step. step. rewrite (sx32_small 4) by lia. step. step. if_true.
    step. step. step. if_true.
    step. step. step. step. step. if_false.
    step. step. step. zstep.
    setreg 10 (Z_to_bv 64 (4 * (4 - 1) + 267696)) ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
    match goal with H : mem_inv ctusegs ?mx |- evt _ _ (MS _ _ _ _ _ ?mx _) => pose proof (jt_ex_prim_oct mx H) as JT2 end.
    change 267708 with (4 * (4 - 1) + 267696) in JT2.
    step. clear JT2. step. step.
    (* [comment removed for export] *)
    step. setreg 23 (Z_to_bv 64 l) ltac:(f_equal; rewrite unsigned_lit by lia; rewrite Z.add_0_r; symmetry; apply swrap32_small; lia).
    step. if_false. step. step. if_true. step. step. if_true.
    step.
    assert_join10 J2 0x1126c8.
    { intros w10.
      step. step. if_true. step. step.
      name_mem mc.
      match goal with H : stk ctusegs mc lo _ |- _ => rename H into STc end.
      match goal with H : mem_inv ctusegs mc |- _ => rename H into MIc end.
      assert (OIc : oinvK (-320) STK sA stA mc OWA errvA boA [(q, A, n)]).
      { eapply (oinv_munch sp m s LB E lo B canary K d D XPO (-320) STK CEIL GLO LO STK0 OFS0 SPB B63 SP16 OFS16 XPokK PBX);
          [exact OI| exact MU| exact WM| exact MIc| exact STc| exact ERRA|]. constructor; [left; cbn; lia| constructor]. }
      pose proof (oinv_call sp m s LB E lo B canary K d D XPO (-320) STK GLO LO STK0 OFS0 SPB B63 _ _ _ _ _ _ _ OIc) as (HEAPc & AUXc & _ & _ & _ & _ & ERRc & _ & CSc & ASc).
      (* [comment removed for export] *)
      apply evt_done. cbn [abind apbind amalloc aret ap_embed fst snd]. to_implM.
      eapply (ASN1_STRING_type_new_walk HM) with (B := B) (lo := lo) (errv := errvA) (L := OWA ++ [(q, A, n)] ++ LB);
        [exact HEAPc | exact AUXc | rewrite ESP; lia | rewrite ESP; exact STc | exact CEIL | unfold GLOBALS_TOP; lia
        | rewrite ESP; unfold ASN1_STRING_TYPE_NEW_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RMALLOC_STACK; lia
        | exact ERRc | exact MIc | reflexivity | exact CSc | reflexivity | lia | reflexivity | ].
      intros pn sN msN PON. unfold calloc_post in PON. rewrite ?ESP in PON.
      destruct PON as (n0 & n1 & n2 & n11 & n12 & n13 & n14 & n15 & n16 & n17 & n3 & n4 & n5 & n6 & mN & Ab & errvN
                       & -> & MIN & STN & ERRN & AUXN & HPN & FAN & SON & BRN & HEAPN & BLKN).
      replace (ret_pc (Z_to_bv 64 1124080)) with (Z_to_bv 64 1124080) by (symmetry; apply ret_pc_even; [lia| reflexivity]). unfold MallocRep.wz.
      unfold LX_ERRNO, RATP in ERRN. change (3355176 - 164) with 3355012 in ERRN.
      pose proof BRN as (BB0 & BB16 & _ & BBC & BBI). unfold ASN1_STRING_SIZE in *.
      assert (OIN : oinvK (-320) STK sN stA mN OWA errvN boA [(pn, Ab, 24); (q, A, n)]).
      { eapply (oinv_alloc sp m s LB E lo B canary K d D XPO (-320) STK CEIL GLO LO STK0 OFS0 SPB B63 PBX);
          [exact OIc| eapply rheap_pres_weaken; [exact HPN| lia| intros b Hb; exact Hb]| exact HEAPN| exact MIN| exact STN| exact ERRN| exact AUXN| exact FAN| exact SON]. }
      pose proof (oinv_facts sp m s LB E lo B canary K d D XPO (-320) STK _ _ _ _ _ _ _ OIN) as (HEAPN' & NDN & BNDN & FRESHN & DJLN & DJON).
      assert (NPQ : pn <> q).
      { pose proof (LH_nodup _ _ _ HEAPN) as ND0. cbn [map blk_id fst snd] in ND0. apply NoDup_cons_iff in ND0.
        intros ->. apply (proj1 ND0). rewrite map_app. apply in_app_iff. right. left. reflexivity. }
      assert (DJqb : Ab + 24 <= A \/ A + n <= Ab).
      { eapply (blk_disjoint _ _ _ pn Ab 24 q A n HEAPN'); [apply in_app_iff; right; left; reflexivity| apply in_app_iff; right; right; left; reflexivity| exact NPQ]. }
      (* [comment removed for export] *)
      pose proof (agree_of_heap_pres _ _ _ _ HPN) as AGN.
      apply (rw_cells_agree _ _ _ _ _ AGN) in FBUF; [| intros a Ha; left; cbn in Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ AGN) in FPP; [| intros a Ha; left; cbn in Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ AGN) in FJ5; [| intros a Ha; left; cbn in Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ AGN) in FFC; [| intros a Ha; left; cbn in Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ AGN) in FPIC; [| intros a Ha; left; cbn in Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ AGN) in FJ4; [| intros a Ha; left; cbn in Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ AGN) in FUT; [| intros a Ha; left; cbn in Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ AGN) in FJ16; [| intros a Ha; left; cbn in Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ AGN) in FCW; [| intros a Ha; left; cbn in Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ AGN) in FJ0; [| intros a Ha; left; cbn in Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ AGN) in FSV; [| intros a Ha; left; cbn in Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ AGN) in FI; [| intros a Ha; left; cbn in Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ AGN) in FD0; [| intros a Ha; left; cbn in Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ AGN) in FTLC; [| intros a Ha; left; cbn in Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ AGN) in FDH; [| intros a Ha; left; cbn in Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ AGN) in HOPP; [| intros a Ha; left; cbn in Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ AGN) in HOCT; [| intros a Ha; left; cbn in Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ AGN) in HA.
      2:{ intros a Ha. right. right. exists (q, A, n). split; [apply in_app_iff; right; left; reflexivity| cbn; cbn in Ha; lia]. }
      pose proof (oinv_call sp m s LB E lo B canary K d D XPO (-320) STK GLO LO STK0 OFS0 SPB B63 _ _ _ _ _ _ _ OIN) as (_ & _ & _ & _ & _ & _ & _ & _ & CSN & ASN).
      clear AGN MU WM.
      pose proof (munch_refl [(SP - 320, SP); (OCT, OCT + 8)]%Z mN) as MU. pose proof (wmono_refl ctusegs mN) as WM.
      unfold asn1_string_cells, MallocRep.wz in BLKN.
      (* [comment removed for export] *)
      unfold implM. iprefix. step. if_cases KA0; zc KA0; [exfalso; lia|]. clear KA0.
      step. step. step. if_true. step. step. step.
      name_mem mC.
      match goal with H : stk ctusegs mC lo _ |- _ => rename H into STC end.
      match goal with H : mem_inv ctusegs mC |- _ => rename H into MIC end.
      assert (OIC : oinvK (-320) STK sN stA mC OWA errvN boA [(pn, Ab, 24); (q, A, n)]).
      { eapply (oinv_munch sp m s LB E lo B canary K d D XPO (-320) STK CEIL GLO LO STK0 OFS0 SPB B63 SP16 OFS16 XPokK PBX);
          [exact OIN| exact MU| exact WM| exact MIC| exact STC| exact ERRN|]. constructor; [left; cbn; lia|]. constructor; [right; left; unfold W_d2i_octet_A.XPO; right; left; reflexivity| constructor]. }
      pose proof (oinv_call sp m s LB E lo B canary K d D XPO (-320) STK GLO LO STK0 OFS0 SPB B63 _ _ _ _ _ _ _ OIC) as (HEAPC & AUXC & _ & _ & _ & _ & ERRC & _ & CSC & ASC).
      unfold LX_ERRNO, RATP in ERRC. change (3355176 - 164) with 3355012 in ERRC.
      change [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 4); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] with (asn1_string_cells 0 4 0 0) in BLKN.
      clear MU WM. pose proof (munch_refl [(SP - 320 - ASN1_STRING_SET0_STACK, SP - 320); (Ab, Ab + 24)]%Z mC) as MU. pose proof (wmono_refl ctusegs mC) as WM.
      apply evt_done. cbn [abind apbind amalloc aret ap_embed fst snd]. to_implM. apply implM_ret.
      step. eapply evt_cut.
      { eapply ASN1_STRING_set0_walk with (lo := lo) (A := Ab) (D := A) (ty := 4) (len := l);
          [rewrite ESP; exact STC| unfold GLOBALS_TOP; lia| rewrite ESP; unfold ASN1_STRING_SET0_STACK; lia| exact MIC| lia| unfold ASN1_STRING_SIZE; lia| lia| lia| lia| exact BLKN| clear - BB16; Z.div_mod_to_equations; lia| reflexivity| reflexivity| reflexivity]. }
      clear BLKN. cbv beta. intros ms5 (u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m5 & -> & MU5 & WM5 & MI5 & ST5 & CELL5). rewrite ?ESP in *.
      unfold ASN1_STRING_SET0_STACK, ASN1_STRING_SIZE in MU, MU5.
      replace (ret_pc (Z_to_bv 64 0x112764)) with (Z_to_bv 64 0x112764) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      xport FBUF MU5 WM5. xport FPP MU5 WM5. xport FJ5 MU5 WM5. xport FFC MU5 WM5. xport FPIC MU5 WM5. xport FJ4 MU5 WM5. xport FUT MU5 WM5. xport FJ16 MU5 WM5. xport FCW MU5 WM5. xport FJ0 MU5 WM5.
      xport FSV MU5 WM5. xport FI MU5 WM5. xport FD0 MU5 WM5. xport FTLC MU5 WM5. xport FDH MU5 WM5. xport HOPP MU5 WM5. xport HOCT MU5 WM5. xport ERRC MU5 WM5. xport HA MU5 WM5.
      assert (OI5 : oinvK (-320) STK sN stA m5 OWA errvN boA [(pn, Ab, 24); (q, A, n)]).
      { eapply (oinv_munch sp m s LB E lo B canary K d D XPO (-320) STK CEIL GLO LO STK0 OFS0 SPB B63 SP16 OFS16 XPokK PBX);
          [exact OIC| exact MU5| exact WM5| exact MI5| exact ST5| exact ERRC|]. constructor; [left; cbn; lia|]. constructor; [| constructor]. right. right. exists pn, Ab, 24. split; [left; reflexivity| cbn; lia]. }
      pose proof (oinv_call sp m s LB E lo B canary K d D XPO (-320) STK GLO LO STK0 OFS0 SPB B63 _ _ _ _ _ _ _ OI5) as (HEAP5 & _ & _ & _ & _ & _ & ERR5 & _).
      unfold LX_ERRNO, RATP in ERR5. change (3355176 - 164) with 3355012 in ERR5.
      clear MU WM MU5 WM5 MIC STC. pose proof (munch_refl [(SP - 320, SP)]%Z m5) as MU. pose proof (wmono_refl ctusegs m5) as WM. rename MI5 into MI.
      (* [comment removed for export] *)
      unfold asn1_string_cells, MallocRep.wz in CELL5.
      step. step.
      name_mem m6. match goal with H : stk ctusegs m6 lo _ |- _ => rename H into ST6 end. match goal with H : mem_inv ctusegs m6 |- _ => rename H into MI6 end.
      assert (OI6 : oinvK (-320) STK sN stA m6 OWA errvN boA [(pn, Ab, 24); (q, A, n)]).
      { eapply (oinv_munch sp m s LB E lo B canary K d D XPO (-320) STK CEIL GLO LO STK0 OFS0 SPB B63 SP16 OFS16 XPokK PBX);
          [exact OI5| exact MU| exact WM| exact MI6| exact ST6| exact ERR5|]. constructor; [left; cbn; lia| constructor]. }
      set (adr2 := fun x : bptr => if bptr_eqb x pn then Ab else if bptr_eqb x q then A else adr x).
      assert (E2pn : adr2 pn = Ab) by (subst adr2; cbn beta; rewrite bptr_eqb_refl; reflexivity).
      assert (E2q : adr2 q = A) by (subst adr2; cbn beta; rewrite (bptr_eqb_neq q pn ltac:(intros X; exact (NPQ (eq_sym X)))); rewrite bptr_eqb_refl; reflexivity).
      assert (ADR2 : forall b, In b LB -> adr2 (blk_id b) = adr (blk_id b)).
      { intros [[y Ay] ny] Hb. subst adr2. cbn beta. cbn [blk_id fst snd].
        rewrite (bptr_eqb_neq y pn) by (intros ->; apply (FRESHN pn Ab 24 ltac:(left; reflexivity)); rewrite map_app; apply in_app_iff; right; exact (in_ids _ _ _ _ Hb)).
        rewrite (bptr_eqb_neq y q) by (intros ->; apply (FRESHN q A n ltac:(right; left; reflexivity)); rewrite map_app; apply in_app_iff; right; exact (in_ids _ _ _ _ Hb)).
        reflexivity. }
      try rewrite le1_lit in FFC.
      destruct (fb_pack sp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FBUF FPP FJ5 FFC FPIC FJ4 FUT FJ16 FCW FJ0) as (jb & jm & FB).
      destruct (fd_pack sp _ _ _ _ FD0 FTLC) as (jd & FD).
      rewrite <- E2pn in HOCT.
      eapply (dx_ok_tail sp m s LB E lo B canary K d D ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F OW adr OPP OCT CEIL GLO SPB B63 SP16 PBX OPPlo OPPhi OCTlo OCThi DJXP STK)
        with (os := mkOct pn (Some (q, n)) l bys) (adr' := adr2);
        [exact LO| exact STK0| | exact FRMA| exact FEA| exact HOPP| exact HOCT| exact OCT8| | exact ADR2| | exact FB| exact FSV| exact FI| exact FD| exact FDH].
      3: lia.
      { unfold oct_blocks. cbn [os_blk os_data]. unfold ASN1_STRING_SIZE. rewrite E2pn, E2q. exact OI6. }
      { unfold octet_rep, oct_blocks, ASN1_STRING_SIZE. cbn [os_blk os_data os_len os_bytes optr app]. rewrite E2pn, E2q.
        split; [apply in_app_iff; right; left; reflexivity|]. split; [exact CELL5|].
        split; [exact LBY|]. split; [exact RBY|]. split; [lia|].
        split; [intros X; exact (NPQ (eq_sym X))|]. split; [apply in_app_iff; right; right; left; reflexivity|]. split; [lia|].
        cut_hd HA HA1 (A + l). pose proof (rw_cells_bytes_at _ _ _ _ HA1) as BY. cbn [cells_bytes cbytes app] in BY. rewrite app_nil_r in BY. exact BY. } }
    (* [comment removed for export] *)
    assert_join10 J1 0x112690.
    { intros w10'. step. step. if_cases KT2; zc KT2; [apply J2|]. step. step. if_true. apply J2. }
    step. if_cases KT1; zc KT1; [apply J1|]. step. step. if_true. apply J1.
  Qed.

  End Act.
End Proofs.
End WithCeiling0.
