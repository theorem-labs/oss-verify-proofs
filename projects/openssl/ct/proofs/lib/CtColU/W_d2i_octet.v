(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
From OSSVerify.Proofs.openssl.ct.lib.Spec Require Import Prelim Malloc Prog LibProg CtSizes CtWire CtModel ApBase ApState ApErr ApParse ApBridge.
From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OSSVerify.Proofs.openssl.ct.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.openssl.ct.lib.CtMallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.openssl.ct.lib.Spec Require Import STree Monad ProgG Stdio.
From OSSVerify.Proofs.openssl.ct.lib.CtU Require Import Layout Lib_iface Lib_kit Startup_B Printf_lib.
From OSSVerify.Proofs.openssl.ct.lib.CtBnU Require Import BnKit BnHeap BnRep W_crypto.
From OSSVerify.Proofs.openssl.ct.lib.CtHXU Require Import HxpInit HxpFacts.
From OSSVerify.Proofs.openssl.ct.lib.CtRepU Require Import ApCells ApRepDefs ApRep ApWalkTac ApErrKit ApErrKit2 ApErrKit3 ApIface W_err_new W_err_set_debug W_err_set_error W_c2i_int W_get_object W_get_object_walk W_check_tlen W_prefix_create W_asn1_string W_item_d2i_stmt W_item_d2i_img W_item_d2i_front W_item_d2i_tail.
From OSSVerify.Proofs.openssl.ct.lib.CtRepU Require Import ApUbTab ApUTac.
From OSSVerify.Proofs.openssl.ct.lib.BnBoth Require Import UbKit.
From OSSVerify.Proofs.openssl.ct.lib.CtParseU Require Import PzDefs.
From OSSVerify.Proofs.openssl.ct.lib.CtEncU Require Import W_asn1_enc_leaves.
From OSSVerify.Proofs.openssl.ct.lib.CtSctU Require Import SctStmt.
From OSSVerify.Proofs.openssl.ct.lib.CtColU Require Import ColKit ColDefs W_bufmem W_check_tlen_gen W_collect W_d2i_octet_A W_d2i_octet_B W_d2i_octet_C W_d2i_octet_D.
From OSSVerify.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.openssl.ct.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope am_scope.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].
Local Ltac ubchk_strong := OSSVerify.Proofs.openssl.ct.lib.Lib.Step.zstep;
  let C := fresh "Cs" in if_cases C;
  [ exfalso; zify_cond C;
    repeat (first [ rewrite ub_land64_small in C by lia | rewrite ub_lxor_sign63 in C by lia | rewrite unsigned_lit in C by lia ]);
    ub_ltb_cases C
  | clear C ].
Local Ltac ub1c :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
      let k := eval vm_compute in (ub_kind pc) in
      lazymatch k with
      | 1%Z => OSSVerify.Proofs.openssl.ct.lib.Lib.Step.zstep
      | 2%Z => first [ (OSSVerify.Proofs.openssl.ct.lib.Lib.Step.zstep; udecide) | ubchk_strong | uchk ]
      end
  end.
Local Ltac step := try udecide; repeat ub1c; OSSVerify.Proofs.openssl.ct.lib.Lib.Step.step.
Local Ltac zstep := try udecide; repeat ub1c; OSSVerify.Proofs.openssl.ct.lib.Lib.Step.zstep.
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
Lemma le8_of_bytes' : forall bs : list byte, length bs = 8%nat -> le8 (le_bytes_to_word bs) = bs.
Proof.
  intros bs HL. unfold le8, word_to_le_bytes, le_bytes_to_word.
  pose proof (bytes_le_to_Z_range bs) as HR. rewrite HL in HR. change (2 ^ (8 * Z.of_nat 8))%Z with (2^64)%Z in HR.
  rewrite unsigned_lit by lia. rewrite <- HL. apply Z_to_le_bytes_to_Z.
Qed.
Lemma cb8_word : forall m a j, rw_cells ctusegs m a [CB 8 j] -> rw_cells ctusegs m a [C8 (le_bytes_to_word j)].
Proof.
  intros m a j BLOB.
  assert (LEN8 : length j = 8%nat) by exact (cb_len m a 8 j BLOB).
  eapply rw_cells_recast; [exact BLOB| cbn; tauto| | reflexivity].
  cbn [cells_bytes cbytes]. f_equal. apply le8_of_bytes'. exact LEN8.
Qed.

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

  Local Notation CONS_STK := (W_d2i_octet_D.CONS_STK).

  (* [comment removed for export] *)
  Lemma d2i_octet_stack_ok : 320 + CONS_STK <= D2I_OCTET_STACK.
  Proof.
    clear. unfold W_d2i_octet_D.CONS_STK, D2I_OCTET_STACK, COLLECT_STACK, COLLECT_FRAME, CHECK_TLEN_STACK, GETOBJ_STACK, ERR_SET_ERROR_STACK. std_lia__.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma dx_intern_fail : forall (STK3 : Z)
      (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word)
      (FA : bvmap 5 word) (fcA : bv 32) sA stA mA OWA errvA boA (ov : word) (jd : list byte),
    lo <= SP + -320 - STK3 -> 0 <= STK3 ->
    oinvK (-320) STK3 sA stA mA OWA errvA boA [] -> stk ctusegs mA lo (SP + -128) -> frm0 fcA -> (forall k : reg, bv_unsigned k <> 10 -> reg_get FA k = reg_get F k) ->
    rw_cells ctusegs mA OPP [C8 ov] -> rw_cells ctusegs mA OCT [C8 (Z_to_bv 64 0)] -> OCT mod 8 = 0 ->
    rw_cells ctusegs mA (SP + -128) iframe -> rw_cells ctusegs mA (SP + -64) [CB 40 jd] -> rw_cells ctusegs mA (SP + -24) dframe_hi ->
    evt ctusegs (d2i_octet_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F s OW LB E lo B canary m K adr OPP OCT (None, stA) sA)
      (MS (mkR (Z_to_bv 64 RA_INTERN) (Z_to_bv 64 (SP + -128)) gp (wz RATP) x5 x6 x7 (Z_to_bv 64 (SP + -64)) (Z_to_bv 64 ITEM_OCTET) (Z_to_bv 64 0) x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 OCT) s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          FA (Z_to_bv 64 RA_INTERN) fcA None mA (seg_rom ctusegs)).
  Proof using CEIL GLO SPB B63 SP16 PBX OPPlo OPPhi OCTlo OCThi.
    intros until jd.
    intros LOW STK0 OI ST FRM FEQ OPPC OCTC OCTA IFC TOPB DHC.
    pose proof (bv_unsigned_in_range 64 sp) as SPRNG. unfold bv_modulus in SPRNG. cbn in SPRNG.
    pose proof (oinv_call sp m s LB E lo B canary K d D XPO (-320) STK3 GLO LOW STK0 ltac:(lia) SPB B63 _ _ _ _ _ _ _ OI)
      as (_ & _ & _ & _ & _ & _ & ERRA & MIA & _ & ASA).
    unfold LX_ERRNO, RATP in ERRA. change (3355176 - 164) with 3355012 in ERRA.
    pose proof ASA as (_ & IMG & _).
    destruct (item_cells_octet mA IMG) as (IB0 & IB8 & _ & IB16 & IB32).
    unfold ITEM_OCTET in IB0, IB8, IB16, IB32. clear ASA IMG.
    assert (E128 : bv_unsigned (Z_to_bv 64 (SP + -128)) = SP + -128) by (apply unsigned_lit; lia).
    unfold W_d2i_octet_A.iframe, W_d2i_octet_A.dframe_hi, RA_INTERN, RA_D2IEX in *.
    pose proof (munch_refl [(SP - 240, SP - 128)]%Z mA) as MU. pose proof (wmono_refl ctusegs mA) as WM.
    step. step. if_false. step. step. step.
    carve_frame 16%nat ST. do 8 step. release_frame FR ST (SP + -128). step.
    name_mem m1.
    eapply embed_free_null with (lo := lo) (PVAL := OCT) (IT := ITEM_OCTET) (w := V_ASN1_OCTET_STRING);
      rewrite ?E128; [exact ST| exact MIA| lia| lia| lia| lia| lia| exact OCTA| exact OCTC| unfold ITEM_OCTET; lia| unfold ITEM_OCTET; lia
      | reflexivity| exact IB0| exact IB8| exact IB16| exact IB32| unfold V_ASN1_OCTET_STRING; lia| unfold V_ASN1_OCTET_STRING; lia| ].
    intros t0' t1' a0' a1' a2' a3' m2 MU2 WM2 MI2 ST2.
    xport IFC MU2 WM2. xport TOPB MU2 WM2. xport DHC MU2 WM2. xport OPPC MU2 WM2. xport OCTC MU2 WM2. xport ERRA MU2 WM2.
    assert (MUA : munch [(SP - 240, SP - 128)]%Z mA m2).
    { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU2]. intros x; cbn; lia. }
    pose proof (wmono_trans _ _ _ _ WM WM2) as WMA. clear MU MU2 WM WM2 IB0 IB8 IB16 IB32 MIA ST.
    replace (ret_pc (Z_to_bv 64 1117848)) with (Z_to_bv 64 1117848) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    step. step. do 5 step. step. release_frame IFC ST2 (SP + -64). step.
    replace (ret_pc (Z_to_bv 64 1118008)) with (Z_to_bv 64 1118008) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    step. if_true. step. step. step. step. step.
    release_frame TOPB ST2 (SP + -24). release_frame DHC ST2 (bv_unsigned sp). step.
    destruct (stk_split ctusegs m2 lo (SP + -320) (bv_unsigned sp) ST2 ltac:(lia)) as [ST320 _].
    assert (OI2 : oinvK (-320) STK3 sA stA m2 OWA errvA boA []).
    { eapply (oinv_munch sp m s LB E lo B canary K d D XPO (-320) STK3 CEIL GLO LOW STK0 ltac:(lia) SPB B63 SP16 ltac:(reflexivity) XPokK PBX);
        [exact OI| exact MUA| exact WMA| exact MI2| exact ST320| exact ERRA|].
      constructor; [left; cbn; lia| constructor]. }
    apply evt_done.
    eapply (dx_fin_none sp m s LB E lo B canary K d D ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F OW adr OPP OCT SPB SP16 (-320) STK3);
      [exact LOW| lia| exact STK0| exact OI2| exact ST2| exact FRM| exact FEQ| exact OPPC| exact OCTC].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma dx_after_fail : forall (STK : Z) (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s7x : word) (FA : bvmap 5 word) (fcA : bv 32)
      sA stA mA OWA errvA boA (ov cw pl pw : word) (vb bi bc : byte) (j5 j4 j16 j31 j0 : list byte),
    lo <= SP + -320 - STK -> ERR_SET_ERROR_STACK <= STK ->
    oinvK (-320) STK sA stA mA OWA errvA boA [] -> frm0 fcA -> (forall k : reg, bv_unsigned k <> 10 -> reg_get FA k = reg_get F k) ->
    rw_cells ctusegs mA OPP [C8 ov] -> rw_cells ctusegs mA OCT [C8 (Z_to_bv 64 0)] -> OCT mod 8 = 0 ->
    rw_cells ctusegs mA (SP + -312) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
    rw_cells ctusegs mA (SP + -280) [C8 pw] ->
    rw_cells ctusegs mA (SP + -272) [CB 5 j5] -> rw_cells ctusegs mA (SP + -267) [C1 (Z_to_bv 8 0)] ->
    rw_cells ctusegs mA (SP + -266) [C1 bi; C1 bc; C8 pl] ->
    rw_cells ctusegs mA (SP + -256) [CB 4 j4] -> rw_cells ctusegs mA (SP + -252) [C4 (Z_to_bv 64 4)] -> rw_cells ctusegs mA (SP + -248) [CB 16 j16] ->
    rw_cells ctusegs mA (SP + -232) [C8 cw] -> rw_cells ctusegs mA (SP + -224) xsaved -> rw_cells ctusegs mA (SP + -128) iframe ->
    rw_cells ctusegs mA (SP + -64) [C8 (Z_to_bv 64 0)] -> rw_cells ctusegs mA (SP + -56) [C1 vb; CB 31 j31] -> rw_cells ctusegs mA (SP + -24) dframe_hi ->
    rw_cells ctusegs mA (SP + -320) [CB 8 j0] ->
    implM ctusegs (interp (ap_embed ((err_raise RS_prim_nested ;;; aret (@None (octet bptr))) stA))) sA
          (d2i_octet_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F s OW LB E lo B canary m K adr OPP OCT)
          (MS (mkR x1 (Z_to_bv 64 (SP + -320)) gp (wz RATP) t0 t1 t2 (Z_to_bv 64 (SP + -128)) (Z_to_bv 64 OPP) (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
                   (Z_to_bv 64 OCT) (Z_to_bv 64 ITEM_OCTET) (Z_to_bv 64 (SP + -56)) (Z_to_bv 64 0) (Z_to_bv 64 (zlength d)) s7x (Z_to_bv 64 0) (Z_to_bv 64 (-1)) s10 s11 t3 t4 t5 t6)
              FA (Z_to_bv 64 EXPRIM_AFTER_TLEN) fcA None mA (seg_rom ctusegs)).
  Proof using HM HF CEIL GLO SPB B63 SP16 PBX OPPlo OPPhi OCTlo OCThi.
    intros until j0.
    intros LOW STKE OI FRM FEQ OPPC OCTC OCTA ZP PWC J5C FCC PIC J4C UTC J16C CWC XSC IFC P0C TLC DHC J0C.
    pose proof (bv_unsigned_in_range 64 sp) as SPRNG. unfold bv_modulus in SPRNG. cbn in SPRNG.
    assert (STK0 : 0 <= STK) by (unfold ERR_SET_ERROR_STACK in STKE; lia).
    destruct (fb_pack sp mA _ _ _ _ pw cw _ _ bi bc pl j5 j4 j16 j0 ZP PWC J5C FCC PIC J4C UTC J16C CWC J0C) as (jb & jm & LOWF).
    destruct (fb_blob sp mA pw _ jb j5 jm LOWF) as (jlo & LOWB).
    destruct (fd_pack sp mA _ vb j31 P0C TLC) as (jd & TOPB).
    clear ZP PWC J5C FCC PIC J4C UTC J16C CWC J0C P0C TLC LOWF.
    unfold EXPRIM_AFTER_TLEN.
    unfold implM. iprefix.
    step. step. if_false. step. if_false.
    ihere. to_implM.
    eapply implM_abind.
    { eapply (dx_raise HM HF sp m s LB E lo B canary K d D gp OPP OCT CEIL GLO SPB B63 PBX OPPlo OPPhi OCTlo OCThi
                1122152 1122180 5%nat 1122200 RS_prim_nested ERR_R_NESTED_ASN1_ERROR A_ASN1_D2I_EX_PRIMITIVE (-320) STK);
        [right; repeat split; reflexivity| exact LOW| lia| reflexivity| exact STKE| exact OI| exact FRM]. }
    intros r sB msB AFTER. unfold dx_raise_post in AFTER.
    destruct AFTER as (q0 & q1 & q2 & p0 & p1 & p2 & p3 & p4 & p5 & p6 & p7 & q3 & q4 & q5 & q6 & FB & fcB & mB & OWB & errvB & boB
                       & -> & FRMB & FEB & OIB & LXB).
    apply agree_of_lx_pres in LXB.
    assert (ABOVE : forall a, SP + -320 <= a -> lx_client ([] ++ LB) (SP + -320) LIBW_AP a).
    { intros a Ha. split; [unfold LIBW_AP; cbn [rin_ivs fst snd]; lia| left; exact Ha]. }
    apply (rw_cells_agree _ _ _ _ _ LXB) in LOWB; [| intros a Ha; apply ABOVE; lia].
    apply (rw_cells_agree _ _ _ _ _ LXB) in XSC; [| intros a Ha; apply ABOVE; lia].
    apply (rw_cells_agree _ _ _ _ _ LXB) in IFC; [| intros a Ha; apply ABOVE; lia].
    apply (rw_cells_agree _ _ _ _ _ LXB) in TOPB; [| intros a Ha; apply ABOVE; lia].
    apply (rw_cells_agree _ _ _ _ _ LXB) in DHC; [| intros a Ha; apply ABOVE; lia].
    apply (rw_cells_agree _ _ _ _ _ LXB) in OPPC; [| intros a Ha; apply ABOVE; lia].
    apply (rw_cells_agree _ _ _ _ _ LXB) in OCTC; [| intros a Ha; apply ABOVE; lia].
    destruct r as [u stB]. cbn [fst snd] in *. apply implM_aret.
    step.
    eapply (dx_fail_tail sp m s LB E lo B canary K d D ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F OW adr OPP OCT
              CEIL GLO SPB B63 SP16 PBX OPPlo OPPhi OCTlo OCThi STK);
      [exact LOW| exact STK0| exact OIB| exact FRMB| | exact OPPC| exact OCTC| exact OCTA| exact LOWB| exact XSC| exact IFC| exact TOPB| exact DHC].
    intros k NOT10. rewrite (FEB k NOT10). exact (FEQ k NOT10).
  Qed.

  End Act.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem d2i_octet_walk : d2i_octet_spec.
  Proof using HM HF HGO.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6.
    intros F fc m s st OW LB E bo lo B errv canary K adr d D OPP OCT.
    intros PRE TP FRM KOW KIDS PAY ADRB OPPlo OPPhi OPPC OPPal OCTlo OCThi OCTC OCTal DJXP EA0 EA1 EA2.
    subst tp a0 a1 a2.
    destruct PAY as (HB & DF & D1 & D63 & D30 & PBB).
    assert (PBX : d = [] \/ exists pb PA psz, In (pb, PA, psz) LB /\ PA <= D /\ D + zlength d <= PA + psz).
    { destruct PBB as [E0|([[pb PA] psz] & H1 & H2 & H3)]; [left; exact E0| right; exists pb, PA, psz].
      cbn [blk_addr blk_size fst snd] in H2, H3. split; [exact H1| split; [exact H2| exact H3]]. }
    pose proof PRE as (HEAP & ASt & IDS & DC & AUX & SPB & B63 & ST & CEIL & GLOT & LOW & ERR & SSP & MI & SP16).
    unfold GLOBALS_TOP in GLOT.
    assert (DSTK : D2I_OCTET_STACK = 10000) by (unfold D2I_OCTET_STACK, GETOBJ_STACK, ERR_SET_ERROR_STACK; reflexivity).
    assert (ESTK : ERR_SET_ERROR_STACK = 8416) by (unfold ERR_SET_ERROR_STACK; reflexivity).
    assert (CTSTK : CHECK_TLEN_STACK = 8608) by (unfold CHECK_TLEN_STACK, GETOBJ_STACK, ERR_SET_ERROR_STACK; reflexivity).
    pose proof (bv_unsigned_in_range 64 sp) as SPRNG. unfold bv_modulus in SPRNG. cbn in SPRNG.
    pose proof d2i_octet_stack_ok as STKOK.
    pose proof cons_stk_facts as (PRIMLE & GROWLE & FREELE).
    assert (STKB : lo <= bv_unsigned sp + -320 - (D2I_OCTET_STACK - 320)) by lia.
    pose proof (oinv_entry sp m s LB E lo B canary K d D (XPO OPP OCT) (-320) (D2I_OCTET_STACK - 320)
                  CEIL GLOT STKB ltac:(lia)
                  ltac:(lia) SPB B63 SP16 ltac:(reflexivity) st OW bo errv
                  ltac:(replace (- (-320) + (D2I_OCTET_STACK - 320)) with D2I_OCTET_STACK by lia; exact PRE)
                  KOW KIDS HB) as OIE.
    unfold wz in *.
    assert (ERRA : rw_cells ctusegs m 3355012 [C4 errv]).
    { replace 3355012 with (bv_unsigned (Z_to_bv 64 RATP) + -164); [exact ERR| unfold RATP; rewrite unsigned_lit by lia; lia]. }
    clear ERR.
    unfold implM. iprefix.
    unfold W_item_d2i_stmt.D2I_ASN1_OCTET_STRING.
    pose proof (munch_refl [(bv_unsigned sp - 320, bv_unsigned sp)]%Z m) as MU.
    pose proof (wmono_refl ctusegs m) as WM.
    carve_frame 16%nat ST. do 9 step. release_frame FR ST (bv_unsigned sp). step.
    carve_frame 16%nat ST. do 9 step. release_frame FR ST (bv_unsigned sp). step.
    carve_frame 64%nat ST. do 9 step.
    step. if_cases KOCT; zc KOCT; [exfalso; lia|]. clear KOCT.
    do 8 step.
    carve_frame 64%nat ST. do 7 step.
    step. if_cases KO2; zc KO2; [exfalso; lia|]. clear KO2.
    step. step. if_cases KIT; zc KIT; [exfalso; revert KIT; vm_compute; congruence|]. clear KIT.
    do 5 step.
    step.
    carve_frame 176%nat ST. do 15 step. do 6 step.
    step. if_cases KE1; zc KE1; [exfalso; lia|]. clear KE1.
    step.
    step. if_cases KE2; zc KE2; [exfalso; revert KE2; vm_compute; congruence|]. clear KE2.
    step.
    assert (ZL0 : 0 <= zlength d) by (unfold zlength; lia).
    assert (ERRSTK : ERR_SET_ERROR_STACK <= D2I_OCTET_STACK - 320) by lia.
    assert (IFC : rw_cells ctusegs m1 (bv_unsigned sp + -128) (iframe sp s2 s3 OCT)) by (unfold W_d2i_octet_A.iframe, RA_D2IEX; exact FR0).
    clear FR0.
    lazymatch type of FR with
    | rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?rest) => change (c0 :: c1 :: c2 :: rest) with ([c0] ++ [c1; c2] ++ rest) in FR
    end.
    apply rw_cells_app in FR. destruct FR as [FDZ FR].
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FR.
    apply rw_cells_app in FR. destruct FR as [FDT FDH].
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FDH.
    replace (bv_unsigned sp + -64 + 8) with (bv_unsigned sp + -56) in FDT by lia.
    replace (bv_unsigned sp + -64 + Z.of_nat 8 + Z.of_nat 32) with (bv_unsigned sp + -24) in FDH by lia.
    assert (DHC : rw_cells ctusegs m1 (bv_unsigned sp + -24) (dframe_hi ra s0 s1)) by (unfold W_d2i_octet_A.dframe_hi; exact FDH).
    clear FDH.
    destruct (stk_split ctusegs m1 lo (bv_unsigned sp + -320) (bv_unsigned sp + -304) ST ltac:(lia)) as [ST320 _].
    assert (OI1 : oinv sp m s LB E lo B canary K d D (XPO OPP OCT) (-320) (D2I_OCTET_STACK - 320) s st m1 OW errv bo []).
    { eapply (oinv_munch sp m s LB E lo B canary K d D (XPO OPP OCT) (-320) (D2I_OCTET_STACK - 320)
                CEIL GLOT STKB ltac:(lia) ltac:(lia) SPB B63 SP16 ltac:(reflexivity)
                (XPok sp B OPP OCT OPPlo OPPhi OCTlo OCThi) PBX);
        [exact OIE| exact MU| exact WM| exact MI| exact ST320| exact ERRA|].
      constructor; [left; cbn; lia| constructor]. }
    unfold d2i_octet.
    destruct (Z.leb_spec (zlength d) 0) as [LEN0|LEN0]; cbv iota.
    - (* empty payload: the length check raises RS_td_small and the call unwinds *)
      destruct (fd_pack sp m1 _ _ _ FDZ FDT) as (jd & TOPB).
      step. if_cases KL; zc KL; [| exfalso; lia]. clear KL.
      assert (OI2 : oinv sp m s LB E lo B canary K d D (XPO OPP OCT) (-304) (D2I_OCTET_STACK - 320) s st m1 OW errv bo []).
      { eapply oinv_reframe; [exact OI1| exact SPB| exact SP16| exact ST| lia| lia| lia| reflexivity]. }
      ihere. to_implM.
      eapply implM_abind.
      { eapply (dx_raise HM HF sp m s LB E lo B canary K d D gp OPP OCT CEIL GLOT SPB B63 PBX OPPlo OPPhi OCTlo OCThi
                  1118380 1118408 4%nat 1118424 RS_td_small 224 A_ASN1_ITEM_EMBED_D2I (-304) (D2I_OCTET_STACK - 320));
          [left; repeat split; reflexivity| lia| lia| reflexivity| exact ERRSTK| exact OI2| exact FRM]. }
      intros r sB msB AFT. unfold dx_raise_post in AFT.
      destruct AFT as (q0 & q1 & q2 & p0 & p1 & p2 & p3 & p4 & p5 & p6 & p7 & q3 & q4 & q5 & q6 & FB & fcB & mB & OWB & errvB & boB
                       & -> & FRMB & FEB & OIB & LXB).
      destruct r as [u stB]. cbn [fst snd] in *. apply implM_aret.
      apply agree_of_lx_pres in LXB.
      assert (ABOVE : forall a, bv_unsigned sp + -304 <= a -> lx_client ([] ++ LB) (bv_unsigned sp + -304) LIBW_AP a).
      { intros a Ha. split; [unfold LIBW_AP; cbn [rin_ivs fst snd]; lia| left; exact Ha]. }
      apply (rw_cells_agree _ _ _ _ _ LXB) in FR1; [| intros a Ha; apply ABOVE; cbn in Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ LXB) in IFC; [| intros a Ha; apply ABOVE; cbn in Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ LXB) in TOPB; [| intros a Ha; apply ABOVE; cbn in Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ LXB) in DHC; [| intros a Ha; apply ABOVE; cbn in Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ LXB) in OPPC; [| intros a Ha; apply ABOVE; cbn in Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ LXB) in OCTC; [| intros a Ha; apply ABOVE; cbn in Ha; lia].
      pose proof (oinv_call sp m s LB E lo B canary K d D (XPO OPP OCT) (-304) (D2I_OCTET_STACK - 320) GLOT ltac:(lia) ltac:(lia) ltac:(lia) SPB B63 _ _ _ _ _ _ _ OIB)
        as (_ & _ & _ & STB & _ & _ & ERRB & MIB & _).
      do 15 step. release_frame FR1 STB (bv_unsigned sp + -128). step.
      replace (ret_pc (Z_to_bv 64 1117828)) with (Z_to_bv 64 1117828) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      destruct (stk_split ctusegs mB lo (bv_unsigned sp + -320) (bv_unsigned sp + -128) STB ltac:(lia)) as [STB320 _].
      eapply (dx_intern_fail sp m s LB E lo B canary K d D ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F OW adr OPP OCT
                CEIL GLOT SPB B63 SP16 PBX OPPlo OPPhi OCTlo OCThi (D2I_OCTET_STACK - 320));
        [lia| lia| | exact STB| exact FRMB| exact FEB| exact OPPC| exact OCTC| exact OCTal| exact IFC| exact TOPB| exact DHC].
      eapply oinv_reframe; [exact OIB| exact SPB| exact SP16| exact STB320| lia| lia| lia| reflexivity].
    - (* non-empty payload: on to asn1_d2i_ex_primitive and asn1_check_tlen *)
      step. if_cases KL; zc KL; [exfalso; lia|].
      pose proof (oinv_call sp m s LB E lo B canary K d D (XPO OPP OCT) (-320) (D2I_OCTET_STACK - 320) GLOT STKB ltac:(lia) ltac:(lia) SPB B63 _ _ _ _ _ _ _ OI1)
        as (_ & _ & _ & _ & _ & _ & _ & _ & _ & AS1).
      pose proof AS1 as (_ & IMG1 & _).
      destruct (item_cells_octet m1 IMG1) as (IB0 & IB8 & IB8L & IB16 & IB32).
      unfold ITEM_OCTET in IB0, IB8, IB8L, IB16, IB32.
      change (2960328 + 8) with 2960336 in IB8, IB8L.
      change (2960328 + 16) with 2960344 in IB16.
      change (2960328 + 32) with 2960360 in IB32.
      repeat step.
      lazymatch goal with
      | |- context [Z_to_bv 64 (?e + 267668)] => change (Z_to_bv 64 (e + 267668)) with (Z_to_bv 64 267668)
      end.
      match goal with H : mem_inv ctusegs ?mx |- evt _ _ (MS _ _ _ _ _ ?mx _) => pose proof (jt_embed_d2i mx H) as JT end.
      step. clear JT. rewrite (sx32_small 851044) by lia.
      repeat step.
      carve_frame 16%nat ST. rename FR into FLO.
      repeat step.
      lazymatch type of FR1 with
      | rw_cells _ _ _ (?c0 :: ?c1 :: ?rest) => change (c0 :: c1 :: rest) with ([c0] ++ [c1] ++ rest) in FR1
      end.
      apply rw_cells_app in FR1. destruct FR1 as [FRJ FR1].
      cbn [cells_size csize Nat.add] in FR1.
      apply rw_cells_app in FR1. destruct FR1 as [FRW FR1].
      cbn [cells_size csize Nat.add] in FR1.
      replace (bv_unsigned sp + -304 + Z.of_nat 32) with (bv_unsigned sp + -272) in FRW by lia.
      replace (bv_unsigned sp + -304 + Z.of_nat 32 + Z.of_nat 8) with (bv_unsigned sp + -264) in FR1 by lia.
      lazymatch type of FRW with
      | rw_cells _ _ _ [C8 ?v] =>
          eapply (rw_cells_recast _ _ _ [CB 8 (le8 v)]) in FRW;
            [| cbn [cells_wf cell_wf]; split; [apply length_le8| exact I]| reflexivity| reflexivity]
      end.
      repeat (lazymatch goal with
              | |- evt _ _ (MS _ _ (Z_to_bv 64 1124252) _ _ _ _) => fail
              | _ => step
              end).
      lazymatch type of FRW with
      | rw_cells _ _ _ (?c0 :: ?c1 :: ?rest) => change (c0 :: c1 :: rest) with ([c0; c1] ++ rest) in FRW
      end.
      apply rw_cells_app in FRW. destruct FRW as [FR5 FRB2].
      cbn [cells_size csize Nat.add] in FRB2.
      replace (bv_unsigned sp + -272 + Z.of_nat 6) with (bv_unsigned sp + -266) in FRB2 by lia.
      apply (cb_split _ _ 1 1) in FRB2.
      lazymatch type of FRB2 with
      | rw_cells _ _ _ (?c0 :: ?rest) => change (c0 :: rest) with ([c0] ++ rest) in FRB2
      end.
      apply rw_cells_app in FRB2. destruct FRB2 as [FRBI0 FRBC0].
      cbn [cells_size csize Nat.add] in FRBC0.
      replace (bv_unsigned sp + -266 + Z.of_nat 1) with (bv_unsigned sp + -265) in FRBC0 by lia.
      destruct (cb_byte _ _ _ FRBI0) as [bi FRBI].
      destruct (cb_byte _ _ _ FRBC0) as [bc FRBC].
      lazymatch type of FR1 with
      | rw_cells _ _ _ (?c0 :: ?rest) => change (c0 :: rest) with ([c0] ++ rest) in FR1
      end.
      apply rw_cells_app in FR1. destruct FR1 as [FRP FR1].
      cbn [cells_size csize Nat.add] in FR1.
      destruct (blob_of _ _ _ 8%nat FRP eq_refl) as [jl FRPL].
      assert (HPIC : rw_cells ctusegs m0 (bv_unsigned sp + -266) [C1 bi; C1 bc; CB 8 jl]).
      { change [C1 bi; C1 bc; CB 8 jl] with ([C1 bi] ++ ([C1 bc] ++ [CB 8 jl])).
        apply rw_cells_app. split; [exact FRBI|].
        cbn [cells_size csize Nat.add].
        replace (bv_unsigned sp + -266 + Z.of_nat 1) with (bv_unsigned sp + -265) by lia.
        apply rw_cells_app. split; [exact FRBC|].
        cbn [cells_size csize Nat.add].
        replace (bv_unsigned sp + -265 + Z.of_nat 1) with (bv_unsigned sp + -264) by lia.
        exact FRPL. }
      lazymatch type of FRJ with
      | rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?rest) => change (c0 :: c1 :: c2 :: rest) with ([c0; c1; c2] ++ rest) in FRJ
      end.
      apply rw_cells_app in FRJ. destruct FRJ as [FRZ3 FRPP].
      cbn [cells_size csize Nat.add] in FRPP.
      replace (bv_unsigned sp + -304 + Z.of_nat 24) with (bv_unsigned sp + -280) in FRPP by lia.
      assert (OI0 : oinv sp m s LB E lo B canary K d D (XPO OPP OCT) (-320) (D2I_OCTET_STACK - 320) s st m0 OW errv bo []).
      { eapply (oinv_munch sp m s LB E lo B canary K d D (XPO OPP OCT) (-320) (D2I_OCTET_STACK - 320)
                  CEIL GLOT STKB ltac:(lia) ltac:(lia) SPB B63 SP16 ltac:(reflexivity)
                  (XPok sp B OPP OCT OPPlo OPPhi OCTlo OCThi) PBX);
          [exact OIE| exact MU| exact WM| exact MI| exact ST| exact ERRA|].
        constructor; [left; cbn; lia| constructor]. }
      lazymatch type of FLO with
      | rw_cells _ _ _ (?c0 :: ?rest) => change (c0 :: rest) with ([c0] ++ rest) in FLO
      end.
      apply rw_cells_app in FLO. destruct FLO as [J0 Z1].
      cbn [cells_size csize Nat.add] in Z1.
      replace (bv_unsigned sp + -320 + Z.of_nat 8) with (bv_unsigned sp + -312) in Z1 by lia.
      assert (Z4 : rw_cells ctusegs m0 (bv_unsigned sp + -312)
                     [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]).
      { change [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
          with ([C8 (Z_to_bv 64 0)] ++ [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]).
        apply rw_cells_app. split; [exact Z1|].
        cbn [cells_size csize Nat.add].
        replace (bv_unsigned sp + -312 + Z.of_nat 8) with (bv_unsigned sp + -304) by lia.
        exact FRZ3. }
      lazymatch type of FR5 with
      | rw_cells _ _ _ (?c0 :: ?rest) => change (c0 :: rest) with ([c0] ++ rest) in FR5
      end.
      apply rw_cells_app in FR5. destruct FR5 as [J5 FC].
      cbn [cells_size csize Nat.add] in FC.
      replace (bv_unsigned sp + -272 + Z.of_nat 5) with (bv_unsigned sp + -267) in FC by lia.
      replace (bv_unsigned sp + -264 + Z.of_nat 8) with (bv_unsigned sp + -256) in FR1 by lia.
      lazymatch type of FR1 with
      | rw_cells _ _ _ (?c0 :: ?rest) => change (c0 :: rest) with ([c0] ++ rest) in FR1
      end.
      apply rw_cells_app in FR1. destruct FR1 as [J4 FR1].
      cbn [cells_size csize Nat.add] in FR1.
      replace (bv_unsigned sp + -256 + Z.of_nat 4) with (bv_unsigned sp + -252) in FR1 by lia.
      lazymatch type of FR1 with
      | rw_cells _ _ _ (?c0 :: ?rest) => change (c0 :: rest) with ([c0] ++ rest) in FR1
      end.
      apply rw_cells_app in FR1. destruct FR1 as [UT FR1].
      cbn [cells_size csize Nat.add] in FR1.
      replace (bv_unsigned sp + -252 + Z.of_nat 4) with (bv_unsigned sp + -248) in FR1 by lia.
      lazymatch type of FR1 with
      | rw_cells _ _ _ (?c0 :: ?c1 :: ?rest) => change (c0 :: c1 :: rest) with ([c0; c1] ++ rest) in FR1
      end.
      apply rw_cells_app in FR1. destruct FR1 as [J16A FR1].
      cbn [cells_size csize Nat.add] in FR1.
      replace (bv_unsigned sp + -248 + Z.of_nat 16) with (bv_unsigned sp + -232) in FR1 by lia.
      destruct (blob_of _ _ _ 16%nat J16A eq_refl) as [j16 J16].
      lazymatch type of FR1 with
      | rw_cells _ _ _ (?c0 :: ?rest) => change (c0 :: rest) with ([c0] ++ rest) in FR1
      end.
      apply rw_cells_app in FR1. destruct FR1 as [CW XS].
      cbn [cells_size csize Nat.add] in XS.
      replace (bv_unsigned sp + -232 + Z.of_nat 8) with (bv_unsigned sp + -224) in XS by lia.
      assert (E4 : sx32 (Z_to_bv 64 ApPrim.V_ASN1_OCTET_STRING) = Z_to_bv 64 ApPrim.V_ASN1_OCTET_STRING)
        by (apply sx32_small; unfold ApPrim.V_ASN1_OCTET_STRING; lia).
      rewrite !E4 in *.
      replace (bv_unsigned sp + -264) with (bv_unsigned sp + -266 + 2) by lia.
      replace (bv_unsigned sp + -265) with (bv_unsigned sp + -266 + 1) by lia.
      ihere. to_implM.
      eapply (check_tlen_gen HM HF HGO sp m s LB E lo B canary K d D (XPO OPP OCT)
                DF CEIL GLOT SPB B63 SP16 (XPok sp B OPP OCT OPPlo OPPhi OCTlo OCThi) PBX D1 D63 D30)
        with (ot := Some ApPrim.V_ASN1_OCTET_STRING) (OFS := -320) (STK := D2I_OCTET_STACK - 320)
             (op := 0) (len := zlength d) (PIC := bv_unsigned sp + -266) (PPC := bv_unsigned sp + -280)
             (TLCo := Some (bv_unsigned sp + -56));
        [ lia | lia | reflexivity | lia | exact OI0 | exact FRM | lia | lia | lia
        | unfold ApPrim.V_ASN1_OCTET_STRING; lia
        | lia | lia | lia | lia | lia
        | clear - SP16; Z.div_mod_to_equations; lia
        | clear - SP16; Z.div_mod_to_equations; lia
        | split; [lia| split; [lia| split; [lia| split; [clear - SP16; Z.div_mod_to_equations; lia| unfold tlc_in; exact FDT]]]]
        | exact HPIC
        | unfold wz; replace (D + 0) with D by lia; exact FRPP
        | | | ].
      + intros e st' s' ms' bi' bc' jl' GOERR POST.
        destruct POST as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & FY & fcY & mY & OWY & errvY & boY
                          & -> & FRMY & FEY & OIY & LXY & PICY & PPCY & TLCY).
        destruct TLCY as (vb & j31 & TLCY).
        replace (ret_pc (Z_to_bv 64 1122140)) with (Z_to_bv 64 1122140) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        apply agree_of_lx_pres in LXY.
        apply (rw_cells_agree _ _ _ _ _ LXY) in OPPC;
          [| intros a Ha;
             cbn [cells_size csize Nat.add W_d2i_octet_A.xsaved W_d2i_octet_A.iframe W_d2i_octet_A.dframe_hi] in Ha;
             split; [unfold LIBW_AP; cbn [rin_ivs fst snd app]; lia| left; lia]].
        apply (rw_cells_agree _ _ _ _ _ LXY) in OCTC;
          [| intros a Ha;
             cbn [cells_size csize Nat.add W_d2i_octet_A.xsaved W_d2i_octet_A.iframe W_d2i_octet_A.dframe_hi] in Ha;
             split; [unfold LIBW_AP; cbn [rin_ivs fst snd app]; lia| left; lia]].
        apply (rw_cells_agree _ _ _ _ _ LXY) in Z4;
          [| intros a Ha;
             cbn [cells_size csize Nat.add W_d2i_octet_A.xsaved W_d2i_octet_A.iframe W_d2i_octet_A.dframe_hi] in Ha;
             split; [unfold LIBW_AP; cbn [rin_ivs fst snd app]; lia| left; lia]].
        apply (rw_cells_agree _ _ _ _ _ LXY) in J5;
          [| intros a Ha;
             cbn [cells_size csize Nat.add W_d2i_octet_A.xsaved W_d2i_octet_A.iframe W_d2i_octet_A.dframe_hi] in Ha;
             split; [unfold LIBW_AP; cbn [rin_ivs fst snd app]; lia| left; lia]].
        apply (rw_cells_agree _ _ _ _ _ LXY) in FC;
          [| intros a Ha;
             cbn [cells_size csize Nat.add W_d2i_octet_A.xsaved W_d2i_octet_A.iframe W_d2i_octet_A.dframe_hi] in Ha;
             split; [unfold LIBW_AP; cbn [rin_ivs fst snd app]; lia| left; lia]].
        apply (rw_cells_agree _ _ _ _ _ LXY) in J4;
          [| intros a Ha;
             cbn [cells_size csize Nat.add W_d2i_octet_A.xsaved W_d2i_octet_A.iframe W_d2i_octet_A.dframe_hi] in Ha;
             split; [unfold LIBW_AP; cbn [rin_ivs fst snd app]; lia| left; lia]].
        apply (rw_cells_agree _ _ _ _ _ LXY) in UT;
          [| intros a Ha;
             cbn [cells_size csize Nat.add W_d2i_octet_A.xsaved W_d2i_octet_A.iframe W_d2i_octet_A.dframe_hi] in Ha;
             split; [unfold LIBW_AP; cbn [rin_ivs fst snd app]; lia| left; lia]].
        apply (rw_cells_agree _ _ _ _ _ LXY) in J16;
          [| intros a Ha;
             cbn [cells_size csize Nat.add W_d2i_octet_A.xsaved W_d2i_octet_A.iframe W_d2i_octet_A.dframe_hi] in Ha;
             split; [unfold LIBW_AP; cbn [rin_ivs fst snd app]; lia| left; lia]].
        apply (rw_cells_agree _ _ _ _ _ LXY) in CW;
          [| intros a Ha;
             cbn [cells_size csize Nat.add W_d2i_octet_A.xsaved W_d2i_octet_A.iframe W_d2i_octet_A.dframe_hi] in Ha;
             split; [unfold LIBW_AP; cbn [rin_ivs fst snd app]; lia| left; lia]].
        apply (rw_cells_agree _ _ _ _ _ LXY) in XS;
          [| intros a Ha;
             cbn [cells_size csize Nat.add W_d2i_octet_A.xsaved W_d2i_octet_A.iframe W_d2i_octet_A.dframe_hi] in Ha;
             split; [unfold LIBW_AP; cbn [rin_ivs fst snd app]; lia| left; lia]].
        apply (rw_cells_agree _ _ _ _ _ LXY) in IFC;
          [| intros a Ha;
             cbn [cells_size csize Nat.add W_d2i_octet_A.xsaved W_d2i_octet_A.iframe W_d2i_octet_A.dframe_hi] in Ha;
             split; [unfold LIBW_AP; cbn [rin_ivs fst snd app]; lia| left; lia]].
        apply (rw_cells_agree _ _ _ _ _ LXY) in FDZ;
          [| intros a Ha;
             cbn [cells_size csize Nat.add W_d2i_octet_A.xsaved W_d2i_octet_A.iframe W_d2i_octet_A.dframe_hi] in Ha;
             split; [unfold LIBW_AP; cbn [rin_ivs fst snd app]; lia| left; lia]].
        apply (rw_cells_agree _ _ _ _ _ LXY) in DHC;
          [| intros a Ha;
             cbn [cells_size csize Nat.add W_d2i_octet_A.xsaved W_d2i_octet_A.iframe W_d2i_octet_A.dframe_hi] in Ha;
             split; [unfold LIBW_AP; cbn [rin_ivs fst snd app]; lia| left; lia]].
        apply (rw_cells_agree _ _ _ _ _ LXY) in J0;
          [| intros a Ha;
             cbn [cells_size csize Nat.add W_d2i_octet_A.xsaved W_d2i_octet_A.iframe W_d2i_octet_A.dframe_hi] in Ha;
             split; [unfold LIBW_AP; cbn [rin_ivs fst snd app]; lia| left; lia]].
        lazymatch type of PICY with
        | rw_cells _ _ _ (?c0 :: ?rest) => change (c0 :: rest) with ([c0] ++ rest) in PICY
        end.
        apply rw_cells_app in PICY. destruct PICY as [PI1 PICY].
        cbn [cells_size csize Nat.add] in PICY.
        lazymatch type of PICY with
        | rw_cells _ _ _ (?c0 :: ?rest) => change (c0 :: rest) with ([c0] ++ rest) in PICY
        end.
        apply rw_cells_app in PICY. destruct PICY as [PI2 PI3].
        cbn [cells_size csize Nat.add] in PI3.
        apply cb8_word in PI3.
        assert (PIC3 : rw_cells ctusegs mY (bv_unsigned sp + -266) [C1 bi'; C1 bc'; C8 (le_bytes_to_word jl')]).
        { change [C1 bi'; C1 bc'; C8 (le_bytes_to_word jl')] with ([C1 bi'] ++ ([C1 bc'] ++ [C8 (le_bytes_to_word jl')])).
          apply rw_cells_app. split; [exact PI1|].
          cbn [cells_size csize Nat.add].
          apply rw_cells_app. split; [exact PI2| exact PI3]. }
        eapply (dx_after_fail sp m s LB E lo B canary K d D ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F OW adr OPP OCT
                  CEIL GLOT SPB B63 SP16 PBX OPPlo OPPhi OCTlo OCThi (D2I_OCTET_STACK - 320));
          [lia| lia| exact OIY| exact FRMY| exact FEY| exact OPPC| exact OCTC| exact OCTal| exact Z4| exact PPCY| exact J5| exact FC
          | exact PIC3| exact J4| exact UT| exact J16| exact CW| exact XS| exact IFC| exact FDZ| exact TLCY| exact DHC| exact J0].
      + intros tt0 st' s' ms' bi' bc' jl' EOT GOOK TAGBAD POST.
        destruct POST as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & FY & fcY & mY & OWY & errvY & boY
                          & -> & FRMY & FEY & OIY & LXY & PICY & PPCY & TLCY).
        destruct TLCY as (vb & j31 & TLCY).
        replace (ret_pc (Z_to_bv 64 1122140)) with (Z_to_bv 64 1122140) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        apply agree_of_lx_pres in LXY.
        apply (rw_cells_agree _ _ _ _ _ LXY) in OPPC;
          [| intros a Ha;
             cbn [cells_size csize Nat.add W_d2i_octet_A.xsaved W_d2i_octet_A.iframe W_d2i_octet_A.dframe_hi] in Ha;
             split; [unfold LIBW_AP; cbn [rin_ivs fst snd app]; lia| left; lia]].
        apply (rw_cells_agree _ _ _ _ _ LXY) in OCTC;
          [| intros a Ha;
             cbn [cells_size csize Nat.add W_d2i_octet_A.xsaved W_d2i_octet_A.iframe W_d2i_octet_A.dframe_hi] in Ha;
             split; [unfold LIBW_AP; cbn [rin_ivs fst snd app]; lia| left; lia]].
        apply (rw_cells_agree _ _ _ _ _ LXY) in Z4;
          [| intros a Ha;
             cbn [cells_size csize Nat.add W_d2i_octet_A.xsaved W_d2i_octet_A.iframe W_d2i_octet_A.dframe_hi] in Ha;
             split; [unfold LIBW_AP; cbn [rin_ivs fst snd app]; lia| left; lia]].
        apply (rw_cells_agree _ _ _ _ _ LXY) in J5;
          [| intros a Ha;
             cbn [cells_size csize Nat.add W_d2i_octet_A.xsaved W_d2i_octet_A.iframe W_d2i_octet_A.dframe_hi] in Ha;
             split; [unfold LIBW_AP; cbn [rin_ivs fst snd app]; lia| left; lia]].
        apply (rw_cells_agree _ _ _ _ _ LXY) in FC;
          [| intros a Ha;
             cbn [cells_size csize Nat.add W_d2i_octet_A.xsaved W_d2i_octet_A.iframe W_d2i_octet_A.dframe_hi] in Ha;
             split; [unfold LIBW_AP; cbn [rin_ivs fst snd app]; lia| left; lia]].
        apply (rw_cells_agree _ _ _ _ _ LXY) in J4;
          [| intros a Ha;
             cbn [cells_size csize Nat.add W_d2i_octet_A.xsaved W_d2i_octet_A.iframe W_d2i_octet_A.dframe_hi] in Ha;
             split; [unfold LIBW_AP; cbn [rin_ivs fst snd app]; lia| left; lia]].
        apply (rw_cells_agree _ _ _ _ _ LXY) in UT;
          [| intros a Ha;
             cbn [cells_size csize Nat.add W_d2i_octet_A.xsaved W_d2i_octet_A.iframe W_d2i_octet_A.dframe_hi] in Ha;
             split; [unfold LIBW_AP; cbn [rin_ivs fst snd app]; lia| left; lia]].
        apply (rw_cells_agree _ _ _ _ _ LXY) in J16;
          [| intros a Ha;
             cbn [cells_size csize Nat.add W_d2i_octet_A.xsaved W_d2i_octet_A.iframe W_d2i_octet_A.dframe_hi] in Ha;
             split; [unfold LIBW_AP; cbn [rin_ivs fst snd app]; lia| left; lia]].
        apply (rw_cells_agree _ _ _ _ _ LXY) in CW;
          [| intros a Ha;
             cbn [cells_size csize Nat.add W_d2i_octet_A.xsaved W_d2i_octet_A.iframe W_d2i_octet_A.dframe_hi] in Ha;
             split; [unfold LIBW_AP; cbn [rin_ivs fst snd app]; lia| left; lia]].
        apply (rw_cells_agree _ _ _ _ _ LXY) in XS;
          [| intros a Ha;
             cbn [cells_size csize Nat.add W_d2i_octet_A.xsaved W_d2i_octet_A.iframe W_d2i_octet_A.dframe_hi] in Ha;
             split; [unfold LIBW_AP; cbn [rin_ivs fst snd app]; lia| left; lia]].
        apply (rw_cells_agree _ _ _ _ _ LXY) in IFC;
          [| intros a Ha;
             cbn [cells_size csize Nat.add W_d2i_octet_A.xsaved W_d2i_octet_A.iframe W_d2i_octet_A.dframe_hi] in Ha;
             split; [unfold LIBW_AP; cbn [rin_ivs fst snd app]; lia| left; lia]].
        apply (rw_cells_agree _ _ _ _ _ LXY) in FDZ;
          [| intros a Ha;
             cbn [cells_size csize Nat.add W_d2i_octet_A.xsaved W_d2i_octet_A.iframe W_d2i_octet_A.dframe_hi] in Ha;
             split; [unfold LIBW_AP; cbn [rin_ivs fst snd app]; lia| left; lia]].
        apply (rw_cells_agree _ _ _ _ _ LXY) in DHC;
          [| intros a Ha;
             cbn [cells_size csize Nat.add W_d2i_octet_A.xsaved W_d2i_octet_A.iframe W_d2i_octet_A.dframe_hi] in Ha;
             split; [unfold LIBW_AP; cbn [rin_ivs fst snd app]; lia| left; lia]].
        apply (rw_cells_agree _ _ _ _ _ LXY) in J0;
          [| intros a Ha;
             cbn [cells_size csize Nat.add W_d2i_octet_A.xsaved W_d2i_octet_A.iframe W_d2i_octet_A.dframe_hi] in Ha;
             split; [unfold LIBW_AP; cbn [rin_ivs fst snd app]; lia| left; lia]].
        lazymatch type of PICY with
        | rw_cells _ _ _ (?c0 :: ?rest) => change (c0 :: rest) with ([c0] ++ rest) in PICY
        end.
        apply rw_cells_app in PICY. destruct PICY as [PI1 PICY].
        cbn [cells_size csize Nat.add] in PICY.
        lazymatch type of PICY with
        | rw_cells _ _ _ (?c0 :: ?rest) => change (c0 :: rest) with ([c0] ++ rest) in PICY
        end.
        apply rw_cells_app in PICY. destruct PICY as [PI2 PI3].
        cbn [cells_size csize Nat.add] in PI3.
        apply cb8_word in PI3.
        assert (PIC3 : rw_cells ctusegs mY (bv_unsigned sp + -266) [C1 bi'; C1 bc'; C8 (le_bytes_to_word jl')]).
        { change [C1 bi'; C1 bc'; C8 (le_bytes_to_word jl')] with ([C1 bi'] ++ ([C1 bc'] ++ [C8 (le_bytes_to_word jl')])).
          apply rw_cells_app. split; [exact PI1|].
          cbn [cells_size csize Nat.add].
          apply rw_cells_app. split; [exact PI2| exact PI3]. }
        eapply (dx_after_fail sp m s LB E lo B canary K d D ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F OW adr OPP OCT
                  CEIL GLOT SPB B63 SP16 PBX OPPlo OPPhi OCTlo OCThi (D2I_OCTET_STACK - 320));
          [lia| lia| exact OIY| exact FRMY| exact FEY| exact OPPC| exact OCTC| exact OCTal| exact Z4| exact PPCY| exact J5| exact FC
          | exact PIC3| exact J4| exact UT| exact J16| exact CW| exact XS| exact IFC| exact FDZ| exact TLCY| exact DHC| exact J0].
      + intros st' s' ms' GOOK TAGOK POST.
        destruct TAGOK as [TAGE CLSE].
        destruct POST as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & FY & fcY & mY & OWY & errvY & boY
                          & -> & FRMY & FEY & OIY & LXY & PICY & PPCY & TLCY).
        destruct TLCY as (vb & j31 & TLCY).
        replace (ret_pc (Z_to_bv 64 1122140)) with (Z_to_bv 64 1122140) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        apply agree_of_lx_pres in LXY.
        apply (rw_cells_agree _ _ _ _ _ LXY) in OPPC;
          [| intros a Ha;
             cbn [cells_size csize Nat.add W_d2i_octet_A.xsaved W_d2i_octet_A.iframe W_d2i_octet_A.dframe_hi] in Ha;
             split; [unfold LIBW_AP; cbn [rin_ivs fst snd app]; lia| left; lia]].
        apply (rw_cells_agree _ _ _ _ _ LXY) in OCTC;
          [| intros a Ha;
             cbn [cells_size csize Nat.add W_d2i_octet_A.xsaved W_d2i_octet_A.iframe W_d2i_octet_A.dframe_hi] in Ha;
             split; [unfold LIBW_AP; cbn [rin_ivs fst snd app]; lia| left; lia]].
        apply (rw_cells_agree _ _ _ _ _ LXY) in Z4;
          [| intros a Ha;
             cbn [cells_size csize Nat.add W_d2i_octet_A.xsaved W_d2i_octet_A.iframe W_d2i_octet_A.dframe_hi] in Ha;
             split; [unfold LIBW_AP; cbn [rin_ivs fst snd app]; lia| left; lia]].
        apply (rw_cells_agree _ _ _ _ _ LXY) in J5;
          [| intros a Ha;
             cbn [cells_size csize Nat.add W_d2i_octet_A.xsaved W_d2i_octet_A.iframe W_d2i_octet_A.dframe_hi] in Ha;
             split; [unfold LIBW_AP; cbn [rin_ivs fst snd app]; lia| left; lia]].
        apply (rw_cells_agree _ _ _ _ _ LXY) in FC;
          [| intros a Ha;
             cbn [cells_size csize Nat.add W_d2i_octet_A.xsaved W_d2i_octet_A.iframe W_d2i_octet_A.dframe_hi] in Ha;
             split; [unfold LIBW_AP; cbn [rin_ivs fst snd app]; lia| left; lia]].
        apply (rw_cells_agree _ _ _ _ _ LXY) in J4;
          [| intros a Ha;
             cbn [cells_size csize Nat.add W_d2i_octet_A.xsaved W_d2i_octet_A.iframe W_d2i_octet_A.dframe_hi] in Ha;
             split; [unfold LIBW_AP; cbn [rin_ivs fst snd app]; lia| left; lia]].
        apply (rw_cells_agree _ _ _ _ _ LXY) in UT;
          [| intros a Ha;
             cbn [cells_size csize Nat.add W_d2i_octet_A.xsaved W_d2i_octet_A.iframe W_d2i_octet_A.dframe_hi] in Ha;
             split; [unfold LIBW_AP; cbn [rin_ivs fst snd app]; lia| left; lia]].
        apply (rw_cells_agree _ _ _ _ _ LXY) in J16;
          [| intros a Ha;
             cbn [cells_size csize Nat.add W_d2i_octet_A.xsaved W_d2i_octet_A.iframe W_d2i_octet_A.dframe_hi] in Ha;
             split; [unfold LIBW_AP; cbn [rin_ivs fst snd app]; lia| left; lia]].
        apply (rw_cells_agree _ _ _ _ _ LXY) in CW;
          [| intros a Ha;
             cbn [cells_size csize Nat.add W_d2i_octet_A.xsaved W_d2i_octet_A.iframe W_d2i_octet_A.dframe_hi] in Ha;
             split; [unfold LIBW_AP; cbn [rin_ivs fst snd app]; lia| left; lia]].
        apply (rw_cells_agree _ _ _ _ _ LXY) in XS;
          [| intros a Ha;
             cbn [cells_size csize Nat.add W_d2i_octet_A.xsaved W_d2i_octet_A.iframe W_d2i_octet_A.dframe_hi] in Ha;
             split; [unfold LIBW_AP; cbn [rin_ivs fst snd app]; lia| left; lia]].
        apply (rw_cells_agree _ _ _ _ _ LXY) in IFC;
          [| intros a Ha;
             cbn [cells_size csize Nat.add W_d2i_octet_A.xsaved W_d2i_octet_A.iframe W_d2i_octet_A.dframe_hi] in Ha;
             split; [unfold LIBW_AP; cbn [rin_ivs fst snd app]; lia| left; lia]].
        apply (rw_cells_agree _ _ _ _ _ LXY) in FDZ;
          [| intros a Ha;
             cbn [cells_size csize Nat.add W_d2i_octet_A.xsaved W_d2i_octet_A.iframe W_d2i_octet_A.dframe_hi] in Ha;
             split; [unfold LIBW_AP; cbn [rin_ivs fst snd app]; lia| left; lia]].
        apply (rw_cells_agree _ _ _ _ _ LXY) in DHC;
          [| intros a Ha;
             cbn [cells_size csize Nat.add W_d2i_octet_A.xsaved W_d2i_octet_A.iframe W_d2i_octet_A.dframe_hi] in Ha;
             split; [unfold LIBW_AP; cbn [rin_ivs fst snd app]; lia| left; lia]].
        apply (rw_cells_agree _ _ _ _ _ LXY) in J0;
          [| intros a Ha;
             cbn [cells_size csize Nat.add W_d2i_octet_A.xsaved W_d2i_octet_A.iframe W_d2i_octet_A.dframe_hi] in Ha;
             split; [unfold LIBW_AP; cbn [rin_ivs fst snd app]; lia| left; lia]].
        destruct (Z.eqb_spec (Z.land (go_ret (get_object d 0 (zlength d))) 32) 0) as [CST|CST]; cbn [negb]; cbv iota.
        * assert (RET0 : go_ret (get_object d 0 (zlength d)) = 0).
          { destruct (go_ret_ok d 0 (zlength d) GOOK) as [R0|[R0|R0]]; [exact R0| exfalso; rewrite R0 in CST; cbv in CST; lia
            | exfalso; rewrite R0 in CST; cbv in CST; lia]. }
          rewrite RET0. change (Z.testbit 0 0) with false. cbv iota.
          eapply (dx_prim HM sp m s LB E lo B canary K d D ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F OW adr OPP OCT
                    DF CEIL GLOT SPB B63 SP16 PBX D1 D63 D30 OPPlo OPPhi OCTlo OCThi DJXP (D2I_OCTET_STACK - 320));
            [exact GOOK| exact TAGE| exact CLSE| exact CST| lia| lia| lia| exact OIY| exact FRMY| exact FEY| exact OPPC| exact OCTC
            | exact Z4| exact PPCY| exact J5| exact FC| exact PICY| exact J4| exact UT| exact J16| exact CW| exact XS| exact IFC
            | exact FDZ| exact TLCY| exact DHC| exact J0| exact OCTal].
        * eapply (dx_cons HM HF HGO sp m s LB E lo B canary K d D ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F OW adr OPP OCT
                    DF CEIL GLOT SPB B63 SP16 PBX D1 D63 D30 OPPlo OPPhi OCTlo OCThi DJXP (D2I_OCTET_STACK - 320));
            [exact GOOK| exact TAGE| exact CLSE| exact CST| lia| lia| lia| exact OIY| exact FRMY| exact FEY| exact OPPC| exact OCTC
            | exact Z4| exact PPCY| exact J5| exact FC| exact PICY| exact J4| exact UT| exact J16| exact CW| exact XS| exact IFC
            | exact FDZ| exact TLCY| exact DHC| exact J0| exact OCTal].
  Qed.
End Proofs.
End WithCeiling0.
