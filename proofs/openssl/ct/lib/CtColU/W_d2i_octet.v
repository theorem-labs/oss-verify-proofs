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
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Layout Lib_iface Lib_kit Startup_B Printf_lib.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtBnU Require Import BnKit BnHeap BnRep W_crypto.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXU Require Import HxpInit HxpFacts.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApCells ApRepDefs ApRep ApWalkTac ApErrKit ApErrKit2 ApErrKit3 ApIface W_err_new W_err_set_debug W_err_set_error W_c2i_int W_get_object W_get_object_walk W_check_tlen W_prefix_create W_asn1_string W_item_d2i_stmt W_item_d2i_img W_item_d2i_front W_item_d2i_tail.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUbTab ApUTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnBoth Require Import UbKit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtParseU Require Import PzDefs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtEncU Require Import W_asn1_enc_leaves.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctU Require Import SctStmt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtColU Require Import ColKit ColDefs W_bufmem W_check_tlen_gen W_collect W_d2i_octet_A W_d2i_octet_B W_d2i_octet_C W_d2i_octet_D.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope am_scope.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].
Local Ltac ubchk_strong := OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep;
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
      | 1%Z => OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep
      | 2%Z => first [ (OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep; udecide) | ubchk_strong | uchk ]
      end
  end.
Local Ltac step := try udecide; repeat ub1c; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.
Local Ltac zstep := try udecide; repeat ub1c; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
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
  intros m a j H. pose proof H as [[W _] _]. cbn in W. destruct W as [L _].
  eapply rw_cells_recast; [exact H| cbn; auto| | reflexivity]. cbn [cells_bytes cbytes app]. rewrite (le8_of_bytes' j L). rewrite ?app_nil_r. reflexivity.
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
  Proof using B63 CEIL GLO OCThi OCTlo OPPhi OPPlo PBX SP16 SPB.
    intros until jd. intros LO STK0 OI STA FRMA FEA HOPP HOCT OCT8 FI FDL FDH.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    assert (OFS0 : -320 <= 0) by lia. assert (OFS16 : (-320) mod 16 = 0) by reflexivity.
    pose proof (oinv_call sp m s LB E lo B canary K d D XPO (-320) STK3 GLO LO STK0 OFS0 SPB B63 _ _ _ _ _ _ _ OI) as (_ & _ & _ & _ & _ & _ & ERRA & MIA & _ & ASA).
    unfold LX_ERRNO, RATP in ERRA. change (3355176 - 164) with 3355012 in ERRA.
    pose proof ASA as (_ & IMG & _).
    pose proof (item_cells_octet mA IMG) as (IT0 & IT8 & IT8L & IT16 & IT32). unfold ITEM_OCTET in IT0, IT8, IT8L, IT16, IT32.
    unfold W_d2i_octet_A.xsaved, W_d2i_octet_A.iframe, W_d2i_octet_A.dframe_hi, RA_INTERN, RA_D2IEX, ITEM_OCTET, MallocRep.wz in *.
    pose proof (munch_refl [(SP - 320, SP)]%Z mA) as MU. pose proof (wmono_refl ctusegs mA) as WM.
    rename MIA into MI.
    (* [comment removed for export] *)
    step. step. if_false. step. step. step.
    carve_frame 16%nat STA. do 8 step. release_frame FR STA (SP + -128). step.
    assert (ESP3 : bv_unsigned (Z_to_bv 64 (SP + -128)) = SP + -128) by (apply unsigned_lit; lia).
    name_mem m3. match goal with H : mem_inv ctusegs m3 |- _ => rename H into MI3 end.
    eapply embed_free_null with (lo := lo) (PVAL := OCT) (IT := 2960328) (w := 4);
      [rewrite ?ESP3; exact STA| exact MI3| lia| rewrite ?ESP3; lia| rewrite ?ESP3; lia| rewrite ?ESP3; lia| lia| exact OCT8| exact HOCT| lia| lia| reflexivity
      | exact IT0| exact IT8| exact IT16| exact IT32| lia| lia|].
    intros t0'' t1'' a0'' a1'' a2'' a3'' m4 MU4 WM4 MI4 ST4. rewrite ?ESP3 in *.
    xport FI MU4 WM4. xport FDL MU4 WM4. xport FDH MU4 WM4. xport HOPP MU4 WM4. xport HOCT MU4 WM4. xport ERRA MU4 WM4.
    assert (MU' : munch [(SP - 320, SP)]%Z mA m4).
    { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU4]. intros x; cbn; lia. }
    pose proof (wmono_trans _ _ _ _ WM WM4) as WM'. clear MU WM MU4 WM4 MI3 IT0 IT8 IT8L IT16 IT32. rename MU' into MU. rename WM' into WM.
    replace (ret_pc (Z_to_bv 64 1117848)) with (Z_to_bv 64 1117848) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    step. step. do 5 step. step. release_frame FI ST4 (SP + -64). step.
    replace (ret_pc (Z_to_bv 64 1118008)) with (Z_to_bv 64 1118008) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    step. if_true. step. step. step. step. step.
    release_frame FDL ST4 (SP + -24). release_frame FDH ST4 (bv_unsigned sp). step.
    name_mem m5. match goal with H : mem_inv ctusegs m5 |- _ => rename H into MI5 end.
    apply evt_done.
    eapply (dx_fin_none sp m s LB E lo B canary K d D ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F OW adr OPP OCT SPB SP16 (-320) STK3);
      [exact LO| exact OFS0| exact STK0| | exact ST4| exact FRMA| exact FEA| exact HOPP| exact HOCT].
    eapply (oinv_munch sp m s LB E lo B canary K d D XPO (-320) STK3 CEIL GLO LO STK0 OFS0 SPB B63 SP16 OFS16 XPokK PBX); [exact OI| exact MU| exact WM| exact MI5| | exact ERRA|].
    - destruct (stk_carve ctusegs m5 lo (bv_unsigned sp) 320 ST4 ltac:(lia)) as [ST5 _]. replace (bv_unsigned sp - Z.of_nat 320) with (bv_unsigned sp + -320) in ST5 by lia. exact ST5.
    - constructor; [left; cbn; lia| constructor].
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
  Proof using B63 CEIL GLO HF HM OCThi OCTlo OPPhi OPPlo PBX SP16 SPB.
    intros until j0. intros LO STKG OI FRMA FEA HOPP HOCT OCT8 FBUF FPP FJ5 FFC FPIC FJ4 FUT FJ16 FCW FSV FI FD0 FTLC FDH FJ0.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    unfold ERR_SET_ERROR_STACK in STKG.
    assert (STK0 : 0 <= STK) by lia. assert (OFS0 : -320 <= 0) by lia. assert (OFS16 : (-320) mod 16 = 0) by reflexivity.
    pose proof (oinv_call sp m s LB E lo B canary K d D XPO (-320) STK GLO LO STK0 OFS0 SPB B63 _ _ _ _ _ _ _ OI) as (_ & _ & _ & STA & _ & _ & ERRA & MIA & _).
    unfold LX_ERRNO, RATP in ERRA. change (3355176 - 164) with 3355012 in ERRA.
    unfold W_d2i_octet_A.xsaved, W_d2i_octet_A.iframe, W_d2i_octet_A.dframe_hi, EXPRIM_AFTER_TLEN, RA_INTERN, RA_D2IEX, ITEM_OCTET, MallocRep.wz in *.
    pose proof (munch_refl (@nil (Z * Z)) mA) as MU. pose proof (wmono_refl ctusegs mA) as WM.
    rename MIA into MI.
    unfold implM. iprefix.
    (* [comment removed for export] *)
    step. step. if_false. step. if_false.
    ihere. to_implM. eapply implM_abind.
    { eapply (dx_raise HM HF sp m s LB E lo B canary K d D gp OPP OCT CEIL GLO SPB B63 PBX OPPlo OPPhi OCTlo OCThi) with (OFS' := -320) (STK' := STK);
        [right; repeat split; reflexivity| exact LO| exact OFS0| exact OFS16| unfold ERR_SET_ERROR_STACK; lia| exact OI| exact FRMA]. }
    intros r sB msB POB. unfold dx_raise_post in POB.
    destruct POB as (o0 & o1 & o2 & n0 & n1 & n2 & n3 & n4 & n5 & n6 & n7 & o3 & o4 & o5 & o6 & F2 & fc2 & mB & OW2 & errv2 & bo2 & -> & FRM2 & FE2 & OIb & LXb).
    destruct r as [u stB]. cbn [fst snd] in *.
    (* [comment removed for export] *)
    pose proof (agree_of_lx_pres _ _ _ _ _ LXb) as AGb. cbn [app] in AGb.
    assert (CL : forall a, ((SP + -320 <= a < SP) \/ (OPP <= a < OPP + 8) \/ (OCT <= a < OCT + 8)) -> lx_client LB (SP + -320) LIBW_AP a).
    { intros a Ha. split; [unfold LIBW_AP; cbn [rin_ivs fst snd app]; lia| left; lia]. }
    apply (rw_cells_agree _ _ _ _ _ AGb) in FBUF; [| intros a Ha; apply CL; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ AGb) in FPP; [| intros a Ha; apply CL; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ AGb) in FJ5; [| intros a Ha; apply CL; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ AGb) in FFC; [| intros a Ha; apply CL; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ AGb) in FPIC; [| intros a Ha; apply CL; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ AGb) in FJ4; [| intros a Ha; apply CL; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ AGb) in FUT; [| intros a Ha; apply CL; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ AGb) in FJ16; [| intros a Ha; apply CL; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ AGb) in FCW; [| intros a Ha; apply CL; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ AGb) in FSV; [| intros a Ha; apply CL; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ AGb) in FI; [| intros a Ha; apply CL; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ AGb) in FD0; [| intros a Ha; apply CL; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ AGb) in FTLC; [| intros a Ha; apply CL; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ AGb) in FDH; [| intros a Ha; apply CL; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ AGb) in HOPP; [| intros a Ha; apply CL; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ AGb) in HOCT; [| intros a Ha; apply CL; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ AGb) in FJ0; [| intros a Ha; apply CL; cbn in Ha; lia].
    pose proof (oinv_call sp m s LB E lo B canary K d D XPO (-320) STK GLO LO STK0 OFS0 SPB B63 _ _ _ _ _ _ _ OIb) as (_ & _ & _ & STb & _ & _ & ERRb & MIb & _).
    unfold LX_ERRNO, RATP in ERRb. change (3355176 - 164) with 3355012 in ERRb.
    clear MU WM AGb CL. pose proof (munch_refl (@nil (Z * Z)) mB) as MU. pose proof (wmono_refl ctusegs mB) as WM.
    apply implM_ret. step.
    destruct (fb_pack sp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FBUF FPP FJ5 FFC FPIC FJ4 FUT FJ16 FCW FJ0) as (jb & jm & FB).
    destruct (fb_blob sp _ _ _ _ _ _ FB) as [jlo FLO].
    destruct (fd_pack sp _ _ _ _ FD0 FTLC) as (jd & FD).
    eapply (dx_fail_tail sp m s LB E lo B canary K d D ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F OW adr OPP OCT CEIL GLO SPB B63 SP16 PBX OPPlo OPPhi OCTlo OCThi STK);
      [exact LO| exact STK0| | exact FRM2| intros k Hk; rewrite (FE2 k Hk); exact (FEA k Hk)| exact HOPP| exact HOCT| exact OCT8| exact FLO| exact FSV| exact FI| exact FD| exact FDH].
    eapply (oinv_munch sp m s LB E lo B canary K d D XPO (-320) STK CEIL GLO LO STK0 OFS0 SPB B63 SP16 OFS16 XPokK PBX); [exact OIb| exact MU| exact WM| exact MIb| exact STb| exact ERRb| constructor].
  Qed.

  End Act.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem d2i_octet_walk : d2i_octet_spec.
  Proof using HF HGO HM.
    unfold d2i_octet_spec. intros until OCT. intros PRE TP FRM KOW KIDS PAY ADR OPPlo OPPhi HOPP OPP8 OCTlo OCThi HOCT OCT8 DJXP -> -> ->.
    pose proof PRE as (HEAP & AS & IDS & DC & AUX & SPB & B63 & ST & CEIL & GLO & LO & ERR & SSP & MI & SP16).
    pose proof PAY as (HB & DF & D1 & D63 & D30 & HBLK).
    assert (PBX : d = [] \/ exists pb PA psz, In (pb, PA, psz) LB /\ PA <= D /\ D + zlength d <= PA + psz).
    { destruct HBLK as [E0|([[pb PA] psz] & H1 & H2 & H3)]; [left; exact E0| right]. exists pb, PA, psz. cbn [blk_addr blk_size fst snd] in H2, H3. auto. }
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    assert (EA : errno_addr (Z_to_bv 64 RATP) = 3355012) by (unfold errno_addr, RATP; rewrite unsigned_lit by lia; reflexivity).
    unfold MallocRep.wz in ERR. rewrite EA in ERR.
    assert (DLEN : Z.of_nat (length (to_bytes d)) = zlength d) by apply zlength_to_bytes.
    pose proof d2i_octet_stack_ok as STKOK. pose proof cons_stk_facts as (STKP & STKW & STKF).
    unfold W_d2i_octet_B.PRIM_STK, ASN1_STRING_TYPE_NEW_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RMALLOC_STACK in STKP.
    set (STK := D2I_OCTET_STACK - 320) in *.
    assert (STKC : CONS_STK <= STK) by lia.
    unfold D2I_OCTET_STACK, GETOBJ_STACK, ERR_SET_ERROR_STACK in STK. unfold GLOBALS_TOP in GLO.
    assert (LO' : lo <= bv_unsigned sp + -320 - STK) by (subst STK; unfold D2I_OCTET_STACK, GETOBJ_STACK, ERR_SET_ERROR_STACK in LO; lia).
    assert (STK0 : 0 <= STK) by (subst STK; lia). assert (OFS0 : -320 <= 0) by lia. assert (OFS16 : (-320) mod 16 = 0) by reflexivity.
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -320)) = bv_unsigned sp + -320) by (apply unsigned_lit; lia).
    pose proof (oinv_entry sp m s LB E lo B canary K d D (XPO OPP OCT) (-320) STK CEIL GLO LO' STK0 OFS0 SPB B63 SP16 OFS16 st OW bo errv) as OI0.
    specialize (OI0 ltac:(subst STK; replace (- -320 + (D2I_OCTET_STACK - 320)) with D2I_OCTET_STACK by lia; exact PRE) KOW KIDS HB).
    pose proof AS as (_ & IMG & _).
    pose proof (item_cells_octet m IMG) as (IT0 & IT8 & IT8L & IT16 & IT32). unfold ITEM_OCTET in IT0, IT8, IT8L, IT16, IT32.
    change (2960328 + 8) with 2960336 in IT8. change (2960328 + 8) with 2960336 in IT8L. change (2960328 + 16) with 2960344 in IT16. change (2960328 + 32) with 2960360 in IT32.
    unfold MallocRep.wz in HOPP, HOCT. unfold D2I_ASN1_OCTET_STRING, MallocRep.wz. subst tp.
    pose proof (munch_refl [(bv_unsigned sp - 320, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
    unfold implM. iprefix.
    (* [comment removed for export] *)
    carve_frame 16%nat ST. do 9 step. release_frame FR ST (bv_unsigned sp). step.
    carve_frame 16%nat ST. do 9 step. release_frame FR ST (bv_unsigned sp). step.
    (* [comment removed for export] *)
    carve_frame 64%nat ST. do 9 step.
    step. if_cases K0; zc K0; [exfalso; lia|]. clear K0. step. do 7 step.
    (* [comment removed for export] *)
    carve_frame 64%nat ST. do 7 step.
    step. if_cases K0; zc K0; [exfalso; lia|]. clear K0. step. step. if_cases K1; zc K1; [exfalso; lia|]. clear K1.
    do 5 step. step.
    (* [comment removed for export] *)
    name_mem mA. pose proof (munch_refl [(bv_unsigned sp - 304, bv_unsigned sp - 128)]%Z mA) as MUp. pose proof (wmono_refl ctusegs mA) as WMp.
    repeat match goal with H : rw_cells ctusegs mA _ _ |- _ => let T := type of H in change (frozen T) in H
                          | H : ro_cells ctusegs mA _ _ |- _ => let T := type of H in change (frozen T) in H
                          | H : bytes_at ctusegs mA _ _ |- _ => let T := type of H in change (frozen T) in H end.
    carve_frame 176%nat ST. do 15 step.
    name_mem mB. unfold frozen in *.
    transport_after_call ctusegs mA mB MUp WMp. clear MUp WMp.
    step. step. step. step. step. step.
    step. if_cases K2; zc K2; [exfalso; lia|]. clear K2. step. step. if_cases K3; zc K3; [exfalso; lia|]. clear K3.
    (* [comment removed for export] *)
    lazymatch type of FR with rw_cells _ _ _ (?c0 :: ?c1 :: CB 31 ?j :: ?rest) => change (c0 :: c1 :: CB 31 j :: rest) with ([c0] ++ (c1 :: [CB 31 j]) ++ rest) in FR end.
    apply rw_cells_app in FR. destruct FR as [FD0 FR]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FR.
    apply rw_cells_app in FR. destruct FR as [FDT FDH]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FDH.
    replace (bv_unsigned sp + -64 + 8) with (bv_unsigned sp + -56) in FDT by lia.
    replace (bv_unsigned sp + -64 + 8 + 32) with (bv_unsigned sp + -24) in FDH by lia.
    lazymatch type of FDT with rw_cells _ ?mx _ [_; CB 31 ?j] => change (rw_cells ctusegs mx (bv_unsigned sp + -56) (tlc_in j)) in FDT end.
    rename FR0 into FI.
    step.
    unfold d2i_octet.
    destruct (Z_le_gt_dec (zlength d) 0) as [LE0|GT0].
    - (* [comment removed for export] *)
      replace (zlength d <=? 0) with true by (symmetry; apply Z.leb_le; exact LE0).
      step. if_cases KL; zc KL; [| exfalso; lia]. clear KL.
      name_mem m1.
      match goal with H : stk ctusegs m1 lo _ |- _ => rename H into ST1 end. match goal with H : mem_inv ctusegs m1 |- _ => rename H into MI1 end.
      match goal with H : rw_cells ctusegs m1 3355012 _ |- _ => rename H into ERR1 end.
      destruct (stk_carve ctusegs m1 lo (bv_unsigned sp + -304) 16 ST1 ltac:(lia)) as [ST320 _].
      replace (bv_unsigned sp + -304 - Z.of_nat 16) with (bv_unsigned sp + -320) in ST320 by lia.
      assert (OI1 : oinv sp m s LB E lo B canary K d D (XPO OPP OCT) (-304) (STK + 16) s st m1 OW errv bo []).
      { eapply (oinv_reframe sp m s LB E lo B canary K d D (XPO OPP OCT) (-320) STK (-304) (STK + 16)); [| exact SPB| exact SP16| exact ST1| lia| lia| lia| reflexivity].
        eapply (oinv_munch sp m s LB E lo B canary K d D (XPO OPP OCT) (-320) STK CEIL GLO LO' STK0 OFS0 SPB B63 SP16 OFS16 (XPok sp B OPP OCT OPPlo OPPhi OCTlo OCThi) PBX);
          [exact OI0| exact MU| exact WM| exact MI1| exact ST320| exact ERR1|]. constructor; [left; cbn; lia| constructor]. }
      ihere. to_implM. eapply implM_abind.
      { replace (Z_to_bv 64 (bv_unsigned sp + -304)) with (Z_to_bv 64 (bv_unsigned sp + (-304))) by (f_equal; lia).
        eapply (dx_raise HM HF sp m s LB E lo B canary K d D gp OPP OCT CEIL GLO SPB B63 PBX OPPlo OPPhi OCTlo OCThi) with (OFS' := -304) (STK' := STK + 16);
          [left; repeat split; reflexivity| lia| lia| reflexivity| unfold ERR_SET_ERROR_STACK; lia| exact OI1| exact FRM]. }
      intros r sB msB POB. unfold dx_raise_post in POB.
      destruct POB as (o0 & o1 & o2 & n0 & n1 & n2 & n3 & n4 & n5 & n6 & n7 & o3 & o4 & o5 & o6 & F2 & fc2 & mR & OW2 & errv2 & bo2 & -> & FRM2 & FE2 & OIb & LXb).
      replace (bv_unsigned sp + (-304)) with (bv_unsigned sp + -304) in LXb |- * by lia.
      destruct r as [u stB]. cbn [fst snd] in *.
      pose proof (agree_of_lx_pres _ _ _ _ _ LXb) as AGb. cbn [app] in AGb.
      assert (CL : forall a, ((bv_unsigned sp + -304 <= a < bv_unsigned sp) \/ (OPP <= a < OPP + 8) \/ (OCT <= a < OCT + 8)) -> lx_client LB (bv_unsigned sp + -304) LIBW_AP a).
      { intros a Ha. split; [unfold LIBW_AP; cbn [rin_ivs fst snd app]; lia| left; lia]. }
      apply (rw_cells_agree _ _ _ _ _ AGb) in FR1; [| intros a Ha; apply CL; cbn in Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ AGb) in FI; [| intros a Ha; apply CL; cbn in Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ AGb) in FD0; [| intros a Ha; apply CL; cbn in Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ AGb) in FDT; [| intros a Ha; apply CL; unfold tlc_in in Ha; cbn in Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ AGb) in FDH; [| intros a Ha; apply CL; cbn in Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ AGb) in HOPP; [| intros a Ha; apply CL; cbn in Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ AGb) in HOCT; [| intros a Ha; apply CL; cbn in Ha; lia].
      pose proof (oinv_call sp m s LB E lo B canary K d D (XPO OPP OCT) (-304) (STK + 16) GLO ltac:(lia) ltac:(lia) ltac:(lia) SPB B63 _ _ _ _ _ _ _ OIb) as (_ & _ & _ & STb & _ & _ & ERRb & MIb & _).
      unfold LX_ERRNO, RATP in ERRb. change (3355176 - 164) with 3355012 in ERRb.
      clear MU WM AGb CL. pose proof (munch_refl (@nil (Z * Z)) mR) as MU. pose proof (wmono_refl ctusegs mR) as WM.
      apply implM_ret.
      (* [comment removed for export] *)
      step. do 13 step. step. release_frame FR1 STb (bv_unsigned sp + -128). step.
      unfold tlc_in in FDT. destruct (fd_pack sp _ _ _ _ FD0 FDT) as (jd & FD).
      replace (ret_pc (Z_to_bv 64 1117828)) with (Z_to_bv 64 1117828) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      eapply (dx_intern_fail sp m s LB E lo B canary K d D ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F OW adr OPP OCT CEIL GLO SPB B63 SP16 PBX OPPlo OPPhi OCTlo OCThi STK);
        [exact LO'| exact STK0| | exact STb| exact FRM2| exact FE2| exact HOPP| exact HOCT| exact OCT8| exact FI| exact FD| exact FDH].
      eapply (oinv_reframe sp m s LB E lo B canary K d D (XPO OPP OCT) (-304) (STK + 16) (-320) STK); [| exact SPB| exact SP16| | lia| lia| lia| reflexivity].
      + eapply (oinv_munch sp m s LB E lo B canary K d D (XPO OPP OCT) (-304) (STK + 16) CEIL GLO ltac:(lia) ltac:(lia) ltac:(lia) SPB B63 SP16 ltac:(reflexivity) (XPok sp B OPP OCT OPPlo OPPhi OCTlo OCThi) PBX);
          [exact OIb| exact MU| exact WM| exact MIb| | exact ERRb| constructor].
        destruct (stk_carve ctusegs mR lo (bv_unsigned sp + -128) 176 STb ltac:(lia)) as [STc _]. replace (bv_unsigned sp + -128 - Z.of_nat 176) with (bv_unsigned sp + -304) in STc by lia. exact STc.
      + destruct (stk_carve ctusegs mR lo (bv_unsigned sp + -128) 192 STb ltac:(lia)) as [STc _]. replace (bv_unsigned sp + -128 - Z.of_nat 192) with (bv_unsigned sp + -320) in STc by lia. exact STc.
    - (* [comment removed for export] *)
      replace (zlength d <=? 0) with false by (symmetry; apply Z.leb_gt; lia).
      step. if_cases K4; zc K4; [exfalso; lia|].
      Ltac at_pc p := lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?q) _ _ _ _) => constr_eq q p end.
      Ltac step_to p := first [ at_pc p | (try change (zxb (Z_to_bv 8 0)) with (Z_to_bv 64 0); step; step_to p) ].
      step_to 1118520. try change (zxb (Z_to_bv 8 0)) with (Z_to_bv 64 0).
      match goal with H : mem_inv ctusegs ?mx |- evt _ _ (MS _ _ _ _ _ ?mx _) => pose proof (jt_embed_d2i mx H) as JT1 end.
      step. clear JT1. try rewrite (sx32_small 851044) by lia. step. setreg 12 (Z_to_bv 64 1118712) ltac:(reflexivity). step. step.
      step. step. if_true. do 7 step. do 13 step. step. release_frame FR1 ST (bv_unsigned sp + -128). step.
      (* [comment removed for export] *)
      name_mem mC. pose proof (munch_refl [(bv_unsigned sp - 320, bv_unsigned sp - 128)]%Z mC) as MUp. pose proof (wmono_refl ctusegs mC) as WMp.
      repeat match goal with H : rw_cells ctusegs mC _ _ |- _ => let T := type of H in change (frozen T) in H
                            | H : ro_cells ctusegs mC _ _ |- _ => let T := type of H in change (frozen T) in H
                            | H : bytes_at ctusegs mC _ _ |- _ => let T := type of H in change (frozen T) in H end.
      carve_frame 192%nat ST. do 15 step. do 8 step.
      name_mem mD. unfold frozen in *.
      transport_after_call ctusegs mC mD MUp WMp. clear MUp WMp.
      step. step. change (zxb (Z_to_bv 8 0)) with (Z_to_bv 64 0). step. step. step. step. step. if_true.
      step. rewrite (sx32_small 4) by lia. step. step. step. if_true.
      OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. ub_sw; ub_lts. if_cases KP0; zify_cond KP0; [exfalso; rewrite ?unsigned_lit in KP0 by lia; lia|]. clear KP0.
      OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. ub_sw; ub_lts. if_cases KP7; zify_cond KP7;
        [exfalso; rewrite ?unsigned_lit in KP7 by lia; change 7 with (Z.ones 3) in KP7; rewrite Z.land_ones in KP7 by lia; clear - KP7 OPP8; Z.div_mod_to_equations; lia|]. clear KP7.
      step. step. step. step. if_false.
      step. try rewrite (sx32_small 4) by lia. step. step. step. step. step. step. step. step. step. step. step. step. step. step. step.
      name_mem m2.
      match goal with H : stk ctusegs m2 lo _ |- _ => rename H into ST2 end. match goal with H : mem_inv ctusegs m2 |- _ => rename H into MI2 end.
      match goal with H : rw_cells ctusegs m2 3355012 _ |- _ => rename H into ERR2 end.
      (* [comment removed for export] *)
      lazymatch type of FR with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: CB 14 ?j :: ?c9 :: CB 24 ?j' :: ?rest) =>
        change (rw_cells ctusegs m2 (bv_unsigned sp + -320) ([c0] ++ [c1; c2; c3; c4] ++ [c5] ++ [c6] ++ [c7] ++ [CB 14 j] ++ [c9] ++ [CB 24 j'] ++ rest)) in FR end.
      apply rw_cells_app in FR. destruct FR as [FJ0 FR]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FR.
      apply rw_cells_app in FR. destruct FR as [FBUF FR]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FR.
      apply rw_cells_app in FR. destruct FR as [FPP FR]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FR.
      apply rw_cells_app in FR. destruct FR as [FJ5 FR]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FR.
      apply rw_cells_app in FR. destruct FR as [FFC FR]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FR.
      apply rw_cells_app in FR. destruct FR as [FX14 FR]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FR.
      apply rw_cells_app in FR. destruct FR as [FUT FR]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FR.
      apply rw_cells_app in FR. destruct FR as [FX24 FSV]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FSV.
      replace (bv_unsigned sp + -320 + 8) with (bv_unsigned sp + -312) in FBUF by lia.
      replace (bv_unsigned sp + -320 + 8 + 32) with (bv_unsigned sp + -280) in FPP by lia.
      replace (bv_unsigned sp + -320 + 8 + 32 + 8) with (bv_unsigned sp + -272) in FJ5 by lia.
      replace (bv_unsigned sp + -320 + 8 + 32 + 8 + 5) with (bv_unsigned sp + -267) in FFC by lia.
      replace (bv_unsigned sp + -320 + 8 + 32 + 8 + 5 + 1) with (bv_unsigned sp + -266) in FX14 by lia.
      replace (bv_unsigned sp + -320 + 8 + 32 + 8 + 5 + 1 + 14) with (bv_unsigned sp + -252) in FUT by lia.
      replace (bv_unsigned sp + -320 + 8 + 32 + 8 + 5 + 1 + 14 + 4) with (bv_unsigned sp + -248) in FX24 by lia.
      replace (bv_unsigned sp + -320 + 8 + 32 + 8 + 5 + 1 + 14 + 4 + 24) with (bv_unsigned sp + -224) in FSV by lia.
      apply (cb_split _ _ 1 13) in FX14. cut_hd FX14 FXI (bv_unsigned sp + -265).
      apply (cb_split _ _ 1 12) in FX14. cut_hd FX14 FXS (bv_unsigned sp + -264).
      apply (cb_split _ _ 8 4) in FX14. cut_hd FX14 FXL (bv_unsigned sp + -256). rename FX14 into FJ4.
      destruct (cb_byte _ _ _ FXI) as [bi FXI']. clear FXI. destruct (cb_byte _ _ _ FXS) as [bc FXS']. clear FXS.
      join2 FXI' FXS'. join2 FXI' FXL. rename FXI' into FPIC.
      apply (cb_split _ _ 16 8) in FX24. cut_hd FX24 FJ16 (bv_unsigned sp + -232). apply cb8_word in FX24. rename FX24 into FCW.
      (* [comment removed for export] *)
      assert (OI2 : oinv sp m s LB E lo B canary K d D (XPO OPP OCT) (-320) STK s st m2 OW errv bo []).
      { eapply (oinv_munch sp m s LB E lo B canary K d D (XPO OPP OCT) (-320) STK CEIL GLO LO' STK0 OFS0 SPB B63 SP16 OFS16 (XPok sp B OPP OCT OPPlo OPPhi OCTlo OCThi) PBX);
          [exact OI0| exact MU| exact WM| exact MI2| exact ST2| exact ERR2|]. constructor; [left; cbn; lia| constructor]. }
      clear MU WM.
      setreg 10%Z (Z_to_bv 64 (bv_unsigned sp + -266 + 2)) ltac:(f_equal; lia). setreg 14%Z (Z_to_bv 64 (bv_unsigned sp + -266 + 1)) ltac:(f_equal; lia).
      ihere. to_implM.
      set (g := get_object d 0 (zlength d)) in *.
      pose proof (check_tlen_gen HM HF HGO sp m s LB E lo B canary K d D (XPO OPP OCT) DF CEIL GLO SPB B63 SP16 (XPok sp B OPP OCT OPPlo OPPhi OCTlo OCThi) PBX D1 D63 D30
                    (option (octet bptr)) (Some V_ASN1_OCTET_STRING)) as W.
      cbv beta iota delta [tlen_tree] in W.
      eapply W with (TLCo := Some (bv_unsigned sp + -56)) (PIC := bv_unsigned sp + -266) (PPC := bv_unsigned sp + -280) (op := 0);
        [exact LO'| exact OFS0| exact OFS16| unfold CHECK_TLEN_STACK, GETOBJ_STACK, ERR_SET_ERROR_STACK; lia| exact OI2| exact FRM| lia| lia| lia| unfold V_ASN1_OCTET_STRING; lia
        | lia| lia| lia| lia| lia| replace (bv_unsigned sp + -266 + 2) with (bv_unsigned sp + 0 + -264) by lia; apply mod8_frame; [exact SP16| reflexivity| reflexivity]
        | replace (bv_unsigned sp + -280) with (bv_unsigned sp + 0 + -280) by lia; apply mod8_frame; [exact SP16| reflexivity| reflexivity]
        | split; [lia| split; [lia| split; [lia| split; [replace (bv_unsigned sp + -56) with (bv_unsigned sp + 0 + -56) by lia; apply mod8_frame; [exact SP16| reflexivity| reflexivity]| exact FDT]]]]
        | exact FPIC| rewrite Z.add_0_r; exact FPP| | | ]; clear W.
      + (* [comment removed for export] *)
        intros e st' s' ms' bi' bc' jl' EG POT. unfold tlen_post in POT.
        destruct POT as (q0 & q1 & q2 & p1' & p2' & p3 & p4 & p5 & p6 & p7 & q3 & q4 & q5 & q6 & F1 & fc1 & mT & OWT & errvT & boT
                         & -> & FRM1 & FE1 & OIT & LXT & HPICT & HPPCT & (vb' & jt' & HTLCT)).
        replace (ret_pc (Z_to_bv 64 1122140)) with (Z_to_bv 64 1122140) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        pose proof (agree_of_lx_pres _ _ _ _ _ LXT) as AGT. cbn [app] in AGT.
        assert (CLT : forall a, ((bv_unsigned sp + -320 <= a < bv_unsigned sp /\ (a < bv_unsigned sp + -280 \/ bv_unsigned sp + -272 <= a) /\ (a < bv_unsigned sp + -266 \/ bv_unsigned sp + -256 <= a)
                                  /\ (a < bv_unsigned sp + -56 \/ bv_unsigned sp + -24 <= a)) \/ (OPP <= a < OPP + 8) \/ (OCT <= a < OCT + 8)) ->
                      lx_client LB (bv_unsigned sp + -320)
                        ([(bv_unsigned sp + -266, bv_unsigned sp + -266 + 10); (bv_unsigned sp + -280, bv_unsigned sp + -280 + 8); (bv_unsigned sp + -56, bv_unsigned sp + -56 + 32)] ++ LIBW_AP) a).
        { intros a Ha. split; [unfold LIBW_AP; cbn [rin_ivs fst snd app]; lia| left; lia]. }
        apply (rw_cells_agree _ _ _ _ _ AGT) in FBUF; [| intros a Ha; apply CLT; cbn in Ha; lia].
        apply (rw_cells_agree _ _ _ _ _ AGT) in FJ5; [| intros a Ha; apply CLT; cbn in Ha; lia].
        apply (rw_cells_agree _ _ _ _ _ AGT) in FFC; [| intros a Ha; apply CLT; cbn in Ha; lia].
        apply (rw_cells_agree _ _ _ _ _ AGT) in FJ4; [| intros a Ha; apply CLT; cbn in Ha; lia].
        apply (rw_cells_agree _ _ _ _ _ AGT) in FUT; [| intros a Ha; apply CLT; cbn in Ha; lia].
        apply (rw_cells_agree _ _ _ _ _ AGT) in FJ16; [| intros a Ha; apply CLT; cbn in Ha; lia].
        apply (rw_cells_agree _ _ _ _ _ AGT) in FCW; [| intros a Ha; apply CLT; cbn in Ha; lia].
        apply (rw_cells_agree _ _ _ _ _ AGT) in FSV; [| intros a Ha; apply CLT; cbn in Ha; lia].
        apply (rw_cells_agree _ _ _ _ _ AGT) in FI; [| intros a Ha; apply CLT; cbn in Ha; lia].
        apply (rw_cells_agree _ _ _ _ _ AGT) in FD0; [| intros a Ha; apply CLT; cbn in Ha; lia].
        apply (rw_cells_agree _ _ _ _ _ AGT) in FDH; [| intros a Ha; apply CLT; cbn in Ha; lia].
        apply (rw_cells_agree _ _ _ _ _ AGT) in HOPP; [| intros a Ha; apply CLT; cbn in Ha; lia].
        apply (rw_cells_agree _ _ _ _ _ AGT) in HOCT; [| intros a Ha; apply CLT; cbn in Ha; lia].
        apply (rw_cells_agree _ _ _ _ _ AGT) in FJ0; [| intros a Ha; apply CLT; cbn in Ha; lia].
        clear AGT CLT. unfold MallocRep.wz in HPPCT.
        cut_hd HPICT HBI (bv_unsigned sp + -265). cut_hd HPICT HBC (bv_unsigned sp + -264). apply cb8_word in HPICT. join2 HBI HBC. join2 HBI HPICT.
        eapply (dx_after_fail sp m s LB E lo B canary K d D ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F OW adr OPP OCT CEIL GLO SPB B63 SP16 PBX OPPlo OPPhi OCTlo OCThi STK);
          [exact LO'| unfold ERR_SET_ERROR_STACK; lia| exact OIT| exact FRM1| exact FE1| exact HOPP| exact HOCT| exact OCT8| exact FBUF| exact HPPCT| exact FJ5| exact FFC| exact HBI| exact FJ4| exact FUT| exact FJ16
          | exact FCW| exact FSV| exact FI| exact FD0| exact HTLCT| exact FDH| exact FJ0].
      + (* [comment removed for export] *)
        intros t st' s' ms' bi' bc' jl' _ EG _ POT. unfold tlen_post in POT.
        destruct POT as (q0 & q1 & q2 & p1' & p2' & p3 & p4 & p5 & p6 & p7 & q3 & q4 & q5 & q6 & F1 & fc1 & mT & OWT & errvT & boT
                         & -> & FRM1 & FE1 & OIT & LXT & HPICT & HPPCT & (vb' & jt' & HTLCT)).
        replace (ret_pc (Z_to_bv 64 1122140)) with (Z_to_bv 64 1122140) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        pose proof (agree_of_lx_pres _ _ _ _ _ LXT) as AGT. cbn [app] in AGT.
        assert (CLT : forall a, ((bv_unsigned sp + -320 <= a < bv_unsigned sp /\ (a < bv_unsigned sp + -280 \/ bv_unsigned sp + -272 <= a) /\ (a < bv_unsigned sp + -266 \/ bv_unsigned sp + -256 <= a)
                                  /\ (a < bv_unsigned sp + -56 \/ bv_unsigned sp + -24 <= a)) \/ (OPP <= a < OPP + 8) \/ (OCT <= a < OCT + 8)) ->
                      lx_client LB (bv_unsigned sp + -320)
                        ([(bv_unsigned sp + -266, bv_unsigned sp + -266 + 10); (bv_unsigned sp + -280, bv_unsigned sp + -280 + 8); (bv_unsigned sp + -56, bv_unsigned sp + -56 + 32)] ++ LIBW_AP) a).
        { intros a Ha. split; [unfold LIBW_AP; cbn [rin_ivs fst snd app]; lia| left; lia]. }
        apply (rw_cells_agree _ _ _ _ _ AGT) in FBUF; [| intros a Ha; apply CLT; cbn in Ha; lia].
        apply (rw_cells_agree _ _ _ _ _ AGT) in FJ5; [| intros a Ha; apply CLT; cbn in Ha; lia].
        apply (rw_cells_agree _ _ _ _ _ AGT) in FFC; [| intros a Ha; apply CLT; cbn in Ha; lia].
        apply (rw_cells_agree _ _ _ _ _ AGT) in FJ4; [| intros a Ha; apply CLT; cbn in Ha; lia].
        apply (rw_cells_agree _ _ _ _ _ AGT) in FUT; [| intros a Ha; apply CLT; cbn in Ha; lia].
        apply (rw_cells_agree _ _ _ _ _ AGT) in FJ16; [| intros a Ha; apply CLT; cbn in Ha; lia].
        apply (rw_cells_agree _ _ _ _ _ AGT) in FCW; [| intros a Ha; apply CLT; cbn in Ha; lia].
        apply (rw_cells_agree _ _ _ _ _ AGT) in FSV; [| intros a Ha; apply CLT; cbn in Ha; lia].
        apply (rw_cells_agree _ _ _ _ _ AGT) in FI; [| intros a Ha; apply CLT; cbn in Ha; lia].
        apply (rw_cells_agree _ _ _ _ _ AGT) in FD0; [| intros a Ha; apply CLT; cbn in Ha; lia].
        apply (rw_cells_agree _ _ _ _ _ AGT) in FDH; [| intros a Ha; apply CLT; cbn in Ha; lia].
        apply (rw_cells_agree _ _ _ _ _ AGT) in HOPP; [| intros a Ha; apply CLT; cbn in Ha; lia].
        apply (rw_cells_agree _ _ _ _ _ AGT) in HOCT; [| intros a Ha; apply CLT; cbn in Ha; lia].
        apply (rw_cells_agree _ _ _ _ _ AGT) in FJ0; [| intros a Ha; apply CLT; cbn in Ha; lia].
        clear AGT CLT. unfold MallocRep.wz in HPPCT.
        cut_hd HPICT HBI (bv_unsigned sp + -265). cut_hd HPICT HBC (bv_unsigned sp + -264). apply cb8_word in HPICT. join2 HBI HBC. join2 HBI HPICT.
        eapply (dx_after_fail sp m s LB E lo B canary K d D ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F OW adr OPP OCT CEIL GLO SPB B63 SP16 PBX OPPlo OPPhi OCTlo OCThi STK);
          [exact LO'| unfold ERR_SET_ERROR_STACK; lia| exact OIT| exact FRM1| exact FE1| exact HOPP| exact HOCT| exact OCT8| exact FBUF| exact HPPCT| exact FJ5| exact FFC| exact HBI| exact FJ4| exact FUT| exact FJ16
          | exact FCW| exact FSV| exact FI| exact FD0| exact HTLCT| exact FDH| exact FJ0].
      + (* [comment removed for export] *)
        intros st' s' ms' EG [ETAG ECLS] POT. unfold tlen_post in POT.
        destruct POT as (q0 & q1 & q2 & p1' & p2' & p3 & p4 & p5 & p6 & p7 & q3 & q4 & q5 & q6 & F1 & fc1 & mT & OWT & errvT & boT
                         & -> & FRM1 & FE1 & OIT & LXT & HPICT & HPPCT & (vb' & jt' & HTLCT)).
        replace (ret_pc (Z_to_bv 64 1122140)) with (Z_to_bv 64 1122140) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        pose proof (agree_of_lx_pres _ _ _ _ _ LXT) as AGT. cbn [app] in AGT.
        assert (CLT : forall a, ((bv_unsigned sp + -320 <= a < bv_unsigned sp /\ (a < bv_unsigned sp + -280 \/ bv_unsigned sp + -272 <= a) /\ (a < bv_unsigned sp + -266 \/ bv_unsigned sp + -256 <= a)
                                  /\ (a < bv_unsigned sp + -56 \/ bv_unsigned sp + -24 <= a)) \/ (OPP <= a < OPP + 8) \/ (OCT <= a < OCT + 8)) ->
                      lx_client LB (bv_unsigned sp + -320)
                        ([(bv_unsigned sp + -266, bv_unsigned sp + -266 + 10); (bv_unsigned sp + -280, bv_unsigned sp + -280 + 8); (bv_unsigned sp + -56, bv_unsigned sp + -56 + 32)] ++ LIBW_AP) a).
        { intros a Ha. split; [unfold LIBW_AP; cbn [rin_ivs fst snd app]; lia| left; lia]. }
        apply (rw_cells_agree _ _ _ _ _ AGT) in FBUF; [| intros a Ha; apply CLT; cbn in Ha; lia].
        apply (rw_cells_agree _ _ _ _ _ AGT) in FJ5; [| intros a Ha; apply CLT; cbn in Ha; lia].
        apply (rw_cells_agree _ _ _ _ _ AGT) in FJ0; [| intros a Ha; apply CLT; cbn in Ha; lia].
        apply (rw_cells_agree _ _ _ _ _ AGT) in FFC; [| intros a Ha; apply CLT; cbn in Ha; lia].
        apply (rw_cells_agree _ _ _ _ _ AGT) in FJ4; [| intros a Ha; apply CLT; cbn in Ha; lia].
        apply (rw_cells_agree _ _ _ _ _ AGT) in FUT; [| intros a Ha; apply CLT; cbn in Ha; lia].
        apply (rw_cells_agree _ _ _ _ _ AGT) in FJ16; [| intros a Ha; apply CLT; cbn in Ha; lia].
        apply (rw_cells_agree _ _ _ _ _ AGT) in FCW; [| intros a Ha; apply CLT; cbn in Ha; lia].
        apply (rw_cells_agree _ _ _ _ _ AGT) in FSV; [| intros a Ha; apply CLT; cbn in Ha; lia].
        apply (rw_cells_agree _ _ _ _ _ AGT) in FI; [| intros a Ha; apply CLT; cbn in Ha; lia].
        apply (rw_cells_agree _ _ _ _ _ AGT) in FD0; [| intros a Ha; apply CLT; cbn in Ha; lia].
        apply (rw_cells_agree _ _ _ _ _ AGT) in FDH; [| intros a Ha; apply CLT; cbn in Ha; lia].
        apply (rw_cells_agree _ _ _ _ _ AGT) in HOPP; [| intros a Ha; apply CLT; cbn in Ha; lia].
        apply (rw_cells_agree _ _ _ _ _ AGT) in HOCT; [| intros a Ha; apply CLT; cbn in Ha; lia].
        clear AGT CLT. unfold MallocRep.wz in HPPCT.
        fold g in HPICT, HPPCT. fold g.
        destruct (Z.land (go_ret g) 32 =? 0) eqn:EC; cbn [negb].
        * (* [comment removed for export] *)
          apply Z.eqb_eq in EC.
          pose proof (go_ret_ok d 0 (zlength d) EG) as RET. cbv zeta in RET. fold g in RET.
          assert (R0 : go_ret g = 0) by (destruct RET as [R|[R|R]]; [exact R| exfalso; rewrite R in EC; cbv in EC; lia| exfalso; rewrite R in EC; cbv in EC; lia]).
          rewrite R0. change (Z.testbit 0 0) with false. cbv iota.
          rewrite R0 in HPICT.
          eapply (dx_prim HM sp m s LB E lo B canary K d D ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F OW adr OPP OCT DF CEIL GLO SPB B63 SP16 PBX D1 D63 D30 OPPlo OPPhi OCTlo OCThi DJXP STK);
            [exact EG| exact ETAG| exact ECLS| rewrite R0; reflexivity| lia| exact LO'| unfold W_d2i_octet_B.PRIM_STK, ASN1_STRING_TYPE_NEW_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RMALLOC_STACK; lia
            | exact OIT| exact FRM1| exact FE1| exact HOPP| exact HOCT| exact FBUF| exact HPPCT| exact FJ5| exact FFC| rewrite R0; exact HPICT| exact FJ4| exact FUT| exact FJ16
            | exact FCW| exact FSV| exact FI| exact FD0| exact HTLCT| exact FDH| exact FJ0| exact OCT8].
        * (* [comment removed for export] *)
          apply Z.eqb_neq in EC.
          eapply (dx_cons HM HF HGO sp m s LB E lo B canary K d D ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F OW adr OPP OCT DF CEIL GLO SPB B63 SP16 PBX D1 D63 D30 OPPlo OPPhi OCTlo OCThi DJXP STK);
            [exact EG| exact ETAG| exact ECLS| exact EC| lia| exact LO'| exact STKC
            | exact OIT| exact FRM1| exact FE1| exact HOPP| exact HOCT| exact FBUF| exact HPPCT| exact FJ5| exact FFC| exact HPICT| exact FJ4| exact FUT| exact FJ16
            | exact FCW| exact FSV| exact FI| exact FD0| exact HTLCT| exact FDH| exact FJ0| exact OCT8].
  Qed.
End Proofs.
End WithCeiling0.
