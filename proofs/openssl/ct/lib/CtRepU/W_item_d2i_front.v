(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Monad Stdio Prog LibProg ProgG.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import ApBase ApState ApInv ApErr ApParse ApPrim ApBridge.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Layout Lib_iface Lib_kit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXU Require Import HxpFacts HxpInit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtBnU Require Import BnKit BnHeap BnRep W_crypto.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApCells ApRepDefs ApRep ApIface ApWalkTac ApErrKit ApErrKit2 W_get_object W_get_object_walk W_c2i_int W_check_tlen W_item_d2i_stmt W_item_d2i_img ApUTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

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

Ltac join2 H1 H2 :=
  lazymatch type of H1 with rw_cells _ ?m ?A ?cs1 =>
  lazymatch type of H2 with rw_cells _ _ ?A2 ?cs2 =>
    replace A2 with (A + Z.of_nat (cells_size cs1))%Z in H2 by (cbn [cells_size csize Nat.add]; lia);
    let J := fresh in
    pose proof (proj2 (rw_cells_app m A cs1 cs2) (conj H1 H2)) as J; clear H1 H2; cbn [app] in J; rename J into H1
  end end.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].
Local Ltac step := ub; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.
Local Ltac zstep := ub; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition ASN1_ITEM_D2I : Z := 0x110f68.
Definition D2I_INT_ARM : Z := 0x112318.
Definition D2I_OCT_ARM : Z := 0x1123c8.
Definition RA_INTERN : Z := 0x110e84.     (* [comment removed for export] *)
Definition RA_D2IEX : Z := 0x110f38.      (* [comment removed for export] *)

Lemma utype_cases : forall e utype, d2i_entry e utype -> utype = 4 \/ utype = 2 \/ utype = 10.
Proof. intros e utype [[_ ->]|[[_ ->]|[_ ->]]]; unfold V_ASN1_OCTET_STRING, V_ASN1_INTEGER, V_ASN1_ENUMERATED; lia. Qed.

Lemma land64_neg_small : forall z, - 2 ^ 64 <= z < 0 -> Z.land z 18446744073709551615 = z + 2 ^ 64.
Proof.
  intros z Hz. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia.
  rewrite <- (Z.mod_add z 1 (2 ^ 64)) by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma land64_pos_small : forall z, 0 <= z < 2 ^ 64 -> Z.land z 18446744073709551615 = z.
Proof. intros z Hz. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.

(* [comment removed for export] *)
Lemma cb_split : forall m a (n1 n2 : nat) j,
  rw_cells ctusegs m a [CB (n1 + n2) j] -> rw_cells ctusegs m a [CB n1 (firstn n1 j); CB n2 (skipn n1 j)].
Proof.
  intros m a n1 n2 j H. pose proof H as [[W _] _]. cbn in W. destruct W as [L _].
  eapply rw_cells_recast; [exact H| cbn; rewrite length_firstn, length_skipn; repeat split; lia| | cbn; lia].
  cbn [cells_bytes cbytes app]. rewrite !app_nil_r. apply firstn_skipn.
Qed.
Lemma cb_byte : forall m a j, rw_cells ctusegs m a [CB 1 j] -> exists b, rw_cells ctusegs m a [C1 b].
Proof.
  intros m a j H. pose proof H as [[W _] _]. cbn in W. destruct W as [L _].
  destruct j as [|b [|]]; cbn in L; try lia. exists b.
  eapply rw_cells_recast; [exact H| cbn; auto| reflexivity| reflexivity].
Qed.

(* [comment removed for export] *)
Definition exprim_frame (sp : word) (s3 s4 s5 s6 s7 s8 s9 s10 : word) (utype D cont plen item : Z) (cw : word) (j5 j4 j16 j0 : list byte) : list cell :=
  [CB 8 j0; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (D + cont + plen)); CB 5 j5;
   C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C8 (Z_to_bv 64 plen); CB 4 j4; C4 (Z_to_bv 64 utype); CB 16 j16; C8 cw;
   C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3;
   C8 (Z_to_bv 64 (bv_unsigned sp + -64)); C8 (Z_to_bv 64 item); C8 (Z_to_bv 64 (bv_unsigned sp + -64)); C8 (Z_to_bv 64 RA_INTERN)].
Definition intern_frame (sp s2 s3 : word) : list cell :=
  [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 s3; C8 s2; C8 (Z_to_bv 64 (bv_unsigned sp + -64)); C8 sp; C8 (Z_to_bv 64 RA_D2IEX)].
Definition d2iex_frame (ra s0 s1 : word) (pv : Z) (jt : list byte) : list cell :=
  [C8 (Z_to_bv 64 pv); CB 32 jt; C8 s1; C8 s0; C8 ra].

(* [comment removed for export] *)
Definition front_post (pc : Z) (ra sp gp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (s : PState) (st : ap_st bptr) (OW LB : list block) (E : ap_env) (bo : Z * Z) (lo B : Z) (canary : word) (m : mem) (K : list block)
    (D : Z) (d : list Z) (op cont plen utype OPP : Z) (POST : machine_state -> Prop) : Prop :=
  forall (ra' t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (OW' : list block) (errv' : word)
         (j5 j4 j16 j0 jt : list byte),
    frm0 fc' -> (forall k : reg, bv_unsigned k <> 10 -> reg_get F' k = reg_get F k) ->
    ap_pre s st m' OW' LB E bo (Z_to_bv 64 (bv_unsigned sp + -320)) lo B errv' canary (D2I_PRIM_STACK - 320) ->
    lx_pres LB (bv_unsigned sp) LIBW_AP m m' -> blocks_kept K st OW' m m' -> payload_ok m' LB D d ->
    rw_cells ctusegs m' OPP [C8 (Z_to_bv 64 (D + op))] ->
    rw_cells ctusegs m' (bv_unsigned sp + -320) (exprim_frame sp s3 s4 s5 s6 s7 s8 s9 s10 utype D cont plen (item_of utype) (Z_to_bv 64 (D + cont)) j5 j4 j16 j0) ->
    rw_cells ctusegs m' (bv_unsigned sp + -128) (intern_frame sp s2 s3) ->
    rw_cells ctusegs m' (bv_unsigned sp + -64) (d2iex_frame ra s0 s1 0 jt) ->
    evt ctusegs POST
      (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -320)) gp (Z_to_bv 64 RATP) t0 t1 t2 (Z_to_bv 64 (bv_unsigned sp + -128)) (Z_to_bv 64 OPP)
               a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 (bv_unsigned sp + -64)) (Z_to_bv 64 0) (Z_to_bv 64 (D + cont)) (Z_to_bv 64 plen) (Z_to_bv 64 utype) (Z_to_bv 64 utype)
               (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 1) s11 t3 t4 t5 t6)
          F' (Z_to_bv 64 pc) fc' None m' (seg_rom ctusegs)).

Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.
  Hypothesis HGO : ASN1_get_object_spec.

  Lemma d2i_front : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (st : ap_st bptr) (OW LB : list block) (E : ap_env) (bo : Z * Z)
      (lo B : Z) (errv canary : word) (K : list block)
      (D : Z) (d : list Z) (op totlen OPP e utype : Z) (POST : machine_state -> Prop),
    ap_pre s st m OW LB E bo sp lo B errv canary D2I_PRIM_STACK -> tp = wz RATP -> frm0 fc ->
    (forall b, In b K -> In b OW) -> (forall b, In b K -> ~ In (blk_id b) (es_ids st ++ env_ids E)) ->
    payload_ok m LB D d -> 0 <= op -> 0 < totlen -> op + totlen <= zlength d ->
    go_err (get_object d op totlen) = None -> go_tag (get_object d op totlen) = utype -> go_cls (get_object d op totlen) = 0 ->
    Z.land (go_ret (get_object d op totlen)) 32 = 0 -> d2i_entry e utype ->
    bv_unsigned sp <= OPP -> OPP + 8 <= B -> OPP mod 8 = 0 -> rw_cells ctusegs m OPP [C8 (wz (D + op))] ->
    ((utype = V_ASN1_INTEGER \/ utype = V_ASN1_ENUMERATED) ->
     front_post D2I_INT_ARM ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F s st OW LB E bo lo B canary m K D d op
                (go_p (get_object d op totlen)) (go_len (get_object d op totlen)) utype OPP POST) ->
    (utype = V_ASN1_OCTET_STRING ->
     front_post D2I_OCT_ARM ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F s st OW LB E bo lo B canary m K D d op
                (go_p (get_object d op totlen)) (go_len (get_object d op totlen)) utype OPP POST) ->
    evt ctusegs POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz 0) (wz OPP) (wz totlen) (wz (item_of utype)) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz ASN1_ITEM_D2I) fc None m (seg_rom ctusegs)).
  Proof using HGO.
    intros until POST. intros PRE TP FRM KOW KIDS PAY OP0 TL0 OPT EG ETAG ECLS ERET ENT OPS OPB OPA HOPP KINT KOCT.
    set (g := get_object d op totlen) in *.
    pose proof (utype_cases _ _ ENT) as UT.
    pose proof PRE as PRE0.
    destruct PRE as (HEAP & AS & IDS & DC & AUX & SPB & B63 & ST & CEIL & GLO & LO & ERR & SSP & MI & SP16).
    pose proof AS as (_ & IMG & _).
    pose proof (item_cells_of m e utype IMG ENT) as (IT0 & IT8 & IT8L & IT16 & IT32).
    pose proof PAY as (HB & PF & D0 & D63 & D30 & HBLK).
    destruct HBLK as [->|(blk & HPB & PA1 & PA2)]; [exfalso; unfold zlength in OPT; cbn in OPT; lia|].
    destruct blk as [[pb PA] psz]. cbn [blk_addr blk_size fst snd] in PA1, PA2.
    pose proof (LH_block_range _ _ _ _ HEAP ltac:(apply in_app_iff; right; exact HPB)) as (BB0 & BB1 & BB2 & BB3 & BB4). cbn [blk_addr blk_size fst snd] in BB0, BB1, BB2, BB3, BB4.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    assert (EA : errno_addr (Z_to_bv 64 RATP) = 3355012) by (unfold errno_addr, RATP; rewrite unsigned_lit by lia; reflexivity).
    unfold MallocRep.wz in ERR. rewrite EA in ERR.
    assert (DLEN : Z.of_nat (length (to_bytes d)) = zlength d) by apply zlength_to_bytes.
    pose proof (get_object_bounds d op totlen ltac:(eapply Forall_impl; [| exact PF]; cbv beta; intros; lia) TL0) as GB. cbv zeta in GB. fold g in GB. rewrite EG in GB.
    destruct GB as (GB1 & GB2 & GB3).
    assert (ITR : IMG_LO <= item_of utype /\ item_of utype + 56 <= IMG_HI) by (unfold item_of, ITEM_OCTET, ITEM_INTEGER, ITEM_ENUM, IMG_LO, IMG_HI; destruct UT as [->|[->| ->]]; cbn; lia).
    assert (ITA : item_of utype mod 8 = 0) by (unfold item_of, ITEM_OCTET, ITEM_INTEGER, ITEM_ENUM; destruct UT as [->|[->| ->]]; reflexivity).
    unfold IMG_LO, IMG_HI in ITR.
    unfold D2I_PRIM_STACK, GETOBJ_STACK, ERR_SET_ERROR_STACK, GLOBALS_TOP, ASN1_ITEM_D2I, MallocRep.wz in *.
    unfold MallocRep.wz in HOPP.
    pose proof (munch_refl [(bv_unsigned sp - 8960, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
    subst tp.
    (* [comment removed for export] *)
    carve_frame 16%nat ST. do 9 step. release_frame FR ST (bv_unsigned sp). step.
    (* [comment removed for export] *)
    carve_frame 64%nat ST. do 9 step.
    step. if_true. do 7 step.
    (* [comment removed for export] *)
    carve_frame 64%nat ST. do 7 step.
    step. if_cases K0; zc K0; [exfalso; lia|]. step. step. if_cases K1; zc K1; [exfalso; lia|].
    do 5 step. step.
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    name_mem mA. pose proof (munch_refl [(bv_unsigned sp - 304, bv_unsigned sp - 128)]%Z mA) as MUp. pose proof (wmono_refl ctusegs mA) as WMp.
    repeat match goal with H : rw_cells ctusegs mA _ _ |- _ => let T := type of H in change (frozen T) in H
                          | H : ro_cells ctusegs mA _ _ |- _ => let T := type of H in change (frozen T) in H
                          | H : bytes_at ctusegs mA _ _ |- _ => let T := type of H in change (frozen T) in H end.
    carve_frame 176%nat ST. do 15 step.
    name_mem mB. unfold frozen in *.
    transport_after_call ctusegs mA mB MUp WMp. clear MUp WMp.
    step. step. step. step. step. step.
    step. if_cases K2; zc K2; [exfalso; lia|]. step. step. if_cases K3; zc K3; [exfalso; lia|].
    step. step. if_cases K4; zc K4; [exfalso; revert K4; rewrite ?signed_small by lia; lia|].
    step. step. step. step. step. if_true.
    step. step. step. step. if_true.
    step. change (zxb (Z_to_bv 8 0)) with (Z_to_bv 64 0). step. step. step. if_false.
    step. step. step. step.
    match goal with H : mem_inv ctusegs ?mx |- evt _ _ (MS _ _ _ _ _ ?mx _) => pose proof (jt_embed_d2i mx H) as JT1 end.
    step. clear JT1. rewrite (sx32_small 851044) by lia. step. setreg 12 (Z_to_bv 64 1118712) ltac:(reflexivity). step. step.
    step. step. if_true. do 7 step. do 13 step. step. release_frame FR1 ST (bv_unsigned sp + -128). step.
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    name_mem mC. pose proof (munch_refl [(bv_unsigned sp - 320, bv_unsigned sp - 128)]%Z mC) as MUp. pose proof (wmono_refl ctusegs mC) as WMp.
    repeat match goal with H : rw_cells ctusegs mC _ _ |- _ => let T := type of H in change (frozen T) in H
                          | H : ro_cells ctusegs mC _ _ |- _ => let T := type of H in change (frozen T) in H
                          | H : bytes_at ctusegs mC _ _ |- _ => let T := type of H in change (frozen T) in H end.
    carve_frame 192%nat ST. do 14 step.
    name_mem mD. unfold frozen in *.
    transport_after_call ctusegs mC mD MUp WMp. clear MUp WMp.
    do 15 step. change (zxb (Z_to_bv 8 0)) with (Z_to_bv 64 0). step. if_true.
    step. rewrite (sx32_small utype) by lia. step. step. step. if_cases KANY; zc KANY; [| exfalso; lia].
    step. step. step. step. if_false.
    step. rewrite (sx32_small utype) by lia. step. step. step. step. step. step. step. step. step. step. step. step. step. step. step.
    name_mem m1.
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -320)) = bv_unsigned sp + -320) by (apply unsigned_lit; lia).
    (* [comment removed for export] *)
    lazymatch type of FR1 with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: CB 14 ?j :: ?rest) =>
      change (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: CB 14 j :: rest) with ([c0] ++ [c1; c2; c3; c4] ++ [c5] ++ [c6; c7] ++ [CB 14 j] ++ rest) in FR1 end.
    apply rw_cells_app in FR1. destruct FR1 as [FX0 FR1]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FR1.
    apply rw_cells_app in FR1. destruct FR1 as [FXA FR1]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FR1.
    apply rw_cells_app in FR1. destruct FR1 as [FXP FR1]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FR1.
    apply rw_cells_app in FR1. destruct FR1 as [FXB FR1]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FR1.
    apply rw_cells_app in FR1. destruct FR1 as [FXC FXD]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FXD.
    replace (bv_unsigned sp + -320 + 8) with (bv_unsigned sp + -312) in FXA by lia.
    replace (bv_unsigned sp + -320 + 8 + 32) with (bv_unsigned sp + -280) in FXP by lia.
    replace (bv_unsigned sp + -320 + 8 + 32 + 8) with (bv_unsigned sp + -272) in FXB by lia.
    replace (bv_unsigned sp + -320 + 8 + 32 + 8 + 6) with (bv_unsigned sp + -266) in FXC by lia.
    replace (bv_unsigned sp + -320 + 8 + 32 + 8 + 6 + 14) with (bv_unsigned sp + -252) in FXD by lia.
    apply (cb_split _ _ 1 13) in FXC. lazymatch type of FXC with rw_cells _ _ _ [?c1; ?c2] => change [c1; c2] with ([c1] ++ [c2]) in FXC end.
    apply rw_cells_app in FXC. destruct FXC as [FXI FXC]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FXC.
    apply (cb_split _ _ 1 12) in FXC. lazymatch type of FXC with rw_cells _ _ _ [?c1; ?c2] => change [c1; c2] with ([c1] ++ [c2]) in FXC end.
    apply rw_cells_app in FXC. destruct FXC as [FXS FXC]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FXC.
    apply (cb_split _ _ 8 4) in FXC. lazymatch type of FXC with rw_cells _ _ _ [?c1; ?c2] => change [c1; c2] with ([c1] ++ [c2]) in FXC end.
    apply rw_cells_app in FXC. destruct FXC as [FXL FX4]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FX4.
    replace (bv_unsigned sp + -266 + 1) with (bv_unsigned sp + -265) in FXS by lia.
    replace (bv_unsigned sp + -266 + 1 + 1) with (bv_unsigned sp + -264) in FXL by lia.
    replace (bv_unsigned sp + -266 + 1 + 1 + 8) with (bv_unsigned sp + -256) in FX4 by lia.
    destruct (cb_byte _ _ _ FXI) as [bi FXI']. clear FXI. destruct (cb_byte _ _ _ FXS) as [bc FXS']. clear FXS.
    lazymatch type of FR with rw_cells _ _ _ (?c0 :: ?c1 :: CB 31 ?j :: ?rest) =>
      change (c0 :: c1 :: CB 31 j :: rest) with ([c0] ++ (c1 :: [CB 31 j]) ++ rest) in FR end.
    apply rw_cells_app in FR. destruct FR as [FDV FR]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FR.
    apply rw_cells_app in FR. destruct FR as [FDT FDS]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FDS.
    replace (bv_unsigned sp + -64 + 8) with (bv_unsigned sp + -56) in FDT by lia.
    replace (bv_unsigned sp + -64 + 8 + 32) with (bv_unsigned sp + -24) in FDS by lia.
    lazymatch type of FDT with rw_cells _ _ _ [_; CB 31 ?j] => change (rw_cells ctusegs m1 (bv_unsigned sp + -56) (tlc_in j)) in FDT end.
    assert (PRE1 : ap_pre s st m1 OW LB E bo (Z_to_bv 64 (bv_unsigned sp + -320)) lo B errv canary CHECK_TLEN_STACK).
    { eapply (ap_pre_seg s st m m1); [exact PRE0| exact MU| exact WM| exact MI| rewrite ESP; exact ST| | rewrite ESP; unfold CHECK_TLEN_STACK, GETOBJ_STACK, ERR_SET_ERROR_STACK; lia| rewrite ESP; lia
        | rewrite ESP; replace (bv_unsigned sp + -320) with (bv_unsigned sp - 320) by lia; rewrite Zminus_mod, SP16; reflexivity| exact ERR].
      constructor; [cbn; lia| constructor]. }
    assert (PAY1 : payload_ok m1 LB D d).
    { split; [exact HB|]. split; [exact PF|]. split; [lia|]. split; [lia|]. split; [lia|]. right. exists (pb, PA, psz). split; [exact HPB|]. cbn. lia. }
    assert (LX1 : lx_pres LB (bv_unsigned sp) LIBW_AP m m1).
    { eapply (lx_pres_stack s OW LB); [exact HEAP| exact CEIL| unfold GLOBALS_TOP; lia| exact MU| exact WM|]. constructor; [cbn; lia| constructor]. }
    assert (KP1 : kept K m m1).
    { eapply (kept_stack s OW LB); [exact HEAP| exact KOW| exact CEIL| exact MU|]. constructor; [cbn; lia| constructor]. }
    (* [comment removed for export] *)
    eapply (check_tlen_walk HGO) with (K := K) (d := d) (op := op) (totlen := totlen) (exptag := utype)
        (POLEN := bv_unsigned sp + -264) (PINF := bv_unsigned sp + -266) (PCST := bv_unsigned sp + -265) (PPC := bv_unsigned sp + -280) (TLC := bv_unsigned sp + -56);
      [ exact PRE1 | reflexivity | exact FRM | exact KOW | exact KIDS | exact PAY1 | lia | lia | lia
      | exact EG | exact ETAG | exact ECLS | exact ERET | lia
      | rewrite ESP; lia | lia | lia | lia | lia | lia
      | clear - SP16; Z.div_mod_to_equations; lia | clear - SP16; Z.div_mod_to_equations; lia | clear - SP16; Z.div_mod_to_equations; lia
      | exact FXL | exact FXI' | exact FXS' | exact FXP | exact FDT | ].
    cbv beta. intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F2 fc2 m2 OW2 errv2 jt FRM2 FEQ2 PRE2 LX2 BK2 HOLEN HINF HCST HPPC HTLC.
    rewrite ?ESP in LX2. unfold MallocRep.wz in HOLEN, HPPC. fold g in HOLEN, HPPC |- *.
    assert (PGR : 0 < D + go_p g /\ D + go_p g + go_len g < 2 ^ 63) by lia.
    replace (ret_pc (Z_to_bv 64 1122140)) with (Z_to_bv 64 1122140) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof PRE2 as (HEAP2 & AS2 & IDS2 & DC2 & AUX2 & _ & _ & ST2 & _ & _ & _ & ERR2 & SSP2 & MI2 & _). rewrite ESP in ST2.
    unfold MallocRep.wz in ERR2. rewrite EA in ERR2.
    pose proof AS2 as (_ & IMG2 & _).
    pose proof (item_cells_of m2 e utype IMG2 ENT) as (JT0 & JT8 & JT8L & JT16 & JT32).
    (* [comment removed for export] *)
    pose proof (agree_of_lx_pres _ _ _ _ _ LX2) as AG2.
    assert (CL : forall a, (bv_unsigned sp + -320 <= a /\ (a < bv_unsigned sp + -280 \/ bv_unsigned sp + -272 <= a) /\ (a < bv_unsigned sp + -266 \/ bv_unsigned sp + -256 <= a)
                            /\ (a < bv_unsigned sp + -56 \/ bv_unsigned sp + -24 <= a)) ->
                 lx_client LB (bv_unsigned sp + -320)
                   ([(bv_unsigned sp + -264, bv_unsigned sp + -264 + 8); (bv_unsigned sp + -266, bv_unsigned sp + -266 + 1); (bv_unsigned sp + -265, bv_unsigned sp + -265 + 1);
                     (bv_unsigned sp + -280, bv_unsigned sp + -280 + 8); (bv_unsigned sp + -56, bv_unsigned sp + -56 + 32)] ++ LIBW_AP) a).
    { intros a Ha. split; [unfold LIBW_AP; cbn [rin_ivs fst snd app]; lia| left; lia]. }
    apply (rw_cells_agree _ _ _ _ _ AG2) in FX0; [| intros a Ha; apply CL; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ AG2) in FXA; [| intros a Ha; apply CL; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ AG2) in FXB; [| intros a Ha; apply CL; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ AG2) in FX4; [| intros a Ha; apply CL; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ AG2) in FXD; [| intros a Ha; apply CL; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ AG2) in FR0; [| intros a Ha; apply CL; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ AG2) in FDV; [| intros a Ha; apply CL; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ AG2) in FDS; [| intros a Ha; apply CL; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ AG2) in HOPP; [| intros a Ha; apply CL; cbn in Ha; lia].
    apply (bytes_at_agree _ _ _ _ _ AG2) in HB.
    2:{ intros a Ha. rewrite DLEN in Ha. split; [unfold LIBW_AP; cbn [rin_ivs fst snd app]; lia|]. right. left. exists (pb, PA, psz). split; [exact HPB| cbn; lia]. }
    clear AG2 CL MU WM MI ST ERR IT0 IT8 IT8L IT16 IT32 FXP FXL FXI' FXS' FDT PRE1 PAY1.
    pose proof (munch_refl [(bv_unsigned sp - 8960, bv_unsigned sp)]%Z m2) as MU. pose proof (wmono_refl ctusegs m2) as WM.
    (* [comment removed for export] *)
    step. step. if_false. step. if_true.
    step. rewrite (sx32_small utype) by lia. step. step.
    step. if_cases KU; zc KU; [| exfalso; revert KU; rewrite land64_neg_small by lia; lia]. clear KU.
    step. step. if_cases KO; zc KO; [| exfalso; revert KO; rewrite ?land64_neg_small, ?land64_pos_small by lia; lia]. clear KO.
    step. change (zxb (Z_to_bv 8 0)) with (Z_to_bv 64 0). step. if_true.
    step. step. step. step. step. step. step. rewrite (sx32_small utype) by lia. step. step. if_true.
    step. step. step. if_cases KA; zc KA; [| exfalso; revert KA; rewrite ?land64_neg_small, ?land64_pos_small by lia; lia]. clear KA.
    step. step. step. step. step.
    if_cases K9; zc K9; [exfalso; revert K9; rewrite ?land64_neg_small, ?land64_pos_small by lia; lia|]. clear K9.
    step. step. step. zstep.
    setreg 10 (Z_to_bv 64 (4 * (utype - 1) + 267696)) ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
    match goal with H : mem_inv ctusegs ?mx |- evt _ _ (MS _ _ _ _ _ ?mx _) => pose proof (jt_ex_prim_of mx e utype H ENT) as JT2 end.
    replace (267696 + 4 * (utype - 1)) with (4 * (utype - 1) + 267696) in JT2 by lia.
    step. clear JT2.
    name_mem m3.
    (* [comment removed for export] *)
    match goal with H : stk ctusegs m3 lo _ |- _ => rename H into ST3 end.
    match goal with H : mem_inv ctusegs m3 |- _ => rename H into MI3 end.
    match goal with H : rw_cells ctusegs m3 3355012 _ |- _ => rename H into ERR3 end.
    assert (PRE3 : ap_pre s st m3 OW2 LB E bo (Z_to_bv 64 (bv_unsigned sp + -320)) lo B errv2 canary (D2I_PRIM_STACK - 320)).
    { eapply (ap_pre_seg s st m2 m3); [exact PRE2| exact MU| exact WM| exact MI3| rewrite ESP; exact ST3| | rewrite ESP; unfold D2I_PRIM_STACK, GETOBJ_STACK, ERR_SET_ERROR_STACK; lia| rewrite ESP; lia
        | rewrite ESP; replace (bv_unsigned sp + -320) with (bv_unsigned sp - 320) by lia; rewrite Zminus_mod, SP16; reflexivity| exact ERR3].
      constructor; [cbn; lia| constructor]. }
    assert (LX3 : lx_pres LB (bv_unsigned sp) LIBW_AP m m3).
    { eapply lx_pres_trans; [exact LX1|]. eapply lx_pres_trans.
      - eapply (lx_pres_above s OW LB) with (lo := lo); [exact HEAP| exact CEIL| unfold GLOBALS_TOP; lia| exact LX2| lia|].
        repeat (constructor; [cbn; lia|]). constructor.
      - eapply (lx_pres_stack s OW2 LB); [exact HEAP2| exact CEIL| unfold GLOBALS_TOP; lia| exact MU| exact WM|]. constructor; [cbn; lia| constructor]. }
    assert (KP3 : blocks_kept K st OW2 m m3).
    { destruct BK2 as (K1' & K2' & K3'). split; [exact K1'|]. split; [exact K2'|].
      eapply kept_trans; [exact KP1|]. eapply kept_trans; [exact K3'|].
      eapply (kept_stack s OW2 LB); [exact HEAP2| exact K1'| exact CEIL| exact MU|]. constructor; [cbn; lia| constructor]. }
    assert (PAY3 : payload_ok m3 LB D d).
    { split; [exact HB|]. split; [exact PF|]. split; [lia|]. split; [lia|]. split; [lia|]. right. exists (pb, PA, psz). split; [exact HPB|]. cbn. lia. }
    (* [comment removed for export] *)
    join2 FX0 FXA. join2 FX0 HPPC. join2 FX0 FXB. join2 FX0 HINF. join2 FX0 HCST. join2 FX0 HOLEN. join2 FX0 FX4. join2 FX0 FXD.
    join2 FDV HTLC. join2 FDV FDS. replace (go_len g + (D + go_p g)) with (D + go_p g + go_len g) in FX0 by lia.
    destruct UT as [U4|[U2|U10]].
    - (* [comment removed for export] *)
      rewrite U4 in *. clear U4.
      change (jt_prim_entry 4) with 855576. rewrite (sx32_small 855576) by lia.
      step. setreg 10 (Z_to_bv 64 1123272) ltac:(reflexivity). step.
      eapply (KOCT eq_refl); [exact FRM2| exact FEQ2| exact PRE3| exact LX3| exact KP3| exact PAY3| exact HOPP| exact FX0| exact FR0| exact FDV].
    - rewrite U2 in *. clear U2. change (jt_prim_entry 2) with 855400. rewrite (sx32_small 855400) by lia.
      step. setreg 10 (Z_to_bv 64 1123096) ltac:(reflexivity). step.
      eapply (KINT (or_introl eq_refl)); [exact FRM2| exact FEQ2| exact PRE3| exact LX3| exact KP3| exact PAY3| exact HOPP| exact FX0| exact FR0| exact FDV].
    - rewrite U10 in *. clear U10. change (jt_prim_entry 10) with 855400. rewrite (sx32_small 855400) by lia.
      step. setreg 10 (Z_to_bv 64 1123096) ltac:(reflexivity). step.
      eapply (KINT (or_intror eq_refl)); [exact FRM2| exact FEQ2| exact PRE3| exact LX3| exact KP3| exact PAY3| exact HOPP| exact FX0| exact FR0| exact FDV].
  Qed.
End Proofs.
End WithCeiling0.
