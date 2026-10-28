(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim Malloc Prog LibProg CtSizes CtWire ApPrim.
From Stdlib Require Import ZArith List Lia Bool.
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
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApCells ApRepDefs ApRep ApWalkTac W_item_d2i_stmt W_item_d2i_img.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtEncU Require Import EncPure EncStmt EncKit W_asn1_enc_leaves W_asn1_i2d.
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
  | le1 ?v => constr:(C1 (Z_to_bv 8 (bv_unsigned v)))
  | Z_to_le_bytes 8 ?z => constr:(C8 (Z_to_bv 64 z))
  | Z_to_le_bytes 4 ?z => constr:(C4 (Z_to_bv 64 z))
  | Z_to_le_bytes 1 ?z => constr:(C1 (Z_to_bv 8 z))
  end.

Ltac to_implM :=
  lazymatch goal with |- impl ?segs _ (?c ?stt) (epost ?EE) ?ms =>
    lazymatch EE with (fun p => ?Q (fst p) (snd p)) => change (implM segs c stt Q ms) end end.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma i2d_octet_fwd : forall (P : machine_state -> Prop)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : mem) (lo : Z),
  stk ctusegs m lo (bv_unsigned sp) -> mem_inv ctusegs m -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - 16 ->
  (forall m1, munch [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m m1 -> wmono ctusegs m m1 -> mem_inv ctusegs m1 ->
              stk ctusegs m1 lo (bv_unsigned sp) ->
              evt ctusegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 (wz ITEM_OCTET) (wz 0) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (wz ASN1_ITEM_FLAGS_I2D) fc None m1 (seg_rom ctusegs))) ->
  evt ctusegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz I2D_ASN1_OCTET_STRING) fc None m (seg_rom ctusegs)).
Proof.
  intros until lo. intros ST MI GLO LO K.
  unfold GLOBALS_TOP in GLO. unfold I2D_ASN1_OCTET_STRING, ASN1_ITEM_FLAGS_I2D, ITEM_OCTET, MallocRep.wz in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
  (* [comment removed for export] *)
  carve_frame 16%nat ST. do 4 zstep. do 4 zstep. zstep. release_frame FR ST (bv_unsigned sp). zstep.
  (* [comment removed for export] *)
  carve_frame 16%nat ST. do 4 zstep. do 3 zstep. zstep. release_frame FR ST (bv_unsigned sp). zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => apply (K mx MU WM ltac:(assumption) ST) end.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ASN1_ITEM_FLAGS_I2D_STACK : Z := 80 + CRYPTO_MALLOC_STACK.

(* [comment removed for export] *)
Definition flags_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (L : list block) (lo B : Z) (m : mem) (A len D DER : Z)
    (p : bptr) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' AD (errv' : word),
    ms' = MS (mkR ra sp gp (wz RATP) t0 t1 t2 s0 s1 (wz (der_hl len + len)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ctusegs)
    /\ mem_inv ctusegs m' /\ stk ctusegs m' lo (bv_unsigned sp)
    /\ rw_cells ctusegs m' LX_ERRNO [C4 errv'] /\ rauxv_ok m' B
    /\ rheap_pres_but L (bv_unsigned sp) (DER, DER + 8) m m'
    /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
    /\ rblock_range AD (der_hl len + len) /\ RHEAP s' ((p, AD, der_hl len + len) :: L) m'
    /\ rw_cells ctusegs m' DER [C8 (wz AD)]
    /\ rw_cells ctusegs m' A (asn1_string_cells len V_ASN1_OCTET_STRING D 0)
    /\ (exists bs, rw_cells ctusegs m' AD [CB (Z.to_nat (der_hl len + len)) bs]).

Section Proofs.
  Hypothesis HM : rmalloc_stmt.

  Lemma asn1_item_flags_i2d_walk : forall {X : Type}
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (L : list block) (lo B : Z) (errv : word)
      (poct pdata : bptr) (A len D DER : Z) (src : list byte)
      (k : option bptr -> lprog X) (Q : X -> PState -> machine_state -> Prop),
    RHEAP s L m -> rauxv_ok m B -> bv_unsigned sp <= B -> B < 2^63 ->
    stk ctusegs m lo (bv_unsigned sp) -> bv_unsigned sp mod 16 = 0 -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - ASN1_ITEM_FLAGS_I2D_STACK ->
    rw_cells ctusegs m LX_ERRNO [C4 errv] -> mem_inv ctusegs m -> tp = wz RATP ->
    crypto_statics m -> ap_img m ->
    In (poct, A, ASN1_STRING_SIZE) L -> In (pdata, D, len) L -> poct <> pdata ->
    rw_cells ctusegs m A (asn1_string_cells len V_ASN1_OCTET_STRING D 0) -> rw_cells ctusegs m D [CB (Z.to_nat len) src] -> 0 < len < 65536 ->
    bv_unsigned sp <= DER -> DER + 8 <= B -> rw_cells ctusegs m DER [C8 (wz 0)] -> DER mod 8 = 0 ->
    a0 = wz A -> a1 = wz DER ->
    k None = LUnr ->
    (forall p s' ms', flags_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s L lo B m A len D DER p s' ms' ->
                      implM ctusegs (interp (k (Some p))) s' Q ms') ->
    implM ctusegs (interp (LMalloc (der_hl len + len) k)) s Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 (wz ITEM_OCTET) (wz 0) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz ASN1_ITEM_FLAGS_I2D) fc None m (seg_rom ctusegs)).
  Proof using HM.
    intros until Q. intros HEAP AUX SPB B63 ST SP16 CEIL GLO LO ERR MI TP CS IMG HOIN HDIN NE HS HD LEN DERlo DERhi HDER DAL8 -> -> KN K.
    unfold asn1_string_cells in HS.
    unfold ASN1_ITEM_FLAGS_I2D_STACK, CRYPTO_MALLOC_STACK, RMALLOC_STACK, ASN1_ITEM_FLAGS_I2D, GLOBALS_TOP, MallocRep.wz in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (LH_block_range _ _ _ _ HEAP HOIN) as (BO0 & BO16 & _ & BOC & BOI). pose proof (LH_block_range _ _ _ _ HEAP HDIN) as (BD0 & BD16 & _ & BDC & BDI).
    cbn [blk_addr blk_size fst snd] in *. unfold ASN1_STRING_SIZE in *.
    pose proof (LH_disjoint _ _ _ (poct, A, 24) (pdata, D, len) HEAP HOIN HDIN ltac:(cbn; exact NE)) as DJOD. cbn [blk_addr blk_size blk_id fst snd] in DJOD.
    change (frozen (A + 24 <= D \/ D + len <= A)) in DJOD.
    pose proof (der_hl_range len ltac:(lia)) as HLR.
    unfold LX_ERRNO, RATP in ERR. change (3355176 - 164) with 3355012 in ERR.
    pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (DER, DER + 8)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
    assert (IT : item_oct m) by (apply item_oct_of_img; exact IMG).
    unfold implM. iprefix.
    carve_frame 80%nat ST. do 10 zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. sfalse.
    zstep. zstep. if_cases KC; zify_cond KC; [exfalso; rewrite ?unsigned_lit in KC by lia; change 7 with (Z.ones 3) in KC; rewrite Z.land_ones in KC by lia; clear - KC DAL8; Z.div_mod_to_equations; lia|]. clear KC.
    zstep. zstep. btaken.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -80)) = bv_unsigned sp + -80) by (apply unsigned_lit; lia).
    assert (IT1 : item_oct m1) by (eapply item_oct_agree; [exact IT| exact MU| constructor; [cbn; unfold ITEM_OCTET; lia| constructor; [cbn; unfold ITEM_OCTET; lia| constructor]]]).
    eapply ASN1_item_ex_i2d_fwd with (lo := lo) (PVAL := bv_unsigned sp + -72); [rewrite ESP; exact ST| assumption| unfold GLOBALS_TOP; lia| rewrite ESP; lia| exact IT1| lia|].
    intros m2 MU2 WM2 MI2 ST2. rewrite ESP in *.
    apply (fun H => rw_cells_transport _ _ _ _ _ _ H MU2 WM2) in FR; [| cbn; lia].
    apply (fun H => rw_cells_transport _ _ _ _ _ _ H MU2 WM2) in HS; [| cbn; lia].
    apply (fun H => rw_cells_transport _ _ _ _ _ _ H MU2 WM2) in HD; [| cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; cbn; lia].
    apply (fun H => rw_cells_transport _ _ _ _ _ _ H MU2 WM2) in HDER; [| cbn; lia].
    apply (fun H => rw_cells_transport _ _ _ _ _ _ H MU2 WM2) in ERR; [| cbn; lia].
    assert (IT2 : item_oct m2) by (eapply item_oct_agree; [exact IT1| exact MU2| constructor; [cbn; unfold ITEM_OCTET; lia| constructor]]).
    assert (MU' : munch [(bv_unsigned sp - 80 - 128 - 16, bv_unsigned sp); (DER, DER + 8)]%Z m m2).
    { eapply munch_trans; [eapply munch_weaken; [| exact MU]| eapply munch_weaken; [| exact MU2]]; unfold sub_fp; cbn [outside]; intros y Hy; lia. }
    assert (WM' : wmono ctusegs m m2) by (eapply wmono_trans; [exact WM| exact WM2]).
    clear MU WM MU2 WM2 MI IT IT1. rename MU' into MU. rename WM' into WM.
    pose proof (cells_pick m2 (bv_unsigned sp + -80) 8 [CB 8%nat _] (C8 (Z_to_bv 64 A)) _ FR eq_refl) as HPV.
    eapply evt_cut.
    { eapply asn1_i2d_ex_prim_len_spec with (lo := lo) (PVAL := bv_unsigned sp + -72) (A := A) (len := len) (D := D) (fl := 0);
        rewrite ?ESP; try eassumption; try reflexivity; try (unfold GLOBALS_TOP, EX_PRIM_STACK, ASN1_STRING_SIZE, MallocRep.wz; first [lia | reflexivity | f_equal; lia]).
      - replace (bv_unsigned sp + -72) with (bv_unsigned sp + -80 + 8) by lia. exact HPV.
      - exact (proj1 HS). }
    cbv beta. intros ms3 PO.
    destruct PO as (p5 & p6 & p7 & p11 & p12 & p13 & p14 & p15 & p16 & p17 & p28 & p29 & p30 & p31 & m3 & -> & MU3 & WM3 & MI3 & ST3). rewrite ESP in *.
    unfold EX_PRIM_STACK in MU3.
    replace (ret_pc (Z_to_bv 64 1135848)) with (Z_to_bv 64 1135848) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply (fun H => rw_cells_transport _ _ _ _ _ _ H MU3 WM3) in FR; [| cbn; lia].
    apply (fun H => rw_cells_transport _ _ _ _ _ _ H MU3 WM3) in HS; [| cbn; lia].
    apply (fun H => rw_cells_transport _ _ _ _ _ _ H MU3 WM3) in HD; [| cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; cbn; lia].
    apply (fun H => rw_cells_transport _ _ _ _ _ _ H MU3 WM3) in HDER; [| cbn; lia].
    apply (fun H => rw_cells_transport _ _ _ _ _ _ H MU3 WM3) in ERR; [| cbn; lia].
    assert (IT3 : item_oct m3) by (eapply item_oct_agree; [exact IT2| exact MU3| constructor; [cbn; unfold ITEM_OCTET; lia| constructor]]).
    assert (MU' : munch [(bv_unsigned sp - 80 - 128 - 16, bv_unsigned sp); (DER, DER + 8)]%Z m m3).
    { eapply munch_trans; [exact MU| eapply munch_weaken; [| exact MU3]]; unfold sub_fp; cbn [outside]; intros y Hy; lia. }
    assert (WM' : wmono ctusegs m m3) by (eapply wmono_trans; [exact WM| exact WM3]).
    clear MU WM MU3 WM3 MI2 IT2 ST2 HPV ST. rename MU' into MU. rename WM' into WM.
    (* [comment removed for export] *)
    zstep. zstep. sfalse. zstep. zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end.
    assert (HEAP4 : RHEAP s L m4).
    { eapply LH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
    assert (AUX4 : rauxv_ok m4 B).
    { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
    assert (AGL : agree_on (lib_addr []) m m4).
    { eapply agree_on_mono; [apply (agree_on_of_munch _ _ _ MU WM)|].
      intros a [Hx|(b & Hb & _)]; [| destruct Hb]. cbn. unfold LIBW_HX in Hx. cbn [rin_ivs fst snd] in Hx. lia. }
    assert (CS4 : crypto_statics m4) by (eapply (ApRep.crypto_statics_agree []); [exact CS| exact AGL]).
    assert (IMG4 : ap_img m4) by (eapply (ap_img_agree []); [exact IMG| exact AGL]).
    ihere. to_implM.
    eapply (CRYPTO_malloc_walk HM) with (B := B) (lo := lo) (errv := errv) (n := der_hl len + len);
      [exact HEAP4 | exact AUX4 | rewrite ESP; lia | rewrite ESP; exact ST3 | exact CEIL | unfold GLOBALS_TOP; lia
      | rewrite ESP; unfold CRYPTO_MALLOC_STACK, RMALLOC_STACK; lia | unfold LX_ERRNO, RATP; exact ERR | exact MI3 | exact TP
      | exact CS4 | reflexivity | lia | exact KN | ].
    intros p st1 ms1 PO. unfold calloc_post in PO. rewrite ?ESP in PO.
    destruct PO as (r5 & r6 & r7 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m5 & AD & errv5
                    & -> & MI5 & ST5 & ERR5 & AUX5 & HP & FA & SO & BR & HEAP5 & BLK).
    replace (ret_pc (Z_to_bv 64 0x115504)) with (Z_to_bv 64 0x115504) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    eapply implM_evt with (P := flags_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s L lo B m A len D DER p st1); [| intros ms' PO'; apply K; exact PO'].
    (* [comment removed for export] *)
    pose proof (agree_of_heap_pres _ _ _ _ HP) as AG.
    apply (rw_cells_agree _ _ _ _ _ AG) in FR; [| intros a Ha; left; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ AG) in HDER; [| intros a Ha; left; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ AG) in HS; [| intros a Ha; right; right; exists (poct, A, 24); split; [exact HOIN| cbn in Ha |- *; lia]].
    apply (rw_cells_agree _ _ _ _ _ AG) in HD; [| intros a Ha; right; right; exists (pdata, D, len); split; [exact HDIN| cbn [cells_size csize Nat.add] in Ha; rewrite Nat.add_0_r, Z2Nat.id in Ha by lia; cbn; lia]].
    assert (IMG5 : ap_img m5).
    { eapply (ap_img_agree []); [exact IMG4|]. intros a Ha Hl. apply (HP a Ha). eapply (lib_addr_rclient []); [intros b Hb; destruct Hb| exact Hl]. }
    pose proof (item_oct_of_img m5 IMG5) as IT5.
    pose proof BR as (BA0 & BA16 & _ & BAC & BAI).
    pose proof (LH_disjoint _ _ _ (p, AD, der_hl len + len) (poct, A, 24) HEAP5 ltac:(left; reflexivity) ltac:(right; exact HOIN)) as DJO.
    pose proof (LH_disjoint _ _ _ (p, AD, der_hl len + len) (pdata, D, len) HEAP5 ltac:(left; reflexivity) ltac:(right; exact HDIN)) as DJD.
    cbn [blk_addr blk_size blk_id fst snd] in DJO, DJD.
    pose proof (LH_nodup _ _ _ HEAP5) as ND5. cbn [map blk_id fst snd] in ND5. apply NoDup_cons_iff in ND5. destruct ND5 as [NIN _].
    assert (NEO : p <> poct) by (intros ->; apply NIN; apply in_map_iff; exists (poct, A, 24); split; [reflexivity| exact HOIN]).
    assert (NED : p <> pdata) by (intros ->; apply NIN; apply in_map_iff; exists (pdata, D, len); split; [reflexivity| exact HDIN]).
    specialize (DJO NEO). specialize (DJD NED).
    change (frozen (AD + (der_hl len + len) <= A \/ A + 24 <= AD)) in DJO. change (frozen (AD + (der_hl len + len) <= D \/ D + len <= AD)) in DJD.
    clear HEAP4 AUX4 CS4 IMG4 MI3 ST3 ERR AG IMG NIN.
    pose proof (munch_refl [(bv_unsigned sp - 80 - 128 - 16, bv_unsigned sp); (DER, DER + 8)]%Z m5) as MU5. pose proof (wmono_refl ctusegs m5) as WM5.
    unfold LX_ERRNO, RATP in ERR5. change (3355176 - 164) with 3355012 in ERR5.
    (* [comment removed for export] *)
    zstep. sfalse. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m6 end.
    pose proof BAI as BAI'. change (frozen (AD + (der_hl len + len) <= 0x10000 \/ 0x355000 <= AD)) in BAI'.
    assert (IT6 : item_oct m6).
    { eapply item_oct_agree; [exact IT5| exact MU5|]. constructor; [cbn; unfold ITEM_OCTET; lia|]. constructor; [cbn; unfold ITEM_OCTET; lia| constructor]. }
    clear BAI.
    destruct BLK as [junk0 BLK]. apply (fun H => rw_cells_transport _ _ _ _ _ _ H MU5 WM5) in BLK; [| cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; cbn; lia].
    eapply ASN1_item_ex_i2d_fwd with (lo := lo) (PVAL := bv_unsigned sp + -72); [rewrite ESP; exact ST5| exact MI5| unfold GLOBALS_TOP; lia| rewrite ESP; lia| exact IT6| lia|].
    intros m7 MU7 WM7 MI7 ST7. rewrite ESP in *.
    apply (fun H => rw_cells_transport _ _ _ _ _ _ H MU7 WM7) in FR; [| cbn; lia].
    apply (fun H => rw_cells_transport _ _ _ _ _ _ H MU7 WM7) in HS; [| cbn; lia].
    apply (fun H => rw_cells_transport _ _ _ _ _ _ H MU7 WM7) in HD; [| cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; cbn; lia].
    apply (fun H => rw_cells_transport _ _ _ _ _ _ H MU7 WM7) in HDER; [| cbn; lia].
    apply (fun H => rw_cells_transport _ _ _ _ _ _ H MU7 WM7) in ERR5; [| cbn; lia].
    apply (fun H => rw_cells_transport _ _ _ _ _ _ H MU7 WM7) in BLK; [| cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; cbn; lia].
    assert (IT7 : item_oct m7) by (eapply item_oct_agree; [exact IT6| exact MU7| constructor; [cbn; unfold ITEM_OCTET; lia| constructor]]).
    assert (MU' : munch [(bv_unsigned sp - 80 - 128 - 16, bv_unsigned sp); (DER, DER + 8)]%Z m5 m7).
    { eapply munch_trans; [exact MU5| eapply munch_weaken; [| exact MU7]]; unfold sub_fp; cbn [outside]; intros y Hy; lia. }
    assert (WM' : wmono ctusegs m5 m7) by (eapply wmono_trans; [exact WM5| exact WM7]).
    clear MU5 WM5 MU7 WM7 MI5 ST5 IT5 IT6. rename MU' into MU5. rename WM' into WM5.
    (* [comment removed for export] *)
    pose proof (cells_at_wf _ _ _ _ (proj1 HD)) as [SLEN _]. cbn in SLEN.
    pose proof (rw_cells_bytes_at _ _ _ _ HD) as SRC. cbn [cells_bytes cbytes] in SRC. rewrite app_nil_r in SRC.
    pose proof (cb_split2 m7 AD (der_hl len) len junk0 BLK ltac:(lia) ltac:(lia)) as [HP1 HP2].
    pose proof (cells_pick m7 (bv_unsigned sp + -80) 8 [C8 (wz AD)] (C8 (Z_to_bv 64 A)) _ FR eq_refl) as HPV.
    pose proof (cells_pick_rw m7 (bv_unsigned sp + -80) 0 [] (C8 (wz AD)) _ FR eq_refl) as HPP. rewrite Z.add_0_r in HPP.
    eapply evt_cut.
    { eapply asn1_i2d_ex_prim_write_spec with (lo := lo) (PVAL := bv_unsigned sp + -72) (PP := bv_unsigned sp + -80) (A := A) (len := len) (D := D) (fl := 0) (P := AD)
                                            (src := src) (j1 := firstn (Z.to_nat (der_hl len)) junk0) (j2 := skipn (Z.to_nat (der_hl len)) junk0);
        rewrite ?ESP; try eassumption; try reflexivity; try (unfold GLOBALS_TOP, EX_PRIM_STACK, ASN1_STRING_SIZE, MallocRep.wz; first [lia | reflexivity | f_equal; lia]).
      - pose proof DJD as X2; unfold frozen in X2; lia.
      - pose proof DJO as X1; unfold frozen in X1; unfold ASN1_STRING_SIZE; lia.
      - pose proof BAI' as X3; unfold frozen in X3; lia.
      - replace (bv_unsigned sp + -72) with (bv_unsigned sp + -80 + 8) by lia. exact HPV.
      - exact (proj1 HS). }
    cbv beta. intros ms8 PO.
    destruct PO as (q5 & q6 & q7 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q28 & q29 & q30 & q31 & m8 & -> & MU8 & WM8 & MI8 & ST8 & HPP8 & [hb HB1] & HB2).
    rewrite ESP in *. unfold EX_PRIM_STACK in MU8.
    replace (ret_pc (Z_to_bv 64 1135912)) with (Z_to_bv 64 1135912) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    (* [comment removed for export] *)
    change ([C8 (wz AD); C8 (Z_to_bv 64 A); C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
      with ([C8 (wz AD)] ++ [C8 (Z_to_bv 64 A); C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) in FR.
    apply rw_cells_app in FR. destruct FR as [_ FR]. cbn [cells_size csize Nat.add] in FR.
    apply (fun H => rw_cells_transport _ _ _ _ _ _ H MU8 WM8) in FR; [| cbn; lia].
    assert (FR' : rw_cells ctusegs m8 (bv_unsigned sp + -80) ([C8 (wz (AD + der_hl len + len))] ++ [C8 (Z_to_bv 64 A); C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])).
    { apply rw_cells_app. split; [exact HPP8| exact FR]. }
    clear FR HPP8. cbn [app] in FR'. rename FR' into FR.
    apply (fun H => rw_cells_transport _ _ _ _ _ _ H MU8 WM8) in HS; [| cbn; pose proof DJO as X1; unfold frozen in X1; lia].
    apply (fun H => rw_cells_transport _ _ _ _ _ _ H MU8 WM8) in HDER; [| cbn; lia].
    apply (fun H => rw_cells_transport _ _ _ _ _ _ H MU8 WM8) in ERR5; [| cbn; pose proof BAI' as X3; unfold frozen in X3; lia].
    assert (MU' : munch [(bv_unsigned sp - 80 - 128 - 16, bv_unsigned sp); (DER, DER + 8); (AD, AD + (der_hl len + len))]%Z m5 m8).
    { eapply munch_trans; [eapply munch_weaken; [| exact MU5]| eapply munch_weaken; [| exact MU8]]; unfold sub_fp; cbn [outside]; intros y Hy; lia. }
    assert (WM' : wmono ctusegs m5 m8) by (eapply wmono_trans; [exact WM5| exact WM8]).
    clear MU5 WM5 MU8 WM8 MI7 ST7 IT7 HPV HPP HP1 HP2 BLK HD SRC. rename MU' into MU5. rename WM' into WM5.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. do 8 zstep. zstep. release_frame FR ST8 (bv_unsigned sp). zstep.
    apply evt_done. unfold flags_post, MallocRep.wz.
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => rename mx into m9 end.
    do 14 eexists. exists m9, AD, errv5. split; [reflexivity|].
    split; [assumption|]. split; [exact ST8|]. split; [unfold LX_ERRNO, RATP; exact ERR5|].
    (* [comment removed for export] *)
    pose proof (LH_nodup _ _ _ HEAP5) as ND5.
    assert (DJL : forall b, In b L -> AD + (der_hl len + len) <= blk_addr b \/ blk_addr b + blk_size b <= AD).
    { intros b Hb. pose proof (LH_disjoint _ _ _ (p, AD, der_hl len + len) b HEAP5 ltac:(left; reflexivity) ltac:(right; exact Hb)) as DJ.
      cbn [blk_addr blk_size blk_id fst snd] in DJ. apply DJ. intros E. cbn [map blk_id fst snd] in ND5. apply NoDup_cons_iff in ND5. apply (proj1 ND5). rewrite E. apply in_map. exact Hb. }
    assert (CLI0 : forall a, 0 <= a < 2^64 -> rclient_addr L (bv_unsigned sp) a -> ~ (DER <= a < DER + 8) ->
                   outside [(bv_unsigned sp - 80 - 128 - 16, bv_unsigned sp); (DER, DER + 8)] a).
    { intros a Ha Hc Hd. cbn. apply rclient_addr_cases in Hc. destruct Hc as [Hc|[Hc|(b' & Hb' & Hr)]]; [split; [lia| split; [lia| exact I]] | split; [lia| split; [lia| exact I]] |].
      pose proof (LH_block_range _ _ _ _ HEAP Hb') as (_ & _ & _ & B3' & _). split; [lia| split; [lia| exact I]]. }
    assert (CLI5 : forall a, 0 <= a < 2^64 -> rclient_addr L (bv_unsigned sp) a -> ~ (DER <= a < DER + 8) ->
                   outside [(bv_unsigned sp - 80 - 128 - 16, bv_unsigned sp); (DER, DER + 8); (AD, AD + (der_hl len + len))] a).
    { intros a Ha Hc Hd. cbn. apply rclient_addr_cases in Hc. destruct Hc as [Hc|[Hc|(b' & Hb' & Hr)]];
        [split; [lia| split; [lia| split; [lia| exact I]]] | split; [lia| split; [lia| split; [pose proof BAI' as X3; unfold frozen in X3; lia| exact I]]] |].
      pose proof (LH_block_range _ _ _ _ HEAP Hb') as (_ & _ & _ & B3' & _). pose proof (DJL b' Hb'). split; [lia| split; [lia| split; [lia| exact I]]]. }
    split. { eapply rauxv_ok_frame; [exact AUX5| exact MU5| exact WM5|]. pose proof BAI' as X3; unfold frozen in X3.
             constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
    split. { intros a Ha Hc Hd. cbn [fst snd] in Hd.
             assert (E1 : m4 (wa a) = m (wa a) /\ (wview ctusegs m (wa a) <> None -> wview ctusegs m4 (wa a) <> None)).
             { split; [apply MU; unfold wa; rewrite unsigned_lit by lia; apply CLI0; assumption|]. intros Hw. apply WM. exact Hw. }
             assert (E2 : m5 (wa a) = m4 (wa a) /\ (wview ctusegs m4 (wa a) <> None -> wview ctusegs m5 (wa a) <> None)).
             { apply (HP a Ha). pose proof Hc as Hc'. unfold rclient_addr in Hc'. destruct Hc' as [Hc'|[Hc'|Hc']]; [left; lia| right; left; exact Hc'| right; right; exact Hc']. }
             assert (E3 : m9 (wa a) = m5 (wa a) /\ (wview ctusegs m5 (wa a) <> None -> wview ctusegs m9 (wa a) <> None)).
             { split; [apply MU5; unfold wa; rewrite unsigned_lit by lia; apply CLI5; assumption|]. intros Hw. apply WM5. exact Hw. }
             destruct E1 as [E1 W1]. destruct E2 as [E2 W2]. destruct E3 as [E3 W3]. split; [congruence| auto]. }
    split; [exact FA|]. split; [exact SO|]. split; [exact BR|].
    split. { eapply LH_frame; [exact HEAP5| exact MU5| exact WM5|].
             constructor; [apply W_ok_stack; cbn; lia|]. constructor; [apply W_ok_stack; cbn; lia|].
             constructor; [eapply (W_ok_block _ (p, AD, der_hl len + len)); [left; reflexivity| cbn; lia| cbn; lia]| constructor]. }
    split; [exact HDER|]. split; [exact HS|].
    exists (hb ++ src). replace (der_hl len + len) with (der_hl len + len) by lia. eapply cb_join2; [exact HB1| exact HB2| lia| lia].
  Qed.
End Proofs.
End WithCeiling0.
