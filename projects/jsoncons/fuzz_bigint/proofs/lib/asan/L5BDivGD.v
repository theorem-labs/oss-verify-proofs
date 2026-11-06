(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA IcptIfaceAB0 LibIface
     AsanAcct AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5Words L5LazyA L5DefsAB0
     L5CoreAB0 L5CoreSpecsAB0 L5StepAB0 L5BCmp L5CoreBB0 L5BDetailG L5BFrameK L5DivKitAB0 L5DivSpecsAB0 L5OpmodSpecsAB0 L5DivLeafSpecsAB0 L5DivInnerSpecsAB0 L5BCopyAS L5BDivH L5BDivT L5BDivD L5BDivE L5BDivEA L5BDivHC L5BDivHA L5BDivHO L5BDivHL L5BDivHM L5BDivPG1 L5BDivPG2 L5BDivGL L5BDivGA L5BDivGB L5BDivGC L5BRed.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Bo0_code_92368_93368.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5ADVGD.
Import L5A. Import L5CA. Import L5CSA. Import L5W. Import L5SA. Import L5CB. Import L5ADH. Import L5ADVH. Import L5ADVT. Import L5ADVD. Import L5ADVE. Import L5ADVEA. Import L5ADVHC. Import L5ADVHA. Import L5ADVHO. Import L5ADIVPG1. Import L5ADIVPG2. Import L5ADVGA. Import L5ADVGB. Import L5ADVGC.
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Local Ltac inl := apply L5K.in_b; vm_compute; reflexivity.
Local Ltac blia := keep_arith; first [ (repeat match goal with H : _ \/ _ |- _ => clear H end); lia
                                     | match goal with H : _ \/ _ |- _ => clear_disj_but H; destruct H; lia end ].
Local Ltac asm := match goal with H : ?T |- ?G => constr_eq T G; exact H end.
Local Ltac sc := first [ asm | rk | gmem | (arith_goal; first [asm | blia]) | assumption ].

Section WithIface.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : as0_layout L C.
Hypothesis HIok : asan_iface_ok L ar C SCFG HI.

Section DIV.
Variables (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet) (LB : list (Z * Z)) (FF LK : list fframe) (A : list (Z * Z))
          (E SCRD F fl ro r : Z) (LK2 : list fframe) (M2 : word -> option byte) (model2 : Model) (cr2 : credit).
Local Notation SPA := (E - 384).
Hypothesis G : L5AFK.gctx L ar HI LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2.
Hypothesis ER : 140735332487680 <= E <= 140737488355328.
Hypothesis EA : aligned E 32.
Hypothesis HK : K [].
Hypothesis G4 : getr R (reg 4) = Z_to_bv 64 (hl_tp L).
Hypothesis HSCR : 384 + 4784 <= SCRD.
Hypothesis HSSH : L5OMA.stksh ar M (E - SCRD).
Hypothesis HSC8 : SCRD mod 8 = 0.
Hypothesis FFR1 : ffrk 1 FF LK 4.
Hypothesis FFRS : ffrs FF E.
Hypothesis Hdel : opdel_sized_spec L ar HI.
Hypothesis Hasg : assign_spec L ar HI.
Hypothesis RA : L5.ra_ok r.
Hypothesis UR1 : U R 1 = r.
Hypothesis G2 : getr R (reg 2) = Z_to_bv 64 E.
Local Notation binv := (L5AFK.binv L ar HI M model LB FF LK A E SCRD SPA (down E F ro R) F 3).
Local Notation FF' := ((F, 3, SPA + 32) :: FF).
Local Notation SH := (F / 8 + 2147450880).
Local Notation offx := (L5ADVEA.offx L ar FF E F).
Local Notation tob := (L5ADVEA.tob).
Local Notation HSCR0 := (L5ADVGA.HSCR0 SCRD HSCR).

Local Ltac open_ctx BI :=
  let PF := fresh "PF" in
  pose proof (pf_of_binv L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G _ _ _ _ _ _ _ BI) as PF;
  destruct PF as (W384 & IMGC & CSB & CUAR & FDEFv & FWv & FSHWv & FLCv & FLWv);
  pose proof (NUM L ar HI R LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER) as ((FRG & FLRG & ERG) & FRP & FLRP & ALF & FBIG & FLBIG & FLA & SFA & SFLA & SFB);
  destruct (L5AFK.vis_facts L ar C HI LY HIok M model LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2 G _ _ _ _ _ _ _ BI) as (_ & OWNv & _ & (_ & _ & FV & SV & SHV));
  change (ff_bytes 3) with 512 in FV; change (ff_bytes 3 / 8) with 64 in SHV.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma g11 (fx : FPState) Rc Mc modelc W BX LKc crc Ac qo (bq : L5.bigobj) wq :
  binv W BX Mc modelc LKc crc Ac -> rinvD R E Rc ->
  aobj FF qo 32 -> tob (BX ++ LB) Mc qo bq wq -> (forall a, qo <= a < qo + 16 -> ~ L5.outside W a) ->
  getr Rc (reg 18) = Z_to_bv 64 SH -> (forall a, in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> L5.outside W a) ->
  L5.u64_at RSEGS Mc (E - 296) qo -> L5.u64_at RSEGS Mc (E - 360) F -> L5.u64_at RSEGS Mc (E - 336) F -> L5.u64_at RSEGS Mc (E - 304) (F + 32) -> L5.u64_at RSEGS Mc (E - 280) (F + 96) ->
  (forall (fx1 : FPState) R1 M1 model1,
      binv W BX M1 model1 LKc crc Ac -> rinvD R E R1 ->
      getr R1 (reg 18) = Z_to_bv 64 SH -> getr R1 (reg 24) = Z_to_bv 64 (F + 32) -> getr R1 (reg 25) = Z_to_bv 64 (F + 96) -> getr R1 (reg 20) = Z_to_bv 64 qo ->
      getr R1 (reg 22) = Z_to_bv 64 F -> getr R1 (reg 27) = Z_to_bv 64 F ->
      (forall a, 0 <= a < 2 ^ 64 -> ~ (qo <= a < qo + 16) -> ~ (SPA - 16 <= a < SPA) -> M1 (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)) ->
      L5.big_at RSEGS M1 qo (L5.BO (if Nat.eqb (L5W.rlen wq) 0 then Z.land (L5.bo_fb bq) 253 else L5.bo_fb bq) (L5W.rlen wq) (L5.bo_st bq)) ->
      srealizes RSEGS SCFG (cfg (fx:=fx1) R1 0x93474 M1 model1) K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc 0x93458 Mc modelc) K.
Proof.
  intros BI RI AOQ (OBQ & OLQ & SZQ & INQ) WRO X18 NW S104 S72 S56 S88 S80 KF.
  pose proof (arg_facts L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G W BX Mc modelc LKc crc Ac qo BI AOQ SZQ)
    as ((ORP & ORG & O8) & OBIG & OZv & OWv & OFR & OF & OSH & SOF & SOSH & SOFR & XB & XC & OCL).
  assert (AOQ' : aobj FF' qo 32) by (apply aobj_cons; exact AOQ).
  pose proof BI as (B1 & _ & _ & _ & _ & B6 & _).
  pose proof (aobj_facts L ar C HI LY HIok (BX ++ LB) FF' LKc crc Ac Mc modelc qo 32 0 0 B1 AOQ' ltac:(clear; lia) ltac:(reflexivity)) as ((OLO & OCE & _) & _).
  pose proof (vis_pack L ar C HI LY HIok (BX ++ LB) FF' LKc crc Ac Mc modelc B1) as (_ & VIS & _).
  pose proof (big_vis L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G W BX Mc modelc LKc crc Ac qo bq BI AOQ SZQ OBQ) as OBv.
  pose proof (one_le_cap Mc qo bq OBQ) as OCQ.
  pose proof (dreg_facts L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G W BX Mc modelc LKc crc Ac qo bq wq (L5.bo_cap bq) BI AOQ' (conj OBQ (conj OLQ (conj SZQ INQ)))
                OCQ ltac:(unfold L5.bo_cap; clear; lia)) as ((QF1 & QF2 & QF3 & QF4) & QNS & QOI & QZ & QDEF & QWR & QVIS).
  cbv zeta in *.
  open_ctx BI. pose proof RI as (X2 & X8 & X9 & X3 & X4 & XSB).
  assert (SLO : ahl_ceil ar + 4096 + SCRD <= E) by (destruct G as [_ _ SLO0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _]; exact SLO0).
  set (MV := mrestrict (ahid Ac modelc) Mc) in *.
  assert (ER' : 140735332487616 <= E <= 140737488355328) by (clear - ER; lia).
  assert (FR' : 4096 <= F <= 140737488354816) by (clear - FRP; lia).
  assert (QOR : 0 <= qo <= 18446744073709551615) by (clear - ORP ORG; lia).
  assert (FV8 : forall a v, L5.u64_at RSEGS Mc a v -> SPA <= a -> a + 8 <= E -> L5.u64_at RSEGS MV a v).
  { intros a v Hc H1 H2. exact (frm_vis L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER W BX Mc modelc LKc crc Ac a v BI Hc H1 H2). }
  pose proof (FV8 _ _ S104 ltac:(clear; lia) ltac:(clear; lia)) as S104v. pose proof (FV8 _ _ S56 ltac:(clear; lia) ltac:(clear; lia)) as S56v. pose proof (FV8 _ _ S72 ltac:(clear; lia) ltac:(clear; lia)) as S72v.
  pose proof (FV8 _ _ S88 ltac:(clear; lia) ltac:(clear; lia)) as S88v. pose proof (FV8 _ _ S80 ltac:(clear; lia) ltac:(clear; lia)) as S80v.
  assert (OLv : L5C.obj_limbs RSEGS MV bq wq).
  { destruct OLQ as (OL1 & OL2 & OL3). split. exact OL1. split. exact OL2. destruct bq as [fb len sto]. cbn [L5.bo_st L5.bo_len L5.bo_cap L5.bo_data] in *. destruct sto as [v0 v1|cap q]. exact OL3.
    destruct OBQ as (_ & _ & _ & (_ & _ & _ & LC & CR & Q8 & Q4096 & Q47 & _)). cbn [L5.bo_len] in LC.
    eapply L5C.limbs_at_agree. 4: exact OL3. 2: clear - Q4096; lia. 2: rewrite OL1; clear - Q47 LC CR; lia.
    intros i Hi. rewrite OL1 in Hi. apply QVIS. unfold L5.bo_data, L5.bo_cap; cbn [L5.bo_st]. clear - Hi LC; lia. }
  pose proof (v5G11_conc fx Rc MV (fun j => match j with 2%nat => E | 35%nat => qo | 40%nat => F | 58%nat => U Rc 1 | _ => 0 end)) as P. cbn beta iota in P.
  feed P ltac:(first [apply UR | apply U_to | sc ]).
  destruct P as (fx1 & R1 & M1v & _ & _ & pEQ & (pMS & pKS & p1 & p10 & p20 & p22 & p24 & p25 & p27)).
  assert (EQM : M1v = MV) by (apply mem_eq_of_agree; exact pEQ). rewrite EQM in pMS. clear EQM pEQ M1v.
  assert (p18 : getr R1 (reg 18) = Z_to_bv 64 SH) by (rewrite (pKS 18%nat) by inl; exact X18).
  assert (SA16 : (E - 384) mod 16 = 0). { clear - EA. unfold aligned in EA. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  assert (W16 : L5.writable RSEGS MV (SPA - 16) 16).
  { apply (L5C.writable_of_defined RSEGS). 2: clear - ER; lia. 2: clear - ER; lia.
    apply (proj2 (defined_vis (ahid Ac modelc) Mc (SPA - 16) 16 (VIS (SPA - 16) 16 ltac:(clear - SLO HSCR; lia) ltac:(clear - ER; lia)))).
    destruct B6 as (_ & _ & _ & _ & DSCR & _). eapply L5.defined_sub. exact DSCR. clear - HSCR; lia. clear; lia. }
  assert (R12 : getr R1 (reg 2) = Z_to_bv 64 SPA) by (rewrite (pKS 2%nat) by inl; exact X2).
  assert (DOB : L5.bo_data qo bq + 8 * L5.bo_cap bq <= qo \/ qo + 16 <= L5.bo_data qo bq).
  { destruct bq as [fb len sto]. unfold L5.bo_data, L5.bo_cap. cbn [L5.bo_st] in *. destruct sto as [v0 v1|cap q]. right; clear; lia.
    destruct (L5ADVEA.blk_frame L ar C HI HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G W BX Mc modelc LKc crc Ac q (8 * cap) qo BI (INQ cap q eq_refl)) as (_ & Y & _).
    specialize (Y AOQ'). clear - Y; lia. }
  destruct (L5ARED.reduce_run fx1 R1 MV qo SPA 0x93474 bq wq p10 p1 ltac:(split; [clear; lia | reflexivity]) R12 ltac:(clear - ER; lia) SA16 W16 IMGC CSB CUAR
              ltac:(clear - OLO ORP; lia) O8 OBIG ltac:(right; clear - OCE SLO HSCR; lia) ltac:(unfold SB; exact OZv) OWv OBv OLv)
    as (fx2 & R2 & M2v & rMS & (rOB & rKS & rR2 & rR10 & rFR & rMG)).
  { cbv zeta. unfold L5ADVGL.nsh in QNS. split. exact QNS. split. right; clear - QF3 SLO HSCR; lia. split. clear - DOB; lia.
    split. exact QWR. split. unfold SB. exact QZ. destruct bq as [fb len sto]. unfold L5.bo_cap. cbn [L5.bo_st] in *. destruct sto. clear; lia.
    destruct OBQ as (_ & _ & _ & (_ & _ & _ & _ & CR & _)). clear - CR; lia. }
  set (Wp := fun a => (qo <= a < qo + 16) \/ (SPA - 16 <= a < SPA)).
  apply (L5DKA.bstage L ar C HI LY HIok M model LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2 G W _ Mc modelc LKc crc Ac fx fx2 Rc 0x93458 R2 0x93474 M2v Wp K BI
           (msteps_trans _ _ _ _ pMS rMS) rMG).
  { intros a Ha Hn. subst Wp; cbn beta in Hn. apply rFR. exact Ha. clear - Hn; lia. clear - Hn; lia. }
  { intros a Ha Wa. subst Wp; cbn beta in Wa. destruct Wa as [Wa|Wa].
    - destruct (OCL a ltac:(clear - Wa; lia)) as (C1 & C2 & C3 & C4). split. exact C4. split. split. exact C1. exact C2. intros _. apply WRO. exact Wa.
    - eapply L5ADVHC.wp_scratch; first [exact LY | exact HIok | exact G | exact ER | exact EA | exact HSCR0 | exact BI | exact HSSH | exact NW | exact HSC8 | idtac]. clear - Wa HSCR; lia. }
  intros M1 model1 BI1 AH1 VIS1 MGM1 FRM1.
  assert (KS2 : forall x, In x [3; 4; 8; 9; 18; 20; 22; 23; 24; 25; 27]%nat -> getr R2 (reg x) = getr R1 (reg x)).
  { intros x Hx. apply rKS. revert Hx. apply (L5K.incl_b [3; 4; 8; 9; 18; 20; 22; 23; 24; 25; 27]%nat). vm_compute; reflexivity. }
  apply (KF fx2 R2 M1 model1 BI1).
  - split. exact rR2. split. rewrite (KS2 8%nat) by inl. rewrite (pKS 8%nat) by inl. exact X8.
    split. rewrite (KS2 9%nat) by inl. rewrite (pKS 9%nat) by inl. exact X9.
    split. rewrite (KS2 3%nat) by inl. rewrite (pKS 3%nat) by inl. exact X3. split. rewrite (KS2 4%nat) by inl. rewrite (pKS 4%nat) by inl. exact X4.
    rewrite (KS2 23%nat) by inl. rewrite (pKS 23%nat) by inl. exact XSB.
  - rewrite (KS2 18%nat) by inl. exact p18.
  - rewrite (KS2 24%nat) by inl. exact p24.
  - rewrite (KS2 25%nat) by inl. exact p25.
  - rewrite (KS2 20%nat) by inl. exact p20.
  - rewrite (KS2 22%nat) by inl. exact p22.
  - rewrite (KS2 27%nat) by inl. exact p27.
  - intros a Ha N1 N2'. apply FRM1. exact Ha. subst Wp; cbn beta. clear - N1 N2'. lia.
  - pose proof (aobj_facts L ar C HI LY HIok (BX ++ LB) FF' LKc crc Ac Mc modelc qo 32 0 0 B1 AOQ' ltac:(clear; lia) ltac:(reflexivity)) as (_ & _ & _ & OVIS & _).
    apply (proj1 (L5ADVHM.big_at_vis (ahid Ac modelc) M1 qo _ OVIS ltac:(clear - ORP; lia) ltac:(clear - ORP; lia))). rewrite VIS1. exact rOB.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma g12_run (fx : FPState) Rc MV to qo qn rd sd xv fb : rinvD R E Rc -> pf E F fl MV -> getr Rc (reg 20) = Z_to_bv 64 qo -> ARGF E F MV qo ->
  L5.u8_at RSEGS MV qo fb -> 0 <= fb < 256 -> 0 <= ro < 2 ^ 64 -> L5.u64_at RSEGS MV (E - 288) ro ->
  L5.u64_at RSEGS MV (E - 320) (qo / 8 + 2147450880) -> L5.u64_at RSEGS MV (E - 264) to -> 0 <= to < 2 ^ 64 ->
  L5.u64_at RSEGS MV (E - 312) qn -> 0 <= qn <= 1 -> L5.u64_at RSEGS MV (E - 344) rd -> (rd = 0 \/ rd = 1) ->
  (rd = 1 -> L5.u32_at RSEGS MV (E - 220) xv /\ 0 <= xv <= 63 /\ L5.u64_at RSEGS MV (E - 376) sd /\ 0 <= sd < 2 ^ 64) ->
  exists (fx' : FPState) R' M', msteps RSEGS (st fx Rc 0x93474 MV) (st fx' R' (if rd =? 1 then L5DSA.UNNORM else 0x934dc) M') /\ mem_grows MV M'
    /\ (forall a, 0 <= a < 2 ^ 64 -> a <> qo -> M' (Z_to_bv 64 a) = MV (Z_to_bv 64 a))
    /\ (forall x, In x [2; 3; 4; 8; 9; 18; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R' (reg x) = getr Rc (reg x))
    /\ getr R' (reg 19) = Z_to_bv 64 ro /\ L5.u8_at RSEGS M' qo (Z.lor (Z.land fb 253) (2 * qn))
    /\ (rd = 1 -> getr R' (reg 1) = Z_to_bv 64 0x934bc /\ getr R' (reg 10) = Z_to_bv 64 to /\ getr R' (reg 11) = Z_to_bv 64 ro /\ getr R' (reg 12) = Z_to_bv 64 xv /\ getr R' (reg 13) = Z_to_bv 64 sd).
Proof.
  intros RI PF X20 ((ORP & ORG & O8) & OBIG & OZ & OW & OFR & OF & OSH & SOF & SOSH & SOFR) O0 FBR ROR S96 S64 S120 TOR S72 QNR S40 RDR XSD.
  unfold pf in PF. destruct PF as (W352 & IMGC & CSB & CUAR & FDEFv & FWv & FSHWv & FLCv & FLWv).
  pose proof (NUM L ar HI R LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER) as ((FRG & FLRG & ERG) & FRP & FLRP & ALF & FBIG & FLBIG & FLA & SFA & SFLA & SFB).
  pose proof RI as (X2 & X8 & X9 & X3 & X4 & XSB).
  assert (ER' : 140735332487616 <= E <= 140737488355328) by (clear - ER; lia). assert (EAL : L5ADIVPG2.aligned E 32) by exact EA.
  assert (OAL : L5ADIVPG2.aligned qo 8) by exact O8.
  assert (VR : 0 <= fb <= 255 /\ 0 <= ro <= 18446744073709551615 /\ 0 <= to <= 18446744073709551615 /\ 0 <= qn < 2 ^ 64 /\ 0 <= fb < 2 ^ 64)
    by (clear - FBR ROR TOR QNR; lia).
  destruct VR as (V1 & V2 & V4 & V5 & V6).
  assert (M2Q : (2 * qn) mod 2 ^ 64 = 2 * qn) by (apply Z.mod_small; clear - QNR; lia).
  destruct RDR as [RD0|RD1]; subst rd; cbn [Z.eqb Pos.eqb].
  - assert (RDX : 0 <= 0 <= 0 /\ 0 <= 0 < 2 ^ 64) by (clear; lia). destruct RDX as [RDX RDX'].
    pose proof (v5G12n_conc fx Rc MV (fun j => match j with 2%nat => E | 33%nat => to | 35%nat => qo | 36%nat => ro | 37%nat => 0 | 40%nat => F | 57%nat => qn | 58%nat => U Rc 1 | 60%nat => fb | _ => 0 end)) as P.
    cbn beta iota in P.
    feed P ltac:(first [apply UR | apply U_to | sc ]).
    destruct P as (fx1 & R1 & M1v & pMG & _ & pFZ & (pMS & pKS & _ & _ & _ & p19 & pC)).
    exists fx1, R1, M1v. split. exact pMS. split. exact pMG.
    split. { intros a Ha Hn. apply pFZ. exact Ha. clear - Hn; lia. }
    split. { intros x Hx. apply pKS. revert Hx. apply (L5K.incl_b [2; 3; 4; 8; 9; 18; 20; 21; 22; 23; 24; 25; 26; 27]%nat). vm_compute; reflexivity. }
    split. exact p19. split. { rewrite M2Q in pC. exact pC. } intros X. exfalso. clear - X. lia.
  - destruct (XSD eq_refl) as (SX & XVR & S16 & SDR).
    assert (RDX : 1 <= 1 <= 1 /\ 0 <= 1 < 2 ^ 64 /\ 0 <= xv < 2 ^ 64 /\ 0 <= sd <= 18446744073709551615) by (clear - XVR SDR; lia). destruct RDX as (RDX & RDX' & XVR' & SDR').
    pose proof (v5G12u_conc fx Rc MV (fun j => match j with 2%nat => E | 33%nat => to | 35%nat => qo | 36%nat => ro | 37%nat => 1 | 40%nat => F | 57%nat => qn | 58%nat => U Rc 1 | 60%nat => fb | 63%nat => sd
                                               | 88%nat => xv | _ => 0 end)) as P.
    cbn beta iota in P.
    feed P ltac:(first [apply UR | apply U_to | sc ]).
    destruct P as (fx1 & R1 & M1v & pMG & _ & pFZ & (pMS & pKS & p1 & p10 & p11 & p12 & p13 & p19 & pC)).
    exists fx1, R1, M1v. split. exact pMS. split. exact pMG.
    split. { intros a Ha Hn. apply pFZ. exact Ha. clear - Hn; lia. }
    split. { intros x Hx. apply pKS. revert Hx. apply (L5K.incl_b [2; 3; 4; 8; 9; 18; 20; 21; 22; 23; 24; 25; 26; 27]%nat). vm_compute; reflexivity. }
    split. exact p19. split. { rewrite M2Q in pC. exact pC. } intros _. split. exact p1. split. exact p10. split. exact p11. split. exact p12. exact p13.
Qed.

Lemma g12 (fx : FPState) Rc Mc modelc W BX LKc crc Ac to qo qn rd sd xv fb :
  binv W BX Mc modelc LKc crc Ac -> rinvD R E Rc -> getr Rc (reg 20) = Z_to_bv 64 qo ->
  aobj FF qo 32 -> shadow_zero Mc qo 4 -> L5.u8_at RSEGS Mc qo fb -> 0 <= fb < 256 -> ~ L5.outside W qo -> 0 <= ro < 2 ^ 64 ->
  L5.u64_at RSEGS Mc (E - 288) ro -> L5.u64_at RSEGS Mc (E - 320) (qo / 8 + 2147450880) -> L5.u64_at RSEGS Mc (E - 264) to -> 0 <= to < 2 ^ 64 ->
  L5.u64_at RSEGS Mc (E - 312) qn -> 0 <= qn <= 1 -> L5.u64_at RSEGS Mc (E - 344) rd -> (rd = 0 \/ rd = 1) ->
  (rd = 1 -> L5.u32_at RSEGS Mc (E - 220) xv /\ 0 <= xv <= 63 /\ L5.u64_at RSEGS Mc (E - 376) sd /\ 0 <= sd < 2 ^ 64) ->
  (forall (fx1 : FPState) R1 M1 model1,
      binv W BX M1 model1 LKc crc Ac -> rinvD R E R1 ->
      (forall x, In x [3; 4; 18; 20; 21; 22; 24; 25; 26; 27]%nat -> getr R1 (reg x) = getr Rc (reg x)) ->
      getr R1 (reg 19) = Z_to_bv 64 ro ->
      (forall a, 0 <= a < 2 ^ 64 -> a <> qo -> M1 (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)) ->
      L5.u8_at RSEGS M1 qo (Z.lor (Z.land fb 253) (2 * qn)) ->
      (rd = 1 -> getr R1 (reg 1) = Z_to_bv 64 0x934bc /\ getr R1 (reg 10) = Z_to_bv 64 to /\ getr R1 (reg 11) = Z_to_bv 64 ro /\ getr R1 (reg 12) = Z_to_bv 64 xv /\ getr R1 (reg 13) = Z_to_bv 64 sd) ->
      srealizes RSEGS SCFG (cfg (fx:=fx1) R1 (if rd =? 1 then L5DSA.UNNORM else 0x934dc) M1 model1) K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc 0x93474 Mc modelc) K.
Proof.
  intros BI RI X20 AOQ SZQ O0 FBR WQ ROR S96 S64 S120 TOR S72 QNR S40 RDR XSD KF.
  pose proof (arg_facts L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G W BX Mc modelc LKc crc Ac qo BI AOQ SZQ)
    as ((ORP & ORG & O8) & OBIG & OZv & OWv & OFR & OF & OSH & SOF & SOSH & SOFR & U8V & U64V & OCL).
  pose proof (pf_of_binv L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G W BX Mc modelc LKc crc Ac BI) as PF.
  open_ctx BI.
  set (MV := mrestrict (ahid Ac modelc) Mc) in *.
  assert (FV8 : forall a v, L5.u64_at RSEGS Mc a v -> SPA <= a -> a + 8 <= E -> L5.u64_at RSEGS MV a v).
  { intros a v Hc H1 H2. exact (frm_vis L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER W BX Mc modelc LKc crc Ac a v BI Hc H1 H2). }
  assert (XSDv : rd = 1 -> L5.u32_at RSEGS MV (E - 220) xv /\ 0 <= xv <= 63 /\ L5.u64_at RSEGS MV (E - 376) sd /\ 0 <= sd < 2 ^ 64).
  { intros X. destruct (XSD X) as (Y1 & Y2 & Y3 & Y4). split. 2: split; [exact Y2 | split; [apply FV8; [exact Y3 | clear; lia | clear; lia] | exact Y4]].
    apply (proj2 (u32_at_vis (ahid Ac modelc) Mc (E - 220) xv ltac:(eapply avis_sub; [exact SV | clear; lia | clear; lia]) ltac:(clear - ER; lia) ltac:(clear - ER; lia))). exact Y1. }
  destruct (g12_run fx Rc MV to qo qn rd sd xv fb RI PF X20 (conj (conj ORP (conj ORG O8)) (conj OBIG (conj OZv (conj OWv (conj OFR (conj OF (conj OSH (conj SOF (conj SOSH SOFR)))))))))
              (U8V _ O0) FBR ROR (FV8 _ _ S96 ltac:(clear; lia) ltac:(clear; lia)) (FV8 _ _ S64 ltac:(clear; lia) ltac:(clear; lia)) (FV8 _ _ S120 ltac:(clear; lia) ltac:(clear; lia)) TOR
              (FV8 _ _ S72 ltac:(clear; lia) ltac:(clear; lia)) QNR (FV8 _ _ S40 ltac:(clear; lia) ltac:(clear; lia)) RDR XSDv)
    as (fx1 & R1 & M1v & pMS & pMG & pFZ & pKS & p19 & pC & pCALL).
  set (Wp := fun a => a = qo).
  apply (L5DKA.bstage L ar C HI LY HIok M model LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2 G W _ Mc modelc LKc crc Ac fx fx1 Rc 0x93474 R1
           (if rd =? 1 then L5DSA.UNNORM else 0x934dc) M1v Wp K BI pMS pMG).
  { intros a Ha Hn. apply pFZ. exact Ha. exact Hn. }
  { intros a Ha Wa. subst Wp; cbn beta in Wa. subst a. destruct (OCL qo ltac:(clear; lia)) as (C1 & C2 & C3 & C4). split. exact C4. split. split. exact C1. exact C2. intros _. exact WQ. }
  intros M1 model1 BI1 AH1 VIS1 MGM1 FRM1.
  apply (KF fx1 R1 M1 model1 BI1).
  - apply (rinvD_keep R E Rc R1 RI). intros k Hk0. apply pKS. revert Hk0. apply (L5K.incl_b DIDX). vm_compute; reflexivity.
  - intros x Hx. apply pKS. revert Hx. apply (L5K.incl_b [3; 4; 18; 20; 21; 22; 24; 25; 26; 27]%nat). vm_compute; reflexivity.
  - exact p19.
  - intros a Ha Hn. apply FRM1. exact Ha. exact Hn.
  - pose proof BI as (B1 & _). assert (AOQ' : aobj FF' qo 32) by (apply aobj_cons; exact AOQ).
    pose proof (aobj_facts L ar C HI LY HIok (BX ++ LB) FF' LKc crc Ac Mc modelc qo 32 0 0 B1 AOQ' ltac:(clear; lia) ltac:(reflexivity)) as (_ & _ & _ & OVIS & _).
    apply (proj1 (u8_at_vis (ahid Ac modelc) M1 qo _ ltac:(eapply avis_sub; [exact OVIS | clear; lia | clear; lia]) ltac:(clear - ORP; lia) ltac:(clear - ORP; lia))). rewrite VIS1. exact pC.
  - exact pCALL.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma g13 (fx : FPState) Rc Mc modelc W BX LKc crc Ac bits fb :
  binv W BX Mc modelc LKc crc Ac -> rinvD R E Rc -> getr Rc (reg 19) = Z_to_bv 64 ro -> L5.u64_at RSEGS Mc (E - 368) (ro / 8 + 2147450880) ->
  aobj FF ro 32 -> shadow_zero Mc ro 4 -> L5.u8_at RSEGS Mc ro fb -> 0 <= fb < 256 -> ~ L5.outside W ro ->
  L5.u64_at RSEGS Mc (E - 328) bits -> 0 <= bits <= 2 ->
  (forall (fx1 : FPState) R1 M1 model1,
      binv W BX M1 model1 LKc crc Ac -> rinvD R E R1 ->
      (forall x, In x [3; 4; 18; 19; 20; 21; 22; 24; 25; 26; 27]%nat -> getr R1 (reg x) = getr Rc (reg x)) ->
      (forall a, 0 <= a < 2 ^ 64 -> a <> ro -> M1 (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)) ->
      L5.u8_at RSEGS M1 ro (Z.lor (Z.land fb 253) bits) ->
      srealizes RSEGS SCFG (cfg (fx:=fx1) R1 0x934dc M1 model1) K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc 0x934bc Mc modelc) K.
Proof.
  intros BI RI X19 S16 AOR SZR O0 FBR WR S64 BITR KF.
  pose proof (arg_facts L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G W BX Mc modelc LKc crc Ac ro BI AOR SZR)
    as ((ORP & ORG & O8) & OBIG & OZ & OW & OFR & OF & OSH & SOF & SOSH & SOFR & U8V & U64V & OCL).
  open_ctx BI. pose proof RI as (X2 & X8 & X9 & X3 & X4 & XSB).
  set (MV := mrestrict (ahid Ac modelc) Mc) in *.
  assert (ER' : 140735332487616 <= E <= 140737488355328) by (clear - ER; lia).
  assert (OAL : L5ADIVPG2.aligned ro 8) by exact O8. assert (EAL : L5ADIVPG2.aligned E 32) by exact EA.
  pose proof (frm_vis L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER W BX Mc modelc LKc crc Ac _ _ BI S64 ltac:(clear; lia) ltac:(clear; lia)) as S64v. fold MV in S64v.
  pose proof (frm_vis L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER W BX Mc modelc LKc crc Ac _ _ BI S16 ltac:(clear; lia) ltac:(clear; lia)) as S16v. fold MV in S16v.
  pose proof (U8V _ O0) as O0v.
  assert (VR : 0 <= fb <= 255 /\ 0 <= fb < 2 ^ 64 /\ 0 <= bits < 2 ^ 64) by (clear - FBR BITR; lia). destruct VR as (V1 & V2 & V3).
  pose proof (v5G13_conc fx Rc MV (fun j => match j with 2%nat => E | 36%nat => ro | 40%nat => F | 58%nat => U Rc 1 | 59%nat => bits | 60%nat => fb | _ => 0 end)) as P. cbn beta iota in P.
  feed P ltac:(first [apply UR | apply U_to | sc ]).
  destruct P as (fx1 & R1 & M1v & pMG & _ & pFZ & (pMS & pKS & _ & _ & pC)).
  set (Wp := fun a => a = ro).
  apply (L5DKA.bstage L ar C HI LY HIok M model LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2 G W _ Mc modelc LKc crc Ac fx fx1 Rc 0x934bc R1 0x934dc M1v Wp K BI pMS pMG).
  { intros a Ha Hn. apply pFZ. exact Ha. subst Wp; cbn beta in Hn. clear - Hn; lia. }
  { intros a Ha Wa. subst Wp; cbn beta in Wa. subst a. destruct (OCL ro ltac:(clear; lia)) as (C1 & C2 & C3 & C4). split. exact C4. split. split. exact C1. exact C2. intros _. exact WR. }
  intros M1 model1 BI1 AH1 VIS1 MGM1 FRM1.
  apply (KF fx1 R1 M1 model1 BI1).
  - apply (rinvD_ks R E Rc R1 KS_v5G13 RI pKS). vm_compute; reflexivity.
  - intros x Hx. apply pKS. revert Hx. apply (L5K.incl_b [3; 4; 18; 19; 20; 21; 22; 24; 25; 26; 27]%nat). vm_compute; reflexivity.
  - intros a Ha Hn. apply FRM1. exact Ha. exact Hn.
  - pose proof BI as (B1 & _). assert (AOR' : aobj FF' ro 32) by (apply aobj_cons; exact AOR).
    pose proof (aobj_facts L ar C HI LY HIok (BX ++ LB) FF' LKc crc Ac Mc modelc ro 32 0 0 B1 AOR' ltac:(clear; lia) ltac:(reflexivity)) as (_ & _ & _ & OVIS & _).
    apply (proj1 (u8_at_vis (ahid Ac modelc) M1 ro _ ltac:(eapply avis_sub; [exact OVIS | clear; lia | clear; lia]) ltac:(clear - ORP; lia) ltac:(clear - ORP; lia))). rewrite VIS1. exact pC.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Notation rinvTL := (L5ADVD.rinvTL R E F).
Local Ltac open_pf PF := destruct PF as (W384 & IMGC & CSB & CUAR & FDEFv & FWv & FSHWv & FLCv & FLWv);
  pose proof (NUM L ar HI R LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER) as ((FRG & FLRG & ERG) & FRP & FLRP & ALF & FBIG & FLBIG & FLA & SFA & SFLA & SFB);
  assert (ER' : 140735332487616 <= E <= 140737488355328) by (clear - ER; lia).
Local Ltac openTL RI := pose proof RI as ((X2 & X8 & X9 & X3 & X4 & XSB) & X18 & X20 & X21 & X24 & X27).
Local Ltac run_inl PIECE OPEN CLOSE :=
  let fx := fresh "fx" in let Rc := fresh "Rc" in let MV := fresh "MV" in let fb := fresh "fb" in
  intros fx Rc MV fb RI PF O0 FBR BT0; open_pf PF; OPEN RI;
  assert (FBR' : 0 <= fb <= 255 /\ 0 <= fb < 2 ^ 64) by (clear - FBR; lia); destruct FBR' as [FBR' FBR''];
  pose proof (PIECE fx Rc MV (fun j => match j with 2%nat => E | 40%nat => F | 41%nat => fl | 58%nat => U Rc 1 | 60%nat => fb | _ => 0 end)) as P; cbn beta iota in P;
  feed P ltac:(first [apply UR | apply U_to | sc ]);
  destruct P as (fx1 & R1 & M1v & _ & pFR & _ & (pMS & pKS & _));
  assert (E1 : M1v = MV) by (apply mem_eq_of_agree; intros a Ha; apply pFR); subst M1v;
  exists fx1, R1; split; [exact pMS | CLOSE Rc R1 RI pKS].
Local Ltac run_dyn PIECE OPEN CLOSE :=
  let fx := fresh "fx" in let Rc := fresh "Rc" in let MV := fresh "MV" in let fb := fresh "fb" in let q := fresh "q" in let cap := fresh "cap" in
  intros fx Rc MV fb q cap RI PF O0 FBR BT1 O24 QR O16 CAPR; open_pf PF; OPEN RI;
  assert (FBR' : 0 <= fb <= 255 /\ 0 <= fb < 2 ^ 64) by (clear - FBR; lia); destruct FBR' as [FBR' FBR''];
  assert (QR' : 4096 <= q <= 140737488355328 /\ 0 <= q < 2 ^ 64) by (clear - QR; lia); destruct QR' as [QR' QR''];
  assert (CR' : 1 <= cap <= 134217728 /\ 0 <= cap < 2 ^ 64) by (clear - CAPR; lia); destruct CR' as [CR' CR''];
  pose proof (PIECE fx Rc MV (fun j => match j with 2%nat => E | 40%nat => F | 41%nat => fl | 58%nat => U Rc 1 | 60%nat => fb | 61%nat => q | 62%nat => cap | _ => 0 end)) as P; cbn beta iota in P;
  feed P ltac:(first [apply UR | apply U_to | sc ]);
  destruct P as (fx1 & R1 & M1v & _ & pFR & _ & (pMS & pKS & pR1 & pR10 & pR11));
  assert (E1 : M1v = MV) by (apply mem_eq_of_agree; intros a Ha; apply pFR); subst M1v;
  exists fx1, R1; split; [exact pMS | split; [CLOSE Rc R1 RI pKS | split; [exact pR1 | split; [exact pR10 | exact pR11]]]].

Lemma run_G14ai : L5ADVD.inl_run E F fl rinvTL rinvTL 0x934dc 0x934fc (SPA + 168).
Proof. unfold L5ADVD.inl_run. replace (SPA + 168) with (E - 216) by (clear; lia).
  run_inl v5G14ai_conc openTL ltac:(fun Rc R1 RI pKS => apply (L5ADVD.rinvTL_ks R E F ER Rc R1 KS_v5G14ai RI pKS); vm_compute; reflexivity). Qed.
Lemma run_G14ad : L5ADVD.dyn_run E F fl rinvTL rinvTL 0x934dc 0x934fc (SPA + 168).
Proof. unfold L5ADVD.dyn_run. replace (SPA + 168 + 24) with (E - 192) by (clear; lia). replace (SPA + 168 + 16) with (E - 200) by (clear; lia). replace (SPA + 168) with (E - 216) by (clear; lia).
  run_dyn v5G14ad_conc openTL ltac:(fun Rc R1 RI pKS => apply (L5ADVD.rinvTL_ks R E F ER Rc R1 KS_v5G14ad RI pKS); vm_compute; reflexivity). Qed.
Lemma run_G14bi : L5ADVD.inl_run E F fl rinvTL rinvTL 0x934fc 0x936e8 (SPA + 200).
Proof. unfold L5ADVD.inl_run. replace (SPA + 200) with (E - 184) by (clear; lia).
  run_inl v5G14bi_conc openTL ltac:(fun Rc R1 RI pKS => apply (L5ADVD.rinvTL_ks R E F ER Rc R1 KS_v5G14bi RI pKS); vm_compute; reflexivity). Qed.
Lemma run_G14bd : L5ADVD.dyn_run E F fl rinvTL rinvTL 0x934fc 0x9351c (SPA + 200).
Proof. unfold L5ADVD.dyn_run. replace (SPA + 200 + 24) with (E - 160) by (clear; lia). replace (SPA + 200 + 16) with (E - 168) by (clear; lia). replace (SPA + 200) with (E - 184) by (clear; lia).
  run_dyn v5G14bd_conc openTL ltac:(fun Rc R1 RI pKS => apply (L5ADVD.rinvTL_ks R E F ER Rc R1 KS_v5G14bd RI pKS); vm_compute; reflexivity). Qed.

(* [comment removed for export] *)
Lemma dtor_stage2 (rin rout : bvmap 5 word -> Prop) (pc pci pcd ox : Z) :
  L5ADVD.inl_run E F fl rin rout pc pci ox -> L5ADVD.dyn_run E F fl rin rout pc pcd ox ->
  (forall Rc, rout Rc -> rinvD R E Rc) -> (forall Ra Rb, rout Ra -> regs_preserved Ra Rb -> rout Rb) -> L5.ra_ok pcd ->
  ((F <= ox /\ ox + 32 <= F + 512) \/ (SPA <= ox /\ ox + 32 <= E)) ->
  forall (fx : FPState) Rc Mc modelc W BX BXn LKc crc Ac b blk,
  binv W BX Mc modelc LKc crc Ac -> rin Rc -> L5ADVD.obj_at Mc ox b blk ->
  match blk with None => BXn = BX | Some (q, n) => In (q, n) (BX ++ LB) /\ lb_remove q (BX ++ LB) = BXn ++ LB end ->
  (forall (fx' : FPState) R' M' model' A',
      binv W BXn M' model' LKc crc A' -> rout R' -> incl Ac A' ->
      (forall a, 0 <= a < 2 ^ 64 -> aclient L ar (BXn ++ LB) FF' SPA OPDEL_SCR a -> M' (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)) ->
      srealizes RSEGS SCFG (cfg (fx:=fx') R' (match blk with None => pci | Some _ => pcd end) M' model') K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc pc Mc modelc) K.
Proof.
  intros INL DYN ROT RPR RAn OXR fx Rc Mc modelc W BX BXn LKc crc Ac b blk BI RI [OB OBLK] BLK KF.
  pose proof (pf_of_binv L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G W BX Mc modelc LKc crc Ac BI) as PF.
  destruct (L5AFK.vis_facts L ar C HI LY HIok M model LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2 G W BX Mc modelc LKc crc Ac BI) as (_ & _ & _ & (_ & _ & FV & SV & _)).
  change (ff_bytes 3) with 512 in FV.
  pose proof BI as (B1 & B2 & B3 & B4 & B5 & B6 & _).
  pose proof (NUM L ar HI R LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER) as ((FRG & FLRG & ERG) & FRP & FLRP & ALF & FBIG & FLBIG & FLA & SFA & SFLA & SFB).
  set (MV := mrestrict (ahid Ac modelc) Mc) in *.
  assert (OXN : 4096 <= ox /\ ox + 32 <= 2 ^ 47) by (clear - OXR FRP ER; lia).
  assert (OV : avis (ahid Ac modelc) ox 32).
  { destruct OXR as [X|X]. eapply avis_sub. exact FV. clear - X; lia. clear - X; lia. eapply avis_sub. exact SV. clear - X; lia. clear - X; lia. }
  assert (CELLV : forall a v, ox <= a -> a + 8 <= ox + 32 -> L5.u64_at RSEGS Mc a v -> L5.u64_at RSEGS MV a v).
  { intros a v H1 H2 Hc. apply (proj2 (u64_at_vis (ahid Ac modelc) Mc a v ltac:(eapply avis_sub; [exact OV | clear - H1; lia | clear - H2; lia]) ltac:(clear - H1 OXN; lia) ltac:(clear - H2 OXN; lia))). exact Hc. }
  assert (CELL1 : forall v, L5.u8_at RSEGS Mc ox v -> L5.u8_at RSEGS MV ox v).
  { intros v Hc. apply (proj2 (u8_at_vis (ahid Ac modelc) Mc ox v ltac:(eapply avis_sub; [exact OV | clear; lia | clear; lia]) ltac:(clear - OXN; lia) ltac:(clear - OXN; lia))). exact Hc. }
  destruct b as [fb len sto]. destruct OB as (O0 & FBR & _ & OST). cbn [L5.bo_fb L5.bo_len L5.bo_st] in *.
  destruct sto as [v0 v1|cap q].
  - (* [comment removed for export] *)
    subst blk. subst BXn. destruct OST as (BT0 & _).
    destruct (INL fx Rc MV fb RI PF (CELL1 _ O0) FBR BT0) as (fx1 & R1 & MS1 & RO1).
    apply (apure L ar C HI LY HIok (BX ++ LB) FF' LKc crc Ac Mc modelc fx fx1 Rc pc R1 pci K B1 B2 MS1).
    intros model1 HH1 AM1 RT1 AH1.
    pose proof (L5AFK.binv_model L ar HI M model LB FF LK A E SCRD SPA (down E F ro R) F 3 W BX Mc modelc LKc crc Ac model1 BI HH1 AM1 RT1) as BI1.
    apply (KF fx1 R1 Mc model1 Ac BI1 RO1 (incl_refl _)). intros a _ _. reflexivity.
  - (* [comment removed for export] *)
    subst blk. destruct BLK as [INP ELB]. destruct OST as (BT1 & O16 & O24 & _ & CAPR & _ & Q4096 & Q47 & _).
    destruct (DYN fx Rc MV fb q cap RI PF (CELL1 _ O0) FBR BT1 (CELLV (ox + 24) q ltac:(clear; lia) ltac:(clear; lia) O24) ltac:(clear - Q4096 Q47 CAPR; lia)
                  (CELLV (ox + 16) cap ltac:(clear; lia) ltac:(clear; lia) O16) CAPR) as (fx1 & R1 & MS1 & RO1 & dR1 & dR10 & dR11).
    apply (apure L ar C HI LY HIok (BX ++ LB) FF' LKc crc Ac Mc modelc fx fx1 Rc pc R1 OPDEL_SIZED K B1 B2 MS1).
    intros model1 HH1 AM1 RT1 AH1.
    pose proof (L5AFK.binv_model L ar HI M model LB FF LK A E SCRD SPA (down E F ro R) F 3 W BX Mc modelc LKc crc Ac model1 BI HH1 AM1 RT1) as BI1.
    pose proof (ROT R1 RO1) as (Z2 & _ & _ & _ & Z4 & _).
    assert (SPA16 : (E - 384) mod 16 = 0). { clear - EA. unfold aligned in EA. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    apply (Hdel fx1 R1 Mc model1 K (BX ++ LB) FF' LKc crc Ac q (8 * cap) SPA pcd HH1 AM1 HK INP).
    + rewrite r10. exact dR10.
    + rewrite r1. exact dR1.
    + exact RAn.
    + rewrite r2. exact Z2.
    + rewrite r4, Z4. rewrite <- G4. reflexivity.
    + replace SPA with (E - 384) by (clear; lia). apply (astk_sub ar Mc Mc E SCRD 384 OPDEL_SCR B6 (mem_grows_refl Mc)).
      clear; lia. rewrite L5ADVD.DEL_EQ; clear; lia. rewrite L5ADVD.DEL_EQ; clear - HSCR; lia. exact SPA16.
    + intros fx3 R3 M3 model3 A3 RP3 AH3 RT3 IA3 AM3 HH3. rewrite ELB in AH3, HH3.
      assert (BI3 : binv W BXn M3 model3 LKc crc A3).
      { apply (L5AFK.binv_callee L ar C HI HIok M model LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2 G
                 W W BX BXn BXn Mc model1 LKc crc Ac M3 model3 LKc crc A3 OPDEL_SCR [] BI1 AH3 HH3 AM3 RT3 IA3 (incl_refl _)).
        - rewrite L5ADVD.DEL_EQ; clear; lia.
        - rewrite L5ADVD.DEL_EQ; clear - HSCR; lia.
        - intros rr a [].
        - intros a _ _ rr [].
        - intros a X. exact X. }
      apply (KF fx3 R3 M3 model3 A3 BI3 (RPR R1 R3 RO1 RP3) IA3).
      intros a Ha Hc. apply (proj1 AH3). split. exact Ha. split. exact Hc. intros rr [].
Qed.

Lemma g14 (fx : FPState) Rc Mc modelc W BX BX1 BX2 LKc crc Ac bd0 od0 bn0 on0 :
  binv W BX Mc modelc LKc crc Ac -> rinvTL Rc -> L5ADVD.obj_at Mc (SPA + 168) bd0 od0 -> L5ADVD.obj_at Mc (SPA + 200) bn0 on0 ->
  match od0 with None => BX1 = BX | Some (q, n) => In (q, n) (BX ++ LB) /\ lb_remove q (BX ++ LB) = BX1 ++ LB end ->
  match on0 with None => BX2 = BX1 | Some (q, n) => In (q, n) (BX1 ++ LB) /\ lb_remove q (BX1 ++ LB) = BX2 ++ LB end ->
  (forall a, aclient L ar (BX2 ++ LB) FF' SPA OPDEL_SCR a -> aclient L ar (BX1 ++ LB) FF' SPA OPDEL_SCR a) ->
  (forall (fx' : FPState) R' M' model' A',
      binv W BX2 M' model' LKc crc A' -> rinvTL R' -> incl Ac A' ->
      (forall a, 0 <= a < 2 ^ 64 -> aclient L ar (BX2 ++ LB) FF' SPA OPDEL_SCR a -> M' (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)) ->
      srealizes RSEGS SCFG (cfg (fx:=fx') R' 0x936e8 M' model') K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc 0x934dc Mc modelc) K.
Proof.
  intros BI RI OD0 ON0 BK1 BK2 BKC KF.
  pose proof G as G'. destruct G' as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG' F32 FLA' FLR FLBIG' NCF NCS]. clear OWNAG HH2 NCF NCS FLNC.
  apply (L5ADVD.dtor_stage L ar C HI LY HIok Hdel R M model K LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER EA HK G4 ltac:(clear - HSCR; lia) rinvTL rinvTL 0x934dc 0x934fc (SPA + 168)
           run_G14ai run_G14ad (fun Rx X => proj1 X) (L5ADVD.rinvTL_pres R E F ER) ltac:(split; [clear; lia | reflexivity]) ltac:(right; clear; lia)
           fx Rc Mc modelc W BX BX1 LKc crc Ac bd0 od0 BI RI OD0 BK1).
  intros fx1 R1 M1 model1 A1 BI1 RI1 IA1 AG1.
  assert (ON1 : L5ADVD.obj_at M1 (SPA + 200) bn0 on0).
  { apply (L5ADVD.obj_at_agree Mc M1 (SPA + 200) bn0 on0 ON0 ltac:(clear - ER; lia) ltac:(clear - ER; lia)). intros i Hi. apply AG1. clear - Hi ER; lia.
    apply stack_client. clear - Hi SLO SHI SPT HSCR; lia. rewrite L5ADVD.DEL_EQ; clear - Hi; lia. }
  apply (dtor_stage2 rinvTL rinvTL 0x934fc 0x936e8 0x9351c (SPA + 200) run_G14bi run_G14bd (fun Rx X => proj1 X) (L5ADVD.rinvTL_pres R E F ER) ltac:(split; [clear; lia | reflexivity]) ltac:(right; clear; lia)
           fx1 R1 M1 model1 W BX1 BX2 LKc crc A1 bn0 on0 BI1 RI1 ON1 BK2).
  intros fx2 R2 M2' model2' A2 BI2 RI2 IA2 AG2.
  assert (AGF : forall a, 0 <= a < 2 ^ 64 -> aclient L ar (BX2 ++ LB) FF' SPA OPDEL_SCR a -> M2' (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)).
  { intros a Ha Hc. rewrite (AG2 a Ha Hc). apply AG1. exact Ha. apply BKC. exact Hc. }
  destruct on0 as [[qn nn]|].
  - (* [comment removed for export] *)
    pose proof (pf_of_binv L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G W BX2 M2' model2' LKc crc A2 BI2) as PF. open_pf PF. openTL RI2.
    set (MV2 := mrestrict (ahid A2 model2') M2') in *.
    pose proof (v5G14j_conc fx2 R2 MV2 (fun j => match j with 2%nat => E | 58%nat => U R2 1 | _ => 0 end)) as P. cbn beta iota in P.
    feed P ltac:(first [apply UR | apply U_to | sc ]).
    destruct P as (fx3 & R3 & M3v & _ & _ & pEQ & (pMS & pKS)).
    assert (EQM : M3v = MV2) by (apply mem_eq_of_agree; exact pEQ). rewrite EQM in pMS.
    pose proof BI2 as (C1 & C2 & _).
    apply (apure L ar C HI LY HIok (BX2 ++ LB) FF' LKc crc A2 M2' model2' fx2 fx3 R2 0x9351c R3 0x936e8 K C1 C2 pMS).
    intros model3 HH3 AM3 RT3 AH3.
    pose proof (L5AFK.binv_model L ar HI M model LB FF LK A E SCRD SPA (down E F ro R) F 3 W BX2 M2' model2' LKc crc A2 model3 BI2 HH3 AM3 RT3) as BI3.
    apply (KF fx3 R3 M2' model3 A2 BI3). apply (L5ADVD.rinvTL_ks R E F ER R2 R3 KS_v5G14j RI2 pKS). vm_compute; reflexivity.
    intros x Hx. apply IA2. apply IA1. exact Hx. exact AGF.
  - apply (KF fx2 R2 M2' model2' A2 BI2 RI2). intros x Hx. apply IA2. apply IA1. exact Hx. exact AGF.
Qed.
End DIV.
End WithIface.
End SCFG_1.
End L5ADVGD.
