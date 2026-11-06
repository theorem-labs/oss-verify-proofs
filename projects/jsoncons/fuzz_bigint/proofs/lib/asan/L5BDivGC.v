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
     L5CoreAB0 L5CoreSpecsAB0 L5StepAB0 L5BCmp L5CoreBB0 L5BDetailG L5BFrameK L5DivKitAB0 L5DivSpecsAB0 L5OpmodSpecsAB0 L5DivLeafSpecsAB0 L5DivInnerSpecsAB0 L5BCopyAS L5BDivH L5BDivT L5BDivD L5BDivE L5BDivEA L5BDivHC L5BDivHA L5BDivHO L5BDivPG1 L5BDivPG2 L5BDivGL L5BDivGA L5BDivGB.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Bo0_code_92368_93368.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5ADVGC.
Import L5A. Import L5CA. Import L5CSA. Import L5W. Import L5SA. Import L5CB. Import L5ADH. Import L5ADVH. Import L5ADVT. Import L5ADVD. Import L5ADVE. Import L5ADVEA. Import L5ADVHC. Import L5ADVHA. Import L5ADVHO. Import L5ADIVPG1. Import L5ADIVPG2. Import L5ADVGA. Import L5ADVGB.
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

Local Ltac hyp9 BIx NWx := first [exact LY | exact HIok | exact G | exact ER | exact EA | exact HSCR0 | exact HSCR | exact BIx | exact HSSH | exact NWx | exact HSC8 | idtac].
Local Ltac wpf := apply (L5DKA.wp_frame L ar HI LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2 G); [ lia | unfold docell; lia ].

(* [comment removed for export] *)
Lemma frm_z W BX Mc modelc LKc crc Ac : binv W BX Mc modelc LKc crc Ac -> (forall a, in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> L5.outside W a) ->
  L5KA.zeros_at (mrestrict (ahid Ac modelc) Mc) ((E - 384) / 8 + 2147450880) 48.
Proof.
  intros BI NW.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (ED8 : (E - 384) mod 8 = 0) by (clear - EA; unfold aligned in EA; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  eapply L5ADVHC.stkz_vis; hyp9 BI NW; [ clear - HSCR; lia | clear; lia | exact ED8 | clear; lia ].
Qed.
Lemma scr_def W BX Mc modelc LKc crc Ac k : binv W BX Mc modelc LKc crc Ac -> 0 <= k <= 96 ->
  L5.defined (mrestrict (ahid Ac modelc) Mc) (E - 384 - k) (384 + k) /\ L5.writable RSEGS (mrestrict (ahid Ac modelc) Mc) (E - 384 - k) (384 + k).
Proof.
  intros BI Hk. pose proof BI as (B1 & _ & _ & _ & _ & B6 & _).
  pose proof (vis_pack L ar C HI LY HIok (BX ++ LB) FF' LKc crc Ac Mc modelc B1) as (_ & VIS & _).
  destruct G as [Hk0 SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG' F32 FLA' FLR FLBIG' NCF NCS].
  assert (DSC : L5.defined (mrestrict (ahid Ac modelc) Mc) (E - 384 - k) (384 + k)).
  { apply (proj2 (defined_vis (ahid Ac modelc) Mc (E - 384 - k) (384 + k) (VIS (E - 384 - k) (384 + k) ltac:(clear - SLO HSCR Hk; lia) ltac:(clear - ER Hk; lia)))).
    eapply astk_defined. exact B6. clear - HSCR Hk; lia. clear - Hk; lia. }
  split. exact DSC. apply (L5C.writable_of_defined RSEGS). exact DSC. clear - ER Hk; lia. clear - ER Hk; lia.
Qed.
(* [comment removed for export] *)
Lemma xs_cell W BX Mc modelc LKc crc Ac M1 M1v a v : binv W BX Mc modelc LKc crc Ac -> mrestrict (ahid Ac modelc) M1 = M1v -> SPA <= a -> a + 8 <= E ->
  L5.u64_at RSEGS M1v a v -> L5.u64_at RSEGS M1 a v.
Proof.
  intros BI VIS1 Ha Hb Hc. open_ctx BI.
  apply (proj1 (u64_at_vis (ahid Ac modelc) M1 a v ltac:(eapply avis_sub; [exact SV | clear - Ha; lia | clear - Hb; lia]) ltac:(clear - Ha ER; lia) ltac:(clear - Hb ER; lia))). rewrite VIS1. exact Hc.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma big_vis W BX Mc modelc LKc crc Ac o b : binv W BX Mc modelc LKc crc Ac -> aobj FF o 32 -> shadow_zero Mc o 4 ->
  L5.big_at RSEGS Mc o b -> L5.big_at RSEGS (mrestrict (ahid Ac modelc) Mc) o b.
Proof.
  intros BI AO SZ OB.
  pose proof (arg_facts L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G W BX Mc modelc LKc crc Ac o BI AO SZ)
    as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & U8V & U64V & _).
  destruct b as [fb len sto]. destruct OB as (O0 & FBR & OL8 & OST). unfold L5.big_at. cbn [L5.bo_fb L5.bo_len L5.bo_st] in *. split. apply U8V. exact O0. split. exact FBR.
  split. apply U64V. clear; lia. clear; lia. exact OL8.
  destruct sto as [v0 v1|cap q].
  - destruct OST as (T0 & C16 & C24 & REST). split. exact T0. split. apply U64V. clear; lia. clear; lia. exact C16. split. apply U64V. clear; lia. clear; lia. exact C24. exact REST.
  - destruct OST as (T0 & C16 & C24 & REST). split. exact T0. split. apply U64V. clear; lia. clear; lia. exact C16. split. apply U64V. clear; lia. clear; lia. exact C24. exact REST.
Qed.

Lemma limb_at Mk o b ws (i : Z) : L5.big_at RSEGS Mk o b -> L5C.obj_limbs RSEGS Mk b ws -> 0 <= i < Z.of_nat (L5.bo_len b) ->
  L5.u64_at RSEGS Mk (L5.bo_data o b + 8 * i) (nth_w ws (Z.to_nat i)) /\ 0 <= nth_w ws (Z.to_nat i) < 2 ^ 64.
Proof.
  intros OB OL Hi. destruct (L5ACMP.obj_limbs_data Mk o b ws OB OL) as (LA & LN & WOK).
  assert (IL : (Z.to_nat i < length ws)%nat) by (rewrite LN; clear - Hi; lia).
  split. { specialize (LA (Z.to_nat i) IL). rewrite Z2Nat.id in LA by (clear - Hi; lia). exact LA. }
  unfold L5W.words_ok in WOK. rewrite Forall_forall in WOK. apply WOK. unfold nth_w. apply nth_In. exact IL.
Qed.

Lemma len_le_cap Mk o b : L5.big_at RSEGS Mk o b -> Z.of_nat (L5.bo_len b) <= match L5.bo_st b with L5.BInl _ _ => 2 | L5.BDyn cap _ => cap end.
Proof. destruct b as [fb len sto]. intros (_ & _ & _ & OST). cbn [L5.bo_st L5.bo_len] in *. destruct sto; [destruct OST as (_ & _ & _ & X & _) | destruct OST as (_ & _ & _ & X & _)]; clear - X; lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma g7 (fx : FPState) Rc Mc modelc W BX LKc crc Ac sd (br bd : L5.bigobj) wr wd (n l : Z) :
  binv W BX Mc modelc LKc crc Ac -> rinvD R E Rc ->
  getr Rc (reg 20) = Z_to_bv 64 (n + 1) -> getr Rc (reg 22) = Z_to_bv 64 ro -> getr Rc (reg 24) = Z_to_bv 64 sd -> 0 <= sd < 2 ^ 64 ->
  aobj FF ro 32 -> tob (BX ++ LB) Mc ro br wr -> tob (BX ++ LB) Mc (F + 32) bd wd ->
  Z.of_nat (L5.bo_len br) = n + 1 -> Z.of_nat (L5.bo_len bd) = l + 1 -> 0 <= n <= 299 -> 0 <= l <= 298 ->
  L5.u64_at RSEGS Mc (E - 272) (l + 1) -> L5.u64_at RSEGS Mc (E - 120) (L5.bo_data (F + 32) bd) ->
  (forall a, in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> L5.outside W a) ->
  (forall (fx1 : FPState) R1 M1 model1,
      binv W BX M1 model1 LKc crc Ac -> rinvD R E R1 ->
      (forall x, In x [3; 4; 18; 20; 25; 26]%nat -> getr R1 (reg x) = getr Rc (reg x)) ->
      getr R1 (reg 19) = Z_to_bv 64 n -> getr R1 (reg 21) = Z_to_bv 64 ((ro + 8) / 8 + 2147450880) -> getr R1 (reg 22) = Z_to_bv 64 (ro + 8) -> getr R1 (reg 27) = Z_to_bv 64 l ->
      (forall a, 0 <= a < 2 ^ 64 -> ~ (E - 376 <= a < E - 360) -> ~ (E - 240 <= a < E - 224) -> ~ (E - 392 <= a < E - 384) -> M1 (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)) ->
      L5.u64_at RSEGS M1 (E - 232) (Z.of_nat (L5.bo_len br)) -> L5.u64_at RSEGS M1 (E - 240) (L5.bo_data ro br) ->
      L5.u64_at RSEGS M1 (E - 376) sd -> L5.u64_at RSEGS M1 (E - 368) (ro / 8 + 2147450880) ->
      srealizes RSEGS SCFG (cfg (fx:=fx1) R1 (if nth_w wr (Z.to_nat n) <? nth_w wd (Z.to_nat l) then 0x93350 else 0x93288) M1 model1) K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc 0x931d4 Mc modelc) K.
Proof.
  intros BI RI X20 X22 X24 SDR AOR (OBR & OLR & SZR & INR) (OBD & OLD & SZD & IND) LENR LEND NR LR S112 S264 NW KF.
  pose proof (arg_facts L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G W BX Mc modelc LKc crc Ac ro BI AOR SZR)
    as ((ORP & ORG & O8) & OBIG & OZ & OW & OFR & OF & OSH & SOF & SOSH & SOFR & _).
  pose proof (pf_of_binv L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G W BX Mc modelc LKc crc Ac BI) as PF.
  assert (AOR' : aobj FF' ro 32) by (apply aobj_cons; exact AOR).
  assert (AOD' : aobj FF' (F + 32) 32) by (eapply L5ADVEA.loc_aobj; [exact G | clear; lia | clear; lia | reflexivity]).
  pose proof (big_vis W BX Mc modelc LKc crc Ac ro br BI AOR SZR OBR) as OBRv.
  pose proof (len_le_cap Mc ro br OBR) as LCR. pose proof (len_le_cap Mc (F + 32) bd OBD) as LCD.
  pose proof (dreg_facts L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G W BX Mc modelc LKc crc Ac ro br wr (n + 1) BI AOR' (conj OBR (conj OLR (conj SZR INR)))
                ltac:(clear - NR; lia) ltac:(rewrite <- LENR; exact LCR)) as (RF1 & RF2 & RF3 & RF4 & RF5 & RF6 & RVIS).
  pose proof (dreg_facts L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G W BX Mc modelc LKc crc Ac (F + 32) bd wd (l + 1) BI AOD' (conj OBD (conj OLD (conj SZD IND)))
                ltac:(clear - LR; lia) ltac:(rewrite <- LEND; exact LCD)) as (DF1 & DF2 & DF3 & DF4 & DF5 & DF6 & DVIS).
  cbv zeta in RF1, RF2, RF3, RF4, RF5, RF6, RVIS, DF1, DF2, DF3, DF4, DF5, DF6, DVIS.
  pose proof (frm_z W BX Mc modelc LKc crc Ac BI NW) as FZv.
  pose proof (scr_def W BX Mc modelc LKc crc Ac 16 BI ltac:(clear; lia)) as (_ & FW400). replace (E - 384 - 16) with (E - 400) in FW400 by (clear; lia). change (384 + 16) with 400 in FW400.
  pose proof BI as (B1 & _).
  pose proof (aobj_facts L ar C HI LY HIok (BX ++ LB) FF' LKc crc Ac Mc modelc ro 32 0 0 B1 AOR' ltac:(clear; lia) ltac:(reflexivity)) as ((_ & OCEIL & _) & _).
  assert (OLOW : ro + 32 <= E - 400).
  { destruct G as [Hk0 SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG' F32 FLA' FLR FLBIG' NCF NCS]. clear - OCEIL SLO HSCR. lia. }
  set (MV := mrestrict (ahid Ac modelc) Mc) in *. set (Dr := L5.bo_data ro br) in *. set (Dd := L5.bo_data (F + 32) bd) in *.
  destruct (limb_at Mc ro br wr n OBR OLR ltac:(clear - LENR NR; lia)) as (CRc & VRR). fold Dr in CRc.
  destruct (limb_at Mc (F + 32) bd wd l OBD OLD ltac:(clear - LEND LR; lia)) as (CDc & DRR). fold Dd in CDc.
  set (vr := nth_w wr (Z.to_nat n)) in *. set (d := nth_w wd (Z.to_nat l)) in *.
  assert (ER' : 0 <= E - 384 /\ E <= 2 ^ 64) by (clear - ER; lia).
  assert (DRRG : 0 <= Dr /\ Dr + 8 * (n + 1) <= 2 ^ 64 /\ 0 <= Dd /\ Dd + 8 * (l + 1) <= 2 ^ 64) by (clear - RF1 DF1 NR LR; lia).
  assert (CRv : L5.u64_at RSEGS MV (Dr + 8 * n) vr).
  { eapply L5C.u64_at_agree. 4: exact CRc. 2: clear - DRRG NR; lia. 2: clear - DRRG NR; lia. intros i Hi. apply RVIS. clear - Hi NR; lia. }
  assert (CDv : L5.u64_at RSEGS MV (Dd + 8 * l) d).
  { eapply L5C.u64_at_agree. 4: exact CDc. 2: clear - DRRG LR; lia. 2: clear - DRRG LR; lia. intros i Hi. apply DVIS. clear - Hi LR; lia. }
  pose proof (frm_vis L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER W BX Mc modelc LKc crc Ac _ _ BI S112 ltac:(clear; lia) ltac:(clear; lia)) as S112v.
  pose proof (frm_vis L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER W BX Mc modelc LKc crc Ac _ _ BI S264 ltac:(clear; lia) ltac:(clear; lia)) as S264v.
  fold MV in S112v, S264v, OBRv, PF.
  destruct br as [fb lenr sto].
  destruct (g7_run L ar HI R LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER EA HSCR fx Rc MV sd fb lenr sto n l Dd vr d RI PF X20 X22 X24 SDR
              (conj (conj ORP (conj ORG O8)) (conj OBIG (conj OZ (conj OW (conj OFR (conj OF (conj OSH (conj SOF (conj SOSH SOFR))))))))) OLOW OBRv NR LR
              (conj RF1 (conj RF2 (conj RF3 (conj RF4 (conj RF5 RF6))))) (conj DF1 (conj DF2 (conj DF3 (conj DF4 (conj DF5 DF6))))) S112v S264v FZv FW400 CRv VRR CDv DRR)
    as (fx1 & R1 & M1v & pMS & pMG & pFZ & pKS & p10 & p24 & p19 & p21 & p22 & p27 & pC232 & pC240 & pC376 & pC368).
  pose proof (br_92f30 fx1 R1 M1v) as BR. rewrite p24, p10, (bltu_Z vr d VRR DRR) in BR.
  set (Wp := fun a => E - 376 <= a < E - 360 \/ E - 240 <= a < E - 224 \/ E - 392 <= a < E - 384).
  apply (L5DKA.bstage L ar C HI LY HIok M model LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2 G W _ Mc modelc LKc crc Ac fx fx1 Rc 0x931d4 R1
           (if vr <? d then 0x93350 else 0x93288) M1v Wp K BI (msteps_trans _ _ _ _ pMS BR) pMG).
  { intros a Ha Hn. apply pFZ. exact Ha. intros X. apply Hn. left; exact X. intros X. apply Hn. right; left; exact X. intros X. apply Hn. right; right; exact X. }
  { intros a Ha [Wa|[Wa|Wa]]; [ wpf | wpf | ]. eapply L5ADVHC.wp_scratch; hyp9 BI NW. clear - Wa HSCR; lia. }
  intros M1 model1 BI1 AH1 VIS1 MGM1 FRM1.
  apply (KF fx1 R1 M1 model1 BI1).
  - apply (rinvD_keep R E Rc R1 RI). intros k Hk0. apply pKS. revert Hk0. apply (L5K.incl_b DIDX). vm_compute; reflexivity.
  - intros x Hx. apply pKS. revert Hx. apply (L5K.incl_b [3; 4; 18; 20; 25; 26]%nat). vm_compute; reflexivity.
  - exact p19.
  - exact p21.
  - exact p22.
  - exact p27.
  - intros a Ha N1 N2 N3. apply FRM1. exact Ha. subst Wp; cbn beta. intros [X|[X|X]]; [exact (N1 X) | exact (N2 X) | exact (N3 X)].
  - apply (xs_cell W BX Mc modelc LKc crc Ac M1 M1v (E - 232) _ BI VIS1 ltac:(clear; lia) ltac:(clear; lia) pC232).
  - apply (xs_cell W BX Mc modelc LKc crc Ac M1 M1v (E - 240) _ BI VIS1 ltac:(clear; lia) ltac:(clear; lia) pC240).
  - apply (xs_cell W BX Mc modelc LKc crc Ac M1 M1v (E - 376) _ BI VIS1 ltac:(clear; lia) ltac:(clear; lia) pC376).
  - apply (xs_cell W BX Mc modelc LKc crc Ac M1 M1v (E - 368) _ BI VIS1 ltac:(clear; lia) ltac:(clear; lia) pC368).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma g7b_run (fx : FPState) Rc MV lenr : rinvD R E Rc -> pf E F fl MV -> L5.u64_at RSEGS MV (E - 288) ro -> 0 <= ro < 2 ^ 64 ->
  L5.u64_at RSEGS MV (E - 232) lenr -> 0 <= lenr < 2 ^ 64 ->
  exists (fx' : FPState) R', msteps RSEGS (st fx Rc 0x93288 MV) (st fx' R' RESIZE MV)
    /\ (forall x, In x [2; 3; 4; 8; 9; 18; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R' (reg x) = getr Rc (reg x))
    /\ getr R' (reg 1) = Z_to_bv 64 0x9329c /\ getr R' (reg 10) = Z_to_bv 64 ro /\ getr R' (reg 11) = Z_to_bv 64 (lenr + 1) /\ getr R' (reg 19) = Z_to_bv 64 ro.
Proof.
  intros RI PF S96 ROR S152 LRG.
  unfold pf in PF. destruct PF as (W352 & IMGC & CSB & CUAR & FDEFv & FWv & FSHWv & FLCv & FLWv).
  pose proof RI as (X2 & X8 & X9 & X3 & X4 & XSB).
  assert (ER' : 140735332487616 <= E <= 140737488355328) by (clear - ER; lia). assert (EAL : L5ADIVPG1.aligned E 32) by exact EA.
  assert (VR : 0 <= ro <= 18446744073709551615 /\ 0 <= lenr <= 18446744073709551615) by (clear - ROR LRG; lia). destruct VR as [VR1 VR2].
  pose proof (v5G7b_conc fx Rc MV (fun j => match j with 2%nat => E | 36%nat => ro | 40%nat => F | 58%nat => U Rc 1 | 72%nat => lenr | _ => 0 end)) as P. cbn beta iota in P.
  feed P ltac:(first [apply UR | apply U_to | sc ]).
  destruct P as (fx1 & R1 & M1v & _ & _ & pEQ & (pMS & pKS & p1 & p10 & p11 & p19)).
  assert (EQM : M1v = MV) by (apply mem_eq_of_agree; exact pEQ). rewrite EQM in pMS.
  exists fx1, R1. split. exact pMS. split. { intros x Hx. apply pKS. revert Hx. apply (L5K.incl_b [2; 3; 4; 8; 9; 18; 20; 21; 22; 23; 24; 25; 26; 27]%nat). vm_compute; reflexivity. }
  split. exact p1. split. exact p10. split. exact p11. exact p19.
Qed.

Lemma g8_run (fx : FPState) Rc MV qo lenq fb (lenr : nat) sto : rinvD R E Rc -> pf E F fl MV -> getr Rc (reg 19) = Z_to_bv 64 ro ->
  getr Rc (reg 21) = Z_to_bv 64 ((ro + 8) / 8 + 2147450880) -> getr Rc (reg 22) = Z_to_bv 64 (ro + 8) -> 0 <= qo < 2 ^ 64 -> 0 <= lenq < 2 ^ 64 -> ARGF E F MV ro ->
  L5.big_at RSEGS MV ro (L5.BO fb lenr sto) -> L5.u64_at RSEGS MV (E - 368) (ro / 8 + 2147450880) -> L5.u64_at RSEGS MV (E - 296) qo -> L5.u64_at RSEGS MV (E - 128) lenq ->
  exists (fx' : FPState) R' M1v, msteps RSEGS (st fx Rc 0x9329c MV) (st fx' R' RESIZE M1v) /\ mem_grows MV M1v
    /\ (forall a, 0 <= a < 2 ^ 64 -> ~ (E - 240 <= a < E - 224) -> M1v (Z_to_bv 64 a) = MV (Z_to_bv 64 a))
    /\ (forall x, In x [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R' (reg x) = getr Rc (reg x))
    /\ getr R' (reg 1) = Z_to_bv 64 0x932f8 /\ getr R' (reg 10) = Z_to_bv 64 qo /\ getr R' (reg 11) = Z_to_bv 64 (lenq + 1)
    /\ L5.u64_at RSEGS M1v (E - 240) (L5.bo_data ro (L5.BO fb lenr sto)) /\ L5.u64_at RSEGS M1v (E - 232) (Z.of_nat lenr).
Proof.
  intros RI PF X19 X21 X22 QOR LQR ((ORP & ORG & O8) & OBIG & OZ & OW & OFR & OF & OSH & SOF & SOSH & SOFR) OB S16 S88 S256.
  unfold pf in PF. destruct PF as (W352 & IMGC & CSB & CUAR & FDEFv & FWv & FSHWv & FLCv & FLWv).
  pose proof (NUM L ar HI R LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER) as ((FRG & FLRG & ERG) & FRP & FLRP & ALF & FBIG & FLBIG & FLA & SFA & SFLA & SFB).
  pose proof RI as (X2 & X8 & X9 & X3 & X4 & XSB).
  assert (ER' : 140735332487616 <= E <= 140737488355328) by (clear - ER; lia). assert (EAL : L5ADIVPG1.aligned E 32) by exact EA.
  assert (OAL : L5ADIVPG1.aligned ro 8) by exact O8.
  destruct OB as (O0 & FBR & OL8 & OST). cbn [L5.bo_fb L5.bo_len L5.bo_st] in *. unfold L5.bo_data. cbn [L5.bo_st].
  assert (FBR' : 0 <= fb <= 255) by (clear - FBR; lia). assert (FBG : 0 <= fb < 2 ^ 64) by (clear - FBR; lia).
  assert (LNR : 0 <= Z.of_nat lenr <= 18446744073709551615 /\ 0 <= Z.of_nat lenr < 2 ^ 64).
  { destruct sto; [destruct OST as (_ & _ & _ & X & _) | destruct OST as (_ & _ & _ & X & X' & _)]; clear - X + clear - X X'; lia. }
  destruct LNR as [LNR LNRG].
  assert (VR : 0 <= qo <= 18446744073709551615 /\ 0 <= lenq <= 18446744073709551615) by (clear - QOR LQR; lia). destruct VR as [VR1 VR2].
  assert (FZ8 : forall (M' : word -> option byte), (forall a : Z, 0 <= a < 2 ^ 64 -> ~ (E - 240 <= a < E - 240 + 16) -> M' (Z_to_bv 64 a) = MV (Z_to_bv 64 a)) ->
                forall a, 0 <= a < 2 ^ 64 -> ~ (E - 240 <= a < E - 224) -> M' (Z_to_bv 64 a) = MV (Z_to_bv 64 a)).
  { intros M' HFZ a Ha Hn. apply HFZ. exact Ha. clear - Hn; lia. }
  destruct sto as [v0 v1|cap q].
  - destruct OST as (BT0 & _).
    pose proof (v5G8i_conc fx Rc MV (fun j => match j with 2%nat => E | 35%nat => qo | 36%nat => ro | 40%nat => F | 58%nat => U Rc 1 | 60%nat => fb | 67%nat => lenq | 72%nat => Z.of_nat lenr | _ => 0 end)) as P. cbn beta iota in P.
    feed P ltac:(first [apply UR | apply U_to | sc ]).
    destruct P as (fx1 & R1 & M1v & pMG & _ & pFZ & (pMS & pKS & p1 & p10 & p11 & _ & pC232 & pC240)).
    exists fx1, R1, M1v. split. exact pMS. split. exact pMG. split. exact (FZ8 M1v pFZ).
    split. { intros x Hx. apply pKS. revert Hx. apply (L5K.incl_b [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat). vm_compute; reflexivity. }
    split. exact p1. split. exact p10. split. exact p11. split. exact pC240. exact pC232.
  - destruct OST as (BT1 & O16 & O24 & _ & CAPR & Q8 & Q4096 & Q47 & _).
    assert (QRG : 0 <= q < 2 ^ 64 /\ 4096 <= q <= 140737488355328) by (clear - Q4096 Q47 CAPR; lia). destruct QRG as [QRG QRG']. assert (QAL : L5ADIVPG1.aligned q 8) by exact Q8.
    pose proof (v5G8d_conc fx Rc MV (fun j => match j with 2%nat => E | 35%nat => qo | 36%nat => ro | 40%nat => F | 58%nat => U Rc 1 | 60%nat => fb | 67%nat => lenq | 70%nat => q | 72%nat => Z.of_nat lenr | _ => 0 end)) as P. cbn beta iota in P.
    feed P ltac:(first [apply UR | apply U_to | sc ]).
    destruct P as (fx1 & R1 & M1v & pMG & _ & pFZ & (pMS & pKS & p1 & p10 & p11 & _ & pC232 & pC240)).
    exists fx1, R1, M1v. split. exact pMS. split. exact pMG. split. exact (FZ8 M1v pFZ).
    split. { intros x Hx. apply pKS. revert Hx. apply (L5K.incl_b [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat). vm_compute; reflexivity. }
    split. exact p1. split. exact p10. split. exact p11. split. exact pC240. exact pC232.
Qed.

Lemma g8b_run (fx : FPState) Rc MV qo n1 fb (lenq : nat) sto : rinvD R E Rc -> pf E F fl MV -> getr Rc (reg 20) = Z_to_bv 64 n1 -> getr Rc (reg 26) = Z_to_bv 64 (qo + 8) ->
  0 <= n1 < 2 ^ 64 -> ARGF E F MV qo ->
  L5.big_at RSEGS MV qo (L5.BO fb lenq sto) -> L5.u64_at RSEGS MV (E - 320) (qo / 8 + 2147450880) -> L5.u64_at RSEGS MV (E - 352) ((qo + 8) / 8 + 2147450880) -> L5.u64_at RSEGS MV (E - 296) qo ->
  exists (fx' : FPState) R' M1v, msteps RSEGS (st fx Rc 0x932f8 MV) (st fx' R' 0x93350 M1v) /\ mem_grows MV M1v
    /\ (forall a, 0 <= a < 2 ^ 64 -> ~ (E - 136 <= a < E - 120) -> M1v (Z_to_bv 64 a) = MV (Z_to_bv 64 a))
    /\ (forall x, In x [2; 3; 4; 8; 9; 18; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R' (reg x) = getr Rc (reg x))
    /\ getr R' (reg 19) = Z_to_bv 64 n1
    /\ L5.u64_at RSEGS M1v (E - 136) (L5.bo_data qo (L5.BO fb lenq sto)) /\ L5.u64_at RSEGS M1v (E - 128) (Z.of_nat lenq).
Proof.
  intros RI PF X20 X26 N1R ((ORP & ORG & O8) & OBIG & OZ & OW & OFR & OF & OSH & SOF & SOSH & SOFR) OB S64 S32 S88.
  unfold pf in PF. destruct PF as (W352 & IMGC & CSB & CUAR & FDEFv & FWv & FSHWv & FLCv & FLWv).
  pose proof (NUM L ar HI R LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER) as ((FRG & FLRG & ERG) & FRP & FLRP & ALF & FBIG & FLBIG & FLA & SFA & SFLA & SFB).
  pose proof RI as (X2 & X8 & X9 & X3 & X4 & XSB).
  assert (ER' : 140735332487616 <= E <= 140737488355328) by (clear - ER; lia). assert (EAL : L5ADIVPG1.aligned E 32) by exact EA.
  assert (OAL : L5ADIVPG1.aligned qo 8) by exact O8.
  destruct OB as (O0 & FBR & OL8 & OST). cbn [L5.bo_fb L5.bo_len L5.bo_st] in *. unfold L5.bo_data. cbn [L5.bo_st].
  assert (FBR' : 0 <= fb <= 255) by (clear - FBR; lia). assert (FBG : 0 <= fb < 2 ^ 64) by (clear - FBR; lia).
  assert (LNR : 0 <= Z.of_nat lenq <= 18446744073709551615 /\ 0 <= Z.of_nat lenq < 2 ^ 64).
  { destruct sto; [destruct OST as (_ & _ & _ & X & _) | destruct OST as (_ & _ & _ & X & X' & _)]; clear - X + clear - X X'; lia. }
  destruct LNR as [LNR LNRG].
  assert (VR : 0 <= n1 <= 18446744073709551615) by (clear - N1R; lia).
  assert (FZ8 : forall (M' : word -> option byte), (forall a : Z, 0 <= a < 2 ^ 64 -> ~ (E - 136 <= a < E - 136 + 16) -> M' (Z_to_bv 64 a) = MV (Z_to_bv 64 a)) ->
                forall a, 0 <= a < 2 ^ 64 -> ~ (E - 136 <= a < E - 120) -> M' (Z_to_bv 64 a) = MV (Z_to_bv 64 a)).
  { intros M' HFZ a Ha Hn. apply HFZ. exact Ha. clear - Hn; lia. }
  destruct sto as [v0 v1|cap q].
  - destruct OST as (BT0 & _).
    pose proof (v5G8bi_conc fx Rc MV (fun j => match j with 2%nat => E | 35%nat => qo | 40%nat => F | 58%nat => U Rc 1 | 60%nat => fb | 66%nat => n1 | 67%nat => Z.of_nat lenq | _ => 0 end)) as P. cbn beta iota in P.
    feed P ltac:(first [apply UR | apply U_to | sc ]).
    destruct P as (fx1 & R1 & M1v & pMG & _ & pFZ & (pMS & pKS & _ & _ & p19 & pC128 & pC136)).
    exists fx1, R1, M1v. split. exact pMS. split. exact pMG. split. exact (FZ8 M1v pFZ).
    split. { intros x Hx. apply pKS. revert Hx. apply (L5K.incl_b [2; 3; 4; 8; 9; 18; 20; 21; 22; 23; 24; 25; 26; 27]%nat). vm_compute; reflexivity. }
    split. exact p19. split. exact pC136. exact pC128.
  - destruct OST as (BT1 & O16 & O24 & _ & CAPR & Q8 & Q4096 & Q47 & _).
    assert (QRG : 0 <= q < 2 ^ 64 /\ 4096 <= q <= 140737488355328) by (clear - Q4096 Q47 CAPR; lia). destruct QRG as [QRG QRG']. assert (QAL : L5ADIVPG1.aligned q 8) by exact Q8.
    pose proof (v5G8bd_conc fx Rc MV (fun j => match j with 2%nat => E | 35%nat => qo | 40%nat => F | 58%nat => U Rc 1 | 60%nat => fb | 66%nat => n1 | 67%nat => Z.of_nat lenq | 68%nat => q | _ => 0 end)) as P. cbn beta iota in P.
    feed P ltac:(first [apply UR | apply U_to | sc ]).
    destruct P as (fx1 & R1 & M1v & pMG & _ & pFZ & (pMS & pKS & _ & _ & p19 & pC128 & pC136)).
    exists fx1, R1, M1v. split. exact pMS. split. exact pMG. split. exact (FZ8 M1v pFZ).
    split. { intros x Hx. apply pKS. revert Hx. apply (L5K.incl_b [2; 3; 4; 8; 9; 18; 20; 21; 22; 23; 24; 25; 26; 27]%nat). vm_compute; reflexivity. }
    split. exact p19. split. exact pC136. exact pC128.
Qed.

(* [comment removed for export] *)
Lemma g7b (fx : FPState) Rc Mc modelc W BX LKc crc Ac (br : L5.bigobj) :
  binv W BX Mc modelc LKc crc Ac -> rinvD R E Rc -> L5.u64_at RSEGS Mc (E - 288) ro ->
  aobj FF ro 32 -> shadow_zero Mc ro 4 -> L5.big_at RSEGS Mc ro br -> L5.u64_at RSEGS Mc (E - 232) (Z.of_nat (L5.bo_len br)) ->
  (forall (fx1 : FPState) R1 model1,
      binv W BX Mc model1 LKc crc Ac -> rinvD R E R1 ->
      (forall x, In x [3; 4; 18; 20; 21; 22; 24; 25; 26; 27]%nat -> getr R1 (reg x) = getr Rc (reg x)) ->
      getr R1 (reg 1) = Z_to_bv 64 0x9329c -> getr R1 (reg 10) = Z_to_bv 64 ro -> getr R1 (reg 11) = Z_to_bv 64 (Z.of_nat (L5.bo_len br) + 1) -> getr R1 (reg 19) = Z_to_bv 64 ro ->
      srealizes RSEGS SCFG (cfg (fx:=fx1) R1 RESIZE Mc model1) K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc 0x93288 Mc modelc) K.
Proof.
  intros BI RI S96 AOR SZR OBR S152 KF.
  pose proof (arg_facts L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G W BX Mc modelc LKc crc Ac ro BI AOR SZR) as ((ORP & ORG & O8) & _).
  pose proof (pf_of_binv L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G W BX Mc modelc LKc crc Ac BI) as PF.
  pose proof (frm_vis L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER W BX Mc modelc LKc crc Ac _ _ BI S96 ltac:(clear; lia) ltac:(clear; lia)) as S96v.
  pose proof (frm_vis L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER W BX Mc modelc LKc crc Ac _ _ BI S152 ltac:(clear; lia) ltac:(clear; lia)) as S152v.
  pose proof BI as (B1 & B2 & _).
  assert (LRG : 0 <= Z.of_nat (L5.bo_len br) < 2 ^ 64).
  { destruct br as [fb lenr sto]. destruct OBR as (_ & _ & _ & OST). cbn [L5.bo_len L5.bo_st] in *. destruct sto; [destruct OST as (_ & _ & _ & X & _) | destruct OST as (_ & _ & _ & X & X' & _)]; clear - X + clear - X X'; lia. }
  destruct (g7b_run fx Rc _ (Z.of_nat (L5.bo_len br)) RI PF S96v ORG S152v LRG) as (fx1 & R1 & pMS & pKS & p1 & p10 & p11 & p19).
  apply (apure L ar C HI LY HIok (BX ++ LB) FF' LKc crc Ac Mc modelc fx fx1 Rc 0x93288 R1 RESIZE K B1 B2 pMS).
  intros model1 HH1 AM1 RT1 AH1.
  pose proof (L5AFK.binv_model L ar HI M model LB FF LK A E SCRD SPA (down E F ro R) F 3 W BX Mc modelc LKc crc Ac model1 BI HH1 AM1 RT1) as BI1.
  apply (KF fx1 R1 model1 BI1).
  - apply (rinvD_keep R E Rc R1 RI). intros k Hk0. apply pKS. revert Hk0. apply (L5K.incl_b DIDX). vm_compute; reflexivity.
  - intros x Hx. apply pKS. revert Hx. apply (L5K.incl_b [3; 4; 18; 20; 21; 22; 24; 25; 26; 27]%nat). vm_compute; reflexivity.
  - exact p1.
  - exact p10.
  - exact p11.
  - exact p19.
Qed.

Lemma g8 (fx : FPState) Rc Mc modelc W BX LKc crc Ac qo lenq (br : L5.bigobj) :
  binv W BX Mc modelc LKc crc Ac -> rinvD R E Rc -> getr Rc (reg 19) = Z_to_bv 64 ro -> getr Rc (reg 21) = Z_to_bv 64 ((ro + 8) / 8 + 2147450880) ->
  getr Rc (reg 22) = Z_to_bv 64 (ro + 8) -> 0 <= qo < 2 ^ 64 -> 0 <= lenq < 2 ^ 64 ->
  aobj FF ro 32 -> shadow_zero Mc ro 4 -> L5.big_at RSEGS Mc ro br ->
  L5.u64_at RSEGS Mc (E - 368) (ro / 8 + 2147450880) -> L5.u64_at RSEGS Mc (E - 296) qo -> L5.u64_at RSEGS Mc (E - 128) lenq ->
  (forall (fx1 : FPState) R1 M1 model1,
      binv W BX M1 model1 LKc crc Ac -> rinvD R E R1 ->
      (forall x, In x [3; 4; 18; 19; 20; 21; 22; 24; 25; 26; 27]%nat -> getr R1 (reg x) = getr Rc (reg x)) ->
      getr R1 (reg 1) = Z_to_bv 64 0x932f8 -> getr R1 (reg 10) = Z_to_bv 64 qo -> getr R1 (reg 11) = Z_to_bv 64 (lenq + 1) ->
      (forall a, 0 <= a < 2 ^ 64 -> ~ (E - 240 <= a < E - 224) -> M1 (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)) ->
      L5.u64_at RSEGS M1 (E - 240) (L5.bo_data ro br) -> L5.u64_at RSEGS M1 (E - 232) (Z.of_nat (L5.bo_len br)) ->
      srealizes RSEGS SCFG (cfg (fx:=fx1) R1 RESIZE M1 model1) K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc 0x9329c Mc modelc) K.
Proof.
  intros BI RI X19 X21 X22 QOR LQR AOR SZR OBR S16 S88 S256 KF.
  pose proof (arg_facts L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G W BX Mc modelc LKc crc Ac ro BI AOR SZR)
    as ((ORP & ORG & O8) & OBIG & OZ & OW & OFR & OF & OSH & SOF & SOSH & SOFR & _).
  pose proof (pf_of_binv L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G W BX Mc modelc LKc crc Ac BI) as PF.
  pose proof (big_vis W BX Mc modelc LKc crc Ac ro br BI AOR SZR OBR) as OBRv.
  pose proof (frm_vis L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER W BX Mc modelc LKc crc Ac _ _ BI S16 ltac:(clear; lia) ltac:(clear; lia)) as S16v.
  pose proof (frm_vis L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER W BX Mc modelc LKc crc Ac _ _ BI S88 ltac:(clear; lia) ltac:(clear; lia)) as S88v.
  pose proof (frm_vis L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER W BX Mc modelc LKc crc Ac _ _ BI S256 ltac:(clear; lia) ltac:(clear; lia)) as S256v.
  destruct br as [fb lenr sto].
  destruct (g8_run fx Rc _ qo lenq fb lenr sto RI PF X19 X21 X22 QOR LQR (conj (conj ORP (conj ORG O8)) (conj OBIG (conj OZ (conj OW (conj OFR (conj OF (conj OSH (conj SOF (conj SOSH SOFR))))))))) OBRv S16v S88v S256v)
    as (fx1 & R1 & M1v & pMS & pMG & pFZ & pKS & p1 & p10 & p11 & pC240 & pC232).
  set (Wp := fun a => E - 240 <= a < E - 224).
  apply (L5DKA.bstage L ar C HI LY HIok M model LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2 G W _ Mc modelc LKc crc Ac fx fx1 Rc 0x9329c R1 RESIZE M1v Wp K BI pMS pMG).
  { intros a Ha Hn. apply pFZ. exact Ha. exact Hn. }
  { intros a Ha Wa. subst Wp; cbn beta in Wa. wpf. }
  intros M1 model1 BI1 AH1 VIS1 MGM1 FRM1.
  apply (KF fx1 R1 M1 model1 BI1).
  - apply (rinvD_keep R E Rc R1 RI). intros k Hk0. apply pKS. revert Hk0. apply (L5K.incl_b DIDX). vm_compute; reflexivity.
  - intros x Hx. apply pKS. revert Hx. apply (L5K.incl_b [3; 4; 18; 19; 20; 21; 22; 24; 25; 26; 27]%nat). vm_compute; reflexivity.
  - exact p1.
  - exact p10.
  - exact p11.
  - intros a Ha Hn. apply FRM1. exact Ha. exact Hn.
  - apply (xs_cell W BX Mc modelc LKc crc Ac M1 M1v (E - 240) _ BI VIS1 ltac:(clear; lia) ltac:(clear; lia) pC240).
  - apply (xs_cell W BX Mc modelc LKc crc Ac M1 M1v (E - 232) _ BI VIS1 ltac:(clear; lia) ltac:(clear; lia) pC232).
Qed.

Lemma g8b (fx : FPState) Rc Mc modelc W BX LKc crc Ac qo n1 (bq : L5.bigobj) :
  binv W BX Mc modelc LKc crc Ac -> rinvD R E Rc -> getr Rc (reg 20) = Z_to_bv 64 n1 -> getr Rc (reg 26) = Z_to_bv 64 (qo + 8) -> 0 <= n1 < 2 ^ 64 ->
  aobj FF qo 32 -> shadow_zero Mc qo 4 -> L5.big_at RSEGS Mc qo bq ->
  L5.u64_at RSEGS Mc (E - 320) (qo / 8 + 2147450880) -> L5.u64_at RSEGS Mc (E - 352) ((qo + 8) / 8 + 2147450880) -> L5.u64_at RSEGS Mc (E - 296) qo ->
  (forall (fx1 : FPState) R1 M1 model1,
      binv W BX M1 model1 LKc crc Ac -> rinvD R E R1 ->
      (forall x, In x [3; 4; 18; 20; 21; 22; 24; 25; 26; 27]%nat -> getr R1 (reg x) = getr Rc (reg x)) ->
      getr R1 (reg 19) = Z_to_bv 64 n1 ->
      (forall a, 0 <= a < 2 ^ 64 -> ~ (E - 136 <= a < E - 120) -> M1 (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)) ->
      L5.u64_at RSEGS M1 (E - 136) (L5.bo_data qo bq) -> L5.u64_at RSEGS M1 (E - 128) (Z.of_nat (L5.bo_len bq)) ->
      srealizes RSEGS SCFG (cfg (fx:=fx1) R1 0x93350 M1 model1) K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc 0x932f8 Mc modelc) K.
Proof.
  intros BI RI X20 X26 N1R AOQ SZQ OBQ S64 S32 S88 KF.
  pose proof (arg_facts L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G W BX Mc modelc LKc crc Ac qo BI AOQ SZQ)
    as ((ORP & ORG & O8) & OBIG & OZ & OW & OFR & OF & OSH & SOF & SOSH & SOFR & _).
  pose proof (pf_of_binv L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G W BX Mc modelc LKc crc Ac BI) as PF.
  pose proof (big_vis W BX Mc modelc LKc crc Ac qo bq BI AOQ SZQ OBQ) as OBQv.
  pose proof (frm_vis L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER W BX Mc modelc LKc crc Ac _ _ BI S64 ltac:(clear; lia) ltac:(clear; lia)) as S64v.
  pose proof (frm_vis L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER W BX Mc modelc LKc crc Ac _ _ BI S32 ltac:(clear; lia) ltac:(clear; lia)) as S32v.
  pose proof (frm_vis L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER W BX Mc modelc LKc crc Ac _ _ BI S88 ltac:(clear; lia) ltac:(clear; lia)) as S88v.
  destruct bq as [fb lenq sto].
  destruct (g8b_run fx Rc _ qo n1 fb lenq sto RI PF X20 X26 N1R (conj (conj ORP (conj ORG O8)) (conj OBIG (conj OZ (conj OW (conj OFR (conj OF (conj OSH (conj SOF (conj SOSH SOFR))))))))) OBQv S64v S32v S88v)
    as (fx1 & R1 & M1v & pMS & pMG & pFZ & pKS & p19 & pC136 & pC128).
  set (Wp := fun a => E - 136 <= a < E - 120).
  apply (L5DKA.bstage L ar C HI LY HIok M model LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2 G W _ Mc modelc LKc crc Ac fx fx1 Rc 0x932f8 R1 0x93350 M1v Wp K BI pMS pMG).
  { intros a Ha Hn. apply pFZ. exact Ha. exact Hn. }
  { intros a Ha Wa. subst Wp; cbn beta in Wa. wpf. }
  intros M1 model1 BI1 AH1 VIS1 MGM1 FRM1.
  apply (KF fx1 R1 M1 model1 BI1).
  - apply (rinvD_keep R E Rc R1 RI). intros k Hk0. apply pKS. revert Hk0. apply (L5K.incl_b DIDX). vm_compute; reflexivity.
  - intros x Hx. apply pKS. revert Hx. apply (L5K.incl_b [3; 4; 18; 20; 21; 22; 24; 25; 26; 27]%nat). vm_compute; reflexivity.
  - exact p19.
  - intros a Ha Hn. apply FRM1. exact Ha. exact Hn.
  - apply (xs_cell W BX Mc modelc LKc crc Ac M1 M1v (E - 136) _ BI VIS1 ltac:(clear; lia) ltac:(clear; lia) pC136).
  - apply (xs_cell W BX Mc modelc LKc crc Ac M1 M1v (E - 128) _ BI VIS1 ltac:(clear; lia) ltac:(clear; lia) pC128).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma dreg_wp W BX Mc modelc LKc crc Ac o b ws (m : Z) a :
  binv W BX Mc modelc LKc crc Ac -> aobj FF' o 32 -> tob (BX ++ LB) Mc o b ws ->
  m <= (match L5.bo_st b with L5.BInl _ _ => 2 | L5.BDyn cap _ => cap end) ->
  L5.bo_data o b <= a < L5.bo_data o b + 8 * m ->
  (aclient L ar LB FF E SCRD a -> ~ L5.outside W a) ->
  L5DKA.wp_ok L ar LB FF E SCRD SPA (docell E) F 3 W BX a.
Proof.
  intros BI AOB (OB & _ & SZ & INB) MC Ha WA. pose proof BI as (B1 & _).
  pose proof (aobj_facts L ar C HI LY HIok (BX ++ LB) FF' LKc crc Ac Mc modelc o 32 0 0 B1 AOB ltac:(clear; lia) ltac:(reflexivity)) as (OR & _).
  pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ B1) as (WB & _).
  destruct G as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG' F32 FLA' FLR FLBIG' NCF NCS].
  unfold L5.bo_data in *. destruct b as [fb len sto]. cbn [L5.bo_st] in *.
  destruct sto as [v0 v1|cap q].
  - split. { intros D. pose proof (OCR a D) as X. clear - X Ha MC OR SLO HSCR. lia. }
    split. 2: exact WA. split. apply (obj_client L ar (BX ++ LB) FF' 0 0 o 32 a AOB). clear - Ha MC; lia. clear - Ha OR; lia.
  - pose proof (WB (q, 8 * cap) (INB cap q eq_refl)) as ((R0 & R1 & R2 & R3 & R4 & R5) & _). cbn [fst snd] in *.
    rewrite (aly_img_lo L C LY), (aly_img_hi L C LY) in R1.
    split. { intros D. pose proof (OCR a D) as X. clear - X Ha MC R4 SLO HSCR. lia. }
    split. 2: exact WA. split. apply (block_client L ar (BX ++ LB) FF' 0 0 q (8 * cap) a (INB cap q eq_refl)). clear - Ha MC; lia. clear - Ha MC R1; lia.
Qed.

Lemma one_le_cap Mk o b : L5.big_at RSEGS Mk o b -> 1 <= match L5.bo_st b with L5.BInl _ _ => 2 | L5.BDyn cap _ => cap end.
Proof. destruct b as [fb len sto]. intros (_ & _ & _ & OST). cbn [L5.bo_st] in *. destruct sto. clear; lia. destruct OST as (_ & _ & _ & _ & X & _). clear - X; lia. Qed.

Lemma g9 (fx : FPState) Rc Mc modelc W BX LKc crc Ac to qo (br bq bd : L5.bigobj) wr wq wd (n l : Z) :
  binv W BX Mc modelc LKc crc Ac -> rinvD R E Rc ->
  getr Rc (reg 19) = Z_to_bv 64 n -> getr Rc (reg 27) = Z_to_bv 64 l ->
  aobj FF ro 32 -> aobj FF qo 32 -> tob (BX ++ LB) Mc ro br wr -> tob (BX ++ LB) Mc qo bq wq -> tob (BX ++ LB) Mc (F + 32) bd wd ->
  Z.of_nat (L5.bo_len br) = n + 1 -> Z.of_nat (L5.bo_len bq) = n - l -> Z.of_nat (L5.bo_len bd) = l + 1 -> l <= n <= 299 -> 0 <= l <= 298 ->
  2 ^ 63 <= nth_w wd (Z.to_nat l) ->
  L5.u64_at RSEGS Mc (E - 272) (l + 1) -> L5.u64_at RSEGS Mc (E - 264) to -> 0 <= to < 2 ^ 64 ->
  L5.u64_at RSEGS Mc (E - 240) (L5.bo_data ro br) -> L5.u64_at RSEGS Mc (E - 136) (L5.bo_data qo bq) -> L5.u64_at RSEGS Mc (E - 120) (L5.bo_data (F + 32) bd) ->
  (forall a, in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> L5.outside W a) ->
  (* [comment removed for export] *)
  (let Dr := L5.bo_data ro br in let Dq := L5.bo_data qo bq in let Dd := L5.bo_data (F + 32) bd in
   (Dr + 8 * (n + 1) <= Dq \/ Dq + 8 * (n - l) <= Dr) /\ (Dr + 8 * (n + 1) <= Dd \/ Dd + 8 * (l + 1) <= Dr) /\ (Dq + 8 * (n - l) <= Dd \/ Dd + 8 * (l + 1) <= Dq)) ->
  (* [comment removed for export] *)
  (forall a, L5.bo_data ro br <= a < L5.bo_data ro br + 8 * (n + 1) -> aclient L ar LB FF E SCRD a -> ~ L5.outside W a) ->
  (forall a, L5.bo_data qo bq <= a < L5.bo_data qo bq + 8 * (n - l) -> aclient L ar LB FF E SCRD a -> ~ L5.outside W a) ->
  (forall (fx1 : FPState) R1 M1 model1,
      binv W BX M1 model1 LKc crc Ac -> rinvD R E R1 -> getr R1 (reg 18) = getr Rc (reg 18) ->
      (forall a, 0 <= a < 2 ^ 64 -> ~ L5ADVGL.FP E (L5.bo_data ro br) (L5.bo_data qo bq) n l a -> M1 (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)) ->
      srealizes RSEGS SCFG (cfg (fx:=fx1) R1 0x93458 M1 model1) K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc 0x93350 Mc modelc) K.
Proof.
  intros BI RI X19 X27 AOR AOQ (OBR & OLR & SZR & INR) (OBQ & OLQ & SZQ & INQ) (OBD & OLD & SZD & IND) LENR LENQ LEND NR LR DTOP S112 S120 TOR S144 S248 S264 NW APART WDR WDQ KF.
  pose proof (pf_of_binv L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G W BX Mc modelc LKc crc Ac BI) as PF.
  assert (AOR' : aobj FF' ro 32) by (apply aobj_cons; exact AOR). assert (AOQ' : aobj FF' qo 32) by (apply aobj_cons; exact AOQ).
  assert (AOD' : aobj FF' (F + 32) 32) by (eapply L5ADVEA.loc_aobj; [exact G | clear; lia | clear; lia | reflexivity]).
  pose proof (len_le_cap Mc ro br OBR) as LCR. pose proof (len_le_cap Mc qo bq OBQ) as LCQ. pose proof (len_le_cap Mc (F + 32) bd OBD) as LCD. pose proof (one_le_cap Mc qo bq OBQ) as OCQ.
  set (mq := Z.max 1 (n - l)).
  assert (MQC : mq <= match L5.bo_st bq with L5.BInl _ _ => 2 | L5.BDyn cap _ => cap end) by (subst mq; clear - LCQ OCQ LENQ; lia).
  pose proof (dreg_facts L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G W BX Mc modelc LKc crc Ac ro br wr (n + 1) BI AOR' (conj OBR (conj OLR (conj SZR INR)))
                ltac:(clear - NR LR; lia) ltac:(rewrite <- LENR; exact LCR)) as ((RF1 & RF2 & RF3 & RF4) & RNS & ROI & RZ & RDEF & RWR & RVIS).
  pose proof (dreg_facts L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G W BX Mc modelc LKc crc Ac qo bq wq mq BI AOQ' (conj OBQ (conj OLQ (conj SZQ INQ)))
                ltac:(subst mq; clear; lia) MQC) as ((QF1 & QF2 & QF3 & QF4) & QNS & QOI & QZ & QDEF & QWR & QVIS).
  pose proof (dreg_facts L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G W BX Mc modelc LKc crc Ac (F + 32) bd wd (l + 1) BI AOD' (conj OBD (conj OLD (conj SZD IND)))
                ltac:(clear - LR; lia) ltac:(rewrite <- LEND; exact LCD)) as ((DF1 & DF2 & DF3 & DF4) & DNS & DOI & DZ & DDEF & DWR & DVIS).
  cbv zeta in *.
  pose proof (frm_z W BX Mc modelc LKc crc Ac BI NW) as FZv.
  pose proof (scr_def W BX Mc modelc LKc crc Ac 96 BI ltac:(clear; lia)) as (DSC & WSC).
  set (MV := mrestrict (ahid Ac modelc) Mc) in *. set (Dr := L5.bo_data ro br) in *. set (Dq := L5.bo_data qo bq) in *. set (Dd := L5.bo_data (F + 32) bd) in *.
  destruct (limb_at Mc (F + 32) bd wd l OBD OLD ltac:(clear - LEND LR; lia)) as (CDc & DRR). fold Dd in CDc. set (d := nth_w wd (Z.to_nat l)) in *.
  assert (CDv : L5.u64_at RSEGS MV (Dd + 8 * l) d).
  { eapply L5C.u64_at_agree. 4: exact CDc. 2: clear - DF1 LR; lia. 2: clear - DF4 LR; lia. intros i Hi. apply DVIS. clear - Hi LR; lia. }
  assert (FV8 : forall a v, L5.u64_at RSEGS Mc a v -> SPA <= a -> a + 8 <= E -> L5.u64_at RSEGS MV a v).
  { intros a v Hc H1 H2. exact (frm_vis L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER W BX Mc modelc LKc crc Ac a v BI Hc H1 H2). }
  pose proof G as G'. destruct G' as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG' F32 FLA' FLR FLBIG' NCF NCS]. clear OWNAG HH2 NCF NCS FLNC.
  destruct PF as (_ & IMGC0 & CSB0 & CUAR0 & _).
  assert (CEIL : ahl_ceil ar + 9104 <= E) by (clear - SLO HSCR; lia).
  assert (LC : L5ADVGL.lctx E to Dr Dq Dd d n l MV).
  { constructor.
    - exact ER.
    - exact EA.
    - clear - NR LR; lia.
    - exact WSC.
    - exact DSC.
    - split. exact IMGC0. split. exact CSB0. exact CUAR0.
    - apply FV8. exact S112. clear; lia. clear; lia.
    - apply FV8. exact S120. clear; lia. clear; lia.
    - apply FV8. exact S144. clear; lia. clear; lia.
    - apply FV8. exact S248. clear; lia. clear; lia.
    - apply FV8. exact S264. clear; lia. clear; lia.
    - exact FZv.
    - exact TOR.
    - split. exact RF1. split. exact RF4. split. exact RF2. split. exact RNS. exact ROI.
    - exact RWR.
    - exact RDEF.
    - exact RZ.
    - split. exact QF1. split. subst mq; clear - QF4 NR; lia. split. exact QF2.
      split. unfold L5ADVGL.nsh in *. subst mq. clear - QNS NR; lia. unfold L5ADVGL.oim in *. subst mq. clear - QOI NR; lia.
    - eapply L5.writable_sub. exact QWR. clear; lia. subst mq; clear - NR; lia.
    - eapply L5KA.zeros_at_sub. exact QZ. clear; lia. subst mq; clear - NR; lia.
    - split. exact DF1. split. exact DF4. split. exact DF2. exact DNS.
    - exact DDEF.
    - exact DZ.
    - split. exact CDv. clear - DTOP DRR; lia.
    - destruct APART as (A1 & A2 & A3). split. exact A1. split. exact A2. split. exact A3. split. clear - RF3 CEIL; lia. split. subst mq; clear - QF3 CEIL NR; lia. clear - DF3 CEIL; lia. }
  pose proof RI as (X2 & X8 & X9 & X3 & X4 & XSB).
  destruct (L5ADVGL.gloop_run E to Dr Dq Dd d n l fx Rc MV LC (conj X2 (conj X8 (conj X9 (conj X19 (conj XSB X27))))))
    as (fx1 & R1 & M1v & pMS & (pMG & pAG) & (k2 & k8 & k9 & k3 & k4) & k18 & k23).
  apply (L5DKA.bstage L ar C HI LY HIok M model LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2 G W _ Mc modelc LKc crc Ac fx fx1 Rc 0x93350 R1 0x93458 M1v
           (L5ADVGL.FP E Dr Dq n l) K BI pMS pMG).
  { exact pAG. }
  { intros a Ha [Wa|[Wa|[Wa|[Wa|Wa]]]].
    - eapply L5ADVHC.wp_scratch; hyp9 BI NW. clear - Wa HSCR; lia.
    - destruct Wa.
    - apply (L5DKA.wp_frame L ar HI LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2 G); [clear - Wa; lia | unfold docell; clear - Wa; lia].
    - apply (dreg_wp W BX Mc modelc LKc crc Ac ro br wr (n + 1) a BI AOR' (conj OBR (conj OLR (conj SZR INR))) ltac:(rewrite <- LENR; exact LCR) Wa (WDR a Wa)).
    - apply (dreg_wp W BX Mc modelc LKc crc Ac qo bq wq mq a BI AOQ' (conj OBQ (conj OLQ (conj SZQ INQ))) MQC ltac:(fold Dq; subst mq; clear - Wa; lia) (WDQ a Wa)). }
  intros M1 model1 BI1 AH1 VIS1 MGM1 FRM1.
  apply (KF fx1 R1 M1 model1 BI1).
  - split. exact k2. split. exact k8. split. exact k9. split. rewrite k3. exact X3. split. rewrite k4. exact X4. exact k23.
  - exact k18.
  - exact FRM1.
Qed.
End DIV.
End WithIface.
End SCFG_1.
End L5ADVGC.
