(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA IcptIfaceA LibIface
     AsanAcct AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5Words L5LazyA L5DefsA
     L5CoreA L5CoreSpecsA L5StepA L5ACmp L5CoreB L5ADetailH L5AFrameK L5DivKitA L5DivSpecsA L5OpmodSpecsA L5DivLeafSpecsA L5DivInnerSpecsA L5ACopyAS L5ADivH L5ADivT L5ADivD L5ADivE L5ADivEA L5ADivHC L5ADivHA L5ADivHO L5ADivPG1 L5ADivPG2 L5ADivGL L5ADivGA L5ADivGB.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require As0_code_92368_93368.
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
Local Notation SPA := (E - 352).
Hypothesis G : L5AFK.gctx L ar HI LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2.
Hypothesis ER : 140735332487680 <= E <= 140737488355328.
Hypothesis EA : aligned E 32.
Hypothesis HK : K [].
Hypothesis G4 : getr R (reg 4) = Z_to_bv 64 (hl_tp L).
Hypothesis HSCR : 352 + 4656 <= SCRD.
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

Local Ltac open_ctx BI :=
  let PF := fresh "PF" in
  pose proof (pf_of_binv L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G _ _ _ _ _ _ _ BI) as PF;
  destruct PF as (W352 & IMGC & CSB & CUAR & FDEFv & FWv & FSHWv & FLCv & FLWv);
  pose proof (NUM L ar HI R LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER) as ((FRG & FLRG & ERG) & FRP & FLRP & ALF & FBIG & FLBIG & FLA & SFA & SFLA & SFB);
  destruct (L5AFK.vis_facts L ar C HI LY HIok M model LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2 G _ _ _ _ _ _ _ BI) as (_ & OWNv & _ & (_ & _ & FV & SV & SHV));
  change (ff_bytes 3) with 512 in FV; change (ff_bytes 3 / 8) with 64 in SHV.

(* [comment removed for export] *)
(* [comment removed for export] *)

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
Lemma g7 (fx : FPState) Rc Mc modelc W BX LKc crc Ac Dq (br bd : L5.bigobj) wr wd (n l : Z) :
  binv W BX Mc modelc LKc crc Ac -> rinvD R E Rc ->
  getr Rc (reg 21) = Z_to_bv 64 2147450880 -> getr Rc (reg 23) = Z_to_bv 64 ro -> getr Rc (reg 24) = Z_to_bv 64 Dq -> getr Rc (reg 27) = Z_to_bv 64 (n + 1) -> 0 <= Dq < 2 ^ 64 ->
  aobj FF ro 32 -> tob (BX ++ LB) Mc ro br wr -> tob (BX ++ LB) Mc (F + 32) bd wd ->
  Z.of_nat (L5.bo_len br) = n + 1 -> Z.of_nat (L5.bo_len bd) = l + 1 -> 0 <= n <= 299 -> 0 <= l <= 298 ->
  L5.u64_at RSEGS Mc (E - 216) (l + 1) -> L5.u64_at RSEGS Mc (E - 224) (L5.bo_data (F + 32) bd) ->
  (forall (fx1 : FPState) R1 M1 model1,
      binv W BX M1 model1 LKc crc Ac -> rinvD R E R1 ->
      (forall x, In x [3; 4; 18; 23; 25; 27]%nat -> getr R1 (reg x) = getr Rc (reg x)) ->
      getr R1 (reg 19) = Z_to_bv 64 (L5.bo_data ro br) -> getr R1 (reg 20) = Z_to_bv 64 Dq ->
      getr R1 (reg 21) = Z_to_bv 64 ((L5.bo_data (F + 32) bd + 8 * l) / 8 + 2147450880) -> getr R1 (reg 22) = Z_to_bv 64 n ->
      getr R1 (reg 24) = Z_to_bv 64 (L5.bo_data (F + 32) bd + 8 * l) -> getr R1 (reg 26) = Z_to_bv 64 (ro / 8 + 2147450880) ->
      (forall a, 0 <= a < 2 ^ 64 -> ~ (E - 232 <= a < E - 224) -> M1 (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)) ->
      L5.u64_at RSEGS M1 (E - 232) l ->
      srealizes RSEGS SCFG (cfg (fx:=fx1) R1 (if nth_w wr (Z.to_nat n) <? nth_w wd (Z.to_nat l) then 0x9290c else 0x92860) M1 model1) K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc 0x927cc Mc modelc) K.
Proof.
  intros BI RI X21 X23 X24 X27 DQR AOR (OBR & OLR & SZR & INR) (OBD & OLD & SZD & IND) LENR LEND NR LR S136 S128 KF.
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
  set (MV := mrestrict (ahid Ac modelc) Mc) in *. set (Dr := L5.bo_data ro br) in *. set (Dd := L5.bo_data (F + 32) bd) in *.
  destruct (limb_at Mc ro br wr n OBR OLR ltac:(clear - LENR NR; lia)) as (CRc & VRR). fold Dr in CRc.
  destruct (limb_at Mc (F + 32) bd wd l OBD OLD ltac:(clear - LEND LR; lia)) as (CDc & DRR). fold Dd in CDc.
  set (vr := nth_w wr (Z.to_nat n)) in *. set (d := nth_w wd (Z.to_nat l)) in *.
  assert (ER' : 0 <= E - 352 /\ E <= 2 ^ 64) by (clear - ER; lia).
  assert (DRRG : 0 <= Dr /\ Dr + 8 * (n + 1) <= 2 ^ 64 /\ 0 <= Dd /\ Dd + 8 * (l + 1) <= 2 ^ 64) by (clear - RF1 DF1 NR LR; lia).
  assert (CRv : L5.u64_at RSEGS MV (Dr + 8 * n) vr).
  { eapply L5C.u64_at_agree. 4: exact CRc. 2: clear - DRRG NR; lia. 2: clear - DRRG NR; lia. intros i Hi. apply RVIS. clear - Hi NR; lia. }
  assert (CDv : L5.u64_at RSEGS MV (Dd + 8 * l) d).
  { eapply L5C.u64_at_agree. 4: exact CDc. 2: clear - DRRG LR; lia. 2: clear - DRRG LR; lia. intros i Hi. apply DVIS. clear - Hi LR; lia. }
  pose proof (frm_vis L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER W BX Mc modelc LKc crc Ac _ _ BI S136 ltac:(clear; lia) ltac:(clear; lia)) as S136v.
  pose proof (frm_vis L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER W BX Mc modelc LKc crc Ac _ _ BI S128 ltac:(clear; lia) ltac:(clear; lia)) as S128v.
  fold MV in S136v, S128v, OBRv, PF.
  destruct br as [fb lenr sto].
  destruct (g7_run L ar HI R LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER EA HSCR fx Rc MV Dq fb lenr sto n l Dd vr d RI PF X21 X23 X24 X27 DQR
              (conj (conj ORP (conj ORG O8)) (conj OBIG (conj OZ (conj OW (conj OFR (conj OF (conj OSH (conj SOF (conj SOSH SOFR))))))))) OBRv NR LR
              (conj RF1 (conj RF2 (conj RF3 (conj RF4 (conj RF5 RF6))))) (conj DF1 (conj DF2 (conj DF3 (conj DF4 (conj DF5 DF6))))) S136v S128v CRv VRR CDv DRR)
    as (fx1 & R1 & M1v & pMS & pMG & pFZ & pKS & p10 & p11 & p19 & p20 & p21 & p22 & p24 & p26 & pC0).
  pose proof (br_92508 fx1 R1 M1v) as BR. rewrite p10, p11, (bltu_Z vr d VRR DRR) in BR.
  set (Wp := fun a => E - 232 <= a < E - 224).
  open_ctx BI.
  apply (L5DKA.bstage L ar C HI LY HIok M model LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2 G W _ Mc modelc LKc crc Ac fx fx1 Rc 0x927cc R1
           (if vr <? d then 0x9290c else 0x92860) M1v Wp K BI (msteps_trans _ _ _ _ pMS BR) pMG).
  { intros a Ha Hn. apply pFZ. exact Ha. exact Hn. }
  { intros a Ha Wa. subst Wp; cbn beta in Wa. apply (L5DKA.wp_frame L ar HI LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2 G). clear - Wa; lia. unfold docell. clear - Wa; lia. }
  intros M1 model1 BI1 AH1 VIS1 MGM1 FRM1.
  apply (KF fx1 R1 M1 model1 BI1).
  - apply (rinvD_keep R E Rc R1 RI). intros k Hk0. apply pKS. revert Hk0. apply (L5K.incl_b DIDX). vm_compute; reflexivity.
  - intros x Hx. apply pKS. revert Hx. apply (L5K.incl_b [3; 4; 18; 23; 25; 27]%nat). vm_compute; reflexivity.
  - exact p19.
  - exact p20.
  - exact p21.
  - exact p22.
  - exact p24.
  - exact p26.
  - intros a Ha Hn. apply FRM1. exact Ha. exact Hn.
  - apply (proj1 (u64_at_vis (ahid Ac modelc) M1 (E - 232) l ltac:(eapply avis_sub; [exact SV | clear; lia | clear; lia]) ltac:(clear - ER; lia) ltac:(clear - ER; lia))). rewrite VIS1. exact pC0.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma g7b_run (fx : FPState) Rc MV fb (lenr : nat) sto : rinvD R E Rc -> pf E F fl MV -> getr Rc (reg 23) = Z_to_bv 64 ro -> ARGF E F MV ro ->
  L5.big_at RSEGS MV ro (L5.BO fb lenr sto) -> L5.u64_at RSEGS MV (E - 200) 2147450880 ->
  exists (fx' : FPState) R', msteps RSEGS (st fx Rc 0x92860 MV) (st fx' R' RESIZE MV)
    /\ (forall x, In x [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R' (reg x) = getr Rc (reg x))
    /\ getr R' (reg 1) = Z_to_bv 64 0x92888 /\ getr R' (reg 10) = Z_to_bv 64 ro /\ getr R' (reg 11) = Z_to_bv 64 (Z.of_nat lenr + 1).
Proof.
  intros RI PF X23 ((ORP & ORG & O8) & OBIG & OZ & OW & OFR & OF & OSH & SOF & SOSH & SOFR) OB S152.
  unfold pf in PF. destruct PF as (W352 & IMGC & CSB & CUAR & FDEFv & FWv & FSHWv & FLCv & FLWv).
  pose proof (NUM L ar HI R LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER) as ((FRG & FLRG & ERG) & FRP & FLRP & ALF & FBIG & FLBIG & FLA & SFA & SFLA & SFB).
  pose proof RI as (X2 & X8 & X9 & X3 & X4).
  assert (ER' : 140735332487584 <= E <= 140737488355328) by (clear - ER; lia).
  assert (OAL : aligned ro 8) by exact O8.
  destruct OB as (O0 & FBR & OL8 & OST). cbn [L5.bo_fb L5.bo_len L5.bo_st] in *.
  assert (LR : 0 <= Z.of_nat lenr <= 18446744073709551615 /\ 0 <= Z.of_nat lenr < 2 ^ 64).
  { destruct sto; [destruct OST as (_ & _ & _ & X & _) | destruct OST as (_ & _ & _ & X & X' & _)]; clear - X + clear - X X'; lia. }
  destruct LR as [LR LRG].
  pose proof (v5G7b_conc fx Rc MV (fun j => match j with 2%nat => E | 36%nat => ro | 40%nat => F | 58%nat => U Rc 1 | 72%nat => Z.of_nat lenr | _ => 0 end)) as P. cbn beta iota in P.
  feed P ltac:(first [apply UR | apply U_to | sc ]).
  destruct P as (fx1 & R1 & M1v & _ & _ & pEQ & (pMS & pKS & p1 & p10 & p11 & _)).
  assert (EQM : M1v = MV) by (apply mem_eq_of_agree; exact pEQ). rewrite EQM in pMS.
  exists fx1, R1. split. exact pMS. split. { intros x Hx. apply pKS. revert Hx. apply (L5K.incl_b [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat). vm_compute; reflexivity. }
  split. exact p1. split. exact p10. exact p11.
Qed.

Lemma g8_run (fx : FPState) Rc MV qo lenq fb (lenr : nat) sto : rinvD R E Rc -> pf E F fl MV -> getr Rc (reg 23) = Z_to_bv 64 ro -> getr Rc (reg 25) = Z_to_bv 64 lenq ->
  getr Rc (reg 26) = Z_to_bv 64 (ro / 8 + 2147450880) -> 0 <= qo < 2 ^ 64 -> 0 <= lenq < 2 ^ 64 -> ARGF E F MV ro ->
  L5.big_at RSEGS MV ro (L5.BO fb lenr sto) -> L5.u64_at RSEGS MV (E - 200) 2147450880 -> L5.u64_at RSEGS MV (E - 248) qo ->
  exists (fx' : FPState) R', msteps RSEGS (st fx Rc 0x92888 MV) (st fx' R' RESIZE MV)
    /\ (forall x, In x [2; 3; 4; 8; 9; 18; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R' (reg x) = getr Rc (reg x))
    /\ getr R' (reg 1) = Z_to_bv 64 0x928d0 /\ getr R' (reg 10) = Z_to_bv 64 qo /\ getr R' (reg 11) = Z_to_bv 64 (lenq + 1)
    /\ getr R' (reg 19) = Z_to_bv 64 (L5.bo_data ro (L5.BO fb lenr sto)) /\ getr R' (reg 20) = Z_to_bv 64 qo.
Proof.
  intros RI PF X23 X25 X26 QOR LQR ((ORP & ORG & O8) & OBIG & OZ & OW & OFR & OF & OSH & SOF & SOSH & SOFR) OB S152 S104.
  unfold pf in PF. destruct PF as (W352 & IMGC & CSB & CUAR & FDEFv & FWv & FSHWv & FLCv & FLWv).
  pose proof (NUM L ar HI R LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER) as ((FRG & FLRG & ERG) & FRP & FLRP & ALF & FBIG & FLBIG & FLA & SFA & SFLA & SFB).
  pose proof RI as (X2 & X8 & X9 & X3 & X4).
  assert (ER' : 140735332487584 <= E <= 140737488355328) by (clear - ER; lia).
  assert (OAL : aligned ro 8) by exact O8.
  destruct OB as (O0 & FBR & OL8 & OST). cbn [L5.bo_fb L5.bo_len L5.bo_st] in *. unfold L5.bo_data. cbn [L5.bo_st].
  assert (FBR' : 0 <= fb <= 255) by (clear - FBR; lia).
  assert (VR : 0 <= qo <= 18446744073709551615 /\ 0 <= lenq <= 18446744073709551615) by (clear - QOR LQR; lia). destruct VR as [VR1 VR2].
  destruct sto as [v0 v1|cap q].
  - destruct OST as (BT0 & _).
    pose proof (v5G8i_conc fx Rc MV (fun j => match j with 2%nat => E | 35%nat => qo | 36%nat => ro | 40%nat => F | 58%nat => U Rc 1 | 60%nat => fb | 67%nat => lenq | _ => 0 end)) as P. cbn beta iota in P.
    feed P ltac:(first [apply UR | apply U_to | sc ]).
    destruct P as (fx1 & R1 & M1v & _ & _ & pEQ & (pMS & pKS & p1 & p10 & p11 & p19 & p20)).
    assert (EQM : M1v = MV) by (apply mem_eq_of_agree; exact pEQ). rewrite EQM in pMS.
    exists fx1, R1. split. exact pMS. split. { intros x Hx. apply pKS. revert Hx. apply (L5K.incl_b [2; 3; 4; 8; 9; 18; 21; 22; 23; 24; 25; 26; 27]%nat). vm_compute; reflexivity. }
    split. exact p1. split. exact p10. split. exact p11. split. exact p19. exact p20.
  - destruct OST as (BT1 & O16 & O24 & _ & CAPR & _ & Q4096 & Q47 & _).
    assert (QRG : 0 <= q < 2 ^ 64 /\ 0 <= q <= 18446744073709551615) by (clear - Q4096 Q47 CAPR; lia). destruct QRG as [QRG QRG'].
    pose proof (v5G8d_conc fx Rc MV (fun j => match j with 2%nat => E | 35%nat => qo | 36%nat => ro | 40%nat => F | 58%nat => U Rc 1 | 60%nat => fb | 67%nat => lenq | 70%nat => q | _ => 0 end)) as P. cbn beta iota in P.
    feed P ltac:(first [apply UR | apply U_to | sc ]).
    destruct P as (fx1 & R1 & M1v & _ & _ & pEQ & (pMS & pKS & p1 & p10 & p11 & _ & p19 & p20)).
    assert (EQM : M1v = MV) by (apply mem_eq_of_agree; exact pEQ). rewrite EQM in pMS.
    exists fx1, R1. split. exact pMS. split. { intros x Hx. apply pKS. revert Hx. apply (L5K.incl_b [2; 3; 4; 8; 9; 18; 21; 22; 23; 24; 25; 26; 27]%nat). vm_compute; reflexivity. }
    split. exact p1. split. exact p10. split. exact p11. split. exact p19. exact p20.
Qed.

Lemma g8b_run (fx : FPState) Rc MV qo n1 fb (lenq : nat) sto : rinvD R E Rc -> pf E F fl MV -> getr Rc (reg 18) = Z_to_bv 64 (qo / 8 + 2147450880) -> getr Rc (reg 20) = Z_to_bv 64 qo ->
  getr Rc (reg 27) = Z_to_bv 64 n1 -> 0 <= n1 < 2 ^ 64 -> ARGF E F MV qo ->
  L5.big_at RSEGS MV qo (L5.BO fb lenq sto) -> L5.u64_at RSEGS MV (E - 200) 2147450880 ->
  exists (fx' : FPState) R', msteps RSEGS (st fx Rc 0x928d0 MV) (st fx' R' 0x9290c MV)
    /\ (forall x, In x [2; 3; 4; 8; 9; 18; 19; 21; 23; 24; 25; 26; 27]%nat -> getr R' (reg x) = getr Rc (reg x))
    /\ getr R' (reg 20) = Z_to_bv 64 (L5.bo_data qo (L5.BO fb lenq sto)) /\ getr R' (reg 22) = Z_to_bv 64 n1.
Proof.
  intros RI PF X18 X20 X27 N1R ((ORP & ORG & O8) & OBIG & OZ & OW & OFR & OF & OSH & SOF & SOSH & SOFR) OB S152.
  unfold pf in PF. destruct PF as (W352 & IMGC & CSB & CUAR & FDEFv & FWv & FSHWv & FLCv & FLWv).
  pose proof (NUM L ar HI R LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER) as ((FRG & FLRG & ERG) & FRP & FLRP & ALF & FBIG & FLBIG & FLA & SFA & SFLA & SFB).
  pose proof RI as (X2 & X8 & X9 & X3 & X4).
  assert (ER' : 140735332487584 <= E <= 140737488355328) by (clear - ER; lia).
  assert (OAL : aligned qo 8) by exact O8.
  destruct OB as (O0 & FBR & OL8 & OST). cbn [L5.bo_fb L5.bo_len L5.bo_st] in *. unfold L5.bo_data. cbn [L5.bo_st].
  assert (FBR' : 0 <= fb <= 255) by (clear - FBR; lia).
  assert (VR : 0 <= n1 <= 18446744073709551615) by (clear - N1R; lia).
  destruct sto as [v0 v1|cap q].
  - destruct OST as (BT0 & _).
    pose proof (v5G8bi_conc fx Rc MV (fun j => match j with 2%nat => E | 35%nat => qo | 40%nat => F | 58%nat => U Rc 1 | 60%nat => fb | 66%nat => n1 | _ => 0 end)) as P. cbn beta iota in P.
    feed P ltac:(first [apply UR | apply U_to | sc ]).
    destruct P as (fx1 & R1 & M1v & _ & _ & pEQ & (pMS & pKS & _ & p20 & p22)).
    assert (EQM : M1v = MV) by (apply mem_eq_of_agree; exact pEQ). rewrite EQM in pMS.
    exists fx1, R1. split. exact pMS. split. { intros x Hx. apply pKS. revert Hx. apply (L5K.incl_b [2; 3; 4; 8; 9; 18; 19; 21; 23; 24; 25; 26; 27]%nat). vm_compute; reflexivity. }
    split. exact p20. exact p22.
  - destruct OST as (BT1 & O16 & O24 & _ & CAPR & _ & Q4096 & Q47 & _).
    assert (QRG : 0 <= q < 2 ^ 64 /\ 0 <= q <= 18446744073709551615) by (clear - Q4096 Q47 CAPR; lia). destruct QRG as [QRG QRG'].
    pose proof (v5G8bd_conc fx Rc MV (fun j => match j with 2%nat => E | 35%nat => qo | 40%nat => F | 58%nat => U Rc 1 | 60%nat => fb | 66%nat => n1 | 68%nat => q | _ => 0 end)) as P. cbn beta iota in P.
    feed P ltac:(first [apply UR | apply U_to | sc ]).
    destruct P as (fx1 & R1 & M1v & _ & _ & pEQ & (pMS & pKS & _ & _ & _ & p20 & p22)).
    assert (EQM : M1v = MV) by (apply mem_eq_of_agree; exact pEQ). rewrite EQM in pMS.
    exists fx1, R1. split. exact pMS. split. { intros x Hx. apply pKS. revert Hx. apply (L5K.incl_b [2; 3; 4; 8; 9; 18; 19; 21; 23; 24; 25; 26; 27]%nat). vm_compute; reflexivity. }
    split. exact p20. exact p22.
Qed.

(* [comment removed for export] *)
Lemma g7b (fx : FPState) Rc Mc modelc W BX LKc crc Ac (br : L5.bigobj) :
  binv W BX Mc modelc LKc crc Ac -> rinvD R E Rc -> getr Rc (reg 23) = Z_to_bv 64 ro ->
  aobj FF ro 32 -> shadow_zero Mc ro 4 -> L5.big_at RSEGS Mc ro br -> L5.u64_at RSEGS Mc (E - 200) 2147450880 ->
  (forall (fx1 : FPState) R1 model1,
      binv W BX Mc model1 LKc crc Ac -> rinvD R E R1 ->
      (forall x, In x [3; 4; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R1 (reg x) = getr Rc (reg x)) ->
      getr R1 (reg 1) = Z_to_bv 64 0x92888 -> getr R1 (reg 10) = Z_to_bv 64 ro -> getr R1 (reg 11) = Z_to_bv 64 (Z.of_nat (L5.bo_len br) + 1) ->
      srealizes RSEGS SCFG (cfg (fx:=fx1) R1 RESIZE Mc model1) K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc 0x92860 Mc modelc) K.
Proof.
  intros BI RI X23 AOR SZR OBR S152 KF.
  pose proof (arg_facts L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G W BX Mc modelc LKc crc Ac ro BI AOR SZR)
    as ((ORP & ORG & O8) & OBIG & OZ & OW & OFR & OF & OSH & SOF & SOSH & SOFR & _).
  pose proof (pf_of_binv L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G W BX Mc modelc LKc crc Ac BI) as PF.
  pose proof (big_vis W BX Mc modelc LKc crc Ac ro br BI AOR SZR OBR) as OBRv.
  pose proof (frm_vis L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER W BX Mc modelc LKc crc Ac _ _ BI S152 ltac:(clear; lia) ltac:(clear; lia)) as S152v.
  pose proof BI as (B1 & B2 & _). destruct br as [fb lenr sto].
  destruct (g7b_run fx Rc _ fb lenr sto RI PF X23 (conj (conj ORP (conj ORG O8)) (conj OBIG (conj OZ (conj OW (conj OFR (conj OF (conj OSH (conj SOF (conj SOSH SOFR))))))))) OBRv S152v)
    as (fx1 & R1 & pMS & pKS & p1 & p10 & p11).
  apply (apure L ar C HI LY HIok (BX ++ LB) FF' LKc crc Ac Mc modelc fx fx1 Rc 0x92860 R1 RESIZE K B1 B2 pMS).
  intros model1 HH1 AM1 RT1 AH1.
  pose proof (L5AFK.binv_model L ar HI M model LB FF LK A E SCRD SPA (down E F ro R) F 3 W BX Mc modelc LKc crc Ac model1 BI HH1 AM1 RT1) as BI1.
  apply (KF fx1 R1 model1 BI1).
  - apply (rinvD_keep R E Rc R1 RI). intros k Hk0. apply pKS. revert Hk0. apply (L5K.incl_b DIDX). vm_compute; reflexivity.
  - intros x Hx. apply pKS. revert Hx. apply (L5K.incl_b [3; 4; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat). vm_compute; reflexivity.
  - exact p1.
  - exact p10.
  - exact p11.
Qed.

Lemma g8 (fx : FPState) Rc Mc modelc W BX LKc crc Ac qo lenq (br : L5.bigobj) :
  binv W BX Mc modelc LKc crc Ac -> rinvD R E Rc -> getr Rc (reg 23) = Z_to_bv 64 ro -> getr Rc (reg 25) = Z_to_bv 64 lenq ->
  getr Rc (reg 26) = Z_to_bv 64 (ro / 8 + 2147450880) -> 0 <= qo < 2 ^ 64 -> 0 <= lenq < 2 ^ 64 ->
  aobj FF ro 32 -> shadow_zero Mc ro 4 -> L5.big_at RSEGS Mc ro br -> L5.u64_at RSEGS Mc (E - 200) 2147450880 -> L5.u64_at RSEGS Mc (E - 248) qo ->
  (forall (fx1 : FPState) R1 model1,
      binv W BX Mc model1 LKc crc Ac -> rinvD R E R1 ->
      (forall x, In x [3; 4; 18; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R1 (reg x) = getr Rc (reg x)) ->
      getr R1 (reg 1) = Z_to_bv 64 0x928d0 -> getr R1 (reg 10) = Z_to_bv 64 qo -> getr R1 (reg 11) = Z_to_bv 64 (lenq + 1) ->
      getr R1 (reg 19) = Z_to_bv 64 (L5.bo_data ro br) -> getr R1 (reg 20) = Z_to_bv 64 qo ->
      srealizes RSEGS SCFG (cfg (fx:=fx1) R1 RESIZE Mc model1) K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc 0x92888 Mc modelc) K.
Proof.
  intros BI RI X23 X25 X26 QOR LQR AOR SZR OBR S152 S104 KF.
  pose proof (arg_facts L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G W BX Mc modelc LKc crc Ac ro BI AOR SZR)
    as ((ORP & ORG & O8) & OBIG & OZ & OW & OFR & OF & OSH & SOF & SOSH & SOFR & _).
  pose proof (pf_of_binv L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G W BX Mc modelc LKc crc Ac BI) as PF.
  pose proof (big_vis W BX Mc modelc LKc crc Ac ro br BI AOR SZR OBR) as OBRv.
  pose proof (frm_vis L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER W BX Mc modelc LKc crc Ac _ _ BI S152 ltac:(clear; lia) ltac:(clear; lia)) as S152v.
  pose proof (frm_vis L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER W BX Mc modelc LKc crc Ac _ _ BI S104 ltac:(clear; lia) ltac:(clear; lia)) as S104v.
  pose proof BI as (B1 & B2 & _). destruct br as [fb lenr sto].
  destruct (g8_run fx Rc _ qo lenq fb lenr sto RI PF X23 X25 X26 QOR LQR (conj (conj ORP (conj ORG O8)) (conj OBIG (conj OZ (conj OW (conj OFR (conj OF (conj OSH (conj SOF (conj SOSH SOFR))))))))) OBRv S152v S104v)
    as (fx1 & R1 & pMS & pKS & p1 & p10 & p11 & p19 & p20).
  apply (apure L ar C HI LY HIok (BX ++ LB) FF' LKc crc Ac Mc modelc fx fx1 Rc 0x92888 R1 RESIZE K B1 B2 pMS).
  intros model1 HH1 AM1 RT1 AH1.
  pose proof (L5AFK.binv_model L ar HI M model LB FF LK A E SCRD SPA (down E F ro R) F 3 W BX Mc modelc LKc crc Ac model1 BI HH1 AM1 RT1) as BI1.
  apply (KF fx1 R1 model1 BI1).
  - apply (rinvD_keep R E Rc R1 RI). intros k Hk0. apply pKS. revert Hk0. apply (L5K.incl_b DIDX). vm_compute; reflexivity.
  - intros x Hx. apply pKS. revert Hx. apply (L5K.incl_b [3; 4; 18; 21; 22; 23; 24; 25; 26; 27]%nat). vm_compute; reflexivity.
  - exact p1.
  - exact p10.
  - exact p11.
  - exact p19.
  - exact p20.
Qed.

Lemma g8b (fx : FPState) Rc Mc modelc W BX LKc crc Ac qo n1 (bq : L5.bigobj) :
  binv W BX Mc modelc LKc crc Ac -> rinvD R E Rc -> getr Rc (reg 18) = Z_to_bv 64 (qo / 8 + 2147450880) -> getr Rc (reg 20) = Z_to_bv 64 qo ->
  getr Rc (reg 27) = Z_to_bv 64 n1 -> 0 <= n1 < 2 ^ 64 ->
  aobj FF qo 32 -> shadow_zero Mc qo 4 -> L5.big_at RSEGS Mc qo bq -> L5.u64_at RSEGS Mc (E - 200) 2147450880 ->
  (forall (fx1 : FPState) R1 model1,
      binv W BX Mc model1 LKc crc Ac -> rinvD R E R1 ->
      (forall x, In x [3; 4; 18; 19; 21; 23; 24; 25; 26; 27]%nat -> getr R1 (reg x) = getr Rc (reg x)) ->
      getr R1 (reg 20) = Z_to_bv 64 (L5.bo_data qo bq) -> getr R1 (reg 22) = Z_to_bv 64 n1 ->
      srealizes RSEGS SCFG (cfg (fx:=fx1) R1 0x9290c Mc model1) K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc 0x928d0 Mc modelc) K.
Proof.
  intros BI RI X18 X20 X27 N1R AOQ SZQ OBQ S152 KF.
  pose proof (arg_facts L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G W BX Mc modelc LKc crc Ac qo BI AOQ SZQ)
    as ((ORP & ORG & O8) & OBIG & OZ & OW & OFR & OF & OSH & SOF & SOSH & SOFR & _).
  pose proof (pf_of_binv L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G W BX Mc modelc LKc crc Ac BI) as PF.
  pose proof (big_vis W BX Mc modelc LKc crc Ac qo bq BI AOQ SZQ OBQ) as OBQv.
  pose proof (frm_vis L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER W BX Mc modelc LKc crc Ac _ _ BI S152 ltac:(clear; lia) ltac:(clear; lia)) as S152v.
  pose proof BI as (B1 & B2 & _). destruct bq as [fb lenq sto].
  destruct (g8b_run fx Rc _ qo n1 fb lenq sto RI PF X18 X20 X27 N1R (conj (conj ORP (conj ORG O8)) (conj OBIG (conj OZ (conj OW (conj OFR (conj OF (conj OSH (conj SOF (conj SOSH SOFR))))))))) OBQv S152v)
    as (fx1 & R1 & pMS & pKS & p20 & p22).
  apply (apure L ar C HI LY HIok (BX ++ LB) FF' LKc crc Ac Mc modelc fx fx1 Rc 0x928d0 R1 0x9290c K B1 B2 pMS).
  intros model1 HH1 AM1 RT1 AH1.
  pose proof (L5AFK.binv_model L ar HI M model LB FF LK A E SCRD SPA (down E F ro R) F 3 W BX Mc modelc LKc crc Ac model1 BI HH1 AM1 RT1) as BI1.
  apply (KF fx1 R1 model1 BI1).
  - apply (rinvD_keep R E Rc R1 RI). intros k Hk0. apply pKS. revert Hk0. apply (L5K.incl_b DIDX). vm_compute; reflexivity.
  - intros x Hx. apply pKS. revert Hx. apply (L5K.incl_b [3; 4; 18; 19; 21; 23; 24; 25; 26; 27]%nat). vm_compute; reflexivity.
  - exact p20.
  - exact p22.
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
  getr Rc (reg 19) = Z_to_bv 64 (L5.bo_data ro br) -> getr Rc (reg 20) = Z_to_bv 64 (L5.bo_data qo bq) ->
  getr Rc (reg 21) = Z_to_bv 64 ((L5.bo_data (F + 32) bd + 8 * l) / 8 + 2147450880) -> getr Rc (reg 22) = Z_to_bv 64 n ->
  getr Rc (reg 24) = Z_to_bv 64 (L5.bo_data (F + 32) bd + 8 * l) ->
  aobj FF ro 32 -> aobj FF qo 32 -> tob (BX ++ LB) Mc ro br wr -> tob (BX ++ LB) Mc qo bq wq -> tob (BX ++ LB) Mc (F + 32) bd wd ->
  Z.of_nat (L5.bo_len br) = n + 1 -> Z.of_nat (L5.bo_len bq) = n - l -> Z.of_nat (L5.bo_len bd) = l + 1 -> l <= n <= 299 -> 0 <= l <= 298 ->
  2 ^ 63 <= nth_w wd (Z.to_nat l) ->
  L5.u64_at RSEGS Mc (E - 232) l -> L5.u64_at RSEGS Mc (E - 224) (L5.bo_data (F + 32) bd) -> L5.u64_at RSEGS Mc (E - 216) (l + 1) ->
  L5.u64_at RSEGS Mc (E - 200) 2147450880 -> L5.u64_at RSEGS Mc (E - 208) to -> 0 <= to < 2 ^ 64 ->
  shadow_zero Mc (E - 184) 1 ->
  (* [comment removed for export] *)
  (let Dr := L5.bo_data ro br in let Dq := L5.bo_data qo bq in let Dd := L5.bo_data (F + 32) bd in
   (Dr + 8 * (n + 1) <= Dq \/ Dq + 8 * (n - l) <= Dr) /\ (Dr + 8 * (n + 1) <= Dd \/ Dd + 8 * (l + 1) <= Dr) /\ (Dq + 8 * (n - l) <= Dd \/ Dd + 8 * (l + 1) <= Dq)) ->
  (* [comment removed for export] *)
  (forall a, L5.bo_data ro br <= a < L5.bo_data ro br + 8 * (n + 1) -> aclient L ar LB FF E SCRD a -> ~ L5.outside W a) ->
  (forall a, L5.bo_data qo bq <= a < L5.bo_data qo bq + 8 * (n - l) -> aclient L ar LB FF E SCRD a -> ~ L5.outside W a) ->
  (forall (fx1 : FPState) R1 M1 model1,
      binv W BX M1 model1 LKc crc Ac -> rinvD R E R1 ->
      (forall a, 0 <= a < 2 ^ 64 -> ~ L5ADVGL.FP E (L5.bo_data ro br) (L5.bo_data qo bq) n l a -> M1 (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)) ->
      L5.u64_at RSEGS M1 (E - 328) (U Rc 18) -> L5.u64_at RSEGS M1 (E - 320) (U Rc 26) ->
      srealizes RSEGS SCFG (cfg (fx:=fx1) R1 0x929e8 M1 model1) K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc 0x9290c Mc modelc) K.
Proof.
  intros BI RI X19 X20 X21 X22 X24 AOR AOQ (OBR & OLR & SZR & INR) (OBQ & OLQ & SZQ & INQ) (OBD & OLD & SZD & IND) LENR LENQ LEND NR LR DTOP S120 S128 S136 S152 S144 TOR QCZ APART WDR WDQ KF.
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
  set (MV := mrestrict (ahid Ac modelc) Mc) in *. set (Dr := L5.bo_data ro br) in *. set (Dq := L5.bo_data qo bq) in *. set (Dd := L5.bo_data (F + 32) bd) in *.
  destruct (limb_at Mc (F + 32) bd wd l OBD OLD ltac:(clear - LEND LR; lia)) as (CDc & DRR). fold Dd in CDc. set (d := nth_w wd (Z.to_nat l)) in *.
  assert (CDv : L5.u64_at RSEGS MV (Dd + 8 * l) d).
  { eapply L5C.u64_at_agree. 4: exact CDc. 2: clear - DF1 LR; lia. 2: clear - DF4 LR; lia. intros i Hi. apply DVIS. clear - Hi LR; lia. }
  assert (FV8 : forall a v, L5.u64_at RSEGS Mc a v -> SPA <= a -> a + 8 <= E -> L5.u64_at RSEGS MV a v).
  { intros a v Hc H1 H2. exact (frm_vis L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER W BX Mc modelc LKc crc Ac a v BI Hc H1 H2). }
  pose proof BI as (B1 & _ & _ & _ & _ & B6 & _).
  pose proof (vis_pack L ar C HI LY HIok (BX ++ LB) FF' LKc crc Ac Mc modelc B1) as (_ & VIS & _ & _ & _ & _ & _ & VSS).
  pose proof G as G'. destruct G' as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG' F32 FLA' FLR FLBIG' NCF NCS]. clear OWNAG HH2 NCF NCS FLNC.
  destruct PF as (_ & IMGC0 & CSB0 & CUAR0 & _).
  assert (DSC : L5.defined MV (SPA - 80) (352 + 80)).
  { apply (proj2 (defined_vis (ahid Ac modelc) Mc (SPA - 80) (352 + 80) (VIS (SPA - 80) (352 + 80) ltac:(clear - SLO HSCR; lia) ltac:(clear - ER; lia)))).
    destruct B6 as (_ & _ & _ & _ & DSCR & _). eapply L5.defined_sub. exact DSCR. clear - HSCR; lia. clear; lia. }
  assert (CEIL : ahl_ceil ar + 9104 <= E) by (clear - SLO HSCR; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (QCD : (E - 184) / 8 * 8 = E - 184 /\ ahl_ceil ar / 8 <= (E - 184) / 8 /\ (E - 184) / 8 <= (ar_sptop ar - 1) / 8) by (clear - EA CEIL SHI; unfold aligned in EA; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  assert (QCv : L5KA.zeros_at MV ((E - 184) / 8 + 2147450880) 1).
  { intros i Hi. assert (i = 0) by (clear - Hi; lia). subst i. unfold MV. rewrite L5LZ.mrestrict_visible'.
    - specialize (QCZ 0 ltac:(clear; lia)). unfold byte_at, S, SB in QCZ. exact QCZ.
    - apply (VSS ((E - 184) / 8 + 2147450880) 1 ltac:(intros j Hj; unfold in_shadow_of, S, SB; replace (ahl_ceil ar + (ar_sptop ar - ahl_ceil ar) - 1) with (ar_sptop ar - 1) by (clear; lia); clear - Hj QCD; lia) 0). clear; lia. }
  assert (LC : L5ADVGL.lctx E to Dr Dq Dd d n l ((Dd + 8 * l) / 8 + 2147450880) MV).
  { constructor.
    - exact ER.
    - exact EA.
    - clear - NR LR; lia.
    - apply (L5C.writable_of_defined RSEGS). exact DSC. clear - ER; lia. clear - ER; lia.
    - exact DSC.
    - split. exact IMGC0. split. exact CSB0. exact CUAR0.
    - apply FV8. exact S120. clear; lia. clear; lia.
    - apply FV8. exact S128. clear; lia. clear; lia.
    - apply FV8. exact S136. clear; lia. clear; lia.
    - apply FV8. exact S152. clear; lia. clear; lia.
    - apply FV8. exact S144. clear; lia. clear; lia.
    - exact TOR.
    - split. exact RF1. split. clear - RF3 CEIL ER; lia. split. exact RF2. split. exact RNS. exact ROI.
    - exact RWR.
    - exact RDEF.
    - exact RZ.
    - split. exact QF1. split. subst mq; clear - QF3 CEIL ER; lia. split. exact QF2.
      split. unfold L5ADVGL.nsh in *. subst mq. clear - QNS NR; lia. unfold L5ADVGL.oim in *. subst mq. clear - QOI NR; lia.
    - eapply L5.writable_sub. exact QWR. clear; lia. subst mq; clear - NR; lia.
    - eapply L5KA.zeros_at_sub. exact QZ. clear; lia. subst mq; clear - NR; lia.
    - split. exact DF1. split. clear - DF3 CEIL ER; lia. split. exact DF2. exact DNS.
    - exact DDEF.
    - exact DZ.
    - split. exact CDv. clear - DTOP DRR; lia.
    - reflexivity.
    - exact QCv.
    - destruct APART as (A1 & A2 & A3). split. exact A1. split. exact A2. split. exact A3. split. clear - RF3 CEIL; lia. split. subst mq; clear - QF3 CEIL NR; lia. clear - DF3 CEIL; lia. }
  pose proof RI as (X2 & X8 & X9 & X3 & X4).
  destruct (L5ADVGL.gloop_run E to Dr Dq Dd d n l ((Dd + 8 * l) / 8 + 2147450880) fx Rc MV LC (conj X2 (conj X8 (conj X9 (conj X19 (conj X20 (conj X21 (conj X22 X24))))))))
    as (fx1 & R1 & M1v & pMS & (pMG & pAG) & (k2 & k8 & k9 & k3 & k4) & pC0 & pC1).
  open_ctx BI.
  apply (L5DKA.bstage L ar C HI LY HIok M model LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2 G W _ Mc modelc LKc crc Ac fx fx1 Rc 0x9290c R1 0x929e8 M1v
           (L5ADVGL.FP E Dr Dq n l) K BI pMS pMG).
  { exact pAG. }
  { intros a Ha [Wa|[Wa|[Wa|[Wa|Wa]]]].
    - apply (wp_scratch L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G W BX Mc modelc LKc crc Ac a BI). clear - Wa HSCR; lia.
    - apply (L5DKA.wp_frame L ar HI LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2 G); [clear - Wa; lia | unfold docell; clear - Wa; lia].
    - apply (L5DKA.wp_frame L ar HI LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2 G); [clear - Wa; lia | unfold docell; clear - Wa; lia].
    - apply (dreg_wp W BX Mc modelc LKc crc Ac ro br wr (n + 1) a BI AOR' (conj OBR (conj OLR (conj SZR INR))) ltac:(rewrite <- LENR; exact LCR) Wa (WDR a Wa)).
    - apply (dreg_wp W BX Mc modelc LKc crc Ac qo bq wq mq a BI AOQ' (conj OBQ (conj OLQ (conj SZQ INQ))) MQC ltac:(fold Dq; subst mq; clear - Wa; lia) (WDQ a Wa)). }
  intros M1 model1 BI1 AH1 VIS1 MGM1 FRM1.
  apply (KF fx1 R1 M1 model1 BI1).
  - split. exact k2. split. exact k8. split. exact k9. split. rewrite k3. exact X3. rewrite k4. exact X4.
  - exact FRM1.
  - apply (proj1 (u64_at_vis (ahid Ac modelc) M1 (E - 328) _ ltac:(eapply avis_sub; [exact SV | clear; lia | clear; lia]) ltac:(clear - ER; lia) ltac:(clear - ER; lia))). rewrite VIS1. exact pC0.
  - apply (proj1 (u64_at_vis (ahid Ac modelc) M1 (E - 320) _ ltac:(eapply avis_sub; [exact SV | clear; lia | clear; lia]) ltac:(clear - ER; lia) ltac:(clear - ER; lia))). rewrite VIS1. exact pC1.
Qed.
End DIV.
End WithIface.
End SCFG_1.
End L5ADVGC.
