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
     AsanAcct AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5LazyA L5DefsAB0
     L5Cmp L5CoreAB0 L5CoreSpecsAB0 L5StepAB0 L5CoreBB0 L5BDetailG L5BFrameK L5DivKitAB0 L5BDivH L5BDivT L5BDivD L5BDivPH L5BDivPL L5BDivE L5BDivEA L5BDivHC L5BDivHD L5BDivHA L5BRed L5BDivHL.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5ADVHM.
Import L5A. Import L5CA. Import L5CSA. Import L5SA. Import L5CB. Import L5ADH. Import L5ADVH. Import L5ADVT. Import L5ADVD. Import L5ADVE. Import L5ADVEA. Import L5ADVHC. Import L5ADVHD. Import L5ADVHA. Import L5ADIVPH. Import L5ADIVPL. Import L5ADVHL.
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Local Ltac inl := apply L5K.in_b; vm_compute; reflexivity.
Local Ltac blia := keep_arith; first [ (repeat match goal with H : _ \/ _ |- _ => clear H end); lia
                                     | match goal with H : _ \/ _ |- _ => clear_disj_but H; destruct H; lia end ].
Local Ltac asm := match goal with H : ?T |- ?G => constr_eq T G; exact H end.
Local Ltac algn := lazymatch goal with |- ?h _ (Zpos _) => is_const h; lazymatch h with Z.le => fail | Z.lt => fail | Z.ge => fail | Z.gt => fail | _ => assumption end end.
Local Ltac sc := first [ asm | rk | gmem | algn | (arith_goal; first [asm | blia]) | assumption ].

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
Hypothesis FFR1 : ffrk 1 FF LK 4.
Hypothesis FFRS : ffrs FF E.
Hypothesis Hrsz : resize_spec L ar HI.
Hypothesis Hdel : opdel_sized_spec L ar HI.
Hypothesis RA : L5.ra_ok r.
Hypothesis UR1 : U R 1 = r.
Hypothesis G2 : getr R (reg 2) = Z_to_bv 64 E.
Local Notation binv := (L5AFK.binv L ar HI M model LB FF LK A E SCRD SPA (down E F ro R) F 3).
Local Notation FF' := ((F, 3, SPA + 32) :: FF).
Local Notation SH := (F / 8 + 2147450880).

Local Ltac open_ctx BI :=
  let PF := fresh "PF" in
  pose proof (pf_of_binv L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G _ _ _ _ _ _ _ BI) as PF;
  destruct PF as (W384 & IMGC & CSB & CUAR & FDEFv & FWv & FSHWv & FLCv & FLWv);
  pose proof (NUM L ar HI R LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER) as ((FRG & FLRG & ERG) & FRP & FLRP & ALF & FBIG & FLBIG & FLA & SFA & SFLA & SFB);
  destruct (L5AFK.vis_facts L ar C HI LY HIok M model LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2 G _ _ _ _ _ _ _ BI) as (_ & OWNv & _ & (_ & _ & FV & SV & SHV));
  change (ff_bytes 3) with 512 in FV; change (ff_bytes 3 / 8) with 64 in SHV.


(* [comment removed for export] *)
Lemma big_at_vis (H : word -> bool) (Mx : word -> option byte) o b : avis H o 32 -> 0 <= o -> o + 32 <= 2 ^ 64 -> (L5.big_at RSEGS (mrestrict H Mx) o b <-> L5.big_at RSEGS Mx o b).
Proof.
  intros V H0 H1. split; intros OB; (eapply L5C.big_at_agree; [ | exact H0 | exact H1 | exact OB]); intros i Hi; replace i with (o + (i - o)) by (clear; lia);
    [symmetry|]; apply mrestrict_visible; apply V; clear - Hi; lia.
Qed.
Lemma red_inl (fx : FPState) Rc Mc modelc W BX LKc crc Ac o pcn fb n v0 v1 :
  binv W BX Mc modelc LKc crc Ac -> rinvD R E Rc -> getr Rc (reg 10) = Z_to_bv 64 o -> getr Rc (reg 1) = Z_to_bv 64 pcn -> L5.ra_ok pcn ->
  L5.big_at RSEGS Mc o (L5.BO fb n (L5.BInl v0 v1)) -> aobj FF o 32 -> shadow_zero Mc o 4 -> (forall a, o <= a < o + 16 -> ~ L5.outside W a) ->
  (forall (fx1 : FPState) R1 M1 model1 fb' n',
      binv W BX M1 model1 LKc crc Ac -> (forall x, In x L5ARED.KS -> getr R1 (reg x) = getr Rc (reg x)) -> getr R1 (reg 2) = Z_to_bv 64 SPA -> getr R1 (reg 10) = Z_to_bv 64 o ->
      (forall a, 0 <= a < 2 ^ 64 -> ~ (o <= a < o + 16) -> ~ (SPA - 16 <= a < SPA) -> M1 (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)) ->
      L5.big_at RSEGS M1 o (L5.BO fb' n' (L5.BInl v0 v1)) -> (fb' = fb \/ fb' = Z.land fb 253) ->
      srealizes RSEGS SCFG (cfg (fx:=fx1) R1 pcn M1 model1) K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc L5ARED.REDUCE Mc modelc) K.
Proof.
  intros BI RI X10 X1 RAn OB AOB SZ WRO KF. open_ctx BI. pose proof RI as (X2 & X8 & X9 & X3 & X4 & XSB). pose proof BI as (B1 & _ & _ & _ & _ & B6 & _).
  pose proof (arg_facts L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G W _ Mc modelc LKc crc Ac o BI AOB SZ)
    as ((ORP & ORG & O8) & OBIG & OZv & OWv & OFR & OF & OSH & SOF & SOSH & SOFR & XB & XC & OCL).
  pose proof (aobj_facts L ar C HI LY HIok (BX ++ LB) FF' LKc crc Ac Mc modelc o 32 0 0 B1 (aobj_cons _ _ _ _ AOB) ltac:(clear; lia) ltac:(reflexivity)) as ((OLO & OCE & _) & _ & _ & OVIS & _).
  pose proof (vis_pack L ar C HI LY HIok (BX ++ LB) FF' LKc crc Ac Mc modelc B1) as (_ & VIS & _).
  assert (SLO : ahl_ceil ar + 4096 + SCRD <= E) by (destruct G as [_ _ SLO0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _]; exact SLO0).
  set (MV := mrestrict (ahid Ac modelc) Mc) in *.
  assert (OBv : L5.big_at RSEGS MV o (L5.BO fb n (L5.BInl v0 v1))) by (apply (proj2 (big_at_vis _ Mc o _ OVIS ltac:(clear - ORP; lia) ltac:(clear - ORP; lia))); exact OB).
  pose proof OB as (_ & FBR & _ & (_ & _ & _ & N2 & V0R & V1R)). cbn [L5.bo_fb L5.bo_len L5.bo_st] in FBR, N2, V0R, V1R.
  assert (OLv : L5C.obj_limbs RSEGS MV (L5.BO fb n (L5.BInl v0 v1)) (firstn n [v0; v1])).
  { split. cbn [L5.bo_len]. rewrite length_firstn. cbn [length]. clear - N2; lia. split. destruct n as [|[|[|n']]]; cbn [firstn]; [constructor | constructor; [exact V0R | constructor] | constructor; [exact V0R | constructor; [exact V1R | constructor]] | exfalso; clear - N2; lia]. reflexivity. }
  assert (SA16 : (E - 384) mod 16 = 0). { clear - EA. unfold aligned in EA. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
  assert (O16 : (o + 16) / 8 = o / 8 + 2) by (clear - O8; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  assert (W16 : L5.writable RSEGS MV (SPA - 16) 16).
  { apply (L5C.writable_of_defined RSEGS). 2: clear - ER; lia. 2: clear - ER; lia.
    apply (proj2 (defined_vis (ahid Ac modelc) Mc (SPA - 16) 16 (VIS (SPA - 16) 16 ltac:(clear - SLO HSCR; lia) ltac:(clear - ER; lia)))).
    destruct B6 as (_ & _ & _ & _ & DSCR & _). eapply L5.defined_sub. exact DSCR. clear - HSCR; lia. clear; lia. }
  destruct (L5ARED.reduce_run fx Rc MV o SPA pcn (L5.BO fb n (L5.BInl v0 v1)) (firstn n [v0; v1]) X10 X1 RAn X2 ltac:(clear - ER; lia) SA16 W16 IMGC CSB CUAR
              ltac:(clear - OLO ORP; lia) O8 OBIG ltac:(right; clear - OCE SLO HSCR; lia) ltac:(unfold SB; exact OZv) OWv OBv OLv)
    as (fx1 & R1 & M1v & rMS & (rOB & rKS & rR2 & rR10 & rFR & rMG)).
  { cbn [L5.bo_data L5.bo_cap L5.bo_st]. split. clear - OBIG; lia. split. right; clear - OCE SLO HSCR; lia. split. left; clear; lia.
    split. eapply L5.writable_sub. exact OWv. clear; lia. clear; lia. split. rewrite O16. intros i Hi. replace (o / 8 + 2 + SB + i) with (o / 8 + 2147450880 + (2 + i)) by (unfold SB; clear; lia). apply OZv. clear - Hi; lia.
    clear; lia. }
  cbn [L5.bo_fb L5.bo_st] in rOB.
  set (Wp := fun a => (o <= a < o + 16) \/ (SPA - 16 <= a < SPA)).
  apply (L5DKA.bstage L ar C HI LY HIok M model LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2 G W _ Mc modelc LKc crc Ac fx fx1 Rc L5ARED.REDUCE R1 pcn M1v Wp K BI rMS rMG).
  { intros a Ha Hn. subst Wp; cbn beta in Hn. apply rFR. exact Ha. clear - Hn; lia. clear - Hn; lia. }
  { intros a Ha Wa. subst Wp; cbn beta in Wa. destruct Wa as [Wa|Wa].
    - destruct (OCL a ltac:(clear - Wa; lia)) as (C1 & C2 & C3 & C4). split. exact C4. split. split. exact C1. exact C2. intros _. apply WRO. exact Wa.
    - eapply L5ADVHC.wp_scratch; try first [exact LY | exact HIok | exact G | exact ER | exact HSCR]; [exact BI | clear - Wa HSCR; lia]. }
  intros M1 model1 BI1 AH1 VIS1 MGM1 FRM1.
  eapply (KF fx1 R1 M1 model1 _ _ BI1 rKS rR2 rR10).
  - intros a Ha N1 N2'. apply FRM1. exact Ha. subst Wp; cbn beta. clear - N1 N2'. lia.
  - apply (proj1 (big_at_vis (ahid Ac modelc) M1 o _ OVIS ltac:(clear - ORP; lia) ltac:(clear - ORP; lia))). rewrite VIS1. exact rOB.
  - match goal with |- (if ?c then _ else _) = _ \/ _ => destruct c end. right; reflexivity. left; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma h3 (fx : FPState) Rc Mc modelc W BX LKc crc Ac :
  binv W BX Mc modelc LKc crc Ac -> rinvD R E Rc -> getr Rc (reg 18) = Z_to_bv 64 SH -> L5.u64_at RSEGS Mc (E - 336) F -> L5.u64_at RSEGS Mc (E - 288) ro -> 0 <= ro < 2 ^ 64 ->
  (forall (fx1 : FPState) R1 M1 model1 (nh : nat) dh,
      binv W BX M1 model1 LKc crc Ac -> (forall x, In x KS_v5H3 -> getr R1 (reg x) = getr Rc (reg x)) ->
      getr R1 (reg 1) = Z_to_bv 64 0x93660 -> getr R1 (reg 10) = Z_to_bv 64 ro -> getr R1 (reg 11) = Z_to_bv 64 (F + 352) -> getr R1 (reg 19) = Z_to_bv 64 (F + 352) ->
      getr R1 (reg 20) = Z_to_bv 64 (F + 368) -> getr R1 (reg 22) = Z_to_bv 64 F ->
      (forall a, 0 <= a < 2 ^ 64 -> ~ (SH + 44 <= a < SH + 48) -> ~ (F + 352 <= a < F + 384) -> M1 (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)) ->
      L5.big_at RSEGS M1 (F + 352) (L5.BO 0 nh (L5.BInl dh 0)) -> (nh <= 1)%nat -> shadow_zero M1 (F + 352) 4 ->
      srealizes RSEGS SCFG (cfg (fx:=fx1) R1 ASSIGN M1 model1) K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc 0x9361c Mc modelc) K.
Proof.
  intros BI RI X18 S48 S96 ROR KF. open_ctx BI. pose proof RI as (X2 & X8 & X9 & X3 & X4 & XSB).
  assert (ALF' : aligned F 32) by exact ALF.
  set (MV := mrestrict (ahid Ac modelc) Mc) in *.
  assert (S48v : L5.u64_at RSEGS MV (E - 336) F).
  { apply (proj2 (u64_at_vis _ Mc (E - 336) _ ltac:(eapply avis_sub; [exact SV | clear; lia | clear; lia]) ltac:(clear - ER; lia) ltac:(clear - ER; lia))). exact S48. }
  assert (S96v : L5.u64_at RSEGS MV (E - 288) ro).
  { apply (proj2 (u64_at_vis _ Mc (E - 288) _ ltac:(eapply avis_sub; [exact SV | clear; lia | clear; lia]) ltac:(clear - ER; lia) ltac:(clear - ER; lia))). exact S96. }
  assert (HV21 : 0 <= U Rc 21 <= 18446744073709551615) by (pose proof (UR Rc 21) as X; clear - X; lia).
  assert (HVR : 0 <= ro <= 18446744073709551615) by (clear - ROR; lia).
  pose proof (v5H3_conc fx Rc MV (fun j => match j with 2%nat => E | 36%nat => ro | 40%nat => F | 41%nat => fl | 58%nat => U Rc 1 | 71%nat => U Rc 21 | _ => 0 end)) as P. cbn beta iota in P.
  feed P ltac:(first [apply UR | apply U_to | sc ]).
  destruct P as (fx1 & R1 & M1v & MG1 & pFR & pFZ & (pMS & pKS & pR1 & pR10 & pR11 & pR19 & pR20 & pR22 & pT24 & pT16 & pT8 & pT0 & pH3 & pH2 & pH1 & pH0 & _)).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (SHQ : (F + 352) / 8 = F / 8 + 44 /\ 0 <= F / 8 /\ F / 8 + 64 <= 17592186044416) by (hnf in ALF; clear - FRP ALF; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  set (Wp := fun a => (SH + 44 <= a < SH + 48) \/ (F + 352 <= a < F + 384)).
  apply (L5DKA.bstage L ar C HI LY HIok M model LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2 G W _ Mc modelc LKc crc Ac fx fx1 Rc 0x9361c R1 ASSIGN M1v Wp K BI pMS MG1).
  { intros a Ha Hn. apply pFZ. exact Ha. all: subst Wp; cbn beta in Hn; clear - Hn; lia. }
  { intros a Ha Wa. subst Wp; cbn beta in Wa. destruct Wa as [Wa|Wa].
    apply (L5DKA.wp_shadow L ar HI LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2 G). unfold SB. change (ff_bytes 3 / 8) with 64. clear - Wa. lia.
    apply (L5DKA.wp_fake L ar HI LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2 G); change (ff_bytes 3) with 512; clear - Wa; lia. }
  intros M1 model1 BI1 AH1 VIS1 MGM1 FRM1.
  assert (FC : forall a v, F <= a -> a + 8 <= F + 512 -> L5.u64_at RSEGS M1v a v -> L5.u64_at RSEGS M1 a v).
  { intros a v H1 H2 Hc. apply (proj1 (u64_at_vis (ahid Ac modelc) M1 a v ltac:(eapply avis_sub; [exact FV | clear - H1; lia | clear - H2; lia]) ltac:(clear - H1 FRP; lia) ltac:(clear - H2 FRP; lia))). rewrite VIS1. exact Hc. }
  set (dh := U Rc 21) in *. set (nh := if 0 <? dh then 1%nat else 0%nat).
  apply (KF fx1 R1 M1 model1 nh dh BI1 pKS pR1 pR10 pR11 pR19 pR20 pR22).
  - intros a Ha N1 N2. apply FRM1. exact Ha. subst Wp; cbn beta. clear - N1 N2. lia.
  - split. { cbn [L5.bo_fb]. apply (proj1 (u8_at_vis (ahid Ac modelc) M1 (F + 352) 0 ltac:(eapply avis_sub; [exact FV | clear; lia | clear; lia]) ltac:(clear - FRP; lia) ltac:(clear - FRP; lia))). rewrite VIS1. exact pT0. }
    split. cbn [L5.bo_fb]. clear; lia.
    split. { cbn [L5.bo_len]. replace (F + 352 + 8) with (F + 360) by (clear; lia). apply FC. clear; lia. clear; lia. subst nh. destruct (0 <? dh); exact pT8. }
    cbn [L5.bo_st L5.bo_fb L5.bo_len]. split. reflexivity. split. replace (F + 352 + 16) with (F + 368) by (clear; lia). apply FC. clear; lia. clear; lia. exact pT16.
    split. replace (F + 352 + 24) with (F + 376) by (clear; lia). apply FC. clear; lia. clear; lia. exact pT24.
    split. subst nh. destruct (0 <? dh); clear; lia. split. subst dh. pose proof (UR Rc 21) as X. clear - X; lia. clear; lia.
  - subst nh. destruct (0 <? dh); clear; lia.
  - intros j Hj. unfold byte_at, S. rewrite (proj1 SHQ).
    apply (byte_of_u8 M1 _ 0). 2: right; unfold SB; clear - Hj SHQ; lia. 2: unfold SB; clear - Hj SHQ; lia.
    apply (proj1 (u8_at_vis (ahid Ac modelc) M1 (F / 8 + 44 + SB + j) 0 ltac:(eapply avis_sub; [exact SHV | unfold SB; clear - Hj; lia | unfold SB; clear - Hj; lia]) ltac:(unfold SB; clear - Hj SHQ; lia) ltac:(unfold SB; clear - Hj SHQ; lia))).
    rewrite VIS1. assert (J : j = 0 \/ j = 1 \/ j = 2 \/ j = 3) by (clear - Hj; lia). unfold SB. destruct J as [J|[J|[J|J]]]; subst j; gmem.
Qed.

(* [comment removed for export] *)
Lemma h4_tail (fx : FPState) Rc Mc modelc W BXf LKc crc Ac qo qn bits fq nq q0 q1 fr nr r0 r1 f0 bn on bd od :
  binv W (ostr on ++ ostr od ++ BXf) Mc modelc LKc crc Ac -> (forall a, (qo <= a < qo + 1 \/ ro <= a < ro + 1) -> ~ L5.outside W a) ->
  rinvD R E Rc -> getr Rc (reg 18) = Z_to_bv 64 SH -> getr Rc (reg 19) = Z_to_bv 64 (F + 352) -> getr Rc (reg 20) = Z_to_bv 64 (F + 368) -> getr Rc (reg 22) = Z_to_bv 64 F ->
  getr Rc (reg 25) = Z_to_bv 64 (F + 96) -> getr Rc (reg 27) = Z_to_bv 64 F ->
  L5.u8_at RSEGS Mc (F + 352) f0 -> 0 <= f0 < 256 -> Z.testbit f0 0 = false ->
  spl E Mc [(E - 296, qo); (E - 304, F + 32); (E - 320, qo / 8 + 2147450880); (E - 312, qn); (E - 288, ro); (E - 328, bits)] -> 0 <= qn <= 1 -> (bits = 0 \/ bits = 2) ->
  obj_at Mc (F + 96) bn on -> obj_at Mc (F + 32) bd od ->
  L5.big_at RSEGS Mc qo (L5.BO fq nq (L5.BInl q0 q1)) -> aobj FF qo 32 -> shadow_zero Mc qo 4 ->
  L5.big_at RSEGS Mc ro (L5.BO fr nr (L5.BInl r0 r1)) -> aobj FF ro 32 -> shadow_zero Mc ro 4 -> (qo + 32 <= ro \/ ro + 32 <= qo) ->
  (forall (fxf : FPState) Rf Mf modelf Af,
      regs_preserved R Rf -> incl Ac Af -> ahpres L ar LB FF E SCRD W M Mf ->
      L5.big_at RSEGS Mf qo (L5.BO (Z.lor (Z.land fq 253) (2 * qn)) nq (L5.BInl q0 q1)) -> L5.big_at RSEGS Mf ro (L5.BO (Z.lor (Z.land fr 253) bits) nr (L5.BInl r0 r1)) ->
      model_rt model modelf -> amodel_ok Af modelf -> ri_inv HI (BXf ++ LB) FF LKc crc Af Mf (vml_of modelf) ->
      srealizes RSEGS SCFG (cfg (fx:=fxf) Rf r Mf modelf) K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc 0x93660 Mc modelc) K.
Proof.
  intros BI WRO RI X18 X19 X20 X22 X25r X27 T0 F0R F0B SP QNR BITS ON OD OBQ AOQ SZQ OBR AOR SZR APT KF. open_ctx BI. pose proof RI as (X2 & X8 & X9 & X3 & X4 & XSB).
  assert (ALF' : aligned F 32) by exact ALF.
  pose proof (arg_facts L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G W _ Mc modelc LKc crc Ac qo BI AOQ SZQ)
    as ((QRP & QRG & Q8) & QBIG & QZv & QWv & QFR & QF & QSH & SQF & SQSH & SQFR & QXB & QXC & QCL).
  pose proof (arg_facts L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G W _ Mc modelc LKc crc Ac ro BI AOR SZR)
    as ((RRP & RRG & R8) & RBIG & RZv & RWv & RFR & RF & RSH & SRF & SRSH & SRFR & RXB & RXC & RCL).
  assert (SPV : forall a v, In (a, v) [(E - 296, qo); (E - 304, F + 32); (E - 320, qo / 8 + 2147450880); (E - 312, qn); (E - 288, ro); (E - 328, bits)] -> L5.u64_at RSEGS (mrestrict (ahid Ac modelc) Mc) a v).
  { intros a v Hin. eapply L5ADVHL.spl_vis; try first [exact LY | exact HIok | exact G | exact ER]; [exact BI | exact SP | exact Hin]. }
  pose proof (SPV (E - 296) _ ltac:(left; reflexivity)) as S88v.
  pose proof (SPV (E - 304) _ ltac:(right; left; reflexivity)) as S80v.
  pose proof (SPV (E - 320) _ ltac:(right; right; left; reflexivity)) as S64v.
  pose proof (SPV (E - 312) _ ltac:(right; right; right; left; reflexivity)) as S72v.
  pose proof (SPV (E - 288) _ ltac:(right; right; right; right; left; reflexivity)) as S96v.
  pose proof (SPV (E - 328) _ ltac:(right; right; right; right; right; left; reflexivity)) as S56v.
  set (MV := mrestrict (ahid Ac modelc) Mc) in *.
  assert (ALQ : aligned qo 8) by exact Q8. assert (ALR : aligned ro 8) by exact R8.
  pose proof OBQ as (Q0 & FQR & _). pose proof OBR as (R0 & FRR & _). cbn [L5.bo_fb] in Q0, FQR, R0, FRR.
  assert (Q0v : L5.u8_at RSEGS MV qo fq) by (apply QXB; exact Q0). assert (R0v : L5.u8_at RSEGS MV ro fr) by (apply RXB; exact R0).
  assert (T0v : L5.u8_at RSEGS MV (F + 352) f0).
  { apply (proj2 (u8_at_vis (ahid Ac modelc) Mc (F + 352) f0 ltac:(eapply avis_sub; [exact FV | clear; lia | clear; lia]) ltac:(clear - FRP; lia) ltac:(clear - FRP; lia))). exact T0. }
  assert (HV0 : 0 <= f0 <= 255 /\ 0 <= f0 < 2 ^ 64) by (clear - F0R; lia). destruct HV0 as [HV0 HV0'].
  assert (HVQ : 0 <= fq <= 255 /\ 0 <= fq < 2 ^ 64) by (clear - FQR; lia). destruct HVQ as [HVQ HVQ'].
  assert (HVR : 0 <= fr <= 255 /\ 0 <= fr < 2 ^ 64) by (clear - FRR; lia). destruct HVR as [HVR HVR'].
  assert (HVB : 0 <= bits <= 2 /\ 0 <= bits < 2 ^ 64) by (clear - BITS; lia). destruct HVB as [HVB HVB'].
  assert (HVN : 0 <= qn < 2 ^ 64) by (clear - QNR; lia).
  pose proof (v5H4i_conc fx Rc MV (fun j => match j with 2%nat => E | 35%nat => qo | 36%nat => ro | 40%nat => F | 41%nat => fl | 57%nat => qn | 58%nat => U Rc 1 | 59%nat => bits | 60%nat => f0 | 69%nat => fq | 72%nat => fr | _ => 0 end)) as P. cbn beta iota in P.
  feed P ltac:(first [apply UR | apply U_to | sc ]).
  destruct P as (fx1 & R1 & M1v & MG1 & pFR & pFZ & (pMS & pKS & pR10 & pU11 & pR12 & pR21 & pR24 & pFBR & pFBQ & _)).
  set (Wp := fun a => (SH + 44 <= a < SH + 48) \/ (qo <= a < qo + 1) \/ (ro <= a < ro + 1)).
  apply (L5DKA.bstage L ar C HI LY HIok M model LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2 G W _ Mc modelc LKc crc Ac fx fx1 Rc 0x93660 R1 0x936e8 M1v Wp K BI pMS MG1).
  { intros a Ha Hn. apply pFZ. exact Ha. all: subst Wp; cbn beta in Hn; clear - Hn; lia. }
  { intros a Ha Wa. subst Wp; cbn beta in Wa. destruct Wa as [Wa|[Wa|Wa]].
    - apply (L5DKA.wp_shadow L ar HI LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2 G). unfold SB. change (ff_bytes 3 / 8) with 64. clear - Wa. lia.
    - destruct (QCL a ltac:(clear - Wa; lia)) as (C1 & C2 & C3 & C4). split. exact C4. split. split. exact C1. exact C2. intros _. apply WRO. left. exact Wa.
    - destruct (RCL a ltac:(clear - Wa; lia)) as (C1 & C2 & C3 & C4). split. exact C4. split. split. exact C1. exact C2. intros _. apply WRO. right. exact Wa. }
  intros M1 model1 BI1 AH1 VIS1 MGM1 FRM1.
  pose proof (aobj_facts L ar C HI LY HIok _ FF' LKc crc Ac Mc modelc qo 32 0 0 (proj1 BI) (aobj_cons _ _ _ _ AOQ) ltac:(clear; lia) ltac:(reflexivity)) as (_ & _ & _ & QVIS & _).
  pose proof (aobj_facts L ar C HI LY HIok _ FF' LKc crc Ac Mc modelc ro 32 0 0 (proj1 BI) (aobj_cons _ _ _ _ AOR) ltac:(clear; lia) ltac:(reflexivity)) as (_ & _ & _ & RVIS & _).
  rewrite (Z.mod_small (2 * qn)) in pFBQ by (clear - QNR; lia).
  pose proof (L5ADVEA.fb_sgn fq (2 * qn) FQR ltac:(clear - QNR; lia)) as (FQR' & FQT). pose proof (L5ADVEA.fb_sgn fr bits FRR BITS) as (FRR' & FRT).
  assert (OBQ1 : L5.big_at RSEGS M1 qo (L5.BO (Z.lor (Z.land fq 253) (2 * qn)) nq (L5.BInl q0 q1))).
  { apply (L5ADVEA.big_at_fb Mc M1 qo _ _ OBQ ltac:(clear - QRP; lia) ltac:(clear - QRP; lia)). 3: exact FQR'. 3: exact FQT.
    intros i Hi. apply FRM1. clear - Hi QRP; lia. subst Wp; cbn beta. clear - Hi QSH APT. lia.
    apply (proj1 (u8_at_vis (ahid Ac modelc) M1 qo _ ltac:(eapply avis_sub; [exact QVIS | clear; lia | clear; lia]) ltac:(clear - QRP; lia) ltac:(clear - QRP; lia))). rewrite VIS1. exact pFBQ. }
  assert (OBR1 : L5.big_at RSEGS M1 ro (L5.BO (Z.lor (Z.land fr 253) bits) nr (L5.BInl r0 r1))).
  { apply (L5ADVEA.big_at_fb Mc M1 ro _ _ OBR ltac:(clear - RRP; lia) ltac:(clear - RRP; lia)). 3: exact FRR'. 3: exact FRT.
    intros i Hi. apply FRM1. clear - Hi RRP; lia. subst Wp; cbn beta. clear - Hi RSH APT. lia.
    apply (proj1 (u8_at_vis (ahid Ac modelc) M1 ro _ ltac:(eapply avis_sub; [exact RVIS | clear; lia | clear; lia]) ltac:(clear - RRP; lia) ltac:(clear - RRP; lia))). rewrite VIS1. exact pFBR. }
  assert (KEEPF : forall i, F + 32 <= i < F + 128 -> M1 (Z_to_bv 64 i) = Mc (Z_to_bv 64 i)).
  { intros i Hi. apply FRM1. clear - Hi FRP; lia. subst Wp; cbn beta. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). clear - Hi QF RF FBIG FRP ALF. hnf in ALF. lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  assert (ON1 : obj_at M1 (F + 96) bn on). { apply (obj_at_agree Mc M1 _ _ _ ON ltac:(clear - FRP; lia) ltac:(clear - FRP; lia)). intros i Hi. apply KEEPF. clear - Hi; lia. }
  assert (OD1 : obj_at M1 (F + 32) bd od). { apply (obj_at_agree Mc M1 _ _ _ OD ltac:(clear - FRP; lia) ltac:(clear - FRP; lia)). intros i Hi. apply KEEPF. clear - Hi; lia. }
  assert (RI1 : rinvTL R E F R1).
  { split. apply (rinvD_ks R E Rc R1 KS_v5H4i RI pKS). vm_compute; reflexivity. split. rewrite (pKS 18%nat) by inl. exact X18. split. exact pR24. split. rewrite (pKS 25%nat) by inl. exact X25r.
    split. rewrite (pKS 22%nat) by inl. exact X22. rewrite (pKS 27%nat) by inl. exact X27. }
  apply (div_dtors L ar C HI LY HIok Hdel R M model K LB FF LK A E SCRD F fl ro r LK2 M2 model2 cr2 G ER EA HK RA UR1 G2 G4 ltac:(clear - HSCR; lia) fx1 R1 M1 model1 W (ostr on ++ ostr od ++ BXf) (ostr od ++ BXf) BXf LKc crc Ac bn on bd od BI1 RI1 ON1 OD1).
  { destruct on as [[q n]|]; cbn [ostr app]. split. left; reflexivity. apply lb_remove_head. reflexivity. }
  { destruct od as [[q n]|]; cbn [ostr app]. split. left; reflexivity. apply lb_remove_head. reflexivity. }
  { intros a Hc. rewrite <- app_assoc. apply aclient_appb. exact Hc. }
  intros fxf Rf Mf modelf Af RPf IAf AHf AGf RTf AMf HHf.
  assert (AGO : forall o, aobj FF o 32 -> (o + 32 <= F \/ F + 512 <= o) -> (o + 32 <= SH \/ SH + 64 <= o) -> (forall i, o <= i < o + 32 -> i <> fl) -> forall i, o <= i < o + 32 -> Mf (Z_to_bv 64 i) = M1 (Z_to_bv 64 i)).
  { intros o AOB OF OSH OFL i Hi. apply AGf. pose proof (aobj_facts L ar C HI LY HIok _ FF' LKc crc Ac Mc modelc o 32 0 0 (proj1 BI) (aobj_cons _ _ _ _ AOB) ltac:(clear; lia) ltac:(reflexivity)) as ((OLO & _ & OHI & _) & _). clear - Hi OLO OHI; lia.
    apply (obj_client L ar (BXf ++ LB) FF' SPA OPDEL_SCR o 32 i). apply aobj_cons. exact AOB. exact Hi.
    unfold L5AFK.Wret. change (ff_bytes 3 / 8) with 64. intros X. specialize (OFL i Hi). clear - X OF OSH OFL Hi. unfold SB in X. lia.
    unfold SB. clear - OSH Hi. lia. }
  apply (KF fxf Rf Mf modelf Af RPf IAf AHf).
  - eapply L5C.big_at_agree. 4: exact OBQ1. 2: clear - QRP; lia. 2: clear - QRP; lia. refine (AGO qo AOQ QF QSH _). intros i Hi. exact (proj1 (proj2 (proj2 (QCL i Hi)))).
  - eapply L5C.big_at_agree. 4: exact OBR1. 2: clear - RRP; lia. 2: clear - RRP; lia. refine (AGO ro AOR RF RSH _). intros i Hi. exact (proj1 (proj2 (proj2 (RCL i Hi)))).
  - exact RTf.
  - exact AMf.
  - exact HHf.
Qed.
End DIV.
End WithIface.
End SCFG_1.
End L5ADVHM.
