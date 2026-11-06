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
     L5Cmp L5CoreAB0 L5CoreSpecsAB0 L5StepAB0 L5CoreBB0 L5BDetailG L5BFrameK L5DivKitAB0 L5BDivH L5BDivT L5BDivD L5BDivPH L5BDivPL L5BDivE L5BDivEA L5BDivHC L5BDivHD L5BDivHA L5BRed L5BDivHL L5OpmodSpecsAB0.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5ADVHL2.
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
Lemma ht (fx : FPState) Rc Mc modelc W BX LKc crc Ac qo d0 lent (toG : bool) :
  binv W BX Mc modelc LKc crc Ac -> rinvD R E Rc -> getr Rc (reg 18) = Z_to_bv 64 SH -> getr Rc (reg 11) = Z_to_bv 64 lent ->
  L5.u64_at RSEGS Mc (E - 120) (F + 48) -> L5.u64_at RSEGS Mc (E - 296) qo -> shr8 Mc F 4 4 0 -> L5.u64_at RSEGS Mc (F + 48) d0 -> (if toG then 4294967296 <= d0 < 2 ^ 64 else 0 <= d0 <= 4294967295) ->
  0 <= lent < 2 ^ 64 -> 0 <= qo < 2 ^ 64 ->
  (forall (fx1 : FPState) R1 model1,
      binv W BX Mc model1 LKc crc Ac -> (forall x, In x (if toG then KS_v5HTg else KS_v5HTh) -> getr R1 (reg x) = getr Rc (reg x)) -> getr R1 (reg 20) = Z_to_bv 64 d0 ->
      (if toG then True else getr R1 (reg 1) = Z_to_bv 64 0x93084 /\ getr R1 (reg 10) = Z_to_bv 64 qo) ->
      srealizes RSEGS SCFG (cfg (fx:=fx1) R1 (if toG then 0x930a8 else RESIZE) Mc model1) K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc 0x93050 Mc modelc) K.
Proof.
  intros BI RI X18 X11 S264 S88 SHD D0 DR LTR QOR KF. open_ctx BI. pose proof RI as (X2 & X8 & X9 & X3 & X4 & XSB). pose proof BI as (B1 & B2 & _).
  assert (ALF' : aligned F 32) by exact ALF.
  assert (DZv : L5KA.zeros_at (mrestrict (ahid Ac modelc) Mc) (F / 8 + 2147450884) 4).
  { eapply (L5ADVHC.fshz_vis L ar C HI LY HIok); try first [exact G | exact ER | exact BI]. exact SHD. clear; lia. clear; lia. reflexivity. }
  set (MV := mrestrict (ahid Ac modelc) Mc) in *.
  assert (S264v : L5.u64_at RSEGS MV (E - 120) (F + 48)).
  { apply (proj2 (u64_at_vis _ Mc (E - 120) _ ltac:(eapply avis_sub; [exact SV | clear; lia | clear; lia]) ltac:(clear - ER; lia) ltac:(clear - ER; lia))). exact S264. }
  assert (S88v : L5.u64_at RSEGS MV (E - 296) qo).
  { apply (proj2 (u64_at_vis _ Mc (E - 296) _ ltac:(eapply avis_sub; [exact SV | clear; lia | clear; lia]) ltac:(clear - ER; lia) ltac:(clear - ER; lia))). exact S88. }
  assert (D0v : L5.u64_at RSEGS MV (F + 48) d0).
  { apply (proj2 (u64_at_vis _ Mc (F + 48) _ ltac:(eapply avis_sub; [exact FV | clear; lia | clear; lia]) ltac:(clear - FRP; lia) ltac:(clear - FRP; lia))). exact D0. }
  assert (HVQ : 0 <= qo <= 18446744073709551615) by (clear - QOR; lia). assert (HVL : 0 <= lent <= 18446744073709551615) by (clear - LTR; lia).
  destruct toG.
  - assert (HVD : 0 <= d0 < 2 ^ 64) by (clear - DR; lia).
    pose proof (v5HTg_conc fx Rc MV (fun j => match j with 2%nat => E | 35%nat => qo | 40%nat => F | 41%nat => fl | 58%nat => U Rc 1 | 68%nat => d0 | 70%nat => lent | _ => 0 end)) as P. cbn beta iota in P.
    feed P ltac:(first [apply UR | apply U_to | sc ]).
    destruct P as (fx1 & R1 & M1v & _ & pFR & _ & (pMS & pKS & pR10 & pR12 & pR20)).
    assert (E1 : M1v = MV) by (apply mem_eq_of_agree; intros a Ha; apply pFR). subst M1v.
    apply (apure L ar C HI LY HIok (BX ++ LB) FF' LKc crc Ac Mc modelc fx fx1 Rc 0x93050 R1 0x930a8 K B1 B2 pMS).
    intros model1 HH1 AM1 RT1 AH1.
    pose proof (L5AFK.binv_model L ar HI M model LB FF LK A E SCRD SPA (down E F ro R) F 3 W BX Mc modelc LKc crc Ac model1 BI HH1 AM1 RT1) as BI1.
    apply (KF fx1 R1 model1 BI1 pKS pR20 I).
  - assert (HVD : 0 <= d0 < 2 ^ 64) by (clear - DR; lia).
    pose proof (v5HTh_conc fx Rc MV (fun j => match j with 2%nat => E | 35%nat => qo | 40%nat => F | 41%nat => fl | 58%nat => U Rc 1 | 68%nat => d0 | 70%nat => lent | _ => 0 end)) as P. cbn beta iota in P.
    feed P ltac:(first [apply UR | apply U_to | sc ]).
    destruct P as (fx1 & R1 & M1v & _ & pFR & _ & (pMS & pKS & pR1 & pR10 & pR12 & pR20)).
    assert (E1 : M1v = MV) by (apply mem_eq_of_agree; intros a Ha; apply pFR). subst M1v.
    apply (apure L ar C HI LY HIok (BX ++ LB) FF' LKc crc Ac Mc modelc fx fx1 Rc 0x93050 R1 RESIZE K B1 B2 pMS).
    intros model1 HH1 AM1 RT1 AH1.
    pose proof (L5AFK.binv_model L ar HI M model LB FF LK A E SCRD SPA (down E F ro R) F 3 W BX Mc modelc LKc crc Ac model1 BI HH1 AM1 RT1) as BI1.
    apply (KF fx1 R1 model1 BI1 pKS pR20). split. exact pR1. exact pR10.
Qed.

(* [comment removed for export] *)
Lemma h1 (fx : FPState) Rc Mc modelc W BX LKc crc Ac qo fq lenq :
  binv W BX Mc modelc LKc crc Ac -> rinvD R E Rc -> getr Rc (reg 18) = Z_to_bv 64 SH -> getr Rc (reg 26) = Z_to_bv 64 (qo + 8) ->
  L5.u64_at RSEGS Mc (E - 320) (qo / 8 + 2147450880) -> L5.u64_at RSEGS Mc (E - 352) ((qo + 8) / 8 + 2147450880) -> L5.u64_at RSEGS Mc (E - 296) qo -> L5.u64_at RSEGS Mc (E - 144) 2 ->
  aobj FF qo 32 -> shadow_zero Mc qo 4 -> L5.u8_at RSEGS Mc qo fq -> 0 <= fq < 256 -> Z.testbit fq 0 = false -> L5.u64_at RSEGS Mc (qo + 8) lenq -> 0 <= lenq < 2 ^ 64 ->
  (forall (fx1 : FPState) R1 M1 model1,
      binv W BX M1 model1 LKc crc Ac -> (forall x, In x KS_v5H1i -> getr R1 (reg x) = getr Rc (reg x)) ->
      getr R1 (reg 19) = Z_to_bv 64 1 -> getr R1 (reg 21) = Z_to_bv 64 0 -> getr R1 (reg 22) = Z_to_bv 64 18446744073709551615 -> getr R1 (reg 26) = Z_to_bv 64 qo ->
      (forall a, 0 <= a < 2 ^ 64 -> ~ (E - 136 <= a < E - 120) -> M1 (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)) ->
      L5.u64_at RSEGS M1 (E - 136) (qo + 16) -> L5.u64_at RSEGS M1 (E - 128) lenq ->
      srealizes RSEGS SCFG (cfg (fx:=fx1) R1 0x93568 M1 model1) K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc 0x93084 Mc modelc) K.
Proof.
  intros BI RI X18 X26 S64 S32 S88 S240 AOQ SZQ Q0 FQR FQ0 Q8' LQR KF. open_ctx BI. pose proof RI as (X2 & X8 & X9 & X3 & X4 & XSB).
  assert (ALF' : aligned F 32) by exact ALF.
  pose proof (arg_facts L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G W _ Mc modelc LKc crc Ac qo BI AOQ SZQ)
    as ((ORP & ORG & O8) & OBIG & OZv & OWv & OFR & OF & OSH & SOF & SOSH & SOFR & XB & XC & OCL).
  set (MV := mrestrict (ahid Ac modelc) Mc) in *.
  assert (ALO : aligned qo 8) by exact O8.
  assert (SCELL : forall a v, SPA <= a -> a + 8 <= E -> L5.u64_at RSEGS Mc a v -> L5.u64_at RSEGS MV a v).
  { intros a v H1 H2 Hc. apply (proj2 (u64_at_vis (ahid Ac modelc) Mc a v ltac:(eapply avis_sub; [exact SV | clear - H1; lia | clear - H2; lia]) ltac:(clear - H1 ER; lia) ltac:(clear - H2 ER; lia))). exact Hc. }
  assert (S64v : L5.u64_at RSEGS MV (E - 320) (qo / 8 + 2147450880)) by (apply SCELL; [clear; lia | clear; lia | exact S64]).
  assert (S32v : L5.u64_at RSEGS MV (E - 352) ((qo + 8) / 8 + 2147450880)) by (apply SCELL; [clear; lia | clear; lia | exact S32]).
  assert (S88v : L5.u64_at RSEGS MV (E - 296) qo) by (apply SCELL; [clear; lia | clear; lia | exact S88]).
  assert (S240v : L5.u64_at RSEGS MV (E - 144) 2) by (apply SCELL; [clear; lia | clear; lia | exact S240]).
  assert (Q0v : L5.u8_at RSEGS MV qo fq) by (apply XB; exact Q0).
  assert (Q8v : L5.u64_at RSEGS MV (qo + 8) lenq) by (apply XC; [clear; lia | clear; lia | exact Q8']).
  assert (HVF : 0 <= fq <= 255 /\ 0 <= fq < 2 ^ 64) by (clear - FQR; lia). destruct HVF as [HVF HVF'].
  assert (HVL : 0 <= lenq <= 18446744073709551615) by (clear - LQR; lia).
  pose proof (v5H1i_conc fx Rc MV (fun j => match j with 2%nat => E | 35%nat => qo | 40%nat => F | 41%nat => fl | 58%nat => U Rc 1 | 69%nat => fq | 73%nat => lenq | _ => 0 end)) as P. cbn beta iota in P.
  feed P ltac:(first [apply UR | apply U_to | sc ]).
  destruct P as (fx1 & R1 & M1v & MG1 & pFR & pFZ & (pMS & pKS & pR10 & pR11 & pR19 & pR21 & pR22 & pR26 & pS256 & pS248)).
  set (Wp := fun a => E - 136 <= a < E - 120).
  apply (L5DKA.bstage L ar C HI LY HIok M model LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2 G W _ Mc modelc LKc crc Ac fx fx1 Rc 0x93084 R1 0x93568 M1v Wp K BI pMS MG1).
  { intros a Ha Hn. apply pFZ. exact Ha. subst Wp; cbn beta in Hn; clear - Hn; lia. }
  { intros a Ha Wa. subst Wp; cbn beta in Wa. apply (L5DKA.wp_frame L ar HI LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2 G); [clear - Wa; lia | unfold docell; clear - Wa; lia]. }
  intros M1 model1 BI1 AH1 VIS1 MGM1 FRM1.
  assert (SPV : forall a v, SPA <= a -> a + 8 <= E -> L5.u64_at RSEGS M1v a v -> L5.u64_at RSEGS M1 a v).
  { intros a v H1 H2 Hc. apply (proj1 (u64_at_vis (ahid Ac modelc) M1 a v ltac:(eapply avis_sub; [exact SV | clear - H1; lia | clear - H2; lia]) ltac:(clear - H1 ER; lia) ltac:(clear - H2 ER; lia))). rewrite VIS1. exact Hc. }
  apply (KF fx1 R1 M1 model1 BI1 pKS pR19 pR21 pR22 pR26).
  - intros a Ha N1. apply FRM1. exact Ha. subst Wp; cbn beta. exact N1.
  - apply SPV. clear; lia. clear; lia. exact pS248.
  - apply SPV. clear; lia. clear; lia. exact pS256.
Qed.

(* [comment removed for export] *)
Lemma hl (fx : FPState) Rc Mc modelc W BX LKc crc Ac to qo d0 tw lenq (last : bool) :
  let k := if last then 16 else 24 in
  binv W BX Mc modelc LKc crc Ac -> rinvD R E Rc -> getr Rc (reg 18) = Z_to_bv 64 SH ->
  getr Rc (reg 19) = Z_to_bv 64 (if last then 0 else 1) -> getr Rc (reg 20) = Z_to_bv 64 d0 -> 1 <= d0 <= 4294967295 ->
  (if last then True else getr Rc (reg 21) = Z_to_bv 64 0) -> getr Rc (reg 22) = Z_to_bv 64 18446744073709551615 -> getr Rc (reg 26) = Z_to_bv 64 qo ->
  L5OMA.stksh ar M (E - SCRD) -> (forall x, in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) x -> L5.outside W x) -> SCRD mod 8 = 0 ->
  aobj FF to 32 -> shadow_zero Mc to 4 -> L5.u64_at RSEGS Mc (to + k) tw -> 0 <= tw < 2 ^ 64 ->
  aobj FF qo 32 -> shadow_zero Mc qo 4 -> (to + 32 <= qo \/ qo + 32 <= to) ->
  L5.u64_at RSEGS Mc (E - 152) (to + 16) -> L5.u64_at RSEGS Mc (E - 144) 2 -> L5.u64_at RSEGS Mc (E - 136) (qo + 16) -> L5.u64_at RSEGS Mc (E - 128) lenq -> 0 <= lenq < 2 ^ 64 ->
  L5.u64_at RSEGS Mc (E - 280) (F + 96) -> L5.u64_at RSEGS Mc (E - 296) qo ->
  (forall a, qo + 16 <= a < qo + 32 -> ~ L5.outside W a) ->
  (forall (fx1 : FPState) R1 M1 model1,
      binv W BX M1 model1 LKc crc Ac -> (forall x, In x (if last then KS_v5HLb else KS_v5HLa) -> getr R1 (reg x) = getr Rc (reg x)) ->
      (if last then getr R1 (reg 1) = Z_to_bv 64 0x9361c /\ getr R1 (reg 10) = Z_to_bv 64 qo /\ getr R1 (reg 25) = Z_to_bv 64 (F + 96)
       else getr R1 (reg 19) = Z_to_bv 64 0 /\ getr R1 (reg 25) = Z_to_bv 64 (F + 96)) ->
      (forall a, 0 <= a < 2 ^ 64 -> ~ (qo + k <= a < qo + k + 8) -> ~ (E - 392 <= a < E - 384) -> M1 (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)) -> L5.defined M1 (qo + k) 8 ->
      srealizes RSEGS SCFG (cfg (fx:=fx1) R1 (if last then L5ARED.REDUCE else 0x93568) M1 model1) K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc 0x93568 Mc modelc) K.
Proof.
  intros k BI RI X18 X19 X20 DR X21 X22 X26 SSH NWSH SC8 AOT SZT TW TWR AOQ SZQ APT S232 S240 S248 S256 LQR S104 S88 WRO KF. open_ctx BI. pose proof RI as (X2 & X8 & X9 & X3 & X4 & XSB).
  assert (ALF' : aligned F 32) by exact ALF.
  pose proof (arg_facts L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G W _ Mc modelc LKc crc Ac to BI AOT SZT)
    as ((TRP & TRG & T8) & TBIG & TZv & TWv & TFR & TF & TSH & STF & STSH & STFR & TXB & TXC & TCL).
  pose proof (arg_facts L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G W _ Mc modelc LKc crc Ac qo BI AOQ SZQ)
    as ((ORP & ORG & O8) & OBIG & OZv & OWv & OFR & OF & OSH & SOF & SOSH & SOFR & XB & XC & OCL).
  pose proof BI as (B1 & _ & _ & _ & _ & B6 & _).
  pose proof (vis_pack L ar C HI LY HIok (BX ++ LB) FF' LKc crc Ac Mc modelc B1) as (_ & VIS & _).
  assert (SLO : ahl_ceil ar + 4096 + SCRD <= E) by (destruct G as [_ _ SLO0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _]; exact SLO0).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (A152 : (E - 152) mod 8 = 0 /\ (E - 136) mod 8 = 0) by (clear - EA; unfold aligned in EA; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  assert (ZT : L5KA.zeros_at (mrestrict (ahid Ac modelc) Mc) ((E - 152) / 8 + 2147450880) 2).
  { eapply (L5ADVHC.stkz_vis L ar C HI LY HIok); try first [exact G | exact ER | exact EA | exact HSCR | exact BI | exact SSH | exact NWSH | exact SC8 | exact (proj1 A152)]; clear - HSCR; lia. }
  assert (ZQ : L5KA.zeros_at (mrestrict (ahid Ac modelc) Mc) ((E - 136) / 8 + 2147450880) 2).
  { eapply (L5ADVHC.stkz_vis L ar C HI LY HIok); try first [exact G | exact ER | exact EA | exact HSCR | exact BI | exact SSH | exact NWSH | exact SC8 | exact (proj2 A152)]; clear - HSCR; lia. }
  set (MV := mrestrict (ahid Ac modelc) Mc) in *.
  assert (WX : L5.writable RSEGS MV (E - 400) 400).
  { apply (L5C.writable_of_defined RSEGS). 2: clear - ER; lia. 2: clear - ER; lia.
    apply (proj2 (defined_vis (ahid Ac modelc) Mc (E - 400) 400 (VIS (E - 400) 400 ltac:(clear - SLO HSCR; lia) ltac:(clear - ER; lia)))).
    destruct B6 as (_ & _ & _ & _ & DSCR & _). eapply L5.defined_sub. exact DSCR. clear - HSCR; lia. clear; lia. }
  assert (ALT : aligned to 8) by exact T8. assert (ALO : aligned qo 8) by exact O8.
  (* [comment removed for export] *)
  assert (SFX : (E - 400 + 400 <= F \/ F + 512 <= E - 400) /\ (E - 400 + 400 <= fl \/ fl + 1 <= E - 400)).
  { destruct G as [Hk SPT SLO' SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG' F32 FLA' FLR FLBIG' NCF NCS]. change (ff_bytes 3) with 512 in *. clear - FCEIL FLR SPC SLO' HSCR. lia. }
  destruct SFX as [SFX SFLX].
  assert (NCSX : forall o, aobj FF o 32 -> (E - 400 + 400 <= o \/ o + 32 <= E - 400)).
  { intros o AOB. pose proof (aobj_facts L ar C HI LY HIok (BX ++ LB) FF' LKc crc Ac Mc modelc o 32 0 0 B1 (aobj_cons _ _ _ _ AOB) ltac:(clear; lia) ltac:(reflexivity)) as ((_ & OCE & _) & _).
    right. clear - OCE SLO HSCR. lia. }
  pose proof (NCSX to AOT) as TFRX. pose proof (NCSX qo AOQ) as OFRX.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (STFRX : to / 8 + 2147450880 + 4 <= E - 400 \/ E - 400 + 400 <= to / 8 + 2147450880) by (left; clear - TRP ER; lia).
  assert (SOFRX : qo / 8 + 2147450880 + 4 <= E - 400 \/ E - 400 + 400 <= qo / 8 + 2147450880) by (left; clear - ORP ER; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  assert (SCELL : forall a v, SPA <= a -> a + 8 <= E -> L5.u64_at RSEGS Mc a v -> L5.u64_at RSEGS MV a v).
  { intros a v H1 H2 Hc. apply (proj2 (u64_at_vis (ahid Ac modelc) Mc a v ltac:(eapply avis_sub; [exact SV | clear - H1; lia | clear - H2; lia]) ltac:(clear - H1 ER; lia) ltac:(clear - H2 ER; lia))). exact Hc. }
  assert (S232v : L5.u64_at RSEGS MV (E - 152) (to + 16)) by (apply SCELL; [clear; lia | clear; lia | exact S232]).
  assert (S240v : L5.u64_at RSEGS MV (E - 144) 2) by (apply SCELL; [clear; lia | clear; lia | exact S240]).
  assert (S248v : L5.u64_at RSEGS MV (E - 136) (qo + 16)) by (apply SCELL; [clear; lia | clear; lia | exact S248]).
  assert (S256v : L5.u64_at RSEGS MV (E - 128) lenq) by (apply SCELL; [clear; lia | clear; lia | exact S256]).
  assert (S104v : L5.u64_at RSEGS MV (E - 280) (F + 96)) by (apply SCELL; [clear; lia | clear; lia | exact S104]).
  assert (S88v : L5.u64_at RSEGS MV (E - 296) qo) by (apply SCELL; [clear; lia | clear; lia | exact S88]).
  assert (HVD : 0 <= d0 < 2 ^ 64) by (clear - DR; lia). assert (HVW : 0 <= tw <= 18446744073709551615) by (clear - TWR; lia).
  assert (HVLQ : 0 <= lenq <= 18446744073709551615) by (clear - LQR; lia).
  set (Wp := fun a => (qo + k <= a < qo + k + 8) \/ (E - 392 <= a < E - 384)).
  assert (WPOK : forall a, 0 <= a < 2 ^ 64 -> Wp a -> L5DKA.wp_ok L ar LB FF E SCRD SPA (docell E) F 3 W BX a).
  { intros a Ha Wa. subst Wp; cbn beta in Wa. assert (KR : k = 16 \/ k = 24) by (subst k; destruct last; [left|right]; reflexivity). destruct Wa as [Wa|Wa].
    - destruct (OCL a ltac:(clear - Wa KR; lia)) as (C1 & C2 & C3 & C4). split. exact C4. split. split. exact C1. exact C2. intros _. apply WRO. clear - Wa KR; lia.
    - eapply (L5ADVHC.wp_scratch L ar C HI LY HIok); try first [exact G | exact ER | exact EA | exact HSCR | exact BI]. clear - Wa HSCR; lia. }
  assert (FIN : forall (fx1 : FPState) R1 M1v pcx, msteps RSEGS (st fx Rc 0x93568 MV) (st fx1 R1 pcx M1v) -> mem_grows MV M1v ->
            (forall a, 0 <= a < 2 ^ 64 -> ~ Wp a -> M1v (Z_to_bv 64 a) = MV (Z_to_bv 64 a)) -> pcx = (if last then L5ARED.REDUCE else 0x93568) ->
            (forall M1 model1, binv W BX M1 model1 LKc crc Ac -> (forall a, 0 <= a < 2 ^ 64 -> ~ (qo + k <= a < qo + k + 8) -> ~ (E - 392 <= a < E - 384) -> M1 (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)) -> L5.defined M1 (qo + k) 8 ->
                srealizes RSEGS SCFG (cfg (fx:=fx1) R1 pcx M1 model1) K) ->
            srealizes RSEGS SCFG (cfg (fx:=fx) Rc 0x93568 Mc modelc) K).
  { intros fx1 R1 M1v pcx pMS MG1 pFZ EPC KF1.
    apply (L5DKA.bstage L ar C HI LY HIok M model LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2 G W _ Mc modelc LKc crc Ac fx fx1 Rc 0x93568 R1 pcx M1v Wp K BI pMS MG1 pFZ WPOK).
    intros M1 model1 BI1 AH1 VIS1 MGM1 FRM1. apply (KF1 M1 model1 BI1).
    - intros a Ha N1 N2. apply FRM1. exact Ha. subst Wp; cbn beta. clear - N1 N2. lia.
    - eapply L5.defined_grows. exact MGM1. assert (KR : k = 16 \/ k = 24) by (subst k; destruct last; [left|right]; reflexivity).
      pose proof (aobj_facts L ar C HI LY HIok (BX ++ LB) FF' LKc crc Ac Mc modelc qo 32 0 0 (proj1 BI) (aobj_cons _ _ _ _ AOQ) ltac:(clear; lia) ltac:(reflexivity)) as (_ & _ & ODEF & _).
      eapply L5.defined_sub. exact ODEF. clear - KR; lia. clear - KR; lia. }
  assert (HV21 : 0 <= U Rc 21 <= 18446744073709551615) by (pose proof (UR Rc 21) as X; clear - X; lia).
  destruct last; subst k; cbn iota in *.
  - pose proof (v5HLb_conc fx Rc MV (fun j => match j with 2%nat => E | 33%nat => to | 35%nat => qo | 40%nat => F | 41%nat => fl | 58%nat => U Rc 1 | 68%nat => d0 | 70%nat => tw | 71%nat => U Rc 21 | 73%nat => lenq | _ => 0 end)) as P. cbn beta iota in P.
    feed P ltac:(first [apply UR | apply U_to | sc | (apply TXC; [clear; lia | clear; lia | sc]) ]).
    destruct P as (fx1 & R1 & M1v & MG1 & pFR & pFZ & (pMS & pKS & pR1 & pR10 & pR14 & pR19 & pR25 & pS)).
    apply (FIN fx1 R1 M1v L5ARED.REDUCE pMS MG1). { intros a Ha Hn. apply pFZ. exact Ha. all: subst Wp; cbn beta in Hn; clear - Hn; lia. } reflexivity.
    intros M1 model1 BI1 AG1 DF1. apply (KF fx1 R1 M1 model1 BI1 pKS). split. exact pR1. split. exact pR10. exact pR25. exact AG1. exact DF1.
  - pose proof (v5HLa_conc fx Rc MV (fun j => match j with 2%nat => E | 33%nat => to | 35%nat => qo | 40%nat => F | 41%nat => fl | 58%nat => U Rc 1 | 68%nat => d0 | 70%nat => tw | 73%nat => lenq | _ => 0 end)) as P. cbn beta iota in P.
    feed P ltac:(first [apply UR | apply U_to | sc | (apply TXC; [clear; lia | clear; lia | sc]) ]).
    destruct P as (fx1 & R1 & M1v & MG1 & pFR & pFZ & (pMS & pKS & pR1 & pR10 & pR14 & pR19 & pR25 & pS)).
    apply (FIN fx1 R1 M1v 0x93568 pMS MG1). { intros a Ha Hn. apply pFZ. exact Ha. all: subst Wp; cbn beta in Hn; clear - Hn; lia. } reflexivity.
    intros M1 model1 BI1 AG1 DF1. apply (KF fx1 R1 M1 model1 BI1 pKS). split. exact pR19. exact pR25. exact AG1. exact DF1.
Qed.

End DIV.
End WithIface.
End SCFG_1.
End L5ADVHL2.
