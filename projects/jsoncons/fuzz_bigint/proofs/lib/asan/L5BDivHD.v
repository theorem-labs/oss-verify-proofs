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
     L5CoreAB0 L5CoreSpecsAB0 L5StepAB0 L5CoreBB0 L5BDetailG L5BFrameK L5DivKitAB0 L5BDivH L5BDivT L5BDivD L5BDivP2 L5BDivE L5BDivEA L5BDivHC.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5ADVHD.
Import L5A. Import L5CA. Import L5CSA. Import L5SA. Import L5CB. Import L5ADH. Import L5ADVH. Import L5ADVT. Import L5ADVD. Import L5ADVE. Import L5ADVEA. Import L5ADVHC. Import L5ADIVP2.
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
Local Notation binv := (L5AFK.binv L ar HI M model LB FF LK A E SCRD SPA (down E F ro R) F 3).
Local Notation SH := (F / 8 + 2147450880).

(* [comment removed for export] *)
Local Ltac open_ctx BI :=
  let PF := fresh "PF" in
  pose proof (pf_of_binv L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G _ _ _ _ _ _ _ BI) as PF;
  destruct PF as (W384 & IMGC & CSB & CUAR & FDEFv & FWv & FSHWv & FLCv & FLWv);
  pose proof (NUM L ar HI R LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER) as ((FRG & FLRG & ERG) & FRP & FLRP & ALF & FBIG & FLBIG & FLA & SFA & SFLA & SFB);
  destruct (L5AFK.vis_facts L ar C HI LY HIok M model LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2 G _ _ _ _ _ _ _ BI) as (_ & OWNv & _ & (_ & _ & FV & SV & SHV));
  change (ff_bytes 3) with 512 in FV; change (ff_bytes 3 / 8) with 64 in SHV.

(* [comment removed for export] *)
Lemma p4e (fx : FPState) Rc Mc modelc W BX LKc crc Ac :
  binv W BX Mc modelc LKc crc Ac -> rinvD R E Rc -> getr Rc (reg 10) = Z_to_bv 64 18446744073709551615 -> getr Rc (reg 18) = Z_to_bv 64 SH -> getr Rc (reg 25) = Z_to_bv 64 (F + 96) ->
  (forall (fx1 : FPState) R1 M1 model1,
      binv W BX M1 model1 LKc crc Ac ->
      (forall x, In x KS_v5P4e -> getr R1 (reg x) = getr Rc (reg x)) ->
      (forall a, 0 <= a < 2 ^ 64 -> ~ (E - 280 <= a < E - 272) -> M1 (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)) ->
      L5.u64_at RSEGS M1 (E - 280) (F + 96) ->
      srealizes RSEGS SCFG (cfg (fx:=fx1) R1 0x92cb8 M1 model1) K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc 0x92c94 Mc modelc) K.
Proof.
  intros BI RI X10 X18 X25r KF. open_ctx BI. pose proof RI as (X2 & X8 & X9 & X3 & X4 & XSB).
  set (MV := mrestrict (ahid Ac modelc) Mc) in *.
  pose proof (v5P4e_conc fx Rc MV (fun j => match j with 2%nat => E | 40%nat => F | 41%nat => fl | 58%nat => U Rc 1 | _ => 0 end)) as P. cbn beta iota in P.
  feed P ltac:(first [apply UR | apply U_to | sc ]).
  destruct P as (fx1 & R1 & M1v & MG1 & pFR & pFZ & (pMS & pKS & pS80)).
  set (Wp := fun a => E - 280 <= a < E - 272).
  apply (L5DKA.bstage L ar C HI LY HIok M model LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2 G W _ Mc modelc LKc crc Ac fx fx1 Rc 0x92c94 R1 0x92cb8 M1v Wp K BI pMS MG1).
  { intros a Ha Hn. apply pFZ. exact Ha. subst Wp; cbn beta in Hn; clear - Hn; lia. }
  { intros a Ha Wa. subst Wp; cbn beta in Wa. apply (L5DKA.wp_frame L ar HI LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2 G); [clear - Wa; lia | unfold docell; clear - Wa; lia]. }
  intros M1 model1 BI1 AH1 VIS1 MGM1 FRM1.
  apply (KF fx1 R1 M1 model1 BI1 pKS).
  - intros a Ha N1. apply FRM1. exact Ha. subst Wp; cbn beta. exact N1.
  - apply (proj1 (u64_at_vis (ahid Ac modelc) M1 (E - 280) _ ltac:(eapply avis_sub; [exact SV | clear; lia | clear; lia]) ltac:(clear - ER; lia) ltac:(clear - ER; lia))). rewrite VIS1. exact pS80.
Qed.

(* [comment removed for export] *)
Lemma p2z (fx : FPState) Rc Mc modelc W BX LKc crc Ac fd v0 v1 to rd :
  binv W BX Mc modelc LKc crc Ac -> rinvD R E Rc -> getr Rc (reg 18) = Z_to_bv 64 SH -> getr Rc (reg 19) = Z_to_bv 64 ro -> getr Rc (reg 22) = Z_to_bv 64 F -> getr Rc (reg 24) = Z_to_bv 64 (F + 32) ->
  getr Rc (reg 25) = Z_to_bv 64 rd -> getr Rc (reg 27) = Z_to_bv 64 F -> L5.u64_at RSEGS Mc (E - 264) to -> 0 <= ro < 2 ^ 64 -> 0 <= rd < 2 ^ 64 -> 0 <= to < 2 ^ 64 ->
  L5.big_at RSEGS Mc (F + 32) (L5.BO fd 0 (L5.BInl v0 v1)) -> shr8 Mc F 4 4 0 ->
  (forall (fx1 : FPState) R1 M1 model1,
      binv W BX M1 model1 LKc crc Ac ->
      (forall x, In x KS_v5P2z -> getr R1 (reg x) = getr Rc (reg x)) ->
      getr R1 (reg 10) = Z_to_bv 64 16 -> getr R1 (reg 20) = Z_to_bv 64 fd ->
      (forall a, 0 <= a < 2 ^ 64 -> ~ (E - 360 <= a < E - 352) -> ~ (E - 336 <= a < E - 328) -> ~ (E - 304 <= a < E - 296) -> ~ (E - 288 <= a < E - 280) -> ~ (E - 120 <= a < E - 104) -> M1 (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)) ->
      L5.u64_at RSEGS M1 (E - 360) F -> L5.u64_at RSEGS M1 (E - 336) F -> L5.u64_at RSEGS M1 (E - 304) (F + 32) -> L5.u64_at RSEGS M1 (E - 288) ro ->
      L5.u64_at RSEGS M1 (E - 120) (F + 48) -> L5.u64_at RSEGS M1 (E - 112) 0 ->
      srealizes RSEGS SCFG (cfg (fx:=fx1) R1 0x93890 M1 model1) K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc 0x92bd4 Mc modelc) K.
Proof.
  intros BI RI X18 X19 X22 X24 X25r X27 S120 ROR RDR TOR OD SHD KF. open_ctx BI. pose proof RI as (X2 & X8 & X9 & X3 & X4 & XSB).
  set (MV := mrestrict (ahid Ac modelc) Mc) in *.
  destruct OD as (D0 & FDR & D8 & (BT0 & _)). cbn [L5.bo_fb L5.bo_len L5.bo_st] in *.
  assert (D0v : L5.u8_at RSEGS MV (F + 32) fd).
  { apply (proj2 (u8_at_vis (ahid Ac modelc) Mc (F + 32) fd ltac:(eapply avis_sub; [exact FV | clear; lia | clear; lia]) ltac:(clear - FRP; lia) ltac:(clear - FRP; lia))). exact D0. }
  assert (D8v : L5.u64_at RSEGS MV (F + 40) 0).
  { apply (proj2 (u64_at_vis (ahid Ac modelc) Mc (F + 40) 0 ltac:(eapply avis_sub; [exact FV | clear; lia | clear; lia]) ltac:(clear - FRP; lia) ltac:(clear - FRP; lia))). replace (F + 40) with (F + 32 + 8) by (clear; lia). exact D8. }
  assert (HVF : 0 <= fd <= 255 /\ 0 <= fd < 2 ^ 64) by (clear - FDR; lia). destruct HVF as [HVF HVF'].
  assert (S120v : L5.u64_at RSEGS MV (E - 264) to).
  { apply (proj2 (u64_at_vis (ahid Ac modelc) Mc (E - 264) to ltac:(eapply avis_sub; [exact SV | clear; lia | clear; lia]) ltac:(clear - ER; lia) ltac:(clear - ER; lia))). exact S120. }
  pose proof (L5ADVHC.fshz_vis L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER _ _ _ _ _ _ _ 4 4 2147450884 BI SHD ltac:(clear; lia) ltac:(clear; lia) eq_refl) as DZv.
  assert (HVRO : 0 <= ro <= 18446744073709551615) by (clear - ROR; lia). assert (HVRD : 0 <= rd <= 18446744073709551615) by (clear - RDR; lia). assert (HVTO : 0 <= to <= 18446744073709551615) by (clear - TOR; lia).
  pose proof (v5P2z_conc fx Rc MV (fun j => match j with 2%nat => E | 33%nat => to | 36%nat => ro | 37%nat => rd | 40%nat => F | 41%nat => fl | 55%nat => fd | 58%nat => U Rc 1 | _ => 0 end)) as P. cbn beta iota in P.
  feed P ltac:(first [apply UR | apply U_to | sc ]).
  destruct P as (fx1 & R1 & M1v & MG1 & pFR & pFZ & (pMS & pKS & pR10 & pR11 & pR12 & pR13 & pR20 & pS24 & pS48 & pS80 & pS272 & pS264 & pS96)).
  set (Wp := fun a => (E - 360 <= a < E - 352) \/ (E - 336 <= a < E - 328) \/ (E - 304 <= a < E - 296) \/ (E - 288 <= a < E - 280) \/ (E - 120 <= a < E - 104)).
  apply (L5DKA.bstage L ar C HI LY HIok M model LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2 G W _ Mc modelc LKc crc Ac fx fx1 Rc 0x92bd4 R1 0x93890 M1v Wp K BI pMS MG1).
  { intros a Ha Hn. apply pFZ. exact Ha. all: subst Wp; cbn beta in Hn; clear - Hn; lia. }
  { intros a Ha Wa. subst Wp; cbn beta in Wa. apply (L5DKA.wp_frame L ar HI LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2 G); [clear - Wa; lia | unfold docell; clear - Wa; lia]. }
  intros M1 model1 BI1 AH1 VIS1 MGM1 FRM1.
  assert (SPV : forall a v, SPA <= a -> a + 8 <= E -> L5.u64_at RSEGS M1v a v -> L5.u64_at RSEGS M1 a v).
  { intros a v H1 H2 Hc. apply (proj1 (u64_at_vis (ahid Ac modelc) M1 a v ltac:(eapply avis_sub; [exact SV | clear - H1; lia | clear - H2; lia]) ltac:(clear - H1 ER; lia) ltac:(clear - H2 ER; lia))). rewrite VIS1. exact Hc. }
  apply (KF fx1 R1 M1 model1 BI1 pKS pR10 pR20).
  - intros a Ha N1 N2 N3 N4 N5. apply FRM1. exact Ha. subst Wp; cbn beta. clear - N1 N2 N3 N4 N5. lia.
  - apply SPV. clear; lia. clear; lia. exact pS24.
  - apply SPV. clear; lia. clear; lia. exact pS48.
  - apply SPV. clear; lia. clear; lia. exact pS80.
  - apply SPV. clear; lia. clear; lia. exact pS96.
  - apply SPV. clear; lia. clear; lia. exact pS264.
  - apply SPV. clear; lia. clear; lia. exact pS272.
Qed.
End DIV.
End WithIface.
End SCFG_1.
End L5ADVHD.
