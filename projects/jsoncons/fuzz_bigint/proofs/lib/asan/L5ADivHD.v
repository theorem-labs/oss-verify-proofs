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
     AsanAcct AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5LazyA L5DefsA
     L5CoreA L5CoreSpecsA L5StepA L5CoreB L5ADetailH L5AFrameK L5DivKitA L5ADivH L5ADivT L5ADivD L5ADivP2 L5ADivE L5ADivEA L5ADivHC.
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
Local Notation binv := (L5AFK.binv L ar HI M model LB FF LK A E SCRD SPA (down E F ro R) F 3).
Local Notation SH := (F / 8 + 2147450880).

(* [comment removed for export] *)
Local Ltac open_ctx BI :=
  let PF := fresh "PF" in
  pose proof (pf_of_binv L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G _ _ _ _ _ _ _ BI) as PF;
  destruct PF as (W352 & IMGC & CSB & CUAR & FDEFv & FWv & FSHWv & FLCv & FLWv);
  pose proof (NUM L ar HI R LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER) as ((FRG & FLRG & ERG) & FRP & FLRP & ALF & FBIG & FLBIG & FLA & SFA & SFLA & SFB);
  destruct (L5AFK.vis_facts L ar C HI LY HIok M model LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2 G _ _ _ _ _ _ _ BI) as (_ & OWNv & _ & (_ & _ & FV & SV & SHV));
  change (ff_bytes 3) with 512 in FV; change (ff_bytes 3 / 8) with 64 in SHV.

(* [comment removed for export] *)
Lemma p4e (fx : FPState) Rc Mc modelc W BX LKc crc Ac :
  binv W BX Mc modelc LKc crc Ac -> rinvD R E Rc -> getr Rc (reg 10) = Z_to_bv 64 18446744073709551615 -> getr Rc (reg 24) = Z_to_bv 64 (F + 96) ->
  (forall (fx1 : FPState) R1 M1 model1,
      binv W BX M1 model1 LKc crc Ac ->
      (forall x, In x KS_v5P4e -> getr R1 (reg x) = getr Rc (reg x)) -> getr R1 (reg 21) = Z_to_bv 64 (F + 96) ->
      (forall a, 0 <= a < 2 ^ 64 -> ~ (E - 272 <= a < E - 264) -> M1 (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)) ->
      L5.u64_at RSEGS M1 (E - 272) (F + 96) ->
      srealizes RSEGS SCFG (cfg (fx:=fx1) R1 0x923a0 M1 model1) K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc 0x92374 Mc modelc) K.
Proof.
  intros BI RI X10 X24 KF. open_ctx BI. pose proof RI as (X2 & X8 & X9 & X3 & X4).
  set (MV := mrestrict (ahid Ac modelc) Mc) in *.
  pose proof (v5P4e_conc fx Rc MV (fun j => match j with 2%nat => E | 40%nat => F | 41%nat => fl | 58%nat => U Rc 1 | _ => 0 end)) as P. cbn beta iota in P.
  feed P ltac:(first [apply UR | apply U_to | sc ]).
  destruct P as (fx1 & R1 & M1v & MG1 & pFR & pFZ & (pMS & pKS & pR21 & pS80)).
  set (Wp := fun a => E - 272 <= a < E - 264).
  apply (L5DKA.bstage L ar C HI LY HIok M model LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2 G W _ Mc modelc LKc crc Ac fx fx1 Rc 0x92374 R1 0x923a0 M1v Wp K BI pMS MG1).
  { intros a Ha Hn. apply pFZ. exact Ha. subst Wp; cbn beta in Hn; clear - Hn; lia. }
  { intros a Ha Wa. subst Wp; cbn beta in Wa. apply (L5DKA.wp_frame L ar HI LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2 G); [clear - Wa; lia | unfold docell; clear - Wa; lia]. }
  intros M1 model1 BI1 AH1 VIS1 MGM1 FRM1.
  apply (KF fx1 R1 M1 model1 BI1 pKS pR21).
  - intros a Ha N1. apply FRM1. exact Ha. subst Wp; cbn beta. exact N1.
  - apply (proj1 (u64_at_vis (ahid Ac modelc) M1 (E - 272) _ ltac:(eapply avis_sub; [exact SV | clear; lia | clear; lia]) ltac:(clear - ER; lia) ltac:(clear - ER; lia))). rewrite VIS1. exact pS80.
Qed.

(* [comment removed for export] *)
Lemma p2z (fx : FPState) Rc Mc modelc W BX LKc crc Ac fd v0 v1 :
  binv W BX Mc modelc LKc crc Ac -> rinvD R E Rc -> getr Rc (reg 18) = Z_to_bv 64 SH -> getr Rc (reg 20) = Z_to_bv 64 2147450880 -> getr Rc (reg 23) = Z_to_bv 64 (F + 32) -> getr Rc (reg 27) = Z_to_bv 64 F ->
  L5.big_at RSEGS Mc (F + 32) (L5.BO fd 0 (L5.BInl v0 v1)) ->
  (forall (fx1 : FPState) R1 M1 model1,
      binv W BX M1 model1 LKc crc Ac ->
      (forall x, In x KS_v5P2z -> getr R1 (reg x) = getr Rc (reg x)) ->
      getr R1 (reg 10) = Z_to_bv 64 16 -> getr R1 (reg 20) = Z_to_bv 64 0 -> getr R1 (reg 21) = Z_to_bv 64 fd -> getr R1 (reg 26) = Z_to_bv 64 (F + 48) ->
      (forall a, 0 <= a < 2 ^ 64 -> ~ (E - 264 <= a < E - 256) -> ~ (E - 296 <= a < E - 288) -> M1 (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)) ->
      L5.u64_at RSEGS M1 (E - 296) F -> L5.u64_at RSEGS M1 (E - 264) (F + 32) ->
      srealizes RSEGS SCFG (cfg (fx:=fx1) R1 0x92de0 M1 model1) K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc 0x922cc Mc modelc) K.
Proof.
  intros BI RI X18 X20 X23 X27 OD KF. open_ctx BI. pose proof RI as (X2 & X8 & X9 & X3 & X4).
  set (MV := mrestrict (ahid Ac modelc) Mc) in *.
  destruct OD as (D0 & FDR & D8 & (BT0 & _)). cbn [L5.bo_fb L5.bo_len L5.bo_st] in *.
  assert (D0v : L5.u8_at RSEGS MV (F + 32) fd).
  { apply (proj2 (u8_at_vis (ahid Ac modelc) Mc (F + 32) fd ltac:(eapply avis_sub; [exact FV | clear; lia | clear; lia]) ltac:(clear - FRP; lia) ltac:(clear - FRP; lia))). exact D0. }
  assert (D8v : L5.u64_at RSEGS MV (F + 40) 0).
  { apply (proj2 (u64_at_vis (ahid Ac modelc) Mc (F + 40) 0 ltac:(eapply avis_sub; [exact FV | clear; lia | clear; lia]) ltac:(clear - FRP; lia) ltac:(clear - FRP; lia))). replace (F + 40) with (F + 32 + 8) by (clear; lia). exact D8. }
  assert (HVF : 0 <= fd <= 255 /\ 0 <= fd < 2 ^ 64) by (clear - FDR; lia). destruct HVF as [HVF HVF'].
  pose proof (v5P2z_conc fx Rc MV (fun j => match j with 2%nat => E | 33%nat => U Rc 24 | 35%nat => U Rc 19 | 37%nat => U Rc 22 | 40%nat => F | 41%nat => fl | 55%nat => fd | 58%nat => U Rc 1 | _ => 0 end)) as P. cbn beta iota in P.
  feed P ltac:(first [apply UR | apply U_to | sc ]).
  destruct P as (fx1 & R1 & M1v & MG1 & pFR & pFZ & (pMS & pKS & pR10 & pR20 & pR21 & pR26 & pS56 & pS88)).
  set (Wp := fun a => (E - 264 <= a < E - 256) \/ (E - 296 <= a < E - 288)).
  apply (L5DKA.bstage L ar C HI LY HIok M model LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2 G W _ Mc modelc LKc crc Ac fx fx1 Rc 0x922cc R1 0x92de0 M1v Wp K BI pMS MG1).
  { intros a Ha Hn. apply pFZ. exact Ha. all: subst Wp; cbn beta in Hn; clear - Hn; lia. }
  { intros a Ha Wa. subst Wp; cbn beta in Wa. apply (L5DKA.wp_frame L ar HI LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2 G); [clear - Wa; lia | unfold docell; clear - Wa; lia]. }
  intros M1 model1 BI1 AH1 VIS1 MGM1 FRM1.
  assert (SPV : forall a v, SPA <= a -> a + 8 <= E -> L5.u64_at RSEGS M1v a v -> L5.u64_at RSEGS M1 a v).
  { intros a v H1 H2 Hc. apply (proj1 (u64_at_vis (ahid Ac modelc) M1 a v ltac:(eapply avis_sub; [exact SV | clear - H1; lia | clear - H2; lia]) ltac:(clear - H1 ER; lia) ltac:(clear - H2 ER; lia))). rewrite VIS1. exact Hc. }
  apply (KF fx1 R1 M1 model1 BI1 pKS pR10 pR20 pR21 pR26).
  - intros a Ha N1 N2. apply FRM1. exact Ha. subst Wp; cbn beta. clear - N1 N2. lia.
  - apply SPV. clear; lia. clear; lia. exact pS56.
  - apply SPV. clear; lia. clear; lia. exact pS88.
Qed.
End DIV.
End WithIface.
End SCFG_1.
End L5ADVHD.
