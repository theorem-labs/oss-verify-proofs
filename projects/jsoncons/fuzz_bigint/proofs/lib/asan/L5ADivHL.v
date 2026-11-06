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
     L5Cmp L5CoreA L5CoreSpecsA L5StepA L5CoreB L5ADetailH L5AFrameK L5DivKitA L5ADivH L5ADivT L5ADivD L5ADivPH L5ADivPL L5ADivE L5ADivEA L5ADivHC L5ADivHD L5ADivHA L5ARed.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5ADVHL.
Import L5A. Import L5CA. Import L5CSA. Import L5SA. Import L5CB. Import L5ADH. Import L5ADVH. Import L5ADVT. Import L5ADVD. Import L5ADVE. Import L5ADVEA. Import L5ADVHC. Import L5ADVHD. Import L5ADVHA. Import L5ADIVPH. Import L5ADIVPL.
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
Hypothesis Hrsz : resize_spec L ar HI.
Local Notation binv := (L5AFK.binv L ar HI M model LB FF LK A E SCRD SPA (down E F ro R) F 3).
Local Notation FF' := ((F, 3, SPA + 32) :: FF).
Local Notation SH := (F / 8 + 2147450880).

Local Ltac open_ctx BI :=
  let PF := fresh "PF" in
  pose proof (pf_of_binv L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G _ _ _ _ _ _ _ BI) as PF;
  destruct PF as (W352 & IMGC & CSB & CUAR & FDEFv & FWv & FSHWv & FLCv & FLWv);
  pose proof (NUM L ar HI R LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER) as ((FRG & FLRG & ERG) & FRP & FLRP & ALF & FBIG & FLBIG & FLA & SFA & SFLA & SFB);
  destruct (L5AFK.vis_facts L ar C HI LY HIok M model LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2 G _ _ _ _ _ _ _ BI) as (_ & OWNv & _ & (_ & _ & FV & SV & SHV));
  change (ff_bytes 3) with 512 in FV; change (ff_bytes 3 / 8) with 64 in SHV.


(* [comment removed for export] *)
Lemma word_of_defined (Mk : word -> option byte) a : L5.defined Mk a 8 -> 0 <= a -> a + 8 <= 2 ^ 64 -> exists w, L5.u64_at RSEGS Mk a w /\ 0 <= w < 2 ^ 64.
Proof.
  intros D Ha Hb. destruct (L5SA.limbs_of_defined Mk a 1 ltac:(exact D) Ha ltac:(clear - Hb; lia)) as (ws & Lw & Rw & LA).
  destruct ws as [|w [|]]; cbn in Lw; try (exfalso; clear - Lw; lia). exists w. split. pose proof (LA 0%nat ltac:(cbn; clear; lia)) as X. rewrite Z.mul_0_r, Z.add_0_r in X. exact X.
  inversion Rw. assumption.
Qed.
(* [comment removed for export] *)
Lemma arg_shz cr0 W BX Mc modelc LKc crc Ac o : ri_inv HI LB FF LK cr0 A M (vml_of model) ->
  binv W BX Mc modelc LKc crc Ac -> aobj FF o 32 -> shadow_zero M o 4 -> (forall j, 0 <= j < 4 -> L5.outside W (o / 8 + SB + j)) -> shadow_zero Mc o 4.
Proof.
  intros HH0 (_ & _ & _ & _ & _ & _ & EK & _) AOB SZ NW.
  pose proof (aobj_facts L ar C HI LY HIok LB FF LK cr0 A M model o 32 E SCRD HH0 AOB ltac:(clear; lia) ltac:(reflexivity)) as (OR & OBIG & ODEF & OVIS & OVSH & OCL & OCLSH). change (32 / 8) with 4 in OCLSH.
  intros j Hj. unfold byte_at. rewrite EK. apply SZ. exact Hj. split.
  unfold S, SB. clear - Hj OR OBIG. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
  split. unfold S. apply OCLSH. exact Hj. unfold S. apply NW. exact Hj.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
Definition spl (Mk : word -> option byte) (cells : list (Z * Z)) : Prop := forall a v, In (a, v) cells -> L5.u64_at RSEGS Mk a v /\ SPA <= a /\ a + 8 <= E.
Lemma spl_keep LBx scr (X : Z -> Prop) Mc M1 cells : spl Mc cells -> L5ADVEA.offx L ar FF E F LBx scr X Mc M1 -> (forall i, SPA <= i < E -> ~ X i) -> spl M1 cells.
Proof.
  intros SP OFF NX a v Hin. destruct (SP a v Hin) as (Hc & H1 & H2). split. 2: split; assumption.
  eapply L5ADVEA.spill_keep; try first [exact LY | exact HIok | exact G | exact ER | exact HSCR]; [exact Hc | exact H1 | exact H2 | exact OFF | ]. intros i Hi. apply NX. clear - Hi H1 H2. lia.
Qed.
Lemma spl_vis W BX Mc modelc LKc crc Ac cells a v : binv W BX Mc modelc LKc crc Ac -> spl Mc cells -> In (a, v) cells -> L5.u64_at RSEGS (mrestrict (ahid Ac modelc) Mc) a v.
Proof.
  intros BI SP Hin. destruct (SP a v Hin) as (Hc & H1 & H2). open_ctx BI.
  apply (proj2 (u64_at_vis (ahid Ac modelc) Mc a v ltac:(eapply avis_sub; [exact SV | clear - H1; lia | clear - H2; lia]) ltac:(clear - H1 ER; lia) ltac:(clear - H2 ER; lia))). exact Hc.
Qed.
(* [comment removed for export] *)
Lemma shz_vis W BX Mc modelc LKc crc Ac off n k : binv W BX Mc modelc LKc crc Ac -> shr8 Mc F off n 0 -> 0 <= off -> off + n <= 64 -> k = 2147450880 + off ->
  L5KA.zeros_at (mrestrict (ahid Ac modelc) Mc) (F / 8 + k) n.
Proof.
  intros BI SHR O1 O2 -> i Hi. open_ctx BI.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (SQ : 0 <= F / 8 /\ F / 8 + 64 <= 17592186044416) by (hnf in ALF; clear - FRP ALF; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  apply byte_of_u8. 2: right; clear - SQ O1 Hi; lia. 2: clear - SQ O1 O2 Hi; lia.
  apply (proj2 (u8_at_vis (ahid Ac modelc) Mc (F / 8 + (2147450880 + off) + i) 0 ltac:(eapply avis_sub; [exact SHV | unfold SB; clear - O1 Hi; lia | unfold SB; clear - O1 O2 Hi; lia]) ltac:(clear - SQ O1 Hi; lia) ltac:(clear - SQ O1 O2 Hi; lia))).
  pose proof (SHR i Hi) as U8. unfold SB in U8. replace (F / 8 + (2147450880 + off) + i) with (F / 8 + 2147450880 + off + i) by (clear; lia). exact U8.
Qed.

(* [comment removed for export] *)
Lemma ht (fx : FPState) Rc Mc modelc W BX LKc crc Ac to qo d0 lent (toG : bool) :
  binv W BX Mc modelc LKc crc Ac -> rinvD R E Rc -> getr Rc (reg 10) = Z_to_bv 64 (to + 8) -> getr Rc (reg 22) = Z_to_bv 64 qo -> getr Rc (reg 26) = Z_to_bv 64 (F + 48) ->
  L5.u64_at RSEGS Mc (E - 296) F -> shr8 Mc F 4 4 0 -> L5.u64_at RSEGS Mc (F + 48) d0 -> (if toG then 4294967296 <= d0 < 2 ^ 64 else 0 <= d0 <= 4294967295) ->
  aobj FF to 32 -> shadow_zero Mc to 4 -> L5.u64_at RSEGS Mc (to + 8) lent -> 0 <= lent < 2 ^ 64 -> 0 <= qo < 2 ^ 64 ->
  (forall (fx1 : FPState) R1 model1,
      binv W BX Mc model1 LKc crc Ac -> (forall x, In x (if toG then KS_v5HTg else KS_v5HTh) -> getr R1 (reg x) = getr Rc (reg x)) -> getr R1 (reg 23) = Z_to_bv 64 d0 ->
      (if toG then True else getr R1 (reg 1) = Z_to_bv 64 0x926b0 /\ getr R1 (reg 10) = Z_to_bv 64 qo /\ getr R1 (reg 11) = Z_to_bv 64 lent /\ getr R1 (reg 24) = Z_to_bv 64 lent /\ getr R1 (reg 27) = Z_to_bv 64 F) ->
      srealizes RSEGS SCFG (cfg (fx:=fx1) R1 (if toG then 0x926d8 else RESIZE) Mc model1) K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc 0x9267c Mc modelc) K.
Proof.
  intros BI RI X10 X22 X26 S56 SHD D0 DR AOT SZT TL LTR QOR KF. open_ctx BI. pose proof RI as (X2 & X8 & X9 & X3 & X4). pose proof BI as (B1 & B2 & _).
  pose proof (arg_facts L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G W _ Mc modelc LKc crc Ac to BI AOT SZT)
    as ((ORP & ORG & O8) & OBIG & OZv & OWv & OFR & OF & OSH & SOF & SOSH & SOFR & XB & XC & OCL).
  pose proof (shz_vis W BX Mc modelc LKc crc Ac 4 4 2147450884 BI SHD ltac:(clear; lia) ltac:(clear; lia) eq_refl) as DZv.
  set (MV := mrestrict (ahid Ac modelc) Mc) in *.
  destruct OWNv as (_ & _ & _ & OW112 & OW152 & _).
  assert (ALO : aligned to 8) by exact O8.
  assert (S56v : L5.u64_at RSEGS MV (E - 296) F).
  { apply (proj2 (u64_at_vis _ Mc (E - 296) _ ltac:(eapply avis_sub; [exact SV | clear; lia | clear; lia]) ltac:(clear - ER; lia) ltac:(clear - ER; lia))). exact S56. }
  assert (D0v : L5.u64_at RSEGS MV (F + 48) d0).
  { apply (proj2 (u64_at_vis _ Mc (F + 48) _ ltac:(eapply avis_sub; [exact FV | clear; lia | clear; lia]) ltac:(clear - FRP; lia) ltac:(clear - FRP; lia))). exact D0. }
  assert (TLv : L5.u64_at RSEGS MV (to + 8) lent) by (apply XC; [clear; lia | clear; lia | exact TL]).
  assert (HVQ : 0 <= qo <= 18446744073709551615) by (clear - QOR; lia). assert (HVL : 0 <= lent <= 18446744073709551615) by (clear - LTR; lia).
  destruct toG.
  - assert (HVD : 0 <= d0 < 2 ^ 64) by (clear - DR; lia).
    pose proof (v5HTg_conc fx Rc MV (fun j => match j with 2%nat => E | 33%nat => to | 35%nat => qo | 40%nat => F | 41%nat => fl | 58%nat => U Rc 1 | 67%nat => lent | 68%nat => d0 | _ => 0 end)) as P. cbn beta iota in P.
    feed P ltac:(first [apply UR | apply U_to | sc ]).
    destruct P as (fx1 & R1 & M1v & _ & pFR & _ & (pMS & pKS & pR11 & pR12 & pR23)).
    assert (E1 : M1v = MV) by (apply mem_eq_of_agree; intros a Ha; apply pFR). subst M1v.
    apply (apure L ar C HI LY HIok (BX ++ LB) FF' LKc crc Ac Mc modelc fx fx1 Rc 0x9267c R1 0x926d8 K B1 B2 pMS).
    intros model1 HH1 AM1 RT1 AH1.
    pose proof (L5AFK.binv_model L ar HI M model LB FF LK A E SCRD SPA (down E F ro R) F 3 W BX Mc modelc LKc crc Ac model1 BI HH1 AM1 RT1) as BI1.
    apply (KF fx1 R1 model1 BI1 pKS pR23 I).
  - assert (HVD : 0 <= d0 < 2 ^ 64) by (clear - DR; lia).
    pose proof (v5HTh_conc fx Rc MV (fun j => match j with 2%nat => E | 33%nat => to | 35%nat => qo | 40%nat => F | 41%nat => fl | 58%nat => U Rc 1 | 67%nat => lent | 68%nat => d0 | _ => 0 end)) as P. cbn beta iota in P.
    feed P ltac:(first [apply UR | apply U_to | sc ]).
    destruct P as (fx1 & R1 & M1v & _ & pFR & _ & (pMS & pKS & pR1 & pR10 & pR11 & pR12 & pR23 & pR24 & pR27)).
    assert (E1 : M1v = MV) by (apply mem_eq_of_agree; intros a Ha; apply pFR). subst M1v.
    apply (apure L ar C HI LY HIok (BX ++ LB) FF' LKc crc Ac Mc modelc fx fx1 Rc 0x9267c R1 RESIZE K B1 B2 pMS).
    intros model1 HH1 AM1 RT1 AH1.
    pose proof (L5AFK.binv_model L ar HI M model LB FF LK A E SCRD SPA (down E F ro R) F 3 W BX Mc modelc LKc crc Ac model1 BI HH1 AM1 RT1) as BI1.
    apply (KF fx1 R1 model1 BI1 pKS pR23). split. exact pR1. split. exact pR10. split. exact pR11. split. exact pR24. exact pR27.
Qed.

(* [comment removed for export] *)
Lemma h1 (fx : FPState) Rc Mc modelc W BX LKc crc Ac to qo fq :
  binv W BX Mc modelc LKc crc Ac -> rinvD R E Rc -> getr Rc (reg 21) = Z_to_bv 64 (to + 16) -> getr Rc (reg 22) = Z_to_bv 64 qo -> getr Rc (reg 24) = Z_to_bv 64 2 ->
  aobj FF qo 32 -> shadow_zero Mc qo 4 -> L5.u8_at RSEGS Mc qo fq -> 0 <= fq < 256 -> Z.testbit fq 0 = false -> 4096 <= to <= 140737488355296 ->
  (forall (fx1 : FPState) R1 model1,
      binv W BX Mc model1 LKc crc Ac -> (forall x, In x KS_v5H1i -> getr R1 (reg x) = getr Rc (reg x)) ->
      getr R1 (reg 10) = Z_to_bv 64 (to + 24) -> getr R1 (reg 11) = Z_to_bv 64 (qo + 24) -> getr R1 (reg 12) = Z_to_bv 64 (qo + 24) ->
      getr R1 (reg 20) = Z_to_bv 64 (qo / 8 + 2147450880) -> getr R1 (reg 21) = Z_to_bv 64 (to + 24) -> getr R1 (reg 22) = Z_to_bv 64 0 -> getr R1 (reg 26) = Z_to_bv 64 2147450880 ->
      srealizes RSEGS SCFG (cfg (fx:=fx1) R1 0x92aec Mc model1) K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc 0x926b0 Mc modelc) K.
Proof.
  intros BI RI X21 X22 X24 AOQ SZQ Q0 FQR FQ0 TOR KF. open_ctx BI. pose proof RI as (X2 & X8 & X9 & X3 & X4). pose proof BI as (B1 & B2 & _).
  pose proof (arg_facts L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G W _ Mc modelc LKc crc Ac qo BI AOQ SZQ)
    as ((ORP & ORG & O8) & OBIG & OZv & OWv & OFR & OF & OSH & SOF & SOSH & SOFR & XB & XC & OCL).
  set (MV := mrestrict (ahid Ac modelc) Mc) in *.
  destruct OWNv as (_ & _ & _ & OW112 & OW152 & _).
  assert (ALO : aligned qo 8) by exact O8.
  assert (Q0v : L5.u8_at RSEGS MV qo fq) by (apply XB; exact Q0).
  assert (HVF : 0 <= fq <= 255 /\ 0 <= fq < 2 ^ 64) by (clear - FQR; lia). destruct HVF as [HVF HVF'].
  assert (HVT : 0 <= to < 2 ^ 64) by (clear - TOR; lia).
  pose proof (v5H1i_conc fx Rc MV (fun j => match j with 2%nat => E | 33%nat => to | 35%nat => qo | 40%nat => F | 41%nat => fl | 58%nat => U Rc 1 | 69%nat => fq | _ => 0 end)) as P. cbn beta iota in P.
  feed P ltac:(first [apply UR | apply U_to | sc ]).
  destruct P as (fx1 & R1 & M1v & _ & pFR & _ & (pMS & pKS & pR10 & pR11 & pR12 & pR20 & pR21 & pR22 & pR26)).
  assert (E1 : M1v = MV) by (apply mem_eq_of_agree; intros a Ha; apply pFR). subst M1v.
  apply (apure L ar C HI LY HIok (BX ++ LB) FF' LKc crc Ac Mc modelc fx fx1 Rc 0x926b0 R1 0x92aec K B1 B2 pMS).
  intros model1 HH1 AM1 RT1 AH1.
  pose proof (L5AFK.binv_model L ar HI M model LB FF LK A E SCRD SPA (down E F ro R) F 3 W BX Mc modelc LKc crc Ac model1 BI HH1 AM1 RT1) as BI1.
  apply (KF fx1 R1 model1 BI1 pKS pR10 pR11 pR12 pR20 pR21 pR22 pR26).
Qed.

(* [comment removed for export] *)
Lemma hl (fx : FPState) Rc Mc modelc W BX LKc crc Ac to qo d0 tw (last : bool) :
  let k := if last then 16 else 24 in
  binv W BX Mc modelc LKc crc Ac -> rinvD R E Rc ->
  getr Rc (reg 10) = Z_to_bv 64 (to + k) -> getr Rc (reg 11) = Z_to_bv 64 (qo + k) -> getr Rc (reg 12) = Z_to_bv 64 (qo + k) -> getr Rc (reg 21) = Z_to_bv 64 (to + k) ->
  (if last then True else getr Rc (reg 22) = Z_to_bv 64 0) -> getr Rc (reg 23) = Z_to_bv 64 d0 -> 0 <= d0 <= 4294967295 ->
  getr Rc (reg 24) = Z_to_bv 64 (if last then 1 else 2) -> getr Rc (reg 26) = Z_to_bv 64 2147450880 ->
  aobj FF to 32 -> shadow_zero Mc to 4 -> L5.u64_at RSEGS Mc (to + k) tw -> 0 <= tw < 2 ^ 64 ->
  aobj FF qo 32 -> shadow_zero Mc qo 4 -> (to + 32 <= qo \/ qo + 32 <= to) -> L5.u64_at RSEGS Mc (E - 248) qo ->
  (forall a, qo + 16 <= a < qo + 32 -> ~ L5.outside W a) ->
  (forall (fx1 : FPState) R1 M1 model1,
      binv W BX M1 model1 LKc crc Ac -> (forall x, In x (if last then KS_v5HLb else KS_v5HLa) -> getr R1 (reg x) = getr Rc (reg x)) ->
      (if last then getr R1 (reg 1) = Z_to_bv 64 0x92b70 /\ getr R1 (reg 10) = Z_to_bv 64 qo
       else getr R1 (reg 10) = Z_to_bv 64 (to + 16) /\ getr R1 (reg 11) = Z_to_bv 64 (qo + 16) /\ getr R1 (reg 12) = Z_to_bv 64 (qo + 16) /\ getr R1 (reg 21) = Z_to_bv 64 (to + 16)
            /\ getr R1 (reg 24) = Z_to_bv 64 1) ->
      (forall a, 0 <= a < 2 ^ 64 -> ~ (qo + k <= a < qo + k + 8) -> M1 (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)) -> L5.defined M1 (qo + k) 8 ->
      srealizes RSEGS SCFG (cfg (fx:=fx1) R1 (if last then L5ARED.REDUCE else 0x92aec) M1 model1) K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc 0x92aec Mc modelc) K.
Proof.
  intros k BI RI X10 X11 X12 X21 X22 X23 DR X24 X26 AOT SZT TW TWR AOQ SZQ APT S104 WRO KF. open_ctx BI. pose proof RI as (X2 & X8 & X9 & X3 & X4).
  pose proof (arg_facts L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G W _ Mc modelc LKc crc Ac to BI AOT SZT)
    as ((TRP & TRG & T8) & TBIG & TZv & TWv & TFR & TF & TSH & STF & STSH & STFR & TXB & TXC & TCL).
  pose proof (arg_facts L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G W _ Mc modelc LKc crc Ac qo BI AOQ SZQ)
    as ((ORP & ORG & O8) & OBIG & OZv & OWv & OFR & OF & OSH & SOF & SOSH & SOFR & XB & XC & OCL).
  set (MV := mrestrict (ahid Ac modelc) Mc) in *.
  assert (ALT : aligned to 8) by exact T8. assert (ALO : aligned qo 8) by exact O8.
  assert (S104v : L5.u64_at RSEGS MV (E - 248) qo).
  { apply (proj2 (u64_at_vis _ Mc (E - 248) _ ltac:(eapply avis_sub; [exact SV | clear; lia | clear; lia]) ltac:(clear - ER; lia) ltac:(clear - ER; lia))). exact S104. }
  assert (HVD : 0 <= d0 < 2 ^ 64) by (clear - DR; lia). assert (HVW : 0 <= tw <= 18446744073709551615) by (clear - TWR; lia).
  set (Wp := fun a => qo + k <= a < qo + k + 8).
  assert (WPOK : forall a, 0 <= a < 2 ^ 64 -> Wp a -> L5DKA.wp_ok L ar LB FF E SCRD SPA (docell E) F 3 W BX a).
  { intros a Ha Wa. subst Wp; cbn beta in Wa. assert (KR : k = 16 \/ k = 24) by (subst k; destruct last; [left|right]; reflexivity).
    destruct (OCL a ltac:(clear - Wa KR; lia)) as (C1 & C2 & C3 & C4). split. exact C4. split. split. exact C1. exact C2. intros _. apply WRO. clear - Wa KR; lia. }
  assert (FIN : forall (fx1 : FPState) R1 M1v pcx, msteps RSEGS (st fx Rc 0x92aec MV) (st fx1 R1 pcx M1v) -> mem_grows MV M1v ->
            (forall a, 0 <= a < 2 ^ 64 -> ~ Wp a -> M1v (Z_to_bv 64 a) = MV (Z_to_bv 64 a)) -> pcx = (if last then L5ARED.REDUCE else 0x92aec) ->
            (forall M1 model1, binv W BX M1 model1 LKc crc Ac -> (forall a, 0 <= a < 2 ^ 64 -> ~ (qo + k <= a < qo + k + 8) -> M1 (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)) -> L5.defined M1 (qo + k) 8 ->
                srealizes RSEGS SCFG (cfg (fx:=fx1) R1 pcx M1 model1) K) ->
            srealizes RSEGS SCFG (cfg (fx:=fx) Rc 0x92aec Mc modelc) K).
  { intros fx1 R1 M1v pcx pMS MG1 pFZ EPC KF1.
    apply (L5DKA.bstage L ar C HI LY HIok M model LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2 G W _ Mc modelc LKc crc Ac fx fx1 Rc 0x92aec R1 pcx M1v Wp K BI pMS MG1 pFZ WPOK).
    intros M1 model1 BI1 AH1 VIS1 MGM1 FRM1. apply (KF1 M1 model1 BI1).
    - intros a Ha N1. apply FRM1. exact Ha. exact N1.
    - eapply L5.defined_grows. exact MGM1. assert (KR : k = 16 \/ k = 24) by (subst k; destruct last; [left|right]; reflexivity).
      pose proof (aobj_facts L ar C HI LY HIok (BX ++ LB) FF' LKc crc Ac Mc modelc qo 32 0 0 (proj1 BI) (aobj_cons _ _ _ _ AOQ) ltac:(clear; lia) ltac:(reflexivity)) as (_ & _ & ODEF & _).
      eapply L5.defined_sub. exact ODEF. clear - KR; lia. clear - KR; lia. }
  assert (HV22 : 0 <= U Rc 22 <= 18446744073709551615) by (pose proof (UR Rc 22) as X; clear - X; lia).
  destruct last; subst k; cbn iota in *.
  - pose proof (v5HLb_conc fx Rc MV (fun j => match j with 2%nat => E | 33%nat => to | 35%nat => qo | 40%nat => F | 41%nat => fl | 58%nat => U Rc 1 | 68%nat => d0 | 70%nat => tw | 71%nat => U Rc 22 | _ => 0 end)) as P. cbn beta iota in P.
    feed P ltac:(first [apply UR | apply U_to | sc | (apply TXC; [clear; lia | clear; lia | sc]) ]).
    destruct P as (fx1 & R1 & M1v & MG1 & pFR & pFZ & (pMS & pKS & pR1 & pR10 & _)).
    apply (FIN fx1 R1 M1v L5ARED.REDUCE pMS MG1). { intros a Ha Hn. apply pFZ. exact Ha. subst Wp; cbn beta in Hn. clear - Hn; lia. } reflexivity.
    intros M1 model1 BI1 AG1 DF1. apply (KF fx1 R1 M1 model1 BI1 pKS). split. exact pR1. exact pR10. exact AG1. exact DF1.
  - pose proof (v5HLa_conc fx Rc MV (fun j => match j with 2%nat => E | 33%nat => to | 35%nat => qo | 40%nat => F | 41%nat => fl | 58%nat => U Rc 1 | 68%nat => d0 | 70%nat => tw | _ => 0 end)) as P. cbn beta iota in P.
    feed P ltac:(first [apply UR | apply U_to | sc | (apply TXC; [clear; lia | clear; lia | sc]) ]).
    destruct P as (fx1 & R1 & M1v & MG1 & pFR & pFZ & (pMS & pKS & pR10 & pR11 & pR12 & _ & pR21 & pR24)).
    apply (FIN fx1 R1 M1v 0x92aec pMS MG1). { intros a Ha Hn. apply pFZ. exact Ha. subst Wp; cbn beta in Hn. clear - Hn; lia. } reflexivity.
    intros M1 model1 BI1 AG1 DF1. apply (KF fx1 R1 M1 model1 BI1 pKS). split. exact pR10. split. exact pR11. split. exact pR12. split. exact pR21. exact pR24. exact AG1. exact DF1.
Qed.

End DIV.
End WithIface.
End SCFG_1.
End L5ADVHL.
