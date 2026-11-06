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
     L5Cmp L5CoreA L5CoreSpecsA L5StepA L5CoreB L5ADetailH L5AFrameK L5DivKitA L5ADivH L5ADivT L5ADivD L5ADivPH L5ADivE L5ADivEA L5ADivHC L5ADivHD L5ADivHA.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5ADVHN.
Import L5A. Import L5CA. Import L5CSA. Import L5SA. Import L5CB. Import L5ADH. Import L5ADVH. Import L5ADVT. Import L5ADVD. Import L5ADVE. Import L5ADVEA. Import L5ADVHC. Import L5ADVHD. Import L5ADVHA. Import L5ADIVPH.
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
Definition KSP4 : list nat := [2; 3; 4; 8; 9; 18; 19; 20; 23; 25; 26]%nat.
Lemma p4n (fx : FPState) Rc Mc modelc W BX LKc crc Ac c to qo qn lend (bn bt : L5.bigobj) (toHT : bool) :
  binv W BX Mc modelc LKc crc Ac -> rinvD R E Rc -> getr Rc (reg 27) = Z_to_bv 64 F ->
  getr Rc (reg 10) = Z_to_bv 64 c -> 0 <= c <= 1 -> getr Rc (reg 19) = Z_to_bv 64 (to / 8 + 2147450880) -> getr Rc (reg 20) = Z_to_bv 64 lend ->
  getr Rc (reg 22) = Z_to_bv 64 qn -> 0 <= qn <= 1 -> getr Rc (reg 24) = Z_to_bv 64 (F + 96) ->
  L5.u64_at RSEGS Mc (E - 248) qo -> L5.u64_at RSEGS Mc (E - 208) to -> 0 <= qo < 2 ^ 64 ->
  L5.big_at RSEGS Mc (F + 96) bn -> L5.big_at RSEGS Mc to bt -> aobj FF to 32 -> shadow_zero Mc to 4 -> L5.bo_dyn bn = L5.bo_dyn bt ->
  (if toHT then lend = 1 /\ (2 <= L5.bo_len bn)%nat else 2 <= lend < 2 ^ 64) ->
  (forall (fx1 : FPState) R1 M1 model1,
      binv W BX M1 model1 LKc crc Ac -> (forall x, In x KSP4 -> getr R1 (reg x) = getr Rc (reg x)) ->
      getr R1 (reg 10) = Z_to_bv 64 (to + 8) -> getr R1 (reg 11) = Z_to_bv 64 (Z.of_nat (L5.bo_len bn)) -> getr R1 (reg 21) = Z_to_bv 64 (L5.bo_data to bt) ->
      getr R1 (reg 22) = Z_to_bv 64 qo -> getr R1 (reg 24) = Z_to_bv 64 to -> getr R1 (reg 27) = Z_to_bv 64 (L5.bo_data (F + 96) bn) ->
      (forall a, 0 <= a < 2 ^ 64 -> ~ (E - 272 <= a < E - 264) -> ~ (E - 312 <= a < E - 304) -> ~ (E - 296 <= a < E - 288) -> M1 (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)) ->
      L5.u64_at RSEGS M1 (E - 272) (F + 96) -> L5.u64_at RSEGS M1 (E - 312) qn -> L5.u64_at RSEGS M1 (E - 296) F ->
      srealizes RSEGS SCFG (cfg (fx:=fx1) R1 (if toHT then 0x9267c else 0x926d8) M1 model1) K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc 0x92374 Mc modelc) K.
Proof.
  intros BI RI X27 X10 CR X19 X20 X22 QNR X24 S104 S144 QOR OBN OBT AOT SZT DYE DISP KF. open_ctx BI. pose proof RI as (X2 & X8 & X9 & X3 & X4).
  pose proof (arg_facts L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G W _ Mc modelc LKc crc Ac to BI AOT SZT)
    as ((ORP & ORG & O8) & OBIG & OZv & OWv & OFR & OF & OSH & SOF & SOSH & SOFR & XB & XC & OCL).
  set (MV := mrestrict (ahid Ac modelc) Mc) in *.
  destruct OWNv as (_ & _ & _ & OW112 & OW152 & _).
  assert (ALO : aligned to 8) by exact O8.
  assert (FCELL : forall a v, F <= a -> a + 8 <= F + 512 -> L5.u64_at RSEGS Mc a v -> L5.u64_at RSEGS MV a v).
  { intros a v H1 H2 Hc. apply (proj2 (u64_at_vis (ahid Ac modelc) Mc a v ltac:(eapply avis_sub; [exact FV | clear - H1; lia | clear - H2; lia]) ltac:(clear - H1 FRP; lia) ltac:(clear - H2 FRP; lia))). exact Hc. }
  assert (SCELL : forall a v, SPA <= a -> a + 8 <= E -> L5.u64_at RSEGS Mc a v -> L5.u64_at RSEGS MV a v).
  { intros a v H1 H2 Hc. apply (proj2 (u64_at_vis (ahid Ac modelc) Mc a v ltac:(eapply avis_sub; [exact SV | clear - H1; lia | clear - H2; lia]) ltac:(clear - H1 ER; lia) ltac:(clear - H2 ER; lia))). exact Hc. }
  assert (S104v : L5.u64_at RSEGS MV (E - 248) qo) by (apply SCELL; [clear; lia | clear; lia | exact S104]).
  assert (S144v : L5.u64_at RSEGS MV (E - 208) to) by (apply SCELL; [clear; lia | clear; lia | exact S144]).
  destruct bn as [fn lenn stn]. destruct OBN as (N0 & FNR & N8 & NST). destruct bt as [ft lent stt]. destruct OBT as (T0 & FTR & T8 & TST).
  unfold L5.bo_dyn in DYE. cbn [L5.bo_fb L5.bo_len L5.bo_st L5.bo_data] in *.
  assert (N0v : L5.u8_at RSEGS MV (F + 96) fn).
  { apply (proj2 (u8_at_vis (ahid Ac modelc) Mc (F + 96) fn ltac:(eapply avis_sub; [exact FV | clear; lia | clear; lia]) ltac:(clear - FRP; lia) ltac:(clear - FRP; lia))). exact N0. }
  assert (N8v : L5.u64_at RSEGS MV (F + 104) (Z.of_nat lenn)) by (apply FCELL; [clear; lia | clear; lia | replace (F + 104) with (F + 96 + 8) by (clear; lia); exact N8]).
  assert (T0v : L5.u8_at RSEGS MV to ft) by (apply XB; exact T0).
  assert (HVN : 0 <= fn <= 255 /\ 0 <= fn < 2 ^ 64) by (clear - FNR; lia). destruct HVN as [HVN HVN'].
  assert (HVT : 0 <= ft <= 255 /\ 0 <= ft < 2 ^ 64) by (clear - FTR; lia). destruct HVT as [HVT HVT'].
  assert (HVQ : 0 <= qo <= 18446744073709551615) by (clear - QOR; lia).
  assert (HVC : 0 <= c < 2 ^ 64) by (clear - CR; lia). assert (HVQN : 0 <= qn < 2 ^ 64) by (clear - QNR; lia).
  set (Wp := fun a => (E - 272 <= a < E - 264) \/ (E - 312 <= a < E - 304) \/ (E - 296 <= a < E - 288)).
  assert (WPOK : forall a, 0 <= a < 2 ^ 64 -> Wp a -> L5DKA.wp_ok L ar LB FF E SCRD SPA (docell E) F 3 W BX a).
  { intros a Ha Wa. subst Wp; cbn beta in Wa.
    apply (L5DKA.wp_frame L ar HI LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2 G); [clear - Wa; lia | unfold docell; clear - Wa; lia]. }
  assert (FIN : forall (fx1 : FPState) R1 M1v (KS : list nat) pcx nd td, forallb (fun i => existsb (Nat.eqb i) KS) KSP4 = true ->
            msteps RSEGS (st fx Rc 0x92374 MV) (st fx1 R1 pcx M1v) -> mem_grows MV M1v ->
            (forall a, 0 <= a < 2 ^ 64 -> ~ Wp a -> M1v (Z_to_bv 64 a) = MV (Z_to_bv 64 a)) ->
            (forall x, In x KS -> getr R1 (reg x) = getr Rc (reg x)) ->
            getr R1 (reg 10) = Z_to_bv 64 (to + 8) -> getr R1 (reg 11) = Z_to_bv 64 (Z.of_nat lenn) -> getr R1 (reg 21) = Z_to_bv 64 td ->
            getr R1 (reg 22) = Z_to_bv 64 qo -> getr R1 (reg 24) = Z_to_bv 64 to -> getr R1 (reg 27) = Z_to_bv 64 nd ->
            L5.u64_at RSEGS M1v (E - 296) F -> L5.u64_at RSEGS M1v (E - 312) qn -> L5.u64_at RSEGS M1v (E - 272) (F + 96) ->
            pcx = (if toHT then 0x9267c else 0x926d8) -> nd = match stn with L5.BInl _ _ => F + 96 + 16 | L5.BDyn _ q => q end -> td = match stt with L5.BInl _ _ => to + 16 | L5.BDyn _ q => q end ->
            srealizes RSEGS SCFG (cfg (fx:=fx) Rc 0x92374 Mc modelc) K).
  { intros fx1 R1 M1v KS pcx nd td KSB pMS MG1 pFZ pKS pR10 pR11 pR21 pR22 pR24 pR27 pS56 pS40 pS80 EPC END ETD. subst pcx nd td.
    apply (L5DKA.bstage L ar C HI LY HIok M model LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2 G W _ Mc modelc LKc crc Ac fx fx1 Rc 0x92374 R1 _ M1v Wp K BI pMS MG1 pFZ WPOK).
    intros M1 model1 BI1 AH1 VIS1 MGM1 FRM1.
    assert (SPV : forall a v, SPA <= a -> a + 8 <= E -> L5.u64_at RSEGS M1v a v -> L5.u64_at RSEGS M1 a v).
    { intros a v H1 H2 Hc. apply (proj1 (u64_at_vis (ahid Ac modelc) M1 a v ltac:(eapply avis_sub; [exact SV | clear - H1; lia | clear - H2; lia]) ltac:(clear - H1 ER; lia) ltac:(clear - H2 ER; lia))). rewrite VIS1. exact Hc. }
    apply (KF fx1 R1 M1 model1 BI1).
    - intros x Hx. apply pKS. revert Hx. apply (L5K.incl_b KSP4). exact KSB.
    - exact pR10.
    - exact pR11.
    - exact pR21.
    - exact pR22.
    - exact pR24.
    - exact pR27.
    - intros a Ha N1 N2 N3. apply FRM1. exact Ha. subst Wp; cbn beta. clear - N1 N2 N3. lia.
    - apply SPV. clear; lia. clear; lia. exact pS80.
    - apply SPV. clear; lia. clear; lia. exact pS40.
    - apply SPV. clear; lia. clear; lia. exact pS56. }
  destruct stn as [n0 n1|capn qd]; destruct stt as [t0 t1|capt qt].
  - (* [comment removed for export] *)
    destruct NST as (NBT & _ & _ & NL2 & _). destruct TST as (TBT & _).
    assert (HVL : 0 <= Z.of_nat lenn <= 18446744073709551615 /\ 0 <= Z.of_nat lenn < 2 ^ 64) by (clear - NL2; lia). destruct HVL as [HVL HVL'].
    destruct toHT.
    + destruct DISP as (L1 & LN2). subst lend.
      pose proof (v5P4hi_conc fx Rc MV (fun j => match j with 2%nat => E | 33%nat => to | 35%nat => qo | 40%nat => F | 41%nat => fl | 56%nat => ft | 57%nat => qn | 58%nat => U Rc 1 | 60%nat => fn | 64%nat => c | 65%nat => Z.of_nat lenn | _ => 0 end)) as P. cbn beta iota in P.
      feed P ltac:(first [apply UR | apply U_to | sc ]).
      destruct P as (fx1 & R1 & M1v & MG1 & pFR & pFZ & (pMS & pKS & pR10 & pR11 & pR12 & pR13 & pR21 & pR22 & pR24 & pR27 & pS56 & pS40 & pS80)).
      apply (FIN fx1 R1 M1v KS_v5P4hi 0x9267c (F + 112) (to + 16) ltac:(vm_compute; reflexivity) pMS MG1).
      { intros a Ha Hn. apply pFZ. exact Ha. all: subst Wp; cbn beta in Hn; clear - Hn; lia. }
      all: try assumption. all: try reflexivity. all: clear; lia.
    + pose proof (v5P4gi_conc fx Rc MV (fun j => match j with 2%nat => E | 33%nat => to | 35%nat => qo | 40%nat => F | 41%nat => fl | 56%nat => ft | 57%nat => qn | 58%nat => U Rc 1 | 60%nat => fn | 63%nat => lend | 64%nat => c | 65%nat => Z.of_nat lenn | _ => 0 end)) as P. cbn beta iota in P.
      feed P ltac:(first [apply UR | apply U_to | sc ]).
      destruct P as (fx1 & R1 & M1v & MG1 & pFR & pFZ & (pMS & pKS & pR10 & pR11 & pR12 & pR13 & pR21 & pR22 & pR24 & pR27 & pS56 & pS40 & pS80)).
      apply (FIN fx1 R1 M1v KS_v5P4gi 0x926d8 (F + 112) (to + 16) ltac:(vm_compute; reflexivity) pMS MG1).
      { intros a Ha Hn. apply pFZ. exact Ha. all: subst Wp; cbn beta in Hn; clear - Hn; lia. }
      all: try assumption. all: try reflexivity. all: clear; lia.
  - exfalso. destruct NST as (NBT & _). destruct TST as (TBT & _). rewrite NBT, TBT in DYE. discriminate DYE.
  - exfalso. destruct NST as (NBT & _). destruct TST as (TBT & _). rewrite NBT, TBT in DYE. discriminate DYE.
  - (* [comment removed for export] *)
    destruct NST as (NBT & N16 & N24 & NLC & NCR & _ & NQ4096 & NQ47 & _). destruct TST as (TBT & T16 & T24 & TLC & TCR & _ & TQ4096 & TQ47 & _).
    assert (HVL : 0 <= Z.of_nat lenn <= 18446744073709551615 /\ 0 <= Z.of_nat lenn < 2 ^ 64) by (clear - NLC NCR; lia). destruct HVL as [HVL HVL'].
    assert (N16v : L5.u64_at RSEGS MV (F + 112) capn) by (apply FCELL; [clear; lia | clear; lia | replace (F + 112) with (F + 96 + 16) by (clear; lia); exact N16]).
    assert (N24v : L5.u64_at RSEGS MV (F + 120) qd) by (apply FCELL; [clear; lia | clear; lia | replace (F + 120) with (F + 96 + 24) by (clear; lia); exact N24]).
    assert (T24v : L5.u64_at RSEGS MV (to + 24) qt) by (apply XC; [clear; lia | clear; lia | exact T24]).
    assert (HVQD : 4096 <= qd <= 140737488355328 /\ 0 <= qd < 2 ^ 64) by (clear - NQ4096 NQ47 NCR; lia). destruct HVQD as [HVQD HVQD'].
    assert (HVQT : 4096 <= qt <= 140737488355328 /\ 0 <= qt < 2 ^ 64) by (clear - TQ4096 TQ47 TCR; lia). destruct HVQT as [HVQT HVQT'].
    assert (HVCN : 1 <= capn <= 134217728 /\ 0 <= capn < 2 ^ 64) by (clear - NCR; lia). destruct HVCN as [HVCN HVCN'].
    destruct toHT.
    + destruct DISP as (L1 & LN2). subst lend.
      pose proof (v5P4hd_conc fx Rc MV (fun j => match j with 2%nat => E | 33%nat => to | 35%nat => qo | 40%nat => F | 41%nat => fl | 56%nat => ft | 57%nat => qn | 58%nat => U Rc 1 | 60%nat => fn | 61%nat => qd | 62%nat => capn | 64%nat => c | 65%nat => Z.of_nat lenn | 66%nat => qt | _ => 0 end)) as P. cbn beta iota in P.
      feed P ltac:(first [apply UR | apply U_to | sc ]).
      destruct P as (fx1 & R1 & M1v & MG1 & pFR & pFZ & (pMS & pKS & pR10 & pR11 & pR12 & pR13 & pR21 & pR22 & pR24 & pR27 & pS56 & pS40 & pS80)).
      apply (FIN fx1 R1 M1v KS_v5P4hd 0x9267c qd qt ltac:(vm_compute; reflexivity) pMS MG1).
      { intros a Ha Hn. apply pFZ. exact Ha. all: subst Wp; cbn beta in Hn; clear - Hn; lia. }
      all: try assumption. all: try reflexivity. all: clear; lia.
    + pose proof (v5P4gd_conc fx Rc MV (fun j => match j with 2%nat => E | 33%nat => to | 35%nat => qo | 40%nat => F | 41%nat => fl | 56%nat => ft | 57%nat => qn | 58%nat => U Rc 1 | 60%nat => fn | 61%nat => qd | 62%nat => capn | 63%nat => lend | 64%nat => c | 65%nat => Z.of_nat lenn | 66%nat => qt | _ => 0 end)) as P. cbn beta iota in P.
      feed P ltac:(first [apply UR | apply U_to | sc ]).
      destruct P as (fx1 & R1 & M1v & MG1 & pFR & pFZ & (pMS & pKS & pR10 & pR11 & pR12 & pR13 & pR21 & pR22 & pR24 & pR27 & pS56 & pS40 & pS80)).
      apply (FIN fx1 R1 M1v KS_v5P4gd 0x926d8 qd qt ltac:(vm_compute; reflexivity) pMS MG1).
      { intros a Ha Hn. apply pFZ. exact Ha. all: subst Wp; cbn beta in Hn; clear - Hn; lia. }
      all: try assumption. all: try reflexivity. all: clear; lia.
Qed.

End DIV.
End WithIface.
End SCFG_1.
End L5ADVHN.
