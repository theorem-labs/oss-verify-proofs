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
     L5Cmp L5CoreA L5CoreSpecsA L5StepA L5CoreB L5ACopy L5ACmp L5ADetailH L5AFrameK L5DivKitA L5ADivH L5ADivT L5ADivD L5ADivPE L5ADivP2 L5ADivE L5ADivEA.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5ADVHC.
Import L5A. Import L5CA. Import L5CSA. Import L5SA. Import L5CB. Import L5ADH. Import L5ADVH. Import L5ADVT. Import L5ADVD. Import L5ADVE. Import L5ADVEA. Import L5ADIVP2.
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
Hypothesis Hcpa : copya_spec L ar HI.

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
Local Notation binv := (L5AFK.binv L ar HI M model LB FF LK A E SCRD SPA (down E F ro R) F 3).
Local Notation FF' := ((F, 3, SPA + 32) :: FF).
Local Notation SH := (F / 8 + 2147450880).
Local Notation tob := (L5ADVEA.tob).

Lemma copy_stage (fx : FPState) Rc Mc modelc W BX LKc crc Ac k o' pcn fbo b' ws' :
  binv W BX Mc modelc LKc crc Ac -> rinvD R E Rc ->
  getr Rc (reg 10) = Z_to_bv 64 (F + k) -> getr Rc (reg 11) = Z_to_bv 64 o' -> getr Rc (reg 1) = Z_to_bv 64 pcn -> L5.ra_ok pcn ->
  32 <= k -> k + 32 <= 504 -> k mod 8 = 0 ->
  L5.u8_at RSEGS Mc (F + k) fbo -> 0 <= fbo < 256 -> shadow_zero Mc (F + k) 4 ->
  tob (BX ++ LB) Mc o' b' ws' -> aobj FF' o' 32 -> (F + k + 32 <= o' \/ o' + 32 <= F + k) ->
  (L5.bo_dyn b' = true -> 8 * L5.bo_cap b' <= 2 ^ 27 /\ acredit_ok L crc (8 * L5.bo_cap b')) ->
  (forall (fx' : FPState) R' M' model' (g : growth) LBn cr' LK' A',
      copy_post L ar (BX ++ LB) FF' LK' crc Mc M' Rc R' (F + k) o' SPA fbo b' ws' g LBn cr' ->
      binv W (match g with Same => BX | Grown q cap => (q, 8 * cap) :: BX end) M' model' LK' cr' A' ->
      incl Ac A' -> incl LK' LKc ->
      srealizes RSEGS SCFG (cfg (fx:=fx') R' pcn M' model') K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc COPYA Mc modelc) K.
Proof.
  intros BI RI X10 X11 X1 RAn K1 K2 K8 DFB FBR DSZ (OB' & OL' & SZ' & INB') AOB' AP CAP KF.
  pose proof BI as (B1 & B2 & B3 & B4 & B5 & B6 & _).
  edestruct L5ADVEA.callee_pre with (SCRc := COPY_SCR) as (STKc & ROOMc & RSc & A32c); [exact HIok | exact EA | exact FFR1 | exact FFRS | exact BI | vm_compute; discriminate | clear - HSCR; change COPY_SCR with 4256; lia | ].
  pose proof (NUM L ar HI R LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER) as ((FRG & FLRG & ERG) & FRP & FLRP & ALF & FBIG & FLBIG & FLA & SFA & SFLA & SFB).
  assert (OCR : forall a, docell E a -> SPA <= a < E). { destruct G as [_ _ _ _ _ OCR0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _]. exact OCR0. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (SHB : 0 <= F / 8 /\ F / 8 + 64 <= 17592186044416) by (clear - FRP; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  pose proof RI as (Z2 & _ & _ & _ & Z4).
  assert (WAV : forall rr a, In rr [(F + k, 32)] -> L5.in_rng rr a -> ~ docell E a /\ ~ (F / 8 + SB <= a < F / 8 + SB + ff_bytes 3 / 8)).
  { intros rr a [Hr|[]] IR; subst rr; unfold L5.in_rng in IR; cbn [fst snd] in IR. split. intros D. pose proof (OCR a D) as X. clear - X IR SFB K1 K2; lia.
    change (ff_bytes 3 / 8) with 64. unfold SB. clear - IR K1 K2 SHB FBIG FRP. lia. }
  assert (WOUT : forall a, aclient L ar LB FF E SCRD a -> L5.outside W a -> L5.outside [(F + k, 32)] a).
  { intros a Hc _ rr [Hr|[]] IR. subst rr. unfold L5.in_rng in IR; cbn [fst snd] in IR.
    destruct G as [_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ NCF _]. apply (NCF a). left. change (ff_bytes 3) with 512. clear - IR K1 K2; lia. exact Hc. }
  apply (Hcpa fx Rc Mc modelc K (BX ++ LB) FF' LKc crc Ac (F + k) o' SPA pcn fbo b' ws' B1 B2 HK).
  - rewrite r10. exact X10.
  - rewrite r11. exact X11.
  - exact CAP.
  - rewrite r1. exact X1.
  - exact RAn.
  - rewrite r2. exact Z2.
  - exact A32c.
  - rewrite r4, Z4. rewrite <- G4. reflexivity.
  - exact STKc.
  - apply (ffrk_le 1 FF' LKc 4 2 ROOMc). clear; lia.
  - exact RSc.
  - exact DFB.
  - exact FBR.
  - eapply L5ADVEA.loc_aobj; [exact G | exact K1 | exact K2 | exact K8].
  - exact DSZ.
  - exact OB'.
  - exact OL'.
  - exact AOB'.
  - exact SZ'.
  - exact INB'.
  - exact AP.
  - intros fx3 R3 M3 model3 g LBn cr3 LK3 A3 POST RT3 IA3 AM3 ILK3 HH3.
    assert (BI3 : binv W (match g with Same => BX | Grown q cap => (q, 8 * cap) :: BX end) M3 model3 LK3 cr3 A3).
    { pose proof POST as (_ & PG). destruct g as [|qn capn].
      - destruct PG as (_ & ELB & _ & _ & AH3). subst LBn.
        apply (L5AFK.binv_callee L ar C HI HIok M model LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2 G
                 W W BX BX BX Mc modelc LKc crc Ac M3 model3 LK3 cr3 A3 COPY_SCR _ BI AH3 HH3 AM3 RT3 IA3 ILK3).
        + vm_compute; discriminate.
        + clear - HSCR; change COPY_SCR with 4256; lia.
        + exact WAV.
        + exact WOUT.
        + intros a X. exact X.
      - destruct PG as (_ & _ & ELB & _ & _ & _ & _ & AH3). subst LBn.
        apply (L5AFK.binv_callee L ar C HI HIok M model LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2 G
                 W W BX BX ((qn, 8 * capn) :: BX) Mc modelc LKc crc Ac M3 model3 LK3 cr3 A3 COPY_SCR _ BI AH3 HH3 AM3 RT3 IA3 ILK3).
        + vm_compute; discriminate.
        + clear - HSCR; change COPY_SCR with 4256; lia.
        + exact WAV.
        + exact WOUT.
        + intros a X. exact X. }
    apply (KF fx3 R3 M3 model3 g LBn cr3 LK3 A3 POST BI3 IA3 ILK3).
Qed.

(* [comment removed for export] *)
Definition rinvH (Rc : bvmap 5 word) : Prop :=
  rinvD R E Rc /\ getr Rc (reg 18) = Z_to_bv 64 SH /\ getr Rc (reg 23) = Z_to_bv 64 (F + 32) /\ getr Rc (reg 27) = Z_to_bv 64 F /\ getr Rc (reg 25) = getr R (reg 25).
Definition HIDX : list nat := [2; 3; 4; 8; 9; 18; 23; 25; 27]%nat.
Lemma rinvH_keep Ra Rb : rinvH Ra -> (forall k, In k HIDX -> getr Rb (reg k) = getr Ra (reg k)) -> rinvH Rb.
Proof.
  intros (RD & X18 & X23 & X27 & X25) Kp. unfold rinvH. split. { apply (rinvD_keep R E Ra Rb RD). intros k Hk. apply Kp. unfold DIDX in Hk. unfold HIDX. cbn [In] in Hk |- *. clear - Hk. tauto. }
  rewrite (Kp 18%nat), (Kp 23%nat), (Kp 27%nat), (Kp 25%nat) by (unfold HIDX; cbn [In]; tauto). repeat split; assumption.
Qed.
Lemma rinvH_ks Ra Rb (KS : list nat) : rinvH Ra -> (forall x, In x KS -> getr Rb (reg x) = getr Ra (reg x)) ->
  forallb (fun i => existsb (Nat.eqb i) KS) HIDX = true -> rinvH Rb.
Proof. intros RI Kp HB. apply (rinvH_keep Ra Rb RI). intros k Hk. apply Kp. exact (L5K.incl_b HIDX KS HB k Hk). Qed.
Lemma rinvH_pres Ra Rb : rinvH Ra -> regs_preserved Ra Rb -> rinvH Rb.
Proof. intros RI RP. apply (rinvH_keep Ra Rb RI). intros k Hk. apply (cs_of_preserved Ra Rb k RP). revert Hk. apply (L5K.incl_b HIDX); vm_compute; reflexivity. Qed.

(* [comment removed for export] *)
Lemma p2 (fx : FPState) Rc Mc modelc W BX LKc crc Ac to qo rd bd ft :
  binv W BX Mc modelc LKc crc Ac -> rinvH Rc ->
  getr Rc (reg 19) = Z_to_bv 64 qo -> getr Rc (reg 20) = Z_to_bv 64 2147450880 -> getr Rc (reg 22) = Z_to_bv 64 rd -> getr Rc (reg 24) = Z_to_bv 64 to ->
  L5.big_at RSEGS Mc (F + 32) bd -> (1 <= L5.bo_len bd)%nat ->
  aobj FF to 32 -> shadow_zero Mc to 4 -> L5.u8_at RSEGS Mc to ft -> 0 <= ft < 256 -> 0 <= qo < 2 ^ 64 -> 0 <= rd < 2 ^ 64 ->
  (forall (fx1 : FPState) R1 M1 model1,
      binv W BX M1 model1 LKc crc Ac -> rinvH R1 ->
      getr R1 (reg 1) = Z_to_bv 64 0x9233c -> getr R1 (reg 10) = Z_to_bv 64 (F + 96) -> getr R1 (reg 11) = Z_to_bv 64 to -> getr R1 (reg 19) = Z_to_bv 64 (to / 8 + 2147450880) ->
      getr R1 (reg 20) = Z_to_bv 64 (Z.of_nat (L5.bo_len bd)) -> getr R1 (reg 21) = Z_to_bv 64 (L5.bo_fb bd) -> getr R1 (reg 22) = Z_to_bv 64 ft ->
      getr R1 (reg 24) = Z_to_bv 64 (F + 96) -> getr R1 (reg 26) = Z_to_bv 64 (L5.bo_data (F + 32) bd) ->
      (forall a, 0 <= a < 2 ^ 64 -> ~ (E - 304 <= a < E - 296) -> ~ (E - 264 <= a < E - 256) -> ~ (E - 248 <= a < E - 240) -> ~ (E - 208 <= a < E - 200) -> ~ (SH + 12 <= a < SH + 16) ->
                 M1 (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)) ->
      L5.u64_at RSEGS M1 (E - 264) (F + 32) -> L5.u64_at RSEGS M1 (E - 304) rd -> L5.u64_at RSEGS M1 (E - 248) qo -> L5.u64_at RSEGS M1 (E - 208) to ->
      shadow_zero M1 (F + 96) 4 ->
      srealizes RSEGS SCFG (cfg (fx:=fx1) R1 COPYA M1 model1) K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc 0x922cc Mc modelc) K.
Proof.
  intros BI RIH X19 X20 X22 X24 OD LD AOT SZT TFB FTR QOR RDR KF.
  pose proof RIH as (RI & X18 & X23 & X27 & X25).
  pose proof (pf_of_binv L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G W _ Mc modelc LKc crc Ac BI) as PF.
  destruct PF as (W352 & IMGC & CSB & CUAR & FDEFv & FWv & FSHWv & FLCv & FLWv).
  pose proof (NUM L ar HI R LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER) as ((FRG & FLRG & ERG) & FRP & FLRP & ALF & FBIG & FLBIG & FLA & SFA & SFLA & SFB).
  pose proof (arg_facts L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G W _ Mc modelc LKc crc Ac to BI AOT SZT)
    as ((ORP & ORG & O8) & OBIG & OZv & OWv & OFR & OF & OSH & SOF & SOSH & SOFR & XB & XC & OCL).
  destruct (L5AFK.vis_facts L ar C HI LY HIok M model LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2 G W _ Mc modelc LKc crc Ac BI) as (_ & OWNv & _ & (_ & _ & FV & SV & SHV)).
  change (ff_bytes 3) with 512 in FV. change (ff_bytes 3 / 8) with 64 in SHV.
  pose proof RI as (X2 & X8 & X9 & X3 & X4).
  set (MV := mrestrict (ahid Ac modelc) Mc) in *.
  destruct OWNv as (_ & _ & _ & OW112 & OW152 & _).
  assert (ALO : aligned to 8) by exact O8.
  assert (FCELL : forall a v, F <= a -> a + 8 <= F + 512 -> L5.u64_at RSEGS Mc a v -> L5.u64_at RSEGS MV a v).
  { intros a v H1 H2 Hc. apply (proj2 (u64_at_vis (ahid Ac modelc) Mc a v ltac:(eapply avis_sub; [exact FV | clear - H1; lia | clear - H2; lia]) ltac:(clear - H1 FRP; lia) ltac:(clear - H2 FRP; lia))). exact Hc. }
  destruct bd as [fd lend sto]. destruct OD as (D0 & FDR & D8 & DST). cbn [L5.bo_fb L5.bo_len L5.bo_st L5.bo_data] in *.
  assert (D0v : L5.u8_at RSEGS MV (F + 32) fd).
  { apply (proj2 (u8_at_vis (ahid Ac modelc) Mc (F + 32) fd ltac:(eapply avis_sub; [exact FV | clear; lia | clear; lia]) ltac:(clear - FRP; lia) ltac:(clear - FRP; lia))). exact D0. }
  assert (D8v : L5.u64_at RSEGS MV (F + 40) (Z.of_nat lend)) by (apply FCELL; [clear; lia | clear; lia | replace (F + 40) with (F + 32 + 8) by (clear; lia); exact D8]).
  assert (HVF : 0 <= fd <= 255 /\ 0 <= fd < 2 ^ 64) by (clear - FDR; lia). destruct HVF as [HVF HVF'].
  assert (HVT : 0 <= ft <= 255 /\ 0 <= ft < 2 ^ 64) by (clear - FTR; lia). destruct HVT as [HVT HVT'].
  assert (HVQ : 0 <= qo <= 18446744073709551615) by (clear - QOR; lia). assert (HVR : 0 <= rd <= 18446744073709551615) by (clear - RDR; lia).
  assert (SHW : forall j, 0 <= j < 4 -> avis (ahid Ac modelc) (F / 8 + 12 + SB + j) 1). { intros j Hj. eapply avis_sub. exact SHV. unfold SB; clear - Hj; lia. unfold SB; clear - Hj; lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (FSH12 : (F + 96) / 8 = F / 8 + 12 /\ 0 <= F / 8 /\ F / 8 + 64 <= 17592186044416) by (clear - FRP ALF; unfold aligned in ALF; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  set (Wp := fun a => (E - 304 <= a < E - 296) \/ (E - 264 <= a < E - 256) \/ (E - 248 <= a < E - 240) \/ (E - 208 <= a < E - 200) \/ (SH + 12 <= a < SH + 16)).
  assert (WPOK : forall a, 0 <= a < 2 ^ 64 -> Wp a -> L5DKA.wp_ok L ar LB FF E SCRD SPA (docell E) F 3 W BX a).
  { intros a Ha Wa. subst Wp; cbn beta in Wa. destruct Wa as [Wa|[Wa|[Wa|[Wa|Wa]]]].
    1,2,3,4: apply (L5DKA.wp_frame L ar HI LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2 G); [clear - Wa; lia | unfold docell; clear - Wa; lia].
    apply (L5DKA.wp_shadow L ar HI LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2 G). unfold SB. change (ff_bytes 3 / 8) with 64. clear - Wa. lia. }
  assert (FIN : forall (fx1 : FPState) R1 M1v (KS : list nat), forallb (fun i => existsb (Nat.eqb i) KS) HIDX = true ->
            msteps RSEGS (st fx Rc 0x922cc MV) (st fx1 R1 COPYA M1v) -> mem_grows MV M1v ->
            (forall a, 0 <= a < 2 ^ 64 -> ~ Wp a -> M1v (Z_to_bv 64 a) = MV (Z_to_bv 64 a)) ->
            (forall x, In x KS -> getr R1 (reg x) = getr Rc (reg x)) ->
            getr R1 (reg 1) = Z_to_bv 64 0x9233c -> getr R1 (reg 10) = Z_to_bv 64 (F + 96) -> getr R1 (reg 11) = Z_to_bv 64 to -> getr R1 (reg 19) = Z_to_bv 64 (to / 8 + 2147450880) ->
            getr R1 (reg 20) = Z_to_bv 64 (Z.of_nat lend) -> getr R1 (reg 21) = Z_to_bv 64 fd -> getr R1 (reg 22) = Z_to_bv 64 ft ->
            getr R1 (reg 24) = Z_to_bv 64 (F + 96) -> getr R1 (reg 26) = Z_to_bv 64 (match sto with L5.BInl _ _ => F + 32 + 16 | L5.BDyn _ q => q end) ->
            L5.u64_at RSEGS M1v (E - 264) (F + 32) -> L5.u64_at RSEGS M1v (E - 304) rd -> L5.u64_at RSEGS M1v (E - 248) qo -> L5.u64_at RSEGS M1v (E - 208) to ->
            (forall j, 0 <= j < 4 -> L5.u8_at RSEGS M1v (F / 8 + 12 + SB + j) 0) ->
            srealizes RSEGS SCFG (cfg (fx:=fx) Rc 0x922cc Mc modelc) K).
  { intros fx1 R1 M1v KS KSB pMS MG1 pFZ pKS pR1 pR10 pR11 pR19 pR20 pR21 pR22 pR24 pR26 pS88 pS48 pS104 pS144 pSH.
    apply (L5DKA.bstage L ar C HI LY HIok M model LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2 G W _ Mc modelc LKc crc Ac fx fx1 Rc 0x922cc R1 COPYA M1v Wp K BI pMS MG1 pFZ WPOK).
    intros M1 model1 BI1 AH1 VIS1 MGM1 FRM1.
    assert (SPV : forall a v, SPA <= a -> a + 8 <= E -> L5.u64_at RSEGS M1v a v -> L5.u64_at RSEGS M1 a v).
    { intros a v H1 H2 Hc. apply (proj1 (u64_at_vis (ahid Ac modelc) M1 a v ltac:(eapply avis_sub; [exact SV | clear - H1; lia | clear - H2; lia]) ltac:(clear - H1 ER; lia) ltac:(clear - H2 ER; lia))). rewrite VIS1. exact Hc. }
    apply (KF fx1 R1 M1 model1 BI1 (rinvH_ks Rc R1 KS RIH pKS KSB) pR1 pR10 pR11 pR19 pR20 pR21 pR22 pR24 pR26).
    - intros a Ha N1 N2 N3 N4 N5. apply FRM1. exact Ha. subst Wp; cbn beta. clear - N1 N2 N3 N4 N5. lia.
    - apply SPV. clear; lia. clear; lia. exact pS88.
    - apply SPV. clear; lia. clear; lia. exact pS48.
    - apply SPV. clear; lia. clear; lia. exact pS104.
    - apply SPV. clear; lia. clear; lia. exact pS144.
    - intros j Hj. unfold byte_at, S. rewrite (proj1 FSH12).
      apply (byte_of_u8 M1 _ 0). 2: right; clear - Hj FSH12; unfold SB; lia. 2: clear - Hj FSH12; unfold SB; lia.
      apply (proj1 (u8_at_vis (ahid Ac modelc) M1 (F / 8 + 12 + SB + j) 0 (SHW j Hj) ltac:(clear - Hj FSH12; unfold SB; lia) ltac:(clear - Hj FSH12; unfold SB; lia))). rewrite VIS1. exact (pSH j Hj). }
  destruct sto as [v0 v1|cap q].
  - destruct DST as (BT0 & _ & _ & L2 & _).
    assert (HVL : 1 <= Z.of_nat lend <= 18446744073709551615 /\ 0 <= Z.of_nat lend < 2 ^ 64) by (clear - LD L2; lia). destruct HVL as [HVL HVL'].
    pose proof (v5P2i_conc fx Rc MV (fun j => match j with 2%nat => E | 33%nat => to | 35%nat => qo | 37%nat => rd | 40%nat => F | 41%nat => fl | 55%nat => fd | 56%nat => ft | 58%nat => U Rc 1 | 63%nat => Z.of_nat lend | _ => 0 end)) as P. cbn beta iota in P.
    feed P ltac:(first [apply UR | apply U_to | sc | (apply XB; sc) ]).
    destruct P as (fx1 & R1 & M1v & MG1 & pFR & pFZ & (pMS & pKS & pR1 & pR10 & pR11 & pR12 & pR19 & pR20 & pR21 & pR22 & pR24 & pR26 & pS144 & pH3 & pH2 & pH1 & pH0 & pS104 & pS48 & pS88)).
    apply (FIN fx1 R1 M1v KS_v5P2i ltac:(vm_compute; reflexivity) pMS MG1).
    { intros a Ha Hn. apply pFZ. exact Ha. all: subst Wp; cbn beta in Hn; unfold SB in *; clear - Hn; lia. }
    all: try assumption.
    + replace (F + 32 + 16) with (F + 48) by (clear; lia). exact pR26.
    + intros j Hj. assert (J : j = 0 \/ j = 1 \/ j = 2 \/ j = 3) by (clear - Hj; lia). unfold SB. destruct J as [J|[J|[J|J]]]; subst j; gmem.
  - destruct DST as (BT1 & D16 & D24 & LC & CR & _ & Q4096 & Q47 & _).
    assert (HVL : 1 <= Z.of_nat lend <= 18446744073709551615 /\ 0 <= Z.of_nat lend < 2 ^ 64) by (clear - LD LC CR; lia). destruct HVL as [HVL HVL'].
    assert (HVQD : 0 <= q <= 18446744073709551615 /\ 0 <= q < 2 ^ 64) by (clear - Q4096 Q47 CR; lia). destruct HVQD as [HVQD HVQD'].
    assert (D24v : L5.u64_at RSEGS MV (F + 56) q) by (apply FCELL; [clear; lia | clear; lia | replace (F + 56) with (F + 32 + 24) by (clear; lia); exact D24]).
    pose proof (v5P2d_conc fx Rc MV (fun j => match j with 2%nat => E | 33%nat => to | 35%nat => qo | 37%nat => rd | 40%nat => F | 41%nat => fl | 55%nat => fd | 56%nat => ft | 58%nat => U Rc 1 | 61%nat => q | 63%nat => Z.of_nat lend | _ => 0 end)) as P. cbn beta iota in P.
    feed P ltac:(first [apply UR | apply U_to | sc | (apply XB; sc) ]).
    destruct P as (fx1 & R1 & M1v & MG1 & pFR & pFZ & (pMS & pKS & pR1 & pR10 & pR11 & pR12 & pR19 & pR20 & pR21 & pR22 & pR24 & pR26 & pS144 & pH3 & pH2 & pH1 & pH0 & pS104 & pS48 & pS88)).
    apply (FIN fx1 R1 M1v KS_v5P2d ltac:(vm_compute; reflexivity) pMS MG1).
    { intros a Ha Hn. apply pFZ. exact Ha. all: subst Wp; cbn beta in Hn; unfold SB in *; clear - Hn; lia. }
    all: try assumption.
    intros j Hj. assert (J : j = 0 \/ j = 1 \/ j = 2 \/ j = 3) by (clear - Hj; lia). unfold SB. destruct J as [J|[J|[J|J]]]; subst j; gmem.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition cmpreg (o : Z) (b : L5.bigobj) (a : Z) : Prop :=
  o + 1 <= a < o + 32 \/ o / 8 + SB <= a < o / 8 + SB + 4 \/ (exists cap q, L5.bo_st b = L5.BDyn cap q /\ (q <= a < q + 8 * cap \/ q / 8 + SB <= a < q / 8 + SB + cap)).
Lemma cmp_obj_mk W BX Mc modelc LKc crc Ac Mx o b ws fb' :
  binv W BX Mc modelc LKc crc Ac -> aobj FF' o 32 -> tob (BX ++ LB) Mc o b ws ->
  (forall a, cmpreg o b a -> Mx (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)) ->
  L5.u8_at RSEGS Mx o fb' -> 0 <= fb' < 256 -> Z.testbit fb' 0 = Z.testbit (L5.bo_fb b) 0 -> Z.testbit fb' 1 = false -> (1 <= L5.bo_len b <= 300)%nat ->
  L5ACMP.cmp_objA Mx SPA o (L5.BO fb' (L5.bo_len b) (L5.bo_st b)) /\ L5C.obj_limbs RSEGS Mx (L5.BO fb' (L5.bo_len b) (L5.bo_st b)) ws.
Proof.
  intros BI AOB (OB & OL & SZ & INB) AG U8 FBR BT0 BT1 LEN.
  pose proof BI as (B1 & _).
  pose proof (aobj_facts L ar C HI LY HIok (BX ++ LB) FF' LKc crc Ac Mc modelc o 32 0 0 B1 AOB ltac:(clear; lia) ltac:(reflexivity)) as (OR & OBIG & _).
  destruct G as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG' F32 FLA' FLR FLBIG' NCF NCS].
  assert (OB' : L5.big_at RSEGS Mx o (L5.BO fb' (L5.bo_len b) (L5.bo_st b))).
  { apply (L5ADVEA.big_at_fb Mc Mx o b fb' OB ltac:(clear - OR; lia) ltac:(clear - OR; lia)). 2: exact U8. 2: exact FBR. 2: exact BT0. intros i Hi. apply AG. left. exact Hi. }
  assert (ZO : L5KA.zeros_at Mx (o / 8 + SB) 4).
  { intros i Hi. rewrite AG. apply SZ. exact Hi. right; left. clear - Hi; lia. }
  destruct b as [fb len sto]. cbn [L5.bo_fb L5.bo_len L5.bo_st] in *.
  pose proof OB as (_ & _ & _ & DST). cbn [L5.bo_fb L5.bo_len L5.bo_st] in DST.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  destruct sto as [v0 v1|cap q].
  - split. 2:{ destruct OL as (OL1 & OL2 & OL3). split. exact OL1. split. exact OL2. exact OL3. }
    destruct DST as (_ & _ & _ & L2 & _).
    unfold L5ACMP.cmp_objA. cbn [L5.bo_fb L5.bo_len L5.bo_st L5.bo_data].
    split. exact OB'. split. exact BT1. split. clear - LEN; lia. split. clear - LEN; lia. split. clear - OR; lia. split. clear - OR; lia. split. exact OBIG.
    split. right. clear - OR SLO HSCR; lia. split. exact ZO.
    split. clear - OR L2; lia. split. clear - OR; lia. split. clear - OBIG L2; lia. split. right. clear - OR SLO HSCR L2; lia.
    intros i Hi. replace ((o + 16) / 8 + SB + i) with (o / 8 + SB + (2 + i)) by (clear - OR; lia). apply ZO. clear - Hi L2; lia.
  - destruct DST as (_ & _ & _ & LC & CR & Q8 & Q4096 & Q47 & _).
    pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ B1) as (WB & _).
    pose proof (WB _ (INB cap q eq_refl)) as ((_ & _ & _ & _ & X5 & (_ & X7 & _)) & _ & (SBK & _) & _). cbn [fst snd] in *. unfold BIGSHADOW_LO, BIGSHADOW_HI in X7.
    split. 2:{ destruct OL as (OL1 & OL2 & OL3). split. exact OL1. split. exact OL2. cbn [L5.bo_st] in *.
               eapply L5C.limbs_at_agree. 4: exact OL3. 2: clear - Q4096; lia. 2:{ rewrite OL1. cbn [L5.bo_len]. clear - Q47 LC CR. lia. }
               intros i Hi. rewrite OL1 in Hi. cbn [L5.bo_len] in Hi. apply AG. right; right. exists cap, q. split. reflexivity. left. clear - Hi LC; lia. }
    unfold L5ACMP.cmp_objA. cbn [L5.bo_fb L5.bo_len L5.bo_st L5.bo_data].
    split. exact OB'. split. exact BT1. split. clear - LEN; lia. split. clear - LEN; lia. split. clear - OR; lia. split. clear - OR; lia. split. exact OBIG.
    split. right. clear - OR SLO HSCR; lia. split. exact ZO.
    split. clear - Q4096 Q47 LC CR; lia. split. exact Q8. split. clear - X7 LC; lia. split. right. clear - X5 SLO HSCR LC; lia.
    intros i Hi. rewrite AG. apply SBK. replace (8 * cap / 8) with cap by (clear; lia). clear - Hi LC; lia.
    right; right. exists cap, q. split. reflexivity. right. clear - Hi LC; lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Lemma cmpreg_vis W BX Mc modelc LKc crc Ac o b ws a : binv W BX Mc modelc LKc crc Ac -> aobj FF' o 32 -> tob (BX ++ LB) Mc o b ws -> (o <= a < o + 1 \/ cmpreg o b a) ->
  mrestrict (ahid Ac modelc) Mc (Z_to_bv 64 a) = Mc (Z_to_bv 64 a).
Proof.
  intros BI AOB (OB & _ & _ & INB) CR. pose proof BI as (B1 & _).
  pose proof (aobj_facts L ar C HI LY HIok (BX ++ LB) FF' LKc crc Ac Mc modelc o 32 0 0 B1 AOB ltac:(clear; lia) ltac:(reflexivity)) as (OR & _ & _ & OVIS & OVSH & _). change (32 / 8) with 4 in OVSH.
  pose proof (vis_pack L ar C HI LY HIok (BX ++ LB) FF' LKc crc Ac Mc modelc B1) as (_ & _ & _ & _ & VBLK & VBSH & _).
  apply L5LZ.mrestrict_visible'.
  destruct CR as [CR|[CR|[CR|(cap & q & Eq & CR)]]].
  - replace a with (o + (a - o)) by (clear; lia). apply OVIS. clear - CR; lia.
  - replace a with (o + (a - o)) by (clear; lia). apply OVIS. clear - CR; lia.
  - replace a with (o / 8 + SB + (a - (o / 8 + SB))) by (clear; lia). apply OVSH. clear - CR; lia.
  - destruct b as [fb len sto]. cbn [L5.bo_st] in *. subst sto. destruct OB as (_ & _ & _ & (_ & _ & _ & LC & CRG & Q8 & Q4096 & Q47 & _)).
    destruct CR as [CR|CR].
    + replace a with (a + 0) by (clear; lia). apply (VBLK q (8 * cap) a 1 (INB cap q eq_refl)). clear - CR; lia. clear - CR; lia. clear; lia.
    + replace a with (a + 0) by (clear; lia). apply (VBSH q (8 * cap) a 1 (INB cap q eq_refl)). 2: clear; lia. intros i Hi. unfold in_shadow_of, S.
      clear - CR Hi Q8 CRG Q4096. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Lemma wp_scratch W BX Mc modelc LKc crc Ac a : binv W BX Mc modelc LKc crc Ac -> E - SCRD <= a < SPA -> L5DKA.wp_ok L ar LB FF E SCRD SPA (docell E) F 3 W BX a.
Proof.
  intros BI Ha. destruct G as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG' F32 FLA' FLR FLBIG' NCF NCS].
  split. { intros D. pose proof (OCR a D) as X. clear - X Ha; lia. }
  split. { split. apply stack_client. clear - Ha SLO SHI SPT; lia. clear; lia. clear - Ha SLO SPT; lia. }
  intros Hc. exfalso. pose proof (aclient_cons L ar LB FF (F, 3, SPA + 32) E SCRD a Hc) as Hc'.
  destruct (aclient_cases L ar C HI LY HIok LB FF' LK2 cr2 A M2 _ E SCRD a HH2 ltac:(clear - SPT; lia) Hc') as [Y|Y]. clear - Y Ha; lia. clear - Y Ha SLO; lia.
Qed.

(* [comment removed for export] *)
Lemma cmpreg_off W BX Mc modelc LKc crc Ac o b ws a : binv W BX Mc modelc LKc crc Ac -> aobj FF' o 32 -> tob (BX ++ LB) Mc o b ws -> cmpreg o b a ->
  (F <= a < F + 512 -> o + 1 <= a < o + 32) /\ ~ (E - SCRD <= a < E).
Proof.
  intros BI AOB (OB & _ & _ & INB) CR. pose proof BI as (B1 & _).
  pose proof (aobj_facts L ar C HI LY HIok (BX ++ LB) FF' LKc crc Ac Mc modelc o 32 0 0 B1 AOB ltac:(clear; lia) ltac:(reflexivity)) as (OR & OBIG & _).
  pose proof (NUM L ar HI R LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER) as ((FRG & FLRG & ERG) & FRP & FLRP & ALF & FBIG & FLBIG & FLA & SFA & SFLA & SFB).
  destruct G as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG' F32 FLA' FLR FLBIG' NCF NCS].
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  destruct CR as [CR|[CR|(cap & q & Eq & CR)]].
  - split. intros _. exact CR. clear - CR OR SLO. lia.
  - unfold SB in CR. split. intros X. exfalso. clear - CR X OR FBIG. lia. clear - CR OR SLO SPT. lia.
  - destruct b as [fb len sto]. cbn [L5.bo_st] in *. subst sto. destruct OB as (_ & _ & _ & (_ & _ & _ & LC & CRG & Q8 & Q4096 & Q47 & _)).
    pose proof (blk_frame L ar C HI HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G W BX Mc modelc LKc crc Ac q (8 * cap) o BI (INB cap q eq_refl)) as (Y4 & _).
    pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ B1) as (WB & _).
    pose proof (proj1 (WB _ (INB cap q eq_refl))) as (_ & _ & _ & _ & X5 & _). cbn [fst snd] in X5.
    destruct CR as [CR|CR].
    + split. intros X. exfalso. clear - CR X Y4. lia. clear - CR X5 SLO. lia.
    + unfold SB in CR. split. intros X. exfalso. clear - CR X FBIG Q4096 Q47 CRG. lia. clear - CR SLO SPT Q47 CRG Q4096. lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma fb_clr fb : 0 <= fb < 256 -> 0 <= Z.land fb 253 < 256 /\ Z.testbit (Z.land fb 253) 0 = Z.testbit fb 0 /\ Z.testbit (Z.land fb 253) 1 = false.
Proof.
  intros Hfb.
  assert (H := L5ACPY.byte_enum2 (fun x y => ((0 <=? Z.land x 253) && (Z.land x 253 <? 256) && Bool.eqb (Z.testbit (Z.land x 253) 0) (Z.testbit x 0) && negb (Z.testbit (Z.land x 253) 1))%bool)
                ltac:(vm_compute; reflexivity) fb 0 Hfb ltac:(lia)).
  cbv beta in H. repeat (apply andb_prop in H; destruct H as [H ?]).
  repeat match goal with X : Bool.eqb _ _ = true |- _ => apply Bool.eqb_prop in X end.
  match goal with X : negb _ = true |- _ => apply negb_true_iff in X end.
  split. lia. split; assumption.
Qed.
Lemma qn_rng a b : 0 <= a < 256 -> 0 <= b < 256 -> 0 <= Z.lxor (Z.land a 2) (Z.land b 2) / 2 <= 1 /\ (Z.land b 2 = 0 \/ Z.land b 2 = 2).
Proof.
  intros Ha Hb.
  assert (H := L5ACPY.byte_enum2 (fun x y => ((0 <=? Z.lxor (Z.land x 2) (Z.land y 2) / 2) && (Z.lxor (Z.land x 2) (Z.land y 2) / 2 <=? 1) && ((Z.land y 2 =? 0) || (Z.land y 2 =? 2)))%bool)
                ltac:(vm_compute; reflexivity) a b Ha Hb).
  cbv beta in H. repeat (apply andb_prop in H; destruct H as [H ?]). apply orb_prop in H0. split. lia. destruct H0; [left|right]; lia.
Qed.

(* [comment removed for export] *)
Lemma p3cmp (fx : FPState) Rc Mc modelc W BX LKc crc Ac fden ft bn wn bd wd :
  binv W BX Mc modelc LKc crc Ac -> rinvH Rc ->
  getr Rc (reg 21) = Z_to_bv 64 fden -> getr Rc (reg 22) = Z_to_bv 64 ft -> getr Rc (reg 24) = Z_to_bv 64 (F + 96) -> 0 <= fden < 256 -> 0 <= ft < 256 ->
  tob (BX ++ LB) Mc (F + 96) bn wn -> tob (BX ++ LB) Mc (F + 32) bd wd -> (1 <= L5.bo_len bn <= 300)%nat -> (1 <= L5.bo_len bd <= 300)%nat ->
  (forall (fx2 : FPState) R2 M2' model2' c,
      binv W BX M2' model2' LKc crc Ac -> rinvH R2 -> (forall x, In x [19; 20; 26]%nat -> getr R2 (reg x) = getr Rc (reg x)) ->
      getr R2 (reg 10) = Z_to_bv 64 c -> L5CMP.res_sized c (L5.bo_len bn) (L5.bo_len bd) -> (L5.bo_len bn = L5.bo_len bd -> c = L5CMP.cmp_val wn wd) ->
      getr R2 (reg 22) = Z_to_bv 64 (Z.lxor (Z.land fden 2) (Z.land ft 2) / 2) -> getr R2 (reg 24) = Z_to_bv 64 (F + 96) ->
      (forall a, 0 <= a < 2 ^ 64 -> a <> F + 96 -> a <> F + 32 -> ~ (E - 288 <= a < E - 280) -> ~ (SPA - 16 <= a < SPA) -> M2' (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)) ->
      L5.u8_at RSEGS M2' (F + 96) (Z.land (L5.bo_fb bn) 253) -> L5.u8_at RSEGS M2' (F + 32) (Z.land (L5.bo_fb bd) 253) -> L5.u64_at RSEGS M2' (E - 288) (Z.land ft 2) ->
      srealizes RSEGS SCFG (cfg (fx:=fx2) R2 0x92374 M2' model2') K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc 0x9233c Mc modelc) K.
Proof.
  intros BI RIH X21 X22 X24 FDR FTR TN TD LN LD KF.
  pose proof RIH as (RI & X18 & X23 & X27 & X25).
  pose proof (pf_of_binv L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G W _ Mc modelc LKc crc Ac BI) as PF.
  destruct PF as (W352 & IMGC & CSB & CUAR & FDEFv & FWv & FSHWv & FLCv & FLWv).
  pose proof (NUM L ar HI R LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER) as ((FRG & FLRG & ERG) & FRP & FLRP & ALF & FBIG & FLBIG & FLA & SFA & SFLA & SFB).
  destruct (L5AFK.vis_facts L ar C HI LY HIok M model LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2 G W _ Mc modelc LKc crc Ac BI) as (_ & _ & _ & (_ & _ & FV & SV & SHV)).
  change (ff_bytes 3) with 512 in FV.
  pose proof RI as (X2 & X8 & X9 & X3 & X4). pose proof BI as (B1 & _ & _ & _ & _ & B6 & _).
  pose proof (vis_pack L ar C HI LY HIok (BX ++ LB) FF' LKc crc Ac Mc modelc B1) as (_ & VIS & _).
  assert (SLO : ahl_ceil ar + 4096 + SCRD <= E) by (destruct G as [_ _ SLO0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _]; exact SLO0).
  set (MV := mrestrict (ahid Ac modelc) Mc) in *.
  assert (AON' : aobj FF' (F + 96) 32) by (eapply L5ADVEA.loc_aobj; [exact G | clear; lia | clear; lia | reflexivity]).
  assert (AOD' : aobj FF' (F + 32) 32) by (eapply L5ADVEA.loc_aobj; [exact G | clear; lia | clear; lia | reflexivity]).
  pose proof (proj1 TN) as (N0 & FNR & _). pose proof (proj1 TD) as (D0 & FDDR & _).
  set (fn := L5.bo_fb bn) in *. set (fdd := L5.bo_fb bd) in *.
  assert (N0v : L5.u8_at RSEGS MV (F + 96) fn).
  { apply (proj2 (u8_at_vis (ahid Ac modelc) Mc (F + 96) fn ltac:(eapply avis_sub; [exact FV | clear; lia | clear; lia]) ltac:(clear - FRP; lia) ltac:(clear - FRP; lia))). exact N0. }
  assert (D0v : L5.u8_at RSEGS MV (F + 32) fdd).
  { apply (proj2 (u8_at_vis (ahid Ac modelc) Mc (F + 32) fdd ltac:(eapply avis_sub; [exact FV | clear; lia | clear; lia]) ltac:(clear - FRP; lia) ltac:(clear - FRP; lia))). exact D0. }
  assert (HV1 : 0 <= fn <= 255 /\ 0 <= fn < 2 ^ 64) by (clear - FNR; lia). destruct HV1 as [HV1 HV1'].
  assert (HV2 : 0 <= fdd <= 255 /\ 0 <= fdd < 2 ^ 64) by (clear - FDDR; lia). destruct HV2 as [HV2 HV2'].
  assert (HV3 : 0 <= fden <= 255 /\ 0 <= fden < 2 ^ 64) by (clear - FDR; lia). destruct HV3 as [HV3 HV3'].
  assert (HV4 : 0 <= ft <= 255 /\ 0 <= ft < 2 ^ 64) by (clear - FTR; lia). destruct HV4 as [HV4 HV4'].
  pose proof (v5P3_conc fx Rc MV (fun j => match j with 2%nat => E | 40%nat => F | 41%nat => fl | 55%nat => fden | 56%nat => ft | 58%nat => U Rc 1 | 63%nat => fdd | 64%nat => fn | _ => 0 end)) as P. cbn beta iota in P.
  feed P ltac:(first [apply UR | apply U_to | sc ]).
  destruct P as (fx1 & R1 & M1v & MG1 & pFR & pFZ & (pMS & pKS & pR1 & pR10 & pR11 & pU12 & pU22 & pD & pS64 & pN & _)).
  (* [comment removed for export] *)
  assert (AG1 : forall o b ws a, aobj FF' o 32 -> tob (BX ++ LB) Mc o b ws -> (o = F + 96 \/ o = F + 32) -> cmpreg o b a -> M1v (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)).
  { intros o b ws a AOB TO EO CRG. destruct (cmpreg_off W BX Mc modelc LKc crc Ac o b ws a BI AOB TO CRG) as (Y1 & Y2).
    assert (NA : 0 <= a < 2 ^ 64 /\ a <> F + 96 /\ a <> F + 32 /\ ~ (E - 288 <= a < E - 280)).
    { split. 2:{ split. intros ->. specialize (Y1 ltac:(clear; lia)). clear - Y1 EO; lia. split. intros ->. specialize (Y1 ltac:(clear; lia)). clear - Y1 EO; lia. intros X. apply Y2. clear - X HSCR; lia. }
      destruct TO as (OB & _ & _ & INB). assert (RG : 4096 <= o /\ o + 32 <= 2 ^ 47 /\ o mod 8 = 0) by (eapply L5ADVEA.obj_rng; [exact LY | exact HIok | exact BI | exact AOB]).
      destruct CRG as [CRG|[CRG|(cap & q & Eq & CRG)]]. clear - CRG RG; lia. unfold SB in CRG. clear - CRG RG. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
      destruct b as [fb len sto]. cbn [L5.bo_st] in *. subst sto. destruct OB as (_ & _ & _ & (_ & _ & _ & LC & CRR & Q8 & Q4096 & Q47 & _)). unfold SB in CRG. clear - CRG CRR Q4096 Q47. lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    destruct NA as (NA0 & NA1 & NA2 & NA3). rewrite (pFZ a NA0). apply (cmpreg_vis W BX Mc modelc LKc crc Ac o b ws a BI AOB TO). right. exact CRG.
    clear - NA1; lia. clear - NA2; lia. clear - NA3; lia. }
  pose proof (fb_clr fn FNR) as (C1n & C2n & C3n). pose proof (fb_clr fdd FDDR) as (C1d & C2d & C3d).
  destruct (cmp_obj_mk W BX Mc modelc LKc crc Ac M1v (F + 96) bn wn (Z.land fn 253) BI AON' TN (fun a => AG1 _ bn wn a AON' TN (or_introl eq_refl)) pN C1n C2n C3n LN) as (OXn & OLn).
  destruct (cmp_obj_mk W BX Mc modelc LKc crc Ac M1v (F + 32) bd wd (Z.land fdd 253) BI AOD' TD (fun a => AG1 _ bd wd a AOD' TD (or_intror eq_refl)) pD C1d C2d C3d LD) as (OXd & OLd).
  assert (RI1 : rinvH R1). { apply (rinvH_ks Rc R1 KS_v5P3 RIH pKS). vm_compute; reflexivity. }
  pose proof RI1 as ((Y2 & _) & _).
  assert (SA16 : (E - 352) mod 16 = 0). { clear - EA. unfold aligned in EA. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  assert (W16 : L5.writable RSEGS M1v (SPA - 16) 16).
  { apply (L5C.writable_of_defined RSEGS). 2: clear - ER; lia. 2: clear - ER; lia. eapply L5.defined_grows. exact MG1.
    apply (proj2 (defined_vis (ahid Ac modelc) Mc (SPA - 16) 16 (VIS (SPA - 16) 16 ltac:(clear - SLO HSCR; lia) ltac:(clear - ER; lia)))).
    destruct B6 as (_ & _ & _ & _ & DSCR & _). eapply L5.defined_sub. exact DSCR. clear - HSCR; lia. clear; lia. }
  assert (FR6 : 6500352 <= F) by (destruct G as [_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FR0 _ _ _ _ _ _ _ _]; clear - FR0; lia).
  assert (IMG1 : L5.img_clear M1v 860160 880640 /\ L5.u64_at RSEGS M1v 908088 2147450880 /\ L5.u32_at RSEGS M1v 908096 1).
  { split. { intros a Ha. rewrite pFZ. apply IMGC. exact Ha. clear - Ha; lia. all: clear - Ha FR6 ER; lia. }
    split. { eapply L5C.u64_at_agree. 4: exact CSB. 2: clear; lia. 2: clear; lia. intros i Hi. apply pFZ. clear - Hi; lia. all: clear - Hi FR6 ER; lia. }
    eapply L5ACMP.u32_at_agree1. 4: exact CUAR. 2: clear; lia. 2: clear; lia. intros i Hi. apply pFZ. clear - Hi; lia. all: clear - Hi FR6 ER; lia. }
  destruct IMG1 as (IMG1 & CSB1 & CUAR1).
  destruct (L5ACMP.cmp_runA fx1 R1 M1v (F + 96) (F + 32) SPA 0x92374 _ _ wn wd pR10 pR11 pR1 ltac:(split; [clear; lia | reflexivity]) Y2 ltac:(clear - ER; lia) SA16 W16 IMG1 CSB1 CUAR1 OXn OXd OLn OLd)
    as (fx2 & R2 & M2v & cMS & (cKS & cRP & (c & cR10 & cRS & cVAL) & cFR & cMG)).
  cbn [L5.bo_len] in cRS, cVAL.
  pose proof (msteps_trans _ _ _ _ pMS cMS) as MS2.
  set (Wp := fun a => a = F + 96 \/ a = F + 32 \/ (E - 288 <= a < E - 280) \/ (SPA - 16 <= a < SPA)).
  apply (L5DKA.bstage L ar C HI LY HIok M model LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2 G W _ Mc modelc LKc crc Ac fx fx2 Rc 0x9233c R2 0x92374 M2v Wp K BI MS2 (mem_grows_trans _ _ _ MG1 cMG)).
  { intros a Ha Hn. subst Wp; cbn beta in Hn. rewrite cFR. apply pFZ. exact Ha. 1,2,3: clear - Hn; lia. exact Ha. clear - Hn; lia. }
  { intros a Ha Wa. subst Wp; cbn beta in Wa. destruct Wa as [Wa|[Wa|[Wa|Wa]]].
    1,2: apply (L5DKA.wp_fake L ar HI LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2 G); change (ff_bytes 3) with 512; clear - Wa; lia.
    apply (L5DKA.wp_frame L ar HI LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2 G); [clear - Wa; lia | unfold docell; clear - Wa; lia].
    apply (wp_scratch W BX Mc modelc LKc crc Ac a BI). clear - Wa HSCR; lia. }
  intros M3 model3 BI3 AH3 VIS3 MGM3 FRM3.
  assert (RI2 : rinvH R2) by (apply (rinvH_pres R1 R2 RI1 cRP)).
  assert (U8V : forall a v, F <= a < F + 512 -> L5.u8_at RSEGS M2v a v -> L5.u8_at RSEGS M3 a v).
  { intros a v Hr Hc. apply (proj1 (u8_at_vis (ahid Ac modelc) M3 a v ltac:(eapply avis_sub; [exact FV | clear - Hr; lia | clear - Hr; lia]) ltac:(clear - Hr FRP; lia) ltac:(clear - Hr FRP; lia))). rewrite VIS3. exact Hc. }
  assert (KEEP2 : forall a n, 0 <= a -> a + n <= 2 ^ 64 -> (a + n <= SPA - 16 \/ SPA <= a) -> forall i, a <= i < a + n -> M2v (Z_to_bv 64 i) = M1v (Z_to_bv 64 i)).
  { intros a n H0 H1 H2 i Hi. apply cFR. clear - Hi H0 H1; lia. clear - Hi H2; lia. }
  assert (KS3 : forall x, In x [19; 20; 26]%nat -> getr R2 (reg x) = getr Rc (reg x)).
  { intros x [<-|[<-|[<-|[]]]]; [rewrite (cs_of_preserved R1 R2 19 cRP) by inl | rewrite (cs_of_preserved R1 R2 20 cRP) by inl | rewrite (cs_of_preserved R1 R2 26 cRP) by inl]; apply pKS; inl. }
  apply (KF fx2 R2 M3 model3 c BI3 RI2 KS3 cR10 cRS cVAL).
  - rewrite (cs_of_preserved R1 R2 22 cRP) by inl. rewrite <- pU22. symmetry. apply Z_to_bv_bv_unsigned.
  - rewrite (cs_of_preserved R1 R2 24 cRP) by inl. rewrite (pKS 24%nat) by inl. exact X24.
  - intros a Ha N1 N2 N3 N4. apply FRM3. exact Ha. subst Wp; cbn beta. clear - N1 N2 N3 N4. lia.
  - apply U8V. clear; lia. eapply L5C.u8_at_agree. 4: exact pN. 2: clear - FRP; lia. 2: clear - FRP; lia. intros i Hi. apply (KEEP2 (F + 96) 1 ltac:(clear - FRP; lia) ltac:(clear - FRP; lia) ltac:(left; clear - SFB; lia) i Hi).
  - apply U8V. clear; lia. eapply L5C.u8_at_agree. 4: exact pD. 2: clear - FRP; lia. 2: clear - FRP; lia. intros i Hi. apply (KEEP2 (F + 32) 1 ltac:(clear - FRP; lia) ltac:(clear - FRP; lia) ltac:(left; clear - SFB; lia) i Hi).
  - apply (proj1 (u64_at_vis (ahid Ac modelc) M3 (E - 288) _ ltac:(eapply avis_sub; [exact SV | clear; lia | clear; lia]) ltac:(clear - ER; lia) ltac:(clear - ER; lia))). rewrite VIS3.
    eapply L5C.u64_at_agree. 4: exact pS64. 2: clear - ER; lia. 2: clear - ER; lia. intros i Hi. apply (KEEP2 (E - 288) 8 ltac:(clear - ER; lia) ltac:(clear - ER; lia) ltac:(right; clear; lia) i Hi).
Qed.
End DIV.
End WithIface.
End SCFG_1.
End L5ADVHC.
