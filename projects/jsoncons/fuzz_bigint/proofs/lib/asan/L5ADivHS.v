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
     L5Cmp L5CoreA L5CoreSpecsA L5StepA L5CoreB L5ADetailH L5ACopyAS L5AFrameK L5DivKitA L5ADivH L5ADivT L5ADivD L5ADivP2 L5ADivE L5ADivEA L5ADivHC L5ADivHD L5ADivHA.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5ADVHS.
Import L5A. Import L5CA. Import L5CSA. Import L5SA. Import L5CB. Import L5ADH. Import L5ADVH. Import L5ADVT. Import L5ADVD. Import L5ADVE. Import L5ADVEA. Import L5ADVHC. Import L5ADVHD. Import L5ADVHA. Import L5ADIVP2.
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Local Ltac inl := apply L5K.in_b; vm_compute; reflexivity.
Section WithIface.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : as0_layout L C.
Hypothesis HIok : asan_iface_ok L ar C SCFG HI.
Hypothesis Hcpss : L5ACPAS.copya_ssrc_spec L ar HI.

Section DIV.
Variables (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet) (LB : list (Z * Z)) (FF LK : list fframe) (A : list (Z * Z)) (cr0 : credit)
          (E SCRD F fl ro : Z) (LK2 : list fframe) (M2 : word -> option byte) (model2 : Model) (cr2 : credit).
Local Notation SPA := (E - 352).
Hypothesis G : L5AFK.gctx L ar HI LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2.
Hypothesis ER : 140735332487680 <= E <= 140737488355328.
Hypothesis EA : L5ADIVP2.aligned E 32.
Hypothesis HK : K [].
Hypothesis G4 : getr R (reg 4) = Z_to_bv 64 (hl_tp L).
Hypothesis HSCR : 352 + 4656 <= SCRD.
Hypothesis FFR1 : ffrk 1 FF LK 4.
Hypothesis FFRS : ffrs FF E.
Hypothesis HH0 : ri_inv HI LB FF LK cr0 A M (vml_of model).
Local Notation binv := (L5AFK.binv L ar HI M model LB FF LK A E SCRD SPA (down E F ro R) F 3).
Local Notation FF' := ((F, 3, SPA + 32) :: FF).
Local Notation SH := (F / 8 + 2147450880).

(* [comment removed for export] *)
Lemma stk_at W BX Mc modelc LKc crc Ac o b :
  binv W BX Mc modelc LKc crc Ac -> L5ACPAS.sobj ar E o 32 -> L5.big_at RSEGS M o b -> L5.defined M o 32 -> shadow_zero M o 4 ->
  (forall a, (o <= a < o + 32 \/ o / 8 + SB <= a < o / 8 + SB + 4) -> L5.outside W a) ->
  L5.big_at RSEGS Mc o b /\ L5.defined Mc o 32 /\ shadow_zero Mc o 4.
Proof.
  intros (_ & _ & _ & _ & _ & _ & EK & _) SO OB DF SZ NW.
  destruct G as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG' F32 FLA' FLR FLBIG' NCF NCS].
  pose proof (L5ACPAS.sobj_facts L ar C HI LY HIok LB FF LK cr0 A M model o 32 E E SCRD HH0 SO ltac:(clear; lia) ltac:(reflexivity) SPT ltac:(clear - SLO SPC; lia) ltac:(clear; lia))
    as ((OLO & OE & OHI & O8 & _) & OBIG & _ & _ & _ & OCL & OCLSH). change (32 / 8) with 4 in OCLSH.
  assert (AGO : forall i, o <= i < o + 32 -> Mc (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
  { intros i Hi. apply EK. split. clear - Hi OLO OHI; lia. split. replace i with (o + (i - o)) by (clear; lia). apply OCL. clear - Hi; lia. apply NW. left. exact Hi. }
  split. { eapply L5C.big_at_agree. 4: exact OB. exact AGO. clear - OLO; lia. clear - OHI; lia. }
  split. { intros i Hi. rewrite AGO by (clear - Hi; lia). apply DF. exact Hi. }
  intros j Hj. unfold byte_at. rewrite EK. apply SZ. exact Hj. split.
  unfold S, SB. clear - Hj OLO OHI OBIG. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
  split. unfold S. apply OCLSH. exact Hj. apply NW. right. unfold S. clear - Hj; lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Lemma copy_stage_ss (fx : FPState) Rc Mc modelc W BX LKc crc Ac k o' pcn fbo b' ws' :
  binv W BX Mc modelc LKc crc Ac -> rinvD R E Rc ->
  getr Rc (reg 10) = Z_to_bv 64 (F + k) -> getr Rc (reg 11) = Z_to_bv 64 o' -> getr Rc (reg 1) = Z_to_bv 64 pcn -> L5.ra_ok pcn ->
  32 <= k -> k + 32 <= 504 -> k mod 8 = 0 ->
  L5.u8_at RSEGS Mc (F + k) fbo -> 0 <= fbo < 256 -> shadow_zero Mc (F + k) 4 ->
  L5.big_at RSEGS Mc o' b' -> L5.bo_dyn b' = false -> L5ACPAS.sobj ar E o' 32 -> L5.defined Mc o' 32 -> shadow_zero Mc o' 4 ->
  (forall (fx' : FPState) R' M' model' (g : growth) LBn cr' LK' A',
      copy_post L ar (BX ++ LB) FF' LK' crc Mc M' Rc R' (F + k) o' SPA fbo b' ws' g LBn cr' ->
      binv W (match g with Same => BX | Grown q cap => (q, 8 * cap) :: BX end) M' model' LK' cr' A' ->
      incl Ac A' -> incl LK' LKc ->
      srealizes RSEGS SCFG (cfg (fx:=fx') R' pcn M' model') K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc COPYA Mc modelc) K.
Proof.
  intros BI RI X10 X11 X1 RAn K1 K2 K8 DFB FBR DSZ OB' DYF SO DF' SZ' KF.
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
  assert (SO' : L5ACPAS.sobj ar SPA o' 32). { destruct SO as (S1 & S2 & S3). split. clear - S1; lia. split. exact S2. exact S3. }
  apply (Hcpss fx Rc Mc modelc K (BX ++ LB) FF' LKc crc Ac (F + k) o' SPA pcn fbo b' ws' B1 B2 HK).
  - rewrite r10. exact X10.
  - rewrite r11. exact X11.
  - exact DYF.
  - rewrite r1. exact X1.
  - exact RAn.
  - rewrite r2. exact Z2.
  - exact A32c.
  - rewrite r4, Z4. rewrite <- G4. reflexivity.
  - exact STKc.
  - exact DFB.
  - exact FBR.
  - eapply L5ADVEA.loc_aobj; [exact G | exact K1 | exact K2 | exact K8].
  - exact DSZ.
  - exact OB'.
  - exact SO'.
  - exact DF'.
  - exact SZ'.
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
      - exfalso. destruct PG as (DYT & _). rewrite DYF in DYT. discriminate DYT. }
    apply (KF fx3 R3 M3 model3 g LBn cr3 LK3 A3 POST BI3 IA3 ILK3).
Qed.
End DIV.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section HEADN.
Lemma head1_ss SCRD (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
      (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (to dno qo ro rd E r : Z) (bdn : L5.bigobj) (wdn : list Z) :
  352 + 4656 <= SCRD ->
  ri_inv HI LB FF LK cr A M (vml_of model) -> amodel_ok A model -> K [] ->
  getr R 10%bv = Z_to_bv 64 to -> getr R 11%bv = Z_to_bv 64 dno -> getr R 12%bv = Z_to_bv 64 qo -> getr R 13%bv = Z_to_bv 64 ro -> getr R 14%bv = Z_to_bv 64 rd ->
  0 <= to < 2 ^ 64 -> 0 <= dno < 2 ^ 64 -> 0 <= qo < 2 ^ 64 -> 0 <= ro < 2 ^ 64 -> 0 <= rd < 2 ^ 64 ->
  getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r ->
  getr R 2%bv = Z_to_bv 64 E -> E mod 32 = 0 -> getr R 4%bv = Z_to_bv 64 (hl_tp L) -> astk ar M E SCRD ->
  ffrk 3 FF LK 2 -> ffrk 1 FF LK 4 -> ffrs FF E ->
  L5.big_at RSEGS M dno bdn -> L5.bo_dyn bdn = false -> L5ACPAS.sobj ar E dno 32 -> L5.defined M dno 32 -> shadow_zero M dno 4 ->
  (forall (F fl : Z) (LK2 : list fframe) (M2 : word -> option byte) (model2 : Model) (fx4 : FPState) R3 R4 M3 model3 M4 model4 (g : growth) LBn cr4 LK4 A4 fbo,
      L5AFK.gctx L ar HI LB FF LK A E SCRD (E - 352) (E - 352) E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr ->
      140735332487680 <= E <= 140737488355328 -> U R 1 = r ->
      L5AFK.binv L ar HI M model LB FF LK A E SCRD (E - 352) (down E F ro R) F 3 [] [] M3 model3 LK2 cr A ->
      L5AFK.binv L ar HI M model LB FF LK A E SCRD (E - 352) (down E F ro R) F 3 [] (match g with Same => [] | Grown q cap => [(q, 8 * cap)] end) M4 model4 LK4 cr4 A4 ->
      rinvD R E R3 -> regs_preserved R3 R4 ->
      getr R3 (reg 18) = Z_to_bv 64 (F / 8 + SB) /\ getr R3 (reg 19) = Z_to_bv 64 qo /\ getr R3 (reg 20) = Z_to_bv 64 SB /\ getr R3 (reg 21) = Z_to_bv 64 dno
      /\ getr R3 (reg 22) = Z_to_bv 64 rd /\ getr R3 (reg 23) = Z_to_bv 64 (F + 32) /\ getr R3 (reg 24) = Z_to_bv 64 to /\ getr R3 (reg 27) = Z_to_bv 64 F
      /\ getr R3 (reg 25) = getr R (reg 25) /\ getr R3 (reg 26) = getr R (reg 26) ->
      copy_post L ar ([] ++ LB) ((F, 3, E - 352 + 32) :: FF) LK4 cr M3 M4 R3 R4 (F + 32) dno (E - 352) fbo bdn wdn g LBn cr4 ->
      0 <= fbo < 256 -> dsh M3 F 248 248 248 248 248 -> shadow_zero M3 (F + 32) 4 -> L5.u64_at RSEGS M3 F 1102416563 ->
      L5.big_at RSEGS M3 dno bdn /\ L5.defined M3 dno 32 /\ shadow_zero M3 dno 4 ->
      srealizes RSEGS SCFG (cfg (fx:=fx4) R4 0x922cc M4 model4) K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) R DIVIDE M model) K.
Proof.
  intros HSCR HH AM HK G10 G11 G12 G13 G14 TOR DNR QOR ROR RDR G1 RA G2 A32 G4 STK FFR3 FFR1 FFRS OBD DYF SO DFD SZDN KF.
  apply (L5ADVH.div_entry L ar C HI LY HIok SCRD fx R M model K LB FF LK cr A to dno qo ro rd E r ltac:(clear - HSCR; lia) HH AM HK G10 G11 G12 G13 G14 TOR DNR QOR ROR RDR G1 RA G2 A32 G4 STK FFR3 FFRS).
  intros F fl LK2 M2 model2 fx3 R3 M3 model3 G UR1 G2' G4' BI3 RI3 X1 (X10 & X11 & X12) XS DSH SZD HDR.
  pose proof STK as (A16 & SLO & SHI & SPT & _).
  assert (ER : 140735332487680 <= E <= 140737488355328) by (clear - SLO SHI SPT HSCR; lia).
  assert (EA : L5ADIVP2.aligned E 32) by exact A32.
  pose proof BI3 as (B1 & _).
  pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ B1) as (_ & WF1 & _).
  pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (WF1 _ (or_introl eq_refl))))))) as FD. cbn [ff_addr ff_class fst snd] in FD. change (ff_bytes 3) with 512 in FD.
  pose proof (stk_at R M model LB FF LK A cr E SCRD F fl ro LK2 M2 model2 cr G HH [] [] M3 model3 LK2 cr A dno bdn BI3 SO OBD DFD SZDN ltac:(intros a _ rr [])) as SK3.
  destruct (u8_of_defined M3 (F + 32) ltac:(replace (F + 32) with (F + (32)) by (clear; lia); apply FD; clear; lia)) as (fbo & DFB & FBR).
  eapply (copy_stage_ss R M model K LB FF LK A E SCRD F fl ro LK2 M2 model2 cr G ER EA HK G4' HSCR FFR1 FFRS) with (k := 32) (o' := dno) (pcn := 0x922cc) (fbo := fbo) (b' := bdn) (ws' := wdn);
    [exact BI3 | exact RI3 | exact X10 | exact X11 | exact X1 | split; [clear; lia | reflexivity] | clear; lia | clear; lia | reflexivity | exact DFB | exact FBR | exact SZD
     | exact (proj1 SK3) | exact DYF | exact SO | exact (proj1 (proj2 SK3)) | exact (proj2 (proj2 SK3)) | ].
  intros fx4 R4 M4 model4 g LBn cr4 LK4 A4 POST BI4 IA4 ILK4.
  apply (KF F fl LK2 M2 model2 fx4 R3 R4 M3 model3 M4 model4 g LBn cr4 LK4 A4 fbo G ER UR1 BI3 BI4 RI3 (proj1 POST) XS POST FBR DSH SZD HDR SK3).
Qed.
End HEADN.
End WithIface.
End SCFG_1.
End L5ADVHS.
