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
     L5CoreA L5CoreSpecsA L5StepA L5CoreB L5ADetailH L5AFrameK L5DivKitA L5DivSpecsA L5OpmodSpecsA L5DivLeafSpecsA L5DivInnerSpecsA L5ACopyAS L5ADivH L5ADivT L5ADivD L5ADivE L5ADivEA L5ADivHC L5ADivHA L5ADivHO L5ADivPG1 L5ADivGL.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5ADVGA.
Import L5A. Import L5CA. Import L5CSA. Import L5W. Import L5SA. Import L5CB. Import L5ADH. Import L5ADVH. Import L5ADVT. Import L5ADVD. Import L5ADVE. Import L5ADVEA. Import L5ADVHC. Import L5ADVHA. Import L5ADVHO. Import L5ADIVPG1.
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
Hypothesis Hcps : L5ACPAS.copya_stk_spec L ar HI.
Hypothesis Hnorm : L5DLA.norm_specA L ar HI.
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
Lemma frm_agree LBx scr (X : Z -> Prop) Mc M1 lo n : offx LBx scr X Mc M1 -> SPA <= lo -> lo + n <= E -> 0 <= scr ->
  (forall i, lo <= i < lo + n -> ~ X i) -> forall i, lo <= i < lo + n -> M1 (Z_to_bv 64 i) = Mc (Z_to_bv 64 i).
Proof.
  intros OFF H1 H2 HS NX i Hi. destruct G as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG' F32 FLA' FLR FLBIG' NCF NCS].
  apply OFF. clear - Hi H1 H2 ER; lia. apply stack_client. clear - Hi H1 H2 SLO SHI SPT HSCR; lia. clear - Hi H1 HS; lia. apply NX. exact Hi.
Qed.

(* [comment removed for export] *)
Lemma stk_shz W BX Mc modelc LKc crc Ac o : binv W BX Mc modelc LKc crc Ac -> L5OMA.stksh ar M (E - SCRD) ->
  SPA <= o -> o + 40 <= E -> o mod 8 = 0 -> (forall j, 0 <= j < 4 -> L5.outside W (o / 8 + SB + j)) -> shadow_zero Mc o 4.
Proof.
  intros (B1 & _ & _ & _ & _ & _ & EK & _) SSH H1 H2 O8 NW.
  destruct G as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG' F32 FLA' FLR FLBIG' NCF NCS].
  pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ B1) as WF0.
  assert (TOP : ar_stack_top ar <= 2 ^ 47). { clear - WF0. decompose [and] WF0. assumption. } clear WF0.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (OD : o / 8 * 8 = o /\ (E - SCRD) / 8 <= o / 8 /\ 0 <= (E - SCRD) / 8 /\ (ahl_ceil ar) / 8 <= o / 8 /\ o / 8 + 4 <= 17592186044416) by (clear - O8 H1 H2 HSCR SLO SPC SPT ER; lia).
  destruct OD as (OD1 & OD2 & OD3 & OD4 & OD5).
  intros j Hj. unfold byte_at, S. rewrite EK.
  - unfold L5OMA.stksh, shadow_zero, byte_at, S in SSH. replace (o / 8 + SB + j) with ((E - SCRD) / 8 + SB + (o / 8 - (E - SCRD) / 8 + j)) by (clear; lia). apply SSH.
    set (mx := Z.max (ar_sptop ar) (ar_stack_top ar)). assert (MX : E <= mx) by (subst mx; clear - SHI; lia).
    clearbody mx. clear - Hj O8 H1 H2 MX HSCR ER. lia.
  - split. unfold SB. clear - Hj OD3 OD2 OD5; lia. split. 2: apply NW; exact Hj.
    right; right; right; right; left. unfold in_shadow_of, S. replace (ahl_ceil ar + (2 ^ 47 - ahl_ceil ar) - 1) with (2 ^ 47 - 1) by (clear; lia). change ((2 ^ 47 - 1) / 8) with 17592186044415.
    clear - Hj OD4 OD5. lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma copy_stage_sd (fx : FPState) Rc Mc modelc W BX LKc crc Ac k k' pcn fbo b' ws' :
  binv W BX Mc modelc LKc crc Ac -> rinvD R E Rc ->
  getr Rc (reg 10) = Z_to_bv 64 (SPA + k) -> getr Rc (reg 11) = Z_to_bv 64 (F + k') -> getr Rc (reg 1) = Z_to_bv 64 pcn -> L5.ra_ok pcn ->
  168 <= k -> k + 32 <= 248 -> k mod 8 = 0 -> 32 <= k' -> k' + 32 <= 504 -> k' mod 8 = 0 ->
  L5.u8_at RSEGS Mc (SPA + k) fbo -> 0 <= fbo < 256 -> shadow_zero Mc (SPA + k) 4 ->
  tob (BX ++ LB) Mc (F + k') b' ws' ->
  (L5.bo_dyn b' = true -> 8 * L5.bo_cap b' <= 2 ^ 27 /\ acredit_ok L crc (8 * L5.bo_cap b')) ->
  (forall (fx' : FPState) R' M' model' (g : growth) LBn cr' LK' A',
      copy_post L ar (BX ++ LB) FF' LK' crc Mc M' Rc R' (SPA + k) (F + k') SPA fbo b' ws' g LBn cr' ->
      binv W (match g with Same => BX | Grown q cap => (q, 8 * cap) :: BX end) M' model' LK' cr' A' ->
      incl Ac A' -> incl LK' LKc ->
      srealizes RSEGS SCFG (cfg (fx:=fx') R' pcn M' model') K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc COPYA Mc modelc) K.
Proof.
  intros BI RI X10 X11 X1 RAn K1 K2 K8 K1' K2' K8' DFB FBR DSZ (OB' & OL' & SZ' & INB') CAP KF.
  pose proof BI as (B1 & B2 & B3 & B4 & B5 & B6 & _).
  edestruct L5ADVEA.callee_pre with (SCRc := COPY_SCR) as (STKc & ROOMc & RSc & A32c); [exact HIok | exact EA | exact FFR1 | exact FFRS | exact BI | vm_compute; discriminate | clear - HSCR; change COPY_SCR with 4256; lia | ].
  pose proof (NUM L ar HI R LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER) as ((FRG & FLRG & ERG) & FRP & FLRP & ALF & FBIG & FLBIG & FLA & SFA & SFLA & SFB).
  pose proof G as G'. destruct G' as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG' F32 FLA' FLR FLBIG' NCF NCS].
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (SHB : 0 <= F / 8 /\ F / 8 + 64 <= 17592186044416) by (clear - FRP; lia).
  assert (O8 : (SPA + k) mod 8 = 0) by (clear - EA K8; unfold aligned in EA; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  pose proof RI as (Z2 & _ & _ & _ & Z4).
  assert (WAV : forall rr a, In rr [(SPA + k, 32)] -> L5.in_rng rr a -> ~ docell E a /\ ~ (F / 8 + SB <= a < F / 8 + SB + ff_bytes 3 / 8)).
  { intros rr a [Hr|[]] IR; subst rr; unfold L5.in_rng in IR; cbn [fst snd] in IR. split. unfold docell. clear - IR K1 K2; lia.
    change (ff_bytes 3 / 8) with 64. unfold SB. clear - IR K1 K2 SHB ER. lia. }
  assert (WOUT : forall a, aclient L ar LB FF E SCRD a -> L5.outside W a -> L5.outside [(SPA + k, 32)] a).
  { intros a Hc _ rr [Hr|[]] IR. subst rr. unfold L5.in_rng in IR; cbn [fst snd] in IR. apply (NCS a). clear - IR K1 K2; lia. exact Hc. }
  apply (Hcps fx Rc Mc modelc K (BX ++ LB) FF' LKc crc Ac (SPA + k) (F + k') SPA pcn fbo b' ws' B1 B2 HK).
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
  - split. clear - K1; lia. split. clear - K2 SHI; lia. exact O8.
  - eapply astk_defined. exact B6. clear - K1 HSCR; lia. clear - K2; lia.
  - exact DSZ.
  - exact OB'.
  - exact OL'.
  - eapply L5ADVEA.loc_aobj; [exact G | exact K1' | exact K2' | exact K8'].
  - exact SZ'.
  - exact INB'.
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
Lemma frm_vis W BX Mc modelc LKc crc Ac a v : binv W BX Mc modelc LKc crc Ac -> L5.u64_at RSEGS Mc a v -> SPA <= a -> a + 8 <= E -> L5.u64_at RSEGS (mrestrict (ahid Ac modelc) Mc) a v.
Proof.
  intros BI Hc H1 H2. open_ctx BI.
  apply (proj2 (u64_at_vis (ahid Ac modelc) Mc a v ltac:(eapply avis_sub; [exact SV | clear - H1; lia | clear - H2; lia]) ltac:(clear - H1 ER; lia) ltac:(clear - H2 ER; lia))). exact Hc.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma g1 (fx : FPState) Rc Mc modelc W BX LKc crc Ac fbo bn wn :
  binv W BX Mc modelc LKc crc Ac -> rinvD R E Rc -> L5.u64_at RSEGS Mc (E - 272) (F + 96) ->
  L5.u8_at RSEGS Mc (SPA + 216) fbo -> 0 <= fbo < 256 -> shadow_zero Mc (SPA + 216) 4 ->
  tob (BX ++ LB) Mc (F + 96) bn wn ->
  (L5.bo_dyn bn = true -> 8 * L5.bo_cap bn <= 2 ^ 27 /\ acredit_ok L crc (8 * L5.bo_cap bn)) ->
  (forall (fx' : FPState) R1 R' M' model' (g : growth) LBn cr' LK' A',
      (forall x, In x KS_v5G1 -> getr R1 (reg x) = getr Rc (reg x)) -> getr R1 (reg 20) = Z_to_bv 64 (F + 96) ->
      copy_post L ar (BX ++ LB) FF' LK' crc Mc M' R1 R' (SPA + 216) (F + 96) SPA fbo bn wn g LBn cr' ->
      binv W (match g with Same => BX | Grown q cap => (q, 8 * cap) :: BX end) M' model' LK' cr' A' ->
      incl Ac A' -> incl LK' LKc ->
      srealizes RSEGS SCFG (cfg (fx:=fx') R' 0x926ec M' model') K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc 0x926d8 Mc modelc) K.
Proof.
  intros BI RI S80 DFB FBR DSZ TN CAP KF.
  pose proof (frm_vis W BX Mc modelc LKc crc Ac _ _ BI S80 ltac:(clear; lia) ltac:(clear; lia)) as S80v.
  open_ctx BI. pose proof BI as (B1 & B2 & _). pose proof RI as (X2 & X8 & X9 & X3 & X4).
  set (MV := mrestrict (ahid Ac modelc) Mc) in *.
  assert (ER' : 140735332487584 <= E <= 140737488355328) by (clear - ER; lia).
  assert (FR' : 4096 <= F <= 140737488354816) by (clear - FRP; lia).
  pose proof (v5G1_conc fx Rc MV (fun j => match j with 2%nat => E | 40%nat => F | 58%nat => U Rc 1 | _ => 0 end)) as P. cbn beta iota in P.
  feed P ltac:(first [apply UR | apply U_to | sc ]).
  destruct P as (fx1 & R1 & M1v & _ & _ & pEQ & (pMS & pKS & pR1 & pR10 & pR11 & _ & pR20)).
  assert (EQM : M1v = MV) by (apply mem_eq_of_agree; exact pEQ). rewrite EQM in pMS.
  apply (apure L ar C HI LY HIok (BX ++ LB) FF' LKc crc Ac Mc modelc fx fx1 Rc 0x926d8 R1 COPYA K B1 B2 pMS).
  intros model1 HH1 AM1 RT1 AH1.
  pose proof (L5AFK.binv_model L ar HI M model LB FF LK A E SCRD SPA (down E F ro R) F 3 W BX Mc modelc LKc crc Ac model1 BI HH1 AM1 RT1) as BI1.
  apply (copy_stage_sd fx1 R1 Mc model1 W BX LKc crc Ac 216 96 0x926ec fbo bn wn BI1).
  - apply (rinvD_ks R E Rc R1 KS_v5G1 RI pKS). vm_compute; reflexivity.
  - rewrite pR10. f_equal. clear; lia.
  - exact pR11.
  - exact pR1.
  - split. clear; lia. reflexivity.
  - clear; lia.
  - clear; lia.
  - reflexivity.
  - clear; lia.
  - clear; lia.
  - reflexivity.
  - exact DFB.
  - exact FBR.
  - exact DSZ.
  - exact TN.
  - exact CAP.
  - intros fx3 R3 M3 model3 g LBn cr3 LK3 A3 POST BI3 IA3 ILK3. apply (KF fx3 R1 R3 M3 model3 g LBn cr3 LK3 A3 pKS pR20 POST BI3 IA3 ILK3).
Qed.

Lemma g2 (fx : FPState) Rc Mc modelc W BX LKc crc Ac fbo bd wd :
  binv W BX Mc modelc LKc crc Ac -> rinvD R E Rc -> L5.u64_at RSEGS Mc (E - 264) (F + 32) ->
  L5.u8_at RSEGS Mc (SPA + 184) fbo -> 0 <= fbo < 256 -> shadow_zero Mc (SPA + 184) 4 ->
  tob (BX ++ LB) Mc (F + 32) bd wd ->
  (L5.bo_dyn bd = true -> 8 * L5.bo_cap bd <= 2 ^ 27 /\ acredit_ok L crc (8 * L5.bo_cap bd)) ->
  (forall (fx' : FPState) R1 R' M' model' (g : growth) LBn cr' LK' A',
      (forall x, In x KS_v5G2 -> getr R1 (reg x) = getr Rc (reg x)) -> getr R1 (reg 19) = Z_to_bv 64 (F + 32) ->
      copy_post L ar (BX ++ LB) FF' LK' crc Mc M' R1 R' (SPA + 184) (F + 32) SPA fbo bd wd g LBn cr' ->
      binv W (match g with Same => BX | Grown q cap => (q, 8 * cap) :: BX end) M' model' LK' cr' A' ->
      incl Ac A' -> incl LK' LKc ->
      srealizes RSEGS SCFG (cfg (fx:=fx') R' 0x92700 M' model') K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc 0x926ec Mc modelc) K.
Proof.
  intros BI RI S88 DFB FBR DSZ TD CAP KF.
  pose proof (frm_vis W BX Mc modelc LKc crc Ac _ _ BI S88 ltac:(clear; lia) ltac:(clear; lia)) as S88v.
  open_ctx BI. pose proof BI as (B1 & B2 & _). pose proof RI as (X2 & X8 & X9 & X3 & X4).
  set (MV := mrestrict (ahid Ac modelc) Mc) in *.
  assert (ER' : 140735332487584 <= E <= 140737488355328) by (clear - ER; lia).
  assert (FR' : 4096 <= F <= 140737488354816) by (clear - FRP; lia).
  pose proof (v5G2_conc fx Rc MV (fun j => match j with 2%nat => E | 40%nat => F | 58%nat => U Rc 1 | _ => 0 end)) as P. cbn beta iota in P.
  feed P ltac:(first [apply UR | apply U_to | sc ]).
  destruct P as (fx1 & R1 & M1v & _ & _ & pEQ & (pMS & pKS & pR1 & pR10 & pR11 & _ & pR19)).
  assert (EQM : M1v = MV) by (apply mem_eq_of_agree; exact pEQ). rewrite EQM in pMS.
  apply (apure L ar C HI LY HIok (BX ++ LB) FF' LKc crc Ac Mc modelc fx fx1 Rc 0x926ec R1 COPYA K B1 B2 pMS).
  intros model1 HH1 AM1 RT1 AH1.
  pose proof (L5AFK.binv_model L ar HI M model LB FF LK A E SCRD SPA (down E F ro R) F 3 W BX Mc modelc LKc crc Ac model1 BI HH1 AM1 RT1) as BI1.
  apply (copy_stage_sd fx1 R1 Mc model1 W BX LKc crc Ac 184 32 0x92700 fbo bd wd BI1).
  - apply (rinvD_ks R E Rc R1 KS_v5G2 RI pKS). vm_compute; reflexivity.
  - rewrite pR10. f_equal. clear; lia.
  - exact pR11.
  - exact pR1.
  - split. clear; lia. reflexivity.
  - clear; lia.
  - clear; lia.
  - reflexivity.
  - clear; lia.
  - clear; lia.
  - reflexivity.
  - exact DFB.
  - exact FBR.
  - exact DSZ.
  - exact TD.
  - exact CAP.
  - intros fx3 R3 M3 model3 g LBn cr3 LK3 A3 POST BI3 IA3 ILK3. apply (KF fx3 R1 R3 M3 model3 g LBn cr3 LK3 A3 pKS pR19 POST BI3 IA3 ILK3).
Qed.

(* [comment removed for export] *)
Lemma bx_not_client W BX Mc modelc LKc crc Ac q n a : binv W BX Mc modelc LKc crc Ac -> In (q, n) BX -> q <= a < q + n -> ~ aclient L ar LB FF E SCRD a.
Proof.
  intros (B1 & _) IN Ha Hc.
  destruct G as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG' F32 FLA' FLR FLBIG' NCF NCS].
  pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ B1) as WF0.
  assert (ND : NoDup (map fst (BX ++ LB))). { clear - WF0. decompose [and] WF0. assumption. }
  destruct WF0 as (WB & _).
  pose proof (WB (q, n) ltac:(apply in_or_app; left; exact IN)) as (BR & _ & _ & _ & BA & FA & _). cbn [fst snd] in BR, BA, FA.
  apply (fresh_block_not_client L ar C HI LY HIok LB FF' LK2 cr2 A M2 (vml_of model2) E SCRD q n a HH2 SPT BR).
  - intros b Hb. apply BA. apply in_lb_remove. apply in_or_app; right; exact Hb.
    intros Eq. apply (nodup_app_fst BX LB (q, n) b ND IN Hb). cbn [fst]. symmetry. exact Eq.
  - intros f Hf. apply FA. apply in_or_app; left; exact Hf.
  - exact Ha.
  - apply aclient_cons. exact Hc.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma g3 (fx : FPState) Rc Mc modelc W BX LKc crc Ac to bd wd bn wn :
  binv W BX Mc modelc LKc crc Ac -> rinvD R E Rc ->
  getr Rc (reg 19) = Z_to_bv 64 (F + 32) -> getr Rc (reg 20) = Z_to_bv 64 (F + 96) -> getr Rc (reg 24) = Z_to_bv 64 to -> 0 <= to < 2 ^ 64 -> 0 <= ro < 2 ^ 64 ->
  shadow_zero Mc (E - 172) 1 ->
  tob (BX ++ LB) Mc (F + 32) bd wd -> tob (BX ++ LB) Mc (F + 96) bn wn ->
  (forall cap q, L5.bo_st bd = L5.BDyn cap q -> In (q, 8 * cap) BX) -> (forall cap q, L5.bo_st bn = L5.BDyn cap q -> In (q, 8 * cap) BX) ->
  (1 <= L5.bo_len bd <= 290)%nat -> nth_w wd (L5.bo_len bd - 1) <> 0 -> ((2 <= L5.bo_len bd)%nat -> nth_w wd (L5.bo_len bd - 1) < 2 ^ 63) ->
  (1 <= L5.bo_len bn <= 290)%nat -> ((2 <= L5.bo_len bd)%nat -> (2 <= L5.bo_len bn)%nat /\ exists i, (i < L5.bo_len bn)%nat /\ nth_w wn i <> 0) ->
  (forall cap q, L5.bo_st bd = L5.BDyn cap q -> Z.of_nat (L5.bo_len bd) + 1 <= cap) ->
  (forall cap q, L5.bo_st bn = L5.BDyn cap q -> Z.of_nat (L5.bo_len bn) + 1 <= cap) ->
  (L5DLA.second (L5.bo_len bd) (L5DLA.shl_result wd (L5DLA.clz_of (nth_w wd (L5.bo_len bd - 1)))) = true ->
     (L5.bo_dyn bd = true -> Z.of_nat (L5.bo_len bd) + 2 <= L5.bo_cap bd) /\ (L5.bo_dyn bn = true -> Z.of_nat (L5.bo_len bn) + 2 <= L5.bo_cap bn)) ->
  (forall cd qd cn qn, L5.bo_st bd = L5.BDyn cd qd -> L5.bo_st bn = L5.BDyn cn qn -> qd + 8 * cd <= qn \/ qn + 8 * cn <= qd) ->
  L5DLA.acredits L crc (L5DLA.cnt bd + L5DLA.cnt bn) ->
  (forall (fx' : FPState) R1 R' M1 M' model' (c : Z) (gd gn : growth) LBn cr' LK' A',
      (forall x, In x KS_v5G3 -> getr R1 (reg x) = getr Rc (reg x)) -> getr R1 (reg 23) = Z_to_bv 64 ro ->
      (forall a, 0 <= a < 2 ^ 64 -> ~ (E - 172 <= a < E - 168) -> M1 (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)) ->
      L5DLA.norm_postA L ar (BX ++ LB) FF' LK' crc M1 M' R1 R' (F + 32) (F + 96) (E - 172) SPA bd bn wd wn c gd gn LBn cr' ->
      binv W (L5DLA.blocks_of gn ++ L5DLA.blocks_of gd ++ BX) M' model' LK' cr' A' ->
      incl Ac A' -> incl LK' LKc ->
      srealizes RSEGS SCFG (cfg (fx:=fx') R' 0x9271c M' model') K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc 0x92700 Mc modelc) K.
Proof.
  intros BI RI X19 X20 X24 TOR RORG SZP TD TN BXD BXN LD TOPNZ TOPSM LN NN2 CAPD CAPN SECC APB CR KF.
  open_ctx BI. pose proof RI as (X2 & X8 & X9 & X3 & X4).
  pose proof G as G'. destruct G' as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG' F32 FLA' FLR FLBIG' NCF NCS]. change (ff_bytes 3) with 512 in *.
  set (MV := mrestrict (ahid Ac modelc) Mc) in *.
  assert (ER' : 140735332487584 <= E <= 140737488355328) by (clear - ER; lia).
  assert (FR' : 4096 <= F <= 140737488354816) by (clear - FRP; lia).
  destruct OWNv as (_ & _ & OW96 & _).
  assert (ROR : 0 <= U R 1 < 2 ^ 64) by apply UR.
  (* [comment removed for export] *)
  pose proof (v5G3_conc fx Rc MV (fun j => match j with 2%nat => E | 33%nat => to | 36%nat => ro | 40%nat => F | 58%nat => U Rc 1 | _ => 0 end)) as P. cbn beta iota in P.
  feed P ltac:(first [apply UR | apply U_to | sc ]).
  destruct P as (fx1 & R1 & M1v & MG1 & _ & pFZ & (pMS & pKS & pR1 & pR10 & pR11 & pR12 & pR13 & pR23 & pX0)).
  set (Wp := fun a => E - 172 <= a < E - 168).
  apply (L5DKA.bstage L ar C HI LY HIok M model LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2 G W _ Mc modelc LKc crc Ac fx fx1 Rc 0x92700 R1 0x932a0 M1v Wp K BI pMS MG1).
  { intros a Ha Hn. apply pFZ. exact Ha. subst Wp; cbn beta in Hn. clear - Hn; lia. }
  { intros a Ha Wa. subst Wp; cbn beta in Wa. apply (L5DKA.wp_frame L ar HI LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2 G). clear - Wa; lia. unfold docell. clear - Wa; lia. }
  intros M1 model1 BI1 AH1 VIS1 MGM1 FRM1.
  pose proof BI as (B1 & _). pose proof BI1 as (C1 & C2 & _ & _ & _ & C6 & _).
  assert (OFF1 : offx (BX ++ LB) 0 Wp Mc M1). { intros a Ha _ NX. apply FRM1. exact Ha. exact NX. }
  assert (AOD' : aobj FF' (F + 32) 32) by (eapply L5ADVEA.loc_aobj; [exact G | clear; lia | clear; lia | reflexivity]).
  assert (AON' : aobj FF' (F + 96) 32) by (eapply L5ADVEA.loc_aobj; [exact G | clear; lia | clear; lia | reflexivity]).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (SHB : 0 <= F / 8 /\ F / 8 + 64 <= 17592186044416 /\ (F + 32) / 8 = F / 8 + 4 /\ (F + 96) / 8 = F / 8 + 12 /\ (E - 172) mod 4 = 0 /\ (E - 172) / 8 <= 17592186044415 /\ 0 <= (E - 172) / 8)
    by (clear - FRP ALF EA ER; unfold aligned in *; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  destruct SHB as (SHB0 & SHB1 & SHB2 & SHB3 & PX4 & PXD & PXD0).
  assert (NXL : forall k (b : L5.bigobj), (k = 32 \/ k = 96) -> (forall cap q, L5.bo_st b = L5.BDyn cap q -> In (q, 8 * cap) (BX ++ LB)) -> forall a, L5ADVEA.oreg (F + k) b a -> ~ Wp a).
  { intros k b Hkk INB a OR. subst Wp; cbn beta. destruct OR as [OR|[OR|(cap & q & Eq & OR)]].
    - clear - OR Hkk SFB; lia.
    - unfold SB in OR. clear - OR Hkk SHB0 SHB1 SHB2 SHB3 ER. destruct Hkk as [-> | ->]; [rewrite SHB2 in OR | rewrite SHB3 in OR]; lia.
    - pose proof (L5ADVEA.blk_avoid L ar C HI HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G HSCR W BX Mc modelc LKc crc Ac q (8 * cap) a BI (INB cap q Eq) OR) as (_ & _ & Y3). clear - Y3. lia. }
  assert (TD1 : tob (BX ++ LB) M1 (F + 32) bd wd).
  { apply (L5ADVEA.tob_keep' L ar C HI LY HIok FF E F (BX ++ LB) (BX ++ LB) (BX ++ LB) LKc crc Ac modelc 0 Wp Mc M1 (F + 32) bd wd B1 AOD' TD OFF1).
    intros cap q Eq. split; apply (proj2 (proj2 (proj2 TD)) cap q Eq). apply (NXL 32 bd (or_introl eq_refl) (proj2 (proj2 (proj2 TD)))). }
  assert (TN1 : tob (BX ++ LB) M1 (F + 96) bn wn).
  { apply (L5ADVEA.tob_keep' L ar C HI LY HIok FF E F (BX ++ LB) (BX ++ LB) (BX ++ LB) LKc crc Ac modelc 0 Wp Mc M1 (F + 96) bn wn B1 AON' TN OFF1).
    intros cap q Eq. split; apply (proj2 (proj2 (proj2 TN)) cap q Eq). apply (NXL 96 bn (or_intror eq_refl) (proj2 (proj2 (proj2 TN)))). }
  assert (SZP1 : shadow_zero M1 (E - 172) 1).
  { intros j Hj. unfold byte_at. rewrite FRM1. exact (SZP j Hj). unfold S, SB. clear - Hj PXD PXD0; lia. subst Wp; cbn beta. unfold S, SB. clear - Hj PXD ER; lia. }
  destruct TD1 as (OBD1 & OLD1 & SZD1 & IND1). destruct TN1 as (OBN1 & OLN1 & SZN1 & INN1).
  (* [comment removed for export] *)
  edestruct L5ADVEA.callee_pre with (SCRc := L5DLA.NORM_SCR) as (STKc & ROOMc & RSc & A32c); [exact HIok | exact EA | exact FFR1 | exact FFRS | exact BI1 | vm_compute; discriminate | clear - HSCR; change L5DLA.NORM_SCR with 4656; lia | ].
  assert (RI1 : rinvD R E R1). { apply (rinvD_ks R E Rc R1 KS_v5G3 RI pKS). vm_compute; reflexivity. }
  pose proof RI1 as (Z2 & _ & _ & _ & Z4).
  assert (WAV : forall rr a, In rr (L5DLA.norm_W (F + 32) (F + 96) (E - 172) bd bn) -> L5.in_rng rr a -> ~ docell E a /\ ~ (F / 8 + SB <= a < F / 8 + SB + ff_bytes 3 / 8)).
  { intros rr a Hr IR. change (ff_bytes 3 / 8) with 64. unfold L5DLA.norm_W in Hr. cbn [app In] in Hr. unfold L5.in_rng in IR.
    destruct Hr as [Hr|[Hr|[Hr|Hr]]]; try (subst rr; cbn [fst snd] in IR).
    - split. unfold docell. clear - IR SFB; lia. unfold SB. clear - IR SHB0 SHB1 FBIG FRP; lia.
    - split. unfold docell. clear - IR SFB; lia. unfold SB. clear - IR SHB0 SHB1 FBIG FRP; lia.
    - split. unfold docell. clear - IR; lia. unfold SB. clear - IR SHB0 SHB1 ER; lia.
    - apply in_app_or in Hr. unfold L5DLA.dyn_area in Hr. destruct Hr as [Hr|Hr].
      + destruct (L5.bo_st bd) as [v0 v1|cap q] eqn:Eq; [destruct Hr|]. destruct Hr as [Hr|[]]. subst rr; cbn [fst snd] in IR.
        pose proof (L5ADVEA.blk_avoid L ar C HI HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G HSCR W BX Mc modelc LKc crc Ac q (8 * cap) a BI (IND1 cap q eq_refl) IR) as (Y1 & Y2 & _).
        split. exact Y1. exact Y2.
      + destruct (L5.bo_st bn) as [v0 v1|cap q] eqn:Eq; [destruct Hr|]. destruct Hr as [Hr|[]]. subst rr; cbn [fst snd] in IR.
        pose proof (L5ADVEA.blk_avoid L ar C HI HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G HSCR W BX Mc modelc LKc crc Ac q (8 * cap) a BI (INN1 cap q eq_refl) IR) as (Y1 & Y2 & _).
        split. exact Y1. exact Y2. }
  assert (WOUT : forall a, aclient L ar LB FF E SCRD a -> L5.outside W a -> L5.outside (L5DLA.norm_W (F + 32) (F + 96) (E - 172) bd bn) a).
  { intros a Hc _ rr Hr IR. unfold L5DLA.norm_W in Hr. cbn [app In] in Hr. unfold L5.in_rng in IR.
    destruct Hr as [Hr|[Hr|[Hr|Hr]]]; try (subst rr; cbn [fst snd] in IR).
    - apply (NCF a). left. clear - IR; lia. exact Hc.
    - apply (NCF a). left. clear - IR; lia. exact Hc.
    - apply (NCS a). clear - IR; lia. exact Hc.
    - apply in_app_or in Hr. unfold L5DLA.dyn_area in Hr. destruct Hr as [Hr|Hr].
      + destruct (L5.bo_st bd) as [v0 v1|cap q] eqn:Eq; [destruct Hr|]. destruct Hr as [Hr|[]]. subst rr; cbn [fst snd] in IR.
        exact (bx_not_client W BX Mc modelc LKc crc Ac q (8 * cap) a BI (BXD cap q eq_refl) IR Hc).
      + destruct (L5.bo_st bn) as [v0 v1|cap q] eqn:Eq; [destruct Hr|]. destruct Hr as [Hr|[]]. subst rr; cbn [fst snd] in IR.
        exact (bx_not_client W BX Mc modelc LKc crc Ac q (8 * cap) a BI (BXN cap q eq_refl) IR Hc). }
  apply (Hnorm fx1 R1 M1 model1 K (BX ++ LB) FF' LKc crc Ac (F + 32) (F + 96) (E - 172) SPA 0x9271c bd bn wd wn C1 C2 HK).
  - rewrite r11. exact pR11.
  - rewrite r12. exact pR12.
  - rewrite r13. exact pR13.
  - rewrite r1. exact pR1.
  - split. clear; lia. reflexivity.
  - rewrite r2. exact Z2.
  - exact A32c.
  - rewrite r4, Z4. rewrite <- G4. reflexivity.
  - exact STKc.
  - apply (ffrk_le 1 FF' LKc 4 4 ROOMc). clear; lia.
  - exact RSc.
  - exact OBD1.
  - exact OLD1.
  - exact LD.
  - exact TOPNZ.
  - exact TOPSM.
  - exact OBN1.
  - exact OLN1.
  - exact LN.
  - exact NN2.
  - exact AOD'.
  - exact SZD1.
  - exact AON'.
  - exact SZN1.
  - clear; lia.
  - exact PX4.
  - clear; lia.
  - eapply astk_defined. exact C6. clear - HSCR; lia. clear; lia.
  - clear - SHI; lia.
  - exact SZP1.
  - intros cap q Eq. split. exact (IND1 cap q Eq). exact (CAPD cap q Eq).
  - intros cap q Eq. split. exact (INN1 cap q Eq). exact (CAPN cap q Eq).
  - exact SECC.
  - exact APB.
  - exact CR.
  - intros fx3 R3 M3 model3 c gd gn LBn cr3 LK3 A3 POST RT3 IA3 AM3 ILK3 HH3.
    pose proof POST as (_ & _ & _ & _ & _ & _ & _ & ELB & _ & _ & _ & AH3 & _). subst LBn.
    assert (BI3 : binv W (L5DLA.blocks_of gn ++ L5DLA.blocks_of gd ++ BX) M3 model3 LK3 cr3 A3).
    { apply (L5AFK.binv_callee L ar C HI HIok M model LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2 G
               W W BX BX (L5DLA.blocks_of gn ++ L5DLA.blocks_of gd ++ BX) M1 model1 LKc crc Ac M3 model3 LK3 cr3 A3 L5DLA.NORM_SCR _ BI1 AH3).
      - rewrite <- !app_assoc. exact HH3.
      - exact AM3.
      - exact RT3.
      - exact IA3.
      - exact ILK3.
      - vm_compute; discriminate.
      - clear - HSCR; change L5DLA.NORM_SCR with 4656; lia.
      - exact WAV.
      - exact WOUT.
      - intros a X. exact X. }
    apply (KF fx3 R1 R3 M1 M3 model3 c gd gn _ cr3 LK3 A3 pKS pR23 FRM1 POST BI3 IA3 ILK3).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma g4 (fx : FPState) Rc Mc modelc W BX LKc crc Ac sd qo (bd : L5.bigobj) lenn :
  binv W BX Mc modelc LKc crc Ac -> rinvD R E Rc ->
  getr Rc (reg 10) = Z_to_bv 64 sd -> getr Rc (reg 19) = Z_to_bv 64 (F + 32) -> getr Rc (reg 20) = Z_to_bv 64 (F + 96) -> getr Rc (reg 22) = Z_to_bv 64 qo ->
  0 <= sd < 2 ^ 64 -> 0 <= qo < 2 ^ 64 ->
  L5.big_at RSEGS Mc (F + 32) bd -> L5.u64_at RSEGS Mc (F + 104) lenn -> 0 <= lenn < 2 ^ 64 ->
  (forall (fx1 : FPState) R1 M1 model1,
      binv W BX M1 model1 LKc crc Ac -> rinvD R E R1 ->
      (forall x, In x [3; 4; 18; 19; 20; 22; 23; 24; 25; 26]%nat -> getr R1 (reg x) = getr Rc (reg x)) ->
      getr R1 (reg 1) = Z_to_bv 64 0x92758 -> getr R1 (reg 10) = Z_to_bv 64 qo -> getr R1 (reg 11) = Z_to_bv 64 (lenn - Z.of_nat (L5.bo_len bd)) ->
      getr R1 (reg 21) = Z_to_bv 64 2147450880 -> getr R1 (reg 27) = Z_to_bv 64 lenn ->
      (forall a, 0 <= a < 2 ^ 64 -> ~ (E - 336 <= a < E - 328) -> ~ (E - 224 <= a < E - 208) -> M1 (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)) ->
      L5.u64_at RSEGS M1 (E - 336) sd -> L5.u64_at RSEGS M1 (E - 224) (L5.bo_data (F + 32) bd) -> L5.u64_at RSEGS M1 (E - 216) (Z.of_nat (L5.bo_len bd)) ->
      srealizes RSEGS SCFG (cfg (fx:=fx1) R1 RESIZE M1 model1) K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc 0x9271c Mc modelc) K.
Proof.
  intros BI RI X10 X19 X20 X22 SDR QOR OBD NLEN NLR KF.
  open_ctx BI. pose proof RI as (X2 & X8 & X9 & X3 & X4).
  set (MV := mrestrict (ahid Ac modelc) Mc) in *.
  assert (ER' : 140735332487584 <= E <= 140737488355328) by (clear - ER; lia).
  assert (FR' : 4096 <= F <= 140737488354816 /\ 4096 <= fl <= 140737488355327) by (clear - FRP FLRP; lia). destruct FR' as [FR' FLR'].
  destruct OWNv as (_ & _ & _ & _ & OW152 & _).
  assert (CELLV : forall a v, F <= a -> a + 8 <= F + 512 -> L5.u64_at RSEGS Mc a v -> L5.u64_at RSEGS MV a v).
  { intros a v H1 H2 Hc. apply (proj2 (u64_at_vis (ahid Ac modelc) Mc a v ltac:(eapply avis_sub; [exact FV | clear - H1; lia | clear - H2; lia]) ltac:(clear - H1 FRP; lia) ltac:(clear - H2 FRP; lia))). exact Hc. }
  assert (CELL1 : forall a v, F <= a -> a + 1 <= F + 512 -> L5.u8_at RSEGS Mc a v -> L5.u8_at RSEGS MV a v).
  { intros a v H1 H2 Hc. apply (proj2 (u8_at_vis (ahid Ac modelc) Mc a v ltac:(eapply avis_sub; [exact FV | clear - H1; lia | clear - H2; lia]) ltac:(clear - H1 FRP; lia) ltac:(clear - H2 FRP; lia))). exact Hc. }
  pose proof (CELLV (F + 104) lenn ltac:(clear; lia) ltac:(clear; lia) NLEN) as NLENv.
  destruct bd as [fb len sto]. destruct OBD as (O0 & FBR & O8 & OST). cbn [L5.bo_fb L5.bo_len L5.bo_st] in *.
  pose proof (CELL1 (F + 32) fb ltac:(clear; lia) ltac:(clear; lia) O0) as O0v. pose proof (CELLV (F + 32 + 8) (Z.of_nat len) ltac:(clear; lia) ltac:(clear; lia) O8) as O8v.
  replace (F + 32 + 8) with (F + 40) in O8v by (clear; lia).
  assert (LR : 0 <= Z.of_nat len < 2 ^ 64 /\ 0 <= fb <= 255).
  { split. 2: clear - FBR; lia. destruct sto; [destruct OST as (_ & _ & _ & X) | destruct OST as (_ & _ & _ & X)]; clear - X; lia. }
  destruct LR as [LR FBR'].
  set (Wp := fun a => E - 336 <= a < E - 328 \/ E - 224 <= a < E - 208).
  assert (WPOK : forall a, 0 <= a < 2 ^ 64 -> Wp a -> L5DKA.wp_ok L ar LB FF E SCRD SPA (docell E) F 3 W BX a).
  { intros a Ha Wa. subst Wp; cbn beta in Wa. apply (L5DKA.wp_frame L ar HI LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2 G). clear - Wa; lia. unfold docell. clear - Wa; lia. }
  destruct sto as [v0 v1|cap q].
  - (* [comment removed for export] *)
    destruct OST as (BT0 & _).
    pose proof (v5G4i_conc fx Rc MV (fun j => match j with 2%nat => E | 35%nat => qo | 40%nat => F | 41%nat => fl | 55%nat => fb | 58%nat => U Rc 1 | 63%nat => sd | 64%nat => Z.of_nat len | 66%nat => lenn | _ => 0 end)) as P. cbn beta iota in P.
    feed P ltac:(first [apply UR | apply U_to | sc ]).
    destruct P as (fx1 & R1 & M1v & MG1 & _ & pFZ & (pMS & pKS & pR1 & pR10 & pR11 & pR21 & pR27 & p136 & p128 & p16)).
    apply (L5DKA.bstage L ar C HI LY HIok M model LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2 G W _ Mc modelc LKc crc Ac fx fx1 Rc 0x9271c R1 RESIZE M1v Wp K BI pMS MG1).
    { intros a Ha Hn. apply pFZ. exact Ha. all: subst Wp; cbn beta in Hn; clear - Hn; lia. }
    { exact WPOK. }
    intros M1 model1 BI1 AH1 VIS1 MGM1 FRM1.
    assert (XS : forall a v, SPA <= a -> a + 8 <= E -> L5.u64_at RSEGS M1v a v -> L5.u64_at RSEGS M1 a v).
    { intros a v Ha Hb Hc. apply (proj1 (u64_at_vis (ahid Ac modelc) M1 a v ltac:(eapply avis_sub; [exact SV | clear - Ha; lia | clear - Hb; lia]) ltac:(clear - Ha ER; lia) ltac:(clear - Hb ER; lia))). rewrite VIS1. exact Hc. }
    apply (KF fx1 R1 M1 model1 BI1).
    + apply (rinvD_ks R E Rc R1 KS_v5G4i RI pKS). vm_compute; reflexivity.
    + intros x Hx. apply pKS. revert Hx. apply (L5K.incl_b [3; 4; 18; 19; 20; 22; 23; 24; 25; 26]%nat). vm_compute; reflexivity.
    + exact pR1.
    + exact pR10.
    + rewrite pR11. f_equal. clear; lia.
    + exact pR21.
    + exact pR27.
    + intros a Ha N1 N2. apply FRM1. exact Ha. subst Wp; cbn beta. clear - N1 N2; lia.
    + apply XS. clear; lia. clear; lia. exact p16.
    + unfold L5.bo_data. cbn [L5.bo_st]. apply XS. clear; lia. clear; lia. replace (F + 32 + 16) with (F + 48) by (clear; lia). exact p128.
    + apply XS. clear; lia. clear; lia. exact p136.
  - (* [comment removed for export] *)
    destruct OST as (BT1 & O16 & O24 & _ & CAPR & _ & Q4096 & Q47 & _).
    pose proof (CELLV (F + 32 + 24) q ltac:(clear; lia) ltac:(clear; lia) O24) as O24v. replace (F + 32 + 24) with (F + 56) in O24v by (clear; lia).
    assert (QRG : 0 <= q < 2 ^ 64) by (clear - Q4096 Q47 CAPR; lia).
    pose proof (v5G4d_conc fx Rc MV (fun j => match j with 2%nat => E | 35%nat => qo | 40%nat => F | 41%nat => fl | 55%nat => fb | 58%nat => U Rc 1 | 63%nat => sd | 64%nat => Z.of_nat len | 65%nat => q | 66%nat => lenn | _ => 0 end)) as P. cbn beta iota in P.
    feed P ltac:(first [apply UR | apply U_to | sc ]).
    destruct P as (fx1 & R1 & M1v & MG1 & _ & pFZ & (pMS & pKS & pR1 & pR10 & pR11 & pR21 & pR27 & p136 & p128 & p16)).
    apply (L5DKA.bstage L ar C HI LY HIok M model LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2 G W _ Mc modelc LKc crc Ac fx fx1 Rc 0x9271c R1 RESIZE M1v Wp K BI pMS MG1).
    { intros a Ha Hn. apply pFZ. exact Ha. all: subst Wp; cbn beta in Hn; clear - Hn; lia. }
    { exact WPOK. }
    intros M1 model1 BI1 AH1 VIS1 MGM1 FRM1.
    assert (XS : forall a v, SPA <= a -> a + 8 <= E -> L5.u64_at RSEGS M1v a v -> L5.u64_at RSEGS M1 a v).
    { intros a v Ha Hb Hc. apply (proj1 (u64_at_vis (ahid Ac modelc) M1 a v ltac:(eapply avis_sub; [exact SV | clear - Ha; lia | clear - Hb; lia]) ltac:(clear - Ha ER; lia) ltac:(clear - Hb ER; lia))). rewrite VIS1. exact Hc. }
    apply (KF fx1 R1 M1 model1 BI1).
    + apply (rinvD_ks R E Rc R1 KS_v5G4d RI pKS). vm_compute; reflexivity.
    + intros x Hx. apply pKS. revert Hx. apply (L5K.incl_b [3; 4; 18; 19; 20; 22; 23; 24; 25; 26]%nat). vm_compute; reflexivity.
    + exact pR1.
    + exact pR10.
    + rewrite pR11. f_equal. clear; lia.
    + exact pR21.
    + exact pR27.
    + intros a Ha N1 N2. apply FRM1. exact Ha. subst Wp; cbn beta. clear - N1 N2; lia.
    + apply XS. clear; lia. clear; lia. exact p16.
    + unfold L5.bo_data. cbn [L5.bo_st]. apply XS. clear; lia. clear; lia. exact p128.
    + apply XS. clear; lia. clear; lia. exact p136.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma binv_memW W W1 BX Mc modelc LKc crc Ac M1 model1 (D : Z -> Prop) scr :
  binv W BX Mc modelc LKc crc Ac ->
  ri_inv HI (BX ++ LB) FF' LKc crc Ac M1 (vml_of model1) -> amodel_ok Ac model1 -> model_rt modelc model1 ->
  (forall a, 0 <= a < 2 ^ 64 -> aclient L ar (BX ++ LB) FF' SPA scr a -> ~ D a -> M1 (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)) ->
  (forall a, SPA - scr <= a < SPA -> M1 (Z_to_bv 64 a) <> None) ->
  (forall a, D a -> M1 (Z_to_bv 64 a) <> None) -> (forall a, D a \/ ~ D a) ->
  (forall a, D a -> a < ahl_ceil ar /\ ~ (F / 8 + SB <= a < F / 8 + SB + 64) /\ (aclient L ar LB FF E SCRD a -> ~ L5.outside W1 a)) ->
  (forall a, L5.outside W1 a -> L5.outside W a) ->
  E - SCRD <= SPA - scr -> 0 <= scr ->
  binv W1 BX M1 model1 LKc crc Ac.
Proof.
  pose proof G as G'. destruct G' as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG F32 FLA FLR FLBIG NCF NCS]. change (ff_bytes 3) with 512 in *. change (512 / 8) with 64 in *.
  intros (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10) HH1 AM1 RT1 PRES SDEF DDEF DDEC DIN WW HS HS0.
  change (ff_bytes 3 / 8) with 64 in *.
  assert (PRES' : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF SPA scr a -> ~ D a -> M1 (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)).
  { intros a Ha Hc ND. apply PRES. exact Ha. apply aclient_cons. apply aclient_appb. exact Hc. exact ND. }
  unfold L5AFK.binv. split. exact HH1. split. exact AM1. split. eapply L5LZ.model_rt_trans. exact B3. exact RT1. split. exact B4. split. exact B5.
  split. { apply (astk_after_eq L ar C HI HIok (BX ++ LB) FF' LKc crc Ac Mc Mc M1 _ E _ SPA scr B1 B6 (mem_grows_refl Mc)).
           - intros a Ha Hs Hns. apply PRES. exact Ha. apply stack_client. exact Hs. exact Hns. intros X. apply DIN in X. clear - X Hs; lia.
           - exact SDEF.
           - exact HS.
           - clear; lia.
           - clear - SPC; lia. }
  split. { eapply ek_trans. { apply (ek_W L ar LB FF E SCRD W1 W M Mc B7). exact WW. }
           apply (ek_mem L ar LB FF E SCRD SPA scr D W1 Mc M1 PRES').
           - exact HS.
           - clear; lia.
           - intros a Hc Ho X. exact (proj2 (proj2 (DIN a X)) Hc Ho). }
  split. { eapply dk_trans. exact B8. apply (dk_mem L ar LB FF E SCRD SPA scr D Mc M1 PRES' SDEF DDEF DDEC).
           - exact HS.
           - clear; lia. }
  split. { apply (OWNAG Mc M1 B9). intros a Ha. pose proof (OCR a Ha) as OC. apply PRES. clear - OC SPC SLO; lia. apply stack_client. clear - OC SPC SLO SHI SPT; lia. clear - OC SPC HS0; lia.
           intros X. apply DIN in X. clear - X OC SPC SLO. lia. }
  change (ff_bytes 3 / 8) with 64. intros i Hi. rewrite PRES. apply B10. exact Hi.
  - unfold SB. destruct F8 as (F8a & _). clear - Hi FR F8a. lia.
  - apply (fframe_shadow_client L ar (BX ++ LB) FF' SPA scr F 3 (SPA + 32)). left; reflexivity. unfold in_shadow_of, S. change (ff_bytes 3) with 512. rewrite (proj1 (proj2 F8)). clear - Hi. lia.
  - intros Y. apply DIN in Y. apply (proj1 (proj2 Y)). clear - Hi. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ARGF (MV : word -> option byte) (o : Z) : Prop :=
  (4096 <= o <= 140737488355296 /\ 0 <= o < 2 ^ 64 /\ o mod 8 = 0) /\ (2147446784 + 17592186048512 <= o \/ o + 32 <= 2147446784)
  /\ L5KA.zeros_at MV (o / 8 + 2147450880) 4 /\ L5.writable RSEGS MV o 32
  /\ (E - 352 + 352 <= o \/ o + 32 <= E - 352) /\ (o + 32 <= F \/ F + 512 <= o) /\ (o + 32 <= SH \/ SH + 64 <= o)
  /\ (o / 8 + 2147450880 + 4 <= F \/ F + 512 <= o / 8 + 2147450880) /\ (o / 8 + 2147450880 + 4 <= SH \/ SH + 64 <= o / 8 + 2147450880)
  /\ (o / 8 + 2147450880 + 4 <= E - 352 \/ E - 352 + 352 <= o / 8 + 2147450880).

Lemma g5_run (fx : FPState) Rc MV qo fb (len : nat) sto : rinvD R E Rc -> pf E F fl MV ->
  getr Rc (reg 21) = Z_to_bv 64 2147450880 -> getr Rc (reg 22) = Z_to_bv 64 qo -> ARGF MV qo ->
  L5.big_at RSEGS MV qo (L5.BO fb len sto) ->
  exists (fx' : FPState) R', msteps RSEGS (st fx Rc 0x92758 MV) (st fx' R' (if (Z.of_nat len =? 0) then 0x927c0 else 0x5e570) MV)
    /\ (forall x, In x [2; 3; 4; 8; 9; 19; 20; 21; 22; 23; 26; 27]%nat -> getr R' (reg x) = getr Rc (reg x))
    /\ getr R' (reg 18) = Z_to_bv 64 (qo / 8 + 2147450880) /\ getr R' (reg 24) = Z_to_bv 64 (L5.bo_data qo (L5.BO fb len sto)) /\ getr R' (reg 25) = Z_to_bv 64 (Z.of_nat len)
    /\ (Z.of_nat len <> 0 -> getr R' (reg 1) = Z_to_bv 64 0x927c0 /\ getr R' (reg 10) = Z_to_bv 64 (L5.bo_data qo (L5.BO fb len sto)) /\ getr R' (reg 11) = Z_to_bv 64 0
                              /\ getr R' (reg 12) = Z_to_bv 64 (8 * Z.of_nat len)).
Proof.
  intros RI PF X21 X22 ((ORP & ORG & O8) & OBIG & OZ & OW & OFR & OF & OSH & SOF & SOSH & SOFR) OB.
  unfold pf in PF. destruct PF as (W352 & IMGC & CSB & CUAR & FDEFv & FWv & FSHWv & FLCv & FLWv).
  pose proof (NUM L ar HI R LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER) as ((FRG & FLRG & ERG) & FRP & FLRP & ALF & FBIG & FLBIG & FLA & SFA & SFLA & SFB).
  pose proof RI as (X2 & X8 & X9 & X3 & X4).
  assert (ER' : 140735332487584 <= E <= 140737488355328) by (clear - ER; lia).
  assert (OAL : aligned qo 8) by exact O8.
  destruct OB as (O0 & FBR & OL8 & OST). cbn [L5.bo_fb L5.bo_len L5.bo_st] in *. unfold L5.bo_data. cbn [L5.bo_st].
  assert (FBR' : 0 <= fb <= 255) by (clear - FBR; lia).
  assert (LR : 0 <= Z.of_nat len <= 134217728 /\ 0 <= Z.of_nat len < 2 ^ 64).
  { destruct sto; [destruct OST as (_ & _ & _ & X & _) | destruct OST as (_ & _ & _ & X & X' & _)]; clear - X + clear - X X'; lia. }
  destruct LR as [LR LRG].
  destruct sto as [v0 v1|cap q]; destruct (Z.eqb_spec (Z.of_nat len) 0) as [L0|LN].
  - destruct OST as (BT0 & _). assert (L00 : 0 <= Z.of_nat len <= 0) by (clear - L0; lia).
    pose proof (v5G5i0_conc fx Rc MV (fun j => match j with 2%nat => E | 35%nat => qo | 40%nat => F | 58%nat => U Rc 1 | 60%nat => fb | 67%nat => Z.of_nat len | _ => 0 end)) as P. cbn beta iota in P.
    feed P ltac:(first [apply UR | apply U_to | sc ]).
    destruct P as (fx1 & R1 & M1v & _ & _ & pEQ & (pMS & pKS & p10x & PREST)).
    assert (EQM : M1v = MV) by (apply mem_eq_of_agree; exact pEQ). rewrite EQM in pMS.
    exists fx1, R1. split. exact pMS. split. { intros x Hx. apply pKS. revert Hx. apply (L5K.incl_b [2; 3; 4; 8; 9; 19; 20; 21; 22; 23; 26; 27]%nat). vm_compute; reflexivity. }
    assert (PR3 : getr R1 (reg 18) = Z_to_bv 64 (qo / 8 + 2147450880) /\ getr R1 (reg 24) = Z_to_bv 64 (qo + 16) /\ getr R1 (reg 25) = Z_to_bv 64 0) by (repeat match type of PREST with _ /\ _ => destruct PREST as [? PREST] end; repeat split; assumption).
    destruct PR3 as (p18 & p24 & p25). split. exact p18. split. exact p24. split. rewrite L0. exact p25. intros X. exfalso. exact (X L0).
  - destruct OST as (BT0 & _). assert (L1 : 1 <= Z.of_nat len <= 134217728) by (clear - LN LR; lia).
    pose proof (v5G5in_conc fx Rc MV (fun j => match j with 2%nat => E | 35%nat => qo | 40%nat => F | 58%nat => U Rc 1 | 60%nat => fb | 67%nat => Z.of_nat len | _ => 0 end)) as P. cbn beta iota in P.
    feed P ltac:(first [apply UR | apply U_to | sc ]).
    destruct P as (fx1 & R1 & M1v & _ & _ & pEQ & (pMS & pKS & p1 & p10 & p11 & p12 & p18 & p24 & p25)).
    assert (EQM : M1v = MV) by (apply mem_eq_of_agree; exact pEQ). rewrite EQM in pMS.
    exists fx1, R1. split. exact pMS. split. { intros x Hx. apply pKS. revert Hx. apply (L5K.incl_b [2; 3; 4; 8; 9; 19; 20; 21; 22; 23; 26; 27]%nat). vm_compute; reflexivity. }
    split. exact p18. split. exact p24. split. exact p25. intros _. split. exact p1. split. exact p10. split. exact p11. exact p12.
  - destruct OST as (BT1 & O16 & O24 & _ & CAPR & _ & Q4096 & Q47 & _). assert (L00 : 0 <= Z.of_nat len <= 0) by (clear - L0; lia).
    assert (QRG : 0 <= q < 2 ^ 64 /\ 0 <= q <= 18446744073709551615) by (clear - Q4096 Q47 CAPR; lia). destruct QRG as [QRG QRG'].
    replace (qo + 24) with (qo + 24) in O24 by reflexivity.
    pose proof (v5G5d0_conc fx Rc MV (fun j => match j with 2%nat => E | 35%nat => qo | 40%nat => F | 58%nat => U Rc 1 | 60%nat => fb | 67%nat => Z.of_nat len | 68%nat => q | _ => 0 end)) as P. cbn beta iota in P.
    feed P ltac:(first [apply UR | apply U_to | sc ]).
    destruct P as (fx1 & R1 & M1v & _ & _ & pEQ & (pMS & pKS & p10x & PREST)).
    assert (EQM : M1v = MV) by (apply mem_eq_of_agree; exact pEQ). rewrite EQM in pMS.
    exists fx1, R1. split. exact pMS. split. { intros x Hx. apply pKS. revert Hx. apply (L5K.incl_b [2; 3; 4; 8; 9; 19; 20; 21; 22; 23; 26; 27]%nat). vm_compute; reflexivity. }
    assert (PR3 : getr R1 (reg 18) = Z_to_bv 64 (qo / 8 + 2147450880) /\ getr R1 (reg 24) = Z_to_bv 64 q /\ getr R1 (reg 25) = Z_to_bv 64 0) by (repeat match type of PREST with _ /\ _ => destruct PREST as [? PREST] end; repeat split; assumption).
    destruct PR3 as (p18 & p24 & p25). split. exact p18. split. exact p24. split. rewrite L0. exact p25. intros X. exfalso. exact (X L0).
  - destruct OST as (BT1 & O16 & O24 & _ & CAPR & _ & Q4096 & Q47 & _). assert (L1 : 1 <= Z.of_nat len <= 134217728) by (clear - LN LR; lia).
    assert (QRG : 0 <= q < 2 ^ 64 /\ 0 <= q <= 18446744073709551615) by (clear - Q4096 Q47 CAPR; lia). destruct QRG as [QRG QRG'].
    pose proof (v5G5dn_conc fx Rc MV (fun j => match j with 2%nat => E | 35%nat => qo | 40%nat => F | 58%nat => U Rc 1 | 60%nat => fb | 67%nat => Z.of_nat len | 68%nat => q | _ => 0 end)) as P. cbn beta iota in P.
    feed P ltac:(first [apply UR | apply U_to | sc ]).
    destruct P as (fx1 & R1 & M1v & _ & _ & pEQ & (pMS & pKS & p1 & p10 & p11 & p12 & p18 & p24 & p25)).
    assert (EQM : M1v = MV) by (apply mem_eq_of_agree; exact pEQ). rewrite EQM in pMS.
    exists fx1, R1. split. exact pMS. split. { intros x Hx. apply pKS. revert Hx. apply (L5K.incl_b [2; 3; 4; 8; 9; 19; 20; 21; 22; 23; 26; 27]%nat). vm_compute; reflexivity. }
    split. exact p18. split. exact p24. split. exact p25. intros _. split. exact p1. split. exact p10. split. exact p11. exact p12.
Qed.

(* [comment removed for export] *)
Lemma binv_wk W W1 BX Mc modelc LKc crc Ac : binv W BX Mc modelc LKc crc Ac -> (forall a, L5.outside W1 a -> L5.outside W a) -> binv W1 BX Mc modelc LKc crc Ac.
Proof.
  intros (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10) WW. unfold L5AFK.binv.
  split. exact B1. split. exact B2. split. exact B3. split. exact B4. split. exact B5. split. exact B6.
  split. { apply (ek_W L ar LB FF E SCRD W1 W M Mc B7). exact WW. } split. exact B8. split. exact B9. exact B10.
Qed.

Lemma g5 (fx : FPState) Rc Mc modelc W W1 BX LKc crc Ac qo (bq : L5.bigobj) :
  binv W BX Mc modelc LKc crc Ac -> rinvD R E Rc -> getr Rc (reg 21) = Z_to_bv 64 2147450880 -> getr Rc (reg 22) = Z_to_bv 64 qo ->
  aobj FF qo 32 -> shadow_zero Mc qo 4 -> L5.big_at RSEGS Mc qo bq -> Z.of_nat (L5.bo_len bq) <= 2 ^ 24 ->
  (forall cap q, L5.bo_st bq = L5.BDyn cap q -> In (q, 8 * cap) (BX ++ LB)) ->
  (forall a, L5.outside W1 a -> L5.outside W a /\ L5.outside [(L5.bo_data qo bq, 8 * Z.of_nat (L5.bo_len bq))] a) ->
  (forall (fx' : FPState) R' M' model',
      binv W1 BX M' model' LKc crc Ac -> rinvD R E R' ->
      (forall x, In x [3; 4; 19; 20; 21; 22; 23; 26; 27]%nat -> getr R' (reg x) = getr Rc (reg x)) ->
      getr R' (reg 18) = Z_to_bv 64 (qo / 8 + 2147450880) -> getr R' (reg 24) = Z_to_bv 64 (L5.bo_data qo bq) -> getr R' (reg 25) = Z_to_bv 64 (Z.of_nat (L5.bo_len bq)) ->
      (forall a, 0 <= a < 2 ^ 64 -> aclient L ar (BX ++ LB) FF' SPA MEM_SCR a -> ~ (L5.bo_data qo bq <= a < L5.bo_data qo bq + 8 * Z.of_nat (L5.bo_len bq)) ->
                 M' (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)) ->
      L5KA.zeros_at M' (L5.bo_data qo bq) (8 * Z.of_nat (L5.bo_len bq)) ->
      srealizes RSEGS SCFG (cfg (fx:=fx') R' 0x927c0 M' model') K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc 0x92758 Mc modelc) K.
Proof.
  intros BI RI X21 X22 AOQ SZQ OBQ LEN24 INB WSUB KF.
  pose proof (arg_facts L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G W BX Mc modelc LKc crc Ac qo BI AOQ SZQ)
    as ((ORP & ORG & O8) & OBIG & OZ & OW & OFR & OF & OSH & SOF & SOSH & SOFR & U8V & U64V & OCL).
  pose proof (pf_of_binv L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G W BX Mc modelc LKc crc Ac BI) as PF.
  pose proof BI as (B1 & B2 & B3 & B4 & B5 & B6 & _).
  pose proof G as G'. destruct G' as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG' F32 FLA' FLR FLBIG' NCF NCS]. change (ff_bytes 3) with 512 in *.
  assert (AOQ' : aobj FF' qo 32) by (apply aobj_cons; exact AOQ).
  pose proof (aobj_facts L ar C HI LY HIok (BX ++ LB) FF' LKc crc Ac Mc modelc qo 32 SPA MEM_SCR B1 AOQ' ltac:(clear; lia) ltac:(reflexivity)) as (OR & _ & ODEF & _).
  set (MV := mrestrict (ahid Ac modelc) Mc) in *.
  destruct bq as [fb len sto].
  assert (OBQv : L5.big_at RSEGS MV qo (L5.BO fb len sto)).
  { destruct OBQ as (O0 & FBR & OL8 & OST). unfold L5.big_at. cbn [L5.bo_fb L5.bo_len L5.bo_st] in *. split. apply U8V. exact O0. split. exact FBR.
    split. apply U64V. clear; lia. clear; lia. exact OL8.
    destruct sto as [v0 v1|cap q].
    - destruct OST as (T0 & C16 & C24 & REST). split. exact T0. split. apply U64V. clear; lia. clear; lia. exact C16. split. apply U64V. clear; lia. clear; lia. exact C24. exact REST.
    - destruct OST as (T0 & C16 & C24 & REST). split. exact T0. split. apply U64V. clear; lia. clear; lia. exact C16. split. apply U64V. clear; lia. clear; lia. exact C24. exact REST. }
  destruct (g5_run fx Rc MV qo fb len sto RI PF X21 X22 (conj (conj ORP (conj ORG O8)) (conj OBIG (conj OZ (conj OW (conj OFR (conj OF (conj OSH (conj SOF (conj SOSH SOFR))))))))) OBQv) as (fx1 & R1 & pMS & pKS & p18 & p24 & p25 & pCALL).
  cbn [L5.bo_len] in *.
  assert (RI1 : rinvD R E R1).
  { apply (rinvD_keep R E Rc R1 RI). intros k Hk0. apply pKS. revert Hk0. apply (L5K.incl_b DIDX). vm_compute; reflexivity. }
  assert (KS8 : forall x, In x [3; 4; 19; 20; 21; 22; 23; 26; 27]%nat -> getr R1 (reg x) = getr Rc (reg x)).
  { intros x Hx. apply pKS. revert Hx. apply (L5K.incl_b [3; 4; 19; 20; 21; 22; 23; 26; 27]%nat). vm_compute; reflexivity. }
  set (dst := L5.bo_data qo (L5.BO fb len sto)) in *.
  destruct (Z.eqb_spec (Z.of_nat len) 0) as [L0|LN].
  - (* [comment removed for export] *)
    apply (apure L ar C HI LY HIok (BX ++ LB) FF' LKc crc Ac Mc modelc fx fx1 Rc 0x92758 R1 0x927c0 K B1 B2 pMS).
    intros model1 HH1 AM1 RT1 AH1.
    pose proof (L5AFK.binv_model L ar HI M model LB FF LK A E SCRD SPA (down E F ro R) F 3 W BX Mc modelc LKc crc Ac model1 BI HH1 AM1 RT1) as BI1.
    apply (KF fx1 R1 Mc model1 (binv_wk W W1 BX Mc model1 LKc crc Ac BI1 (fun a X => proj1 (WSUB a X))) RI1 KS8 p18 p24 p25).
    + intros a _ _ _. reflexivity.
    + intros i Hi. exfalso. clear - Hi L0. lia.
  - (* [comment removed for export] *)
    destruct (pCALL LN) as (c1 & c10 & c11 & c12).
    apply (apure L ar C HI LY HIok (BX ++ LB) FF' LKc crc Ac Mc modelc fx fx1 Rc 0x92758 R1 0x5e570 K B1 B2 pMS).
    intros model1 HH1 AM1 RT1 AH1.
    pose proof (L5AFK.binv_model L ar HI M model LB FF LK A E SCRD SPA (down E F ro R) F 3 W BX Mc modelc LKc crc Ac model1 BI HH1 AM1 RT1) as BI1.
    pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ B1) as (WB & _).
    (* [comment removed for export] *)
    assert (DLOC : (sto = sto) /\ 0 <= dst /\ dst + 8 * Z.of_nat len <= ahl_ceil ar /\ dst + 8 * Z.of_nat len <= 2 ^ 47
                   /\ aacc Mc dst (8 * Z.of_nat len) /\ L5.defined Mc dst (8 * Z.of_nat len)
                   /\ (forall i, 0 <= i < 8 * Z.of_nat len -> aclientw L ar (BX ++ LB) FF' SPA MEM_SCR (dst + i))
                   /\ app_rng ar dst (8 * Z.of_nat len)
                   /\ (forall a, dst <= a < dst + 8 * Z.of_nat len -> ~ (F / 8 + SB <= a < F / 8 + SB + 64))).
    { destruct OBQ as (O0 & FBR & OL8 & OST). cbn [L5.bo_fb L5.bo_len L5.bo_st] in *. subst dst. unfold L5.bo_data. cbn [L5.bo_st].
      destruct sto as [v0 v1|cap q].
      - destruct OST as (_ & _ & _ & L2 & _).
        split. reflexivity. split. clear - OR; lia. split. clear - OR L2; lia. split. clear - OR L2; lia.
        split. { eapply aacc_of_zero. exact SZQ. exact O8. clear - OR; lia. clear; lia. clear - L2; lia. }
        split. { eapply L5.defined_sub. exact ODEF. clear; lia. clear - L2; lia. }
        split. { intros i Hi. apply (obj_client L ar (BX ++ LB) FF' SPA MEM_SCR qo 32 (qo + 16 + i) AOQ'). clear - Hi L2; lia. }
        split. { apply (app_rng_aobj L ar C HI HIok _ _ _ _ _ _ _ qo 32 (qo + 16) (8 * Z.of_nat len) B1 AOQ'). clear; lia. clear - L2; lia. }
        intros a Ha. unfold SB. clear - Ha L2 OSH. lia.
      - destruct OST as (_ & _ & _ & LC & CAPR & Q8 & Q4096 & Q47 & _).
        pose proof (WB (q, 8 * cap) (INB cap q eq_refl)) as ((R0 & _ & _ & _ & R4 & _) & BDEF & BSH & _). cbn [fst snd] in *.
        split. reflexivity. split. clear - Q4096; lia. split. clear - R4 LC; lia. split. clear - Q47 LC; lia.
        split. { eapply aacc_of_blk. exact BSH. exact Q8. clear - Q4096; lia. clear; lia. clear - LC; lia. }
        split. { eapply L5.defined_sub. exact BDEF. clear; lia. clear - LC; lia. }
        split. { intros i Hi. apply (block_client L ar (BX ++ LB) FF' SPA MEM_SCR q (8 * cap) (q + i) (INB cap q eq_refl)). clear - Hi LC; lia. }
        split. { apply (app_rng_block L ar C HI HIok _ _ _ _ _ _ _ q (8 * cap) q (8 * Z.of_nat len) B1 (INB cap q eq_refl)). clear; lia. clear - LC; lia. }
        intros a Ha. pose proof (L5ADVEA.blk_avoid L ar C HI HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G HSCR W BX Mc modelc LKc crc Ac q (8 * cap) a BI (INB cap q eq_refl) ltac:(clear - Ha LC; lia)) as (_ & Y2 & _).
        exact Y2. }
    destruct DLOC as (_ & D0 & DCEIL & D47 & DACC & DDEF & DCLI & DAPP & DSH).
    pose proof RI1 as (Z2 & _ & _ & _ & Z4).
    pose proof (aio_memset _ _ _ _ _ HIok) as MS. unfold amemset_spec, amem_pre, amem_post in MS.
    rewrite (aly_segs L C LY), (aly_memset L C LY), (aly_scr_mem L C LY) in MS.
    assert (U25 : bv_unsigned (getr R1 2%bv) = SPA). { rewrite r2, Z2. apply L5.unsigned_lit. clear - ER; lia. }
    assert (SA16 : (E - 352) mod 16 = 0). { clear - EA. unfold aligned in EA. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    pose proof BI1 as (C1 & C2 & _ & _ & _ & C6 & _).
    eapply (MS fx1 R1 Mc model1 (BX ++ LB) FF' LKc crc Ac dst 0 (8 * Z.of_nat len) K); clear MS.
    { split. exact C1. split. exact (proj1 C2). split. exact (proj2 C2).
      split. rewrite r10. exact c10. split. rewrite r12. exact c12. split. clear - LEN24; lia.
      split. rewrite r4, Z4. exact G4. split. rewrite r1, c1. apply Hoare.ret_ok_even. rewrite L5.unsigned_lit by (clear; lia). reflexivity.
      split. { rewrite U25. apply (astack_ok_of_astk L ar C LY Mc Mc E SCRD 352 2560 C6 (mem_grows_refl Mc)). clear; lia. clear; lia. clear - HSCR; lia. exact SA16. }
      split. exact DACC.
      split. { intros i Hi. rewrite U25. apply DCLI. exact Hi. }
      split. { intros i m Hi Hm. apply (L5C.writable_of_defined RSEGS Mc dst (8 * Z.of_nat len)). exact DDEF. exact D0. clear - D47; lia. exact Hi. exact Hm. }
      split. exact HK. exact DAPP. }
    { rewrite r11. exact c11. }
    intros R6 M6 model6 mR10 RP6 ZB PRES6 SDEF6 RT6 MI6 HH6. rewrite U25 in PRES6, SDEF6. rewrite r1, c1.
    assert (Hh6 : m_halted model6 = None). { rewrite (L5LZ.model_rt_halted _ _ RT6). exact (proj1 C2). }
    assert (BI6 : binv W1 BX M6 model6 LKc crc Ac).
    { apply (binv_memW W W1 BX Mc model1 LKc crc Ac M6 model6 (fun a => dst <= a < dst + 8 * Z.of_nat len) 2560 BI1 HH6 (conj Hh6 MI6) RT6 PRES6).
      - intros a Ha. apply SDEF6. exact Ha.
      - intros a Da. destruct (ZB (a - dst) ltac:(clear - Da; lia)) as (v & _ & Bv). unfold byte_at in Bv. replace (dst + (a - dst)) with a in Bv by (clear; lia). rewrite Bv. discriminate.
      - intros a. destruct (rng_dec a dst (dst + 8 * Z.of_nat len)); [left|right]; assumption.
      - intros a Da. split. clear - Da DCEIL; lia. split. exact (DSH a Da).
        intros _ Ho. apply (proj2 (WSUB a Ho) (dst, 8 * Z.of_nat len)). left; reflexivity. unfold L5.in_rng. cbn [fst snd]. exact Da.
      - intros a X. exact (proj1 (WSUB a X)).
      - clear - HSCR; lia.
      - clear; lia. }
    apply (KF fx1 R6 M6 model6 BI6 (rinvD_pres R E R1 R6 RI1 RP6)).
    + intros x Hx. rewrite (cs_of_preserved R1 R6 x RP6). apply KS8. exact Hx. revert Hx. apply (L5K.incl_b [3; 4; 19; 20; 21; 22; 23; 26; 27]%nat). vm_compute; reflexivity.
    + rewrite (cs_of_preserved R1 R6 18 RP6) by inl. exact p18.
    + rewrite (cs_of_preserved R1 R6 24 RP6) by inl. exact p24.
    + rewrite (cs_of_preserved R1 R6 25 RP6) by inl. exact p25.
    + intros a Ha Hc ND. apply PRES6. exact Ha. exact Hc. exact ND.
    + intros i Hi. destruct (ZB i Hi) as (v & Ev & Bv). subst v. exact Bv.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma dreg_facts W BX Mc modelc LKc crc Ac o b ws (m : Z) :
  binv W BX Mc modelc LKc crc Ac -> aobj FF' o 32 -> tob (BX ++ LB) Mc o b ws -> 1 <= m ->
  m <= (match L5.bo_st b with L5.BInl _ _ => 2 | L5.BDyn cap _ => cap end) ->
  let D := L5.bo_data o b in let MV := mrestrict (ahid Ac modelc) Mc in
  (4096 <= D /\ D mod 8 = 0 /\ D + 8 * m <= ahl_ceil ar /\ D + 8 * m <= 140737479966720) /\ L5ADVGL.nsh D (8 * m) /\ L5ADVGL.oim D (8 * m)
  /\ L5KA.zeros_at MV (D / 8 + 2147450880) m /\ L5.defined MV D (8 * m) /\ L5.writable RSEGS MV D (8 * m)
  /\ (forall a, D <= a < D + 8 * m -> MV (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)).
Proof.
  intros BI AOB (OB & _ & SZ & INB) M1 MC D MV. pose proof BI as (B1 & _).
  pose proof (aobj_facts L ar C HI LY HIok (BX ++ LB) FF' LKc crc Ac Mc modelc o 32 0 0 B1 AOB ltac:(clear; lia) ltac:(reflexivity)) as (OR & OBIG & ODEF & OVIS & OVSH & _). change (32 / 8) with 4 in OVSH.
  pose proof (vis_pack L ar C HI LY HIok (BX ++ LB) FF' LKc crc Ac Mc modelc B1) as (_ & _ & _ & _ & VBLK & VBSH & _).
  pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ B1) as (WB & _).
  destruct G as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG' F32 FLA' FLR FLBIG' NCF NCS].
  unfold L5ADVGL.nsh, L5ADVGL.oim. subst D. unfold L5.bo_data in *. destruct b as [fb len sto]. cbn [L5.bo_st] in *.
  destruct sto as [v0 v1|cap q].
  - assert (VIS : forall a, o + 16 <= a < o + 16 + 8 * m -> MV (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)).
    { intros a Ha. apply L5LZ.mrestrict_visible'. replace a with (o + (a - o)) by (clear; lia). apply OVIS. clear - Ha MC; lia. }
    assert (DEFv : L5.defined MV (o + 16) (8 * m)). { intros i Hi. rewrite VIS by (clear - Hi; lia). replace (o + 16 + i) with (o + (16 + i)) by (clear; lia). apply ODEF. clear - Hi MC; lia. }
    split. clear - OR MC M1 SPT; lia. split. clear - OBIG MC M1; lia. split. clear - OR; lia.
    split. { intros i Hi. replace ((o + 16) / 8 + 2147450880 + i) with (o / 8 + SB + (2 + i)) by (unfold SB; clear - OR; lia).
             unfold MV. rewrite L5LZ.mrestrict_visible' by (apply OVSH; clear - Hi MC; lia). specialize (SZ (2 + i) ltac:(clear - Hi MC; lia)). unfold byte_at, S in SZ. exact SZ. }
    split. exact DEFv. split. apply (L5C.writable_of_defined RSEGS). exact DEFv. clear - OR; lia. clear - OR MC; lia. exact VIS.
  - destruct OB as (_ & _ & _ & (_ & _ & _ & LC & CRG & Q8 & Q4096 & Q47 & _)).
    pose proof (WB (q, 8 * cap) (INB cap q eq_refl)) as ((R0 & R1 & R2 & R3 & R4 & R5) & BDEF & (BSH & _) & _). cbn [fst snd] in *.
    rewrite (aly_img_lo L C LY), (aly_img_hi L C LY) in R1. unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in R5.
    assert (VIS : forall a, q <= a < q + 8 * m -> MV (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)).
    { intros a Ha. apply L5LZ.mrestrict_visible'. replace a with (a + 0) by (clear; lia). apply (VBLK q (8 * cap) a 1 (INB cap q eq_refl)). clear - Ha; lia. clear - Ha MC; lia. clear; lia. }
    assert (DEFv : L5.defined MV q (8 * m)). { intros i Hi. rewrite VIS by (clear - Hi; lia). apply BDEF. clear - Hi MC; lia. }
    split. clear - R0 R2 R4 MC M1 SPT; lia. split. clear - R5 MC M1; lia. split. clear - R1 MC M1; lia.
    split. { intros i Hi. unfold MV. rewrite L5LZ.mrestrict_visible'.
             - replace (8 * cap / 8) with cap in BSH by (clear; lia). specialize (BSH i ltac:(clear - Hi MC; lia)). unfold byte_at, S, SB in BSH. exact BSH.
             - replace (q / 8 + 2147450880 + i) with (q / 8 + 2147450880 + i + 0) by (clear; lia). apply (VBSH q (8 * cap) (q / 8 + 2147450880 + i) 1 (INB cap q eq_refl)). 2: clear; lia.
               intros j Hj. unfold in_shadow_of, S, SB. clear - Hi Hj MC Q8 CRG Q4096. lia. }
    split. exact DEFv. split. apply (L5C.writable_of_defined RSEGS). exact DEFv. clear - R0; lia. clear - R4 MC SPT; lia. exact VIS.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
End DIV.
End WithIface.
End SCFG_1.
End L5ADVGA.
