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
     AsanAcct AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5Words L5LazyA L5DefsAB0
     L5CoreAB0 L5CoreSpecsAB0 L5StepAB0 L5CoreBB0 L5BDetailG L5BFrameK L5DivKitAB0 L5DivSpecsAB0 L5OpmodSpecsAB0 L5DivLeafSpecsAB0 L5DivInnerSpecsAB0 L5BCopyAS L5BDivH L5BDivT L5BDivD L5BDivE L5BDivEA L5BDivHC L5BDivHA L5BDivHO L5BDivPG1 L5BDivGL L5BDivGZ.
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
Local Notation SPA := (E - 384).
Hypothesis G : L5AFK.gctx L ar HI LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2.
Hypothesis ER : 140735332487680 <= E <= 140737488355328.
Hypothesis EA : aligned E 32.
Hypothesis HK : K [].
Hypothesis G4 : getr R (reg 4) = Z_to_bv 64 (hl_tp L).
Hypothesis HSCR : 384 + 4784 <= SCRD.
Hypothesis HSSH : L5OMA.stksh ar M (E - SCRD).
Hypothesis HSC8 : SCRD mod 8 = 0.
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
  destruct PF as (W384 & IMGC & CSB & CUAR & FDEFv & FWv & FSHWv & FLCv & FLWv);
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
Lemma HSCR0 : 384 + 4784 <= SCRD. Proof. exact HSCR. Qed.          (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma stksh_cal W BX Mc modelc LKc crc Ac scr : binv W BX Mc modelc LKc crc Ac -> 0 <= scr -> 384 + scr <= SCRD -> scr mod 8 = 0 ->
  (forall a, in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> L5.outside W a) -> L5OMA.stksh ar Mc (SPA - scr).
Proof.
  intros (B1 & _ & _ & _ & _ & _ & EK & _) HS0 HS sc8 NW. pose proof HSSH as SSH'. pose proof HSC8 as SC8.
  destruct G as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG' F32 FLA' FLR FLBIG' NCF NCS].
  pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ B1) as WF0.
  assert (TOP : ar_stack_top ar <= 2 ^ 47). { clear - WF0. decompose [and] WF0. assumption. } clear WF0.
  set (mx := Z.max (ar_sptop ar) (ar_stack_top ar)) in *.
  assert (MX : mx <= 2 ^ 47 /\ E <= mx) by (subst mx; split; [apply Z.max_lub; [clear - SPT; lia | exact TOP] | clear - SHI; lia]).
  set (lo := SPA - scr). set (lo0 := E - SCRD).
  assert (LOR : lo0 <= lo /\ ahl_ceil ar <= lo0 /\ lo <= E /\ 0 <= lo0) by (subst lo lo0; clear - HS0 HS SLO SPC FR FCEIL; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (DV : lo0 / 8 <= lo / 8 /\ ahl_ceil ar / 8 <= lo0 / 8 /\ 0 <= lo0 / 8 /\ lo / 8 + (mx - lo) / 8 <= lo0 / 8 + (mx - lo0) / 8 /\ lo0 / 8 + (mx - lo0) / 8 <= 17592186044416)
    by (subst lo lo0; clear - LOR MX EA SC8 sc8; unfold aligned in EA; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  destruct DV as (D1 & D2 & D3 & D4 & D5).
  unfold L5OMA.stksh in *. fold mx in SSH' |- *. fold lo lo0 in SSH' |- *.
  intros j Hj. unfold byte_at, S. rewrite EK.
  - unfold shadow_zero, byte_at, S in SSH'. replace (lo / 8 + SB + j) with (lo0 / 8 + SB + (lo / 8 - lo0 / 8 + j)) by (clear; lia). apply SSH'. clear - Hj D1 D4; lia.
  - assert (ISH : in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) (lo / 8 + SB + j)).
    { unfold in_shadow_of, S. replace (ahl_ceil ar + (2 ^ 47 - ahl_ceil ar) - 1) with (2 ^ 47 - 1) by (clear; lia). change ((2 ^ 47 - 1) / 8) with 17592186044415. clear - Hj D1 D2 D4 D5. lia. }
    split. unfold SB. clear - Hj D1 D3 D4 D5; lia. split. 2: exact (NW _ ISH). right; right; right; right; left. exact ISH.
Qed.

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
  pose proof RI as (Z2 & _ & _ & _ & Z4 & _).
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
Lemma loc_off_frame W BX Mc modelc LKc crc Ac k (b : L5.bigobj) a : binv W BX Mc modelc LKc crc Ac -> (k = 32 \/ k = 96) ->
  (forall cap q, L5.bo_st b = L5.BDyn cap q -> In (q, 8 * cap) (BX ++ LB)) -> L5ADVEA.oreg (F + k) b a -> ~ (SPA <= a < E).
Proof.
  intros BI Hkk INB OR.
  pose proof (NUM L ar HI R LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER) as ((FRG & FLRG & ERG) & FRP & FLRP & ALF & FBIG & FLBIG & FLA & SFA & SFLA & SFB).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (SHB : 0 <= F / 8 /\ F / 8 + 64 <= 17592186044416 /\ (F + 32) / 8 = F / 8 + 4 /\ (F + 96) / 8 = F / 8 + 12) by (clear - FRP ALF; unfold aligned in *; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  destruct SHB as (SHB0 & SHB1 & SHB2 & SHB3).
  destruct OR as [OR|[OR|(cap & q & Eq & OR)]].
  - clear - OR Hkk SFB; lia.
  - unfold SB in OR. clear - OR Hkk SHB0 SHB1 SHB2 SHB3 ER. destruct Hkk as [-> | ->]; [rewrite SHB2 in OR | rewrite SHB3 in OR]; lia.
  - pose proof (L5ADVEA.blk_avoid L ar C HI HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G HSCR0 W BX Mc modelc LKc crc Ac q (8 * cap) a BI (INB cap q Eq) OR) as (_ & _ & Y3). clear - Y3. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma g1 (fx : FPState) Rc Mc modelc W BX LKc crc Ac fbo bn wn :
  binv W BX Mc modelc LKc crc Ac -> rinvD R E Rc -> getr Rc (reg 25) = Z_to_bv 64 (F + 96) -> getr Rc (reg 27) = Z_to_bv 64 F ->
  L5.u8_at RSEGS Mc (SPA + 200) fbo -> 0 <= fbo < 256 -> shadow_zero Mc (SPA + 200) 4 ->
  tob (BX ++ LB) Mc (F + 96) bn wn ->
  (L5.bo_dyn bn = true -> 8 * L5.bo_cap bn <= 2 ^ 27 /\ acredit_ok L crc (8 * L5.bo_cap bn)) ->
  (forall (fx' : FPState) R1 R' M1 M' model' (g : growth) LBn cr' LK' A',
      (forall x, In x KS_v5G1 -> getr R1 (reg x) = getr Rc (reg x)) ->
      (forall a, 0 <= a < 2 ^ 64 -> ~ (E - 360 <= a < E - 352) -> M1 (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)) -> L5.u64_at RSEGS M1 (E - 360) F -> tob (BX ++ LB) M1 (F + 96) bn wn ->
      copy_post L ar (BX ++ LB) FF' LK' crc M1 M' R1 R' (SPA + 200) (F + 96) SPA fbo bn wn g LBn cr' ->
      binv W (match g with Same => BX | Grown q cap => (q, 8 * cap) :: BX end) M' model' LK' cr' A' ->
      incl Ac A' -> incl LK' LKc ->
      srealizes RSEGS SCFG (cfg (fx:=fx') R' 0x930bc M' model') K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc 0x930a8 Mc modelc) K.
Proof.
  intros BI RI X25 X27 DFB FBR DSZ TN CAP KF.
  open_ctx BI. pose proof BI as (B1 & B2 & _). pose proof RI as (X2 & X8 & X9 & X3 & X4 & XSB).
  set (MV := mrestrict (ahid Ac modelc) Mc) in *.
  assert (ER' : 140735332487616 <= E <= 140737488355328) by (clear - ER; lia).
  assert (FR' : 4096 <= F <= 140737488354816) by (clear - FRP; lia).
  pose proof (v5G1_conc fx Rc MV (fun j => match j with 2%nat => E | 40%nat => F | 58%nat => U Rc 1 | _ => 0 end)) as P. cbn beta iota in P.
  feed P ltac:(first [apply UR | apply U_to | sc ]).
  destruct P as (fx1 & R1 & M1v & MG1 & _ & pFZ & (pMS & pKS & pR1 & pR10 & pR11 & pR12 & p360)).
  set (Wp := fun a => E - 360 <= a < E - 352).
  apply (L5DKA.bstage L ar C HI LY HIok M model LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2 G W _ Mc modelc LKc crc Ac fx fx1 Rc 0x930a8 R1 COPYA M1v Wp K BI pMS MG1).
  { intros a Ha Hn. apply pFZ. exact Ha. subst Wp; cbn beta in Hn. clear - Hn; lia. }
  { intros a Ha Wa. subst Wp; cbn beta in Wa. apply (L5DKA.wp_frame L ar HI LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2 G). clear - Wa; lia. unfold docell. clear - Wa; lia. }
  intros M1 model1 BI1 AH1 VIS1 MGM1 FRM1.
  assert (OFF1 : offx (BX ++ LB) 0 Wp Mc M1). { intros a Ha _ NX. apply FRM1. exact Ha. exact NX. }
  assert (AON' : aobj FF' (F + 96) 32) by (eapply L5ADVEA.loc_aobj; [exact G | clear; lia | clear; lia | reflexivity]).
  assert (TN1 : tob (BX ++ LB) M1 (F + 96) bn wn).
  { apply (L5ADVEA.tob_keep' L ar C HI LY HIok FF E F (BX ++ LB) (BX ++ LB) (BX ++ LB) LKc crc Ac modelc 0 Wp Mc M1 (F + 96) bn wn B1 AON' TN OFF1).
    intros cap q Eq. split; apply (proj2 (proj2 (proj2 TN)) cap q Eq).
    intros a OR Wa. subst Wp; cbn beta in Wa. apply (loc_off_frame W BX Mc modelc LKc crc Ac 96 bn a BI (or_intror eq_refl) (proj2 (proj2 (proj2 TN))) OR). clear - Wa; lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (SD : 0 <= (E - 184) / 8 /\ (E - 184) / 8 + 4 <= 17592186044416) by (clear - ER; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  assert (DFB1 : L5.u8_at RSEGS M1 (SPA + 200) fbo).
  { unfold L5.u8_at in *. rewrite (L5C.rdn_agree RSEGS Mc M1 1 (SPA + 200) ltac:(clear - ER; lia) ltac:(cbn; clear - ER; lia)). exact DFB.
    intros i Hi. apply FRM1. cbn in Hi; clear - Hi ER; lia. subst Wp; cbn beta. cbn in Hi; clear - Hi; lia. }
  assert (DSZ1 : shadow_zero M1 (SPA + 200) 4).
  { intros j Hj. unfold byte_at. rewrite FRM1. exact (DSZ j Hj). unfold S, SB. replace (E - 384 + 200) with (E - 184) by (clear; lia). clear - Hj SD; lia.
    subst Wp; cbn beta. unfold S, SB. replace (E - 384 + 200) with (E - 184) by (clear; lia). clear - Hj SD ER; lia. }
  assert (S360 : L5.u64_at RSEGS M1 (E - 360) F).
  { apply (proj1 (u64_at_vis (ahid Ac modelc) M1 (E - 360) F ltac:(eapply avis_sub; [exact SV | clear; lia | clear; lia]) ltac:(clear - ER; lia) ltac:(clear - ER; lia))). rewrite VIS1. exact p360. }
  apply (copy_stage_sd fx1 R1 M1 model1 W BX LKc crc Ac 200 96 0x930bc fbo bn wn BI1).
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
  - exact DFB1.
  - exact FBR.
  - exact DSZ1.
  - exact TN1.
  - exact CAP.
  - intros fx3 R3 M3 model3 g LBn cr3 LK3 A3 POST BI3 IA3 ILK3. apply (KF fx3 R1 R3 M1 M3 model3 g LBn cr3 LK3 A3 pKS FRM1 S360 TN1 POST BI3 IA3 ILK3).
Qed.

Lemma g2 (fx : FPState) Rc Mc modelc W BX LKc crc Ac fbo bd wd :
  binv W BX Mc modelc LKc crc Ac -> rinvD R E Rc -> L5.u64_at RSEGS Mc (E - 304) (F + 32) ->
  L5.u8_at RSEGS Mc (SPA + 168) fbo -> 0 <= fbo < 256 -> shadow_zero Mc (SPA + 168) 4 ->
  tob (BX ++ LB) Mc (F + 32) bd wd ->
  (L5.bo_dyn bd = true -> 8 * L5.bo_cap bd <= 2 ^ 27 /\ acredit_ok L crc (8 * L5.bo_cap bd)) ->
  (forall (fx' : FPState) R1 R' M' model' (g : growth) LBn cr' LK' A',
      (forall x, In x KS_v5G2 -> getr R1 (reg x) = getr Rc (reg x)) -> getr R1 (reg 19) = Z_to_bv 64 (F + 32) ->
      copy_post L ar (BX ++ LB) FF' LK' crc Mc M' R1 R' (SPA + 168) (F + 32) SPA fbo bd wd g LBn cr' ->
      binv W (match g with Same => BX | Grown q cap => (q, 8 * cap) :: BX end) M' model' LK' cr' A' ->
      incl Ac A' -> incl LK' LKc ->
      srealizes RSEGS SCFG (cfg (fx:=fx') R' 0x930d0 M' model') K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc 0x930bc Mc modelc) K.
Proof.
  intros BI RI S88 DFB FBR DSZ TD CAP KF.
  pose proof (frm_vis W BX Mc modelc LKc crc Ac _ _ BI S88 ltac:(clear; lia) ltac:(clear; lia)) as S88v.
  open_ctx BI. pose proof BI as (B1 & B2 & _). pose proof RI as (X2 & X8 & X9 & X3 & X4 & XSB).
  set (MV := mrestrict (ahid Ac modelc) Mc) in *.
  assert (ER' : 140735332487616 <= E <= 140737488355328) by (clear - ER; lia).
  assert (FR' : 4096 <= F <= 140737488354816) by (clear - FRP; lia).
  pose proof (v5G2_conc fx Rc MV (fun j => match j with 2%nat => E | 40%nat => F | 58%nat => U Rc 1 | _ => 0 end)) as P. cbn beta iota in P.
  feed P ltac:(first [apply UR | apply U_to | sc ]).
  destruct P as (fx1 & R1 & M1v & _ & _ & pEQ & (pMS & pKS & pR1 & pR10 & pR11 & _ & pR19)).
  assert (EQM : M1v = MV) by (apply mem_eq_of_agree; exact pEQ). rewrite EQM in pMS.
  apply (apure L ar C HI LY HIok (BX ++ LB) FF' LKc crc Ac Mc modelc fx fx1 Rc 0x930bc R1 COPYA K B1 B2 pMS).
  intros model1 HH1 AM1 RT1 AH1.
  pose proof (L5AFK.binv_model L ar HI M model LB FF LK A E SCRD SPA (down E F ro R) F 3 W BX Mc modelc LKc crc Ac model1 BI HH1 AM1 RT1) as BI1.
  apply (copy_stage_sd fx1 R1 Mc model1 W BX LKc crc Ac 168 32 0x930d0 fbo bd wd BI1).
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
  getr Rc (reg 19) = Z_to_bv 64 (F + 32) -> getr Rc (reg 25) = Z_to_bv 64 (F + 96) -> getr Rc (reg 21) = Z_to_bv 64 to -> 0 <= to < 2 ^ 64 -> 0 <= ro < 2 ^ 64 ->
  shadow_zero Mc (E - 220) 1 -> (forall a, in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> L5.outside W a) ->
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
      (forall x, In x KS_v5G3 -> getr R1 (reg x) = getr Rc (reg x)) ->
      (forall a, 0 <= a < 2 ^ 64 -> ~ (E - 220 <= a < E - 216) -> M1 (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)) ->
      L5DLA.norm_postA L ar (BX ++ LB) FF' LK' crc M1 M' R1 R' (F + 32) (F + 96) (E - 220) SPA bd bn wd wn c gd gn LBn cr' ->
      binv W (L5DLA.blocks_of gn ++ L5DLA.blocks_of gd ++ BX) M' model' LK' cr' A' ->
      incl Ac A' -> incl LK' LKc ->
      srealizes RSEGS SCFG (cfg (fx:=fx') R' 0x930e8 M' model') K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc 0x930d0 Mc modelc) K.
Proof.
  intros BI RI X19 X25 X21 TOR RORG SZP NW TD TN BXD BXN LD TOPNZ TOPSM LN NN2 CAPD CAPN SECC APB CR KF.
  open_ctx BI. pose proof RI as (X2 & X8 & X9 & X3 & X4 & XSB).
  pose proof G as G'. destruct G' as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG' F32 FLA' FLR FLBIG' NCF NCS]. change (ff_bytes 3) with 512 in *.
  set (MV := mrestrict (ahid Ac modelc) Mc) in *.
  assert (ER' : 140735332487616 <= E <= 140737488355328) by (clear - ER; lia).
  assert (FR' : 4096 <= F <= 140737488354816) by (clear - FRP; lia).
  assert (ROR : 0 <= U R 1 < 2 ^ 64) by apply UR.
  (* [comment removed for export] *)
  pose proof (v5G3_conc fx Rc MV (fun j => match j with 2%nat => E | 33%nat => to | 36%nat => ro | 40%nat => F | 58%nat => U Rc 1 | _ => 0 end)) as P. cbn beta iota in P.
  feed P ltac:(first [apply UR | apply U_to | sc ]).
  destruct P as (fx1 & R1 & M1v & MG1 & _ & pFZ & (pMS & pKS & pR1 & pR10 & pR11 & pR12 & pR13 & pX0)).
  set (Wp := fun a => E - 220 <= a < E - 216).
  apply (L5DKA.bstage L ar C HI LY HIok M model LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2 G W _ Mc modelc LKc crc Ac fx fx1 Rc 0x930d0 R1 0x93d94 M1v Wp K BI pMS MG1).
  { intros a Ha Hn. apply pFZ. exact Ha. subst Wp; cbn beta in Hn. clear - Hn; lia. }
  { intros a Ha Wa. subst Wp; cbn beta in Wa. apply (L5DKA.wp_frame L ar HI LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2 G). clear - Wa; lia. unfold docell. clear - Wa; lia. }
  intros M1 model1 BI1 AH1 VIS1 MGM1 FRM1.
  pose proof BI as (B1 & _). pose proof BI1 as (C1 & C2 & _ & _ & _ & C6 & _).
  assert (OFF1 : offx (BX ++ LB) 0 Wp Mc M1). { intros a Ha _ NX. apply FRM1. exact Ha. exact NX. }
  assert (AOD' : aobj FF' (F + 32) 32) by (eapply L5ADVEA.loc_aobj; [exact G | clear; lia | clear; lia | reflexivity]).
  assert (AON' : aobj FF' (F + 96) 32) by (eapply L5ADVEA.loc_aobj; [exact G | clear; lia | clear; lia | reflexivity]).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (SHB : 0 <= F / 8 /\ F / 8 + 64 <= 17592186044416 /\ (F + 32) / 8 = F / 8 + 4 /\ (F + 96) / 8 = F / 8 + 12 /\ (E - 220) mod 4 = 0 /\ (E - 220) / 8 <= 17592186044415 /\ 0 <= (E - 220) / 8)
    by (clear - FRP ALF EA ER; unfold aligned in *; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  destruct SHB as (SHB0 & SHB1 & SHB2 & SHB3 & PX4 & PXD & PXD0).
  assert (NXL : forall k (b : L5.bigobj), (k = 32 \/ k = 96) -> (forall cap q, L5.bo_st b = L5.BDyn cap q -> In (q, 8 * cap) (BX ++ LB)) -> forall a, L5ADVEA.oreg (F + k) b a -> ~ Wp a).
  { intros k b Hkk INB a OR. subst Wp; cbn beta. destruct OR as [OR|[OR|(cap & q & Eq & OR)]].
    - clear - OR Hkk SFB; lia.
    - unfold SB in OR. clear - OR Hkk SHB0 SHB1 SHB2 SHB3 ER. destruct Hkk as [-> | ->]; [rewrite SHB2 in OR | rewrite SHB3 in OR]; lia.
    - pose proof (L5ADVEA.blk_avoid L ar C HI HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G HSCR0 W BX Mc modelc LKc crc Ac q (8 * cap) a BI (INB cap q Eq) OR) as (_ & _ & Y3). clear - Y3. lia. }
  assert (TD1 : tob (BX ++ LB) M1 (F + 32) bd wd).
  { apply (L5ADVEA.tob_keep' L ar C HI LY HIok FF E F (BX ++ LB) (BX ++ LB) (BX ++ LB) LKc crc Ac modelc 0 Wp Mc M1 (F + 32) bd wd B1 AOD' TD OFF1).
    intros cap q Eq. split; apply (proj2 (proj2 (proj2 TD)) cap q Eq). apply (NXL 32 bd (or_introl eq_refl) (proj2 (proj2 (proj2 TD)))). }
  assert (TN1 : tob (BX ++ LB) M1 (F + 96) bn wn).
  { apply (L5ADVEA.tob_keep' L ar C HI LY HIok FF E F (BX ++ LB) (BX ++ LB) (BX ++ LB) LKc crc Ac modelc 0 Wp Mc M1 (F + 96) bn wn B1 AON' TN OFF1).
    intros cap q Eq. split; apply (proj2 (proj2 (proj2 TN)) cap q Eq). apply (NXL 96 bn (or_intror eq_refl) (proj2 (proj2 (proj2 TN)))). }
  assert (SZP1 : shadow_zero M1 (E - 220) 1).
  { intros j Hj. unfold byte_at. rewrite FRM1. exact (SZP j Hj). unfold S, SB. clear - Hj PXD PXD0; lia. subst Wp; cbn beta. unfold S, SB. clear - Hj PXD ER; lia. }
  destruct TD1 as (OBD1 & OLD1 & SZD1 & IND1). destruct TN1 as (OBN1 & OLN1 & SZN1 & INN1).
  (* [comment removed for export] *)
  edestruct L5ADVEA.callee_pre with (SCRc := L5DLA.NORM_SCR) as (STKc & ROOMc & RSc & A32c); [exact HIok | exact EA | exact FFR1 | exact FFRS | exact BI1 | vm_compute; discriminate | clear - HSCR; change L5DLA.NORM_SCR with 4784; lia | ].
  assert (RI1 : rinvD R E R1). { apply (rinvD_ks R E Rc R1 KS_v5G3 RI pKS). vm_compute; reflexivity. }
  pose proof RI1 as (Z2 & _ & _ & _ & Z4 & _).
  assert (WAV : forall rr a, In rr (L5DLA.norm_W (F + 32) (F + 96) (E - 220) bd bn) -> L5.in_rng rr a -> ~ docell E a /\ ~ (F / 8 + SB <= a < F / 8 + SB + ff_bytes 3 / 8)).
  { intros rr a Hr IR. change (ff_bytes 3 / 8) with 64. unfold L5DLA.norm_W in Hr. cbn [app In] in Hr. unfold L5.in_rng in IR.
    destruct Hr as [Hr|[Hr|[Hr|Hr]]]; try (subst rr; cbn [fst snd] in IR).
    - split. unfold docell. clear - IR SFB; lia. unfold SB. clear - IR SHB0 SHB1 FBIG FRP; lia.
    - split. unfold docell. clear - IR SFB; lia. unfold SB. clear - IR SHB0 SHB1 FBIG FRP; lia.
    - split. unfold docell. clear - IR; lia. unfold SB. clear - IR SHB0 SHB1 ER; lia.
    - apply in_app_or in Hr. unfold L5DLA.dyn_area in Hr. destruct Hr as [Hr|Hr].
      + destruct (L5.bo_st bd) as [v0 v1|cap q] eqn:Eq; [destruct Hr|]. destruct Hr as [Hr|[]]. subst rr; cbn [fst snd] in IR.
        pose proof (L5ADVEA.blk_avoid L ar C HI HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G HSCR0 W BX Mc modelc LKc crc Ac q (8 * cap) a BI (IND1 cap q eq_refl) IR) as (Y1 & Y2 & _).
        split. exact Y1. exact Y2.
      + destruct (L5.bo_st bn) as [v0 v1|cap q] eqn:Eq; [destruct Hr|]. destruct Hr as [Hr|[]]. subst rr; cbn [fst snd] in IR.
        pose proof (L5ADVEA.blk_avoid L ar C HI HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G HSCR0 W BX Mc modelc LKc crc Ac q (8 * cap) a BI (INN1 cap q eq_refl) IR) as (Y1 & Y2 & _).
        split. exact Y1. exact Y2. }
  assert (WOUT : forall a, aclient L ar LB FF E SCRD a -> L5.outside W a -> L5.outside (L5DLA.norm_W (F + 32) (F + 96) (E - 220) bd bn) a).
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
  apply (Hnorm fx1 R1 M1 model1 K (BX ++ LB) FF' LKc crc Ac (F + 32) (F + 96) (E - 220) SPA 0x930e8 bd bn wd wn C1 C2 HK).
  - rewrite r11. exact pR11.
  - rewrite r12. exact pR12.
  - rewrite r13. exact pR13.
  - rewrite r1. exact pR1.
  - split. clear; lia. reflexivity.
  - rewrite r2. exact Z2.
  - exact A32c.
  - rewrite r4, Z4. rewrite <- G4. reflexivity.
  - exact STKc.
  - apply (stksh_cal W _ M1 model1 LKc crc Ac L5DLA.NORM_SCR BI1); [vm_compute; discriminate | clear - HSCR; change L5DLA.NORM_SCR with 4784; lia | reflexivity | exact NW].
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
      - clear - HSCR; change L5DLA.NORM_SCR with 4784; lia.
      - exact WAV.
      - exact WOUT.
      - intros a X. exact X. }
    apply (KF fx3 R1 R3 M1 M3 model3 c gd gn _ cr3 LK3 A3 pKS FRM1 POST BI3 IA3 ILK3).
Qed.

(* [comment removed for export] *)
Lemma locz_vis W BX Mc modelc LKc crc Ac : binv W BX Mc modelc LKc crc Ac -> shadow_zero Mc (F + 32) 4 -> L5KA.zeros_at (mrestrict (ahid Ac modelc) Mc) (F / 8 + 2147450884) 4.
Proof.
  intros BI SZ. open_ctx BI.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (SHB : (F + 32) / 8 = F / 8 + 4) by (clear - FRP ALF; unfold aligned in *; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  intros i Hi. rewrite L5LZ.mrestrict_visible'.
  - specialize (SZ i Hi). unfold byte_at, S, SB in SZ. rewrite SHB in SZ. replace (F / 8 + 2147450884 + i) with (F / 8 + 4 + 2147450880 + i) by (clear; lia). exact SZ.
  - replace (F / 8 + 2147450884 + i) with (F / 8 + SB + (4 + i)) by (unfold SB; clear; lia). apply SHV. clear - Hi; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma g4 (fx : FPState) Rc Mc modelc W BX LKc crc Ac sd qo (bd : L5.bigobj) lenn :
  binv W BX Mc modelc LKc crc Ac -> rinvD R E Rc ->
  getr Rc (reg 10) = Z_to_bv 64 sd -> getr Rc (reg 19) = Z_to_bv 64 (F + 32) -> getr Rc (reg 25) = Z_to_bv 64 (F + 96) ->
  0 <= sd < 2 ^ 64 -> 0 <= qo < 2 ^ 64 -> L5.u64_at RSEGS Mc (E - 296) qo -> shadow_zero Mc (F + 32) 4 ->
  L5.big_at RSEGS Mc (F + 32) bd -> L5.u64_at RSEGS Mc (F + 104) lenn -> 0 <= lenn < 2 ^ 64 ->
  (forall (fx1 : FPState) R1 M1 model1,
      binv W BX M1 model1 LKc crc Ac -> rinvD R E R1 ->
      (forall x, In x [3; 4; 18; 19; 21; 22; 25; 26; 27]%nat -> getr R1 (reg x) = getr Rc (reg x)) ->
      getr R1 (reg 1) = Z_to_bv 64 0x9313c -> getr R1 (reg 10) = Z_to_bv 64 qo -> getr R1 (reg 11) = Z_to_bv 64 (lenn - Z.of_nat (L5.bo_len bd)) ->
      getr R1 (reg 20) = Z_to_bv 64 lenn -> getr R1 (reg 24) = Z_to_bv 64 sd ->
      (forall a, 0 <= a < 2 ^ 64 -> ~ (E - 120 <= a < E - 104) -> ~ (E - 272 <= a < E - 264) -> M1 (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)) ->
      L5.u64_at RSEGS M1 (E - 120) (L5.bo_data (F + 32) bd) -> L5.u64_at RSEGS M1 (E - 112) (Z.of_nat (L5.bo_len bd)) -> L5.u64_at RSEGS M1 (E - 272) (Z.of_nat (L5.bo_len bd)) ->
      srealizes RSEGS SCFG (cfg (fx:=fx1) R1 RESIZE M1 model1) K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc 0x930e8 Mc modelc) K.
Proof.
  intros BI RI X10 X19 X25 SDR QOR S88 SZD OBD NLEN NLR KF.
  pose proof (frm_vis W BX Mc modelc LKc crc Ac _ _ BI S88 ltac:(clear; lia) ltac:(clear; lia)) as S88v.
  pose proof (locz_vis W BX Mc modelc LKc crc Ac BI SZD) as SZDv.
  open_ctx BI. pose proof RI as (X2 & X8 & X9 & X3 & X4 & XSB).
  set (MV := mrestrict (ahid Ac modelc) Mc) in *.
  assert (ER' : 140735332487616 <= E <= 140737488355328) by (clear - ER; lia).
  assert (FR' : 4096 <= F <= 140737488354816 /\ 4096 <= fl <= 140737488355327) by (clear - FRP FLRP; lia). destruct FR' as [FR' FLR'].
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
  set (Wp := fun a => E - 120 <= a < E - 104 \/ E - 272 <= a < E - 264).
  assert (WPOK : forall a, 0 <= a < 2 ^ 64 -> Wp a -> L5DKA.wp_ok L ar LB FF E SCRD SPA (docell E) F 3 W BX a).
  { intros a Ha Wa. subst Wp; cbn beta in Wa. apply (L5DKA.wp_frame L ar HI LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2 G). clear - Wa; lia. unfold docell. clear - Wa; lia. }
  destruct sto as [v0 v1|cap q].
  - (* [comment removed for export] *)
    destruct OST as (BT0 & _).
    pose proof (v5G4i_conc fx Rc MV (fun j => match j with 2%nat => E | 35%nat => qo | 40%nat => F | 41%nat => fl | 55%nat => fb | 58%nat => U Rc 1 | 63%nat => sd | 64%nat => Z.of_nat len | 66%nat => lenn | _ => 0 end)) as P. cbn beta iota in P.
    feed P ltac:(first [apply UR | apply U_to | sc ]).
    destruct P as (fx1 & R1 & M1v & MG1 & _ & pFZ & (pMS & pKS & pR1 & pR10 & pR11 & _ & pR20 & pR24 & p272 & p112 & p120)).
    apply (L5DKA.bstage L ar C HI LY HIok M model LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2 G W _ Mc modelc LKc crc Ac fx fx1 Rc 0x930e8 R1 RESIZE M1v Wp K BI pMS MG1).
    { intros a Ha Hn. apply pFZ. exact Ha. all: subst Wp; cbn beta in Hn; clear - Hn; lia. }
    { exact WPOK. }
    intros M1 model1 BI1 AH1 VIS1 MGM1 FRM1.
    assert (XS : forall a v, SPA <= a -> a + 8 <= E -> L5.u64_at RSEGS M1v a v -> L5.u64_at RSEGS M1 a v).
    { intros a v Ha Hb Hc. apply (proj1 (u64_at_vis (ahid Ac modelc) M1 a v ltac:(eapply avis_sub; [exact SV | clear - Ha; lia | clear - Hb; lia]) ltac:(clear - Ha ER; lia) ltac:(clear - Hb ER; lia))). rewrite VIS1. exact Hc. }
    apply (KF fx1 R1 M1 model1 BI1).
    + apply (rinvD_ks R E Rc R1 KS_v5G4i RI pKS). vm_compute; reflexivity.
    + intros x Hx. apply pKS. revert Hx. apply (L5K.incl_b [3; 4; 18; 19; 21; 22; 25; 26; 27]%nat). vm_compute; reflexivity.
    + exact pR1.
    + exact pR10.
    + rewrite pR11. f_equal. clear; lia.
    + exact pR20.
    + exact pR24.
    + intros a Ha N1 N2. apply FRM1. exact Ha. subst Wp; cbn beta. clear - N1 N2; lia.
    + unfold L5.bo_data. cbn [L5.bo_st]. apply XS. clear; lia. clear; lia. replace (F + 32 + 16) with (F + 48) by (clear; lia). exact p120.
    + apply XS. clear; lia. clear; lia. exact p112.
    + apply XS. clear; lia. clear; lia. exact p272.
  - (* [comment removed for export] *)
    destruct OST as (BT1 & O16 & O24 & _ & CAPR & Q8 & Q4096 & Q47 & _). assert (QAL : aligned q 8) by exact Q8.
    pose proof (CELLV (F + 32 + 24) q ltac:(clear; lia) ltac:(clear; lia) O24) as O24v. replace (F + 32 + 24) with (F + 56) in O24v by (clear; lia).
    assert (QRG : 0 <= q < 2 ^ 64) by (clear - Q4096 Q47 CAPR; lia).
    pose proof (v5G4d_conc fx Rc MV (fun j => match j with 2%nat => E | 35%nat => qo | 40%nat => F | 41%nat => fl | 55%nat => fb | 58%nat => U Rc 1 | 63%nat => sd | 64%nat => Z.of_nat len | 65%nat => q | 66%nat => lenn | _ => 0 end)) as P. cbn beta iota in P.
    feed P ltac:(first [apply UR | apply U_to | sc ]).
    destruct P as (fx1 & R1 & M1v & MG1 & _ & pFZ & (pMS & pKS & pR1 & pR10 & pR11 & _ & pR20 & pR24 & p272 & p112 & p120)).
    apply (L5DKA.bstage L ar C HI LY HIok M model LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2 G W _ Mc modelc LKc crc Ac fx fx1 Rc 0x930e8 R1 RESIZE M1v Wp K BI pMS MG1).
    { intros a Ha Hn. apply pFZ. exact Ha. all: subst Wp; cbn beta in Hn; clear - Hn; lia. }
    { exact WPOK. }
    intros M1 model1 BI1 AH1 VIS1 MGM1 FRM1.
    assert (XS : forall a v, SPA <= a -> a + 8 <= E -> L5.u64_at RSEGS M1v a v -> L5.u64_at RSEGS M1 a v).
    { intros a v Ha Hb Hc. apply (proj1 (u64_at_vis (ahid Ac modelc) M1 a v ltac:(eapply avis_sub; [exact SV | clear - Ha; lia | clear - Hb; lia]) ltac:(clear - Ha ER; lia) ltac:(clear - Hb ER; lia))). rewrite VIS1. exact Hc. }
    apply (KF fx1 R1 M1 model1 BI1).
    + apply (rinvD_ks R E Rc R1 KS_v5G4d RI pKS). vm_compute; reflexivity.
    + intros x Hx. apply pKS. revert Hx. apply (L5K.incl_b [3; 4; 18; 19; 21; 22; 25; 26; 27]%nat). vm_compute; reflexivity.
    + exact pR1.
    + exact pR10.
    + rewrite pR11. f_equal. clear; lia.
    + exact pR20.
    + exact pR24.
    + intros a Ha N1 N2. apply FRM1. exact Ha. subst Wp; cbn beta. clear - N1 N2; lia.
    + unfold L5.bo_data. cbn [L5.bo_st]. apply XS. clear; lia. clear; lia. exact p120.
    + apply XS. clear; lia. clear; lia. exact p112.
    + apply XS. clear; lia. clear; lia. exact p272.
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
  /\ (E - 384 + 384 <= o \/ o + 32 <= E - 384) /\ (o + 32 <= F \/ F + 512 <= o) /\ (o + 32 <= SH \/ SH + 64 <= o)
  /\ (o / 8 + 2147450880 + 4 <= F \/ F + 512 <= o / 8 + 2147450880) /\ (o / 8 + 2147450880 + 4 <= SH \/ SH + 64 <= o / 8 + 2147450880)
  /\ (o / 8 + 2147450880 + 4 <= E - 384 \/ E - 384 + 384 <= o / 8 + 2147450880).

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

Lemma len_le_cap Mk o b : L5.big_at RSEGS Mk o b -> Z.of_nat (L5.bo_len b) <= match L5.bo_st b with L5.BInl _ _ => 2 | L5.BDyn cap _ => cap end.
Proof. destruct b as [fb len sto]. intros (_ & _ & _ & OST). cbn [L5.bo_st L5.bo_len] in *. destruct sto; [destruct OST as (_ & _ & _ & X & _) | destruct OST as (_ & _ & _ & X & _)]; clear - X; lia. Qed.

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

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma g5_run (fx : FPState) Rc MV qo fb (len : nat) sto : rinvD R E Rc -> pf E F fl MV ->
  getr Rc (reg 26) = Z_to_bv 64 (qo + 8) -> ARGF MV qo ->
  L5.u64_at RSEGS MV (E - 320) (qo / 8 + 2147450880) -> L5.u64_at RSEGS MV (E - 352) ((qo + 8) / 8 + 2147450880) -> L5.u64_at RSEGS MV (E - 296) qo ->
  L5.big_at RSEGS MV qo (L5.BO fb len sto) ->
  exists (fx' : FPState) R' M1v, msteps RSEGS (st fx Rc 0x9313c MV) (st fx' R' (if (Z.of_nat len =? 0) then 0x931c4 else 0x9319c) M1v) /\ mem_grows MV M1v
    /\ (forall a, 0 <= a < 2 ^ 64 -> ~ (E - 136 <= a < E - 120) -> M1v (Z_to_bv 64 a) = MV (Z_to_bv 64 a))
    /\ (forall x, In x [2; 3; 4; 8; 9; 18; 20; 22; 23; 24; 25; 26; 27]%nat -> getr R' (reg x) = getr Rc (reg x))
    /\ L5.u64_at RSEGS M1v (E - 136) (L5.bo_data qo (L5.BO fb len sto)) /\ L5.u64_at RSEGS M1v (E - 128) (Z.of_nat len)
    /\ (Z.of_nat len <> 0 -> getr R' (reg 19) = Z_to_bv 64 (Z.of_nat len - 1) /\ getr R' (reg 21) = Z_to_bv 64 18446744073709551615).
Proof.
  intros RI PF X26 ((ORP & ORG & O8) & OBIG & OZ & OW & OFR & OF & OSH & SOF & SOSH & SOFR) S64 S32 S88 OB.
  unfold pf in PF. destruct PF as (W352 & IMGC & CSB & CUAR & FDEFv & FWv & FSHWv & FLCv & FLWv).
  pose proof (NUM L ar HI R LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER) as ((FRG & FLRG & ERG) & FRP & FLRP & ALF & FBIG & FLBIG & FLA & SFA & SFLA & SFB).
  pose proof RI as (X2 & X8 & X9 & X3 & X4 & XSB).
  assert (ER' : 140735332487616 <= E <= 140737488355328) by (clear - ER; lia).
  assert (OAL : aligned qo 8) by exact O8.
  destruct OB as (O0 & FBR & OL8 & OST). cbn [L5.bo_fb L5.bo_len L5.bo_st] in *. unfold L5.bo_data. cbn [L5.bo_st].
  assert (FBR' : 0 <= fb <= 255) by (clear - FBR; lia).
  assert (LR : 0 <= Z.of_nat len <= 134217728 /\ 0 <= Z.of_nat len < 2 ^ 64).
  { destruct sto; [destruct OST as (_ & _ & _ & X & _) | destruct OST as (_ & _ & _ & X & X' & _)]; clear - X + clear - X X'; lia. }
  destruct LR as [LR LRG].
  assert (FZ8 : forall (M' : word -> option byte), (forall a : Z, 0 <= a < 2 ^ 64 -> ~ (E - 136 <= a < E - 136 + 16) -> M' (Z_to_bv 64 a) = MV (Z_to_bv 64 a)) ->
                forall a, 0 <= a < 2 ^ 64 -> ~ (E - 136 <= a < E - 120) -> M' (Z_to_bv 64 a) = MV (Z_to_bv 64 a)).
  { intros M' HFZ a Ha Hn. apply HFZ. exact Ha. clear - Hn; lia. }
  destruct sto as [v0 v1|cap q]; destruct (Z.eqb_spec (Z.of_nat len) 0) as [L0|LN].
  - destruct OST as (BT0 & _). assert (L00 : 0 <= Z.of_nat len <= 0) by (clear - L0; lia).
    pose proof (v5G5i0_conc fx Rc MV (fun j => match j with 2%nat => E | 35%nat => qo | 40%nat => F | 58%nat => U Rc 1 | 60%nat => fb | 67%nat => Z.of_nat len | _ => 0 end)) as P. cbn beta iota in P.
    feed P ltac:(first [apply UR | apply U_to | sc ]).
    destruct P as (fx1 & R1 & M1v & MG1 & _ & pFZ & (pMS & pKS & _ & _ & _ & p128 & p136)).
    exists fx1, R1, M1v. split. exact pMS. split. exact MG1. split. exact (FZ8 M1v pFZ).
    split. { intros x Hx. apply pKS. revert Hx. apply (L5K.incl_b [2; 3; 4; 8; 9; 18; 20; 22; 23; 24; 25; 26; 27]%nat). vm_compute; reflexivity. }
    split. exact p136. split. rewrite L0. exact p128. intros X. exfalso. exact (X L0).
  - destruct OST as (BT0 & _). assert (L1 : 1 <= Z.of_nat len <= 134217728) by (clear - LN LR; lia).
    pose proof (v5G5in_conc fx Rc MV (fun j => match j with 2%nat => E | 35%nat => qo | 40%nat => F | 58%nat => U Rc 1 | 60%nat => fb | 67%nat => Z.of_nat len | _ => 0 end)) as P. cbn beta iota in P.
    feed P ltac:(first [apply UR | apply U_to | sc ]).
    destruct P as (fx1 & R1 & M1v & MG1 & _ & pFZ & (pMS & pKS & _ & _ & p19 & p21 & p128 & p136)).
    exists fx1, R1, M1v. split. exact pMS. split. exact MG1. split. exact (FZ8 M1v pFZ).
    split. { intros x Hx. apply pKS. revert Hx. apply (L5K.incl_b [2; 3; 4; 8; 9; 18; 20; 22; 23; 24; 25; 26; 27]%nat). vm_compute; reflexivity. }
    split. exact p136. split. exact p128. intros _. split. exact p19. exact p21.
  - destruct OST as (BT1 & O16 & O24 & _ & CAPR & Q8 & Q4096 & Q47 & _). assert (L00 : 0 <= Z.of_nat len <= 0) by (clear - L0; lia).
    assert (QRG : 0 <= q < 2 ^ 64 /\ 4096 <= q <= 140737488355328) by (clear - Q4096 Q47 CAPR; lia). destruct QRG as [QRG QRG']. assert (QAL : aligned q 8) by exact Q8.
    pose proof (v5G5d0_conc fx Rc MV (fun j => match j with 2%nat => E | 35%nat => qo | 40%nat => F | 58%nat => U Rc 1 | 60%nat => fb | 67%nat => Z.of_nat len | 68%nat => q | _ => 0 end)) as P. cbn beta iota in P.
    feed P ltac:(first [apply UR | apply U_to | sc ]).
    destruct P as (fx1 & R1 & M1v & MG1 & _ & pFZ & (pMS & pKS & _ & _ & _ & p128 & p136)).
    exists fx1, R1, M1v. split. exact pMS. split. exact MG1. split. exact (FZ8 M1v pFZ).
    split. { intros x Hx. apply pKS. revert Hx. apply (L5K.incl_b [2; 3; 4; 8; 9; 18; 20; 22; 23; 24; 25; 26; 27]%nat). vm_compute; reflexivity. }
    split. exact p136. split. rewrite L0. exact p128. intros X. exfalso. exact (X L0).
  - destruct OST as (BT1 & O16 & O24 & _ & CAPR & Q8 & Q4096 & Q47 & _). assert (L1 : 1 <= Z.of_nat len <= 134217728) by (clear - LN LR; lia).
    assert (QRG : 0 <= q < 2 ^ 64 /\ 4096 <= q <= 140737488355328) by (clear - Q4096 Q47 CAPR; lia). destruct QRG as [QRG QRG']. assert (QAL : aligned q 8) by exact Q8.
    pose proof (v5G5dn_conc fx Rc MV (fun j => match j with 2%nat => E | 35%nat => qo | 40%nat => F | 58%nat => U Rc 1 | 60%nat => fb | 67%nat => Z.of_nat len | 68%nat => q | _ => 0 end)) as P. cbn beta iota in P.
    feed P ltac:(first [apply UR | apply U_to | sc ]).
    destruct P as (fx1 & R1 & M1v & MG1 & _ & pFZ & (pMS & pKS & _ & _ & p19 & p21 & p128 & p136)).
    exists fx1, R1, M1v. split. exact pMS. split. exact MG1. split. exact (FZ8 M1v pFZ).
    split. { intros x Hx. apply pKS. revert Hx. apply (L5K.incl_b [2; 3; 4; 8; 9; 18; 20; 22; 23; 24; 25; 26; 27]%nat). vm_compute; reflexivity. }
    split. exact p136. split. exact p128. intros _. split. exact p19. exact p21.
Qed.

(* [comment removed for export] *)
Lemma binv_wk W W1 BX Mc modelc LKc crc Ac : binv W BX Mc modelc LKc crc Ac -> (forall a, L5.outside W1 a -> L5.outside W a) -> binv W1 BX Mc modelc LKc crc Ac.
Proof.
  intros (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10) WW. unfold L5AFK.binv.
  split. exact B1. split. exact B2. split. exact B3. split. exact B4. split. exact B5. split. exact B6.
  split. { apply (ek_W L ar LB FF E SCRD W1 W M Mc B7). exact WW. } split. exact B8. split. exact B9. exact B10.
Qed.

Local Ltac hyp9 W1x BIx NWx := first [exact LY | exact HIok | exact G | exact ER | exact EA | exact HSCR0 | exact HSCR | exact BIx | exact HSSH | exact NWx | exact HSC8 | idtac].

Lemma g5 (fx : FPState) Rc Mc modelc W W1 BX LKc crc Ac qo (bq : L5.bigobj) wq :
  binv W BX Mc modelc LKc crc Ac -> rinvD R E Rc -> getr Rc (reg 26) = Z_to_bv 64 (qo + 8) ->
  L5.u64_at RSEGS Mc (E - 320) (qo / 8 + 2147450880) -> L5.u64_at RSEGS Mc (E - 352) ((qo + 8) / 8 + 2147450880) -> L5.u64_at RSEGS Mc (E - 296) qo ->
  aobj FF qo 32 -> tob (BX ++ LB) Mc qo bq wq -> Z.of_nat (L5.bo_len bq) <= 2 ^ 24 ->
  (forall a, in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> L5.outside W1 a) ->
  (forall a, L5.outside W1 a -> L5.outside W a /\ L5.outside [(L5.bo_data qo bq, 8 * Z.of_nat (L5.bo_len bq))] a) ->
  (forall (fx' : FPState) R' M' model',
      binv W1 BX M' model' LKc crc Ac -> rinvD R E R' ->
      (forall x, In x [3; 4; 18; 20; 22; 24; 25; 26; 27]%nat -> getr R' (reg x) = getr Rc (reg x)) ->
      (forall a, 0 <= a < 2 ^ 64 -> ~ (E - 136 <= a < E - 120) -> ~ (E - 392 <= a < E - 384) -> ~ (L5.bo_data qo bq <= a < L5.bo_data qo bq + 8 * Z.of_nat (L5.bo_len bq)) ->
                 M' (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)) ->
      L5.u64_at RSEGS M' (E - 136) (L5.bo_data qo bq) -> L5.u64_at RSEGS M' (E - 128) (Z.of_nat (L5.bo_len bq)) ->
      L5.defined M' (L5.bo_data qo bq) (8 * Z.of_nat (L5.bo_len bq)) ->
      srealizes RSEGS SCFG (cfg (fx:=fx') R' 0x931c4 M' model') K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc 0x9313c Mc modelc) K.
Proof.
  intros BI0 RI X26 S64 S32 S88 AOQ TQ LEN24 NW1 WSUB KF. pose proof TQ as (OBQ & OLQ & SZQ & INQ).
  pose proof (binv_wk W W1 BX Mc modelc LKc crc Ac BI0 (fun a X => proj1 (WSUB a X))) as BI.
  pose proof (arg_facts L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G W1 BX Mc modelc LKc crc Ac qo BI AOQ SZQ)
    as ((ORP & ORG & O8) & OBIG & OZ & OW & OFR & OF & OSH & SOF & SOSH & SOFR & U8V & U64V & OCL).
  pose proof (pf_of_binv L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G W1 BX Mc modelc LKc crc Ac BI) as PF.
  pose proof (frm_vis W1 BX Mc modelc LKc crc Ac _ _ BI S64 ltac:(clear; lia) ltac:(clear; lia)) as S64v.
  pose proof (frm_vis W1 BX Mc modelc LKc crc Ac _ _ BI S32 ltac:(clear; lia) ltac:(clear; lia)) as S32v.
  pose proof (frm_vis W1 BX Mc modelc LKc crc Ac _ _ BI S88 ltac:(clear; lia) ltac:(clear; lia)) as S88v.
  assert (AOQ' : aobj FF' qo 32) by (apply aobj_cons; exact AOQ).
  pose proof (len_le_cap Mc qo bq OBQ) as LCQ.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (ED : (E - 136) mod 8 = 0 /\ 17591916560912 <= (E - 136) / 8 /\ (E - 136) / 8 + 1 <= 17592186044416) by (clear - EA ER; unfold aligned in EA; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  destruct ED as (ED8 & EDL & EDH).
  assert (VZ : L5KA.zeros_at (mrestrict (ahid Ac modelc) Mc) ((E - 136) / 8 + 2147450880) 1).
  { eapply L5ADVHC.stkz_vis; hyp9 W1 BI NW1; [ clear - HSCR; lia | clear; lia | exact ED8 | clear; lia ]. }
  pose proof BI as (B1 & _ & _ & _ & _ & B6 & _).
  pose proof (vis_pack L ar C HI LY HIok (BX ++ LB) FF' LKc crc Ac Mc modelc B1) as (_ & VIS & _).
  pose proof G as G'. destruct G' as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG' F32 FLA' FLR FLBIG' NCF NCS]. clear OWNAG HH2 NCF NCS FLNC.
  set (MV := mrestrict (ahid Ac modelc) Mc) in *.
  assert (DSC : L5.defined MV (E - 400) 400).
  { apply (proj2 (defined_vis (ahid Ac modelc) Mc (E - 400) 400 (VIS (E - 400) 400 ltac:(clear - SLO HSCR; lia) ltac:(clear - ER; lia)))).
    eapply astk_defined. exact B6. clear - HSCR; lia. clear; lia. }
  destruct bq as [fb len sto].
  assert (OBQv : L5.big_at RSEGS MV qo (L5.BO fb len sto)).
  { destruct OBQ as (O0 & FBR & OL8 & OST). unfold L5.big_at. cbn [L5.bo_fb L5.bo_len L5.bo_st] in *. split. apply U8V. exact O0. split. exact FBR.
    split. apply U64V. clear; lia. clear; lia. exact OL8.
    destruct sto as [v0 v1|cap q].
    - destruct OST as (T0 & C16 & C24 & REST). split. exact T0. split. apply U64V. clear; lia. clear; lia. exact C16. split. apply U64V. clear; lia. clear; lia. exact C24. exact REST.
    - destruct OST as (T0 & C16 & C24 & REST). split. exact T0. split. apply U64V. clear; lia. clear; lia. exact C16. split. apply U64V. clear; lia. clear; lia. exact C24. exact REST. }
  destruct (g5_run fx Rc MV qo fb len sto RI PF X26 (conj (conj ORP (conj ORG O8)) (conj OBIG (conj OZ (conj OW (conj OFR (conj OF (conj OSH (conj SOF (conj SOSH SOFR))))))))) S64v S32v S88v OBQv)
    as (fx1 & R1 & M1v & pMS & pMG & pAG & pKS & p136 & p128 & pHEAD).
  cbn [L5.bo_len] in *.
  assert (RI1 : rinvD R E R1).
  { apply (rinvD_keep R E Rc R1 RI). intros k Hk0. apply pKS. revert Hk0. apply (L5K.incl_b DIDX). vm_compute; reflexivity. }
  assert (KS9 : forall x, In x [3; 4; 18; 20; 22; 24; 25; 26; 27]%nat -> getr R1 (reg x) = getr Rc (reg x)).
  { intros x Hx. apply pKS. revert Hx. apply (L5K.incl_b [3; 4; 18; 20; 22; 24; 25; 26; 27]%nat). vm_compute; reflexivity. }
  set (dst := L5.bo_data qo (L5.BO fb len sto)) in *.
  destruct (L5AFK.vis_facts L ar C HI LY HIok M model LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2 G W1 _ Mc modelc LKc crc Ac BI) as (_ & _ & _ & (_ & _ & _ & SV & _)).
  assert (WPF : forall a, E - 136 <= a < E - 120 -> L5DKA.wp_ok L ar LB FF E SCRD SPA (docell E) F 3 W1 BX a).
  { intros a Wa. apply (L5DKA.wp_frame L ar HI LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2 G). clear - Wa; lia. unfold docell. clear - Wa; lia. }
  destruct (Z.eqb_spec (Z.of_nat len) 0) as [L0|LN].
  - (* [comment removed for export] *)
    set (Wp := fun a => E - 136 <= a < E - 120).
    apply (L5DKA.bstage L ar C HI LY HIok M model LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2 G W1 _ Mc modelc LKc crc Ac fx fx1 Rc 0x9313c R1 0x931c4 M1v Wp K BI pMS pMG).
    { intros a Ha Hn. apply pAG. exact Ha. exact Hn. }
    { intros a Ha Wa. exact (WPF a Wa). }
    intros M1 model1 BI1 AH1 VIS1 MGM1 FRM1.
    assert (XS : forall a v, SPA <= a -> a + 8 <= E -> L5.u64_at RSEGS M1v a v -> L5.u64_at RSEGS M1 a v).
    { intros a v Ha Hb Hc. apply (proj1 (u64_at_vis (ahid Ac modelc) M1 a v ltac:(eapply avis_sub; [exact SV | clear - Ha; lia | clear - Hb; lia]) ltac:(clear - Ha ER; lia) ltac:(clear - Hb ER; lia))). rewrite VIS1. exact Hc. }
    apply (KF fx1 R1 M1 model1 BI1 RI1 KS9).
    + intros a Ha N1 _ _. apply FRM1. exact Ha. exact N1.
    + apply XS. clear; lia. clear; lia. exact p136.
    + apply XS. clear; lia. clear; lia. exact p128.
    + intros i Hi. exfalso. clear - Hi L0. lia.
  - (* [comment removed for export] *)
    destruct (pHEAD LN) as (p19 & p21).
    assert (LENR : 1 <= Z.of_nat len <= 134217727) by (clear - LN LEN24; lia).
    pose proof (dreg_facts W1 BX Mc modelc LKc crc Ac qo (L5.BO fb len sto) wq (Z.of_nat len) BI AOQ' (conj OBQ (conj OLQ (conj SZQ INQ))) ltac:(clear - LENR; lia) LCQ)
      as ((QF1 & QF2 & QF3 & QF4) & QNS & QOI & QZ & QDEF & QWR & QVIS).
    cbv zeta in *. fold MV in QZ, QDEF, QWR, QVIS. fold dst in QF1, QF2, QF3, QF4, QNS, QOI, QZ, QDEF, QWR, QVIS.
    destruct PF as (_ & IMGC0 & CSB0 & CUAR0 & _).
    assert (CEIL : ahl_ceil ar + 4096 <= E - SCRD) by (clear - SLO; lia).
    assert (NV : forall a, 0 <= a < 6504448 \/ 2147450880 <= a < 17594333495296 -> ~ (E - 136 <= a < E - 120)) by (intros a Ha; clear - Ha ER; lia).
    assert (ZC : L5ADVGZ.zctx E dst (Z.of_nat len) M1v).
    { constructor.
      - exact ER.
      - exact EA.
      - exact LENR.
      - eapply L5.writable_grows. exact pMG. apply (L5C.writable_of_defined RSEGS). exact DSC. clear - ER; lia. clear - ER; lia.
      - split. { intros i Hi. rewrite pAG. apply IMGC0. exact Hi. clear - Hi; lia. apply NV. clear - Hi; lia. }
        split. { eapply L5C.u64_at_agree. 4: exact CSB0. 2: clear; lia. 2: clear; lia. intros j Hj. apply pAG. clear - Hj; lia. apply NV. clear - Hj; lia. }
        unfold L5.u32_at in *. rewrite (L5C.rdn_agree RSEGS MV M1v 4 911168 ltac:(clear; lia) ltac:(cbn; clear; lia)). exact CUAR0.
        intros i Hi. apply pAG. cbn in Hi; clear - Hi; lia. apply NV. cbn in Hi; clear - Hi; lia.
      - exact p136.
      - apply (L5KA.zeros_at_agree1 MV M1v). 2: exact VZ. intros i Hi. apply pAG. clear - Hi EDL EDH; lia. apply NV. clear - Hi EDL EDH; lia.
      - unfold L5ADVGZ.nsh, L5ADVGZ.oim. unfold L5ADVGL.nsh, L5ADVGL.oim in QNS, QOI. split. exact QF1. split. exact QF4. split. exact QF2. split. exact QNS. exact QOI.
      - eapply L5.writable_grows. exact pMG. exact QWR.
      - apply (L5KA.zeros_at_agree1 MV M1v). 2: exact QZ. intros i Hi. apply pAG.
        + Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). clear - Hi QF1 QF4 LENR; lia.
        + Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). apply NV. clear - Hi QF1 QF4 LENR; lia.
      - Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). clear - QF3 CEIL HSCR; lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    pose proof RI1 as (Y2 & Y8 & Y9 & Y3 & Y4 & YSB).
    assert (ZR : L5ADVGZ.zregs E R1 R1 (Z.of_nat len - 1)).
    { unfold L5ADVGZ.zregs. split. exact Y2. split. exact Y8. split. exact Y9. split. exact YSB. split. exact p19. split. exact p21. intros x _. reflexivity. }
    destruct (L5ADVGZ.gzero_run E dst (Z.of_nat len) fx1 R1 M1v ZC ZR) as (fx2 & R2 & M2v & zMS & (zMG & zAG) & (z2 & z8 & z9 & z23 & zK)).
    set (Wp := fun a => E - 136 <= a < E - 120 \/ L5ADVGZ.FPZ E dst (Z.of_nat len) a).
    apply (L5DKA.bstage L ar C HI LY HIok M model LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2 G W1 _ Mc modelc LKc crc Ac fx fx2 Rc 0x9313c R2 0x931c4 M2v Wp K BI
             (msteps_trans _ _ _ _ pMS zMS) (mem_grows_trans _ _ _ pMG zMG)).
    { intros a Ha Hn. rewrite zAG. apply pAG. exact Ha. intros X. apply Hn. left. exact X. exact Ha. intros X. apply Hn. right. exact X. }
    { intros a Ha [Wa|[Wa|Wa]].
      - exact (WPF a Wa).
      - eapply L5ADVHC.wp_scratch; hyp9 W1 BI NW1. clear - Wa HSCR; lia.
      - apply (dreg_wp W1 BX Mc modelc LKc crc Ac qo (L5.BO fb len sto) wq (Z.of_nat len) a BI AOQ' (conj OBQ (conj OLQ (conj SZQ INQ))) LCQ Wa).
        intros Hc Ho. destruct (WSUB a Ho) as (_ & O2). apply (O2 (dst, 8 * Z.of_nat len)). left; reflexivity. unfold L5.in_rng; cbn [fst snd]. exact Wa. }
    intros M1 model1 BI1 AH1 VIS1 MGM1 FRM1.
    assert (XS : forall a v, SPA <= a -> a + 8 <= E -> L5.u64_at RSEGS M2v a v -> L5.u64_at RSEGS M1 a v).
    { intros a v Ha Hb Hc. apply (proj1 (u64_at_vis (ahid Ac modelc) M1 a v ltac:(eapply avis_sub; [exact SV | clear - Ha; lia | clear - Hb; lia]) ltac:(clear - Ha ER; lia) ltac:(clear - Hb ER; lia))). rewrite VIS1. exact Hc. }
    assert (RI2 : rinvD R E R2).
    { apply (rinvD_keep R E R1 R2 RI1). intros k Hk0. unfold DIDX in Hk0. cbn [In] in Hk0. clear - Hk0 z2 z8 z9 z23 zK Y2 Y8 Y9 YSB.
      destruct Hk0 as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]].
      - rewrite z2; symmetry; exact Y2.
      - apply zK. unfold L5ADVGZ.zkept. left; reflexivity.
      - apply zK. unfold L5ADVGZ.zkept. right; left; reflexivity.
      - rewrite z8; symmetry; exact Y8.
      - rewrite z9; symmetry; exact Y9.
      - rewrite z23; symmetry; exact YSB. }
    apply (KF fx2 R2 M1 model1 BI1 RI2).
    + intros x Hx. rewrite <- (KS9 x Hx). apply zK. revert Hx. apply (L5K.incl_b [3; 4; 18; 20; 22; 24; 25; 26; 27]%nat). vm_compute; reflexivity.
    + intros a Ha N1 N2 N3. apply FRM1. exact Ha. subst Wp; cbn beta. unfold L5ADVGZ.FPZ. intros [X|[X|X]]; [exact (N1 X) | exact (N2 X) | exact (N3 X)].
    + apply XS. clear; lia. clear; lia. exact (L5ADVGZ.zc_vq _ _ _ _ (L5ADVGZ.zctx_keep E dst (Z.of_nat len) M1v M2v ZC (conj zMG zAG))).
    + apply XS. clear; lia. clear; lia. eapply L5C.u64_at_agree. 4: exact p128. 2: clear - ER; lia. 2: clear - ER; lia.
      intros j Hj. apply zAG. clear - Hj ER; lia. unfold L5ADVGZ.FPZ. clear - Hj QF3 CEIL HSCR. lia.
    + eapply L5.defined_grows. exact MGM1. intros i Hi. rewrite <- QVIS by (clear - Hi; lia). apply QDEF. exact Hi.
Qed.

End DIV.
End WithIface.
End SCFG_1.
End L5ADVGA.
