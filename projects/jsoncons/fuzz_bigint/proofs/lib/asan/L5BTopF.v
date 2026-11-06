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
     AsanAcct AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue BigModel BigFactsRun BigFactsDigits L5Defs L5Kn L5KnA L5Core L5LazyA L5DefsAB0
     L5CoreAB0 L5CoreSpecsAB0 L5StepAB0 L5CoreBB0 L5ParseSpecsAB0 L5OpmodSpecsAB0 L5BStrInit L5BCopyS L5BCopyS16 L5BOpModF L5ArithSpecsB0 L5ParseSpecsBB0 L5BStrctorS L5BDetailG L5BFrameK L5BTopP1 L5BTopP2 L5BTopH L5BTopD L5BTopE L5DivSpecsAB0 L5UnwindSpecsAB0 L5BTopX.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Module L5ATF.
Import L5A. Import L5CA. Import L5CSA. Import L5SA. Import L5CB. Import L5ADH. Import L5ATH.
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Section WithIface.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : as0_layout L C.
Hypothesis HIok : asan_iface_ok L ar C SCFG HI.
Section FINAL.
Variable IL : icpt_layout.
Variables (SCRo SCRf D1 D2 D3 K1 K2 SCRs d1 d2 d3 : Z) (bytes1 bytes2 : Z -> Z) (st0 : L5USA.XS).
Hypothesis Hsi : strinit_spec L ar HI.
Hypothesis Hdel : opdel_sized_spec L ar HI.
Hypothesis Hcp : copy_spec L ar HI.
Hypothesis Hcs : L5PSB.cstr_specB L ar IL HI.
Hypothesis Hsc : L5ASCS.strctor_norm_specB L ar IL HI SCRs.
(* [comment removed for export] *)
Hypothesis Hom1 : L5BOMF.opmodf1_spec L ar HI L5USA.XS (L5USA.xs_pre ar) L5USA.xs_foot (L5USA.e2_landed L) (L5USA.e3_landed L) SCRo SCRf D1 D2 D3 K1 bytes1.
Hypothesis Hom2 : L5BOMF.opmodf2_spec L ar HI SCRo SCRf D1 D2 D3 K2 bytes2.
Hypothesis HDO : D1 <= d1 /\ D2 <= d2 /\ D3 <= d3.
Hypothesis HD : 5 <= d1 /\ 2 <= d2 /\ 1 <= d3.
Hypothesis HK1 : 0 <= K1 /\ forall c, 0 <= c -> 0 <= bytes1 c.
Hypothesis HK2 : 0 <= K2 /\ forall c, 0 <= c -> 0 <= bytes2 c.
Hypothesis HBM : (forall c c', c <= c' -> bytes1 c <= bytes1 c') /\ (forall c c', c <= c' -> bytes2 c <= bytes2 c').
(* [comment removed for export] *)
Hypothesis He1 : L5USA.e1_chainA_spec L ar HI IL.
Hypothesis Hcatch1 : L5USA.catch1A_spec L ar HI.
Hypothesis Hcatch2 : L5USA.catch2A_spec L ar HI.
Hypothesis Hcatch3 : L5USA.catch3A_spec L ar HI.
Hypothesis UNWL : L5USA.as0_unw_layout L.
Hypothesis HCR2 : forall c, 0 <= c -> L5USA.EXC23_SZ + L5USA.REF2_SZ <= bytes1 c + (64 + (8 * c + bytes2 c + 8 * Z.max c 8)).
Hypothesis HCR3 : forall c, 0 <= c -> L5USA.EXC23_SZ + L5USA.MSG3_SZ + L5USA.REF3_SZ <= 64 + (8 * c + bytes2 c + 8 * Z.max c 8).
Local Notation REST := (bytes1 268 + (64 + (8 * 268 + bytes2 268 + 8 * Z.max 268 8))).

Theorem top_ok SCRT (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
      (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (data sp r : Z) (cs : list byte) :
  let n := Z.of_nat (length cs) in
  let NEED := str_cap n + (2 * 64 + (2 * L5PSA.vblk (length (snd (L5PSA.split_sign (map bv_unsigned cs)))) + REST)) in
  let crmin := L5OMA.adebits L cr (5 + (K1 + K2 + 3)) NEED in
  208 + 4304 <= SCRT -> 208 + COPY_SCR <= SCRT -> 208 + L5PSB.CSTR_SCRB <= SCRT -> 0 <= SCRs /\ 208 + SCRs <= SCRT -> 0 <= SCRo /\ 208 + SCRo <= SCRT ->
  SCRo + 16 <= SCRf /\ COPY_SCR + 32 <= SCRf /\ 208 + SCRf <= SCRT ->
  ri_inv HI LB FF LK cr A M (vml_of model) -> amodel_ok A model -> K [] ->
  getr R 10%bv = Z_to_bv 64 data -> getr R 11%bv = Z_to_bv 64 n -> 0 <= n < 2 ^ 26 ->
  getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r ->
  getr R 2%bv = Z_to_bv 64 sp -> sp mod 16 = 0 -> getr R 4%bv = Z_to_bv 64 (hl_tp L) -> astk ar M sp SCRT ->
  ffrk 1 FF LK d1 -> ffrk 2 FF LK d2 -> ffrk 3 FF LK (d3 + 1) -> ffrs FF sp ->
  L5OMA.stksh ar M (sp - SCRT) -> SCRT mod 8 = 0 -> SCRo mod 8 = 0 -> getr R 3%bv = Z_to_bv 64 67584 ->      (* [comment removed for export] *)
  L5.img_clear M 0x10000 0x3c000 ->
  rdn RSEGS M (Z_to_bv 64 data) (length cs) = Some cs -> 0 <= data /\ data + n <= 2 ^ 47 ->
  (n = 0 \/ exists b m, In (b, m) LB /\ b <= data /\ data + n <= b + m) ->
  (forall Mk, L5ATD.img_same L ar M Mk -> L5USA.xs_pre ar st0 Mk) ->
  L5OMA.acredit_for L cr (5 + (K1 + K2 + 3)) NEED ->
  208 + L5USA.CATCH_SCR <= SCRT -> L5USA.CHAIN_SCR <= SCRs -> SCRs mod 8 = 0 ->
  (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) cr' (LK' : list fframe) (A' : list (Z * Z)),
      getr R' 10%bv = Z_to_bv 64 0 -> regs_preserved R R' ->
      ahpres L ar LB FF sp SCRT L5ATX.UNWW M M' -> (exists st', L5USA.xs_pre ar st' M') -> credit_le crmin cr' ->      (* [comment removed for export] *)
      model_rt model model' -> incl A A' -> amodel_ok A' model' -> L5USA.lk_bound LK LK' ->
      ri_inv HI LB FF LK' cr' A' M' (vml_of model') ->
      srealizes RSEGS SCFG (cfg (fx:=fx') R' r M' model') K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) R L5ATE.TOP M model) K.
Proof.
  intros n NEED crmin HSCR HS_COPY HS_CS HS_SC HS_OM HS_OMF HH AM HK G10 G11 NR G1 RA G2 A16 G4 STK FFR1 FFR2 FFR3 FFRS STKSH HSCR8 HSO8 G3 IMG0 RDN DRG0 SRCB XSP CRF HS_CATCH HS_E1 HSCs8 KONT.
  apply (L5ATE.top_norm_ok L ar C HI LY HIok IL L5USA.XS (L5USA.xs_pre ar) L5USA.xs_foot (L5USA.e2_landed L) (L5USA.e3_landed L) SCRo SCRf D1 D2 D3 K1 K2 SCRs d1 d2 d3 bytes1 bytes2 st0
           Hsi Hdel Hcp Hcs Hsc Hom1 Hom2 HDO HD HK1 HK2 HBM SCRT fx R M model K LB FF LK cr A data sp r cs
           HSCR HS_COPY HS_CS HS_SC HSCs8 HS_OM HS_OMF HH AM HK G10 G11 NR G1 RA G2 A16 G4 STK FFR1 FFR2 FFR3 FFRS STKSH HSCR8 HSO8 G3 IMG0 RDN DRG0 SRCB XSP CRF).
  - (* [comment removed for export] *)
    intros V2 cls F fl LK2 M2 model2 G SE CLS V2A. fold n. fold NEED. fold crmin.
    pose proof G as G'. destruct G' as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG F32 FLA FLR FLBIG NCF NCS].
    assert (V2R : 140735332487424 <= V2 <= 140737488355328) by (clear - SPT SLO SPC CLS HSCR; lia).
    assert (V2S : V2 + cls <= 140737488355328) by (clear - SPC; lia).
    assert (UR1 : U R 1 = r). { apply U_of. rewrite <- r1. exact G1. destruct RA as [X _]. clear - X; lia. }
    assert (G2' : getr R (reg 2) = Z_to_bv 64 (V2 + cls)). { rewrite <- SE. rewrite <- r2. exact G2. }
    assert (G4' : getr R (reg 4) = Z_to_bv 64 (hl_tp L)). { rewrite <- r4. exact G4. }
    assert (G3' : getr R (reg 3) = Z_to_bv 64 67584). { replace (reg 3) with (3%bv : bv 5) by (apply bv_eq; reflexivity). exact G3. }
    assert (KFX : forall (fxf : FPState) Rf Mf modelf LKf Af crf, regs_preserved R Rf -> getr Rf (reg 10) = Z_to_bv 64 0 -> ahpres L ar LB FF (V2 + cls) SCRT L5ATX.UNWW M Mf ->
               (exists st', L5USA.xs_pre ar st' Mf) ->
               model_rt model modelf -> incl A Af -> amodel_ok Af modelf -> L5USA.lk_bound LK LKf -> credit_le crmin crf -> ri_inv HI LB FF LKf crf Af Mf (vml_of modelf) ->
               srealizes RSEGS SCFG (cfg (fx:=fxf) Rf r Mf modelf) K).
    { intros fxf Rf Mf modelf LKf Af crf RPf R10f AHf XSf RTf IAf AMf LKBf CRLf HHf.
      apply (KONT fxf Rf Mf modelf crf LKf Af). rewrite r10. exact R10f. exact RPf. rewrite SE. exact AHf. exact XSf. exact CRLf. exact RTf. exact IAf. exact AMf. exact LKBf. exact HHf. }
    assert (HSCR' : 208 + 4096 <= SCRT) by (clear - HSCR; lia).
    assert (STKSH' : L5OMA.stksh ar M (V2 + cls - SCRT)) by (rewrite <- SE; exact STKSH).
    exact (L5ATX.pads_okX L ar C HI LY HIok Hdel R M model K LB FF LK A V2 cls r SCRT F fl LK2 M2 model2 cr G CLS V2A V2R V2S HK RA UR1 G2' G4' G3'
             HSCR' HSCR8 STKSH' UNWL HS_CATCH crmin KFX Hcatch1 Hcatch2 Hcatch3 SCRo K1 K2 bytes1 bytes2 ltac:(clear - HS_OM HS_OMF; lia) HK1 HK2 HCR2 HCR3 IL SCRs st0 He1 HS_SC HS_E1 HSCs8 XSP).
  - (* [comment removed for export] *)
    intros fx' R' M' model' cr' LK' A' R10' RP' AH' CRL' RT' IA' AM' LKI' HH''.
    apply (KONT fx' R' M' model' cr' LK' A' R10' RP'). 3: exact CRL'. 3: exact RT'. 3: exact IA'. 3: exact AM'. 4: exact HH''.
    + apply (L5ATX.ahpres_W L ar LB FF sp SCRT [] L5ATX.UNWW M M' AH'). intros a _ rr [].
    + (* [comment removed for export] *)
      exists st0. apply XSP. pose proof STK as (_ & SLO' & SHI' & SPT' & _). split.
      * intros a Ha NS. apply (proj1 AH'). split. clear - Ha; lia. split. 2:{ intros rr []. }
        right; right; left. rewrite (aly_img_lo L C LY), (aly_img_hi L C LY). split. exact Ha. exact NS.
      * intros a Ha. apply (proj1 AH'). split. clear - Ha SPT'; lia. split. 2:{ intros rr []. }
        right; left. split. clear - Ha; lia. clear - Ha SHI' HSCR; lia.
    + apply L5USA.lk_bound_incl. exact LKI'.
Qed.
End FINAL.
End WithIface.
End SCFG_1.
End L5ATF.
