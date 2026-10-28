(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.LeanFeed.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import LibIface
     AsanAcct AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5CoreKit L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b L5StepAR_b L5CoreBR_b L5ADetailHR_b L5AFrameKR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HeapIfaceABx PmLayout PmLayoutA PnLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmModelFactsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStatics PmStaticsA PnStatics PnStaticsA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PnSpecsAa_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgSrc PgV8. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgSrcA_b PgV8A_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnModel PnRun. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnRunA_b PnRunAa_b PnStepA_b PnAReset1_b PnAHarnessStmts_b PnAHarnessKit_b PnAHarnessP2_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module PNHA2.
Import L5A. Import L5CA. Import L5SAR. Import PNHAS.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Local Ltac inl := apply L5K.in_b; vm_compute; reflexivity.
Local Ltac asm := match goal with H : ?T |- ?G => constr_eq T G; exact H end.
Local Ltac hsc := first [ asm | apply UR | apply U_to | rk | gmem | (arith_goal; first [asm | alia]) | assumption ].
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Section Stage.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Let LYa := PMA.ly_as0 L C LY.
Variables (M : word -> option byte) (model : Model) (LB : list (Z * Z)) (FF LK : list fframe) (A : list (Z * Z)) (R : bvmap 5 word)
          (V2 cls F fl : Z) (LK2 : list fframe) (M2 : word -> option byte) (model2 : Model) (cr : credit) (W : list L5.range).
Hypothesis G : L5AFKR.gctx L ar HI LB FF LK A (V2 + cls) 36864 (V2 - 128) (V2 - 128) (V2 + cls) (tocell (V2 + cls)) (tfrk (V2 + cls) R) F fl 5 LK2 M2 model2 cr.
Hypothesis CLS : cls = 0 \/ cls = 16.
Hypothesis V2R : 140735332487360 <= V2 <= 140737488355328.
Hypothesis V2S : V2 + cls <= 140737488355328.
Hypothesis V2A : V2 mod 32 = 0.
(* [comment removed for export] *)
Hypothesis GP : getr R (reg 3) = Z_to_bv 64 (pa_gp PMA.AD).
Hypothesis TP : getr R (reg 4) = Z_to_bv 64 (hl_tp L).
Hypothesis FFRS : forall f, In f FF -> V2 + cls + 32 <= ff_rs f.
Hypothesis ROOM : forall LKc, incl LKc LK -> NoDup (map ff_addr ((F, 5, V2 - 128 + 32) :: FF ++ LKc)) -> PMSPA.ffroomA 11 ((F, 5, V2 - 128 + 32) :: FF) LKc.
Hypothesis STKSH : shadow_zero M (V2 + cls - 36864) 4608.
Hypothesis WAPP : PMKA.wapp W.
Local Notation Bv := (L5AFKR.binv L ar HI M model LB FF LK A (V2 + cls) 36864 (V2 - 128) (tfrk (V2 + cls) R) F 5).
Local Notation FF' := ((F, 5, V2 - 128 + 32) :: FF).

Lemma stage2 (STR : PMA.str_ctor_spec L ar HI) (fx3 : FPState) (R3 : bvmap 5 word) (M3 : word -> option byte) (model3 : Model) (K : TSet) (data n : Z) (g : PNST.st) :
  Bv W [] M3 model3 LK2 cr A -> rinvH R R3 V2 cls F -> K [] -> PNSTA.ls_okA RSEGS PMA.AD PMA.AAD PMA.AN g M3 ->
  getr R3 (reg 1) = Z_to_bv 64 0xa82ac -> getr R3 (reg 10) = Z_to_bv 64 (F + 32) ->
  getr R3 (reg 11) = Z_to_bv 64 data -> getr R3 (reg 12) = Z_to_bv 64 n -> getr R3 (reg 21) = Z_to_bv 64 (F + 96) ->
  getr R3 (reg 22) = Z_to_bv 64 n -> getr R3 (reg 23) = Z_to_bv 64 data ->
  shadow_zero M3 (F + 32) 3 -> 0 <= n < 2 ^ 26 -> 0 <= data < 2 ^ 64 ->
  (n = 0 \/ (exists B m, In (B, m) LB /\ B <= data /\ data + n <= B + m)) -> aacc M3 data n ->
  PMSPA.credit_le (PMSPA.scA L (PM.cost1 (PMSPA.HV L ar) (n + 16))) cr ->
  (forall (fx4 : FPState) (R4 : bvmap 5 word) (M4 : word -> option byte) (model4 : Model) (LK4 : list fframe) (cr4 : credit) (A4 : list (Z * Z)) (s : PM.vstr),
      Bv W (PM.vs_own s) M4 model4 LK4 cr4 A4 -> rinvH R R4 V2 cls F ->
      getr R4 (reg 1) = Z_to_bv 64 0xa8344 -> getr R4 (reg 10) = Z_to_bv 64 (F + 96) -> getr R4 (reg 11) = Z_to_bv 64 (F + 32) ->
      getr R4 (reg 12) = Z_to_bv 64 8 -> getr R4 (reg 21) = Z_to_bv 64 (F + 96) -> getr R4 (reg 22) = Z_to_bv 64 n -> getr R4 (reg 23) = Z_to_bv 64 data ->
      PM.vstr_at RSEGS PMSPA.accA M4 (F + 32) s -> PM.vs_size s = n -> (n <= 22 -> s = PM.VShort n) -> (23 <= n -> exists p, s = PM.VLong (PMSPA.str_count n) n p) ->
      PMSPA.credit_keep cr cr4 (PMSPA.scA L (PM.cost1 (PMSPA.HV L ar) (n + 16))) PMSPA.cr0 ->
      shadow_zero M4 (F + 96) 34 -> PNSTA.ls_okA RSEGS PMA.AD PMA.AAD PMA.AN g M4 ->
      srealizes RSEGS SCFG (@L5A.cfg fx4 R4 0xa8b74 M4 model4) K) ->
  srealizes RSEGS SCFG (@L5A.cfg fx3 R3 0xa8a0c M3 model3) K.
Proof.
  intros BI RI K0 LS R1a R10 R11 R12 R21 R22 R23 SZS Hn Hd SRCB ACCd CRD KONT.
  pose proof G as G'. destruct G' as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG F32 FLA FLR FLBIG NCF NCS].
  change (ff_bytes 5) with 2048 in *. change (2048 / 8) with 256 in *.
  pose proof BI as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10). cbn [app] in B1.
  pose proof (L5AFKR.vis_facts L ar C HI LYa HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W [] M3 model3 LK2 cr A BI)
    as ((VW3 & VIC3 & VSB3 & VUAR3 & VMS3) & VOWN3 & (VFD3 & VFW3 & VFSW3 & VFLC3 & VFLW3) & (FLCc3 & FLV3 & FV3 & SPV3 & FSV3)).
  change (ff_bytes 5) with 2048 in *. change (2048 / 8) with 256 in *.
  set (H3 := ahid A model3) in *. set (MV3 := mrestrict H3 M3) in *.
  pose proof RI as (X2 & X8 & X9 & X18 & X19 & X20 & X24 & X25 & X3 & X4 & X27).
  assert (FDEF3 : L5.defined M3 F 2048) by (apply (proj1 (L5A.defined_vis H3 M3 F 2048 FV3)); exact VFD3).
  assert (SZ3 : shadow_zero M3 (V2 - 128 - 12288) 1536).
  { apply (PMKA.shadow_zero_sub M3 (V2 + cls - 36864) 4608); [| | clear - CLS; lia| clear - CLS; lia| lia|].
    - replace (V2 + cls - 36864) with ((V2 - 36864) + cls) by (clear; lia). destruct CLS as [E|E]; subst cls; [rewrite Z.add_0_r|].
      + apply PMKA.mod16_8'. replace (V2 - 36864) with (V2 + (-2304) * 16) by (clear; lia). rewrite Z_mod_plus_full. apply Z.mod_divide; [lia|].
        destruct (proj1 (Z.mod_divide V2 32 ltac:(lia)) V2A) as (q & ->). exists (2 * q). lia.
      + apply PMKA.mod16_8'. replace (V2 - 36864 + 16) with (V2 + (-2303) * 16) by (clear; lia). rewrite Z_mod_plus_full. apply Z.mod_divide; [lia|].
        destruct (proj1 (Z.mod_divide V2 32 ltac:(lia)) V2A) as (q & ->). exists (2 * q). lia.
    - apply PMKA.mod16_8'. replace (V2 - 128 - 12288) with (V2 + (-776) * 16) by (clear; lia). rewrite Z_mod_plus_full. apply Z.mod_divide; [lia|].
      destruct (proj1 (Z.mod_divide V2 32 ltac:(lia)) V2A) as (q & ->). exists (2 * q). lia.
    - apply (PMKA.stksh_keepA L ar LB FF (V2 + cls) 36864 W M M3 B7 WAPP); [clear - SLO SPT; lia| clear - SLO SPT; lia| clear - V2S CLS; lia| | lia| exact STKSH].
      replace (V2 + cls - 36864) with ((V2 - 36864) + cls) by (clear; lia). destruct CLS as [E|E]; subst cls; [rewrite Z.add_0_r|].
      + apply PMKA.mod16_8'. replace (V2 - 36864) with (V2 + (-2304) * 16) by (clear; lia). rewrite Z_mod_plus_full. apply Z.mod_divide; [lia|].
        destruct (proj1 (Z.mod_divide V2 32 ltac:(lia)) V2A) as (q & ->). exists (2 * q). lia.
      + apply PMKA.mod16_8'. replace (V2 - 36864 + 16) with (V2 + (-2303) * 16) by (clear; lia). rewrite Z_mod_plus_full. apply Z.mod_divide; [lia|].
        destruct (proj1 (Z.mod_divide V2 32 ltac:(lia)) V2A) as (q & ->). exists (2 * q). lia. }
  assert (ASTKc : L5CA.astk ar M3 (V2 - 128) 12288).
  { replace (V2 - 128) with ((V2 + cls) - (128 + cls)) by (clear; lia).
    apply (L5SAR.astk_sub ar M3 M3 (V2 + cls) 36864 (128 + cls) 12288 B6 (fun _ X => X)); [clear - CLS; lia| lia| clear - CLS; lia|].
    replace (V2 + cls - (128 + cls)) with (V2 + (-8) * 16) by (clear; lia). rewrite Z_mod_plus_full. apply Z.mod_divide; [lia|].
    destruct (proj1 (Z.mod_divide V2 32 ltac:(lia)) V2A) as (q & ->). exists (2 * q). lia. }
  assert (NDF : NoDup (map ff_addr (FF' ++ LK2))).
  { pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ B1) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X & _). exact X. }
  unfold PMA.str_ctor_spec, PMSPA.str_ctor_spec in STR. cbn [pa_str_ctor PMA.AD ADDR_A] in STR.
  apply (STR fx3 R3 M3 model3 K LB FF' LK2 A cr (F + 32) data n (V2 - 128) 0xa82ac B1 B2 K0).
  { split; [rewrite L5K.rl1; exact R1a|]. split; [split; [lia| reflexivity]|]. split; [rewrite L5K.rl2; exact X2|].
    split; [rewrite L5K.rl3, X3; exact GP|]. split; [rewrite L5K.rl4, X4; exact TP|].
    change (PMSPA.pm_scr 0) with 12288. split; [exact ASTKc|]. change (12288 / 8) with 1536. exact SZ3. }
  { intros k0 Hk0. specialize (ROOM LK2 LKI2 NDF k0 Hk0). lia. }
  { intros f [<-|Hf]; [cbn [ff_rs fst snd]; lia| specialize (FFRS f Hf); lia]. }
  { rewrite L5K.rl10. exact R10. }
  { rewrite L5K.rl11. exact R11. }
  { rewrite L5K.rl12. exact R12. }
  { exact Hn. }
  { exists (F, 5, V2 - 128 + 32). split; [left; reflexivity|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 5) with 2048. lia. }
  { replace (F + 32) with (F + 4 * 8) by (clear; lia). rewrite Z_mod_plus_full. pose proof (proj1 F8) as E8. clear - E8 FR. lia. }
  { apply (L5.defined_sub M3 F 2048 (F + 32) 24 FDEF3); lia. }
  { apply (PMARS1.acc_of_shadow_zero M3 (F + 32) 3 (F + 32) 24 SZS); [| lia| lia].
    replace (F + 32) with (F + 4 * 8) by (clear; lia). rewrite Z_mod_plus_full. pose proof (proj1 F8) as E8. clear - E8 FR. lia. }
  { exact SRCB. }
  { exact ACCd. }
  { exact CRD. }
  intros fx' R' M' model' LK' Aw' s cr' RP' VSTR SIZE SSH SLG HP' CK' MRT' INCLK' INCA' AM' HH'.
  assert (LS' : PNSTA.ls_okA RSEGS PMA.AD PMA.AAD PMA.AN g M').
  { apply (PNHAK.ls_ahpres L C LY g ar LB FF' (V2 - 128) _ [(F + 32, 24)] M3 M' HP'); [| exact LS].
    apply PNHAK.far_cons; [cbn [fst snd]; clear - FR; lia| apply PNHAK.far_nil]. }
  change (PMSPA.pm_scr 0) with 12288 in HP'.
  (* [comment removed for export] *)
  assert (BI' : Bv W (PM.vs_own s) M' model' LK' cr' Aw').
  { apply (L5AFKR.binv_callee L ar C HI HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W W [] [] (PM.vs_own s) M3 model3 LK2 cr A M' model' LK' cr' Aw' 12288 [(F + 32, 24)] BI HP' HH' AM' MRT' INCA' INCLK').
    - lia.
    - clear - CLS; lia.
    - intros rr a [<-|[]] Ha. unfold L5.in_rng in Ha; cbn [fst snd] in Ha. unfold tocell. split; [clear - Ha FCEIL SLO CLS; lia|]. unfold HeapIfaceA.SB. change (ff_bytes 5) with 2048. clear - Ha FR F8 FBIG. lia.
    - intros a Hc _ rr [<-|[]] Ha. unfold L5.in_rng in Ha; cbn [fst snd] in Ha. apply (NCF a); [left; clear - Ha; lia| exact Hc].
    - intros a X. exact X. }
  pose proof (L5AFKR.vis_facts L ar C HI LYa HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W (PM.vs_own s) M' model' LK' cr' Aw' BI')
    as ((VW' & VIC' & VSB' & VUAR' & VMS') & VOWN' & (VFD' & VFW' & VFSW' & VFLC' & VFLW') & (FLCc' & FLV' & FV' & SPV' & FSV')).
  change (ff_bytes 5) with 2048 in *. change (2048 / 8) with 256 in *.
  set (H' := ahid Aw' model') in *. set (MV' := mrestrict H' M') in *.
  assert (RI' : rinvH R R' V2 cls F) by exact (rinvH_pres R R3 R' V2 cls F RI RP').
  pose proof RI' as (Y2 & Y8 & Y9 & Y18 & Y19 & Y20 & Y24 & Y25 & Y3 & Y4 & Y27).
  assert (Y21 : getr R' (reg 21) = Z_to_bv 64 (F + 96)) by (rewrite (cs_of_preserved R3 R' 21 RP') by inl; exact R21).
  assert (Y22 : getr R' (reg 22) = Z_to_bv 64 n) by (rewrite (cs_of_preserved R3 R' 22 RP') by inl; exact R22).
  assert (Y23 : getr R' (reg 23) = Z_to_bv 64 data) by (rewrite (cs_of_preserved R3 R' 23 RP') by inl; exact R23).
  assert (Q1 : 4096 <= F <= 140737488353280) by (clear - FR; lia).
  assert (Q2 : 4096 <= fl <= 140737488355327) by (clear - FLR; lia).
  assert (Q3 : V2 - 128 + 144 <= F \/ F + 2048 <= V2 - 128) by (clear - FCEIL SLO CLS; lia).
  assert (Q4 : V2 - 128 + 144 <= fl \/ fl + 1 <= V2 - 128) by (clear - FLR SLO CLS; lia).
  assert (Q5 : L5.writable RSEGS MV' (V2 - 128) 128) by (eapply L5.writable_sub; [exact VW'| clear; lia| clear - CLS; lia]).
  assert (Q6 : L5.u64_at RSEGS MV' (F + 2040) fl) by (replace (F + 2040) with (F + 2048 - 8) by (clear; lia); exact VFLC').
  LeanFeed.pfeed P (PNAHP2.bhaC_conc fx' R' MV' (fun j => match j with 2%nat => V2 | 33%nat => data | 34%nat => n | 40%nat => F | 41%nat => fl | 58%nat => U R' 1 | _ => 0 end)) ltac:(first [ asm | apply UR | apply U_to | (clear - Hn; lia) | (clear - Hd; lia) | (clear - V2R; lia) | (clear - FR; lia) | (clear - FLR; lia) | exact F32
                     | exact VFD' | exact VFW' | exact VFSW' | exact VFLW' | exact Q5 | exact Q6 | (unfold PNAHP2.aligned; exact V2A) ]).
  destruct P as (fx4 & R4 & M4v & MG4 & cFR & cFZ & (cMS & cKS & cR1 & cR10 & cR11 & cR12 & CQ)).
  set (W4 := fun a => F / 8 + 2147450880 + 12 <= a < F / 8 + 2147450880 + 12 + 34).
  apply (apiece L ar C HI LYa HIok _ FF' LK' cr' Aw' M' model' fx' fx4 R' 0xa82ac R4 0xa8b74 M4v W4 K HH' AM' cMS MG4).
  { intros a Ha Hna. apply cFZ. exact Ha. intros X; apply Hna; subst W4; cbn beta; clear - X; lia. }
  { intros a Ha Wa. subst W4; cbn beta in Wa. split.
    - apply (fframe_shadow_client L ar _ _ 0 0 F 5 (V2 - 128 + 32)). left; reflexivity. change (ff_bytes 5) with 2048.
      unfold in_shadow_of, HeapIfaceA.S. rewrite (proj1 (proj2 F8)). unfold HeapIfaceA.SB. clear - Wa. lia.
    - clear - Wa FR. lia. }
  intros M4 model4 HH4 AM4 MRT4 HID4 VIS4 MGM4 FR4 VV4. change (mrestrict H' M4 = M4v) in VIS4.
  assert (LS4 : PNSTA.ls_okA RSEGS PMA.AD PMA.AAD PMA.AN g M4).
  { apply (PNHAK.ls_piece g M' M4 W4 FR4); [| exact LS']. intros a Wa. subst W4; cbn beta in Wa. clear - Wa FR. lia. }
  decompose [and] CQ. clear CQ.
  assert (BI4 : Bv W (PM.vs_own s) M4 model4 LK' cr' Aw').
  { apply (L5AFKR.binv_piece L ar HI M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W (PM.vs_own s) M' model' LK' cr' Aw' M4 model4 W4 BI' HH4 AM4 MRT4 MGM4 FR4).
    intros a Wa. subst W4; cbn beta in Wa. right; right. change (ff_bytes 5) with 2048. change (2048 / 8) with 256. unfold HeapIfaceA.SB in *. clear - Wa. lia. }
  assert (RI4 : rinvH R R4 V2 cls F) by (apply (rinvH_ks R R' R4 V2 cls F PNAHP2.KS_bhaC RI' cKS); vm_compute; reflexivity).
  assert (SZ4 : shadow_zero M4 (F + 96) 34).
  { intros j Hj. unfold byte_at, HeapIfaceA.S.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    assert (E96 : (F + 96) / 8 = F / 8 + 12) by (pose proof (proj1 (proj2 F8)) as E8; clear - E8; lia).
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    rewrite E96. rewrite VV4.
    - assert (X : L5.u8_at RSEGS M4v (F / 8 + 2147450892 + j) 0).
      { assert (J : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6 \/ j = 7 \/ j = 8 \/ j = 9 \/ j = 10 \/ j = 11 \/ j = 12 \/ j = 13 \/ j = 14 \/ j = 15 \/ j = 16 \/ j = 17 \/ j = 18 \/ j = 19 \/ j = 20 \/ j = 21 \/ j = 22 \/ j = 23 \/ j = 24 \/ j = 25 \/ j = 26 \/ j = 27 \/ j = 28 \/ j = 29 \/ j = 30 \/ j = 31 \/ j = 32 \/ j = 33) by (clear - Hj; lia).
        repeat (destruct J as [J|J]; [subst j; gmem|]). subst j; gmem. }
      replace (F / 8 + 12 + HeapIfaceA.SB + j) with (F / 8 + 2147450892 + j) by (unfold HeapIfaceA.SB; clear; lia).
      apply (L5ADHR.byte_of_u8 M4v _ 0 X). right. clear - Hj FR F8. lia. clear - Hj FR F8. lia.
    - replace (F / 8 + 12 + HeapIfaceA.SB + j) with ((F / 8 + HeapIfaceA.SB) + (12 + j)) by (clear; lia). apply FSV'. clear - Hj. lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (VSTR4 : PM.vstr_at RSEGS PMSPA.accA M4 (F + 32) s).
  { apply (PMFA.vstr_at_agreeA RSEGS M' M4 (F + 32) s); [clear - FR; lia| clear - FR; lia| | |].
    - split.
      + intros i Hi. apply FR4; [clear - Hi FR; lia| subst W4; cbn beta; intros X; clear - Hi X FR F8 FBIG; unfold HeapIfaceA.SB in *; lia].
      + intros x Hx. pose proof (PMKA.S_in_shadow x ltac:(clear - Hx FR; lia)) as SX. apply FR4; [unfold BIGSHADOW_LO, BIGSHADOW_HI in SX; clear - SX; lia|].
        subst W4; cbn beta. intros X. unfold HeapIfaceA.S, HeapIfaceA.SB in X. clear - Hx X F8. lia.
    - intros c0 n0 p0 E0. subst s. cbn [PM.vs_own app] in HH'.
      pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH') as (WB' & _).
      pose proof (WB' (p0, c0) (or_introl eq_refl)) as ((P0 & _ & _ & P3 & _ & P5) & _ & _ & _ & _ & PFA & _). cbn [fst snd] in P0, P3, P5, PFA. unfold app_mem in P5.
      pose proof (PFA (F, 5, V2 - 128 + 32) (in_or_app FF' LK' (F, 5, V2 - 128 + 32) (or_introl (or_introl eq_refl)))) as PF. cbn [ff_addr ff_class fst snd] in PF. change (ff_bytes 5) with 2048 in PF.
      split.
      + intros i Hi. apply FR4; [clear - Hi P5; lia| subst W4; cbn beta; intros X; clear - Hi X P5 FR; unfold BIGSHADOW_LO, BIGSHADOW_HI in *; lia].
      + intros x Hx. pose proof (PMKA.S_in_shadow x ltac:(clear - Hx P5; lia)) as SX. apply FR4; [unfold BIGSHADOW_LO, BIGSHADOW_HI in SX; clear - SX; lia|].
        subst W4; cbn beta. intros X. unfold HeapIfaceA.S in X.
        (* [comment removed for export] *)
        unfold HeapIfaceA.SB in X. clear - Hx X PF F8 P3. lia.
    - exact VSTR. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  apply (KONT fx4 R4 M4 model4 LK' cr' Aw' s BI4 RI4).
  - exact cR1.
  - exact cR10.
  - exact cR11.
  - exact cR12.
  - rewrite (cKS 21%nat) by inl. exact Y21.
  - rewrite (cKS 22%nat) by inl. exact Y22.
  - rewrite (cKS 23%nat) by inl. exact Y23.
  - exact VSTR4.
  - exact SIZE.
  - exact SSH.
  - exact SLG.
  - exact CK'.
  - exact SZ4.
  - exact LS4.
Qed.
End Stage.
End SCFG_1.
End PNHA2.
