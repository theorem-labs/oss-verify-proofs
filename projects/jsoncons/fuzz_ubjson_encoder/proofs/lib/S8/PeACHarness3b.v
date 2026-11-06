(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA IcptIfaceA LibIface AsanAcct AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5CoreKit L5LazyA L5DefsA L5CoreAS8 L5StepARS8 L5CoreBRS8 L5ADetailHRS8 L5AFrameKRS8 HeapIfaceAEx.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout PmLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PmModel PmModelFacts PmModelFactsA PmStatics PmStaticsA PnStatics PnStaticsA PmSpecs PmSpecsA PeSpecsAa PeStepA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PeCLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PeCStaticsA PeCSink PeCSinkA PeCModel PeCModelA PeCSpecs PeCSpecsA PeCSpecsAa PeACHarnessStmts PeACHarnessKit PeACHarnessKit2 PeACHarnessSK PeACHarnessKit3 PeACHarnessKit4 PeACHarnessP2.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module PEACH3b.
Import L5A. Import L5CA. Import L5SAR. Import PEACH.
Abbreviation RSEGS := Asan.M.loaded_segments.
Abbreviation AD := PeCLayoutA.CADDR_A.
Abbreviation AAD := PeCLayoutA.CAADDR_A.
Abbreviation EE := PeCLayoutA.EADDR_A.
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
Hypothesis G : L5AFKR.gctx L ar HI LB FF LK A (V2 + cls) 36864 (V2 - 160) (V2 - 160) (V2 + cls) (tocell (V2 + cls)) (tfrk (V2 + cls) R) F fl 5 LK2 M2 model2 cr.
Hypothesis CLS : cls = 0 \/ cls = 16.
Hypothesis V2R : 140735332487392 <= V2 <= 140737488355328.
Hypothesis V2S : V2 + cls <= 140737488355328.
Hypothesis V2A : V2 mod 32 = 0.

Hypothesis GP : getr R (reg 3) = Z_to_bv 64 (pa_gp AD).
Hypothesis TP : getr R (reg 4) = Z_to_bv 64 (hl_tp L).
Hypothesis FFRS : forall f, In f FF -> V2 + cls + 32 <= ff_rs f.
Hypothesis ROOM : forall LKc, incl LKc LK -> NoDup (map ff_addr ((F, 5, V2 - 160 + 32) :: FF ++ LKc)) -> PMSPA.ffroomA 11 ((F, 5, V2 - 160 + 32) :: FF) LKc.
Hypothesis STKSH : shadow_zero M (V2 + cls - 36864) 4608.
Hypothesis WAPP : PMKA.wapp W.
Hypothesis WLOC : forall a, L5.outside W a -> L5.outside (PMSPA.loc_W AD) a.
Local Notation Bv := (L5AFKR.binv L ar HI M model LB FF LK A (V2 + cls) 36864 (V2 - 160) (tfrk (V2 + cls) R) F 5).
Local Notation FF' := ((F, 5, V2 - 160 + 32) :: FF).

Variable P : PESKA.sink_policyA.
Variable payload : list byte.
Local Notation n := (PEACH.n payload).
Local Notation p := (PEACH.p payload).

Lemma stage3b (fx5 : FPState) (R5 : bvmap 5 word) (M5 : word -> option byte) (model5 : Model) (K : TSet)
      (LK5 : list fframe) (cr5 : credit) (A5 : list (Z * Z)) (s s' : PM.vstr) (sm : PM.strm) (g : PMST.st) :
  Bv W (PM.vs_own s' ++ PM.vs_own s) M5 model5 LK5 cr5 A5 -> rinvH R R5 (V2 - 160) F 2147450880 -> K [] -> PESTA.ls_okA RSEGS AD AAD EE g M5 ->
  getr R5 (reg 1) = Z_to_bv 64 0xa8d24 -> getr R5 (reg 10) = Z_to_bv 64 (F + 432) -> getr R5 (reg 11) = Z_to_bv 64 0 ->
  getr R5 (reg 12) = Z_to_bv 64 24 -> getr R5 (reg 18) = Z_to_bv 64 (F + 32) -> getr R5 (reg 22) = Z_to_bv 64 (F + 432) -> getr R5 (reg 23) = Z_to_bv 64 (F + 496) ->
  PM.vstr_at RSEGS PMSPA.accA M5 (F + 32) s -> PEACH.his_pay payload F M5 s' sm ->
  shadow_zero M5 (F + 432) 3 -> shadow_zero M5 (F + 96) 34 -> L5.u64_at RSEGS M5 (V2 - 144) (F + 32) -> L5.u64_at RSEGS M5 (V2 - 136) F ->
  (forall (fx6 : FPState) (R6 : bvmap 5 word) (M6 : word -> option byte) (model6 : Model),
      Bv W (PM.vs_own s' ++ PM.vs_own s) M6 model6 LK5 cr5 A5 -> rinvH R R6 (V2 - 160) F 2147450880 -> PESTA.ls_okA RSEGS AD AAD EE g M6 ->
      getr R6 (reg 1) = Z_to_bv 64 0xa8e94 -> getr R6 (reg 10) = Z_to_bv 64 (F + 592) -> getr R6 (reg 11) = Z_to_bv 64 (F + 96) ->
      getr R6 (reg 12) = Z_to_bv 64 (F + 1056) -> getr R6 (reg 13) = Z_to_bv 64 (V2 - 112) ->
      getr R6 (reg 18) = Z_to_bv 64 (F + 520) -> getr R6 (reg 20) = Z_to_bv 64 1024 -> getr R6 (reg 22) = Z_to_bv 64 (F + 432) ->
      getr R6 (reg 23) = Z_to_bv 64 (F + 496) -> getr R6 (reg 24) = Z_to_bv 64 (F + 1056) -> getr R6 (reg 25) = Z_to_bv 64 (F + 592) ->
      PM.vstr_at RSEGS PMSPA.accA M6 (F + 32) s -> PEACH.his_pay payload F M6 s' sm -> PEACH.hse0 L ar P F M6 ->
      L5.u64_at RSEGS M6 (F + 1056) 0x133428 -> L5.u64_at RSEGS M6 (F + 1064) 16777216 -> L5.u64_at RSEGS M6 (F + 1072) 0x133450 -> L5.u32_at RSEGS M6 (F + 1080) 1024 ->
      L5.defined M6 (F + 592) 384 -> shadow_zero M6 (F + 592) 49 -> shadow_zero M6 (F + 1056) 4 ->
      shadow_zero M6 (F + 96) 34 -> shadow_zero M6 (F + 432) 3 -> shadow_zero M6 (F + 496) 7 ->
      L5.u64_at RSEGS M6 (V2 - 144) (F + 32) -> L5.u64_at RSEGS M6 (V2 - 136) F ->
      srealizes RSEGS SCFG (@L5A.cfg fx6 R6 0xb153c M6 model6) K) ->
  srealizes RSEGS SCFG (@L5A.cfg fx5 R5 0x78ab4 M5 model5) K.
Proof.
  intros BI RI K0 LS R1a R10 R11 R12 R18 R22 R23 VS0 HIS SZK SZI HSTKa HSTKb KONT.
  pose proof G as G'. destruct G' as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG F32 FLA FLR FLBIG NCF NCS].
  change (ff_bytes 5) with 2048 in *. change (2048 / 8) with 256 in *.
  assert (FM8 : F mod 8 = 0) by (pose proof (proj1 F8) as E8; clear - E8; lia).
  assert (FHF : PEAHK2.hf F) by (unfold PEAHK2.hf, BIGSHADOW_LO, BIGSHADOW_HI; clear - FR FBIG FM8; lia).
  assert (Q1 : 4096 <= F <= 140737488353280) by (clear - FR; lia).
  assert (Q2 : 4096 <= fl <= 140737488355327) by (clear - FLR; lia).
  assert (Q3 : V2 - 160 + 176 <= F \/ F + 2048 <= V2 - 160) by (clear - FCEIL SLO CLS; lia).
  assert (Q4 : V2 - 160 + 176 <= fl \/ fl + 1 <= V2 - 160) by (clear - FLR SLO CLS; lia).
  assert (SLOW : ahl_ceil ar <= V2 - 160) by (clear - SLO CLS; lia).
  assert (SHW : BIGSHADOW_HI <= V2 - 160) by (unfold BIGSHADOW_HI; clear - V2R; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (FBD : 0 <= F / 8 /\ F / 8 + 256 <= 2 ^ 44) by (clear - FR; lia).
  assert (SPA16 : (V2 - 160) mod 16 = 0) by (clear - V2A; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  assert (LENp : Z.of_nat (length p) = n) by (unfold PEACH.p, PEACH.n; rewrite length_map; reflexivity).

  assert (MSET : forall (fx0 : FPState) Ra Ma modela BXa LKa cra Aa Kc dst nn ra, F + 32 <= dst -> dst + nn <= F + 2040 -> 0 < nn <= 48 -> dst mod 8 = 0 ->
     ri_inv HI (BXa ++ LB) FF' LKa cra Aa Ma (vml_of modela) -> amodel_ok Aa modela -> astk ar Ma (V2 + cls) 36864 -> PMSPA.accA Ma dst nn -> L5.defined Ma F 2048 ->
     getr Ra (reg 10) = Z_to_bv 64 dst -> getr Ra (reg 11) = Z_to_bv 64 0 -> getr Ra (reg 12) = Z_to_bv 64 nn -> getr Ra (reg 4) = Z_to_bv 64 (hl_tp L) ->
     getr Ra (reg 1) = Z_to_bv 64 ra -> ra mod 2 = 0 -> 0 <= ra < 2 ^ 64 -> getr Ra (reg 2) = Z_to_bv 64 (V2 - 160) -> Kc [] ->
     (forall Rb Mb modelb, getr Rb (reg 10) = Z_to_bv 64 dst -> regs_preserved Ra Rb -> PM.zeros_at Mb dst nn ->
        ahpres L ar (BXa ++ LB) FF' (V2 - 160) 2560 [(dst, nn)] Ma Mb ->
        model_rt modela modelb -> amodel_ok Aa modelb -> ri_inv HI (BXa ++ LB) FF' LKa cra Aa Mb (vml_of modelb) ->
        srealizes RSEGS SCFG (@L5A.cfg fx0 Rb ra Mb modelb) Kc) ->
     srealizes RSEGS SCFG (@L5A.cfg fx0 Ra 0x78ab4 Ma modela) Kc).
  { intros fx0 Ra Ma modela BXa LKa cra Aa Kc dst nn ra Hd1 Hd2 Hn Hd8 HHa AMa ASTKa ACCa DEFa Ra10 Ra11 Ra12 Ra4 Ra1 Hra Hra' Ra2 Ka KC.
    pose proof (HAJ.aior_memset _ _ _ _ _ HIok) as MS. unfold amemset_spec, amem_pre, amem_post in MS.
    rewrite (L5A.aly_segs L C LYa), (L5A.aly_memset L C LYa), (L5A.aly_scr_mem L C LYa) in MS.
    assert (U2 : bv_unsigned (getr Ra 2%bv) = V2 - 160) by (rewrite L5K.rl2, Ra2; apply L5.unsigned_lit; clear - V2R; lia).
    assert (AOB : aobj FF' dst nn).
    { exists (F, 5, V2 - 160 + 32). split; [left; reflexivity|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 5) with 2048.
      split; [clear - Hd1; lia| split; [clear - Hd2; lia| exact Hd8]]. }
    apply (MS fx0 Ra Ma modela (BXa ++ LB) FF' LKa cra Aa dst 0 nn Kc); clear MS.
    - split; [exact HHa|]. split; [exact (proj1 AMa)|]. split; [exact (proj2 AMa)|].
      split; [rewrite L5K.rl10; exact Ra10|]. split; [rewrite L5K.rl12; exact Ra12|]. split; [clear - Hn; lia|].
      split; [rewrite L5K.rl4; exact Ra4|]. split; [rewrite L5K.rl1, Ra1; apply Hoare.ret_ok_even; rewrite L5.unsigned_lit by (clear - Hra'; lia); exact Hra|].
      split. { rewrite U2. replace (V2 - 160) with (V2 + cls - (160 + cls)) by (clear; lia).
               apply (astack_ok_of_astk L ar C LYa Ma Ma (V2 + cls) 36864 (160 + cls) 2560 ASTKa (mem_grows_refl Ma)); [clear - CLS; lia| clear; lia| clear - CLS; lia|].
               replace (V2 + cls - (160 + cls)) with (V2 - 160) by (clear; lia). exact SPA16. }
      split. { exact ACCa. }
      split. { intros i Hi. rewrite U2. apply (fframe_client L ar _ FF' (V2 - 160) 2560 F 5 (V2 - 160 + 32)); [left; reflexivity|]. change (ff_bytes 5) with 2048. clear - Hi Hd1 Hd2; lia. }
      split. { intros i m Hi Hm. pose proof (L5C.writable_of_defined RSEGS Ma F 2048 DEFa ltac:(clear - FR; lia) ltac:(clear - FR; lia)) as WD.
               replace (dst + i) with (F + (dst - F + i)) by (clear; lia). apply WD; clear - Hi Hm Hd1 Hd2; lia. }
      split; [exact Ka|]. apply (app_rng_aobj L ar C HI HIok _ FF' LKa cra Aa Ma _ dst nn dst nn HHa AOB); clear; lia.
    - rewrite L5K.rl11. exact Ra11.
    - intros Rb Mb modelb Rb10 RPb BYTES PRES SDEFb RTb MIb HHb. rewrite U2 in PRES, SDEFb. rewrite L5K.rl1, Ra1.
      assert (ZB : PM.zeros_at Mb dst nn).
      { intros i Hi. destruct (BYTES i Hi) as (v & Ev & Bv0). unfold byte_at in Bv0. rewrite Bv0. subst v. reflexivity. }
      apply (KC Rb Mb modelb); [rewrite <- L5K.rl10; exact Rb10| exact RPb| exact ZB| | exact RTb| | exact HHb].
      + split; [| split].
        * intros a (Ha & Hc & Ho). apply (PRES a Ha Hc). intros X. apply (Ho (dst, nn)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; clear - X; lia].
        * intros i Hi. apply SDEFb. clear - Hi; lia.
        * intros a Ha Hc Hm. destruct (rng_dec a dst (dst + nn)) as [I0|O0].
          -- replace a with (dst + (a - dst)) by (clear; lia). rewrite (ZB (a - dst)) by (clear - I0; lia). discriminate.
          -- rewrite (PRES a Ha Hc O0). exact Hm.
      + split; [rewrite (L5LZ.model_rt_halted _ _ RTb); exact (proj1 AMa)| exact MIb]. }

  pose proof BI as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10).
  pose proof RI as (X2 & X3 & X4 & X8 & X9 & X19 & X21 & X26 & X27).
  pose proof (L5AFKR.vis_facts L ar C HI LYa HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W _ M5 model5 LK5 cr5 A5 BI)
    as ((_ & _ & _ & _ & _) & _ & (VFD5 & _ & _ & _ & _) & (_ & _ & FV5 & _ & _)).
  change (ff_bytes 5) with 2048 in *. change (2048 / 8) with 256 in *.
  assert (FDEF5 : L5.defined M5 F 2048) by (apply (proj1 (L5A.defined_vis (ahid A5 model5) M5 F 2048 FV5)); exact VFD5).
  assert (ACC1 : PMSPA.accA M5 (F + 432) 24).
  { apply (PEAHK2.acc_of_shz M5 (F + 432) 3 (F + 432) 24 SZK); [| clear - FR; lia| clear; lia| clear; lia].
    replace (F + 432) with (F + 54 * 8) by (clear; lia). rewrite Z_mod_plus_full. exact FM8. }
  assert (FIN5 : In (F, 5, V2 - 160 + 32) (FF' ++ LK5)) by (apply in_or_app; left; left; reflexivity).
  apply (MSET fx5 R5 M5 model5 (PM.vs_own s' ++ PM.vs_own s) LK5 cr5 A5 K (F + 432) 24 0xa8d24);
    [clear; lia| clear; lia| clear; lia| replace (F + 432) with (F + 54 * 8) by (clear; lia); rewrite Z_mod_plus_full; exact FM8
    | exact B1| exact B2| exact B6| exact ACC1| exact FDEF5| exact R10| exact R11| exact R12| rewrite X4; exact TP| exact R1a| reflexivity| clear; lia| exact X2| exact K0|].
  intros R6 M6 model6 R6a0 RP6 Z6 HP6 MRT6 AM6 HH6.
  assert (WFI6 : PEAHK2.wfi F [(F + 432, 24)]) by (apply PEAHK2.wfi_cons; [cbn [fst snd]; left; clear; lia| apply PEAHK2.wfi_nil]).
  assert (LS6 : PESTA.ls_okA RSEGS AD AAD EE g M6).
  { apply (PEAHK.ls_ahpres L C LY g ar _ FF' (V2 - 160) 2560 [(F + 432, 24)] M5 M6 HP6); [| exact LS].
    apply PEAHK.far_cons; [cbn [fst snd]; clear - FR; lia| apply PEAHK.far_nil]. }
  assert (BI6 : Bv W (PM.vs_own s' ++ PM.vs_own s) M6 model6 LK5 cr5 A5).
  { apply (L5AFKR.binv_callee L ar C HI HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W W _ (PM.vs_own s' ++ PM.vs_own s) _ M5 model5 LK5 cr5 A5 M6 model6 LK5 cr5 A5 2560 [(F + 432, 24)] BI HP6 HH6 AM6 MRT6 (incl_refl _) (incl_refl _)).
    - clear; lia.
    - clear - CLS; lia.
    - intros rr a [<-|[]] Ha. unfold L5.in_rng in Ha; cbn [fst snd] in Ha. unfold tocell. split; [clear - Ha FCEIL SLO CLS; lia|]. unfold HeapIfaceA.SB. change (ff_bytes 5) with 2048. clear - Ha FR F8 FBIG. lia.
    - intros a Hc _ rr [<-|[]] Ha. unfold L5.in_rng in Ha; cbn [fst snd] in Ha. apply (NCF a); [left; clear - Ha; lia| exact Hc].
    - intros a X0. exact X0. }
  assert (RI6 : rinvH R R6 (V2 - 160) F 2147450880) by exact (rinvH_pres R R5 R6 (V2 - 160) F 2147450880 RI RP6).
  pose proof RI6 as (Y2 & Y3 & Y4 & Y8 & Y9 & Y19 & Y21 & Y26 & Y27).
  assert (Y18 : getr R6 (reg 18) = Z_to_bv 64 (F + 32)) by (rewrite (cs_of_preserved R5 R6 18 RP6) by inl; exact R18).
  assert (Y22 : getr R6 (reg 22) = Z_to_bv 64 (F + 432)) by (rewrite (cs_of_preserved R5 R6 22 RP6) by inl; exact R22).
  assert (Y23 : getr R6 (reg 23) = Z_to_bv 64 (F + 496)) by (rewrite (cs_of_preserved R5 R6 23 RP6) by inl; exact R23).

  assert (VS6 : PM.vstr_at RSEGS PMSPA.accA M6 (F + 32) s).
  { eapply PEAHK2.vstr_keep_callee; first [ exact LY | exact HIok | exact B1 | exact HP6 | exact VS0 | exact FHF | exact FIN5 | exact WFI6 | exact (or_introl eq_refl)
      | (split; reflexivity) | (intros x Hx; apply in_or_app; left; apply in_or_app; right; exact Hx) | (apply PEAHK2.wapart_cons; [cbn [fst snd]; lia| apply PEAHK2.wapart_nil]) | lia ]. }
  pose proof HIS as (IS5 & SZ5 & SMG & SMST & PAYB5).
  assert (IS6 : PM.iss_at RSEGS AD PMSPA.accA M6 (F + 96) s' sm).
  { eapply PEAHK2.iss_keep_callee; first [ exact LY | exact HIok | exact B1 | exact HP6 | exact IS5 | exact FHF | exact FIN5 | exact WFI6 | exact (or_introl eq_refl)
      | (split; reflexivity) | (intros x Hx; apply in_or_app; left; apply in_or_app; left; exact Hx) | (apply PEAHK2.wapart_cons; [cbn [fst snd]; lia| apply PEAHK2.wapart_nil]) | lia ]. }
  assert (SZI6 : shadow_zero M6 (F + 96) 34).
  { apply (PEAHK2.shz_callee L ar _ FF' (V2 - 160) 2560 [(F + 432, 24)] M5 M6 (F, 5, V2 - 160 + 32) F (F + 96) 34 HP6 (or_introl eq_refl) (conj eq_refl eq_refl) FHF WFI6);
      [clear; lia| clear; lia| clear - FM8; lia| clear; lia| exact SZI]. }
  assert (SZK6 : shadow_zero M6 (F + 432) 3).
  { apply (PEAHK2.shz_callee L ar _ FF' (V2 - 160) 2560 [(F + 432, 24)] M5 M6 (F, 5, V2 - 160 + 32) F (F + 432) 3 HP6 (or_introl eq_refl) (conj eq_refl eq_refl) FHF WFI6);
      [clear; lia| clear; lia| clear - FM8; lia| clear; lia| exact SZK]. }
  assert (AGstk6 : forall a, V2 - 160 <= a < V2 + cls -> M6 (Z_to_bv 64 a) = M5 (Z_to_bv 64 a)).
  { intros a Ha. apply (proj1 HP6 a). split; [clear - Ha V2R V2S CLS; lia| split].
    - apply stack_client; [clear - Ha SLO V2S CLS; lia| clear - Ha; lia].
    - intros rr [<-|[]]. unfold L5.in_rng; cbn [fst snd]. clear - Ha FCEIL SLO CLS. lia. }
  assert (HSTKa6 : L5.u64_at RSEGS M6 (V2 - 144) (F + 32)).
  { apply (L5C.u64_at_agree RSEGS M5 M6 (V2 - 144) (F + 32)); [intros i Hi; apply AGstk6; clear - Hi CLS; lia| clear - V2R; lia| clear - V2R; lia| exact HSTKa]. }
  assert (HSTKb6 : L5.u64_at RSEGS M6 (V2 - 136) F).
  { apply (L5C.u64_at_agree RSEGS M5 M6 (V2 - 136) F); [intros i Hi; apply AGstk6; clear - Hi CLS; lia| clear - V2R; lia| clear - V2R; lia| exact HSTKb]. }

  assert (PAYB6 : L5.bytes_at RSEGS M6 (PM.vs_data (F + 176) s') p).
  { pose proof IS5 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & VSA & _). replace (F + 96 + 80) with (F + 176) in VSA by (clear; lia).
    pose proof VSA as (_ & _ & VX). destruct s' as [n0|c0 n0 q0]; cbn [PM.vs_data] in PAYB5 |- *; cbn in SZ5, VX.
    - pose proof (proj1 VX) as SZB.
      apply (L5C.bytes_at_agree RSEGS M5 M6 (F + 176 + 1) p); rewrite ?LENp; [| clear - FR; lia| clear - FR SZB SZ5; lia| exact PAYB5].
      intros i Hi. apply (proj1 HP6 i). split; [clear - Hi FR SZB SZ5; lia| split].
      + apply (fframe_client L ar _ FF' (V2 - 160) 2560 F 5 (V2 - 160 + 32)); [left; reflexivity|]. change (ff_bytes 5) with 2048. clear - Hi SZB SZ5; lia.
      + intros rr [<-|[]]. unfold L5.in_rng; cbn [fst snd]. clear - Hi SZB SZ5. lia.
    - pose proof VX as (_ & _ & _ & NC & CC & _).
      destruct (PEAHK.blk_facts L ar C SCFG HI HIok _ _ _ _ _ _ _ q0 c0 B1 ltac:(apply in_or_app; left; apply in_or_app; left; left; reflexivity)) as (P0 & P3 & P4 & P5 & PSH & P47 & PIMG & PFA).
      pose proof (PFA (F, 5, V2 - 160 + 32) FIN5) as PF. cbn [ff_addr ff_class fst snd] in PF. change (ff_bytes 5) with 2048 in PF.
      apply (L5C.bytes_at_agree RSEGS M5 M6 q0 p); rewrite ?LENp; [| clear - P0; lia| clear - P47 NC SZ5; lia| exact PAYB5].
      intros i Hi. apply (proj1 HP6 i). split; [clear - Hi P0 P47 NC SZ5; lia| split].
      + left. exists (q0, c0). split; [apply in_or_app; left; apply in_or_app; left; left; reflexivity| cbn [fst snd]; clear - Hi NC SZ5; lia].
      + intros rr [<-|[]]. unfold L5.in_rng; cbn [fst snd]. clear - Hi PF NC SZ5. lia. }

  pose proof (L5AFKR.vis_facts L ar C HI LYa HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W _ M6 model6 LK5 cr5 A5 BI6)
    as ((VW6 & VIC6 & VSB6 & VUAR6 & VMS6) & VOWN6 & (VFD6 & VFW6 & VFSW6 & VFLC6 & VFLW6) & (FLCc6 & FLV6 & FV6 & SPV6 & FSV6)).
  change (ff_bytes 5) with 2048 in *. change (2048 / 8) with 256 in *.
  set (H6 := ahid A5 model6) in *. set (MV6 := mrestrict H6 M6) in *.
  pose proof BI6 as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10).
  assert (Q5 : L5.writable RSEGS MV6 (V2 - 160) 160) by (eapply L5.writable_sub; [exact VW6| clear; lia| clear - CLS; lia]).
  assert (Q6 : L5.u64_at RSEGS MV6 (F + 2040) fl) by (replace (F + 2040) with (F + 2048 - 8) by (clear; lia); exact VFLC6).
  pose proof (PEACHP2.ahnD2a_conc fx5 R6 MV6 (fun j => match j with 2%nat => V2 | 40%nat => F | 41%nat => fl | 58%nat => U R6 1 | _ => 0 end)) as PP.
  cbn beta iota in PP.
  feed PP ltac:(first [ asm | apply UR | apply U_to | (clear - V2R; lia) | (clear - FR; lia) | (clear - FLR; lia) | exact F32
                     | exact VFD6 | exact VFW6 | exact VFSW6 | exact VFLW6 | exact Q5 | exact Q6 | (unfold PEACHP2.aligned; exact V2A) ]).
  destruct PP as (fx7 & R7 & M7v & MG7 & aFR & aFZ & (aMS & aKS & aR10 & aR11 & AQ)).
  set (W7 := fun a => F / 8 + 2147450942 <= a < F / 8 + 2147450942 + 7 \/ F + 496 <= a < F + 496 + 8).
  assert (WC7 : forall a, 0 <= a < 2 ^ 64 -> W7 a -> aclientw L ar (PM.vs_own s' ++ PM.vs_own s ++ LB) FF' 0 0 a /\ ~ (65536 <= a < 6914048)).
  { intros a Ha Wa. subst W7; cbn beta in Wa. destruct Wa as [Wa|Wa]; split.
    - apply (fframe_shadow_client L ar _ _ 0 0 F 5 (V2 - 160 + 32)). left; reflexivity. change (ff_bytes 5) with 2048.
      unfold in_shadow_of, HeapIfaceA.S. rewrite (proj1 (proj2 F8)). unfold HeapIfaceA.SB. clear - Wa. lia.
    - unfold HeapIfaceA.SB in *. clear - Wa FR. lia.
    - apply (fframe_client L ar _ _ 0 0 F 5 (V2 - 160 + 32)). left; reflexivity. change (ff_bytes 5) with 2048. clear - Wa; lia.
    - clear - Wa FR; lia. }
  rewrite <- app_assoc in C1.
  apply (apiece L ar C HI LYa HIok _ FF' LK5 cr5 A5 M6 model6 fx5 fx7 R6 0xa8d24 R7 0xa8d50 M7v W7 K C1 C2 aMS MG7).
  { intros a Ha Hna. apply aFZ; [exact Ha|..]; intros X0; apply Hna; subst W7; cbn beta; clear - X0; lia. }
  { exact WC7. }
  intros M7 model7 HH7 AM7 MRT7 HID7 VIS7 MGM7 FR7 VV7. change (mrestrict H6 M7 = M7v) in VIS7.
  rewrite app_assoc in HH7.
  assert (BI7 : Bv W (PM.vs_own s' ++ PM.vs_own s) M7 model7 LK5 cr5 A5).
  { apply (L5AFKR.binv_piece L ar HI M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W _ M6 model6 LK5 cr5 A5 M7 model7 W7 BI6 HH7 AM7 MRT7 MGM7 FR7).
    intros a Wa. subst W7; cbn beta in Wa. destruct Wa as [Wa|Wa]; [right; right| right; left]; change (ff_bytes 5) with 2048; [change (2048 / 8) with 256; unfold HeapIfaceA.SB in *; clear - Wa; lia| clear - Wa; lia]. }
  assert (RI7 : rinvH R R7 (V2 - 160) F 2147450880) by (apply (rinvH_ks R R6 R7 (V2 - 160) F 2147450880 PEACHP2.KS_ahnD2a RI6 aKS); unfold incl; apply L5K.incl_b; vm_compute; reflexivity).
  assert (LS7 : PESTA.ls_okA RSEGS AD AAD EE g M7).
  { apply (PEAHK.ls_piece _ M6 M7 W7 FR7); [| exact LS6]. intros a Wa. subst W7; cbn beta in Wa. clear - Wa FR. lia. }
  assert (PF7 : PEAHK2.pfoot F (V2 - 160) V2 W7) by (intros a Wa; subst W7; cbn beta in Wa; unfold HeapIfaceA.SB; clear - Wa; lia).
  assert (OAX7 : forall o k, F <= o -> o + k <= F + 496 -> PEAHK2.oav W7 o k).
  { intros o k H1 H2 x Hx. subst W7; cbn beta. pose proof (PMKA.S_in_shadow x ltac:(clear - Hx H1 H2 FR; lia)) as SX.
    unfold HeapIfaceA.S, HeapIfaceA.SB, BIGSHADOW_LO, BIGSHADOW_HI in *. split; intros X; clear - Hx X H1 H2 SX FBIG FR FM8; lia. }
  assert (HB7 : PEAHK2.hbase F M7 s s' sm).
  { apply (PEAHK2.hbase_piece L ar C SCFG HI HIok _ _ _ _ _ _ _ F (V2 - 160 + 32) C1 FIN5 FHF (V2 - 160) V2 W7 M6 M7 SLOW SHW FR7 PF7 s s' sm);
      [intros x Hx; rewrite app_assoc; apply in_or_app; left; exact Hx| apply OAX7; clear; lia| apply OAX7; clear; lia| exact (conj VS6 (conj IS6 SZI6))]. }

  assert (FR7lo : forall a, 0 <= a < 2 ^ 64 -> (a < BIGSHADOW_LO \/ BIGSHADOW_HI <= a) -> ~ (F + 496 <= a < F + 504) -> M7 (Z_to_bv 64 a) = M6 (Z_to_bv 64 a)).
  { intros a Ha Hr Hn. apply FR7; [exact Ha|]. subst W7; cbn beta. intros X. unfold BIGSHADOW_LO, BIGSHADOW_HI in Hr. clear - Hr Hn X FBD. lia. }
  assert (Z7 : PM.zeros_at M7 (F + 432) 24).
  { intros i Hi. rewrite (FR7lo (F + 432 + i)); [exact (Z6 i Hi)| clear - Hi FR; lia| unfold BIGSHADOW_LO, BIGSHADOW_HI in *; clear - Hi FBIG; lia| clear - Hi; lia]. }
  assert (SZK7 : shadow_zero M7 (F + 432) 3).
  { apply (PEAHK2.shz_frame M6 M7 W7 (F + 432) 3 FR7); [| unfold HeapIfaceA.S, HeapIfaceA.SB; clear - FBD; lia| unfold HeapIfaceA.S, HeapIfaceA.SB; clear - FBD; lia| exact SZK6].
    intros j Hj X. subst W7; cbn beta in X. unfold HeapIfaceA.S, HeapIfaceA.SB in X.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    assert (E432 : (F + 432) / 8 = F / 8 + 54) by (clear - FM8; lia).
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    rewrite E432 in X. clear - X Hj FBD FR FBIG. lia. }
  assert (HSTKa7 : L5.u64_at RSEGS M7 (V2 - 144) (F + 32)).
  { apply (L5C.u64_at_agree RSEGS M6 M7 (V2 - 144) (F + 32)); [| clear - V2R; lia| clear - V2R; lia| exact HSTKa6].
    intros i Hi; apply FR7lo; [clear - Hi V2R; lia| unfold BIGSHADOW_HI; clear - Hi V2R; lia| clear - Hi Q3 CLS; lia]. }
  assert (HSTKb7 : L5.u64_at RSEGS M7 (V2 - 136) F).
  { apply (L5C.u64_at_agree RSEGS M6 M7 (V2 - 136) F); [| clear - V2R; lia| clear - V2R; lia| exact HSTKb6].
    intros i Hi; apply FR7lo; [clear - Hi V2R; lia| unfold BIGSHADOW_HI; clear - Hi V2R; lia| clear - Hi Q3 CLS; lia]. }
  assert (PAYB7 : L5.bytes_at RSEGS M7 (PM.vs_data (F + 176) s') p).
  { pose proof IS6 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & VSA & _). replace (F + 96 + 80) with (F + 176) in VSA by (clear; lia).
    pose proof VSA as (_ & _ & VX). destruct s' as [n0|c0 n0 q0]; cbn [PM.vs_data] in PAYB6 |- *; cbn in SZ5, VX.
    - pose proof (proj1 VX) as SZB.
      apply (L5C.bytes_at_agree RSEGS M6 M7 (F + 176 + 1) p); rewrite ?LENp; [| clear - FR; lia| clear - FR SZB SZ5; lia| exact PAYB6].
      intros i Hi. apply FR7lo; [clear - Hi FR SZB SZ5; lia| unfold BIGSHADOW_LO, BIGSHADOW_HI; clear - Hi SZB SZ5 FBIG; lia| clear - Hi SZB SZ5; lia].
    - pose proof VX as (_ & _ & _ & NC & CC & _).
      destruct (PEAHK.blk_facts L ar C SCFG HI HIok _ _ _ _ _ _ _ q0 c0 C1 ltac:(apply in_or_app; left; left; reflexivity)) as (P0 & P3 & P4 & P5 & PSH & P47 & PIMG & PFA).
      pose proof (PFA (F, 5, V2 - 160 + 32) FIN5) as PF. cbn [ff_addr ff_class fst snd] in PF. change (ff_bytes 5) with 2048 in PF.
      apply (L5C.bytes_at_agree RSEGS M6 M7 q0 p); rewrite ?LENp; [| clear - P0; lia| clear - P47 NC SZ5; lia| exact PAYB6].
      intros i Hi. apply FR7; [clear - Hi P0 P47 NC SZ5; lia|]. subst W7; cbn beta. intros X. unfold BIGSHADOW_LO, BIGSHADOW_HI in PSH. clear - Hi X PF PSH NC SZ5 FBD FR. lia. }

  pose proof (L5AFKR.vis_facts L ar C HI LYa HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W _ M7 model7 LK5 cr5 A5 BI7)
    as ((VW7 & VIC7 & VSB7 & VUAR7 & VMS7) & VOWN7 & (VFD7 & VFW7 & VFSW7 & VFLC7 & VFLW7) & (FLCc7 & FLV7 & FV7 & SPV7 & FSV7)).
  change (ff_bytes 5) with 2048 in *. change (2048 / 8) with 256 in *.
  set (H7 := ahid A5 model7) in *. set (MV7 := mrestrict H7 M7) in *.
  assert (EMV7 : MV7 = M7v) by (subst MV7 H7; rewrite HID7; exact VIS7). rewrite <- EMV7 in AQ.
  pose proof AQ as (aV496 & aZ68 & aZ67 & aZ66 & aZ65 & aZ64 & aZ63 & aZ62 & _ & _).
  pose proof BI7 as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10).
  assert (Q5' : L5.writable RSEGS MV7 (V2 - 160) 160) by (eapply L5.writable_sub; [exact VW7| clear; lia| clear - CLS; lia]).
  assert (Q6' : L5.u64_at RSEGS MV7 (F + 2040) fl) by (replace (F + 2040) with (F + 2048 - 8) by (clear; lia); exact VFLC7).
  assert (ZE7 : L5KA.zeros_at MV7 (F / 8 + 2147450942) 7).
  { intros i Hi. assert (J : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6) by (clear - Hi; lia).
    assert (BU : forall j v, L5.u8_at RSEGS MV7 (F / 8 + 2147450942 + j) v -> 0 <= j < 7 -> MV7 (Z_to_bv 64 (F / 8 + 2147450942 + j)) = Some (Z_to_bv 8 v)).
    { intros j v U Hj. apply (L5ADHR.byte_of_u8 MV7 _ v U); clear - Hj FBD; lia. }
    repeat (destruct J as [J|J]; [subst i; apply BU; [gmem| clear; lia]|]). subst i; apply BU; [gmem| clear; lia]. }
  assert (R7_1 : getr R7 (reg 1) = Z_to_bv 64 (U R7 1)) by apply U_to.
  pose proof (PEACHP2.ahnD2b_conc fx7 R7 MV7 (fun j => match j with 2%nat => V2 | 40%nat => F | 41%nat => fl | 58%nat => U R7 1 | _ => 0 end)) as PP.
  cbn beta iota in PP.
  feed PP ltac:(first [ asm | apply UR | apply U_to | (clear - V2R; lia) | (clear - FR; lia) | (clear - FLR; lia) | exact F32
                     | exact VFD7 | exact VFW7 | exact VFSW7 | exact VFLW7 | exact Q5' | exact Q6' | exact ZE7 | (unfold PEACHP2.aligned; exact V2A)
                     | (match goal with |- getr R7 (reg ?k) = _ => rewrite (aKS k) by inl; asm end) ]).
  destruct PP as (fx8 & R8 & M8v & MG8 & bFR & bFZ & (bMS & bKS & bR1 & bR10 & bR11 & bR12 & bR18 & bR20 & bR24 & bR25 & BQ)).
  set (W8 := fun a => F + 504 <= a < F + 504 + 12).
  assert (WC8 : forall a, 0 <= a < 2 ^ 64 -> W8 a -> aclientw L ar (PM.vs_own s' ++ PM.vs_own s ++ LB) FF' 0 0 a /\ ~ (65536 <= a < 6914048)).
  { intros a Ha Wa. subst W8; cbn beta in Wa. split.
    - apply (fframe_client L ar _ _ 0 0 F 5 (V2 - 160 + 32)). left; reflexivity. change (ff_bytes 5) with 2048. clear - Wa; lia.
    - clear - Wa FR; lia. }
  rewrite <- app_assoc in D1.
  apply (apiece L ar C HI LYa HIok _ FF' LK5 cr5 A5 M7 model7 fx7 fx8 R7 0xa8d50 R8 0x78ab4 M8v W8 K D1 D2 bMS MG8).
  { intros a Ha Hna. apply bFZ; [exact Ha|]. intros X0; apply Hna; subst W8; cbn beta; clear - X0; lia. }
  { exact WC8. }
  intros M8 model8 HH8 AM8 MRT8 HID8 VIS8 MGM8 FR8 VV8. change (mrestrict H7 M8 = M8v) in VIS8.
  rewrite app_assoc in HH8.
  assert (BI8 : Bv W (PM.vs_own s' ++ PM.vs_own s) M8 model8 LK5 cr5 A5).
  { apply (L5AFKR.binv_piece L ar HI M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W _ M7 model7 LK5 cr5 A5 M8 model8 W8 BI7 HH8 AM8 MRT8 MGM8 FR8).
    intros a Wa. subst W8; cbn beta in Wa. right; left. change (ff_bytes 5) with 2048. clear - Wa; lia. }
  assert (RI8 : rinvH R R8 (V2 - 160) F 2147450880) by (apply (rinvH_ks R R7 R8 (V2 - 160) F 2147450880 PEACHP2.KS_ahnD2b RI7 bKS); unfold incl; apply L5K.incl_b; vm_compute; reflexivity).
  assert (LS8 : PESTA.ls_okA RSEGS AD AAD EE g M8).
  { apply (PEAHK.ls_piece _ M7 M8 W8 FR8); [| exact LS7]. intros a Wa. subst W8; cbn beta in Wa. clear - Wa FR. lia. }
  assert (PF8 : PEAHK2.pfoot F (V2 - 160) V2 W8) by (intros a Wa; subst W8; cbn beta in Wa; clear - Wa; lia).
  assert (OAX8 : forall o k, F <= o -> o + k <= F + 504 -> PEAHK2.oav W8 o k).
  { intros o k H1 H2 x Hx. subst W8; cbn beta. pose proof (PMKA.S_in_shadow x ltac:(clear - Hx H1 H2 FR; lia)) as SX.
    unfold HeapIfaceA.S, HeapIfaceA.SB, BIGSHADOW_LO, BIGSHADOW_HI in *. split; intros X; clear - Hx X H1 H2 SX FBIG FR; lia. }
  pose proof BI8 as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10).
  assert (HB8 : PEAHK2.hbase F M8 s s' sm).
  { apply (PEAHK2.hbase_piece L ar C SCFG HI HIok _ _ _ _ _ _ _ F (V2 - 160 + 32) D1 FIN5 FHF (V2 - 160) V2 W8 M7 M8 SLOW SHW FR8 PF8 s s' sm);
      [intros x Hx; rewrite app_assoc; apply in_or_app; left; exact Hx| apply OAX8; clear; lia| apply OAX8; clear; lia| exact HB7]. }
  assert (FR8lo : forall a, 0 <= a < 2 ^ 64 -> (a < F + 504 \/ F + 516 <= a) -> M8 (Z_to_bv 64 a) = M7 (Z_to_bv 64 a)).
  { intros a Ha Hr. apply FR8; [exact Ha|]. subst W8; cbn beta. intros X. clear - Hr X. lia. }
  assert (Z8 : PM.zeros_at M8 (F + 432) 24) by (intros i Hi; rewrite (FR8lo (F + 432 + i)) by (clear - Hi FR; lia); exact (Z7 i Hi)).
  assert (SZK8 : shadow_zero M8 (F + 432) 3).
  { apply (PEAHK2.shz_frame M7 M8 W8 (F + 432) 3 FR8); [| unfold HeapIfaceA.S, HeapIfaceA.SB; clear - FBD; lia| unfold HeapIfaceA.S, HeapIfaceA.SB; clear - FBD; lia| exact SZK7].
    intros j Hj X. subst W8; cbn beta in X. unfold HeapIfaceA.S, HeapIfaceA.SB in X. clear - X Hj FBD FR FBIG. unfold BIGSHADOW_LO, BIGSHADOW_HI in *. lia. }
  assert (SZE7 : shadow_zero M7 (F + 496) 7).
  { assert (AVS7 : L5A.avis H7 (F / 8 + 2147450942) 7) by (apply (PEAHK.avis_sub H7 (F / 8 + HeapIfaceA.SB) 256 _ 7 FSV7); unfold HeapIfaceA.SB; clear; lia).
    pose proof (proj1 (L5A.zeros_at_vis H7 M7 _ 7 AVS7) ZE7) as ZR7.
    intros j Hj. unfold byte_at, HeapIfaceA.S.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    assert (E496 : (F + 496) / 8 = F / 8 + 62) by (clear - FM8; lia).
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    rewrite E496. replace (F / 8 + 62 + HeapIfaceA.SB + j) with (F / 8 + 2147450942 + j) by (unfold HeapIfaceA.SB; clear; lia). apply ZR7. exact Hj. }
  assert (SZE8 : shadow_zero M8 (F + 496) 7).
  { apply (PEAHK2.shz_frame M7 M8 W8 (F + 496) 7 FR8); [| unfold HeapIfaceA.S, HeapIfaceA.SB; clear - FBD; lia| unfold HeapIfaceA.S, HeapIfaceA.SB; clear - FBD; lia| exact SZE7].
    intros j Hj X. subst W8; cbn beta in X. unfold HeapIfaceA.S, HeapIfaceA.SB in X. clear - X Hj FBD FR FBIG. unfold BIGSHADOW_LO, BIGSHADOW_HI in *. lia. }
  assert (HSTKa8 : L5.u64_at RSEGS M8 (V2 - 144) (F + 32)).
  { apply (L5C.u64_at_agree RSEGS M7 M8 (V2 - 144) (F + 32)); [intros i Hi; apply FR8lo; clear - Hi V2R Q3 CLS; lia| clear - V2R; lia| clear - V2R; lia| exact HSTKa7]. }
  assert (HSTKb8 : L5.u64_at RSEGS M8 (V2 - 136) F).
  { apply (L5C.u64_at_agree RSEGS M7 M8 (V2 - 136) F); [intros i Hi; apply FR8lo; clear - Hi V2R Q3 CLS; lia| clear - V2R; lia| clear - V2R; lia| exact HSTKb7]. }
  assert (PAYB8 : L5.bytes_at RSEGS M8 (PM.vs_data (F + 176) s') p).
  { pose proof IS6 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & VSA & _). replace (F + 96 + 80) with (F + 176) in VSA by (clear; lia).
    pose proof VSA as (_ & _ & VX). destruct s' as [n0|c0 n0 q0]; cbn [PM.vs_data] in PAYB7 |- *; cbn in SZ5, VX.
    - pose proof (proj1 VX) as SZB.
      apply (L5C.bytes_at_agree RSEGS M7 M8 (F + 176 + 1) p); rewrite ?LENp; [| clear - FR; lia| clear - FR SZB SZ5; lia| exact PAYB7].
      intros i Hi. apply FR8lo; [clear - Hi FR SZB SZ5; lia| left; clear - Hi SZB SZ5; lia].
    - pose proof VX as (_ & _ & _ & NC & CC & _).
      destruct (PEAHK.blk_facts L ar C SCFG HI HIok _ _ _ _ _ _ _ q0 c0 C1 ltac:(apply in_or_app; left; left; reflexivity)) as (P0 & P3 & P4 & P5 & PSH & P47 & PIMG & PFA).
      pose proof (PFA (F, 5, V2 - 160 + 32) FIN5) as PF. cbn [ff_addr ff_class fst snd] in PF. change (ff_bytes 5) with 2048 in PF.
      apply (L5C.bytes_at_agree RSEGS M7 M8 q0 p); rewrite ?LENp; [| clear - P0; lia| clear - P47 NC SZ5; lia| exact PAYB7].
      intros i Hi. apply FR8lo; [clear - Hi P0 P47 NC SZ5; lia|]. clear - Hi PF NC SZ5. lia. }

  assert (AVF7 : forall d k, 0 <= d -> d + k <= 2048 -> L5A.avis H7 (F + d) k) by (intros d k Hd1 Hd2; apply (PEAHK.avis_sub H7 F 2048 (F + d) k FV7); lia).
  assert (U496 : L5.u64_at RSEGS M8 (F + 496) 1258992).
  { apply (L5C.u64_at_agree RSEGS M7 M8 (F + 496) 1258992); [intros i Hi; apply FR8lo; clear - Hi FR; lia| clear - FR; lia| clear - FR; lia|].
    apply (proj1 (L5A.u64_at_vis H7 M7 (F + 496) 1258992 (AVF7 496 8 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - FR; lia) ltac:(clear - FR; lia))). exact aV496. }
  pose proof BQ as (bU512 & bU504 & _).
  assert (U504 : L5.u64_at RSEGS M8 (F + 504) (F + 432)).
  { apply (PEAHK.u64_vis H7 M8 M8v (F + 504) _ VV8 (AVF7 504 8 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - FR; lia) ltac:(clear - FR; lia)). exact bU504. }
  assert (U512 : L5.u32_at RSEGS M8 (F + 512) 1024).
  { apply (PEAHK.u32_vis H7 M8 M8v (F + 512) _ VV8 (AVF7 512 4 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - FR; lia) ltac:(clear - FR; lia)). exact bU512. }

  pose proof (L5AFKR.vis_facts L ar C HI LYa HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W _ M8 model8 LK5 cr5 A5 BI8)
    as ((_ & _ & _ & _ & _) & _ & (VFD8 & _ & _ & _ & _) & (_ & _ & FV8 & _ & _)).
  change (ff_bytes 5) with 2048 in *. change (2048 / 8) with 256 in *.
  assert (FDEF8 : L5.defined M8 F 2048) by (apply (proj1 (L5A.defined_vis (ahid A5 model8) M8 F 2048 FV8)); exact VFD8).
  assert (ACC2 : PMSPA.accA M8 (F + 520) 28).
  { apply (PEAHK2.acc_of_shz M8 (F + 496) 7 (F + 520) 28 SZE8); [| clear - FR; lia| clear; lia| clear; lia].
    replace (F + 496) with (F + 62 * 8) by (clear; lia). rewrite Z_mod_plus_full. exact FM8. }
  pose proof RI8 as (Z2 & Z3 & Z4 & Z8' & Z9 & Z19 & Z21 & Z26 & Z27).
  apply (MSET fx8 R8 M8 model8 (PM.vs_own s' ++ PM.vs_own s) LK5 cr5 A5 K (F + 520) 28 0xa8d84);
    [clear; lia| clear; lia| clear; lia| replace (F + 520) with (F + 65 * 8) by (clear; lia); rewrite Z_mod_plus_full; exact FM8
    | exact E1| exact E2| exact E6| exact ACC2| exact FDEF8| exact bR10| exact bR11| exact bR12| rewrite Z4; exact TP| exact bR1| reflexivity| clear; lia| exact Z2| exact K0|].
  intros R9 M9 model9 R9a0 RP9 Z9b HP9 MRT9 AM9 HH9.
  assert (WFI9 : PEAHK2.wfi F [(F + 520, 28)]) by (apply PEAHK2.wfi_cons; [cbn [fst snd]; left; clear; lia| apply PEAHK2.wfi_nil]).
  assert (LS9 : PESTA.ls_okA RSEGS AD AAD EE g M9).
  { apply (PEAHK.ls_ahpres L C LY g ar _ FF' (V2 - 160) 2560 [(F + 520, 28)] M8 M9 HP9); [| exact LS8].
    apply PEAHK.far_cons; [cbn [fst snd]; clear - FR; lia| apply PEAHK.far_nil]. }
  assert (BI9 : Bv W (PM.vs_own s' ++ PM.vs_own s) M9 model9 LK5 cr5 A5).
  { apply (L5AFKR.binv_callee L ar C HI HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W W _ (PM.vs_own s' ++ PM.vs_own s) _ M8 model8 LK5 cr5 A5 M9 model9 LK5 cr5 A5 2560 [(F + 520, 28)] BI8 HP9 HH9 AM9 MRT9 (incl_refl _) (incl_refl _)).
    - clear; lia.
    - clear - CLS; lia.
    - intros rr a [<-|[]] Ha. unfold L5.in_rng in Ha; cbn [fst snd] in Ha. unfold tocell. split; [clear - Ha FCEIL SLO CLS; lia|]. unfold HeapIfaceA.SB. change (ff_bytes 5) with 2048. clear - Ha FR F8 FBIG. lia.
    - intros a Hc _ rr [<-|[]] Ha. unfold L5.in_rng in Ha; cbn [fst snd] in Ha. apply (NCF a); [left; clear - Ha; lia| exact Hc].
    - intros a X0. exact X0. }
  assert (RI9 : rinvH R R9 (V2 - 160) F 2147450880) by exact (rinvH_pres R R8 R9 (V2 - 160) F 2147450880 RI8 RP9).
  pose proof RI9 as (Y2' & Y3' & Y4' & Y8'' & Y9' & Y19' & Y21' & Y26' & Y27').
  assert (S18 : getr R9 (reg 18) = Z_to_bv 64 (F + 520)) by (rewrite (cs_of_preserved R8 R9 18 RP9) by inl; exact bR18).
  assert (S20 : getr R9 (reg 20) = Z_to_bv 64 1024) by (rewrite (cs_of_preserved R8 R9 20 RP9) by inl; exact bR20).
  assert (S22 : getr R9 (reg 22) = Z_to_bv 64 (F + 432)) by (rewrite (cs_of_preserved R8 R9 22 RP9) by inl; rewrite (bKS 22%nat) by inl; rewrite (aKS 22%nat) by inl; exact Y22).
  assert (S23 : getr R9 (reg 23) = Z_to_bv 64 (F + 496)) by (rewrite (cs_of_preserved R8 R9 23 RP9) by inl; rewrite (bKS 23%nat) by inl; rewrite (aKS 23%nat) by inl; exact Y23).
  assert (S24 : getr R9 (reg 24) = Z_to_bv 64 (F + 1056)) by (rewrite (cs_of_preserved R8 R9 24 RP9) by inl; exact bR24).
  assert (S25 : getr R9 (reg 25) = Z_to_bv 64 (F + 592)) by (rewrite (cs_of_preserved R8 R9 25 RP9) by inl; exact bR25).

  assert (HB9 : PEAHK2.hbase F M9 s s' sm).
  { eapply PEAHK2.hbase_callee; first [ exact LY | exact HIok | exact E1 | exact HP9 | exact HB8 | exact FHF | exact FIN5 | exact WFI9 | exact (or_introl eq_refl)
      | (split; reflexivity) | (intros x Hx; apply in_or_app; left; exact Hx) | (apply PEAHK2.wapart_cons; [cbn [fst snd]; lia| apply PEAHK2.wapart_nil]) | apply incl_refl | lia ]. }
  assert (AK9 : forall a, 0 <= a < 2 ^ 64 -> ((F <= a < F + 520 \/ F + 548 <= a < F + 2040) /\ ~ (F + 24 <= a < F + 32)) -> M9 (Z_to_bv 64 a) = M8 (Z_to_bv 64 a)).
  { intros a Ha Hr. apply (proj1 HP9 a). split; [exact Ha| split].
    - apply (fframe_client L ar _ FF' (V2 - 160) 2560 F 5 (V2 - 160 + 32)); [left; reflexivity|]. change (ff_bytes 5) with 2048. clear - Hr; lia.
    - intros rr [<-|[]]. unfold L5.in_rng; cbn [fst snd]. clear - Hr. lia. }
  assert (AGstk9 : forall a, V2 - 160 <= a < V2 + cls -> M9 (Z_to_bv 64 a) = M8 (Z_to_bv 64 a)).
  { intros a Ha. apply (proj1 HP9 a). split; [clear - Ha V2R V2S CLS; lia| split].
    - apply stack_client; [clear - Ha SLO V2S CLS; lia| clear - Ha; lia].
    - intros rr [<-|[]]. unfold L5.in_rng; cbn [fst snd]. clear - Ha FCEIL SLO CLS. lia. }
  assert (Z9a : PM.zeros_at M9 (F + 432) 24) by (intros i Hi; rewrite (AK9 (F + 432 + i)) by (clear - Hi FR; lia); exact (Z8 i Hi)).
  assert (U496' : L5.u64_at RSEGS M9 (F + 496) 1258992) by (apply (L5C.u64_at_agree RSEGS M8 M9 (F + 496) 1258992); [intros i Hi; apply AK9; clear - Hi FR; lia| clear - FR; lia| clear - FR; lia| exact U496]).
  assert (U504' : L5.u64_at RSEGS M9 (F + 504) (F + 432)) by (apply (L5C.u64_at_agree RSEGS M8 M9 (F + 504) (F + 432)); [intros i Hi; apply AK9; clear - Hi FR; lia| clear - FR; lia| clear - FR; lia| exact U504]).
  assert (U512' : L5.u32_at RSEGS M9 (F + 512) 1024) by (apply (PEAHK.u32_agree M8 M9 (F + 512) 1024); [intros i Hi; apply AK9; clear - Hi FR; lia| clear - FR; lia| clear - FR; lia| exact U512]).
  assert (SZK9 : shadow_zero M9 (F + 432) 3).
  { apply (PEAHK2.shz_callee L ar _ FF' (V2 - 160) 2560 [(F + 520, 28)] M8 M9 (F, 5, V2 - 160 + 32) F (F + 432) 3 HP9 (or_introl eq_refl) (conj eq_refl eq_refl) FHF WFI9);
      [clear; lia| clear; lia| clear - FM8; lia| clear; lia| exact SZK8]. }
  assert (SZE9 : shadow_zero M9 (F + 496) 7).
  { apply (PEAHK2.shz_callee L ar _ FF' (V2 - 160) 2560 [(F + 520, 28)] M8 M9 (F, 5, V2 - 160 + 32) F (F + 496) 7 HP9 (or_introl eq_refl) (conj eq_refl eq_refl) FHF WFI9);
      [clear; lia| clear; lia| clear - FM8; lia| clear; lia| exact SZE8]. }
  assert (HSTKa9 : L5.u64_at RSEGS M9 (V2 - 144) (F + 32)).
  { apply (L5C.u64_at_agree RSEGS M8 M9 (V2 - 144) (F + 32)); [intros i Hi; apply AGstk9; clear - Hi CLS; lia| clear - V2R; lia| clear - V2R; lia| exact HSTKa8]. }
  assert (HSTKb9 : L5.u64_at RSEGS M9 (V2 - 136) F).
  { apply (L5C.u64_at_agree RSEGS M8 M9 (V2 - 136) F); [intros i Hi; apply AGstk9; clear - Hi CLS; lia| clear - V2R; lia| clear - V2R; lia| exact HSTKb8]. }
  assert (PAYB9 : L5.bytes_at RSEGS M9 (PM.vs_data (F + 176) s') p).
  { pose proof IS6 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & VSA & _). replace (F + 96 + 80) with (F + 176) in VSA by (clear; lia).
    pose proof VSA as (_ & _ & VX). destruct s' as [n0|c0 n0 q0]; cbn [PM.vs_data] in PAYB8 |- *; cbn in SZ5, VX.
    - pose proof (proj1 VX) as SZB.
      apply (L5C.bytes_at_agree RSEGS M8 M9 (F + 176 + 1) p); rewrite ?LENp; [| clear - FR; lia| clear - FR SZB SZ5; lia| exact PAYB8].
      intros i Hi. apply AK9; [clear - Hi FR SZB SZ5; lia| clear - Hi SZB SZ5; lia].
    - pose proof VX as (_ & _ & _ & NC & CC & _).
      destruct (PEAHK.blk_facts L ar C SCFG HI HIok _ _ _ _ _ _ _ q0 c0 C1 ltac:(apply in_or_app; left; left; reflexivity)) as (P0 & P3 & P4 & P5 & PSH & P47 & PIMG & PFA).
      pose proof (PFA (F, 5, V2 - 160 + 32) FIN5) as PF. cbn [ff_addr ff_class fst snd] in PF. change (ff_bytes 5) with 2048 in PF.
      apply (L5C.bytes_at_agree RSEGS M8 M9 q0 p); rewrite ?LENp; [| clear - P0; lia| clear - P47 NC SZ5; lia| exact PAYB8].
      intros i Hi. apply (proj1 HP9 i). split; [clear - Hi P0 P47 NC SZ5; lia| split].
      + left. exists (q0, c0). split; [apply in_or_app; left; apply in_or_app; left; left; reflexivity| cbn [fst snd]; clear - Hi NC SZ5; lia].
      + intros rr [<-|[]]. unfold L5.in_rng; cbn [fst snd]. clear - Hi PF NC SZ5. lia. }

  pose proof (L5AFKR.vis_facts L ar C HI LYa HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W _ M9 model9 LK5 cr5 A5 BI9)
    as ((VW9 & VIC9 & VSB9 & VUAR9 & VMS9) & VOWN9 & (VFD9 & VFW9 & VFSW9 & VFLC9 & VFLW9) & (FLCc9 & FLV9 & FV9 & SPV9 & FSV9)).
  change (ff_bytes 5) with 2048 in *. change (2048 / 8) with 256 in *.
  set (H9 := ahid A5 model9) in *. set (MV9 := mrestrict H9 M9) in *.
  pose proof BI9 as (G1 & G2' & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10).
  assert (Q5c : L5.writable RSEGS MV9 (V2 - 160) 160) by (eapply L5.writable_sub; [exact VW9| clear; lia| clear - CLS; lia]).
  assert (Q6c : L5.u64_at RSEGS MV9 (F + 2040) fl) by (replace (F + 2040) with (F + 2048 - 8) by (clear; lia); exact VFLC9).
  pose proof (PEACHP2.ahnE_conc fx8 R9 MV9 (fun j => match j with 2%nat => V2 | 40%nat => F | 41%nat => fl | 58%nat => U R9 1 | _ => 0 end)) as PP.
  cbn beta iota in PP.
  feed PP ltac:(first [ asm | apply UR | apply U_to | (clear - V2R; lia) | (clear - FR; lia) | (clear - FLR; lia) | exact F32
                     | exact VFD9 | exact VFW9 | exact VFSW9 | exact VFLW9 | exact Q5c | exact Q6c | (unfold PEACHP2.aligned; exact V2A) ]).
  destruct PP as (fx10 & R10' & M10v & MG10 & eFR & eFZ & (eMS & eKS & eR1 & eR10 & eR11 & eR12 & eR13 & EQ)).
  set (W10 := fun a => F / 8 + 2147450954 <= a < F / 8 + 2147450954 + 49 \/ F / 8 + 2147451012 <= a < F / 8 + 2147451012 + 4 \/ F + 1056 <= a < F + 1056 + 32).
  assert (WC10 : forall a, 0 <= a < 2 ^ 64 -> W10 a -> aclientw L ar (PM.vs_own s' ++ PM.vs_own s ++ LB) FF' 0 0 a /\ ~ (65536 <= a < 6914048)).
  { intros a Ha Wa. subst W10; cbn beta in Wa. destruct Wa as [Wa|[Wa|Wa]]; split.
    - apply (fframe_shadow_client L ar _ _ 0 0 F 5 (V2 - 160 + 32)). left; reflexivity. change (ff_bytes 5) with 2048.
      unfold in_shadow_of, HeapIfaceA.S. rewrite (proj1 (proj2 F8)). unfold HeapIfaceA.SB. clear - Wa. lia.
    - unfold HeapIfaceA.SB in *. clear - Wa FR. lia.
    - apply (fframe_shadow_client L ar _ _ 0 0 F 5 (V2 - 160 + 32)). left; reflexivity. change (ff_bytes 5) with 2048.
      unfold in_shadow_of, HeapIfaceA.S. rewrite (proj1 (proj2 F8)). unfold HeapIfaceA.SB. clear - Wa. lia.
    - unfold HeapIfaceA.SB in *. clear - Wa FR. lia.
    - apply (fframe_client L ar _ _ 0 0 F 5 (V2 - 160 + 32)). left; reflexivity. change (ff_bytes 5) with 2048. clear - Wa; lia.
    - clear - Wa FR; lia. }
  rewrite <- app_assoc in G1.
  apply (apiece L ar C HI LYa HIok _ FF' LK5 cr5 A5 M9 model9 fx8 fx10 R9 0xa8d84 R10' 0xb153c M10v W10 K G1 G2' eMS MG10).
  { intros a Ha Hna. apply eFZ; [exact Ha|..]; intros X0; apply Hna; subst W10; cbn beta; clear - X0; lia. }
  { exact WC10. }
  intros M10 model10 HH10 AM10 MRT10 HID10 VIS10 MGM10 FR10 VV10. change (mrestrict H9 M10 = M10v) in VIS10.
  rewrite app_assoc in HH10.
  assert (BI10 : Bv W (PM.vs_own s' ++ PM.vs_own s) M10 model10 LK5 cr5 A5).
  { apply (L5AFKR.binv_piece L ar HI M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W _ M9 model9 LK5 cr5 A5 M10 model10 W10 BI9 HH10 AM10 MRT10 MGM10 FR10).
    intros a Wa. subst W10; cbn beta in Wa. destruct Wa as [Wa|[Wa|Wa]]; [right; right| right; right| right; left]; change (ff_bytes 5) with 2048;
      [change (2048 / 8) with 256; unfold HeapIfaceA.SB in *; clear - Wa; lia| change (2048 / 8) with 256; unfold HeapIfaceA.SB in *; clear - Wa; lia| clear - Wa; lia]. }
  assert (RI10 : rinvH R R10' (V2 - 160) F 2147450880) by (apply (rinvH_ks R R9 R10' (V2 - 160) F 2147450880 PEACHP2.KS_ahnE RI9 eKS); unfold incl; apply L5K.incl_b; vm_compute; reflexivity).
  assert (LS10 : PESTA.ls_okA RSEGS AD AAD EE g M10).
  { apply (PEAHK.ls_piece _ M9 M10 W10 FR10); [| exact LS9]. intros a Wa. subst W10; cbn beta in Wa. unfold HeapIfaceA.SB in *. clear - Wa FR. lia. }
  assert (PF10 : PEAHK2.pfoot F (V2 - 160) V2 W10) by (intros a Wa; subst W10; cbn beta in Wa; unfold HeapIfaceA.SB; clear - Wa; lia).
  assert (OAX10 : forall o k, F <= o -> o + k <= F + 592 -> PEAHK2.oav W10 o k).
  { intros o k H1 H2 x Hx. subst W10; cbn beta. pose proof (PMKA.S_in_shadow x ltac:(clear - Hx H1 H2 FR; lia)) as SX.
    unfold HeapIfaceA.S, HeapIfaceA.SB, BIGSHADOW_LO, BIGSHADOW_HI in *. split; intros X; clear - Hx X H1 H2 SX FBIG FR FM8 FBD; lia. }
  assert (HB10 : PEAHK2.hbase F M10 s s' sm).
  { apply (PEAHK2.hbase_piece L ar C SCFG HI HIok _ _ _ _ _ _ _ F (V2 - 160 + 32) G1 FIN5 FHF (V2 - 160) V2 W10 M9 M10 SLOW SHW FR10 PF10 s s' sm);
      [intros x Hx; rewrite app_assoc; apply in_or_app; left; exact Hx| apply OAX10; clear; lia| apply OAX10; clear; lia| exact HB9]. }
  pose proof HB10 as (VS10 & IS10 & SZI10).
  assert (FR10lo : forall a, 0 <= a < 2 ^ 64 -> (a < BIGSHADOW_LO \/ BIGSHADOW_HI <= a) -> ~ (F + 1056 <= a < F + 1088) -> M10 (Z_to_bv 64 a) = M9 (Z_to_bv 64 a)).
  { intros a Ha Hr Hn. apply FR10; [exact Ha|]. subst W10; cbn beta. intros X. unfold BIGSHADOW_LO, BIGSHADOW_HI in Hr. clear - Hr Hn X FBD. lia. }
  assert (FAPP : forall a, F <= a < F + 2048 -> a < BIGSHADOW_LO \/ BIGSHADOW_HI <= a) by (intros a Ha; unfold BIGSHADOW_LO, BIGSHADOW_HI; clear - Ha FBIG; lia).
  assert (Z10a : PM.zeros_at M10 (F + 432) 24) by (intros i Hi; rewrite (FR10lo (F + 432 + i)); [exact (Z9a i Hi)| clear - Hi FR; lia| apply FAPP; clear - Hi; lia| clear - Hi; lia]).
  assert (Z10b : PM.zeros_at M10 (F + 520) 28) by (intros i Hi; rewrite (FR10lo (F + 520 + i)); [exact (Z9b i Hi)| clear - Hi FR; lia| apply FAPP; clear - Hi; lia| clear - Hi; lia]).
  assert (AGF10 : forall o k, F <= o -> o + k <= F + 1056 -> forall i, o <= i < o + k -> M10 (Z_to_bv 64 i) = M9 (Z_to_bv 64 i)).
  { intros o k H1 H2 i Hi. apply FR10lo; [clear - Hi H1 H2 FR; lia| apply FAPP; clear - Hi H1 H2; lia| clear - Hi H1 H2; lia]. }
  assert (V496 : L5.u64_at RSEGS M10 (F + 496) 1258992) by (apply (L5C.u64_at_agree RSEGS M9 M10 (F + 496) 1258992 (AGF10 (F + 496) 8 ltac:(clear; lia) ltac:(clear; lia))); [clear - FR; lia| clear - FR; lia| exact U496']).
  assert (V504 : L5.u64_at RSEGS M10 (F + 504) (F + 432)) by (apply (L5C.u64_at_agree RSEGS M9 M10 (F + 504) (F + 432) (AGF10 (F + 504) 8 ltac:(clear; lia) ltac:(clear; lia))); [clear - FR; lia| clear - FR; lia| exact U504']).
  assert (V512 : L5.u32_at RSEGS M10 (F + 512) 1024) by (apply (PEAHK.u32_agree M9 M10 (F + 512) 1024 (AGF10 (F + 512) 4 ltac:(clear; lia) ltac:(clear; lia))); [clear - FR; lia| clear - FR; lia| exact U512']).
  assert (SZK10 : shadow_zero M10 (F + 432) 3).
  { apply (PEAHK2.shz_frame M9 M10 W10 (F + 432) 3 FR10); [| unfold HeapIfaceA.S, HeapIfaceA.SB; clear - FBD; lia| unfold HeapIfaceA.S, HeapIfaceA.SB; clear - FBD; lia| exact SZK9].
    intros j Hj X. subst W10; cbn beta in X. unfold HeapIfaceA.S, HeapIfaceA.SB in X.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    assert (E432 : (F + 432) / 8 = F / 8 + 54) by (clear - FM8; lia).
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    rewrite E432 in X. clear - X Hj FBD FR FBIG. lia. }
  assert (SZE10 : shadow_zero M10 (F + 496) 7).
  { apply (PEAHK2.shz_frame M9 M10 W10 (F + 496) 7 FR10); [| unfold HeapIfaceA.S, HeapIfaceA.SB; clear - FBD; lia| unfold HeapIfaceA.S, HeapIfaceA.SB; clear - FBD; lia| exact SZE9].
    intros j Hj X. subst W10; cbn beta in X. unfold HeapIfaceA.S, HeapIfaceA.SB in X.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    assert (E496 : (F + 496) / 8 = F / 8 + 62) by (clear - FM8; lia).
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    rewrite E496 in X. clear - X Hj FBD FR FBIG. lia. }
  assert (HSTKa10 : L5.u64_at RSEGS M10 (V2 - 144) (F + 32)).
  { apply (L5C.u64_at_agree RSEGS M9 M10 (V2 - 144) (F + 32)); [| clear - V2R; lia| clear - V2R; lia| exact HSTKa9].
    intros i Hi; apply FR10lo; [clear - Hi V2R; lia| unfold BIGSHADOW_HI; clear - Hi V2R; lia| clear - Hi Q3 CLS; lia]. }
  assert (HSTKb10 : L5.u64_at RSEGS M10 (V2 - 136) F).
  { apply (L5C.u64_at_agree RSEGS M9 M10 (V2 - 136) F); [| clear - V2R; lia| clear - V2R; lia| exact HSTKb9].
    intros i Hi; apply FR10lo; [clear - Hi V2R; lia| unfold BIGSHADOW_HI; clear - Hi V2R; lia| clear - Hi Q3 CLS; lia]. }
  assert (PAYB10 : L5.bytes_at RSEGS M10 (PM.vs_data (F + 176) s') p).
  { pose proof IS6 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & VSA & _). replace (F + 96 + 80) with (F + 176) in VSA by (clear; lia).
    pose proof VSA as (_ & _ & VX). destruct s' as [n0|c0 n0 q0]; cbn [PM.vs_data] in PAYB9 |- *; cbn in SZ5, VX.
    - pose proof (proj1 VX) as SZB.
      apply (L5C.bytes_at_agree RSEGS M9 M10 (F + 176 + 1) p); rewrite ?LENp; [| clear - FR; lia| clear - FR SZB SZ5; lia| exact PAYB9].
      intros i Hi. apply FR10lo; [clear - Hi FR SZB SZ5; lia| apply FAPP; clear - Hi SZB SZ5; lia| clear - Hi SZB SZ5; lia].
    - pose proof VX as (_ & _ & _ & NC & CC & _).
      destruct (PEAHK.blk_facts L ar C SCFG HI HIok _ _ _ _ _ _ _ q0 c0 C1 ltac:(apply in_or_app; left; left; reflexivity)) as (P0 & P3 & P4 & P5 & PSH & P47 & PIMG & PFA).
      pose proof (PFA (F, 5, V2 - 160 + 32) FIN5) as PF. cbn [ff_addr ff_class fst snd] in PF. change (ff_bytes 5) with 2048 in PF.
      apply (L5C.bytes_at_agree RSEGS M9 M10 q0 p); rewrite ?LENp; [| clear - P0; lia| clear - P47 NC SZ5; lia| exact PAYB9].
      intros i Hi. apply FR10lo; [clear - Hi P0 P47 NC SZ5; lia| clear - Hi PSH NC SZ5; lia| clear - Hi PF NC SZ5; lia]. }

  assert (AVF9 : forall d k, 0 <= d -> d + k <= 2048 -> L5A.avis H9 (F + d) k) by (intros d k Hd1 Hd2; apply (PEAHK.avis_sub H9 F 2048 (F + d) k FV9); lia).
  assert (AVS9 : forall q k, F / 8 + 2147450880 <= q -> q + k <= F / 8 + 2147450880 + 256 -> L5A.avis H9 q k)
    by (intros q k Hd1 Hd2; apply (PEAHK.avis_sub H9 (F / 8 + HeapIfaceA.SB) 256 q k FSV9); unfold HeapIfaceA.SB; lia).
  pose proof EQ as (eU1080 & eU1084 & eU1072 & eU1064 & eU1056 & EQ'). decompose [and] EQ'. clear EQ'.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (Q592 : (F + 592) / 8 + HeapIfaceA.SB = F / 8 + 2147450954) by (unfold HeapIfaceA.SB; clear - FM8; lia).
  assert (Q1056 : (F + 1056) / 8 + HeapIfaceA.SB = F / 8 + 2147451012) by (unfold HeapIfaceA.SB; clear - FM8; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  assert (FDEF10 : L5.defined M10 F 2048).
  { pose proof (L5AFKR.vis_facts L ar C HI LYa HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W _ M10 model10 LK5 cr5 A5 BI10)
      as ((_ & _ & _ & _ & _) & _ & (VFD10 & _ & _ & _ & _) & (_ & _ & FV10 & _ & _)).
    apply (proj1 (L5A.defined_vis (ahid A5 model10) M10 F 2048 FV10)); exact VFD10. }
  apply (KONT fx10 R10' M10 model10 BI10 RI10 LS10).
  - exact eR1.
  - exact eR10.
  - exact eR11.
  - exact eR12.
  - exact eR13.
  - rewrite (eKS 18%nat) by inl. exact S18.
  - rewrite (eKS 20%nat) by inl. exact S20.
  - rewrite (eKS 22%nat) by inl. exact S22.
  - rewrite (eKS 23%nat) by inl. exact S23.
  - rewrite (eKS 24%nat) by inl. exact S24.
  - rewrite (eKS 25%nat) by inl. exact S25.
  - exact VS10.
  - split; [exact IS10| split; [exact SZ5| split; [exact SMG| split; [exact SMST| exact PAYB10]]]].
  -
    split.
    + apply (PEAHK4.sink0A_intro L ar P M10 (F + 432)).
      * apply (PEAHK4.u64_of_zeros M10 (F + 432) 24 (F + 432) Z10a); clear - FR; lia.
      * apply (PEAHK4.u64_of_zeros M10 (F + 432) 24 (F + 432 + 8) Z10a); clear - FR; lia.
      * apply (PEAHK4.u64_of_zeros M10 (F + 432) 24 (F + 432 + 16) Z10a); clear - FR; lia.
      * apply (L5.defined_sub M10 F 2048 (F + 432) 24 FDEF10); clear; lia.
      * apply (PEAHK2.acc_of_shz M10 (F + 432) 3 (F + 432) 24 SZK10); [| clear - FR; lia| clear; lia| clear; lia].
        replace (F + 432) with (F + 54 * 8) by (clear; lia). rewrite Z_mod_plus_full. exact FM8.
    + apply (PEAHK4.enc0A_intro L ar M10 (F + 496) F).
      * exact V496.
      * replace (F + 496 + 8) with (F + 504) by (clear; lia). exact V504.
      * replace (F + 496 + 16) with (F + 512) by (clear; lia). exact V512.
      * apply (PEAHK4.u64_of_zeros M10 (F + 520) 28 (F + 496 + 24) Z10b); clear - FR; lia.
      * apply (PEAHK4.u64_of_zeros M10 (F + 520) 28 (F + 496 + 32) Z10b); clear - FR; lia.
      * apply (PEAHK4.u64_of_zeros M10 (F + 520) 28 (F + 496 + 40) Z10b); clear - FR; lia.
      * apply (PEAHK4.u32_of_zeros M10 (F + 520) 28 (F + 496 + 48) Z10b); clear - FR; lia.
      * apply (L5.defined_sub M10 F 2048 (F + 496) 56 FDEF10); clear; lia.
      * apply (PEAHK2.acc_of_shz M10 (F + 496) 7 (F + 496) 56 SZE10); [| clear - FR; lia| clear; lia| clear; lia].
        replace (F + 496) with (F + 62 * 8) by (clear; lia). rewrite Z_mod_plus_full. exact FM8.
  - apply (PEAHK.u64_vis H9 M10 M10v (F + 1056) _ VV10 (AVF9 1056 8 ltac:(lia) ltac:(lia)) ltac:(clear - FR; lia) ltac:(clear - FR; lia)). exact eU1056.
  - apply (PEAHK.u64_vis H9 M10 M10v (F + 1064) _ VV10 (AVF9 1064 8 ltac:(lia) ltac:(lia)) ltac:(clear - FR; lia) ltac:(clear - FR; lia)). exact eU1064.
  - apply (PEAHK.u64_vis H9 M10 M10v (F + 1072) _ VV10 (AVF9 1072 8 ltac:(lia) ltac:(lia)) ltac:(clear - FR; lia) ltac:(clear - FR; lia)). exact eU1072.
  - apply (PEAHK.u32_vis H9 M10 M10v (F + 1080) _ VV10 (AVF9 1080 4 ltac:(lia) ltac:(lia)) ltac:(clear - FR; lia) ltac:(clear - FR; lia)). exact eU1080.
  - apply (L5.defined_sub M10 F 2048 (F + 592) 384 FDEF10); clear; lia.
  - apply (PEAHK.shz_vis H9 M10 M10v (F + 592) 49 (F / 8 + 2147450954) VV10 (AVS9 (F / 8 + 2147450954) 49 ltac:(lia) ltac:(lia)) Q592 ltac:(clear - FBD; lia) ltac:(clear - FBD; lia)).
    intros j Hj.
    assert (J : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6 \/ j = 7 \/ j = 8 \/ j = 9 \/ j = 10 \/ j = 11 \/ j = 12 \/ j = 13 \/ j = 14 \/ j = 15 \/ j = 16 \/ j = 17 \/ j = 18 \/ j = 19
                \/ j = 20 \/ j = 21 \/ j = 22 \/ j = 23 \/ j = 24 \/ j = 25 \/ j = 26 \/ j = 27 \/ j = 28 \/ j = 29 \/ j = 30 \/ j = 31 \/ j = 32 \/ j = 33 \/ j = 34 \/ j = 35 \/ j = 36 \/ j = 37
                \/ j = 38 \/ j = 39 \/ j = 40 \/ j = 41 \/ j = 42 \/ j = 43 \/ j = 44 \/ j = 45 \/ j = 46 \/ j = 47 \/ j = 48) by (clear - Hj; lia).
    repeat (destruct J as [J|J]; [subst j; gmem|]). subst j; gmem.
  - apply (PEAHK.shz_vis H9 M10 M10v (F + 1056) 4 (F / 8 + 2147451012) VV10 (AVS9 (F / 8 + 2147451012) 4 ltac:(lia) ltac:(lia)) Q1056 ltac:(clear - FBD; lia) ltac:(clear - FBD; lia)).
    intros j Hj. assert (J : j = 0 \/ j = 1 \/ j = 2 \/ j = 3) by (clear - Hj; lia).
    repeat (destruct J as [J|J]; [subst j; gmem|]). subst j; gmem.
  - exact SZI10.
  - exact SZK10.
  - exact SZE10.
  - exact HSTKa10.
  - exact HSTKb10.
Qed.
End Stage.
End SCFG_1.
End PEACH3b.
