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
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b L5StepAR_b L5CoreBR_b L5ADetailHR_b L5AFrameKR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HeapIfaceABx PmLayout PmLayoutA PnLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmModelFactsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStatics PmStaticsA PnStatics PnStaticsA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PnSpecsAa_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgSrc PgV8. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgSrcA_b PgV8A_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnModel PnRun. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnRunA_b PnRunAa_b PnStepA_b PnAReset1_b PnAHarnessStmts_b PnAHarnessKit_b PnAHarnessKit2_b PnAHarnessSK_b PnAHarnessP2_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module PNHA3.
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
Hypothesis WLOC : forall a, L5.outside W a -> L5.outside (PMSPA.loc_W PMA.AD) a.
Local Notation Bv := (L5AFKR.binv L ar HI M model LB FF LK A (V2 + cls) 36864 (V2 - 128) (tfrk (V2 + cls) R) F 5).
Local Notation FF' := ((F, 5, V2 - 128 + 32) :: FF).

Lemma stage3 (ISS : PMA.iss_ctor_spec L ar HI) (fx4 : FPState) (R4 : bvmap 5 word) (M4 : word -> option byte) (model4 : Model) (K : TSet)
      (LK4 : list fframe) (cr4 : credit) (A4 : list (Z * Z)) (s : PM.vstr) (data n : Z) (g : PNST.st) :
  Bv W (PM.vs_own s) M4 model4 LK4 cr4 A4 -> rinvH R R4 V2 cls F -> K [] -> PNSTA.ls_okA RSEGS PMA.AD PMA.AAD PMA.AN g M4 ->
  getr R4 (reg 1) = Z_to_bv 64 0xa8344 -> getr R4 (reg 10) = Z_to_bv 64 (F + 96) -> getr R4 (reg 11) = Z_to_bv 64 (F + 32) ->
  getr R4 (reg 12) = Z_to_bv 64 8 -> getr R4 (reg 21) = Z_to_bv 64 (F + 96) -> getr R4 (reg 22) = Z_to_bv 64 n -> getr R4 (reg 23) = Z_to_bv 64 data ->
  PM.vstr_at RSEGS PMSPA.accA M4 (F + 32) s -> PM.vs_size s = n -> (forall c n0 p, s = PM.VLong c n0 p -> 23 <= n0) -> 0 <= n < 2 ^ 26 -> 0 <= data < 2 ^ 64 ->
  PMSPA.credit_le (PMSPA.scA L (PM.cost1 (PMSPA.HV L ar) (n + 32))) cr4 ->
  shadow_zero M4 (F + 96) 34 ->
  (forall (fx5 : FPState) (R5 : bvmap 5 word) (M5 : word -> option byte) (model5 : Model) (LK5 : list fframe) (cr5 : credit) (A5 : list (Z * Z)) (s' : PM.vstr) (sm : PM.strm),
      Bv W (PM.vs_own s' ++ PM.vs_own s) M5 model5 LK5 cr5 A5 -> rinvH R R5 V2 cls F ->
      PNSTA.ls_okA RSEGS PMA.AD PMA.AAD PMA.AN (PNST.ST true (PNST.st_sys g) (PNST.st_ax g)) M5 ->
      getr R5 (reg 1) = Z_to_bv 64 0xa8474 -> getr R5 (reg 10) = Z_to_bv 64 (F + 464) -> getr R5 (reg 11) = Z_to_bv 64 (F + 96) ->
      getr R5 (reg 12) = Z_to_bv 64 (F + 960) -> getr R5 (reg 13) = Z_to_bv 64 (V2 - 104) ->
      getr R5 (reg 21) = Z_to_bv 64 (F + 96) -> getr R5 (reg 22) = Z_to_bv 64 (F + 464) -> getr R5 (reg 23) = Z_to_bv 64 data -> getr R5 (reg 26) = Z_to_bv 64 (F + 432) ->
      PM.vstr_at RSEGS PMSPA.accA M5 (F + 32) s -> PM.iss_at RSEGS PMA.AD PMSPA.accA M5 (F + 96) s' sm -> PM.vs_size s' = n ->
      PM.sm_g sm = PM.vs_data (F + 96 + 80) s' -> PM.sm_st sm = 0 ->
      PMSPA.credit_keep cr4 cr5 (PMSPA.scA L (PM.cost1 (PMSPA.HV L ar) (n + 32))) PMSPA.cr0 ->
      L5.u64_at RSEGS M5 (F + 432) 1251456 -> L5.u64_at RSEGS M5 (F + 960) 1251800 -> L5.u64_at RSEGS M5 (F + 968) 1251840 ->
      L5.u32_at RSEGS M5 (F + 976) 1024 -> L5.u32_at RSEGS M5 (F + 980) 0 ->
      shadow_zero M5 (F + 432) 1 -> shadow_zero M5 (F + 464) 53 -> shadow_zero M5 (F + 960) 3 -> shadow_zero M5 (F + 96) 34 ->
      srealizes RSEGS SCFG (@L5A.cfg fx5 R5 0xac78c M5 model5) K) ->
  srealizes RSEGS SCFG (@L5A.cfg fx4 R4 0xa8b74 M4 model4) K.
Proof.
  intros BI RI K0 LS R1a R10 R11 R12 R21 R22 R23 VS0 SIZE0 LONG0 Hn Hd CRD SZI KONT.
  pose proof G as G'. destruct G' as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG F32 FLA FLR FLBIG NCF NCS].
  change (ff_bytes 5) with 2048 in *. change (2048 / 8) with 256 in *.
  pose proof BI as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10).
  pose proof (L5AFKR.vis_facts L ar C HI LYa HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W (PM.vs_own s) M4 model4 LK4 cr4 A4 BI)
    as ((VW4 & VIC4 & VSB4 & VUAR4 & VMS4) & VOWN4 & (VFD4 & VFW4 & VFSW4 & VFLC4 & VFLW4) & (FLCc4 & FLV4 & FV4 & SPV4 & FSV4)).
  change (ff_bytes 5) with 2048 in *. change (2048 / 8) with 256 in *.
  pose proof RI as (X2 & X8 & X9 & X18 & X19 & X20 & X24 & X25 & X3 & X4 & X27).
  assert (FDEF4 : L5.defined M4 F 2048) by (apply (proj1 (L5A.defined_vis (ahid A4 model4) M4 F 2048 FV4)); exact VFD4).
  destruct LS as (LSB & LSL & LSS & LSE).
  unfold PMA.iss_ctor_spec, PMSPA.iss_ctor_spec in ISS. cbn [pa_iss_ctor PMA.AD ADDR_A] in ISS.
  apply (ISS fx4 R4 M4 model4 K (PM.vs_own s ++ LB) FF' LK4 A4 cr4 (F + 96) (F + 32) (V2 - 128) 0xa8344 s (PNST.st_loc g) B1 B2 K0).
  { eapply PNHASK.callee_entry; first [exact BI | exact RI | exact R1a | eassumption | (split; [lia| reflexivity]) | lia]. }
  { eapply PNHASK.callee_room; first [exact BI | eassumption | lia]. }
  { eapply PNHASK.callee_rs; eassumption. }
  { rewrite L5K.rl10. exact R10. }
  { rewrite L5K.rl11. exact R11. }
  { rewrite L5K.rl12. exact R12. }
  { exists (F, 5, V2 - 128 + 32). split; [left; reflexivity|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 5) with 2048. lia. }
  { exists (F, 5, V2 - 128 + 32). split; [left; reflexivity|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 5) with 2048. lia. }
  { lia. }
  { replace (F + 96) with (F + 12 * 8) by (clear; lia). rewrite Z_mod_plus_full. pose proof (proj1 F8) as E8. clear - E8 FR. lia. }
  { replace (F + 32) with (F + 4 * 8) by (clear; lia). rewrite Z_mod_plus_full. pose proof (proj1 F8) as E8. clear - E8 FR. lia. }
  { apply (L5.defined_sub M4 F 2048 (F + 96) 272 FDEF4); lia. }
  { apply (PMARS1.acc_of_shadow_zero M4 (F + 96) 34 (F + 96) 272 SZI); [| lia| lia].
    replace (F + 96) with (F + 12 * 8) by (clear; lia). rewrite Z_mod_plus_full. pose proof (proj1 F8) as E8. clear - E8 FR. lia. }
  { exact VS0. }
  { apply incl_appl. apply incl_refl. }
  { lia. }
  { exact LONG0. }
  { exact LSB. }
  { exact LSL. }
  { rewrite SIZE0. exact CRD. }
  intros fx' R' M' model' LK' Aw' s' sm cr' RP' ISA SZ' SMG SMST LOC' HP' CK' MRT' INCLK' INCA' AM' HH'.
  change (PMSPA.pm_scr 4) with 20480 in HP'.
  rewrite app_assoc in HH'.
  set (Wc := (F + 96, 272) :: (if PNST.st_loc g then [] else PMSPA.loc_W PMA.AD)) in *.
  assert (WcL : forall r, In r Wc -> r = (F + 96, 272) \/ In r (PMSPA.loc_W PMA.AD)).
  { intros r Hr. subst Wc. destruct Hr as [<-|Hr]; [left; reflexivity| right; destruct (PNST.st_loc g); [destruct Hr| exact Hr]]. }
  assert (LOCW : forall r, In r (PMSPA.loc_W PMA.AD) -> 0x672532 <= fst r /\ fst r + snd r <= 0x6733f0).
  { intros r Hr. cbn in Hr. destruct Hr as [<-|[<-|[]]]; cbn; lia. }
  (* [comment removed for export] *)
  assert (LS' : PNSTA.ls_okA RSEGS PMA.AD PMA.AAD PMA.AN (PNST.ST true (PNST.st_sys g) (PNST.st_ax g)) M').
  { apply (PNHAK.ls_ahpres_loc L C LY g ar (PM.vs_own s ++ LB) FF' (V2 - 128) 20480 Wc M4 M' HP'); [| split; [exact LSB| split; [exact LSL| split; [exact LSS| exact LSE]]]| exact LOC'].
    intros a Ha r Hr Hin. unfold L5.in_rng in Hin. destruct (WcL r Hr) as [->|X].
    - cbn [fst snd] in Hin. unfold PNHAK.bcell, PNHAK.scell, PNHAK.ecell in Ha. clear - Ha Hin FR. lia.
    - cbn in X. unfold PNHAK.bcell, PNHAK.scell, PNHAK.ecell in Ha. destruct X as [<-|[<-|[]]]; cbn [fst snd] in Hin; clear - Ha Hin; lia. }
  (* [comment removed for export] *)
  assert (BI' : Bv W (PM.vs_own s' ++ PM.vs_own s) M' model' LK' cr' Aw').
  { apply (L5AFKR.binv_callee L ar C HI HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W W (PM.vs_own s) (PM.vs_own s) (PM.vs_own s' ++ PM.vs_own s) M4 model4 LK4 cr4 A4 M' model' LK' cr' Aw' 20480 Wc BI HP' HH' AM' MRT' INCA' INCLK').
    - lia.
    - clear - CLS; lia.
    - intros rr a Hr Ha. unfold L5.in_rng in Ha. destruct (WcL rr Hr) as [->|X].
      + cbn [fst snd] in Ha. unfold tocell. split; [clear - Ha FCEIL SLO CLS; lia|]. unfold HeapIfaceA.SB. change (ff_bytes 5) with 2048. clear - Ha FR F8 FBIG. lia.
      + destruct (LOCW rr X) as (Y1 & Y2). unfold tocell. split; [clear - Ha Y1 Y2 SLO SPT; lia|]. unfold HeapIfaceA.SB. clear - Ha Y1 Y2 FR. lia.
    - intros a Hc Ho rr Hr Ha. destruct (WcL rr Hr) as [->|X].
      + unfold L5.in_rng in Ha; cbn [fst snd] in Ha. apply (NCF a); [left; clear - Ha; lia| exact Hc].
      + exact (WLOC a Ho rr X Ha).
    - intros a X. exact X. }
  pose proof (L5AFKR.vis_facts L ar C HI LYa HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W (PM.vs_own s' ++ PM.vs_own s) M' model' LK' cr' Aw' BI')
    as ((VW' & VIC' & VSB' & VUAR' & VMS') & VOWN' & (VFD' & VFW' & VFSW' & VFLC' & VFLW') & (FLCc' & FLV' & FV' & SPV' & FSV')).
  change (ff_bytes 5) with 2048 in *. change (2048 / 8) with 256 in *.
  set (H' := ahid Aw' model') in *. set (MV' := mrestrict H' M') in *.
  assert (RI' : rinvH R R' V2 cls F) by exact (rinvH_pres R R4 R' V2 cls F RI RP').
  pose proof RI' as (Y2 & Y8 & Y9 & Y18 & Y19 & Y20 & Y24 & Y25 & Y3 & Y4 & Y27).
  assert (Y21 : getr R' (reg 21) = Z_to_bv 64 (F + 96)) by (rewrite (cs_of_preserved R4 R' 21 RP') by inl; exact R21).
  assert (Y22 : getr R' (reg 22) = Z_to_bv 64 n) by (rewrite (cs_of_preserved R4 R' 22 RP') by inl; exact R22).
  assert (Y23 : getr R' (reg 23) = Z_to_bv 64 data) by (rewrite (cs_of_preserved R4 R' 23 RP') by inl; exact R23).
  (* [comment removed for export] *)
  assert (VS' : PM.vstr_at RSEGS PMSPA.accA M' (F + 32) s).
  { apply (PMFA.vstr_at_agreeA RSEGS M4 M' (F + 32) s); [clear - FR; lia| clear - FR; lia| | |exact VS0].
    - apply (PNHAK.agA_ahpres_ff L ar _ FF' (V2 - 128) 20480 Wc M4 M' (F, 5, V2 - 128 + 32) (F + 32) 24 HP' (or_introl eq_refl));
        cbn [ff_addr ff_class fst snd]; change (ff_bytes 5) with 2048; [lia| lia| clear - FR; lia| clear - FR; lia|].
      intros x Hx. split; intros rr Hr Hin; unfold L5.in_rng in Hin; destruct (WcL rr Hr) as [->|X]; cbn [fst snd] in Hin.
      + clear - Hx Hin; lia.
      + destruct (LOCW rr X) as (Z1 & Z2). clear - Hx Hin Z1 Z2 FR; lia.
      + pose proof (PMKA.S_in_shadow x ltac:(clear - Hx FR; lia)) as SX. unfold BIGSHADOW_LO, BIGSHADOW_HI in *. clear - SX Hin FBIG; lia.
      + pose proof (PMKA.S_in_shadow x ltac:(clear - Hx FR; lia)) as SX. destruct (LOCW rr X) as (Z1 & Z2). unfold BIGSHADOW_LO, BIGSHADOW_HI in *. clear - SX Hin Z1 Z2; lia.
    - intros c0 n0 p0 E0. subst s. cbn [PM.vs_own app] in B1 |- *.
      destruct (PNHAK.blk_facts L ar C SCFG HI HIok _ _ _ _ _ _ _ p0 c0 B1 (or_introl eq_refl)) as (P0 & P3 & P4 & P5 & PSH & P47 & PIMG & PFA).
      pose proof (PFA (F, 5, V2 - 128 + 32) (in_or_app FF' LK4 _ (or_introl (or_introl eq_refl)))) as PF. cbn [ff_addr ff_class fst snd] in PF. change (ff_bytes 5) with 2048 in PF.
      rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in PIMG.
      apply (PNHAK.agA_ahpres_blk L ar _ FF' (V2 - 128) 20480 Wc M4 M' p0 c0 HP' (or_introl eq_refl)); [lia| lia|].
      intros x Hx. split; intros rr Hr Hin; unfold L5.in_rng in Hin; destruct (WcL rr Hr) as [->|X]; cbn [fst snd] in Hin.
      + clear - Hx Hin PF; lia.
      + destruct (LOCW rr X) as (Z1 & Z2). clear - Hx Hin Z1 Z2 PIMG; lia.
      + pose proof (PMKA.S_in_shadow x ltac:(clear - Hx P47 P0; lia)) as SX. unfold BIGSHADOW_LO, BIGSHADOW_HI in *. clear - SX Hin FBIG; lia.
      + pose proof (PMKA.S_in_shadow x ltac:(clear - Hx P47 P0; lia)) as SX. destruct (LOCW rr X) as (Z1 & Z2). unfold BIGSHADOW_LO, BIGSHADOW_HI in *. clear - SX Hin Z1 Z2; lia. }
  assert (FHF3 : PNHAK2.hf F) by (unfold PNHAK2.hf, BIGSHADOW_LO, BIGSHADOW_HI; pose proof (proj1 F8) as E8; clear - FR FBIG E8; lia).
  assert (SZI' : shadow_zero M' (F + 96) 34).
  { assert (WFIc : PNHAK2.wfi F Wc) by (intros r Hr; destruct (WcL r Hr) as [->|X]; [left; cbn [fst snd]; lia| right; destruct (LOCW r X); lia]).
    apply (PNHAK2.shz_callee L ar _ FF' (V2 - 128) 20480 Wc M4 M' (F, 5, V2 - 128 + 32) F (F + 96) 34 HP' (or_introl eq_refl) (conj eq_refl eq_refl) FHF3 WFIc);
      [lia| lia| pose proof (proj1 F8) as E8; clear - E8; lia| lia| exact SZI]. }
  (* [comment removed for export] *)
  idtac.
  assert (Q1 : 4096 <= F <= 140737488353280) by (clear - FR; lia).
  assert (Q2 : 4096 <= fl <= 140737488355327) by (clear - FLR; lia).
  assert (Q3 : V2 - 128 + 144 <= F \/ F + 2048 <= V2 - 128) by (clear - FCEIL SLO CLS; lia).
  assert (Q4 : V2 - 128 + 144 <= fl \/ fl + 1 <= V2 - 128) by (clear - FLR SLO CLS; lia).
  assert (Q5 : L5.writable RSEGS MV' (V2 - 128) 128) by (eapply L5.writable_sub; [exact VW'| clear; lia| clear - CLS; lia]).
  assert (Q6 : L5.u64_at RSEGS MV' (F + 2040) fl) by (replace (F + 2040) with (F + 2048 - 8) by (clear; lia); exact VFLC').
  LeanFeed.pfeed P (PNAHP2.bhaD_conc fx' R' MV' (fun j => match j with 2%nat => V2 | 33%nat => data | 34%nat => n | 40%nat => F | 41%nat => fl | 58%nat => U R' 1 | _ => 0 end)) ltac:(first [ asm | apply UR | apply U_to | (clear - Hn; lia) | (clear - Hd; lia) | (clear - V2R; lia) | (clear - FR; lia) | (clear - FLR; lia) | exact F32
                     | exact VFD' | exact VFW' | exact VFSW' | exact VFLW' | exact Q5 | exact Q6 | (unfold PNAHP2.aligned; exact V2A) ]).
  destruct P as (fx5 & R5 & M5v & MG5 & dFR & dFZ & (dMS & dKS & dR1 & dR10 & dR11 & dR12 & dR13 & dR14 & dR22 & dR26 & DQ)).
  set (W5 := fun a => F + 432 <= a < F + 432 + 8 \/ F + 960 <= a < F + 960 + 24 \/ F / 8 + 2147450934 <= a < F / 8 + 2147450934 + 1
                      \/ F / 8 + 2147450938 <= a < F / 8 + 2147450938 + 53 \/ F / 8 + 2147451000 <= a < F / 8 + 2147451000 + 3).
  apply (apiece L ar C HI LYa HIok _ FF' LK' cr' Aw' M' model' fx' fx5 R' 0xa8344 R5 0xac78c M5v W5 K HH' AM' dMS MG5).
  { intros a Ha Hna. apply dFZ; [exact Ha|..]; intros X; apply Hna; subst W5; cbn beta; clear - X; lia. }
  { intros a Ha Wa. subst W5; cbn beta in Wa. split.
    - destruct Wa as [Wa|[Wa|Wa]].
      + apply (fframe_client L ar _ _ 0 0 F 5 (V2 - 128 + 32)). left; reflexivity. change (ff_bytes 5) with 2048. clear - Wa; lia.
      + apply (fframe_client L ar _ _ 0 0 F 5 (V2 - 128 + 32)). left; reflexivity. change (ff_bytes 5) with 2048. clear - Wa; lia.
      + apply (fframe_shadow_client L ar _ _ 0 0 F 5 (V2 - 128 + 32)). left; reflexivity. change (ff_bytes 5) with 2048.
        unfold in_shadow_of, HeapIfaceA.S. rewrite (proj1 (proj2 F8)). unfold HeapIfaceA.SB. clear - Wa. lia.
    - unfold HeapIfaceA.SB in *. clear - Wa FR. lia. }
  intros M5 model5 HH5 AM5 MRT5 HID5 VIS5 MGM5 FR5 VV5. change (mrestrict H' M5 = M5v) in VIS5.
  decompose [and] DQ. clear DQ.
  assert (BI5 : Bv W (PM.vs_own s' ++ PM.vs_own s) M5 model5 LK' cr' Aw').
  { apply (L5AFKR.binv_piece L ar HI M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W (PM.vs_own s' ++ PM.vs_own s) M' model' LK' cr' Aw' M5 model5 W5 BI' HH5 AM5 MRT5 MGM5 FR5).
    intros a Wa. subst W5; cbn beta in Wa. right. change (ff_bytes 5) with 2048. change (2048 / 8) with 256. unfold HeapIfaceA.SB in *. clear - Wa. lia. }
  assert (RI5 : rinvH R R5 V2 cls F) by (apply (rinvH_ks R R' R5 V2 cls F PNAHP2.KS_bhaD RI' dKS); vm_compute; reflexivity).
  assert (LS5 : PNSTA.ls_okA RSEGS PMA.AD PMA.AAD PMA.AN (PNST.ST true (PNST.st_sys g) (PNST.st_ax g)) M5).
  { apply (PNHAK.ls_piece _ M' M5 W5 FR5); [| exact LS']. intros a Wa. subst W5; cbn beta in Wa. clear - Wa FR. lia. }
  assert (WPF : forall a, W5 a -> (F <= a < F + 2048) \/ (F / 8 + HeapIfaceA.SB <= a < F / 8 + HeapIfaceA.SB + 256) \/ (V2 - 128 <= a < V2)).
  { intros a Wa. subst W5; cbn beta in Wa. unfold HeapIfaceA.SB. clear - Wa. lia. }
  assert (FIN : In (F, 5, V2 - 128 + 32) (FF' ++ LK')) by (apply in_or_app; left; left; reflexivity).
  assert (FM8 : F mod 8 = 0) by (pose proof (proj1 F8) as E8; clear - E8; lia).
  assert (SLOW : ahl_ceil ar <= V2 - 128) by (clear - SLO CLS; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (VS5 : PM.vstr_at RSEGS PMSPA.accA M5 (F + 32) s).
  { apply (PMFA.vstr_at_agreeA RSEGS M' M5 (F + 32) s); [clear - FR; lia| clear - FR; lia| | |exact VS'].
    - apply (PNHAK.agA_frame M' M5 W5 (F + 32) 24 FR5); [clear - FR; lia| clear - FR; lia|].
      intros x Hx. subst W5; cbn beta. unfold HeapIfaceA.S, HeapIfaceA.SB. split; intros X.
      + clear - Hx X FR FBIG F8. unfold BIGSHADOW_LO, BIGSHADOW_HI in *. lia.
      + clear - Hx X FR FBIG FM8. unfold BIGSHADOW_LO, BIGSHADOW_HI in *. lia.
    - intros c0 n0 p0 E0. apply (PNHAK.blk_agA L ar C SCFG HI HIok _ _ _ _ _ _ _ p0 c0 F (V2 - 128 + 32) (V2 - 128) V2 W5 M' M5 HH');
        [ rewrite E0; apply in_or_app; left; apply in_or_app; right; left; reflexivity | exact FIN | exact FM8 | clear - FR; lia | clear - FR; lia
        | unfold BIGSHADOW_LO, BIGSHADOW_HI; clear - FBIG; lia | exact SLOW | unfold BIGSHADOW_HI; clear - V2R; lia | exact FR5 | exact WPF ]. }
  assert (IS5 : PM.iss_at RSEGS PMA.AD PMSPA.accA M5 (F + 96) s' sm).
  { apply (PMFA.iss_at_agreeA RSEGS PMA.AD M' M5 (F + 96) s' sm); [clear - FR; lia| clear - FR; lia| | |exact ISA].
    - apply (PNHAK.agA_frame M' M5 W5 (F + 96) 272 FR5); [clear - FR; lia| clear - FR; lia|].
      intros x Hx. subst W5; cbn beta. unfold HeapIfaceA.S, HeapIfaceA.SB. split; intros X.
      + clear - Hx X FR FBIG F8. unfold BIGSHADOW_LO, BIGSHADOW_HI in *. lia.
      + clear - Hx X FR FBIG FM8. unfold BIGSHADOW_LO, BIGSHADOW_HI in *. lia.
    - intros c0 n0 p0 E0. apply (PNHAK.blk_agA L ar C SCFG HI HIok _ _ _ _ _ _ _ p0 c0 F (V2 - 128 + 32) (V2 - 128) V2 W5 M' M5 HH');
        [ rewrite E0; apply in_or_app; left; apply in_or_app; left; left; reflexivity | exact FIN | exact FM8 | clear - FR; lia | clear - FR; lia
        | unfold BIGSHADOW_LO, BIGSHADOW_HI; clear - FBIG; lia | exact SLOW | unfold BIGSHADOW_HI; clear - V2R; lia | exact FR5 | exact WPF ]. }
  assert (Q432 : (F + 432) / 8 + HeapIfaceA.SB = F / 8 + 2147450934) by (unfold HeapIfaceA.SB; clear - FM8; lia).
  assert (Q464 : (F + 464) / 8 + HeapIfaceA.SB = F / 8 + 2147450938) by (unfold HeapIfaceA.SB; clear - FM8; lia).
  assert (Q960 : (F + 960) / 8 + HeapIfaceA.SB = F / 8 + 2147451000) by (unfold HeapIfaceA.SB; clear - FM8; lia).
  assert (FBD : 0 <= F / 8 /\ F / 8 + 256 <= 2 ^ 44) by (clear - FR; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  assert (AVF : forall d k, 0 <= d -> d + k <= 2048 -> L5A.avis H' (F + d) k) by (intros d k Hd1 Hd2; apply (PNHAK.avis_sub H' F 2048 (F + d) k FV'); lia).
  assert (AVS : forall q k, F / 8 + 2147450880 <= q -> q + k <= F / 8 + 2147450880 + 256 -> L5A.avis H' q k)
    by (intros q k Hd1 Hd2; apply (PNHAK.avis_sub H' (F / 8 + HeapIfaceA.SB) 256 q k FSV'); unfold HeapIfaceA.SB; lia).
  apply (KONT fx5 R5 M5 model5 LK' cr' Aw' s' sm BI5 RI5 LS5).
  - exact dR1.
  - exact dR10.
  - exact dR11.
  - exact dR12.
  - exact dR13.
  - rewrite (dKS 21%nat) by inl. exact Y21.
  - exact dR22.
  - rewrite (dKS 23%nat) by inl. exact Y23.
  - exact dR26.
  - exact VS5.
  - exact IS5.
  - rewrite SZ'. exact SIZE0.
  - exact SMG.
  - exact SMST.
  - rewrite SIZE0 in CK'. exact CK'.
  - apply (PNHAK.u64_vis H' M5 M5v (F + 432) _ VV5 (AVF 432 8 ltac:(lia) ltac:(lia)) ltac:(clear - FR; lia) ltac:(clear - FR; lia)). asm.
  - apply (PNHAK.u64_vis H' M5 M5v (F + 960) _ VV5 (AVF 960 8 ltac:(lia) ltac:(lia)) ltac:(clear - FR; lia) ltac:(clear - FR; lia)). asm.
  - apply (PNHAK.u64_vis H' M5 M5v (F + 968) _ VV5 (AVF 968 8 ltac:(lia) ltac:(lia)) ltac:(clear - FR; lia) ltac:(clear - FR; lia)). asm.
  - apply (PNHAK.u32_vis H' M5 M5v (F + 976) _ VV5 (AVF 976 4 ltac:(lia) ltac:(lia)) ltac:(clear - FR; lia) ltac:(clear - FR; lia)). asm.
  - apply (PNHAK.u32_vis H' M5 M5v (F + 980) _ VV5 (AVF 980 4 ltac:(lia) ltac:(lia)) ltac:(clear - FR; lia) ltac:(clear - FR; lia)). asm.
  - apply (PNHAK.shz_vis H' M5 M5v (F + 432) 1 (F / 8 + 2147450934) VV5 (AVS (F / 8 + 2147450934) 1 ltac:(lia) ltac:(lia)) Q432 ltac:(clear - FBD; lia) ltac:(clear - FBD; lia)).
    intros j Hj. assert (J : j = 0) by (clear - Hj; lia). subst j. gmem.
  - apply (PNHAK.shz_vis H' M5 M5v (F + 464) 53 (F / 8 + 2147450938) VV5 (AVS (F / 8 + 2147450938) 53 ltac:(lia) ltac:(lia)) Q464 ltac:(clear - FBD; lia) ltac:(clear - FBD; lia)).
    intros j Hj. assert (J : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6 \/ j = 7 \/ j = 8 \/ j = 9 \/ j = 10 \/ j = 11 \/ j = 12 \/ j = 13 \/ j = 14 \/ j = 15 \/ j = 16 \/ j = 17 \/ j = 18 \/ j = 19 \/ j = 20 \/ j = 21 \/ j = 22 \/ j = 23 \/ j = 24 \/ j = 25 \/ j = 26 \/ j = 27 \/ j = 28 \/ j = 29 \/ j = 30 \/ j = 31 \/ j = 32 \/ j = 33 \/ j = 34 \/ j = 35 \/ j = 36 \/ j = 37 \/ j = 38 \/ j = 39 \/ j = 40 \/ j = 41 \/ j = 42 \/ j = 43 \/ j = 44 \/ j = 45 \/ j = 46 \/ j = 47 \/ j = 48 \/ j = 49 \/ j = 50 \/ j = 51 \/ j = 52) by (clear - Hj; lia).
    repeat (destruct J as [J|J]; [subst j; gmem|]). subst j; gmem.
  - apply (PNHAK.shz_vis H' M5 M5v (F + 960) 3 (F / 8 + 2147451000) VV5 (AVS (F / 8 + 2147451000) 3 ltac:(lia) ltac:(lia)) Q960 ltac:(clear - FBD; lia) ltac:(clear - FBD; lia)).
    intros j Hj. assert (J : j = 0 \/ j = 1 \/ j = 2) by (clear - Hj; lia).
    repeat (destruct J as [J|J]; [subst j; gmem|]). subst j; gmem.
  - apply (PNHAK2.shz_frame M' M5 W5 (F + 96) 34 FR5); [| unfold HeapIfaceA.S, HeapIfaceA.SB; clear - FBD; lia| unfold HeapIfaceA.S, HeapIfaceA.SB; clear - FBD; lia| exact SZI'].
    intros j Hj X. subst W5; cbn beta in X. unfold HeapIfaceA.S, HeapIfaceA.SB in X.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    assert (E96 : (F + 96) / 8 = F / 8 + 12) by (clear - FM8; lia).
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    rewrite E96 in X. clear - X Hj FBD FR FBIG. lia.
Qed.
End Stage.
End SCFG_1.
End PNHA3.
