(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA IcptIfaceAB0 LibIface AsanAcct AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5CoreKit L5LazyA L5DefsAB0 L5CoreAB0S9 L5StepARB0S9 L5CoreBRB0S9 L5ADetailHRB0S9 L5AFrameKRB0S9 HeapIfaceAEx.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout PmLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PmModel PmModelFacts PmModelFactsA PmStatics PmStaticsA PnStatics PnStaticsA PmSpecs PmSpecsA PeSpecsAb PeStepAB0.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PeCLayout PeCLayoutB.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PeCStaticsA PeCSink PeCSinkA PeCModel PeCModelA PeCSpecs PeCSpecsA PeCSpecsAb PeBCHarnessStmts PeBCHarnessKit PeBCHarnessKit2 PeBCHarnessSK PeBCHarnessKit3 PeBCHarnessP2.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Spec Require Import UbjRef.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9.Spec Require Import UbjRefFactsS9.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module PEBCH3.
Import L5A. Import L5CA. Import L5SAR. Import PEBCH.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Abbreviation AD := PeCLayoutB.CADDR_B.
Abbreviation AAD := PeCLayoutB.CAADDR_B.
Abbreviation EE := PeCLayoutB.EADDR_B.
Local Ltac inl := apply L5K.in_b; vm_compute; reflexivity.
Local Ltac asm := match goal with H : ?T |- ?G => constr_eq T G; exact H end.
Local Ltac hsc := first [ asm | apply UR | apply U_to | rk | gmem | (arith_goal; first [asm | alia]) | assumption ].
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Section Stage.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMB.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Let LYa := PMB.ly_as0 L C LY.
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
Hypothesis WAPP : PMKB.wapp W.
Hypothesis WLOC : forall a, L5.outside W a -> L5.outside (PMSPA.loc_W AD) a.
Local Notation Bv := (L5AFKR.binv L ar HI M model LB FF LK A (V2 + cls) 36864 (V2 - 160) (tfrk (V2 + cls) R) F 5).
Local Notation FF' := ((F, 5, V2 - 160 + 32) :: FF).

Variable payload : list byte.
Local Notation n := (PEBCH.n payload).
Local Notation p := (PEBCH.p payload).
Lemma stage3 (ISS : PECSB.iss_ctor_c_spec L ar HI) (fx4 : FPState) (R4 : bvmap 5 word) (M4 : word -> option byte) (model4 : Model) (K : TSet)
      (LK4 : list fframe) (cr4 : credit) (A4 : list (Z * Z)) (s : PM.vstr) (data : Z) (g : PMST.st) :
  Bv W (PM.vs_own s) M4 model4 LK4 cr4 A4 -> rinvH R R4 (V2 - 160) F 2147450880 -> K [] -> PESTA.ls_okA RSEGS AD AAD EE g M4 ->
  getr R4 (reg 1) = Z_to_bv 64 0xa9528 -> getr R4 (reg 10) = Z_to_bv 64 (F + 96) -> getr R4 (reg 11) = Z_to_bv 64 (F + 32) ->
  getr R4 (reg 12) = Z_to_bv 64 8 -> getr R4 (reg 18) = Z_to_bv 64 (F + 32) -> getr R4 (reg 22) = Z_to_bv 64 n -> getr R4 (reg 23) = Z_to_bv 64 data ->
  PEBCH.hs_pay payload F M4 s -> 0 <= n < 2 ^ 26 -> 0 <= data < 2 ^ 64 ->
  PMSPA.credit_le (PMSPA.scA L (PM.cost1 (PMSPA.HV L ar) (n + 32))) cr4 ->
  shadow_zero M4 (F + 96) 34 -> L5.u64_at RSEGS M4 (V2 - 144) (F + 32) -> L5.u64_at RSEGS M4 (V2 - 136) F ->
  (forall (fx5 : FPState) (R5 : bvmap 5 word) (M5 : word -> option byte) (model5 : Model) (LK5 : list fframe) (cr5 : credit) (A5 : list (Z * Z)) (s' : PM.vstr) (sm : PM.strm),
      Bv W (PM.vs_own s' ++ PM.vs_own s) M5 model5 LK5 cr5 A5 -> rinvH R R5 (V2 - 160) F 2147450880 ->
      PESTA.ls_okA RSEGS AD AAD EE (PMST.ST true (PMST.st_sys g) (PMST.st_err g)) M5 ->
      getr R5 (reg 1) = Z_to_bv 64 0xa954c -> getr R5 (reg 10) = Z_to_bv 64 (F + 432) -> getr R5 (reg 11) = Z_to_bv 64 0 ->
      getr R5 (reg 12) = Z_to_bv 64 24 -> getr R5 (reg 18) = Z_to_bv 64 (F + 32) -> getr R5 (reg 22) = Z_to_bv 64 (F + 432) -> getr R5 (reg 23) = Z_to_bv 64 (F + 496) ->
      PM.vstr_at RSEGS PMSPA.accA M5 (F + 32) s -> PEBCH.his_pay payload F M5 s' sm ->
      PMSPA.credit_keep cr4 cr5 (PMSPA.scA L (PM.cost1 (PMSPA.HV L ar) (n + 32))) PMSPA.cr0 ->
      shadow_zero M5 (F + 432) 3 -> shadow_zero M5 (F + 96) 34 -> L5.u64_at RSEGS M5 (V2 - 144) (F + 32) -> L5.u64_at RSEGS M5 (V2 - 136) F ->
      srealizes RSEGS SCFG (@L5A.cfg fx5 R5 0x792dc M5 model5) K) ->
  srealizes RSEGS SCFG (@L5A.cfg fx4 R4 0xa9e08 M4 model4) K.
Proof.
  intros BI RI K0 LS R1a R10 R11 R12 R18 R22 R23 (VS0 & SIZE0 & PAYB & LONG0) Hn Hd CRD SZI HSTKa HSTKb KONT.
  pose proof G as G'. destruct G' as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG F32 FLA FLR FLBIG NCF NCS].
  change (ff_bytes 5) with 2048 in *. change (2048 / 8) with 256 in *.
  pose proof BI as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10).
  pose proof (L5AFKR.vis_facts L ar C HI LYa HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W (PM.vs_own s) M4 model4 LK4 cr4 A4 BI)
    as ((VW4 & VIC4 & VSB4 & VUAR4 & VMS4) & VOWN4 & (VFD4 & VFW4 & VFSW4 & VFLC4 & VFLW4) & (FLCc4 & FLV4 & FV4 & SPV4 & FSV4)).
  change (ff_bytes 5) with 2048 in *. change (2048 / 8) with 256 in *.
  pose proof RI as (X2 & X3 & X4 & X8 & X9 & X19 & X21 & X26 & X27).
  assert (FDEF4 : L5.defined M4 F 2048) by (apply (proj1 (L5A.defined_vis (ahid A4 model4) M4 F 2048 FV4)); exact VFD4).
  destruct LS as (LSB & LSL & LSS & LSE).
  unfold PECSB.iss_ctor_c_spec, PECSPA.iss_ctor_c_spec in ISS. cbn [pa_iss_ctor PeCLayoutB.CADDR_B] in ISS.
  apply (ISS fx4 R4 M4 model4 K (PM.vs_own s ++ LB) FF' LK4 A4 cr4 (F + 96) (F + 32) (V2 - 160) 0xa9528 s (PMST.st_loc g) p B1 B2 K0).
  { eapply PEBHSK.callee_entry; first [exact BI | exact RI | exact R1a | eassumption | (split; [lia| reflexivity]) | lia]. }
  { eapply PEBHSK.callee_room; first [exact BI | eassumption | lia]. }
  { eapply PEBHSK.callee_rs; eassumption. }
  { rewrite L5K.rl10. exact R10. }
  { rewrite L5K.rl11. exact R11. }
  { rewrite L5K.rl12. exact R12. }
  { exists (F, 5, V2 - 160 + 32). split; [left; reflexivity|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 5) with 2048. lia. }
  { exists (F, 5, V2 - 160 + 32). split; [left; reflexivity|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 5) with 2048. lia. }
  { lia. }
  { replace (F + 96) with (F + 12 * 8) by (clear; lia). rewrite Z_mod_plus_full. pose proof (proj1 F8) as E8. clear - E8 FR. lia. }
  { replace (F + 32) with (F + 4 * 8) by (clear; lia). rewrite Z_mod_plus_full. pose proof (proj1 F8) as E8. clear - E8 FR. lia. }
  { apply (L5.defined_sub M4 F 2048 (F + 96) 272 FDEF4); lia. }
  { apply (PEBHK2.acc_of_shz M4 (F + 96) 34 (F + 96) 272 SZI); [| clear - FR; lia| clear; lia| clear; lia].
    replace (F + 96) with (F + 12 * 8) by (clear; lia). rewrite Z_mod_plus_full. pose proof (proj1 F8) as E8. clear - E8 FR. lia. }
  { exact VS0. }
  { apply incl_appl. apply incl_refl. }
  { lia. }
  { exact LONG0. }
  { rewrite SIZE0. unfold PEBCH.p, PEBCH.n. rewrite length_map. reflexivity. }
  { exact PAYB. }
  { exact LSB. }
  { exact LSL. }
  { rewrite SIZE0. exact CRD. }
  intros fx' R' M' model' LK' Aw' s' sm cr' RP' ISA SZ' SMG SMST PAYB' LOC' HP' CK' MRT' INCLK' INCA' AM' HH'. replace (F + 96 + 80) with (F + 176) in SMG, PAYB' by (clear; lia).
  change (PMSPA.pm_scr 4) with 20480 in HP'.
  rewrite app_assoc in HH'.
  set (Wc := (F + 96, 272) :: (if PMST.st_loc g then [] else PMSPA.loc_W AD)) in *.
  assert (WcL : forall r, In r Wc -> r = (F + 96, 272) \/ In r (PMSPA.loc_W AD)).
  { intros r Hr. subst Wc. destruct Hr as [<-|Hr]; [left; reflexivity| right; destruct (PMST.st_loc g); [destruct Hr| exact Hr]]. }
  assert (LOCW : forall r, In r (PMSPA.loc_W AD) -> 0x6789b2 <= fst r /\ fst r + snd r <= 0x679870).
  { intros r Hr. cbn in Hr. destruct Hr as [<-|[<-|[]]]; cbn; lia. }

  assert (LS' : PESTA.ls_okA RSEGS AD AAD EE (PMST.ST true (PMST.st_sys g) (PMST.st_err g)) M').
  { apply (PEBHK.ls_ahpres_loc L C LY g ar (PM.vs_own s ++ LB) FF' (V2 - 160) 20480 Wc M4 M' HP'); [| split; [exact LSB| split; [exact LSL| split; [exact LSS| exact LSE]]]| exact LOC'].
    intros a Ha r Hr Hin. unfold L5.in_rng in Hin. destruct (WcL r Hr) as [->|X].
    - cbn [fst snd] in Hin. unfold PEBHK.bcell, PEBHK.scell, PEBHK.ecell in Ha. clear - Ha Hin FR. lia.
    - cbn in X. unfold PEBHK.bcell, PEBHK.scell, PEBHK.ecell in Ha. destruct X as [<-|[<-|[]]]; cbn [fst snd] in Hin; clear - Ha Hin; lia. }

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
  assert (RI' : rinvH R R' (V2 - 160) F 2147450880) by exact (rinvH_pres R R4 R' (V2 - 160) F 2147450880 RI RP').
  pose proof RI' as (Y2 & Y3 & Y4 & Y8 & Y9 & Y19 & Y21 & Y26 & Y27).
  assert (Y18 : getr R' (reg 18) = Z_to_bv 64 (F + 32)) by (rewrite (cs_of_preserved R4 R' 18 RP') by inl; exact R18).

  assert (AGstk : forall a, V2 - 160 <= a < V2 + cls -> M' (Z_to_bv 64 a) = M4 (Z_to_bv 64 a)).
  { intros a Ha. apply (proj1 HP' a). split; [clear - Ha V2R V2S CLS; lia| split].
    - apply stack_client; [clear - Ha SLO V2S CLS; lia| clear - Ha; lia].
    - intros rr Hr. destruct (WcL rr Hr) as [->|X]; unfold L5.in_rng; cbn [fst snd]; [clear - Ha FCEIL SLO CLS; lia|].
      destruct (LOCW rr X) as (Y1' & Y2'). clear - Ha Y1' Y2' V2R. lia. }
  assert (HSTKa' : L5.u64_at RSEGS M' (V2 - 144) (F + 32)).
  { apply (L5C.u64_at_agree RSEGS M4 M' (V2 - 144) (F + 32)); [intros i Hi; apply AGstk; clear - Hi CLS; lia| clear - V2R; lia| clear - V2R; lia| exact HSTKa]. }
  assert (HSTKb' : L5.u64_at RSEGS M' (V2 - 136) F).
  { apply (L5C.u64_at_agree RSEGS M4 M' (V2 - 136) F); [intros i Hi; apply AGstk; clear - Hi CLS; lia| clear - V2R; lia| clear - V2R; lia| exact HSTKb]. }
  assert (Y22 : getr R' (reg 22) = Z_to_bv 64 n) by (rewrite (cs_of_preserved R4 R' 22 RP') by inl; exact R22).
  assert (Y23 : getr R' (reg 23) = Z_to_bv 64 data) by (rewrite (cs_of_preserved R4 R' 23 RP') by inl; exact R23).

  assert (VS' : PM.vstr_at RSEGS PMSPA.accA M' (F + 32) s).
  { apply (PMFA.vstr_at_agreeA RSEGS M4 M' (F + 32) s); [clear - FR; lia| clear - FR; lia| | |exact VS0].
    - apply (PEBHK.agA_ahpres_ff L ar _ FF' (V2 - 160) 20480 Wc M4 M' (F, 5, V2 - 160 + 32) (F + 32) 24 HP' (or_introl eq_refl));
        cbn [ff_addr ff_class fst snd]; change (ff_bytes 5) with 2048; [lia| lia| clear - FR; lia| clear - FR; lia|].
      intros x Hx. split; intros rr Hr Hin; unfold L5.in_rng in Hin; destruct (WcL rr Hr) as [->|X]; cbn [fst snd] in Hin.
      + clear - Hx Hin; lia.
      + destruct (LOCW rr X) as (Z1 & Z2). clear - Hx Hin Z1 Z2 FR; lia.
      + pose proof (PMKB.S_in_shadow x ltac:(clear - Hx FR; lia)) as SX. unfold BIGSHADOW_LO, BIGSHADOW_HI in *. clear - SX Hin FBIG; lia.
      + pose proof (PMKB.S_in_shadow x ltac:(clear - Hx FR; lia)) as SX. destruct (LOCW rr X) as (Z1 & Z2). unfold BIGSHADOW_LO, BIGSHADOW_HI in *. clear - SX Hin Z1 Z2; lia.
    - intros c0 n0 p0 E0. subst s. cbn [PM.vs_own app] in B1 |- *.
      destruct (PEBHK.blk_facts L ar C SCFG HI HIok _ _ _ _ _ _ _ p0 c0 B1 (or_introl eq_refl)) as (P0 & P3 & P4 & P5 & PSH & P47 & PIMG & PFA).
      pose proof (PFA (F, 5, V2 - 160 + 32) (in_or_app FF' LK4 _ (or_introl (or_introl eq_refl)))) as PF. cbn [ff_addr ff_class fst snd] in PF. change (ff_bytes 5) with 2048 in PF.
      rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in PIMG.
      apply (PEBHK.agA_ahpres_blk L ar _ FF' (V2 - 160) 20480 Wc M4 M' p0 c0 HP' (or_introl eq_refl)); [lia| lia|].
      intros x Hx. split; intros rr Hr Hin; unfold L5.in_rng in Hin; destruct (WcL rr Hr) as [->|X]; cbn [fst snd] in Hin.
      + clear - Hx Hin PF; lia.
      + destruct (LOCW rr X) as (Z1 & Z2). clear - Hx Hin Z1 Z2 PIMG; lia.
      + pose proof (PMKB.S_in_shadow x ltac:(clear - Hx P47 P0; lia)) as SX. unfold BIGSHADOW_LO, BIGSHADOW_HI in *. clear - SX Hin FBIG; lia.
      + pose proof (PMKB.S_in_shadow x ltac:(clear - Hx P47 P0; lia)) as SX. destruct (LOCW rr X) as (Z1 & Z2). unfold BIGSHADOW_LO, BIGSHADOW_HI in *. clear - SX Hin Z1 Z2; lia. }
  assert (FHF3 : PEBHK2.hf F) by (unfold PEBHK2.hf, BIGSHADOW_LO, BIGSHADOW_HI; pose proof (proj1 F8) as E8; clear - FR FBIG E8; lia).
  assert (SZI' : shadow_zero M' (F + 96) 34).
  { assert (WFIc : PEBHK2.wfi F Wc) by (intros r Hr; destruct (WcL r Hr) as [->|X]; [left; cbn [fst snd]; lia| right; destruct (LOCW r X); lia]).
    apply (PEBHK2.shz_callee L ar _ FF' (V2 - 160) 20480 Wc M4 M' (F, 5, V2 - 160 + 32) F (F + 96) 34 HP' (or_introl eq_refl) (conj eq_refl eq_refl) FHF3 WFIc);
      [lia| lia| pose proof (proj1 F8) as E8; clear - E8; lia| lia| exact SZI]. }

  pose proof (PEBCHP2.bhnD1_conc fx' R' MV' (fun j => match j with 2%nat => V2 | 33%nat => data | 34%nat => n | 40%nat => F | 41%nat => fl | 58%nat => U R' 1 | _ => 0 end)) as P.
  cbn beta iota in P.
  assert (Q1 : 4096 <= F <= 140737488353280) by (clear - FR; lia).
  assert (Q2 : 4096 <= fl <= 140737488355327) by (clear - FLR; lia).
  assert (Q3 : V2 - 160 + 176 <= F \/ F + 2048 <= V2 - 160) by (clear - FCEIL SLO CLS; lia).
  assert (Q4 : V2 - 160 + 176 <= fl \/ fl + 1 <= V2 - 160) by (clear - FLR SLO CLS; lia).
  assert (Q5 : L5.writable RSEGS MV' (V2 - 160) 160) by (eapply L5.writable_sub; [exact VW'| clear; lia| clear - CLS; lia]).
  assert (Q6 : L5.u64_at RSEGS MV' (F + 2040) fl) by (replace (F + 2040) with (F + 2048 - 8) by (clear; lia); exact VFLC').
  feed P ltac:(first [ asm | apply UR | apply U_to | (clear - Hn; lia) | (clear - Hd; lia) | (clear - V2R; lia) | (clear - FR; lia) | (clear - FLR; lia) | exact F32
                     | exact VFD' | exact VFW' | exact VFSW' | exact VFLW' | exact Q5 | exact Q6 | (unfold PEBCHP2.aligned; exact V2A) ]).
  destruct P as (fx5 & R5 & M5v & MG5 & dFR & dFZ & (dMS & dKS & dR1 & dR10 & dR11 & dR12 & dR22 & dR23 & DQ)).
  set (W5 := fun a => F / 8 + 2147450934 <= a < F / 8 + 2147450934 + 3).
  apply (apiece L ar C HI LYa HIok _ FF' LK' cr' Aw' M' model' fx' fx5 R' 0xa9528 R5 0x792dc M5v W5 K HH' AM' dMS MG5).
  { intros a Ha Hna. apply dFZ; [exact Ha|]. intros X; apply Hna; subst W5; cbn beta; clear - X; lia. }
  { intros a Ha Wa. subst W5; cbn beta in Wa. split.
    - apply (fframe_shadow_client L ar _ _ 0 0 F 5 (V2 - 160 + 32)). left; reflexivity. change (ff_bytes 5) with 2048.
      unfold in_shadow_of, HeapIfaceA.S. rewrite (proj1 (proj2 F8)). unfold HeapIfaceA.SB. clear - Wa. lia.
    - unfold HeapIfaceA.SB in *. clear - Wa FR. lia. }
  intros M5 model5 HH5 AM5 MRT5 HID5 VIS5 MGM5 FR5 VV5. change (mrestrict H' M5 = M5v) in VIS5.
  decompose [and] DQ. clear DQ.
  assert (BI5 : Bv W (PM.vs_own s' ++ PM.vs_own s) M5 model5 LK' cr' Aw').
  { apply (L5AFKR.binv_piece L ar HI M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W (PM.vs_own s' ++ PM.vs_own s) M' model' LK' cr' Aw' M5 model5 W5 BI' HH5 AM5 MRT5 MGM5 FR5).
    intros a Wa. subst W5; cbn beta in Wa. right; right. change (ff_bytes 5) with 2048. change (2048 / 8) with 256. unfold HeapIfaceA.SB in *. clear - Wa. lia. }
  assert (RI5 : rinvH R R5 (V2 - 160) F 2147450880) by (apply (rinvH_ks R R' R5 (V2 - 160) F 2147450880 PEBCHP2.KS_bhnD1 RI' dKS); unfold incl; apply L5K.incl_b; vm_compute; reflexivity).
  assert (LS5 : PESTA.ls_okA RSEGS AD AAD EE (PMST.ST true (PMST.st_sys g) (PMST.st_err g)) M5).
  { apply (PEBHK.ls_piece _ M' M5 W5 FR5); [| exact LS']. intros a Wa. subst W5; cbn beta in Wa. clear - Wa FR. lia. }
  assert (WPF : forall a, W5 a -> (F <= a < F + 2048) \/ (F / 8 + HeapIfaceA.SB <= a < F / 8 + HeapIfaceA.SB + 256) \/ (V2 - 160 <= a < V2)).
  { intros a Wa. subst W5; cbn beta in Wa. unfold HeapIfaceA.SB. clear - Wa. lia. }
  assert (FIN : In (F, 5, V2 - 160 + 32) (FF' ++ LK')) by (apply in_or_app; left; left; reflexivity).
  assert (FM8 : F mod 8 = 0) by (pose proof (proj1 F8) as E8; clear - E8; lia).
  assert (SLOW : ahl_ceil ar <= V2 - 160) by (clear - SLO CLS; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (FBD : 0 <= F / 8 /\ F / 8 + 256 <= 2 ^ 44) by (clear - FR; lia).
  assert (VS5 : PM.vstr_at RSEGS PMSPA.accA M5 (F + 32) s).
  { apply (PMFA.vstr_at_agreeA RSEGS M' M5 (F + 32) s); [clear - FR; lia| clear - FR; lia| | |exact VS'].
    - apply (PEBHK.agA_frame M' M5 W5 (F + 32) 24 FR5); [clear - FR; lia| clear - FR; lia|].
      intros x Hx. subst W5; cbn beta. unfold HeapIfaceA.S, HeapIfaceA.SB. split; intros X.
      + clear - Hx X FR FBIG F8. unfold BIGSHADOW_LO, BIGSHADOW_HI in *. lia.
      + clear - Hx X FR FBIG FM8. unfold BIGSHADOW_LO, BIGSHADOW_HI in *. lia.
    - intros c0 n0 p0 E0. apply (PEBHK.blk_agA L ar C SCFG HI HIok _ _ _ _ _ _ _ p0 c0 F (V2 - 160 + 32) (V2 - 160) V2 W5 M' M5 HH');
        [ rewrite E0; apply in_or_app; left; apply in_or_app; right; left; reflexivity | exact FIN | exact FM8 | clear - FR; lia | clear - FR; lia
        | unfold BIGSHADOW_LO, BIGSHADOW_HI; clear - FBIG; lia | exact SLOW | unfold BIGSHADOW_HI; clear - V2R; lia | exact FR5 | exact WPF ]. }
  assert (IS5 : PM.iss_at RSEGS AD PMSPA.accA M5 (F + 96) s' sm).
  { apply (PMFA.iss_at_agreeA RSEGS AD M' M5 (F + 96) s' sm); [clear - FR; lia| clear - FR; lia| | |exact ISA].
    - apply (PEBHK.agA_frame M' M5 W5 (F + 96) 272 FR5); [clear - FR; lia| clear - FR; lia|].
      intros x Hx. subst W5; cbn beta. unfold HeapIfaceA.S, HeapIfaceA.SB. split; intros X.
      + clear - Hx X FR FBIG F8. unfold BIGSHADOW_LO, BIGSHADOW_HI in *. lia.
      + clear - Hx X FR FBIG FM8. unfold BIGSHADOW_LO, BIGSHADOW_HI in *. lia.
    - intros c0 n0 p0 E0. apply (PEBHK.blk_agA L ar C SCFG HI HIok _ _ _ _ _ _ _ p0 c0 F (V2 - 160 + 32) (V2 - 160) V2 W5 M' M5 HH');
        [ rewrite E0; apply in_or_app; left; apply in_or_app; left; left; reflexivity | exact FIN | exact FM8 | clear - FR; lia | clear - FR; lia
        | unfold BIGSHADOW_LO, BIGSHADOW_HI; clear - FBIG; lia | exact SLOW | unfold BIGSHADOW_HI; clear - V2R; lia | exact FR5 | exact WPF ]. }

  assert (LENp : Z.of_nat (length p) = n) by (unfold PEBCH.p, PEBCH.n; rewrite length_map; reflexivity).
  assert (PAYB5 : L5.bytes_at RSEGS M5 (PM.vs_data (F + 176) s') p).
  { pose proof ISA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & VSA & _). replace (F + 96 + 80) with (F + 176) in VSA by (clear; lia).
    pose proof VSA as (_ & _ & VX). destruct s' as [n0|c0 n0 q0]; cbn [PM.vs_data] in PAYB' |- *; cbn in SZ', VX.
    - pose proof (proj1 VX) as SZB.
      apply (L5C.bytes_at_agree RSEGS M' M5 (F + 176 + 1) p); rewrite ?LENp; [| clear - FR; lia| clear - FR SZB SZ' SIZE0; lia| exact PAYB'].
      intros i Hi. apply FR5; [clear - Hi FR SZB SZ' SIZE0; lia|]. subst W5; cbn beta. intros X. clear - Hi X FR FBIG FBD SZB SZ' SIZE0. unfold BIGSHADOW_LO, BIGSHADOW_HI in *. lia.
    - pose proof VX as (_ & _ & _ & NC & CC & _).
      destruct (PEBHK.blk_facts L ar C SCFG HI HIok _ _ _ _ _ _ _ q0 c0 HH' ltac:(apply in_or_app; left; apply in_or_app; left; left; reflexivity)) as (P0 & P3 & P4 & P5 & PSH & P47 & PIMG & PFA).
      apply (L5C.bytes_at_agree RSEGS M' M5 q0 p); rewrite ?LENp; [| clear - P0; lia| clear - P47 NC SZ' SIZE0; lia| exact PAYB'].
      intros i Hi. apply FR5; [clear - Hi P0 P47 NC SZ' SIZE0; lia|]. subst W5; cbn beta. intros X.
      unfold BIGSHADOW_LO, BIGSHADOW_HI in PSH. clear - Hi X PSH FBD FR NC SZ' SIZE0. lia. }
  assert (HSTKa5 : L5.u64_at RSEGS M5 (V2 - 144) (F + 32)).
  { apply (L5C.u64_at_agree RSEGS M' M5 (V2 - 144) (F + 32)); [| clear - V2R; lia| clear - V2R; lia| exact HSTKa'].
    intros i Hi. apply FR5; [clear - Hi V2R; lia|]. subst W5; cbn beta. intros X. clear - Hi X V2R FBD. lia. }
  assert (HSTKb5 : L5.u64_at RSEGS M5 (V2 - 136) F).
  { apply (L5C.u64_at_agree RSEGS M' M5 (V2 - 136) F); [| clear - V2R; lia| clear - V2R; lia| exact HSTKb'].
    intros i Hi. apply FR5; [clear - Hi V2R; lia|]. subst W5; cbn beta. intros X. clear - Hi X V2R FBD. lia. }
  assert (Q432 : (F + 432) / 8 + HeapIfaceA.SB = F / 8 + 2147450934) by (unfold HeapIfaceA.SB; clear - FM8; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  assert (AVS : forall q k, F / 8 + 2147450880 <= q -> q + k <= F / 8 + 2147450880 + 256 -> L5A.avis H' q k)
    by (intros q k Hd1 Hd2; apply (PEBHK.avis_sub H' (F / 8 + HeapIfaceA.SB) 256 q k FSV'); unfold HeapIfaceA.SB; lia).
  apply (KONT fx5 R5 M5 model5 LK' cr' Aw' s' sm BI5 RI5 LS5).
  - exact dR1.
  - exact dR10.
  - exact dR11.
  - exact dR12.
  - rewrite (dKS 18%nat) by inl. exact Y18.
  - exact dR22.
  - exact dR23.
  - exact VS5.
  - split; [exact IS5| split; [rewrite SZ'; exact SIZE0| split; [exact SMG| split; [exact SMST| exact PAYB5]]]].
  - rewrite SIZE0 in CK'. exact CK'.
  - apply (PEBHK.shz_vis H' M5 M5v (F + 432) 3 (F / 8 + 2147450934) VV5 (AVS (F / 8 + 2147450934) 3 ltac:(lia) ltac:(lia)) Q432 ltac:(clear - FBD; lia) ltac:(clear - FBD; lia)).
    intros j Hj. assert (J : j = 0 \/ j = 1 \/ j = 2) by (clear - Hj; lia).
    repeat (destruct J as [J|J]; [subst j; gmem|]). subst j; gmem.
  - apply (PEBHK2.shz_frame M' M5 W5 (F + 96) 34 FR5); [| unfold HeapIfaceA.S, HeapIfaceA.SB; clear - FBD; lia| unfold HeapIfaceA.S, HeapIfaceA.SB; clear - FBD; lia| exact SZI'].
    intros j Hj X. subst W5; cbn beta in X. unfold HeapIfaceA.S, HeapIfaceA.SB in X.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    assert (E96 : (F + 96) / 8 = F / 8 + 12) by (clear - FM8; lia).
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    rewrite E96 in X. clear - X Hj FBD FR FBIG. lia.
  - exact HSTKa5.
  - exact HSTKb5.
Qed.
End Stage.
End SCFG_1.
End PEBCH3.
