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
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b L5StepAR_b L5CoreBR_b L5ADetailHR_b L5AFrameKR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HeapIfaceABx PmLayout PmLayoutA PnLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmModelFacts. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmModelFactsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStatics PmStaticsA PnStatics PnStaticsA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PnSpecsAa_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgSrc PgV8. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgSrcA_b PgV8A_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnModel PnRun. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnRunA_b PnRunAa_b PnStepA_b PnAReset1_b PnAHarnessStmts_b PnAHarnessKit_b PnAHarnessKit2_b PnAHarnessSK_b PnAHarnessKit3_b PnSpecsAX_b PnAHarnessP3_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module PNHA8c.
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
Hypothesis FAL : F mod 2048 = 0.
Local Notation Bv := (L5AFKR.binv L ar HI M model LB FF LK A (V2 + cls) 36864 (V2 - 128) (tfrk (V2 + cls) R) F 5).
Local Notation FF' := ((F, 5, V2 - 128 + 32) :: FF).

Ltac hsolve := first [ exact LY | exact HIok | eassumption | exact (or_introl eq_refl) | (split; reflexivity) | apply incl_refl
  | (apply PNHAK2.wapart_cons; [cbn [fst snd]; lia| first [apply PNHAK2.wapart_nil | (apply PNHAK2.wapart_cons; [cbn [fst snd]; lia| apply PNHAK2.wapart_nil])]])
  | (apply PNHAK2.wapart_nil) | lia ].

Lemma stage8c (V8D : PNSAX.vu8_dtor_spec RSEGS PMA.AD L ar HI 0xab9e0) (fx11 : FPState) (R11 : bvmap 5 word) (M11 : word -> option byte) (model11 : Model) (K : TSet)
      (LK11 : list fframe) (cr11 : credit) (A11 : list (Z * Z)) (s str : PM.vstr) (bb : PGV8.v8) (sm : PM.strm) (src : PM.srcst) (g : PNST.st) :
  Bv W ((PM.sr_qc src, PM.CHUNK) :: PGV8.v8_own bb ++ PM.vs_own str ++ PM.vs_own s) M11 model11 LK11 cr11 A11 -> rinvH R R11 V2 cls F -> K [] ->
  PNSTA.ls_okA RSEGS PMA.AD PMA.AAD PMA.AN g M11 ->
  getr R11 (reg 1) = Z_to_bv 64 0xa852c -> getr R11 (reg 10) = Z_to_bv 64 (V2 - 104) ->
  getr R11 (reg 21) = Z_to_bv 64 (F + 96) -> getr R11 (reg 22) = Z_to_bv 64 (F + 464) -> getr R11 (reg 23) = Z_to_bv 64 (F + 1024) ->
  getr R11 (reg 26) = Z_to_bv 64 18446744073709551608 ->
  PNHAK2.hbase F M11 s str sm -> PNHAK2.hsrc F M11 src -> PNHAK2.v8_at M11 (F + 784) bb -> L5.u64_at RSEGS M11 (V2 - 104) (F + 784) ->
  (forall (fx12 : FPState) (R12 : bvmap 5 word) (M12 : word -> option byte) (model12 : Model) (LK12 : list fframe) (A12 : list (Z * Z)),
      Bv W ((PM.sr_qc src, PM.CHUNK) :: PM.vs_own str ++ PM.vs_own s) M12 model12 LK12 cr11 A12 -> rinvH R R12 V2 cls F ->
      PNSTA.ls_okA RSEGS PMA.AD PMA.AAD PMA.AN g M12 ->
      getr R12 (reg 1) = Z_to_bv 64 0xa8534 -> getr R12 (reg 10) = Z_to_bv 64 (F + 480) -> getr R12 (reg 21) = Z_to_bv 64 (F + 96) ->
      getr R12 (reg 22) = Z_to_bv 64 (F + 464) -> getr R12 (reg 23) = Z_to_bv 64 (F + 1024) -> getr R12 (reg 26) = Z_to_bv 64 18446744073709551608 ->
      PNHAK2.hbase F M12 s str sm -> PNHAK2.hsrc F M12 src ->
      srealizes RSEGS SCFG (@L5A.cfg fx12 R12 0xab344 M12 model12) K) ->
  srealizes RSEGS SCFG (@L5A.cfg fx11 R11 0xab9e0 M11 model11) K.
Proof.
  intros BI RI K0 LS R1a R10 R21 R22 R23 R26 HB0 HS0 BB0 FT0 KONT.
  pose proof G as G'. destruct G' as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG F32 FLA FLR FLBIG NCF NCS].
  change (ff_bytes 5) with 2048 in *. change (2048 / 8) with 256 in *.
  pose proof BI as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10).
  pose proof RI as (X2 & X8 & X9 & X18 & X19 & X20 & X24 & X25 & X3 & X4 & X27).
  assert (FM8 : F mod 8 = 0) by (pose proof (proj1 F8) as E8; clear - E8; lia).
  assert (FHF : PNHAK2.hf F) by (unfold PNHAK2.hf, BIGSHADOW_LO, BIGSHADOW_HI; clear - FR FBIG FM8; lia).
  set (X := PGV8.v8_own bb ++ PM.vs_own str ++ PM.vs_own s) in *.
  set (Xr := PM.vs_own str ++ PM.vs_own s) in *.
  assert (INs : forall x, In x Xr -> In x X) by (intros x Hx; subst X; apply in_or_app; right; exact Hx).
  assert (INbb : forall x, In x (PGV8.v8_own bb) -> In x X) by (intros x Hx; subst X; apply in_or_app; left; exact Hx).
  assert (OSZ : shadow_zero M11 (V2 - 128) 16) by (eapply PNHASK.own_shz; first [exact BI | eassumption]).
  assert (FDEF : L5.defined M11 F 2048).
  { pose proof (L5AFKR.vis_facts L ar C HI LYa HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W _ M11 model11 LK11 cr11 A11 BI) as (_ & _ & (VFD & _) & (_ & _ & FV & _)).
    apply (proj1 (L5A.defined_vis (ahid A11 model11) M11 F 2048 FV)); exact VFD. }
  pose proof BB0 as (VD0 & VA0 & _).
  (* [comment removed for export] *)
  assert (ELB : PNRA.lb_remove_v8 bb (((PM.sr_qc src, PM.CHUNK) :: X) ++ LB) = ((PM.sr_qc src, PM.CHUNK) :: Xr) ++ LB).
  { destruct bb as [| b0 n0 c0]; [subst X Xr; reflexivity|]. cbn [PNRA.lb_remove_v8].
    pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ B1) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ND & _).
    assert (EL : ((PM.sr_qc src, PM.CHUNK) :: X) ++ LB = [(PM.sr_qc src, PM.CHUNK)] ++ (b0, c0) :: (Xr ++ LB)) by (subst X Xr; cbn [PGV8.v8_own app]; rewrite <- ?app_assoc; reflexivity).
    rewrite (PNHAK3.lb_remove_at b0 c0 _ _ _ EL); [reflexivity| exact ND]. }
  unfold PNSAX.vu8_dtor_spec in V8D.
  apply (V8D fx11 R11 M11 model11 K _ FF' LK11 A11 cr11 (V2 - 104) (F + 784) (V2 - 128) 0xa852c bb B1 B2 K0).
  { eapply PNHASK.callee_entry; first [exact BI | exact RI | exact R1a | eassumption | (split; [lia| reflexivity]) | lia]. }
  { eapply PNHASK.callee_roomB; first [exact BI | eassumption | lia]. }
  { eapply PNHASK.callee_rs; eassumption. }
  { rewrite L5K.rl10. exact R10. }
  { lia. }
  { clear - SHI CLS SPT. lia. }
  { Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). clear - V2A. lia. }
  { Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    apply (PMARS1.acc_of_shadow_zero M11 (V2 - 128) 16 (V2 - 104) 8 OSZ); [| lia| lia].
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). clear - V2A. lia. }
  { Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). exact FT0. }
  { exists (F, 5, V2 - 128 + 32). split; [left; reflexivity|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 5) with 2048. lia. }
  { clear - FM8. lia. }
  { exact VD0. }
  { exact VA0. }
  { exact BB0. }
  { intros x Hx. right. apply in_or_app. left. apply INbb. exact Hx. }
  intros fx' R' M' model' LK' Aw' RP' HP' MRT' INCLK' INCA' AM' HH'.
  change (PMSPA.pm_scr 1) with 14336 in HP'.
  rewrite ELB in HP', HH'.
  assert (WFI : PNHAK2.wfi F [(F + 784, 24)]) by (apply PNHAK2.wfi_cons; [cbn [fst snd]; left; lia| apply PNHAK2.wfi_nil]).
  assert (LS' : PNSTA.ls_okA RSEGS PMA.AD PMA.AAD PMA.AN g M').
  { apply (PNHAK.ls_ahpres L C LY g ar _ FF' (V2 - 128) 14336 [(F + 784, 24)] M11 M' HP'); [| exact LS].
    apply PNHAK.far_cons; [cbn [fst snd]; clear - FR; lia| apply PNHAK.far_nil]. }
  assert (BI' : Bv W ((PM.sr_qc src, PM.CHUNK) :: Xr) M' model' LK' cr11 Aw').
  { apply (L5AFKR.binv_callee L ar C HI HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W W _ ((PM.sr_qc src, PM.CHUNK) :: Xr) _ M11 model11 LK11 cr11 A11 M' model' LK' cr11 Aw' 14336 [(F + 784, 24)] BI HP' HH' AM' MRT' INCA' INCLK').
    - lia.
    - clear - CLS; lia.
    - intros rr a [<-|[]] Ha. unfold L5.in_rng in Ha; cbn [fst snd] in Ha. unfold tocell. split; [clear - Ha FCEIL SLO CLS; lia|]. unfold HeapIfaceA.SB. change (ff_bytes 5) with 2048. clear - Ha FR F8 FBIG. lia.
    - intros a Hc _ rr [<-|[]] Ha. unfold L5.in_rng in Ha; cbn [fst snd] in Ha. apply (NCF a); [left; clear - Ha; lia| exact Hc].
    - intros a X0. exact X0. }
  pose proof (L5AFKR.vis_facts L ar C HI LYa HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W _ M' model' LK' cr11 Aw' BI')
    as ((VW' & VIC' & VSB' & VUAR' & VMS') & VOWN' & (VFD' & VFW' & VFSW' & VFLC' & VFLW') & (FLCc' & FLV' & FV' & SPV' & FSV')).
  change (ff_bytes 5) with 2048 in *. change (2048 / 8) with 256 in *.
  set (H' := ahid Aw' model') in *. set (MV' := mrestrict H' M') in *.
  assert (RI' : rinvH R R' V2 cls F) by exact (rinvH_pres R R11 R' V2 cls F RI RP').
  pose proof RI' as (Y2 & Y8 & Y9 & Y18 & Y19 & Y20 & Y24 & Y25 & Y3 & Y4 & Y27).
  assert (Y21 : getr R' (reg 21) = Z_to_bv 64 (F + 96)) by (rewrite (cs_of_preserved R11 R' 21 RP') by inl; exact R21).
  assert (Y22 : getr R' (reg 22) = Z_to_bv 64 (F + 464)) by (rewrite (cs_of_preserved R11 R' 22 RP') by inl; exact R22).
  assert (Y23 : getr R' (reg 23) = Z_to_bv 64 (F + 1024)) by (rewrite (cs_of_preserved R11 R' 23 RP') by inl; exact R23).
  assert (Y26 : getr R' (reg 26) = Z_to_bv 64 18446744073709551608) by (rewrite (cs_of_preserved R11 R' 26 RP') by inl; exact R26).
  assert (FIN11 : In (F, 5, V2 - 128 + 32) (FF' ++ LK11)) by (apply in_or_app; left; left; reflexivity).
  assert (INX : forall x, In x Xr -> In x (((PM.sr_qc src, PM.CHUNK) :: X) ++ LB) /\ In x (((PM.sr_qc src, PM.CHUNK) :: Xr) ++ LB)).
  { intros x Hx. split; [right; apply in_or_app; left; apply INs; exact Hx| right; apply in_or_app; left; exact Hx]. }
  assert (HB' : PNHAK2.hbase F M' s str sm).
  { eapply PNHAK2.hbase_callee; first [ exact LY | exact HIok | exact B1 | exact HP' | exact HB0 | exact FHF | exact FIN11 | exact WFI | exact (or_introl eq_refl)
      | (split; reflexivity) | (intros x Hx; apply INX; exact Hx)
      | (apply PNHAK2.wapart_cons; [cbn [fst snd]; lia| apply PNHAK2.wapart_nil]) | lia ]. }
  assert (HS' : PNHAK2.hsrc F M' src).
  { eapply PNHAK2.hsrc_callee; first [ exact LY | exact HIok | exact B1 | exact HP' | exact HS0 | exact FHF | exact FIN11 | exact WFI | exact (or_introl eq_refl)
      | (split; reflexivity) | (left; reflexivity) | (apply PNHAK2.wapart_cons; [cbn [fst snd]; lia| apply PNHAK2.wapart_nil]) | lia ]. }
  assert (SLOW : ahl_ceil ar <= V2 - 128) by (clear - SLO CLS; lia).
  assert (SHW : BIGSHADOW_HI <= V2 - 128) by (unfold BIGSHADOW_HI; clear - V2R; lia).
  assert (Q1 : 4096 <= F <= 140737488353280) by (clear - FR; lia).
  assert (Q2 : 4096 <= fl <= 140737488355327) by (clear - FLR; lia).
  assert (Q3 : V2 - 128 + 144 <= F \/ F + 2048 <= V2 - 128) by (clear - FCEIL SLO CLS; lia).
  assert (Q4 : V2 - 128 + 144 <= fl \/ fl + 1 <= V2 - 128) by (clear - FLR SLO CLS; lia).
  assert (Q5 : L5.writable RSEGS MV' (V2 - 128) 128) by (eapply L5.writable_sub; [exact VW'| clear; lia| clear - CLS; lia]).
  assert (Q6 : L5.u64_at RSEGS MV' (F + 2040) fl) by (replace (F + 2040) with (F + 2048 - 8) by (clear; lia); exact VFLC').
  LeanFeed.pfeed P (PNAHP3.bhaJ2_conc fx' R' MV' (fun j => match j with 2%nat => V2 | 40%nat => F | 41%nat => fl | 58%nat => U R' 1 | _ => 0 end)) ltac:(first [ asm | apply UR | apply U_to | (clear - V2R; lia) | (clear - FR; lia) | (clear - FLR; lia) | exact F32
                     | exact VFD' | exact VFW' | exact VFSW' | exact VFLW' | exact Q5 | exact Q6 | (unfold PNAHP3.aligned; exact V2A) ]).
  destruct P as (fx12 & R12 & M12v & MG12 & jFR & jFZ & (jMS & jKS & jR1 & jR10)).
  apply (apiece L ar C HI LYa HIok _ FF' LK' cr11 Aw' M' model' fx' fx12 R' 0xa852c R12 0xab344 M12v (fun _ => False) K HH' AM' jMS MG12).
  { intros a Ha Hna. apply jFZ; exact Ha. }
  { intros a Ha []. }
  intros M12 model12 HH12 AM12 MRT12 HID12 VIS12 MGM12 FR12 VV12.
  assert (FIN' : In (F, 5, V2 - 128 + 32) (FF' ++ LK')) by (apply in_or_app; left; left; reflexivity).
  assert (PF0 : PNHAK2.pfoot F (V2 - 128) V2 (fun _ => False)) by (intros a []).
  assert (OAX : forall o n, PNHAK2.oav (fun _ => False) o n) by (intros o n x Hx; split; intros []).
  apply (KONT fx12 R12 M12 model12 LK' Aw').
  - apply (L5AFKR.binv_piece L ar HI M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W _ M' model' LK' cr11 Aw' M12 model12 (fun _ => False) BI' HH12 AM12 MRT12 MGM12 FR12).
    intros a [].
  - apply (rinvH_ks R R' R12 V2 cls F PNAHP3.KS_bhaJ2 RI' jKS); vm_compute; reflexivity.
  - apply (PNHAK.ls_piece _ M' M12 (fun _ => False) FR12); [intros a []| exact LS'].
  - exact jR1.
  - exact jR10.
  - rewrite (jKS 21%nat) by inl. exact Y21.
  - rewrite (jKS 22%nat) by inl. exact Y22.
  - rewrite (jKS 23%nat) by inl. exact Y23.
  - rewrite (jKS 26%nat) by inl. exact Y26.
  - apply (PNHAK2.hbase_piece L ar C SCFG HI HIok _ _ _ _ _ _ _ F (V2 - 128 + 32) HH' FIN' FHF (V2 - 128) V2 (fun _ => False) M' M12 SLOW SHW FR12 PF0 s str sm);
      [intros x Hx; right; apply in_or_app; left; exact Hx| apply OAX| apply OAX| apply OAX| exact HB'].
  - apply (PNHAK2.hsrc_piece L ar C SCFG HI HIok _ _ _ _ _ _ _ F (V2 - 128 + 32) HH' FIN' FHF (V2 - 128) V2 (fun _ => False) M' M12 SLOW SHW FR12 PF0 src);
      [left; reflexivity| apply OAX| exact HS'].
Qed.
End Stage.
End SCFG_1.
End PNHA8c.
