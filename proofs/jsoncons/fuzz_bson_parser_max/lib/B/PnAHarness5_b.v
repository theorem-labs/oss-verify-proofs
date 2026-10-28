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

Module PNHA5.
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
Hypothesis WSYS : forall a, L5.outside W a -> L5.outside [(0x672530, 2)] a.
Local Notation Bv := (L5AFKR.binv L ar HI M model LB FF LK A (V2 + cls) 36864 (V2 - 128) (tfrk (V2 + cls) R) F 5).
Local Notation FF' := ((F, 5, V2 - 128 + 32) :: FF).

Ltac hsolve := first [ exact LY | exact HIok | eassumption | exact (or_introl eq_refl) | (split; reflexivity) | apply incl_refl
  | (apply PNHAK2.wapart_cons; [cbn [fst snd]; lia| first [apply PNHAK2.wapart_nil | (apply PNHAK2.wapart_cons; [cbn [fst snd]; lia| apply PNHAK2.wapart_nil])]])
  | (apply PNHAK2.wapart_nil) | lia ].

Lemma stage5 (SYS : PMA.syscat_spec L ar HI) (fx6 : FPState) (R6 : bvmap 5 word) (M6 : word -> option byte) (model6 : Model) (K : TSet)
      (LK6 : list fframe) (cr6 : credit) (A6 : list (Z * Z)) (s s' : PM.vstr) (sm : PM.strm) (ps : PNM.bpst) (g : PNST.st) :
  Bv W (PNM.bparser_own ps ++ PM.vs_own s' ++ PM.vs_own s) M6 model6 LK6 cr6 A6 -> rinvH R R6 V2 cls F -> K [] -> PNSTA.ls_okA RSEGS PMA.AD PMA.AAD PMA.AN g M6 ->
  getr R6 (reg 1) = Z_to_bv 64 0xa84b0 -> getr R6 (reg 21) = Z_to_bv 64 (F + 96) -> getr R6 (reg 22) = Z_to_bv 64 (F + 464) ->
  getr R6 (reg 23) = Z_to_bv 64 (F + 1024) -> getr R6 (reg 26) = Z_to_bv 64 18446744073709551608 ->
  PNHAK2.hbase F M6 s s' sm -> PNHAK2.hpar F M6 ps -> L5.u32_at RSEGS M6 (F + 1024) 0 -> shadow_zero M6 (F + 1024) 2 ->
  (forall (fx7 : FPState) (R7 : bvmap 5 word) (M7 : word -> option byte) (model7 : Model) (LK7 : list fframe) (A7 : list (Z * Z)),
      Bv W (PNM.bparser_own ps ++ PM.vs_own s' ++ PM.vs_own s) M7 model7 LK7 cr6 A7 ->
      (getr R7 (reg 2) = Z_to_bv 64 (V2 - 160) /\ getr R7 (reg 8) = Z_to_bv 64 (F + 1024) /\ getr R7 (reg 9) = Z_to_bv 64 (F + 464) /\
       getr R7 (reg 18) = Z_to_bv 64 0x7fff8000 /\ getr R7 (reg 19) = Z_to_bv 64 (F / 8 + 2147450880) /\ getr R7 (reg 20) = Z_to_bv 64 (F + 32) /\
       getr R7 (reg 24) = Z_to_bv 64 F /\ getr R7 (reg 25) = Z_to_bv 64 2147450880 /\
       getr R7 (reg 3) = getr R (reg 3) /\ getr R7 (reg 4) = getr R (reg 4) /\ getr R7 (reg 27) = getr R (reg 27) /\
       L5.u64_at RSEGS M7 (V2 - 160) F /\ L5.u64_at RSEGS M7 (V2 - 152) (V2 - 128) /\ L5.u64_at RSEGS M7 (V2 - 144) (V2 + cls) /\
       L5.u64_at RSEGS M7 (V2 - 136) 0xa84c0) ->
      PNSTA.ls_okA RSEGS PMA.AD PMA.AAD PMA.AN (PNST.ST (PNST.st_loc g) true (PNST.st_ax g)) M7 ->
      getr R7 (reg 1) = Z_to_bv 64 0xa8e44 -> getr R7 (reg 10) = Z_to_bv 64 (F + 464) -> getr R7 (reg 21) = Z_to_bv 64 (F + 96) ->
      getr R7 (reg 22) = Z_to_bv 64 (F + 464) -> getr R7 (reg 23) = Z_to_bv 64 (F + 1024) -> getr R7 (reg 26) = Z_to_bv 64 18446744073709551608 ->
      PNHAK2.hbase F M7 s s' sm -> PNHAK2.hpar F M7 ps -> PNHAK2.hec F M7 0 (pa_syscat_obj PMA.AD) ->
      srealizes RSEGS SCFG (@L5A.cfg fx7 R7 0xadb68 M7 model7) K) ->
  srealizes RSEGS SCFG (@L5A.cfg fx6 R6 0xd950c M6 model6) K.
Proof.
  intros BI RI K0 LS R1a R21 R22 R23 R26 HB0 HP0 EC0 SZE0 KONT.
  pose proof G as G'. destruct G' as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG F32 FLA FLR FLBIG NCF NCS].
  change (ff_bytes 5) with 2048 in *. change (2048 / 8) with 256 in *.
  pose proof BI as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10).
  pose proof RI as (X2 & X8 & X9 & X18 & X19 & X20 & X24 & X25 & X3 & X4 & X27).
  assert (FM8 : F mod 8 = 0) by (pose proof (proj1 F8) as E8; clear - E8; lia).
  assert (FHF : PNHAK2.hf F) by (unfold PNHAK2.hf, BIGSHADOW_LO, BIGSHADOW_HI; clear - FR FBIG FM8; lia).
  pose proof LS as (LSB & LSL & LSS & LSE).
  unfold PMA.syscat_spec, PMSPA.syscat_spec in SYS. cbn [pa_syscat pa_syscat_guard pa_syscat_obj PMA.AD ADDR_A] in SYS.
  apply (SYS fx6 R6 M6 model6 K ((PNM.bparser_own ps ++ PM.vs_own s' ++ PM.vs_own s) ++ LB) FF' LK6 A6 cr6 (V2 - 128) 0xa84b0 (PNST.st_sys g) B1 B2 K0).
  { eapply PNHASK.callee_entry; first [exact BI | exact RI | exact R1a | eassumption | (split; [lia| reflexivity]) | lia]. }
  { eapply PNHASK.callee_room; first [exact BI | eassumption | lia]. }
  { eapply PNHASK.callee_rs; eassumption. }
  { exact LSB. }
  { exact LSS. }
  intros fx' R' M' model' LK' Aw' RP' RV' SYS' HP' MRT' INCLK' INCA' AM' HH'.
  change (PMSPA.pm_scr 1) with 14336 in HP'.
  set (Wc := if PNST.st_sys g then [] else [(6759728, 2)]) in *.
  assert (WcL : forall r, In r Wc -> r = (6759728, 2)) by (intros r Hr; subst Wc; destruct (PNST.st_sys g); [destruct Hr| destruct Hr as [<-|[]]; reflexivity]).
  assert (WFI : PNHAK2.wfi F Wc) by (intros r Hr; rewrite (WcL r Hr); right; cbn [fst snd]; lia).
  assert (WA : forall o n, F <= o -> PNHAK2.wapart Wc o n) by (intros o n Ho r Hr; rewrite (WcL r Hr); cbn [fst snd]; clear - Ho FR; lia).
  assert (LS' : PNSTA.ls_okA RSEGS PMA.AD PMA.AAD PMA.AN (PNST.ST (PNST.st_loc g) true (PNST.st_ax g)) M').
  { apply (PNHAK.ls_ahpres_sys L C LY g ar _ FF' (V2 - 128) 14336 Wc M6 M' HP'); [| exact LS| exact SYS'].
    intros a Ha r Hr Hin. rewrite (WcL r Hr) in Hin. unfold L5.in_rng in Hin; cbn [fst snd] in Hin.
    unfold PNHAK.bcell, PNHAK.lcell, PNHAK.ecell in Ha. clear - Ha Hin. lia. }
  assert (BI' : Bv W (PNM.bparser_own ps ++ PM.vs_own s' ++ PM.vs_own s) M' model' LK' cr6 Aw').
  { apply (L5AFKR.binv_callee L ar C HI HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W W _ _ _ M6 model6 LK6 cr6 A6 M' model' LK' cr6 Aw' 14336 Wc BI HP' HH' AM' MRT' INCA' INCLK').
    - lia.
    - clear - CLS; lia.
    - intros rr a Hr Ha. rewrite (WcL rr Hr) in Ha. unfold L5.in_rng in Ha; cbn [fst snd] in Ha. unfold tocell. split; [clear - Ha SLO SPT; lia|].
      unfold HeapIfaceA.SB. change (ff_bytes 5) with 2048. clear - Ha FR F8. lia.
    - intros a Hc Ho rr Hr Ha. pose proof (WcL rr Hr) as E. subst rr. exact (WSYS a Ho _ (or_introl eq_refl) Ha).
    - intros a X. exact X. }
  pose proof (L5AFKR.vis_facts L ar C HI LYa HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W _ M' model' LK' cr6 Aw' BI')
    as ((VW' & VIC' & VSB' & VUAR' & VMS') & VOWN' & (VFD' & VFW' & VFSW' & VFLC' & VFLW') & (FLCc' & FLV' & FV' & SPV' & FSV')).
  change (ff_bytes 5) with 2048 in *. change (2048 / 8) with 256 in *.
  set (H' := ahid Aw' model') in *. set (MV' := mrestrict H' M') in *.
  assert (RI' : rinvH R R' V2 cls F) by exact (rinvH_pres R R6 R' V2 cls F RI RP').
  pose proof RI' as (Y2 & Y8 & Y9 & Y18 & Y19 & Y20 & Y24 & Y25 & Y3 & Y4 & Y27).
  assert (Y21 : getr R' (reg 21) = Z_to_bv 64 (F + 96)) by (rewrite (cs_of_preserved R6 R' 21 RP') by inl; exact R21).
  assert (Y22 : getr R' (reg 22) = Z_to_bv 64 (F + 464)) by (rewrite (cs_of_preserved R6 R' 22 RP') by inl; exact R22).
  assert (Y23 : getr R' (reg 23) = Z_to_bv 64 (F + 1024)) by (rewrite (cs_of_preserved R6 R' 23 RP') by inl; exact R23).
  assert (Y26 : getr R' (reg 26) = Z_to_bv 64 18446744073709551608) by (rewrite (cs_of_preserved R6 R' 26 RP') by inl; exact R26).
  assert (FIN6 : In (F, 5, V2 - 128 + 32) (FF' ++ LK6)) by (apply in_or_app; left; left; reflexivity).
  (* [comment removed for export] *)
  assert (HB' : PNHAK2.hbase F M' s s' sm).
  { eapply PNHAK2.hbase_callee; first [ exact B1 | exact HP0 | exact HB0 | exact FHF | exact FIN6 | exact WFI | apply WA; lia
      | (intros x Hx; apply in_or_app; left; apply in_or_app; right; exact Hx) | hsolve ]. }
  assert (HQ' : PNHAK2.hpar F M' ps).
  { eapply PNHAK2.hpar_callee; first [ exact B1 | exact HP0 | exact FHF | exact FIN6 | exact WFI | apply WA; lia
      | (intros x Hx; apply in_or_app; left; apply in_or_app; left; exact Hx) | hsolve ]. }
  assert (AGE : PMFA.agA M6 M' (F + 1024) 16).
  { apply (PNHAK2.ff_callee L ar _ FF' (V2 - 128) 14336 Wc M6 M' (F, 5, V2 - 128 + 32) F (F + 1024) 16 HP' (or_introl eq_refl));
      cbn [ff_addr ff_class fst snd]; change (ff_bytes 5) with 2048; [lia| lia| exact FHF| lia| lia| exact WFI| apply WA; lia]. }
  assert (EC' : L5.u32_at RSEGS M' (F + 1024) 0) by (apply (PNHAK2.u32_agA M6 M' (F + 1024) 16 (F + 1024) _ AGE); [lia| lia| lia| lia| exact EC0]).
  assert (SZE' : shadow_zero M' (F + 1024) 2) by (apply (PNHAK2.shz_agA M6 M' (F + 1024) 16 (F + 1024) 2 AGE); [lia| lia| clear - FM8; lia| lia| exact SZE0]).
  assert (Q1 : 4096 <= F <= 140737488353280) by (clear - FR; lia).
  assert (Q2 : 4096 <= fl <= 140737488355327) by (clear - FLR; lia).
  pose proof BI' as (BH1 & _ & _ & _ & _ & BASTK & _).
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ FF' LK' cr6 Aw' M' model' BH1) as (_ & VISS & _).
  assert (Q3 : V2 - 160 + 176 <= F \/ F + 2048 <= V2 - 160) by (clear - FCEIL SLO CLS; lia).
  assert (Q4 : V2 - 160 + 176 <= fl \/ fl + 1 <= V2 - 160) by (clear - FLR SLO CLS; lia).
  assert (Q5 : L5.writable RSEGS MV' (V2 - 160) 160).
  { apply (proj2 (L5A.writable_vis H' M' (V2 - 160) 160 (VISS (V2 - 160) 160 ltac:(clear - SLO CLS; lia) ltac:(clear - SPC CLS; lia)) ltac:(clear - V2R; lia) ltac:(clear - SPC CLS; lia))).
    apply (L5SAR.astk_writable ar M' _ _ (V2 - 160) 160 BASTK); clear - SPC CLS; lia. }
  assert (QG1 : L5.u64_at RSEGS MV' 0x1374c0 0x13fc38).
  { unfold L5.u64_at. rewrite (L5C.rdn_agree RSEGS (fun _ => None) MV' 8 0x1374c0 ltac:(lia) ltac:(lia)).
    - vm_compute. f_equal. repeat (apply f_equal2; [apply bv_eq; reflexivity|]). reflexivity.
    - intros i Hi. first [apply VIC'; lia | symmetry; apply VIC'; lia]. }
  assert (QG2 : L5.u64_at RSEGS MV' 0x13fc38 0x7fff8000) by exact VSB'.
  assert (Q9 : 0x7fff7000 + 0x100000001000 <= F \/ F + 2048 <= 0x7fff7000) by (clear - FBIG; lia).
  assert (Q6 : L5.u64_at RSEGS MV' (F + 2040) fl) by (replace (F + 2040) with (F + 2048 - 8) by (clear; lia); exact VFLC').
  LeanFeed.pfeed P (PNAHP2.bhaF_conc fx' R' MV' (fun j => match j with 2%nat => V2 | 40%nat => F | 41%nat => fl | 58%nat => U R' 1 | _ => 0 end)) ltac:(first [ asm | apply UR | apply U_to | (clear - V2R; lia) | (clear - FR; lia) | (clear - FLR; lia) | exact F32
                     | exact VFD' | exact VFW' | exact VFSW' | exact VFLW' | exact Q5 | exact Q6 | (unfold PNAHP2.aligned; exact V2A) ]).
  destruct P as (fx7 & R7 & M7v & MG7 & fFR & fFZ & (fMS & fKS & fR1 & fR2 & fR8 & fR9 & fR10 & fR11 & fR18 & fC & fD1 & fD2 & fS160 & fS152 & fS144 & fS136)).
  set (W7 := fun a => F + 1032 <= a < F + 1032 + 8 \/ V2 - 160 <= a < V2 - 160 + 32).
  apply (apiece L ar C HI LYa HIok _ FF' LK' cr6 Aw' M' model' fx' fx7 R' 0xa84b0 R7 0xadb68 M7v W7 K HH' AM' fMS MG7).
  { intros a Ha Hna. apply fFZ; [exact Ha|..]; intros X; apply Hna; subst W7; cbn beta; clear - X; lia. }
  { intros a Ha Wa. subst W7; cbn beta in Wa. destruct Wa as [Wa|Wa]; split.
    - apply (fframe_client L ar _ _ 0 0 F 5 (V2 - 128 + 32)). left; reflexivity. change (ff_bytes 5) with 2048. clear - Wa; lia.
    - clear - Wa FR. lia.
    - unfold aclientw, aclient_g. right; left. clear - Wa SLO SPC CLS. lia.
    - clear - Wa V2R SLO SPC CLS. lia. }
  intros M7 model7 HH7 AM7 MRT7 HID7 VIS7 MGM7 FR7 VV7. change (mrestrict H' M7 = M7v) in VIS7.
  assert (BI7 : Bv W (PNM.bparser_own ps ++ PM.vs_own s' ++ PM.vs_own s) M7 model7 LK' cr6 Aw').
  { apply (L5AFKR.binv_mem L ar C HI HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W _ M' model' LK' cr6 Aw' M7 model7 (fun a => F + 1032 <= a < F + 1032 + 8) 32 BI' HH7 AM7 MRT7).
    - intros a Ha CA ND. apply FR7; [exact Ha|]. subst W7; cbn beta. intros [X|X]; [exact (ND X)|].
      destruct (aclient_cases L ar C HI LYa HIok _ FF' LK' cr6 Aw' M7 _ (V2 - 128) 32 a HH7 SPT CA) as [(_ & Z2)|Z2]; [apply Z2; clear - X; lia| clear - X Z2 SLO CLS; lia].
    - intros a Ha. apply MGM7. pose proof (L5SAR.astk_defined ar M' _ _ a 1 BASTK ltac:(clear - Ha SPC CLS; lia) ltac:(clear - Ha CLS; lia)) as DD. specialize (DD 0 ltac:(lia)). rewrite Z.add_0_r in DD. exact DD.
    - intros a Da. apply MGM7. pose proof (proj1 (L5A.defined_vis H' M' F 2048 FV') VFD') as DF. cbn beta in Da. pose proof (DF (a - F) ltac:(clear - Da; lia)) as DFa. replace (F + (a - F)) with a in DFa by (clear; lia). exact DFa.
    - intros a. cbn beta. lia.
    - intros a Da. cbn beta in Da. first [change (ff_bytes 5) with 2048 | idtac]. clear - Da. lia.
    - clear - SPC CLS. lia.
    - lia. }
  assert (LS7 : PNSTA.ls_okA RSEGS PMA.AD PMA.AAD PMA.AN (PNST.ST (PNST.st_loc g) true (PNST.st_ax g)) M7).
  { apply (PNHAK.ls_piece _ M' M7 W7 FR7); [| exact LS']. intros a Wa. subst W7; cbn beta in Wa. clear - Wa FR FCEIL SLO CLS V2R. lia. }
  assert (PF7 : PNHAK2.pfoot F (V2 - 160) V2 W7) by (intros a Wa; subst W7; cbn beta in Wa; clear - Wa; lia).
  assert (FIN' : In (F, 5, V2 - 128 + 32) (FF' ++ LK')) by (apply in_or_app; left; left; reflexivity).
  assert (SLOW : ahl_ceil ar <= V2 - 160) by (clear - SLO CLS; lia).
  assert (SHW : BIGSHADOW_HI <= V2 - 160) by (unfold BIGSHADOW_HI; clear - V2R; lia).
  assert (OAX : forall o n, F <= o -> o + n <= F + 1032 -> PNHAK2.oav W7 o n).
  { intros o n H1 H2 x Hx. subst W7; cbn beta. pose proof (PMKA.S_in_shadow x ltac:(clear - Hx H1 H2 FR; lia)) as SX.
    unfold BIGSHADOW_LO, BIGSHADOW_HI in *. split; intros X; clear - Hx X H1 H2 SX FBIG FR FCEIL SLO CLS V2R; lia. }
  assert (HB7 : PNHAK2.hbase F M7 s s' sm).
  { apply (PNHAK2.hbase_piece L ar C SCFG HI HIok _ _ _ _ _ _ _ F (V2 - 128 + 32) HH' FIN' FHF (V2 - 160) V2 W7 M' M7 SLOW SHW FR7 PF7 s s' sm);
      [intros x Hx; apply in_or_app; left; apply in_or_app; right; exact Hx| apply OAX; lia| apply OAX; lia| apply OAX; lia| exact HB']. }
  assert (HQ7 : PNHAK2.hpar F M7 ps).
  { apply (PNHAK2.hpar_piece L ar C SCFG HI HIok _ _ _ _ _ _ _ F (V2 - 128 + 32) HH' FIN' FHF (V2 - 160) V2 W7 M' M7 SLOW SHW FR7 PF7 ps);
      [intros x Hx; apply in_or_app; left; apply in_or_app; left; exact Hx| apply OAX; lia| exact HQ']. }
  assert (U10 : bv_unsigned (getr R' (reg 10)) = 1293360) by (rewrite <- L5K.rl10, RV'; apply L5.unsigned_lit; lia).
  rewrite U10 in fC.
  assert (HE7 : PNHAK2.hec F M7 0 (pa_syscat_obj PMA.AD)).
  { cbn [pa_syscat_obj PMA.AD ADDR_A]. split; [|split; [|split]].
    - apply (PNHAK.u32_agree M' M7 (F + 1024) 0); [intros i Hi; apply FR7; [clear - Hi FR; lia| subst W7; cbn beta; clear - Hi FR FCEIL SLO CLS; lia]| clear - FR; lia| clear - FR; lia| exact EC'].
    - apply (PNHAK.u64_vis H' M7 M7v (F + 1032) _ VV7 (PNHAK.avis_sub H' F 2048 (F + 1032) 8 FV' ltac:(lia) ltac:(lia)) ltac:(clear - FR; lia) ltac:(clear - FR; lia)). exact fC.
    - apply (PNHAK2.shz_frame M' M7 W7 (F + 1024) 2 FR7); [| unfold HeapIfaceA.S, HeapIfaceA.SB; clear - FR; lia| unfold HeapIfaceA.S, HeapIfaceA.SB; clear - FR; lia| exact SZE'].
      intros j Hj X. subst W7; cbn beta in X. pose proof (PMKA.S_in_shadow (F + 1024) ltac:(clear - FR; lia)) as SX.
      unfold BIGSHADOW_LO, BIGSHADOW_HI in *. clear - Hj X SX FBIG FR V2R CLS. lia.
    - pose proof (L5AFKR.vis_facts L ar C HI LYa HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W _ M7 model7 LK' cr6 Aw' BI7) as (_ & _ & (VFD7 & _) & (_ & _ & FV7 & _)).
      change (ff_bytes 5) with 2048 in VFD7, FV7.
      apply (L5.defined_sub M7 F 2048 (F + 1024) 16); [| lia| lia]. apply (proj1 (L5A.defined_vis (ahid Aw' model7) M7 F 2048 FV7)). exact VFD7. }
  assert (RB7 : getr R7 (reg 2) = Z_to_bv 64 (V2 - 160) /\ getr R7 (reg 8) = Z_to_bv 64 (F + 1024) /\ getr R7 (reg 9) = Z_to_bv 64 (F + 464) /\
       getr R7 (reg 18) = Z_to_bv 64 0x7fff8000 /\ getr R7 (reg 19) = Z_to_bv 64 (F / 8 + 2147450880) /\ getr R7 (reg 20) = Z_to_bv 64 (F + 32) /\
       getr R7 (reg 24) = Z_to_bv 64 F /\ getr R7 (reg 25) = Z_to_bv 64 2147450880 /\
       getr R7 (reg 3) = getr R (reg 3) /\ getr R7 (reg 4) = getr R (reg 4) /\ getr R7 (reg 27) = getr R (reg 27) /\
       L5.u64_at RSEGS M7 (V2 - 160) F /\ L5.u64_at RSEGS M7 (V2 - 152) (V2 - 128) /\ L5.u64_at RSEGS M7 (V2 - 144) (V2 + cls) /\
       L5.u64_at RSEGS M7 (V2 - 136) 0xa84c0).
  { rewrite Y8 in fS144. rewrite L5.unsigned_lit in fS144 by (clear - SPC CLS; lia).
    split; [exact fR2|]. split; [exact fR8|]. split; [exact fR9|]. split; [exact fR18|].
    split; [rewrite (fKS 19%nat) by inl; exact Y19|]. split; [rewrite (fKS 20%nat) by inl; exact Y20|].
    split; [rewrite (fKS 24%nat) by inl; exact Y24|]. split; [rewrite (fKS 25%nat) by inl; exact Y25|].
    split; [rewrite (fKS 3%nat) by inl; exact Y3|]. split; [rewrite (fKS 4%nat) by inl; exact Y4|]. split; [rewrite (fKS 27%nat) by inl; exact Y27|].
    split; [apply (PNHAK.u64_vis H' M7 M7v (V2 - 160) _ VV7 (VISS (V2 - 160) 8 ltac:(clear - SLO CLS; lia) ltac:(clear - SPC CLS; lia)) ltac:(clear - V2R; lia) ltac:(clear - SPC CLS; lia)); exact fS160|].
    split; [apply (PNHAK.u64_vis H' M7 M7v (V2 - 152) _ VV7 (VISS (V2 - 152) 8 ltac:(clear - SLO CLS; lia) ltac:(clear - SPC CLS; lia)) ltac:(clear - V2R; lia) ltac:(clear - SPC CLS; lia)); exact fS152|].
    split; [apply (PNHAK.u64_vis H' M7 M7v (V2 - 144) _ VV7 (VISS (V2 - 144) 8 ltac:(clear - SLO CLS; lia) ltac:(clear - SPC CLS; lia)) ltac:(clear - V2R; lia) ltac:(clear - SPC CLS; lia)); exact fS144|].
    apply (PNHAK.u64_vis H' M7 M7v (V2 - 136) _ VV7 (VISS (V2 - 136) 8 ltac:(clear - SLO CLS; lia) ltac:(clear - SPC CLS; lia)) ltac:(clear - V2R; lia) ltac:(clear - SPC CLS; lia)); exact fS136. }
  apply (KONT fx7 R7 M7 model7 LK' Aw' BI7 RB7 LS7).
  - exact fR1.
  - exact fR10.
  - rewrite (fKS 21%nat) by inl. exact Y21.
  - rewrite (fKS 22%nat) by inl. exact Y22.
  - rewrite (fKS 23%nat) by inl. exact Y23.
  - rewrite (fKS 26%nat) by inl. exact Y26.
  - exact HB7.
  - exact HQ7.
  - exact HE7.
Qed.
End Stage.
End SCFG_1.
End PNHA5.
