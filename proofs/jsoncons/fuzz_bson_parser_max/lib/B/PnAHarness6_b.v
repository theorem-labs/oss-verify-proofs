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
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b L5StepAR_b L5CoreBR_b L5ADetailHR_b L5AFrameKR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HeapIfaceABx PmLayout PmLayoutA PnLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmModelFactsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStatics PmStaticsA PnStatics PnStaticsA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PnSpecsAa_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgSrc PgV8. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgSrcA_b PgV8A_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnModel PnRun. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnRunA_b PnRunAa_b PnStepA_b PnAReset1_b PnAHarnessStmts_b PnAHarnessKit_b PnAHarnessKit2_b PnAHarnessSK_b PnAParKit_b PnAHarnessP2_b PnAResetBStmts_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module PNHA6.
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

Lemma own_resetA ps : PNM.bparser_own (PNRA.bpst_reset ps) = PNM.bparser_own ps.
Proof.
  destruct ps as [mo dn src bb nb tb ng tg bg sb sk stk]. unfold PNM.bparser_own, PNM.brest_own, PNRA.bpst_reset. cbn.
  destruct bb; destruct nb; destruct tb; reflexivity.
Qed.

Definition rinvB (R0 Rc : bvmap 5 word) (Mc : word -> option byte) (V2 cls F : Z) : Prop :=
  getr Rc (reg 2) = Z_to_bv 64 (V2 - 160) /\ getr Rc (reg 8) = Z_to_bv 64 (F + 1024) /\ getr Rc (reg 9) = Z_to_bv 64 (F + 464) /\
  getr Rc (reg 18) = Z_to_bv 64 0x7fff8000 /\ getr Rc (reg 19) = Z_to_bv 64 (F / 8 + 2147450880) /\ getr Rc (reg 20) = Z_to_bv 64 (F + 32) /\
  getr Rc (reg 24) = Z_to_bv 64 F /\ getr Rc (reg 25) = Z_to_bv 64 2147450880 /\
  getr Rc (reg 3) = getr R0 (reg 3) /\ getr Rc (reg 4) = getr R0 (reg 4) /\ getr Rc (reg 27) = getr R0 (reg 27) /\
  L5.u64_at RSEGS Mc (V2 - 160) F /\ L5.u64_at RSEGS Mc (V2 - 152) (V2 - 128) /\ L5.u64_at RSEGS Mc (V2 - 144) (V2 + cls) /\
  L5.u64_at RSEGS Mc (V2 - 136) 0xa84c0.

Lemma callee_stack160 BX Mc modelc LKc crc Ac h :
  Bv W BX Mc modelc LKc crc Ac -> 0 <= h <= 11 ->
  L5CA.astk ar Mc (V2 - 160) (PMSPA.pm_scr h) /\ shadow_zero Mc (V2 - 160 - PMSPA.pm_scr h) (PMSPA.pm_scr h / 8).
Proof.
  intros BI Hh. pose proof G as G'. destruct G' as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG F32 FLA FLR FLBIG NCF NCS].
  pose proof BI as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10).
  unfold PMSPA.pm_scr.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (AL1 : (V2 + cls - 36864) mod 8 = 0) by (clear - CLS V2A; lia).
  assert (AL2 : (V2 - 160 - (12288 + 2048 * h)) mod 8 = 0) by (clear - V2A; lia).
  assert (AL3 : (V2 + cls - (160 + cls)) mod 16 = 0) by (clear - V2A; lia).
  assert (DV : (12288 + 2048 * h) / 8 = 1536 + 256 * h) by (clear; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  rewrite DV. split.
  - replace (V2 - 160) with ((V2 + cls) - (160 + cls)) by (clear; lia).
    apply (L5SAR.astk_sub ar Mc Mc (V2 + cls) 36864 (160 + cls) (12288 + 2048 * h) B6 (fun _ X => X)); [clear - CLS; lia| clear - Hh; lia| clear - CLS Hh; lia| exact AL3].
  - apply (PMKA.shadow_zero_sub Mc (V2 + cls - 36864) 4608); [exact AL1| exact AL2| clear - CLS Hh; lia| clear - CLS Hh; lia| clear - Hh; lia|].
    apply (PMKA.stksh_keepA L ar LB FF (V2 + cls) 36864 W M Mc B7 WAPP); [clear - SLO SPT; lia| clear - SLO SPT; lia| clear - V2S CLS; lia| exact AL1| lia| exact STKSH].
Qed.

Lemma callee_entry160 BX Mc modelc LKc crc Ac Rc r h :
  Bv W BX Mc modelc LKc crc Ac -> rinvB R Rc Mc V2 cls F -> getr Rc (reg 1) = Z_to_bv 64 r -> L5.ra_ok r -> 0 <= h <= 11 ->
  PMSPA.entryA PMA.AD L ar Rc Mc (V2 - 160) r h.
Proof.
  intros BI RI R1 RA Hh. pose proof RI as (X2 & X8 & X9 & X18 & X19 & X20 & X24 & X25 & X3 & X4 & X27 & _).
  destruct (callee_stack160 BX Mc modelc LKc crc Ac h BI Hh) as (AS & SZ).
  split; [rewrite L5K.rl1; exact R1|]. split; [exact RA|]. split; [rewrite L5K.rl2; exact X2|].
  split; [rewrite L5K.rl3, X3; exact GP|]. split; [rewrite L5K.rl4, X4; exact TP|]. split; [exact AS| exact SZ].
Qed.

Lemma ahpres_up (LBx : list (Z * Z)) (FFx : list fframe) (sp scr d : Z) (Wx : list L5.range) (Ma Mb : word -> option byte) :
  L5CA.ahpres L ar LBx FFx sp scr Wx Ma Mb -> 0 <= d -> 0 <= scr -> 0 <= sp -> ahl_ceil ar <= sp -> sp + d <= 2 ^ 47 -> L5.defined Ma sp d ->
  L5CA.ahpres L ar LBx FFx (sp + d) (scr + d) Wx Ma Mb.
Proof.
  intros (AK & DF & DK) Hd Hs Hp Hc Ht DA.
  assert (CL : forall a, HeapIfaceA.aclient L ar LBx FFx (sp + d) (scr + d) a -> HeapIfaceA.aclient L ar LBx FFx sp scr a).
  { intros a X. unfold HeapIfaceA.aclient, HeapIfaceA.aclient_g in X |- *.
    destruct X as [X|[(X1 & X2)|X]]; [left; exact X| right; left; split; [exact X1| intros (Y1 & Y2); apply X2; split; lia]| right; right; exact X]. }
  split; [| split].
  - intros a (A0 & A1 & A2). apply AK. split; [exact A0|]. split; [exact (CL a A1)| exact A2].
  - intros i Hi. replace (sp + d - (scr + d) + i) with (sp - scr + i) by lia.
    destruct (Z_lt_ge_dec i scr) as [Hl|Hg]; [apply DF; lia|].
    replace (sp - scr + i) with (sp + (i - scr)) by lia.
    apply (DK (sp + (i - scr))); [lia| | apply DA; lia].
    unfold HeapIfaceA.aclient, HeapIfaceA.aclient_g. right; left. split; [lia| intros (Y1 & Y2); lia].
  - intros a Ha Hc'. apply DK; [exact Ha| exact (CL a Hc')].
Qed.

Lemma stage6 (RST : PNARBS.reset_spec L ar HI) (fx7 : FPState) (R7 : bvmap 5 word) (M7 : word -> option byte) (model7 : Model) (K : TSet)
      (LK7 : list fframe) (cr7 : credit) (A7 : list (Z * Z)) (s s' : PM.vstr) (sm : PM.strm) (ps : PNM.bpst) (g : PNST.st) (v c : Z) :
  Bv W (PNM.bparser_own ps ++ PM.vs_own s' ++ PM.vs_own s) M7 model7 LK7 cr7 A7 -> rinvB R R7 M7 V2 cls F -> K [] -> PNSTA.ls_okA RSEGS PMA.AD PMA.AAD PMA.AN g M7 ->
  getr R7 (reg 1) = Z_to_bv 64 0xa8e44 -> getr R7 (reg 10) = Z_to_bv 64 (F + 464) -> getr R7 (reg 21) = Z_to_bv 64 (F + 96) ->
  getr R7 (reg 22) = Z_to_bv 64 (F + 464) -> getr R7 (reg 23) = Z_to_bv 64 (F + 1024) -> getr R7 (reg 26) = Z_to_bv 64 18446744073709551608 ->
  PNHAK2.hbase F M7 s s' sm -> PNHAK2.hpar F M7 ps -> PNHAK2.hec F M7 v c ->
  (forall (fx8 : FPState) (R8 : bvmap 5 word) (M8 : word -> option byte) (model8 : Model) (LK8 : list fframe) (A8 : list (Z * Z)),
      Bv W (PNM.bparser_own ps ++ PM.vs_own s' ++ PM.vs_own s) M8 model8 LK8 cr7 A8 -> rinvH R R8 V2 cls F ->
      PNSTA.ls_okA RSEGS PMA.AD PMA.AAD PMA.AN g M8 ->
      getr R8 (reg 1) = Z_to_bv 64 0xa84c0 -> getr R8 (reg 10) = Z_to_bv 64 (F + 464) -> getr R8 (reg 11) = Z_to_bv 64 (F + 432) ->
      getr R8 (reg 12) = Z_to_bv 64 (F + 1024) -> getr R8 (reg 21) = Z_to_bv 64 (F + 96) ->
      getr R8 (reg 22) = Z_to_bv 64 (F + 464) -> getr R8 (reg 23) = Z_to_bv 64 (F + 1024) -> getr R8 (reg 26) = Z_to_bv 64 18446744073709551608 ->
      PNHAK2.hbase F M8 s s' sm -> PNHAK2.hpar F M8 (PNRA.bpst_reset ps) -> PNHAK2.hec F M8 v c ->
      srealizes RSEGS SCFG (@L5A.cfg fx8 R8 0xade6c M8 model8) K) ->
  srealizes RSEGS SCFG (@L5A.cfg fx7 R7 0xadb68 M7 model7) K.
Proof.
  intros BI RI K0 LS R1a R10 R21 R22 R23 R26 HB0 HP0 HE0 KONT.
  pose proof G as G'. destruct G' as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG F32 FLA FLR FLBIG NCF NCS].
  change (ff_bytes 5) with 2048 in *. change (2048 / 8) with 256 in *.
  pose proof BI as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10).
  pose proof RI as (X2 & X8 & X9 & X18 & X19 & X20 & X24 & X25 & X3 & X4 & X27 & C160 & C152 & C144 & C136).
  assert (FM8 : F mod 8 = 0) by (pose proof (proj1 F8) as E8; clear - E8; lia).
  assert (FHF : PNHAK2.hf F) by (unfold PNHAK2.hf, BIGSHADOW_LO, BIGSHADOW_HI; clear - FR FBIG FM8; lia).
  assert (B1' : ri_inv HI (PNM.bparser_own ps ++ ((PM.vs_own s' ++ PM.vs_own s) ++ LB)) FF' LK7 cr7 A7 M7 (vml_of model7)) by (rewrite app_assoc; exact B1).
  pose proof HP0 as (PA0 & REF0 & ACC0).
  unfold PNARBS.reset_spec, PNARBS.bparser_at in RST.
  apply (RST fx7 R7 M7 model7 K ((PM.vs_own s' ++ PM.vs_own s) ++ LB) FF' LK7 A7 cr7 (V2 - 160) 0xa8e44 F ps B1' B2 K0).
  { eapply callee_entry160; first [exact BI | exact RI | exact R1a | eassumption | (split; [lia| reflexivity]) | lia]. }
  { eapply PNHASK.callee_room; first [exact BI | eassumption | lia]. }
  { intros f [<-|Hf]; [cbn [ff_rs fst snd]; lia| specialize (FFRS f Hf); clear - Hf FFRS CLS; lia]. }
  { exact (PNHASK.callee_frame FF V2 F FAL). }
  { rewrite L5K.rl10. exact R10. }
  { exact PA0. }
  { intros a Ha. apply ACC0. clear - Ha. lia. }
  { exact (proj1 LS). }
  intros fx' R' M' model' LK' Aw' RP' PA' HP0' MRT' INCLK' INCA' AM' HH'.
  change (PMSPA.pm_scr 1) with 14336 in HP0'.
  rewrite app_assoc in HH'.
  set (Wc := [(F + 464 + 8, 8); (F + 464 + 320, 24); (F + 464 + 344, 24); (F + 464 + 368, 24); (F + 464 + 392, 24)]) in *.
  assert (WcF : forall r, In r Wc -> F + 464 <= fst r /\ fst r + snd r <= F + 880) by (intros r Hr; subst Wc; destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd]; lia).
  assert (WFI : PNHAK2.wfi F Wc) by (intros r Hr; destruct (WcF r Hr); left; lia).
  assert (WA : forall o n, (o + n <= F + 464 \/ F + 880 <= o) -> PNHAK2.wapart Wc o n) by (intros o n Ho r Hr; destruct (WcF r Hr); lia).
  assert (KEEP : forall a, V2 - 160 <= a < V2 - 128 -> M' (Z_to_bv 64 a) = M7 (Z_to_bv 64 a)).
  { pose proof HP0' as (AK0 & _ & _). intros a Ha. apply AK0. split; [clear - Ha V2R; lia|]. split.
    - right; left. split; [clear - Ha SLO CLS V2R; lia| intros (Y1 & Y2); clear - Ha Y2; lia].
    - intros rr Hr Hin. destruct (WcF rr Hr) as (Z1 & Z2). unfold L5.in_rng in Hin. clear - Ha Hin Z1 Z2 FCEIL SLO CLS. lia. }
  assert (CM : forall a vq, V2 - 160 <= a -> a + 8 <= V2 - 128 -> L5.u64_at RSEGS M7 a vq -> L5.u64_at RSEGS M' a vq).
  { intros a vq H1 H2. apply (L5C.u64_at_agree RSEGS M7 M' a vq); [intros i Hi; apply KEEP; lia| clear - H1 V2R; lia| clear - H2 V2R; lia]. }
  assert (D7 : L5.defined M7 (V2 - 160) 32).
  { pose proof B6 as (_ & _ & _ & _ & BD & _). apply (L5.defined_sub M7 _ _ (V2 - 160) 32 BD); clear - CLS; lia. }
  pose proof (ahpres_up _ _ (V2 - 160) _ 32 _ _ _ HP0' ltac:(lia) ltac:(lia) ltac:(clear - V2R; lia) ltac:(clear - SLO CLS; lia) ltac:(clear - V2R; lia) D7) as HP'.
  replace (V2 - 160 + 32) with (V2 - 128) in HP' by lia.
  assert (LS' : PNSTA.ls_okA RSEGS PMA.AD PMA.AAD PMA.AN g M').
  { apply (PNHAK.ls_ahpres L C LY g ar _ FF' (V2 - 128) _ Wc M7 M' HP'); [| exact LS].
    intros r Hr. destruct (WcF r Hr). right. clear - H H0 FR. lia. }
  assert (BI' : Bv W (PNM.bparser_own ps ++ PM.vs_own s' ++ PM.vs_own s) M' model' LK' cr7 Aw').
  { apply (L5AFKR.binv_callee L ar C HI HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W W _ (PM.vs_own s' ++ PM.vs_own s) _ M7 model7 LK7 cr7 A7 M' model' LK' cr7 Aw' _ Wc BI HP' HH' AM' MRT' INCA' INCLK').
    - lia.
    - clear - CLS; lia.
    - intros rr a Hr Ha. destruct (WcF rr Hr) as (Z1 & Z2). unfold L5.in_rng in Ha. unfold tocell. split; [clear - Ha Z1 Z2 FCEIL SLO CLS; lia|].
      unfold HeapIfaceA.SB. change (ff_bytes 5) with 2048. clear - Ha Z1 Z2 FR F8 FBIG. lia.
    - intros a Hc _ rr Hr Ha. destruct (WcF rr Hr) as (Z1 & Z2). unfold L5.in_rng in Ha. apply (NCF a); [left; clear - Ha Z1 Z2; lia| exact Hc].
    - intros a X. exact X. }
  pose proof (L5AFKR.vis_facts L ar C HI LYa HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W _ M' model' LK' cr7 Aw' BI')
    as ((VW' & VIC' & VSB' & VUAR' & VMS') & VOWN' & (VFD' & VFW' & VFSW' & VFLC' & VFLW') & (FLCc' & FLV' & FV' & SPV' & FSV')).
  change (ff_bytes 5) with 2048 in *. change (2048 / 8) with 256 in *.
  set (H' := ahid Aw' model') in *. set (MV' := mrestrict H' M') in *.
  pose proof (cs_of_preserved R7 R' 2 RP' ltac:(inl)) as Y2. rewrite X2 in Y2.
  pose proof (cs_of_preserved R7 R' 8 RP' ltac:(inl)) as Y8. rewrite X8 in Y8.
  pose proof (cs_of_preserved R7 R' 9 RP' ltac:(inl)) as Y9. rewrite X9 in Y9.
  pose proof (cs_of_preserved R7 R' 18 RP' ltac:(inl)) as Y18. rewrite X18 in Y18.
  pose proof (cs_of_preserved R7 R' 19 RP' ltac:(inl)) as Y19. rewrite X19 in Y19.
  pose proof (cs_of_preserved R7 R' 20 RP' ltac:(inl)) as Y20. rewrite X20 in Y20.
  pose proof (cs_of_preserved R7 R' 24 RP' ltac:(inl)) as Y24. rewrite X24 in Y24.
  pose proof (cs_of_preserved R7 R' 25 RP' ltac:(inl)) as Y25. rewrite X25 in Y25.
  pose proof (cs_of_preserved R7 R' 3 RP' ltac:(inl)) as Y3. rewrite X3 in Y3.
  pose proof (cs_of_preserved R7 R' 4 RP' ltac:(inl)) as Y4. rewrite X4 in Y4.
  pose proof (cs_of_preserved R7 R' 27 RP' ltac:(inl)) as Y27. rewrite X27 in Y27.
  assert (Y21 : getr R' (reg 21) = Z_to_bv 64 (F + 96)) by (rewrite (cs_of_preserved R7 R' 21 RP') by inl; exact R21).
  assert (Y22 : getr R' (reg 22) = Z_to_bv 64 (F + 464)) by (rewrite (cs_of_preserved R7 R' 22 RP') by inl; exact R22).
  assert (Y23 : getr R' (reg 23) = Z_to_bv 64 (F + 1024)) by (rewrite (cs_of_preserved R7 R' 23 RP') by inl; exact R23).
  assert (Y26 : getr R' (reg 26) = Z_to_bv 64 18446744073709551608) by (rewrite (cs_of_preserved R7 R' 26 RP') by inl; exact R26).
  assert (FIN7 : In (F, 5, V2 - 128 + 32) (FF' ++ LK7)) by (apply in_or_app; left; left; reflexivity).
  (* [comment removed for export] *)
  assert (HB' : PNHAK2.hbase F M' s s' sm).
  { eapply PNHAK2.hbase_callee; first [ exact B1 | exact HP' | exact HB0 | exact FHF | exact FIN7 | exact WFI | (apply WA; lia)
      | (intros x Hx; apply in_or_app; left; apply in_or_app; right; exact Hx) | (intros x Hx; apply in_or_app; left; exact Hx) | hsolve ]. }
  assert (HE' : PNHAK2.hec F M' v c).
  { eapply PNHAK2.hec_callee; first [ exact B1 | exact HP' | exact HE0 | exact FHF | exact FIN7 | exact WFI | (apply WA; lia) | hsolve ]. }
  assert (AGR : PMFA.agA M7 M' (F + 880) 8).
  { apply (PNHAK2.ff_callee L ar _ FF' (V2 - 128) _ Wc M7 M' (F, 5, V2 - 128 + 32) F (F + 880) 8 HP' (or_introl eq_refl));
      cbn [ff_addr ff_class fst snd]; change (ff_bytes 5) with 2048; [lia| lia| exact FHF| lia| lia| exact WFI| apply WA; lia]. }
  assert (REF' : L5.u64_at RSEGS M' (F + 880) (F + 432)) by (apply (PNHAK2.u64_agA M7 M' (F + 880) 8 (F + 880) _ AGR); [lia| lia| lia| lia| exact REF0]).
  assert (SZP' : shadow_zero M' (F + 464) 53).
  { apply (PNHAK2.shz_callee L ar _ FF' (V2 - 128) _ Wc M7 M' (F, 5, V2 - 128 + 32) F (F + 464) 53 HP' (or_introl eq_refl) (conj eq_refl eq_refl) FHF WFI);
      [lia| lia| exact (PNAPAR.fb_mod8 F 58 FAL)| lia|].
  apply (PNHAK2.shz_of_acc M7 (F + 464) 53); [exact ACC0| exact (PNAPAR.fb_mod8 F 58 FAL)| clear - FR; lia]. }
  assert (ACC' : PMSPA.accA M' (F + 464) 424).
  { apply (PNHAK2.acc_of_shz M' (F + 464) 53 (F + 464) 424); [| exact (PNAPAR.fb_mod8 F 58 FAL)| clear - FR; lia| lia| lia].
    apply (PNHAK2.shz_callee L ar _ FF' (V2 - 128) _ Wc M7 M' (F, 5, V2 - 128 + 32) F (F + 464) 53 HP' (or_introl eq_refl) (conj eq_refl eq_refl) FHF WFI);
      [lia| lia| exact (PNAPAR.fb_mod8 F 58 FAL)| lia|].
    apply (PNHAK2.shz_of_acc M7 (F + 464) 53); [exact ACC0| exact (PNAPAR.fb_mod8 F 58 FAL)| clear - FR; lia]. }
  (* [comment removed for export] *)
  idtac.
  assert (Q1 : 4096 <= F <= 140737488353280) by (clear - FR; lia).
  assert (Q2 : 4096 <= fl <= 140737488355327) by (clear - FLR; lia).
  assert (Q3 : V2 - 160 + 176 <= F \/ F + 2048 <= V2 - 160) by (clear - FCEIL SLO CLS; lia).
  assert (Q4 : V2 - 160 + 176 <= fl \/ fl + 1 <= V2 - 160) by (clear - FLR SLO CLS; lia).
  pose proof BI' as (BH1 & _ & _ & _ & _ & BASTK & _).
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ FF' LK' cr7 Aw' M' model' BH1) as (_ & VISS & _).
  assert (Q5 : L5.writable RSEGS MV' (V2 - 160) 160).
  { apply (proj2 (L5A.writable_vis H' M' (V2 - 160) 160 (VISS (V2 - 160) 160 ltac:(clear - SLO CLS; lia) ltac:(clear - SPC CLS; lia)) ltac:(clear - V2R; lia) ltac:(clear - SPC CLS; lia))).
    apply (L5SAR.astk_writable ar M' _ _ (V2 - 160) 160 BASTK); clear - SPC CLS; lia. }
  pose proof (VISS (V2 - 160) 160 ltac:(clear - SLO CLS; lia) ltac:(clear - SPC CLS; lia)) as VST.
  assert (QC : forall a vq, V2 - 160 <= a -> a + 8 <= V2 - 128 -> L5.u64_at RSEGS M7 a vq -> L5.u64_at RSEGS MV' a vq).
  { intros a vq H1 H2 U. apply (proj2 (L5A.u64_at_vis H' M' a vq (PNHAK.avis_sub H' (V2 - 160) 160 a 8 VST ltac:(clear - H1; lia) ltac:(clear - H2; lia)) ltac:(clear - H1 V2R; lia) ltac:(clear - H2 V2R; lia))).
    exact (CM a vq H1 H2 U). }
  pose proof (QC (V2 - 160) F ltac:(clear; lia) ltac:(clear; lia) C160) as QC160.
  pose proof (QC (V2 - 152) (V2 - 128) ltac:(clear; lia) ltac:(clear; lia) C152) as QC152.
  pose proof (QC (V2 - 144) (V2 + cls) ltac:(clear; lia) ltac:(clear; lia) C144) as QC144.
  pose proof (QC (V2 - 136) _ ltac:(clear; lia) ltac:(clear; lia) C136) as QC136.
  assert (SZE' : shadow_zero M' (F + 880) 1)
    by (apply (PMKA.shadow_zero_sub M' (F + 464) 53); [clear - FM8; lia| clear - FM8; lia| lia| lia| lia| exact SZP']).
  assert (ZE' : L5KA.zeros_at MV' (F / 8 + 2147450990) 1).
  { apply (proj2 (L5A.zeros_at_vis H' M' (F / 8 + 2147450990) 1 (PNHAK.avis_sub H' (F / 8 + HeapIfaceA.SB) 256 (F / 8 + 2147450990) 1 FSV' ltac:(unfold HeapIfaceA.SB; lia) ltac:(unfold HeapIfaceA.SB; lia)))).
    replace (F / 8 + 2147450990) with (HeapIfaceA.S (F + 880)). apply PNHAK2.zeros_of_shz. exact SZE'.
    unfold HeapIfaceA.S, HeapIfaceA.SB. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). clear - FM8. lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  assert (Q6 : L5.u64_at RSEGS MV' (F + 2040) fl) by (replace (F + 2040) with (F + 2048 - 8) by (clear; lia); exact VFLC').
  assert (Q7 : L5.u64_at RSEGS MV' (F + 880) (F + 432))
    by (apply (proj2 (L5A.u64_at_vis H' M' (F + 880) (F + 432) (PNHAK.avis_sub H' F 2048 (F + 880) 8 FV' ltac:(lia) ltac:(lia)) ltac:(clear - FR; lia) ltac:(clear - FR; lia))); exact REF').
  LeanFeed.pfeed P (PNAHP2.bhaG_conc fx' R' MV' (fun j => match j with 2%nat => V2 | 8%nat => V2 + cls | 35%nat => F + 432 | 40%nat => F | 41%nat => fl | 58%nat => U R' 1 | _ => 0 end)) ltac:(first [ asm | apply UR | apply U_to | (clear - V2R; lia) | (clear - FR; lia) | (clear - FLR; lia) | exact F32
                     | exact VFD' | exact VFW' | exact VFSW' | exact VFLW' | exact Q5 | exact Q6 | exact Q7 | exact QC160 | exact QC152 | exact QC144 | exact QC136 | exact ZE' | (unfold PNAHP2.aligned; clear - FM8; lia) | (clear - V2R V2S CLS; lia) | (unfold PNAHP2.aligned; exact V2A) ]).
  destruct P as (fx8 & R8 & M8v & MG8 & gFR & gFZ & (gMS & gKS & gR1 & gR2 & gR8 & gR9 & gR10 & gR11 & gR12 & gR18)).
  set (W8 := fun a : Z => False).
  apply (apiece L ar C HI LYa HIok _ FF' LK' cr7 Aw' M' model' fx' fx8 R' 0xa8e44 R8 0xade6c M8v W8 K HH' AM' gMS MG8).
  { intros a Ha Hna. apply gFZ; exact Ha. }
  { intros a Ha Wa. destruct Wa. }
  intros M8 model8 HH8 AM8 MRT8 HID8 VIS8 MGM8 FR8 VV8.
  assert (BI8 : Bv W (PNM.bparser_own ps ++ PM.vs_own s' ++ PM.vs_own s) M8 model8 LK' cr7 Aw').
  { apply (L5AFKR.binv_piece L ar HI M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W _ M' model' LK' cr7 Aw' M8 model8 W8 BI' HH8 AM8 MRT8 MGM8 FR8).
    intros a Wa. destruct Wa. }
  assert (RI8 : rinvH R R8 V2 cls F).
  { unfold rinvH. split; [exact gR2|]. split; [exact gR8|]. split; [exact gR9|]. split; [exact gR18|].
    rewrite (gKS 19%nat), (gKS 20%nat), (gKS 24%nat), (gKS 25%nat), (gKS 3%nat), (gKS 4%nat), (gKS 27%nat) by inl.
    repeat split; assumption. }
  assert (LS8 : PNSTA.ls_okA RSEGS PMA.AD PMA.AAD PMA.AN g M8) by (apply (PNHAK.ls_piece _ M' M8 W8 FR8); [intros a []| exact LS']).
  assert (PF8 : PNHAK2.pfoot F (V2 - 128) V2 W8) by (intros a []).
  assert (FIN' : In (F, 5, V2 - 128 + 32) (FF' ++ LK')) by (apply in_or_app; left; left; reflexivity).
  assert (SLOW : ahl_ceil ar <= V2 - 128) by (clear - SLO CLS; lia).
  assert (SHW : BIGSHADOW_HI <= V2 - 128) by (unfold BIGSHADOW_HI; clear - V2R; lia).
  assert (OAX : forall o n, PNHAK2.oav W8 o n) by (intros o n x Hx; split; intros []).
  apply (KONT fx8 R8 M8 model8 LK' Aw' BI8 RI8 LS8).
  - exact gR1.
  - exact gR10.
  - exact gR11.
  - exact gR12.
  - rewrite (gKS 21%nat) by inl. exact Y21.
  - rewrite (gKS 22%nat) by inl. exact Y22.
  - rewrite (gKS 23%nat) by inl. exact Y23.
  - rewrite (gKS 26%nat) by inl. exact Y26.
  - apply (PNHAK2.hbase_piece L ar C SCFG HI HIok _ _ _ _ _ _ _ F (V2 - 128 + 32) HH' FIN' FHF (V2 - 128) V2 W8 M' M8 SLOW SHW FR8 PF8 s s' sm);
      [intros x Hx; apply in_or_app; left; apply in_or_app; right; exact Hx| apply OAX| apply OAX| apply OAX| exact HB'].
  - apply (PNHAK2.hpar_piece L ar C SCFG HI HIok _ _ _ _ _ _ _ F (V2 - 128 + 32) HH' FIN' FHF (V2 - 128) V2 W8 M' M8 SLOW SHW FR8 PF8 (PNRA.bpst_reset ps));
      [| apply OAX| split; [exact PA'| split; [exact REF'| exact ACC']]].
    intros x Hx. apply in_or_app. left. apply in_or_app. left. rewrite own_resetA in Hx. exact Hx.
  - eapply PNHAK2.hec_piece; first [exact FHF | exact FR8 | exact HE' | apply OAX].
Qed.
End Stage.
End SCFG_1.
End PNHA6.
