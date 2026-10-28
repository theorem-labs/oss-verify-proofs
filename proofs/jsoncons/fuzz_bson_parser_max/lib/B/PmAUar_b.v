(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HeapIfaceABx PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import LibIface
     AsanAcct AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b L5CoreSpecsA_b L5StepAR_b L5CoreBR_b L5ADetailHR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PnSpecsAa_b PgSrcA_b PmAUarK_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PMAUAR.
Import L5A. Import L5CA. Import L5SAR.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.

(* [comment removed for export] *)
Lemma ffroomA_push h h' FF LK LK2 (f : fframe) :
  PMSPA.ffroomA h FF LK -> incl LK2 LK -> NoDup (map ff_addr ((f :: FF) ++ LK2)) -> h' + 1 <= h -> PMSPA.ffroomA h' (f :: FF) LK2.
Proof.
  intros FR INC ND Hh k Hk. specialize (FR k Hk). rewrite ff_count_app in FR. rewrite ff_count_app.
  pose proof (ff_count_cons k f FF) as C1.
  pose proof (ff_count_incl k LK2 LK INC (nodup_of_map_app_r (f :: FF) LK2 ND)) as C2. lia.
Qed.
Lemma ffrsA_push FF sp sp' F k rs : PMSPA.ffrsA FF sp -> sp' + 32 <= rs -> sp' <= sp -> PMSPA.ffrsA ((F, k, rs) :: FF) sp'.
Proof. intros H1 H2 H3 f [<-|Hf]; [cbn; lia| specialize (H1 f Hf); lia]. Qed.
Lemma frame_okA_push FF fb F k rs : PMSPA.frame_okA FF fb -> PMSPA.frame_okA ((F, k, rs) :: FF) fb.
Proof. intros ((r0 & Hf) & Hm). split; [exists r0; right; exact Hf| exact Hm]. Qed.
Lemma aobjA_push FF o n f : PMSPA.aobjA FF o n -> PMSPA.aobjA (f :: FF) o n.
Proof. intros (g & Hg & X). exists g. split; [right; exact Hg| exact X]. Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ffroomB_push FC h h' FF LK LK2 (f : fframe) :
  PGSA.ffroomB FC h FF LK -> incl LK2 LK -> NoDup (map ff_addr ((f :: FF) ++ LK2)) -> h' + 1 <= h -> PGSA.ffroomB FC h' (f :: FF) LK2.
Proof.
  intros FR INC ND Hh k Hk. specialize (FR k Hk). rewrite ff_count_app in FR. rewrite ff_count_app.
  pose proof (ff_count_cons k f FF) as C1.
  pose proof (ff_count_incl k LK2 LK INC (nodup_of_map_app_r (f :: FF) LK2 ND)) as C2. lia.
Qed.
Lemma ff_room_ofB FC h FF LK k : PGSA.ffroomB FC h FF LK -> 0 <= h -> In k FC -> ff_room k FF LK.
Proof. intros FR Hh Hk. specialize (FR k Hk). unfold ff_room. lia. Qed.
Lemma classB_in6 k : In k [0; 1; 3; 5] -> In k [0; 1; 2; 3; 4; 5].
Proof. intros Hk. cbn in Hk |- *. tauto. Qed.

Section SCFG_1.
Context {SCFG_P : ScfgP}.
Section WithIface.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Let LYa := PMA.ly_as0 L C LY.

Lemma uar_sm (k : Z) (LB BX0 : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z))
      (E SCR spc olo ohi : Z) (ocell : Z -> Prop) (own : (word -> option byte) -> Prop)
      (fx : FPState) (R1 : bvmap 5 word) (M M1 : word -> option byte) (model model1 : Model) (K : TSet) (rr : Z) :
  In k [0; 1; 3; 5] ->
  ri_inv HI (BX0 ++ LB) FF LK cr A M (vml_of model) ->
  ri_inv HI (BX0 ++ LB) FF LK cr A M1 (vml_of model1) -> amodel_ok A model1 -> K [] ->
  astk ar M E SCR -> mem_grows M M1 -> ek L ar LB FF E SCR [] M M1 -> dk L ar LB FF E SCR M M1 ->
  getr R1 2%bv = Z_to_bv 64 spc -> getr R1 4%bv = Z_to_bv 64 (hl_tp L) -> getr R1 1%bv = Z_to_bv 64 rr -> rr mod 2 = 0 -> 0 <= rr < 2 ^ 64 ->
  spc mod 16 = 0 -> E - SCR + 512 <= spc -> spc <= olo -> olo <= ohi -> ohi <= E ->
  (forall a, ocell a -> olo <= a < ohi) ->
  (forall M1 M1', own M1 -> (forall a, ocell a -> M1' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) -> own M1') ->
  ff_room k FF LK -> (forall f, In f FF -> E + 32 <= ff_rs f) ->
  (forall (R2 : bvmap 5 word) (M2 : word -> option byte) (model2 : Model) (F fl : Z) (LK2 : list fframe),
     PMAUK.gctx L ar HI LB FF LK A E SCR spc olo ohi ocell own F fl k LK2 M2 model2 cr BX0 ->
     getr R2 10%bv = Z_to_bv 64 F -> regs_preserved R1 R2 -> amodel_ok A model2 -> model_rt model1 model2 ->
     astk ar M2 E SCR -> ek L ar LB FF E SCR [] M M2 -> dk L ar LB FF E SCR M M2 ->
     ek L ar (BX0 ++ LB) FF E SCR [] M1 M2 -> dk L ar (BX0 ++ LB) FF E SCR M1 M2 ->
     (forall a, spc <= a < E -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) ->
     L5.writable RSEGS (mrestrict (ahid A model2) M2) F (ff_bytes k) ->
     L5.writable RSEGS (mrestrict (ahid A model2) M2) (F / 8 + SB) (ff_bytes k / 8) ->
     L5KA.zeros_at (mrestrict (ahid A model2) M2) (F / 8 + SB) (ff_bytes k / 8) ->
     L5.u64_at RSEGS (mrestrict (ahid A model2) M2) (F + ff_bytes k - 8) fl -> L5.writable RSEGS (mrestrict (ahid A model2) M2) fl 1 ->
     L5.defined (mrestrict (ahid A model2) M2) F (ff_bytes k) ->
     avis (ahid A model2) F (ff_bytes k) -> avis (ahid A model2) (F / 8 + SB) (ff_bytes k / 8) -> avis (ahid A model2) fl 1 ->
     (forall a n sp0 scr0, (forall i, 0 <= i < n -> aclient L ar (BX0 ++ LB) FF sp0 scr0 (a + i)) -> 0 < n ->
         (a + n <= F \/ F + ff_bytes k <= a) /\ (a + n <= F / 8 + SB \/ F / 8 + SB + ff_bytes k / 8 <= a) /\ (a + n <= fl \/ fl + 1 <= a)) ->
     srealizes RSEGS SCFG (@L5A.cfg fx R2 rr M2 model2) K) ->
  srealizes RSEGS SCFG (@L5A.cfg fx R1 (PMA.SM_PC k) M1 model1) K.
Proof.
  intros Hk HH HH1 AM1 K0 ASTK MG01 EK01 DK01 G2 G4 G1 RR0 RR1 SP16 SPSC SPO1 SPO2 SPO3 OCR OWNAG FFRk FFRS KONT.
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  pose proof (classB_in6 k Hk) as Hk6.
  pose proof (HAJ.aior_stack_malloc _ _ _ _ _ HIok k Hk) as SM. unfold astack_malloc_spec in SM.
  rewrite (aly_segs L C LYa), (PMA.ly_sm L C LY k Hk), (aly_scr_sm L C LYa) in SM.
  assert (U2 : bv_unsigned (getr R1 2%bv) = spc) by (rewrite G2; apply L5.unsigned_lit; clear - SPSC SPO1 SPO2 SPO3 SHI SPT SLO; lia).
  eapply (SM fx R1 M1 model1 (BX0 ++ LB) FF LK cr A K HH1 (proj1 AM1) (proj2 AM1)); clear SM.
  - exact G4.
  - rewrite G1. apply Hoare.ret_ok_even. rewrite L5.unsigned_lit by exact RR1. exact RR0.
  - rewrite U2. replace spc with (E - (E - spc)) by (clear; lia).
    apply (astack_ok_of_astk L ar C LYa M M1 E SCR (E - spc) 512 ASTK MG01); [clear - SPO1 SPO2 SPO3; lia| clear; lia| clear - SPSC; lia|].
    replace (E - (E - spc)) with spc by (clear; lia). exact SP16.
  - exact FFRk.
  - intros f Hf. rewrite U2. specialize (FFRS f Hf). clear - FFRS SPO1 SPO2 SPO3. lia.
  - exact K0.
  - intros R2 M2 model2 F fl LK2 B10 RP2 (FS1 & FS2 & FAL & FAPP & FCEIL) FIMG FAPART FBLK LKI2 FDEF FLC FLP FLNC FLA FLW FSH PRES2 RT2 MI2 HH2.
    rewrite U2 in FLNC, PRES2, HH2. rewrite G1.
    pose proof (sm_facts L ar C HI LYa HIok (BX0 ++ LB) FF LK2 cr A M2 model2 F k (spc + 32) fl HH2 Hk6 FS1 FS2 FAL FAPP FCEIL FDEF FLC FLP FLNC FLA FSH)
      as (FR & FFL & F32 & F8 & B64 & FDEFv & FWv & FBIG & FSHW & FSHZ & FLCv & FLR & FLWv & FLBIG & VF & VSH & VFL).
    assert (Hh2 : m_halted model2 = None) by (rewrite (L5LZ.model_rt_halted _ _ RT2); exact (proj1 AM1)).
    assert (ASTK2 : astk ar M2 E SCR).
    { apply (astk_after_rt L ar C HI HIok (BX0 ++ LB) FF LK cr A M M1 M2 _ E SCR spc 512 HH ASTK MG01 PRES2); clear - SPSC SPO1 SPO2 SPO3 SLO; lia. }
    assert (NCS : forall a, spc <= a < E -> ~ aclient L ar LB FF E SCR a).
    { intros a Xa Hc. destruct (aclient_cases L ar C HI LYa HIok (BX0 ++ LB) FF LK cr A M _ E SCR a HH SPT (aclient_appb L ar LB BX0 FF E SCR a Hc)) as [Y|Y].
      - clear - Xa Y SPSC SPO1 SPO2 SPO3; lia.
      - clear - Xa Y SLO SPSC SPO1 SPO2 SPO3; lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    assert (BQ : ff_bytes k mod 8 = 0 /\ (F + ff_bytes k - 1) / 8 = F / 8 + ff_bytes k / 8 - 1 /\ ff_bytes k / 8 * 8 = ff_bytes k) by (clear - F8 B64 FR; lia).
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    assert (NCF : forall a, (F <= a < F + ff_bytes k \/ S F <= a <= S (F + ff_bytes k - 1)) -> ~ aclient L ar LB FF E SCR a).
    { intros a Ha Hc. apply (fresh_frame_not_client L ar C HI LYa HIok (BX0 ++ LB) FF LK cr A M _ E SCR F (ff_bytes k) a HH SPT).
      - clear - FR; lia.
      - exact FCEIL.
      - exact FAPP.
      - clear - F8; lia.
      - clear - FR; lia.
      - exact (proj1 BQ).
      - eapply fframes_apart_incl. exact FAPART. intros g0 Hg; apply in_or_app; left; exact Hg.
      - exact FBLK.
      - exact Ha.
      - exact (aclient_appb L ar LB BX0 FF E SCR a Hc). }
    assert (AGF : forall a, spc <= a < E -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
    { intros a Ha. apply (proj1 PRES2 a); [clear - Ha SPSC SPO1 SPO2 SPO3 SLO SHI SPT; lia|]. apply stack_client; clear - Ha SPSC SPO1 SPO2 SPO3 SLO SHI SPT; lia. }
    assert (FLNCl : ~ aclient L ar LB ((F, k, spc + 32) :: FF) 0 0 fl) by (intros X; apply FLNC; exact (aclient_appb L ar LB BX0 _ 0 0 fl X)).
    assert (G : PMAUK.gctx L ar HI LB FF LK A E SCR spc olo ohi ocell own F fl k LK2 M2 model2 cr BX0).
    { refine (PMAUK.GCTX L ar HI LB FF LK A E SCR spc olo ohi ocell own F fl k LK2 M2 model2 cr BX0
               Hk6 SPT SLO SHI _ OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNCl HH2 FLC _ _ FBIG F32 FLA FLR FLBIG NCF NCS).
      - clear - SLO SHI SPT SPSC SPO1 SPO2 SPO3; lia.
      - clear - FR; lia.
      - split; [exact F8| exact (proj2 BQ)]. }
    apply (KONT R2 M2 model2 F fl LK2 G B10 RP2 (conj Hh2 MI2) RT2 ASTK2).
    + eapply ek_trans. exact EK01. intros a (Ha & Hc & _). apply (proj1 PRES2 a Ha).
      apply (aclient_mono L ar (BX0 ++ LB) FF E SCR spc 512 a (aclient_appb L ar LB BX0 FF E SCR a Hc)). intros x Hx. clear - Hx SPSC SPO1 SPO2 SPO3; lia.
    + eapply dk_trans. exact DK01. intros a Ha Hc Hn. rewrite (proj1 PRES2 a Ha). exact Hn.
      apply (aclient_mono L ar (BX0 ++ LB) FF E SCR spc 512 a (aclient_appb L ar LB BX0 FF E SCR a Hc)). intros x Hx. clear - Hx SPSC SPO1 SPO2 SPO3; lia.
    + intros a (Ha & Hc & _). apply (proj1 PRES2 a Ha).
      apply (aclient_mono L ar (BX0 ++ LB) FF E SCR spc 512 a Hc). intros x Hx. clear - Hx SPSC SPO1 SPO2 SPO3; lia.
    + intros a Ha Hc Hn. rewrite (proj1 PRES2 a Ha). exact Hn.
      apply (aclient_mono L ar (BX0 ++ LB) FF E SCR spc 512 a Hc). intros x Hx. clear - Hx SPSC SPO1 SPO2 SPO3; lia.
    + exact AGF.
    + exact FWv.
    + exact FSHW.
    + exact FSHZ.
    + exact FLCv.
    + exact FLWv.
    + exact FDEFv.
    + exact VF.
    + exact VSH.
    + exact VFL.
    + intros a n sp0 scr0 Hc Hn.
      exact (sm_apart L ar C HI LYa HIok (BX0 ++ LB) FF LK2 cr A M2 _ F k (spc + 32) fl sp0 scr0 a n HH2 SPT Hk6 ltac:(clear - FR; lia) FCEIL FAPP FAL FAPART FBLK FLNC Hc Hn).
Qed.

(* [comment removed for export] *)
Lemma wret_ek LB FF LK A sp SCR spc olo ohi ocell own F fl k LK2 M2 model2 cr2 BX0 LB6 LK6 cr6 A6 (Mx Mf : word -> option byte) V6
      (W : list L5.range) (Wx : Z -> Prop) :
  PMAUK.gctx L ar HI LB FF LK A sp SCR spc olo ohi ocell own F fl k LK2 M2 model2 cr2 BX0 ->
  ri_inv HI LB6 ((F, k, spc + 32) :: FF) LK6 cr6 A6 Mx V6 ->
  (forall a, Wx a -> ~ L5.outside W a) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ PMAUK.WretX F fl k Wx a -> Mf (Z_to_bv 64 a) = Mx (Z_to_bv 64 a)) ->
  L5SAR.ek L ar LB6 FF 0 0 W Mx Mf.
Proof.
  intros G HH6 WXin FZ. pose proof G as G'. destruct G' as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG F32 FLA FLR FLBIG NCF NCS].
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH6) as (WB & WF & FSAPP & FSCEIL & _).
  unfold app_mem, FS_BYTES, BIGSHADOW_LO, BIGSHADOW_HI in FSAPP, FSCEIL.
  assert (FB8 : (F + ff_bytes k - 1) / 8 = F / 8 + ff_bytes k / 8 - 1 /\ ff_bytes k / 8 * 8 = ff_bytes k) by (split; [exact (proj1 (proj2 F8)) | exact (proj2 (proj2 F8))]).
  apply (ek_piece L ar LB6 FF 0 0 W Mx Mf (PMAUK.WretX F fl k Wx) FZ).
  intros a Ha Hc Ho [Wa|Wa]; [| exact (WXin a Wa Ho)].
  (* [comment removed for export] *)
  assert (IND : forall BS ST, aclient_g BS ST L ar LB6 FF 0 0 a -> in_block LB6 a \/ (hl_img_lo L <= a < hl_img_hi L) \/ (exists b, In b LB6 /\ BS (fst b) (snd b) a)
                  \/ aclient L ar LB FF sp SCR a).
  { intros BS ST X. destruct X as [X|[X|[X|[X|[X|[X|X]]]]]].
    - left; exact X.
    - right; right; right. unfold aclient, aclient_g. right; left. split; [exact (proj1 X)|]. intros Y. destruct Wa as [[Y1|Y1]|Y1].
      + clear - Y1 FCEIL X FR. lia.
      + clear - Y1 FR F8 X SPT. unfold SB in *. pose proof (Z.div_le_mono F (2 ^ 47) 8 ltac:(lia) ltac:(lia)) as D. change (2 ^ 47 / 8) with 17592186044416 in D. lia.
      + subst a. clear - FLR X. lia.
    - right; left. exact (proj1 X).
    - right; right; right. unfold aclient, aclient_g. do 3 right; left. exact X.
    - right; right; right. unfold aclient, aclient_g. do 4 right; left. exact X.
    - right; right; right. unfold aclient, aclient_g. do 5 right; left. exact X.
    - right; right; left. exact X. }
  destruct (IND _ _ Hc) as [X|[X|[X|X]]].
  - (* [comment removed for export] *)
    destruct X as (b & Hb & Xb). destruct (WB b Hb) as ((B0 & B1 & B2 & B3 & B4 & B5) & _ & _ & _ & _ & FA & BFS).
    unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in B5. destruct Wa as [[Y|Y]|Y].
    + destruct (FA (F, k, spc + 32) (or_introl eq_refl)) as [Z|Z]; cbn [ff_addr ff_class fst snd] in Z; clear - Y Z Xb FR; lia.
    + destruct B5 as (_ & B5 & _). clear - Y Xb B5 FR F8. unfold SB in *.
      pose proof (Z.div_le_mono F (2 ^ 47) 8 ltac:(lia) ltac:(lia)) as D. change (2 ^ 47 / 8) with 17592186044416 in D.
      pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)). lia.
    + subst a. unfold FS_BYTES in BFS, FLP. clear - Xb BFS FLP. lia.
  - rewrite (aly_img_lo L C LYa), (aly_img_hi L C LYa) in X. destruct Wa as [[Y|Y]|Y].
    + clear - X Y FR; lia.
    + clear - X Y FR. unfold SB in *. pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)). lia.
    + subst a. clear - X FLR; lia.
  - (* [comment removed for export] *)
    destruct X as (b & Hb & Xb). destruct (WB b Hb) as ((B0 & B1 & B2 & B3 & B4 & B5) & _ & _ & _ & _ & FA & BFS).
    unfold in_shadow_of, S in Xb. destruct Wa as [[Y|Y]|Y].
    + destruct FBIG as [Z|Z]; unfold SB in Xb.
      * pose proof (Z.div_le_mono (fst b + snd b - 1) (2 ^ 47 - 8388608) 8 ltac:(clear - B0 B3; lia) ltac:(clear - B4 SPT; lia)) as D. change ((2 ^ 47 - 8388608) / 8) with 17592184995840 in D. clear - Y Z Xb D; lia.
      * pose proof (Z.div_pos (fst b) 8 ltac:(clear - B0; lia) ltac:(lia)) as D. clear - Y Z Xb D FR; lia.
    + destruct (FA (F, k, spc + 32) (or_introl eq_refl)) as [Z|Z]; cbn [ff_addr ff_class fst snd] in Z.
      * assert (E1 : (F - 1) / 8 = F / 8 - 1).
        { rewrite <- (proj1 F8) at 1. replace (F / 8 * 8 - 1) with (7 + (F / 8 - 1) * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
        pose proof (Z.div_le_mono (fst b + snd b - 1) (F - 1) 8 ltac:(lia) ltac:(clear - Z; lia)) as D. rewrite E1 in D.
        clear - Y Xb D. unfold SB in *. lia.
      * assert (E1 : (F + ff_bytes k) / 8 = F / 8 + ff_bytes k / 8).
        { rewrite <- (proj1 F8) at 1. rewrite <- (proj2 FB8) at 1. replace (F / 8 * 8 + ff_bytes k / 8 * 8) with ((F / 8 + ff_bytes k / 8) * 8) by lia.
          rewrite Z.div_mul by lia. reflexivity. }
        pose proof (Z.div_le_mono (F + ff_bytes k) (fst b) 8 ltac:(lia) ltac:(clear - Z; lia)) as D. rewrite E1 in D.
        clear - Y Xb D FB8. unfold SB in *. lia.
    + subst a. destruct FLBIG as [Z|Z]; unfold SB in Xb.
      * pose proof (Z.div_le_mono (fst b + snd b - 1) (2 ^ 47 - 8388608) 8 ltac:(clear - B0 B3; lia) ltac:(clear - B4 SPT; lia)) as D. change ((2 ^ 47 - 8388608) / 8) with 17592184995840 in D. clear - Z Xb D; lia.
      * pose proof (Z.div_pos (fst b) 8 ltac:(clear - B0; lia) ltac:(lia)) as D. clear - Z Xb D; lia.
  - destruct Wa as [[Y|Y]|Y].
    + apply (NCF a); [left; clear - Y FR; lia| exact X].
    + apply (NCF a); [right; unfold S; rewrite (proj1 FB8); unfold SB in *; clear - Y; lia| exact X].
    + subst a. apply FLNC. apply aclient_cons. eapply aclient_00. exact X.
Qed.

(* [comment removed for export] *)
Definition Wfr (F fl k : Z) (Wx : Z -> Prop) (a : Z) : Prop := ((F <= a < F + ff_bytes k \/ F / 8 + SB <= a < F / 8 + SB + ff_bytes k / 8) \/ a = fl) \/ Wx a.
Lemma wfr_ek LB FF LK A sp SCR spc olo ohi ocell own F fl k LK2 M2 model2 cr2 BX0 LB6 LK6 cr6 A6 (Mx Mf : word -> option byte) V6
      (W : list L5.range) (Wx : Z -> Prop) :
  PMAUK.gctx L ar HI LB FF LK A sp SCR spc olo ohi ocell own F fl k LK2 M2 model2 cr2 BX0 ->
  ri_inv HI LB6 ((F, k, spc + 32) :: FF) LK6 cr6 A6 Mx V6 ->
  (forall a, Wx a -> ~ L5.outside W a) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Wfr F fl k Wx a -> Mf (Z_to_bv 64 a) = Mx (Z_to_bv 64 a)) ->
  L5SAR.ek L ar LB6 FF 0 0 W Mx Mf.
Proof.
  intros G HH6 WXin FZ. pose proof G as G'. destruct G' as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG F32 FLA FLR FLBIG NCF NCS].
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH6) as (WB & WF & FSAPP & FSCEIL & _).
  unfold app_mem, FS_BYTES, BIGSHADOW_LO, BIGSHADOW_HI in FSAPP, FSCEIL.
  assert (FB8 : (F + ff_bytes k - 1) / 8 = F / 8 + ff_bytes k / 8 - 1 /\ ff_bytes k / 8 * 8 = ff_bytes k) by (split; [exact (proj1 (proj2 F8)) | exact (proj2 (proj2 F8))]).
  apply (ek_piece L ar LB6 FF 0 0 W Mx Mf (Wfr F fl k Wx) FZ).
  intros a Ha Hc Ho [Wa|Wa]; [| exact (WXin a Wa Ho)].
  (* [comment removed for export] *)
  assert (IND : forall BS ST, aclient_g BS ST L ar LB6 FF 0 0 a -> in_block LB6 a \/ (hl_img_lo L <= a < hl_img_hi L) \/ (exists b, In b LB6 /\ BS (fst b) (snd b) a)
                  \/ aclient L ar LB FF sp SCR a).
  { intros BS ST X. destruct X as [X|[X|[X|[X|[X|[X|X]]]]]].
    - left; exact X.
    - right; right; right. unfold aclient, aclient_g. right; left. split; [exact (proj1 X)|]. intros Y. destruct Wa as [[Y1|Y1]|Y1].
      + clear - Y1 FCEIL X FR. lia.
      + clear - Y1 FR F8 X SPT. unfold SB in *. pose proof (Z.div_le_mono F (2 ^ 47) 8 ltac:(lia) ltac:(lia)) as D. change (2 ^ 47 / 8) with 17592186044416 in D. lia.
      + subst a. clear - FLR X. lia.
    - right; left. exact (proj1 X).
    - right; right; right. unfold aclient, aclient_g. do 3 right; left. exact X.
    - right; right; right. unfold aclient, aclient_g. do 4 right; left. exact X.
    - right; right; right. unfold aclient, aclient_g. do 5 right; left. exact X.
    - right; right; left. exact X. }
  destruct (IND _ _ Hc) as [X|[X|[X|X]]].
  - (* [comment removed for export] *)
    destruct X as (b & Hb & Xb). destruct (WB b Hb) as ((B0 & B1 & B2 & B3 & B4 & B5) & _ & _ & _ & _ & FA & BFS).
    unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in B5. destruct Wa as [[Y|Y]|Y].
    + destruct (FA (F, k, spc + 32) (or_introl eq_refl)) as [Z|Z]; cbn [ff_addr ff_class fst snd] in Z; clear - Y Z Xb FR; lia.
    + destruct B5 as (_ & B5 & _). clear - Y Xb B5 FR F8. unfold SB in *.
      pose proof (Z.div_le_mono F (2 ^ 47) 8 ltac:(lia) ltac:(lia)) as D. change (2 ^ 47 / 8) with 17592186044416 in D.
      pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)). lia.
    + subst a. unfold FS_BYTES in BFS, FLP. clear - Xb BFS FLP. lia.
  - rewrite (aly_img_lo L C LYa), (aly_img_hi L C LYa) in X. destruct Wa as [[Y|Y]|Y].
    + clear - X Y FR; lia.
    + clear - X Y FR. unfold SB in *. pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)). lia.
    + subst a. clear - X FLR; lia.
  - (* [comment removed for export] *)
    destruct X as (b & Hb & Xb). destruct (WB b Hb) as ((B0 & B1 & B2 & B3 & B4 & B5) & _ & _ & _ & _ & FA & BFS).
    unfold in_shadow_of, S in Xb. destruct Wa as [[Y|Y]|Y].
    + destruct FBIG as [Z|Z]; unfold SB in Xb.
      * pose proof (Z.div_le_mono (fst b + snd b - 1) (2 ^ 47 - 8388608) 8 ltac:(clear - B0 B3; lia) ltac:(clear - B4 SPT; lia)) as D. change ((2 ^ 47 - 8388608) / 8) with 17592184995840 in D. clear - Y Z Xb D; lia.
      * pose proof (Z.div_pos (fst b) 8 ltac:(clear - B0; lia) ltac:(lia)) as D. clear - Y Z Xb D FR; lia.
    + destruct (FA (F, k, spc + 32) (or_introl eq_refl)) as [Z|Z]; cbn [ff_addr ff_class fst snd] in Z.
      * assert (E1 : (F - 1) / 8 = F / 8 - 1).
        { rewrite <- (proj1 F8) at 1. replace (F / 8 * 8 - 1) with (7 + (F / 8 - 1) * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
        pose proof (Z.div_le_mono (fst b + snd b - 1) (F - 1) 8 ltac:(lia) ltac:(clear - Z; lia)) as D. rewrite E1 in D.
        clear - Y Xb D. unfold SB in *. lia.
      * assert (E1 : (F + ff_bytes k) / 8 = F / 8 + ff_bytes k / 8).
        { rewrite <- (proj1 F8) at 1. rewrite <- (proj2 FB8) at 1. replace (F / 8 * 8 + ff_bytes k / 8 * 8) with ((F / 8 + ff_bytes k / 8) * 8) by lia.
          rewrite Z.div_mul by lia. reflexivity. }
        pose proof (Z.div_le_mono (F + ff_bytes k) (fst b) 8 ltac:(lia) ltac:(clear - Z; lia)) as D. rewrite E1 in D.
        clear - Y Xb D FB8. unfold SB in *. lia.
    + subst a. destruct FLBIG as [Z|Z]; unfold SB in Xb.
      * pose proof (Z.div_le_mono (fst b + snd b - 1) (2 ^ 47 - 8388608) 8 ltac:(clear - B0 B3; lia) ltac:(clear - B4 SPT; lia)) as D. change ((2 ^ 47 - 8388608) / 8) with 17592184995840 in D. clear - Z Xb D; lia.
      * pose proof (Z.div_pos (fst b) 8 ltac:(clear - B0; lia) ltac:(lia)) as D. clear - Z Xb D; lia.
  - destruct Wa as [[Y|Y]|Y].
    + apply (NCF a); [left; clear - Y FR; lia| exact X].
    + apply (NCF a); [right; unfold S; rewrite (proj1 FB8); unfold SB in *; clear - Y; lia| exact X].
    + subst a. apply FLNC. apply aclient_cons. eapply aclient_00. exact X.
Qed.

(* [comment removed for export] *)
Lemma ahpres_of_frame_but LB FF LK cr A M M' V sp scr :
  ri_inv HI LB FF LK cr A M V -> 140735340871680 <= ar_sptop ar <= 2 ^ 47 -> ahl_ceil ar <= sp - scr -> 0 <= scr ->
  L5.frame_but [(sp - scr, scr)] M M' -> mem_grows M M' -> L5.defined M (sp - scr) scr ->
  ahpres L ar LB FF sp scr [] M M'.
Proof.
  intros HH SPT HC HS FB MG D. split; [|split].
  - intros a (Ha & Hc & _). apply FB. rewrite L5.unsigned_lit by lia.
    destruct (aclient_cases L ar C HI LYa HIok LB FF LK cr A M V sp scr a HH SPT Hc) as [(Y1 & Y2)|Y].
    + intros r0 [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. apply Y2. lia.
    + intros r0 [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. lia.
  - apply (L5.defined_grows M M' _ _ MG D).
  - intros a Ha Hc Hn. exact (MG _ Hn).
Qed.
End WithIface.
End SCFG_1.
End PMAUAR.
