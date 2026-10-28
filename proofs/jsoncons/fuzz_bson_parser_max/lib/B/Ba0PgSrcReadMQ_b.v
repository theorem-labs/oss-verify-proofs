(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnASrcKit_b PgSrcKitA_b PnASrcRead1_b PnASrcReadK_b PnASrcReadP_b Ba0PgSrcReadK_b Ba0PgSrcReadC_b Ba0PgSrcReadMB_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.LeanFeed.
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b L5StepAR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmModelFacts PmStatics PmStaticsA PmSpecs PmParSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PmSpecsAX_b PnSpecsAa_b
     PmModelFactsA_b PnStepA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PmParStep. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnASrcKit_b PnASrcReadK_b PnASrcRead1_b PnASrcReadP_b Ba0_code_raf314_af318_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgSrc. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgSrcA_b PgSrcKitA_b PnRunA_b PmAUarK_b PmAUar_b PnAReadCsK_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := first [ L5FastLia.plia | Lia.lia ].

Module PGSRDMQ.
Abbreviation RSEGS := PGSRDK.RSEGS.
Abbreviation mem := (word -> option byte).
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).

Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).

Definition srd_beqX (V : nat -> Z) (R : bvmap 5 word) (M : mem) : Prop :=
  (0 <= (V 33%nat) < 2 ^ 64)
  /\ (getr R (reg 22) = Z_to_bv 64 (V 39%nat))
  /\ (L5.u64_at RSEGS M ((V 36%nat) + 288) (V 33%nat))
  /\ (1 <= (V 33%nat) <= 16384)
  /\ (1 <= (V 39%nat) <= 16384)
  /\ (0 <= ((V 33%nat) - (V 39%nat)) <= 16383).

Definition srd_beq_T (al : Z) : Prop :=
  forall (O : PGS.owner) (R0 : bvmap 5 word) (M0 : mem) (model0 : Model) (K : TSet) (OB LBX : list (Z * Z))
         (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r : Z) (str : PM.vstr) (Wextra : list L5.range)
         (qc de rem g eg sst p k : Z),
    PGSRDK.srd_ctx L ar HI al O R0 M0 model0 K OB LBX FF LK Aw cr sp r (PM.SRC qc de rem) str (PM.STRM g eg sst) Wextra ->
    getr R0 (reg 11) = Z_to_bv 64 p -> getr R0 (reg 12) = Z_to_bv 64 k ->
    forall (F fl : Z) (LK2 : list fframe) (M2 : mem) (model2 : Model),
    PGSRDK.srd_frame L ar HI al R0 OB LBX FF LK Aw cr sp (PM.SRC qc de rem) F fl LK2 M2 model2 ->
    forall (fx : FPState) (R : bvmap 5 word) (M : mem) (model : Model) (LKc : list fframe) (Ac : list (Z * Z))
           (V : nat -> Z),
    PGSRDK.srd_body L ar HI al O R0 M0 model0 OB LBX FF LK Aw sp (PM.SRC qc de rem) Wextra F M model LKc cr Ac ->
    V 2%nat = sp - al -> V 36%nat = PGS.ow_os O -> V 37%nat = p -> V 38%nat = k -> 32 * V 50%nat = F -> V 51%nat = fl ->
    (forall i, In i [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> V i = bv_unsigned (getr R0 (reg i))) ->
    getr R (reg 3) = getr R0 (reg 3) -> getr R (reg 4) = getr R0 (reg 4) ->
    forall (len1 : Z),
    PGSRDMB.srd_stM V R (mrestrict (ahid Ac model) M) -> srd_beqX V R (mrestrict (ahid Ac model) M) ->
    V 39%nat = len1 -> V 33%nat = rem -> V 34%nat = qc -> V 35%nat = de -> V 45%nat = PGS.ow_ois O ->
    PGS.ow_at O M (PM.SRC qc de rem) OB -> PM.iss_at RSEGS PMA.AD PMSPA.accA M (PGS.ow_ois O) str (PM.STRM g eg sst) ->
    PMSTA.base_okA RSEGS PMA.AD M -> len1 = k -> len1 <= rem -> L5.defined M p len1 ->
    srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0xaeed4 M model) K.

End WithHeap.

Section Beq.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Variable IL : icpt_layout.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Ltac pdestr PP := repeat match type of PP with _ /\ _ => let H := fresh "S" in destruct PP as (H & PP) end.

Lemma srd_beq_ok : PGSRDK.srd_exit_T L ar HI 0 -> srd_beq_T L ar HI 0.
Proof using All.
  intros EXIT. unfold srd_beq_T.
  intros O R0 M0 model0 K OB LBX FF LK Aw cr sp r str Wextra qc de rem g eg sst p k CTX R11 R12 F fl LK2 M2 model2 FR
         fx R M model LKc Ac V BI V2 V36 V37 V38 V50 V51 VSV X3 X4 len1 STM BQX V39 V33 V34 V35 V45 PA IA BASE Hlk Hlr DP.
  pose proof CTX as (OK & HH & AM & K0 & ENT & FRM & FRS & OFR & A10 & SP32 & ARGS & WX & PA0 & IA0 & BASE0 & INCS & KONT).
  destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH).
  pose proof (PGSA.oo_lay _ _ _ _ _ _ OK) as (LY1 & LY2 & LY3 & LY4 & LY5 & O8 & I8 & LY6 & LYD).
  pose proof (PGSA.oo_src _ _ _ _ _ _ OK M0 _ OB PA0) as (PSRC & PNI & SDEF0).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & _).
  pose proof (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as FRB.
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  set (os := PGS.ow_os O) in *. set (ois := PGS.ow_ois O) in *. set (lo := PGS.ow_lo O) in *. set (hi := PGS.ow_hi O) in *.
  set (LB := PM.src_own (PM.SRC qc de rem) ++ OB ++ LBX) in *.
  assert (AO : PMSPA.aobjA FF os 296) by (apply (PGSKA.aobjA_sub FF lo hi); [exact OFR| exact LY1| exact LY2]).
  assert (AOI : PMSPA.aobjA FF ois 272) by (apply (PGSKA.aobjA_sub FF lo hi); [exact OFR| exact LY3| exact LY4]).
  pose proof (PGSKA.src_visG L ar C HI LY HIok LB FF LK cr Aw M0 model0 os _ _ _ sp (PMSPA.pm_scr 4) HH AO O8 PSRC PNI ASTK)
    as ((O1 & _ & OBIG) & _ & _ & OCE & _ & _ & OFS1 & OFS2).
  pose proof (PGSKA.iss_visG L ar C HI LY HIok LB FF LK cr Aw M0 model0 ois str _ sp (PMSPA.pm_scr 4) HH AOI I8 IA0 ASTK)
    as ((I1 & _ & IBIG) & _ & _ & ICE & _ & _).
  cbn [PM.sr_qc PM.sr_de PM.sr_rem PM.sm_g PM.sm_eg PM.sm_st] in *.
  assert (SOWN : incl (PM.vs_own str) LB) by (unfold LB; intros x Hx; apply in_or_app; right; apply in_or_app; right; exact (INCS x Hx)).
  assert (STb : forall c1 n1 q1, str = PM.VLong c1 n1 q1 -> In (q1, c1) LB).
  { intros c1 n1 q1 E. apply SOWN. rewrite E. cbn. left. reflexivity. }
  assert (ISSC : forall (M' : mem) (W : list L5.range), L5SAR.ek L ar LB FF sp (PMSPA.pm_scr 4) W M M' -> PMKA.wapp W ->
      (forall a, ois <= a < ois + 272 -> L5.outside W a) ->
      (forall c1 n1 q1, str = PM.VLong c1 n1 q1 -> forall a, q1 <= a < q1 + c1 -> L5.outside W a) ->
      forall sm0, PM.iss_at RSEGS PMA.AD PMSPA.accA M ois str sm0 -> PM.iss_at RSEGS PMA.AD PMSPA.accA M' ois str sm0).
  { intros M' W E WP OI OS sm0 IS.
    apply (PMFA.iss_at_agreeA RSEGS PMA.AD M M' ois str sm0); [clear - I1; lia| clear - I1; lia| split| | exact IS].
    - intros i Hi. apply E. split; [clear - Hi I1; lia|].
      split; [apply PMASR1.cl_of_bf; right; exact (PMASR1.in_fframe_of_aobjA FF ois 272 i AOI Hi)| exact (OI i Hi)].
    - exact (PMKA.agsh_obj L ar LB FF sp (PMSPA.pm_scr 4) W M M' E WP FRB ois 272 AOI).
    - intros c1 n1 q1 Es. pose proof (STb c1 n1 q1 Es) as TIN. destruct (WB _ TIN) as ((T0 & _ & _ & _ & T4 & _) & _).
      cbn [fst snd] in T0, T4. split.
      + intros i Hi. apply E. split; [clear - Hi T0 T4 SLO SHI SPT; lia|].
        split; [apply PMASR1.cl_of_bf; left; exact (PMASR1.in_block_of LB q1 c1 i TIN Hi)| exact (OS c1 n1 q1 Es i Hi)].
      + apply (PMASK.agsh_blk L ar LB FF sp (PMSPA.pm_scr 4) W M M' q1 c1 E WP TIN); clear - T0 T4 SLO SHI SPT; lia. }
  assert (WOS : PMKA.wapp [(PGS.ow_os O + 256, 40)]).
  { apply PMKA.wapp_cons; [cbn [fst snd]; clear - OBIG; unfold BIGSHADOW_LO, BIGSHADOW_HI in *; lia| apply PMKA.wapp_nil]. }
  assert (OI_os : forall a, ois <= a < ois + 272 -> L5.outside [(PGS.ow_os O + 256, 40)] a).
  { intros a Ha r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. clear - Ha LYD. lia. }
  assert (OS_os : forall c1 n1 q1, str = PM.VLong c1 n1 q1 -> forall a, q1 <= a < q1 + c1 -> L5.outside [(PGS.ow_os O + 256, 40)] a).
  { intros c1 n1 q1 Es a Ha r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd].
    destruct (PMASK.blk_obj_apart L ar C HI HIok LB FF LK cr Aw M0 _ q1 c1 os 296 HH (STb c1 n1 q1 Es) AO) as [Z|Z]; clear - Ha Z; lia. }
  specialize (EXIT O R0 M0 model0 K OB LBX FF LK Aw cr sp r str Wextra qc de rem g eg sst p k CTX R11 R12 F fl LK2 M2 model2 FR).
  pose proof (PGSA.oo_src _ _ _ _ _ _ OK M _ OB PA) as (PSRC1 & _ & _).
  pose proof PSRC1 as (_ & _ & _ & F264 & F272 & _ & _ & Hqd & Hr0 & Hdr & _). cbn [PM.sr_qc PM.sr_de PM.sr_rem] in F264, Hqd, Hr0, Hdr.
  set (MV := mrestrict (ahid Ac model) M) in *.
  unfold PGSRDMB.srd_stM in STM. pdestr STM. destruct BQX as (B33 & B22 & B288 & B33c & B39c & B3339).
  match goal with
  | H2 : _ <= V 2%nat <= _, H36 : _ <= V 36%nat <= _, H50 : _ <= V 50%nat <= _, H51 : 4096 <= V 51%nat <= _ |- _ =>
      pose proof (conj H2 (conj H36 (conj H50 H51))) as KB
  end.
  LeanFeed.pfeed P0 (PMASRP.asrBeq_conc fx R MV V)
    ltac:(first [assumption | (unfold PMASRP.aligned; assumption)]).
  destruct P0 as (fx1 & R1 & M1v & MG1 & _ & AG1 & MS1 & KS1 & Q1 & Q2 & Q8 & Q9 & Q10 & Q12 & Q18 & Q19 & Q20 & Q21 & Q22 & Q23 & Q24 & P288 & P280).
  apply (PGSRDC.srd_piece L ar C HI LY HIok O R0 M0 model0 K OB LBX FF LK Aw cr sp r (PM.SRC qc de rem) str (PM.STRM g eg sst) Wextra F fl LK2 M2 model2 M model LKc Ac
           fx fx1 R R1 _ _ M1v (fun a => V 36%nat + 256 <= a < V 36%nat + 256 + 8 \/ V 36%nat + 280 <= a < V 36%nat + 280 + 16) CTX FR BI MS1 MG1
           (fun a Ha N => AG1 a Ha (fun X => N (or_introl X)) (fun X => N (or_intror X)))).
  { intros a Wa. cbn beta in Wa. right; right; left. clear - Wa V36. lia. }
  intros M1 model1 BI1 HID1 MRT1 MGM1 FR1 VIS1 EK1.
  assert (SV1 : forall i, In i [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> PGSRDC.vx V R1 i = bv_unsigned (getr R0 (reg i))).
  { intros i Hi. rewrite <- (VSV i Hi). cbn in Hi. repeat destruct Hi as [<-|Hi]; first [reflexivity | destruct Hi]. }
  assert (X3' : getr R1 (reg 3) = getr R0 (reg 3)) by (rewrite KS1 by inl; exact X3).
  assert (X4' : getr R1 (reg 4) = getr R0 (reg 4)) by (rewrite KS1 by inl; exact X4).
  assert (STR1 : PGSRDK.srd_stR (PGSRDC.vx V R1) R1 M1v).
  { unfold PGSRDK.srd_stR, PGSRDC.vx. cbn beta iota.
    PGSRDC.sweep ltac:(first [assumption | exact (bv_unsigned_in_range _ _) | (symmetry; apply Z_to_bv_bv_unsigned)
                      | (rewrite KS1 by inl; assumption) | (eapply L5.writable_grows; [exact MG1| assumption])
                      | (eapply L5.defined_grows; [exact MG1| assumption]) | PGSRDC.carry MV AG1 KB]). }
  assert (STR1' : PGSRDK.srd_stR (PGSRDC.vx V R1) R1 (mrestrict (ahid Ac model1) M1)) by (rewrite HID1, MRT1; exact STR1).
  assert (V76 : PGSRDC.vx V R1 76%nat = len1).
  { unfold PGSRDC.vx. cbn beta iota. rewrite Q22, L5.unsigned_lit; [exact V39| assumption]. }
  assert (U264 : L5.u64_at RSEGS M1 (os + 264) qc).
  { apply (L5C.u64_at_agree RSEGS M M1); [| clear - O1; lia| clear - O1; lia| exact F264].
    intros i Hi. apply FR1; [clear - Hi O1; lia|]. cbn beta. clear - Hi V36. lia. }
  assert (U272 : L5.u64_at RSEGS M1 (os + 272) PM.CHUNK).
  { apply (L5C.u64_at_agree RSEGS M M1); [| clear - O1; lia| clear - O1; lia| exact F272].
    intros i Hi. apply FR1; [clear - Hi O1; lia|]. cbn beta. clear - Hi V36. lia. }
  assert (VO1 : forall i, V 36%nat + 280 <= i < V 36%nat + 296 -> M1 (Z_to_bv 64 i) = M1v (Z_to_bv 64 i)).
  { intros i Hi. apply VIS1.
    apply (PGSRDC.srd_vis L ar C HI LY HIok O R0 M0 model0 K OB LBX FF LK Aw cr sp r (PM.SRC qc de rem) str (PM.STRM g eg sst) Wextra F fl LK2 M2 model2 M model LKc Ac i CTX FR BI).
    right; right; right; left. clear - Hi V36. lia. }
  assert (U280 : L5.u64_at RSEGS M1 (os + 280) (de + len1)).
  { rewrite <- V35, <- V39. replace (os + 280) with (V 36%nat + 280) by (clear - V36; lia).
    apply (L5C.u64_at_agree RSEGS M1v M1); [| PGSRDC.sd KB| PGSRDC.sd KB| exact P280]. intros i Hi. apply VO1. clear - Hi. lia. }
  assert (U288 : L5.u64_at RSEGS M1 (os + 288) (rem - len1)).
  { rewrite <- V33, <- V39. replace (os + 288) with (V 36%nat + 288) by (clear - V36; lia).
    apply (L5C.u64_at_agree RSEGS M1v M1); [| PGSRDC.sd KB| PGSRDC.sd KB| exact P288]. intros i Hi. apply VO1. clear - Hi. lia. }
  assert (ISS1 : PM.iss_at RSEGS PMA.AD PMSPA.accA M1 ois str (PM.STRM g eg sst)) by exact (ISSC M1 _ EK1 WOS OI_os OS_os _ IA).
  assert (DEF1 : L5.defined M1 p len1) by (eapply L5.defined_grows; [exact MGM1| exact DP]).
  assert (L1 : 1 <= len1) by (rewrite <- V39; exact (proj1 B39c)).
  assert (A0 : qc <= de + len1) by (clear - Hqd L1; lia).
  assert (A1 : 0 <= rem - len1) by (clear - Hlr; lia).
  assert (A2 : de + len1 + (rem - len1) <= qc + PM.CHUNK) by (clear - Hdr; lia).
  assert (A3 : g <= g <= eg) by (pose proof IA as GE; unfold PM.iss_at in GE; pdestr GE; cbn [PM.sm_g PM.sm_eg] in GE; clear - GE; lia).
  assert (A4 : 0 <= len1 <= k) by (clear - L1 Hlk; lia).
  assert (A5 : rem + (eg - g) - (rem - len1 + (eg - g)) = len1) by (clear; lia).
  assert (A6 : 1 <= rem -> 1 <= len1) by (intros _; exact L1).
  assert (A7 : len1 = 0 -> rem - len1 = 0 /\ sst = 2) by (intros Z0; exfalso; clear - Z0 L1; lia).
  exact (EXIT fx1 R1 M1 model1 LKc Ac (PGSRDC.vx V R1) BI1 V2 V36 V37 V38 V50 V51 SV1 X3' X4' (de + len1) (rem - len1) g sst len1 STR1' V76 U264 U272 U280 U288
           A0 A1 A2 ISS1 A3 (fun H => H) A4 A5 A6 A7 DEF1).
Qed.

End Beq.

End PGSRDMQ.
