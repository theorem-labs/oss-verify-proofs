(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.LeanFeed.
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b L5StepAR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmModelFacts PmStatics PmStaticsA PmSpecs PmParSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PmSpecsAX_b PnSpecsAa_b
     PmModelFactsA_b PnStepA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PmParStep. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnASrcKit_b PnASrcReadK_b PnASrcRead1_b PnASrcReadP_b Ba0_code_raf314_af318_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgSrc. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgSrcA_b PgSrcKitA_b PnRunA_b PmAUarK_b PmAUar_b PnAReadCsK_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0PgSrcReadK_b Ba0PgSrcReadC_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := first [ L5FastLia.plia | Lia.lia ].

Module PGSRDA0E.
Abbreviation RSEGS := PGSRDK.RSEGS.
Abbreviation mem := (word -> option byte).
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).

Definition srd_pA0e (V : nat -> Z) (R : bvmap 5 word) (M : mem) : Prop :=
  (0 <= (V 45%nat) < 2 ^ 64)
  /\ (L5.u64_at RSEGS M ((V 36%nat) + 288) 0)
  /\ (6905856 <= (V 45%nat) <= 140737488355056)
  /\ ((V 45%nat) mod 8 = 0)
  /\ ((2147446784 + 17592186048512 <= (V 45%nat) \/ (V 45%nat) + 272 <= 2147446784))
  /\ (L5KA.zeros_at M (((V 45%nat) / 8) + 2147450880) 34)
  /\ (L5.writable RSEGS M (V 45%nat) 272)
  /\ ((((V 2%nat) - 160) + 160 <= (V 45%nat) \/ (V 45%nat) + 272 <= ((V 2%nat) - 160)))
  /\ (((V 36%nat) + 296 <= (V 45%nat) \/ (V 45%nat) + 272 <= (V 36%nat)))
  /\ (L5.u64_at RSEGS M ((V 36%nat) + 240) (V 45%nat))
  /\ (L5.u64_at RSEGS M ((V 36%nat) + 248) ((V 45%nat) + 16))
  /\ (L5.u64_at RSEGS M (V 45%nat) 1265968)
  /\ (L5.u64_at RSEGS M ((V 45%nat) + 16) 1265728)
  /\ (L5.u32_at RSEGS M ((V 45%nat) + 152) 2)
  /\ (L5.u32_at RSEGS M ((V 45%nat) + 156) 0)
  /\ (L5.u64_at RSEGS M ((V 45%nat) + 160) ((V 45%nat) + 16))
  /\ (L5KA.zeros_at M 2147609123 1)
  /\ (L5KA.zeros_at M 2147609104 1)
  /\ (16384 <= (V 38%nat) <= 16384)
  /\ (((32 * (V 50%nat)) + 128 <= (V 45%nat) \/ (V 45%nat) + 272 <= (32 * (V 50%nat))))
  /\ (((V 51%nat) + 1 <= (V 45%nat) \/ (V 45%nat) + 272 <= (V 51%nat)))
  /\ ((((4 * (V 50%nat)) + 2147450880) + 16 <= (V 45%nat) \/ (V 45%nat) + 272 <= ((4 * (V 50%nat)) + 2147450880)))
  /\ ((((4 * (V 50%nat)) + 2147450880) + 16 <= (((V 45%nat) / 8) + 2147450880) \/ (((V 45%nat) / 8) + 2147450880) + 34 <= ((4 * (V 50%nat)) + 2147450880)))
  /\ (((32 * (V 50%nat)) + 128 <= (((V 45%nat) / 8) + 2147450880) \/ (((V 45%nat) / 8) + 2147450880) + 34 <= (32 * (V 50%nat))))
  /\ (((V 51%nat) + 1 <= (((V 45%nat) / 8) + 2147450880) \/ (((V 45%nat) / 8) + 2147450880) + 34 <= (V 51%nat))).

Definition srd_pthE (V : nat -> Z) (R : bvmap 5 word) (M : mem) (rem sst : Z) : Prop :=
  rem = 0 /\ V 38%nat = PM.CHUNK /\ sst = 2 /\ srd_pA0e V R M.

Section A0e.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Variable IL : icpt_layout.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.

Lemma srd_a0e_ok : PGSRDK.srd_exit_T L ar HI 0 -> PGSRDK.srd_a0_T L ar HI 0 srd_pthE.
Proof using All.
  intros EXIT. unfold PGSRDK.srd_a0_T.
  intros O R0 M0 model0 K OB LBX FF LK Aw cr sp r str Wextra qc de rem g eg sst p k CTX R11 R12 F fl LK2 M2 model2 FR
         fx R M model LKc Ac V BI V2 V36 V37 V38 V50 V51 VSV X3 X4 V34 V35 V45 IA STA PTH.
  destruct PTH as (Hrem & H38 & Hsst & PA0E). subst rem sst.
  pose proof CTX as (OK & HH & AM & K0 & ENT & FRM & FRS & OFR & A10 & SP32 & ARGS & WX & PA0 & IA0 & BASE0 & INCS & KONT).
  destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH).
  pose proof (PGSA.oo_lay _ _ _ _ _ _ OK) as (LY1 & LY2 & LY3 & LY4 & LY5 & O8 & I8 & LY6 & LYD).
  pose proof (PGSA.oo_src _ _ _ _ _ _ OK M0 _ OB PA0) as (PSRC & PNI & SDEF0).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & _).
  pose proof (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as FRB.
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  set (os := PGS.ow_os O) in *. set (ois := PGS.ow_ois O) in *. set (lo := PGS.ow_lo O) in *. set (hi := PGS.ow_hi O) in *.
  set (LB := PM.src_own (PM.SRC qc de 0) ++ OB ++ LBX) in *.
  assert (AO : PMSPA.aobjA FF os 296) by (apply (PGSKA.aobjA_sub FF lo hi); [exact OFR| exact LY1| exact LY2]).
  assert (AOI : PMSPA.aobjA FF ois 272) by (apply (PGSKA.aobjA_sub FF lo hi); [exact OFR| exact LY3| exact LY4]).
  pose proof (PGSKA.src_visG L ar C HI LY HIok LB FF LK cr Aw M0 model0 os _ _ _ sp (PMSPA.pm_scr 4) HH AO O8 PSRC PNI ASTK)
    as ((O1 & _ & OBIG) & _ & _ & OCE & _ & _ & OFS1 & OFS2).
  pose proof (PGSKA.iss_visG L ar C HI LY HIok LB FF LK cr Aw M0 model0 ois str _ sp (PMSPA.pm_scr 4) HH AOI I8 IA0 ASTK)
    as ((I1 & _ & IBIG) & _ & _ & ICE & _ & _).
  cbn [PM.sr_qc PM.sr_de PM.sr_rem PM.sm_g PM.sm_eg PM.sm_st] in *.
  pose proof PSRC as (_ & _ & _ & _ & _ & _ & _ & G1 & G2 & G3 & _). cbn [PM.sr_qc PM.sr_de PM.sr_rem] in G1, G2, G3.
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
  specialize (EXIT O R0 M0 model0 K OB LBX FF LK Aw cr sp r str Wextra qc de 0 g eg 2 p k CTX R11 R12 F fl LK2 M2 model2 FR).
  set (MV := mrestrict (ahid Ac model) M) in *.
  unfold PGSRDK.srd_stA in STA. repeat match type of STA with _ /\ _ => let H := fresh "QS" in destruct STA as (H & STA) end.
  unfold srd_pA0e in PA0E. repeat match type of PA0E with _ /\ _ => let H := fresh "QE" in destruct PA0E as (H & PA0E) end.
  match goal with
  | H2 : _ <= V 2%nat <= _, H36 : _ <= V 36%nat <= _, H50 : _ <= V 50%nat <= _, H51 : 4096 <= V 51%nat <= _ |- _ =>
      pose proof (conj H2 (conj H36 (conj H50 H51))) as KB
  end.
  LeanFeed.pfeed P0 (PMASRP.asrA0e_conc fx R MV V)
    ltac:(first [assumption | (unfold PMASRP.aligned; assumption)]).
  destruct P0 as (fx1 & R1 & M1v & MG1 & _ & AG1 & MS1 & KS1 & PR10 & PR11 & PR12 & PR13 & PR14 & PR15 & PR16 & PR18 & PR20 & PR22 & PR23 & PR24
                  & PR25 & PR26 & P288 & P280 & PP).
  repeat match type of PP with _ /\ _ => let H := fresh "QP" in destruct PP as (H & PP) end.
  apply (PGSRDC.srd_piece L ar C HI LY HIok O R0 M0 model0 K OB LBX FF LK Aw cr sp r (PM.SRC qc de 0) str (PM.STRM g eg 2) Wextra F fl LK2 M2 model2
           M model LKc Ac fx fx1 R R1 _ _ M1v
           (fun a => (((V 2%nat) - 152) <= a < ((V 2%nat) - 152) + 16) \/ (((V 2%nat) - 112) <= a < ((V 2%nat) - 112) + 8)
                     \/ (((32 * (V 50%nat)) + 0) <= a < ((32 * (V 50%nat)) + 0) + 24) \/ (((32 * (V 50%nat)) + 32) <= a < ((32 * (V 50%nat)) + 32) + 8)
                     \/ (((4 * (V 50%nat)) + 2147450880) <= a < ((4 * (V 50%nat)) + 2147450880) + 12) \/ (((V 36%nat) + 280) <= a < ((V 36%nat) + 280) + 16))
           CTX FR BI MS1 MG1
           (fun a Ha N => AG1 a Ha (fun X => N (or_introl X)) (fun X => N (or_intror (or_introl X))) (fun X => N (or_intror (or_intror (or_introl X))))
                              (fun X => N (or_intror (or_intror (or_intror (or_introl X))))) (fun X => N (or_intror (or_intror (or_intror (or_intror (or_introl X))))))
                              (fun X => N (or_intror (or_intror (or_intror (or_intror (or_intror X)))))))).
  { intros a Wa. cbn beta in Wa. destruct Wa as [Y|[Y|[Y|[Y|[Y|Y]]]]].
    - right; right; right. clear - Y V2. lia.
    - right; right; right. clear - Y V2. lia.
    - left. clear - Y V50. lia.
    - left. clear - Y V50. lia.
    - right; left. unfold SB. clear - Y V50. lia.
    - right; right; left. clear - Y V36. lia. }
  intros M1 model1 BI1 HID1 MRT1 MGM1 FR1 VIS1 EK1.
  assert (SV1 : forall i, In i [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> PGSRDC.vx V R1 i = bv_unsigned (getr R0 (reg i))).
  { intros i Hi. rewrite <- (VSV i Hi). cbn in Hi. repeat destruct Hi as [<-|Hi]; first [reflexivity | destruct Hi]. }
  assert (X3' : getr R1 (reg 3) = getr R0 (reg 3)) by (rewrite KS1 by PGSRDC.inl; exact X3).
  assert (X4' : getr R1 (reg 4) = getr R0 (reg 4)) by (rewrite KS1 by PGSRDC.inl; exact X4).
  assert (V2s : V 2%nat = sp) by (clear - V2; lia).
  assert (OWV : forall a v, sp - 160 <= a -> a + 8 <= sp -> L5.u64_at RSEGS M1 a v -> L5.u64_at RSEGS M1v a v).
  { intros a v Ha Hb X. apply (L5C.u64_at_agree RSEGS M1 M1v a v); [| clear - Ha KB V2s; lia| clear - Hb KB V2s; lia| exact X].
    intros i Hi. symmetry. apply VIS1.
    apply (PGSRDC.srd_vis L ar C HI LY HIok O R0 M0 model0 K OB LBX FF LK Aw cr sp r _ str _ Wextra F fl LK2 M2 model2 M model LKc Ac i CTX FR BI).
    left. clear - Hi Ha Hb. lia. }
  pose proof BI1 as BI1u. unfold PGSRDK.srd_body in BI1u.
  pose proof BI1u as (_ & _ & _ & _ & _ & _ & _ & _ & OWN1 & _).
  destruct OWN1 as (W8 & W16 & W24 & W32 & W40 & W48 & W56 & W64 & W72 & W80 & W88 & W96 & W104).
  assert (B18 : 0 <= V 18%nat < 2 ^ 64) by (rewrite (VSV 18%nat) by PGSRDC.inl; exact (bv_unsigned_in_range _ _)).
  assert (B20 : 0 <= V 20%nat < 2 ^ 64) by (rewrite (VSV 20%nat) by PGSRDC.inl; exact (bv_unsigned_in_range _ _)).
  assert (B21 : 0 <= V 21%nat < 2 ^ 64) by (rewrite (VSV 21%nat) by PGSRDC.inl; exact (bv_unsigned_in_range _ _)).
  assert (B23 : 0 <= V 23%nat < 2 ^ 64) by (rewrite (VSV 23%nat) by PGSRDC.inl; exact (bv_unsigned_in_range _ _)).
  assert (B24 : 0 <= V 24%nat < 2 ^ 64) by (rewrite (VSV 24%nat) by PGSRDC.inl; exact (bv_unsigned_in_range _ _)).
  assert (B25 : 0 <= V 25%nat < 2 ^ 64) by (rewrite (VSV 25%nat) by PGSRDC.inl; exact (bv_unsigned_in_range _ _)).
  assert (B26 : 0 <= V 26%nat < 2 ^ 64) by (rewrite (VSV 26%nat) by PGSRDC.inl; exact (bv_unsigned_in_range _ _)).
  assert (S32 : L5.u64_at RSEGS M1v ((V 2%nat) - 32) (V 18%nat)) by (rewrite V2s, (VSV 18%nat) by PGSRDC.inl; apply OWV; [clear; lia| clear; lia| exact W32]).
  assert (S48 : L5.u64_at RSEGS M1v ((V 2%nat) - 48) (V 20%nat)) by (rewrite V2s, (VSV 20%nat) by PGSRDC.inl; apply OWV; [clear; lia| clear; lia| exact W48]).
  assert (S56 : L5.u64_at RSEGS M1v ((V 2%nat) - 56) (V 21%nat)) by (rewrite V2s, (VSV 21%nat) by PGSRDC.inl; apply OWV; [clear; lia| clear; lia| exact W56]).
  assert (S72 : L5.u64_at RSEGS M1v ((V 2%nat) - 72) (V 23%nat)) by (rewrite V2s, (VSV 23%nat) by PGSRDC.inl; apply OWV; [clear; lia| clear; lia| exact W72]).
  assert (S80 : L5.u64_at RSEGS M1v ((V 2%nat) - 80) (V 24%nat)) by (rewrite V2s, (VSV 24%nat) by PGSRDC.inl; apply OWV; [clear; lia| clear; lia| exact W80]).
  assert (S88 : L5.u64_at RSEGS M1v ((V 2%nat) - 88) (V 25%nat)) by (rewrite V2s, (VSV 25%nat) by PGSRDC.inl; apply OWV; [clear; lia| clear; lia| exact W88]).
  assert (S96 : L5.u64_at RSEGS M1v ((V 2%nat) - 96) (V 26%nat)) by (rewrite V2s, (VSV 26%nat) by PGSRDC.inl; apply OWV; [clear; lia| clear; lia| exact W96]).
  assert (STR1 : PGSRDK.srd_stR (PGSRDC.vx V R1) R1 M1v).
  { unfold PGSRDK.srd_stR, PGSRDC.vx. cbn beta iota.
    PGSRDC.sweep ltac:(first [assumption | exact (bv_unsigned_in_range _ _) | (symmetry; apply Z_to_bv_bv_unsigned)
                      | (rewrite KS1 by PGSRDC.inl; assumption) | (eapply L5.writable_grows; [exact MG1| assumption])
                      | (eapply L5.defined_grows; [exact MG1| assumption]) | PGSRDC.carry MV AG1 KB]). }
  assert (STR1' : PGSRDK.srd_stR (PGSRDC.vx V R1) R1 (mrestrict (ahid Ac model1) M1)) by (rewrite HID1, MRT1; exact STR1).
  assert (V76 : PGSRDC.vx V R1 76%nat = 0).
  { unfold PGSRDC.vx. cbn beta iota. rewrite PR22, L5.unsigned_lit; [reflexivity| clear; lia]. }
  assert (VO1 : forall i, V 36%nat <= i < V 36%nat + 296 -> M1 (Z_to_bv 64 i) = M1v (Z_to_bv 64 i)).
  { intros i Hi. apply VIS1.
    apply (PGSRDC.srd_vis L ar C HI LY HIok O R0 M0 model0 K OB LBX FF LK Aw cr sp r _ str _ Wextra F fl LK2 M2 model2 M model LKc Ac i CTX FR BI).
    right; right; right; left. clear - Hi V36. lia. }
  assert (C264 : L5.u64_at RSEGS M1v ((V 36%nat) + 264) (V 34%nat)) by PGSRDC.carry MV AG1 KB.
  assert (C272 : L5.u64_at RSEGS M1v ((V 36%nat) + 272) 16384) by PGSRDC.carry MV AG1 KB.
  assert (U264 : L5.u64_at RSEGS M1 (os + 264) qc).
  { rewrite <- V34. replace (os + 264) with (V 36%nat + 264) by (clear - V36; lia).
    apply (L5C.u64_at_agree RSEGS M1v M1); [| PGSRDC.sd KB| PGSRDC.sd KB| exact C264]. intros i Hi. apply VO1. clear - Hi. lia. }
  assert (U272 : L5.u64_at RSEGS M1 (os + 272) 16384).
  { replace (os + 272) with (V 36%nat + 272) by (clear - V36; lia).
    apply (L5C.u64_at_agree RSEGS M1v M1); [| PGSRDC.sd KB| PGSRDC.sd KB| exact C272]. intros i Hi. apply VO1. clear - Hi. lia. }
  assert (U280 : L5.u64_at RSEGS M1 (os + 280) de).
  { rewrite <- V35. replace (os + 280) with (V 36%nat + 280) by (clear - V36; lia).
    apply (L5C.u64_at_agree RSEGS M1v M1); [| PGSRDC.sd KB| PGSRDC.sd KB| exact P280]. intros i Hi. apply VO1. clear - Hi. lia. }
  assert (U288 : L5.u64_at RSEGS M1 (os + 288) 0).
  { replace (os + 288) with (V 36%nat + 288) by (clear - V36; lia).
    apply (L5C.u64_at_agree RSEGS M1v M1); [| PGSRDC.sd KB| PGSRDC.sd KB| exact P288]. intros i Hi. apply VO1. clear - Hi. lia. }
  assert (ISS1 : PM.iss_at RSEGS PMA.AD PMSPA.accA M1 ois str (PM.STRM g eg 2)) by exact (ISSC M1 _ EK1 WOS OI_os OS_os _ IA).
  assert (DEF1 : L5.defined M1 p 0) by (intros i Hi; exfalso; clear - Hi; lia).
  pose proof (PMASK.iss_size_ltA M ois str _ IA) as SZ. cbn [PM.sm_g PM.sm_eg] in SZ.
  assert (A2 : de + 0 <= qc + 16384) by (clear - G3; unfold PM.CHUNK in G3; lia).
  assert (A3 : g <= g <= eg) by (clear - SZ; lia).
  assert (A5 : 0 <= 0 <= k) by (clear - H38 V38; unfold PM.CHUNK in H38; lia).
  assert (A6 : 0 + (eg - g) - (0 + (eg - g)) = 0) by (clear; lia).
  assert (A7 : 1 <= 0 -> 1 <= 0) by (intros X; exact X).
  assert (A8 : 0 = 0 -> 0 = 0 /\ 2 = 2) by (intros _; split; reflexivity).
  exact (EXIT fx1 R1 M1 model1 LKc Ac (PGSRDC.vx V R1) BI1 V2 V36 V37 V38 V50 V51 SV1 X3' X4' de 0 g 2 0 STR1' V76 U264 U272 U280 U288
           G1 (Z.le_refl 0) A2 ISS1 A3 (fun X => X) A5 A6 A7 A8 DEF1).
Qed.
End A0e.
End PGSRDA0E.
