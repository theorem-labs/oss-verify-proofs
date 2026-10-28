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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0PgSrcReadK16_b Ba0PgSrcReadC16_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := first [ L5FastLia.plia | Lia.lia ].

Module PGSRDA0D16.
Abbreviation RSEGS := PGSRDK16.RSEGS.
Abbreviation mem := (word -> option byte).
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).

Definition srd_pA0d (V : nat -> Z) (R : bvmap 5 word) (M : mem) : Prop :=
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
  /\ (L5.u32_at RSEGS M ((V 45%nat) + 152) 0)
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
  /\ (((V 51%nat) + 1 <= (((V 45%nat) / 8) + 2147450880) \/ (((V 45%nat) / 8) + 2147450880) + 34 <= (V 51%nat)))
  /\ (4096 <= (V 37%nat) <= 140737488338944).

Definition srd_pthD (V : nat -> Z) (R : bvmap 5 word) (M : mem) (rem sst : Z) : Prop :=
  rem = 0 /\ V 38%nat = PM.CHUNK /\ sst = 0 /\ srd_pA0d V R M.
Import PGSRDC16.
Ltac pick H := let H' := fresh "PH" in pose proof H as H';
  repeat match type of H' with
  | ?a <= ?x /\ ?x <= ?b => fail 1
  | ?a <= ?x /\ ?x < ?b => fail 1
  | _ /\ _ => let X := fresh "PH" in destruct H' as (X & H')
  end.
Ltac sfind := match goal with
  | H : ?a <= ?x <= ?b |- ?a <= ?x <= ?b => exact H
  | H : ?a <= ?x < ?b |- ?a <= ?x < ?b => exact H
  | H : ?a <= ?b \/ ?c <= ?d |- ?a <= ?b \/ ?c <= ?d => exact H
  | H : ?a < ?b \/ ?c <= ?d |- ?a < ?b \/ ?c <= ?d => exact H
  | H : ?a <= ?b \/ ?c < ?d |- ?a <= ?b \/ ?c < ?d => exact H
  | H : ?a < ?b \/ ?c < ?d |- ?a < ?b \/ ?c < ?d => exact H
  | H : ?a mod ?b = ?c |- ?a mod ?b = ?c => exact H
  | H : getr ?R ?r = ?v |- getr ?R ?r = ?v => exact H
  | H : L5.u64_at ?s ?m ?a ?v |- L5.u64_at ?s ?m ?a ?v => exact H
  | H : L5.u32_at ?s ?m ?a ?v |- L5.u32_at ?s ?m ?a ?v => exact H
  | H : L5.u8_at ?s ?m ?a ?v |- L5.u8_at ?s ?m ?a ?v => exact H
  | H : L5.defined ?m ?a ?n |- L5.defined ?m ?a ?n => exact H
  | H : L5.writable ?s ?m ?a ?n |- L5.writable ?s ?m ?a ?n => exact H
  | H : L5KA.zeros_at ?m ?a ?n |- L5KA.zeros_at ?m ?a ?n => exact H
  | H : L5.img_clear ?m ?a ?n |- L5.img_clear ?m ?a ?n => exact H
  end.
Ltac feed P tac :=
  lazymatch type of P with
  | ?A -> _ =>
      let H := fresh "FD" in
      assert (H : A) by (first [ tac | fail 100 "feed: premise" A ]);
      specialize (P H); clear H; feed P tac
  | _ => idtac
  end.
Ltac dsp LIA MEM :=
  lazymatch goal with
  | |- PMASRP.aligned _ _ => unfold PMASRP.aligned; sfind
  | |- 0 <= bv_unsigned _ < 2 ^ 64 => exact (bv_unsigned_in_range _ _)
  | |- _ <= _ <= _ => first [ sfind | LIA ]
  | |- _ <= _ < _ => first [ sfind | LIA ]
  | |- getr _ _ = Z_to_bv 64 (bv_unsigned _) => symmetry; apply Z_to_bv_bv_unsigned
  | |- _ => first [ sfind | MEM ]
  end.
Ltac carry_with Ms AG KB fin :=
  lazymatch goal with
  | |- L5.u64_at ?s ?Mt ?a ?v => apply (L5C.u64_at_agree s Ms Mt a v); [let ii := fresh in let Hii := fresh in intros ii Hii; apply AG; sdi Hii KB| sd KB| sd KB| fin]
  | |- L5.u32_at ?s ?Mt ?a ?v => apply (PMF.u32_at_agree s Ms Mt a v); [let ii := fresh in let Hii := fresh in intros ii Hii; apply AG; sdi Hii KB| sd KB| sd KB| fin]
  | |- L5.u8_at ?s ?Mt ?a ?v => apply (L5C.u8_at_agree s Ms Mt a v); [let ii := fresh in let Hii := fresh in intros ii Hii; apply AG; sdi Hii KB| sd KB| sd KB| fin]
  | |- L5.defined ?Mt ?a ?n => apply (L5C.defined_agree Ms Mt a n); [let ii := fresh in let Hii := fresh in intros ii Hii; apply AG; sdi Hii KB| fin]
  | |- L5.writable ?s ?Mt ?a ?n => apply (L5C.writable_agree s Ms Mt a n); [let ii := fresh in let Hii := fresh in intros ii Hii; apply AG; sdi Hii KB| sd KB| sd KB| fin]
  | |- L5KA.zeros_at ?Mt ?a ?n => apply (L5KA.zeros_at_agree1 Ms Mt a n); [let ii := fresh in let Hii := fresh in intros ii Hii; apply AG; sdi Hii KB| fin]
  | |- L5.img_clear ?Mt ?lo ?hi => let ii := fresh in let Hii := fresh in intros ii Hii; rewrite (AG ii) by sdi Hii KB; revert ii Hii;
      change (L5.img_clear Ms lo hi); fin
  end.
Ltac sdj Hii KB := first [ clear - Hii; lia | clear - Hii KB; lia ].
Ltac sk KB := clear - KB; lia.
Ltac cw Ms AG KB fin :=
  lazymatch goal with
  | |- L5.u64_at ?s ?Mt ?a ?v => apply (L5C.u64_at_agree s Ms Mt a v); [let ii := fresh in let Hii := fresh in intros ii Hii; apply AG; sdj Hii KB| sk KB| sk KB| fin]
  | |- L5.u32_at ?s ?Mt ?a ?v => apply (PMF.u32_at_agree s Ms Mt a v); [let ii := fresh in let Hii := fresh in intros ii Hii; apply AG; sdj Hii KB| sk KB| sk KB| fin]
  | |- L5.u8_at ?s ?Mt ?a ?v => apply (L5C.u8_at_agree s Ms Mt a v); [let ii := fresh in let Hii := fresh in intros ii Hii; apply AG; sdj Hii KB| sk KB| sk KB| fin]
  | |- L5.defined ?Mt ?a ?n => apply (L5C.defined_agree Ms Mt a n); [let ii := fresh in let Hii := fresh in intros ii Hii; apply AG; sdj Hii KB| fin]
  | |- L5.writable ?s ?Mt ?a ?n => apply (L5C.writable_agree s Ms Mt a n); [let ii := fresh in let Hii := fresh in intros ii Hii; apply AG; sdj Hii KB| sk KB| sk KB| fin]
  | |- L5KA.zeros_at ?Mt ?a ?n => apply (L5KA.zeros_at_agree1 Ms Mt a n); [let ii := fresh in let Hii := fresh in intros ii Hii; apply AG; sdj Hii KB| fin]
  end.

Section A0d.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Variable IL : icpt_layout.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.

Let LYa := PMA.ly_as0 L C LY.

Lemma srd_visI O R0 M0 model0 K OB LBX FF LK Aw cr sp r src str sm Wextra F fl LK2 M2 model2 Mc modelc LKc Ac i :
  PGSRDK16.srd_ctx L ar HI 16 O R0 M0 model0 K OB LBX FF LK Aw cr sp r src str sm Wextra ->
  PGSRDK16.srd_frame L ar HI 16 R0 OB LBX FF LK Aw cr sp src F fl LK2 M2 model2 ->
  PGSRDK16.srd_body L ar HI 16 O R0 M0 model0 OB LBX FF LK Aw sp src Wextra F Mc modelc LKc cr Ac ->
  (PGS.ow_ois O <= i < PGS.ow_ois O + 272) \/ (PGS.ow_ois O / 8 + SB <= i < PGS.ow_ois O / 8 + SB + 34) ->
  ahid Ac modelc (Z_to_bv 64 i) = false.
Proof.
  intros CTX G BI Hi.
  pose proof CTX as (OK & HH0 & _ & _ & _ & _ & _ & OFR & _).
  pose proof (PGSA.oo_lay _ _ _ _ _ _ OK) as (_ & _ & LY3 & LY4 & _ & _ & I8 & _).
  assert (AO : PMSPA.aobjA FF (PGS.ow_ois O) 272).
  { apply (PGSKA.aobjA_sub FF (PGS.ow_lo O) (PGS.ow_hi O)); [exact OFR| exact LY3| exact LY4]. }
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH0) as (_ & WF & _).
  pose proof AO as (f & Hf & X1 & X2). destruct (WF f Hf) as (Y1 & Y2 & _).
  unfold PGSRDK16.srd_body in BI.
  pose proof BI as (B1 & _).
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ _ _ _ _ Mc modelc B1) as (_ & _ & _ & VFS & _ & _ & VFSSH & _).
  cbv zeta in VFS, VFSSH.
  assert (E0 : forall (P : Z -> Prop) a, (forall j, 0 <= j < 1 -> P (a + j)) -> P a).
  { intros P a X. specialize (X 0 ltac:(lia)). rewrite Z.add_0_r in X. exact X. }
  set (ois := PGS.ow_ois O) in *.
  destruct Hi as [Y|Y].
  - apply (E0 (fun x => ahid Ac modelc (Z_to_bv 64 x) = false)). apply (VFS i 1); clear - Y X1 X2 Y1 Y2; lia.
  - apply (E0 (fun x => ahid Ac modelc (Z_to_bv 64 x) = false)). apply (VFSSH i 1).
    intros j Hj. unfold in_shadow_of, S. clear - Y Hj X1 X2 Y1 Y2 I8. unfold FS_BYTES in *. lia.
Qed.

Lemma srd_ag2 O R0 M0 model0 K OB LBX FF LK Aw cr sp r src str sm Wextra F fl LK2 M2 model2 M3 model3 LK3 Ac3 M4 model4 LK4 Ac4
    scr x n dst m i :
  PGSRDK16.srd_ctx L ar HI 16 O R0 M0 model0 K OB LBX FF LK Aw cr sp r src str sm Wextra ->
  PGSRDK16.srd_frame L ar HI 16 R0 OB LBX FF LK Aw cr sp src F fl LK2 M2 model2 ->
  PGSRDK16.srd_body L ar HI 16 O R0 M0 model0 OB LBX FF LK Aw sp src Wextra F M3 model3 LK3 cr Ac3 ->
  PGSRDK16.srd_body L ar HI 16 O R0 M0 model0 OB LBX FF LK Aw sp src Wextra F M4 model4 LK4 cr Ac4 ->
  L5CA.ahpres L ar ([] ++ (PM.src_own src ++ OB ++ LBX)) ((F, 1, sp - 160 - 16 + 32) :: FF) (sp - 160 - 16) scr [(x, n); (dst, m)] M3 M4 ->
  0 <= i < 2 ^ 64 ->
  (sp - 160 - 16 <= i < sp) \/ (F <= i < F + 120 /\ ~ (F + 24 <= i < F + 32)) \/ (F / 8 + SB <= i < F / 8 + SB + 16)
    \/ (PGS.ow_os O <= i < PGS.ow_os O + 296) \/ ((PGS.ow_os O + 8) / 8 + SB <= i < (PGS.ow_os O + 8) / 8 + SB + 36)
    \/ ((PGS.ow_ois O <= i < PGS.ow_ois O + 272) \/ (PGS.ow_ois O / 8 + SB <= i < PGS.ow_ois O / 8 + SB + 34)) ->
  ~ (x <= i < x + n) -> ~ (dst <= i < dst + m) ->
  mrestrict (ahid Ac4 model4) M4 (Z_to_bv 64 i) = mrestrict (ahid Ac3 model3) M3 (Z_to_bv 64 i).
Proof.
  intros CTX G BI3 BI4 AH Hi RG NX ND.
  assert (VS : forall Mc modelc LKc Ac, PGSRDK16.srd_body L ar HI 16 O R0 M0 model0 OB LBX FF LK Aw sp src Wextra F Mc modelc LKc cr Ac ->
      ahid Ac modelc (Z_to_bv 64 i) = false).
  { intros Mc modelc LKc Ac BI. destruct RG as [Y|[Y|[Y|[Y|[Y|Y]]]]].
    - apply (PGSRDC16.srd_vis L ar C HI LY HIok O R0 M0 model0 K OB LBX FF LK Aw cr sp r src str sm Wextra F fl LK2 M2 model2 Mc modelc LKc Ac i CTX G BI).
      left. exact Y.
    - apply (PGSRDC16.srd_vis L ar C HI LY HIok O R0 M0 model0 K OB LBX FF LK Aw cr sp r src str sm Wextra F fl LK2 M2 model2 Mc modelc LKc Ac i CTX G BI).
      right; left. clear - Y. lia.
    - apply (PGSRDC16.srd_vis L ar C HI LY HIok O R0 M0 model0 K OB LBX FF LK Aw cr sp r src str sm Wextra F fl LK2 M2 model2 Mc modelc LKc Ac i CTX G BI).
      right; right; left. exact Y.
    - apply (PGSRDC16.srd_vis L ar C HI LY HIok O R0 M0 model0 K OB LBX FF LK Aw cr sp r src str sm Wextra F fl LK2 M2 model2 Mc modelc LKc Ac i CTX G BI).
      right; right; right; left. exact Y.
    - apply (PGSRDC16.srd_vis L ar C HI LY HIok O R0 M0 model0 K OB LBX FF LK Aw cr sp r src str sm Wextra F fl LK2 M2 model2 Mc modelc LKc Ac i CTX G BI).
      right; right; right; right. exact Y.
    - exact (srd_visI O R0 M0 model0 K OB LBX FF LK Aw cr sp r src str sm Wextra F fl LK2 M2 model2 Mc modelc LKc Ac i CTX G BI Y). }
  apply PGSRDC16.mr_eq; [exact (VS M3 model3 LK3 Ac3 BI3)| exact (VS M4 model4 LK4 Ac4 BI4)|].
  pose proof CTX as (OK & HH0 & _ & _ & _ & _ & _ & OFR & _).
  pose proof (PGSA.oo_lay _ _ _ _ _ _ OK) as (LY1 & LY2 & LY3 & LY4 & _ & O8 & I8 & _).
  assert (AO : PMSPA.aobjA FF (PGS.ow_os O) 296).
  { apply (PGSKA.aobjA_sub FF (PGS.ow_lo O) (PGS.ow_hi O)); [exact OFR| exact LY1| exact LY2]. }
  assert (AOI : PMSPA.aobjA FF (PGS.ow_ois O) 272).
  { apply (PGSKA.aobjA_sub FF (PGS.ow_lo O) (PGS.ow_hi O)); [exact OFR| exact LY3| exact LY4]. }
  unfold PGSRDK16.srd_frame in G.
  pose proof G as G'. destruct G' as [_ GSPT GSLO GSHI GSPC GOCR GOWN GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
  change (ff_bytes 1) with 128 in *. change (128 / 8) with 16 in *.
  destruct AH as (AK & _). apply AK. split; [exact Hi|]. split.
  2:{ intros rr [<-|[<-|[]]] X; unfold L5.in_rng in X; cbn [fst snd] in X; [clear - X NX; lia| clear - X ND; lia]. }
  unfold aclient. set (os := PGS.ow_os O) in *. set (ois := PGS.ow_ois O) in *.
  destruct RG as [Y|[Y|[Y|[Y|[Y|[Y|Y]]]]]].
  - apply (L5SAR.stack_client L ar). clear - Y GSLO GSPC. lia. clear - Y. lia.
  - apply (L5SAR.fframe_client L ar _ _ _ _ F 1 (sp - 160 - 16 + 32)); [left; reflexivity|]. change (ff_bytes 1) with 128. clear - Y. lia.
  - apply (L5SAR.fframe_shadow_client L ar _ _ _ _ F 1 (sp - 160 - 16 + 32)); [left; reflexivity|].
    change (ff_bytes 1) with 128. unfold in_shadow_of, S. destruct GF8 as (_ & GF8b & _). rewrite GF8b. clear - Y. lia.
  - apply L5SAR.aclient_cons. apply PMASR1.cl_of_bf. right. apply (PMASR1.in_fframe_of_aobjA FF _ 296 i AO). clear - Y. lia.
  - apply L5SAR.aclient_cons. destruct AO as ([[fa fk] frs] & Hf & X1 & X2). cbn [ff_addr ff_class fst snd] in X1, X2.
    apply (L5SAR.fframe_shadow_client L ar _ _ _ _ fa fk frs); [exact Hf|]. unfold in_shadow_of, S. clear - Y X1 X2 O8. lia.
  - apply L5SAR.aclient_cons. apply PMASR1.cl_of_bf. right. apply (PMASR1.in_fframe_of_aobjA FF _ 272 i AOI). clear - Y. lia.
  - apply L5SAR.aclient_cons. destruct AOI as ([[fa fk] frs] & Hf & X1 & X2). cbn [ff_addr ff_class fst snd] in X1, X2.
    apply (L5SAR.fframe_shadow_client L ar _ _ _ _ fa fk frs); [exact Hf|]. unfold in_shadow_of, S. clear - Y X1 X2 I8. lia.
Qed.

Lemma srd_pieceI O R0 M0 model0 K OB LBX FF LK Aw cr sp r src str sm Wextra F fl LK2 M2 model2 M model LKc Ac
    (fx fx1 : FPState) R R1 (pc pc1 : Z) (M1v : mem) (Wp : Z -> Prop) :
  PGSRDK16.srd_ctx L ar HI 16 O R0 M0 model0 K OB LBX FF LK Aw cr sp r src str sm Wextra ->
  PGSRDK16.srd_frame L ar HI 16 R0 OB LBX FF LK Aw cr sp src F fl LK2 M2 model2 ->
  PGSRDK16.srd_body L ar HI 16 O R0 M0 model0 OB LBX FF LK Aw sp src Wextra F M model LKc cr Ac ->
  msteps RSEGS (st fx R pc (mrestrict (ahid Ac model) M)) (st fx1 R1 pc1 M1v) ->
  mem_grows (mrestrict (ahid Ac model) M) M1v ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Wp a -> M1v (Z_to_bv 64 a) = mrestrict (ahid Ac model) M (Z_to_bv 64 a)) ->
  (forall a, Wp a -> PGS.ow_os O + 256 <= a < PGS.ow_os O + 296 \/ PGS.ow_ois O + 152 <= a < PGS.ow_ois O + 156) ->
  (forall M1 model1, PGSRDK16.srd_body L ar HI 16 O R0 M0 model0 OB LBX FF LK Aw sp src Wextra F M1 model1 LKc cr Ac ->
      ahid Ac model1 = ahid Ac model -> mrestrict (ahid Ac model) M1 = M1v -> mem_grows M M1 ->
      (forall a, 0 <= a < 2 ^ 64 -> ~ Wp a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
      (forall a : word, ahid Ac model a = false -> M1 a = M1v a) ->
      L5SAR.ek L ar (PM.src_own src ++ OB ++ LBX) FF sp (PMSPA.pm_scr 4) [(PGS.ow_os O + 256, 40); (PGS.ow_ois O + 152, 4)] M M1 ->
      srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx1 R1 pc1 M1 model1) K) ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R pc M model) K.
Proof.
  intros CTX G BI MS MG FRZ WP KR.
  pose proof CTX as (OK & HH0 & _ & _ & _ & _ & _ & OFR & _).
  pose proof (PGSA.oo_lay _ _ _ _ _ _ OK) as (LY1 & LY2 & LY3 & LY4 & _).
  assert (AO : PMSPA.aobjA FF (PGS.ow_os O) 296).
  { apply (PGSKA.aobjA_sub FF (PGS.ow_lo O) (PGS.ow_hi O)); [exact OFR| exact LY1| exact LY2]. }
  assert (AOI : PMSPA.aobjA FF (PGS.ow_ois O) 272).
  { apply (PGSKA.aobjA_sub FF (PGS.ow_lo O) (PGS.ow_hi O)); [exact OFR| exact LY3| exact LY4]. }
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH0) as (_ & WF & _ & FSCEIL & _).
  pose proof (PMASK.fs_above_img L ar C HI LY HIok _ _ _ _ _ _ _ HH0) as FSI.
  pose proof AO as (f & Hf & X1 & X2). destruct (WF f Hf) as (Y1 & Y2 & _).
  pose proof AOI as (fi & Hfi & XI1 & XI2). destruct (WF fi Hfi) as (YI1 & YI2 & _).
  unfold PGSRDK16.srd_frame in G. unfold PGSRDK16.srd_body in BI.
  pose proof G as G'. destruct G' as [_ GSPT GSLO GSHI GSPC GOCR GOWN GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
  change (ff_bytes 1) with 128 in *. change (128 / 8) with 16 in *.
  pose proof BI as (B1 & B2 & _).
  unfold PMSPA.cfg, PMSP.cfg.
  apply (L5SAR.apiece L ar C HI LYa HIok _ _ _ _ _ _ _ fx fx1 R pc R1 pc1 M1v Wp K B1 B2 MS MG FRZ).
  - intros a Ha Wa. destruct (WP a Wa) as [Y|Y].
    + split.
      * unfold aclientw. apply L5SAR.aclient_cons. apply PMASR1.cl_of_bf. right. apply (PMASR1.in_fframe_of_aobjA FF _ 296 a AO). clear - Y. lia.
      * clear - Y X1 Y1 FSI. lia.
    + split.
      * unfold aclientw. apply L5SAR.aclient_cons. apply PMASR1.cl_of_bf. right. apply (PMASR1.in_fframe_of_aobjA FF _ 272 a AOI). clear - Y. lia.
      * clear - Y XI1 YI1 FSI. lia.
  - intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MG1 FR1 VV1.
    apply KR; [| exact HID1| exact VIS1| exact MG1| exact FR1| exact VV1|].
    2:{ intros a (Ha & Hc & Ho). apply FR1; [exact Ha|]. intros Wa. destruct (WP a Wa) as [Y|Y].
        - apply (Ho (PGS.ow_os O + 256, 40)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; clear - Y; lia].
        - apply (Ho (PGS.ow_ois O + 152, 4)); [right; left; reflexivity| unfold L5.in_rng; cbn [fst snd]; clear - Y; lia]. }
    unfold PGSRDK16.srd_body.
    eapply (PMAUK.binv_pieceW L ar HI); [exact G| exact BI| exact HH1| exact AM1| exact MRT1| exact MG1| exact FR1|].
    intros a Wa. unfold PNACSK.ocell. change (ff_bytes 1) with 128. change (128 / 8) with 16. destruct (WP a Wa) as [Y|Y].
    + split; [clear - Y X2 Y2 FSCEIL GSLO GSPC; lia|]. right; right; right. intros Oq.
      apply (Oq (PGS.ow_os O + 256, 40)); [unfold PGS.W_srcG, PGS.W_srcfG; apply in_or_app; left; apply in_or_app; left; left; reflexivity|].
      unfold L5.in_rng. cbn [fst snd]. clear - Y. lia.
    + split; [clear - Y XI2 YI2 FSCEIL GSLO GSPC; lia|]. right; right; right. intros Oq.
      apply (Oq (PGS.ow_ois O + 152, 4)); [unfold PGS.W_srcG, PGS.W_srcfG; apply in_or_app; left; apply in_or_app; left; right; right; left; reflexivity|].
      unfold L5.in_rng. cbn [fst snd]. clear - Y. lia.
Qed.

Lemma srd_a0d_ok : PMA.xsgetn_spec L ar HI -> PGSRDK16.srd_exit_T L ar HI 16 -> PGSRDK16.srd_a0_T L ar HI 16 srd_pthD.
Proof.
  intros XS EXIT. unfold PGSRDK16.srd_a0_T.
  intros O R0 M0 model0 K OB LBX FF LK Aw cr sp r str Wextra qc de rem g eg sst p k CTX R11 R12 F fl LK2 M2 model2 FR
         fx R M model LKc Ac V BI V2 V36 V37 V38 V50 V51 VSV X3 X4 V34 V35 V45 IA STA PTH.
  destruct PTH as (Hrem & V38c & Hsst & PA0D). subst rem sst.
  assert (KC : k = PM.CHUNK) by (rewrite <- V38; exact V38c). rewrite KC in R12, V38. clear KC.
  assert (CHv : PM.CHUNK = 16384) by reflexivity.
  unfold PMA.xsgetn_spec, PMSPA.xsgetn_spec in XS. cbn [pa_xsgetn PMA.AD ADDR_A] in XS.
  pose proof CTX as (OK & HH & AM & K0 & ENT & FRM & FRS & OFR & A10 & SP32 & ARGS & WX & PA0 & IA0 & BASE0 & INCS & KONT).
  destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH).
  destruct ARGS as (p' & k' & A11 & A12 & Hk & DST). destruct WX as (p'' & k'' & A11' & A12' & Hp'' & Hk'' & WE).
  rewrite L5SAR.r11 in A11, A11'. rewrite L5SAR.r12 in A12, A12'.
  pose proof (PGSA.oo_lay _ _ _ _ _ _ OK) as (LY1 & LY2 & LY3 & LY4 & LY5 & O8 & I8 & LY6 & LYD).
  pose proof (PGSA.oo_src _ _ _ _ _ _ OK M0 _ OB PA0) as (PSRC & PNI & SDEF0).
  pose proof (PMASK.fs_above_img L ar C HI LY HIok _ _ _ _ _ _ _ HH) as FSI.
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & _).
  pose proof (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as FRB. pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as BRB.
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
  pose proof PSRC as (S240 & S248 & SD256 & S264 & S272 & S280 & S288 & G1 & G2 & G3 & G16 & DCH & ACH & ACC240).
  assert (QIN : In (qc, PM.CHUNK) LB) by (unfold LB, PM.src_own; cbn; left; reflexivity).
  assert (OBIN : forall B m, In (B, m) OB -> In (B, m) LB) by (intros B m Hin; unfold LB, PM.src_own; cbn; right; apply in_or_app; left; exact Hin).
  assert (SOWN : incl (PM.vs_own str) LB) by (unfold LB; intros x Hx; apply in_or_app; right; apply in_or_app; right; exact (INCS x Hx)).
  assert (STb : forall c1 n1 q1, str = PM.VLong c1 n1 q1 -> In (q1, c1) LB).
  { intros c1 n1 q1 E. apply SOWN. rewrite E. cbn. left. reflexivity. }
  assert (STbX : forall c1 n1 q1, str = PM.VLong c1 n1 q1 -> In (q1, c1) LBX).
  { intros c1 n1 q1 E. apply INCS. rewrite E. cbn. left. reflexivity. }
  assert (ND : NoDup (map fst LB)) by exact (PMASK.lb_nodup L ar C HI HIok _ _ _ _ _ _ _ HH).
  destruct (WB _ QIN) as ((Q0 & QI & Q16 & _ & Q4 & QAPP) & _). cbn [fst snd] in Q0, QI, Q16, Q4, QAPP.
  unfold app_mem in QAPP, FSAPP. destruct FSAPP as (FSA0 & FSAs & FSA47). destruct QAPP as (QA0 & QAs & QA47).
  assert (DF : 0 <= p' /\ p' + k' <= 2 ^ 47 /\ L5.defined M0 p' k' /\ aacc M0 p' k' /\ app_rng ar p' k'
     /\ (forall a, p' <= a < p' + k' -> in_block LB a \/ in_fframe FF a)
     /\ (forall a, p' <= a < p' + k' -> ~ (sp - PMSPA.pm_scr 4 <= a < sp) /\ ~ (ois <= a < ois + 272) /\ ~ (os <= a < os + 296)
           /\ ~ (qc <= a < qc + PM.CHUNK) /\ (forall c1 n1 q1, str = PM.VLong c1 n1 q1 -> ~ (q1 <= a < q1 + c1)))
     /\ (p' + k' <= BIGSHADOW_LO \/ BIGSHADOW_HI <= p')
     /\ (PMSPA.aobjA FF p' k' \/ exists q m, In (q, m) LB /\ q <= p' /\ p' + k' <= q + m)
     /\ (p' + k' <= qc \/ qc + PM.CHUNK <= p')
     /\ (k' = PM.CHUNK -> exists q m, In (q, m) OB /\ q <= p' /\ p' + k' <= q + m)).
  { assert (OBJ : forall (APo : p' + k' <= os \/ os + 296 <= p') (APi : p' + k' <= ois \/ ois + 272 <= p') (KNC : k' < PM.CHUNK),
      PMSPA.aobjA FF p' k' -> L5.defined M0 p' k' -> aacc M0 p' k' ->
      0 <= p' /\ p' + k' <= 2 ^ 47 /\ L5.defined M0 p' k' /\ aacc M0 p' k' /\ app_rng ar p' k'
      /\ (forall a, p' <= a < p' + k' -> in_block LB a \/ in_fframe FF a)
      /\ (forall a, p' <= a < p' + k' -> ~ (sp - PMSPA.pm_scr 4 <= a < sp) /\ ~ (ois <= a < ois + 272) /\ ~ (os <= a < os + 296)
            /\ ~ (qc <= a < qc + PM.CHUNK) /\ (forall c1 n1 q1, str = PM.VLong c1 n1 q1 -> ~ (q1 <= a < q1 + c1)))
      /\ (p' + k' <= BIGSHADOW_LO \/ BIGSHADOW_HI <= p')
      /\ (PMSPA.aobjA FF p' k' \/ exists q m, In (q, m) LB /\ q <= p' /\ p' + k' <= q + m)
      /\ (p' + k' <= qc \/ qc + PM.CHUNK <= p')
      /\ (k' = PM.CHUNK -> exists q m, In (q, m) OB /\ q <= p' /\ p' + k' <= q + m)).
    { intros APo APi KNC AOD DD AD.
      pose proof AOD as (f & Hf & X1 & X2). destruct (WF f Hf) as (Y1 & Y2 & _).
      pose proof (PMASK.blk_obj_apart L ar C HI HIok LB FF LK cr Aw M0 _ qc PM.CHUNK p' k' HH QIN AOD) as APQ.
      split; [clear - X1 Y1 FSI; lia|]. split; [clear - X2 Y2 FSCEIL SLO SHI SPT; lia|]. split; [exact DD|]. split; [exact AD|].
      split; [apply (L5SAR.app_rng_fs L ar C HI HIok LB FF LK cr Aw M0 _ p' k' HH); clear - X1 X2 Y1 Y2; lia|].
      split; [intros a Ha; right; apply (PMASR1.in_fframe_of_aobjA FF p' k' a AOD Ha)|].
      split; [|split; [destruct FSAs as [Z|Z]; [left|right]; clear - Z X1 X2 Y1 Y2; lia|
               split; [left; exact AOD| split; [clear - APQ; lia| intros E; exfalso; clear - E KNC; lia]]]].
      intros a Ha. split; [clear - Ha X2 Y2 FSCEIL SLO; lia|]. split; [clear - Ha APi; lia|]. split; [clear - Ha APo; lia|].
      split; [clear - Ha APQ; lia|].
      intros c1 n1 q1 E. destruct (PMASK.blk_obj_apart L ar C HI HIok LB FF LK cr Aw M0 _ q1 c1 p' k' HH (STb c1 n1 q1 E) AOD) as [Z|Z]; clear - Ha Z; lia. }
    destruct DST as [(AOD & Hk8 & DD & AD & APF)|DW].
    - apply OBJ; [clear - APF LY1 LY2; lia| clear - APF LY3 LY4; lia| clear - Hk8 CHv; lia| exact AOD| exact DD| exact AD].
    - destruct (PGSA.oo_win _ _ _ _ _ _ OK M0 (PM.SRC qc de 0) OB p' k' PA0 DW) as (W0 & WD & [(B & m & BIN & WB1 & WB2)|(W1 & W2 & WL1 & WL2 & WL3 & WL4 & WL5)] & WACC).
      + pose proof (OBIN B m BIN) as TIN.
        destruct (WB _ TIN) as ((T0 & _ & _ & _ & T4 & TAPP) & _). cbn [fst snd] in T0, T4, TAPP.
        unfold app_mem in TAPP. destruct TAPP as (TA0 & TAs & TA47).
        assert (NQ : B <> qc).
        { intros E. apply (PMASK.fst_neq_appA [(qc, PM.CHUNK)] (OB ++ LBX) qc PM.CHUNK B m); [exact ND| left; reflexivity| apply in_or_app; left; exact BIN| symmetry; exact E]. }
        pose proof (PMASK.blk_apart L ar C HI HIok LB FF LK cr Aw M0 _ B m qc PM.CHUNK HH TIN QIN NQ) as APQ.
        pose proof (PMASK.blk_obj_apart L ar C HI HIok LB FF LK cr Aw M0 _ B m os 296 HH TIN AO) as APP.
        pose proof (PMASK.blk_obj_apart L ar C HI HIok LB FF LK cr Aw M0 _ B m ois 272 HH TIN AOI) as API.
        split; [clear - WB1 T0; lia|]. split; [clear - WB2 T4 SLO SHI SPT; lia|]. split; [exact WD|]. split; [exact WACC|].
        split; [apply (L5SAR.app_rng_block L ar C HI HIok LB FF LK cr Aw M0 _ B m p' k' HH TIN); clear - WB1 WB2; lia|].
        split; [intros a Ha; left; apply (PMASR1.in_block_of LB B m a TIN); clear - Ha WB1 WB2; lia|].
        split; [|split; [destruct TAs as [Z|Z]; [left|right]; clear - Z WB1 WB2; lia|
                 split; [right; exists B, m; split; [exact TIN|]; split; [exact WB1| exact WB2]|
                 split; [clear - APQ WB1 WB2; lia| intros _; exists B, m; split; [exact BIN| split; [exact WB1| exact WB2]]]]]].
        intros a Ha. split; [clear - Ha WB1 WB2 T4 SLO; lia|]. split; [clear - Ha WB1 WB2 API; lia|]. split; [clear - Ha WB1 WB2 APP; lia|].
        split; [clear - Ha WB1 WB2 APQ; lia|].
        intros c1 n1 q1 E.
        assert (NS : B <> q1) by (apply (PMASK.fst_neq_appA ((qc, PM.CHUNK) :: OB) LBX B m q1 c1); [exact ND| right; exact BIN| exact (STbX c1 n1 q1 E)]).
        destruct (PMASK.blk_apart L ar C HI HIok LB FF LK cr Aw M0 _ B m q1 c1 HH TIN (STb c1 n1 q1 E) NS) as [Z|Z]; clear - Ha WB1 WB2 Z; lia.
      + apply OBJ; [exact WL4| exact WL5| exact WL3| apply (PGSKA.aobjA_sub FF lo hi p' k' OFR WL1 WL2)| exact WD| exact WACC]. }
  destruct DF as (DP0 & DP1 & DDP & DAP & DAPP & DCL & DX & DSH & DLOC & DQA & DOB).
  set (MV := mrestrict (ahid Ac model) M) in *.
  unfold PGSRDK16.srd_stA in STA. unfold srd_pA0d in PA0D. pick STA. pick PA0D.
  assert (P37 : 0 <= p < 2 ^ 64) by (rewrite <- V37; match goal with H : 0 <= V 37%nat < _ |- _ => exact H end).
  assert (EP : p' = p).
  { rewrite R11 in A11. apply (f_equal bv_unsigned) in A11. rewrite !L5.unsigned_lit in A11 by (clear - P37 DP0 DP1 Hk; lia). lia. }
  assert (EK : k' = PM.CHUNK).
  { rewrite R12 in A12. apply (f_equal bv_unsigned) in A12.
    assert (CH64 : 0 <= PM.CHUNK < 2 ^ 64) by (rewrite CHv; lia).
    assert (K64 : 0 <= k' < 2 ^ 64) by (clear - Hk CH64; lia).
    rewrite (L5.unsigned_lit _ CH64), (L5.unsigned_lit _ K64) in A12. lia. }
  assert (EP2 : p'' = p).
  { rewrite R11 in A11'. apply (f_equal bv_unsigned) in A11'. rewrite !L5.unsigned_lit in A11' by (clear - P37 Hp''; lia). lia. }
  assert (EK2 : k'' = PM.CHUNK).
  { rewrite R12 in A12'. apply (f_equal bv_unsigned) in A12'.
    assert (CH64 : 0 <= PM.CHUNK < 2 ^ 64) by (rewrite CHv; lia).
    rewrite (L5.unsigned_lit _ CH64), (L5.unsigned_lit _ Hk'') in A12'. lia. }
  subst p' k' p'' k''.
  destruct (DOB eq_refl) as (q0 & c0 & BIN0 & Dq1 & Dq2).
  assert (WAPP : PMKA.wapp (PGS.W_srcG os ois (PM.SRC qc de 0) ++ Wextra)).
  { rewrite WE. unfold PGS.W_srcG, PGS.W_srcfG. cbn [PM.sr_qc app].
    apply PMKA.wapp_cons; [cbn [fst snd]; clear - OBIG; unfold BIGSHADOW_LO, BIGSHADOW_HI; lia|].
    apply PMKA.wapp_cons; [cbn [fst snd]; clear - IBIG; unfold BIGSHADOW_LO, BIGSHADOW_HI; lia|].
    apply PMKA.wapp_cons; [cbn [fst snd]; clear - IBIG; unfold BIGSHADOW_LO, BIGSHADOW_HI; lia|].
    apply PMKA.wapp_cons; [cbn [fst snd]; clear - QAs; lia|].
    apply PMKA.wapp_cons; [cbn [fst snd]; clear - DSH; lia| apply PMKA.wapp_nil]. }
  assert (AGSHP : forall Ma Mb W, L5SAR.ek L ar LB FF sp (PMSPA.pm_scr 4) W Ma Mb -> PMKA.wapp W -> PMFA.agsh Ma Mb p PM.CHUNK).
  { intros Ma Mb W E WP. destruct DLOC as [AOD|(q & m & Hq & X1 & X2)].
    - exact (PMKA.agsh_obj L ar LB FF sp (PMSPA.pm_scr 4) W Ma Mb E WP FRB p PM.CHUNK AOD).
    - destruct (BRB _ Hq) as (Y1 & Y2). cbn [fst snd] in Y1, Y2.
      intros x Hx. apply (PMASK.agsh_blk L ar LB FF sp (PMSPA.pm_scr 4) W Ma Mb q m E WP Hq ltac:(clear - Y1; lia) ltac:(clear - Y2; lia)). clear - Hx X1 X2; lia. }
  assert (ISSG : forall (Ma Mb : mem) (W : list L5.range), L5SAR.ek L ar LB FF sp (PMSPA.pm_scr 4) W Ma Mb -> PMKA.wapp W ->
      (forall a, ois <= a < ois + 272 -> L5.outside W a) ->
      (forall c1 n1 q1, str = PM.VLong c1 n1 q1 -> forall a, q1 <= a < q1 + c1 -> L5.outside W a) ->
      forall sm0, PM.iss_at RSEGS PMA.AD PMSPA.accA Ma ois str sm0 -> PM.iss_at RSEGS PMA.AD PMSPA.accA Mb ois str sm0).
  { intros Ma Mb W E WP OI OS sm0 IS.
    apply (PMFA.iss_at_agreeA RSEGS PMA.AD Ma Mb ois str sm0); [clear - I1; lia| clear - I1; lia| split| | exact IS].
    - intros i Hi. apply E. split; [clear - Hi I1; lia|].
      split; [apply PMASR1.cl_of_bf; right; exact (PMASR1.in_fframe_of_aobjA FF ois 272 i AOI Hi)| exact (OI i Hi)].
    - exact (PMKA.agsh_obj L ar LB FF sp (PMSPA.pm_scr 4) W Ma Mb E WP FRB ois 272 AOI).
    - intros c1 n1 q1 Es. pose proof (STb c1 n1 q1 Es) as TIN. destruct (WB _ TIN) as ((T0 & _ & _ & _ & T4 & _) & _).
      cbn [fst snd] in T0, T4. split.
      + intros i Hi. apply E. split; [clear - Hi T0 T4 SLO SHI SPT; lia|].
        split; [apply PMASR1.cl_of_bf; left; exact (PMASR1.in_block_of LB q1 c1 i TIN Hi)| exact (OS c1 n1 q1 Es i Hi)].
      + apply (PMASK.agsh_blk L ar LB FF sp (PMSPA.pm_scr 4) W Ma Mb q1 c1 E WP TIN); clear - T0 T4 SLO SHI SPT; lia. }
  assert (WOS : PMKA.wapp [(PGS.ow_os O + 256, 40)]).
  { apply PMKA.wapp_cons; [cbn [fst snd]; clear - OBIG; unfold BIGSHADOW_LO, BIGSHADOW_HI in *; lia| apply PMKA.wapp_nil]. }
  assert (OI_os : forall a, ois <= a < ois + 272 -> L5.outside [(PGS.ow_os O + 256, 40)] a).
  { intros a Ha r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. clear - Ha LYD. lia. }
  assert (OS_os : forall c1 n1 q1, str = PM.VLong c1 n1 q1 -> forall a, q1 <= a < q1 + c1 -> L5.outside [(PGS.ow_os O + 256, 40)] a).
  { intros c1 n1 q1 Es a Ha r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd].
    destruct (PMASK.blk_obj_apart L ar C HI HIok LB FF LK cr Aw M0 _ q1 c1 os 296 HH (STb c1 n1 q1 Es) AO) as [Z|Z]; clear - Ha Z; lia. }
  specialize (EXIT O R0 M0 model0 K OB LBX FF LK Aw cr sp r str Wextra qc de 0 g eg 0 p PM.CHUNK CTX R11 R12 F fl LK2 M2 model2 FR).
  assert (DFX : 4096 <= p /\ p + PM.CHUNK <= ahl_ceil ar /\ (forall a, p <= a < p + PM.CHUNK -> ~ (65536 <= a < 6905856))).
  { destruct DLOC as [(f & Hf & X1 & X2)|(q & m & Hq & X1 & X2)].
    - destruct (WF f Hf) as (Y1 & Y2 & _).
      split; [clear - X1 Y1 FSI; lia|]. split; [clear - X2 Y2 FSCEIL SLO SHI SPT; lia|].
      intros a Ha. clear - Ha X1 Y1 FSI. lia.
    - destruct (WB _ Hq) as ((T0 & TI & _ & _ & T4 & _) & _). cbn [fst snd] in T0, TI, T4.
      rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in TI.
      split; [clear - X1 T0; lia|]. split; [clear - X2 T4; lia|].
      intros a Ha. clear - Ha X1 X2 TI T0. lia. }
  destruct DFX as (P4096 & PCEIL & IMX).
  assert (OUTIMG : forall a, 65536 <= a < 6905856 -> L5.outside (PGS.W_srcG os ois (PM.SRC qc de 0) ++ Wextra) a).
  { intros a Ha r0 Hr. rewrite WE in Hr. unfold PGS.W_srcG, PGS.W_srcfG in Hr. cbn [PM.sr_qc app] in Hr. unfold L5.in_rng.
    pose proof QI as QI'. rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in QI'.
    destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd].
    - clear - Ha O1. lia.
    - clear - Ha I1. lia.
    - clear - Ha I1. lia.
    - clear - Ha QI' Q0 CHv. lia.
    - intros Y. exact (IMX a Y Ha). }
  pose proof FR as G'. unfold PGSRDK16.srd_frame in G'.
  destruct G' as [_ GSPT GSLO GSHI GSPC GOCR GOWN GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
  change (ff_bytes 1) with 128 in GFR, GNCF, GF8.
  pose proof AOI as (fi & Hfi & XI1 & XI2). destruct (WF fi Hfi) as (YI1 & YI2 & _).
  match goal with
  | H2 : _ <= V 2%nat <= _, H36 : _ <= V 36%nat <= _, H45 : _ <= V 45%nat <= _, H50 : _ <= V 50%nat <= _,
    H51 : 4096 <= V 51%nat <= _, H37 : 4096 <= V 37%nat <= _ |- _ =>
      pose proof (conj H2 (conj H36 (conj H45 (conj H50 (conj H51 H37))))) as KB
  end.
  assert (IBV := IBIG). rewrite <- V45 in IBV. assert (OBV := OBIG). rewrite <- V36 in OBV.
  pose proof (PMASRP.asrA0d16_conc fx R MV V) as P0.
  feed P0 ltac:(idtac; dsp ltac:(idtac; fail) ltac:(idtac; sfind)).
  destruct P0 as (fx1 & R1 & M1v & MG1 & _ & AG1 & MS1 & KS1 & T1 & T2 & T8 & T9 & T10 & T11 & T12 & T13 & T14 & T15 & T16 & T18 & T19 & T20
                  & T21 & T22 & T23 & T24 & T25 & T26 & S152 & S144 & S112 & S32 & U1 & U2 & U3 & U4 & U5 & U6 & U7 & U8 & U9 & U10 & U11 & U12
                  & F16 & F8 & F0 & D24 & D40).
  apply (PGSRDC16.srd_piece L ar C HI LY HIok O R0 M0 model0 K OB LBX FF LK Aw cr sp r (PM.SRC qc de 0) str (PM.STRM g eg 0) Wextra F fl LK2 M2 model2
           M model LKc Ac fx fx1 R R1 _ _ M1v
           (fun a => (V 2%nat - 152 <= a < V 2%nat - 152 + 16) \/ (V 2%nat - 112 <= a < V 2%nat - 112 + 8) \/ (32 * V 50%nat <= a < 32 * V 50%nat + 24)
                     \/ (32 * V 50%nat + 32 <= a < 32 * V 50%nat + 32 + 8) \/ (4 * V 50%nat + SB <= a < 4 * V 50%nat + SB + 12)) CTX FR BI MS1 MG1).
  { intros a Ha NW. cbn beta in NW. apply AG1; [exact Ha|..]; intros Y; apply NW; clear - Y; unfold SB; lia. }
  { intros a Wa. cbn beta in Wa. destruct Wa as [Y|[Y|[Y|[Y|Y]]]].
    - right; right; right. clear - Y V2. lia.
    - right; right; right. clear - Y V2. lia.
    - left. clear - Y V50. lia.
    - left. clear - Y V50. lia.
    - right; left. clear - Y V50. lia. }
  intros M1 model1 BI1 HID1 MRT1 MGM1 FR1 VIS1 EK1.
  pose proof BI1 as BI1'. unfold PGSRDK16.srd_body, PMAUK.binv in BI1'.
  destruct BI1' as (HH1 & AM1 & RT1 & IA1 & ILK1 & ASTK1 & EK1' & DK1 & OWN1 & DSH1).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH1) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NDF1 & _).
  pose proof (PMASK.base_keep L ar C LY LB FF sp (PMSPA.pm_scr 4) _ M0 M1 EK1' OUTIMG BASE0) as BASE1.
  assert (ISS1 : PM.iss_at RSEGS PMA.AD PMSPA.accA M1 ois str (PM.STRM g eg 0)) by exact (ISSG M M1 _ EK1 WOS OI_os OS_os _ IA).
  pose proof (OBIN q0 c0 BIN0) as TIN0.
  assert (APG : p + PM.CHUNK <= g \/ eg <= p).
  { destruct (PMASK.iss_unread_whereA M0 ois str _ IA0) as [(Y1 & Y2)|(c1 & n1 & q1 & E & Y1 & Y2)]; cbn [PM.sm_g PM.sm_eg] in Y1, Y2.
    - destruct (PMASK.blk_obj_apart L ar C HI HIok LB FF LK cr Aw M0 _ q0 c0 ois 272 HH TIN0 AOI) as [Z1|Z1]; clear - Y1 Y2 Z1 Dq1 Dq2; lia.
    - assert (NS : q0 <> q1) by (apply (PMASK.fst_neq_appA ((qc, PM.CHUNK) :: OB) LBX q0 c0 q1 c1); [exact ND| right; exact BIN0| exact (STbX c1 n1 q1 E)]).
      destruct (PMASK.blk_apart L ar C HI HIok LB FF LK cr Aw M0 _ q0 c0 q1 c1 HH TIN0 (STb c1 n1 q1 E) NS) as [Z1|Z1]; clear - Y1 Y2 Z1 Dq1 Dq2; lia. }
  apply (XS fx1 R1 M1 model1 K ([] ++ LB) ((F, 1, sp - 160 - 16 + 32) :: FF) LKc Ac cr (sp - 160 - 16) 717164 ois p str (PM.STRM g eg 0) HH1 AM1 K0).
  { unfold PMSPA.entryA. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4.
    split; [exact T1|]. split; [split; [clear; lia| reflexivity]|].
    split; [rewrite T2, V2; f_equal; clear; lia|].
    split; [rewrite (KS1 3%nat) by inl; rewrite X3; exact Rgp|].
    split; [rewrite (KS1 4%nat) by inl; rewrite X4; exact Rtp|].
    split.
    - replace (sp - 160 - 16) with (sp - 176) by (clear; lia).
      try (replace (sp - 160 - 16) with (sp - 176) by lia); apply (L5SAR.astk_sub ar M1 M1 sp (PMSPA.pm_scr 4) 176 (PMSPA.pm_scr 2) ASTK1 (mem_grows_refl M1));
        [clear; lia| clear; unfold PMSPA.pm_scr; lia| clear; unfold PMSPA.pm_scr; lia| clear - A16; lia].
    - apply (PMKA.shadow_zero_sub M1 (sp - PMSPA.pm_scr 4) (PMSPA.pm_scr 4 / 8));
        [clear - A16; unfold PMSPA.pm_scr; lia| clear - A16; unfold PMSPA.pm_scr; lia| clear; unfold PMSPA.pm_scr; lia
        | clear; unfold PMSPA.pm_scr; lia| clear; unfold PMSPA.pm_scr; lia|].
      apply (PMKA.stksh_keepA L ar LB FF sp (PMSPA.pm_scr 4) _ M0 M1 EK1' WAPP (sp - PMSPA.pm_scr 4) (PMSPA.pm_scr 4 / 8));
        [clear - SLO SHI SPT; unfold PMSPA.pm_scr in *; lia| clear - SLO SHI SPT; unfold PMSPA.pm_scr in *; lia
        | clear - SLO SHI SPT; unfold PMSPA.pm_scr in *; lia| clear - A16; unfold PMSPA.pm_scr; lia| clear; unfold PMSPA.pm_scr; lia| exact STKSH]. }
  { assert (FRA : PGSA.ffroomB PNRA.FCB 2 ((F, 1, sp - 160 - 16 + 32) :: FF) LKc).
    { apply (PMAUAR.ffroomB_push PNRA.FCB 4 2 FF LK LKc _ FRM ILK1); [exact NDF1| clear; lia]. }
    exact FRA. }
  { apply (PMAUAR.ffrsA_push FF sp (sp - 160 - 16) F 1 (sp - 160 - 16 + 32) FRS); clear; lia. }
  { rewrite L5K.rl10, T10, V45. reflexivity. }
  { rewrite L5SAR.r11, T11, V37. reflexivity. }
  { rewrite L5SAR.r12, T12. reflexivity. }
  { apply PMAUAR.aobjA_push. exact AOI. }
  { exact I8. }
  { exact ISS1. }
  { exact BASE1. }
  { exact SOWN. }
  { exists q0, c0. split; [exact TIN0|]. split; [exact Dq1| exact Dq2]. }
  { intros a Ha. apply (PMFA.accA_agree M0 M1 p PM.CHUNK (AGSHP M0 M1 _ EK1' WAPP) DAP a). exact Ha. }
  { cbn [PM.sm_g PM.sm_eg]. exact APG. }
  intros fx3 R3 M3 model3 LK3 Ac3 c RP3 A10c Hc IA3 DF3 HP3 MRT3 INC3 INCA3 AM3 HH3.
  cbn [PM.sm_g PM.sm_eg PM.sm_st] in Hc, IA3. rewrite L5K.rl10 in A10c.
  assert (C0 : 0 <= c <= PM.CHUNK /\ g + c <= eg).
  { pose proof (PMASK.iss_size_ltA M0 ois str _ IA0) as SZ. cbn [PM.sm_g PM.sm_eg] in SZ. rewrite Hc. clear - SZ CHv.
    destruct (Z.min_spec PM.CHUNK (eg - g)) as [[X1 X2]|[X1 X2]]; rewrite X2; lia. }
  assert (BI3 : PGSRDK16.srd_body L ar HI 16 O R0 M0 model0 OB LBX FF LK Aw sp (PM.SRC qc de 0) Wextra F M3 model3 LK3 cr Ac3).
  { pose proof FR as FRu. unfold PGSRDK16.srd_frame in FRu. pose proof BI1 as BI1u. unfold PGSRDK16.srd_body in BI1u.
    unfold PGSRDK16.srd_body.
    eapply (PMAUK.binv_callee L ar C HI HIok); [exact FRu| exact BI1u| exact HP3| exact HH3| exact AM3| exact MRT3| exact INCA3| exact INC3
                                               | clear; unfold PMSPA.pm_scr; lia| clear; unfold PMSPA.pm_scr; lia| | |].
    - intros rr a [<-|[<-|[]]] Ha; unfold L5.in_rng in Ha; cbn [fst snd] in Ha; change (ff_bytes 1) with 128; change (128 / 8) with 16;
        unfold PNACSK.ocell.
      + split; [clear - Ha XI2 YI2 FSCEIL GSLO GSPC; lia|].
        intros Y. apply (GNCF a); [right; unfold S; destruct GF8 as (_ & GF8b & _); rewrite GF8b; clear - Y; lia|].
        apply PMASR1.cl_of_bf. right. apply (PMASR1.in_fframe_of_aobjA FF ois 272 a AOI). clear - Ha. lia.
      + destruct (DX a ltac:(clear - Ha; lia)) as (N1 & _).
        split; [intros Y; apply N1; clear - Y; unfold PMSPA.pm_scr; lia|].
        intros Y. apply (GNCF a); [right; unfold S; destruct GF8 as (_ & GF8b & _); rewrite GF8b; clear - Y; lia|].
        apply PMASR1.cl_of_bf. exact (DCL a ltac:(clear - Ha; lia)).
    - intros a _ Oq rr [<-|[<-|[]]] X.
      + apply (Oq (ois + 40, 8)); [unfold PGS.W_srcG, PGS.W_srcfG; apply in_or_app; left; apply in_or_app; left; right; left; reflexivity| exact X].
      + apply (Oq (p, PM.CHUNK)); [rewrite WE; apply in_or_app; right; left; reflexivity| exact X].
    - intros a X. exact X. }
  pose proof BI3 as BI3'. unfold PGSRDK16.srd_body, PMAUK.binv in BI3'. destruct BI3' as (HH3' & _ & _ & _ & _ & ASTK3 & EK3 & _).
  pose proof (PMASK.base_keep L ar C LY LB FF sp (PMSPA.pm_scr 4) _ M0 M3 EK3 OUTIMG BASE0) as BASE3.
  pose proof (PMASK.mach_vis L ar C HI LY HIok _ _ _ _ _ M3 model3 HH3' BASE3) as (IM0 & IM1 & IM2).
  pose proof (PMAUK.vis_facts L ar C HI LYa HIok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FR _ _ _ _ _ _ _ BI3)
    as ((VW & _) & OWN3 & (VF1 & VF2 & VF3 & VF4 & VF5) & _).
  change (ff_bytes 1) with 128 in VF1, VF2, VF3, VF4. change (128 / 8) with 16 in VF3.
  pose proof (PMASK.img_shz_vis L ar C HI LY IL ICok ILY _ _ _ _ _ M3 model3 1265944 1 HH3' ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia) ltac:(lia)) as VT1.
  pose proof (PMASK.img_shz_vis L ar C HI LY IL ICok ILY _ _ _ _ _ M3 model3 1265792 1 HH3' ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia) ltac:(lia)) as VT2.
  pose proof (PGSKA.iss_visG L ar C HI LY HIok _ _ _ _ _ M3 model3 ois str _ sp (PMSPA.pm_scr 4) HH3' (PMAUAR.aobjA_push _ _ _ _ AOI) I8 IA3 ASTK3)
    as (_ & _ & JW & _).
  set (MV3 := mrestrict (ahid Ac3 model3) M3) in *.
  assert (WSTK : L5.writable RSEGS MV3 (V 2%nat - 160) 176).
  { assert (E : sp - (sp - 160 - 16) = 176) by (clear; lia). rewrite E in VW. rewrite V2.
    replace (sp - 16 - 160) with (sp - 160 - 16) by (clear; lia). exact VW. }
  assert (WSTK160 : L5.writable RSEGS MV3 (V 2%nat - 160) 160) by (apply (L5.writable_sub RSEGS MV3 (V 2%nat - 160) 176 _ _ WSTK); clear; lia).
  assert (DF128 : L5.defined MV3 (32 * V 50%nat) 128) by (rewrite V50; exact VF1).
  assert (WF128 : L5.writable RSEGS MV3 (32 * V 50%nat) 128) by (rewrite V50; exact VF2).
  assert (WSH : L5.writable RSEGS MV3 (4 * V 50%nat + SB) 16).
  { replace (4 * V 50%nat) with (F / 8) by (clear - V50; lia). exact VF3. }
  unfold SB in WSH.
  assert (U120 : L5.u64_at RSEGS MV3 (32 * V 50%nat + 120) (V 51%nat)).
  { rewrite V50, V51. replace (F + 120) with (F + 128 - 8) by (clear; lia). exact VF4. }
  assert (WFL : L5.writable RSEGS MV3 (V 51%nat) 1) by (rewrite V51; exact VF5).
  assert (D24' : L5.defined MV3 (32 * V 50%nat + 24) 8) by (eapply L5.defined_sub; [exact DF128| clear; lia| clear; lia]).
  assert (D40' : L5.defined MV3 (32 * V 50%nat + 40) 88) by (eapply L5.defined_sub; [exact DF128| clear; lia| clear; lia]).
  assert (W83 : L5.writable RSEGS MV3 (V 45%nat) 272) by (rewrite V45; exact JW).
  unfold PNACSK.own in OWN3.
  destruct OWN3 as (OW1 & OW8 & OW9 & OW18 & OW19 & OW20 & OW21 & OW22 & OW23 & OW24 & OW25 & OW26 & OW27).
  assert (Q1 : L5.u64_at RSEGS MV3 (V 2%nat + 8) (V 1%nat)) by (rewrite V2; rewrite (VSV 1%nat) by inl; replace (sp - 16 + 8) with (sp - 8) by (clear; lia); exact OW1).
  assert (Q8 : L5.u64_at RSEGS MV3 (V 2%nat) (V 8%nat)) by (rewrite V2; rewrite (VSV 8%nat) by inl; replace (sp - 16) with (sp - 16) by (clear; lia); exact OW8).
  assert (Q9 : L5.u64_at RSEGS MV3 (V 2%nat - 8) (V 9%nat)) by (rewrite V2; rewrite (VSV 9%nat) by inl; replace (sp - 16 - 8) with (sp - 24) by (clear; lia); exact OW9).
  assert (Q18 : L5.u64_at RSEGS MV3 (V 2%nat - 16) (V 18%nat)) by (rewrite V2; rewrite (VSV 18%nat) by inl; replace (sp - 16 - 16) with (sp - 32) by (clear; lia); exact OW18).
  assert (Q19 : L5.u64_at RSEGS MV3 (V 2%nat - 24) (V 19%nat)) by (rewrite V2; rewrite (VSV 19%nat) by inl; replace (sp - 16 - 24) with (sp - 40) by (clear; lia); exact OW19).
  assert (Q20 : L5.u64_at RSEGS MV3 (V 2%nat - 32) (V 20%nat)) by (rewrite V2; rewrite (VSV 20%nat) by inl; replace (sp - 16 - 32) with (sp - 48) by (clear; lia); exact OW20).
  assert (Q21 : L5.u64_at RSEGS MV3 (V 2%nat - 40) (V 21%nat)) by (rewrite V2; rewrite (VSV 21%nat) by inl; replace (sp - 16 - 40) with (sp - 56) by (clear; lia); exact OW21).
  assert (Q22 : L5.u64_at RSEGS MV3 (V 2%nat - 48) (V 22%nat)) by (rewrite V2; rewrite (VSV 22%nat) by inl; replace (sp - 16 - 48) with (sp - 64) by (clear; lia); exact OW22).
  assert (Q23 : L5.u64_at RSEGS MV3 (V 2%nat - 56) (V 23%nat)) by (rewrite V2; rewrite (VSV 23%nat) by inl; replace (sp - 16 - 56) with (sp - 72) by (clear; lia); exact OW23).
  assert (Q24 : L5.u64_at RSEGS MV3 (V 2%nat - 64) (V 24%nat)) by (rewrite V2; rewrite (VSV 24%nat) by inl; replace (sp - 16 - 64) with (sp - 80) by (clear; lia); exact OW24).
  assert (Q25 : L5.u64_at RSEGS MV3 (V 2%nat - 72) (V 25%nat)) by (rewrite V2; rewrite (VSV 25%nat) by inl; replace (sp - 16 - 72) with (sp - 88) by (clear; lia); exact OW25).
  assert (Q26 : L5.u64_at RSEGS MV3 (V 2%nat - 80) (V 26%nat)) by (rewrite V2; rewrite (VSV 26%nat) by inl; replace (sp - 16 - 80) with (sp - 96) by (clear; lia); exact OW26).
  assert (Q27 : L5.u64_at RSEGS MV3 (V 2%nat - 88) (V 27%nat)) by (rewrite V2; rewrite (VSV 27%nat) by inl; replace (sp - 16 - 88) with (sp - 104) by (clear; lia); exact OW27).
  assert (B18 : 0 <= V 18%nat < 2 ^ 64) by (rewrite (VSV 18%nat) by inl; apply bv_unsigned_in_range).
  assert (B20 : 0 <= V 20%nat < 2 ^ 64) by (rewrite (VSV 20%nat) by inl; apply bv_unsigned_in_range).
  assert (B21 : 0 <= V 21%nat < 2 ^ 64) by (rewrite (VSV 21%nat) by inl; apply bv_unsigned_in_range).
  assert (B23 : 0 <= V 23%nat < 2 ^ 64) by (rewrite (VSV 23%nat) by inl; apply bv_unsigned_in_range).
  assert (B24 : 0 <= V 24%nat < 2 ^ 64) by (rewrite (VSV 24%nat) by inl; apply bv_unsigned_in_range).
  assert (B25 : 0 <= V 25%nat < 2 ^ 64) by (rewrite (VSV 25%nat) by inl; apply bv_unsigned_in_range).
  assert (B26 : 0 <= V 26%nat < 2 ^ 64) by (rewrite (VSV 26%nat) by inl; apply bv_unsigned_in_range).
  assert (RG3 : forall x, In x L5SAR.cs_all -> getr R3 (reg x) = getr R1 (reg x)) by (intros x Hx; apply (L5SAR.cs_of_preserved R1 R3 x RP3 Hx)).
  assert (Y2 := T2). rewrite <- (RG3 2%nat ltac:(inl)) in Y2. assert (Y8 := T8). rewrite <- (RG3 8%nat ltac:(inl)) in Y8.
  assert (Y9 := T9). rewrite <- (RG3 9%nat ltac:(inl)) in Y9. assert (Y18 := T18). rewrite <- (RG3 18%nat ltac:(inl)) in Y18.
  assert (Y19 := T19). rewrite <- (RG3 19%nat ltac:(inl)) in Y19. assert (Y20 := T20). rewrite <- (RG3 20%nat ltac:(inl)) in Y20.
  assert (Y22 := T22). rewrite <- (RG3 22%nat ltac:(inl)) in Y22. assert (Y23 := T23). rewrite <- (RG3 23%nat ltac:(inl)) in Y23.
  assert (Y24 := T24). rewrite <- (RG3 24%nat ltac:(inl)) in Y24. assert (Y25 := T25). rewrite <- (RG3 25%nat ltac:(inl)) in Y25.
  assert (Y26 := T26). rewrite <- (RG3 26%nat ltac:(inl)) in Y26.
  assert (Y21 : getr R3 (reg 21) = getr R (reg 21)) by (rewrite (RG3 21%nat) by inl; exact T21).
  assert (Y3 : getr R3 (reg 3) = getr R0 (reg 3)) by (rewrite (RG3 3%nat) by inl; rewrite (KS1 3%nat) by inl; exact X3).
  assert (Y4 : getr R3 (reg 4) = getr R0 (reg 4)) by (rewrite (RG3 4%nat) by inl; rewrite (KS1 4%nat) by inl; exact X4).
  match goal with H : getr R (reg 27) = _ |- _ => assert (Y27 := H) end.
  rewrite <- (KS1 27%nat ltac:(inl)), <- (RG3 27%nat ltac:(inl)) in Y27.
  assert (NDST : forall i, (sp - 160 - 16 <= i < sp) \/ (F <= i < F + 120 /\ ~ (F + 24 <= i < F + 32)) \/ (F / 8 + SB <= i < F / 8 + SB + 16)
                    \/ (os <= i < os + 296) \/ ((os + 8) / 8 + SB <= i < (os + 8) / 8 + SB + 36)
                    \/ ((ois <= i < ois + 272) \/ (ois / 8 + SB <= i < ois / 8 + SB + 34)) -> ~ (p <= i < p + PM.CHUNK)).
  { intros i RGi Y. destruct (DX i Y) as (D1 & D2 & D3 & _).
    destruct RGi as [Z|[Z|[Z|[Z|[Z|[Z|Z]]]]]].
    - apply D1. clear - Z. unfold PMSPA.pm_scr. lia.
    - apply (GNCF i); [left; clear - Z; lia| apply PMASR1.cl_of_bf; exact (DCL i Y)].
    - clear - Z Y DSH GFR. unfold BIGSHADOW_LO, BIGSHADOW_HI, SB in *. lia.
    - apply D3. exact Z.
    - clear - Z Y DSH KB V36. unfold BIGSHADOW_LO, BIGSHADOW_HI, SB in *. lia.
    - apply D2. exact Z.
    - clear - Z Y DSH KB V45. unfold BIGSHADOW_LO, BIGSHADOW_HI, SB in *. lia. }
  assert (AG31 : forall i, 0 <= i < 2 ^ 64 ->
      (V 2%nat - 160 <= i < V 2%nat) \/ (32 * V 50%nat <= i < 32 * V 50%nat + 120 /\ ~ (32 * V 50%nat + 24 <= i < 32 * V 50%nat + 32))
      \/ (4 * V 50%nat + SB <= i < 4 * V 50%nat + SB + 16) \/ (V 36%nat <= i < V 36%nat + 296)
      \/ ((V 36%nat + 8) / 8 + SB <= i < (V 36%nat + 8) / 8 + SB + 36)
      \/ (V 45%nat <= i < V 45%nat + 40) \/ (V 45%nat + 48 <= i < V 45%nat + 272)
      \/ (V 45%nat / 8 + SB <= i < V 45%nat / 8 + SB + 34) ->
      MV3 (Z_to_bv 64 i) = M1v (Z_to_bv 64 i)).
  { intros i Hi RGi.
    assert (RG' : (sp - 160 - 16 <= i < sp) \/ (F <= i < F + 120 /\ ~ (F + 24 <= i < F + 32)) \/ (F / 8 + SB <= i < F / 8 + SB + 16)
                  \/ (os <= i < os + 296) \/ ((os + 8) / 8 + SB <= i < (os + 8) / 8 + SB + 36)
                  \/ ((ois <= i < ois + 272) \/ (ois / 8 + SB <= i < ois / 8 + SB + 34))) by (clear - RGi V2 V50 V36 V45; lia).
    assert (NX : ~ (ois + 40 <= i < ois + 40 + 8)).
    { intros Y. rewrite <- V45 in Y. unfold SB in RGi.
      destruct RGi as [Z|[Z|[Z|[Z|[Z|[Z|[Z|Z]]]]]]];
        first [ clear - Z Y; lia | clear - Z Y KB; lia | match goal with D : _ \/ _ |- _ => clear - Z Y KB D; lia end ]. }
    unfold MV3. rewrite (srd_ag2 O R0 M0 model0 K OB LBX FF LK Aw cr sp r (PM.SRC qc de 0) str (PM.STRM g eg 0) Wextra F fl LK2 M2 model2
               M1 model1 LKc Ac M3 model3 LK3 Ac3 (PMSPA.pm_scr 2) (ois + 40) 8 p PM.CHUNK i CTX FR BI1 BI3 HP3 Hi RG' NX (NDST i RG')).
    rewrite HID1, MRT1. reflexivity. }
  unfold SB in AG31.
  assert (AG3V : forall i, 0 <= i < 2 ^ 64 ->
      (V 2%nat - 160 <= i < V 2%nat - 152) \/ (V 2%nat - 136 <= i < V 2%nat - 112) \/ (V 2%nat - 104 <= i < V 2%nat)
      \/ (V 36%nat <= i < V 36%nat + 296) \/ ((V 36%nat + 8) / 8 + SB <= i < (V 36%nat + 8) / 8 + SB + 36)
      \/ (V 45%nat <= i < V 45%nat + 40) \/ (V 45%nat + 48 <= i < V 45%nat + 272)
      \/ (V 45%nat / 8 + SB <= i < V 45%nat / 8 + SB + 34) ->
      MV3 (Z_to_bv 64 i) = MV (Z_to_bv 64 i)).
  { intros i Hi RGi. unfold SB in RGi. rewrite (AG31 i Hi) by (clear - RGi; lia).
    apply AG1; [exact Hi|..]; intros Z; destruct RGi as [Y|[Y|[Y|[Y|[Y|[Y|[Y|Y]]]]]]];
      first [ clear - Y Z; lia | clear - Y Z KB; lia | match goal with D : _ \/ _ |- _ => clear - Y Z KB D; lia end ]. }
  unfold SB in AG3V.
  assert (S56 : L5.u64_at RSEGS MV3 ((V 2%nat) - 40) (bv_unsigned (getr R3 (reg 21)))).
  { rewrite Y21. cw MV AG3V KB ltac:(idtac; sfind). }
  assert (MF3 : (L5.img_clear MV3 65536 1282048)
      /\ (L5.u64_at RSEGS MV3 1309752 2147450880)
      /\ (L5.u32_at RSEGS MV3 1309760 1)
      /\ (L5.writable RSEGS MV3 ((V 2%nat) - 160) 160)
      /\ (L5KA.zeros_at MV3 ((((V 36%nat) + 8) / 8) + 2147450880) 36)
      /\ (L5.writable RSEGS MV3 (V 36%nat) 296)
      /\ (L5.u64_at RSEGS MV3 ((V 36%nat) + 264) (V 34%nat))
      /\ (L5.u64_at RSEGS MV3 ((V 36%nat) + 272) 16384)
      /\ (L5.u64_at RSEGS MV3 ((V 36%nat) + 280) (V 35%nat))
      /\ (L5.defined MV3 ((V 36%nat) + 256) 8)
      /\ (L5.u64_at RSEGS MV3 ((V 36%nat) + 288) 0)
      /\ (L5KA.zeros_at MV3 (((V 45%nat) / 8) + 2147450880) 34)
      /\ (L5.writable RSEGS MV3 (V 45%nat) 272)
      /\ (L5.u64_at RSEGS MV3 ((V 36%nat) + 240) (V 45%nat))
      /\ (L5.u64_at RSEGS MV3 ((V 36%nat) + 248) ((V 45%nat) + 16))
      /\ (L5.u64_at RSEGS MV3 (V 45%nat) 1265968)
      /\ (L5.u64_at RSEGS MV3 ((V 45%nat) + 16) 1265728)
      /\ (L5.u32_at RSEGS MV3 ((V 45%nat) + 152) 0)
      /\ (L5.u32_at RSEGS MV3 ((V 45%nat) + 156) 0)
      /\ (L5.u64_at RSEGS MV3 ((V 45%nat) + 160) ((V 45%nat) + 16))
      /\ (L5KA.zeros_at MV3 2147609123 1)
      /\ (L5KA.zeros_at MV3 2147609104 1)
      /\ (L5.defined MV3 (32 * (V 50%nat)) 128)
      /\ (L5.writable RSEGS MV3 (32 * (V 50%nat)) 128)
      /\ (L5.writable RSEGS MV3 ((4 * (V 50%nat)) + 2147450880) 16)
      /\ (L5.writable RSEGS MV3 (V 51%nat) 1)
      /\ (L5.u64_at RSEGS MV3 ((V 2%nat) - 152) ((32 * (V 50%nat)) + 32))
      /\ (L5.u64_at RSEGS MV3 ((V 2%nat) - 144) (32 * (V 50%nat)))
      /\ (L5.u64_at RSEGS MV3 ((V 2%nat) - 112) (32 * (V 50%nat)))
      /\ (L5.u64_at RSEGS MV3 ((32 * (V 50%nat)) + 32) (V 38%nat))
      /\ (L5.u8_at RSEGS MV3 ((4 * (V 50%nat)) + 2147450891) 243)
      /\ (L5.u8_at RSEGS MV3 ((4 * (V 50%nat)) + 2147450890) 243)
      /\ (L5.u8_at RSEGS MV3 ((4 * (V 50%nat)) + 2147450889) 243)
      /\ (L5.u8_at RSEGS MV3 ((4 * (V 50%nat)) + 2147450888) 248)
      /\ (L5.u8_at RSEGS MV3 ((4 * (V 50%nat)) + 2147450883) 241)
      /\ (L5.u8_at RSEGS MV3 ((4 * (V 50%nat)) + 2147450882) 241)
      /\ (L5.u8_at RSEGS MV3 ((4 * (V 50%nat)) + 2147450881) 241)
      /\ (L5.u8_at RSEGS MV3 ((4 * (V 50%nat)) + 2147450880) 241)
      /\ (L5.u8_at RSEGS MV3 ((4 * (V 50%nat)) + 2147450887) 242)
      /\ (L5.u8_at RSEGS MV3 ((4 * (V 50%nat)) + 2147450886) 242)
      /\ (L5.u8_at RSEGS MV3 ((4 * (V 50%nat)) + 2147450885) 242)
      /\ (L5.u8_at RSEGS MV3 ((4 * (V 50%nat)) + 2147450884) 0)
      /\ (L5.u64_at RSEGS MV3 ((32 * (V 50%nat)) + 16) 716108)
      /\ (L5.u64_at RSEGS MV3 ((32 * (V 50%nat)) + 8) 127274)
      /\ (L5.u64_at RSEGS MV3 (32 * (V 50%nat)) 1102416563)
      /\ (L5.u64_at RSEGS MV3 ((V 2%nat) - 136) (V 37%nat))
      /\ (L5.u64_at RSEGS MV3 ((V 2%nat) - 88) (V 27%nat))
      /\ (L5.u64_at RSEGS MV3 ((V 2%nat) - 80) (V 26%nat))
      /\ (L5.u64_at RSEGS MV3 ((V 2%nat) - 72) (V 25%nat))
      /\ (L5.u64_at RSEGS MV3 ((V 2%nat) - 64) (V 24%nat))
      /\ (L5.u64_at RSEGS MV3 ((V 2%nat) - 56) (V 23%nat))
      /\ (L5.u64_at RSEGS MV3 ((V 2%nat) - 48) (V 22%nat))
      /\ (L5.u64_at RSEGS MV3 ((V 2%nat) - 40) (bv_unsigned (getr R3 (reg 21))))
      /\ (L5.u64_at RSEGS MV3 ((V 2%nat) - 32) (V 20%nat))
      /\ (L5.u64_at RSEGS MV3 ((V 2%nat) - 24) (V 19%nat))
      /\ (L5.u64_at RSEGS MV3 ((V 2%nat) - 16) (V 18%nat))
      /\ (L5.u64_at RSEGS MV3 ((V 2%nat) - 8) (V 9%nat))
      /\ (L5.u64_at RSEGS MV3 (V 2%nat) (V 8%nat))
      /\ (L5.u64_at RSEGS MV3 ((V 2%nat) + 8) (V 1%nat))
      /\ (L5.defined MV3 ((32 * (V 50%nat)) + 24) 8)
      /\ (L5.defined MV3 ((32 * (V 50%nat)) + 40) 88)
      /\ (L5.u64_at RSEGS MV3 ((32 * (V 50%nat)) + 120) (V 51%nat))
      /\ (L5.writable RSEGS MV3 ((V 2%nat) - 160) 176)).
  { sweep ltac:(idtac; first [ sfind
                             | lazymatch goal with |- L5KA.zeros_at _ _ 1 => first [ exact VT1 | exact VT2 ] end
                             | cw MV AG3V KB ltac:(idtac; sfind)
                             | cw M1v AG31 KB ltac:(idtac; sfind) ]). }
  pick MF3.
  set (VE := fun j : nat => match j with 33%nat => c
       | 61%nat => bv_unsigned (getr R3 (reg 1)) | 62%nat => bv_unsigned (getr R3 (reg 5)) | 63%nat => bv_unsigned (getr R3 (reg 6))
       | 64%nat => bv_unsigned (getr R3 (reg 7)) | 65%nat => bv_unsigned (getr R3 (reg 12)) | 66%nat => bv_unsigned (getr R3 (reg 13))
       | 67%nat => bv_unsigned (getr R3 (reg 14)) | 68%nat => bv_unsigned (getr R3 (reg 15)) | 69%nat => bv_unsigned (getr R3 (reg 16))
       | 70%nat => bv_unsigned (getr R3 (reg 17)) | 71%nat => bv_unsigned (getr R3 (reg 28)) | 72%nat => bv_unsigned (getr R3 (reg 29))
       | 73%nat => bv_unsigned (getr R3 (reg 30)) | 74%nat => bv_unsigned (getr R3 (reg 31)) | _ => V j end).
  assert (VO5 : forall (M5 M5v : mem), (forall a : word, ahid Ac3 model3 a = false -> M5 a = M5v a) ->
      forall i, V 36%nat <= i < V 36%nat + 296 -> M5 (Z_to_bv 64 i) = M5v (Z_to_bv 64 i)).
  { intros M5 M5v VIS5 i Hi. apply VIS5.
    apply (PGSRDC16.srd_vis L ar C HI LY HIok O R0 M0 model0 K OB LBX FF LK Aw cr sp r (PM.SRC qc de 0) str (PM.STRM g eg 0) Wextra F fl LK2 M2 model2
             M3 model3 LK3 Ac3 i CTX FR BI3).
    right; right; right; left. clear - Hi V36. lia. }
  assert (SV5 : forall R5, forall i, In i [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> PGSRDC16.vx V R5 i = bv_unsigned (getr R0 (reg i))).
  { intros R5 i Hi. rewrite <- (VSV i Hi). cbn in Hi. repeat destruct Hi as [<-|Hi]; first [reflexivity | destruct Hi]. }
  destruct (Z.eq_dec c PM.CHUNK) as [CF|CNF].
  - assert (A10E : getr R3 (reg 10) = Z_to_bv 64 PM.CHUNK) by (rewrite A10c, CF; reflexivity). rewrite CHv in A10E.
    pose proof (PMASRP.asrE116_conc fx3 R3 MV3 VE) as P5. unfold VE in P5. cbn beta iota in P5.
    feed P5 ltac:(idtac; dsp ltac:(idtac; clear - KB C0 CF CHv; lia) ltac:(idtac; sfind)).
    destruct P5 as (fx5 & R5 & M5v & MG5 & _ & AG5 & MS5 & KS5 & Z1 & Z2 & Z8 & Z9 & Z10 & Z18 & Z19 & Z20 & Z21 & Z22 & Z23 & Z24).
    apply (PGSRDC16.srd_piece L ar C HI LY HIok O R0 M0 model0 K OB LBX FF LK Aw cr sp r (PM.SRC qc de 0) str (PM.STRM g eg 0) Wextra F fl LK2 M2 model2
             M3 model3 LK3 Ac3 fx3 fx5 R3 R5 _ _ M5v (fun a => V 36%nat + 256 <= a < V 36%nat + 256 + 8) CTX FR BI3 MS5 MG5).
    { intros a Ha NW. cbn beta in NW. apply AG5; [exact Ha| exact NW]. }
    { intros a Wa. cbn beta in Wa. right; right; left. clear - Wa V36. lia. }
    intros M5 model5 BI5 HID5 MRT5 MGM5 FR5 VIS5 EK5.
    assert (X3' : getr R5 (reg 3) = getr R0 (reg 3)) by (rewrite KS5 by inl; exact Y3).
    assert (X4' : getr R5 (reg 4) = getr R0 (reg 4)) by (rewrite KS5 by inl; exact Y4).
    assert (STR5 : PGSRDK16.srd_stR (PGSRDC16.vx V R5) R5 M5v).
    { unfold PGSRDK16.srd_stR, PGSRDC16.vx. cbn beta iota.
      sweep ltac:(idtac; dsp ltac:(idtac; clear - KB; lia)
                      ltac:(idtac; first [ (rewrite KS5 by inl; sfind)
                                  | (eapply L5.writable_grows; [exact MG5| sfind])
                                  | (eapply L5.defined_grows; [exact MG5| sfind])
                                  | carry_with MV3 AG5 KB ltac:(idtac; sfind) ])). }
    assert (STR5' : PGSRDK16.srd_stR (PGSRDC16.vx V R5) R5 (mrestrict (ahid Ac3 model5) M5)) by (rewrite HID5, MRT5; exact STR5).
    assert (V76 : PGSRDC16.vx V R5 76%nat = c).
    { unfold PGSRDC16.vx. cbn beta iota. rewrite Z22, L5.unsigned_lit by (clear; lia). rewrite CF. reflexivity. }
    assert (U264 : L5.u64_at RSEGS M5 (os + 264) qc).
    { rewrite <- V34. replace (os + 264) with (V 36%nat + 264) by (clear - V36; lia).
      apply (L5C.u64_at_agree RSEGS M5v M5); [intros i Hi; apply (VO5 M5 M5v VIS5); clear - Hi; lia| sd KB| sd KB|].
      carry_with MV3 AG5 KB ltac:(idtac; sfind). }
    assert (U272 : L5.u64_at RSEGS M5 (os + 272) PM.CHUNK).
    { rewrite CHv. replace (os + 272) with (V 36%nat + 272) by (clear - V36; lia).
      apply (L5C.u64_at_agree RSEGS M5v M5); [intros i Hi; apply (VO5 M5 M5v VIS5); clear - Hi; lia| sd KB| sd KB|].
      carry_with MV3 AG5 KB ltac:(idtac; sfind). }
    assert (U280 : L5.u64_at RSEGS M5 (os + 280) de).
    { rewrite <- V35. replace (os + 280) with (V 36%nat + 280) by (clear - V36; lia).
      apply (L5C.u64_at_agree RSEGS M5v M5); [intros i Hi; apply (VO5 M5 M5v VIS5); clear - Hi; lia| sd KB| sd KB|].
      carry_with MV3 AG5 KB ltac:(idtac; sfind). }
    assert (U288 : L5.u64_at RSEGS M5 (os + 288) 0).
    { replace (os + 288) with (V 36%nat + 288) by (clear - V36; lia).
      apply (L5C.u64_at_agree RSEGS M5v M5); [intros i Hi; apply (VO5 M5 M5v VIS5); clear - Hi; lia| sd KB| sd KB|].
      carry_with MV3 AG5 KB ltac:(idtac; sfind). }
    assert (ISS5 : PM.iss_at RSEGS PMA.AD PMSPA.accA M5 ois str (PM.STRM (g + c) eg 0)) by exact (ISSG M3 M5 _ EK5 WOS OI_os OS_os _ IA3).
    assert (DEF5 : L5.defined M5 p c) by exact (L5.defined_grows M3 M5 p c MGM5 DF3).
    assert (A3 : de + 0 <= qc + PM.CHUNK) by exact G3.
    assert (A4 : g <= g + c <= eg) by (clear - C0; lia).
    assert (A6 : 0 + (eg - g) - (0 + (eg - (g + c))) = c) by (clear; lia).
    assert (A7 : 1 <= 0 -> 1 <= c) by (intros X; exfalso; clear - X; lia).
    assert (A8 : c = 0 -> 0 = 0 /\ 0 = 2) by (intros X; exfalso; clear - X CF CHv; lia).
    exact (EXIT fx5 R5 M5 model5 LK3 Ac3 (PGSRDC16.vx V R5) BI5 V2 V36 V37 V38 V50 V51 (SV5 R5) X3' X4' de 0 (g + c) 0 c
             STR5' V76 U264 U272 U280 U288 G1 (Z.le_refl 0) A3 ISS5 A4 (fun X => X) (proj1 C0) A6 A7 A8 DEF5).
  - pose proof (PMASRP.asrE216_conc fx3 R3 MV3 VE) as P5. unfold VE in P5. cbn beta iota in P5.
    feed P5 ltac:(idtac; dsp ltac:(idtac; clear - KB C0 CNF CHv; lia) ltac:(idtac; sfind)).
    destruct P5 as (fx5 & R5 & M5v & MG5 & _ & AG5 & MS5 & KS5 & Z1 & Z2 & Z8 & Z9 & Z10 & Z12 & Z13 & Z18 & Z19 & Z20 & Z21 & Z22 & Z23 & Z24 & V152).
    apply (srd_pieceI O R0 M0 model0 K OB LBX FF LK Aw cr sp r (PM.SRC qc de 0) str (PM.STRM g eg 0) Wextra F fl LK2 M2 model2
             M3 model3 LK3 Ac3 fx3 fx5 R3 R5 _ _ M5v
             (fun a => (V 36%nat + 256 <= a < V 36%nat + 256 + 8) \/ (V 45%nat + 152 <= a < V 45%nat + 152 + 4)) CTX FR BI3 MS5 MG5).
    { intros a Ha NW. cbn beta in NW. apply AG5; [exact Ha| intros Y; apply NW; left; exact Y| intros Y; apply NW; right; exact Y]. }
    { intros a Wa. cbn beta in Wa. destruct Wa as [Y|Y]; [left; clear - Y V36; lia| right; clear - Y V45; lia]. }
    intros M5 model5 BI5 HID5 MRT5 MGM5 FR5 VIS5 EK5.
    assert (X3' : getr R5 (reg 3) = getr R0 (reg 3)) by (rewrite KS5 by inl; exact Y3).
    assert (X4' : getr R5 (reg 4) = getr R0 (reg 4)) by (rewrite KS5 by inl; exact Y4).
    assert (STR5 : PGSRDK16.srd_stR (PGSRDC16.vx V R5) R5 M5v).
    { unfold PGSRDK16.srd_stR, PGSRDC16.vx. cbn beta iota.
      sweep ltac:(idtac; dsp ltac:(idtac; clear - KB; lia)
                      ltac:(idtac; first [ (rewrite KS5 by inl; sfind)
                                  | (eapply L5.writable_grows; [exact MG5| sfind])
                                  | (eapply L5.defined_grows; [exact MG5| sfind])
                                  | carry_with MV3 AG5 KB ltac:(idtac; sfind) ])). }
    assert (STR5' : PGSRDK16.srd_stR (PGSRDC16.vx V R5) R5 (mrestrict (ahid Ac3 model5) M5)) by (rewrite HID5, MRT5; exact STR5).
    assert (V76 : PGSRDC16.vx V R5 76%nat = c).
    { unfold PGSRDC16.vx. cbn beta iota. rewrite Z22, L5.unsigned_lit by (clear - C0 CHv; lia). reflexivity. }
    assert (U264 : L5.u64_at RSEGS M5 (os + 264) qc).
    { rewrite <- V34. replace (os + 264) with (V 36%nat + 264) by (clear - V36; lia).
      apply (L5C.u64_at_agree RSEGS M5v M5); [intros i Hi; apply (VO5 M5 M5v VIS5); clear - Hi; lia| sd KB| sd KB|].
      carry_with MV3 AG5 KB ltac:(idtac; sfind). }
    assert (U272 : L5.u64_at RSEGS M5 (os + 272) PM.CHUNK).
    { rewrite CHv. replace (os + 272) with (V 36%nat + 272) by (clear - V36; lia).
      apply (L5C.u64_at_agree RSEGS M5v M5); [intros i Hi; apply (VO5 M5 M5v VIS5); clear - Hi; lia| sd KB| sd KB|].
      carry_with MV3 AG5 KB ltac:(idtac; sfind). }
    assert (U280 : L5.u64_at RSEGS M5 (os + 280) de).
    { rewrite <- V35. replace (os + 280) with (V 36%nat + 280) by (clear - V36; lia).
      apply (L5C.u64_at_agree RSEGS M5v M5); [intros i Hi; apply (VO5 M5 M5v VIS5); clear - Hi; lia| sd KB| sd KB|].
      carry_with MV3 AG5 KB ltac:(idtac; sfind). }
    assert (U288 : L5.u64_at RSEGS M5 (os + 288) 0).
    { replace (os + 288) with (V 36%nat + 288) by (clear - V36; lia).
      apply (L5C.u64_at_agree RSEGS M5v M5); [intros i Hi; apply (VO5 M5 M5v VIS5); clear - Hi; lia| sd KB| sd KB|].
      carry_with MV3 AG5 KB ltac:(idtac; sfind). }
    assert (VI5 : forall i, ois <= i < ois + 272 -> M5 (Z_to_bv 64 i) = M5v (Z_to_bv 64 i)).
    { intros i Hi. apply VIS5.
      apply (srd_visI O R0 M0 model0 K OB LBX FF LK Aw cr sp r (PM.SRC qc de 0) str (PM.STRM g eg 0) Wextra F fl LK2 M2 model2 M3 model3 LK3 Ac3 i CTX FR BI3).
      left. exact Hi. }
    assert (U152 : L5.u32_at RSEGS M5 (ois + 152) 2).
    { replace (ois + 152) with (V 45%nat + 152) by (clear - V45; lia).
      apply (PMF.u32_at_agree RSEGS M5v M5); [intros i Hi; apply VI5; clear - Hi V45; lia| sd KB| sd KB| exact V152]. }
    assert (WSE : PMKA.wapp [(PGS.ow_os O + 256, 40); (PGS.ow_ois O + 152, 4)]).
    { apply PMKA.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI in *; clear - OBIG; lia|].
      apply PMKA.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI in *; clear - IBIG; lia| apply PMKA.wapp_nil]. }
    assert (OUTI : forall i, ois <= i < ois + 272 -> ~ (ois + 152 <= i < ois + 156) -> L5.outside [(PGS.ow_os O + 256, 40); (PGS.ow_ois O + 152, 4)] i).
    { intros i Hi N r0 [<-|[<-|[]]]; unfold L5.in_rng; cbn [fst snd]; [clear - Hi LYD; lia| clear - N; lia]. }
    assert (ISS5 : PM.iss_at RSEGS PMA.AD PMSPA.accA M5 ois str (PM.STRM (g + c) eg 2)).
    { apply (PMASK.iss_st_updA M3 M5 ois str (g + c) eg 0 2 IA3); [clear - I1; lia| clear - I1; lia| | | | exact MGM5| | exact U152| right; reflexivity].
      - apply (PMKA.agA_obj L ar LB FF sp (PMSPA.pm_scr 4) _ M3 M5 EK5 WSE FRB ois 152); [apply (PGSKA.aobjA_sub FF lo hi); [exact OFR| clear - LY3; lia| clear - LY4; lia]|].
        intros i Hi. apply OUTI; clear - Hi; lia.
      - apply (PMKA.agA_obj L ar LB FF sp (PMSPA.pm_scr 4) _ M3 M5 EK5 WSE FRB (ois + 156) 116); [apply (PGSKA.aobjA_sub FF lo hi); [exact OFR| clear - LY3; lia| clear - LY4; lia]|].
        intros i Hi. apply OUTI; clear - Hi; lia.
      - apply (PMKA.agsh_obj L ar LB FF sp (PMSPA.pm_scr 4) _ M3 M5 EK5 WSE FRB (ois + 152) 4). apply (PGSKA.aobjA_sub FF lo hi); [exact OFR| clear - LY3; lia| clear - LY4; lia].
      - intros c1 n1 q1 E. assert (SIN : In (q1, c1) LB) by (apply SOWN; rewrite E; left; reflexivity).
        apply (PMKA.agA_blk L ar LB FF sp (PMSPA.pm_scr 4) _ M3 M5 EK5 WSE BRB q1 c1 SIN). intros i Hi r0 [<-|[<-|[]]]; unfold L5.in_rng; cbn [fst snd].
        + destruct (PMASK.blk_obj_apart L ar C HI HIok LB FF LK cr Aw M0 _ q1 c1 os 296 HH SIN AO) as [Z|Z]; clear - Hi Z; lia.
        + destruct (PMASK.blk_obj_apart L ar C HI HIok LB FF LK cr Aw M0 _ q1 c1 ois 272 HH SIN AOI) as [Z|Z]; clear - Hi Z; lia. }
    assert (DEF5 : L5.defined M5 p c) by exact (L5.defined_grows M3 M5 p c MGM5 DF3).
    assert (A3 : de + 0 <= qc + PM.CHUNK) by exact G3.
    assert (A4 : g <= g + c <= eg) by (clear - C0; lia).
    assert (A6 : 0 + (eg - g) - (0 + (eg - (g + c))) = c) by (clear; lia).
    assert (A7 : 1 <= 0 -> 1 <= c) by (intros X; exfalso; clear - X; lia).
    assert (A8 : c = 0 -> 0 = 0 /\ 2 = 2) by (intros _; split; reflexivity).
    exact (EXIT fx5 R5 M5 model5 LK3 Ac3 (PGSRDC16.vx V R5) BI5 V2 V36 V37 V38 V50 V51 (SV5 R5) X3' X4' de 0 (g + c) 2 c
             STR5' V76 U264 U272 U280 U288 G1 (Z.le_refl 0) A3 ISS5 A4 (fun _ => eq_refl) (proj1 C0) A6 A7 A8 DEF5).
Qed.

End A0d.
End PGSRDA0D16.
