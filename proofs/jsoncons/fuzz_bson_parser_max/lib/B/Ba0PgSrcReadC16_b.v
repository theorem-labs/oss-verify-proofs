(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnASrcKit_b PgSrcKitA_b PnASrcRead1_b PnASrcReadK_b PnASrcReadP_b Ba0PgSrcReadK16_b.
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

Module PGSRDC16.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := PGSRDK16.RSEGS.
Abbreviation mem := (word -> option byte).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom PGSRDK16.RSEGS)) (only parsing).
Ltac pick_st H := unfold PGSRDK16.srd_stC in H; let H' := fresh in pose proof H as H';
  repeat match type of H' with _ /\ _ => let X := fresh in destruct H' as (X & H') end.
Ltac sd KB := first [ clear - KB; lia | match goal with H : _ \/ _ |- _ => clear - KB H; lia end ].
Ltac sdi Hii KB := first [ clear - Hii; lia | clear - Hii KB; lia | match goal with H : _ \/ _ |- _ => clear - Hii KB H; lia end ].
Ltac carry Ms AG KB :=
  lazymatch goal with
  | |- L5.u64_at ?s ?Mt ?a ?v => apply (L5C.u64_at_agree s Ms Mt a v); [let ii := fresh in let Hii := fresh in intros ii Hii; apply AG; sdi Hii KB| sd KB| sd KB| assumption]
  | |- L5.u32_at ?s ?Mt ?a ?v => apply (PMF.u32_at_agree s Ms Mt a v); [let ii := fresh in let Hii := fresh in intros ii Hii; apply AG; sdi Hii KB| sd KB| sd KB| assumption]
  | |- L5.u8_at ?s ?Mt ?a ?v => apply (L5C.u8_at_agree s Ms Mt a v); [let ii := fresh in let Hii := fresh in intros ii Hii; apply AG; sdi Hii KB| sd KB| sd KB| assumption]
  | |- L5.defined ?Mt ?a ?n => apply (L5C.defined_agree Ms Mt a n); [let ii := fresh in let Hii := fresh in intros ii Hii; apply AG; sdi Hii KB| assumption]
  | |- L5.writable ?s ?Mt ?a ?n => apply (L5C.writable_agree s Ms Mt a n); [let ii := fresh in let Hii := fresh in intros ii Hii; apply AG; sdi Hii KB| sd KB| sd KB| assumption]
  | |- L5KA.zeros_at ?Mt ?a ?n => apply (L5KA.zeros_at_agree1 Ms Mt a n); [let ii := fresh in let Hii := fresh in intros ii Hii; apply AG; sdi Hii KB| assumption]
  | |- L5.img_clear ?Mt ?lo ?hi => let ii := fresh in let Hii := fresh in intros ii Hii; rewrite (AG ii) by sdi Hii KB;
      match goal with H : L5.img_clear Ms lo hi |- _ => exact (H ii Hii) end
  end.
Ltac sweep tac := lazymatch goal with
  | |- _ /\ _ => split; [first [solve [tac] | match goal with |- ?G => fail 100 "sweep" G end] | sweep tac]
  | |- _ => first [solve [tac] | match goal with |- ?G => fail 100 "sweep" G end]
  end.
Definition vx (V : nat -> Z) (R : bvmap 5 word) : nat -> Z := fun i =>
  match i with
  | 52%nat => bv_unsigned (getr R (reg 30)) | 53%nat => bv_unsigned (getr R (reg 31))
  | 61%nat => bv_unsigned (getr R (reg 1)) | 62%nat => bv_unsigned (getr R (reg 5)) | 63%nat => bv_unsigned (getr R (reg 6))
  | 64%nat => bv_unsigned (getr R (reg 7)) | 65%nat => bv_unsigned (getr R (reg 10)) | 66%nat => bv_unsigned (getr R (reg 11))
  | 67%nat => bv_unsigned (getr R (reg 12)) | 68%nat => bv_unsigned (getr R (reg 13)) | 69%nat => bv_unsigned (getr R (reg 14))
  | 70%nat => bv_unsigned (getr R (reg 15)) | 71%nat => bv_unsigned (getr R (reg 16)) | 72%nat => bv_unsigned (getr R (reg 17))
  | 73%nat => bv_unsigned (getr R (reg 18)) | 74%nat => bv_unsigned (getr R (reg 20)) | 75%nat => bv_unsigned (getr R (reg 21))
  | 76%nat => bv_unsigned (getr R (reg 22)) | 77%nat => bv_unsigned (getr R (reg 24)) | 78%nat => bv_unsigned (getr R (reg 28))
  | 79%nat => bv_unsigned (getr R (reg 29)) | _ => V i
  end.
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Variable IL : icpt_layout.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Let LYa := PMA.ly_as0 L C LY.

Lemma srd_piece O R0 M0 model0 K OB LBX FF LK Aw cr sp r src str sm Wextra F fl LK2 M2 model2 M model LKc Ac
    (fx fx1 : FPState) R R1 (pc pc1 : Z) (M1v : mem) (Wp : Z -> Prop) :
  PGSRDK16.srd_ctx L ar HI 16 O R0 M0 model0 K OB LBX FF LK Aw cr sp r src str sm Wextra ->
  PGSRDK16.srd_frame L ar HI 16 R0 OB LBX FF LK Aw cr sp src F fl LK2 M2 model2 ->
  PGSRDK16.srd_body L ar HI 16 O R0 M0 model0 OB LBX FF LK Aw sp src Wextra F M model LKc cr Ac ->
  msteps RSEGS (st fx R pc (mrestrict (ahid Ac model) M)) (st fx1 R1 pc1 M1v) ->
  mem_grows (mrestrict (ahid Ac model) M) M1v ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Wp a -> M1v (Z_to_bv 64 a) = mrestrict (ahid Ac model) M (Z_to_bv 64 a)) ->
  (forall a, Wp a -> (F <= a < F + 120 /\ ~ (F + 24 <= a < F + 32)) \/ F / 8 + SB <= a < F / 8 + SB + 16
                     \/ PGS.ow_os O + 256 <= a < PGS.ow_os O + 296 \/ sp - 160 - 16 <= a < sp - 104) ->
  (forall M1 model1, PGSRDK16.srd_body L ar HI 16 O R0 M0 model0 OB LBX FF LK Aw sp src Wextra F M1 model1 LKc cr Ac ->
      ahid Ac model1 = ahid Ac model -> mrestrict (ahid Ac model) M1 = M1v -> mem_grows M M1 ->
      (forall a, 0 <= a < 2 ^ 64 -> ~ Wp a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
      (forall a : word, ahid Ac model a = false -> M1 a = M1v a) ->
      L5SAR.ek L ar (PM.src_own src ++ OB ++ LBX) FF sp (PMSPA.pm_scr 4) [(PGS.ow_os O + 256, 40)] M M1 ->
      srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx1 R1 pc1 M1 model1) K) ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R pc M model) K.
Proof.
  intros CTX G BI MS MG FRZ WP KR.
  pose proof CTX as (OK & HH0 & _ & _ & _ & _ & _ & OFR & _).
  pose proof (PGSA.oo_lay _ _ _ _ _ _ OK) as (LY1 & LY2 & _).
  assert (AO : PMSPA.aobjA FF (PGS.ow_os O) 296).
  { apply (PGSKA.aobjA_sub FF (PGS.ow_lo O) (PGS.ow_hi O)); [exact OFR| exact LY1| exact LY2]. }
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH0) as (_ & WF & _ & FSCEIL & _).
  pose proof (PMASK.fs_above_img L ar C HI LY HIok _ _ _ _ _ _ _ HH0) as FSI.
  pose proof AO as (f & Hf & X1 & X2). destruct (WF f Hf) as (Y1 & Y2 & _).
  unfold PGSRDK16.srd_frame in G. unfold PGSRDK16.srd_body in BI.
  pose proof G as G'. destruct G' as [_ GSPT GSLO GSHI GSPC GOCR GOWN GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
  change (ff_bytes 1) with 128 in *. change (128 / 8) with 16 in *.
  pose proof BI as (B1 & B2 & _).
  unfold PMSPA.cfg, PMSP.cfg.
  apply (L5SAR.apiece L ar C HI LYa HIok _ _ _ _ _ _ _ fx fx1 R pc R1 pc1 M1v Wp K B1 B2 MS MG FRZ).
  - intros a Ha Wa. destruct (WP a Wa) as [Y|[Y|[Y|Y]]].
    + split.
      * unfold aclientw. apply (L5SAR.fframe_client L ar _ _ 0 0 F 1 (sp - 160 - 16 + 32)); [left; reflexivity|]. change (ff_bytes 1) with 128. clear - Y. lia.
      * clear - Y GFR. lia.
    + split.
      * unfold aclientw. apply (L5SAR.fframe_shadow_client L ar _ _ 0 0 F 1 (sp - 160 - 16 + 32)); [left; reflexivity|].
        change (ff_bytes 1) with 128. unfold in_shadow_of, S. destruct GF8 as (_ & GF8b & _). rewrite GF8b. clear - Y. lia.
      * clear - Y GFR. unfold SB in Y. lia.
    + split.
      * unfold aclientw. apply L5SAR.aclient_cons. apply PMASR1.cl_of_bf. right. apply (PMASR1.in_fframe_of_aobjA FF _ 296 a AO). clear - Y. lia.
      * clear - Y X1 Y1 FSI. lia.
    + split.
      * unfold aclientw. apply (L5SAR.stack_client L ar); [clear - Y GSLO GSPC; unfold PMSPA.pm_scr in GSLO; lia| clear; lia].
      * clear - Y GSLO GFCEIL GFS1 FSI. unfold PMSPA.pm_scr in GSLO. lia.
  - intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MG1 FR1 VV1.
    apply KR; [| exact HID1| exact VIS1| exact MG1| exact FR1| exact VV1|].
    2:{ intros a (Ha & Hc & Ho). apply FR1; [exact Ha|]. intros Wa. destruct (WP a Wa) as [Y|[Y|[Y|Y]]].
        - apply (GNCF a); [left; clear - Y; lia| exact Hc].
        - apply (GNCF a); [right; unfold S; destruct GF8 as (_ & GF8b & _); rewrite GF8b; clear - Y; lia| exact Hc].
        - apply (Ho (PGS.ow_os O + 256, 40)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; clear - Y; lia].
        - apply (GNCS a); [clear - Y; lia| exact Hc]. }
    unfold PGSRDK16.srd_body.
    eapply (PMAUK.binv_pieceW L ar HI); [exact G| exact BI| exact HH1| exact AM1| exact MRT1| exact MG1| exact FR1|].
    intros a Wa. unfold PNACSK.ocell. change (ff_bytes 1) with 128. change (128 / 8) with 16. destruct (WP a Wa) as [Y|[Y|[Y|Y]]].
    + split; [clear - Y GFCEIL GSLO GSPC; lia| right; left; clear - Y; lia].
    + split; [clear - Y GFR GF8 GFCEIL GSLO GSPC GSPT; unfold SB in Y; lia| right; right; left; clear - Y; lia].
    + split; [clear - Y X2 Y2 FSCEIL GSLO GSPC; lia|]. right; right; right. intros Oq.
      apply (Oq (PGS.ow_os O + 256, 40)); [unfold PGS.W_srcG, PGS.W_srcfG; apply in_or_app; left; apply in_or_app; left; left; reflexivity|].
      unfold L5.in_rng. cbn [fst snd]. clear - Y. lia.
    + split; [clear - Y; lia| left; clear - Y; lia].
Qed.

Lemma srd_call O R0 M0 model0 K OB LBX FF LK Aw cr sp r src str sm Wextra F fl LK2 M2 model2 M model LKc Ac
    (fx : FPState) R (ra dst sq n : Z) :
  PGSRDK16.srd_ctx L ar HI 16 O R0 M0 model0 K OB LBX FF LK Aw cr sp r src str sm Wextra ->
  PGSRDK16.srd_frame L ar HI 16 R0 OB LBX FF LK Aw cr sp src F fl LK2 M2 model2 ->
  PGSRDK16.srd_body L ar HI 16 O R0 M0 model0 OB LBX FF LK Aw sp src Wextra F M model LKc cr Ac ->
  getr R (reg 1) = Z_to_bv 64 ra -> L5.ra_ok ra -> getr R (reg 2) = Z_to_bv 64 (sp - 160 - 16) ->
  getr R (reg 4) = Z_to_bv 64 (hl_tp L) -> getr R (reg 10) = Z_to_bv 64 dst -> getr R (reg 11) = Z_to_bv 64 sq ->
  getr R (reg 12) = Z_to_bv 64 n -> 0 <= n <= PM.CHUNK ->
  aacc M dst n -> L5.defined M dst n -> 0 <= dst -> dst + n <= 2 ^ 47 -> app_rng ar dst n ->
  (forall i, 0 <= i < n -> in_block (PM.src_own src ++ OB ++ LBX) (dst + i) \/ in_fframe FF (dst + i)) ->
  (forall i, 0 <= i < n -> ~ (sp - PMSPA.pm_scr 4 <= dst + i < sp) /\
                           ~ L5.outside (PGS.W_srcG (PGS.ow_os O) (PGS.ow_ois O) src ++ Wextra) (dst + i)) ->
  aacc M sq n -> L5.defined M sq n -> 0 <= sq -> sq + n <= 2 ^ 47 -> app_rng ar sq n ->
  (forall i, 0 <= i < n -> in_block (PM.src_own src ++ OB ++ LBX) (sq + i)) ->
  (dst + n <= sq \/ sq + n <= dst) ->
  (forall (fx' : FPState) R' M' model', regs_preserved R R' -> L5.defined M' dst n ->
      PGSRDK16.srd_body L ar HI 16 O R0 M0 model0 OB LBX FF LK Aw sp src Wextra F M' model' LKc cr Ac ->
      L5CA.ahpres L ar ([] ++ (PM.src_own src ++ OB ++ LBX)) ((F, 1, sp - 160 - 16 + 32) :: FF) (sp - 160 - 16) 2560 [(dst, n)] M M' ->
      srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx' R' ra M' model') K) ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0x77c94 M model) K.
Proof.
  intros CTX G BI X1 RA X2 X4 X10 X11 X12 Hn ACD DDF D0 D1 APD CLD NSD ACS DSF S0 S1 APS CLS NOV KR.
  pose proof CTX as (_ & _ & _ & K0 & _ & _ & _ & _ & _ & SP32 & _).
  unfold PGSRDK16.srd_frame in G. unfold PGSRDK16.srd_body in BI.
  pose proof G as G'. destruct G' as [_ GSPT GSLO GSHI GSPC GOCR GOWN GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
  change (ff_bytes 1) with 128 in *. change (128 / 8) with 16 in *.
  pose proof BI as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10).
  assert (SCRv : PMSPA.pm_scr 4 = PMSPA.pm_scr 4) by reflexivity.
  unfold PMSPA.pm_scr in SCRv.
  apply (PMASRK.memcpy_call L ar C HI LY HIok fx R M model K _ _ _ _ _ (sp - 160 - 16) ra dst sq n B1 B2 K0 X1 RA X2 X4 X10 X11 X12).
  - unfold PM.CHUNK in Hn. clear - Hn. lia.
  - replace (sp - 160 - 16) with (sp - 176) by lia.
    apply (L5SAR.astk_sub ar M M sp (PMSPA.pm_scr 4) 176 2560 B6 (fun _ X => X)); [lia| lia| unfold PMSPA.pm_scr; lia|].
    clear - SP32. lia.
  - exact ACD.
  - intros i Hi. unfold aclientw. apply L5SAR.aclient_cons. apply PMASR1.cl_of_bf. exact (CLD i Hi).
  - exact DDF.
  - exact D0.
  - exact D1.
  - exact APD.
  - exact ACS.
  - exact S0.
  - exact S1.
  - exact APS.
  - intros i Hi. unfold aclient. apply L5SAR.aclient_cons. apply PMASR1.cl_of_bf. left. exact (CLS i Hi).
  - exact DSF.
  - exact NOV.
  - intros fx' R' M' model' RP DEF AH MRT AM HH.
    apply KR; [exact RP| exact DEF| | exact AH].
    unfold PGSRDK16.srd_body.
    eapply (PMAUK.binv_callee L ar C HI HIok); [exact G| exact BI| exact AH| exact HH| exact AM| exact MRT| apply incl_refl| apply incl_refl| lia| unfold PMSPA.pm_scr; lia| | |].
    + intros rr a [<-|[]] Ha. unfold L5.in_rng in Ha. cbn [fst snd] in Ha. change (ff_bytes 1) with 128. change (128 / 8) with 16.
      destruct (NSD (a - dst) ltac:(lia)) as (N1 & _). replace (dst + (a - dst)) with a in N1 by lia.
      unfold PNACSK.ocell. split; [unfold PMSPA.pm_scr in N1; lia|].
      intros Y. apply (GNCF a); [right; unfold S; destruct GF8 as (_ & GF8b & _); rewrite GF8b; lia|].
      apply PMASR1.cl_of_bf. replace a with (dst + (a - dst)) by lia. apply CLD. lia.
    + intros a _ Oq rr [<-|[]] X. unfold L5.in_rng in X. cbn [fst snd] in X.
      destruct (NSD (a - dst) ltac:(lia)) as (_ & N2). replace (dst + (a - dst)) with a in N2 by lia. exact (N2 Oq).
    + intros a X. exact X.
Qed.

Lemma mr_eq (H1 H2 : word -> bool) (Ma Mb : mem) a :
  H1 a = false -> H2 a = false -> Mb a = Ma a -> mrestrict H2 Mb a = mrestrict H1 Ma a.
Proof. intros X1 X2 E. rewrite (mrestrict_visible H2 Mb a X2), (mrestrict_visible H1 Ma a X1). exact E. Qed.

Lemma srd_vis O R0 M0 model0 K OB LBX FF LK Aw cr sp r src str sm Wextra F fl LK2 M2 model2 Mc modelc LKc Ac i :
  PGSRDK16.srd_ctx L ar HI 16 O R0 M0 model0 K OB LBX FF LK Aw cr sp r src str sm Wextra ->
  PGSRDK16.srd_frame L ar HI 16 R0 OB LBX FF LK Aw cr sp src F fl LK2 M2 model2 ->
  PGSRDK16.srd_body L ar HI 16 O R0 M0 model0 OB LBX FF LK Aw sp src Wextra F Mc modelc LKc cr Ac ->
  (sp - 160 - 16 <= i < sp) \/ (F <= i < F + 128) \/ (F / 8 + SB <= i < F / 8 + SB + 16) \/ (PGS.ow_os O <= i < PGS.ow_os O + 296)
    \/ ((PGS.ow_os O + 8) / 8 + SB <= i < (PGS.ow_os O + 8) / 8 + SB + 36) ->
  ahid Ac modelc (Z_to_bv 64 i) = false.
Proof.
  intros CTX G BI Hi.
  pose proof CTX as (OK & HH0 & _ & _ & _ & _ & _ & OFR & _).
  pose proof (PGSA.oo_lay _ _ _ _ _ _ OK) as (LY1 & LY2 & _).
  assert (AO : PMSPA.aobjA FF (PGS.ow_os O) 296).
  { apply (PGSKA.aobjA_sub FF (PGS.ow_lo O) (PGS.ow_hi O)); [exact OFR| exact LY1| exact LY2]. }
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH0) as (_ & WF & _ & FSCEIL & _).
  pose proof AO as (f & Hf & X1 & X2). destruct (WF f Hf) as (Y1 & Y2 & _).
  unfold PGSRDK16.srd_frame in G. unfold PGSRDK16.srd_body in BI.
  pose proof G as G'. destruct G' as [_ GSPT GSLO GSHI GSPC GOCR GOWN GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
  change (ff_bytes 1) with 128 in *.
  pose proof BI as (B1 & _).
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ _ _ _ _ Mc modelc B1) as (_ & VST & _ & VFS & _ & _ & VFSSH & _).
  cbv zeta in VST, VFS, VFSSH.
  assert (E0 : forall (P : Z -> Prop) a, (forall j, 0 <= j < 1 -> P (a + j)) -> P a).
  { intros P a X. specialize (X 0 ltac:(lia)). rewrite Z.add_0_r in X. exact X. }
  set (os := PGS.ow_os O) in *.
  destruct Hi as [Y|[Y|[Y|[Y|Y]]]].
  - apply (E0 (fun x => ahid Ac modelc (Z_to_bv 64 x) = false)). apply (VST i 1); clear - Y GSLO GSPC; lia.
  - apply (E0 (fun x => ahid Ac modelc (Z_to_bv 64 x) = false)). apply (VFS i 1); clear - Y GFS1 GFS2; lia.
  - apply (E0 (fun x => ahid Ac modelc (Z_to_bv 64 x) = false)). apply (VFSSH i 1).
    intros j Hj. unfold in_shadow_of, S. clear - Y Hj GFS1 GFS2 GF32 GFR. unfold FS_BYTES in *. lia.
  - apply (E0 (fun x => ahid Ac modelc (Z_to_bv 64 x) = false)). apply (VFS i 1); clear - Y X1 X2 Y1 Y2; lia.
  - apply (E0 (fun x => ahid Ac modelc (Z_to_bv 64 x) = false)). apply (VFSSH i 1).
    intros j Hj. unfold in_shadow_of, S. clear - Y Hj X1 X2 Y1 Y2. unfold FS_BYTES in *. lia.
Qed.

Lemma srd_call_ag O R0 M0 model0 K OB LBX FF LK Aw cr sp r src str sm Wextra F fl LK2 M2 model2 M3 model3 LK3 Ac3 M4 model4 LK4 Ac4 dst n i :
  PGSRDK16.srd_ctx L ar HI 16 O R0 M0 model0 K OB LBX FF LK Aw cr sp r src str sm Wextra ->
  PGSRDK16.srd_frame L ar HI 16 R0 OB LBX FF LK Aw cr sp src F fl LK2 M2 model2 ->
  PGSRDK16.srd_body L ar HI 16 O R0 M0 model0 OB LBX FF LK Aw sp src Wextra F M3 model3 LK3 cr Ac3 ->
  PGSRDK16.srd_body L ar HI 16 O R0 M0 model0 OB LBX FF LK Aw sp src Wextra F M4 model4 LK4 cr Ac4 ->
  L5CA.ahpres L ar ([] ++ (PM.src_own src ++ OB ++ LBX)) ((F, 1, sp - 160 - 16 + 32) :: FF) (sp - 160 - 16) 2560 [(dst, n)] M3 M4 ->
  0 <= i < 2 ^ 64 ->
  (sp - 160 - 16 <= i < sp) \/ (F <= i < F + 120 /\ ~ (F + 24 <= i < F + 32)) \/ (F / 8 + SB <= i < F / 8 + SB + 16)
    \/ (PGS.ow_os O <= i < PGS.ow_os O + 296) \/ ((PGS.ow_os O + 8) / 8 + SB <= i < (PGS.ow_os O + 8) / 8 + SB + 36) ->
  ~ (dst <= i < dst + n) ->
  mrestrict (ahid Ac4 model4) M4 (Z_to_bv 64 i) = mrestrict (ahid Ac3 model3) M3 (Z_to_bv 64 i).
Proof.
  intros CTX G BI3 BI4 AH Hi RG ND.
  assert (RG' : (sp - 160 - 16 <= i < sp) \/ (F <= i < F + 128) \/ (F / 8 + SB <= i < F / 8 + SB + 16)
    \/ (PGS.ow_os O <= i < PGS.ow_os O + 296) \/ ((PGS.ow_os O + 8) / 8 + SB <= i < (PGS.ow_os O + 8) / 8 + SB + 36)) by (clear - RG; lia).
  apply mr_eq; [exact (srd_vis O R0 M0 model0 K OB LBX FF LK Aw cr sp r src str sm Wextra F fl LK2 M2 model2 M3 model3 LK3 Ac3 i CTX G BI3 RG')|
                exact (srd_vis O R0 M0 model0 K OB LBX FF LK Aw cr sp r src str sm Wextra F fl LK2 M2 model2 M4 model4 LK4 Ac4 i CTX G BI4 RG')|].
  pose proof CTX as (OK & HH0 & _ & _ & _ & _ & _ & OFR & _).
  pose proof (PGSA.oo_lay _ _ _ _ _ _ OK) as (LY1 & LY2 & _ & _ & _ & O8 & _).
  assert (AO : PMSPA.aobjA FF (PGS.ow_os O) 296).
  { apply (PGSKA.aobjA_sub FF (PGS.ow_lo O) (PGS.ow_hi O)); [exact OFR| exact LY1| exact LY2]. }
  unfold PGSRDK16.srd_frame in G.
  pose proof G as G'. destruct G' as [_ GSPT GSLO GSHI GSPC GOCR GOWN GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
  change (ff_bytes 1) with 128 in *. change (128 / 8) with 16 in *.
  destruct AH as (AK & _). apply AK. split; [exact Hi|]. split.
  2:{ intros rr [<-|[]] X. unfold L5.in_rng in X. cbn [fst snd] in X. clear - X ND. lia. }
  unfold aclient. set (os := PGS.ow_os O) in *.
  destruct RG as [Y|[Y|[Y|[Y|Y]]]].
  - apply (L5SAR.stack_client L ar). clear - Y GSLO GSPC. lia. clear - Y. lia.
  - apply (L5SAR.fframe_client L ar _ _ _ _ F 1 (sp - 160 - 16 + 32)); [left; reflexivity|]. change (ff_bytes 1) with 128. clear - Y. lia.
  - apply (L5SAR.fframe_shadow_client L ar _ _ _ _ F 1 (sp - 160 - 16 + 32)); [left; reflexivity|].
    change (ff_bytes 1) with 128. unfold in_shadow_of, S. destruct GF8 as (_ & GF8b & _). rewrite GF8b. clear - Y. lia.
  - apply L5SAR.aclient_cons. apply PMASR1.cl_of_bf. right. apply (PMASR1.in_fframe_of_aobjA FF _ 296 i AO). clear - Y. lia.
  - apply L5SAR.aclient_cons. destruct AO as ([[fa fk] frs] & Hf & X1 & X2). cbn [ff_addr ff_class fst snd] in X1, X2.
    apply (L5SAR.fframe_shadow_client L ar _ _ _ _ fa fk frs); [exact Hf|]. unfold in_shadow_of, S. clear - Y X1 X2 O8. lia.
Qed.

Definition srd_fill_ret_case (Pc : Z -> Prop) : Prop :=
  forall (O : PGS.owner) (R0 : bvmap 5 word) (M0 : mem) (model0 : Model) (K : TSet) (OB LBX : list (Z * Z))
         (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r : Z) (str : PM.vstr) (Wextra : list L5.range)
         (qc de rem g eg sst p k : Z),
    PGSRDK16.srd_ctx L ar HI 16 O R0 M0 model0 K OB LBX FF LK Aw cr sp r (PM.SRC qc de rem) str (PM.STRM g eg sst) Wextra ->
    getr R0 (reg 11) = Z_to_bv 64 p -> getr R0 (reg 12) = Z_to_bv 64 k ->
    forall (F fl : Z) (LK2 : list fframe) (M2 : mem) (model2 : Model),
    PGSRDK16.srd_frame L ar HI 16 R0 OB LBX FF LK Aw cr sp (PM.SRC qc de rem) F fl LK2 M2 model2 ->
    forall (fx : FPState) (R : bvmap 5 word) (M : mem) (model : Model) (LKc : list fframe) (Ac : list (Z * Z))
           (V : nat -> Z),
    PGSRDK16.srd_body L ar HI 16 O R0 M0 model0 OB LBX FF LK Aw sp (PM.SRC qc de rem) Wextra F M model LKc cr Ac ->
    V 2%nat = sp - 16 -> V 36%nat = PGS.ow_os O -> V 37%nat = p -> V 38%nat = k -> 32 * V 50%nat = F -> V 51%nat = fl ->
    (forall i, In i [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> V i = bv_unsigned (getr R0 (reg i))) ->
    getr R (reg 3) = getr R0 (reg 3) -> getr R (reg 4) = getr R0 (reg 4) ->
    forall (len1 c g2 st2 : Z),
    PGSRDK16.srd_stC V R (mrestrict (ahid Ac model) M) -> V 39%nat = len1 -> V 34%nat = qc -> getr R (reg 10) = Z_to_bv 64 c -> Pc c ->
    PGS.ow_at O M (PM.SRC qc qc 0) OB -> PM.iss_at RSEGS PMA.AD PMSPA.accA M (PGS.ow_ois O) str (PM.STRM g2 eg st2) -> PMSTA.base_okA RSEGS PMA.AD M -> len1 = rem -> len1 < k -> k - len1 <= 16383 -> 0 <= c <= 16384 -> g2 = g + c -> g2 <= eg -> (sst = 2 -> st2 = 2) -> (c = 0 -> st2 = 2) -> L5.defined M p len1 ->
    srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 716700 M model) K.

Lemma srd_fill_ret_case_split : srd_fill_ret_case (fun c => c = 0) -> srd_fill_ret_case (fun c => c <> 0) ->
  PGSRDK16.srd_fill_ret_T L ar HI 16.
Proof.
  intros H0 H1. unfold PGSRDK16.srd_fill_ret_T. intros.
  destruct (Z.eq_dec c 0) as [E|E]; [eapply H0| eapply H1]; eassumption.
Qed.

Lemma srd_c0 : PGSRDK16.srd_exit_T L ar HI 16 -> srd_fill_ret_case (fun c => c = 0).
Proof using All.
  intros EXIT. unfold srd_fill_ret_case.
  intros O R0 M0 model0 K OB LBX FF LK Aw cr sp r str Wextra qc de rem g eg sst p k CTX R11 R12 F fl LK2 M2 model2 FR
         fx R M model LKc Ac V BI V2 V36 V37 V38 V50 V51 VSV X3 X4 len1 c g2 st2 STC V39 V34 R10 HC PA IA BASE Hl1 Hl1k Hl1k' Hc Hg2 Hg2e Hst2 Hc0 DP.
  change (c = 0) in HC. subst c.
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
  pose proof PSRC1 as (_ & _ & _ & F264 & F272 & _). cbn [PM.sr_qc] in F264.
  set (MV := mrestrict (ahid Ac model) M) in *.
  pick_st STC.
  match goal with
  | H2 : _ <= V 2%nat <= _, H36 : _ <= V 36%nat <= _, H50 : _ <= V 50%nat <= _, H51 : 4096 <= V 51%nat <= _ |- _ =>
      pose proof (conj H2 (conj H36 (conj H50 H51))) as KB
  end.
  assert (V39r : 0 <= len1) by (rewrite <- V39; match goal with H : 0 <= V 39%nat < _ |- _ => exact (proj1 H) end).
  LeanFeed.pfeed P0 (PMASRP.asrC016_conc fx R MV V)
    ltac:(first [assumption | (unfold PMASRP.aligned; assumption) | (rewrite V38, V39; clear - Hl1k Hl1k'; lia)]).
  destruct P0 as (fx1 & R1 & M1v & MG1 & _ & AG1 & MS1 & KS1 & Q1 & Q2 & Q8 & Q9 & Q10 & Q11 & Q18 & Q19 & Q20 & Q21 & Q22 & Q23 & Q24 & P288 & P280).
  apply (srd_piece O R0 M0 model0 K OB LBX FF LK Aw cr sp r (PM.SRC qc de rem) str (PM.STRM g eg sst) Wextra F fl LK2 M2 model2 M model LKc Ac
           fx fx1 R R1 _ _ M1v (fun a => V 36%nat + 280 <= a < V 36%nat + 280 + 16) CTX FR BI MS1 MG1 AG1).
  { intros a Wa. cbn beta in Wa. right; right; left. clear - Wa V36. lia. }
  intros M1 model1 BI1 HID1 MRT1 MGM1 FR1 VIS1 EK1.
  assert (SV1 : forall i, In i [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> vx V R1 i = bv_unsigned (getr R0 (reg i))).
  { intros i Hi. rewrite <- (VSV i Hi). cbn in Hi. repeat destruct Hi as [<-|Hi]; first [reflexivity | destruct Hi]. }
  assert (X3' : getr R1 (reg 3) = getr R0 (reg 3)) by (rewrite KS1 by inl; exact X3).
  assert (X4' : getr R1 (reg 4) = getr R0 (reg 4)) by (rewrite KS1 by inl; exact X4).
  assert (STR1 : PGSRDK16.srd_stR (vx V R1) R1 M1v).
  { unfold PGSRDK16.srd_stR, vx. cbn beta iota.
    sweep ltac:(first [assumption | exact (bv_unsigned_in_range _ _) | (symmetry; apply Z_to_bv_bv_unsigned)
                      | (rewrite KS1 by inl; assumption) | (eapply L5.writable_grows; [exact MG1| assumption])
                      | (eapply L5.defined_grows; [exact MG1| assumption]) | carry MV AG1 KB]). }
  assert (STR1' : PGSRDK16.srd_stR (vx V R1) R1 (mrestrict (ahid Ac model1) M1)) by (rewrite HID1, MRT1; exact STR1).
  assert (V76 : vx V R1 76%nat = len1).
  { unfold vx. cbn beta iota. rewrite Q22, L5.unsigned_lit; [exact V39| assumption]. }
  assert (U264 : L5.u64_at RSEGS M1 (os + 264) qc).
  { apply (L5C.u64_at_agree RSEGS M M1); [| clear - O1; lia| clear - O1; lia| exact F264].
    intros i Hi. apply FR1; [clear - Hi O1; lia|]. cbn beta. clear - Hi V36. lia. }
  assert (U272 : L5.u64_at RSEGS M1 (os + 272) PM.CHUNK).
  { apply (L5C.u64_at_agree RSEGS M M1); [| clear - O1; lia| clear - O1; lia| exact F272].
    intros i Hi. apply FR1; [clear - Hi O1; lia|]. cbn beta. clear - Hi V36. lia. }
  assert (VO1 : forall i, V 36%nat + 280 <= i < V 36%nat + 296 -> M1 (Z_to_bv 64 i) = M1v (Z_to_bv 64 i)).
  { intros i Hi. apply VIS1.
    apply (srd_vis O R0 M0 model0 K OB LBX FF LK Aw cr sp r (PM.SRC qc de rem) str (PM.STRM g eg sst) Wextra F fl LK2 M2 model2 M model LKc Ac i CTX FR BI).
    right; right; right; left. clear - Hi V36. lia. }
  assert (U280 : L5.u64_at RSEGS M1 (os + 280) qc).
  { rewrite <- V34. replace (os + 280) with (V 36%nat + 280) by (clear - V36; lia).
    apply (L5C.u64_at_agree RSEGS M1v M1); [| sd KB| sd KB| exact P280]. intros i Hi. apply VO1. clear - Hi. lia. }
  assert (U288 : L5.u64_at RSEGS M1 (os + 288) 0).
  { replace (os + 288) with (V 36%nat + 288) by (clear - V36; lia).
    apply (L5C.u64_at_agree RSEGS M1v M1); [| sd KB| sd KB| exact P288]. intros i Hi. apply VO1. clear - Hi. lia. }
  assert (ISS1 : PM.iss_at RSEGS PMA.AD PMSPA.accA M1 ois str (PM.STRM g2 eg st2)) by exact (ISSC M1 _ EK1 WOS OI_os OS_os _ IA).
  assert (DEF1 : L5.defined M1 p len1) by (eapply L5.defined_grows; [exact MGM1| exact DP]).
  assert (A1 : qc + 0 <= qc + PM.CHUNK) by (clear; unfold PM.CHUNK; lia).
  assert (A2 : g <= g2 <= eg) by (clear - Hg2 Hg2e; lia).
  assert (A3 : 0 <= len1 <= k) by (clear - V39r Hl1k; lia).
  assert (A4 : rem + (eg - g) - (0 + (eg - g2)) = len1) by (clear - Hl1 Hg2; lia).
  assert (A5 : 1 <= rem -> 1 <= len1) by (clear - Hl1; lia).
  assert (A6 : len1 = 0 -> 0 = 0 /\ st2 = 2) by (intros _; split; [reflexivity| exact (Hc0 eq_refl)]).
  exact (EXIT fx1 R1 M1 model1 LKc Ac (vx V R1) BI1 V2 V36 V37 V38 V50 V51 SV1 X3' X4' qc 0 g2 st2 len1 STR1' V76 U264 U272 U280 U288
           (Z.le_refl qc) (Z.le_refl 0) A1 ISS1 A2 Hst2 A3 A4 A5 A6 DEF1).
Qed.

End WithHeap.
End PGSRDC16.
