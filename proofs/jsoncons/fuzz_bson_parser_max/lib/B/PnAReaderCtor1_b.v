(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.LeanFeed.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StreamSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b L5StepAR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmLayout PmLayoutA PnLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PnModel PmModelFacts PmStatics PmStaticsA PnStatics PnStaticsA
     PmSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PnSpecsAa_b PnSpecsAX_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgSrc PgV8. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgSrcA_b PgV8A_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnRun. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnRunA_b PnRunAa_b
     PmModelFactsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnStepA_b PnStepA2_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmCertKitG. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import XIcptAs0_b PnAReaderCtorStmts_b PnAReaderCtorPA_b PnAIss1_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import XIcptA_b XIcptAs0Kit_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia.
Ltac nodisj := repeat match goal with H : _ \/ _ |- _ => clear H end.
Ltac dlia := first [ solve [ L5FastLia.prune_arith; nodisj; L5FastLia.lia_ne ]
                   | solve [ L5FastLia.prune_arith; match goal with H : _ \/ _ |- _ => L5SAR.clear_disj_but H; destruct H; L5FastLia.lia_ne end ]
                   | solve [ L5FastLia.prune_arith; nodisj; L5FastLia.lia_st ]
                   | solve [ L5FastLia.prune_arith; match goal with H : _ \/ _ |- _ => L5SAR.clear_disj_but H; destruct H; L5FastLia.lia_st end ] ].
Local Ltac lia := dlia.
Module PNARC1.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)).

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma stack_zeros6 M sp : shadow_zero M (sp - 24576) 3072 -> sp mod 16 = 0 -> L5KA.zeros_at M (sp / 8 + 2147450368) 512.
Proof.
  intros SZ S16 i Hi. pose proof (SZ (2560 + i) ltac:(Lia.lia)) as X. unfold byte_at, S, SB in X.
  replace (sp / 8 + 2147450368 + i) with ((sp - 24576) / 8 + 2147450880 + (2560 + i)) by Lia.lia. exact X.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma vis_u8 H M1 M1v a v : mrestrict H M1 = M1v -> L5A.avis H a 1 -> 0 <= a -> a < 2 ^ 63 -> L5.u8_at RSEGS M1v a v -> L5.u8_at RSEGS M1 a v.
Proof. intros E AV H0 H1 X. rewrite <- E in X. exact (proj1 (L5A.u8_at_vis H M1 a v AV ltac:(Lia.lia) ltac:(Lia.lia)) X). Qed.

Section Stage.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (IL : icpt_layout) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Let LYa := PMA.ly_as0 L C LY.

(* [comment removed for export] *)
Lemma img_sh_vis LB FF LK cr Aw M model a n : ri_inv HI LB FF LK cr Aw M (vml_of model) ->
  0x10000 <= a -> a + n <= 0x696000 -> 0 < n -> a mod 8 = 0 -> n mod 8 = 0 ->
  Forall (fun r => a + n <= fst r \/ snd r <= a) [(0x231c0, 0x23980); (0x13bfc0, 0x13c580)] ->
  L5KA.zeros_at (mrestrict (ahid Aw model) M) (a / 8 + 2147450880) (n / 8).
Proof.
  intros HH Ha Hn H0 A8 N8 PO.
  destruct (aic_img_shadow _ _ _ _ _ ICok _ _ _ _ _ _ _ HH a n) as (ZB & SA).
  - rewrite (L5A.aly_img_lo L C LYa). Lia.lia. - rewrite (L5A.aly_img_hi L C LYa). Lia.lia. - Lia.lia.
  - rewrite (aicl_poison IL ILY). exact PO.
  - Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    intros i Hi. assert (AV : L5A.avis (ahid Aw model) (a / 8 + 2147450880 + i) 1).
    { apply (L5A.avis_of_shadow_allowed Aw model a n). exact SA. intros j Hj. unfold in_shadow_of, S, SB. Lia.lia. }
    pose proof (ZB (a / 8 + 2147450880 + i) ltac:(unfold in_shadow_of, S, SB; Lia.lia)) as Z1. unfold byte_at in Z1.
    rewrite (AsanAcct.mrestrict_visible (ahid Aw model) M); [exact Z1|]. pose proof (AV 0 ltac:(Lia.lia)) as X. rewrite Z.add_0_r in X. exact X.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

Theorem head : PMA.locale_ctor_spec L ar HI ->
  forall (fx : FPState) R0 M0 model0 K LB FF LK0 Aw0 cr sp r fb oo oa str sm,
    PNARCS.pre L ar HI R0 M0 model0 K LB FF LK0 Aw0 cr sp r fb oo oa str sm ->
    (forall (fx1 : FPState) R1 M1 model1 LK1 Aw1, PNARCS.rmid1 L ar HI R0 M0 model0 LB FF LK0 Aw0 cr sp fb oo R1 M1 model1 LK1 Aw1 ->
        srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fx1) R1 0xace24 M1 model1) K) ->
    srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fx) R0 0xac78c M0 model0) K.
Proof.
  intros LOC fx R0 M0 model0 K LB FF LK0 Aw0 cr sp r fb oo oa str sm PRE KONT.
  destruct PRE as (HH & AM & K0 & ENT & FRM & FRS & FOK & A10 & A11 & A12 & A13 & AOO & OOAP & OO8' & ODEF & ACC & ACCO & OO0 & OO16 & ISS & BASE & LOCb & CRED).
  destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH).
  pose proof AM as (Mh & MI). pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP). pose proof RAok as (Hr1 & Hr2).
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp.
  change (PMSPA.pm_scr 6) with 24576 in *. change (24576 / 8) with 3072 in STKSH.
  unfold PNARCS.op in *. set (op := fb + 464) in *.
  destruct FOK as ((rs & Hfb) & FB8).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & _).
  pose proof (WF _ Hfb) as (F1 & F2 & _). cbn in F1, F2. change (ff_bytes 5) with 2048 in F2.
  assert (AOP : PMSPA.aobjA FF op 416) by (exists (fb, 5, rs); split; [exact Hfb| cbn; unfold op; change (ff_bytes 5) with 2048; lia]).
  assert (AOIS : PMSPA.aobjA FF (fb + 96) 272) by (exists (fb, 5, rs); split; [exact Hfb| cbn; change (ff_bytes 5) with 2048; lia]).
  assert (FB16 : fb mod 16 = 0) by (apply Z.mod_divide; [lia|]; apply (Z.divide_trans 16 2048 fb); [exists 128; reflexivity| apply Z.mod_divide; [lia| exact FB8]]).
  assert (O8 : op mod 8 = 0) by (unfold op; replace (fb + 464) with (fb - (-464)) by lia; apply PMAIS1.sub8; [exact FB16| reflexivity]).
  assert (OIS8 : (fb + 96) mod 8 = 0) by (replace (fb + 96) with (fb - (-96)) by lia; apply PMAIS1.sub8; [exact FB16| reflexivity]).
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK0 cr Aw0 M0 model0 HH) as (HOFF & VIS & VIMG & VFS & VBLK & VBSH & VFSSH & VSTSH).
  set (H := ahid Aw0 model0) in *. set (MV := mrestrict H M0) in *.
  pose proof (PMKA.aobj_of_aobjA FF op 416 AOP O8) as AOB.
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB FF LK0 cr Aw0 M0 model0 op 416 sp 24576 HH AOB ltac:(lia) ltac:(reflexivity))
    as (OR & OBIG & ODEF' & OVIS & OVSH & OCL & OCLSH).
  (* [comment removed for export] *)
  assert (OCLS : (6905856 <= op - 368 <= 2147446000) \/ (17592186044416 + 2147450880 <= op - 368 <= 140737488354535)).
  { rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in FSIMG. unfold app_mem, FS_BYTES, BIGSHADOW_LO, BIGSHADOW_HI in FSAPP, FSIMG, F2. unfold op.
    destruct FSAPP as (FA0 & [FA|FA] & FA2); destruct FSIMG as [FI|FI]; [left; lia| left; lia| right; lia| right; lia]. }
  pose proof (HAJ.aior_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as ST. rewrite (L5A.aly_segs L C LYa) in ST.
  pose proof (L5A.statics_facts L C M0 LYa ST) as (GOT & CSB & CUAR & _).
  assert (VU8 : forall x v0, 0x10000 <= x < 0x696000 -> L5.u8_at RSEGS M0 x v0 -> L5.u8_at RSEGS MV x v0).
  { intros x v0 Hx X. apply (proj2 (L5A.u8_at_vis H M0 x v0 (VIMG x 1 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact X. }
  assert (VU64 : forall x v0, 0x10000 <= x -> x + 8 <= 0x696000 -> L5.u64_at RSEGS M0 x v0 -> L5.u64_at RSEGS MV x v0).
  { intros x v0 Hx Hx' X. apply (proj2 (L5A.u64_at_vis H M0 x v0 (VIMG x 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact X. }
  assert (V0 : L5.img_clear MV 1249280 1282048) by (apply L5A.img_clear_mrestrict; exact GOT).
  assert (V1 : L5.u64_at RSEGS MV 1309752 2147450880) by (apply VU64; [lia| lia| exact CSB]).
  assert (V2 : L5.u32_at RSEGS MV 1309760 1) by (apply (proj2 (L5A.u32_at_vis H M0 1309760 1 (VIMG 1309760 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CUAR).
  assert (W4096 : L5.writable RSEGS MV (sp - 4096) 4096).
  { apply (proj2 (L5A.writable_vis H M0 (sp - 4096) 4096 (VIS (sp - 4096) 4096 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5SAR.astk_writable ar M0 sp 24576); [exact ASTK| lia| lia| lia]. }
  (* [comment removed for export] *)
  destruct ISS as (IVP & IDEF & IACC & I16 & I24 & I32 & I40 & I48 & I64 & IVS & I104 & I112 & IIOS & IE1 & IE2).
  assert (ACCI : PMSPA.accA M0 (fb + 96) 272).
  { intros a Ha. destruct (Z_lt_le_dec a (fb + 96 + 120)) as [X|X]; [apply IACC; lia|].
    destruct IIOS as (_ & _ & _ & _ & _ & _ & _ & IA & _). apply IA. lia. }
  assert (ZOP : L5KA.zeros_at MV (op / 8 + 2147450880) 52).
  { exact (PMKA.obj_shadow_vis L ar C HI LYa HIok LB FF LK0 cr Aw0 M0 model0 op 416 HH AOP O8 ltac:(lia) ltac:(reflexivity) ACC). }
  assert (ZOIS : L5KA.zeros_at MV ((op - 368) / 8 + 2147450880) 34).
  { replace (op - 368) with (fb + 96) by (unfold op; lia).
    exact (PMKA.obj_shadow_vis L ar C HI LYa HIok LB FF LK0 cr Aw0 M0 model0 (fb + 96) 272 HH AOIS OIS8 ltac:(lia) ltac:(reflexivity) ACCI). }
  assert (ZOO : L5KA.zeros_at MV (oo / 8 + 2147450880) 3).
  { exact (PMKA.obj_shadow_vis L ar C HI LYa HIok LB FF LK0 cr Aw0 M0 model0 oo 24 HH AOO OO8' ltac:(lia) ltac:(reflexivity) ACCO). }
  assert (OWv : L5.writable RSEGS MV op 416).
  { apply (proj2 (L5A.writable_vis H M0 op 416 OVIS ltac:(lia) ltac:(lia))). apply (L5C.writable_of_defined RSEGS). exact ODEF. lia. lia. }
  (* [comment removed for export] *)
  assert (XC1 : L5.u64_at RSEGS MV 1275072 1309752) by (apply VU64; [lia| lia| exact (PMAIS1.d4cell L ar C HI LY HIok _ _ _ _ _ _ _ 1275072 8 1309752 HH ltac:(unfold L5A.AS0_ALY_CELLS_D4; do 4 right; left; reflexivity))]).
  assert (XC2 : L5.u64_at RSEGS MV 1275080 1313064) by (apply VU64; [lia| lia| exact (PMAIS1.d4cell L ar C HI LY HIok _ _ _ _ _ _ _ 1275080 8 1313064 HH ltac:(unfold L5A.AS0_ALY_CELLS_D4; do 5 right; left; reflexivity))]).
  assert (XC3 : L5.u64_at RSEGS MV 1313064 0) by (apply VU64; [lia| lia| exact (PMAIS1.d4cell L ar C HI LY HIok _ _ _ _ _ _ _ 1313064 8 0 HH ltac:(unfold L5A.AS0_ALY_CELLS_D4; do 6 right; left; reflexivity))]).
  assert (XC4 : L5.u64_at RSEGS MV 1275088 1313072) by (apply VU64; [lia| lia| exact (PMAIS1.d4cell L ar C HI LY HIok _ _ _ _ _ _ _ 1275088 8 1313072 HH ltac:(unfold L5A.AS0_ALY_CELLS_D4; do 7 right; left; reflexivity))]).
  assert (XC5 : L5.u64_at RSEGS MV 1313072 0) by (apply VU64; [lia| lia| exact (PMAIS1.d4cell L ar C HI LY HIok _ _ _ _ _ _ _ 1313072 8 0 HH ltac:(unfold L5A.AS0_ALY_CELLS_D4; do 8 right; left; reflexivity))]).
  assert (XC6 : L5.u64_at RSEGS MV 1275096 1313056) by (apply VU64; [lia| lia| exact (PMAIS1.d4cell L ar C HI LY HIok _ _ _ _ _ _ _ 1275096 8 1313056 HH ltac:(unfold L5A.AS0_ALY_CELLS_D4; do 9 right; left; reflexivity))]).
  assert (XC7 : L5.u64_at RSEGS MV 1313056 140737488355327) by (apply VU64; [lia| lia| exact (PMAIS1.d4cell L ar C HI LY HIok _ _ _ _ _ _ _ 1313056 8 140737488355327 HH ltac:(unfold L5A.AS0_ALY_CELLS_D4; do 10 right; left; reflexivity))]).
  assert (XC8 : L5.u64_at RSEGS MV 1277992 1313049) by (apply VU64; [lia| lia| exact (PMAIS1.d4cell L ar C HI LY HIok _ _ _ _ _ _ _ 1277992 8 1313049 HH ltac:(unfold L5A.AS0_ALY_CELLS_D4; do 11 right; left; reflexivity))]).
  assert (XC9 : L5.u8_at RSEGS MV 1313049 1) by (apply VU8; [lia| exact (PMAIS1.d4cell L ar C HI LY HIok _ _ _ _ _ _ _ 1313049 1 1 HH ltac:(unfold L5A.AS0_ALY_CELLS_D4; do 12 right; left; reflexivity))]).
  assert (XC10 : L5.u64_at RSEGS MV 1283280 1219844) by (apply VU64; [lia| lia| exact (PMAIS1.d4cell L ar C HI LY HIok _ _ _ _ _ _ _ 1283280 8 1219844 HH ltac:(unfold L5A.AS0_ALY_CELLS_D4; do 2 right; left; reflexivity))]).
  assert (XC11 : L5.u64_at RSEGS MV 1283272 1218816) by (apply VU64; [lia| lia| exact (PMAIS1.d4cell L ar C HI LY HIok _ _ _ _ _ _ _ 1283272 8 1218816 HH ltac:(unfold L5A.AS0_ALY_CELLS_D4; do 13 right; left; reflexivity))]).
  assert (IMG1 : L5KA.zeros_at MV 2147607348 64).
  { pose proof (img_sh_vis LB FF LK0 cr Aw0 M0 model0 0x1319a0 512 HH ltac:(lia) ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(reflexivity)
                  ltac:(repeat constructor; cbn [fst snd]; lia)) as X. exact X. }
  assert (IMG2 : L5KA.zeros_at MV 2147609117 32).
  { pose proof (img_sh_vis LB FF LK0 cr Aw0 M0 model0 0x1350e8 256 HH ltac:(lia) ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(reflexivity)
                  ltac:(repeat constructor; cbn [fst snd]; lia)) as X. exact X. }
  (* [comment removed for export] *)
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB FF LK0 cr Aw0 M0 model0 oo 24 sp 24576 HH (PMKA.aobj_of_aobjA FF oo 24 AOO OO8') ltac:(Lia.lia) ltac:(reflexivity))
    as (OOR & OOBIG & _).
  assert (OOSTK : oo + 24 <= sp - 24576) by Lia.lia.
  assert (OOAP' : op + 416 <= oo \/ oo + 24 <= op) by (destruct OOAP as [X|X]; [right|left]; Lia.lia).
  assert (OOSTK' : sp - 4096 + 4096 <= oo \/ oo + 24 <= sp - 4096) by (right; Lia.lia).
  assert (OOIMG : 65536 + 6840320 <= oo \/ oo + 24 <= 65536) by (left; Lia.lia).
  (* [comment removed for export] *)
  assert (A11' : getr R0 (reg 11) = Z_to_bv 64 (op - 368)) by (rewrite A11; f_equal; unfold op; lia).
  (* [comment removed for export] *)
  pose proof (PNARCPA.abrcAl_conc as0_icpt_fill as0_icpt_copy as0_icpt_tls fx R0 MV (fun j => match j with 2%nat => sp | 33%nat => op | 34%nat => oo | _ => 0 end)) as PL.
  cbn beta iota in PL.
  let T := type of PL in let G := L5SAR.feed_concl T in assert (P : G).
  { destruct OCLS as [CL|CL].
    - L5SAR.feed PL ltac:(first [assumption | unfold PNARCPA.aligned; lia | lia]). exact PL.
    - LeanFeed.pfeed PH (PNARCPA.abrcAh_conc as0_icpt_fill as0_icpt_copy as0_icpt_tls fx R0 MV (fun j => match j with 2%nat => sp | 33%nat => op | 34%nat => oo | _ => 0 end)) ltac:(first [assumption | unfold PNARCPA.aligned; lia | lia]). exact PH. }
  clear PL.
  destruct P as (fx1 & R1 & M1v & MG1 & _ & FZ1 & MS1 & KS1 & B1 & B2 & B8 & B9 & B10 & B18 & B19 & B20 & B21 & B22 & B23
                 & Z168 & C144 & C136 & C128 & C120 & C152 & C148 & C40 & C112 & C32 & C160
                 & F200 & F192 & F184 & F176 & F168 & F152 & F136 & F128 & F120
                 & C12 & C10 & C9 & C8 & C0 & S72 & S64 & S56 & S48 & S40 & S32 & S24 & S16 & S8
                 & S80 & S88 & F144 & F208 & F216 & F224 & F232).
  set (W1 := fun a => (sp - 4096 <= a < sp - 4096 + 4096) \/ (op + 0 <= a < op + 0 + 416)).
  unfold PMSPA.cfg.
  apply (L5SAR.apiece L ar C HI LYa HIok LB FF LK0 cr Aw0 M0 model0 fx fx1 R0 0xac78c R1 0xfee68 M1v W1 K HH AM MS1 MG1).
  { intros a Ha N. apply FZ1; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X]. }
  { intros a Ha [Wa|Wa].
    - split; [|lia]. unfold aclientw, aclient_g. right; left. split; [lia| intros X; lia].
    - split; [apply (L5SAR.obj_client L ar LB FF 0 0 op 416 a AOB); lia| lia]. }
  intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
  assert (WAPP : PMKA.wapp [(op, 416)]).
  { apply PMKA.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; lia| apply PMKA.wapp_nil]. }
  assert (EKO : forall M' M'' (P : Z -> Prop), (forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M'' (Z_to_bv 64 a) = M' (Z_to_bv 64 a)) ->
            (forall a, P a -> sp - 24576 <= a < sp \/ op <= a < op + 416) -> L5SAR.ek L ar LB FF sp 24576 [(op, 416)] M' M'').
  { intros M' M'' P FRM0 HP. apply (L5SAR.ek_piece L ar LB FF sp 24576 [(op, 416)] M' M'' P FRM0). intros a Ha Hc Ho X. destruct (HP a X) as [Y|Y].
    - destruct (L5SAR.aclient_cases L ar C HI LYa HIok LB FF LK0 cr Aw0 M0 _ sp 24576 a HH SPT Hc) as [Z1|Z1]; lia.
    - apply (Ho (op, 416)). left; reflexivity. unfold L5.in_rng; cbn [fst snd]. exact Y. }
  assert (EK01 : L5SAR.ek L ar LB FF sp 24576 [(op, 416)] M0 M1) by (apply (EKO M0 M1 W1 FR1); intros a [X|X]; lia).
  assert (FRB : forall f, In f FF -> 0 <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= 2 ^ 47).
  { intros f Hf. destruct (WF f Hf) as (X1 & X2 & _). unfold app_mem, FS_BYTES in *. lia. }
  assert (ASTK1 : L5CA.astk ar M1 sp 24576) by (apply (L5SAR.astk_grows ar M0 M1 sp 24576 ASTK MGM1)).
  assert (STKSH1 : shadow_zero M1 (sp - 24576) 3072).
  { apply (PMKA.stksh_keepA L ar LB FF sp 24576 [(op, 416)] M0 M1 EK01 WAPP); [lia| lia| lia| | lia| exact STKSH].
    apply PMAIS1.sub8; [exact A16| reflexivity]. }
  assert (STD : forall a, PMST.dep PMA.AD a -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_rt_static L a /\ L5.outside [(op, 416)] a).
  { intros a D. pose proof (PMAIS1.dep_img a D) as DI. rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa). split; [lia|].
    split; [exact (PMA.ly_static L C LY a (PnStatics.PNST.dep_of_j _ _ a D))|]. intros rg [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. lia. }
  assert (SRO : forall a, 65536 <= a < pa_rw_lo PMA.AD -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_rt_static L a /\ L5.outside [(op, 416)] a).
  { intros a Ha. cbn [pa_rw_lo PMA.AD ADDR_A] in Ha. rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa). split; [lia|].
    split; [intros X; pose proof (L5A.aly_static_lo L C LYa a X); lia|]. intros rg [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. lia. }
  assert (BASE1 : PMSTA.base_okA RSEGS PMA.AD M1) by (apply (PMKA.base_ok_keepA RSEGS PMA.AD L ar LB FF sp 24576 [(op, 416)] M0 M1 EK01 PMA.addrs_wf_A STD SRO BASE)).
  assert (LOC1 : PMST.loc_ok RSEGS PMA.AD M1 true).
  { apply (PMAIS1.loc_ok_agree M0 M1 true); [|exact LOCb]. intros a Ha. apply FR1; [lia| unfold W1; lia]. }
  (* [comment removed for export] *)
  unfold PMA.locale_ctor_spec, PMSPA.locale_ctor_spec in LOC. cbn [pa_locale_ctor PMA.AD ADDR_A] in LOC.
  apply (LOC fx1 R1 M1 model1 K LB FF LK0 Aw0 cr (op + 152) (sp - 240) 708012 true HH1 AM1 K0).
  { split; [rewrite L5K.rl1; exact B1|]. split; [split; [lia| reflexivity]|]. split; [rewrite L5K.rl2; exact B2|].
    split; [rewrite L5K.rl3, (KS1 3%nat) by inl; exact Rgp|]. split; [rewrite L5K.rl4, (KS1 4%nat) by inl; exact Rtp|].
    change (PMSPA.pm_scr 2) with 16384. split.
    - apply (L5SAR.astk_sub ar M1 M1 sp 24576 240 16384 ASTK1 (fun x X => X)); [lia| lia| lia|].
      replace (sp - 240) with (sp + (-15) * 16) by lia. rewrite Z.mod_add by lia. exact A16.
    - change (16384 / 8) with 2048. apply (PMKA.shadow_zero_sub M1 (sp - 24576) 3072 (sp - 240 - 16384) 2048);
        [apply PMAIS1.sub8; [exact A16| reflexivity]| replace (sp - 240 - 16384) with (sp - 16624) by lia; apply PMAIS1.sub8; [exact A16| reflexivity]| lia| lia| lia| exact STKSH1]. }
  { unfold PMSPA.ffroomA in *. intros k Hk. specialize (FRM k Hk). lia. }
  { intros f Hf. specialize (FRS f Hf). lia. }
  { rewrite L5K.rl10. exact B10. }
  { destruct AOP as (f & Hf & X1 & X2). exists f. split; [exact Hf| lia]. }
  { replace (op + 152) with (op + 19 * 8) by lia. rewrite Z.mod_add by lia. exact O8. }
  { apply (L5.defined_grows M0 M1 _ _ MGM1). apply (L5.defined_sub M0 op 416); [exact ODEF| lia| lia]. }
  { exact BASE1. }
  { exact LOC1. }
  intros fx2 R2 M2 model2 LK2 Aw2 RP2 C160' LOC2 HP2 MRT2 INC2 IA2 AM2 HH2.
  change (PMSPA.pm_scr 2) with 16384 in HP2. change ((op + 152, 8) :: (if true then [] else PMSPA.loc_W PMA.AD)) with [(op + 152, 8)] in HP2.
  assert (EK12 : L5SAR.ek L ar LB FF sp 24576 [(op, 416)] M1 M2).
  { apply (L5SAR.ek_callee L ar LB [] FF [] sp 24576 (sp - 240) 16384 [(op, 416)] [(op + 152, 8)] M1 M2 HP2); [lia| lia|].
    intros a Hc Ho rg [<-|[]] Hr. apply (Ho (op, 416)); [left; reflexivity| unfold L5.in_rng in *; cbn [fst snd] in *; lia]. }
  assert (DK12 : L5SAR.dk L ar LB FF sp 24576 M1 M2) by (apply (L5SAR.dk_callee L ar LB [] FF [] sp 24576 (sp - 240) 16384 [(op + 152, 8)] M1 M2 HP2); lia).
  assert (ASTK2 : L5CA.astk ar M2 sp 24576).
  { apply (L5SAR.astk_after L ar C HI HIok LB FF LK0 cr Aw0 M1 M1 M2 _ sp 24576 (sp - 240) 16384 [(op + 152, 8)] HH1 ASTK1 (fun x X => X) HP2); lia. }
  assert (EK02 : L5SAR.ek L ar LB FF sp 24576 [(op, 416)] M0 M2) by (apply (L5SAR.ek_trans L ar LB FF sp 24576 _ M0 M1 M2 EK01 EK12)).
  assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp - 240 - 16384 <= a < sp - 240) -> ~ (op + 152 <= a < op + 160) ->
                  aclient L ar LB FF 0 0 a -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
  { intros a Ha N0 N1 Hc. apply (proj1 HP2). split; [lia|]. split.
    - apply (L5SAR.aclient_narrow L ar LB FF 0 0); [exact Hc| lia].
    - intros rg [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. lia. }
  assert (BASE2 : PMSTA.base_okA RSEGS PMA.AD M2).
  { apply (PMAIS1.base_ok_agree M1 M2); [|exact BASE1]. intros a Ha. unfold PMAIS1.brg in Ha. apply KEEP2; [lia| lia| lia|].
    unfold aclient, aclient_g. right; right; left. rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa). split; [lia|].
    destruct Ha as [Ha|Ha]; [intros X; pose proof (L5A.aly_static_lo L C LYa a X); lia|].
    apply (fun D_ => PMA.ly_static L C LY a (PnStatics.PNST.dep_of_j _ _ a D_)). unfold PMST.dep, pm_initc. cbn [pa_canary pa_need_locks pa_locale_lock PMA.AD ADDR_A].
    destruct Ha as [Ha|[Ha|Ha]];
      [right; left; lia
      | right; right; exists (0x693f93, 0x693f94); split; [left; reflexivity| cbn [fst snd]; lia]
      | right; right; exists (0x694070, 0x694074); split; [right; left; reflexivity| cbn [fst snd]; lia]]. }
  (* [comment removed for export] *)
  assert (CS2 : forall k, In k L5SAR.cs_all -> getr R2 (reg k) = getr R1 (reg k)) by (intros k Hk; apply (L5SAR.cs_of_preserved R1 R2 k RP2 Hk)).
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK2 cr Aw2 M2 model2 HH2) as (HOFF2 & VIS2 & VIMG2 & VFS2 & VBLK2 & VBSH2 & VFSSH2 & VSTSH2).
  set (H2 := ahid Aw2 model2) in *. set (MV2 := mrestrict H2 M2) in *.
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB FF LK2 cr Aw2 M2 model2 op 416 sp 24576 HH2 AOB ltac:(lia) ltac:(reflexivity))
    as (_ & _ & ODEF2 & OVIS2 & _ & _ & _).
  pose proof (HAJ.aior_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH2) as ST2. rewrite (L5A.aly_segs L C LYa) in ST2.
  pose proof (L5A.statics_facts L C M2 LYa ST2) as (GOT2 & CSB2 & CUAR2 & _).
  assert (ACC2 : PMSPA.accA M2 op 416) by (apply (PMKA.acc_keepA' L ar LB FF sp 24576 _ M0 M2 EK02 WAPP FRB op 416 AOP ACC)).
  assert (ACCI2 : PMSPA.accA M2 (fb + 96) 272) by (apply (PMKA.acc_keepA' L ar LB FF sp 24576 _ M0 M2 EK02 WAPP FRB (fb + 96) 272 AOIS ACCI)).
  assert (ACCO2 : PMSPA.accA M2 oo 24) by (apply (PMKA.acc_keepA' L ar LB FF sp 24576 _ M0 M2 EK02 WAPP FRB oo 24 AOO ACCO)).
  assert (Y0 : L5.img_clear MV2 1249280 1282048) by (apply L5A.img_clear_mrestrict; exact GOT2).
  assert (Y1 : L5.u64_at RSEGS MV2 1309752 2147450880) by (apply (proj2 (L5A.u64_at_vis H2 M2 1309752 2147450880 (VIMG2 1309752 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CSB2).
  assert (Y2 : L5.u32_at RSEGS MV2 1309760 1) by (apply (proj2 (L5A.u32_at_vis H2 M2 1309760 1 (VIMG2 1309760 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CUAR2).
  assert (Y3 : L5.writable RSEGS MV2 (sp - 4096) 4096).
  { apply (proj2 (L5A.writable_vis H2 M2 (sp - 4096) 4096 (VIS2 (sp - 4096) 4096 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5SAR.astk_writable ar M2 sp 24576); [exact ASTK2| lia| lia| lia]. }
  assert (YZOP : L5KA.zeros_at MV2 (op / 8 + 2147450880) 52).
  { exact (PMKA.obj_shadow_vis L ar C HI LYa HIok LB FF LK2 cr Aw2 M2 model2 op 416 HH2 AOP O8 ltac:(lia) ltac:(reflexivity) ACC2). }
  assert (YZOIS : L5KA.zeros_at MV2 ((op - 368) / 8 + 2147450880) 34).
  { replace (op - 368) with (fb + 96) by (unfold op; lia).
    exact (PMKA.obj_shadow_vis L ar C HI LYa HIok LB FF LK2 cr Aw2 M2 model2 (fb + 96) 272 HH2 AOIS OIS8 ltac:(lia) ltac:(reflexivity) ACCI2). }
  assert (YZOO : L5KA.zeros_at MV2 (oo / 8 + 2147450880) 3).
  { exact (PMKA.obj_shadow_vis L ar C HI LYa HIok LB FF LK2 cr Aw2 M2 model2 oo 24 HH2 AOO OO8' ltac:(lia) ltac:(reflexivity) ACCO2). }
  assert (YW : L5.writable RSEGS MV2 op 416).
  { apply (proj2 (L5A.writable_vis H2 M2 op 416 OVIS2 ltac:(lia) ltac:(lia))). apply (L5C.writable_of_defined RSEGS). exact ODEF2. lia. lia. }
  assert (YIMG1 : L5KA.zeros_at MV2 2147607348 64).
  { pose proof (img_sh_vis LB FF LK2 cr Aw2 M2 model2 0x1319a0 512 HH2 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(reflexivity)
                  ltac:(repeat constructor; cbn [fst snd]; lia)) as X. exact X. }
  assert (YIMG2 : L5KA.zeros_at MV2 2147609117 32).
  { pose proof (img_sh_vis LB FF LK2 cr Aw2 M2 model2 0x1350e8 256 HH2 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(reflexivity)
                  ltac:(repeat constructor; cbn [fst snd]; lia)) as X. exact X. }
  assert (J2 : getr R2 (reg 2) = Z_to_bv 64 (sp - 240)) by (rewrite CS2 by inl; exact B2).
  assert (J8 : getr R2 (reg 8) = Z_to_bv 64 (op + 24)) by (rewrite CS2 by inl; exact B8).
  assert (J9 : getr R2 (reg 9) = Z_to_bv 64 (op + 104)) by (rewrite CS2 by inl; exact B9).
  assert (J18 : getr R2 (reg 18) = Z_to_bv 64 (op + 40)) by (rewrite CS2 by inl; exact B18).
  assert (J19 : getr R2 (reg 19) = Z_to_bv 64 2147450880) by (rewrite CS2 by inl; exact B19).
  assert (J20 : getr R2 (reg 20) = Z_to_bv 64 0x131ab8) by (rewrite CS2 by inl; exact B20).
  assert (J21 : getr R2 (reg 21) = Z_to_bv 64 ((op + 24) / 8 + 2147450880)) by (rewrite CS2 by inl; exact B21).
  assert (J22 : getr R2 (reg 22) = Z_to_bv 64 0x131ad0) by (rewrite CS2 by inl; exact B22).
  assert (J23 : getr R2 (reg 23) = Z_to_bv 64 ((op + 104) / 8 + 2147450880)) by (rewrite CS2 by inl; exact B23).
  (* [comment removed for export] *)
  assert (V1a : forall a n, (op <= a /\ a + n <= op + 416) \/ (sp - 4096 <= a /\ a + n <= sp) -> L5A.avis H a n).
  { intros a n [Ha|Ha]; [eapply L5A.avis_sub; [exact OVIS| lia| lia]| apply VIS; lia]. }
  assert (V2a : forall a n, (op <= a /\ a + n <= op + 416) \/ (sp - 4096 <= a /\ a + n <= sp) -> L5A.avis H2 a n).
  { intros a n [Ha|Ha]; [eapply L5A.avis_sub; [exact OVIS2| lia| lia]| apply VIS2; lia]. }
  assert (CL : forall a, op <= a < op + 416 -> aclient L ar LB FF 0 0 a) by (intros a Ha; apply (L5SAR.obj_client L ar LB FF 0 0 op 416 a AOB); lia).
  assert (SCL : forall a, sp - 24576 <= a < sp -> aclient L ar LB FF 0 0 a) by (intros a Ha; apply L5SAR.stack_client; lia).
  assert (T12 : forall a v, sp - 232 <= a -> a + 8 <= sp -> L5.u64_at RSEGS M1v a v -> L5.u64_at RSEGS MV2 a v).
  { intros a v Ha Ha' X. apply (proj2 (L5A.u64_at_vis H2 M2 a v (V2a a 8 ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply KEEP2; [lia| lia| lia| apply SCL; lia]| lia| lia|].
    apply (PMAIS1.vis_u64 _ _ _ _ _ VIS1); [apply V1a; lia| lia| lia| exact X]. }
  pose proof (T12 (sp - 8) _ ltac:(lia) ltac:(lia) S8) as Q8. pose proof (T12 (sp - 16) _ ltac:(lia) ltac:(lia) S16) as Q16.
  pose proof (T12 (sp - 24) _ ltac:(lia) ltac:(lia) S24) as Q24. pose proof (T12 (sp - 32) _ ltac:(lia) ltac:(lia) S32) as Q32.
  pose proof (T12 (sp - 40) _ ltac:(lia) ltac:(lia) S40) as Q40. pose proof (T12 (sp - 48) _ ltac:(lia) ltac:(lia) S48) as Q48.
  pose proof (T12 (sp - 56) _ ltac:(lia) ltac:(lia) S56) as Q56. pose proof (T12 (sp - 64) _ ltac:(lia) ltac:(lia) S64) as Q64.
  pose proof (T12 (sp - 72) _ ltac:(lia) ltac:(lia) S72) as Q72. pose proof (T12 (sp - 120) _ ltac:(lia) ltac:(lia) F120) as Q120.
  pose proof (T12 (sp - 128) _ ltac:(lia) ltac:(lia) F128) as Q128. pose proof (T12 (sp - 136) _ ltac:(lia) ltac:(lia) F136) as Q136.
  pose proof (T12 (sp - 144) _ ltac:(lia) ltac:(lia) F144) as Q144. pose proof (T12 (sp - 152) _ ltac:(lia) ltac:(lia) F152) as Q152.
  pose proof (T12 (sp - 168) _ ltac:(lia) ltac:(lia) F168) as Q168. pose proof (T12 (sp - 176) _ ltac:(lia) ltac:(lia) F176) as Q176.
  pose proof (T12 (sp - 184) _ ltac:(lia) ltac:(lia) F184) as Q184. pose proof (T12 (sp - 192) _ ltac:(lia) ltac:(lia) F192) as Q192.
  pose proof (T12 (sp - 200) _ ltac:(lia) ltac:(lia) F200) as Q200. pose proof (T12 (sp - 208) _ ltac:(lia) ltac:(lia) F208) as Q208.
  pose proof (T12 (sp - 216) _ ltac:(lia) ltac:(lia) F216) as Q216. pose proof (T12 (sp - 224) _ ltac:(lia) ltac:(lia) F224) as Q224.
  pose proof (T12 (sp - 232) _ ltac:(lia) ltac:(lia) F232) as Q232.
  pose proof (PMAIS1.bvu (getr R0 (reg 1))) as UR1. pose proof (PMAIS1.bvu (getr R0 (reg 8))) as UR8. pose proof (PMAIS1.bvu (getr R0 (reg 9))) as UR9.
  pose proof (PMAIS1.bvu (getr R0 (reg 18))) as UR18. pose proof (PMAIS1.bvu (getr R0 (reg 19))) as UR19. pose proof (PMAIS1.bvu (getr R0 (reg 20))) as UR20.
  pose proof (PMAIS1.bvu (getr R0 (reg 21))) as UR21. pose proof (PMAIS1.bvu (getr R0 (reg 22))) as UR22. pose proof (PMAIS1.bvu (getr R0 (reg 23))) as UR23.
  LeanFeed.pfeed P (PNARCPA.abrcB_conc as0_icpt_fill as0_icpt_copy as0_icpt_tls fx2 R2 MV2
    (fun j => match j with 2%nat => sp | 33%nat => op | 34%nat => oo | 43%nat => bv_unsigned (getr R0 (reg 1)) | 44%nat => bv_unsigned (getr R0 (reg 8))
                     | 45%nat => bv_unsigned (getr R0 (reg 9)) | 46%nat => bv_unsigned (getr R0 (reg 18)) | 47%nat => bv_unsigned (getr R0 (reg 19))
                     | 48%nat => bv_unsigned (getr R0 (reg 20)) | 49%nat => bv_unsigned (getr R0 (reg 21)) | 50%nat => bv_unsigned (getr R0 (reg 22))
                     | 51%nat => bv_unsigned (getr R0 (reg 23)) | _ => 0 end)) ltac:(first [assumption | unfold PNARCPA.aligned; lia | lia]).
  destruct P as (fx3 & R3 & M3v & MG3 & _ & FZ3 & MS3 & KS3 & D1 & D10 & D11 & D19 & D48 & D112 & D32 & D256 & D248).
  set (W3 := fun a => (op + 24 <= a < op + 24 + 8) \/ (op + 40 <= a < op + 40 + 8) \/ (op + 104 <= a < op + 104 + 8) \/ (op + 240 <= a < op + 240 + 12)).
  apply (L5SAR.apiece L ar C HI LYa HIok LB FF LK2 cr Aw2 M2 model2 fx2 fx3 R2 0xacdac R3 0xfee68 M3v W3 K HH2 AM2 MS3 MG3).
  { intros a Ha N. apply FZ3; [exact Ha| intros X; apply N; unfold W3; left; exact X| intros X; apply N; unfold W3; right; left; exact X
                              | intros X; apply N; unfold W3; right; right; left; exact X| intros X; apply N; unfold W3; right; right; right; exact X]. }
  { intros a Ha Wa. assert (Wa' : op <= a < op + 416) by (unfold W3 in Wa; lia).
    split; [apply (L5SAR.obj_client L ar LB FF 0 0 op 416 a AOB); lia| lia]. }
  intros M3 model3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3 VV3.
  assert (EK23n : L5SAR.ek L ar LB FF sp 24576 [(op, 416)] M2 M3) by (apply (EKO M2 M3 W3 FR3); intros a X; unfold W3 in X; lia).
  assert (EK03 : L5SAR.ek L ar LB FF sp 24576 [(op, 416)] M0 M3) by (apply (L5SAR.ek_trans L ar LB FF sp 24576 _ M0 M2 M3 EK02 EK23n)).
  assert (ASTK3 : L5CA.astk ar M3 sp 24576) by (apply (L5SAR.astk_grows ar M2 M3 sp 24576 ASTK2 MGM3)).
  assert (BASE3 : PMSTA.base_okA RSEGS PMA.AD M3).
  { apply (PMAIS1.base_ok_agree M2 M3); [|exact BASE2]. intros a Ha. unfold PMAIS1.brg in Ha. apply FR3; [lia| unfold W3; lia]. }
  assert (LOC3 : PMST.loc_ok RSEGS PMA.AD M3 true).
  { apply (PMAIS1.loc_ok_agree M2 M3 true); [|exact LOC2]. intros a Ha. apply FR3; [lia| unfold W3; lia]. }
  assert (STKSH3 : shadow_zero M3 (sp - 24576) 3072).
  { apply (PMKA.stksh_keepA L ar LB FF sp 24576 [(op, 416)] M0 M3 EK03 WAPP); [lia| lia| lia| | lia| exact STKSH].
    apply PMAIS1.sub8; [exact A16| reflexivity]. }
  assert (ND3 : NoDup (map ff_addr (FF ++ LK2))).
  { pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH3) as WF3. cbn zeta in WF3.
    destruct WF3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ND & _). exact ND. }
  (* [comment removed for export] *)
  apply (LOC fx3 R3 M3 model3 K LB FF LK2 Aw2 cr (op + 48) (sp - 240) 708132 true HH3 AM3 K0).
  { split; [rewrite L5K.rl1; exact D1|]. split; [split; [lia| reflexivity]|]. split; [rewrite L5K.rl2, (KS3 2%nat) by inl; exact J2|].
    split; [rewrite L5K.rl3, (KS3 3%nat) by inl; rewrite CS2 by inl; rewrite (KS1 3%nat) by inl; exact Rgp|].
    split; [rewrite L5K.rl4, (KS3 4%nat) by inl; rewrite CS2 by inl; rewrite (KS1 4%nat) by inl; exact Rtp|].
    change (PMSPA.pm_scr 2) with 16384. split.
    - apply (L5SAR.astk_sub ar M3 M3 sp 24576 240 16384 ASTK3 (fun x X => X)); [lia| lia| lia|].
      replace (sp - 240) with (sp + (-15) * 16) by lia. rewrite Z.mod_add by lia. exact A16.
    - change (16384 / 8) with 2048. apply (PMKA.shadow_zero_sub M3 (sp - 24576) 3072 (sp - 240 - 16384) 2048);
        [apply PMAIS1.sub8; [exact A16| reflexivity]| replace (sp - 240 - 16384) with (sp - 16624) by lia; apply PMAIS1.sub8; [exact A16| reflexivity]| lia| lia| lia| exact STKSH3]. }
  { apply (PMAIS1.ffroom_incl 6 2 FF LK0 LK2 FRM INC2 ND3). lia. }
  { intros f Hf. specialize (FRS f Hf). lia. }
  { rewrite L5K.rl10. exact D10. }
  { destruct AOP as (f & Hf & X1 & X2). exists f. split; [exact Hf| lia]. }
  { replace (op + 48) with (op + 6 * 8) by lia. rewrite Z.mod_add by lia. exact O8. }
  { apply (L5.defined_grows M2 M3 _ _ MGM3). apply (L5.defined_sub M2 op 416); [exact ODEF2| lia| lia]. }
  { exact BASE3. }
  { exact LOC3. }
  intros fx4 R4 M4 model4 LK4 Aw4 RP4 C56 LOC4 HP4 MRT4 INC4 IA4 AM4 HH4.
  change (PMSPA.pm_scr 2) with 16384 in HP4. change ((op + 48, 8) :: (if true then [] else PMSPA.loc_W PMA.AD)) with [(op + 48, 8)] in HP4.
  assert (EK34 : L5SAR.ek L ar LB FF sp 24576 [(op, 416)] M3 M4).
  { apply (L5SAR.ek_callee L ar LB [] FF [] sp 24576 (sp - 240) 16384 [(op, 416)] [(op + 48, 8)] M3 M4 HP4); [lia| lia|].
    intros a Hc Ho rg [<-|[]] Hr. apply (Ho (op, 416)); [left; reflexivity| unfold L5.in_rng in *; cbn [fst snd] in *; lia]. }
  assert (DK34 : L5SAR.dk L ar LB FF sp 24576 M3 M4) by (apply (L5SAR.dk_callee L ar LB [] FF [] sp 24576 (sp - 240) 16384 [(op + 48, 8)] M3 M4 HP4); lia).
  assert (ASTK4 : L5CA.astk ar M4 sp 24576).
  { apply (L5SAR.astk_after L ar C HI HIok LB FF LK2 cr Aw2 M3 M3 M4 _ sp 24576 (sp - 240) 16384 [(op + 48, 8)] HH3 ASTK3 (fun x X => X) HP4); lia. }
  assert (EK04 : L5SAR.ek L ar LB FF sp 24576 [(op, 416)] M0 M4) by (apply (L5SAR.ek_trans L ar LB FF sp 24576 _ M0 M3 M4 EK03 EK34)).
  assert (DK04 : L5SAR.dk L ar LB FF sp 24576 M0 M4).
  { apply (L5SAR.dk_trans L ar LB FF sp 24576 M0 M1 M4 (L5SAR.dk_grows L ar LB FF sp 24576 M0 M1 MGM1)).
    apply (L5SAR.dk_trans L ar LB FF sp 24576 M1 M2 M4 DK12).
    apply (L5SAR.dk_trans L ar LB FF sp 24576 M2 M3 M4 (L5SAR.dk_grows L ar LB FF sp 24576 M2 M3 MGM3) DK34). }
  assert (KEEP4 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp - 240 - 16384 <= a < sp - 240) -> ~ (op + 48 <= a < op + 56) ->
                  aclient L ar LB FF 0 0 a -> M4 (Z_to_bv 64 a) = M3 (Z_to_bv 64 a)).
  { intros a Ha N0 N1 Hc. apply (proj1 HP4). split; [lia|]. split.
    - apply (L5SAR.aclient_narrow L ar LB FF 0 0); [exact Hc| lia].
    - intros rg [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. lia. }
  (* [comment removed for export] *)
  assert (AG14 : forall a, (op <= a < op + 416 /\ ~ (op + 24 <= a < op + 56) /\ ~ (op + 104 <= a < op + 112) /\ ~ (op + 152 <= a < op + 160)
                            /\ ~ (op + 240 <= a < op + 252)) \/ (sp - 232 <= a < sp) -> M4 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
  { intros a Ha. assert (CLa : aclient L ar LB FF 0 0 a) by (destruct Ha as [Ha|Ha]; [apply CL; lia| apply SCL; lia]).
    rewrite KEEP4; [| lia| lia| lia| exact CLa]. rewrite FR3; [| lia| unfold W3; lia]. apply KEEP2; [lia| lia| lia| exact CLa]. }
  assert (AG34 : forall a, op <= a < op + 416 /\ ~ (op + 48 <= a < op + 56) -> M4 (Z_to_bv 64 a) = M3 (Z_to_bv 64 a)).
  { intros a Ha. apply KEEP4; [lia| lia| lia| apply CL; lia]. }
  assert (AG24 : forall a, op + 152 <= a < op + 160 -> M4 (Z_to_bv 64 a) = M2 (Z_to_bv 64 a)).
  { intros a Ha. rewrite AG34 by lia. apply FR3; [lia| unfold W3; lia]. }
  Ltac t64 AG V VIS X Ms := apply (L5C.u64_at_agree RSEGS Ms); [intros i Hi; apply AG; (lia || fail 1 "AG")| (lia || fail 1 "B1")| (lia || fail 1 "B2")|];
                            apply (PMAIS1.vis_u64 _ _ _ _ _ VIS); [apply V; (lia || fail 1 "V") | (lia || fail 1 "B3") | (lia || fail 1 "B4") | exact X].
  Ltac t32 AG V VIS X Ms := apply (PMF.u32_at_agree RSEGS Ms); [intros i Hi; apply AG; (lia || fail 1 "AG32")| (lia || fail 1 "C1")| (lia || fail 1 "C2")|];
                            apply (PMAIS1.vis_u32 _ _ _ _ _ VIS); [apply V; (lia || fail 1 "V32") | (lia || fail 1 "C3") | (lia || fail 1 "C4") | exact X].
  Ltac t8 AG V VIS X Ms := apply (L5C.u8_at_agree RSEGS Ms); [intros i Hi; apply AG; (lia || fail 1 "AG8")| (lia || fail 1 "E1")| (lia || fail 1 "E2")|];
                           apply (vis_u8 _ _ _ _ _ VIS); [apply V; (lia || fail 1 "V8") | (lia || fail 1 "E3") | (lia || fail 1 "E4") | exact X].
  assert (V3a : forall a n, op <= a /\ a + n <= op + 416 -> L5A.avis H2 a n).
  { intros a n Ha. eapply L5A.avis_sub; [exact OVIS2| lia| lia]. }
  assert (AOF : forall a n, fb + 32 <= a -> a + n <= fb + 2040 -> PMSPA.aobjA FF a n).
  { intros a n Ha Hn. exists (fb, 5, rs); split; [exact Hfb| cbn; change (ff_bytes 5) with 2048; lia]. }
  assert (OUT0 : forall a n, fb + 32 <= a -> a + n <= op \/ op + 416 <= a -> forall i, a <= i < a + n -> L5.outside [(op, 416)] i).
  { intros a n Ha Hn i Hi rg [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. lia. }
  assert (Eop : PNARCS.op fb = op) by reflexivity.
  apply (KONT fx4 R4 M4 model4 LK4 Aw4).
  assert (CS4 : forall k, In k L5SAR.cs_all -> getr R4 (reg k) = getr R3 (reg k)) by (intros k Hk; apply (L5SAR.cs_of_preserved R3 R4 k RP4 Hk)).
  split; [rewrite CS4 by inl; rewrite (KS3 2%nat) by inl; exact J2|]. split; [rewrite CS4 by inl; rewrite (KS3 8%nat) by inl; exact J8|].
  split; [rewrite CS4 by inl; rewrite (KS3 9%nat) by inl; exact J9|]. split; [rewrite CS4 by inl; rewrite (KS3 18%nat) by inl; exact J18|].
  split; [rewrite CS4 by inl; exact D19|]. split; [rewrite CS4 by inl; rewrite (KS3 20%nat) by inl; exact J20|].
  split; [rewrite CS4 by inl; rewrite (KS3 21%nat) by inl; exact J21|]. split; [rewrite CS4 by inl; rewrite (KS3 22%nat) by inl; exact J22|].
  split; [rewrite CS4 by inl; rewrite (KS3 23%nat) by inl; exact J23|].
  split. { intros k Hk. assert (Hk' : In k L5SAR.cs_all /\ In k PNARCPA.KS_abrcB /\ In k PNARCPA.KS_abrcAl)
             by (destruct Hk as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; (split; [inl| split; inl])).
           destruct Hk' as (K1 & K2 & K3). rewrite (CS4 k K1), (KS3 k K2), (CS2 k K1). exact (KS1 k K3). }
  split. { apply (PMKA.u64_keepA RSEGS L ar LB FF sp 24576 [(op, 416)] M0 M4 EK04 WAPP FRB (fb + 96) _ (AOF (fb + 96) 8 ltac:(lia) ltac:(lia)));
             [apply OUT0; unfold op; lia| exact IVP]. }
  split. { destruct IIOS as (_ & _ & _ & IRD & _). replace (fb + 256) with (fb + 96 + 120 + 40) by lia. replace (fb + 112) with (fb + 96 + 16) by lia.
           apply (PMKA.u64_keepA RSEGS L ar LB FF sp 24576 [(op, 416)] M0 M4 EK04 WAPP FRB (fb + 96 + 120 + 40) _ (AOF (fb + 96 + 120 + 40) 8 ltac:(lia) ltac:(lia)));
             [apply OUT0; unfold op; lia| exact IRD]. }
  split. { unfold PNARCS.saves_nis.
           split; [t64 AG14 V1a VIS1 F168 M1|]. split; [t64 AG14 V1a VIS1 F176 M1|]. split; [t64 AG14 V1a VIS1 F184 M1|].
           split; [replace (fb + 96) with (op - 368) by (unfold op; lia); t64 AG14 V1a VIS1 F192 M1|]. split; [t64 AG14 V1a VIS1 F200 M1|].
           split; [t64 AG14 V1a VIS1 F208 M1|]. split; [t64 AG14 V1a VIS1 F216 M1|]. split; [t64 AG14 V1a VIS1 F224 M1| t64 AG14 V1a VIS1 F232 M1]. }
  unfold PNARCS.rmidc.
  split. { unfold PNARCS.saves_rd.
           split; [t64 AG14 V1a VIS1 S8 M1|]. split; [t64 AG14 V1a VIS1 S16 M1|]. split; [t64 AG14 V1a VIS1 S24 M1|]. split; [t64 AG14 V1a VIS1 S32 M1|].
           split; [t64 AG14 V1a VIS1 S40 M1|]. split; [t64 AG14 V1a VIS1 S48 M1|]. split; [t64 AG14 V1a VIS1 S56 M1|].
           split; [t64 AG14 V1a VIS1 S64 M1|]. split; [t64 AG14 V1a VIS1 S72 M1|]. split; [t64 AG14 V1a VIS1 S80 M1| t64 AG14 V1a VIS1 S88 M1]. }
  split. { unfold PNARCS.saves_src.
           split; [t64 AG14 V1a VIS1 F120 M1|]. split; [t64 AG14 V1a VIS1 F128 M1|]. split; [t64 AG14 V1a VIS1 F136 M1|].
           split; [t64 AG14 V1a VIS1 F144 M1| t64 AG14 V1a VIS1 F152 M1]. }
  split. { unfold PNARCS.hcells.
           split; [t64 AG14 V1a VIS1 C0 M1|]. split; [t8 AG14 V1a VIS1 C8 M1|]. split; [t8 AG14 V1a VIS1 C9 M1|]. split; [t8 AG14 V1a VIS1 C10 M1|].
           split; [t32 AG14 V1a VIS1 C12 M1|].
           split; [t64 AG34 V3a VIS3 D32 M3|]. split; [exact C56|]. split; [t64 AG34 V3a VIS3 D112 M3|].
           split; [t32 AG14 V1a VIS1 C144 M1|]. split; [t32 AG14 V1a VIS1 C148 M1|]. split; [t64 AG14 V1a VIS1 C152 M1|].
           split; [apply (L5C.u64_at_agree RSEGS M2); [intros i Hi; apply AG24; lia| lia| lia| exact C160']|].
           apply (PMF.zeros_at_agree M1); [intros i Hi; apply AG14; lia|]. apply (PMAIS1.vis_zeros _ _ _ _ _ VIS1); [apply V1a; lia| exact Z168]. }
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB FF LK4 cr Aw4 M4 model4 op 416 sp 24576 HH4 AOB ltac:(lia) ltac:(reflexivity)) as (_ & _ & ODEF4 & _).
  split; [exact ODEF4|].
  split; [apply (PMKA.acc_keepA' L ar LB FF sp 24576 _ M0 M4 EK04 WAPP FRB op 416 AOP ACC)|].
  split; [apply (PMKA.acc_keepA' L ar LB FF sp 24576 _ M0 M4 EK04 WAPP FRB oo 24 AOO ACCO)|].
  assert (AOOs : forall a n, oo <= a -> a + n <= oo + 24 -> PMSPA.aobjA FF a n).
  { intros a n Ha Hn. destruct AOO as (f & Hf & X1 & X2). exists f. split; [exact Hf| clear - Ha Hn X1 X2; Lia.lia]. }
  assert (OUTO : forall i, oo <= i < oo + 24 -> L5.outside [(op, 416)] i).
  { intros i Hi rg [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. clear - Hi Hr OOAP'. destruct OOAP'; Lia.lia. }
  split. { apply (PMKA.u64_keepA RSEGS L ar LB FF sp 24576 [(op, 416)] M0 M4 EK04 WAPP FRB oo _ (AOOs oo 8 ltac:(Lia.lia) ltac:(Lia.lia)));
             [intros i Hi; apply OUTO; Lia.lia| exact OO0]. }
  split. { apply (PMKA.u32_keepA RSEGS L ar LB FF sp 24576 [(op, 416)] M0 M4 EK04 WAPP FRB (oo + 16) _ (AOOs (oo + 16) 4 ltac:(Lia.lia) ltac:(Lia.lia)));
             [intros i Hi; apply OUTO; Lia.lia| exact OO16]. }
  split; [apply (PMKA.acc_keepA' L ar LB FF sp 24576 _ M0 M4 EK04 WAPP FRB (fb + 96) 272 AOIS ACCI)|].
  split; [exact ASTK4|].
  split. { unfold PNARCS.SCR. change (24576 / 8) with 3072. apply (PMKA.stksh_keepA L ar LB FF sp 24576 [(op, 416)] M0 M4 EK04 WAPP); [lia| lia| lia| | lia| exact STKSH].
           apply PMAIS1.sub8; [exact A16| reflexivity]. }
  split. { apply (PMAIS1.base_ok_agree M3 M4); [|exact BASE3]. intros a Ha. unfold PMAIS1.brg in Ha. apply KEEP4; [lia| lia| lia|].
           unfold aclient, aclient_g. right; right; left. rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa). split; [lia|].
           destruct Ha as [Ha|Ha]; [intros X; pose proof (L5A.aly_static_lo L C LYa a X); lia|].
           apply (fun D_ => PMA.ly_static L C LY a (PnStatics.PNST.dep_of_j _ _ a D_)). unfold PMST.dep, pm_initc. cbn [pa_canary pa_need_locks pa_locale_lock PMA.AD ADDR_A].
           destruct Ha as [Ha|[Ha|Ha]];
             [right; left; lia
             | right; right; exists (0x693f93, 0x693f94); split; [left; reflexivity| cbn [fst snd]; lia]
             | right; right; exists (0x694070, 0x694074); split; [right; left; reflexivity| cbn [fst snd]; lia]]. }
  split; [exact LOC4|].
  split; [exact HH4|]. split; [exact AM4|].
  split. { apply (L5LZ.model_rt_trans model0 model3 model4); [|exact MRT4]. apply (L5LZ.model_rt_trans model0 model2 model3); [|exact MRT3].
           apply (L5LZ.model_rt_trans model0 model1 model2); [exact MRT1| exact MRT2]. }
  split; [intros x Hx; apply INC2; apply INC4; exact Hx|].
  split; [intros x Hx; apply IA4; apply IA2; exact Hx|].
  split; [unfold PNARCS.SCR; exact EK04| unfold PNARCS.SCR; exact DK04].
Qed.

End Stage.
End PNARC1.
