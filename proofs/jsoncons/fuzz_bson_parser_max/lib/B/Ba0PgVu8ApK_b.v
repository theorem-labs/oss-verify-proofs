(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.LeanFeed.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality Permutation.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b L5StepAR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmModelFacts PmStatics PmStaticsA PmSpecs PmParSpecs PmTxtSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PmSpecsAX_b PnSpecsAa_b
     PmModelFactsA_b PnStepA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnASrcKit_b PnASrcReadK_b PnAReset1_b PnAEmbKit_b PnAVu8Dtor_b PnAVu8GrowP_b Ba0_code_b404c_b4050_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgSrc. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgSrcA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgV8. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgV8A_b PgV8KitA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnRunA_b PnSpecsAX_b PnSpecsAX8_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PGVAPK.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Abbreviation AD := PMA.AD.
Abbreviation v8_atA := (PGV8.v8_at RSEGS PMSPA.accA PGV8A.annA).

Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Let LYa := PMA.ly_as0 L C LY.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma memcpy_call27 (fx : FPState) R M model K LB FF LK cr Aw (sp' r dst src n : Z) :
  ri_inv HI LB FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] ->
  getr R (reg 1) = Z_to_bv 64 r -> L5.ra_ok r -> getr R (reg 2) = Z_to_bv 64 sp' -> getr R (reg 4) = Z_to_bv 64 (hl_tp L) ->
  getr R (reg 10) = Z_to_bv 64 dst -> getr R (reg 11) = Z_to_bv 64 src -> getr R (reg 12) = Z_to_bv 64 n -> 0 <= n <= 2 ^ 27 ->
  L5CA.astk ar M sp' 2560 ->
  aacc M dst n -> (forall i, 0 <= i < n -> aclientw L ar LB FF sp' 2560 (dst + i)) -> L5.defined M dst n -> 0 <= dst -> dst + n <= 2 ^ 47 -> app_rng ar dst n ->
  aacc M src n -> 0 <= src -> src + n <= 2 ^ 47 -> app_rng ar src n -> (forall i, 0 <= i < n -> aclient L ar LB FF sp' 2560 (src + i)) -> L5.defined M src n ->
  (dst + n <= src \/ src + n <= dst) ->
  (forall (fx' : FPState) R' M' model', regs_preserved R R' -> L5.defined M' dst n ->
      L5CA.ahpres L ar LB FF sp' 2560 [(dst, n)] M M' ->
      model_rt model model' -> L5CA.amodel_ok Aw model' -> ri_inv HI LB FF LK cr Aw M' (vml_of model') ->
      srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx' R' r M' model') K) ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0x77c94 M model) K.
Proof using All.
  intros HH AM HK G1 RA G2 G4 G10 G11 G12 Hn ASTK ACD CLD DDEF D0 D1 APD ACS S0 S1 APS CLS SDEF0 NOV KONT.
  pose proof (HAJ.aior_memcpy _ _ _ _ _ HIok) as HF.
  unfold amemcpy_spec, amemcpy_spec_at, amem_pre, amem_post in HF. rewrite (L5A.aly_segs L C LYa), (L5A.aly_scr_mem L C LYa), (L5A.aly_memcpy L C LYa) in HF.
  pose proof ASTK as (A16 & SLO & SHI & SPT & SD & SU).
  assert (U2 : bv_unsigned (getr R 2%bv) = sp') by (rewrite L5K.rl2, G2; apply L5.unsigned_lit; clear - SLO SHI SPT; lia).
  destruct (PMASRK.rdn_of_defR M (Z.to_nat n) src S0 ltac:(rewrite Z2Nat.id by lia; lia)) as (bs & RDN).
  { intros i Hi. rewrite Z2Nat.id in Hi by lia. apply SDEF0. lia. }
  unfold PMSPA.cfg.
  eapply (HF fx R M model LB FF LK cr Aw dst src n bs K); clear HF.
  - split. exact HH. split. exact (proj1 AM). split. exact (proj2 AM).
    split. rewrite L5K.rl10. exact G10. split. rewrite L5K.rl12. exact G12. split. lia.
    split. rewrite L5K.rl4. exact G4.
    split. rewrite L5K.rl1, G1. apply Hoare.ret_ok_even. rewrite L5.unsigned_lit by (destruct RA as [X _]; clear - X; lia). exact (proj2 RA).
    split. { rewrite U2. pose proof (L5SAR.astack_ok_of_astk L ar C LYa M M sp' 2560 0 2560 ASTK (mem_grows_refl M)) as X.
             replace (sp' - 0) with sp' in X by (clear; lia). apply X; [clear; lia| clear; lia| clear; lia| replace (sp' - 0) with sp' by (clear; lia); exact A16]. }
    split. exact ACD.
    split. { intros i Hi. rewrite U2. apply CLD. exact Hi. }
    split. { intros i m0 Hi Hm. apply (L5C.writable_of_defined RSEGS M dst n DDEF D0 ltac:(clear - D1; lia)). exact Hi. exact Hm. }
    split. exact HK. exact APD.
  - rewrite L5K.rl11. exact G11.
  - exact ACS.
  - split; [exact S0| exact S1].
  - exact APS.
  - intros i Hi. right. rewrite U2. apply CLS. exact Hi.
  - exact RDN.
  - intros _. exact NOV.
  - intros R' M' model' mR10 RP BYTES PRES SDEF RT2 MI2 HH2. rewrite U2 in PRES, SDEF. rewrite L5K.rl1, G1 in *.
    apply (KONT fx R' M' model' RP).
    + intros i Hi. destruct (BYTES i Hi) as (v & _ & Bv). unfold byte_at in Bv. rewrite Bv. discriminate.
    + split; [|split].
      * intros a (Ha & Hc & Ho). apply PRES; [exact Ha| exact Hc|]. intros X. apply (Ho (dst, n)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; exact X].
      * intros i Hi. apply SDEF. clear - Hi; lia.
      * intros a Ha Hc D. destruct (L5SAR.rng_dec a dst (dst + n)) as [X|X].
        -- destruct (BYTES (a - dst) ltac:(clear - X; lia)) as (v & _ & Bv). unfold byte_at in Bv. replace (dst + (a - dst)) with a in Bv by (clear; lia). rewrite Bv. discriminate.
        -- rewrite (PRES a Ha Hc X). exact D.
    + exact RT2.
    + split; [rewrite (L5LZ.model_rt_halted _ _ RT2); exact (proj1 AM)| exact MI2].
    + exact HH2.
Qed.

Definition nsh (a n : Z) : Prop := a + n <= 2147446784 \/ 17594333495296 <= a.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma blksh_ek LBc FF sp' scr' W' M M' q m :
  L5SAR.ek L ar LBc FF sp' scr' W' M M' -> PMKA.wapp W' -> In (q, m) LBc -> 0 <= q -> q + m <= 2 ^ 47 -> PMFA.agsh M M' q m.
Proof using All.
  intros EK WA Hin H0 H1 x Hx. pose proof (PMKA.S_in_shadow x ltac:(lia)) as SX.
  apply EK. split; [unfold BIGSHADOW_LO, BIGSHADOW_HI in SX; lia|]. split; [| exact (PMKA.wapp_outside_shadow W' (S x) WA SX)].
  unfold aclient, aclient_g. do 6 right. exists (q, m). split; [exact Hin|]. cbn [fst snd]. unfold in_shadow_of. split; apply PMKA.S_mono; lia.
Qed.
(* [comment removed for export] *)
Lemma objsh_ek LBc FF sp' scr' W' M M' o n :
  L5SAR.ek L ar LBc FF sp' scr' W' M M' -> PMKA.wapp W' -> PMSPA.aobjA FF o n -> 0 <= o -> o + n <= 2 ^ 47 -> PMFA.agsh M M' o n.
Proof using All.
  intros EK WA AO H0 H1 x Hx. pose proof (PMKA.S_in_shadow x ltac:(lia)) as SX.
  apply EK. split; [unfold BIGSHADOW_LO, BIGSHADOW_HI in SX; lia|]. split; [| exact (PMKA.wapp_outside_shadow W' (S x) WA SX)].
  exact (PNAEK.frame_sh_client L ar FF o n x LBc sp' scr' AO Hx).
Qed.
(* [comment removed for export] *)
Lemma obj_ek LBc FF sp' scr' W' M M' o n a m :
  L5SAR.ek L ar LBc FF sp' scr' W' M M' -> PMSPA.aobjA FF o n -> o mod 8 = 0 -> 0 <= o -> o + n <= 2 ^ 47 -> o <= a -> a + m <= o + n ->
  (forall i, a <= i < a + m -> L5.outside W' i) -> L5C.agree_on M M' a m.
Proof using All.
  intros EK AO O8 H0 H1 H2 H3 OW i Hi. apply EK. split; [lia|]. split; [| apply OW; exact Hi].
  apply (L5SAR.obj_client L ar LBc FF sp' scr' o n i (PMKA.aobj_of_aobjA FF o n AO O8)). lia.
Qed.
(* [comment removed for export] *)
Lemma shz_agree (M M' : word -> option byte) lo g : lo mod 8 = 0 -> 0 <= g -> PMFA.agsh M M' lo (8 * g) -> shadow_zero M lo g -> shadow_zero M' lo g.
Proof using All.
  intros L8 Hg AG SZ j Hj. pose proof (SZ j Hj) as Z1. unfold byte_at in *. rewrite (PMFA.S_granule lo j L8 ltac:(lia)) in *.
  rewrite (AG (lo + 8 * j) ltac:(lia)). exact Z1.
Qed.
Lemma shblk_agree (M M' : word -> option byte) b c : b mod 8 = 0 -> 0 <= c -> PMFA.agsh M M' b c -> shadow_blk M b c -> shadow_blk M' b c.
Proof using All.
  intros B8 Hc AG (Z0 & P1).
  assert (D : 0 <= c / 8 /\ 8 * (c / 8) <= c /\ c mod 8 = c - 8 * (c / 8) /\ 0 <= c mod 8 < 8).
  { pose proof (Z.div_mod c 8 ltac:(lia)). pose proof (Z.mod_pos_bound c 8 ltac:(lia)). pose proof (Z.div_pos c 8 Hc ltac:(lia)). lia. }
  split.
  - intros j Hj. pose proof (Z0 j Hj) as Z1. unfold byte_at in *. rewrite (PMFA.S_granule b j B8 ltac:(lia)) in *. rewrite (AG (b + 8 * j) ltac:(lia)). exact Z1.
  - intros N. pose proof (P1 N) as Z1. unfold byte_at in *. rewrite (PMFA.S_granule b (c / 8) B8 ltac:(lia)) in *. rewrite (AG (b + 8 * (c / 8)) ltac:(lia)). exact Z1.
Qed.
(* [comment removed for export] *)
Lemma agsh_piece (M M1 : word -> option byte) (P : Z -> Prop) a n :
  (forall i, 0 <= i < 2 ^ 64 -> ~ P i -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i)) -> (forall i, P i -> ~ (BIGSHADOW_LO <= i < BIGSHADOW_HI)) ->
  0 <= a -> a + n <= 2 ^ 47 -> PMFA.agsh M M1 a n.
Proof using All.
  intros FR PS H0 H1 x Hx. pose proof (PMKA.S_in_shadow x ltac:(lia)) as SX. apply FR; [unfold BIGSHADOW_LO, BIGSHADOW_HI in SX; lia|].
  intros X. exact (PS _ X SX).
Qed.
Lemma aacc_sub (M : word -> option byte) a n a' n' : aacc M a n -> a <= a' -> a' + n' <= a + n -> aacc M a' n'.
Proof using All. intros AC H1 H2 y Hy. apply AC. clear - H1 H2 Hy. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Call.
Variables (R0 : bvmap 5 word) (M0 : word -> option byte) (model0 : Model) (K : TSet) (LB : list (Z * Z)) (FF LK0 : list fframe) (Aw0 : list (Z * Z)) (cr0 : credit).
Variables (v S r g k : Z) (x : PGV8.v8).
Hypothesis Rra0 : getr R0 (reg 1) = Z_to_bv 64 r.
Hypothesis RAok : L5.ra_ok r.
Hypothesis Rsp0 : getr R0 (reg 2) = Z_to_bv 64 S.
Hypothesis Rgp0 : getr R0 (reg 3) = Z_to_bv 64 (pa_gp AD).
Hypothesis Rtp0 : getr R0 (reg 4) = Z_to_bv 64 (hl_tp L).
Hypothesis K0 : K [].
Hypothesis FRS : PMSPA.ffrsA FF S.
Hypothesis AO : PMSPA.aobjA FF v 24.
Hypothesis V8 : v mod 8 = 0.
Hypothesis OK0 : PGV8.v8_ok x g.
Hypothesis Hk : 1 <= k.
Hypothesis GROK : PGV8.v8_grow_ok x (PGV8.v8_size x + k).
Hypothesis CRL0 : PMSP.credit_le (PMSPA.scA L (PGV8.pot_v8 (PMSPA.HV L ar) x g)) cr0.
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)) (x' : PGV8.v8) (g' : Z) (cr' : credit),
  regs_preserved R0 R' -> v8_atA M' v x' -> PGV8.v8_size x' = PGV8.v8_size x + k -> PGV8.v8_ok x' g' ->
  PGV8.v8_cap x <= PGV8.v8_cap x' ->
  (PGV8.v8_size x' <= PGV8.v8_cap x -> PGV8.v8_own x' = PGV8.v8_own x /\ PGV8.v8_cap x' = PGV8.v8_cap x /\ g' = g) ->
  (PGV8.v8_cap x' = PGV8.v8_cap x \/ PGV8.v8_cap x' = Z.max (2 * PGV8.v8_cap x) (PGV8.v8_size x + k)) ->
  L5CA.ahpres L ar LB FF S (PMSPA.pm_scr 1) [(v, 24)] M0 M' ->
  PMSP.credit_keep cr0 cr' (PMSPA.scA L (PGV8.pot_v8 (PMSPA.HV L ar) x g)) (PMSPA.scA L (PGV8.pot_v8 (PMSPA.HV L ar) x' g')) ->
  model_rt model0 model' -> incl LK' LK0 -> incl Aw0 Aw' -> L5CA.amodel_ok Aw' model' -> ri_inv HI (PGV8.v8_own x' ++ LB) FF LK' cr' Aw' M' (vml_of model') ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx' R' r M' model') K.
(* [comment removed for export] *)
Hypothesis OPN : PMA.opnew_spec L ar HI.
Hypothesis OPD : PMA.opdel_spec L ar HI.
Hypothesis ANNI : PNSAX8.ann_increase_v8_spec RSEGS AD L ar HI 0xb609c.
Hypothesis ANNN : PNSAX8.ann_new_v8_spec RSEGS AD L ar HI 0xb615c.
Hypothesis ANND : PNSAX.ann_delete_v8_spec RSEGS AD L ar HI 0xabb8c.
(* [comment removed for export] *)
Hypothesis VS0 : v8_atA M0 v x.
Hypothesis HH0 : ri_inv HI (PGV8.v8_own x ++ LB) FF LK0 cr0 Aw0 M0 (vml_of model0).
(* [comment removed for export] *)
(* [comment removed for export] *)
Hypothesis Ra0 : getr R0 (reg 10) = Z_to_bv 64 v.
Hypothesis Ra1 : getr R0 (reg 11) = Z_to_bv 64 k.
Hypothesis AM0 : L5CA.amodel_ok Aw0 model0.
Hypothesis STK0 : L5CA.astk ar M0 S 14336.
Hypothesis STKSH0 : shadow_zero M0 (S - 14336) 1792.

Definition U (i : nat) : Z := bv_unsigned (getr R0 (reg i)).
(* [comment removed for export] *)
Definition saves (M : word -> option byte) : Prop :=
  L5.u64_at RSEGS M (S - 8) (U 1) /\ L5.u64_at RSEGS M (S - 16) (U 8) /\ L5.u64_at RSEGS M (S - 24) (U 9).
(* [comment removed for export] *)
Definition kept0 (R : bvmap 5 word) : Prop := forall i, In i [3; 4; 22; 23; 24; 25; 26; 27]%nat -> getr R (reg i) = getr R0 (reg i).
Definition stok (model : Model) (LK : list fframe) (Aw : list (Z * Z)) : Prop :=
  L5CA.amodel_ok Aw model /\ model_rt model0 model /\ incl LK LK0 /\ incl Aw0 Aw.
(* [comment removed for export] *)
Definition mem_ok (M : word -> option byte) : Prop :=
  L5SAR.ek L ar LB FF S 14336 [(v, 24)] M0 M /\ L5SAR.dk L ar LB FF S 14336 M0 M /\ L5CA.astk ar M S 14336 /\ PMSPA.accA M v 24
  /\ shadow_zero M (S - 14336) 1792.

Lemma kept0_of (R R1 : bvmap 5 word) : kept0 R -> (forall i, In i [3; 4; 22; 23; 24; 25; 26; 27]%nat -> getr R1 (reg i) = getr R (reg i)) -> kept0 R1.
Proof using All. intros KP H i Hi. rewrite (H i Hi). exact (KP i Hi). Qed.
Lemma kept0_pres (R R1 : bvmap 5 word) : kept0 R -> regs_preserved R R1 -> kept0 R1.
Proof using All.
  intros KP RP. apply (kept0_of R R1 KP). intros i Hi. apply (L5SAR.cs_of_preserved R R1 i RP). unfold L5SAR.cs_all. cbn in Hi |- *. tauto.
Qed.
Lemma stok_step model LK Aw model1 LK1 Aw1 : stok model LK Aw -> L5CA.amodel_ok Aw1 model1 -> model_rt model model1 -> incl LK1 LK -> incl Aw Aw1 -> stok model1 LK1 Aw1.
Proof using All.
  intros (A1 & A2 & A3 & A4) B1 B2 B3 B4. split; [exact B1|]. split; [eapply L5LZ.model_rt_trans; [exact A2| exact B2]|].
  split; [intros f Hf; apply A3; apply B3; exact Hf| intros q Hq; apply B4; apply A4; exact Hq].
Qed.

(* [comment removed for export] *)
Lemma nfacts HL LK cr Aw M model : ri_inv HI (HL ++ LB) FF LK cr Aw M (vml_of model) -> mem_ok M ->
  (S mod 16 = 0 /\ ahl_ceil ar + 4096 + 14336 <= S /\ S <= ar_sptop ar /\ 140735340871680 <= ar_sptop ar <= 2 ^ 47 /\ 0 <= ahl_ceil ar)
  /\ (6905856 <= v /\ v + 24 <= ahl_ceil ar /\ nsh v 24 /\ L5.defined M v 24)
  /\ (forall q m, In (q, m) (HL ++ LB) -> 4096 <= q /\ 0 < m /\ q + m <= ahl_ceil ar /\ q mod 16 = 0 /\ nsh q m /\ (q + m <= v \/ v + 24 <= q) /\ L5.defined M q m).
Proof using All.
  intros HH (_ & _ & STK & _). pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & _ & _ & _ & _ & _ & TOP & _).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LK cr Aw M model v 24 S 14336 HH (PMKA.aobj_of_aobjA FF v 24 AO V8) ltac:(lia) ltac:(reflexivity))
    as ((O1 & O2 & O3 & O4 & O5) & OBIG & ODEF & _).
  unfold app_mem, FS_BYTES, BIGSHADOW_LO, BIGSHADOW_HI in *.
  split; [split; [exact A16|]; lia|]. split; [split; [exact O1|]; split; [exact O2|]; split; [unfold nsh; lia| exact ODEF]|].
  intros q m Hin. destruct (PNAEK.blk_facts L ar C HI LY HIok _ FF LK cr Aw M _ q m HH Hin) as (Q0 & Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & QD & QF).
  split; [exact Q0|]. split; [exact Q1|]. split; [exact Q2|]. split; [exact Q4|]. split; [unfold nsh; lia|]. split; [|exact QD].
  destruct AO as (f & Hf & Y1 & Y2). specialize (QF f Hf). lia.
Qed.

(* [comment removed for export] *)
Lemma vfacts HL LK cr Aw M model : ri_inv HI (HL ++ LB) FF LK cr Aw M (vml_of model) -> mem_ok M ->
  L5.img_clear (mrestrict (ahid Aw model) M) 1249280 1282048 /\ L5.u64_at RSEGS (mrestrict (ahid Aw model) M) 1309752 2147450880
  /\ L5.u32_at RSEGS (mrestrict (ahid Aw model) M) 1309760 1
  /\ (forall a n, S - 14336 <= a -> a + n <= S -> 0 <= n -> L5.writable RSEGS (mrestrict (ahid Aw model) M) a n)
  /\ L5KA.zeros_at (mrestrict (ahid Aw model) M) (v / 8 + 2147450880) 3 /\ L5.writable RSEGS (mrestrict (ahid Aw model) M) v 24
  /\ (forall a n, S - 14336 <= a -> a + 8 * n <= S -> a mod 8 = 0 -> 0 <= n -> L5KA.zeros_at (mrestrict (ahid Aw model) M) (a / 8 + 2147450880) n)
  /\ (forall a n, (S - 14336 <= a /\ a + n <= 2 ^ 47) \/ (v <= a /\ a + n <= v + 24) -> L5A.avis (ahid Aw model) a n).
Proof using All.
  intros HH MO. destruct (nfacts HL LK cr Aw M model HH MO) as ((A16 & SLO & SHI & SPT & C0) & (O1 & O2 & O5 & ODEF) & _).
  destruct MO as (_ & _ & STK & ACC & STKSH).
  pose proof (HAJ.aior_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as ST. rewrite (L5A.aly_segs L C LYa) in ST.
  pose proof (L5A.statics_facts L C M LYa ST) as (GOT & CSB & CUAR & _).
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ FF LK cr Aw M model HH) as (HOFF & VIS & VIMG & _ & _ & _ & _ & VSTSH).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LK cr Aw M model v 24 S 14336 HH (PMKA.aobj_of_aobjA FF v 24 AO V8) ltac:(lia) ltac:(reflexivity))
    as (_ & _ & _ & OVIS & _).
  set (H := ahid Aw model) in *.
  split; [apply L5A.img_clear_mrestrict; exact GOT|].
  split; [apply (proj2 (L5A.u64_at_vis H M 1309752 2147450880 (VIMG 1309752 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CSB|].
  split; [apply (proj2 (L5A.u32_at_vis H M 1309760 1 (VIMG 1309760 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CUAR|].
  split.
  { intros a n X1 X2 X3. apply (proj2 (L5A.writable_vis H M a n (VIS a n ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5SAR.astk_writable ar M S 14336 a n STK); lia. }
  split; [exact (PMKA.obj_shadow_vis L ar C HI LYa HIok _ FF LK cr Aw M model v 24 HH AO V8 ltac:(lia) ltac:(reflexivity) ACC)|].
  split.
  { apply (proj2 (L5A.writable_vis H M v 24 OVIS ltac:(lia) ltac:(lia))). apply (L5C.writable_of_defined RSEGS M v 24 ODEF); lia. }
  split.
  { intros a n X1 X2 X3 X4.
    assert (M8a : (S - 14336) mod 8 = 0) by (apply PMKA.mod16_8'; replace (S - 14336) with (S + (-896) * 16) by lia; rewrite Z_mod_plus_full; exact A16).
    pose proof (PMKA.shadow_zero_sub M (S - 14336) 1792 a n M8a X3 X1 ltac:(lia) X4 STKSH) as SZ.
    assert (AV : L5A.avis H (a / 8 + 2147450880) n).
    { apply VSTSH. intros i Hi. change (a / 8 + 2147450880) with (HeapIfaceA.S a). rewrite (PMFA.S_granule a i X3 ltac:(lia)).
      unfold in_shadow_of. split; apply PMKA.S_mono; lia. }
    apply (proj2 (L5A.zeros_at_vis H M (a / 8 + 2147450880) n AV)). intros i Hi. exact (SZ i Hi). }
  intros a n [(X1 & X2)|(X1 & X2)]; [apply VIS; lia| exact (L5A.avis_sub H v 24 a n OVIS X1 X2)].
Qed.

Lemma pw_nsh HL LK cr Aw M model (P : Z -> Prop) : ri_inv HI (HL ++ LB) FF LK cr Aw M (vml_of model) -> mem_ok M ->
  (forall a, P a -> (S - 14336 <= a < S) \/ (v <= a < v + 24) \/ (exists q m, In (q, m) HL /\ q <= a < q + m)) ->
  forall i, P i -> ~ (BIGSHADOW_LO <= i < BIGSHADOW_HI).
Proof using All.
  intros HH MO PW i Pi X. destruct (nfacts HL LK cr Aw M model HH MO) as ((A16 & SLO & SHI & SPT & C0) & (O1 & O2 & O5 & ODEF) & BF).
  destruct (PW i Pi) as [Y|[Y|(q & m & Hin & Y)]].
  - unfold BIGSHADOW_LO, BIGSHADOW_HI, nsh in *. lia.
  - unfold BIGSHADOW_LO, BIGSHADOW_HI, nsh in *. lia.
  - destruct (BF q m (in_or_app _ _ _ (or_introl Hin))) as (_ & _ & _ & _ & Q5 & _). unfold BIGSHADOW_LO, BIGSHADOW_HI, nsh in *. lia.
Qed.

(* [comment removed for export] *)
Lemma mem_ok_piece HL LK cr Aw M model M1 (P : Z -> Prop) :
  ri_inv HI (HL ++ LB) FF LK cr Aw M (vml_of model) -> mem_ok M -> mem_grows M M1 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
  (forall a, P a -> (S - 14336 <= a < S) \/ (v <= a < v + 24) \/ (exists q m, In (q, m) HL /\ q <= a < q + m)) -> mem_ok M1.
Proof using All.
  intros HH MO MG FR PW. pose proof (pw_nsh HL LK cr Aw M model P HH MO PW) as PS.
  destruct (nfacts HL LK cr Aw M model HH MO) as ((A16 & SLO & SHI & SPT & C0) & (O1 & O2 & O5 & ODEF) & _).
  destruct MO as (EK & DK & STK & ACC & STKSH).
  split; [|split; [|split; [|split]]].
  - apply (L5SAR.ek_trans L ar LB FF S 14336 _ M0 M M1 EK). apply (L5SAR.ek_piece L ar LB FF S 14336 _ M M1 P FR). intros a Ha CA OW Pa.
    destruct (PW a Pa) as [X|[X|(q & m & Hin & X)]].
    + destruct (L5SAR.aclient_cases L ar C HI LYa HIok _ FF LK cr Aw M _ S 14336 a HH SPT (L5SAR.aclient_appb L ar LB HL FF S 14336 a CA)) as [(_ & Z2)|Z2]; [apply Z2; lia| lia].
    + apply (OW (v, 24)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia].
    + apply (PMARS1.own_not_aclient L ar C HI HIok HL LB FF LK cr Aw M _ q m a S 14336 HH Hin); [lia| exact CA].
  - apply (L5SAR.dk_trans L ar LB FF S 14336 M0 M M1 DK). apply L5SAR.dk_grows. exact MG.
  - exact (L5SAR.astk_grows ar M M1 S 14336 STK MG).
  - apply (PMFA.accA_agree M M1 v 24); [| exact ACC]. apply (agsh_piece M M1 P v 24 FR PS); lia.
  - apply (shz_agree M M1 (S - 14336) 1792); [apply PMKA.mod16_8'; replace (S - 14336) with (S + (-896) * 16) by lia; rewrite Z_mod_plus_full; exact A16| lia| | exact STKSH].
    apply (agsh_piece M M1 P _ _ FR PS); lia.
Qed.

(* [comment removed for export] *)
Lemma mem_ok_callee HL HL' LK cr Aw M model M' sp' scr' W' :
  ri_inv HI (HL ++ LB) FF LK cr Aw M (vml_of model) -> mem_ok M ->
  L5CA.ahpres L ar (HL' ++ LB) FF sp' scr' W' M M' -> S - 14336 <= sp' - scr' -> sp' <= S -> 0 <= scr' ->
  (forall rg, In rg W' -> exists q m, In (q, m) HL /\ q <= fst rg /\ fst rg + snd rg <= q + m) -> mem_ok M'.
Proof using All.
  intros HH MO HP H1 H2 H3 WIN. destruct (nfacts HL LK cr Aw M model HH MO) as ((A16 & SLO & SHI & SPT & C0) & (O1 & O2 & O5 & ODEF) & BF).
  destruct MO as (EK & DK & STK & ACC & STKSH).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & TOP & _).
  assert (WA : PMKA.wapp W').
  { intros rg Hrg. destruct (WIN rg Hrg) as (q & m & Hin & X1 & X2). destruct (BF q m (in_or_app _ _ _ (or_introl Hin))) as (Q0 & Q1 & Q2 & Q4 & Q5 & _).
    unfold BIGSHADOW_LO, BIGSHADOW_HI, nsh in *. lia. }
  pose proof HP as (EKc & _).
  split; [|split; [|split; [|split]]].
  - apply (L5SAR.ek_trans L ar LB FF S 14336 _ M0 M M' EK). apply (L5SAR.ek_callee L ar LB HL' FF [] S 14336 sp' scr' _ W' M M' HP H1 H2).
    intros a CA _ rg Hrg X. destruct (WIN rg Hrg) as (q & m & Hin & X1 & X2).
    apply (PMARS1.own_not_aclient L ar C HI HIok HL LB FF LK cr Aw M _ q m a S 14336 HH Hin); [unfold L5.in_rng in X; lia| exact CA].
  - apply (L5SAR.dk_trans L ar LB FF S 14336 M0 M M' DK). exact (L5SAR.dk_callee L ar LB HL' FF [] S 14336 sp' scr' W' M M' HP H1 H2).
  - apply (PMKA.astk_after_ahpres L ar _ FF M M' S 14336 sp' scr' W' STK HP); lia.
  - apply (PMFA.accA_agree M M' v 24); [| exact ACC]. apply (objsh_ek _ FF sp' scr' W' M M' v 24 EKc WA AO); lia.
  - apply (PMKA.stksh_keepA L ar _ FF sp' scr' W' M M' EKc WA (S - 14336) 1792); [lia| lia| lia| | lia| exact STKSH].
    apply PMKA.mod16_8'; replace (S - 14336) with (S + (-896) * 16) by lia; rewrite Z_mod_plus_full; exact A16.
Qed.

(* [comment removed for export] *)
Lemma cell_callee HL LK cr Aw M model M' HL' sp' scr' W' a val :
  ri_inv HI (HL ++ LB) FF LK cr Aw M (vml_of model) -> mem_ok M ->
  L5CA.ahpres L ar (HL' ++ LB) FF sp' scr' W' M M' -> S - 14336 <= sp' - scr' -> sp' <= S -> 0 <= scr' ->
  (forall rg, In rg W' -> exists q m, In (q, m) HL /\ q <= fst rg /\ fst rg + snd rg <= q + m) ->
  (sp' <= a /\ a + 8 <= S) \/ (v <= a /\ a + 8 <= v + 24) -> L5.u64_at RSEGS M a val -> L5.u64_at RSEGS M' a val.
Proof using All.
  intros HH MO (EKc & _) H1 H2 H3 WIN Ha X. destruct (nfacts HL LK cr Aw M model HH MO) as ((A16 & SLO & SHI & SPT & C0) & (O1 & O2 & O5 & ODEF) & BF).
  assert (OW : forall i, a <= i < a + 8 -> L5.outside W' i).
  { intros i Hi rg Hrg Y. destruct (WIN rg Hrg) as (q & m & Hin & X1 & X2). destruct (BF q m (in_or_app _ _ _ (or_introl Hin))) as (Q0 & Q1 & Q2 & Q4 & Q5 & Q6 & _).
    unfold L5.in_rng in Y. lia. }
  apply (L5C.u64_at_agree RSEGS M M'); [| lia| lia| exact X]. destruct Ha as [(Y1 & Y2)|(Y1 & Y2)].
  - intros i Hi. apply EKc. split; [lia|]. split; [| exact (OW i Hi)]. apply L5SAR.stack_client; lia.
  - exact (obj_ek _ FF sp' scr' W' M M' v 24 a 8 EKc AO V8 ltac:(lia) ltac:(lia) Y1 Y2 OW).
Qed.

(* [comment removed for export] *)
Lemma grow_credit (A : Z) b' n' :
  2 * PGV8.v8_cap x <= A -> 1 <= A <= 2 ^ 27 ->
  acredit_ok L cr0 A
  /\ PMSP.credit_keep cr0 (adebit L cr0 A) (PMSPA.scA L (PGV8.pot_v8 (PMSPA.HV L ar) x g)) (PMSPA.scA L (PGV8.pot_v8 (PMSPA.HV L ar) (PGV8.V8Blk b' n' A) (g + 1)))
  /\ PGV8.v8_ok (PGV8.V8Blk b' n' A) (g + 1).
Proof using All.
  intros HA HA1. destruct CRL0 as (CR1 & CR2).
  pose proof (PMA.ly_cost L C LY) as (HK & HL & HB).
  pose proof (PGV8.v8_ok_grow x g b' n' A OK0 HA HA1) as OK1.
  pose proof (PGV8.v8_ok_cap _ _ OK0) as (G0 & _). pose proof (PGV8.v8_ok_cap _ _ OK1) as (G1 & _).
  unfold PMSPA.scA, PGV8.pot_v8, PMSPA.HV, LibIfaceAB.heap_view in CR1, CR2 |- *.
  cbn [fst snd HeapIface.hl_k_per_malloc HeapIface.hl_b_overhead PGV8.v8_cap] in CR1, CR2 |- *. rewrite HK, HL, HB in *.
  change (2 ^ 21) with 2097152 in *. change (2 ^ 28) with 268435456 in *.
  split; [unfold acredit_ok; rewrite HK, HL, HB; change (2 ^ 21) with 2097152; cbn [fst snd]; split; clear - CR1 CR2 G1 HA HA1; Lia.lia|]. split; [|exact OK1].
  unfold PMSP.credit_keep, adebit. rewrite HK, HL, HB. change (2 ^ 21) with 2097152. cbn [fst snd]. split; clear - CR1 CR2 G1 HA HA1; Lia.lia.
Qed.

(* [comment removed for export] *)
Lemma finish (fx : FPState) R M model LK Aw x' g' cr' (pc : Z) (W : bv 32) :
  fetch_word RSEGS (Z_to_bv 64 pc) = Some W -> is_ecall W = false -> decode_any W = Some (Jalr 0 1 0, 4%Z) ->
  getr R (reg 1) = Z_to_bv 64 (U 1) -> getr R (reg 2) = Z_to_bv 64 S ->
  (forall i, In i [8; 9; 18; 19; 20; 21]%nat -> getr R (reg i) = Z_to_bv 64 (U i)) -> kept0 R ->
  stok model LK Aw -> mem_ok M -> ri_inv HI (PGV8.v8_own x' ++ LB) FF LK cr' Aw M (vml_of model) ->
  v8_atA M v x' -> PGV8.v8_size x' = PGV8.v8_size x + k -> PGV8.v8_ok x' g' -> PGV8.v8_cap x <= PGV8.v8_cap x' ->
  (PGV8.v8_size x' <= PGV8.v8_cap x -> PGV8.v8_own x' = PGV8.v8_own x /\ PGV8.v8_cap x' = PGV8.v8_cap x /\ g' = g) ->
  (PGV8.v8_cap x' = PGV8.v8_cap x \/ PGV8.v8_cap x' = Z.max (2 * PGV8.v8_cap x) (PGV8.v8_size x + k)) ->
  PMSP.credit_keep cr0 cr' (PMSPA.scA L (PGV8.pot_v8 (PMSPA.HV L ar) x g)) (PMSPA.scA L (PGV8.pot_v8 (PMSPA.HV L ar) x' g')) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R pc M model) K.
Proof using All.
  intros FW EW DW E1 E2 ES KP (AM & MRT & ILK & IAW) (EK & DK & STK & ACC & STKSH) HH VS SZ OK' CAPLE OWN CL CK.
  pose proof RAok as (Hr1 & Hr2).
  assert (RA : getr R (reg 1) = Z_to_bv 64 r) by (rewrite E1; unfold U; rewrite Z_to_bv_bv_unsigned; exact Rra0).
  unfold PMSP.cfg.
  apply (PMASK.ret_exit L ar C HI LY HIok fx R M model K _ FF LK cr' Aw pc r W HH AM FW EW DW RA ltac:(lia) Hr2).
  intros model1 MRT1 AM1 HH1.
  apply (KONT fx R M model1 LK Aw x' g' cr'); try assumption.
  - apply L5SAR.preserved_by_index. intros xr Hx. unfold L5SAR.cs_all in Hx.
    destruct Hx as [<-|Hx]; [rewrite E2, Rsp0; reflexivity|].
    destruct Hx as [<-|Hx]; [apply KP; cbn; auto|]. destruct Hx as [<-|Hx]; [apply KP; cbn; auto|].
    destruct Hx as [<-|Hx]; [rewrite (ES 8%nat) by (cbn; auto); unfold U; apply Z_to_bv_bv_unsigned|].
    destruct Hx as [<-|Hx]; [rewrite (ES 9%nat) by (cbn; auto); unfold U; apply Z_to_bv_bv_unsigned|].
    destruct Hx as [<-|Hx]; [rewrite (ES 18%nat) by (cbn; auto); unfold U; apply Z_to_bv_bv_unsigned|].
    destruct Hx as [<-|Hx]; [rewrite (ES 19%nat) by (cbn; auto); unfold U; apply Z_to_bv_bv_unsigned|].
    destruct Hx as [<-|Hx]; [rewrite (ES 20%nat) by (cbn; auto 10); unfold U; apply Z_to_bv_bv_unsigned|].
    destruct Hx as [<-|Hx]; [rewrite (ES 21%nat) by (cbn; auto 10); unfold U; apply Z_to_bv_bv_unsigned|].
    apply KP. cbn in Hx |- *. tauto.
  - change (PMSPA.pm_scr 1) with 14336. apply (L5SAR.ahpres_of L ar LB FF S 14336 _ M0 M); [exact EK| destruct STK as (_ & _ & _ & _ & D & _); exact D| exact DK].
  - eapply L5LZ.model_rt_trans; [exact MRT| exact MRT1].
Qed.

(* [comment removed for export] *)
Lemma wob HL LK cr Aw M model a : ri_inv HI (HL ++ LB) FF LK cr Aw M (vml_of model) -> mem_ok M ->
  (S - 14336 <= a < S) \/ (v <= a < v + 24) \/ (exists q m, In (q, m) HL /\ q <= a < q + m) ->
  aclientw L ar (HL ++ LB) FF 0 0 a /\ ~ (0x10000 <= a < 0x696000).
Proof using All.
  intros HH MO Ha. destruct (nfacts HL LK cr Aw M model HH MO) as ((A16 & SLO & SHI & SPT & C0) & (O1 & O2 & O5 & ODEF) & _).
  destruct Ha as [X|[X|(q & m & Hin & X)]].
  - split; [|lia]. unfold aclientw, aclient_g. right; left. split; [lia| lia].
  - split; [|lia]. unfold aclientw, aclient_g. right; right; right; left. destruct AO as (f & Hf & Y1 & Y2). exists f. split; [exact Hf|]. clear - X Y1 Y2. lia.
  - destruct (PNAEK.blk_facts L ar C HI LY HIok _ FF LK cr Aw M _ q m HH (in_or_app _ _ _ (or_introl Hin))) as (_ & _ & _ & _ & _ & IMG & _).
    split; [|lia]. unfold aclientw, aclient_g. left. exists (q, m). split; [apply in_or_app; left; exact Hin| cbn [fst snd]; lia].
Qed.

(* [comment removed for export] *)
Lemma piece_step (fx fx1 : FPState) R (pc : Z) R1 (pc1 : Z) HL M model cr LK Aw (M1v : word -> option byte) (P : Z -> Prop) :
  ri_inv HI (HL ++ LB) FF LK cr Aw M (vml_of model) -> stok model LK Aw -> mem_ok M ->
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) (mrestrict (ahid Aw model) M) (seg_rom RSEGS)) (@mkst fx1 R1 (Z_to_bv 64 pc1) M1v (seg_rom RSEGS)) ->
  mem_grows (mrestrict (ahid Aw model) M) M1v ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M1v (Z_to_bv 64 a) = mrestrict (ahid Aw model) M (Z_to_bv 64 a)) ->
  (forall a, P a -> (S - 14336 <= a < S) \/ (v <= a < v + 24) \/ (exists q m, In (q, m) HL /\ q <= a < q + m)) ->
  (forall M1 model1, ri_inv HI (HL ++ LB) FF LK cr Aw M1 (vml_of model1) -> stok model1 LK Aw -> mem_ok M1 ->
      (forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
      (forall a val, (S - 14336 <= a /\ a + 8 <= S) \/ (v <= a /\ a + 8 <= v + 24) -> L5.u64_at RSEGS M1v a val -> L5.u64_at RSEGS M1 a val) ->
      (forall a n, 0 <= a -> a + n <= 2 ^ 47 -> PMFA.agsh M M1 a n) ->
      srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 pc1 M1 model1) K) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R pc M model) K.
Proof using All.
  intros HH SO MO MS MG FZ PW KC. pose proof SO as (AM & MRT & ILK & IAW).
  destruct (nfacts HL LK cr Aw M model HH MO) as ((A16 & SLO & SHI & SPT & C0) & (O1 & O2 & O5 & ODEF) & _).
  destruct (vfacts HL LK cr Aw M model HH MO) as (_ & _ & _ & _ & _ & _ & _ & XAV).
  unfold PMSP.cfg.
  apply (L5SAR.apiece L ar C HI LYa HIok _ FF LK cr Aw M model fx fx1 R pc R1 pc1 M1v P K HH AM MS MG FZ).
  { intros a Ha Pa. exact (wob HL LK cr Aw M model a HH MO (PW a Pa)). }
  intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
  apply (KC M1 model1 HH1).
  - split; [exact AM1|]. split; [eapply L5LZ.model_rt_trans; [exact MRT| exact MRT1]|]. split; [exact ILK| exact IAW].
  - exact (mem_ok_piece HL LK cr Aw M model M1 P HH MO MGM1 FR1 PW).
  - exact FR1.
  - intros a val Ha X. apply (proj1 (L5A.u64_at_vis (ahid Aw model) M1 a val (XAV a 8 ltac:(lia)) ltac:(lia) ltac:(lia))). rewrite VIS1. exact X.
  - intros a n Ha Hn. exact (agsh_piece M M1 P a n FR1 (pw_nsh HL LK cr Aw M model P HH MO PW) Ha Hn).
Qed.

(* [comment removed for export] *)
Definition hdr (M : word -> option byte) (b e ce : Z) : Prop := L5.u64_at RSEGS M v b /\ L5.u64_at RSEGS M (v + 8) e /\ L5.u64_at RSEGS M (v + 16) ce.
Lemma saves_callee HL LK cr Aw M model M' HL' sp' scr' W' :
  ri_inv HI (HL ++ LB) FF LK cr Aw M (vml_of model) -> mem_ok M ->
  L5CA.ahpres L ar (HL' ++ LB) FF sp' scr' W' M M' -> S - 14336 <= sp' - scr' -> sp' <= S - 24 -> 0 <= scr' ->
  (forall rg, In rg W' -> exists q m, In (q, m) HL /\ q <= fst rg /\ fst rg + snd rg <= q + m) -> saves M -> saves M'.
Proof using All.
  intros HH MO HP H1 H2 H3 WIN (S8 & S16 & S24).
  repeat split; (eapply (cell_callee HL LK cr Aw M model M' HL' sp' scr' W' _ _ HH MO HP H1 ltac:(lia) H3 WIN); [left; lia| eassumption]).
Qed.
Lemma hdr_callee HL LK cr Aw M model M' HL' sp' scr' W' b e ce :
  ri_inv HI (HL ++ LB) FF LK cr Aw M (vml_of model) -> mem_ok M ->
  L5CA.ahpres L ar (HL' ++ LB) FF sp' scr' W' M M' -> S - 14336 <= sp' - scr' -> sp' <= S -> 0 <= scr' ->
  (forall rg, In rg W' -> exists q m, In (q, m) HL /\ q <= fst rg /\ fst rg + snd rg <= q + m) -> hdr M b e ce -> hdr M' b e ce.
Proof using All.
  intros HH MO HP H1 H2 H3 WIN (W0 & W8 & W16).
  repeat split; (eapply (cell_callee HL LK cr Aw M model M' HL' sp' scr' W' _ _ HH MO HP H1 H2 H3 WIN); [right; lia| eassumption]).
Qed.
Lemma cell_piece (M M1 : word -> option byte) (P : Z -> Prop) a val :
  (forall i, 0 <= i < 2 ^ 64 -> ~ P i -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i)) -> (forall i, a <= i < a + 8 -> ~ P i) -> 0 <= a -> a + 8 <= 2 ^ 64 ->
  L5.u64_at RSEGS M a val -> L5.u64_at RSEGS M1 a val.
Proof using All. intros FR NP H0 H1 X. apply (L5C.u64_at_agree RSEGS M M1); [intros i Hi; apply FR; [lia| apply NP; exact Hi]| exact H0| exact H1| exact X]. Qed.
Lemma saves_piece HL LK cr Aw M model (M1 : word -> option byte) (P : Z -> Prop) :
  ri_inv HI (HL ++ LB) FF LK cr Aw M (vml_of model) -> mem_ok M ->
  (forall i, 0 <= i < 2 ^ 64 -> ~ P i -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i)) -> (forall i, P i -> ~ (S - 24 <= i < S)) -> saves M -> saves M1.
Proof using All.
  intros HH MO FR NP (S8 & S16 & S24). destruct (nfacts HL LK cr Aw M model HH MO) as ((A16 & SLO & SHI & SPT & C0) & _).
  repeat split; (eapply (cell_piece M M1 P _ _ FR); [intros i Hi Pi; apply (NP i Pi); lia| lia| lia| eassumption]).
Qed.
Lemma hdr_piece HL LK cr Aw M model (M1 : word -> option byte) (P : Z -> Prop) b e ce :
  ri_inv HI (HL ++ LB) FF LK cr Aw M (vml_of model) -> mem_ok M ->
  (forall i, 0 <= i < 2 ^ 64 -> ~ P i -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i)) -> (forall i, P i -> ~ (v <= i < v + 24)) -> hdr M b e ce -> hdr M1 b e ce.
Proof using All.
  intros HH MO FR NP (W0 & W8 & W16). destruct (nfacts HL LK cr Aw M model HH MO) as ((A16 & SLO & SHI & SPT & C0) & (O1 & O2 & O5 & ODEF) & _).
  repeat split; (eapply (cell_piece M M1 P _ _ FR); [intros i Hi Pi; apply (NP i Pi); lia| lia| lia| eassumption]).
Qed.
(* [comment removed for export] *)
Lemma cstk HL LK cr Aw M model fr scr' : ri_inv HI (HL ++ LB) FF LK cr Aw M (vml_of model) -> mem_ok M -> 0 <= fr -> 0 <= scr' -> fr + scr' <= 14336 -> fr mod 16 = 0 -> scr' mod 8 = 0 ->
  L5CA.astk ar M (S - fr) scr' /\ shadow_zero M (S - fr - scr') (scr' / 8).
Proof using All.
  intros HH MO H1 H2 H3 H4 H5. destruct (nfacts HL LK cr Aw M model HH MO) as ((A16 & SLO & SHI & SPT & C0) & _). destruct MO as (_ & _ & STK & _ & STKSH).
  assert (E16 : (S - fr) mod 16 = 0).
  { rewrite Zminus_mod, A16, H4. reflexivity. }
  split; [exact (L5SAR.astk_sub ar M M S 14336 fr scr' STK (fun _ Y => Y) H1 H2 H3 E16)|].
  assert (M8a : (S - 14336) mod 8 = 0) by (apply PMKA.mod16_8'; replace (S - 14336) with (S + (-896) * 16) by lia; rewrite Z_mod_plus_full; exact A16).
  assert (M8b : (S - fr - scr') mod 8 = 0).
  { rewrite Zminus_mod, H5, (PMKA.mod16_8' _ E16). reflexivity. }
  pose proof (Z.div_mod scr' 8 ltac:(lia)) as D. rewrite H5 in D.
  apply (PMKA.shadow_zero_sub M (S - 14336) 1792 (S - fr - scr') (scr' / 8) M8a M8b); [lia| lia| apply Z.div_pos; lia| exact STKSH].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac pfeed XW XSZ XAV :=
  first [ assumption
        | lazymatch goal with
          | |- L5.u64_at _ (mrestrict ?H ?M) ?a ?val => apply (proj2 (L5A.u64_at_vis H M a val (XAV a 8 ltac:(lia)) ltac:(lia) ltac:(lia))); assumption
          | |- L5.writable _ _ _ _ => apply XW; lia
          | |- L5KA.zeros_at _ _ _ => apply XSZ; lia
          | |- PMAVGP.aligned _ _ => unfold PMAVGP.aligned; lia
          | |- _ => lia
          end ].


(* [comment removed for export] *)
Lemma centry0 (R : bvmap 5 word) HL LK cr Aw M model (fr X : Z) :
  ri_inv HI (HL ++ LB) FF LK cr Aw M (vml_of model) -> mem_ok M -> kept0 R ->
  getr R (reg 1) = Z_to_bv 64 X -> L5.ra_ok X -> getr R (reg 2) = Z_to_bv 64 (S - fr) -> 0 <= fr <= 2048 -> fr mod 16 = 0 ->
  PMSPA.entryA AD L ar R M (S - fr) X 0 /\ PMSPA.ffrsA FF (S - fr).
Proof using All.
  intros HH MO KP A1 RAX A2 Hfr F16.
  destruct (cstk HL LK cr Aw M model fr 12288 HH MO ltac:(lia) ltac:(lia) ltac:(lia) F16 ltac:(reflexivity)) as (STKc & SHc).
  split; [| intros f Hf; specialize (FRS f Hf); lia].
  unfold PMSPA.entryA. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact A1|]. split; [exact RAX|]. split; [exact A2|].
  split; [rewrite (KP 3%nat) by (cbn; tauto); exact Rgp0|]. split; [rewrite (KP 4%nat) by (cbn; tauto); exact Rtp0|].
  change (PMSPA.pm_scr 0) with 12288. change (12288 / 8) with 1536. split; [exact STKc| exact SHc].
Qed.

Lemma xr : match x with PGV8.V8Null => True | PGV8.V8Blk b n c => 0 <= n <= c /\ 1 <= c <= 2 ^ 27 /\ 4096 <= b /\ b mod 16 = 0 /\ b + c <= 2 ^ 47 end.
Proof using All.
  destruct x as [|b n c]; [exact I|]. destruct VS0 as (_ & _ & _ & _ & _ & Hn & Hc & Hb & Hb16 & _).
  pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH0 (b, c) ltac:(left; reflexivity)) as (Q0 & Q1). cbn [fst snd] in Q1.
  split; [exact Hn|]. split; [exact Hc|]. split; [exact Hb|]. split; [exact Hb16| exact Q1].
Qed.
Lemma xnum : 0 <= PGV8.v8_data x <= 2 ^ 47 /\ 0 <= PGV8.v8_size x <= PGV8.v8_cap x /\ PGV8.v8_cap x <= 2 ^ 27 /\ k <= 2 ^ 27 /\ PGV8.v8_size x + k <= 2 ^ 27
  /\ PGV8.v8_data x + PGV8.v8_cap x <= 2 ^ 47.
Proof using All.
  pose proof xr as XR. unfold PGV8.v8_grow_ok in GROK. destruct x as [|b n c]; cbn [PGV8.v8_data PGV8.v8_size PGV8.v8_cap] in *; lia.
Qed.

(* [comment removed for export] *)
Definition post_ok (x' : PGV8.v8) (g' : Z) (cr' : credit) : Prop :=
  PGV8.v8_size x' = PGV8.v8_size x + k /\ PGV8.v8_ok x' g' /\ PGV8.v8_cap x <= PGV8.v8_cap x'
  /\ (PGV8.v8_size x' <= PGV8.v8_cap x -> PGV8.v8_own x' = PGV8.v8_own x /\ PGV8.v8_cap x' = PGV8.v8_cap x /\ g' = g)
  /\ (PGV8.v8_cap x' = PGV8.v8_cap x \/ PGV8.v8_cap x' = Z.max (2 * PGV8.v8_cap x) (PGV8.v8_size x + k))
  /\ PMSP.credit_keep cr0 cr' (PMSPA.scA L (PGV8.pot_v8 (PMSPA.HV L ar) x g)) (PMSPA.scA L (PGV8.pot_v8 (PMSPA.HV L ar) x' g')).
Lemma finish_p (fx : FPState) R M model LK Aw x' g' cr' (pc : Z) (W : bv 32) :
  fetch_word RSEGS (Z_to_bv 64 pc) = Some W -> is_ecall W = false -> decode_any W = Some (Jalr 0 1 0, 4%Z) ->
  getr R (reg 1) = Z_to_bv 64 (U 1) -> getr R (reg 2) = Z_to_bv 64 S ->
  (forall i, In i [8; 9; 18; 19; 20; 21]%nat -> getr R (reg i) = Z_to_bv 64 (U i)) -> kept0 R ->
  stok model LK Aw -> mem_ok M -> ri_inv HI (PGV8.v8_own x' ++ LB) FF LK cr' Aw M (vml_of model) -> v8_atA M v x' -> post_ok x' g' cr' ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R pc M model) K.
Proof using All.
  intros FW EW DW E1 E2 ES KP SO MO HH VS (P1 & P2 & P3 & P4 & P5 & P6).
  exact (finish fx R M model LK Aw x' g' cr' pc W FW EW DW E1 E2 ES KP SO MO HH VS P1 P2 P3 P4 P5 P6).
Qed.

Definition gbuf (M : word -> option byte) (p1 p2 p3 p4 : Z) : Prop :=
  L5.u64_at RSEGS M (S - 64) p1 /\ L5.u64_at RSEGS M (S - 56) p2 /\ L5.u64_at RSEGS M (S - 48) p3 /\ L5.u64_at RSEGS M (S - 40) p4.
Definition gtail : Prop := forall (fx : FPState) R M model LK Aw cr B A g',
  getr R (reg 1) = Z_to_bv 64 743616 -> getr R (reg 2) = Z_to_bv 64 (S - 64) -> getr R (reg 8) = Z_to_bv 64 v ->
  getr R (reg 9) = Z_to_bv 64 k -> getr R (reg 10) = Z_to_bv 64 v -> getr R (reg 11) = Z_to_bv 64 (S - 64) ->
  (forall i, In i [18; 19; 20; 21]%nat -> getr R (reg i) = Z_to_bv 64 (U i)) -> kept0 R ->
  stok model LK Aw -> mem_ok M -> saves M -> L5.u64_at RSEGS M (S - 32) v ->
  ri_inv HI (((B, A) :: PGV8.v8_own x) ++ LB) FF LK cr Aw M (vml_of model) -> v8_atA M v x ->
  gbuf M B (B + PGV8.v8_size x) ((B + PGV8.v8_size x) + k) (B + A) ->
  A <= 2 ^ 27 -> PGV8.v8_size x + k <= A -> shadow_blk M B A ->
  post_ok (PGV8.V8Blk B (PGV8.v8_size x + k) A) g' cr ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0xb5cb8 M model) K.

(* [comment removed for export] *)
Lemma piece_ro (fx fx1 : FPState) R (pc : Z) R1 (pc1 : Z) HL M model cr LK Aw (M1v : word -> option byte) :
  ri_inv HI (HL ++ LB) FF LK cr Aw M (vml_of model) -> stok model LK Aw -> mem_ok M ->
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) (mrestrict (ahid Aw model) M) (seg_rom RSEGS)) (@mkst fx1 R1 (Z_to_bv 64 pc1) M1v (seg_rom RSEGS)) ->
  mem_grows (mrestrict (ahid Aw model) M) M1v ->
  (forall a, 0 <= a < 2 ^ 64 -> M1v (Z_to_bv 64 a) = mrestrict (ahid Aw model) M (Z_to_bv 64 a)) ->
  (forall model1, ri_inv HI (HL ++ LB) FF LK cr Aw M (vml_of model1) -> stok model1 LK Aw ->
      srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 pc1 M model1) K) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R pc M model) K.
Proof using All.
  intros HH SO MO MS MG FZ KC.
  apply (piece_step fx fx1 R pc R1 pc1 HL M model cr LK Aw M1v (fun _ => False) HH SO MO MS MG (fun a Ha _ => FZ a Ha)); [intros a []|].
  intros M1 model1 HH1 SO1 MO1 FR1 VUP AGS.
  assert (EQ1 : M1 = M).
  { apply functional_extensionality. intros a. pose proof (FR1 (bv_unsigned a) (bv_unsigned_in_range _ a) (fun X => X)) as E. rewrite Z_to_bv_bv_unsigned in E. exact E. }
  subst M1. exact (KC model1 HH1 SO1).
Qed.

(* [comment removed for export] *)
Lemma v8_at_agree (M M' : word -> option byte) (y : PGV8.v8) :
  v8_atA M v y -> L5.defined M' v 24 -> L5C.agree_on M M' v 24 -> PMFA.agsh M M' v 24 -> 0 <= v -> v + 24 <= 2 ^ 47 ->
  (forall b n c, y = PGV8.V8Blk b n c -> L5.defined M' b c /\ PMFA.agsh M M' b c) -> v8_atA M' v y.
Proof using All.
  intros (VD & VC & VR) VD' AG AGS H0 H1 BLK. split; [exact VD'|]. split; [exact (PMFA.accA_agree M M' v 24 AGS VC)|].
  assert (KEEP : forall a val, v <= a -> a + 8 <= v + 24 -> L5.u64_at RSEGS M a val -> L5.u64_at RSEGS M' a val).
  { intros a val X1 X2 X. apply (L5C.u64_at_agree RSEGS M M'); [intros i Hi; apply AG; lia| lia| lia| exact X]. }
  destruct y as [|b n c].
  - destruct VR as (U0 & U8 & U16). split; [apply KEEP; [lia| lia| exact U0]|]. split; [apply KEEP; [lia| lia| exact U8]| apply KEEP; [lia| lia| exact U16]].
  - destruct VR as (U0 & U8 & U16 & Hn & Hc & Hb & Hb16 & BD & BA & BN). destruct (BLK b n c eq_refl) as (BD' & AGB).
    split; [apply KEEP; [lia| lia| exact U0]|]. split; [apply KEEP; [lia| lia| exact U8]|]. split; [apply KEEP; [lia| lia| exact U16]|].
    split; [exact Hn|]. split; [exact Hc|]. split; [exact Hb|]. split; [exact Hb16|]. split; [exact BD'|].
    split; [apply (PMFA.accA_agree M M' b n); [intros y Hy; apply AGB; lia| exact BA]|].
    apply (PGV8KA.annA_agree M M' b n c); [lia| apply PMKA.mod16_8'; exact Hb16| exact AGB| exact BN].
Qed.

Lemma v8_case (y : PGV8.v8) : y = PGV8.V8Null \/ exists b n c, y = PGV8.V8Blk b n c.
Proof using All. destruct y as [|b n c]; [left; reflexivity| right; exists b, n, c; reflexivity]. Qed.

End Call.

End WithHeap.
End PGVAPK.
