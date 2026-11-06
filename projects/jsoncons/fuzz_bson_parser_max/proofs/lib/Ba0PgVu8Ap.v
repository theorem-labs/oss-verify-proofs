(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
Require OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib.LeanFeed.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality Permutation.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceABx IcptIfaceA
     L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA L5DefsA L5CoreA L5StepAR PmLayout PnLayoutA PmModel PmModelFacts PmStatics PmStaticsA PmSpecs PmParSpecs PmTxtSpecs PmSpecsA PmSpecsAX PnSpecsAa
     PmModelFactsA PnStepA PmStep PnASrcKit PnASrcReadK PnAReset1 PnAEmbKit PnAVu8Dtor PnAVu8GrowP Ba0_code_b404c_b4050 PgSrc PgSrcA PgV8 PgV8A PgV8KitA PnLayout PnRunA PnSpecsAX PnSpecsAX8.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PGVAPA.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := Asan.M.loaded_segments.
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
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0x778cc M model) K.
Proof.
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

Lemma memset_call27 (fx : FPState) R M model K LB FF LK cr Aw (sp' r dst c n : Z) :
  ri_inv HI LB FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] ->
  getr R (reg 1) = Z_to_bv 64 r -> L5.ra_ok r -> getr R (reg 2) = Z_to_bv 64 sp' -> getr R (reg 4) = Z_to_bv 64 (hl_tp L) ->
  getr R (reg 10) = Z_to_bv 64 dst -> getr R (reg 11) = Z_to_bv 64 c -> getr R (reg 12) = Z_to_bv 64 n -> 0 <= n <= 2 ^ 27 ->
  L5CA.astk ar M sp' 2560 ->
  aacc M dst n -> (forall i, 0 <= i < n -> aclientw L ar LB FF sp' 2560 (dst + i)) -> L5.defined M dst n -> 0 <= dst -> dst + n <= 2 ^ 47 -> app_rng ar dst n ->
  (forall (fx' : FPState) R' M' model', regs_preserved R R' -> L5.defined M' dst n ->
      L5CA.ahpres L ar LB FF sp' 2560 [(dst, n)] M M' ->
      model_rt model model' -> L5CA.amodel_ok Aw model' -> ri_inv HI LB FF LK cr Aw M' (vml_of model') ->
      srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx' R' r M' model') K) ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0x77d68 M model) K.
Proof.
  intros HH AM HK G1 RA G2 G4 G10 G11 G12 Hn ASTK ACD CLD DDEF D0 D1 APD KONT.
  pose proof (HAJ.aior_memset _ _ _ _ _ HIok) as HF.
  unfold amemset_spec, amem_pre, amem_post in HF. rewrite (L5A.aly_segs L C LYa), (L5A.aly_scr_mem L C LYa), (L5A.aly_memset L C LYa) in HF.
  pose proof ASTK as (A16 & SLO & SHI & SPT & SD & SU).
  assert (U2 : bv_unsigned (getr R 2%bv) = sp') by (rewrite L5K.rl2, G2; apply L5.unsigned_lit; clear - SLO SHI SPT; lia).
  unfold PMSPA.cfg.
  apply (HF fx R M model LB FF LK cr Aw dst c n K); clear HF.
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
Proof.
  intros EK WA Hin H0 H1 x Hx. pose proof (PMKA.S_in_shadow x ltac:(lia)) as SX.
  apply EK. split; [unfold BIGSHADOW_LO, BIGSHADOW_HI in SX; lia|]. split; [| exact (PMKA.wapp_outside_shadow W' (S x) WA SX)].
  unfold aclient, aclient_g. do 6 right. exists (q, m). split; [exact Hin|]. cbn [fst snd]. unfold in_shadow_of. split; apply PMKA.S_mono; lia.
Qed.
(* [comment removed for export] *)
Lemma objsh_ek LBc FF sp' scr' W' M M' o n :
  L5SAR.ek L ar LBc FF sp' scr' W' M M' -> PMKA.wapp W' -> PMSPA.aobjA FF o n -> 0 <= o -> o + n <= 2 ^ 47 -> PMFA.agsh M M' o n.
Proof.
  intros EK WA AO H0 H1 x Hx. pose proof (PMKA.S_in_shadow x ltac:(lia)) as SX.
  apply EK. split; [unfold BIGSHADOW_LO, BIGSHADOW_HI in SX; lia|]. split; [| exact (PMKA.wapp_outside_shadow W' (S x) WA SX)].
  exact (PNAEK.frame_sh_client L ar FF o n x LBc sp' scr' AO Hx).
Qed.
(* [comment removed for export] *)
Lemma obj_ek LBc FF sp' scr' W' M M' o n a m :
  L5SAR.ek L ar LBc FF sp' scr' W' M M' -> PMSPA.aobjA FF o n -> o mod 8 = 0 -> 0 <= o -> o + n <= 2 ^ 47 -> o <= a -> a + m <= o + n ->
  (forall i, a <= i < a + m -> L5.outside W' i) -> L5C.agree_on M M' a m.
Proof.
  intros EK AO O8 H0 H1 H2 H3 OW i Hi. apply EK. split; [lia|]. split; [| apply OW; exact Hi].
  apply (L5SAR.obj_client L ar LBc FF sp' scr' o n i (PMKA.aobj_of_aobjA FF o n AO O8)). lia.
Qed.
(* [comment removed for export] *)
Lemma shz_agree (M M' : word -> option byte) lo g : lo mod 8 = 0 -> 0 <= g -> PMFA.agsh M M' lo (8 * g) -> shadow_zero M lo g -> shadow_zero M' lo g.
Proof.
  intros L8 Hg AG SZ j Hj. pose proof (SZ j Hj) as Z1. unfold byte_at in *. rewrite (PMFA.S_granule lo j L8 ltac:(lia)) in *.
  rewrite (AG (lo + 8 * j) ltac:(lia)). exact Z1.
Qed.
Lemma shblk_agree (M M' : word -> option byte) b c : b mod 8 = 0 -> 0 <= c -> PMFA.agsh M M' b c -> shadow_blk M b c -> shadow_blk M' b c.
Proof.
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
Proof.
  intros FR PS H0 H1 x Hx. pose proof (PMKA.S_in_shadow x ltac:(lia)) as SX. apply FR; [unfold BIGSHADOW_LO, BIGSHADOW_HI in SX; lia|].
  intros X. exact (PS _ X SX).
Qed.
Lemma aacc_sub (M : word -> option byte) a n a' n' : aacc M a n -> a <= a' -> a' + n' <= a + n -> aacc M a' n'.
Proof. intros AC H1 H2 y Hy. apply AC. clear - H1 H2 Hy. lia. Qed.

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

Definition U (i : nat) : Z := bv_unsigned (getr R0 (reg i)).
(* [comment removed for export] *)
Definition saves (M : word -> option byte) : Prop :=
  L5.u64_at RSEGS M (S - 8) (U 1) /\ L5.u64_at RSEGS M (S - 16) (U 8) /\ L5.u64_at RSEGS M (S - 24) (U 9) /\ L5.u64_at RSEGS M (S - 32) (U 18)
  /\ L5.u64_at RSEGS M (S - 40) (U 19) /\ L5.u64_at RSEGS M (S - 48) (U 20).
(* [comment removed for export] *)
Definition kept0 (R : bvmap 5 word) : Prop := forall i, In i [3; 4; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R (reg i) = getr R0 (reg i).
Definition stok (model : Model) (LK : list fframe) (Aw : list (Z * Z)) : Prop :=
  L5CA.amodel_ok Aw model /\ model_rt model0 model /\ incl LK LK0 /\ incl Aw0 Aw.
(* [comment removed for export] *)
Definition mem_ok (M : word -> option byte) : Prop :=
  L5SAR.ek L ar LB FF S 14336 [(v, 24)] M0 M /\ L5SAR.dk L ar LB FF S 14336 M0 M /\ L5CA.astk ar M S 14336 /\ PMSPA.accA M v 24
  /\ shadow_zero M (S - 14336) 1792.

Lemma kept0_of (R R1 : bvmap 5 word) : kept0 R -> (forall i, In i [3; 4; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R1 (reg i) = getr R (reg i)) -> kept0 R1.
Proof. intros KP H i Hi. rewrite (H i Hi). exact (KP i Hi). Qed.
Lemma kept0_pres (R R1 : bvmap 5 word) : kept0 R -> regs_preserved R R1 -> kept0 R1.
Proof.
  intros KP RP. apply (kept0_of R R1 KP). intros i Hi. apply (L5SAR.cs_of_preserved R R1 i RP). unfold L5SAR.cs_all. cbn in Hi |- *. tauto.
Qed.
Lemma stok_step model LK Aw model1 LK1 Aw1 : stok model LK Aw -> L5CA.amodel_ok Aw1 model1 -> model_rt model model1 -> incl LK1 LK -> incl Aw Aw1 -> stok model1 LK1 Aw1.
Proof.
  intros (A1 & A2 & A3 & A4) B1 B2 B3 B4. split; [exact B1|]. split; [eapply L5LZ.model_rt_trans; [exact A2| exact B2]|].
  split; [intros f Hf; apply A3; apply B3; exact Hf| intros q Hq; apply B4; apply A4; exact Hq].
Qed.

(* [comment removed for export] *)
Lemma nfacts HL LK cr Aw M model : ri_inv HI (HL ++ LB) FF LK cr Aw M (vml_of model) -> mem_ok M ->
  (S mod 16 = 0 /\ ahl_ceil ar + 4096 + 14336 <= S /\ S <= ar_sptop ar /\ 140735340871680 <= ar_sptop ar <= 2 ^ 47 /\ 0 <= ahl_ceil ar)
  /\ (6897664 <= v /\ v + 24 <= ahl_ceil ar /\ nsh v 24 /\ L5.defined M v 24)
  /\ (forall q m, In (q, m) (HL ++ LB) -> 4096 <= q /\ 0 < m /\ q + m <= ahl_ceil ar /\ q mod 16 = 0 /\ nsh q m /\ (q + m <= v \/ v + 24 <= q) /\ L5.defined M q m).
Proof.
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
  L5.img_clear (mrestrict (ahid Aw model) M) 1236992 1269760 /\ L5.u64_at RSEGS (mrestrict (ahid Aw model) M) 1300408 2147450880
  /\ L5.u32_at RSEGS (mrestrict (ahid Aw model) M) 1300416 1
  /\ (forall a n, S - 14336 <= a -> a + n <= S -> 0 <= n -> L5.writable RSEGS (mrestrict (ahid Aw model) M) a n)
  /\ L5KA.zeros_at (mrestrict (ahid Aw model) M) (v / 8 + 2147450880) 3 /\ L5.writable RSEGS (mrestrict (ahid Aw model) M) v 24
  /\ (forall a n, S - 14336 <= a -> a + 8 * n <= S -> a mod 8 = 0 -> 0 <= n -> L5KA.zeros_at (mrestrict (ahid Aw model) M) (a / 8 + 2147450880) n)
  /\ (forall a n, (S - 14336 <= a /\ a + n <= 2 ^ 47) \/ (v <= a /\ a + n <= v + 24) -> L5A.avis (ahid Aw model) a n).
Proof.
  intros HH MO. destruct (nfacts HL LK cr Aw M model HH MO) as ((A16 & SLO & SHI & SPT & C0) & (O1 & O2 & O5 & ODEF) & _).
  destruct MO as (_ & _ & STK & ACC & STKSH).
  pose proof (HAJ.aior_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as ST. rewrite (L5A.aly_segs L C LYa) in ST.
  pose proof (L5A.statics_facts L C M LYa ST) as (GOT & CSB & CUAR & _).
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ FF LK cr Aw M model HH) as (HOFF & VIS & VIMG & _ & _ & _ & _ & VSTSH).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LK cr Aw M model v 24 S 14336 HH (PMKA.aobj_of_aobjA FF v 24 AO V8) ltac:(lia) ltac:(reflexivity))
    as (_ & _ & _ & OVIS & _).
  set (H := ahid Aw model) in *.
  split; [apply L5A.img_clear_mrestrict; exact GOT|].
  split; [apply (proj2 (L5A.u64_at_vis H M 1300408 2147450880 (VIMG 1300408 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CSB|].
  split; [apply (proj2 (L5A.u32_at_vis H M 1300416 1 (VIMG 1300416 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CUAR|].
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

(* [comment removed for export] *)
Lemma mem_ok_piece HL LK cr Aw M model M1 (P : Z -> Prop) :
  ri_inv HI (HL ++ LB) FF LK cr Aw M (vml_of model) -> mem_ok M -> mem_grows M M1 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
  (forall a, P a -> (S - 14336 <= a < S) \/ (v <= a < v + 24)) -> mem_ok M1.
Proof.
  intros HH MO MG FR PW. destruct (nfacts HL LK cr Aw M model HH MO) as ((A16 & SLO & SHI & SPT & C0) & (O1 & O2 & O5 & ODEF) & _).
  destruct MO as (EK & DK & STK & ACC & STKSH).
  assert (PS : forall i, P i -> ~ (BIGSHADOW_LO <= i < BIGSHADOW_HI)).
  { intros i Pi X. unfold BIGSHADOW_LO, BIGSHADOW_HI, nsh in *. destruct (PW i Pi); lia. }
  split; [|split; [|split; [|split]]].
  - apply (L5SAR.ek_trans L ar LB FF S 14336 _ M0 M M1 EK). apply (L5SAR.ek_piece L ar LB FF S 14336 _ M M1 P FR). intros a Ha CA OW Pa.
    destruct (PW a Pa) as [X|X].
    + destruct (L5SAR.aclient_cases L ar C HI LYa HIok _ FF LK cr Aw M _ S 14336 a HH SPT (L5SAR.aclient_appb L ar LB HL FF S 14336 a CA)) as [(_ & Z2)|Z2]; [apply Z2; lia| lia].
    + apply (OW (v, 24)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia].
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
Proof.
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
Proof.
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
Lemma finish (fx : FPState) R M model LK Aw x' g' cr' :
  getr R (reg 1) = Z_to_bv 64 (U 1) -> getr R (reg 2) = Z_to_bv 64 S ->
  (forall i, In i [8; 9; 18; 19; 20]%nat -> getr R (reg i) = Z_to_bv 64 (U i)) -> kept0 R ->
  stok model LK Aw -> mem_ok M -> ri_inv HI (PGV8.v8_own x' ++ LB) FF LK cr' Aw M (vml_of model) ->
  v8_atA M v x' -> PGV8.v8_size x' = PGV8.v8_size x + k -> PGV8.v8_ok x' g' -> PGV8.v8_cap x <= PGV8.v8_cap x' ->
  (PGV8.v8_size x' <= PGV8.v8_cap x -> PGV8.v8_own x' = PGV8.v8_own x /\ PGV8.v8_cap x' = PGV8.v8_cap x /\ g' = g) ->
  (PGV8.v8_cap x' = PGV8.v8_cap x \/ PGV8.v8_cap x' = Z.max (2 * PGV8.v8_cap x) (PGV8.v8_size x + k)) ->
  PMSP.credit_keep cr0 cr' (PMSPA.scA L (PGV8.pot_v8 (PMSPA.HV L ar) x g)) (PMSPA.scA L (PGV8.pot_v8 (PMSPA.HV L ar) x' g')) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0xb409c M model) K.
Proof using All.
  intros E1 E2 ES KP (AM & MRT & ILK & IAW) (EK & DK & STK & ACC & STKSH) HH VS SZ OK' CAPLE OWN CL CK.
  pose proof RAok as (Hr1 & Hr2).
  assert (RA : getr R (reg 1) = Z_to_bv 64 r) by (rewrite E1; unfold U; rewrite Z_to_bv_bv_unsigned; exact Rra0).
  unfold PMSP.cfg.
  apply (PMASK.ret_exit L ar C HI LY HIok fx R M model K _ FF LK cr' Aw 0xb409c r W_b404c HH AM F_b404c eq_refl D_b404c RA ltac:(lia) Hr2).
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
    apply KP. cbn in Hx |- *. tauto.
  - change (PMSPA.pm_scr 1) with 14336. apply (L5SAR.ahpres_of L ar LB FF S 14336 _ M0 M); [exact EK| destruct STK as (_ & _ & _ & _ & D & _); exact D| exact DK].
  - eapply L5LZ.model_rt_trans; [exact MRT| exact MRT1].
Qed.

(* [comment removed for export] *)
Lemma wob HL LK cr Aw M model a : ri_inv HI (HL ++ LB) FF LK cr Aw M (vml_of model) -> mem_ok M ->
  (S - 14336 <= a < S) \/ (v <= a < v + 24) -> aclientw L ar (HL ++ LB) FF 0 0 a /\ ~ (0x10000 <= a < 0x694000).
Proof.
  intros HH MO Ha. destruct (nfacts HL LK cr Aw M model HH MO) as ((A16 & SLO & SHI & SPT & C0) & (O1 & O2 & O5 & ODEF) & _).
  split; [|lia]. unfold aclientw, aclient_g. destruct Ha as [X|X].
  - right; left. split; [lia| lia].
  - right; right; right; left. destruct AO as (f & Hf & Y1 & Y2). exists f. split; [exact Hf|]. clear - X Y1 Y2. lia.
Qed.

(* [comment removed for export] *)
Lemma piece_step (fx fx1 : FPState) R (pc : Z) R1 (pc1 : Z) HL M model cr LK Aw (M1v : word -> option byte) (P : Z -> Prop) :
  ri_inv HI (HL ++ LB) FF LK cr Aw M (vml_of model) -> stok model LK Aw -> mem_ok M ->
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) (mrestrict (ahid Aw model) M) (seg_rom RSEGS)) (@mkst fx1 R1 (Z_to_bv 64 pc1) M1v (seg_rom RSEGS)) ->
  mem_grows (mrestrict (ahid Aw model) M) M1v ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M1v (Z_to_bv 64 a) = mrestrict (ahid Aw model) M (Z_to_bv 64 a)) ->
  (forall a, P a -> (S - 14336 <= a < S) \/ (v <= a < v + 24)) ->
  (forall M1 model1, ri_inv HI (HL ++ LB) FF LK cr Aw M1 (vml_of model1) -> stok model1 LK Aw -> mem_ok M1 ->
      (forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
      (forall a val, (S - 14336 <= a /\ a + 8 <= S) \/ (v <= a /\ a + 8 <= v + 24) -> L5.u64_at RSEGS M1v a val -> L5.u64_at RSEGS M1 a val) ->
      (forall a n, 0 <= a -> a + n <= 2 ^ 47 -> PMFA.agsh M M1 a n) ->
      srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 pc1 M1 model1) K) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R pc M model) K.
Proof.
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
  - intros a n Ha Hn. apply (agsh_piece M M1 P a n FR1); [| exact Ha| exact Hn].
    intros i Pi X. unfold BIGSHADOW_LO, BIGSHADOW_HI, nsh in *. destruct (PW i Pi); lia.
Qed.

(* [comment removed for export] *)
Definition hdr (M : word -> option byte) (b e ce : Z) : Prop := L5.u64_at RSEGS M v b /\ L5.u64_at RSEGS M (v + 8) e /\ L5.u64_at RSEGS M (v + 16) ce.
Lemma saves_callee HL LK cr Aw M model M' HL' sp' scr' W' :
  ri_inv HI (HL ++ LB) FF LK cr Aw M (vml_of model) -> mem_ok M ->
  L5CA.ahpres L ar (HL' ++ LB) FF sp' scr' W' M M' -> S - 14336 <= sp' - scr' -> sp' <= S - 48 -> 0 <= scr' ->
  (forall rg, In rg W' -> exists q m, In (q, m) HL /\ q <= fst rg /\ fst rg + snd rg <= q + m) -> saves M -> saves M'.
Proof.
  intros HH MO HP H1 H2 H3 WIN (S8 & S16 & S24 & S32 & S40 & S48).
  repeat split; (eapply (cell_callee HL LK cr Aw M model M' HL' sp' scr' W' _ _ HH MO HP H1 ltac:(lia) H3 WIN); [left; lia| eassumption]).
Qed.
Lemma hdr_callee HL LK cr Aw M model M' HL' sp' scr' W' b e ce :
  ri_inv HI (HL ++ LB) FF LK cr Aw M (vml_of model) -> mem_ok M ->
  L5CA.ahpres L ar (HL' ++ LB) FF sp' scr' W' M M' -> S - 14336 <= sp' - scr' -> sp' <= S -> 0 <= scr' ->
  (forall rg, In rg W' -> exists q m, In (q, m) HL /\ q <= fst rg /\ fst rg + snd rg <= q + m) -> hdr M b e ce -> hdr M' b e ce.
Proof.
  intros HH MO HP H1 H2 H3 WIN (W0 & W8 & W16).
  repeat split; (eapply (cell_callee HL LK cr Aw M model M' HL' sp' scr' W' _ _ HH MO HP H1 H2 H3 WIN); [right; lia| eassumption]).
Qed.
Lemma cell_piece (M M1 : word -> option byte) (P : Z -> Prop) a val :
  (forall i, 0 <= i < 2 ^ 64 -> ~ P i -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i)) -> (forall i, a <= i < a + 8 -> ~ P i) -> 0 <= a -> a + 8 <= 2 ^ 64 ->
  L5.u64_at RSEGS M a val -> L5.u64_at RSEGS M1 a val.
Proof. intros FR NP H0 H1 X. apply (L5C.u64_at_agree RSEGS M M1); [intros i Hi; apply FR; [lia| apply NP; exact Hi]| exact H0| exact H1| exact X]. Qed.
Lemma saves_piece HL LK cr Aw M model (M1 : word -> option byte) (P : Z -> Prop) :
  ri_inv HI (HL ++ LB) FF LK cr Aw M (vml_of model) -> mem_ok M ->
  (forall i, 0 <= i < 2 ^ 64 -> ~ P i -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i)) -> (forall i, P i -> ~ (S - 48 <= i < S)) -> saves M -> saves M1.
Proof.
  intros HH MO FR NP (S8 & S16 & S24 & S32 & S40 & S48). destruct (nfacts HL LK cr Aw M model HH MO) as ((A16 & SLO & SHI & SPT & C0) & _).
  repeat split; (eapply (cell_piece M M1 P _ _ FR); [intros i Hi Pi; apply (NP i Pi); lia| lia| lia| eassumption]).
Qed.
Lemma hdr_piece HL LK cr Aw M model (M1 : word -> option byte) (P : Z -> Prop) b e ce :
  ri_inv HI (HL ++ LB) FF LK cr Aw M (vml_of model) -> mem_ok M ->
  (forall i, 0 <= i < 2 ^ 64 -> ~ P i -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i)) -> (forall i, P i -> ~ (v <= i < v + 24)) -> hdr M b e ce -> hdr M1 b e ce.
Proof.
  intros HH MO FR NP (W0 & W8 & W16). destruct (nfacts HL LK cr Aw M model HH MO) as ((A16 & SLO & SHI & SPT & C0) & (O1 & O2 & O5 & ODEF) & _).
  repeat split; (eapply (cell_piece M M1 P _ _ FR); [intros i Hi Pi; apply (NP i Pi); lia| lia| lia| eassumption]).
Qed.
(* [comment removed for export] *)
Lemma cstk HL LK cr Aw M model fr scr' : ri_inv HI (HL ++ LB) FF LK cr Aw M (vml_of model) -> mem_ok M -> 0 <= fr -> 0 <= scr' -> fr + scr' <= 14336 -> fr mod 16 = 0 -> scr' mod 8 = 0 ->
  L5CA.astk ar M (S - fr) scr' /\ shadow_zero M (S - fr - scr') (scr' / 8).
Proof.
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
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ip_C (fx : FPState) R M model LK Aw b n c :
  x = PGV8.V8Blk b n c -> n + k <= c ->
  getr R (reg 2) = Z_to_bv 64 (S - 96) -> getr R (reg 8) = Z_to_bv 64 ((b + n) + k) -> getr R (reg 9) = Z_to_bv 64 k -> getr R (reg 18) = Z_to_bv 64 (v + 8) ->
  getr R (reg 20) = Z_to_bv 64 ((v + 8) / 8 + 2147450880) -> kept0 R ->
  stok model LK Aw -> mem_ok M -> saves M -> ri_inv HI ([(b, c)] ++ LB) FF LK cr0 Aw M (vml_of model) ->
  L5.u64_at RSEGS M v b -> L5.u64_at RSEGS M (v + 8) (b + n) -> L5.u64_at RSEGS M (v + 16) (b + c) ->
  0 <= n <= c -> 1 <= c <= 2 ^ 27 -> 4096 <= b -> b mod 16 = 0 ->
  PMSPA.accA M b (n + k) -> PGV8A.annA M b (n + k) c ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0xb400c M model) K.
Proof using All.
  intros EX Hnk E2 E8 E9 E18 E20 KP SO MO SV HH W0 W8 W16 Hn Hc Hb Hb16 ACB ANB.
  destruct (nfacts _ LK cr0 Aw M model HH MO) as ((A16 & SLO & SHI & SPT & C0) & (O1 & O2 & O5 & ODEF) & BF).
  destruct (BF b c ltac:(left; reflexivity)) as (Q0 & Q1 & Q2 & Q4 & Q5 & Q6 & QD). unfold nsh in O5, Q5.
  destruct (vfacts _ LK cr0 Aw M model HH MO) as (X0 & X1 & X2 & XW & XZ & XWV & XSZ & XAV).
  destruct SV as (S8 & S16 & S24 & S32 & S40 & S48).
  assert (UB : forall i, 0 <= U i < 2 ^ 64) by (intros i; unfold U; apply bv_unsigned_in_range).
  pose proof (UB 1%nat) as UB1. pose proof (UB 8%nat) as UB8. pose proof (UB 9%nat) as UB9. pose proof (UB 18%nat) as UB18. pose proof (UB 19%nat) as UB19. pose proof (UB 20%nat) as UB20.
  LeanFeed.pfeed PP (PMAVGP.avaC_conc fx R (mrestrict (ahid Aw model) M) (fun j => match j with 2%nat => S | 37%nat => v | 40%nat => b | 41%nat => n | 43%nat => k
     | 48%nat => U 1 | 49%nat => U 8 | 50%nat => U 9 | 51%nat => U 18 | 52%nat => U 19 | 53%nat => U 20 | _ => 0 end)) ltac:(pfeed XW XSZ XAV).
  destruct PP as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & A1 & A2 & A8 & A9 & A10 & A18 & A19 & A20 & C8).
  apply (piece_step fx fx1 R 0xb400c R1 0xb409c _ M model cr0 LK Aw M1v (fun a => v + 8 <= a < v + 8 + 8) HH SO MO MS1 MG1 FRZ1); [intros a Pa; right; lia|].
  intros M1 model1 HH1 SO1 MO1 FR1 VUP AGS.
  assert (KEEP : forall a val, a + 8 <= v + 8 \/ v + 16 <= a -> 0 <= a -> a + 8 <= 2 ^ 64 -> L5.u64_at RSEGS M a val -> L5.u64_at RSEGS M1 a val).
  { intros a val Ha H0 H1 X. apply (L5C.u64_at_agree RSEGS M M1); [intros i Hi; apply FR1; lia| lia| lia| exact X]. }
  destruct (nfacts _ LK cr0 Aw M1 model1 HH1 MO1) as (_ & (_ & _ & _ & ODEF1) & BF1).
  destruct (BF1 b c ltac:(left; reflexivity)) as (_ & _ & _ & _ & _ & _ & QD1).
  apply (finish fx1 R1 M1 model1 LK Aw (PGV8.V8Blk b (n + k) c) g cr0 A1 A2); try assumption.
  - intros i Hi. cbn in Hi. destruct Hi as [<-|[<-|[<-|[<-|[<-|[]]]]]]; assumption.
  - apply (kept0_of R R1 KP). intros i Hi. apply KS1. cbn in Hi. repeat (destruct Hi as [<-|Hi]; [inl|]). destruct Hi.
  - destruct MO1 as (_ & _ & _ & ACC1 & _). split; [exact ODEF1|]. split; [exact ACC1|].
    split; [apply KEEP; [lia| lia| lia| exact W0]|]. split; [apply VUP; [lia|]; replace (b + (n + k)) with (b + (n + k)) by lia; exact C8|].
    split; [apply KEEP; [lia| lia| lia| exact W16]|]. split; [lia|]. split; [lia|]. split; [exact Hb|]. split; [exact Hb16|]. split; [exact QD1|].
    split; [apply (PMFA.accA_agree M M1 b (n + k)); [apply AGS; lia| exact ACB]|].
    apply (PGV8KA.annA_agree M M1 b (n + k) c); [lia| apply PMKA.mod16_8'; exact Hb16| apply AGS; lia| exact ANB].
  - subst x. cbn [PGV8.v8_size]. lia.
  - subst x. exact OK0.
  - subst x. cbn [PGV8.v8_cap]. lia.
  - subst x. intros _. cbn [PGV8.v8_own PGV8.v8_cap]. split; [reflexivity|]. split; reflexivity.
  - subst x. left. reflexivity.
  - subst x. unfold PMSP.credit_keep, PMSPA.scA, PGV8.pot_v8. cbn [fst snd PGV8.v8_cap]. lia.
Qed.

(* [comment removed for export] *)
Lemma ip_B (fx : FPState) R M model LK Aw b n c :
  x = PGV8.V8Blk b n c -> n + k <= c ->
  getr R (reg 2) = Z_to_bv 64 (S - 96) -> getr R (reg 8) = Z_to_bv 64 v -> getr R (reg 9) = Z_to_bv 64 k -> getr R (reg 18) = Z_to_bv 64 (v + 8) ->
  getr R (reg 19) = Z_to_bv 64 (b + n) -> getr R (reg 20) = Z_to_bv 64 ((v + 8) / 8 + 2147450880) -> kept0 R ->
  stok model LK Aw -> mem_ok M -> saves M -> ri_inv HI ([(b, c)] ++ LB) FF LK cr0 Aw M (vml_of model) ->
  hdr M b (b + n) (b + c) ->
  0 <= n <= c -> 1 <= c <= 2 ^ 27 -> 4096 <= b -> b mod 16 = 0 ->
  PMSPA.accA M b (n + k) -> PGV8A.annA M b (n + k) c ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0xb3ff4 M model) K.
Proof using All.
  intros EX Hnk E2 E8 E9 E18 E19 E20 KP SO MO SV HH HD Hn Hc Hb Hb16 ACB ANB.
  destruct (nfacts _ LK cr0 Aw M model HH MO) as ((A16 & SLO & SHI & SPT & C0) & (O1 & O2 & O5 & ODEF) & BF).
  destruct (BF b c ltac:(left; reflexivity)) as (Q0 & Q1 & Q2 & Q4 & Q5 & Q6 & QD). unfold nsh in O5, Q5.
  destruct (vfacts _ LK cr0 Aw M model HH MO) as (X0 & X1 & X2 & XW & XZ & XWV & XSZ & XAV).
  pose proof SV as (S8 & S16 & S24 & S32 & S40 & S48). pose proof HD as (W0 & W8 & W16).
  assert (UB : forall i, 0 <= U i < 2 ^ 64) by (intros i; unfold U; apply bv_unsigned_in_range).
  pose proof (UB 1%nat) as UB1. pose proof (UB 8%nat) as UB8. pose proof (UB 9%nat) as UB9. pose proof (UB 18%nat) as UB18. pose proof (UB 19%nat) as UB19. pose proof (UB 20%nat) as UB20.
  LeanFeed.pfeed PP (PMAVGP.avaB_conc fx R (mrestrict (ahid Aw model) M) (fun j => match j with 2%nat => S | 37%nat => v | 40%nat => b | 41%nat => n | 43%nat => k
     | 48%nat => U 1 | 49%nat => U 8 | 50%nat => U 9 | 51%nat => U 18 | 52%nat => U 19 | 53%nat => U 20 | _ => 0 end)) ltac:(pfeed XW XSZ XAV).
  destruct PP as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & A1 & A8 & A10 & A11 & A12).
  apply (piece_step fx fx1 R 0xb3ff4 R1 0x77d68 _ M model cr0 LK Aw M1v (fun _ => False) HH SO MO MS1 MG1 (fun a Ha _ => FRZ1 a Ha)); [intros a []|].
  intros M1 model1 HH1 SO1 MO1 FR1 VUP AGS.
  assert (EQ1 : forall a, 0 <= a < 2 ^ 64 -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) by (intros a Ha; apply FR1; [exact Ha| intros []]).
  pose proof (saves_piece _ LK cr0 Aw M model M1 _ HH MO FR1 ltac:(intros i []) SV) as SV1.
  pose proof (hdr_piece _ LK cr0 Aw M model M1 _ b _ _ HH MO FR1 ltac:(intros i []) HD) as HD1.
  assert (ACB1 : PMSPA.accA M1 b (n + k)) by (apply (PMFA.accA_agree M M1 b (n + k)); [apply AGS; lia| exact ACB]).
  assert (ANB1 : PGV8A.annA M1 b (n + k) c) by (apply (PGV8KA.annA_agree M M1 b (n + k) c); [lia| apply PMKA.mod16_8'; exact Hb16| apply AGS; lia| exact ANB]).
  destruct (nfacts _ LK cr0 Aw M1 model1 HH1 MO1) as (_ & _ & BF1).
  destruct (BF1 b c ltac:(left; reflexivity)) as (_ & _ & _ & _ & _ & _ & QD1).
  destruct (cstk _ LK cr0 Aw M1 model1 96 2560 HH1 MO1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(reflexivity)) as (STKc & _).
  pose proof SO1 as (AM1 & MRT1 & ILK1 & IAW1).
  assert (KS2 : forall i, In i [2; 3; 4; 9; 18; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R1 (reg i) = getr R (reg i)).
  { intros i Hi. apply KS1. cbn in Hi. repeat (destruct Hi as [<-|Hi]; [inl|]). destruct Hi. }
  (* [comment removed for export] *)
  apply (memset_call27 fx1 R1 M1 model1 K _ FF LK cr0 Aw (S - 96) 737292 (b + n) 0 k HH1 AM1 K0 A1 ltac:(split; [lia| reflexivity])).
  { rewrite (KS2 2%nat) by inl. exact E2. }
  { rewrite (KS2 4%nat) by inl. rewrite (KP 4%nat) by inl. exact Rtp0. }
  { exact A10. } { exact A11. } { exact A12. } { lia. } { exact STKc. }
  { apply (aacc_sub M1 b (n + k)); [exact ACB1| lia| lia]. }
  { intros i Hi. unfold aclientw, aclient_g. left. exists (b, c). split; [left; reflexivity|]. cbn [fst snd]. lia. }
  { intros i Hi. replace (b + n + i) with (b + (n + i)) by lia. apply QD1. lia. }
  { lia. } { lia. }
  { unfold app_rng, BIGSHADOW_LO, BIGSHADOW_HI. lia. }
  intros fx2 R2 M2 model2 RP2 DD2 HP2 MRT2 AM2 HH2.
  assert (WIN : forall rg, In rg [(b + n, k)] -> exists q m, In (q, m) [(b, c)] /\ q <= fst rg /\ fst rg + snd rg <= q + m).
  { intros rg [<-|[]]. exists b, c. split; [left; reflexivity|]. cbn [fst snd]. lia. }
  pose proof (mem_ok_callee _ _ LK cr0 Aw M1 model1 M2 (S - 96) 2560 _ HH1 MO1 HP2 ltac:(lia) ltac:(lia) ltac:(lia) WIN) as MO2.
  pose proof (saves_callee _ LK cr0 Aw M1 model1 M2 _ (S - 96) 2560 _ HH1 MO1 HP2 ltac:(lia) ltac:(lia) ltac:(lia) WIN SV1) as SV2.
  pose proof (hdr_callee _ LK cr0 Aw M1 model1 M2 _ (S - 96) 2560 _ b _ _ HH1 MO1 HP2 ltac:(lia) ltac:(lia) ltac:(lia) WIN HD1) as HD2.
  assert (WA : PMKA.wapp [(b + n, k)]) by (apply PMKA.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; lia| intros rg []]).
  pose proof (blksh_ek _ FF (S - 96) 2560 _ M1 M2 b c (proj1 HP2) WA ltac:(left; reflexivity) ltac:(lia) ltac:(lia)) as AGB.
  assert (CS2 : forall i, In i L5SAR.cs_all -> getr R2 (reg i) = getr R1 (reg i)) by (intros i Hi; exact (L5SAR.cs_of_preserved R1 R2 i RP2 Hi)).
  destruct HD2 as (W0' & W8' & W16').
  apply (ip_C fx2 R2 M2 model2 LK Aw b n c EX Hnk); try assumption.
  - rewrite CS2 by inl. rewrite (KS2 2%nat) by inl. exact E2.
  - rewrite CS2 by inl. rewrite A8. f_equal. lia.
  - rewrite CS2 by inl. rewrite (KS2 9%nat) by inl. exact E9.
  - rewrite CS2 by inl. rewrite (KS2 18%nat) by inl. exact E18.
  - rewrite CS2 by inl. rewrite (KS2 20%nat) by inl. exact E20.
  - apply (kept0_pres R1 R2); [| exact RP2]. apply (kept0_of R R1 KP). intros i Hi. apply KS2. clear - Hi. cbn in Hi |- *. tauto.
  - exact (stok_step model1 LK Aw model2 LK Aw SO1 AM2 MRT2 (incl_refl _) (incl_refl _)).
  - apply (PMFA.accA_agree M1 M2 b (n + k)); [intros y Hy; apply AGB; lia| exact ACB1].
  - apply (PGV8KA.annA_agree M1 M2 b (n + k) c); [lia| apply PMKA.mod16_8'; exact Hb16| exact AGB| exact ANB1].
Qed.

(* [comment removed for export] *)
Hypothesis OPN : PMA.opnew_spec L ar HI.
Hypothesis OPD : PMA.opdel_spec L ar HI.
Hypothesis ANNI : PNSAX8.ann_increase_v8_spec RSEGS AD L ar HI 0xb4260.
Hypothesis ANNN : PNSAX8.ann_new_v8_spec RSEGS AD L ar HI 0xb431c.
Hypothesis ANND : PNSAX.ann_delete_v8_spec RSEGS AD L ar HI 0xab098.

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

(* [comment removed for export] *)
Lemma ip_inc (fx : FPState) R M model LK Aw b n c :
  x = PGV8.V8Blk b n c -> n + k <= c ->
  getr R (reg 1) = Z_to_bv 64 737268 -> getr R (reg 2) = Z_to_bv 64 (S - 96) -> getr R (reg 8) = Z_to_bv 64 v -> getr R (reg 9) = Z_to_bv 64 k ->
  getr R (reg 10) = Z_to_bv 64 v -> getr R (reg 11) = Z_to_bv 64 k -> getr R (reg 18) = Z_to_bv 64 (v + 8) ->
  getr R (reg 19) = Z_to_bv 64 (b + n) -> getr R (reg 20) = Z_to_bv 64 ((v + 8) / 8 + 2147450880) -> kept0 R ->
  stok model LK Aw -> mem_ok M -> saves M -> ri_inv HI ([(b, c)] ++ LB) FF LK cr0 Aw M (vml_of model) -> v8_atA M v x ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0xb4260 M model) K.
Proof using All.
  intros EX Hnk E1 E2 E8 E9 E10 E11 E18 E19 E20 KP SO MO SV HH VS.
  destruct (centry0 R _ LK cr0 Aw M model 96 737268 HH MO KP E1 ltac:(split; [lia| reflexivity]) E2 ltac:(lia) ltac:(reflexivity)) as (ENT & FRSc).
  pose proof SO as (AM & MRT & ILK & IAW). pose proof MO as (_ & _ & _ & ACC & _).
  pose proof ANNI as AI. unfold PNSAX8.ann_increase_v8_spec in AI.
  assert (HHx : ri_inv HI (PGV8.v8_own x ++ LB) FF LK cr0 Aw M (vml_of model)) by (rewrite EX; exact HH).
  assert (A10 : getr R 10%bv = Z_to_bv 64 v) by (rewrite L5K.rl10; exact E10).
  assert (A11 : getr R 11%bv = Z_to_bv 64 k) by (rewrite L5SAR.r11; exact E11).
  assert (Hsz : PGV8.v8_size x + k <= PGV8.v8_cap x) by (rewrite EX; cbn [PGV8.v8_size PGV8.v8_cap]; lia).
  unfold PMSP.cfg.
  apply (AI fx R M model K LB FF LK Aw cr0 v k x (S - 96) 737268 HHx AM K0 ENT FRSc A10 A11 AO V8 ACC VS ltac:(lia) Hsz).
  intros fx' R' M' model' LK' Aw' RP HD' ACC' BLK' KEPT' HP' MRT' ILK' IAW' AM' HH'.
  change (PMSPA.pm_scr 0) with 12288 in HP'. rewrite EX in HH', HD'. cbn [PGV8.v8_own] in HH'.
  assert (WIN : forall rg, In rg (@nil L5.range) -> exists q m, In (q, m) [(b, c)] /\ q <= fst rg /\ fst rg + snd rg <= q + m) by (intros rg []).
  pose proof (mem_ok_callee _ [] LK cr0 Aw M model M' (S - 96) 12288 _ HH MO HP' ltac:(lia) ltac:(lia) ltac:(lia) WIN) as MO'.
  pose proof (saves_callee _ LK cr0 Aw M model M' [] (S - 96) 12288 _ HH MO HP' ltac:(lia) ltac:(lia) ltac:(lia) WIN SV) as SV'.
  destruct HD' as (_ & W0 & W8 & W16 & Hn & Hc & Hb & Hb16 & _).
  destruct (BLK' b n c EX) as (ACB & ANB).
  assert (CS : forall i, In i L5SAR.cs_all -> getr R' (reg i) = getr R (reg i)) by (intros i Hi; exact (L5SAR.cs_of_preserved R R' i RP Hi)).
  apply (ip_B fx' R' M' model' LK' Aw' b n c EX Hnk); try assumption.
  - rewrite CS by inl. exact E2.
  - rewrite CS by inl. exact E8.
  - rewrite CS by inl. exact E9.
  - rewrite CS by inl. exact E18.
  - rewrite CS by inl. exact E19.
  - rewrite CS by inl. exact E20.
  - exact (kept0_pres R R' KP RP).
  - exact (stok_step model LK Aw model' LK' Aw' SO AM' MRT' ILK' IAW').
  - split; [exact W0|]. split; [exact W8| exact W16].
Qed.

(* [comment removed for export] *)
Hypothesis VS0 : v8_atA M0 v x.
Hypothesis HH0 : ri_inv HI (PGV8.v8_own x ++ LB) FF LK0 cr0 Aw0 M0 (vml_of model0).
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
Lemma finish_p (fx : FPState) R M model LK Aw x' g' cr' :
  getr R (reg 1) = Z_to_bv 64 (U 1) -> getr R (reg 2) = Z_to_bv 64 S ->
  (forall i, In i [8; 9; 18; 19; 20]%nat -> getr R (reg i) = Z_to_bv 64 (U i)) -> kept0 R ->
  stok model LK Aw -> mem_ok M -> ri_inv HI (PGV8.v8_own x' ++ LB) FF LK cr' Aw M (vml_of model) -> v8_atA M v x' -> post_ok x' g' cr' ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0xb409c M model) K.
Proof using All.
  intros E1 E2 ES KP SO MO HH VS (P1 & P2 & P3 & P4 & P5 & P6). exact (finish fx R M model LK Aw x' g' cr' E1 E2 ES KP SO MO HH VS P1 P2 P3 P4 P5 P6).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma tail_J (fx : FPState) R M model LK Aw x' g' cr' :
  getr R (reg 2) = Z_to_bv 64 (S - 96) -> kept0 R -> stok model LK Aw -> mem_ok M -> saves M ->
  ri_inv HI (PGV8.v8_own x' ++ LB) FF LK cr' Aw M (vml_of model) -> v8_atA M v x' -> post_ok x' g' cr' ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0xb4080 M model) K.
Proof using All.
  intros E2 KP SO MO SV HH VS PO.
  destruct (nfacts _ LK cr' Aw M model HH MO) as ((A16 & SLO & SHI & SPT & C0) & (O1 & O2 & O5 & ODEF) & BF). unfold nsh in O5.
  destruct (vfacts _ LK cr' Aw M model HH MO) as (X0 & X1 & X2 & XW & XZ & XWV & XSZ & XAV).
  pose proof SV as (S8 & S16 & S24 & S32 & S40 & S48). pose proof xnum as (_ & _ & _ & K27 & _).
  assert (UB : forall i, 0 <= U i < 2 ^ 64) by (intros i; unfold U; apply bv_unsigned_in_range).
  pose proof (UB 1%nat) as UB1. pose proof (UB 8%nat) as UB8. pose proof (UB 9%nat) as UB9. pose proof (UB 18%nat) as UB18. pose proof (UB 19%nat) as UB19. pose proof (UB 20%nat) as UB20.
  LeanFeed.pfeed PP (PMAVGP.avaJ_conc fx R (mrestrict (ahid Aw model) M) (fun j => match j with 2%nat => S | 37%nat => v | 43%nat => k
     | 48%nat => U 1 | 49%nat => U 8 | 50%nat => U 9 | 51%nat => U 18 | 52%nat => U 19 | 53%nat => U 20 | _ => 0 end)) ltac:(pfeed XW XSZ XAV).
  destruct PP as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & A1 & A2 & A8 & A9 & A18 & A19 & A20).
  apply (piece_step fx fx1 R 0xb4080 R1 0xb409c _ M model cr' LK Aw M1v (fun _ => False) HH SO MO MS1 MG1 (fun a Ha _ => FRZ1 a Ha)); [intros a []|].
  intros M1 model1 HH1 SO1 MO1 FR1 VUP AGS.
  assert (EQ1 : M1 = M).
  { apply functional_extensionality. intros a. pose proof (FR1 (bv_unsigned a) (bv_unsigned_in_range _ a) (fun X => X)) as E. rewrite Z_to_bv_bv_unsigned in E. exact E. }
  subst M1.
  apply (finish_p fx1 R1 M model1 LK Aw x' g' cr' A1 A2); try assumption.
  - intros i Hi. cbn in Hi. destruct Hi as [<-|[<-|[<-|[<-|[<-|[]]]]]]; assumption.
  - apply (kept0_of R R1 KP). intros i Hi. apply KS1. clear - Hi. cbn in Hi. repeat (destruct Hi as [<-|Hi]; [inl|]). destruct Hi.
Qed.

(* [comment removed for export] *)
Lemma piece_ro (fx fx1 : FPState) R (pc : Z) R1 (pc1 : Z) HL M model cr LK Aw (M1v : word -> option byte) :
  ri_inv HI (HL ++ LB) FF LK cr Aw M (vml_of model) -> stok model LK Aw -> mem_ok M ->
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) (mrestrict (ahid Aw model) M) (seg_rom RSEGS)) (@mkst fx1 R1 (Z_to_bv 64 pc1) M1v (seg_rom RSEGS)) ->
  mem_grows (mrestrict (ahid Aw model) M) M1v ->
  (forall a, 0 <= a < 2 ^ 64 -> M1v (Z_to_bv 64 a) = mrestrict (ahid Aw model) M (Z_to_bv 64 a)) ->
  (forall model1, ri_inv HI (HL ++ LB) FF LK cr Aw M (vml_of model1) -> stok model1 LK Aw ->
      srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 pc1 M model1) K) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R pc M model) K.
Proof.
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
Proof.
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
Proof. destruct y as [|b n c]; [left; reflexivity| right; exists b, n, c; reflexivity]. Qed.

(* [comment removed for export] *)
Lemma tail_I (fx : FPState) R M model LK Aw cr B A g' :
  getr R (reg 2) = Z_to_bv 64 (S - 96) -> kept0 R -> stok model LK Aw -> mem_ok M -> saves M ->
  ri_inv HI (((B, A) :: PGV8.v8_own x) ++ LB) FF LK cr Aw M (vml_of model) ->
  v8_atA M v (PGV8.V8Blk B (PGV8.v8_size x + k) A) ->
  L5.u64_at RSEGS M (S - 88) (PGV8.v8_data x) -> L5.u64_at RSEGS M (S - 80) (PGV8.v8_data x) -> L5.u64_at RSEGS M (S - 72) (PGV8.v8_data x) ->
  L5.u64_at RSEGS M (S - 64) (PGV8.v8_data x + PGV8.v8_cap x) ->
  post_ok (PGV8.V8Blk B (PGV8.v8_size x + k) A) g' cr ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0xb405c M model) K.
Proof using All.
  intros E2 KP SO MO SV HH VS SB1 SB2 SB3 SB4 PO.
  destruct (nfacts _ LK cr Aw M model HH MO) as ((A16 & SLO & SHI & SPT & C0) & (O1 & O2 & O5 & ODEF) & BF). unfold nsh in O5.
  destruct (vfacts _ LK cr Aw M model HH MO) as (X0 & X1 & X2 & XW & XZ & XWV & XSZ & XAV).
  pose proof SV as (S8 & S16 & S24 & S32 & S40 & S48). pose proof xnum as (XD & XS & XC & K27 & XSK & XDC). pose proof xr as XR.
  assert (UB : forall i, 0 <= U i < 2 ^ 64) by (intros i; unfold U; apply bv_unsigned_in_range).
  pose proof (UB 1%nat) as UB1. pose proof (UB 8%nat) as UB8. pose proof (UB 9%nat) as UB9. pose proof (UB 18%nat) as UB18. pose proof (UB 19%nat) as UB19. pose proof (UB 20%nat) as UB20.
  LeanFeed.pfeed PP (PMAVGP.avaI_conc fx R (mrestrict (ahid Aw model) M) (fun j => match j with 2%nat => S | 37%nat => v | 40%nat => PGV8.v8_data x | 42%nat => PGV8.v8_cap x | 43%nat => k
     | 48%nat => U 1 | 49%nat => U 8 | 50%nat => U 9 | 51%nat => U 18 | 52%nat => U 19 | 53%nat => U 20 | _ => 0 end)) ltac:(pfeed XW XSZ XAV).
  destruct PP as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & [(MS1 & KS1 & A1 & A10 & A11 & NZ)|(MS1 & KS1 & A1 & A2 & A8 & A9 & A10 & A11 & A18 & A19 & A20 & ZZ)]).
  - (* [comment removed for export] *)
    apply (piece_ro fx fx1 R 0xb405c R1 0xd1400 _ M model cr LK Aw M1v HH SO MO MS1 MG1 FRZ1). intros model1 HH1 SO1.
    destruct (v8_case x) as [EX|(b & n & c & EX)]; rewrite EX in XR, NZ, HH1, A10, A11, VS, PO, HH, SB1, SB2, SB3, SB4; cbn [PGV8.v8_data PGV8.v8_cap PGV8.v8_size PGV8.v8_own] in *;
      [exfalso; clear - NZ; rewrite Z.sub_0_r, Z.mod_0_l in NZ by lia; lia|].
    destruct XR as (Hn & Hc & Hb & Hb16 & Hbc).
    pose proof SO1 as (AM1 & MRT1 & ILK1 & IAW1).
    destruct (cstk _ LK cr Aw M model1 96 4096 HH1 MO ltac:(lia) ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(reflexivity)) as (STKc & _).
    destruct (PNAEK.own_facts L ar C HI HIok B A _ FF LK cr Aw M _ HH1) as (BAp & _). pose proof (BAp b c ltac:(left; reflexivity)) as BNE.
    destruct (BF B A ltac:(left; reflexivity)) as (QB0 & QB1 & QB2 & QB4 & QB5 & QB6 & QBD).
    assert (NEQ : (B =? b) = false) by (apply Z.eqb_neq; clear - BNE QB1 Hc; lia).
    assert (KS2 : forall i, In i [2; 3; 4; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R1 (reg i) = getr R (reg i)).
    { intros i Hi. apply KS1. clear - Hi. cbn in Hi. repeat (destruct Hi as [<-|Hi]; [inl|]). destruct Hi. }
    pose proof OPD as OD. unfold PMA.opdel_spec, PMSPA.opdel_spec, PMSPA.opdel_spec_at in OD. cbn [pa_opdel PMA.AD ADDR_A] in OD.
    assert (E10 : getr R1 10%bv = Z_to_bv 64 b) by (rewrite L5K.rl10; exact A10).
    assert (E1 : getr R1 1%bv = Z_to_bv 64 737408) by (rewrite L5K.rl1; exact A1).
    assert (E2' : getr R1 2%bv = Z_to_bv 64 (S - 96)) by (rewrite L5K.rl2, (KS2 2%nat) by inl; exact E2).
    assert (E4 : getr R1 4%bv = Z_to_bv 64 (hl_tp L)) by (rewrite L5K.rl4, (KS2 4%nat) by inl; rewrite (KP 4%nat) by inl; exact Rtp0).
    unfold PMSP.cfg.
    apply (OD fx1 R1 M model1 K _ FF LK Aw cr b c (S - 96) 737408 HH1 AM1 K0 ltac:(right; left; reflexivity) E10 E1 ltac:(split; [lia| reflexivity]) E2' E4 STKc).
    intros fx2 R2 M2 model2 Aw2 RP2 HP2 MRT2 IAW2 AM2 HH2.
    cbn [app lb_remove fst] in HP2, HH2. rewrite NEQ, Z.eqb_refl in HP2, HH2. unfold PMSPA.OPDEL_SCR, PMSPA.MALLOC_SCR in HP2.
    assert (WIN : forall rg, In rg (@nil L5.range) -> exists q m, In (q, m) [(B, A); (b, c)] /\ q <= fst rg /\ fst rg + snd rg <= q + m) by (intros rg []).
    pose proof (mem_ok_callee [(B, A); (b, c)] [(B, A)] LK cr Aw M model1 M2 (S - 96) 4096 _ HH1 MO HP2 ltac:(lia) ltac:(lia) ltac:(lia) WIN) as MO2.
    pose proof (saves_callee [(B, A); (b, c)] LK cr Aw M model1 M2 [(B, A)] (S - 96) 4096 _ HH1 MO HP2 ltac:(lia) ltac:(lia) ltac:(lia) WIN SV) as SV2.
    destruct (nfacts [(B, A)] LK cr Aw2 M2 model2 HH2 MO2) as (_ & (_ & _ & _ & ODEF2) & BF2).
    destruct (BF2 B A ltac:(left; reflexivity)) as (_ & _ & _ & _ & _ & _ & QBD2).
    pose proof HP2 as (EK2 & _).
    apply (tail_J fx2 R2 M2 model2 LK Aw2 (PGV8.V8Blk B (PGV8.v8_size x + k) A) g' cr).
    + rewrite (L5SAR.cs_of_preserved R1 R2 2%nat RP2) by inl. rewrite (KS2 2%nat) by inl. exact E2.
    + apply (kept0_pres R1 R2); [| exact RP2]. apply (kept0_of R R1 KP). intros i Hi. apply KS2. clear - Hi. cbn in Hi |- *. tauto.
    + exact (stok_step model1 LK Aw model2 LK Aw2 SO1 AM2 MRT2 (incl_refl _) IAW2).
    + exact MO2.
    + exact SV2.
    + exact HH2.
    + rewrite EX. cbn [PGV8.v8_size]. apply (v8_at_agree M M2 _ VS ODEF2); [| | lia| lia|].
      * apply (obj_ek _ FF (S - 96) 4096 [] M M2 v 24 v 24 EK2 AO V8); [lia| lia| lia| lia| intros i _ rg []].
      * apply (objsh_ek _ FF (S - 96) 4096 [] M M2 v 24 EK2 ltac:(intros rg []) AO); lia.
      * intros b' n' c' E. injection E as <- <- <-. split; [exact QBD2|].
        apply (blksh_ek _ FF (S - 96) 4096 [] M M2 B A EK2 ltac:(intros rg []) ltac:(left; reflexivity)); lia.
    + rewrite EX at 1. cbn [PGV8.v8_size]. exact PO.
  - (* [comment removed for export] *)
    apply (piece_ro fx fx1 R 0xb405c R1 0xb409c _ M model cr LK Aw M1v HH SO MO MS1 MG1 FRZ1). intros model1 HH1 SO1.
    destruct (v8_case x) as [EX|(b & n & c & EX)]; rewrite EX in XR, ZZ, HH1; cbn [PGV8.v8_data PGV8.v8_cap PGV8.v8_size PGV8.v8_own] in *.
    2: { exfalso. destruct XR as (Hn & Hc & Hb & Hb16 & Hbc). clear - ZZ Hb Hbc Hc. rewrite Z.sub_0_r, Z.mod_small in ZZ by lia. lia. }
    apply (finish_p fx1 R1 M model1 LK Aw (PGV8.V8Blk B (PGV8.v8_size x + k) A) g' cr A1 A2); try assumption.
    + intros i Hi. cbn in Hi. destruct Hi as [<-|[<-|[<-|[<-|[<-|[]]]]]]; assumption.
    + apply (kept0_of R R1 KP). intros i Hi. apply KS1. clear - Hi. cbn in Hi. repeat (destruct Hi as [<-|Hi]; [inl|]). destruct Hi.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ssaves (M : word -> option byte) (w8 w9 w18 w19 : Z) : Prop :=
  L5.u64_at RSEGS M (S - 104) 737372 /\ L5.u64_at RSEGS M (S - 112) w8 /\ L5.u64_at RSEGS M (S - 120) w9 /\ L5.u64_at RSEGS M (S - 128) w18
  /\ L5.u64_at RSEGS M (S - 136) w19.
Definition sbuf (M : word -> option byte) (p1 p2 p3 p4 : Z) : Prop :=
  L5.u64_at RSEGS M (S - 88) p1 /\ L5.u64_at RSEGS M (S - 80) p2 /\ L5.u64_at RSEGS M (S - 72) p3 /\ L5.u64_at RSEGS M (S - 64) p4.

(* [comment removed for export] *)
Lemma sw_C (fx : FPState) R M model LK Aw cr B A g' w8 w9 w18 w19 :
  getr R (reg 2) = Z_to_bv 64 (S - 144) -> getr R (reg 8) = Z_to_bv 64 (S - 88) -> getr R (reg 9) = Z_to_bv 64 v -> getr R (reg 18) = Z_to_bv 64 B ->
  getr R (reg 19) = Z_to_bv 64 2147450880 -> kept0 R ->
  stok model LK Aw -> mem_ok M -> saves M -> ssaves M w8 w9 w18 w19 -> 0 <= w8 < 2 ^ 64 -> 0 <= w9 < 2 ^ 64 -> 0 <= w18 < 2 ^ 64 -> 0 <= w19 < 2 ^ 64 ->
  ri_inv HI (((B, A) :: PGV8.v8_own x) ++ LB) FF LK cr Aw M (vml_of model) ->
  hdr M (PGV8.v8_data x) (PGV8.v8_data x + PGV8.v8_size x) (PGV8.v8_data x + PGV8.v8_cap x) ->
  sbuf M B (B + PGV8.v8_size x) ((B + PGV8.v8_size x) + k) (B + A) ->
  A <= 2 ^ 27 -> PGV8.v8_size x + k <= A -> shadow_blk M B A ->
  post_ok (PGV8.V8Blk B (PGV8.v8_size x + k) A) g' cr ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0xb417c M model) K.
Proof using All.
  intros E2 E8 E9 E18 E19 KP SO MO SV SSV Hw8 Hw9 Hw18 Hw19 HH HD SBF HA HnkA SHB PO.
  destruct (nfacts _ LK cr Aw M model HH MO) as ((A16 & SLO & SHI & SPT & C0) & (O1 & O2 & O5 & ODEF) & BF). unfold nsh in O5.
  destruct (BF B A ltac:(left; reflexivity)) as (QB0 & QB1 & QB2 & QB4 & QB5 & QB6 & QBD). unfold nsh in QB5.
  destruct (vfacts _ LK cr Aw M model HH MO) as (X0 & X1 & X2 & XW & XZ & XWV & XSZ & XAV).
  pose proof SSV as (T8 & T16 & T24 & T32 & T40). pose proof HD as (W0 & W8 & W16). pose proof SBF as (B1 & B2 & B3 & B4).
  pose proof xnum as (XD & XS & XC & K27 & XSK & XDC).
  pose proof (PMAVGP.avsC_conc fx R (mrestrict (ahid Aw model) M) (fun j => match j with 2%nat => S - 96 | 37%nat => v | 40%nat => PGV8.v8_data x | 41%nat => PGV8.v8_size x
     | 42%nat => PGV8.v8_cap x | 43%nat => k | 44%nat => B | 46%nat => A
     | 48%nat => 737372 | 49%nat => w8 | 50%nat => w9 | 51%nat => w18 | 52%nat => w19 | _ => 0 end)) as PP.
  cbn beta iota in PP.
  replace (S - 96 - 48) with (S - 144) in PP by lia. replace (S - 96 + 8) with (S - 88) in PP by lia. replace (S - 96 - 8) with (S - 104) in PP by lia.
  replace (S - 96 - 16) with (S - 112) in PP by lia. replace (S - 96 - 24) with (S - 120) in PP by lia. replace (S - 96 - 32) with (S - 128) in PP by lia.
  replace (S - 96 - 40) with (S - 136) in PP by lia. replace (S - 96 + 16) with (S - 80) in PP by lia. replace (S - 96 + 24) with (S - 72) in PP by lia.
  replace (S - 96 + 32) with (S - 64) in PP by lia. replace (v + 0) with v in PP by lia.
  L5SAR.feed PP ltac:(pfeed XW XSZ XAV).
  destruct PP as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & A1 & A2 & A8 & A9 & A10 & A11 & A12 & A18 & A19 & C1 & C2 & C3 & C4 & C5 & C6 & C7).
  apply (piece_step fx fx1 R 0xb417c R1 0xb431c _ M model cr LK Aw M1v (fun a => v <= a < v + 24 \/ S - 88 <= a < S - 88 + 32) HH SO MO MS1 MG1).
  { intros a Ha N. apply FRZ1; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X]. }
  { intros a [Pa|Pa]; [right; lia| left; lia]. }
  intros M1 model1 HH1 SO1 MO1 FR1 VUP AGS.
  pose proof (saves_piece _ LK cr Aw M model M1 _ HH MO FR1 ltac:(intros i [X|X]; lia) SV) as SV1.
  destruct (nfacts _ LK cr Aw M1 model1 HH1 MO1) as (_ & (_ & _ & _ & ODEF1) & BF1).
  destruct (BF1 B A ltac:(left; reflexivity)) as (_ & _ & _ & _ & _ & _ & QBD1).
  pose proof MO1 as (_ & _ & _ & ACC1 & _). pose proof SO1 as (AM1 & MRT1 & ILK1 & IAW1).
  assert (KS2 : forall i, In i [3; 4; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R1 (reg i) = getr R (reg i)).
  { intros i Hi. apply KS1. clear - Hi. cbn in Hi. repeat (destruct Hi as [<-|Hi]; [inl|]). destruct Hi. }
  pose proof (kept0_of R R1 KP KS2) as KP1.
  assert (E2' : getr R1 (reg 2) = Z_to_bv 64 (S - 96)) by exact A2.
  destruct (centry0 R1 _ LK cr Aw M1 model1 96 737372 HH1 MO1 KP1 A1 ltac:(split; [lia| reflexivity]) E2' ltac:(lia) ltac:(reflexivity)) as (ENT & FRSc).
  set (x' := PGV8.V8Blk B (PGV8.v8_size x + k) A) in *.
  assert (HD1 : PNSAX.v8_hdr RSEGS M1 v x').
  { split; [exact ODEF1|]. unfold x'. split; [apply VUP; [right; lia| exact C7]|]. split; [apply VUP; [right; lia| replace (B + (PGV8.v8_size x + k)) with (B + PGV8.v8_size x + k) by lia; exact C5]|]. split; [apply VUP; [right; lia| exact C3]|].
    split; [lia|]. split; [lia|]. split; [lia|]. split; [exact QB4| exact QBD1]. }
  assert (SHB1 : forall b n c, x' = PGV8.V8Blk b n c -> PMSPA.annA M1 b c c).
  { intros b n c E. unfold x' in E. injection E as <- <- <-. apply PNSAX8.ann_full_of_blk.
    apply (shblk_agree M M1 B A); [apply PMKA.mod16_8'; exact QB4| lia| apply AGS; lia| exact SHB]. }
  assert (HHx : ri_inv HI (PGV8.v8_own x' ++ (PGV8.v8_own x ++ LB)) FF LK cr Aw M1 (vml_of model1)) by exact HH1.
  pose proof ANNN as AN. unfold PNSAX8.ann_new_v8_spec in AN.
  assert (E10 : getr R1 10%bv = Z_to_bv 64 v) by (rewrite L5K.rl10; exact A10).
  assert (E11 : getr R1 11%bv = Z_to_bv 64 (PGV8.v8_size x + k)) by (rewrite L5SAR.r11; exact A11).
  unfold PMSP.cfg.
  apply (AN fx1 R1 M1 model1 K (PGV8.v8_own x ++ LB) FF LK Aw cr v (PGV8.v8_size x + k) x' (S - 96) 737372 HHx AM1 K0 ENT FRSc E10 E11 AO V8 ACC1 HD1 eq_refl SHB1).
  intros fx2 R2 M2 model2 LK2 Aw2 RP2 VS2 KEPT2 HP2 MRT2 ILK2 IAW2 AM2 HH2.
  change (PMSPA.pm_scr 0) with 12288 in HP2.
  assert (WIN : forall rg, In rg (@nil L5.range) -> exists q m, In (q, m) ((B, A) :: PGV8.v8_own x) /\ q <= fst rg /\ fst rg + snd rg <= q + m) by (intros rg []).
  pose proof (mem_ok_callee _ (PGV8.v8_own x) LK cr Aw M1 model1 M2 (S - 96) 12288 _ HH1 MO1 HP2 ltac:(lia) ltac:(lia) ltac:(lia) WIN) as MO2.
  pose proof (saves_callee _ LK cr Aw M1 model1 M2 (PGV8.v8_own x) (S - 96) 12288 _ HH1 MO1 HP2 ltac:(lia) ltac:(lia) ltac:(lia) WIN SV1) as SV2.
  assert (CK : forall a val, S - 96 <= a /\ a + 8 <= S -> L5.u64_at RSEGS M1v a val -> L5.u64_at RSEGS M2 a val).
  { intros a val Ha X. apply (cell_callee _ LK cr Aw M1 model1 M2 (PGV8.v8_own x) (S - 96) 12288 _ a val HH1 MO1 HP2 ltac:(lia) ltac:(lia) ltac:(lia) WIN); [left; lia|].
    apply VUP; [left; lia| exact X]. }
  apply (tail_I fx2 R2 M2 model2 LK2 Aw2 cr B A g').
  - rewrite (L5SAR.cs_of_preserved R1 R2 2%nat RP2) by inl. exact A2.
  - exact (kept0_pres R1 R2 KP1 RP2).
  - exact (stok_step model1 LK Aw model2 LK2 Aw2 SO1 AM2 MRT2 ILK2 IAW2).
  - exact MO2.
  - exact SV2.
  - exact HH2.
  - exact VS2.
  - apply CK; [lia| exact C1].
  - apply CK; [lia| exact C6].
  - apply CK; [lia| exact C4].
  - apply CK; [lia| exact C2].
  - exact PO.
Qed.

Lemma aacc_of_block (M : word -> option byte) u m p n : shadow_blk M u m -> u mod 8 = 0 -> 0 <= u -> u <= p -> p + n <= u + m -> aacc M p n.
Proof.
  intros [SZ SP] U8 U0 H1 H2 a Ha. clear - SZ SP U8 U0 H1 H2 Ha. unfold shadow_zero, byte_at in SZ, SP |- *.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (E : HeapIfaceA.S a = HeapIfaceA.S u + (a / 8 - u / 8)) by (unfold HeapIfaceA.S; Lia.lia).
  destruct (Z_lt_le_dec (a / 8 - u / 8) (m / 8)) as [LT|GE].
  - left. rewrite E. apply SZ. Lia.lia.
  - right. exists (m mod 8). assert (NZ : m mod 8 <> 0) by Lia.lia. assert (G : a / 8 - u / 8 = m / 8) by Lia.lia.
    split. rewrite E, G. apply SP. exact NZ. Lia.lia.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

(* [comment removed for export] *)
Lemma src_facts B A LK cr Aw M model :
  ri_inv HI (((B, A) :: PGV8.v8_own x) ++ LB) FF LK cr Aw M (vml_of model) -> mem_ok M ->
  (forall b n c, x = PGV8.V8Blk b n c -> PMSPA.accA M b n) -> PGV8.v8_size x <= A ->
  aacc M (PGV8.v8_data x) (PGV8.v8_size x) /\ app_rng ar (PGV8.v8_data x) (PGV8.v8_size x)
  /\ (forall i sp' scr', 0 <= i < PGV8.v8_size x -> aclient L ar (((B, A) :: PGV8.v8_own x) ++ LB) FF sp' scr' (PGV8.v8_data x + i))
  /\ L5.defined M (PGV8.v8_data x) (PGV8.v8_size x)
  /\ (B + PGV8.v8_size x <= PGV8.v8_data x \/ PGV8.v8_data x + PGV8.v8_size x <= B).
Proof using All.
  intros HH MO ACX HsA. destruct (nfacts _ LK cr Aw M model HH MO) as ((A16 & SLO & SHI & SPT & C0) & _ & BF).
  destruct (BF B A ltac:(left; reflexivity)) as (QB0 & QB1 & QB2 & QB4 & QB5 & QB6 & QBD).
  pose proof xr as XR. destruct (v8_case x) as [EX|(b & n & c & EX)]; rewrite EX in XR, HH, BF, HsA |- *; cbn [PGV8.v8_data PGV8.v8_size PGV8.v8_own] in *.
  - split; [intros a Ha; lia|]. split; [unfold app_rng, BIGSHADOW_LO, BIGSHADOW_HI; lia|]. split; [intros i sp' scr' Hi; lia|]. split; [intros i Hi; lia| right; lia].
  - destruct XR as (Hn & Hc & Hb & Hb16 & Hbc). destruct (BF b c ltac:(right; left; reflexivity)) as (Q0 & Q1 & Q2 & Q4 & Q5 & Q6 & QD). unfold nsh in Q5.
    destruct (PNAEK.own_facts L ar C HI HIok B A _ FF LK cr Aw M _ HH) as (BAp & _). pose proof (BAp b c ltac:(left; reflexivity)) as BNE.
    split; [exact (ACX b n c EX)|]. split; [unfold app_rng, BIGSHADOW_LO, BIGSHADOW_HI; lia|].
    split; [intros i sp' scr' Hi; unfold aclient, aclient_g; left; exists (b, c); split; [right; left; reflexivity| cbn [fst snd]; lia]|].
    split; [intros i Hi; apply QD; lia| lia].
Qed.

(* [comment removed for export] *)
Lemma sw_B (fx : FPState) R M model LK Aw cr B A g' w8 w9 w18 w19 :
  getr R (reg 2) = Z_to_bv 64 (S - 144) -> getr R (reg 8) = Z_to_bv 64 (S - 88) -> getr R (reg 9) = Z_to_bv 64 v ->
  getr R (reg 19) = Z_to_bv 64 2147450880 -> kept0 R ->
  stok model LK Aw -> mem_ok M -> saves M -> ssaves M w8 w9 w18 w19 -> 0 <= w8 < 2 ^ 64 -> 0 <= w9 < 2 ^ 64 -> 0 <= w18 < 2 ^ 64 -> 0 <= w19 < 2 ^ 64 ->
  ri_inv HI (((B, A) :: PGV8.v8_own x) ++ LB) FF LK cr Aw M (vml_of model) ->
  hdr M (PGV8.v8_data x) (PGV8.v8_data x + PGV8.v8_size x) (PGV8.v8_data x + PGV8.v8_cap x) ->
  sbuf M B (B + PGV8.v8_size x) ((B + PGV8.v8_size x) + k) (B + A) ->
  A <= 2 ^ 27 -> PGV8.v8_size x + k <= A -> shadow_blk M B A ->
  (forall b n c, x = PGV8.V8Blk b n c -> PMSPA.accA M b n) ->
  post_ok (PGV8.V8Blk B (PGV8.v8_size x + k) A) g' cr ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0xb4124 M model) K.
Proof using All.
  intros E2 E8 E9 E19 KP SO MO SV SSV Hw8 Hw9 Hw18 Hw19 HH HD SBF HA HnkA SHB ACX PO.
  destruct (nfacts _ LK cr Aw M model HH MO) as ((A16 & SLO & SHI & SPT & C0) & (O1 & O2 & O5 & ODEF) & BF). unfold nsh in O5.
  destruct (BF B A ltac:(left; reflexivity)) as (QB0 & QB1 & QB2 & QB4 & QB5 & QB6 & QBD). unfold nsh in QB5.
  destruct (vfacts _ LK cr Aw M model HH MO) as (X0 & X1 & X2 & XW & XZ & XWV & XSZ & XAV).
  pose proof SSV as (T8 & T16 & T24 & T32 & T40). pose proof HD as (W0 & W8 & W16). pose proof SBF as (B1 & B2 & B3 & B4).
  pose proof xnum as (XD & XS & XC & K27 & XSK & XDC).
  pose proof (PMAVGP.avsB_conc fx R (mrestrict (ahid Aw model) M) (fun j => match j with 2%nat => S - 96 | 37%nat => v | 40%nat => PGV8.v8_data x | 41%nat => PGV8.v8_size x
     | 44%nat => B | 48%nat => 737372 | 49%nat => w8 | 50%nat => w9 | 51%nat => w18 | 52%nat => w19 | _ => 0 end)) as PP.
  cbn beta iota in PP.
  replace (S - 96 - 48) with (S - 144) in PP by lia. replace (S - 96 + 8) with (S - 88) in PP by lia. replace (S - 96 - 8) with (S - 104) in PP by lia.
  replace (S - 96 - 16) with (S - 112) in PP by lia. replace (S - 96 - 24) with (S - 120) in PP by lia. replace (S - 96 - 32) with (S - 128) in PP by lia.
  replace (S - 96 - 40) with (S - 136) in PP by lia. replace (S - 96 + 16) with (S - 80) in PP by lia.
  L5SAR.feed PP ltac:(pfeed XW XSZ XAV).
  destruct PP as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & A1 & A10 & A11 & A12 & A18).
  apply (piece_ro fx fx1 R 0xb4124 R1 0x778cc _ M model cr LK Aw M1v HH SO MO MS1 MG1 FRZ1). intros model1 HH1 SO1.
  pose proof SO1 as (AM1 & MRT1 & ILK1 & IAW1).
  assert (KS2 : forall i, In i [2; 3; 4; 8; 9; 19; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R1 (reg i) = getr R (reg i)).
  { intros i Hi. apply KS1. clear - Hi. cbn in Hi. repeat (destruct Hi as [<-|Hi]; [inl|]). destruct Hi. }
  destruct (cstk _ LK cr Aw M model1 144 2560 HH1 MO ltac:(lia) ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(reflexivity)) as (STKc & _).
  destruct (src_facts B A LK cr Aw M model1 HH1 MO ACX ltac:(lia)) as (SAC & SAP & SCL & SDF & SNO).
  assert (E2' : getr R1 (reg 2) = Z_to_bv 64 (S - 144)) by (rewrite (KS2 2%nat) by inl; exact E2).
  assert (E4 : getr R1 (reg 4) = Z_to_bv 64 (hl_tp L)) by (rewrite (KS2 4%nat) by inl; rewrite (KP 4%nat) by inl; exact Rtp0).
  (* [comment removed for export] *)
  apply (memcpy_call27 fx1 R1 M model1 K _ FF LK cr Aw (S - 144) 737660 B (PGV8.v8_data x) (PGV8.v8_size x) HH1 AM1 K0 A1 ltac:(split; [lia| reflexivity]) E2' E4 A10 A11 A12 ltac:(lia) STKc).
  { apply (aacc_of_block M B A B (PGV8.v8_size x) SHB); [apply PMKA.mod16_8'; exact QB4| lia| lia| lia]. }
  { intros i Hi. unfold aclientw, aclient_g. left. exists (B, A). split; [left; reflexivity|]. cbn [fst snd]. lia. }
  { intros i Hi. apply QBD. lia. }
  { lia. } { lia. }
  { unfold app_rng, BIGSHADOW_LO, BIGSHADOW_HI. lia. }
  { exact SAC. } { lia. } { lia. } { exact SAP. }
  { intros i Hi. exact (SCL i (S - 144) 2560 Hi). }
  { exact SDF. } { exact SNO. }
  intros fx2 R2 M2 model2 RP2 DD2 HP2 MRT2 AM2 HH2.
  assert (WIN : forall rg, In rg [(B, PGV8.v8_size x)] -> exists q m, In (q, m) ((B, A) :: PGV8.v8_own x) /\ q <= fst rg /\ fst rg + snd rg <= q + m).
  { intros rg [<-|[]]. exists B, A. split; [left; reflexivity|]. cbn [fst snd]. lia. }
  pose proof (mem_ok_callee _ _ LK cr Aw M model1 M2 (S - 144) 2560 _ HH1 MO HP2 ltac:(lia) ltac:(lia) ltac:(lia) WIN) as MO2.
  pose proof (saves_callee _ LK cr Aw M model1 M2 _ (S - 144) 2560 _ HH1 MO HP2 ltac:(lia) ltac:(lia) ltac:(lia) WIN SV) as SV2.
  pose proof (hdr_callee _ LK cr Aw M model1 M2 _ (S - 144) 2560 _ _ _ _ HH1 MO HP2 ltac:(lia) ltac:(lia) ltac:(lia) WIN HD) as HD2.
  assert (CK : forall a val, S - 144 <= a /\ a + 8 <= S -> L5.u64_at RSEGS M a val -> L5.u64_at RSEGS M2 a val).
  { intros a val Ha X. apply (cell_callee _ LK cr Aw M model1 M2 _ (S - 144) 2560 _ a val HH1 MO HP2 ltac:(lia) ltac:(lia) ltac:(lia) WIN); [left; lia| exact X]. }
  assert (WA : PMKA.wapp [(B, PGV8.v8_size x)]) by (apply PMKA.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; lia| intros rg []]).
  pose proof (blksh_ek _ FF (S - 144) 2560 _ M M2 B A (proj1 HP2) WA ltac:(left; reflexivity) ltac:(lia) ltac:(lia)) as AGB.
  assert (CS2 : forall i, In i L5SAR.cs_all -> getr R2 (reg i) = getr R1 (reg i)) by (intros i Hi; exact (L5SAR.cs_of_preserved R1 R2 i RP2 Hi)).
  apply (sw_C fx2 R2 M2 model2 LK Aw cr B A g' w8 w9 w18 w19); try assumption.
  - rewrite CS2 by inl. exact E2'.
  - rewrite CS2 by inl. rewrite (KS2 8%nat) by inl. exact E8.
  - rewrite CS2 by inl. rewrite (KS2 9%nat) by inl. exact E9.
  - rewrite CS2 by inl. exact A18.
  - rewrite CS2 by inl. rewrite (KS2 19%nat) by inl. exact E19.
  - apply (kept0_pres R1 R2); [| exact RP2]. apply (kept0_of R R1 KP). intros i Hi. apply KS2. clear - Hi. cbn in Hi |- *. tauto.
  - exact (stok_step model1 LK Aw model2 LK Aw SO1 AM2 MRT2 (incl_refl _) (incl_refl _)).
  - split; [apply CK; [lia| exact T8]|]. split; [apply CK; [lia| exact T16]|]. split; [apply CK; [lia| exact T24]|]. split; [apply CK; [lia| exact T32]| apply CK; [lia| exact T40]].
  - split; [apply CK; [lia| exact B1]|]. split; [apply CK; [lia| exact B2]|]. split; [apply CK; [lia| exact B3]| apply CK; [lia| exact B4]].
  - apply (shblk_agree M M2 B A); [apply PMKA.mod16_8'; exact QB4| lia| exact AGB| exact SHB].
Qed.

(* [comment removed for export] *)
Lemma ri_swap B A LK cr Aw M V :
  ri_inv HI (((B, A) :: PGV8.v8_own x) ++ LB) FF LK cr Aw M V <-> ri_inv HI (PGV8.v8_own x ++ ((B, A) :: LB)) FF LK cr Aw M V.
Proof.
  assert (G : forall (l1 l2 : list (Z * Z)), (forall y, In y l1 <-> In y l2) -> (NoDup (map fst l1) -> NoDup (map fst l2)) ->
            ri_inv HI l1 FF LK cr Aw M V -> ri_inv HI l2 FF LK cr Aw M V).
  { intros l1 l2 IFF ND HH. pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ND1 & NDF & _).
    apply (HAJ.aior_perm _ _ _ _ _ HIok l1 l2 FF FF LK cr Aw M V HH IFF (ND ND1)); [intros f; tauto|].
    rewrite map_app in NDF. apply stdpp.list_relations.list.NoDup_app in NDF. exact (proj1 NDF). }
  destruct (v8_case x) as [EX|(b & n & c & EX)]; rewrite EX; cbn [PGV8.v8_own app]; [tauto|].
  assert (SW : forall (p q : Z * Z) l, NoDup (map fst (p :: q :: l)) -> NoDup (map fst (q :: p :: l))).
  { intros p q l ND. cbn [map] in *. apply stdpp.list_relations.list.NoDup_cons in ND as (N1 & ND). apply stdpp.list_relations.list.NoDup_cons in ND as (N2 & ND).
    apply stdpp.list_relations.list.NoDup_cons. split.
    - intros X. apply stdpp.list_basics.list.elem_of_cons in X as [X|X]; [apply N1; rewrite X; apply stdpp.list_basics.list.elem_of_cons; left; reflexivity| exact (N2 X)].
    - apply stdpp.list_relations.list.NoDup_cons. split; [| exact ND]. intros X. apply N1. apply stdpp.list_basics.list.elem_of_cons. right. exact X. }
  split; apply G; try apply SW; intros y; cbn [In]; tauto.
Qed.

(* [comment removed for export] *)
Lemma sw_A (fx : FPState) R M model LK Aw cr B A g' :
  getr R (reg 1) = Z_to_bv 64 737372 -> getr R (reg 2) = Z_to_bv 64 (S - 96) -> getr R (reg 10) = Z_to_bv 64 v -> getr R (reg 11) = Z_to_bv 64 (S - 88) -> kept0 R ->
  stok model LK Aw -> mem_ok M -> saves M ->
  ri_inv HI (((B, A) :: PGV8.v8_own x) ++ LB) FF LK cr Aw M (vml_of model) -> v8_atA M v x ->
  sbuf M B (B + PGV8.v8_size x) ((B + PGV8.v8_size x) + k) (B + A) ->
  A <= 2 ^ 27 -> PGV8.v8_size x + k <= A -> shadow_blk M B A ->
  post_ok (PGV8.V8Blk B (PGV8.v8_size x + k) A) g' cr ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0xb40f4 M model) K.
Proof using All.
  intros E1 E2 E10 E11 KP SO MO SV HH VS SBF HA HnkA SHB PO.
  destruct (nfacts _ LK cr Aw M model HH MO) as ((A16 & SLO & SHI & SPT & C0) & (O1 & O2 & O5 & ODEF) & BF). unfold nsh in O5.
  destruct (BF B A ltac:(left; reflexivity)) as (QB0 & QB1 & QB2 & QB4 & QB5 & QB6 & QBD). unfold nsh in QB5.
  destruct (vfacts _ LK cr Aw M model HH MO) as (X0 & X1 & X2 & XW & XZ & XWV & XSZ & XAV).
  pose proof SBF as (B1 & B2 & B3 & B4). pose proof xnum as (XD & XS & XC & K27 & XSK & XDC).
  pose proof (PMAVGP.avsA_conc fx R (mrestrict (ahid Aw model) M) (fun j => match j with 2%nat => S - 96 | 37%nat => v | _ => 0 end)) as PP.
  cbn beta iota in PP.
  replace (S - 96 - 48) with (S - 144) in PP by lia. replace (S - 96 + 8) with (S - 88) in PP by lia. replace (S - 96 - 8) with (S - 104) in PP by lia.
  replace (S - 96 - 16) with (S - 112) in PP by lia. replace (S - 96 - 24) with (S - 120) in PP by lia. replace (S - 96 - 32) with (S - 128) in PP by lia.
  replace (S - 96 - 40) with (S - 136) in PP by lia.
  L5SAR.feed PP ltac:(pfeed XW XSZ XAV).
  destruct PP as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & A1 & A2 & A8 & A9 & A11 & A19 & C40 & C32 & C24 & C16 & C8).
  assert (U1 : bv_unsigned (getr R (reg 1)) = 737372) by (rewrite E1; apply L5.unsigned_lit; lia).
  rewrite U1 in C8.
  apply (piece_step fx fx1 R 0xb40f4 R1 0xab098 _ M model cr LK Aw M1v (fun a => S - 144 <= a < S - 144 + 48) HH SO MO MS1 MG1 FRZ1); [intros a Pa; left; lia|].
  intros M1 model1 HH1 SO1 MO1 FR1 VUP AGS.
  pose proof (saves_piece _ LK cr Aw M model M1 (fun a => S - 144 <= a < S - 144 + 48) HH MO FR1 ltac:(intros i X; cbv beta in X; lia) SV) as SV1.
  destruct (nfacts _ LK cr Aw M1 model1 HH1 MO1) as (_ & (_ & _ & _ & ODEF1) & BF1).
  destruct (BF1 B A ltac:(left; reflexivity)) as (_ & _ & _ & _ & _ & _ & QBD1).
  pose proof MO1 as (_ & _ & _ & ACC1 & _). pose proof SO1 as (AM1 & MRT1 & ILK1 & IAW1).
  assert (KS2 : forall i, In i [3; 4; 10; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R1 (reg i) = getr R (reg i)).
  { intros i Hi. apply KS1. clear - Hi. cbn in Hi. repeat (destruct Hi as [<-|Hi]; [inl|]). destruct Hi. }
  assert (KP1 : kept0 R1) by (apply (kept0_of R R1 KP); intros i Hi; apply KS2; clear - Hi; cbn in Hi |- *; tauto).
  destruct (centry0 R1 _ LK cr Aw M1 model1 144 737572 HH1 MO1 KP1 A1 ltac:(split; [lia| reflexivity]) A2 ltac:(lia) ltac:(reflexivity)) as (ENT & FRSc).
  assert (VS1 : v8_atA M1 v x).
  { apply (v8_at_agree M M1 x VS ODEF1); [intros i Hi; apply FR1; lia| apply AGS; lia| lia| lia|].
    intros b n c EX. destruct (BF1 b c ltac:(rewrite EX; right; left; reflexivity)) as (Q0 & Q1 & Q2 & Q4 & Q5 & Q6 & QD). unfold nsh in Q5. split; [exact QD| apply AGS; lia]. }
  assert (SBF1 : sbuf M1 B (B + PGV8.v8_size x) ((B + PGV8.v8_size x) + k) (B + A)).
  { repeat split; (eapply (cell_piece M M1 _ _ _ FR1); [intros i Hi X; lia| lia| lia| eassumption]). }
  assert (SHB1 : shadow_blk M1 B A) by (apply (shblk_agree M M1 B A); [apply PMKA.mod16_8'; exact QB4| lia| apply AGS; lia| exact SHB]).
  pose proof (proj1 (ri_swap B A LK cr Aw M1 _) HH1) as HHx.
  pose proof ANND as AD'. unfold PNSAX.ann_delete_v8_spec in AD'.
  assert (E10' : getr R1 10%bv = Z_to_bv 64 v) by (rewrite L5K.rl10, (KS2 10%nat) by inl; exact E10).
  unfold PMSP.cfg.
  apply (AD' fx1 R1 M1 model1 K ((B, A) :: LB) FF LK Aw cr v x (S - 144) 737572 HHx AM1 K0 ENT FRSc E10' AO V8 ACC1 VS1).
  intros fx2 R2 M2 model2 LK2 Aw2 RP2 HD2 ACC2 ACX2 KEPT2 HP2 MRT2 ILK2 IAW2 AM2 HH2.
  change (PMSPA.pm_scr 0) with 12288 in HP2.
  pose proof (proj2 (ri_swap B A LK2 cr Aw2 M2 _) HH2) as HH2s.
  assert (WIN : forall rg, In rg (@nil L5.range) -> exists q m, In (q, m) ((B, A) :: PGV8.v8_own x) /\ q <= fst rg /\ fst rg + snd rg <= q + m) by (intros rg []).
  pose proof (mem_ok_callee _ [(B, A)] LK cr Aw M1 model1 M2 (S - 144) 12288 _ HH1 MO1 HP2 ltac:(lia) ltac:(lia) ltac:(lia) WIN) as MO2.
  pose proof (saves_callee _ LK cr Aw M1 model1 M2 [(B, A)] (S - 144) 12288 _ HH1 MO1 HP2 ltac:(lia) ltac:(lia) ltac:(lia) WIN SV1) as SV2.
  assert (CK : forall a val, S - 144 <= a /\ a + 8 <= S -> L5.u64_at RSEGS M1 a val -> L5.u64_at RSEGS M2 a val).
  { intros a val Ha X. apply (cell_callee _ LK cr Aw M1 model1 M2 [(B, A)] (S - 144) 12288 _ a val HH1 MO1 HP2 ltac:(lia) ltac:(lia) ltac:(lia) WIN); [left; lia| exact X]. }
  pose proof (blksh_ek _ FF (S - 144) 12288 _ M1 M2 B A (proj1 HP2) ltac:(intros rg []) ltac:(left; reflexivity) ltac:(lia) ltac:(lia)) as AGB.
  assert (CS2 : forall i, In i L5SAR.cs_all -> getr R2 (reg i) = getr R1 (reg i)) by (intros i Hi; exact (L5SAR.cs_of_preserved R1 R2 i RP2 Hi)).
  destruct SBF1 as (B1' & B2' & B3' & B4').
  apply (sw_B fx2 R2 M2 model2 LK2 Aw2 cr B A g' (bv_unsigned (getr R (reg 8))) (bv_unsigned (getr R (reg 9))) (bv_unsigned (getr R (reg 18))) (bv_unsigned (getr R (reg 19))));
    try apply bv_unsigned_in_range; try assumption.
  - rewrite CS2 by inl. exact A2.
  - rewrite CS2 by inl. exact A8.
  - rewrite CS2 by inl. exact A9.
  - rewrite CS2 by inl. exact A19.
  - exact (kept0_pres R1 R2 KP1 RP2).
  - exact (stok_step model1 LK Aw model2 LK2 Aw2 SO1 AM2 MRT2 ILK2 IAW2).
  - split; [apply CK; [lia|]; apply VUP; [left; lia| exact C8]|]. split; [apply CK; [lia|]; apply VUP; [left; lia| exact C16]|].
    split; [apply CK; [lia|]; apply VUP; [left; lia| exact C24]|]. split; [apply CK; [lia|]; apply VUP; [left; lia| exact C32]| apply CK; [lia|]; apply VUP; [left; lia| exact C40]].
  - clear - HD2. destruct HD2 as (_ & HR). destruct (v8_case x) as [EX|(b & n & c & EX)]; rewrite EX in HR |- *; cbn [PGV8.v8_data PGV8.v8_size PGV8.v8_cap].
    + destruct HR as (U0 & U8 & U16). split; [exact U0|]. split; [exact U8| exact U16].
    + destruct HR as (U0 & U8 & U16 & _). split; [exact U0|]. split; [exact U8| exact U16].
  - split; [apply CK; [lia| exact B1']|]. split; [apply CK; [lia| exact B2']|]. split; [apply CK; [lia| exact B3']| apply CK; [lia| exact B4']].
  - apply (shblk_agree M1 M2 B A); [apply PMKA.mod16_8'; exact QB4| lia| exact AGB| exact SHB1].
  - intros b n c EX. pose proof xr as XR. rewrite EX in XR. apply (aacc_sub M2 b c); [exact (ACX2 b n c EX)| lia| lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma gr_H (fx : FPState) R M model LK Aw cr B A g' :
  getr R (reg 2) = Z_to_bv 64 (S - 96) -> getr R (reg 8) = Z_to_bv 64 v -> getr R (reg 9) = Z_to_bv 64 k ->
  getr R (reg 18) = Z_to_bv 64 ((B + PGV8.v8_size x) + k) -> getr R (reg 19) = Z_to_bv 64 (PGV8.v8_size x) ->
  getr R (reg 20) = Z_to_bv 64 ((v + 8) / 8 + 2147450880) -> kept0 R ->
  stok model LK Aw -> mem_ok M -> saves M -> L5.u64_at RSEGS M (S - 56) v ->
  ri_inv HI (((B, A) :: PGV8.v8_own x) ++ LB) FF LK cr Aw M (vml_of model) -> v8_atA M v x ->
  L5.u64_at RSEGS M (S - 88) B -> L5.u64_at RSEGS M (S - 80) (B + PGV8.v8_size x) -> L5.u64_at RSEGS M (S - 64) (B + A) ->
  1 <= A <= 2 ^ 27 -> PGV8.v8_size x + k <= A -> shadow_blk M B A ->
  post_ok (PGV8.V8Blk B (PGV8.v8_size x + k) A) g' cr ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0xb404c M model) K.
Proof using All.
  intros E2 E8 E9 E18 E19 E20 KP SO MO SV S56 HH VS B1 B2 B4 HA HnkA SHB PO.
  destruct (nfacts _ LK cr Aw M model HH MO) as ((A16 & SLO & SHI & SPT & C0) & (O1 & O2 & O5 & ODEF) & BF). unfold nsh in O5.
  destruct (BF B A ltac:(left; reflexivity)) as (QB0 & QB1 & QB2 & QB4 & QB5 & QB6 & QBD). unfold nsh in QB5.
  destruct (vfacts _ LK cr Aw M model HH MO) as (X0 & X1 & X2 & XW & XZ & XWV & XSZ & XAV).
  pose proof SV as (S8 & S16 & S24 & S32 & S40 & S48). pose proof xnum as (XD & XS & XC & K27 & XSK & XDC).
  assert (UB : forall i, 0 <= U i < 2 ^ 64) by (intros i; unfold U; apply bv_unsigned_in_range).
  pose proof (UB 1%nat) as UB1. pose proof (UB 8%nat) as UB8. pose proof (UB 9%nat) as UB9. pose proof (UB 18%nat) as UB18. pose proof (UB 19%nat) as UB19. pose proof (UB 20%nat) as UB20.
  LeanFeed.pfeed PP (PMAVGP.avaH_conc fx R (mrestrict (ahid Aw model) M) (fun j => match j with 2%nat => S | 37%nat => v | 41%nat => PGV8.v8_size x | 43%nat => k | 44%nat => B | 46%nat => A
     | 48%nat => U 1 | 49%nat => U 8 | 50%nat => U 9 | 51%nat => U 18 | 52%nat => U 19 | 53%nat => U 20 | _ => 0 end)) ltac:(pfeed XW XSZ XAV).
  destruct PP as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & A1 & A10 & A11 & C72).
  apply (piece_step fx fx1 R 0xb404c R1 0xb40f4 _ M model cr LK Aw M1v (fun a => S - 72 <= a < S - 72 + 8) HH SO MO MS1 MG1 FRZ1); [intros a Pa; left; lia|].
  intros M1 model1 HH1 SO1 MO1 FR1 VUP AGS.
  pose proof (saves_piece _ LK cr Aw M model M1 (fun a => S - 72 <= a < S - 72 + 8) HH MO FR1 ltac:(intros i X; cbv beta in X; lia) SV) as SV1.
  destruct (nfacts _ LK cr Aw M1 model1 HH1 MO1) as (_ & (_ & _ & _ & ODEF1) & BF1).
  assert (KS2 : forall i, In i [2; 3; 4; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R1 (reg i) = getr R (reg i)).
  { intros i Hi. apply KS1. clear - Hi. cbn in Hi. repeat (destruct Hi as [<-|Hi]; [inl|]). destruct Hi. }
  assert (KP1 : kept0 R1) by (apply (kept0_of R R1 KP); intros i Hi; apply KS2; clear - Hi; cbn in Hi |- *; tauto).
  assert (CK : forall a val, (forall i, a <= i < a + 8 -> ~ (S - 72 <= i < S - 72 + 8)) -> 0 <= a -> a + 8 <= 2 ^ 64 -> L5.u64_at RSEGS M a val -> L5.u64_at RSEGS M1 a val).
  { intros a val N H0 H1 X. exact (cell_piece M M1 _ a val FR1 N H0 H1 X). }
  assert (E2' : getr R1 (reg 2) = Z_to_bv 64 (S - 96)) by (rewrite (KS2 2%nat) by inl; exact E2).
  assert (VS1 : v8_atA M1 v x).
  { apply (v8_at_agree M M1 x VS ODEF1); [intros i Hi; apply FR1; lia| apply AGS; lia| lia| lia|].
    intros b n c EX. destruct (BF1 b c ltac:(rewrite EX; right; left; reflexivity)) as (Q0 & Q1 & Q2 & Q4 & Q5 & Q6 & QD). unfold nsh in Q5. split; [exact QD| apply AGS; lia]. }
  assert (SBF1 : sbuf M1 B (B + PGV8.v8_size x) ((B + PGV8.v8_size x) + k) (B + A)).
  { split; [apply CK; [intros i Hi; lia| lia| lia| exact B1]|]. split; [apply CK; [intros i Hi; lia| lia| lia| exact B2]|].
    split; [apply VUP; [left; lia| exact C72]| apply CK; [intros i Hi; lia| lia| lia| exact B4]]. }
  assert (SHB1 : shadow_blk M1 B A) by (apply (shblk_agree M M1 B A); [apply PMKA.mod16_8'; exact QB4| lia| apply AGS; lia| exact SHB]).
  exact (sw_A fx1 R1 M1 model1 LK Aw cr B A g' A1 E2' A10 A11 KP1 SO1 MO1 SV1 HH1 VS1 SBF1 ltac:(lia) HnkA SHB1 PO).
Qed.

(* [comment removed for export] *)
Lemma gr_G (fx : FPState) R M model LK Aw cr B A g' :
  getr R (reg 2) = Z_to_bv 64 (S - 96) -> getr R (reg 8) = Z_to_bv 64 v -> getr R (reg 9) = Z_to_bv 64 k -> getr R (reg 10) = Z_to_bv 64 B ->
  getr R (reg 18) = Z_to_bv 64 A -> getr R (reg 19) = Z_to_bv 64 (PGV8.v8_size x) ->
  getr R (reg 20) = Z_to_bv 64 ((v + 8) / 8 + 2147450880) -> kept0 R ->
  stok model LK Aw -> mem_ok M -> saves M -> L5.u64_at RSEGS M (S - 56) v ->
  ri_inv HI (((B, A) :: PGV8.v8_own x) ++ LB) FF LK cr Aw M (vml_of model) -> v8_atA M v x ->
  1 <= A <= 2 ^ 27 -> PGV8.v8_size x + k <= A -> shadow_blk M B A ->
  post_ok (PGV8.V8Blk B (PGV8.v8_size x + k) A) g' cr ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0xb3fe4 M model) K.
Proof using All.
  intros E2 E8 E9 E10 E18 E19 E20 KP SO MO SV S56 HH VS HA HnkA SHB PO.
  destruct (nfacts _ LK cr Aw M model HH MO) as ((A16 & SLO & SHI & SPT & C0) & (O1 & O2 & O5 & ODEF) & BF). unfold nsh in O5.
  destruct (BF B A ltac:(left; reflexivity)) as (QB0 & QB1 & QB2 & QB4 & QB5 & QB6 & QBD). unfold nsh in QB5.
  destruct (vfacts _ LK cr Aw M model HH MO) as (X0 & X1 & X2 & XW & XZ & XWV & XSZ & XAV).
  pose proof SV as (S8 & S16 & S24 & S32 & S40 & S48). pose proof xnum as (XD & XS & XC & K27 & XSK & XDC).
  assert (UB : forall i, 0 <= U i < 2 ^ 64) by (intros i; unfold U; apply bv_unsigned_in_range).
  pose proof (UB 1%nat) as UB1. pose proof (UB 8%nat) as UB8. pose proof (UB 9%nat) as UB9. pose proof (UB 18%nat) as UB18. pose proof (UB 19%nat) as UB19. pose proof (UB 20%nat) as UB20.
  LeanFeed.pfeed PP (PMAVGP.avaG_conc fx R (mrestrict (ahid Aw model) M) (fun j => match j with 2%nat => S | 37%nat => v | 41%nat => PGV8.v8_size x | 43%nat => k | 44%nat => B | 46%nat => A
     | 48%nat => U 1 | 49%nat => U 8 | 50%nat => U 9 | 51%nat => U 18 | 52%nat => U 19 | 53%nat => U 20 | _ => 0 end)) ltac:(pfeed XW XSZ XAV).
  destruct PP as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & A1 & A10 & A11 & A12 & A18 & C64 & C80 & C88).
  apply (piece_step fx fx1 R 0xb3fe4 R1 0x77d68 _ M model cr LK Aw M1v (fun a => S - 88 <= a < S - 88 + 32) HH SO MO MS1 MG1 FRZ1); [intros a Pa; left; lia|].
  intros M1 model1 HH1 SO1 MO1 FR1 VUP AGS.
  pose proof (saves_piece _ LK cr Aw M model M1 (fun a => S - 88 <= a < S - 88 + 32) HH MO FR1 ltac:(intros i X; cbv beta in X; lia) SV) as SV1.
  destruct (nfacts _ LK cr Aw M1 model1 HH1 MO1) as (_ & (_ & _ & _ & ODEF1) & BF1).
  destruct (BF1 B A ltac:(left; reflexivity)) as (_ & _ & _ & _ & _ & _ & QBD1).
  pose proof SO1 as (AM1 & MRT1 & ILK1 & IAW1).
  assert (KS2 : forall i, In i [2; 3; 4; 8; 9; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R1 (reg i) = getr R (reg i)).
  { intros i Hi. apply KS1. clear - Hi. cbn in Hi. repeat (destruct Hi as [<-|Hi]; [inl|]). destruct Hi. }
  assert (KP1 : kept0 R1) by (apply (kept0_of R R1 KP); intros i Hi; apply KS2; clear - Hi; cbn in Hi |- *; tauto).
  assert (E2' : getr R1 (reg 2) = Z_to_bv 64 (S - 96)) by (rewrite (KS2 2%nat) by inl; exact E2).
  assert (E4 : getr R1 (reg 4) = Z_to_bv 64 (hl_tp L)) by (rewrite (KS2 4%nat) by inl; rewrite (KP 4%nat) by inl; exact Rtp0).
  assert (VS1 : v8_atA M1 v x).
  { apply (v8_at_agree M M1 x VS ODEF1); [intros i Hi; apply FR1; lia| apply AGS; lia| lia| lia|].
    intros b n c EX. destruct (BF1 b c ltac:(rewrite EX; right; left; reflexivity)) as (Q0 & Q1 & Q2 & Q4 & Q5 & Q6 & QD). unfold nsh in Q5. split; [exact QD| apply AGS; lia]. }
  assert (SHB1 : shadow_blk M1 B A) by (apply (shblk_agree M M1 B A); [apply PMKA.mod16_8'; exact QB4| lia| apply AGS; lia| exact SHB]).
  assert (S56' : L5.u64_at RSEGS M1 (S - 56) v) by (apply (cell_piece M M1 _ _ _ FR1); [intros i Hi X; lia| lia| lia| exact S56]).
  destruct (cstk _ LK cr Aw M1 model1 96 2560 HH1 MO1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(reflexivity)) as (STKc & _).
  (* [comment removed for export] *)
  apply (memset_call27 fx1 R1 M1 model1 K _ FF LK cr Aw (S - 96) 737356 (PGV8.v8_size x + B) 0 k HH1 AM1 K0 A1 ltac:(split; [lia| reflexivity]) E2' E4 A10 A11 A12 ltac:(lia) STKc).
  { apply (aacc_of_block M1 B A _ k SHB1); [apply PMKA.mod16_8'; exact QB4| lia| lia| lia]. }
  { intros i Hi. unfold aclientw, aclient_g. left. exists (B, A). split; [left; reflexivity|]. cbn [fst snd]. lia. }
  { intros i Hi. replace (PGV8.v8_size x + B + i) with (B + (PGV8.v8_size x + i)) by lia. apply QBD1. lia. }
  { lia. } { lia. }
  { unfold app_rng, BIGSHADOW_LO, BIGSHADOW_HI. lia. }
  intros fx2 R2 M2 model2 RP2 DD2 HP2 MRT2 AM2 HH2.
  assert (WIN : forall rg, In rg [(PGV8.v8_size x + B, k)] -> exists q m, In (q, m) ((B, A) :: PGV8.v8_own x) /\ q <= fst rg /\ fst rg + snd rg <= q + m).
  { intros rg [<-|[]]. exists B, A. split; [left; reflexivity|]. cbn [fst snd]. lia. }
  pose proof (mem_ok_callee _ _ LK cr Aw M1 model1 M2 (S - 96) 2560 _ HH1 MO1 HP2 ltac:(lia) ltac:(lia) ltac:(lia) WIN) as MO2.
  pose proof (saves_callee _ LK cr Aw M1 model1 M2 _ (S - 96) 2560 _ HH1 MO1 HP2 ltac:(lia) ltac:(lia) ltac:(lia) WIN SV1) as SV2.
  assert (CK : forall a val, S - 96 <= a /\ a + 8 <= S -> L5.u64_at RSEGS M1 a val -> L5.u64_at RSEGS M2 a val).
  { intros a val Ha X. apply (cell_callee _ LK cr Aw M1 model1 M2 _ (S - 96) 2560 _ a val HH1 MO1 HP2 ltac:(lia) ltac:(lia) ltac:(lia) WIN); [left; lia| exact X]. }
  assert (WA : PMKA.wapp [(PGV8.v8_size x + B, k)]) by (apply PMKA.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; lia| intros rg []]).
  pose proof HP2 as (EK2 & _).
  pose proof (blksh_ek _ FF (S - 96) 2560 _ M1 M2 B A EK2 WA ltac:(left; reflexivity) ltac:(lia) ltac:(lia)) as AGB.
  assert (CS2 : forall i, In i L5SAR.cs_all -> getr R2 (reg i) = getr R1 (reg i)) by (intros i Hi; exact (L5SAR.cs_of_preserved R1 R2 i RP2 Hi)).
  destruct (nfacts _ LK cr Aw M2 model2 HH2 MO2) as (_ & (_ & _ & _ & ODEF2) & BF2).
  assert (VS2 : v8_atA M2 v x).
  { apply (v8_at_agree M1 M2 x VS1 ODEF2); [| | lia| lia|].
    - apply (obj_ek _ FF (S - 96) 2560 _ M1 M2 v 24 v 24 EK2 AO V8); [lia| lia| lia| lia|].
      intros i Hi rg [<-|[]] X. unfold L5.in_rng in X. cbn [fst snd] in X. destruct (BF1 B A ltac:(left; reflexivity)) as (_ & _ & _ & _ & _ & Q6 & _). lia.
    - apply (objsh_ek _ FF (S - 96) 2560 _ M1 M2 v 24 EK2 WA AO); lia.
    - intros b n c EX. destruct (BF2 b c ltac:(rewrite EX; right; left; reflexivity)) as (Q0 & Q1 & Q2 & Q4 & Q5 & Q6 & QD). unfold nsh in Q5. split; [exact QD|].
      apply (blksh_ek _ FF (S - 96) 2560 _ M1 M2 b c EK2 WA ltac:(rewrite EX; right; left; reflexivity)); lia. }
  assert (R2_2 : getr R2 (reg 2) = Z_to_bv 64 (S - 96)) by (rewrite CS2 by inl; exact E2').
  assert (R2_8 : getr R2 (reg 8) = Z_to_bv 64 v) by (rewrite CS2 by inl; rewrite (KS2 8%nat) by inl; exact E8).
  assert (R2_9 : getr R2 (reg 9) = Z_to_bv 64 k) by (rewrite CS2 by inl; rewrite (KS2 9%nat) by inl; exact E9).
  assert (R2_18 : getr R2 (reg 18) = Z_to_bv 64 ((B + PGV8.v8_size x) + k)) by (rewrite CS2 by inl; rewrite A18; f_equal; lia).
  assert (R2_19 : getr R2 (reg 19) = Z_to_bv 64 (PGV8.v8_size x)) by (rewrite CS2 by inl; rewrite (KS2 19%nat) by inl; exact E19).
  assert (R2_20 : getr R2 (reg 20) = Z_to_bv 64 ((v + 8) / 8 + 2147450880)) by (rewrite CS2 by inl; rewrite (KS2 20%nat) by inl; exact E20).
  assert (B1 : L5.u64_at RSEGS M2 (S - 88) B) by (apply CK; [lia|]; apply VUP; [left; lia| exact C88]).
  assert (B2 : L5.u64_at RSEGS M2 (S - 80) (B + PGV8.v8_size x)) by (apply CK; [lia|]; apply VUP; [left; lia|]; replace (B + PGV8.v8_size x) with (PGV8.v8_size x + B) by lia; exact C80).
  assert (B4 : L5.u64_at RSEGS M2 (S - 64) (B + A)) by (apply CK; [lia|]; apply VUP; [left; lia| exact C64]).
  assert (SHB2 : shadow_blk M2 B A) by (apply (shblk_agree M1 M2 B A); [apply PMKA.mod16_8'; exact QB4| lia| exact AGB| exact SHB1]).
  assert (S56'' : L5.u64_at RSEGS M2 (S - 56) v) by (apply CK; [lia| exact S56']).
  exact (gr_H fx2 R2 M2 model2 LK Aw cr B A g' R2_2 R2_8 R2_9 R2_18 R2_19 R2_20 (kept0_pres R1 R2 KP1 RP2)
           (stok_step model1 LK Aw model2 LK Aw SO1 AM2 MRT2 (incl_refl _) (incl_refl _)) MO2 SV2 S56'' HH2 VS2 B1 B2 B4 HA HnkA SHB2 PO).
Qed.

(* [comment removed for export] *)
Lemma gr_new (fx : FPState) R M model LK Aw A :
  getr R (reg 1) = Z_to_bv 64 737252 -> getr R (reg 2) = Z_to_bv 64 (S - 96) -> getr R (reg 8) = Z_to_bv 64 v -> getr R (reg 9) = Z_to_bv 64 k -> getr R (reg 10) = Z_to_bv 64 A ->
  getr R (reg 18) = Z_to_bv 64 A -> getr R (reg 19) = Z_to_bv 64 (PGV8.v8_size x) ->
  getr R (reg 20) = Z_to_bv 64 ((v + 8) / 8 + 2147450880) -> kept0 R ->
  stok model LK Aw -> mem_ok M -> saves M -> L5.u64_at RSEGS M (S - 56) v ->
  ri_inv HI (PGV8.v8_own x ++ LB) FF LK cr0 Aw M (vml_of model) -> v8_atA M v x ->
  A = Z.max (2 * PGV8.v8_cap x) (PGV8.v8_size x + k) -> PGV8.v8_cap x < PGV8.v8_size x + k ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0x12dd8c M model) K.
Proof using All.
  intros E1 E2 E8 E9 E10 E18 E19 E20 KP SO MO SV S56 HH VS EA GRW.
  pose proof xnum as (XD & XS & XC & K27 & XSK & XDC).
  assert (HA : 1 <= A <= 2 ^ 27).
  { unfold PGV8.v8_grow_ok in GROK. clear - GROK GRW EA XS Hk. lia. }
  assert (HnkA : PGV8.v8_size x + k <= A) by (clear - EA; lia).
  assert (H2c : 2 * PGV8.v8_cap x <= A) by (clear - EA; lia).
  destruct (nfacts _ LK cr0 Aw M model HH MO) as ((A16 & SLO & SHI & SPT & C0) & (O1 & O2 & O5 & ODEF) & BF). unfold nsh in O5.
  pose proof SO as (AM & MRT & ILK & IAW).
  destruct (cstk _ LK cr0 Aw M model 96 4112 HH MO ltac:(lia) ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(reflexivity)) as (STKc & _).
  pose proof OPN as ON. unfold PMA.opnew_spec, PMSPA.opnew_spec in ON. cbn [pa_opnew PMA.AD ADDR_A] in ON.
  assert (E10' : getr R 10%bv = Z_to_bv 64 A) by (rewrite L5K.rl10; exact E10).
  assert (E1' : getr R 1%bv = Z_to_bv 64 737252) by (rewrite L5K.rl1; exact E1).
  assert (E2' : getr R 2%bv = Z_to_bv 64 (S - 96)) by (rewrite L5K.rl2; exact E2).
  assert (E4' : getr R 4%bv = Z_to_bv 64 (hl_tp L)) by (rewrite L5K.rl4; rewrite (KP 4%nat) by inl; exact Rtp0).
  unfold PMSP.cfg.
  apply (ON fx R M model K _ FF LK Aw cr0 A (S - 96) 737252 HH AM K0 E10' ltac:(lia)).
  { exact (proj1 (grow_credit A 0 0 H2c HA)). }
  { exact E1'. } { split; [lia| reflexivity]. } { exact E2'. } { exact E4'. } { exact STKc. }
  intros fx2 R2 M2 model2 Aw2 B RB RP2 FRESH HP2 MRT2 IA2 AM2 HH2.
  unfold PMSPA.OPNEW_SCR, PMSPA.MALLOC_SCR in HP2. change (16 + 4096) with 4112 in HP2. rewrite L5K.rl10 in RB.
  destruct FRESH as (QR & QAP & QFA & QDEF & QSH).
  assert (WIN : forall rg, In rg (@nil L5.range) -> exists q m, In (q, m) (PGV8.v8_own x) /\ q <= fst rg /\ fst rg + snd rg <= q + m) by (intros rg []).
  pose proof (mem_ok_callee _ (PGV8.v8_own x) LK cr0 Aw M model M2 (S - 96) 4112 _ HH MO HP2 ltac:(lia) ltac:(lia) ltac:(lia) WIN) as MO2.
  pose proof (saves_callee _ LK cr0 Aw M model M2 (PGV8.v8_own x) (S - 96) 4112 _ HH MO HP2 ltac:(lia) ltac:(lia) ltac:(lia) WIN SV) as SV2.
  assert (S56' : L5.u64_at RSEGS M2 (S - 56) v).
  { apply (cell_callee _ LK cr0 Aw M model M2 (PGV8.v8_own x) (S - 96) 4112 _ _ _ HH MO HP2 ltac:(lia) ltac:(lia) ltac:(lia) WIN); [left; lia| exact S56]. }
  assert (HH2' : ri_inv HI (((B, A) :: PGV8.v8_own x) ++ LB) FF LK (adebit L cr0 A) Aw2 M2 (vml_of model2)) by exact HH2.
  pose proof HP2 as (EK2 & _).
  destruct (nfacts _ LK (adebit L cr0 A) Aw2 M2 model2 HH2' MO2) as (_ & (_ & _ & _ & ODEF2) & BF2).
  assert (VS2 : v8_atA M2 v x).
  { apply (v8_at_agree M M2 x VS ODEF2); [| | lia| lia|].
    - apply (obj_ek _ FF (S - 96) 4112 _ M M2 v 24 v 24 EK2 AO V8); [lia| lia| lia| lia| intros i Hi rg []].
    - apply (objsh_ek _ FF (S - 96) 4112 _ M M2 v 24 EK2 ltac:(intros rg []) AO); lia.
    - intros b n c EX. destruct (BF2 b c ltac:(rewrite EX; right; left; reflexivity)) as (Q0 & Q1 & Q2 & Q4 & Q5 & Q6 & QD). unfold nsh in Q5. split; [exact QD|].
      apply (blksh_ek _ FF (S - 96) 4112 _ M M2 b c EK2 ltac:(intros rg []) ltac:(rewrite EX; left; reflexivity)); lia. }
  assert (CS2 : forall i, In i L5SAR.cs_all -> getr R2 (reg i) = getr R (reg i)) by (intros i Hi; exact (L5SAR.cs_of_preserved R R2 i RP2 Hi)).
  destruct (grow_credit A B (PGV8.v8_size x + k) H2c HA) as (_ & CK' & OK').
  assert (PO : post_ok (PGV8.V8Blk B (PGV8.v8_size x + k) A) (g + 1) (adebit L cr0 A)).
  { unfold post_ok. cbn [PGV8.v8_size PGV8.v8_cap PGV8.v8_own]. split; [reflexivity|]. split; [exact OK'|]. split; [clear - H2c XS; lia|].
    split; [intros X; exfalso; clear - X GRW; lia|]. split; [right; exact EA| exact CK']. }
  assert (R2_2 : getr R2 (reg 2) = Z_to_bv 64 (S - 96)) by (rewrite CS2 by inl; exact E2).
  assert (R2_8 : getr R2 (reg 8) = Z_to_bv 64 v) by (rewrite CS2 by inl; exact E8).
  assert (R2_9 : getr R2 (reg 9) = Z_to_bv 64 k) by (rewrite CS2 by inl; exact E9).
  assert (R2_18 : getr R2 (reg 18) = Z_to_bv 64 A) by (rewrite CS2 by inl; exact E18).
  assert (R2_19 : getr R2 (reg 19) = Z_to_bv 64 (PGV8.v8_size x)) by (rewrite CS2 by inl; exact E19).
  assert (R2_20 : getr R2 (reg 20) = Z_to_bv 64 ((v + 8) / 8 + 2147450880)) by (rewrite CS2 by inl; exact E20).
  exact (gr_G fx2 R2 M2 model2 LK Aw2 (adebit L cr0 A) B A (g + 1) R2_2 R2_8 R2_9 RB R2_18 R2_19 R2_20 (kept0_pres R R2 KP RP2)
           (stok_step model LK Aw model2 LK Aw2 SO AM2 MRT2 (incl_refl _) IA2) MO2 SV2 S56' HH2' VS2 HA HnkA QSH PO).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Hypothesis Ra0 : getr R0 (reg 10) = Z_to_bv 64 v.
Hypothesis Ra1 : getr R0 (reg 11) = Z_to_bv 64 k.
Hypothesis AM0 : L5CA.amodel_ok Aw0 model0.
Hypothesis STK0 : L5CA.astk ar M0 S 14336.
Hypothesis STKSH0 : shadow_zero M0 (S - 14336) 1792.

Lemma room_mod n c : 0 <= n <= c -> c <= 2 ^ 27 -> ((18446744073709551615 * n) mod 2 ^ 64 + c) mod 2 ^ 64 = c - n.
Proof.
  intros H1 H2. rewrite Zplus_mod_idemp_l. replace (18446744073709551615 * n + c) with ((c - n) + n * 2 ^ 64) by lia.
  rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
Lemma model_rt_refl (m : Model) : model_rt m m.
Proof. destruct m; reflexivity. Qed.
Lemma stok0 : stok model0 LK0 Aw0.
Proof using All. split; [exact AM0|]. split; [apply model_rt_refl|]. split; apply incl_refl. Qed.
Lemma mem_ok0 : mem_ok M0.
Proof using All.
  split; [intros a _; reflexivity|]. split; [intros a _ _ X; exact X|]. split; [exact STK0|]. split; [destruct VS0 as (_ & X & _); exact X| exact STKSH0].
Qed.

Lemma entry_ok (fx : FPState) : srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R0 0xb3f2c M0 model0) K.
Proof using All.
  pose proof stok0 as SO. pose proof mem_ok0 as MO. pose proof HH0 as HH.
  destruct (nfacts _ LK0 cr0 Aw0 M0 model0 HH MO) as ((A16 & SLO & SHI & SPT & C0) & (O1 & O2 & O5 & ODEF) & BF). unfold nsh in O5.
  destruct (vfacts _ LK0 cr0 Aw0 M0 model0 HH MO) as (X0 & X1 & X2 & XW & XZ & XWV & XSZ & XAV).
  pose proof xnum as (XD & XS & XC & K27 & XSK & XDC). pose proof xr as XR.
  assert (KPR : forall R1 (KS : list nat), (forall i, In i KS -> getr R1 (reg i) = getr R0 (reg i)) ->
                (forall i, In i [3; 4; 21; 22; 23; 24; 25; 26; 27]%nat -> In i KS) -> kept0 R1).
  { intros R1 KS KS1 SUB i Hi. exact (KS1 i (SUB i Hi)). }
  assert (SVP : forall (M1v M1 : word -> option byte),
      (forall a val, (S - 14336 <= a /\ a + 8 <= S) \/ (v <= a /\ a + 8 <= v + 24) -> L5.u64_at RSEGS M1v a val -> L5.u64_at RSEGS M1 a val) ->
      L5.u64_at RSEGS M1v (S - 48) (bv_unsigned (getr R0 (reg 20))) -> L5.u64_at RSEGS M1v (S - 40) (bv_unsigned (getr R0 (reg 19))) ->
      L5.u64_at RSEGS M1v (S - 32) (bv_unsigned (getr R0 (reg 18))) -> L5.u64_at RSEGS M1v (S - 24) (bv_unsigned (getr R0 (reg 9))) ->
      L5.u64_at RSEGS M1v (S - 16) (bv_unsigned (getr R0 (reg 8))) -> L5.u64_at RSEGS M1v (S - 8) (bv_unsigned (getr R0 (reg 1))) -> saves M1).
  { intros M1v M1 VUP C48 C40 C32 C24 C16 C8. unfold saves, U. repeat split; (apply VUP; [left; lia| assumption]). }
  assert (VSP : forall (M1 : word -> option byte) model1,
      ri_inv HI (PGV8.v8_own x ++ LB) FF LK0 cr0 Aw0 M1 (vml_of model1) -> mem_ok M1 ->
      (forall a, 0 <= a < 2 ^ 64 -> ~ (S - 96 <= a < S - 96 + 96) -> M1 (Z_to_bv 64 a) = M0 (Z_to_bv 64 a)) ->
      (forall a n, 0 <= a -> a + n <= 2 ^ 47 -> PMFA.agsh M0 M1 a n) -> v8_atA M1 v x).
  { intros M1 model1 HH1 MO1 FR1 AGS. destruct (nfacts _ LK0 cr0 Aw0 M1 model1 HH1 MO1) as (_ & (_ & _ & _ & ODEF1) & BF1).
    apply (v8_at_agree M0 M1 x VS0 ODEF1); [intros i Hi; apply FR1; lia| apply AGS; lia| lia| lia|].
    intros b n c EX. destruct (BF1 b c ltac:(rewrite EX; left; reflexivity)) as (Q0 & Q1 & Q2 & Q4 & Q5 & Q6 & QD). unfold nsh in Q5. split; [exact QD| apply AGS; lia]. }
  destruct (v8_case x) as [EX|(b & n & c & EX)].
  - (* [comment removed for export] *)
    pose proof VS0 as (_ & _ & VR). rewrite EX in VR, XS, XC. cbn [PGV8.v8_size PGV8.v8_cap] in XS, XC. destruct VR as (W0 & W8 & W16).
    LeanFeed.pfeed PP (PMAVGP.avaA0_conc fx R0 (mrestrict (ahid Aw0 model0) M0) (fun j => match j with 2%nat => S | 37%nat => v | 43%nat => k | _ => 0 end)) ltac:(pfeed XW XSZ XAV).
    destruct PP as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & A1 & A2 & A8 & A9 & A10 & A11 & A12 & A13 & A18 & A19 & A20 & C56 & C48 & C40 & C32 & C24 & C16 & C8).
    apply (piece_step fx fx1 R0 0xb3f2c R1 0x12dd8c _ M0 model0 cr0 LK0 Aw0 M1v (fun a => S - 96 <= a < S - 96 + 96) HH SO MO MS1 MG1 FRZ1); [intros a Pa; left; lia|].
    intros M1 model1 HH1 SO1 MO1 FR1 VUP AGS.
    assert (KP1 : kept0 R1) by (apply (KPR R1 _ KS1); intros i Hi; clear - Hi; cbn in Hi; repeat (destruct Hi as [<-|Hi]; [inl|]); destruct Hi).
    assert (E19 : getr R1 (reg 19) = Z_to_bv 64 (PGV8.v8_size x)) by (rewrite EX; exact A19).
    assert (EA : k = Z.max (2 * PGV8.v8_cap x) (PGV8.v8_size x + k)) by (rewrite EX; cbn [PGV8.v8_size PGV8.v8_cap]; lia).
    assert (GRW : PGV8.v8_cap x < PGV8.v8_size x + k) by (rewrite EX; cbn [PGV8.v8_size PGV8.v8_cap]; lia).
    exact (gr_new fx1 R1 M1 model1 LK0 Aw0 k A1 A2 A8 A9 A10 A18 E19 A20 KP1 SO1 MO1 (SVP M1v M1 VUP C48 C40 C32 C24 C16 C8) (VUP (S - 56) v ltac:(left; lia) C56)
             HH1 (VSP M1 model1 HH1 MO1 FR1 AGS) EA GRW).
  - (* [comment removed for export] *)
    pose proof VS0 as (_ & _ & VR). rewrite EX in VR, XS, XC, XR, XD, XSK. cbn [PGV8.v8_size PGV8.v8_cap PGV8.v8_data] in XS, XC, XD, XSK.
    destruct VR as (W0 & W8 & W16 & Hn & Hc & Hb & Hb16 & _).
    LeanFeed.pfeed PP (PMAVGP.avaA_conc fx R0 (mrestrict (ahid Aw0 model0) M0) (fun j => match j with 2%nat => S | 37%nat => v | 40%nat => b | 41%nat => n | 42%nat => c | 43%nat => k | _ => 0 end)) ltac:(pfeed XW XSZ XAV).
    rewrite (room_mod n c Hn ltac:(lia)) in PP.
    destruct PP as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & [(MS1 & KS1 & A1 & A2 & A8 & A9 & A12 & A13 & A18 & A19 & A20 & CND & C48 & C40 & C32 & C24 & C16 & C8)
       | [(MS1 & KS1 & A1 & A2 & A8 & A9 & A10 & A11 & A12 & A13 & A18 & A19 & A20 & C56 & CND2 & CND & C48 & C40 & C32 & C24 & C16 & C8)
         | (MS1 & KS1 & A1 & A2 & A8 & A9 & A10 & A11 & A12 & A13 & A18 & A19 & A20 & C56 & CND2 & CND & C48 & C40 & C32 & C24 & C16 & C8)]]).
    + (* [comment removed for export] *)
      apply (piece_step fx fx1 R0 0xb3f2c R1 0xb4260 _ M0 model0 cr0 LK0 Aw0 M1v (fun a => S - 96 <= a < S - 96 + 96) HH SO MO MS1 MG1 FRZ1); [intros a Pa; left; lia|].
      intros M1 model1 HH1 SO1 MO1 FR1 VUP AGS.
      assert (KP1 : kept0 R1) by (apply (KPR R1 _ KS1); intros i Hi; clear - Hi; cbn in Hi; repeat (destruct Hi as [<-|Hi]; [inl|]); destruct Hi).
      assert (E10 : getr R1 (reg 10) = Z_to_bv 64 v) by (rewrite (KS1 10%nat) by inl; exact Ra0).
      assert (E11 : getr R1 (reg 11) = Z_to_bv 64 k) by (rewrite (KS1 11%nat) by inl; exact Ra1).
      assert (HH1' : ri_inv HI ([(b, c)] ++ LB) FF LK0 cr0 Aw0 M1 (vml_of model1)) by (rewrite EX in HH1; exact HH1).
      exact (ip_inc fx1 R1 M1 model1 LK0 Aw0 b n c EX ltac:(lia) A1 A2 A8 A9 E10 E11 A18 A19 A20 KP1 SO1 MO1 (SVP M1v M1 VUP C48 C40 C32 C24 C16 C8) HH1' (VSP M1 model1 HH1 MO1 FR1 AGS)).
    + (* [comment removed for export] *)
      apply (piece_step fx fx1 R0 0xb3f2c R1 0x12dd8c _ M0 model0 cr0 LK0 Aw0 M1v (fun a => S - 96 <= a < S - 96 + 96) HH SO MO MS1 MG1 FRZ1); [intros a Pa; left; lia|].
      intros M1 model1 HH1 SO1 MO1 FR1 VUP AGS.
      assert (KP1 : kept0 R1) by (apply (KPR R1 _ KS1); intros i Hi; clear - Hi; cbn in Hi; repeat (destruct Hi as [<-|Hi]; [inl|]); destruct Hi).
      assert (E19 : getr R1 (reg 19) = Z_to_bv 64 (PGV8.v8_size x)) by (rewrite EX; exact A19).
      rewrite !Z.mod_small in CND2 by lia.
      assert (EA : 2 * c = Z.max (2 * PGV8.v8_cap x) (PGV8.v8_size x + k)) by (rewrite EX; cbn [PGV8.v8_size PGV8.v8_cap]; lia).
      assert (GRW : PGV8.v8_cap x < PGV8.v8_size x + k) by (rewrite EX; cbn [PGV8.v8_size PGV8.v8_cap]; lia).
      exact (gr_new fx1 R1 M1 model1 LK0 Aw0 (2 * c) A1 A2 A8 A9 A10 A18 E19 A20 KP1 SO1 MO1 (SVP M1v M1 VUP C48 C40 C32 C24 C16 C8) (VUP (S - 56) v ltac:(left; lia) C56)
               HH1 (VSP M1 model1 HH1 MO1 FR1 AGS) EA GRW).
    + (* [comment removed for export] *)
      apply (piece_step fx fx1 R0 0xb3f2c R1 0x12dd8c _ M0 model0 cr0 LK0 Aw0 M1v (fun a => S - 96 <= a < S - 96 + 96) HH SO MO MS1 MG1 FRZ1); [intros a Pa; left; lia|].
      intros M1 model1 HH1 SO1 MO1 FR1 VUP AGS.
      assert (KP1 : kept0 R1) by (apply (KPR R1 _ KS1); intros i Hi; clear - Hi; cbn in Hi; repeat (destruct Hi as [<-|Hi]; [inl|]); destruct Hi).
      assert (E19 : getr R1 (reg 19) = Z_to_bv 64 (PGV8.v8_size x)) by (rewrite EX; exact A19).
      rewrite !Z.mod_small in CND2 by lia.
      assert (EA : n + k = Z.max (2 * PGV8.v8_cap x) (PGV8.v8_size x + k)) by (rewrite EX; cbn [PGV8.v8_size PGV8.v8_cap]; lia).
      assert (GRW : PGV8.v8_cap x < PGV8.v8_size x + k) by (rewrite EX; cbn [PGV8.v8_size PGV8.v8_cap]; lia).
      exact (gr_new fx1 R1 M1 model1 LK0 Aw0 (n + k) A1 A2 A8 A9 A10 A18 E19 A20 KP1 SO1 MO1 (SVP M1v M1 VUP C48 C40 C32 C24 C16 C8) (VUP (S - 56) v ltac:(left; lia) C56)
               HH1 (VSP M1 model1 HH1 MO1 FR1 AGS) EA GRW).
Qed.

End Call.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem vu8_append_ok :
  PMA.opnew_spec L ar HI -> PMA.opdel_spec L ar HI ->
  PNSAX8.ann_increase_v8_spec RSEGS AD L ar HI 0xb4260 -> PNSAX8.ann_new_v8_spec RSEGS AD L ar HI 0xb431c -> PNSAX.ann_delete_v8_spec RSEGS AD L ar HI 0xab098 ->
  PGV8A.vu8_append_spec RSEGS AD L ar HI PNRA.FCB (PNL.pn_vu8_append PMA.AN).
Proof.
  intros OPN OPD ANNI ANNN ANND. unfold PGV8A.vu8_append_spec, PGV8A.vu8_grow_spec.
  intros fx R M model K LB FF LK Aw cr v a sp r g x HH AM K0 ENT FRM FRS A10 A11 AO V8 ACC VS OK Ha GOK CRL KONT.
  cbn [PNL.pn_vu8_append PMA.AN NADDR_A].
  destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH).
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp. rewrite L5K.rl10 in A10. rewrite L5SAR.r11 in A11.
  change (PMSPA.pm_scr 1) with 14336 in ASTK, STKSH. change (14336 / 8) with 1792 in STKSH.
  exact (entry_ok R M model K LB FF LK Aw cr v sp r g a x Rra RAok Rsp Rgp Rtp K0 FRS AO V8 OK (proj1 Ha) GOK CRL KONT OPN OPD ANNI ANNN ANND VS HH A10 A11 AM ASTK STKSH fx).
Qed.

End WithHeap.
End PGVAPA.

