(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality Permutation.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec CatExec CatSim SeqExec StreamSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceAEx HeapIfaceAEr IcptIfaceA L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA L5DefsA L5CoreAS8 L5StepARS8.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout PeLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PmModel PmModelFacts PmStatics PmStaticsA PmSpecs PmSpecsA PmSpecsAX PeSpecsAa PgV8 PgV8A PgV8KitA PnModel PnModelFacts PeSpecsAX PmModelFactsA PmStep PeStepA PeStepA2 PeAIss1 PeAEmbKit PeAReset1 PeASrcKit PeASrcReadK LibIfaceAB.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PeCLayout PeCLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PeCSink PeCSinkA PeASnkAnn PeASnkAnnG PeASnkAnnD PeASinkPushP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Ea0_code_af0a4_af0a8 Ea0_code_af24c_af250.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.asan Require Import L5CoreBS8.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PEASKP.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := Asan.M.loaded_segments.
Abbreviation AD := PeCLayoutA.CADDR_A.
Abbreviation EE := PeCLayoutA.EADDR_A.
Abbreviation mst fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)).
Abbreviation SBL := 2147450880.
Abbreviation PC0 := 0xaf02c.
Abbreviation ANNI := 0xaf310. Abbreviation ANND := 0xaa6ec. Abbreviation ANNN := 0xaf538.
Abbreviation OPNEW := 0x131ec0. Abbreviation OPDEL := 0xd4a60. Abbreviation MEMCPY := 0x78618.
Abbreviation RET_F := 0xaf0f4. Abbreviation RET_S := 0xaf29c. Abbreviation RA_SLOW := 0xaf0cc.

Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface) (P : PESKA.sink_policyA).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis EXT : HAJ.asan_ext_ok L ar SCFG HI PMA.EXT.
Hypothesis PO : PESKA.sink_policyA_ok L P.
Let LYa := PMA.ly_as0 L C LY.

Hypothesis OPNWP : PESKA.opnew_n_spec RSEGS AD L ar HI (PESKA.spa_nmax P) (PESKA.spa_cap P).
Hypothesis OPD : PMSPA.opdel_spec RSEGS AD L ar HI.
Hypothesis MEMCPYN : HAR.amemcpyN_spec_at L ar SCFG (fun _ => HI) (hl_asan_memcpy L).
Hypothesis NMAXI : PESKA.spa_nmax P <= 2 ^ 34.

Let COPYB : forall c, PESK.is_cap c -> 0 < PESK.cap_next c <= PESKA.spa_nmax P -> PESKA.spa_cap P (PESK.cap_next c) -> c <= 2 ^ 32 := PESKA.spao_copy L P PO.
Lemma NREQI_ge : 2 ^ 32 <= HAR.NREQI.
Proof. unfold HAR.NREQI. apply Z.leb_le. vm_compute. reflexivity. Qed.
Let ANNI_ok := PEASKANG.ann_increase_s_ok L ar C HI LY HIok EXT.
Let ANNN_ok := PEASKANG.ann_new_s_ok L ar C HI LY HIok EXT.
Let ANND_ok := PEASKAND.ann_delete_s_ok L ar C HI LY HIok EXT.
Let ANNDN_ok := PEASKAND.ann_delete_null_s_ok L ar C HI LY HIok.

Lemma memcpy_callN (fx : FPState) R M model K LB FF LK cr Aw (sp' r dst src n : Z) :
  ri_inv HI LB FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] ->
  getr R (reg 1) = Z_to_bv 64 r -> L5.ra_ok r -> getr R (reg 2) = Z_to_bv 64 sp' -> getr R (reg 4) = Z_to_bv 64 (hl_tp L) ->
  getr R (reg 10) = Z_to_bv 64 dst -> getr R (reg 11) = Z_to_bv 64 src -> getr R (reg 12) = Z_to_bv 64 n -> 0 <= n <= HAR.NREQI ->
  L5CA.astk ar M sp' 2560 ->
  aacc M dst n -> (forall i, 0 <= i < n -> aclientw L ar LB FF sp' 2560 (dst + i)) -> L5.defined M dst n -> 0 <= dst -> dst + n <= 2 ^ 47 -> app_rng ar dst n ->
  aacc M src n -> 0 <= src -> src + n <= 2 ^ 47 -> app_rng ar src n -> (forall i, 0 <= i < n -> aclient L ar LB FF sp' 2560 (src + i)) -> L5.defined M src n ->
  (dst + n <= src \/ src + n <= dst) ->
  (forall (fx' : FPState) R' M' model', regs_preserved R R' -> L5.defined M' dst n ->
      L5CA.ahpres L ar LB FF sp' 2560 [(dst, n)] M M' ->
      model_rt model model' -> L5CA.amodel_ok Aw model' -> ri_inv HI LB FF LK cr Aw M' (vml_of model') ->
      srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx' R' r M' model') K) ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R MEMCPY M model) K.
Proof.
  intros HH AM HK G1 RA G2 G4 G10 G11 G12 Hn ASTK ACD CLD DDEF D0 D1 APD ACS S0 S1 APS CLS SDEF0 NOV KONT.
  pose proof (MEMCPYN []) as HF.
  unfold HAR.amemN_pre, amem_post in HF. rewrite (L5A.aly_segs L C LYa), (L5A.aly_scr_mem L C LYa), (L5A.aly_memcpy L C LYa) in HF.
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
  - exact NOV.
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

Lemma blksh_ek LBc FF sp' scr' W' M M' q m :
  L5SAR.ek L ar LBc FF sp' scr' W' M M' -> PMKA.wapp W' -> In (q, m) LBc -> 0 <= q -> q + m <= 2 ^ 47 -> PMFA.agsh M M' q m.
Proof.
  intros EK WA Hin H0 H1 x Hx. pose proof (PMKA.S_in_shadow x ltac:(lia)) as SX.
  apply EK. split; [unfold BIGSHADOW_LO, BIGSHADOW_HI in SX; lia|]. split; [| exact (PMKA.wapp_outside_shadow W' (S x) WA SX)].
  unfold aclient, aclient_g. do 6 right. exists (q, m). split; [exact Hin|]. cbn [fst snd]. unfold in_shadow_of. split; apply PMKA.S_mono; lia.
Qed.

Lemma objsh_ek LBc FF sp' scr' W' M M' o n :
  L5SAR.ek L ar LBc FF sp' scr' W' M M' -> PMKA.wapp W' -> PMSPA.aobjA FF o n -> 0 <= o -> o + n <= 2 ^ 47 -> PMFA.agsh M M' o n.
Proof.
  intros EK WA AO H0 H1 x Hx. pose proof (PMKA.S_in_shadow x ltac:(lia)) as SX.
  apply EK. split; [unfold BIGSHADOW_LO, BIGSHADOW_HI in SX; lia|]. split; [| exact (PMKA.wapp_outside_shadow W' (S x) WA SX)].
  exact (PNAEK.frame_sh_client L ar FF o n x LBc sp' scr' AO Hx).
Qed.

Lemma obj_ek LBc FF sp' scr' W' M M' o n a m :
  L5SAR.ek L ar LBc FF sp' scr' W' M M' -> PMSPA.aobjA FF o n -> o mod 8 = 0 -> 0 <= o -> o + n <= 2 ^ 47 -> o <= a -> a + m <= o + n ->
  (forall i, a <= i < a + m -> L5.outside W' i) -> L5C.agree_on M M' a m.
Proof.
  intros EK AO O8 H0 H1 H2 H3 OW i Hi. apply EK. split; [lia|]. split; [| apply OW; exact Hi].
  apply (L5SAR.obj_client L ar LBc FF sp' scr' o n i (PMKA.aobj_of_aobjA FF o n AO O8)). lia.
Qed.

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

Lemma agsh_piece (M M1 : word -> option byte) (Wp : Z -> Prop) a n :
  (forall i, 0 <= i < 2 ^ 64 -> ~ Wp i -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i)) -> (forall i, Wp i -> ~ (BIGSHADOW_LO <= i < BIGSHADOW_HI)) ->
  0 <= a -> a + n <= 2 ^ 47 -> PMFA.agsh M M1 a n.
Proof.
  intros FR PS H0 H1 x Hx. pose proof (PMKA.S_in_shadow x ltac:(lia)) as SX. apply FR; [unfold BIGSHADOW_LO, BIGSHADOW_HI in SX; lia|].
  intros X. exact (PS _ X SX).
Qed.
Lemma aacc_sub (M : word -> option byte) a n a' n' : aacc M a n -> a <= a' -> a' + n' <= a + n -> aacc M a' n'.
Proof. intros AC H1 H2 y Hy. apply AC. clear - H1 H2 Hy. lia. Qed.

Lemma wid (w : word) : w = Z_to_bv 64 (bv_unsigned w). Proof. symmetry. apply Z_to_bv_bv_unsigned. Qed.
Lemma wrng (w : word) : 0 <= bv_unsigned w < 2 ^ 64.
Proof. pose proof (bv_unsigned_in_range 64 w) as X. change (bv_modulus 64) with (2 ^ 64) in X. exact X. Qed.

Lemma u8_at_of_defined (M : word -> option byte) a : 0 <= a < 2 ^ 64 -> M (Z_to_bv 64 a) <> None -> exists b, 0 <= b <= 255 /\ L5.u8_at RSEGS M a b.
Proof.
  intros Ha D. destruct (M (Z_to_bv 64 a)) as [w|] eqn:E; [| exfalso; exact (D eq_refl)].
  exists (bv_unsigned w). pose proof (bv_unsigned_in_range 8 w) as X. change (bv_modulus 8) with 256 in X.
  split; [lia|]. unfold L5.u8_at. cbn [rdn]. rewrite E. rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.

Section Call.
Hypothesis PMODE : PESKA.spa_mode P.
Variables (R0 : bvmap 5 word) (M0 : word -> option byte) (model0 : Model) (K : TSet) (LB : list (Z * Z)) (FF LK0 : list fframe) (Aw0 : list (Z * Z)) (cr0 : credit).
Variables (v pv S r : Z) (sk : PESK.sink).

Hypothesis HH0 : ri_inv HI (PESK.sink_own sk ++ LB) FF LK0 cr0 Aw0 M0 (vml_of model0).
Hypothesis AM0 : L5CA.amodel_ok Aw0 model0.
Hypothesis K0 : K [].
Hypothesis ENT0 : PMSPA.entryA AD L ar R0 M0 S r 0.
Hypothesis FRS : PMSPA.ffrsA FF S.
Hypothesis Ra0 : getr R0 10%bv = Z_to_bv 64 v.
Hypothesis Ra1 : getr R0 11%bv = Z_to_bv 64 pv.
Hypothesis SKA0 : PESKA.sink_atA RSEGS L ar P M0 v sk.
Hypothesis AO : PMSPA.aobjA FF v 24.
Hypothesis V8 : v mod 8 = 0.
Hypothesis PVOK : PESKA.pv_ok ar FF M0 S v pv.
Hypothesis GROW : PESK.sk_z sk = PESK.sk_c sk ->
        0 < PESK.cap_next (PESK.sk_c sk) <= PESKA.spa_nmax P
        /\ acredit_ok L (PESKA.spa_pot P (PESK.sk_c sk)) (PESK.cap_next (PESK.sk_c sk))
        /\ PMSP.credit_le (PESKA.spa_pot P (PESK.cap_next (PESK.sk_c sk))) (adebit L (PESKA.spa_pot P (PESK.sk_c sk)) (PESK.cap_next (PESK.sk_c sk))).
Hypothesis CRL0 : PMSP.credit_le (PESKA.spa_pot P (PESK.sk_c sk)) cr0.
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)) (cr' : credit) (b' : Z),
        regs_preserved R0 R' ->
        PESKA.sink_atA RSEGS L ar P M' v (PESK.sk_push sk b') ->
        L5CA.ahpres L ar LB FF S (PMSPA.pm_scr 0) [(v, 24)] M0 M' ->
        PMSP.credit_keep cr0 cr' (PESKA.spa_pot P (PESK.sk_c sk)) (PESKA.spa_pot P (PESK.sk_c (PESK.sk_push sk b'))) ->
        model_rt model0 model' -> incl LK' LK0 -> incl Aw0 Aw' -> L5CA.amodel_ok Aw' model' ->
        ri_inv HI (PESK.sink_own (PESK.sk_push sk b') ++ LB) FF LK' cr' Aw' M' (vml_of model') ->
        srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx' R' r M' model') K.

Lemma Rra0 : getr R0 (reg 1) = Z_to_bv 64 r. Proof. rewrite <- L5K.rl1. exact (proj1 ENT0). Qed.
Lemma RAok : L5.ra_ok r. Proof. exact (proj1 (proj2 ENT0)). Qed.
Lemma Rsp0 : getr R0 (reg 2) = Z_to_bv 64 S. Proof. rewrite <- L5K.rl2. exact (proj1 (proj2 (proj2 ENT0))). Qed.
Lemma Rgp0 : getr R0 (reg 3) = Z_to_bv 64 (pa_gp AD). Proof. rewrite <- L5K.rl3. exact (proj1 (proj2 (proj2 (proj2 ENT0)))). Qed.
Lemma Rtp0 : getr R0 (reg 4) = Z_to_bv 64 (hl_tp L). Proof. rewrite <- L5K.rl4. exact (proj1 (proj2 (proj2 (proj2 (proj2 ENT0))))). Qed.
Lemma ASTK0 : L5CA.astk ar M0 S 12288. Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 ENT0)))))). Qed.
Lemma STKSH0 : shadow_zero M0 (S - 12288) 1536. Proof. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 ENT0)))))). Qed.
Definition U (i : nat) : Z := bv_unsigned (getr R0 (reg i)).

Definition saves (M : word -> option byte) : Prop :=
  L5.u64_at RSEGS M (S - 8) (U 1) /\ L5.u64_at RSEGS M (S - 16) (U 8) /\ L5.u64_at RSEGS M (S - 24) (U 9) /\ L5.u64_at RSEGS M (S - 32) (U 18)
  /\ L5.u64_at RSEGS M (S - 40) (U 19) /\ L5.u64_at RSEGS M (S - 48) (U 20).

Definition kept0 (R : bvmap 5 word) : Prop := forall i, In i [3; 4; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R (reg i) = getr R0 (reg i).
Definition stok (model : Model) (LK : list fframe) (Aw : list (Z * Z)) : Prop :=
  L5CA.amodel_ok Aw model /\ model_rt model0 model /\ incl LK LK0 /\ incl Aw0 Aw.

Definition mem_ok (M : word -> option byte) : Prop :=
  L5SAR.ek L ar LB FF S 12288 [(v, 24)] M0 M /\ L5SAR.dk L ar LB FF S 12288 M0 M /\ L5CA.astk ar M S 12288 /\ PMSPA.accA M v 24
  /\ shadow_zero M (S - 12288) 1536.

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

Lemma nfacts HL LK cr Aw M model : ri_inv HI (HL ++ LB) FF LK cr Aw M (vml_of model) -> mem_ok M ->
  (S mod 16 = 0 /\ ahl_ceil ar + 4096 + 12288 <= S /\ S <= ar_sptop ar /\ 140735340871680 <= ar_sptop ar <= 2 ^ 47 /\ 0 <= ahl_ceil ar)
  /\ (6914048 <= v /\ v + 24 <= ahl_ceil ar /\ nsh v 24 /\ L5.defined M v 24)
  /\ (forall q m, In (q, m) (HL ++ LB) -> 4096 <= q /\ 0 < m /\ q + m <= ahl_ceil ar /\ q mod 16 = 0 /\ nsh q m /\ (q + m <= v \/ v + 24 <= q) /\ L5.defined M q m).
Proof.
  intros HH (_ & _ & STK & _). pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & _ & _ & _ & _ & _ & TOP & _).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LK cr Aw M model v 24 S 12288 HH (PMKA.aobj_of_aobjA FF v 24 AO V8) ltac:(lia) ltac:(reflexivity))
    as ((O1 & O2 & O3 & O4 & O5) & OBIG & ODEF & _).
  unfold app_mem, FS_BYTES, BIGSHADOW_LO, BIGSHADOW_HI in *.
  split; [split; [exact A16|]; lia|]. split; [split; [exact O1|]; split; [exact O2|]; split; [unfold nsh; lia| exact ODEF]|].
  intros q m Hin. destruct (PNAEK.blk_facts L ar C HI LY HIok _ FF LK cr Aw M _ q m HH Hin) as (Q0 & Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & QD & QF).
  split; [exact Q0|]. split; [exact Q1|]. split; [exact Q2|]. split; [exact Q4|]. split; [unfold nsh; lia|]. split; [|exact QD].
  destruct AO as (f & Hf & Y1 & Y2). specialize (QF f Hf). lia.
Qed.

Lemma vfacts HL LK cr Aw M model : ri_inv HI (HL ++ LB) FF LK cr Aw M (vml_of model) -> mem_ok M ->
  L5.img_clear (mrestrict (ahid Aw model) M) 1253376 1286144 /\ L5.u64_at RSEGS (mrestrict (ahid Aw model) M) 1317368 2147450880
  /\ L5.u32_at RSEGS (mrestrict (ahid Aw model) M) 1317376 1
  /\ (forall a n, S - 12288 <= a -> a + n <= S -> 0 <= n -> L5.writable RSEGS (mrestrict (ahid Aw model) M) a n)
  /\ L5KA.zeros_at (mrestrict (ahid Aw model) M) (v / 8 + 2147450880) 3 /\ L5.writable RSEGS (mrestrict (ahid Aw model) M) v 24
  /\ (forall a n, S - 12288 <= a -> a + 8 * n <= S -> a mod 8 = 0 -> 0 <= n -> L5KA.zeros_at (mrestrict (ahid Aw model) M) (a / 8 + 2147450880) n)
  /\ (forall a n, (S - 12288 <= a /\ a + n <= 2 ^ 47) \/ (v <= a /\ a + n <= v + 24) -> L5A.avis (ahid Aw model) a n).
Proof.
  intros HH MO. destruct (nfacts HL LK cr Aw M model HH MO) as ((A16 & SLO & SHI & SPT & C0) & (O1 & O2 & O5 & ODEF) & _).
  destruct MO as (_ & _ & STK & ACC & STKSH).
  pose proof (HAJ.aior_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as ST. rewrite (L5A.aly_segs L C LYa) in ST.
  pose proof (L5A.statics_facts L C M LYa ST) as (GOT & CSB & CUAR & _).
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ FF LK cr Aw M model HH) as (HOFF & VIS & VIMG & _ & _ & _ & _ & VSTSH).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LK cr Aw M model v 24 S 12288 HH (PMKA.aobj_of_aobjA FF v 24 AO V8) ltac:(lia) ltac:(reflexivity))
    as (_ & _ & _ & OVIS & _).
  set (H := ahid Aw model) in *.
  split; [apply L5A.img_clear_mrestrict; exact GOT|].
  split; [apply (proj2 (L5A.u64_at_vis H M 1317368 2147450880 (VIMG 1317368 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CSB|].
  split; [apply (proj2 (L5A.u32_at_vis H M 1317376 1 (VIMG 1317376 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CUAR|].
  split.
  { intros a n X1 X2 X3. apply (proj2 (L5A.writable_vis H M a n (VIS a n ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5SAR.astk_writable ar M S 12288 a n STK); lia. }
  split; [exact (PMKA.obj_shadow_vis L ar C HI LYa HIok _ FF LK cr Aw M model v 24 HH AO V8 ltac:(lia) ltac:(reflexivity) ACC)|].
  split.
  { apply (proj2 (L5A.writable_vis H M v 24 OVIS ltac:(lia) ltac:(lia))). apply (L5C.writable_of_defined RSEGS M v 24 ODEF); lia. }
  split.
  { intros a n X1 X2 X3 X4.
    assert (M8a : (S - 12288) mod 8 = 0) by (apply PMKA.mod16_8'; replace (S - 12288) with (S + (-768) * 16) by lia; rewrite Z_mod_plus_full; exact A16).
    pose proof (PMKA.shadow_zero_sub M (S - 12288) 1536 a n M8a X3 X1 ltac:(lia) X4 STKSH) as SZ.
    assert (AV : L5A.avis H (a / 8 + 2147450880) n).
    { apply VSTSH. intros i Hi. change (a / 8 + 2147450880) with (HeapIfaceA.S a). rewrite (PMFA.S_granule a i X3 ltac:(lia)).
      unfold in_shadow_of. split; apply PMKA.S_mono; lia. }
    apply (proj2 (L5A.zeros_at_vis H M (a / 8 + 2147450880) n AV)). intros i Hi. exact (SZ i Hi). }
  intros a n [(X1 & X2)|(X1 & X2)]; [apply VIS; lia| exact (L5A.avis_sub H v 24 a n OVIS X1 X2)].
Qed.

Lemma mem_ok_piece HL LK cr Aw M model M1 (Wp : Z -> Prop) :
  ri_inv HI (HL ++ LB) FF LK cr Aw M (vml_of model) -> mem_ok M -> mem_grows M M1 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Wp a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
  (forall a, Wp a -> (S - 12288 <= a < S) \/ (v <= a < v + 24)) -> mem_ok M1.
Proof.
  intros HH MO MG FR PW. destruct (nfacts HL LK cr Aw M model HH MO) as ((A16 & SLO & SHI & SPT & C0) & (O1 & O2 & O5 & ODEF) & _).
  destruct MO as (EK & DK & STK & ACC & STKSH).
  assert (PS : forall i, Wp i -> ~ (BIGSHADOW_LO <= i < BIGSHADOW_HI)).
  { intros i Pi X. unfold BIGSHADOW_LO, BIGSHADOW_HI, nsh in *. destruct (PW i Pi); lia. }
  split; [|split; [|split; [|split]]].
  - apply (L5SAR.ek_trans L ar LB FF S 12288 _ M0 M M1 EK). apply (L5SAR.ek_piece L ar LB FF S 12288 _ M M1 Wp FR). intros a Ha CA OW Pa.
    destruct (PW a Pa) as [X|X].
    + destruct (L5SAR.aclient_cases L ar C HI LYa HIok _ FF LK cr Aw M _ S 12288 a HH SPT (L5SAR.aclient_appb L ar LB HL FF S 12288 a CA)) as [(_ & Z2)|Z2]; [apply Z2; lia| lia].
    + apply (OW (v, 24)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia].
  - apply (L5SAR.dk_trans L ar LB FF S 12288 M0 M M1 DK). apply L5SAR.dk_grows. exact MG.
  - exact (L5SAR.astk_grows ar M M1 S 12288 STK MG).
  - apply (PMFA.accA_agree M M1 v 24); [| exact ACC]. apply (agsh_piece M M1 Wp v 24 FR PS); lia.
  - apply (shz_agree M M1 (S - 12288) 1536); [apply PMKA.mod16_8'; replace (S - 12288) with (S + (-768) * 16) by lia; rewrite Z_mod_plus_full; exact A16| lia| | exact STKSH].
    apply (agsh_piece M M1 Wp _ _ FR PS); lia.
Qed.

Lemma mem_ok_callee HL HL' LK cr Aw M model M' sp' scr' W' :
  ri_inv HI (HL ++ LB) FF LK cr Aw M (vml_of model) -> mem_ok M ->
  L5CA.ahpres L ar (HL' ++ LB) FF sp' scr' W' M M' -> S - 12288 <= sp' - scr' -> sp' <= S -> 0 <= scr' ->
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
  - apply (L5SAR.ek_trans L ar LB FF S 12288 _ M0 M M' EK). apply (L5SAR.ek_callee L ar LB HL' FF [] S 12288 sp' scr' _ W' M M' HP H1 H2).
    intros a CA _ rg Hrg X. destruct (WIN rg Hrg) as (q & m & Hin & X1 & X2).
    apply (PMARS1.own_not_aclient L ar C HI HIok HL LB FF LK cr Aw M _ q m a S 12288 HH Hin); [unfold L5.in_rng in X; lia| exact CA].
  - apply (L5SAR.dk_trans L ar LB FF S 12288 M0 M M' DK). exact (L5SAR.dk_callee L ar LB HL' FF [] S 12288 sp' scr' W' M M' HP H1 H2).
  - apply (PMKA.astk_after_ahpres L ar _ FF M M' S 12288 sp' scr' W' STK HP); lia.
  - apply (PMFA.accA_agree M M' v 24); [| exact ACC]. apply (objsh_ek _ FF sp' scr' W' M M' v 24 EKc WA AO); lia.
  - apply (PMKA.stksh_keepA L ar _ FF sp' scr' W' M M' EKc WA (S - 12288) 1536); [lia| lia| lia| | lia| exact STKSH].
    apply PMKA.mod16_8'; replace (S - 12288) with (S + (-768) * 16) by lia; rewrite Z_mod_plus_full; exact A16.
Qed.

Lemma cell_callee HL LK cr Aw M model M' HL' sp' scr' W' a val :
  ri_inv HI (HL ++ LB) FF LK cr Aw M (vml_of model) -> mem_ok M ->
  L5CA.ahpres L ar (HL' ++ LB) FF sp' scr' W' M M' -> S - 12288 <= sp' - scr' -> sp' <= S -> 0 <= scr' ->
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

Lemma wob HL LK cr Aw M model a : ri_inv HI (HL ++ LB) FF LK cr Aw M (vml_of model) -> mem_ok M ->
  (S - 12288 <= a < S) \/ (v <= a < v + 24) -> aclientw L ar (HL ++ LB) FF 0 0 a /\ ~ (0x10000 <= a < 0x698000).
Proof.
  intros HH MO Ha. destruct (nfacts HL LK cr Aw M model HH MO) as ((A16 & SLO & SHI & SPT & C0) & (O1 & O2 & O5 & ODEF) & _).
  split; [|lia]. unfold aclientw, aclient_g. destruct Ha as [X|X].
  - right; left. split; [lia| lia].
  - right; right; right; left. destruct AO as (f & Hf & Y1 & Y2). exists f. split; [exact Hf|]. clear - X Y1 Y2. lia.
Qed.

Lemma piece_step (fx fx1 : FPState) R (pc : Z) R1 (pc1 : Z) HL M model cr LK Aw (M1v : word -> option byte) (Wp : Z -> Prop) :
  ri_inv HI (HL ++ LB) FF LK cr Aw M (vml_of model) -> stok model LK Aw -> mem_ok M ->
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) (mrestrict (ahid Aw model) M) (seg_rom RSEGS)) (@mkst fx1 R1 (Z_to_bv 64 pc1) M1v (seg_rom RSEGS)) ->
  mem_grows (mrestrict (ahid Aw model) M) M1v ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Wp a -> M1v (Z_to_bv 64 a) = mrestrict (ahid Aw model) M (Z_to_bv 64 a)) ->
  (forall a, Wp a -> (S - 12288 <= a < S) \/ (v <= a < v + 24)) ->
  (forall M1 model1, ri_inv HI (HL ++ LB) FF LK cr Aw M1 (vml_of model1) -> stok model1 LK Aw -> mem_ok M1 ->
      (forall a, 0 <= a < 2 ^ 64 -> ~ Wp a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
      (forall a val, (S - 12288 <= a /\ a + 8 <= S) \/ (v <= a /\ a + 8 <= v + 24) -> L5.u64_at RSEGS M1v a val -> L5.u64_at RSEGS M1 a val) ->
      (forall a n, 0 <= a -> a + n <= 2 ^ 47 -> PMFA.agsh M M1 a n) ->
      srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx1 R1 pc1 M1 model1) K) ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R pc M model) K.
Proof.
  intros HH SO MO MS MG FZ PW KC. pose proof SO as (AM & MRT & ILK & IAW).
  destruct (nfacts HL LK cr Aw M model HH MO) as ((A16 & SLO & SHI & SPT & C0) & (O1 & O2 & O5 & ODEF) & _).
  destruct (vfacts HL LK cr Aw M model HH MO) as (_ & _ & _ & _ & _ & _ & _ & XAV).
  unfold PMSPA.cfg.
  apply (L5SAR.apiece L ar C HI LYa HIok _ FF LK cr Aw M model fx fx1 R pc R1 pc1 M1v Wp K HH AM MS MG FZ).
  { intros a Ha Pa. exact (wob HL LK cr Aw M model a HH MO (PW a Pa)). }
  intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
  apply (KC M1 model1 HH1).
  - split; [exact AM1|]. split; [eapply L5LZ.model_rt_trans; [exact MRT| exact MRT1]|]. split; [exact ILK| exact IAW].
  - exact (mem_ok_piece HL LK cr Aw M model M1 Wp HH MO MGM1 FR1 PW).
  - exact FR1.
  - intros a val Ha X. apply (proj1 (L5A.u64_at_vis (ahid Aw model) M1 a val (XAV a 8 ltac:(lia)) ltac:(lia) ltac:(lia))). rewrite VIS1. exact X.
  - intros a n Ha Hn. apply (agsh_piece M M1 Wp a n FR1); [| exact Ha| exact Hn].
    intros i Pi X. unfold BIGSHADOW_LO, BIGSHADOW_HI, nsh in *. destruct (PW i Pi); lia.
Qed.

Lemma mem_ok_pieceB HL LK cr Aw M model M1 (Wp : Z -> Prop) q m :
  ri_inv HI (HL ++ LB) FF LK cr Aw M (vml_of model) -> mem_ok M -> mem_grows M M1 -> In (q, m) HL ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Wp a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
  (forall a, Wp a -> (S - 12288 <= a < S) \/ (v <= a < v + 24) \/ (q <= a < q + m)) -> mem_ok M1.
Proof.
  intros HH MO MG HIN FR PW. destruct (nfacts HL LK cr Aw M model HH MO) as ((A16 & SLO & SHI & SPT & C0) & (O1 & O2 & O5 & ODEF) & BF).
  destruct (BF q m (in_or_app _ _ _ (or_introl HIN))) as (Q0 & Q1 & Q2 & Q4 & Q5 & Q6 & QD).
  destruct MO as (EK & DK & STK & ACC & STKSH).
  assert (PS : forall i, Wp i -> ~ (BIGSHADOW_LO <= i < BIGSHADOW_HI)).
  { intros i Pi X. unfold BIGSHADOW_LO, BIGSHADOW_HI, nsh in *. destruct (PW i Pi) as [Y|[Y|Y]]; lia. }
  split; [|split; [|split; [|split]]].
  - apply (L5SAR.ek_trans L ar LB FF S 12288 _ M0 M M1 EK). apply (L5SAR.ek_piece L ar LB FF S 12288 _ M M1 Wp FR). intros a Ha CA OW Pa.
    destruct (PW a Pa) as [X|[X|X]].
    + destruct (L5SAR.aclient_cases L ar C HI LYa HIok _ FF LK cr Aw M _ S 12288 a HH SPT (L5SAR.aclient_appb L ar LB HL FF S 12288 a CA)) as [(_ & Z2)|Z2]; [apply Z2; lia| lia].
    + apply (OW (v, 24)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia].
    + exact (PMARS1.own_not_aclient L ar C HI HIok HL LB FF LK cr Aw M _ q m a S 12288 HH HIN X CA).
  - apply (L5SAR.dk_trans L ar LB FF S 12288 M0 M M1 DK). apply L5SAR.dk_grows. exact MG.
  - exact (L5SAR.astk_grows ar M M1 S 12288 STK MG).
  - apply (PMFA.accA_agree M M1 v 24); [| exact ACC]. apply (agsh_piece M M1 Wp v 24 FR PS); lia.
  - apply (shz_agree M M1 (S - 12288) 1536); [apply PMKA.mod16_8'; replace (S - 12288) with (S + (-768) * 16) by lia; rewrite Z_mod_plus_full; exact A16| lia| | exact STKSH].
    apply (agsh_piece M M1 Wp _ _ FR PS); lia.
Qed.
Lemma wobB HL LK cr Aw M model a q m : ri_inv HI (HL ++ LB) FF LK cr Aw M (vml_of model) -> mem_ok M -> In (q, m) HL ->
  (S - 12288 <= a < S) \/ (v <= a < v + 24) \/ (q <= a < q + m) -> aclientw L ar (HL ++ LB) FF 0 0 a /\ ~ (0x10000 <= a < 0x698000).
Proof.
  intros HH MO HIN Ha. destruct Ha as [X|[X|X]]; [exact (wob HL LK cr Aw M model a HH MO (or_introl X))| exact (wob HL LK cr Aw M model a HH MO (or_intror X))|].
  assert (IN : In (q, m) (HL ++ LB)) by (apply in_or_app; left; exact HIN).
  destruct (PNAEK.blk_facts L ar C HI LY HIok _ FF LK cr Aw M _ q m HH IN) as (Q0 & Q1 & Q2 & Q3 & Q4 & QIMG & _).
  split; [| lia]. unfold aclientw, aclient_g. left. exists (q, m). split; [exact IN| cbn [fst snd]; lia].
Qed.
Lemma piece_stepB (fx fx1 : FPState) R (pc : Z) R1 (pc1 : Z) HL M model cr LK Aw (M1v : word -> option byte) (Wp : Z -> Prop) q m :
  ri_inv HI (HL ++ LB) FF LK cr Aw M (vml_of model) -> stok model LK Aw -> mem_ok M -> In (q, m) HL ->
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) (mrestrict (ahid Aw model) M) (seg_rom RSEGS)) (@mkst fx1 R1 (Z_to_bv 64 pc1) M1v (seg_rom RSEGS)) ->
  mem_grows (mrestrict (ahid Aw model) M) M1v ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Wp a -> M1v (Z_to_bv 64 a) = mrestrict (ahid Aw model) M (Z_to_bv 64 a)) ->
  (forall a, Wp a -> (S - 12288 <= a < S) \/ (v <= a < v + 24) \/ (q <= a < q + m)) ->
  (forall M1 model1, ri_inv HI (HL ++ LB) FF LK cr Aw M1 (vml_of model1) -> stok model1 LK Aw -> mem_ok M1 ->
      (forall a, 0 <= a < 2 ^ 64 -> ~ Wp a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
      (forall a val, (S - 12288 <= a /\ a + 8 <= S) \/ (v <= a /\ a + 8 <= v + 24) -> L5.u64_at RSEGS M1v a val -> L5.u64_at RSEGS M1 a val) ->
      (forall a n, 0 <= a -> a + n <= 2 ^ 47 -> PMFA.agsh M M1 a n) ->
      mrestrict (ahid Aw model) M1 = M1v ->
      srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx1 R1 pc1 M1 model1) K) ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R pc M model) K.
Proof.
  intros HH SO MO HIN MS MG FZ PW KC. pose proof SO as (AM & MRT & ILK & IAW).
  destruct (nfacts HL LK cr Aw M model HH MO) as ((A16 & SLO & SHI & SPT & C0) & (O1 & O2 & O5 & ODEF) & BF).
  destruct (BF q m (in_or_app _ _ _ (or_introl HIN))) as (Q0 & Q1 & Q2 & Q4 & Q5 & Q6 & QD).
  destruct (vfacts HL LK cr Aw M model HH MO) as (_ & _ & _ & _ & _ & _ & _ & XAV).
  unfold PMSPA.cfg.
  apply (L5SAR.apiece L ar C HI LYa HIok _ FF LK cr Aw M model fx fx1 R pc R1 pc1 M1v Wp K HH AM MS MG FZ).
  { intros a Ha Pa. exact (wobB HL LK cr Aw M model a q m HH MO HIN (PW a Pa)). }
  intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
  apply (KC M1 model1 HH1).
  - split; [exact AM1|]. split; [eapply L5LZ.model_rt_trans; [exact MRT| exact MRT1]|]. split; [exact ILK| exact IAW].
  - exact (mem_ok_pieceB HL LK cr Aw M model M1 Wp q m HH MO MGM1 HIN FR1 PW).
  - exact FR1.
  - intros a val Ha X. apply (proj1 (L5A.u64_at_vis (ahid Aw model) M1 a val (XAV a 8 ltac:(lia)) ltac:(lia) ltac:(lia))). rewrite VIS1. exact X.
  - intros a n Ha Hn. apply (agsh_piece M M1 Wp a n FR1); [| exact Ha| exact Hn].
    intros i Pi X. unfold BIGSHADOW_LO, BIGSHADOW_HI, nsh in *. destruct (PW i Pi) as [Y|[Y|Y]]; lia.
  - exact VIS1.
Qed.

Definition hdr (M : word -> option byte) (b e ce : Z) : Prop := L5.u64_at RSEGS M v b /\ L5.u64_at RSEGS M (v + 8) e /\ L5.u64_at RSEGS M (v + 16) ce.
Lemma saves_callee HL LK cr Aw M model M' HL' sp' scr' W' :
  ri_inv HI (HL ++ LB) FF LK cr Aw M (vml_of model) -> mem_ok M ->
  L5CA.ahpres L ar (HL' ++ LB) FF sp' scr' W' M M' -> S - 12288 <= sp' - scr' -> sp' <= S - 48 -> 0 <= scr' ->
  (forall rg, In rg W' -> exists q m, In (q, m) HL /\ q <= fst rg /\ fst rg + snd rg <= q + m) -> saves M -> saves M'.
Proof.
  intros HH MO HP H1 H2 H3 WIN (S8 & S16 & S24 & S32 & S40 & S48).
  repeat split; (eapply (cell_callee HL LK cr Aw M model M' HL' sp' scr' W' _ _ HH MO HP H1 ltac:(lia) H3 WIN); [left; lia| eassumption]).
Qed.
Lemma hdr_callee HL LK cr Aw M model M' HL' sp' scr' W' b e ce :
  ri_inv HI (HL ++ LB) FF LK cr Aw M (vml_of model) -> mem_ok M ->
  L5CA.ahpres L ar (HL' ++ LB) FF sp' scr' W' M M' -> S - 12288 <= sp' - scr' -> sp' <= S -> 0 <= scr' ->
  (forall rg, In rg W' -> exists q m, In (q, m) HL /\ q <= fst rg /\ fst rg + snd rg <= q + m) -> hdr M b e ce -> hdr M' b e ce.
Proof.
  intros HH MO HP H1 H2 H3 WIN (W0 & W8 & W16).
  repeat split; (eapply (cell_callee HL LK cr Aw M model M' HL' sp' scr' W' _ _ HH MO HP H1 H2 H3 WIN); [right; lia| eassumption]).
Qed.
Lemma cell_piece (M M1 : word -> option byte) (Wp : Z -> Prop) a val :
  (forall i, 0 <= i < 2 ^ 64 -> ~ Wp i -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i)) -> (forall i, a <= i < a + 8 -> ~ Wp i) -> 0 <= a -> a + 8 <= 2 ^ 64 ->
  L5.u64_at RSEGS M a val -> L5.u64_at RSEGS M1 a val.
Proof. intros FR NP H0 H1 X. apply (L5C.u64_at_agree RSEGS M M1); [intros i Hi; apply FR; [lia| apply NP; exact Hi]| exact H0| exact H1| exact X]. Qed.
Lemma saves_piece HL LK cr Aw M model (M1 : word -> option byte) (Wp : Z -> Prop) :
  ri_inv HI (HL ++ LB) FF LK cr Aw M (vml_of model) -> mem_ok M ->
  (forall i, 0 <= i < 2 ^ 64 -> ~ Wp i -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i)) -> (forall i, Wp i -> ~ (S - 48 <= i < S)) -> saves M -> saves M1.
Proof.
  intros HH MO FR NP (S8 & S16 & S24 & S32 & S40 & S48). destruct (nfacts HL LK cr Aw M model HH MO) as ((A16 & SLO & SHI & SPT & C0) & _).
  repeat split; (eapply (cell_piece M M1 Wp _ _ FR); [intros i Hi Pi; apply (NP i Pi); lia| lia| lia| eassumption]).
Qed.
Lemma hdr_piece HL LK cr Aw M model (M1 : word -> option byte) (Wp : Z -> Prop) b e ce :
  ri_inv HI (HL ++ LB) FF LK cr Aw M (vml_of model) -> mem_ok M ->
  (forall i, 0 <= i < 2 ^ 64 -> ~ Wp i -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i)) -> (forall i, Wp i -> ~ (v <= i < v + 24)) -> hdr M b e ce -> hdr M1 b e ce.
Proof.
  intros HH MO FR NP (W0 & W8 & W16). destruct (nfacts HL LK cr Aw M model HH MO) as ((A16 & SLO & SHI & SPT & C0) & (O1 & O2 & O5 & ODEF) & _).
  repeat split; (eapply (cell_piece M M1 Wp _ _ FR); [intros i Hi Pi; apply (NP i Pi); lia| lia| lia| eassumption]).
Qed.

Lemma cstk HL LK cr Aw M model fr scr' : ri_inv HI (HL ++ LB) FF LK cr Aw M (vml_of model) -> mem_ok M -> 0 <= fr -> 0 <= scr' -> fr + scr' <= 12288 -> fr mod 16 = 0 -> scr' mod 8 = 0 ->
  L5CA.astk ar M (S - fr) scr' /\ shadow_zero M (S - fr - scr') (scr' / 8).
Proof.
  intros HH MO H1 H2 H3 H4 H5. destruct (nfacts HL LK cr Aw M model HH MO) as ((A16 & SLO & SHI & SPT & C0) & _). destruct MO as (_ & _ & STK & _ & STKSH).
  assert (E16 : (S - fr) mod 16 = 0).
  { rewrite Zminus_mod, A16, H4. reflexivity. }
  split; [exact (L5SAR.astk_sub ar M M S 12288 fr scr' STK (fun _ Y => Y) H1 H2 H3 E16)|].
  assert (M8a : (S - 12288) mod 8 = 0) by (apply PMKA.mod16_8'; replace (S - 12288) with (S + (-768) * 16) by lia; rewrite Z_mod_plus_full; exact A16).
  assert (M8b : (S - fr - scr') mod 8 = 0).
  { rewrite Zminus_mod, H5, (PMKA.mod16_8' _ E16). reflexivity. }
  pose proof (Z.div_mod scr' 8 ltac:(lia)) as D. rewrite H5 in D.
  apply (PMKA.shadow_zero_sub M (S - 12288) 1536 (S - fr - scr') (scr' / 8) M8a M8b); [lia| lia| apply Z.div_pos; lia| exact STKSH].
Qed.

Lemma piece_ro (fx fx1 : FPState) R (pc : Z) R1 (pc1 : Z) HL M model cr LK Aw (M1v : word -> option byte) :
  ri_inv HI (HL ++ LB) FF LK cr Aw M (vml_of model) -> stok model LK Aw -> mem_ok M ->
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) (mrestrict (ahid Aw model) M) (seg_rom RSEGS)) (@mkst fx1 R1 (Z_to_bv 64 pc1) M1v (seg_rom RSEGS)) ->
  mem_grows (mrestrict (ahid Aw model) M) M1v ->
  (forall a, 0 <= a < 2 ^ 64 -> M1v (Z_to_bv 64 a) = mrestrict (ahid Aw model) M (Z_to_bv 64 a)) ->
  (forall model1, ri_inv HI (HL ++ LB) FF LK cr Aw M (vml_of model1) -> stok model1 LK Aw ->
      srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx1 R1 pc1 M model1) K) ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R pc M model) K.
Proof.
  intros HH SO MO MS MG FZ KC.
  apply (piece_step fx fx1 R pc R1 pc1 HL M model cr LK Aw M1v (fun _ => False) HH SO MO MS MG (fun a Ha _ => FZ a Ha)); [intros a []|].
  intros M1 model1 HH1 SO1 MO1 FR1 VUP AGS.
  assert (EQ1 : M1 = M).
  { apply functional_extensionality. intros a. pose proof (FR1 (bv_unsigned a) (bv_unsigned_in_range _ a) (fun X => X)) as E. rewrite Z_to_bv_bv_unsigned in E. exact E. }
  subst M1. exact (KC model1 HH1 SO1).
Qed.

Ltac pfeed XW XSZ XAV :=
  first [ assumption
        | lazymatch goal with
          | |- L5.u64_at _ (mrestrict ?H ?M) ?a ?val => apply (proj2 (L5A.u64_at_vis H M a val (XAV a 8 ltac:(lia)) ltac:(lia) ltac:(lia))); assumption
          | |- L5.u8_at _ (mrestrict ?H ?M) ?a ?val => apply (proj2 (L5A.u8_at_vis H M a val (XAV a 1 ltac:(lia)) ltac:(lia) ltac:(lia))); assumption
          | |- L5.writable _ _ _ _ => first [apply XW; lia | assumption]
          | |- L5KA.zeros_at _ _ _ => first [apply XSZ; lia | assumption]
          | |- PEASKPP.aligned _ _ => unfold PEASKPP.aligned; lia
          | |- _ => lia
          end ].
Lemma UB i : 0 <= U i < 2 ^ 64. Proof. unfold U. apply bv_unsigned_in_range. Qed.

Definition hidden (X : Prop) : Prop := X.
Ltac hide_disj := repeat match goal with H : ?A \/ ?B |- _ => change (A \/ B) with (hidden (A \/ B)) in H end.
Ltac unhide := unfold hidden in *.

Lemma sk_facts HL LK cr Aw M model k' : ri_inv HI (HL ++ LB) FF LK cr Aw M (vml_of model) -> mem_ok M -> PESKA.sink_atA RSEGS L ar P M v k' ->
  incl (PESK.sink_own k') HL ->
  0 <= PESK.sk_z k' <= PESK.sk_c k' /\ PESK.sk_c k' <= 2 ^ 34 /\ 0 <= PESK.sk_b k'
  /\ (PESK.sk_c k' = 0 -> PESK.sk_b k' = 0)
  /\ (0 < PESK.sk_c k' -> 4096 <= PESK.sk_b k' /\ PESK.sk_b k' + PESK.sk_c k' <= ahl_ceil ar /\ PESK.sk_b k' mod 16 = 0 /\ nsh (PESK.sk_b k') (PESK.sk_c k')
                          /\ (PESK.sk_b k' + PESK.sk_c k' <= 65536 \/ 0x698000 <= PESK.sk_b k') /\ (PESK.sk_b k' + PESK.sk_c k' <= v \/ v + 24 <= PESK.sk_b k')
                          /\ L5.defined M (PESK.sk_b k') (PESK.sk_c k') /\ In (PESK.sk_b k', PESK.sk_c k') (HL ++ LB)).
Proof using NMAXI HIok AO LY LYa V8.
  intros HH MO (_ & _ & _ & _ & _ & ZC & CAP & C0 & LIVE) INC. destruct (nfacts HL LK cr Aw M model HH MO) as (_ & _ & BF).
  split; [exact ZC|]. destruct (Z.eq_dec (PESK.sk_c k') 0) as [E0|NE].
  - split; [lia|]. split; [rewrite (C0 E0); lia|]. split; [exact C0|]. intros X; lia.
  - destruct (LIVE ltac:(lia)) as (_ & _ & _ & ABR & _ & LE). split; [lia|]. destruct ABR as (B4 & _). split; [lia|]. split; [exact C0|]. intros _.
    assert (IN : In (PESK.sk_b k', PESK.sk_c k') (HL ++ LB)).
    { apply in_or_app. left. apply INC. unfold PESK.sink_own. replace (PESK.sk_c k' =? 0) with false by (symmetry; apply Z.eqb_neq; lia). left; reflexivity. }
    destruct (BF _ _ IN) as (Q0 & Q1 & Q2 & Q4 & Q5 & Q6 & QD). destruct (PNAEK.blk_facts L ar C HI LY HIok _ FF LK cr Aw M _ _ _ HH IN) as (_ & _ & _ & _ & _ & QIMG & _).
    repeat split; try assumption.
Qed.

Lemma finish (fx : FPState) R M model LK Aw k' cr' :
  getr R (reg 1) = Z_to_bv 64 (U 1) -> getr R (reg 2) = Z_to_bv 64 S ->
  (forall i, In i [8; 9; 18; 19; 20; 21; 22]%nat -> getr R (reg i) = Z_to_bv 64 (U i)) -> kept0 R ->
  stok model LK Aw -> mem_ok M -> ri_inv HI (PESK.sink_own k' ++ LB) FF LK cr' Aw M (vml_of model) ->
  k' = PESK.sk_push sk (PESK.sk_b k') -> PESKA.sink_atA RSEGS L ar P M v k' ->
  PMSP.credit_keep cr0 cr' (PESKA.spa_pot P (PESK.sk_c sk)) (PESKA.spa_pot P (PESK.sk_c k')) ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R RET_F M model) K.
Proof using All.
  intros E1 E2 ES KP (AM & MRT & ILK & IAW) (EK & DK & STK & ACC & STKSH) HH EK' SKA CK.
  pose proof RAok as (Hr1 & Hr2).
  assert (RA : getr R (reg 1) = Z_to_bv 64 r) by (rewrite E1; unfold U; rewrite Z_to_bv_bv_unsigned; exact Rra0).
  unfold PMSPA.cfg.
  apply (PMASK.ret_exit L ar C HI LY HIok fx R M model K _ FF LK cr' Aw RET_F r W_af0a4 HH AM F_af0a4 eq_refl D_af0a4 RA ltac:(lia) Hr2).
  intros model1 MRT1 AM1 HH1.
  rewrite EK' in HH1, SKA, CK.
  apply (KONT fx R M model1 LK Aw cr' (PESK.sk_b k')); try assumption.
  - apply L5SAR.preserved_by_index. intros xr Hx. unfold L5SAR.cs_all in Hx.
    destruct Hx as [<-|Hx]; [rewrite E2, Rsp0; reflexivity|].
    destruct Hx as [<-|Hx]; [apply KP; cbn; auto|]. destruct Hx as [<-|Hx]; [apply KP; cbn; auto|].
    destruct Hx as [<-|Hx]; [rewrite (ES 8%nat) by (cbn; auto); unfold U; apply Z_to_bv_bv_unsigned|].
    destruct Hx as [<-|Hx]; [rewrite (ES 9%nat) by (cbn; auto); unfold U; apply Z_to_bv_bv_unsigned|].
    destruct Hx as [<-|Hx]; [rewrite (ES 18%nat) by (cbn; auto 10); unfold U; apply Z_to_bv_bv_unsigned|].
    destruct Hx as [<-|Hx]; [rewrite (ES 19%nat) by (cbn; auto 10); unfold U; apply Z_to_bv_bv_unsigned|].
    destruct Hx as [<-|Hx]; [rewrite (ES 20%nat) by (cbn; auto 10); unfold U; apply Z_to_bv_bv_unsigned|].
    destruct Hx as [<-|Hx]; [rewrite (ES 21%nat) by (cbn; auto 10); unfold U; apply Z_to_bv_bv_unsigned|].
    destruct Hx as [<-|Hx]; [rewrite (ES 22%nat) by (cbn; auto 10); unfold U; apply Z_to_bv_bv_unsigned|].
    apply KP. cbn in Hx |- *. tauto.
  - change (PMSPA.pm_scr 0) with 12288. apply (L5SAR.ahpres_of L ar LB FF S 12288 _ M0 M); [exact EK| destruct STK as (_ & _ & _ & _ & D & _); exact D| exact DK].
  - eapply L5LZ.model_rt_trans; [exact MRT| exact MRT1].
Qed.

Definition kept1 (R : bvmap 5 word) : Prop := forall i, In i [3; 4; 23; 24; 25; 26; 27]%nat -> getr R (reg i) = getr R0 (reg i).
Lemma kept1_of0 R : kept0 R -> kept1 R.
Proof. intros KP i Hi. apply KP. cbn in Hi |- *. clear - Hi. tauto. Qed.
Lemma kept1_of (R R1 : bvmap 5 word) : kept1 R -> (forall i, In i [3; 4; 23; 24; 25; 26; 27]%nat -> getr R1 (reg i) = getr R (reg i)) -> kept1 R1.
Proof. intros KP H i Hi. rewrite (H i Hi). exact (KP i Hi). Qed.
Lemma kept1_pres (R R1 : bvmap 5 word) : kept1 R -> regs_preserved R R1 -> kept1 R1.
Proof.
  intros KP RP. apply (kept1_of R R1 KP). intros i Hi. apply (L5SAR.cs_of_preserved R R1 i RP). unfold L5SAR.cs_all. cbn in Hi |- *. clear - Hi. tauto.
Qed.
Lemma kept0_of1 R : kept1 R -> getr R (reg 21) = Z_to_bv 64 (U 21) -> getr R (reg 22) = Z_to_bv 64 (U 22) -> kept0 R.
Proof.
  intros KP E21 E22 i Hi. cbn in Hi.
  destruct Hi as [<-|[<-|[<-|[<-|Hi]]]]; [apply KP; left; reflexivity| apply KP; right; left; reflexivity
    | rewrite E21; unfold U; apply Z_to_bv_bv_unsigned| rewrite E22; unfold U; apply Z_to_bv_bv_unsigned|].
  apply KP. cbn. clear - Hi. tauto.
Qed.

Lemma centryS (R : bvmap 5 word) HL LK cr Aw M model (fr X : Z) :
  ri_inv HI (HL ++ LB) FF LK cr Aw M (vml_of model) -> mem_ok M -> kept1 R ->
  getr R (reg 1) = Z_to_bv 64 X -> L5.ra_ok X -> getr R (reg 2) = Z_to_bv 64 (S - fr) -> 0 <= fr <= 4096 -> fr mod 16 = 0 ->
  PEASKANG.entryS AD L ar R M (S - fr) X /\ PMSPA.ffrsA FF (S - fr).
Proof using All.
  intros HH MO KP A1 RAX A2 Hfr F16.
  destruct (cstk HL LK cr Aw M model fr 4096 HH MO ltac:(lia) ltac:(lia) ltac:(lia) F16 ltac:(reflexivity)) as (STKc & SHc).
  split; [| intros f Hf; specialize (FRS f Hf); lia].
  unfold PEASKANG.entryS. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact A1|]. split; [exact RAX|]. split; [exact A2|].
  split; [rewrite (KP 3%nat) by (cbn; tauto); exact Rgp0|]. split; [rewrite (KP 4%nat) by (cbn; tauto); exact Rtp0|].
  change (4096 / 8) with 512 in SHc. split; [exact STKc| exact SHc].
Qed.
Lemma centryD (R : bvmap 5 word) HL LK cr Aw M model (fr X : Z) :
  ri_inv HI (HL ++ LB) FF LK cr Aw M (vml_of model) -> mem_ok M -> kept1 R ->
  getr R (reg 1) = Z_to_bv 64 X -> L5.ra_ok X -> getr R (reg 2) = Z_to_bv 64 (S - fr) -> 0 <= fr <= 4096 -> fr mod 16 = 0 ->
  PEASKAND.entryS AD L ar R M (S - fr) X /\ PMSPA.ffrsA FF (S - fr).
Proof using All.
  intros HH MO KP A1 RAX A2 Hfr F16. destruct (centryS R HL LK cr Aw M model fr X HH MO KP A1 RAX A2 Hfr F16) as (E & F). split; [exact E| exact F].
Qed.

Lemma pv_facts HL LK cr Aw M model : ri_inv HI (HL ++ LB) FF LK cr Aw M (vml_of model) -> mem_ok M -> PESKA.pv_ok ar FF M S v pv ->
  L5.defined M pv 1 /\ byte_at M (HeapIfaceA.S pv) 0 /\ (pv + 1 <= v \/ v + 24 <= pv)
  /\ 4096 <= pv /\ pv + 1 <= 2 ^ 47 /\ 6914048 <= pv /\ (pv + 1 <= S - 12288 \/ S <= pv) /\ (2147446784 + 17592186048512 <= pv \/ pv + 1 <= 2147446784)
  /\ (forall LBc sp' scr', sp' <= S -> aclient L ar LBc FF sp' scr' pv) /\ L5A.avis (ahid Aw model) pv 1
  /\ (forall q m, In (q, m) (HL ++ LB) -> q + m <= pv \/ pv + 1 <= q).
Proof using All.
  intros HH MO (PVD & PVZ & PVO & PVW). destruct (nfacts HL LK cr Aw M model HH MO) as ((A16 & SLO & SHI & SPT & C0') & (O1 & O2 & O5 & ODEF) & BF).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & _ & _ & _ & _ & STOP & _).
  rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in FSIMG.
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ FF LK cr Aw M model HH) as (_ & VIS & _ & VFS & _).
  unfold app_mem, FS_BYTES, BIGSHADOW_LO, BIGSHADOW_HI in *.
  split; [exact PVD|]. split; [exact PVZ|]. split; [exact PVO|].
  destruct PVW as [(P1 & P2)|(f & Hf & P1 & P2)].
  - split; [lia|]. split; [lia|]. split; [lia|]. split; [right; exact P1|]. split; [lia|]. split; [intros LBc sp' scr' LE; apply L5SAR.stack_client; lia|]. split; [apply VIS; lia|].
    intros q m Hq. destruct (BF q m Hq) as (_ & _ & Q2 & _). left. lia.
  - destruct (WF f Hf) as (F1 & F2 & _ & FK & _). pose proof (fun q m Hq => proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (WB (q, m) Hq))))))) as WBF. cbn [fst snd] in WBF.
    destruct f as [[F kc] rs]. cbn [ff_addr ff_class fst snd] in *.
    split; [lia|]. split; [lia|]. split; [lia|]. split; [left; lia|]. split; [lia|].
    split; [intros LBc sp' scr' _; apply (L5SAR.fframe_client L ar LBc FF sp' scr' F kc rs pv Hf); lia|]. split; [apply VFS; lia|].
    intros q m Hq. destruct (WBF q m Hq) as [X|X]; [left; lia| right; lia].
Qed.

Lemma model_rt_refl (m : Model) : model_rt m m. Proof. destruct m; reflexivity. Qed.
Lemma stok0 : stok model0 LK0 Aw0.
Proof using All. split; [exact AM0|]. split; [apply model_rt_refl|]. split; apply incl_refl. Qed.
Lemma mem_ok0 : mem_ok M0.
Proof using All.
  split; [intros a _; reflexivity|]. split; [intros a _ _ X; exact X|]. split; [exact ASTK0|].
  split; [pose proof SKA0 as (_ & _ & _ & _ & X & _); exact X| exact STKSH0].
Qed.
Lemma pv_num : 4096 <= pv /\ pv + 1 <= 2 ^ 47.
Proof using All. destruct (pv_facts _ LK0 cr0 Aw0 M0 model0 HH0 mem_ok0 PVOK) as (_ & _ & _ & P4 & P47 & _). split; assumption. Qed.

Lemma sk0_num : 0 <= PESK.sk_z sk <= PESK.sk_c sk /\ PESK.sk_c sk <= 2 ^ 34 /\ 0 <= PESK.sk_b sk /\ (PESK.sk_c sk = 0 -> PESK.sk_b sk = 0)
  /\ (0 < PESK.sk_c sk -> 4096 <= PESK.sk_b sk /\ PESK.sk_b sk + PESK.sk_c sk <= ahl_ceil ar /\ PESK.sk_b sk mod 16 = 0 /\ nsh (PESK.sk_b sk) (PESK.sk_c sk)
      /\ (PESK.sk_b sk + PESK.sk_c sk <= 65536 \/ 0x698000 <= PESK.sk_b sk) /\ (PESK.sk_b sk + PESK.sk_c sk <= v \/ v + 24 <= PESK.sk_b sk)).
Proof using All.
  destruct (sk_facts _ LK0 cr0 Aw0 M0 model0 sk HH0 mem_ok0 SKA0 ltac:(apply incl_refl)) as (A & B & C0 & D & E).
  split; [exact A|]. split; [exact B|]. split; [exact C0|]. split; [exact D|]. intros HC. destruct (E HC) as (E1 & E2 & E3 & E4 & E5 & E6 & _). repeat split; assumption.
Qed.

Ltac fastB_tail fx1 R1 M1v MG1 FRZ1 MS1 KS1 A1 A2 A8 A9 A18 A19 A20 C8 b z c LK Aw ZC ZC0 HH SKA Esk KP E2122 W0 W16 ACB AZ O1 O2 BV SLO SHI SPT B4 BCEIL B8 :=
  lazymatch goal with |- srealizes _ _ (PMSPA.cfg _ ?R ?pc ?M ?model) _ =>
  lazymatch type of MS1 with msteps _ _ (mst _ _ ?pc1 _) =>
  apply (piece_stepB _ fx1 R pc R1 pc1 _ M model cr0 LK Aw M1v (fun a => (b + z <= a < b + z + 1) \/ (v + 8 <= a < v + 8 + 8)) b c HH);
    [ assumption | assumption | left; reflexivity | exact MS1 | exact MG1
    | intros a Ha Na; apply FRZ1; [exact Ha| clear - Na; intros X; apply Na; left; lia| clear - Na; intros X; apply Na; right; lia]
    | intros a [X|X]; [right; right; clear - X ZC ZC0; lia| right; left; clear - X; lia] |];
  let M1 := fresh "M1" in let model1 := fresh "model1" in
  intros M1 model1 HH1 SO1 MO1 FR1 VUP AGS VIS1;
  assert (KEEP : forall a val, a + 8 <= v + 8 \/ v + 16 <= a -> (a + 8 <= b + z \/ b + z + 1 <= a) -> 0 <= a -> a + 8 <= 2 ^ 64 -> L5.u64_at RSEGS M a val -> L5.u64_at RSEGS M1 a val)
    by (intros a val Ha Hb H0 H1 X; apply (L5C.u64_at_agree RSEGS M M1); [intros i Hi; apply FR1; [clear - Hi H0 H1; lia| clear - Hi Ha Hb; lia]| exact H0| exact H1| exact X]);
  destruct (nfacts _ LK cr0 Aw M1 model1 HH1 MO1) as (_ & (_ & _ & _ & ODEF1) & BF1);
  destruct (BF1 b c ltac:(left; reflexivity)) as (_ & _ & _ & _ & _ & _ & QD1);
  pose proof SKA as (_ & _ & _ & _ & _ & _ & CAP & _ & LIVE0); rewrite Esk in CAP, LIVE0; cbn [PESK.sk_b PESK.sk_z PESK.sk_c] in CAP, LIVE0;
  destruct (LIVE0 ltac:(clear - ZC ZC0; lia)) as (_ & _ & _ & ABR & SCAP & SNM);
  apply (finish fx1 R1 M1 model1 LK Aw (PESK.SK b (z + 1) c) cr0 A1 A2);
    [ intros i Hi; cbn in Hi;
      destruct Hi as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]];
      [exact A8| exact A9| exact A18| exact A19| exact A20| rewrite (KS1 21%nat) by inl; apply (E2122 21%nat); left; reflexivity| rewrite (KS1 22%nat) by inl; apply (E2122 22%nat); right; left; reflexivity]
    | apply (kept0_of R R1 KP); intros i Hi; apply KS1; cbn in Hi; repeat (destruct Hi as [<-|Hi]; [inl|]); destruct Hi
    | exact SO1 | exact MO1
    | unfold PESK.sink_own; cbn [PESK.sk_b PESK.sk_c]; replace (c =? 0) with false by (symmetry; apply Z.eqb_neq; clear - ZC ZC0; lia); exact HH1
    | rewrite Esk; unfold PESK.sk_push; cbn [PESK.sk_b PESK.sk_z PESK.sk_c]; replace (z <? c) with true by (symmetry; apply Z.ltb_lt; exact ZC); reflexivity
    | unfold PESKA.sink_atA; cbn [PESK.sk_b PESK.sk_z PESK.sk_c]
    | rewrite Esk; cbn [PESK.sk_c]; unfold PMSP.credit_keep; clear; lia ];

  split; [apply KEEP; [clear; lia| clear - BV ZC ZC0; lia| clear - O1; lia| clear - O2 SLO SHI SPT; lia| exact W0]|];
  split; [replace (b + (z + 1)) with (b + z + 1) by (clear; lia); apply VUP; [right; clear; lia| exact C8]|];
  split; [apply KEEP; [clear; lia| clear - BV ZC ZC0; lia| clear - O1; lia| clear - O2 SLO SHI SPT; lia| exact W16]|];
  split; [exact ODEF1|]; split; [destruct MO1 as (_ & _ & _ & ACC1 & _); exact ACC1|];
  split; [clear - ZC ZC0; lia|]; split; [exact CAP|]; split; [intros X; exfalso; clear - X ZC ZC0; lia|];
  intros _; split; [exact QD1|];
  split; [apply (PMFA.accA_agree M M1 b (z + 1)); [apply AGS; clear - B4 BCEIL SPT ZC ZC0; lia| exact ACB]|];
  split; [change (PGV8A.annA M1 b (z + 1) c); apply (PGV8KA.annA_agree M M1 b (z + 1) c); [clear - ZC ZC0; lia| exact B8| apply AGS; clear - B4 BCEIL SPT ZC0; lia| split; [exact AZ| split; assumption]]|];
  split; [exact ABR|]; split; [exact SCAP| exact SNM]
  end end.

Lemma fast_B (fx : FPState) R M model LK Aw b z c :
  sk = PESK.SK b z c -> z < c ->
  getr R (reg 2) = Z_to_bv 64 (S - 48) -> getr R (reg 8) = Z_to_bv 64 (v + 8) -> getr R (reg 9) = Z_to_bv 64 pv -> getr R (reg 18) = Z_to_bv 64 (b + z) ->
  getr R (reg 19) = Z_to_bv 64 ((v + 8) / 8 + 2147450880) -> getr R (reg 20) = Z_to_bv 64 2147450880 ->
  (forall i, In i [21; 22]%nat -> getr R (reg i) = Z_to_bv 64 (U i)) -> kept0 R ->
  stok model LK Aw -> mem_ok M -> saves M -> ri_inv HI ([(b, c)] ++ LB) FF LK cr0 Aw M (vml_of model) ->
  PEASKAN.bhdr RSEGS M v b z c -> PMSPA.accA M b (z + 1) -> PMSPA.annA M b (z + 1) c ->
  PESKA.pv_ok ar FF M S v pv ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0xaf094 M model) K.
Proof using All.
  intros Esk ZC E2 E8 E9 E18 E19 E20 E2122 KP SO MO SV HH SKA ACB ANB PV.
  pose proof SKA as (_ & W0 & W8 & W16 & ZC0 & C1 & B4 & B16 & BDEF).
  destruct (nfacts _ LK cr0 Aw M model HH MO) as ((A16 & SLO & SHI & SPT & C0') & (O1 & O2 & O5 & ODEF) & BF). unfold nsh in O5.
  assert (BIN : In (b, c) ([(b, c)] ++ LB)) by (left; reflexivity).
  destruct (BF b c BIN) as (_ & _ & BCEIL & _ & BSH & BV & _). unfold nsh in BSH.
  pose proof sk0_num as (_ & C31 & _ & _ & LIVEn). rewrite Esk in C31, LIVEn. cbn [PESK.sk_b PESK.sk_z PESK.sk_c] in C31, LIVEn.
  destruct (LIVEn ltac:(clear - C1; lia)) as (_ & _ & _ & _ & BIMG & _).
  destruct (vfacts _ LK cr0 Aw M model HH MO) as (X0 & X1 & X2 & XW & XZ & XWV & XSZ & XAV).
  pose proof SV as (S8 & S16 & S24 & S32 & S40 & S48).
  destruct (pv_facts _ LK cr0 Aw M model HH MO PV) as (PVD & PVZ & PVO & PV1 & PV2 & PV3 & PVS & PVBIG & PVCL & PVVIS & PVBL).

  assert (DJ1 : 2147446784 + 17592186048512 <= v \/ v + 24 <= 2147446784) by (clear - O5; unfold nsh in O5; lia).
  assert (DJ2 : S - 256 + 256 <= v \/ v + 24 <= S - 256) by (clear - O2 SLO; lia).
  assert (DJ3 : pv + 1 <= S - 256 \/ S - 256 + 256 <= pv) by (clear - PVS; lia).
  assert (DJ4 : 2147446784 + 17592186048512 <= b \/ b + c <= 2147446784) by (clear - BSH; lia).
  assert (DJ5 : 65536 + 6848512 <= b \/ b + c <= 65536) by (clear - BIMG; lia).
  assert (DJ6 : b + z + 1 <= S - 256 \/ S - 256 + 256 <= b + z) by (clear - BCEIL SLO ZC ZC0; lia).
  assert (DJ7 : b + z + 1 <= v \/ v + 24 <= b + z) by (clear - BV ZC ZC0; lia).
  assert (DJ8 : b + z + 1 <= pv \/ pv + 1 <= b + z) by (destruct (PVBL b c BIN) as [X|X]; clear - X ZC ZC0; lia).
  assert (DJ9 : 2147446784 + 17592186048512 <= b + z \/ b + z + 1 <= 2147446784) by (clear - BSH ZC ZC0; lia).

  destruct (u8_at_of_defined M pv ltac:(lia) ltac:(pose proof (PVD 0 ltac:(lia)) as D0; rewrite Z.add_0_r in D0; exact D0)) as (bt & BT & BTM).
  assert (BTv : L5.u8_at RSEGS (mrestrict (ahid Aw model) M) pv bt) by (apply (proj2 (L5A.u8_at_vis (ahid Aw model) M pv bt PVVIS ltac:(lia) ltac:(lia))); exact BTM).
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ FF LK cr0 Aw M model HH) as (HOFF & VIS & VIMG & VFS & VBLK & VBSH & VFSSH & VSTSH).
  assert (PVSHV : L5A.avis (ahid Aw model) (pv / 8 + SBL) 1).
  { destruct PV as (_ & _ & _ & [(P1 & P2)|(f & Hf & P1 & P2)]).
    - apply VSTSH. intros i Hi. unfold in_shadow_of, HeapIfaceA.S. rewrite Z.add_0_r || idtac. replace (pv / 8 + SBL + i) with (pv / 8 + SBL) by lia.
      split; [apply Z.add_le_mono_r; apply Z.div_le_mono; lia| apply Z.add_le_mono_r; apply Z.div_le_mono; lia].
    - pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & WF & _). destruct (WF f Hf) as (F1 & F2 & _). destruct f as [[F kc] rs]. cbn [ff_addr ff_class fst snd] in *.
      apply VFSSH. intros i Hi. unfold in_shadow_of, HeapIfaceA.S. replace (pv / 8 + SBL + i) with (pv / 8 + SBL) by lia.
      split; [apply Z.add_le_mono_r; apply Z.div_le_mono; lia| apply Z.add_le_mono_r; apply Z.div_le_mono; unfold FS_BYTES in *; lia]. }
  assert (PVZv : L5KA.zeros_at (mrestrict (ahid Aw model) M) (pv / 8 + SBL) 1).
  { intros i Hi. replace (pv / 8 + SBL + i) with (pv / 8 + SBL) by lia.
    pose proof (PVSHV 0 ltac:(lia)) as AV0. rewrite Z.add_0_r in AV0. rewrite (mrestrict_visible (ahid Aw model) M _ AV0). exact PVZ. }

  assert (B8 : b mod 8 = 0) by (apply PMKA.mod16_8'; exact B16).
  assert (EBZ : (b + z) / 8 + SBL = HeapIfaceA.S b + z / 8).
  { unfold HeapIfaceA.S, SB. pose proof (Z.div_mod b 8 ltac:(clear; lia)) as DB. rewrite B8 in DB. replace (b + z) with (b / 8 * 8 + z) by (clear - DB; lia). rewrite Z.div_add_l by (clear; lia). clear; lia. }
  assert (EBC : HeapIfaceA.S (b + c - 1) = HeapIfaceA.S b + (c - 1) / 8).
  { unfold HeapIfaceA.S, SB. pose proof (Z.div_mod b 8 ltac:(clear; lia)) as DB. rewrite B8 in DB. replace (b + c - 1) with (b / 8 * 8 + (c - 1)) by (clear - DB; lia). rewrite Z.div_add_l by (clear; lia). clear; lia. }
  pose proof (Z.div_pos z 8 ltac:(lia) ltac:(lia)) as DZ0. pose proof (Z.div_le_mono z (c - 1) 8 ltac:(lia) ltac:(lia)) as DZC.
  assert (GVIS : L5A.avis (ahid Aw model) ((b + z) / 8 + SBL) 1).
  { apply (VBSH b c); [exact BIN|]. intros i Hi. rewrite EBZ. unfold in_shadow_of. rewrite EBC. clear - Hi DZ0 DZC. lia. }
  destruct ANB as (AZ & AP & ATAIL).
  assert (KS21 : forall R', (forall i, In i [21; 22]%nat -> getr R' (reg i) = getr R (reg i)) -> forall i, In i [21; 22]%nat -> getr R' (reg i) = Z_to_bv 64 (U i)).
  { intros R' KS i Hi. rewrite (KS i Hi). exact (E2122 i Hi). }
  destruct (Z.eq_dec ((z + 1) mod 8) 0) as [G0|GP].
  -
    assert (XG : L5KA.zeros_at (mrestrict (ahid Aw model) M) ((b + z) / 8 + SBL) 1).
    { intros i Hi. replace ((b + z) / 8 + SBL + i) with ((b + z) / 8 + SBL) by lia. pose proof (GVIS 0 ltac:(lia)) as AV0. rewrite Z.add_0_r in AV0.
      rewrite (mrestrict_visible (ahid Aw model) M _ AV0). rewrite EBZ. apply (AZ (z / 8)).
      pose proof (Z.div_mod (z + 1) 8 ltac:(lia)) as D1. pose proof (Z.div_mod z 8 ltac:(lia)) as D0. pose proof (Z.mod_pos_bound z 8 ltac:(lia)) as MR0. clear - G0 D1 D0 MR0 ZC0; lia. }
    pose proof (PEASKPP.askB7_conc fx R (mrestrict (ahid Aw model) M) (fun j => match j with 2%nat => S | 10%nat => v | 33%nat => b | 34%nat => z | 35%nat => c | 36%nat => pv | 40%nat => bt
       | 44%nat => U 1 | 45%nat => U 8 | 46%nat => U 9 | 47%nat => U 18 | 48%nat => U 19 | 49%nat => U 20
       | 55%nat => bv_unsigned (getr R (reg 10)) | 56%nat => bv_unsigned (getr R (reg 11)) | 57%nat => bv_unsigned (getr R (reg 12)) | _ => 0 end)) as PP.
    cbn beta iota in PP.
    pose proof (UB 1%nat) as UB1. pose proof (UB 8%nat) as UB8. pose proof (UB 9%nat) as UB9. pose proof (UB 18%nat) as UB18. pose proof (UB 19%nat) as UB19. pose proof (UB 20%nat) as UB20.
    assert (XWB : L5.writable RSEGS (mrestrict (ahid Aw model) M) (b + z) 1).
    { apply (proj2 (L5A.writable_vis (ahid Aw model) M (b + z) 1 (VBLK b c (b + z) 1 BIN ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
      apply (L5.writable_sub _ M b c); [apply (L5C.writable_of_defined RSEGS M b c BDEF); lia| lia| lia]. }
    hide_disj. L5SAR.feed PP ltac:(first [apply wid | apply wrng | pfeed XW XSZ XAV]). unhide.
    destruct PP as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & A1 & A2 & A8 & A9 & A10 & A11 & A18 & A19 & A20 & C8 & CB).
    fastB_tail fx1 R1 M1v MG1 FRZ1 MS1 KS1 A1 A2 A8 A9 A18 A19 A20 C8 b z c LK Aw ZC ZC0 HH SKA0 Esk KP E2122 W0 W16 ACB AZ O1 O2 BV SLO SHI SPT B4 BCEIL B8.
  -
    assert (XG : L5.u8_at RSEGS (mrestrict (ahid Aw model) M) ((b + z) / 8 + SBL) ((Z.land z 7 + 1) mod 2 ^ 64)).
    { pose proof (Z.mod_pos_bound z 8 ltac:(clear; lia)) as MR0.
      replace (Z.land z 7) with (z mod 8) by (symmetry; exact (Z.land_ones z 3 ltac:(clear; lia))).
      rewrite (Z.mod_small (z mod 8 + 1) (2 ^ 64)) by (clear - MR0; lia).
      pose proof (GVIS 0 ltac:(lia)) as AV0. rewrite Z.add_0_r in AV0. unfold L5.u8_at. cbn [rdn]. rewrite (mrestrict_visible (ahid Aw model) M _ AV0). rewrite EBZ.
      pose proof (Z.div_mod (z + 1) 8 ltac:(lia)) as D1. pose proof (Z.div_mod z 8 ltac:(lia)) as D0.
      pose proof (Z.mod_pos_bound (z + 1) 8 ltac:(lia)) as MR1.
      assert (E1 : (z + 1) / 8 = z / 8 /\ (z + 1) mod 8 = z mod 8 + 1) by (clear - GP D1 D0 MR0 MR1; lia).
      pose proof (AP GP) as BY. rewrite (proj1 E1), (proj2 E1) in BY. unfold byte_at in BY. rewrite BY. reflexivity. }
    pose proof (PEASKPP.askBp_conc fx R (mrestrict (ahid Aw model) M) (fun j => match j with 2%nat => S | 10%nat => v | 33%nat => b | 34%nat => z | 35%nat => c | 36%nat => pv | 40%nat => bt
       | 44%nat => U 1 | 45%nat => U 8 | 46%nat => U 9 | 47%nat => U 18 | 48%nat => U 19 | 49%nat => U 20
       | 55%nat => bv_unsigned (getr R (reg 10)) | 56%nat => bv_unsigned (getr R (reg 11)) | 57%nat => bv_unsigned (getr R (reg 12)) | _ => 0 end)) as PP.
    cbn beta iota in PP.
    pose proof (UB 1%nat) as UB1. pose proof (UB 8%nat) as UB8. pose proof (UB 9%nat) as UB9. pose proof (UB 18%nat) as UB18. pose proof (UB 19%nat) as UB19. pose proof (UB 20%nat) as UB20.
    assert (XWB : L5.writable RSEGS (mrestrict (ahid Aw model) M) (b + z) 1).
    { apply (proj2 (L5A.writable_vis (ahid Aw model) M (b + z) 1 (VBLK b c (b + z) 1 BIN ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
      apply (L5.writable_sub _ M b c); [apply (L5C.writable_of_defined RSEGS M b c BDEF); lia| lia| lia]. }
    hide_disj. L5SAR.feed PP ltac:(first [apply wid | apply wrng | pfeed XW XSZ XAV]). unhide.
    destruct PP as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & A1 & A2 & A8 & A9 & A10 & A11 & _ & A18 & A19 & A20 & C8 & CB).
    fastB_tail fx1 R1 M1v MG1 FRZ1 MS1 KS1 A1 A2 A8 A9 A18 A19 A20 C8 b z c LK Aw ZC ZC0 HH SKA0 Esk KP E2122 W0 W16 ACB AZ O1 O2 BV SLO SHI SPT B4 BCEIL B8.
Qed.

Lemma sink_at_xfer HL HL1 LK cr Aw M model LK1 cr1 Aw1 M1 model1 k' :
  ri_inv HI (HL ++ LB) FF LK cr Aw M (vml_of model) -> mem_ok M ->
  ri_inv HI (HL1 ++ LB) FF LK1 cr1 Aw1 M1 (vml_of model1) -> mem_ok M1 ->
  incl (PESK.sink_own k') HL -> incl (PESK.sink_own k') HL1 ->
  PESKA.sink_atA RSEGS L ar P M v k' ->
  L5.u64_at RSEGS M1 v (PESK.sk_b k') -> L5.u64_at RSEGS M1 (v + 8) (PESK.sk_b k' + PESK.sk_z k') -> L5.u64_at RSEGS M1 (v + 16) (PESK.sk_b k' + PESK.sk_c k') ->
  (0 < PESK.sk_c k' -> PMFA.agsh M M1 (PESK.sk_b k') (PESK.sk_c k')) ->
  PESKA.sink_atA RSEGS L ar P M1 v k'.
Proof using NMAXI HIok AO LY LYa V8.
  intros HH MO HH1 MO1 INC INC1 SKA W0 W8 W16 AGS.
  destruct (sk_facts _ LK cr Aw M model k' HH MO SKA INC) as (ZC & C31 & B0 & C0 & LIVE).
  destruct (nfacts _ LK1 cr1 Aw1 M1 model1 HH1 MO1) as (_ & (_ & _ & _ & ODEF1) & BF1).
  pose proof SKA as (_ & _ & _ & _ & _ & _ & CAP & _ & LIVE0).
  split; [exact W0|]. split; [exact W8|]. split; [exact W16|]. split; [exact ODEF1|].
  split; [destruct MO1 as (_ & _ & _ & ACC1 & _); exact ACC1|].
  split; [exact ZC|]. split; [exact CAP|]. split; [exact C0|].
  intros HC. destruct (LIVE HC) as (B4 & BCEIL & B16 & BSH & BIMG & BV & BDEF & BIN).
  destruct (LIVE0 HC) as (_ & ACB & ANB & ABR & SCAP & SNM).
  assert (BIN1 : In (PESK.sk_b k', PESK.sk_c k') (HL1 ++ LB)).
  { apply in_or_app. left. apply INC1. unfold PESK.sink_own. replace (PESK.sk_c k' =? 0) with false by (symmetry; apply Z.eqb_neq; clear - HC; lia). left; reflexivity. }
  destruct (BF1 _ _ BIN1) as (_ & _ & _ & _ & _ & _ & QD1).
  split; [exact QD1|].
  split; [apply (PMFA.accA_agree M M1); [apply (PMFA.agsh_sub M M1 _ _ _ _ (AGS HC)); clear - ZC; lia| exact ACB]|].
  split; [change (PGV8A.annA M1 (PESK.sk_b k') (PESK.sk_z k') (PESK.sk_c k')); apply (PGV8KA.annA_agree M M1); [clear - ZC; lia| apply PMKA.mod16_8'; exact B16| exact (AGS HC)| exact ANB]|].
  split; [exact ABR|]. split; [exact SCAP| exact SNM].
Qed.

Lemma tail_R (fx : FPState) R M model LK Aw cr' B b z c cap' e18 :
  sk = PESK.SK b z c -> z = c -> cap' = PESK.cap_next c -> 0 <= e18 < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (S - 48) -> getr R (reg 8) = Z_to_bv 64 (v + 8) -> getr R (reg 9) = Z_to_bv 64 pv -> getr R (reg 10) = Z_to_bv 64 (B + z + 1) ->
  getr R (reg 18) = Z_to_bv 64 e18 -> getr R (reg 19) = Z_to_bv 64 ((v + 8) / 8 + SBL) -> getr R (reg 20) = Z_to_bv 64 SBL ->
  (forall i, In i [21; 22]%nat -> getr R (reg i) = Z_to_bv 64 (U i)) -> kept0 R ->
  stok model LK Aw -> mem_ok M -> saves M -> ri_inv HI ([(B, cap')] ++ LB) FF LK cr' Aw M (vml_of model) ->
  PESKA.sink_atA RSEGS L ar P M v (PESK.SK B (z + 1) cap') ->
  PMSP.credit_keep cr0 cr' (PESKA.spa_pot P c) (PESKA.spa_pot P cap') ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R RA_SLOW M model) K.
Proof using All.
  intros Esk EZC Ecap E18B E2 E8 E9 E10 E18 E19 E20 E2122 KP SO MO SV HH SKA CK.
  destruct (nfacts _ LK cr' Aw M model HH MO) as ((A16 & SLO & SHI & SPT & C0') & (O1 & O2 & O5 & ODEF) & BF). unfold nsh in O5.
  destruct (vfacts _ LK cr' Aw M model HH MO) as (X0 & X1 & X2 & XW & XZ & XWV & XSZ & XAV).
  pose proof SV as (S8 & S16 & S24 & S32 & S40 & S48). pose proof pv_num as (PV4 & PV47).
  assert (INC : incl (PESK.sink_own (PESK.SK B (z + 1) cap')) [(B, cap')]).
  { unfold PESK.sink_own; cbn [PESK.sk_b PESK.sk_c]. destruct (cap' =? 0); [intros x []| apply incl_refl]. }
  destruct (sk_facts _ LK cr' Aw M model _ HH MO SKA INC) as (ZC1 & C31 & B0 & _ & LIVE1). cbn [PESK.sk_b PESK.sk_z PESK.sk_c] in ZC1, C31, B0, LIVE1.
  pose proof (PESK.cap_next_pos c) as CP. pose proof sk0_num as (ZC0 & _). rewrite Esk in ZC0. cbn [PESK.sk_z PESK.sk_c] in ZC0.
  destruct (LIVE1 ltac:(clear - CP Ecap ZC0; subst cap'; pose proof (CP ltac:(lia)); lia)) as (B4 & BCEIL & B16 & BSH & BIMG & BV).
  pose proof SKA as (W0 & W8 & W16 & _). cbn [PESK.sk_b PESK.sk_z PESK.sk_c] in W0, W8, W16.
  assert (DJ1 : 2147446784 + 17592186048512 <= v \/ v + 24 <= 2147446784) by (clear - O5; lia).
  assert (DJ2 : S - 256 + 256 <= v \/ v + 24 <= S - 256) by (clear - O2 SLO; lia).
  pose proof (PEASKPP.askR_conc fx R (mrestrict (ahid Aw model) M) (fun j => match j with 2%nat => S | 10%nat => v | 33%nat => e18 | 36%nat => pv | 41%nat => B + z + 1
     | 44%nat => U 1 | 45%nat => U 8 | 46%nat => U 9 | 47%nat => U 18 | 48%nat => U 19 | 49%nat => U 20
     | 56%nat => bv_unsigned (getr R (reg 11)) | 57%nat => bv_unsigned (getr R (reg 12)) | _ => 0 end)) as PP.
  cbn beta iota in PP. replace (e18 + 0) with e18 in PP by (rewrite Z.add_0_r; reflexivity).
  pose proof (UB 1%nat) as UB1. pose proof (UB 8%nat) as UB8. pose proof (UB 9%nat) as UB9. pose proof (UB 18%nat) as UB18. pose proof (UB 19%nat) as UB19. pose proof (UB 20%nat) as UB20.
  hide_disj. L5SAR.feed PP ltac:(first [apply wid | apply wrng | pfeed XW XSZ XAV]). unhide.
  destruct PP as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & A1 & A2 & A8 & A9 & A11 & A18 & A19 & A20 & C0).
  apply (piece_step fx fx1 R RA_SLOW R1 RET_F _ M model cr' LK Aw M1v (fun a => v + 8 <= a < v + 8 + 8) HH SO MO MS1 MG1 FRZ1); [intros a Pa; right; clear - Pa; lia|].
  intros M1 model1 HH1 SO1 MO1 FR1 VUP AGS.
  assert (KEEP : forall a val, a + 8 <= v + 8 \/ v + 16 <= a -> 0 <= a -> a + 8 <= 2 ^ 64 -> L5.u64_at RSEGS M a val -> L5.u64_at RSEGS M1 a val)
    by (intros a val Ha H0 H1 X; apply (L5C.u64_at_agree RSEGS M M1); [intros i Hi; apply FR1; [clear - Hi H0 H1; lia| clear - Hi Ha; lia]| exact H0| exact H1| exact X]).
  assert (SKA1 : PESKA.sink_atA RSEGS L ar P M1 v (PESK.SK B (z + 1) cap')).
  { apply (sink_at_xfer _ _ LK cr' Aw M model LK cr' Aw M1 model1 _ HH MO HH1 MO1 INC INC SKA); cbn [PESK.sk_b PESK.sk_z PESK.sk_c].
    - apply KEEP; [clear; lia| clear - O1; lia| clear - O2 SLO SHI SPT; lia| exact W0].
    - replace (B + (z + 1)) with (B + z + 1) by (clear; lia). apply VUP; [right; clear; lia| exact C0].
    - apply KEEP; [clear; lia| clear - O1; lia| clear - O2 SLO SHI SPT; lia| exact W16].
    - intros _. apply AGS; clear - B4 BCEIL SLO SHI SPT; lia. }
  apply (finish fx1 R1 M1 model1 LK Aw (PESK.SK B (z + 1) cap') cr' A1 A2).
  - intros i Hi; cbn in Hi.
    destruct Hi as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]];
    [exact A8| exact A9| exact A18| exact A19| exact A20| rewrite (KS1 21%nat) by inl; apply (E2122 21%nat); left; reflexivity| rewrite (KS1 22%nat) by inl; apply (E2122 22%nat); right; left; reflexivity].
  - apply (kept0_of R R1 KP); intros i Hi; apply KS1; cbn in Hi; repeat (destruct Hi as [<-|Hi]; [inl|]); destruct Hi.
  - exact SO1. - exact MO1.
  - unfold PESK.sink_own; cbn [PESK.sk_b PESK.sk_c]. replace (cap' =? 0) with false by (symmetry; apply Z.eqb_neq; clear - CP Ecap ZC0; subst cap'; pose proof (CP ltac:(lia)); lia). exact HH1.
  - rewrite Esk; unfold PESK.sk_push; cbn [PESK.sk_b PESK.sk_z PESK.sk_c]. replace (z <? c) with false by (symmetry; apply Z.ltb_ge; clear - EZC; lia). rewrite Ecap. reflexivity.
  - exact SKA1.
  - rewrite Esk; cbn [PESK.sk_c]. exact CK.
Qed.

Definition ssaves (M : word -> option byte) (e18 : Z) : Prop :=
  L5.u64_at RSEGS M (S - 56) RA_SLOW /\ L5.u64_at RSEGS M (S - 64) (v + 8) /\ L5.u64_at RSEGS M (S - 72) pv /\ L5.u64_at RSEGS M (S - 80) e18
  /\ L5.u64_at RSEGS M (S - 88) ((v + 8) / 8 + SBL) /\ L5.u64_at RSEGS M (S - 96) SBL /\ L5.u64_at RSEGS M (S - 104) (U 21) /\ L5.u64_at RSEGS M (S - 112) (U 22).

Lemma sh4096 s : s mod 16 = 0 -> (s - 4096) / 8 + 2147450880 = s / 8 + 2147450368.
Proof.
  intros H. pose proof (Z.div_mod s 16 ltac:(clear; lia)) as D. rewrite H, Z.add_0_r in D.
  replace s with (2 * (s / 16) * 8) by (clear - D; lia). replace (2 * (s / 16) * 8 - 4096) with ((2 * (s / 16) - 512) * 8) by (clear; lia).
  rewrite !Z.div_mul by (clear; lia). clear; lia.
Qed.

Lemma tail_S4 (fx : FPState) R M model LK Aw cr' B b z c cap' e18 :
  sk = PESK.SK b z c -> z = c -> cap' = PESK.cap_next c -> 0 <= e18 <= 2 ^ 47 ->
  getr R (reg 2) = Z_to_bv 64 (S - 160) -> getr R (reg 8) = Z_to_bv 64 (B + z + 1) -> getr R (reg 9) = Z_to_bv 64 v -> getr R (reg 18) = Z_to_bv 64 pv ->
  getr R (reg 20) = Z_to_bv 64 ((v + 8) / 8 + SBL) -> getr R (reg 21) = Z_to_bv 64 SBL -> kept1 R ->
  stok model LK Aw -> mem_ok M -> saves M -> ssaves M e18 -> ri_inv HI ([(B, cap')] ++ LB) FF LK cr' Aw M (vml_of model) ->
  PESKA.sink_atA RSEGS L ar P M v (PESK.SK B (z + 1) cap') ->
  PMSP.credit_keep cr0 cr' (PESKA.spa_pot P c) (PESKA.spa_pot P cap') ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0xaf274 M model) K.
Proof using All.
  intros Esk EZC Ecap E18B E2 E8 E9 E18 E20 E21 KP SO MO SV SSV HH SKA CK.
  destruct (nfacts _ LK cr' Aw M model HH MO) as ((A16 & SLO & SHI & SPT & C0') & (O1 & O2 & O5 & ODEF) & BF). unfold nsh in O5.
  destruct (vfacts _ LK cr' Aw M model HH MO) as (X0 & X1 & X2 & XW & XZ & XWV & XSZ & XAV).
  pose proof SV as (S8 & S16 & S24 & S32 & S40 & S48). pose proof SSV as (T56 & T64 & T72 & T80 & T88 & T96 & T104 & T112). pose proof pv_num as (PV4 & PV47).
  assert (INC : incl (PESK.sink_own (PESK.SK B (z + 1) cap')) [(B, cap')]).
  { unfold PESK.sink_own; cbn [PESK.sk_b PESK.sk_c]. destruct (cap' =? 0); [intros x []| apply incl_refl]. }
  destruct (sk_facts _ LK cr' Aw M model _ HH MO SKA INC) as (ZC1 & C31 & B0 & _ & LIVE1). cbn [PESK.sk_b PESK.sk_z PESK.sk_c] in ZC1, C31, B0, LIVE1.
  pose proof (PESK.cap_next_pos c) as CP. pose proof sk0_num as (ZC0 & _). rewrite Esk in ZC0. cbn [PESK.sk_z PESK.sk_c] in ZC0.
  destruct (LIVE1 ltac:(clear - CP Ecap ZC0; subst cap'; pose proof (CP ltac:(lia)); lia)) as (B4 & BCEIL & B16 & BSH & BIMG & BV).
  assert (DJ1 : 2147446784 + 17592186048512 <= v \/ v + 24 <= 2147446784) by (clear - O5; lia).
  assert (DJ2 : S - 256 + 256 <= v \/ v + 24 <= S - 256) by (clear - O2 SLO; lia).
  assert (XSS : L5KA.zeros_at (mrestrict (ahid Aw model) M) (S / 8 + 2147450368) 512) by (rewrite <- (sh4096 S A16); apply XSZ; clear - A16; lia).
  pose proof (PEASKPP.askS4_conc fx R (mrestrict (ahid Aw model) M) (fun j => match j with 2%nat => S | 10%nat => v | 33%nat => e18 | 36%nat => pv | 41%nat => B + z + 1
     | 50%nat => U 21 | 51%nat => U 22
     | 55%nat => bv_unsigned (getr R (reg 10)) | 56%nat => bv_unsigned (getr R (reg 11)) | 57%nat => bv_unsigned (getr R (reg 12)) | _ => 0 end)) as PP.
  cbn beta iota in PP. replace (e18 + 0) with e18 in PP by (rewrite Z.add_0_r; reflexivity).
  pose proof (UB 21%nat) as UB21. pose proof (UB 22%nat) as UB22.
  hide_disj. L5SAR.feed PP ltac:(first [apply wid | apply wrng | pfeed XW XSZ XAV]). unhide.
  destruct PP as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & A1 & A2 & A8 & A9 & A10 & A18 & A19 & A20 & A21 & A22).
  apply (piece_ro fx fx1 R 0xaf274 R1 RET_S _ M model cr' LK Aw M1v HH SO MO MS1 MG1 FRZ1). intros model1 HH1 SO1.
  pose proof SO1 as (AM1 & _).
  unfold PMSPA.cfg.
  apply (PMASK.ret_exit L ar C HI LY HIok fx1 R1 M model1 K _ FF LK cr' Aw RET_S RA_SLOW W_af24c HH1 AM1 F_af24c eq_refl D_af24c A1 ltac:(clear; lia) ltac:(reflexivity)).
  intros model2 MRT2 AM2 HH2.
  apply (tail_R fx1 R1 M model2 LK Aw cr' B b z c cap' e18 Esk EZC Ecap ltac:(clear - E18B; lia) A2 A8 A9 A10 A18 A19 A20).
  - intros i Hi. destruct Hi as [<-|[<-|[]]]; [exact A21| exact A22].
  - apply (kept0_of1 R1); [| exact A21| exact A22]. apply (kept1_of R R1 KP). intros i Hi; apply KS1; cbn in Hi; repeat (destruct Hi as [<-|Hi]; [inl|]); destruct Hi.
  - exact (stok_step model1 LK Aw model2 LK Aw SO1 AM2 MRT2 (incl_refl _) (incl_refl _)).
  - exact MO. - exact SV. - exact HH2. - exact SKA. - exact CK.
Qed.

Lemma ssaves_callee HL LK cr Aw M model M' HL' sp' scr' W' e18 :
  ri_inv HI (HL ++ LB) FF LK cr Aw M (vml_of model) -> mem_ok M ->
  L5CA.ahpres L ar (HL' ++ LB) FF sp' scr' W' M M' -> S - 12288 <= sp' - scr' -> sp' <= S - 112 -> 0 <= scr' ->
  (forall rg, In rg W' -> exists q m, In (q, m) HL /\ q <= fst rg /\ fst rg + snd rg <= q + m) -> ssaves M e18 -> ssaves M' e18.
Proof.
  intros HH MO HP H1 H2 H3 WIN (T56 & T64 & T72 & T80 & T88 & T96 & T104 & T112).
  repeat split; (eapply (cell_callee HL LK cr Aw M model M' HL' sp' scr' W' _ _ HH MO HP H1 ltac:(lia) H3 WIN); [left; lia| eassumption]).
Qed.
Lemma ssaves_piece HL LK cr Aw M model (M1 : word -> option byte) (Wp : Z -> Prop) e18 :
  ri_inv HI (HL ++ LB) FF LK cr Aw M (vml_of model) -> mem_ok M ->
  (forall i, 0 <= i < 2 ^ 64 -> ~ Wp i -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i)) -> (forall i, Wp i -> ~ (S - 112 <= i < S - 48)) -> ssaves M e18 -> ssaves M1 e18.
Proof.
  intros HH MO FR NP (T56 & T64 & T72 & T80 & T88 & T96 & T104 & T112). destruct (nfacts HL LK cr Aw M model HH MO) as ((A16 & SLO & SHI & SPT & C0) & _).
  repeat split; (eapply (cell_piece M M1 Wp _ _ FR); [intros i Hi Pi; apply (NP i Pi); lia| lia| lia| eassumption]).
Qed.

Lemma tail_S3 (fx : FPState) R M model LK Aw cr' B b z c cap' e18 :
  sk = PESK.SK b z c -> z = c -> cap' = PESK.cap_next c -> 0 < c -> 0 <= e18 <= 2 ^ 47 ->
  getr R (reg 2) = Z_to_bv 64 (S - 160) -> getr R (reg 8) = Z_to_bv 64 (v + 8) -> getr R (reg 9) = Z_to_bv 64 v -> getr R (reg 18) = Z_to_bv 64 pv ->
  getr R (reg 20) = Z_to_bv 64 ((v + 8) / 8 + SBL) -> getr R (reg 21) = Z_to_bv 64 SBL -> getr R (reg 22) = Z_to_bv 64 z -> kept1 R ->
  stok model LK Aw -> mem_ok M -> saves M -> ssaves M e18 -> ri_inv HI ([(B, cap'); (b, c)] ++ LB) FF LK cr' Aw M (vml_of model) ->
  PESKA.sink_atA RSEGS L ar P M v (PESK.SK B (z + 1) cap') ->
  L5.u64_at RSEGS M (S - 152) b -> L5.u64_at RSEGS M (S - 144) b -> L5.u64_at RSEGS M (S - 136) b -> L5.u64_at RSEGS M (S - 128) (b + c) ->
  PMSP.credit_keep cr0 cr' (PESKA.spa_pot P c) (PESKA.spa_pot P cap') ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0xaf244 M model) K.
Proof using All.
  intros Esk EZC Ecap HC E18B E2 E8 E9 E18 E20 E21 E22 KP SO MO SV SSV HH SKA Q1 Q2 Q3 Q4 CK.
  destruct (nfacts _ LK cr' Aw M model HH MO) as ((A16 & SLO & SHI & SPT & C0') & (O1 & O2 & O5 & ODEF) & BF). unfold nsh in O5.
  destruct (vfacts _ LK cr' Aw M model HH MO) as (X0 & X1 & X2 & XW & XZ & XWV & XSZ & XAV).
  pose proof SV as (S8 & S16 & S24 & S32 & S40 & S48). pose proof SSV as (T56 & T64 & T72 & T80 & T88 & T96 & T104 & T112). pose proof pv_num as (PV4 & PV47).
  assert (INC : incl (PESK.sink_own (PESK.SK B (z + 1) cap')) [(B, cap'); (b, c)]).
  { unfold PESK.sink_own; cbn [PESK.sk_b PESK.sk_c]. destruct (cap' =? 0); [intros x []| intros x [<-|[]]; left; reflexivity]. }
  destruct (sk_facts _ LK cr' Aw M model _ HH MO SKA INC) as (ZC1 & C31 & B0 & _ & LIVE1). cbn [PESK.sk_b PESK.sk_z PESK.sk_c] in ZC1, C31, B0, LIVE1.
  pose proof (PESK.cap_next_pos c) as CP. pose proof sk0_num as (ZC0 & C310 & _ & _ & LIVE0). rewrite Esk in ZC0, C310, LIVE0. cbn [PESK.sk_b PESK.sk_z PESK.sk_c] in ZC0, C310, LIVE0.
  destruct (LIVE1 ltac:(clear - CP Ecap ZC0; subst cap'; pose proof (CP ltac:(lia)); lia)) as (B4 & BCEIL & B16 & BSH & BIMG & BV).
  destruct (LIVE0 HC) as (B4o & BCEILo & B16o & BSHo & BIMGo & BVo). unfold nsh in BSHo.
  assert (DJ1 : 2147446784 + 17592186048512 <= v \/ v + 24 <= 2147446784) by (clear - O5; lia).
  assert (DJ2 : S - 256 + 256 <= v \/ v + 24 <= S - 256) by (clear - O2 SLO; lia).
  assert (DJ4 : 2147446784 + 17592186048512 <= b \/ b + c <= 2147446784) by (clear - BSHo; lia).
  assert (DJ5 : 65536 + 6848512 <= b \/ b + c <= 65536) by (clear - BIMGo; lia).
  assert (XSS : L5KA.zeros_at (mrestrict (ahid Aw model) M) (S / 8 + 2147450368) 512) by (rewrite <- (sh4096 S A16); apply XSZ; clear - A16; lia).
  pose proof SKA as (W0 & W8 & W16 & _). cbn [PESK.sk_b PESK.sk_z PESK.sk_c] in W0, W8, W16.
  pose proof W8 as W8f. replace (B + (z + 1)) with (B + z + 1) in W8f by (clear; lia).
  pose proof (PEASKPP.askS3_conc fx R (mrestrict (ahid Aw model) M) (fun j => match j with 2%nat => S | 10%nat => v | 33%nat => b | 34%nat => z | 35%nat => c | 36%nat => pv | 37%nat => B | 38%nat => cap'
     | 55%nat => bv_unsigned (getr R (reg 10)) | 56%nat => bv_unsigned (getr R (reg 11)) | 57%nat => bv_unsigned (getr R (reg 12)) | _ => 0 end)) as PP.
  cbn beta iota in PP. replace (z + B) with (B + z) in PP by (clear; lia).
  hide_disj. L5SAR.feed PP ltac:(first [apply wid | apply wrng | pfeed XW XSZ XAV]). unhide.
  destruct PP as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & A1 & A8 & A10 & A11 & C0).
  apply (piece_step fx fx1 R 0xaf244 R1 OPDEL _ M model cr' LK Aw M1v (fun a => S - 136 <= a < S - 136 + 8) HH SO MO MS1 MG1 FRZ1); [intros a Pa; left; clear - Pa; lia|].
  intros M1 model1 HH1 SO1 MO1 FR1 VUP AGS.
  pose proof SO1 as (AM1 & _).
  pose proof (saves_piece _ LK cr' Aw M model M1 (fun a => S - 136 <= a < S - 136 + 8) HH MO FR1 ltac:(intros i Pi; cbv beta in Pi; clear - Pi; lia) SV) as SV1.
  pose proof (ssaves_piece _ LK cr' Aw M model M1 (fun a => S - 136 <= a < S - 136 + 8) e18 HH MO FR1 ltac:(intros i Pi; cbv beta in Pi; clear - Pi; lia) SSV) as SSV1.
  assert (KEEP : forall a val, v <= a -> a + 8 <= v + 24 -> L5.u64_at RSEGS M a val -> L5.u64_at RSEGS M1 a val)
    by (intros a val Ha Hb X; apply (L5C.u64_at_agree RSEGS M M1); [intros i Hi; apply FR1; [clear - Hi Ha Hb O1 O2 SLO SHI SPT; lia| clear - Hi Ha Hb O2 SLO; lia]| clear - Ha O1; lia| clear - Hb O2 SLO SHI SPT; lia| exact X]).
  assert (SKA1 : PESKA.sink_atA RSEGS L ar P M1 v (PESK.SK B (z + 1) cap')).
  { apply (sink_at_xfer _ _ LK cr' Aw M model LK cr' Aw M1 model1 _ HH MO HH1 MO1 INC INC SKA); cbn [PESK.sk_b PESK.sk_z PESK.sk_c].
    - apply KEEP; [clear; lia| clear; lia| exact W0].
    - apply KEEP; [clear; lia| clear; lia| exact W8].
    - apply KEEP; [clear; lia| clear; lia| exact W16].
    - intros _. apply AGS; clear - B4 BCEIL SLO SHI SPT; lia. }

  destruct (cstk _ LK cr' Aw M1 model1 160 4096 HH1 MO1 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(reflexivity) ltac:(reflexivity)) as (STKc & _).
  destruct (PNAEK.own_facts L ar C HI HIok B cap' _ FF LK cr' Aw M1 _ HH1) as (BAp & _). pose proof (BAp b c ltac:(left; reflexivity)) as BNE.
  assert (NEQ : (B =? b) = false) by (apply Z.eqb_neq; clear - BNE HC CP Ecap ZC0; subst cap'; pose proof (CP ltac:(lia)); lia).
  assert (KS2 : forall i, In i [2; 3; 4; 23; 24; 25; 26; 27]%nat -> getr R1 (reg i) = getr R (reg i)).
  { intros i Hi. apply KS1. clear - Hi. cbn in Hi. repeat (destruct Hi as [<-|Hi]; [inl|]). destruct Hi. }
  pose proof OPD as OD. unfold PMSPA.opdel_spec, PMSPA.opdel_spec_at in OD.
  assert (E10 : getr R1 10%bv = Z_to_bv 64 b) by (rewrite L5K.rl10; exact A10).
  assert (E1 : getr R1 1%bv = Z_to_bv 64 0xaf274) by (rewrite L5K.rl1; exact A1).
  assert (E2' : getr R1 2%bv = Z_to_bv 64 (S - 160)) by (rewrite L5K.rl2, (KS2 2%nat) by inl; exact E2).
  assert (E4 : getr R1 4%bv = Z_to_bv 64 (hl_tp L)) by (rewrite L5K.rl4, (KS2 4%nat) by inl; rewrite (KP 4%nat) by (right; left; reflexivity); exact Rtp0).
  unfold PMSPA.cfg.
  apply (OD fx1 R1 M1 model1 K _ FF LK Aw cr' b c (S - 160) 0xaf274 HH1 AM1 K0 ltac:(right; left; reflexivity) E10 E1 ltac:(split; [clear; lia| reflexivity]) E2' E4 STKc).
  intros fx2 R2 M2 model2 Aw2 RP2 HP2 MRT2 IAW2 AM2 HH2.
  cbn [app lb_remove fst] in HP2, HH2. rewrite NEQ, Z.eqb_refl in HP2, HH2. unfold PMSPA.OPDEL_SCR, PMSPA.MALLOC_SCR in HP2.
  assert (WIN : forall rg, In rg (@nil L5.range) -> exists q m, In (q, m) [(B, cap'); (b, c)] /\ q <= fst rg /\ fst rg + snd rg <= q + m) by (intros rg []).
  pose proof (mem_ok_callee [(B, cap'); (b, c)] [(B, cap')] LK cr' Aw M1 model1 M2 (S - 160) 4096 _ HH1 MO1 HP2 ltac:(clear - SLO C0'; lia) ltac:(clear; lia) ltac:(clear; lia) WIN) as MO2.
  pose proof (saves_callee [(B, cap'); (b, c)] LK cr' Aw M1 model1 M2 [(B, cap')] (S - 160) 4096 _ HH1 MO1 HP2 ltac:(clear - SLO C0'; lia) ltac:(clear; lia) ltac:(clear; lia) WIN SV1) as SV2.
  pose proof (ssaves_callee [(B, cap'); (b, c)] LK cr' Aw M1 model1 M2 [(B, cap')] (S - 160) 4096 _ e18 HH1 MO1 HP2 ltac:(clear - SLO C0'; lia) ltac:(clear; lia) ltac:(clear; lia) WIN SSV1) as SSV2.
  pose proof HP2 as (EK2 & _).
  assert (SKA2 : PESKA.sink_atA RSEGS L ar P M2 v (PESK.SK B (z + 1) cap')).
  { pose proof SKA1 as (W0' & W8' & W16' & _). cbn [PESK.sk_b PESK.sk_z PESK.sk_c] in W0', W8', W16'.
    apply (sink_at_xfer _ [(B, cap')] LK cr' Aw M1 model1 LK cr' Aw2 M2 model2 _ HH1 MO1 HH2 MO2 INC); cbn [PESK.sk_b PESK.sk_z PESK.sk_c].
    - unfold PESK.sink_own; cbn [PESK.sk_b PESK.sk_c]. destruct (cap' =? 0); [intros x []| apply incl_refl].
    - exact SKA1.
    - exact (cell_callee _ LK cr' Aw M1 model1 M2 [(B, cap')] (S - 160) 4096 [] v B HH1 MO1 HP2 ltac:(clear - SLO C0'; lia) ltac:(clear; lia) ltac:(clear; lia) WIN ltac:(right; clear; lia) W0').
    - exact (cell_callee _ LK cr' Aw M1 model1 M2 [(B, cap')] (S - 160) 4096 [] (v + 8) (B + (z + 1)) HH1 MO1 HP2 ltac:(clear - SLO C0'; lia) ltac:(clear; lia) ltac:(clear; lia) WIN ltac:(right; clear; lia) W8').
    - exact (cell_callee _ LK cr' Aw M1 model1 M2 [(B, cap')] (S - 160) 4096 [] (v + 16) (B + cap') HH1 MO1 HP2 ltac:(clear - SLO C0'; lia) ltac:(clear; lia) ltac:(clear; lia) WIN ltac:(right; clear; lia) W16').
    - intros _. apply (blksh_ek _ FF (S - 160) 4096 [] M1 M2 B cap' EK2 (PMKA.wapp_nil) ltac:(left; reflexivity)); clear - B4 BCEIL SPT; lia. }
  apply (tail_S4 fx2 R2 M2 model2 LK Aw2 cr' B b z c cap' e18 Esk EZC Ecap E18B).
  - rewrite (L5SAR.cs_of_preserved R1 R2 2%nat RP2) by inl. exact E2'.
  - rewrite (L5SAR.cs_of_preserved R1 R2 8%nat RP2) by inl. exact A8.
  - rewrite (L5SAR.cs_of_preserved R1 R2 9%nat RP2) by inl. rewrite (KS1 9%nat) by inl. exact E9.
  - rewrite (L5SAR.cs_of_preserved R1 R2 18%nat RP2) by inl. rewrite (KS1 18%nat) by inl. exact E18.
  - rewrite (L5SAR.cs_of_preserved R1 R2 20%nat RP2) by inl. rewrite (KS1 20%nat) by inl. exact E20.
  - rewrite (L5SAR.cs_of_preserved R1 R2 21%nat RP2) by inl. rewrite (KS1 21%nat) by inl. exact E21.
  - apply (kept1_pres R1 R2); [| exact RP2]. apply (kept1_of R R1 KP). intros i Hi. apply KS2. clear - Hi. cbn in Hi |- *. tauto.
  - exact (stok_step model1 LK Aw model2 LK Aw2 SO1 AM2 MRT2 (incl_refl _) IAW2).
  - exact MO2. - exact SV2. - exact SSV2. - exact HH2. - exact SKA2. - exact CK.
Qed.

Lemma tail_S3n (fx : FPState) R M model LK Aw cr' B :
  sk = PESK.SK 0 0 0 ->
  getr R (reg 2) = Z_to_bv 64 (S - 160) -> getr R (reg 8) = Z_to_bv 64 (v + 8) -> getr R (reg 9) = Z_to_bv 64 v -> getr R (reg 18) = Z_to_bv 64 pv ->
  getr R (reg 20) = Z_to_bv 64 ((v + 8) / 8 + SBL) -> getr R (reg 21) = Z_to_bv 64 SBL -> getr R (reg 22) = Z_to_bv 64 0 -> kept1 R ->
  stok model LK Aw -> mem_ok M -> saves M -> ssaves M 0 -> ri_inv HI ([(B, 1)] ++ LB) FF LK cr' Aw M (vml_of model) ->
  PESKA.sink_atA RSEGS L ar P M v (PESK.SK B 1 1) ->
  L5.u64_at RSEGS M (S - 152) 0 -> L5.u64_at RSEGS M (S - 144) 0 -> L5.u64_at RSEGS M (S - 136) 0 -> L5.u64_at RSEGS M (S - 128) 0 ->
  PMSP.credit_keep cr0 cr' (PESKA.spa_pot P 0) (PESKA.spa_pot P 1) ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0xaf244 M model) K.
Proof using All.
  intros Esk E2 E8 E9 E18 E20 E21 E22 KP SO MO SV SSV HH SKA Q1 Q2 Q3 Q4 CK.
  destruct (nfacts _ LK cr' Aw M model HH MO) as ((A16 & SLO & SHI & SPT & C0') & (O1 & O2 & O5 & ODEF) & BF). unfold nsh in O5.
  destruct (vfacts _ LK cr' Aw M model HH MO) as (X0 & X1 & X2 & XW & XZ & XWV & XSZ & XAV).
  pose proof SV as (S8 & S16 & S24 & S32 & S40 & S48). pose proof SSV as (T56 & T64 & T72 & T80 & T88 & T96 & T104 & T112). pose proof pv_num as (PV4 & PV47).
  assert (INC : incl (PESK.sink_own (PESK.SK B 1 1)) [(B, 1)]) by (unfold PESK.sink_own; cbn; apply incl_refl).
  destruct (sk_facts _ LK cr' Aw M model _ HH MO SKA INC) as (ZC1 & C31 & B0 & _ & LIVE1). cbn [PESK.sk_b PESK.sk_z PESK.sk_c] in ZC1, C31, B0, LIVE1.
  destruct (LIVE1 ltac:(clear; lia)) as (B4 & BCEIL & B16 & BSH & BIMG & BV).
  assert (DJ1 : 2147446784 + 17592186048512 <= v \/ v + 24 <= 2147446784) by (clear - O5; lia).
  assert (DJ2 : S - 256 + 256 <= v \/ v + 24 <= S - 256) by (clear - O2 SLO; lia).
  assert (XSS : L5KA.zeros_at (mrestrict (ahid Aw model) M) (S / 8 + 2147450368) 512) by (rewrite <- (sh4096 S A16); apply XSZ; clear - A16; lia).
  pose proof SKA as (W0 & W8 & W16 & _). cbn [PESK.sk_b PESK.sk_z PESK.sk_c] in W0, W8, W16.
  pose proof (PEASKPP.askS3n_conc fx R (mrestrict (ahid Aw model) M) (fun j => match j with 2%nat => S | 10%nat => v | 36%nat => pv | 37%nat => B | 50%nat => U 21 | 51%nat => U 22
     | 55%nat => bv_unsigned (getr R (reg 10)) | 56%nat => bv_unsigned (getr R (reg 11)) | 57%nat => bv_unsigned (getr R (reg 12)) | _ => 0 end)) as PP.
  cbn beta iota in PP.
  pose proof (UB 21%nat) as UB21. pose proof (UB 22%nat) as UB22.
  hide_disj. L5SAR.feed PP ltac:(first [apply wid | apply wrng | pfeed XW XSZ XAV]). unhide.
  destruct PP as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & A1 & A2 & A9 & A10 & A11 & A18 & A19 & A20 & A21 & A22).
  apply (piece_step fx fx1 R 0xaf244 R1 RET_S _ M model cr' LK Aw M1v (fun a => S - 136 <= a < S - 136 + 8) HH SO MO MS1 MG1 FRZ1); [intros a Pa; left; clear - Pa; lia|].
  intros M1 model1 HH1 SO1 MO1 FR1 VUP AGS.
  pose proof SO1 as (AM1 & _).
  pose proof (saves_piece _ LK cr' Aw M model M1 (fun a => S - 136 <= a < S - 136 + 8) HH MO FR1 ltac:(intros i Pi; cbv beta in Pi; clear - Pi; lia) SV) as SV1.
  assert (KEEP : forall a val, v <= a -> a + 8 <= v + 24 -> L5.u64_at RSEGS M a val -> L5.u64_at RSEGS M1 a val)
    by (intros a val Ha Hb X; apply (L5C.u64_at_agree RSEGS M M1); [intros i Hi; apply FR1; [clear - Hi Ha Hb O1 O2 SLO SHI SPT; lia| clear - Hi Ha Hb O2 SLO; lia]| clear - Ha O1; lia| clear - Hb O2 SLO SHI SPT; lia| exact X]).
  assert (SKA1 : PESKA.sink_atA RSEGS L ar P M1 v (PESK.SK B 1 1)).
  { apply (sink_at_xfer _ _ LK cr' Aw M model LK cr' Aw M1 model1 _ HH MO HH1 MO1 INC INC SKA); cbn [PESK.sk_b PESK.sk_z PESK.sk_c].
    - apply KEEP; [clear; lia| clear; lia| exact W0].
    - apply KEEP; [clear; lia| clear; lia| exact W8].
    - apply KEEP; [clear; lia| clear; lia| exact W16].
    - intros _. apply AGS; clear - B4 BCEIL SLO SHI SPT; lia. }
  unfold PMSPA.cfg.
  apply (PMASK.ret_exit L ar C HI LY HIok fx1 R1 M1 model1 K _ FF LK cr' Aw RET_S RA_SLOW W_af24c HH1 AM1 F_af24c eq_refl D_af24c A1 ltac:(clear; lia) ltac:(reflexivity)).
  intros model2 MRT2 AM2 HH2.
  apply (tail_R fx1 R1 M1 model2 LK Aw cr' B 0 0 0 1 0 Esk eq_refl eq_refl ltac:(clear; lia) A2).
  - rewrite (KS1 8%nat) by inl. exact E8.
  - exact A9.
  - rewrite A10. f_equal. clear; lia.
  - exact A18. - exact A19. - exact A20.
  - intros i Hi. destruct Hi as [<-|[<-|[]]]; [exact A21| exact A22].
  - apply (kept0_of1 R1); [| exact A21| exact A22]. apply (kept1_of R R1 KP). intros i Hi; apply KS1; cbn in Hi; repeat (destruct Hi as [<-|Hi]; [inl|]); destruct Hi.
  - exact (stok_step model1 LK Aw model2 LK Aw SO1 AM2 MRT2 (incl_refl _) (incl_refl _)).
  - exact MO1. - exact SV1. - exact HH2. - exact SKA1. - exact CK.
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
Lemma annA_of_shadow_blk (M : word -> option byte) b c : shadow_blk M b c -> PMSPA.annA M b c c.
Proof. intros [Z0 P1]. split; [exact Z0|]. split; [exact P1|]. intros j Hj. exfalso. clear - Hj. lia. Qed.

Lemma sink_of_bat M B z' cap' : PEASKAN.bat RSEGS M v B z' cap' -> PESK.is_cap cap' -> ablock_range L ar B cap' -> PESKA.spa_cap P cap' -> cap' <= PESKA.spa_nmax P ->
  PESKA.sink_atA RSEGS L ar P M v (PESK.SK B z' cap').
Proof.
  intros (D24 & A24 & W0 & W8 & W16 & HZ & HC & B4 & B16 & DB & ACB & ANB) CAP ABR SCAP SNM.
  unfold PESKA.sink_atA. cbn [PESK.sk_b PESK.sk_z PESK.sk_c].
  split; [exact W0|]. split; [exact W8|]. split; [exact W16|]. split; [exact D24|]. split; [exact A24|].
  split; [exact HZ|]. split; [exact CAP|]. split; [intros X; exfalso; clear - X HC; lia|].
  intros _. split; [exact DB|]. split; [exact ACB|]. split; [exact ANB|]. split; [exact ABR|]. split; [exact SCAP| exact SNM].
Qed.

Lemma next_facts : PESK.sk_z sk = PESK.sk_c sk ->
  PESK.is_cap (PESK.cap_next (PESK.sk_c sk)) /\ 0 < PESK.cap_next (PESK.sk_c sk) <= PESKA.spa_nmax P.
Proof using All.
  intros EZ. pose proof SKA0 as (_ & _ & _ & _ & _ & _ & CAP & _ & LIVE). destruct (GROW EZ) as (G1 & _).
  split; [apply PESK.is_cap_next; exact CAP| exact G1].
Qed.

Lemma tail_W3 (fx : FPState) R M model LK Aw cr' B b z c cap' e18 :
  sk = PESK.SK b z c -> z = c -> cap' = PESK.cap_next c -> PESKA.spa_cap P cap'   -> 0 <= e18 <= 2 ^ 47 -> (c = 0 -> e18 = 0) ->
  getr R (reg 2) = Z_to_bv 64 (S - 208) -> getr R (reg 8) = Z_to_bv 64 (S - 152) -> getr R (reg 9) = Z_to_bv 64 v -> getr R (reg 18) = Z_to_bv 64 B ->
  getr R (reg 19) = Z_to_bv 64 SBL -> getr R (reg 20) = Z_to_bv 64 ((v + 8) / 8 + SBL) -> getr R (reg 21) = Z_to_bv 64 SBL -> getr R (reg 22) = Z_to_bv 64 z -> kept1 R ->
  stok model LK Aw -> mem_ok M -> saves M -> ssaves M e18 -> ri_inv HI (((B, cap') :: PESK.sink_own sk) ++ LB) FF LK cr' Aw M (vml_of model) ->
  hdr M b (b + z) (b + c) ->
  L5.u64_at RSEGS M (S - 152) B -> L5.u64_at RSEGS M (S - 144) (B + z) -> L5.u64_at RSEGS M (S - 136) (B + z + 1) -> L5.u64_at RSEGS M (S - 128) (B + cap') ->
  L5.u64_at RSEGS M (S - 168) 0xaf244 -> L5.u64_at RSEGS M (S - 176) (v + 8) -> L5.u64_at RSEGS M (S - 184) v -> L5.u64_at RSEGS M (S - 192) pv -> L5.u64_at RSEGS M (S - 200) (B + cap') ->
  shadow_blk M B cap' -> PMSPA.accA M B (z + 1) -> ablock_range L ar B cap' ->
  PMSP.credit_keep cr0 cr' (PESKA.spa_pot P c) (PESKA.spa_pot P cap') ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0xaf43c M model) K.
Proof using All.
  intros Esk EZC Ecap SCAPn E18B E18Z E2 E8 E9 E18 E19 E20 E21 E22 KP SO MO SV SSV HH HDR Q1 Q2 Q3 Q4 F1 F2 F3 F4 F5 SHB ACB ABR CK.
  destruct (nfacts _ LK cr' Aw M model HH MO) as ((A16 & SLO & SHI & SPT & C0') & (O1 & O2 & O5 & ODEF) & BF). unfold nsh in O5.
  destruct (vfacts _ LK cr' Aw M model HH MO) as (X0 & X1 & X2 & XW & XZ & XWV & XSZ & XAV).
  pose proof SV as (S8 & S16 & S24 & S32 & S40 & S48). pose proof SSV as (T56 & T64 & T72 & T80 & T88 & T96 & T104 & T112). pose proof pv_num as (PV4 & PV47).
  pose proof HDR as (W0 & W8 & W16).
  pose proof (PESK.cap_next_pos c) as CP. pose proof sk0_num as (ZC0 & C310 & B00 & BZ0 & LIVE0). rewrite Esk in ZC0, C310, B00, BZ0, LIVE0. cbn [PESK.sk_b PESK.sk_z PESK.sk_c] in ZC0, C310, B00, BZ0, LIVE0.
  destruct (next_facts ltac:(rewrite Esk; exact EZC)) as (CAPn & NMn). rewrite Esk in CAPn, NMn. cbn [PESK.sk_c] in CAPn, NMn. rewrite <- Ecap in CAPn, NMn.
  destruct (BF B cap' ltac:(left; reflexivity)) as (B4 & _ & BCEIL & B16 & BSH & BV & BDEF). unfold nsh in BSH.
  assert (BC47 : 0 <= b + c <= 2 ^ 47) by (destruct (Z.eq_dec c 0) as [E0|NE]; [rewrite (BZ0 E0), E0; clear; lia| destruct (LIVE0 ltac:(clear - NE ZC0; lia)) as (X1' & X2' & _); clear - X1' X2' SPT ZC0; lia]).
  assert (ZC1 : 0 <= z + 1 <= cap') by (clear - ZC0 EZC Ecap CP; subst cap'; unfold PESK.cap_next; destruct (c =? 0) eqn:E0; [apply Z.eqb_eq in E0| apply Z.eqb_neq in E0]; lia).
  assert (DJ1 : 2147446784 + 17592186048512 <= v \/ v + 24 <= 2147446784) by (clear - O5; lia).
  assert (DJ2 : S - 256 + 256 <= v \/ v + 24 <= S - 256) by (clear - O2 SLO; lia).
  assert (XSS : L5KA.zeros_at (mrestrict (ahid Aw model) M) (S / 8 + 2147450368) 512) by (rewrite <- (sh4096 S A16); apply XSZ; clear - A16; lia).
  pose proof (PEASKPP.askW3_conc fx R (mrestrict (ahid Aw model) M) (fun j => match j with 2%nat => S | 10%nat => v | 33%nat => b | 34%nat => z | 35%nat => c | 36%nat => pv | 37%nat => B | 38%nat => cap'
     | 55%nat => bv_unsigned (getr R (reg 10)) | 56%nat => bv_unsigned (getr R (reg 11)) | 57%nat => bv_unsigned (getr R (reg 12)) | _ => 0 end)) as PP.
  cbn beta iota in PP. replace (z + B) with (B + z) in PP by (clear; lia).
  hide_disj. L5SAR.feed PP ltac:(first [apply wid | apply wrng | pfeed XW XSZ XAV]). unhide.
  destruct PP as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & A1 & A2 & A8 & A10 & A11 & A12 & A18 & A19 & C152 & C128 & Cv16 & C136 & Cv8 & C144 & Cv0).
  apply (piece_step fx fx1 R 0xaf43c R1 ANNN _ M model cr' LK Aw M1v (fun a => (S - 152 <= a < S - 152 + 32) \/ (v + 0 <= a < v + 0 + 24)) HH SO MO MS1 MG1
           (fun a Ha Na => FRZ1 a Ha (fun X => Na (or_introl X)) (fun X => Na (or_intror X)))); [intros a [Pa|Pa]; [left; clear - Pa; lia| right; clear - Pa; lia]|].
  intros M1 model1 HH1 SO1 MO1 FR1 VUP AGS.
  pose proof SO1 as (AM1 & _).
  pose proof (saves_piece _ LK cr' Aw M model M1 (fun a => (S - 152 <= a < S - 152 + 32) \/ (v + 0 <= a < v + 0 + 24)) HH MO FR1 ltac:(intros i Pi; cbv beta in Pi; clear - Pi O2 SLO; lia) SV) as SV1.
  pose proof (ssaves_piece _ LK cr' Aw M model M1 (fun a => (S - 152 <= a < S - 152 + 32) \/ (v + 0 <= a < v + 0 + 24)) e18 HH MO FR1 ltac:(intros i Pi; cbv beta in Pi; clear - Pi O2 SLO; lia) SSV) as SSV1.
  assert (KP1 : kept1 R1) by (apply (kept1_of R R1 KP); intros i Hi; apply KS1; cbn in Hi; repeat (destruct Hi as [<-|Hi]; [inl|]); destruct Hi).
  assert (SHB1 : shadow_blk M1 B cap') by (apply (shblk_agree M M1 B cap'); [apply PMKA.mod16_8'; exact B16| clear - ZC1 ZC0; lia| apply AGS; clear - B4 BCEIL SLO SHI SPT; lia| exact SHB]).
  assert (ACB1 : PMSPA.accA M1 B (z + 1)) by (apply (PMFA.accA_agree M M1); [apply AGS; clear - B4 BCEIL SLO SHI SPT ZC1 ZC0; lia| exact ACB]).
  destruct (nfacts _ LK cr' Aw M1 model1 HH1 MO1) as (_ & (_ & _ & _ & ODEF1) & BF1). destruct (BF1 B cap' ltac:(left; reflexivity)) as (_ & _ & _ & _ & _ & _ & BDEF1).
  assert (BHDR : PEASKAN.bhdr RSEGS M1 v B (z + 1) cap').
  { split; [exact ODEF1|]. split; [apply VUP; [right; clear; lia| exact Cv0]|]. split; [replace (B + (z + 1)) with (B + z + 1) by (clear; lia); apply VUP; [right; clear; lia| exact Cv8]|].
    split; [apply VUP; [right; clear; lia| exact Cv16]|]. split; [exact ZC1|]. split; [clear - CP Ecap ZC0; subst cap'; pose proof (CP ltac:(lia)); lia|].
    split; [exact B4|]. split; [exact B16| exact BDEF1]. }

  destruct (centryS R1 _ LK cr' Aw M1 model1 160 0xaf244 HH1 MO1 KP1 A1 ltac:(split; [clear; lia| reflexivity]) A2 ltac:(clear; lia) ltac:(reflexivity)) as (ENT1 & FRS1).
  assert (E10 : getr R1 10%bv = Z_to_bv 64 v) by (rewrite L5K.rl10; exact A10).
  assert (E11 : getr R1 11%bv = Z_to_bv 64 (z + 1)) by (rewrite L5K.rl11; exact A11).
  assert (ACC1 : PMSPA.accA M1 v 24) by (destruct MO1 as (_ & _ & _ & X & _); exact X).
  pose proof ANNN_ok as AN. unfold PEASKANG.ann_new_s_spec in AN. unfold PMSPA.cfg.
  apply (AN fx1 R1 M1 model1 K (PESK.sink_own sk ++ LB) FF LK Aw cr' v (z + 1) B (z + 1) cap' (S - 160) 0xaf244 HH1 AM1 K0 ENT1 FRS1 E10 E11 AO V8 ACC1 BHDR eq_refl
            (annA_of_shadow_blk M1 B cap' SHB1)).
  intros fx2 R2 M2 model2 LK2 Aw2 RP2 BAT2 FRB2 HP2 MRT2 ILK2 IAW2 AM2 HH2.
  assert (WIN : forall rg, In rg (@nil L5.range) -> exists q m, In (q, m) ((B, cap') :: PESK.sink_own sk) /\ q <= fst rg /\ fst rg + snd rg <= q + m) by (intros rg []).
  pose proof (mem_ok_callee ((B, cap') :: PESK.sink_own sk) (PESK.sink_own sk) LK cr' Aw M1 model1 M2 (S - 160) 4096 [] HH1 MO1 HP2 ltac:(clear - SLO C0'; lia) ltac:(clear; lia) ltac:(clear; lia) WIN) as MO2.
  pose proof (saves_callee ((B, cap') :: PESK.sink_own sk) LK cr' Aw M1 model1 M2 (PESK.sink_own sk) (S - 160) 4096 [] HH1 MO1 HP2 ltac:(clear - SLO C0'; lia) ltac:(clear; lia) ltac:(clear; lia) WIN SV1) as SV2.
  pose proof (ssaves_callee ((B, cap') :: PESK.sink_own sk) LK cr' Aw M1 model1 M2 (PESK.sink_own sk) (S - 160) 4096 [] e18 HH1 MO1 HP2 ltac:(clear - SLO C0'; lia) ltac:(clear; lia) ltac:(clear; lia) WIN SSV1) as SSV2.
  pose proof (sink_of_bat M2 B (z + 1) cap' BAT2 CAPn ABR SCAPn (proj2 NMn)) as SKA2.
  assert (SO2 : stok model2 LK2 Aw2) by exact (stok_step model1 LK Aw model2 LK2 Aw2 SO1 AM2 MRT2 ILK2 IAW2).
  assert (KS2 : forall i, In i [2; 8; 9; 18; 19; 20; 21; 22]%nat -> getr R2 (reg i) = getr R1 (reg i)) by (intros i Hi; apply (L5SAR.cs_of_preserved R1 R2 i RP2); unfold L5SAR.cs_all; cbn in Hi |- *; clear - Hi; tauto).
  assert (CELL : forall a val, S - 160 <= a -> a + 8 <= S -> L5.u64_at RSEGS M1 a val -> L5.u64_at RSEGS M2 a val).
  { intros a val Ha Hb X. exact (cell_callee _ LK cr' Aw M1 model1 M2 (PESK.sink_own sk) (S - 160) 4096 [] a val HH1 MO1 HP2 ltac:(clear - SLO C0'; lia) ltac:(clear; lia) ltac:(clear; lia) WIN ltac:(left; clear - Ha Hb; lia) X). }
  destruct (Z.eq_dec c 0) as [EC0|NEC].
  -
    pose proof (BZ0 EC0) as EB0. pose proof EZC as EZ0. rewrite EC0 in EZ0. pose proof (E18Z EC0) as EE0.
    assert (EC1 : cap' = 1) by (rewrite Ecap, EC0; reflexivity).
    rewrite EB0, EZ0, EC0 in Esk. rewrite EB0 in C152, C144, C136, C128. rewrite EC0 in C128. rewrite EE0 in SSV2. rewrite EZ0 in SKA2, E22. rewrite EC1 in SKA2, HH2, CK. rewrite EC0 in CK.
    apply (tail_S3n fx2 R2 M2 model2 LK2 Aw2 cr' B Esk).
    + rewrite (KS2 2%nat) by inl. exact A2.
    + rewrite (KS2 8%nat) by inl. exact A8.
    + rewrite (KS2 9%nat) by inl. rewrite (KS1 9%nat) by inl. exact E9.
    + rewrite (KS2 18%nat) by inl. exact A18.
    + rewrite (KS2 20%nat) by inl. rewrite (KS1 20%nat) by inl. exact E20.
    + rewrite (KS2 21%nat) by inl. rewrite (KS1 21%nat) by inl. exact E21.
    + rewrite (KS2 22%nat) by inl. rewrite (KS1 22%nat) by inl. exact E22.
    + exact (kept1_pres R1 R2 KP1 RP2).
    + exact SO2. + exact MO2. + exact SV2. + exact SSV2.
    + rewrite Esk in HH2. exact HH2.
    + exact SKA2.
    + apply CELL; [clear; lia| clear; lia| apply VUP; [left; clear; lia| exact C152]].
    + apply CELL; [clear; lia| clear; lia| apply VUP; [left; clear; lia| exact C144]].
    + apply CELL; [clear; lia| clear; lia| apply VUP; [left; clear; lia| exact C136]].
    + apply CELL; [clear; lia| clear; lia| apply VUP; [left; clear; lia| exact C128]].
    + exact CK.
  -
    assert (HC : 0 < c) by (clear - NEC ZC0; lia).
    assert (OWN : PESK.sink_own sk = [(b, c)]) by (rewrite Esk; unfold PESK.sink_own; cbn [PESK.sk_b PESK.sk_c]; replace (c =? 0) with false by (symmetry; apply Z.eqb_neq; exact NEC); reflexivity).
    rewrite OWN in HH2.
    apply (tail_S3 fx2 R2 M2 model2 LK2 Aw2 cr' B b z c cap' e18 Esk EZC Ecap HC E18B).
    + rewrite (KS2 2%nat) by inl. exact A2.
    + rewrite (KS2 8%nat) by inl. exact A8.
    + rewrite (KS2 9%nat) by inl. rewrite (KS1 9%nat) by inl. exact E9.
    + rewrite (KS2 18%nat) by inl. exact A18.
    + rewrite (KS2 20%nat) by inl. rewrite (KS1 20%nat) by inl. exact E20.
    + rewrite (KS2 21%nat) by inl. rewrite (KS1 21%nat) by inl. exact E21.
    + rewrite (KS2 22%nat) by inl. rewrite (KS1 22%nat) by inl. exact E22.
    + exact (kept1_pres R1 R2 KP1 RP2).
    + exact SO2. + exact MO2. + exact SV2. + exact SSV2. + exact HH2. + exact SKA2.
    + apply CELL; [clear; lia| clear; lia| apply VUP; [left; clear; lia| exact C152]].
    + apply CELL; [clear; lia| clear; lia| apply VUP; [left; clear; lia| exact C144]].
    + apply CELL; [clear; lia| clear; lia| apply VUP; [left; clear; lia| exact C136]].
    + apply CELL; [clear; lia| clear; lia| apply VUP; [left; clear; lia| exact C128]].
    + exact CK.
Qed.

Lemma tail_W2 (fx : FPState) R M model LK Aw cr' B b z c cap' e18 :
  sk = PESK.SK b z c -> z = c -> cap' = PESK.cap_next c -> PESKA.spa_cap P cap'   -> 0 <= e18 <= 2 ^ 47 -> (c = 0 -> e18 = 0) ->
  getr R (reg 2) = Z_to_bv 64 (S - 208) -> getr R (reg 8) = Z_to_bv 64 (S - 152) -> getr R (reg 9) = Z_to_bv 64 v -> getr R (reg 18) = Z_to_bv 64 pv ->
  getr R (reg 19) = Z_to_bv 64 SBL -> getr R (reg 20) = Z_to_bv 64 ((v + 8) / 8 + SBL) -> getr R (reg 21) = Z_to_bv 64 SBL -> getr R (reg 22) = Z_to_bv 64 z -> kept1 R ->
  stok model LK Aw -> mem_ok M -> saves M -> ssaves M e18 -> ri_inv HI (((B, cap') :: PESK.sink_own sk) ++ LB) FF LK cr' Aw M (vml_of model) ->
  hdr M b (b + z) (b + c) ->
  L5.u64_at RSEGS M (S - 152) B -> L5.u64_at RSEGS M (S - 144) (B + z) -> L5.u64_at RSEGS M (S - 136) (B + z + 1) -> L5.u64_at RSEGS M (S - 128) (B + cap') ->
  L5.u64_at RSEGS M (S - 168) 0xaf244 -> L5.u64_at RSEGS M (S - 176) (v + 8) -> L5.u64_at RSEGS M (S - 184) v -> L5.u64_at RSEGS M (S - 192) pv -> L5.u64_at RSEGS M (S - 200) (B + cap') ->
  shadow_blk M B cap' -> (0 < c -> PMSPA.accA M b c) -> ablock_range L ar B cap' ->
  PMSP.credit_keep cr0 cr' (PESKA.spa_pot P c) (PESKA.spa_pot P cap') ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0xaf3e4 M model) K.
Proof using All.
  intros Esk EZC Ecap SCAPn E18B E18Z E2 E8 E9 E18 E19 E20 E21 E22 KP SO MO SV SSV HH HDR Q1 Q2 Q3 Q4 F1 F2 F3 F4 F5 SHB ACCb ABR CK.
  destruct (nfacts _ LK cr' Aw M model HH MO) as ((A16 & SLO & SHI & SPT & C0') & (O1 & O2 & O5 & ODEF) & BF). unfold nsh in O5.
  destruct (vfacts _ LK cr' Aw M model HH MO) as (X0 & X1 & X2 & XW & XZ & XWV & XSZ & XAV).
  pose proof SV as (S8 & S16 & S24 & S32 & S40 & S48). pose proof SSV as (T56 & T64 & T72 & T80 & T88 & T96 & T104 & T112). pose proof pv_num as (PV4 & PV47).
  pose proof HDR as (W0 & W8 & W16).
  pose proof (PESK.cap_next_pos c) as CP. pose proof sk0_num as (ZC0 & C310 & B00 & BZ0 & LIVE0). rewrite Esk in ZC0, C310, B00, BZ0, LIVE0. cbn [PESK.sk_b PESK.sk_z PESK.sk_c] in ZC0, C310, B00, BZ0, LIVE0.
  destruct (next_facts ltac:(rewrite Esk; exact EZC)) as (CAPn & NMn). rewrite Esk in CAPn, NMn. cbn [PESK.sk_c] in CAPn, NMn. rewrite <- Ecap in CAPn, NMn.
  destruct (BF B cap' ltac:(left; reflexivity)) as (B4 & _ & BCEIL & B16 & BSH & BV & BDEF). unfold nsh in BSH.
  assert (BC47 : 0 <= b + c <= 2 ^ 47) by (destruct (Z.eq_dec c 0) as [E0|NE]; [rewrite (BZ0 E0), E0; clear; lia| destruct (LIVE0 ltac:(clear - NE ZC0; lia)) as (X1' & X2' & _); clear - X1' X2' SLO SHI SPT ZC0; lia]).
  assert (ZC1 : 0 <= z + 1 <= cap') by (clear - ZC0 EZC Ecap CP; subst cap'; unfold PESK.cap_next; destruct (c =? 0) eqn:E0; [apply Z.eqb_eq in E0| apply Z.eqb_neq in E0]; lia).
assert (Z30 : 0 <= z <= HAR.NREQI).
  { pose proof SKA0 as (_ & _ & _ & _ & _ & _ & CAP0 & _). rewrite Esk in CAP0. cbn [PESK.sk_c] in CAP0.
    pose proof (COPYB c CAP0 ltac:(rewrite <- Ecap; exact NMn) ltac:(rewrite <- Ecap; exact SCAPn)) as CB. pose proof NREQI_ge as NG. clear - ZC0 EZC CB NG. lia. }
  assert (DJ1 : 2147446784 + 17592186048512 <= v \/ v + 24 <= 2147446784) by (clear - O5; lia).
  assert (DJ2 : S - 256 + 256 <= v \/ v + 24 <= S - 256) by (clear - O2 SLO; lia).
  assert (XSS : L5KA.zeros_at (mrestrict (ahid Aw model) M) (S / 8 + 2147450368) 512) by (rewrite <- (sh4096 S A16); apply XSZ; clear - A16; lia).
  pose proof (PEASKPP.askW2_conc fx R (mrestrict (ahid Aw model) M) (fun j => match j with 2%nat => S | 10%nat => v | 33%nat => b | 34%nat => z | 35%nat => c | 36%nat => pv | 37%nat => B | 38%nat => cap'
     | 55%nat => bv_unsigned (getr R (reg 10)) | 56%nat => bv_unsigned (getr R (reg 11)) | 57%nat => bv_unsigned (getr R (reg 12)) | _ => 0 end)) as PP.
  cbn beta iota in PP. replace (z + B) with (B + z) in PP by (clear; lia).
  hide_disj. L5SAR.feed PP ltac:(first [apply wid | apply wrng | pfeed XW XSZ XAV]). unhide.
  destruct PP as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & A1 & A10 & A11 & A12 & A18).
  apply (piece_ro fx fx1 R 0xaf3e4 R1 MEMCPY _ M model cr' LK Aw M1v HH SO MO MS1 MG1 FRZ1). intros model1 HH1 SO1.
  pose proof SO1 as (AM1 & _).
  assert (KS2 : forall i, In i [2; 3; 4; 8; 9; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R1 (reg i) = getr R (reg i)).
  { intros i Hi. apply KS1. clear - Hi. cbn in Hi. repeat (destruct Hi as [<-|Hi]; [inl|]). destruct Hi. }
  assert (KP1 : kept1 R1) by (apply (kept1_of R R1 KP); intros i Hi; apply KS2; clear - Hi; cbn in Hi |- *; tauto).
  destruct (cstk _ LK cr' Aw M model1 208 2560 HH1 MO ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(reflexivity) ltac:(reflexivity)) as (STKc & _).
  assert (E2' : getr R1 (reg 2) = Z_to_bv 64 (S - 208)) by (rewrite (KS2 2%nat) by inl; exact E2).
  assert (E4 : getr R1 (reg 4) = Z_to_bv 64 (hl_tp L)) by (rewrite (KS2 4%nat) by inl; rewrite (KP 4%nat) by (right; left; reflexivity); exact Rtp0).

  assert (SRC : aacc M b z /\ app_rng ar b z /\ (forall i, 0 <= i < z -> aclient L ar (((B, cap') :: PESK.sink_own sk) ++ LB) FF (S - 208) 2560 (b + i))
                /\ L5.defined M b z /\ (B + z <= b \/ b + z <= B)).
  { destruct (Z.eq_dec c 0) as [E0|NE].
    - pose proof (BZ0 E0) as EB0. assert (EZ0 : z = 0) by (clear - EZC E0; lia). rewrite EB0, EZ0.
      split; [intros a Ha; exfalso; clear - Ha; lia|]. split; [unfold app_rng, BIGSHADOW_LO, BIGSHADOW_HI; clear; lia|].
      split; [intros i Hi; exfalso; clear - Hi; lia|]. split; [intros i Hi; exfalso; clear - Hi; lia| right; clear - B4; lia].
    - assert (HC : 0 < c) by (clear - NE ZC0; lia). destruct (LIVE0 HC) as (Hb4 & Hbce & Hb16 & Hbsh & Hbimg & Hbv). unfold nsh in Hbsh.
      assert (OWN : PESK.sink_own sk = [(b, c)]) by (rewrite Esk; unfold PESK.sink_own; cbn [PESK.sk_b PESK.sk_c]; replace (c =? 0) with false by (symmetry; apply Z.eqb_neq; exact NE); reflexivity).
      assert (BIN : In (b, c) (((B, cap') :: PESK.sink_own sk) ++ LB)) by (right; apply in_or_app; left; rewrite OWN; left; reflexivity).
      destruct (BF b c BIN) as (_ & _ & _ & _ & _ & _ & QD).
      destruct (PNAEK.own_facts L ar C HI HIok B cap' _ FF LK cr' Aw M _ HH) as (BAp & _). pose proof (BAp b c ltac:(apply in_or_app; left; rewrite OWN; left; reflexivity)) as BNE.
      split; [unfold PMSPA.accA in ACCb; apply (aacc_sub M b c b z (ACCb HC)); clear - ZC0; lia|].
      split; [unfold app_rng, BIGSHADOW_LO, BIGSHADOW_HI; clear - Hb4 Hbce Hbsh SLO SHI SPT ZC0; lia|].
      split; [intros i Hi; unfold aclient, aclient_g; left; exists (b, c); split; [exact BIN| cbn [fst snd]; clear - Hi ZC0; lia]|].
      split; [intros i Hi; apply QD; clear - Hi ZC0; lia| clear - BNE ZC0 ZC1; lia]. }
  destruct SRC as (SAC & SAP & SCL & SDF & SNO).

  apply (memcpy_callN fx1 R1 M model1 K _ FF LK cr' Aw (S - 208) 0xaf43c B b z HH1 AM1 K0 A1 ltac:(split; [clear; lia| reflexivity]) E2' E4 A10 A11 A12 Z30 STKc).
  { apply (aacc_of_block M B cap' B z SHB); [apply PMKA.mod16_8'; exact B16| clear - B4; lia| clear; lia| clear - ZC1; lia]. }
  { intros i Hi. unfold aclientw, aclient_g. left. exists (B, cap'). split; [left; reflexivity|]. cbn [fst snd]. clear - Hi ZC1; lia. }
  { intros i Hi. apply BDEF. clear - Hi ZC1; lia. }
  { clear - B4; lia. } { clear - BCEIL SLO SHI SPT ZC1; lia. }
  { unfold app_rng, BIGSHADOW_LO, BIGSHADOW_HI. clear - B4 BCEIL BSH SLO SHI SPT ZC1; lia. }
  { exact SAC. } { clear - B00; lia. } { clear - BC47 ZC0 EZC; lia. } { exact SAP. }
  { exact SCL. } { exact SDF. } { exact SNO. }
  intros fx2 R2 M2 model2 RP2 DD2 HP2 MRT2 AM2 HH2.
  assert (WIN : forall rg, In rg [(B, z)] -> exists q m, In (q, m) ((B, cap') :: PESK.sink_own sk) /\ q <= fst rg /\ fst rg + snd rg <= q + m).
  { intros rg [<-|[]]. exists B, cap'. split; [left; reflexivity|]. cbn [fst snd]. clear - ZC1; lia. }
  pose proof (mem_ok_callee _ _ LK cr' Aw M model1 M2 (S - 208) 2560 _ HH1 MO HP2 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) WIN) as MO2.
  pose proof (saves_callee _ LK cr' Aw M model1 M2 _ (S - 208) 2560 _ HH1 MO HP2 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) WIN SV) as SV2.
  pose proof (ssaves_callee _ LK cr' Aw M model1 M2 _ (S - 208) 2560 _ e18 HH1 MO HP2 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) WIN SSV) as SSV2.
  pose proof (hdr_callee _ LK cr' Aw M model1 M2 _ (S - 208) 2560 _ _ _ _ HH1 MO HP2 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) WIN HDR) as HD2.
  assert (CELL : forall a val, S - 208 <= a -> a + 8 <= S -> L5.u64_at RSEGS M a val -> L5.u64_at RSEGS M2 a val).
  { intros a val Ha Hb X. exact (cell_callee _ LK cr' Aw M model1 M2 ((B, cap') :: PESK.sink_own sk) (S - 208) 2560 [(B, z)] a val HH1 MO HP2 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) WIN ltac:(left; clear - Ha Hb; lia) X). }
  assert (WA : PMKA.wapp [(B, z)]) by (apply PMKA.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; clear - B4 BSH ZC1; lia| exact PMKA.wapp_nil]).
  pose proof (blksh_ek _ FF (S - 208) 2560 _ M M2 B cap' (proj1 HP2) WA ltac:(left; reflexivity) ltac:(clear - B4; lia) ltac:(clear - BCEIL SLO SHI SPT; lia)) as AGB.
  assert (SHB2 : shadow_blk M2 B cap') by (apply (shblk_agree M M2 B cap'); [apply PMKA.mod16_8'; exact B16| clear - ZC1 ZC0; lia| exact AGB| exact SHB]).
  assert (CS2 : forall i, In i L5SAR.cs_all -> getr R2 (reg i) = getr R1 (reg i)) by (intros i Hi; exact (L5SAR.cs_of_preserved R1 R2 i RP2 Hi)).
  apply (tail_W3 fx2 R2 M2 model2 LK Aw cr' B b z c cap' e18 Esk EZC Ecap SCAPn E18B E18Z).
  - rewrite CS2 by inl. exact E2'.
  - rewrite CS2 by inl. rewrite (KS2 8%nat) by inl. exact E8.
  - rewrite CS2 by inl. rewrite (KS2 9%nat) by inl. exact E9.
  - rewrite CS2 by inl. exact A18.
  - rewrite CS2 by inl. rewrite (KS2 19%nat) by inl. exact E19.
  - rewrite CS2 by inl. rewrite (KS2 20%nat) by inl. exact E20.
  - rewrite CS2 by inl. rewrite (KS2 21%nat) by inl. exact E21.
  - rewrite CS2 by inl. rewrite (KS2 22%nat) by inl. exact E22.
  - exact (kept1_pres R1 R2 KP1 RP2).
  - exact (stok_step model1 LK Aw model2 LK Aw SO1 AM2 MRT2 (incl_refl _) (incl_refl _)).
  - exact MO2. - exact SV2. - exact SSV2. - exact HH2. - exact HD2.
  - apply CELL; [clear; lia| clear; lia| exact Q1].
  - apply CELL; [clear; lia| clear; lia| exact Q2].
  - apply CELL; [clear; lia| clear; lia| exact Q3].
  - apply CELL; [clear; lia| clear; lia| exact Q4].
  - apply CELL; [clear; lia| clear; lia| exact F1].
  - apply CELL; [clear; lia| clear; lia| exact F2].
  - apply CELL; [clear; lia| clear; lia| exact F3].
  - apply CELL; [clear; lia| clear; lia| exact F4].
  - apply CELL; [clear; lia| clear; lia| exact F5].
  - exact SHB2.
  - apply (aacc_of_block M2 B cap' B (z + 1) SHB2); [apply PMKA.mod16_8'; exact B16| clear - B4; lia| clear; lia| clear - ZC1; lia].
  - exact ABR.
  - exact CK.
Qed.

Lemma ri_swap (p q : Z * Z) LK cr Aw M V : ri_inv HI (p :: q :: LB) FF LK cr Aw M V -> ri_inv HI (q :: p :: LB) FF LK cr Aw M V.
Proof.
  intros HH. pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ND1 & NDF & _).
  apply (HAJ.aior_perm _ _ _ _ _ HIok (p :: q :: LB) (q :: p :: LB) FF FF LK cr Aw M V HH); [intros y; cbn [In]; clear; tauto| | intros f; clear; tauto|].
  - clear - ND1. cbn [map] in *. apply stdpp.list_relations.list.NoDup_cons in ND1 as (N1 & ND). apply stdpp.list_relations.list.NoDup_cons in ND as (N2 & ND).
    apply stdpp.list_relations.list.NoDup_cons. split.
    + intros X. apply stdpp.list_basics.list.elem_of_cons in X as [X|X]; [apply N1; rewrite X; apply stdpp.list_basics.list.elem_of_cons; left; reflexivity| exact (N2 X)].
    + apply stdpp.list_relations.list.NoDup_cons. split; [| exact ND]. intros X. apply N1. apply stdpp.list_basics.list.elem_of_cons. right. exact X.
  - rewrite map_app in NDF. apply stdpp.list_relations.list.NoDup_app in NDF. exact (proj1 NDF).
Qed.

Lemma pv_piece HL LK cr Aw M model (M1 : word -> option byte) (Wp : Z -> Prop) :
  ri_inv HI (HL ++ LB) FF LK cr Aw M (vml_of model) -> mem_ok M ->
  (forall i, 0 <= i < 2 ^ 64 -> ~ Wp i -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
  (forall i, Wp i -> (S - 12288 <= i < S) \/ (v <= i < v + 24) \/ (exists q m, In (q, m) (HL ++ LB) /\ q <= i < q + m)) ->
  (forall a n, 0 <= a -> a + n <= 2 ^ 47 -> PMFA.agsh M M1 a n) ->
  PESKA.pv_ok ar FF M S v pv -> PESKA.pv_ok ar FF M1 S v pv.
Proof using All.
  intros HH MO FR NP AGS PV. destruct (pv_facts HL LK cr Aw M model HH MO PV) as (PVD & PVZ & PVO & PV1 & PV2 & PV3 & PVS & PVBIG & PVCL & PVVIS & PVBL).
  destruct PV as (_ & _ & _ & PVW). split; [| split; [| split; [exact PVO| exact PVW]]].
  - intros i Hi. rewrite FR; [apply PVD; exact Hi| clear - Hi PV1 PV2; lia|]. intros X. destruct (NP (pv + i) X) as [Y|[Y|(q & m & Hq & Y)]]; [clear - Y Hi PVS; lia| clear - Y Hi PVO; lia|].
    destruct (PVBL q m Hq) as [Z'|Z']; clear - Z' Y Hi; lia.
  - unfold byte_at in *. rewrite (AGS pv 1 ltac:(clear - PV1; lia) ltac:(clear - PV2; lia) pv ltac:(clear; lia)). exact PVZ.
Qed.
Lemma pv_callee HL LK cr Aw M model M' HL' sp' scr' W' :
  ri_inv HI (HL ++ LB) FF LK cr Aw M (vml_of model) -> mem_ok M ->
  L5CA.ahpres L ar (HL' ++ LB) FF sp' scr' W' M M' -> sp' <= S -> PMKA.wapp W' ->
  (forall rg, In rg W' -> exists q m, In (q, m) HL /\ q <= fst rg /\ fst rg + snd rg <= q + m) ->
  PESKA.pv_ok ar FF M S v pv -> PESKA.pv_ok ar FF M' S v pv.
Proof using All.
  intros HH MO (EK & _ & _) LE WA WIN PV. destruct (pv_facts HL LK cr Aw M model HH MO PV) as (PVD & PVZ & PVO & PV1 & PV2 & PV3 & PVS & PVBIG & PVCL & PVVIS & PVBL).
  destruct (nfacts HL LK cr Aw M model HH MO) as ((A16 & SLO & SHI & SPT & C0') & _ & BF).
  destruct PV as (_ & _ & _ & PVW).
  assert (OUT : L5.outside W' pv).
  { intros rg Hrg Y. unfold L5.in_rng in Y. destruct (WIN rg Hrg) as (q & m & Hq & Q1 & Q2). destruct (PVBL q m ltac:(apply in_or_app; left; exact Hq)) as [X|X]; clear - X Y Q1 Q2; lia. }
  split; [| split; [| split; [exact PVO| exact PVW]]].
  - intros i Hi. replace (pv + i) with pv by (clear - Hi; lia). rewrite EK; [pose proof (PVD 0 ltac:(clear; lia)) as D0; rewrite Z.add_0_r in D0; exact D0|].
    split; [clear - PV1 PV2; lia|]. split; [apply PVCL; exact LE| exact OUT].
  - unfold byte_at in *. rewrite EK; [exact PVZ|]. pose proof (PMKA.S_in_shadow pv ltac:(clear - PV1 PV2; lia)) as SX.
    split; [unfold BIGSHADOW_LO, BIGSHADOW_HI in SX; clear - SX; lia|]. split; [| exact (PMKA.wapp_outside_shadow W' (HeapIfaceA.S pv) WA SX)].
    destruct PVW as [(P1 & P2)|(f & Hf & P1 & P2)].
    + unfold aclient, aclient_g. do 4 right; left. unfold in_shadow_of. split; apply PMKA.S_mono; clear - P1 P2 SLO SHI SPT; lia.
    + unfold aclient, aclient_g. do 5 right; left. exists f. split; [exact Hf|]. unfold in_shadow_of. split; apply PMKA.S_mono; clear - P1 P2; lia.
Qed.

Lemma bat_of_sink HL LK cr Aw M model b z c : ri_inv HI (HL ++ LB) FF LK cr Aw M (vml_of model) -> mem_ok M ->
  PESKA.sink_atA RSEGS L ar P M v (PESK.SK b z c) -> incl [(b, c)] HL -> 0 < c -> PEASKAN.bat RSEGS M v b z c.
Proof using NMAXI HIok AO LY LYa V8.
  intros HH MO SKA INC HC.
  destruct (sk_facts HL LK cr Aw M model _ HH MO SKA ltac:(unfold PESK.sink_own; cbn [PESK.sk_b PESK.sk_c]; destruct (c =? 0); [intros x []| exact INC])) as (ZC & C31 & B0 & _ & LIVE).
  cbn [PESK.sk_b PESK.sk_z PESK.sk_c] in ZC, C31, B0, LIVE. destruct (LIVE HC) as (B4 & BCEIL & B16 & _ & _ & _ & BDEF & _).
  pose proof SKA as (W0 & W8 & W16 & D24 & A24 & _ & _ & _ & LIVE0). cbn [PESK.sk_b PESK.sk_z PESK.sk_c] in W0, W8, W16, LIVE0.
  destruct (LIVE0 HC) as (_ & ACB & ANB & _).
  split; [exact D24|]. split; [exact A24|]. split; [exact W0|]. split; [exact W8|]. split; [exact W16|]. split; [exact ZC|]. split; [clear - HC; lia|].
  split; [exact B4|]. split; [exact B16|]. split; [exact BDEF|]. split; [exact ACB| exact ANB].
Qed.
Lemma v8null_of_sink M : PESKA.sink_atA RSEGS L ar P M v (PESK.SK 0 0 0) -> PGV8.v8_at RSEGS PMSPA.accA PMSPA.annA M v PGV8.V8Null.
Proof.
  intros (W0 & W8 & W16 & D24 & A24 & _). cbn [PESK.sk_b PESK.sk_z PESK.sk_c Z.add] in W0, W8, W16.
  split; [exact D24|]. split; [exact A24|]. split; [exact W0|]. split; [exact W8| exact W16].
Qed.

Lemma cap_cases c : PESK.is_cap c -> c = 0 \/ c = 1 \/ c = 2 \/ 4 <= c.
Proof.
  intros [->|(e & He & ->)]; [left; reflexivity|]. destruct (Z.eq_dec e 0) as [->|N0]; [right; left; reflexivity|].
  destruct (Z.eq_dec e 1) as [->|N1]; [right; right; left; reflexivity|]. right; right; right.
  replace e with (2 + (e - 2)) by (clear; lia). rewrite Z.pow_add_r by (clear - He N0 N1; lia). change (2 ^ 2) with 4.
  pose proof (Z.pow_pos_nonneg 2 (e - 2) ltac:(clear; lia) ltac:(clear - He N0 N1; lia)). clear - H. lia.
Qed.

Lemma tail_S2 (fx : FPState) R M model LK Aw cr' B b z c cap' e18 :
  sk = PESK.SK b z c -> z = c -> cap' = PESK.cap_next c -> PESKA.spa_cap P cap'   -> 0 <= e18 <= 2 ^ 47 -> (c = 0 -> e18 = 0) ->
  getr R (reg 2) = Z_to_bv 64 (S - 160) -> getr R (reg 8) = Z_to_bv 64 (v + 8) -> getr R (reg 9) = Z_to_bv 64 v -> getr R (reg 10) = Z_to_bv 64 B ->
  getr R (reg 18) = Z_to_bv 64 pv -> getr R (reg 19) = Z_to_bv 64 cap' -> getr R (reg 20) = Z_to_bv 64 ((v + 8) / 8 + SBL) -> getr R (reg 21) = Z_to_bv 64 SBL ->
  getr R (reg 22) = Z_to_bv 64 z -> kept1 R ->
  stok model LK Aw -> mem_ok M -> saves M -> ssaves M e18 -> ri_inv HI (((B, cap') :: PESK.sink_own sk) ++ LB) FF LK cr' Aw M (vml_of model) ->
  PESKA.sink_atA RSEGS L ar P M v sk -> PESKA.pv_ok ar FF M S v pv ->
  shadow_blk M B cap' -> ablock_range L ar B cap' ->
  PMSP.credit_keep cr0 cr' (PESKA.spa_pot P c) (PESKA.spa_pot P cap') ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0xaf1e8 M model) K.
Proof using All.
  intros Esk EZC Ecap SCAPn E18B E18Z E2 E8 E9 E10 E18 E19 E20 E21 E22 KP SO MO SV SSV HH SKA PV SHB ABR CK.
  destruct (nfacts _ LK cr' Aw M model HH MO) as ((A16 & SLO & SHI & SPT & C0') & (O1 & O2 & O5 & ODEF) & BF). unfold nsh in O5.
  destruct (vfacts _ LK cr' Aw M model HH MO) as (X0 & X1 & X2 & XW & XZ & XWV & XSZ & XAV).
  pose proof SV as (S8 & S16 & S24 & S32 & S40 & S48). pose proof SSV as (T56 & T64 & T72 & T80 & T88 & T96 & T104 & T112).
  pose proof (PESK.cap_next_pos c) as CP. pose proof sk0_num as (ZC0 & C310 & B00 & BZ0 & LIVE0). rewrite Esk in ZC0, C310, B00, BZ0, LIVE0. cbn [PESK.sk_b PESK.sk_z PESK.sk_c] in ZC0, C310, B00, BZ0, LIVE0.
  pose proof SKA0 as (_ & _ & _ & _ & _ & _ & CAP0 & _). rewrite Esk in CAP0. cbn [PESK.sk_c] in CAP0.
  destruct (next_facts ltac:(rewrite Esk; exact EZC)) as (CAPn & NMn). rewrite Esk in CAPn, NMn. cbn [PESK.sk_c] in CAPn, NMn. rewrite <- Ecap in CAPn, NMn.
  destruct (BF B cap' ltac:(left; reflexivity)) as (B4 & _ & BCEIL & B16 & BSH & BV & BDEF). unfold nsh in BSH.
  assert (B8 : B mod 8 = 0) by (apply PMKA.mod16_8'; exact B16).
  assert (ZC1 : 0 <= z + 1 <= cap') by (clear - ZC0 EZC Ecap CP; subst cap'; unfold PESK.cap_next; destruct (c =? 0) eqn:E0; [apply Z.eqb_eq in E0| apply Z.eqb_neq in E0]; lia).
  destruct (pv_facts _ LK cr' Aw M model HH MO PV) as (PVD & PVZ & PVO & PV1 & PV2 & PV3 & PVS & PVBIG & PVCL & PVVIS & PVBL).
  pose proof (PVBL B cap' ltac:(left; reflexivity)) as PVB.
  assert (DJ1 : 2147446784 + 17592186048512 <= v \/ v + 24 <= 2147446784) by (clear - O5; lia).
  assert (DJ2 : S - 256 + 256 <= v \/ v + 24 <= S - 256) by (clear - O2 SLO; lia).
  assert (DJ3 : pv + 1 <= S - 256 \/ S - 256 + 256 <= pv) by (clear - PVS; lia).
  assert (DJ4 : 2147446784 + 17592186048512 <= B \/ B + cap' <= 2147446784) by (clear - BSH; lia).
  assert (DJ5 : 65536 + 6848512 <= B \/ B + cap' <= 65536) by (destruct ABR as (_ & AI & _); rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in AI; clear - AI; lia).
  assert (DJ6 : S - 256 + 256 <= B \/ B + cap' <= S - 256) by (clear - BCEIL SLO; lia).
  assert (DJ7 : v + 24 <= B \/ B + cap' <= v) by (clear - BV; lia).
  assert (DJ8 : pv + 1 <= B \/ B + cap' <= pv) by (clear - PVB; lia).
  assert (XSS : L5KA.zeros_at (mrestrict (ahid Aw model) M) (S / 8 + 2147450368) 512) by (rewrite <- (sh4096 S A16); apply XSZ; clear - A16; lia).

  destruct (u8_at_of_defined M pv ltac:(clear - PV1 PV2; lia) ltac:(pose proof (PVD 0 ltac:(clear; lia)) as D0; rewrite Z.add_0_r in D0; exact D0)) as (bt & BT & BTM).
  assert (BTv : L5.u8_at RSEGS (mrestrict (ahid Aw model) M) pv bt) by (apply (proj2 (L5A.u8_at_vis (ahid Aw model) M pv bt PVVIS ltac:(clear - PV1; lia) ltac:(clear - PV2; lia))); exact BTM).
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ FF LK cr' Aw M model HH) as (HOFF & VIS & VIMG & VFS & VBLK & VBSH & VFSSH & VSTSH).
  assert (PVSHV : L5A.avis (ahid Aw model) (pv / 8 + SBL) 1).
  { destruct PV as (_ & _ & _ & [(P1 & P2)|(f & Hf & P1 & P2)]).
    - apply VSTSH. intros i Hi. unfold in_shadow_of, HeapIfaceA.S. replace (pv / 8 + SBL + i) with (pv / 8 + SBL) by (clear - Hi; lia).
      split; [apply Z.add_le_mono_r; apply Z.div_le_mono; clear - P1 SLO C0'; lia| apply Z.add_le_mono_r; apply Z.div_le_mono; clear - P2 SPT; lia].
    - pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & WF & _). destruct (WF f Hf) as (F1 & F2 & _). destruct f as [[F kc] rs]. cbn [ff_addr ff_class fst snd] in *.
      apply VFSSH. intros i Hi. unfold in_shadow_of, HeapIfaceA.S. replace (pv / 8 + SBL + i) with (pv / 8 + SBL) by (clear - Hi; lia).
      split; [apply Z.add_le_mono_r; apply Z.div_le_mono; clear - P1 F1; lia| apply Z.add_le_mono_r; apply Z.div_le_mono; unfold FS_BYTES in *; clear - P2 F2; lia]. }
  assert (PVZv : L5KA.zeros_at (mrestrict (ahid Aw model) M) (pv / 8 + SBL) 1).
  { intros i Hi. replace (pv / 8 + SBL + i) with (pv / 8 + SBL) by (clear - Hi; lia).
    pose proof (PVSHV 0 ltac:(clear; lia)) as AV0. rewrite Z.add_0_r in AV0. rewrite (mrestrict_visible (ahid Aw model) M _ AV0). exact PVZ. }

  assert (XWB : L5.writable RSEGS (mrestrict (ahid Aw model) M) B cap').
  { apply (proj2 (L5A.writable_vis (ahid Aw model) M B cap' (VBLK B cap' B cap' ltac:(left; reflexivity) ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - B4; lia) ltac:(clear - BCEIL SLO SHI SPT; lia))).
    apply (L5C.writable_of_defined RSEGS M B cap' BDEF); [clear - B4; lia| clear - BCEIL SLO SHI SPT; lia]. }
  assert (GVIS : forall k, 0 <= k < cap' -> L5A.avis (ahid Aw model) ((B + k) / 8 + SBL) 1).
  { intros k Hk. apply (VBSH B cap'); [left; reflexivity|]. intros i Hi. unfold in_shadow_of, HeapIfaceA.S. replace ((B + k) / 8 + SBL + i) with ((B + k) / 8 + SBL) by (clear - Hi; lia).
    split; apply Z.add_le_mono_r; apply Z.div_le_mono; clear - Hk; lia. }
  assert (EBK : forall k, 0 <= k -> (B + k) / 8 + SBL = HeapIfaceA.S B + k / 8).
  { intros k Hk. unfold HeapIfaceA.S, SB. pose proof (Z.div_mod B 8 ltac:(clear; lia)) as DB. rewrite B8 in DB. replace (B + k) with (B / 8 * 8 + k) by (clear - DB; lia).
    rewrite Z.div_add_l by (clear; lia). clear; lia. }
  destruct SHB as (SHZ & SHP).
  set (Wp := fun a : Z => (S - 208 <= a < S - 120) \/ (B + z <= a < B + z + 1)).
  assert (CONT : forall (fx1 : FPState) (R1 : bvmap 5 word) (M1v : word -> option byte),
    msteps RSEGS (mst fx R 0xaf1e8 (mrestrict (ahid Aw model) M)) (mst fx1 R1 ANND M1v) ->
    mem_grows (mrestrict (ahid Aw model) M) M1v ->
    (forall a, 0 <= a < 2 ^ 64 -> ~ Wp a -> M1v (Z_to_bv 64 a) = mrestrict (ahid Aw model) M (Z_to_bv 64 a)) ->
    (forall i, In i [3; 4; 9; 18; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R1 (reg i) = getr R (reg i)) ->
    getr R1 (reg 1) = Z_to_bv 64 0xaf3e4 -> getr R1 (reg 2) = Z_to_bv 64 (S - 208) -> getr R1 (reg 8) = Z_to_bv 64 (S - 152) -> getr R1 (reg 10) = Z_to_bv 64 v ->
    getr R1 (reg 19) = Z_to_bv 64 SBL ->
    L5.u64_at RSEGS M1v (S - 200) (B + cap') -> L5.u64_at RSEGS M1v (S - 192) pv -> L5.u64_at RSEGS M1v (S - 184) v -> L5.u64_at RSEGS M1v (S - 176) (v + 8) ->
    L5.u64_at RSEGS M1v (S - 168) 0xaf244 -> L5.u64_at RSEGS M1v (S - 152) B -> L5.u64_at RSEGS M1v (S - 144) (B + z) -> L5.u64_at RSEGS M1v (S - 136) (B + z + 1) ->
    L5.u64_at RSEGS M1v (S - 128) (B + cap') ->
    srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0xaf1e8 M model) K).
  { intros fx1 R1 M1v MS1 MG1 FRZ1 KS1 A1 A2 A8 A10 A19 C200 C192 C184 C176 C168 C152 C144 C136 C128.
    apply (piece_stepB fx fx1 R 0xaf1e8 R1 ANND _ M model cr' LK Aw M1v Wp B cap' HH SO MO ltac:(left; reflexivity) MS1 MG1 FRZ1);
      [intros a [Pa|Pa]; [left; clear - Pa; lia| right; right; clear - Pa ZC1 ZC0; lia]|].
    intros M1 model1 HH1 SO1 MO1 FR1 VUP AGS VIS1.
    pose proof SO1 as (AM1 & _).
    pose proof (saves_piece _ LK cr' Aw M model M1 Wp HH MO FR1 ltac:(intros i Pi; subst Wp; cbv beta in Pi; clear - Pi BCEIL SLO ZC1 ZC0; lia) SV) as SV1.
    pose proof (ssaves_piece _ LK cr' Aw M model M1 Wp e18 HH MO FR1 ltac:(intros i Pi; subst Wp; cbv beta in Pi; clear - Pi BCEIL SLO ZC1 ZC0; lia) SSV) as SSV1.
    pose proof (pv_piece _ LK cr' Aw M model M1 Wp HH MO FR1 ltac:(intros i Pi; subst Wp; cbv beta in Pi; destruct Pi as [Pi|Pi]; [left; clear - Pi; lia| right; right; exists B, cap'; split; [left; reflexivity| clear - Pi ZC1 ZC0; lia]]) AGS PV) as PV1'.
    assert (KP1 : kept1 R1) by (apply (kept1_of R R1 KP); intros i Hi; apply KS1; clear - Hi; cbn in Hi |- *; tauto).
    assert (SHB1 : shadow_blk M1 B cap') by (apply (shblk_agree M M1 B cap'); [exact B8| clear - ZC1 ZC0; lia| apply AGS; clear - B4 BCEIL SLO SHI SPT; lia| split; [exact SHZ| exact SHP]]).
    assert (KEEP : forall a val, v <= a -> a + 8 <= v + 24 -> L5.u64_at RSEGS M a val -> L5.u64_at RSEGS M1 a val).
    { intros a val Ha Hb X. apply (L5C.u64_at_agree RSEGS M M1); [| clear - Ha O1; lia| clear - Hb O2 SLO SHI SPT; lia| exact X].
      intros i Hi. apply FR1; [clear - Hi Ha Hb O1 O2 SLO SHI SPT; lia|]. subst Wp. cbv beta. intros [Y|Y]; [clear - Y Hi Ha Hb O2 SLO; lia| clear - Y Hi Ha Hb BV ZC1 ZC0; lia]. }
    assert (INC : incl (PESK.sink_own sk) ((B, cap') :: PESK.sink_own sk)) by (intros x Hx; right; exact Hx).
    pose proof SKA as (W0 & W8 & W16 & _).
    pose proof (sink_at_xfer _ _ LK cr' Aw M model LK cr' Aw M1 model1 sk HH MO HH1 MO1 INC INC SKA (KEEP v (PESK.sk_b sk) ltac:(clear; lia) ltac:(clear; lia) W0)
                  (KEEP (v + 8) (PESK.sk_b sk + PESK.sk_z sk) ltac:(clear; lia) ltac:(clear; lia) W8) (KEEP (v + 16) (PESK.sk_b sk + PESK.sk_c sk) ltac:(clear; lia) ltac:(clear; lia) W16)) as SKA1'.
    assert (SKA1 : PESKA.sink_atA RSEGS L ar P M1 v sk).
    { apply SKA1'. intros HC. rewrite Esk in HC |- *. cbn [PESK.sk_b PESK.sk_c] in HC |- *. destruct (LIVE0 HC) as (Hb4 & Hbce & _). apply AGS; clear - Hb4 Hbce SLO SHI SPT; lia. }
    clear SKA1'.
    destruct (cstk _ LK cr' Aw M1 model1 208 4096 HH1 MO1 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(reflexivity) ltac:(reflexivity)) as (STKc & SHc).
    destruct (centryD R1 _ LK cr' Aw M1 model1 208 0xaf3e4 HH1 MO1 KP1 A1 ltac:(split; [clear; lia| reflexivity]) A2 ltac:(clear; lia) ltac:(reflexivity)) as (ENT1 & FRS1).
    assert (E10' : getr R1 10%bv = Z_to_bv 64 v) by (rewrite L5K.rl10; exact A10).
    assert (ACC1 : PMSPA.accA M1 v 24) by (destruct MO1 as (_ & _ & _ & X & _); exact X).
    assert (AFTER : forall fx2 R2 (M2 : word -> option byte) model2 LK2 Aw2,
      regs_preserved R1 R2 -> hdr M2 b (b + z) (b + c) -> (0 < c -> PMSPA.accA M2 b c) ->
      L5CA.ahpres L ar ([(B, cap')] ++ LB) FF (S - 208) 4096 [] M1 M2 ->
      model_rt model1 model2 -> incl LK2 LK -> incl Aw Aw2 -> L5CA.amodel_ok Aw2 model2 ->
      ri_inv HI (((B, cap') :: PESK.sink_own sk) ++ LB) FF LK2 cr' Aw2 M2 (vml_of model2) ->
      srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx2 R2 0xaf3e4 M2 model2) K).
    { intros fx2 R2 M2 model2 LK2 Aw2 RP2 HD2 ACCb2 HP2 MRT2 ILK2 IAW2 AM2 HH2.
      assert (WIN : forall rg, In rg (@nil L5.range) -> exists q m, In (q, m) ((B, cap') :: PESK.sink_own sk) /\ q <= fst rg /\ fst rg + snd rg <= q + m) by (intros rg []).
      pose proof (mem_ok_callee ((B, cap') :: PESK.sink_own sk) [(B, cap')] LK cr' Aw M1 model1 M2 (S - 208) 4096 [] HH1 MO1 HP2 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) WIN) as MO2.
      pose proof (saves_callee ((B, cap') :: PESK.sink_own sk) LK cr' Aw M1 model1 M2 [(B, cap')] (S - 208) 4096 [] HH1 MO1 HP2 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) WIN SV1) as SV2.
      pose proof (ssaves_callee ((B, cap') :: PESK.sink_own sk) LK cr' Aw M1 model1 M2 [(B, cap')] (S - 208) 4096 [] e18 HH1 MO1 HP2 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) WIN SSV1) as SSV2.
      assert (CELL : forall a val, S - 208 <= a -> a + 8 <= S -> L5.u64_at RSEGS M1v a val -> L5.u64_at RSEGS M2 a val).
      { intros a val Ha Hb X. exact (cell_callee _ LK cr' Aw M1 model1 M2 [(B, cap')] (S - 208) 4096 [] a val HH1 MO1 HP2 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) WIN ltac:(left; clear - Ha Hb; lia)
                  (VUP a val ltac:(left; clear - Ha Hb; lia) X)). }
      pose proof (blksh_ek _ FF (S - 208) 4096 [] M1 M2 B cap' (proj1 HP2) (PMKA.wapp_nil) ltac:(left; reflexivity) ltac:(clear - B4; lia) ltac:(clear - BCEIL SLO SHI SPT; lia)) as AGB.
      assert (SHB2 : shadow_blk M2 B cap') by (apply (shblk_agree M1 M2 B cap'); [exact B8| clear - ZC1 ZC0; lia| exact AGB| exact SHB1]).
      assert (CS2 : forall i, In i L5SAR.cs_all -> getr R2 (reg i) = getr R1 (reg i)) by (intros i Hi; exact (L5SAR.cs_of_preserved R1 R2 i RP2 Hi)).
      apply (tail_W2 fx2 R2 M2 model2 LK2 Aw2 cr' B b z c cap' e18 Esk EZC Ecap SCAPn E18B E18Z).
      - rewrite CS2 by inl. exact A2.
      - rewrite CS2 by inl. exact A8.
      - rewrite CS2 by inl. rewrite (KS1 9%nat) by inl. exact E9.
      - rewrite CS2 by inl. rewrite (KS1 18%nat) by inl. exact E18.
      - rewrite CS2 by inl. exact A19.
      - rewrite CS2 by inl. rewrite (KS1 20%nat) by inl. exact E20.
      - rewrite CS2 by inl. rewrite (KS1 21%nat) by inl. exact E21.
      - rewrite CS2 by inl. rewrite (KS1 22%nat) by inl. exact E22.
      - exact (kept1_pres R1 R2 KP1 RP2).
      - exact (stok_step model1 LK Aw model2 LK2 Aw2 SO1 AM2 MRT2 ILK2 IAW2).
      - exact MO2. - exact SV2. - exact SSV2. - exact HH2. - exact HD2.
      - apply CELL; [clear; lia| clear; lia| exact C152].
      - apply CELL; [clear; lia| clear; lia| exact C144].
      - apply CELL; [clear; lia| clear; lia| exact C136].
      - apply CELL; [clear; lia| clear; lia| exact C128].
      - apply CELL; [clear; lia| clear; lia| exact C168].
      - apply CELL; [clear; lia| clear; lia| exact C176].
      - apply CELL; [clear; lia| clear; lia| exact C184].
      - apply CELL; [clear; lia| clear; lia| exact C192].
      - apply CELL; [clear; lia| clear; lia| exact C200].
      - exact SHB2. - exact ACCb2. - exact ABR. - exact CK. }
    unfold PMSPA.cfg.
    destruct (Z.eq_dec c 0) as [EC0|NEC].
    -
      pose proof (BZ0 EC0) as EB0. assert (EZ0 : z = 0) by (clear - EZC EC0; lia).
      assert (OWN0 : PESK.sink_own sk = []) by (rewrite Esk; unfold PESK.sink_own; cbn [PESK.sk_c]; rewrite EC0; reflexivity).
      pose proof HH1 as HH1'. rewrite OWN0 in HH1'. cbn [app] in HH1'.
      pose proof SKA1 as SKA1z. rewrite Esk, EB0, EZ0, EC0 in SKA1z.
      pose proof ANNDN_ok as ADN. unfold PEASKAND.ann_delete_null_s_spec in ADN.
      apply (ADN fx1 R1 M1 model1 K ((B, cap') :: LB) FF LK Aw cr' v (S - 208) 0xaf3e4 HH1' AM1 K0 ENT1 FRS1 E10' AO V8 ACC1 (v8null_of_sink M1 SKA1z)).
      intros fx2 R2 M2 model2 LK2 Aw2 RP2 VH2 ACCv2 HP2 MRT2 ILK2 IAW2 AM2 HH2.
      destruct VH2 as (_ & V0 & V8' & V16).
      apply (AFTER fx2 R2 M2 model2 LK2 Aw2 RP2); [| intros HC; exfalso; clear - HC EC0; lia| exact HP2| exact MRT2| exact ILK2| exact IAW2| exact AM2| rewrite OWN0; cbn [app]; exact HH2].
      rewrite EB0, EZ0, EC0. cbn [Z.add]. split; [exact V0|]. split; [exact V8'| exact V16].
    -
      assert (HC : 0 < c) by (clear - NEC ZC0; lia).
      assert (OWN : PESK.sink_own sk = [(b, c)]) by (rewrite Esk; unfold PESK.sink_own; cbn [PESK.sk_b PESK.sk_c]; replace (c =? 0) with false by (symmetry; apply Z.eqb_neq; exact NEC); reflexivity).
      pose proof HH1 as HH1'. rewrite OWN in HH1'. cbn [app] in HH1'.
      pose proof SKA1 as SKA1b. rewrite Esk in SKA1b.
      pose proof (bat_of_sink _ LK cr' Aw M1 model1 b z c HH1 MO1 SKA1b ltac:(rewrite OWN; intros x Hx; right; exact Hx) HC) as BAT1.
      pose proof ANND_ok as AD. unfold PEASKAND.ann_delete_s_spec in AD.
      apply (AD fx1 R1 M1 model1 K ((B, cap') :: LB) FF LK Aw cr' v b z c (S - 208) 0xaf3e4 (ri_swap _ _ LK cr' Aw M1 _ HH1') AM1 K0 ENT1 FRS1 E10' AO V8 ACC1 BAT1).
      intros fx2 R2 M2 model2 LK2 Aw2 RP2 BH2 ACCv2 ACCb2 FRB2 HP2 MRT2 ILK2 IAW2 AM2 HH2.
      destruct BH2 as (_ & V0 & V8' & V16 & _).
      apply (AFTER fx2 R2 M2 model2 LK2 Aw2 RP2); [| intros _; exact ACCb2| exact HP2| exact MRT2| exact ILK2| exact IAW2| exact AM2| rewrite OWN; cbn [app]; exact (ri_swap _ _ LK2 cr' Aw2 M2 _ HH2)].
      split; [exact V0|]. split; [exact V8'| exact V16]. }

  pose proof (UB 1%nat) as UB1.
  destruct (cap_cases c CAP0) as [EC0|[EC1|[EC2|GE4]]].
  -
    assert (EZ0 : z = 0) by (clear - EZC EC0; lia). assert (EK1 : cap' = 1) by (rewrite Ecap, EC0; reflexivity).
    assert (XG : L5.u8_at RSEGS (mrestrict (ahid Aw model) M) (B / 8 + SBL) 1).
    { pose proof (GVIS 0 ltac:(clear - EK1; lia) 0 ltac:(clear; lia)) as AV0. rewrite !Z.add_0_r in AV0. unfold L5.u8_at. cbn [rdn]. rewrite (mrestrict_visible (ahid Aw model) M _ AV0).
      pose proof (EBK 0 ltac:(clear; lia)) as E0. rewrite Z.add_0_r in E0. change (0 / 8) with 0 in E0. rewrite Z.add_0_r in E0. rewrite E0.
      pose proof (SHP ltac:(rewrite EK1; clear; lia)) as BY. rewrite EK1 in BY. change (1 / 8) with 0 in BY. change (1 mod 8) with 1 in BY. rewrite Z.add_0_r in BY.
      unfold byte_at in BY. rewrite BY. reflexivity. }
    pose proof (PEASKPP.askS2z_conc fx R (mrestrict (ahid Aw model) M) (fun j => match j with 2%nat => S | 10%nat => v | 36%nat => pv | 37%nat => B | 40%nat => bt
       | 56%nat => bv_unsigned (getr R (reg 11)) | 57%nat => bv_unsigned (getr R (reg 12)) | _ => 0 end)) as PP.
    cbn beta iota in PP. rewrite EK1 in E19, XWB, DJ4, DJ5, DJ6, DJ7, DJ8. rewrite EZ0 in E22.
    hide_disj. L5SAR.feed PP ltac:(first [apply wid | apply wrng | pfeed XW XSZ XAV]). unhide.
    destruct PP as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & A1 & A2 & A8 & A10 & A11 & A12 & A13 & A19 & C200 & C192 & C184 & C176 & C168 & C136 & CB & C128 & C144 & C152).
    apply (CONT fx1 R1 M1v MS1 MG1); try assumption.
    + intros a Ha Na. apply FRZ1; [exact Ha| | |]; intros X; apply Na; subst Wp; cbv beta; [left; clear - X; lia| right; clear - X EZ0; lia| left; clear - X; lia].
    + intros i Hi. apply KS1. clear - Hi. cbn in Hi. repeat (destruct Hi as [<-|Hi]; [inl|]). destruct Hi.
    + rewrite EK1. exact C200.
    + rewrite EZ0, Z.add_0_r. exact C144.
    + rewrite EZ0, Z.add_0_r. exact C136.
    + rewrite EK1. exact C128.
  -
    assert (EZ1 : z = 1) by (clear - EZC EC1; lia). assert (EK2 : cap' = 2) by (rewrite Ecap, EC1; reflexivity).
    assert (XG : L5.u8_at RSEGS (mrestrict (ahid Aw model) M) ((B + 1) / 8 + SBL) 2).
    { pose proof (GVIS 1 ltac:(clear - EK2; lia) 0 ltac:(clear; lia)) as AV0. rewrite Z.add_0_r in AV0. unfold L5.u8_at. cbn [rdn]. rewrite (mrestrict_visible (ahid Aw model) M _ AV0).
      rewrite (EBK 1 ltac:(clear; lia)). change (1 / 8) with 0. rewrite Z.add_0_r.
      pose proof (SHP ltac:(rewrite EK2; clear; lia)) as BY. rewrite EK2 in BY. change (2 / 8) with 0 in BY. change (2 mod 8) with 2 in BY. rewrite Z.add_0_r in BY.
      unfold byte_at in BY. rewrite BY. reflexivity. }
    pose proof (PEASKPP.askS2o_conc fx R (mrestrict (ahid Aw model) M) (fun j => match j with 2%nat => S | 10%nat => v | 36%nat => pv | 37%nat => B | 40%nat => bt
       | 56%nat => bv_unsigned (getr R (reg 11)) | 57%nat => bv_unsigned (getr R (reg 12)) | _ => 0 end)) as PP.
    cbn beta iota in PP. rewrite EK2 in E19, XWB, DJ4, DJ5, DJ6, DJ7, DJ8. rewrite EZ1 in E22.
    hide_disj. L5SAR.feed PP ltac:(first [apply wid | apply wrng | pfeed XW XSZ XAV]). unhide.
    destruct PP as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & A1 & A2 & A8 & A10 & A11 & A12 & A13 & A19 & C200 & C192 & C184 & C176 & C168 & C136 & CB & C128 & C144 & C152).
    apply (CONT fx1 R1 M1v MS1 MG1); try assumption.
    + intros a Ha Na. apply FRZ1; [exact Ha| | |]; intros X; apply Na; subst Wp; cbv beta; [left; clear - X; lia| right; clear - X EZ1; lia| left; clear - X; lia].
    + intros i Hi. apply KS1. clear - Hi. cbn in Hi. repeat (destruct Hi as [<-|Hi]; [inl|]). destruct Hi.
    + rewrite EK2. exact C200.
    + rewrite EZ1. exact C144.
    + rewrite EZ1. replace (B + 1 + 1) with (B + 2) by (clear; lia). exact C136.
    + rewrite EK2. exact C128.
  -
    assert (EZ2 : z = 2) by (clear - EZC EC2; lia). assert (EK4 : cap' = 4) by (rewrite Ecap, EC2; reflexivity).
    assert (XG : L5.u8_at RSEGS (mrestrict (ahid Aw model) M) ((B + 2) / 8 + SBL) 4).
    { pose proof (GVIS 2 ltac:(clear - EK4; lia) 0 ltac:(clear; lia)) as AV0. rewrite Z.add_0_r in AV0. unfold L5.u8_at. cbn [rdn]. rewrite (mrestrict_visible (ahid Aw model) M _ AV0).
      rewrite (EBK 2 ltac:(clear; lia)). change (2 / 8) with 0. rewrite Z.add_0_r.
      pose proof (SHP ltac:(rewrite EK4; clear; lia)) as BY. rewrite EK4 in BY. change (4 / 8) with 0 in BY. change (4 mod 8) with 4 in BY. rewrite Z.add_0_r in BY.
      unfold byte_at in BY. rewrite BY. reflexivity. }
    pose proof (PEASKPP.askS2t_conc fx R (mrestrict (ahid Aw model) M) (fun j => match j with 2%nat => S | 10%nat => v | 36%nat => pv | 37%nat => B | 40%nat => bt
       | 56%nat => bv_unsigned (getr R (reg 11)) | 57%nat => bv_unsigned (getr R (reg 12)) | _ => 0 end)) as PP.
    cbn beta iota in PP. rewrite EK4 in E19, XWB, DJ4, DJ5, DJ6, DJ7, DJ8. rewrite EZ2 in E22.
    hide_disj. L5SAR.feed PP ltac:(first [apply wid | apply wrng | pfeed XW XSZ XAV]). unhide.
    destruct PP as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & A1 & A2 & A8 & A10 & A11 & A12 & A13 & A19 & C200 & C192 & C184 & C176 & C168 & C136 & CB & C128 & C144 & C152).
    apply (CONT fx1 R1 M1v MS1 MG1); try assumption.
    + intros a Ha Na. apply FRZ1; [exact Ha| | |]; intros X; apply Na; subst Wp; cbv beta; [left; clear - X; lia| right; clear - X EZ2; lia| left; clear - X; lia].
    + intros i Hi. apply KS1. clear - Hi. cbn in Hi. repeat (destruct Hi as [<-|Hi]; [inl|]). destruct Hi.
    + rewrite EK4. exact C200.
    + rewrite EZ2. exact C144.
    + rewrite EZ2. replace (B + 2 + 1) with (B + 3) by (clear; lia). exact C136.
    + rewrite EK4. exact C128.
  -
    assert (EK : cap' = 2 * c) by (rewrite Ecap; unfold PESK.cap_next; replace (c =? 0) with false by (symmetry; apply Z.eqb_neq; clear - GE4; lia); reflexivity).
    assert (XG : L5KA.zeros_at (mrestrict (ahid Aw model) M) ((B + z) / 8 + SBL) 1).
    { intros i Hi. replace ((B + z) / 8 + SBL + i) with ((B + z) / 8 + SBL) by (clear - Hi; lia). pose proof (GVIS z ltac:(clear - ZC1 ZC0; lia) 0 ltac:(clear; lia)) as AV0. rewrite Z.add_0_r in AV0.
      rewrite (mrestrict_visible (ahid Aw model) M _ AV0). rewrite (EBK z ltac:(clear - ZC0; lia)). apply (SHZ (z / 8)).
      pose proof (Z.div_mod z 8 ltac:(clear; lia)) as D0. pose proof (Z.mod_pos_bound z 8 ltac:(clear; lia)) as MR0.
      pose proof (Z.div_mod cap' 8 ltac:(clear; lia)) as D1. pose proof (Z.mod_pos_bound cap' 8 ltac:(clear; lia)) as MR1. clear - D0 MR0 D1 MR1 EK EZC GE4 ZC0. lia. }
    pose proof (PEASKPP.askS2_conc fx R (mrestrict (ahid Aw model) M) (fun j => match j with 2%nat => S | 10%nat => v | 34%nat => z | 36%nat => pv | 37%nat => B | 38%nat => cap' | 40%nat => bt
       | 56%nat => bv_unsigned (getr R (reg 11)) | 57%nat => bv_unsigned (getr R (reg 12)) | _ => 0 end)) as PP.
    cbn beta iota in PP. replace (z + B) with (B + z) in PP by (clear; lia).
    pose proof NMAXI as NMX.
    hide_disj. L5SAR.feed PP ltac:(first [apply wid | apply wrng | pfeed XW XSZ XAV]). unhide.
    destruct PP as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & A1 & A2 & A8 & A10 & A11 & A12 & A19 & C200 & C192 & C184 & C176 & C168 & C136 & CB & C128 & C144 & C152).
    apply (CONT fx1 R1 M1v MS1 MG1); try assumption.
    + intros a Ha Na. apply FRZ1; [exact Ha| | |]; intros X; apply Na; subst Wp; cbv beta; [left; clear - X; lia| right; clear - X; lia| left; clear - X; lia].
    + intros i Hi. apply KS1. clear - Hi. cbn in Hi. repeat (destruct Hi as [<-|Hi]; [inl|]). destruct Hi.
Qed.

Lemma tail_S1 (fx : FPState) R M model LK Aw b z c :
  sk = PESK.SK b z c -> z = c ->
  getr R (reg 1) = Z_to_bv 64 RA_SLOW -> getr R (reg 2) = Z_to_bv 64 (S - 48) -> getr R (reg 8) = Z_to_bv 64 (v + 8) -> getr R (reg 9) = Z_to_bv 64 pv ->
  getr R (reg 10) = Z_to_bv 64 v -> getr R (reg 11) = Z_to_bv 64 pv -> getr R (reg 18) = Z_to_bv 64 (b + z) ->
  getr R (reg 19) = Z_to_bv 64 ((v + 8) / 8 + SBL) -> getr R (reg 20) = Z_to_bv 64 SBL ->
  (forall i, In i [21; 22]%nat -> getr R (reg i) = Z_to_bv 64 (U i)) -> kept0 R ->
  stok model LK Aw -> mem_ok M -> saves M -> ri_inv HI (PESK.sink_own sk ++ LB) FF LK cr0 Aw M (vml_of model) ->
  PESKA.sink_atA RSEGS L ar P M v sk -> PESKA.pv_ok ar FF M S v pv ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0xaf130 M model) K.
Proof using All.
  intros Esk EZC E1 E2 E8 E9 E10 E11 E18 E19 E20 E2122 KP SO MO SV HH SKA PV.
  destruct (nfacts _ LK cr0 Aw M model HH MO) as ((A16 & SLO & SHI & SPT & C0') & (O1 & O2 & O5 & ODEF) & BF). unfold nsh in O5.
  destruct (vfacts _ LK cr0 Aw M model HH MO) as (X0 & X1 & X2 & XW & XZ & XWV & XSZ & XAV).
  pose proof SV as (S8 & S16 & S24 & S32 & S40 & S48).
  pose proof (PESK.cap_next_pos c) as CP. pose proof sk0_num as (ZC0 & C310 & B00 & BZ0 & LIVE0). rewrite Esk in ZC0, C310, B00, BZ0, LIVE0. cbn [PESK.sk_b PESK.sk_z PESK.sk_c] in ZC0, C310, B00, BZ0, LIVE0.
  pose proof SKA0 as (_ & _ & _ & _ & _ & _ & CAP0 & _). rewrite Esk in CAP0. cbn [PESK.sk_c] in CAP0.
  destruct (next_facts ltac:(rewrite Esk; exact EZC)) as (CAPn & NMn). rewrite Esk in CAPn, NMn. cbn [PESK.sk_c] in CAPn, NMn.
  destruct (GROW ltac:(rewrite Esk; exact EZC)) as (_ & GACR & GCLE). rewrite Esk in GACR, GCLE. cbn [PESK.sk_c] in GACR, GCLE.
  set (cap' := PESK.cap_next c) in *.
  assert (BC47 : 0 <= b + c <= 2 ^ 47) by (destruct (Z.eq_dec c 0) as [E0|NE]; [rewrite (BZ0 E0), E0; clear; lia| destruct (LIVE0 ltac:(clear - NE ZC0; lia)) as (X1' & X2' & _); clear - X1' X2' SLO SHI SPT ZC0; lia]).
  destruct (pv_facts _ LK cr0 Aw M model HH MO PV) as (PVD & PVZ & PVO & PV1 & PV2 & PV3 & PVS & PVBIG & PVCL & PVVIS & PVBL).
  assert (DJ1 : 2147446784 + 17592186048512 <= v \/ v + 24 <= 2147446784) by (clear - O5; lia).
  assert (DJ2 : S - 256 + 256 <= v \/ v + 24 <= S - 256) by (clear - O2 SLO; lia).
  assert (DJ3 : pv + 1 <= S - 256 \/ S - 256 + 256 <= pv) by (clear - PVS; lia).
  assert (XSS : L5KA.zeros_at (mrestrict (ahid Aw model) M) (S / 8 + 2147450368) 512) by (rewrite <- (sh4096 S A16); apply XSZ; clear - A16; lia).
  destruct (u8_at_of_defined M pv ltac:(clear - PV1 PV2; lia) ltac:(pose proof (PVD 0 ltac:(clear; lia)) as D0; rewrite Z.add_0_r in D0; exact D0)) as (bt & BT & BTM).
  assert (BTv : L5.u8_at RSEGS (mrestrict (ahid Aw model) M) pv bt) by (apply (proj2 (L5A.u8_at_vis (ahid Aw model) M pv bt PVVIS ltac:(clear - PV1; lia) ltac:(clear - PV2; lia))); exact BTM).
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ FF LK cr0 Aw M model HH) as (HOFF & VIS & VIMG & VFS & VBLK & VBSH & VFSSH & VSTSH).
  assert (PVSHV : L5A.avis (ahid Aw model) (pv / 8 + SBL) 1).
  { destruct PV as (_ & _ & _ & [(P1 & P2)|(f & Hf & P1 & P2)]).
    - apply VSTSH. intros i Hi. unfold in_shadow_of, HeapIfaceA.S. replace (pv / 8 + SBL + i) with (pv / 8 + SBL) by (clear - Hi; lia).
      split; [apply Z.add_le_mono_r; apply Z.div_le_mono; clear - P1 SLO C0'; lia| apply Z.add_le_mono_r; apply Z.div_le_mono; clear - P2 SPT; lia].
    - pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & WF & _). destruct (WF f Hf) as (F1 & F2 & _). destruct f as [[F kc] rs]. cbn [ff_addr ff_class fst snd] in *.
      apply VFSSH. intros i Hi. unfold in_shadow_of, HeapIfaceA.S. replace (pv / 8 + SBL + i) with (pv / 8 + SBL) by (clear - Hi; lia).
      split; [apply Z.add_le_mono_r; apply Z.div_le_mono; clear - P1 F1; lia| apply Z.add_le_mono_r; apply Z.div_le_mono; unfold FS_BYTES in *; clear - P2 F2; lia]. }
  assert (PVZv : L5KA.zeros_at (mrestrict (ahid Aw model) M) (pv / 8 + SBL) 1).
  { intros i Hi. replace (pv / 8 + SBL + i) with (pv / 8 + SBL) by (clear - Hi; lia).
    pose proof (PVSHV 0 ltac:(clear; lia)) as AV0. rewrite Z.add_0_r in AV0. rewrite (mrestrict_visible (ahid Aw model) M _ AV0). exact PVZ. }
  pose proof SKA as (W0 & W8 & W16 & _). rewrite Esk in W0, W8, W16. cbn [PESK.sk_b PESK.sk_z PESK.sk_c] in W0, W8, W16. rewrite EZC in W8.
  pose proof (UB 21%nat) as UB21. pose proof (UB 22%nat) as UB22. pose proof (E2122 21%nat ltac:(left; reflexivity)) as E21. pose proof (E2122 22%nat ltac:(right; left; reflexivity)) as E22.
  assert (CONT : forall (fx1 : FPState) (R1 : bvmap 5 word) (M1v : word -> option byte),
    msteps RSEGS (mst fx R 0xaf130 (mrestrict (ahid Aw model) M)) (mst fx1 R1 OPNEW M1v) ->
    mem_grows (mrestrict (ahid Aw model) M) M1v ->
    (forall a, 0 <= a < 2 ^ 64 -> ~ (S - 160 <= a < S - 160 + 112) -> M1v (Z_to_bv 64 a) = mrestrict (ahid Aw model) M (Z_to_bv 64 a)) ->
    (forall i, In i [3; 4; 8; 23; 24; 25; 26; 27]%nat -> getr R1 (reg i) = getr R (reg i)) ->
    getr R1 (reg 1) = Z_to_bv 64 0xaf1e8 -> getr R1 (reg 2) = Z_to_bv 64 (S - 160) -> getr R1 (reg 9) = Z_to_bv 64 v -> getr R1 (reg 10) = Z_to_bv 64 cap' ->
    getr R1 (reg 18) = Z_to_bv 64 pv -> getr R1 (reg 19) = Z_to_bv 64 cap' -> getr R1 (reg 20) = Z_to_bv 64 ((v + 8) / 8 + SBL) -> getr R1 (reg 21) = Z_to_bv 64 SBL ->
    getr R1 (reg 22) = Z_to_bv 64 z ->
    L5.u64_at RSEGS M1v (S - 120) v -> L5.u64_at RSEGS M1v (S - 112) (U 22) -> L5.u64_at RSEGS M1v (S - 104) (U 21) -> L5.u64_at RSEGS M1v (S - 96) SBL ->
    L5.u64_at RSEGS M1v (S - 88) ((v + 8) / 8 + SBL) -> L5.u64_at RSEGS M1v (S - 80) (b + z) -> L5.u64_at RSEGS M1v (S - 72) pv -> L5.u64_at RSEGS M1v (S - 64) (v + 8) ->
    L5.u64_at RSEGS M1v (S - 56) RA_SLOW ->
    srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0xaf130 M model) K).
  { intros fx1 R1 M1v MS1 MG1 FRZ1 KS1 A1 A2 A9 A10 A18 A19 A20 A21 A22 C120 C112 C104 C96 C88 C80 C72 C64 C56.
    apply (piece_step fx fx1 R 0xaf130 R1 OPNEW _ M model cr0 LK Aw M1v (fun a => S - 160 <= a < S - 160 + 112) HH SO MO MS1 MG1 FRZ1); [intros a Pa; left; clear - Pa; lia|].
    intros M1 model1 HH1 SO1 MO1 FR1 VUP AGS.
    pose proof SO1 as (AM1 & _).
    pose proof (saves_piece _ LK cr0 Aw M model M1 (fun a => S - 160 <= a < S - 160 + 112) HH MO FR1 ltac:(intros i Pi; cbv beta in Pi; clear - Pi; lia) SV) as SV1.
    assert (SSV1 : ssaves M1 (b + z)).
    { split; [apply VUP; [left; clear; lia| exact C56]|]. split; [apply VUP; [left; clear; lia| exact C64]|]. split; [apply VUP; [left; clear; lia| exact C72]|].
      split; [apply VUP; [left; clear; lia| exact C80]|]. split; [apply VUP; [left; clear; lia| exact C88]|]. split; [apply VUP; [left; clear; lia| exact C96]|].
      split; [apply VUP; [left; clear; lia| exact C104]| apply VUP; [left; clear; lia| exact C112]]. }
    pose proof (pv_piece _ LK cr0 Aw M model M1 (fun a => S - 160 <= a < S - 160 + 112) HH MO FR1 ltac:(intros i Pi; cbv beta in Pi; left; clear - Pi; lia) AGS PV) as PV1'.
    assert (KP1 : kept1 R1) by (apply (kept1_of R R1 (kept1_of0 R KP)); intros i Hi; apply KS1; clear - Hi; cbn in Hi |- *; tauto).
    assert (KEEP : forall a val, v <= a -> a + 8 <= v + 24 -> L5.u64_at RSEGS M a val -> L5.u64_at RSEGS M1 a val).
    { intros a val Ha Hb X. apply (L5C.u64_at_agree RSEGS M M1); [| clear - Ha O1; lia| clear - Hb O2 SLO SHI SPT; lia| exact X].
      intros i Hi. apply FR1; [clear - Hi Ha Hb O1 O2 SLO SHI SPT; lia|]. intros Y. clear - Y Hi Ha Hb O2 SLO. lia. }
    pose proof SKA as (W0' & W8' & W16' & _).
    pose proof (sink_at_xfer _ _ LK cr0 Aw M model LK cr0 Aw M1 model1 sk HH MO HH1 MO1 ltac:(apply incl_refl) ltac:(apply incl_refl) SKA (KEEP v (PESK.sk_b sk) ltac:(clear; lia) ltac:(clear; lia) W0')
                  (KEEP (v + 8) (PESK.sk_b sk + PESK.sk_z sk) ltac:(clear; lia) ltac:(clear; lia) W8') (KEEP (v + 16) (PESK.sk_b sk + PESK.sk_c sk) ltac:(clear; lia) ltac:(clear; lia) W16')) as SKA1'.
    assert (SKA1 : PESKA.sink_atA RSEGS L ar P M1 v sk).
    { apply SKA1'. intros HC. rewrite Esk in HC |- *. cbn [PESK.sk_b PESK.sk_c] in HC |- *. destruct (LIVE0 HC) as (Hb4 & Hbce & _). apply AGS; clear - Hb4 Hbce SLO SHI SPT; lia. }
    clear SKA1'.

    destruct (cstk _ LK cr0 Aw M1 model1 160 4112 HH1 MO1 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(reflexivity) ltac:(reflexivity)) as (STKc & _).
    assert (E10' : getr R1 10%bv = Z_to_bv 64 cap') by (rewrite L5K.rl10; exact A10).
    assert (E1' : getr R1 1%bv = Z_to_bv 64 0xaf1e8) by (rewrite L5K.rl1; exact A1).
    assert (E2' : getr R1 2%bv = Z_to_bv 64 (S - 160)) by (rewrite L5K.rl2; exact A2).
    assert (E4' : getr R1 4%bv = Z_to_bv 64 (hl_tp L)) by (rewrite L5K.rl4, (KS1 4%nat) by inl; rewrite (KP 4%nat) by inl; exact Rtp0).
    assert (ACR : acredit_ok L cr0 cap').
    { pose proof CRL0 as CR. rewrite Esk in CR. cbn [PESK.sk_c] in CR. clear - GACR CR. unfold acredit_ok, PMSP.credit_le in *. destruct GACR as [G1 G2]. destruct CR as [C1 C2].
      split; [eapply Z.le_trans; [exact G1| exact C1]| eapply Z.le_trans; [exact G2| exact C2]]. }
    pose proof OPNWP as ON. unfold PESKA.opnew_n_spec in ON. unfold PMSPA.cfg.
    apply (ON fx1 R1 M1 model1 K (PESK.sink_own sk ++ LB) FF LK Aw cr0 cap' (S - 160) 0xaf1e8 HH1 AM1 K0 E10' NMn ACR E1' ltac:(split; [clear; lia| reflexivity]) E2' E4'
              ltac:(unfold PMSPA.OPNEW_SCR, PMSPA.MALLOC_SCR; exact STKc)).
    intros fx2 R2 M2 model2 Aw2 B E10q RP2 FRESH HP2 MRT2 IAW2 AM2 HH2 SCAPn.
    destruct FRESH as (ABR & BAP & FAP & BDEF2 & SHB2). unfold PMSPA.OPNEW_SCR, PMSPA.MALLOC_SCR in HP2.
    assert (WIN : forall rg, In rg (@nil L5.range) -> exists q m, In (q, m) (PESK.sink_own sk) /\ q <= fst rg /\ fst rg + snd rg <= q + m) by (intros rg []).
    pose proof (mem_ok_callee _ _ LK cr0 Aw M1 model1 M2 (S - 160) 4112 [] HH1 MO1 HP2 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) WIN) as MO2.
    pose proof (saves_callee _ LK cr0 Aw M1 model1 M2 _ (S - 160) 4112 [] HH1 MO1 HP2 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) WIN SV1) as SV2.
    pose proof (ssaves_callee _ LK cr0 Aw M1 model1 M2 _ (S - 160) 4112 [] (b + z) HH1 MO1 HP2 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) WIN SSV1) as SSV2.
    pose proof (pv_callee _ LK cr0 Aw M1 model1 M2 _ (S - 160) 4112 [] HH1 MO1 HP2 ltac:(clear; lia) (PMKA.wapp_nil) WIN PV1') as PVK2.
    assert (CELL : forall a val, v <= a -> a + 8 <= v + 24 -> L5.u64_at RSEGS M1 a val -> L5.u64_at RSEGS M2 a val).
    { intros a val Ha Hb X. exact (cell_callee _ LK cr0 Aw M1 model1 M2 (PESK.sink_own sk) (S - 160) 4112 [] a val HH1 MO1 HP2 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) WIN ltac:(right; clear - Ha Hb; lia) X). }
    assert (SKA2 : PESKA.sink_atA RSEGS L ar P M2 v sk).
    { pose proof SKA1 as (V0 & V8' & V16 & _).
      apply (sink_at_xfer (PESK.sink_own sk) ((B, cap') :: PESK.sink_own sk) LK cr0 Aw M1 model1 LK (adebit L cr0 cap') Aw2 M2 model2 sk HH1 MO1 HH2 MO2 ltac:(apply incl_refl) ltac:(intros x Hx; right; exact Hx) SKA1
               (CELL v (PESK.sk_b sk) ltac:(clear; lia) ltac:(clear; lia) V0) (CELL (v + 8) (PESK.sk_b sk + PESK.sk_z sk) ltac:(clear; lia) ltac:(clear; lia) V8')
               (CELL (v + 16) (PESK.sk_b sk + PESK.sk_c sk) ltac:(clear; lia) ltac:(clear; lia) V16)).
      intros HC. rewrite Esk in HC |- *. cbn [PESK.sk_b PESK.sk_c] in HC |- *. destruct (LIVE0 HC) as (Hb4 & Hbce & _).
      apply (blksh_ek _ FF (S - 160) 4112 [] M1 M2 b c (proj1 HP2) (PMKA.wapp_nil)); [| clear - Hb4; lia| clear - Hbce SLO SHI SPT; lia].
      apply in_or_app. left. rewrite Esk. unfold PESK.sink_own. cbn [PESK.sk_b PESK.sk_c]. replace (c =? 0) with false by (symmetry; apply Z.eqb_neq; clear - HC; lia). left; reflexivity. }
    assert (CS2 : forall i, In i L5SAR.cs_all -> getr R2 (reg i) = getr R1 (reg i)) by (intros i Hi; exact (L5SAR.cs_of_preserved R1 R2 i RP2 Hi)).
    apply (tail_S2 fx2 R2 M2 model2 LK Aw2 (adebit L cr0 cap') B b z c cap' (b + z) Esk EZC eq_refl SCAPn ltac:(clear - BC47 ZC0 EZC; lia) ltac:(intros E0; rewrite (BZ0 E0); clear - E0 EZC; lia)).
    - rewrite CS2 by inl. exact A2.
    - rewrite CS2 by inl. rewrite (KS1 8%nat) by inl. exact E8.
    - rewrite CS2 by inl. exact A9.
    - rewrite <- L5K.rl10. exact E10q.
    - rewrite CS2 by inl. exact A18.
    - rewrite CS2 by inl. exact A19.
    - rewrite CS2 by inl. exact A20.
    - rewrite CS2 by inl. exact A21.
    - rewrite CS2 by inl. exact A22.
    - exact (kept1_pres R1 R2 KP1 RP2).
    - exact (stok_step model1 LK Aw model2 LK Aw2 SO1 AM2 MRT2 (incl_refl _) IAW2).
    - exact MO2. - exact SV2. - exact SSV2. - exact HH2. - exact SKA2. - exact PVK2. - exact SHB2. - exact ABR.
    - pose proof CRL0 as CR. rewrite Esk in CR. cbn [PESK.sk_c] in CR. clear - GCLE CR. unfold PMSP.credit_keep, PMSP.credit_le, adebit in *. cbn [fst snd] in *.
      destruct GCLE as [G1 G2]. destruct CR as [C1 C2]. split; [clear - G1 C1; lia| clear - G2 C2; lia]. }

  destruct (Z.eq_dec c 0) as [EC0|NEC]; [| destruct (Z.eq_dec c 1) as [EC1|NEC1]].
  -
    pose proof (BZ0 EC0) as EB0. assert (EZ0 : z = 0) by (clear - EZC EC0; lia). assert (EK1 : cap' = 1) by (subst cap'; rewrite EC0; reflexivity).
    rewrite EB0, EZ0 in E18. cbn [Z.add] in E18. rewrite EB0 in W0. rewrite EB0, EC0 in W8, W16. cbn [Z.add] in W8, W16.
    pose proof (PEASKPP.askS1z_conc fx R (mrestrict (ahid Aw model) M) (fun j => match j with 2%nat => S | 40%nat => bt | 50%nat => U 21 | 51%nat => U 22
       | 57%nat => bv_unsigned (getr R (reg 12)) | _ => 0 end)) as PP.
    cbn beta iota in PP. rewrite E10, E11 in PP. rewrite !(L5.unsigned_lit v) in PP by (clear - O1 O2 SLO SHI SPT; lia). rewrite !(L5.unsigned_lit pv) in PP by (clear - PV1 PV2; lia).
    hide_disj. L5SAR.feed PP ltac:(first [apply wid | apply wrng | pfeed XW XSZ XAV]). unhide.
    destruct PP as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & A1 & A2 & A9 & A10 & A11 & A12 & A13 & A18 & A19 & A20 & A21 & A22 & C120 & C112 & C104 & C96 & C88 & C80 & C72 & C64 & C56).
    apply (CONT fx1 R1 M1v MS1 MG1 FRZ1); try assumption.
    + intros i Hi. apply KS1. clear - Hi. cbn in Hi. repeat (destruct Hi as [<-|Hi]; [inl|]). destruct Hi.
    + rewrite EK1. exact A10. + rewrite EK1. exact A19. + rewrite EZ0. exact A22.
    + rewrite EB0, EZ0. exact C80.
  -
    assert (EZ1 : z = 1) by (clear - EZC EC1; lia). assert (EK2 : cap' = 2) by (subst cap'; rewrite EC1; reflexivity).
    destruct (LIVE0 ltac:(clear - EC1; lia)) as (Hb4 & Hbce & Hb16 & Hbsh & Hbimg & Hbv). unfold nsh in Hbsh. rewrite EC1 in Hbce, Hbsh, Hbimg, Hbv.
    assert (DJ4 : 2147446784 + 17592186048512 <= b \/ b + 1 <= 2147446784) by (clear - Hbsh; lia).
    assert (DJ5 : 65536 + 6848512 <= b \/ b + 1 <= 65536) by (clear - Hbimg; lia).
    rewrite EZ1 in E18. rewrite EC1 in W8, W16.
    pose proof (PEASKPP.askS1o_conc fx R (mrestrict (ahid Aw model) M) (fun j => match j with 2%nat => S | 33%nat => b | 40%nat => bt | 50%nat => U 21 | 51%nat => U 22
       | 57%nat => bv_unsigned (getr R (reg 12)) | _ => 0 end)) as PP.
    cbn beta iota in PP. rewrite E10, E11 in PP. rewrite !(L5.unsigned_lit v) in PP by (clear - O1 O2 SLO SHI SPT; lia). rewrite !(L5.unsigned_lit pv) in PP by (clear - PV1 PV2; lia).
    hide_disj. L5SAR.feed PP ltac:(first [apply wid | apply wrng | pfeed XW XSZ XAV]). unhide.
    destruct PP as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & A1 & A2 & A9 & A10 & A11 & A12 & A13 & A18 & A19 & A20 & A21 & A22 & C120 & C112 & C104 & C96 & C88 & C80 & C72 & C64 & C56).
    apply (CONT fx1 R1 M1v MS1 MG1 FRZ1); try assumption.
    + intros i Hi. apply KS1. clear - Hi. cbn in Hi. repeat (destruct Hi as [<-|Hi]; [inl|]). destruct Hi.
    + rewrite EK2. exact A10. + rewrite EK2. exact A19. + rewrite EZ1. exact A22.
    + rewrite EZ1. exact C80.
  -
    assert (HC2 : 2 <= c) by (clear - NEC NEC1 ZC0; lia). assert (EK : cap' = 2 * c) by (subst cap'; unfold PESK.cap_next; replace (c =? 0) with false by (symmetry; apply Z.eqb_neq; exact NEC); reflexivity).
    destruct (LIVE0 ltac:(clear - HC2; lia)) as (Hb4 & Hbce & Hb16 & Hbsh & Hbimg & Hbv). unfold nsh in Hbsh.
    assert (DJ4 : 2147446784 + 17592186048512 <= b \/ b + c <= 2147446784) by (clear - Hbsh; lia).
    assert (DJ5 : 65536 + 6848512 <= b \/ b + c <= 65536) by (clear - Hbimg; lia).
    assert (C30 : 2 <= c <= 2 ^ 33) by (clear - HC2 EK NMn NMAXI; lia).
    rewrite EZC in E18.
    pose proof (PEASKPP.askS1_conc fx R (mrestrict (ahid Aw model) M) (fun j => match j with 2%nat => S | 33%nat => b | 35%nat => c | 40%nat => bt | 50%nat => U 21 | 51%nat => U 22
       | 57%nat => bv_unsigned (getr R (reg 12)) | _ => 0 end)) as PP.
    cbn beta iota in PP. rewrite E10, E11 in PP. rewrite !(L5.unsigned_lit v) in PP by (clear - O1 O2 SLO SHI SPT; lia). rewrite !(L5.unsigned_lit pv) in PP by (clear - PV1 PV2; lia).
    hide_disj. L5SAR.feed PP ltac:(first [apply wid | apply wrng | pfeed XW XSZ XAV]). unhide.
    destruct PP as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & A1 & A2 & A9 & A10 & A11 & A12 & A13 & A18 & A19 & A20 & A21 & A22 & C120 & C112 & C104 & C96 & C88 & C80 & C72 & C64 & C56).
    apply (CONT fx1 R1 M1v MS1 MG1 FRZ1); try assumption.
    + intros i Hi. apply KS1. clear - Hi. cbn in Hi. repeat (destruct Hi as [<-|Hi]; [inl|]). destruct Hi.
    + rewrite EK. exact A10. + rewrite EK. exact A19. + rewrite EZC. exact A22.
    + rewrite EZC. exact C80.
Qed.

Lemma entry_ok (fx : FPState) b z c : sk = PESK.SK b z c -> srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R0 PC0 M0 model0) K.
Proof using All.
  intros Esk. pose proof stok0 as SO. pose proof mem_ok0 as MO. pose proof HH0 as HH.
  destruct (nfacts _ LK0 cr0 Aw0 M0 model0 HH MO) as ((A16 & SLO & SHI & SPT & C0') & (O1 & O2 & O5 & ODEF) & BF). unfold nsh in O5.
  destruct (vfacts _ LK0 cr0 Aw0 M0 model0 HH MO) as (X0 & X1 & X2 & XW & XZ & XWV & XSZ & XAV).
  pose proof sk0_num as (ZC0 & C310 & B00 & BZ0 & LIVE0). rewrite Esk in ZC0, C310, B00, BZ0, LIVE0. cbn [PESK.sk_b PESK.sk_z PESK.sk_c] in ZC0, C310, B00, BZ0, LIVE0.
  assert (KP0 : kept0 R0) by (intros i _; reflexivity).
  assert (E10 : getr R0 (reg 10) = Z_to_bv 64 v) by (rewrite <- L5K.rl10; exact Ra0).
  assert (E11 : getr R0 (reg 11) = Z_to_bv 64 pv) by (rewrite <- L5K.rl11; exact Ra1).
  pose proof Rsp0 as E2r.
  destruct (pv_facts _ LK0 cr0 Aw0 M0 model0 HH MO PVOK) as (PVD & PVZ & PVO & PV1 & PV2 & PV3 & PVS & PVBIG & PVCL & PVVIS & PVBL).
  assert (DJ1 : 2147446784 + 17592186048512 <= v \/ v + 24 <= 2147446784) by (clear - O5; lia).
  assert (DJ2 : S - 256 + 256 <= v \/ v + 24 <= S - 256) by (clear - O2 SLO; lia).
  assert (DJ3 : pv + 1 <= S - 256 \/ S - 256 + 256 <= pv) by (clear - PVS; lia).
  assert (BC47 : 0 <= b + c <= 2 ^ 47) by (destruct (Z.eq_dec c 0) as [E0|NE]; [rewrite (BZ0 E0), E0; clear; lia| destruct (LIVE0 ltac:(clear - NE ZC0; lia)) as (X1' & X2' & _); clear - X1' X2' SLO SHI SPT ZC0; lia]).
  destruct (u8_at_of_defined M0 pv ltac:(clear - PV1 PV2; lia) ltac:(pose proof (PVD 0 ltac:(clear; lia)) as D0; rewrite Z.add_0_r in D0; exact D0)) as (bt & BT & BTM).
  assert (BTv : L5.u8_at RSEGS (mrestrict (ahid Aw0 model0) M0) pv bt) by (apply (proj2 (L5A.u8_at_vis (ahid Aw0 model0) M0 pv bt PVVIS ltac:(clear - PV1; lia) ltac:(clear - PV2; lia))); exact BTM).
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ FF LK0 cr0 Aw0 M0 model0 HH) as (HOFF & VIS & VIMG & VFS & VBLK & VBSH & VFSSH & VSTSH).
  assert (PVSHV : L5A.avis (ahid Aw0 model0) (pv / 8 + SBL) 1).
  { destruct PVOK as (_ & _ & _ & [(P1 & P2)|(f & Hf & P1 & P2)]).
    - apply VSTSH. intros i Hi. unfold in_shadow_of, HeapIfaceA.S. replace (pv / 8 + SBL + i) with (pv / 8 + SBL) by (clear - Hi; lia).
      split; [apply Z.add_le_mono_r; apply Z.div_le_mono; clear - P1 SLO C0'; lia| apply Z.add_le_mono_r; apply Z.div_le_mono; clear - P2 SPT; lia].
    - pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & WF & _). destruct (WF f Hf) as (F1 & F2 & _). destruct f as [[F kc] rs]. cbn [ff_addr ff_class fst snd] in *.
      apply VFSSH. intros i Hi. unfold in_shadow_of, HeapIfaceA.S. replace (pv / 8 + SBL + i) with (pv / 8 + SBL) by (clear - Hi; lia).
      split; [apply Z.add_le_mono_r; apply Z.div_le_mono; clear - P1 F1; lia| apply Z.add_le_mono_r; apply Z.div_le_mono; unfold FS_BYTES in *; clear - P2 F2; lia]. }
  assert (PVZv : L5KA.zeros_at (mrestrict (ahid Aw0 model0) M0) (pv / 8 + SBL) 1).
  { intros i Hi. replace (pv / 8 + SBL + i) with (pv / 8 + SBL) by (clear - Hi; lia).
    pose proof (PVSHV 0 ltac:(clear; lia)) as AV0. rewrite Z.add_0_r in AV0. rewrite (mrestrict_visible (ahid Aw0 model0) M0 _ AV0). exact PVZ. }
  pose proof SKA0 as SKAe. rewrite Esk in SKAe. pose proof SKAe as (W0 & W8 & W16 & _). cbn [PESK.sk_b PESK.sk_z PESK.sk_c] in W0, W8, W16.
  assert (INC0 : incl (PESK.sink_own (PESK.SK b z c)) (PESK.sink_own sk)) by (rewrite <- Esk; apply incl_refl).
  pose proof (UB 1%nat) as UB1. pose proof (UB 8%nat) as UB8. pose proof (UB 9%nat) as UB9. pose proof (UB 18%nat) as UB18. pose proof (UB 19%nat) as UB19. pose proof (UB 20%nat) as UB20.
  assert (SVP : forall (M1v M1 : word -> option byte),
      (forall a val, (S - 12288 <= a /\ a + 8 <= S) \/ (v <= a /\ a + 8 <= v + 24) -> L5.u64_at RSEGS M1v a val -> L5.u64_at RSEGS M1 a val) ->
      L5.u64_at RSEGS M1v (S - 48) (bv_unsigned (getr R0 (reg 20))) -> L5.u64_at RSEGS M1v (S - 40) (bv_unsigned (getr R0 (reg 19))) ->
      L5.u64_at RSEGS M1v (S - 32) (bv_unsigned (getr R0 (reg 18))) -> L5.u64_at RSEGS M1v (S - 24) (bv_unsigned (getr R0 (reg 9))) ->
      L5.u64_at RSEGS M1v (S - 16) (bv_unsigned (getr R0 (reg 8))) -> L5.u64_at RSEGS M1v (S - 8) (bv_unsigned (getr R0 (reg 1))) -> saves M1).
  { intros M1v M1 VUP C48 C40 C32 C24 C16 C8. unfold saves, U. repeat split; (apply VUP; [left; clear; lia| assumption]). }
  assert (E2122 : forall R1, (forall i, In i [21; 22]%nat -> getr R1 (reg i) = getr R0 (reg i)) -> forall i, In i [21; 22]%nat -> getr R1 (reg i) = Z_to_bv 64 (U i)).
  { intros R1 KS i Hi. rewrite (KS i Hi). unfold U. apply wid. }
  assert (KEEPv : forall M1 : word -> option byte, (forall a, 0 <= a < 2 ^ 64 -> ~ (S - 48 <= a < S - 48 + 48) -> M1 (Z_to_bv 64 a) = M0 (Z_to_bv 64 a)) ->
      forall a val, v <= a -> a + 8 <= v + 24 -> L5.u64_at RSEGS M0 a val -> L5.u64_at RSEGS M1 a val).
  { intros M1 FR1 a val Ha Hb X. apply (L5C.u64_at_agree RSEGS M0 M1); [| clear - Ha O1; lia| clear - Hb O2 SLO SHI SPT; lia| exact X].
    intros i Hi. apply FR1; [clear - Hi Ha Hb O1 O2 SLO SHI SPT; lia|]. intros Y. clear - Y Hi Ha Hb O2 SLO. lia. }
  destruct (Z.eq_dec z c) as [EZC|NZC].
  -
    pose proof W8 as W8c. rewrite EZC in W8c.
    pose proof (PEASKPP.askAS_conc fx R0 (mrestrict (ahid Aw0 model0) M0) (fun j => match j with 2%nat => S | 33%nat => b | 34%nat => c | 35%nat => c | 40%nat => bt | _ => 0 end)) as PP.
    cbn beta iota in PP. rewrite E10, E11 in PP. rewrite !(L5.unsigned_lit v) in PP by (clear - O1 O2 SLO SHI SPT; lia). rewrite !(L5.unsigned_lit pv) in PP by (clear - PV1 PV2; lia).
    pose proof NMAXI as NMX. pose proof C310 as C31.
    hide_disj. L5SAR.feed PP ltac:(first [apply wid | apply wrng | pfeed XW XSZ XAV]). unhide.
    destruct PP as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & A1 & A2 & A8 & A9 & A12 & A18 & A19 & A20 & C48 & C40 & C32 & C24 & C16 & C8).
    apply (piece_step fx fx1 R0 PC0 R1 0xaf130 _ M0 model0 cr0 LK0 Aw0 M1v (fun a => S - 48 <= a < S - 48 + 48) HH SO MO MS1 MG1 FRZ1); [intros a Pa; left; clear - Pa; lia|].
    intros M1 model1 HH1 SO1 MO1 FR1 VUP AGS.
    pose proof (sink_at_xfer _ _ LK0 cr0 Aw0 M0 model0 LK0 cr0 Aw0 M1 model1 (PESK.SK b z c) HH MO HH1 MO1 INC0 INC0 SKAe
                  (KEEPv M1 FR1 v b ltac:(clear; lia) ltac:(clear; lia) W0) (KEEPv M1 FR1 (v + 8) (b + z) ltac:(clear; lia) ltac:(clear; lia) W8)
                  (KEEPv M1 FR1 (v + 16) (b + c) ltac:(clear; lia) ltac:(clear; lia) W16)) as SKA1'.
    assert (SKA1 : PESKA.sink_atA RSEGS L ar P M1 v sk).
    { rewrite Esk. apply SKA1'. cbn [PESK.sk_b PESK.sk_c]. intros HC. destruct (LIVE0 HC) as (Hb4 & Hbce & _). apply AGS; clear - Hb4 Hbce SLO SHI SPT; lia. }
    apply (tail_S1 fx1 R1 M1 model1 LK0 Aw0 b z c Esk EZC A1 A2 A8 A9).
    + rewrite (KS1 10%nat) by inl. exact E10.
    + rewrite (KS1 11%nat) by inl. exact E11.
    + rewrite EZC. exact A18.
    + exact A19. + exact A20.
    + apply E2122. intros i Hi. apply KS1. clear - Hi. cbn in Hi |- *. tauto.
    + apply (kept0_of R0 R1 KP0). intros i Hi. apply KS1. clear - Hi. cbn in Hi. repeat (destruct Hi as [<-|Hi]; [inl|]). destruct Hi.
    + exact SO1. + exact MO1.
    + exact (SVP M1v M1 VUP C48 C40 C32 C24 C16 C8).
    + exact HH1. + exact SKA1.
    + exact (pv_piece _ LK0 cr0 Aw0 M0 model0 M1 (fun a => S - 48 <= a < S - 48 + 48) HH MO FR1 ltac:(intros i Pi; cbv beta in Pi; left; clear - Pi; lia) AGS PVOK).
  -
    assert (ZC : z < c) by (clear - NZC ZC0; lia). assert (HC : 0 < c) by (clear - ZC ZC0; lia).
    destruct (LIVE0 HC) as (Hb4 & Hbce & Hb16 & Hbsh & Hbimg & Hbv). unfold nsh in Hbsh.
    assert (DJ4 : 2147446784 + 17592186048512 <= b \/ b + c <= 2147446784) by (clear - Hbsh; lia).
    assert (DJ5 : 65536 + 6848512 <= b \/ b + c <= 65536) by (clear - Hbimg; lia).
    assert (OWN : PESK.sink_own sk = [(b, c)]) by (rewrite Esk; unfold PESK.sink_own; cbn [PESK.sk_b PESK.sk_c]; replace (c =? 0) with false by (symmetry; apply Z.eqb_neq; clear - HC; lia); reflexivity).
    pose proof NMAXI as NMX. pose proof C310 as C31.
    pose proof (PEASKPP.askA_conc fx R0 (mrestrict (ahid Aw0 model0) M0) (fun j => match j with 2%nat => S | 33%nat => b | 34%nat => z | 35%nat => c | 40%nat => bt | _ => 0 end)) as PP.
    cbn beta iota in PP. rewrite E10, E11 in PP. rewrite !(L5.unsigned_lit v) in PP by (clear - O1 O2 SLO SHI SPT; lia). rewrite !(L5.unsigned_lit pv) in PP by (clear - PV1 PV2; lia).
    hide_disj. L5SAR.feed PP ltac:(first [apply wid | apply wrng | pfeed XW XSZ XAV]). unhide.
    destruct PP as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & A1 & A2 & A8 & A9 & A11 & A12 & A18 & A19 & A20 & C48 & C40 & C32 & C24 & C16 & C8).
    apply (piece_step fx fx1 R0 PC0 R1 ANNI _ M0 model0 cr0 LK0 Aw0 M1v (fun a => S - 48 <= a < S - 48 + 48) HH SO MO MS1 MG1 FRZ1); [intros a Pa; left; clear - Pa; lia|].
    intros M1 model1 HH1 SO1 MO1 FR1 VUP AGS.
    pose proof SO1 as (AM1 & _).
    pose proof (SVP M1v M1 VUP C48 C40 C32 C24 C16 C8) as SV1.
    pose proof (sink_at_xfer _ _ LK0 cr0 Aw0 M0 model0 LK0 cr0 Aw0 M1 model1 (PESK.SK b z c) HH MO HH1 MO1 INC0 INC0 SKAe
                  (KEEPv M1 FR1 v b ltac:(clear; lia) ltac:(clear; lia) W0) (KEEPv M1 FR1 (v + 8) (b + z) ltac:(clear; lia) ltac:(clear; lia) W8)
                  (KEEPv M1 FR1 (v + 16) (b + c) ltac:(clear; lia) ltac:(clear; lia) W16)) as SKA1'.
    assert (SKA1 : PESKA.sink_atA RSEGS L ar P M1 v sk).
    { rewrite Esk. apply SKA1'. cbn [PESK.sk_b PESK.sk_c]. intros _. apply AGS; clear - Hb4 Hbce SLO SHI SPT; lia. }
    clear SKA1'.
    pose proof (pv_piece _ LK0 cr0 Aw0 M0 model0 M1 (fun a => S - 48 <= a < S - 48 + 48) HH MO FR1 ltac:(intros i Pi; cbv beta in Pi; left; clear - Pi; lia) AGS PVOK) as PV1'.
    assert (KP1 : kept0 R1) by (apply (kept0_of R0 R1 KP0); intros i Hi; apply KS1; clear - Hi; cbn in Hi; repeat (destruct Hi as [<-|Hi]; [inl|]); destruct Hi).
    rewrite OWN in HH1.
    pose proof SKA1 as SKA1b. rewrite Esk in SKA1b.
    pose proof (bat_of_sink _ LK0 cr0 Aw0 M1 model1 b z c HH1 MO1 SKA1b ltac:(apply incl_refl) HC) as BAT1.
    destruct (centryS R1 _ LK0 cr0 Aw0 M1 model1 48 0xaf094 HH1 MO1 (kept1_of0 R1 KP1) A1 ltac:(split; [clear; lia| reflexivity]) A2 ltac:(clear; lia) ltac:(reflexivity)) as (ENT1 & FRS1).
    assert (E10' : getr R1 10%bv = Z_to_bv 64 v) by (rewrite L5K.rl10, (KS1 10%nat) by inl; exact E10).
    assert (E11' : getr R1 11%bv = Z_to_bv 64 1) by (rewrite L5K.rl11; exact A11).
    assert (ACC1 : PMSPA.accA M1 v 24) by (destruct MO1 as (_ & _ & _ & X & _); exact X).
    pose proof ANNI_ok as AI. unfold PEASKANG.ann_increase_s_spec in AI. unfold PMSPA.cfg.
    apply (AI fx1 R1 M1 model1 K LB FF LK0 Aw0 cr0 v 1 b z c (S - 48) 0xaf094 HH1 AM1 K0 ENT1 FRS1 E10' E11' AO V8 ACC1 BAT1 ltac:(clear; lia) ltac:(clear - ZC; lia)).
    intros fx2 R2 M2 model2 LK2 Aw2 RP2 BH2 ACCv2 [ACCb2 ANN2] FRB2 HP2 MRT2 ILK2 IAW2 AM2 HH2.
    assert (WIN : forall rg, In rg (@nil L5.range) -> exists q m, In (q, m) [(b, c)] /\ q <= fst rg /\ fst rg + snd rg <= q + m) by (intros rg []).
    pose proof (mem_ok_callee [(b, c)] [] LK0 cr0 Aw0 M1 model1 M2 (S - 48) 4096 [] HH1 MO1 HP2 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) WIN) as MO2.
    pose proof (saves_callee [(b, c)] LK0 cr0 Aw0 M1 model1 M2 [] (S - 48) 4096 [] HH1 MO1 HP2 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) WIN SV1) as SV2.
    pose proof (pv_callee [(b, c)] LK0 cr0 Aw0 M1 model1 M2 [] (S - 48) 4096 [] HH1 MO1 HP2 ltac:(clear; lia) (PMKA.wapp_nil) WIN PV1') as PV2'.
    assert (CS2 : forall i, In i L5SAR.cs_all -> getr R2 (reg i) = getr R1 (reg i)) by (intros i Hi; exact (L5SAR.cs_of_preserved R1 R2 i RP2 Hi)).
    apply (fast_B fx2 R2 M2 model2 LK2 Aw2 b z c Esk ZC).
    + rewrite CS2 by inl. exact A2.
    + rewrite CS2 by inl. exact A8.
    + rewrite CS2 by inl. exact A9.
    + rewrite CS2 by inl. exact A18.
    + rewrite CS2 by inl. exact A19.
    + rewrite CS2 by inl. exact A20.
    + apply E2122. intros i Hi. rewrite CS2 by (clear - Hi; cbn in Hi |- *; unfold L5SAR.cs_all; cbn; tauto). apply KS1. clear - Hi. cbn in Hi |- *. tauto.
    + exact (kept0_pres R1 R2 KP1 RP2).
    + exact (stok_step model1 LK0 Aw0 model2 LK2 Aw2 SO1 AM2 MRT2 ILK2 IAW2).
    + exact MO2. + exact SV2. + exact HH2. + exact BH2. + exact ACCb2. + exact ANN2. + exact PV2'.
Qed.

End Call.

Theorem push_back_ok : PESKA.push_back_specA RSEGS AD EE L ar HI P.
Proof.
  unfold PESKA.push_back_specA. intros PMODE fx R M model K LBX FF LK Aw cr o pv sp r k HH AM K0 ENT FRM FRS A10 A11 SKA AO V8 PVOK GROW CRL KONT.
  change (pe_push_back EE) with 0xaf02c.
  exact (entry_ok PMODE R M model K LBX FF LK Aw cr o pv sp r k HH AM K0 ENT FRS A10 A11 SKA AO V8 PVOK GROW CRL KONT fx (PESK.sk_b k) (PESK.sk_z k) (PESK.sk_c k) ltac:(destruct k; reflexivity)).
Qed.

End WithHeap.
End PEASKP.

