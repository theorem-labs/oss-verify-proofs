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
     AsanAcct AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5CoreKit L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b L5CoreSpecsA_b L5StepAR_b L5CoreBR_b L5ADetailHR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PnSpecsAa_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PMASRK.
Import L5A. Import L5CA. Import L5SAR.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).

Lemma rdn_cons1R (MV : word -> option byte) a b (n : nat) bs : 0 <= a ->
  rdn RSEGS MV (Z_to_bv 64 a) 1 = Some [b] -> rdn RSEGS MV (Z_to_bv 64 (a + 1)) n = Some bs -> rdn RSEGS MV (Z_to_bv 64 a) (Datatypes.S n) = Some (b :: bs).
Proof.
  intros Ha H1 H2. change (Datatypes.S n) with (1 + n)%nat. change (b :: bs) with ([b] ++ bs). apply (SeqExec.rdn_app RSEGS MV 1%nat n _ _ _ H1).
  replace (Z_to_bv 64 a + nat_to_word 1)%bv with (Z_to_bv 64 (a + 1)); [exact H2|].
  apply bv_eq. unfold nat_to_word. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. rewrite <- Zplus_mod. reflexivity.
Qed.
Lemma rdn_of_defR (Mx : word -> option byte) (n : nat) a : 0 <= a -> a + Z.of_nat n <= 2 ^ 63 ->
  (forall i, 0 <= i < Z.of_nat n -> Mx (Z_to_bv 64 (a + i)) <> None) -> exists bs, rdn RSEGS Mx (Z_to_bv 64 a) n = Some bs.
Proof.
  revert a. induction n as [|n IH]; intros a Ha Hn Hd.
  - exists []. reflexivity.
  - destruct (Mx (Z_to_bv 64 a)) as [b|] eqn:Eb; [|exfalso; apply (Hd 0 ltac:(lia)); rewrite Z.add_0_r; exact Eb].
    destruct (IH (a + 1) ltac:(lia) ltac:(lia)) as (bs & Hr).
    { intros i Hi. replace (a + 1 + i) with (a + (1 + i)) by lia. apply Hd. lia. }
    exists (b :: bs). apply (rdn_cons1R Mx a b n bs Ha); [cbn [rdn]; rewrite Eb; reflexivity | exact Hr].
Qed.

Section SCFG_1.
Context {SCFG_P : ScfgP}.
Section WithIface.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Let LYa := PMA.ly_as0 L C LY.

Lemma memcpy_call (fx : FPState) R M model K LB FF LK cr Aw (sp' r dst src n : Z) :
  ri_inv HI LB FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] ->
  getr R (reg 1) = Z_to_bv 64 r -> L5.ra_ok r -> getr R (reg 2) = Z_to_bv 64 sp' -> getr R (reg 4) = Z_to_bv 64 (hl_tp L) ->
  getr R (reg 10) = Z_to_bv 64 dst -> getr R (reg 11) = Z_to_bv 64 src -> getr R (reg 12) = Z_to_bv 64 n -> 0 <= n <= 16384 ->
  L5CA.astk ar M sp' 2560 ->
  aacc M dst n -> (forall i, 0 <= i < n -> aclientw L ar LB FF sp' 2560 (dst + i)) -> L5.defined M dst n -> 0 <= dst -> dst + n <= 2 ^ 47 -> app_rng ar dst n ->
  aacc M src n -> 0 <= src -> src + n <= 2 ^ 47 -> app_rng ar src n -> (forall i, 0 <= i < n -> aclient L ar LB FF sp' 2560 (src + i)) -> L5.defined M src n ->
  (dst + n <= src \/ src + n <= dst) ->
  (forall (fx' : FPState) R' M' model', regs_preserved R R' -> L5.defined M' dst n ->
      L5CA.ahpres L ar LB FF sp' 2560 [(dst, n)] M M' ->
      model_rt model model' -> L5CA.amodel_ok Aw model' -> ri_inv HI LB FF LK cr Aw M' (vml_of model') ->
      srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx' R' r M' model') K) ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0x77c94 M model) K.
Proof.
  intros HH AM HK G1 RA G2 G4 G10 G11 G12 Hn ASTK ACD CLD DDEF D0 D1 APD ACS S0 S1 APS CLS SDEF0 NOV KONT.
  pose proof (HAJ.aior_memcpy _ _ _ _ _ HIok) as HF.
  unfold amemcpy_spec, amemcpy_spec_at, amem_pre, amem_post in HF. rewrite (aly_segs L C LYa), (aly_scr_mem L C LYa), (aly_memcpy L C LYa) in HF.
  pose proof ASTK as (A16 & SLO & SHI & SPT & SD & SU).
  assert (U2 : bv_unsigned (getr R 2%bv) = sp') by (rewrite L5K.rl2, G2; apply L5.unsigned_lit; clear - SLO SHI SPT; lia).
  destruct (rdn_of_defR M (Z.to_nat n) src S0 ltac:(rewrite Z2Nat.id by lia; lia)) as (bs & RDN).
  { intros i Hi. rewrite Z2Nat.id in Hi by lia. apply SDEF0. lia. }
  unfold PMSPA.cfg.
  eapply (HF fx R M model LB FF LK cr Aw dst src n bs K); clear HF.
  - split. exact HH. split. exact (proj1 AM). split. exact (proj2 AM).
    split. rewrite L5K.rl10. exact G10. split. rewrite L5K.rl12. exact G12. split. lia.
    split. rewrite L5K.rl4. exact G4.
    split. rewrite L5K.rl1, G1. apply Hoare.ret_ok_even. rewrite L5.unsigned_lit by (destruct RA as [X _]; clear - X; lia). exact (proj2 RA).
    split. { rewrite U2. pose proof (astack_ok_of_astk L ar C LYa M M sp' 2560 0 2560 ASTK (mem_grows_refl M)) as X.
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

End WithIface.
End SCFG_1.
End PMASRK.
