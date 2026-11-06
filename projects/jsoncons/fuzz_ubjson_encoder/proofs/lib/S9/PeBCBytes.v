(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec SeqExec LibIface AxSymExec3 SegRun BigLinkBase BigLinkGlue CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct AxSymExec3Sound HeapIface HeapIfaceA HeapIfaceAEx IcptIfaceAB0 L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA L5DefsAB0 L5CoreAB0S9 L5StepARB0S9 HeapIfaceAEx L5CoreSpecsAB0S9 L5CoreBRB0S9 L5ADetailHRB0S9 PeBSrcReadK.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout PeLayoutA PeLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PmSpecsA PeSpecsAb PmModelFactsA PeStepAB0 XIcptAs0B0.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9.asan Require Import XIcptAB0S9.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PECBB.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)).

Lemma u8_copy (M1 M2 : word -> option byte) a a' v :
  M2 (Z_to_bv 64 a') = M1 (Z_to_bv 64 a) -> M1 (Z_to_bv 64 a) <> None -> L5.u8_at RSEGS M1 a v -> L5.u8_at RSEGS M2 a' v.
Proof.
  unfold L5.u8_at. cbn [rdn]. intros E D H. rewrite E. destruct (M1 (Z_to_bv 64 a)) as [b|]; [exact H| exfalso; apply D; reflexivity].
Qed.
Lemma bytes_at_copy (M1 M2 : word -> option byte) src dst l :
  (forall i, 0 <= i < Z.of_nat (length l) -> M2 (Z_to_bv 64 (dst + i)) = M1 (Z_to_bv 64 (src + i))) ->
  L5.defined M1 src (Z.of_nat (length l)) -> L5.bytes_at RSEGS M1 src l -> L5.bytes_at RSEGS M2 dst l.
Proof.
  intros C D B i Hi. apply (u8_copy M1 M2 (src + Z.of_nat i) (dst + Z.of_nat i)); [apply C; lia| apply D; lia| apply B; exact Hi].
Qed.

Lemma rdn_nth_def : forall (M : word -> option byte) (n : nat) a bs (k : nat),
  rdn RSEGS M (Z_to_bv 64 a) n = Some bs -> (k < n)%nat -> M (Z_to_bv 64 (a + Z.of_nat k)) <> None ->
  M (Z_to_bv 64 (a + Z.of_nat k)) = Some (nth k bs (Z_to_bv 8 0)).
Proof.
  intros M n. induction n as [|n IH]; intros a bs k R Hk D; [lia|].
  cbn [rdn] in R. rewrite (L5C.add1_lit a) in R.
  destruct (M (Z_to_bv 64 a)) as [b|] eqn:E1.
  - destruct (rdn RSEGS M (Z_to_bv 64 (a + 1)) n) as [r1|] eqn:E3; [|discriminate]. injection R as <-.
    destruct k as [|k]; [rewrite Z.add_0_r; rewrite E1; reflexivity|].
    replace (a + Z.of_nat (Datatypes.S k)) with ((a + 1) + Z.of_nat k) by lia. cbn [nth].
    apply (IH (a + 1) r1 k E3 ltac:(lia)). replace (a + 1 + Z.of_nat k) with (a + Z.of_nat (Datatypes.S k)) by lia. exact D.
  - destruct (seg_rom RSEGS (Z_to_bv 64 a)) as [b|]; [|discriminate].
    destruct (rdn RSEGS M (Z_to_bv 64 (a + 1)) n) as [r1|] eqn:E3; [|discriminate]. injection R as <-.
    destruct k as [|k]; [exfalso; apply D; rewrite Z.add_0_r; exact E1|].
    replace (a + Z.of_nat (Datatypes.S k)) with ((a + 1) + Z.of_nat k) by lia. cbn [nth].
    apply (IH (a + 1) r1 k E3 ltac:(lia)). replace (a + 1 + Z.of_nat k) with (a + Z.of_nat (Datatypes.S k)) by lia. exact D.
Qed.

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
Section Kit.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMB.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Let LYa := PMB.ly_as0 L C LY.

Lemma move_stage_pre_c (IL : icpt_layout) (ICok : aicpt_ok L ar IL SCFG HI) (ILY : as0_icpt_layout IL)
      LB' FF LK cr Aw M model (fx0 fx : FPState) R0 (pc0 : Z) R (dst src len sp r : Z) K :
  ri_inv HI LB' FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] ->
  msteps RSEGS (st fx0 R0 pc0 (mrestrict (ahid Aw model) M)) (st fx R 0x78e38 (mrestrict (ahid Aw model) M)) ->
  getr R (reg 1) = Z_to_bv 64 r -> L5.ra_ok r -> getr R (reg 2) = Z_to_bv 64 sp -> getr R (reg 4) = Z_to_bv 64 (hl_tp L) ->
  getr R (reg 10) = Z_to_bv 64 dst -> getr R (reg 11) = Z_to_bv 64 src -> getr R (reg 12) = Z_to_bv 64 len ->
  0 <= len <= 2 ^ 27 -> L5CA.astk ar M sp 2560 ->
  (exists q A0, In (q, A0) LB' /\ q <= dst /\ dst + len <= q + A0) -> L5.defined M dst len -> aacc M dst len ->
  ((exists q A0, In (q, A0) LB' /\ q <= src /\ src + len <= q + A0) \/ (exists o' sz', L5CA.aobj FF o' sz' /\ o' <= src /\ src + len <= o' + sz')) ->
  L5.defined M src len -> aacc M src len ->
  (dst + len <= src \/ src + len <= dst) ->
  (forall (R1 : bvmap 5 word) M1 model1, regs_preserved R R1 -> getr R1 (reg 10) = Z_to_bv 64 dst ->
     (forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB' FF sp 2560 a -> ~ (dst <= a < dst + len) -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
     (forall a, sp - 2560 <= a < sp -> M1 (Z_to_bv 64 a) <> None) -> L5.defined M1 dst len ->
     (forall i, 0 <= i < len -> M1 (Z_to_bv 64 (dst + i)) = M (Z_to_bv 64 (src + i))) ->
     model_rt model model1 -> L5CA.amodel_ok Aw model1 -> ri_inv HI LB' FF LK cr Aw M1 (vml_of model1) ->
     srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R1 r M1 model1) K) ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx0 R0 pc0 M model) K.
Proof.
  intros HH AM K0 PRE H1 RA H2 H4 H10 H11 H12 Hlen STK DC DD DA SC SD SA OVL KONT.
  pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & _).
  destruct DC as (qd & Ad & Hind & D1 & D2).
  destruct (WB (qd, Ad) Hind) as ((Q0 & Q1 & Q2 & Q3 & Q4 & Q5) & _). cbn [fst snd] in *. unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in Q5.
  assert (SRCB : 0 <= src /\ src + len <= ahl_ceil ar /\ app_rng ar src len /\ (forall i, 0 <= i < len -> aclient L ar LB' FF sp 2560 (src + i))).
  { destruct SC as [(qs & As & Hins & X1 & X2)|(o' & sz' & AO & X1 & X2)].
    - destruct (WB (qs, As) Hins) as ((P0 & P1 & P2 & P3 & P4 & P5) & _). cbn [fst snd] in *.
      split; [lia|]. split; [lia|]. split; [apply (L5SAR.app_rng_block L ar C HI HIok LB' FF LK cr Aw M _ qs As src len HH Hins X1 X2)|].
      intros i Hi. apply (L5SAR.block_client L ar LB' FF sp 2560 qs As); [exact Hins| lia].
    - pose proof AO as (f & Hf & F1 & F2 & F3). destruct (WF f Hf) as (Y1 & Y2 & _). unfold app_mem, FS_BYTES in FSAPP, Y2. unfold FS_BYTES in FSCEIL.
      split; [lia|]. split; [lia|]. split; [apply (L5SAR.app_rng_aobj L ar C HI HIok LB' FF LK cr Aw M _ o' sz' src len HH AO X1 X2)|].
      intros i Hi. apply (L5SAR.obj_client L ar LB' FF sp 2560 o' sz'); [exact AO| lia]. }
  destruct SRCB as (S0 & S1 & SAR & SCL).
  unfold PMSPA.cfg.
  apply (L5SAR.apiece_ro L ar C HI LYa HIok LB' FF LK cr Aw M model fx0 fx R0 pc0 R 0x78e38 _ K HH AM PRE (fun x X => X) (fun a _ => eq_refl)).
  intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1.
  assert (EM : M1 = M).
  { apply functional_extensionality. intros x. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply FR1. pose proof (bv_unsigned_in_range 64 x) as X.
    change (bv_modulus 64) with (2 ^ 64) in X. exact X. }
  subst M1. pose proof AM1 as (Mh1 & MI1).
  pose proof (aic_memmove_libc _ _ _ _ _ ICok) as MMV. unfold amemmove_libc_spec, amemcpy_spec_at, amem_pre, amem_post in MMV.
  rewrite (aicl_memmove IL ILY), (L5A.aly_segs L C LYa), (L5A.aly_scr_mem L C LYa) in MMV.
  destruct (AX2S.rdn_defined RSEGS M (Z.to_nat len) (Z_to_bv 64 src)) as (bs & RDN & LEN).
  { rewrite L5.unsigned_lit by lia. lia. }
  { intros j Hj. unfold AX2S.rd1. rewrite L5.unsigned_lit by lia. specialize (SD (Z.of_nat j) ltac:(lia)). destruct (M _); [discriminate| exfalso; exact (SD eq_refl)]. }
  assert (U2 : bv_unsigned (getr R 2%bv) = sp).
  { rewrite L5K.rl2, H2. apply L5.unsigned_lit. lia. }
  apply (MMV fx R M model1 LB' FF LK cr Aw dst src len bs K); clear MMV.
  - split; [exact HH1|]. split; [exact Mh1|]. split; [exact MI1|].
    split; [rewrite L5K.rl10; exact H10|]. split; [rewrite L5K.rl12; exact H12|]. split; [lia|].
    split; [rewrite L5K.rl4; exact H4|].
    split; [rewrite L5K.rl1, H1; apply L5K.ret_ok_lit; exact RA|].
    split; [rewrite U2; pose proof (L5SAR.astack_ok_of_astk L ar C LYa M M sp 2560 0 2560 STK (fun x X => X) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite Z.sub_0_r; exact A16)) as AS0;
            rewrite Z.sub_0_r in AS0; exact AS0|].
    split; [exact DA|].
    split; [intros i Hi; rewrite U2; apply (L5SAR.block_client L ar LB' FF sp 2560 qd Ad); [exact Hind| lia]|].
    split; [intros i m Hi Hm; apply (L5C.writable_of_defined RSEGS M dst len DD); lia|].
    split; [exact K0|]. apply (L5SAR.app_rng_block L ar C HI HIok LB' FF LK cr Aw M _ qd Ad dst len HH Hind D1 D2).
  - rewrite L5K.rl11. exact H11.
  - exact SA.
  - lia.
  - exact SAR.
  - intros i Hi. right. rewrite U2. apply SCL. exact Hi.
  - exact RDN.
  - intros _. exact OVL.
  - intros R' M' model' R10' RP BYTES PRES SDEF' RT MI' HH'. rewrite U2 in PRES, SDEF'. rewrite <- L5K.rl1 in H1. rewrite H1.
    apply (KONT R' M' model' RP ltac:(rewrite <- L5K.rl10; exact R10') PRES SDEF').
    + intros i Hi. destruct (BYTES i Hi) as (v & _ & Bv). unfold byte_at in Bv. rewrite Bv. discriminate.
    + intros i Hi. destruct (BYTES i Hi) as (v & (NB & _) & Bv). unfold byte_at in Bv. rewrite Bv.
      pose proof (rdn_nth_def M (Z.to_nat len) src bs (Z.to_nat i) RDN ltac:(lia) ltac:(replace (src + Z.of_nat (Z.to_nat i)) with (src + i) by lia; apply SD; lia)) as RB.
      replace (src + Z.of_nat (Z.to_nat i)) with (src + i) in RB by lia. rewrite RB. f_equal. symmetry. apply nth_error_nth. exact NB.
    + exact (L5LZ.model_rt_trans model model1 model' MRT1 RT).
    + split; [rewrite (L5LZ.model_rt_halted _ _ RT); exact Mh1| exact MI'].
    + exact HH'.
Qed.

Import L5A. Import L5CA. Import L5SAR.
Lemma memcpy_call_c (fx : FPState) R M model K LB FF LK cr Aw (sp' r dst src n : Z) :
  ri_inv HI LB FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] ->
  getr R (reg 1) = Z_to_bv 64 r -> L5.ra_ok r -> getr R (reg 2) = Z_to_bv 64 sp' -> getr R (reg 4) = Z_to_bv 64 (hl_tp L) ->
  getr R (reg 10) = Z_to_bv 64 dst -> getr R (reg 11) = Z_to_bv 64 src -> getr R (reg 12) = Z_to_bv 64 n -> 0 <= n <= 16384 ->
  L5CA.astk ar M sp' 2560 ->
  aacc M dst n -> (forall i, 0 <= i < n -> aclientw L ar LB FF sp' 2560 (dst + i)) -> L5.defined M dst n -> 0 <= dst -> dst + n <= 2 ^ 47 -> app_rng ar dst n ->
  aacc M src n -> 0 <= src -> src + n <= 2 ^ 47 -> app_rng ar src n -> (forall i, 0 <= i < n -> aclient L ar LB FF sp' 2560 (src + i)) -> L5.defined M src n ->
  (dst + n <= src \/ src + n <= dst) ->
  (forall (fx' : FPState) R' M' model', regs_preserved R R' -> L5.defined M' dst n ->
      (forall i, 0 <= i < n -> M' (Z_to_bv 64 (dst + i)) = M (Z_to_bv 64 (src + i))) ->
      L5CA.ahpres L ar LB FF sp' 2560 [(dst, n)] M M' ->
      model_rt model model' -> L5CA.amodel_ok Aw model' -> ri_inv HI LB FF LK cr Aw M' (vml_of model') ->
      srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx' R' r M' model') K) ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0x78e40 M model) K.
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
    + intros i Hi. destruct (BYTES i Hi) as (v & (NB & _) & Bv). unfold byte_at in Bv. rewrite Bv.
      pose proof (rdn_nth_def M (Z.to_nat n) src bs (Z.to_nat i) RDN ltac:(lia) ltac:(replace (src + Z.of_nat (Z.to_nat i)) with (src + i) by lia; apply SDEF0; lia)) as RB.
      replace (src + Z.of_nat (Z.to_nat i)) with (src + i) in RB by lia. rewrite RB. f_equal. symmetry. apply nth_error_nth. exact NB.
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
End Kit.
End PECBB.
