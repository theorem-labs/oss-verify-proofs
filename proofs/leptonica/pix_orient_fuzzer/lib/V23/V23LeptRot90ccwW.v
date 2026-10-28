(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac SeqExec.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic PFLib LeptDefs LeptStructs LeptArith LeptArith2.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require Import O23LeptRot90cwW.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptBase V23LeptRot90cwW V23LeptRot90ccw.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section R90W.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V23Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Section CCW.
Variables (C : lctx) (Ar A : AS) (md : Model) (mB : word -> option byte) (s datad wpld hd wd kd datas wpls ks : Z) (S : TSet).
Hypothesis CK : Cok C.
Hypothesis SUB : sub_live Ar A.
Hypothesis Ld : live A (Z_to_bv 64 datad) = Some kd.
Hypothesis Hkd : (4 * wpld * hd <= kd)%Z.
Hypothesis Ldr : live Ar (Z_to_bv 64 datad) = None.
Hypothesis Ld0 : live (c_A0 C) (Z_to_bv 64 datad) = None.
Hypothesis Ls : live A (Z_to_bv 64 datas) = Some ks.
Hypothesis Hks : (4 * wpls * wd <= ks)%Z.
Hypothesis Hdd : (0 <= datad < 2 ^ 64)%Z.
Hypothesis Hds : (0 <= datas < 2 ^ 64)%Z.
Hypothesis Hwd : (1 <= wd < 2 ^ 24)%Z.
Hypothesis Hhd : (1 <= hd < 2 ^ 24)%Z.
Hypothesis Hwpld : (1 <= wpld < 2 ^ 24)%Z.
Hypothesis Hwpls : (1 <= wpls < 2 ^ 24)%Z.
Hypothesis Hwd32 : (wd <= 32 * wpld)%Z.
Hypothesis Hhd32 : (hd <= 32 * wpls)%Z.
Hypothesis Hs : (128 <= s)%Z.
Hypothesis Hs64 : (s < 2 ^ 64)%Z.
Hypothesis Hbelow : (datad + kd <= s - 192)%Z.
Hypothesis RWD : rdn SEGS mB (Z_to_bv 64 (s - 108)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 wd)).
Hypothesis RHD : rdn SEGS mB (Z_to_bv 64 (s - 112)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 hd)).
Hypothesis RDD : rdn SEGS mB (Z_to_bv 64 (s - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 datad)).
Hypothesis ALd : (datad mod 16 = 0)%Z.
Hypothesis ALs : (datas mod 16 = 0)%Z.
Hypothesis Hd4k : (4096 <= datad)%Z.
Hypothesis Hs4k : (4096 <= datas)%Z.
Hypothesis Hszs : (4 * wpls * wd <= 2 ^ 26)%Z.
Hypothesis Hstk : (c_top C - LSTK + 192 <= s)%Z.
Hypothesis Htop : (s <= c_top C)%Z.
Hypothesis Hszd : (4 * wpld * hd <= 2 ^ 26)%Z.
Hypothesis Hdw : (4 * wpld < datad)%Z.

(* [comment removed for export] *)
Definition FTc (m : word -> option byte) : Prop :=
  forall a : word, ~ (datad <= u a < datad + 4 * wpld * hd)%Z -> ~ (s - 192 <= u a < s - 136)%Z -> m a = mB a.

Definition FTi (m : word -> option byte) : Prop :=
  forall a : word, ~ (datad <= u a < datad + 4 * wpld * hd)%Z -> m a = SLW mB s hd a.

Lemma FTc_cell : forall m (a : Z) (n : nat), FTc m -> (s - 136 <= a)%Z -> (a + Z.of_nat n <= s)%Z ->
  rdn SEGS m (Z_to_bv 64 a) n = rdn SEGS mB (Z_to_bv 64 a) n.
Proof using Hbelow Hs64 Hs Hkd kd Hdd Hwpld Hhd.
  clear - Hbelow Hs64 Hs Hkd Hdd Hwpld Hhd.
  intros m a n HF Ha Hn. assert (HP : (0 <= 4 * wpld * hd)%Z) by (apply Z.mul_nonneg_nonneg; lia).
  apply rdn_ext; rewrite u_Z2bv by lia; [lia|].
  intros x Hx. apply HF; lia.
Qed.

Ltac ccw_ad := rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; lia.

Lemma ccw_s192 : (0 <= 4 * wpld * hd)%Z /\ (192 <= s)%Z.
Proof. assert (0 <= 4 * wpld * hd)%Z by (apply Z.mul_nonneg_nonneg; lia). split; lia. Qed.

Lemma FTi_FTc : forall m, FTi m -> FTc m.
Proof.
  intros m HF a H1 H2. destruct ccw_s192 as [HP HS]. pose proof (u64_range a) as Ua.
  rewrite (HF a H1). unfold SLW.
  repeat (rewrite wbytes_outside; [| ccw_ad | ccw_ad]). reflexivity.
Qed.

Lemma FTi_cellr : forall m (a : Z) (n : nat), FTi m -> (s - 192 <= a)%Z -> (a + Z.of_nat n <= s)%Z ->
  rdn SEGS m (Z_to_bv 64 a) n = rdn SEGS (SLW mB s hd) (Z_to_bv 64 a) n.
Proof.
  intros m a n HF Ha Hn. destruct ccw_s192 as [HP HS].
  apply rdn_ext; rewrite u_Z2bv by lia; [lia|].
  intros x Hx. apply HF; lia.
Qed.

Lemma FTi_wd : forall m, FTi m -> rdn SEGS m (Z_to_bv 64 (s - 108)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 wd)).
Proof.
  intros m HF. destruct ccw_s192 as [HP HS]. rewrite (FTi_cellr m (s - 108) 4 HF) by lia. unfold SLW.
  rewrite !rdn_wbytes_out by ccw_ad. exact RWD.
Qed.

Lemma FTi_hd : forall m, FTi m -> rdn SEGS m (Z_to_bv 64 (s - 112)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 hd)).
Proof.
  intros m HF. destruct ccw_s192 as [HP HS]. rewrite (FTi_cellr m (s - 112) 4 HF) by lia. unfold SLW.
  rewrite !rdn_wbytes_out by ccw_ad. exact RHD.
Qed.

Lemma FTi_dd : forall m, FTi m -> rdn SEGS m (Z_to_bv 64 (s - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 datad)).
Proof.
  intros m HF. destruct ccw_s192 as [HP HS]. rewrite (FTi_cellr m (s - 136) 8 HF) by lia. unfold SLW.
  rewrite !rdn_wbytes_out by ccw_ad. exact RDD.
Qed.

Lemma ccw_hit8 : forall m' (a : Z) (w : word), (0 <= a)%Z -> (a + 8 <= 2 ^ 64)%Z ->
  rdn SEGS (wbytes m' (Z_to_bv 64 a) (word_to_le_bytes 8 w)) (Z_to_bv 64 a) 8 = Some (word_to_le_bytes 8 w).
Proof.
  intros m' a w H0 H1. pose proof (rdn_wbytes_hit SEGS (word_to_le_bytes 8 w) m' (Z_to_bv 64 a)) as Hh.
  rewrite length_N_to_le_bytes in Hh. apply Hh. ccw_ad.
Qed.

Lemma FTi_one : forall m, FTi m -> rdn SEGS m (Z_to_bv 64 (s - 152)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 1)).
Proof.
  intros m HF. destruct ccw_s192 as [HP HS]. rewrite (FTi_cellr m (s - 152) 8 HF) by lia. unfold SLW.
  rewrite rdn_wbytes_out by ccw_ad. rewrite rdn_wbytes_out by ccw_ad. apply ccw_hit8; lia.
Qed.

Lemma FTi_hd8 : forall m, FTi m -> rdn SEGS m (Z_to_bv 64 (s - 160)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 hd)).
Proof.
  intros m HF. destruct ccw_s192 as [HP HS]. rewrite (FTi_cellr m (s - 160) 8 HF) by lia. unfold SLW.
  apply ccw_hit8; lia.
Qed.

Lemma FTi_a7 : forall m, FTi m -> rdn SEGS m (Z_to_bv 64 (s - 144)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (32 * (hd / 32)))).
Proof.
  intros m HF. destruct ccw_s192 as [HP HS]. rewrite (FTi_cellr m (s - 144) 8 HF) by lia. unfold SLW.
  rewrite rdn_wbytes_out by ccw_ad. apply ccw_hit8; lia.
Qed.

(* [comment removed for export] *)
Lemma FTi_store : forall m md' (tgt : Z) (wv : word), W C A m md' -> POSTM C Ar s mB m -> FTi m ->
  (datad <= tgt)%Z -> (tgt + 4 <= datad + 4 * wpld * hd)%Z ->
  W C A (wbytes m (Z_to_bv 64 tgt) (word_to_le_bytes 4 wv)) md' /\ POSTM C Ar s mB (wbytes m (Z_to_bv 64 tgt) (word_to_le_bytes 4 wv))
  /\ FTi (wbytes m (Z_to_bv 64 tgt) (word_to_le_bytes 4 wv)).
Proof.
  intros m md' tgt wv HW PM HF H1 H2. destruct ccw_s192 as [HP HS].
  destruct (WP_blk C Ar A mB m md' (Z_to_bv 64 datad) (Z_to_bv 64 tgt) kd (word_to_le_bytes 4 wv) s CK (conj HW PM)
              Ld Ldr Ld0 SUB) as [HW' PM']; [ccw_ad | ccw_ad |].
  split; [exact HW'|]. split; [exact PM'|].
  intros a Ha. pose proof (u64_range a) as Ua. rewrite wbytes_outside; [apply HF; exact Ha | ccw_ad | ccw_ad].
Qed.

Lemma SLW_W : W C A mB md ->
  store_ok SEGS mB (Z_to_bv 64 (s - 160)) 24 = true /\
  W C A (SLW mB s hd) md /\ POSTM C Ar s mB (SLW mB s hd) /\ FTi (SLW mB s hd).
Proof.
  intros HW. pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *.
  assert (HS : (192 <= s)%Z) by lia.
  split; [apply (W_sok_win C A mB md); [exact CK | exact HW | lia | cbn; lia]|].
  assert (H0 : W C A mB md /\ POSTM C Ar s mB mB) by (split; [exact HW | apply POSTM_refl]).
  pose proof (WP_win C A Ar mB mB md (Z_to_bv 64 (s - 152)) (word_to_le_bytes 8 (Z_to_bv 64 1)) s CK H0 SUB
                ltac:(ccw_ad) ltac:(ccw_ad) Htop) as H1.
  pose proof (WP_win C A Ar mB _ md (Z_to_bv 64 (s - 144)) (word_to_le_bytes 8 (Z_to_bv 64 (32 * (hd / 32)))) s CK H1 SUB
                ltac:(ccw_ad) ltac:(ccw_ad) Htop) as H2.
  pose proof (WP_win C A Ar mB _ md (Z_to_bv 64 (s - 160)) (word_to_le_bytes 8 (Z_to_bv 64 hd)) s CK H2 SUB
                ltac:(ccw_ad) ltac:(ccw_ad) Htop) as H3.
  unfold SLW. destruct H3 as [H3a H3b]. split; [exact H3a|]. split; [exact H3b|]. intros a _. reflexivity.
Qed.

Lemma ccw_alloc_hi : forall m md' (p : word) (n : Z), W C A m md' -> live A p = Some n -> (0 < n)%Z -> (u p + n < 2 ^ 47)%Z.
Proof.
  intros m md' p n HW L Hn. pose proof CK as [T1 T2 T3 T4 T5]. laypins.
  destruct (blk_range C A m md' p n CK HW L Hn) as [B1 B2]. lia.
Qed.

Lemma ccw_m4 : forall (a b : Z), (a mod 16 = 0)%Z -> ((a + 4 * b) mod 4 = 0)%Z.
Proof.
  intros a b Ha. assert (E : (a = 16 * (a / 16))%Z) by (pose proof (Z.div_mod a 16 ltac:(lia)); lia).
  rewrite E. replace (16 * (a / 16) + 4 * b)%Z with ((4 * (a / 16) + b) * 4)%Z by ring. apply Z_mod_mult.
Qed.

Lemma ccw_dst : forall m md' (i j : Z), W C A m md' -> (0 <= i < hd)%Z -> (0 <= j < wd)%Z ->
  (datad <= datad + 4 * wpld * i + 4 * ((wd - 1 - j) / 32))%Z /\
  (datad + 4 * wpld * i + 4 * ((wd - 1 - j) / 32) + 4 <= datad + 4 * wpld * hd)%Z /\
  (datad <= datad + 4 * wpld * i)%Z /\ ((datad + 4 * wpld * i) mod 4 = 0)%Z /\ (datad + 4 * wpld * hd + 192 <= s)%Z /\
  (exists (bt : list byte) (vt : word), rdn SEGS m (Z_to_bv 64 (datad + 4 * wpld * i + 4 * ((wd - 1 - j) / 32))) 4 = Some bt /\ bytes_le_to_Z bt = u vt) /\
  store_ok SEGS m (Z_to_bv 64 (datad + 4 * wpld * i + 4 * ((wd - 1 - j) / 32))) 4 = true.
Proof.
  intros m md' i j HW Hi Hj. destruct ccw_s192 as [HP HS].
  destruct (r90w_cell datad i (wd - 1 - j) wpld hd wd ltac:(lia) Hi ltac:(lia) Hwd32) as [B1 B2].
  assert (HPi : (0 <= 4 * wpld * i)%Z) by (apply Z.mul_nonneg_nonneg; lia).
  split; [lia|]. split; [lia|]. split; [lia|]. split; [rewrite <- Z.mul_assoc; apply ccw_m4; exact ALd|]. split; [lia|]. split.
  - destruct (r90w_rd4_blk C A m md' (Z_to_bv 64 datad) kd (datad + 4 * wpld * i + 4 * ((wd - 1 - j) / 32)) CK HW Ld
                ltac:(rewrite u_Z2bv by lia; lia) ltac:(rewrite u_Z2bv by lia; lia) ltac:(rewrite u_Z2bv by lia; lia)) as (bt & vt & R & V).
    exists bt, vt. split; assumption.
  - apply (r90w_sok_blk C A m md' (Z_to_bv 64 datad) kd _ 4 CK HW Ld); rewrite u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia.
Qed.

Lemma ccw_src : forall m md' (j kk : Z), W C A m md' -> (0 <= j < wd)%Z -> (0 <= kk < wpls)%Z ->
  (4096 <= datas + 4 * wpls * (wd - 1 - j))%Z /\ ((datas + 4 * wpls * (wd - 1 - j)) mod 4 = 0)%Z /\
  (datas + 4 * wpls * wd < 2 ^ 47)%Z /\ (datas + 4 * wpls * (wd - 1 - j) + 4 * kk + 4 <= datas + 4 * wpls * wd)%Z /\
  exists (bs : list byte) (v : word), rdn SEGS m (Z_to_bv 64 (datas + 4 * wpls * (wd - 1 - j) + 4 * kk)) 4 = Some bs /\ bytes_le_to_Z bs = u v.
Proof.
  intros m md' j kk HW Hj Hk.
  destruct (r90w_src datas wpls wd (wd - 1 - j) kk ltac:(lia) ltac:(lia) Hk) as [B1 B2].
  assert (HPs : (0 <= 4 * wpls * (wd - 1 - j))%Z) by (apply Z.mul_nonneg_nonneg; lia).
  assert (HPw : (4 * 1 * 1 <= 4 * wpls * wd)%Z) by (apply Z.mul_le_mono_nonneg; [lia | apply Z.mul_le_mono_nonneg_l; lia | lia | lia]).
  pose proof (ccw_alloc_hi m md' (Z_to_bv 64 datas) ks HW Ls ltac:(lia)) as HA. rewrite u_Z2bv in HA by lia.
  split; [lia|]. split; [rewrite <- Z.mul_assoc; apply ccw_m4; exact ALs|]. split; [lia|]. split; [lia|].
  destruct (r90w_rd4_blk C A m md' (Z_to_bv 64 datas) ks (datas + 4 * wpls * (wd - 1 - j) + 4 * kk) CK HW Ls
              ltac:(rewrite u_Z2bv by lia; lia) ltac:(rewrite u_Z2bv by lia; lia) ltac:(rewrite u_Z2bv by lia; lia)) as (bs & v & R & V).
  exists bs, v. split; assumption.
Qed.

(* [comment removed for export] *)
Lemma cc_bits_W : forall (n : nat) (r0 r : bvmap 5 word) (m : word -> option byte) (v : word) (k mm j : Z),
  W C A m md -> POSTM C Ar s mB m -> FTi m ->
  (0 <= j < wd)%Z -> (0 <= k)%Z -> (32 * k + 32 <= hd)%Z -> (0 <= mm)%Z -> (Z.of_nat n = 31 - mm)%Z ->
  regs_agree (fun x => In x [1; 9; 12; 15; 20; 25; 26; 27; 31]%list) r0 r ->
  getr r 24 = v_lw v -> getr r 9 = Z_to_bv 64 mm ->
  getr r 20 = Z_to_bv 64 (datad + 4 * wpld * (hd - 1 - (32 * k + mm))) ->
  getr r 25 = Z_to_bv 64 (datad + 4 * wpld * (hd - 1 - (32 * k + mm))) ->
  getr r 11 = Z_to_bv 64 j -> getr r 6 = Z_to_bv 64 (- (4 * wpld)) -> getr r 7 = Z_to_bv 64 (- (4 * wpld)) ->
  getr r 14 = Z_to_bv 64 (4 * wpld) -> getr r 17 = Z_to_bv 64 32 -> getr r 22 = Z_to_bv 64 0 ->
  getr r 19 = Z_to_bv 64 (- 2 ^ 31) -> getr r 2 = Z_to_bv 64 (s - 192) ->
  (forall m' r', W C A m' md -> POSTM C Ar s mB m' -> FTi m' ->
     regs_agree (fun x => In x [1; 9; 12; 15; 20; 25; 26; 27; 31]%list) r0 r' ->
     getr r' 20 = Z_to_bv 64 (datad + 4 * wpld * (hd - 1 - (32 * k + 32))) ->
     realizes SEGS (mkCfg (mkst r' (Z_to_bv 64 0x97798) m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst r (Z_to_bv 64 0x977f8) m al_rom) md) S.
Proof.
  induction n as [|n IH]; intros r0 r m v k mm j HW PM HF Hj Hk Hk32 Hmm Hn AG R24 R9 R20 R25 R11 R6 R7 R14 R17 R22 R19 R2 K;
    destruct ccw_s192 as [HP HS];
    destruct (ccw_dst m md (hd - 1 - (32 * k + mm)) j HW ltac:(lia) Hj) as (D1 & D2 & D3 & D4 & D5 & (bt & vt & RB & VB) & SOK);
    assert (HPi : (0 <= 4 * wpld * (hd - 1 - (32 * k + mm)))%Z) by (apply Z.mul_nonneg_nonneg; lia);
    destruct (@cc_M fx al_rom (c_lts (v_sllw (v_lw v) (Z_to_bv 64 mm)) (Z_to_bv 64 0)) r m s
                (datad + 4 * wpld * (hd - 1 - (32 * k + mm))) wd j mm v bt vt
                eq_refl HS Hs64 Hj ltac:(lia) ltac:(lia) ltac:(lia) D4 ltac:(lia) (FTi_wd m HF) RB VB SOK R2 R24 R9 R20 R25 R11 R19)
      as (r1 & m1 & RUN1 & MEM1 & Q15 & AG1);
    (eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |]); clear RUN1;
    assert (HM1 : W C A m1 md /\ POSTM C Ar s mB m1 /\ FTi m1) by
      (revert MEM1; destruct (c_lts (v_sllw (v_lw v) (Z_to_bv 64 mm)) (Z_to_bv 64 0)); intros MEM1;
       [destruct MEM1 as [wv ->]; apply FTi_store; first [assumption | lia] | subst m1; auto]);
    destruct HM1 as (HW1 & PM1 & HF1);
    assert (Q9 : getr r1 9 = Z_to_bv 64 mm) by (rewrite (AG1 9%bv) by notin_list; exact R9);
    assert (Q20 : getr r1 20 = Z_to_bv 64 (datad + 4 * wpld * (hd - 1 - (32 * k + mm)))) by (rewrite (AG1 20%bv) by notin_list; exact R20);
    assert (Q25 : getr r1 25 = Z_to_bv 64 (datad + 4 * wpld * (hd - 1 - (32 * k + mm)))) by (rewrite (AG1 25%bv) by notin_list; exact R25);
    assert (Q6 : getr r1 6 = Z_to_bv 64 (- (4 * wpld))) by (rewrite (AG1 6%bv) by notin_list; exact R6);
    assert (Q7 : getr r1 7 = Z_to_bv 64 (- (4 * wpld))) by (rewrite (AG1 7%bv) by notin_list; exact R7);
    assert (Q14 : getr r1 14 = Z_to_bv 64 (4 * wpld)) by (rewrite (AG1 14%bv) by notin_list; exact R14);
    assert (Q17 : getr r1 17 = Z_to_bv 64 32) by (rewrite (AG1 17%bv) by notin_list; exact R17);
    assert (Q22 : getr r1 22 = Z_to_bv 64 0) by (rewrite (AG1 22%bv) by notin_list; exact R22).
  - destruct (@cc_Mx fx al_rom r1 m1 mm (datad + 4 * wpld * (hd - 1 - (32 * k + mm))) wpld ltac:(lia) Hwpld ltac:(lia)
                Q9 Q20 Q25 Q15 Q6 Q7 Q14 Q17 Q22) as (r2 & RUN2 & S20 & AG2).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN2 |].
    apply K; [exact HW1 | exact PM1 | exact HF1 | |].
    + eapply regs_agree_trans; [exact AG|]. eapply regs_agree_trans; [regs_agree_weaken AG1 | regs_agree_weaken AG2].
    + rewrite S20. f_equal. lia.
  - destruct (@cc_Mn fx al_rom r1 m1 mm (datad + 4 * wpld * (hd - 1 - (32 * k + mm))) wpld Hmm ltac:(lia) Hwpld ltac:(lia)
                Q9 Q20 Q25 Q15 Q6 Q7 Q14 Q17 Q22) as (r2 & RUN2 & S9 & S20 & S25 & AG2).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN2 |].
    apply (IH r0 r2 m1 v k (mm + 1)%Z j HW1 PM1 HF1 Hj Hk Hk32 ltac:(lia) ltac:(lia)).
    + eapply regs_agree_trans; [exact AG|]. eapply regs_agree_trans; [regs_agree_weaken AG1 | regs_agree_weaken AG2].
    + rewrite (AG2 24%bv), (AG1 24%bv) by notin_list. exact R24.
    + exact S9.
    + rewrite S20. f_equal. lia.
    + rewrite S25. f_equal. lia.
    + rewrite (AG2 11%bv), (AG1 11%bv) by notin_list. exact R11.
    + rewrite (AG2 6%bv) by notin_list. exact Q6.
    + rewrite (AG2 7%bv) by notin_list. exact Q7.
    + rewrite (AG2 14%bv) by notin_list. exact Q14.
    + rewrite (AG2 17%bv) by notin_list. exact Q17.
    + rewrite (AG2 22%bv) by notin_list. exact Q22.
    + rewrite (AG2 19%bv), (AG1 19%bv) by notin_list. exact R19.
    + rewrite (AG2 2%bv), (AG1 2%bv) by notin_list. exact R2.
    + exact K.
Qed.

(* [comment removed for export] *)
Lemma cc_words_W : forall (n : nat) (r0 r : bvmap 5 word) (m : word -> option byte) (k j : Z),
  W C A m md -> POSTM C Ar s mB m -> FTi m ->
  (0 <= j < wd)%Z -> (0 <= k)%Z -> (Z.of_nat n = hd / 32 - 1 - k)%Z ->
  regs_agree (fun x => In x [1; 9; 12; 15; 20; 23; 24; 25; 26; 27; 31]%list) r0 r ->
  getr r 23 = Z_to_bv 64 k -> getr r 21 = Z_to_bv 64 (datas + 4 * wpls * (wd - 1 - j)) ->
  getr r 20 = Z_to_bv 64 (datad + 4 * wpld * (hd - 1 - 32 * k)) ->
  getr r 11 = Z_to_bv 64 j -> getr r 6 = Z_to_bv 64 (- (4 * wpld)) -> getr r 7 = Z_to_bv 64 (- (4 * wpld)) ->
  getr r 14 = Z_to_bv 64 (4 * wpld) -> getr r 17 = Z_to_bv 64 32 -> getr r 22 = Z_to_bv 64 0 ->
  getr r 19 = Z_to_bv 64 (- 2 ^ 31) -> getr r 2 = Z_to_bv 64 (s - 192) ->
  getr r 28 = Z_to_bv 64 (- (128 * wpld)) -> getr r 8 = Z_to_bv 64 datas -> getr r 16 = Z_to_bv 64 1 ->
  getr r 29 = Z_to_bv 64 0 -> getr r 30 = Z_to_bv 64 (hd / 32) ->
  getr r 5 = Z_to_bv 64 0x4000001 -> getr r 13 = Z_to_bv 64 0x4000000 ->
  (forall m' r', W C A m' md -> POSTM C Ar s mB m' -> FTi m' ->
     regs_agree (fun x => In x [1; 9; 12; 15; 20; 23; 24; 25; 26; 27; 31]%list) r0 r' ->
     getr r' 25 = Z_to_bv 64 hd -> getr r' 20 = Z_to_bv 64 (datad + 4 * wpld * (hd - 1 - 32 * (hd / 32))) ->
     realizes SEGS (mkCfg (mkst r' (Z_to_bv 64 0x978f8) m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst r (Z_to_bv 64 0x977a0) m al_rom) md) S.
Proof.
  induction n as [|n IH]; intros r0 r m k j HW PM HF Hj Hk Hn AG R23 R21 R20 R11 R6 R7 R14 R17 R22 R19 R2 R28 R8 R16 R29 R30 R5 R13 K;
    destruct ccw_s192 as [HP HS];
    pose proof (Z.div_mod hd 32 ltac:(lia)) as DM; pose proof (Z.mod_pos_bound hd 32 ltac:(lia)) as MB;
    assert (Hlk : (32 * k + 32 <= hd)%Z) by lia;
    assert (Hkw : (0 <= k < wpls)%Z) by lia;
    assert (HL1 : (datad + 124 * wpld <= datad + 4 * wpld * (hd - 1 - 32 * k) <= datad + 4 * wpld * hd)%Z)
      by (assert (4 * wpld * 31 <= 4 * wpld * (hd - 1 - 32 * k) <= 4 * wpld * hd)%Z
            by (split; apply Z.mul_le_mono_nonneg_l; lia); lia);
    destruct (ccw_src m md j k HW Hj Hkw) as (L1 & L2 & L3 & L4 & (bs & v & RS & VS));
    assert (TAIL : forall m' r', W C A m' md -> POSTM C Ar s mB m' -> FTi m' ->
              regs_agree (fun x => In x [1; 9; 12; 15; 20; 23; 24; 25; 26; 27; 31]%list) r0 r' ->
              getr r' 23 = Z_to_bv 64 k ->
              getr r' 20 = Z_to_bv 64 (datad + 4 * wpld * (hd - 1 - 32 * (k + 1))) ->
              realizes SEGS (mkCfg (mkst r' (Z_to_bv 64 0x97798) m' al_rom) md) S);
    [ intros m' r' HW' PM' HF' AG' T23 T20;
      assert (AGr : regs_agree (fun x => In x [1; 9; 12; 15; 20; 23; 24; 25; 26; 27; 31]%list) r r')
        by (intros x Hx; rewrite (AG' x Hx), (AG x Hx); reflexivity);
      assert (T30 : getr r' 30 = Z_to_bv 64 (hd / 32)) by (rewrite (AGr 30%bv) by notin_list; exact R30)
    | | intros m' r' HW' PM' HF' AG' T23 T20;
      assert (AGr : regs_agree (fun x => In x [1; 9; 12; 15; 20; 23; 24; 25; 26; 27; 31]%list) r r')
        by (intros x Hx; rewrite (AG' x Hx), (AG x Hx); reflexivity);
      assert (T30 : getr r' 30 = Z_to_bv 64 (hd / 32)) by (rewrite (AGr 30%bv) by notin_list; exact R30)
    | ].
  1: { destruct (@cc_Kx fx al_rom r' m' s k (hd / 32) hd HS Hs64 ltac:(lia) ltac:(lia) ltac:(lia) (FTi_hd m' HF')
                  ltac:(rewrite (AGr 2%bv) by notin_list; exact R2) T23 T30) as (r2 & RUN2 & S25 & AG2).
       eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW')) | exact (mp_lazy _ (w_pure _ _ _ _ HW')) | exact RUN2 |].
       apply K; [exact HW' | exact PM' | exact HF' | | exact S25 | ].
       - eapply regs_agree_trans; [exact AG' | regs_agree_weaken AG2].
       - rewrite (AG2 20%bv) by notin_list. rewrite T20. f_equal. replace (hd / 32)%Z with (k + 1)%Z by lia. reflexivity. }
  2: { destruct (@cc_Kn fx al_rom r' m' k (hd / 32) Hk ltac:(lia) T23 T30) as (r2 & RUN2 & S23 & AG2).
       eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW')) | exact (mp_lazy _ (w_pure _ _ _ _ HW')) | exact RUN2 |].
       apply (IH r0 r2 m' (k + 1)%Z j HW' PM' HF' Hj ltac:(lia) ltac:(lia)).
       - eapply regs_agree_trans; [exact AG' | regs_agree_weaken AG2].
       - exact S23.
       - rewrite (AG2 21%bv), (AGr 21%bv) by notin_list. exact R21.
       - rewrite (AG2 20%bv) by notin_list. exact T20.
       - rewrite (AG2 11%bv), (AGr 11%bv) by notin_list. exact R11.
       - rewrite (AG2 6%bv), (AGr 6%bv) by notin_list. exact R6.
       - rewrite (AG2 7%bv), (AGr 7%bv) by notin_list. exact R7.
       - rewrite (AG2 14%bv), (AGr 14%bv) by notin_list. exact R14.
       - rewrite (AG2 17%bv), (AGr 17%bv) by notin_list. exact R17.
       - rewrite (AG2 22%bv), (AGr 22%bv) by notin_list. exact R22.
       - rewrite (AG2 19%bv), (AGr 19%bv) by notin_list. exact R19.
       - rewrite (AG2 2%bv), (AGr 2%bv) by notin_list. exact R2.
       - rewrite (AG2 28%bv), (AGr 28%bv) by notin_list. exact R28.
       - rewrite (AG2 8%bv), (AGr 8%bv) by notin_list. exact R8.
       - rewrite (AG2 16%bv), (AGr 16%bv) by notin_list. exact R16.
       - rewrite (AG2 29%bv), (AGr 29%bv) by notin_list. exact R29.
       - rewrite (AG2 30%bv) by notin_list. exact T30.
       - rewrite (AG2 5%bv), (AGr 5%bv) by notin_list. exact R5.
       - rewrite (AG2 13%bv), (AGr 13%bv) by notin_list. exact R13.
       - exact K. }
  all: destruct (bv_eq_dec _ (v_lw v) (Z_to_bv 64 0)) as [Z0|NZ].
  all: try (destruct (@cc_Kz fx al_rom r m (datas + 4 * wpls * (wd - 1 - j)) (datad + 4 * wpld * (hd - 1 - 32 * k)) wpld k datas bs v
                  RS VS Z0 ltac:(lia) ltac:(lia) ltac:(lia) L2 ltac:(lia) Hwpld ltac:(lia) R23 R21 R20 R28 R8 R16 R29 R22)
               as (r1 & RUN1 & S20 & AG1);
            eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |];
            apply (TAIL m r1 HW PM HF);
            [ eapply regs_agree_trans; [exact AG | regs_agree_weaken AG1]
            | rewrite (AG1 23%bv) by notin_list; exact R23
            | rewrite S20; f_equal; lia ]).
  all: destruct (@cc_Knz fx al_rom r m (datas + 4 * wpls * (wd - 1 - j)) (datad + 4 * wpld * (hd - 1 - 32 * k)) k datas bs v
                  RS VS NZ ltac:(lia) ltac:(lia) ltac:(lia) L2 ltac:(lia) R23 R21 R20 R8 R16 R5 R13) as (r1 & RUN1 & S24 & S9 & S25 & AG1).
  all: eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  all: apply (cc_bits_W 31 r1 r1 m v k 0 j HW PM HF Hj Hk Hlk ltac:(lia) ltac:(lia) (regs_agree_refl _ _) S24 S9);
    [ rewrite (AG1 20%bv) by notin_list; rewrite R20; f_equal; lia
    | rewrite S25; f_equal; lia
    | rewrite (AG1 11%bv) by notin_list; exact R11
    | rewrite (AG1 6%bv) by notin_list; exact R6
    | rewrite (AG1 7%bv) by notin_list; exact R7
    | rewrite (AG1 14%bv) by notin_list; exact R14
    | rewrite (AG1 17%bv) by notin_list; exact R17
    | rewrite (AG1 22%bv) by notin_list; exact R22
    | rewrite (AG1 19%bv) by notin_list; exact R19
    | rewrite (AG1 2%bv) by notin_list; exact R2
    | intros m' r' HW' PM' HF' AG' T20; apply (TAIL m' r' HW' PM' HF');
      [ eapply regs_agree_trans; [exact AG|]; eapply regs_agree_trans; [regs_agree_weaken AG1 | regs_agree_weaken AG']
      | rewrite (AG' 23%bv), (AG1 23%bv) by notin_list; exact R23
      | rewrite T20; f_equal; lia ] ].
Qed.

Lemma ccx_m4 : forall a b c : Z, (a mod 16 = 0)%Z -> ((a + 4 * b * c) mod 4 = 0)%Z.
Proof.
  intros a b c H. pose proof (Z.div_mod a 16 ltac:(lia)) as E. rewrite H, Z.add_0_r in E.
  rewrite E. replace (16 * (a / 16) + 4 * b * c)%Z with ((4 * (a / 16) + b * c) * 4)%Z by ring.
  apply Z.mod_mul. lia.
Qed.

Lemma ccx_ra2 : forall (L L1 : list reg) (r0 r r1 : bvmap 5 word), incl L1 L ->
  regs_agree (fun x => In x L) r0 r -> regs_agree (fun x => In x L1) r r1 -> regs_agree (fun x => In x L) r0 r1.
Proof.
  unfold regs_agree. intros L L1 r0 r r1 I A0 A1 x Hx.
  rewrite (A1 x); [exact (A0 x Hx) |]. intros H. exact (Hx (I x H)).
Qed.

Ltac ccx_incl := let x := fresh "x" in let H := fresh "H" in intros x H; cbn [In] in H |- *; tauto.
Ltac ccx_ag A B := eapply ccx_ra2; [| exact A | exact B]; ccx_incl.
Ltac ccx_get :=
  first [ assumption
        | match goal with
          | AG : regs_agree _ _ ?r |- getr ?r ?x = _ => rewrite (AG x) by notin_list; ccx_get
          end ].
Ltac ccx_go HW RUN :=
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN |]; clear RUN.

(* [comment removed for export] *)
Lemma cc_tail_W : forall (n : nat) (r0 r : bvmap 5 word) (m : word -> option byte) (i j : Z),
  W C A m md -> POSTM C Ar s mB m -> FTi m ->
  (0 <= j < wd)%Z -> (0 <= i)%Z -> (Z.of_nat n = hd - 1 - i)%Z ->
  regs_agree (fun x => In x [9; 12; 15; 20; 23; 24; 25; 26; 31]%list) r0 r ->
  getr r 24 = Z_to_bv 64 i -> getr r 21 = Z_to_bv 64 (datas + 4 * wpls * (wd - 1 - j)) ->
  getr r 20 = Z_to_bv 64 (datad + 4 * wpld * (hd - 1 - i)) -> getr r 23 = Z_to_bv 64 (datad + 4 * wpld * (hd - 1 - i)) ->
  getr r 11 = Z_to_bv 64 j -> getr r 6 = Z_to_bv 64 (- (4 * wpld)) -> getr r 7 = Z_to_bv 64 (- (4 * wpld)) ->
  getr r 14 = Z_to_bv 64 (4 * wpld) -> getr r 22 = Z_to_bv 64 0 ->
  getr r 19 = Z_to_bv 64 (- 2 ^ 31) -> getr r 2 = Z_to_bv 64 (s - 192) ->
  getr r 8 = Z_to_bv 64 datas -> getr r 16 = Z_to_bv 64 1 ->
  (forall m' r', W C A m' md -> POSTM C Ar s mB m' -> FTi m' ->
     regs_agree (fun x => In x [9; 12; 15; 20; 23; 24; 25; 26; 31]%list) r0 r' ->
     getr r' 25 = Z_to_bv 64 hd ->
     realizes SEGS (mkCfg (mkst r' (Z_to_bv 64 0x976c4) m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst r (Z_to_bv 64 0x97908) m al_rom) md) S.
Proof.
  intros n r0 r m i j HW PM FT Hj Hi Hn RA Q24 Q21 Q20 Q23 Q11 Q6 Q7 Q14 Q22 Q19 Q2 Q8 Q16 K.
  rewrite (RA 21%bv) in Q21 by notin_list. rewrite (RA 11%bv) in Q11 by notin_list.
  rewrite (RA 6%bv) in Q6 by notin_list. rewrite (RA 7%bv) in Q7 by notin_list.
  rewrite (RA 14%bv) in Q14 by notin_list. rewrite (RA 22%bv) in Q22 by notin_list.
  rewrite (RA 19%bv) in Q19 by notin_list. rewrite (RA 2%bv) in Q2 by notin_list.
  rewrite (RA 8%bv) in Q8 by notin_list. rewrite (RA 16%bv) in Q16 by notin_list.
  assert (Uds : u (Z_to_bv 64 datas) = datas) by (apply u_Z2bv; lia).
  assert (Udd : u (Z_to_bv 64 datad) = datad) by (apply u_Z2bv; lia).
  assert (P1 : (0 <= wpld * hd)%Z) by (apply Z.mul_nonneg_nonneg; lia).
  assert (P2 : (0 < wpls * wd)%Z) by (apply Z.mul_pos_pos; lia).
  assert (Hdk : (datad + 4 * wpld * hd < 2 ^ 64)%Z) by lia.
  assert (Hks64 : (datas + ks < 2 ^ 64)%Z).
  { destruct (blk_range C A m md (Z_to_bv 64 datas) ks CK HW Ls ltac:(lia)) as [_ BR]. rewrite Uds in BR.
    pose proof CK as [T1 T2 T3 T4 T5]. pose proof (u64_range (c_sp0 C)). lia. }
  assert (Hsk : (datas + 4 * wpls * wd < 2 ^ 64)%Z) by lia.
  assert (Hs192 : (192 <= s)%Z) by lia.
  assert (STEP : forall r m i, W C A m md -> POSTM C Ar s mB m -> FTi m -> (0 <= i < hd)%Z ->
      regs_agree (fun x => In x [9; 12; 15; 20; 23; 24; 25; 26; 31]%list) r0 r ->
      getr r 24 = Z_to_bv 64 i -> getr r 20 = Z_to_bv 64 (datad + 4 * wpld * (hd - 1 - i)) ->
      getr r 23 = Z_to_bv 64 (datad + 4 * wpld * (hd - 1 - i)) ->
      ((i + 1 < hd)%Z -> forall m' r', W C A m' md -> POSTM C Ar s mB m' -> FTi m' ->
         regs_agree (fun x => In x [9; 12; 15; 20; 23; 24; 25; 26; 31]%list) r0 r' ->
         getr r' 24 = Z_to_bv 64 (i + 1) -> getr r' 20 = Z_to_bv 64 (datad + 4 * wpld * (hd - 1 - (i + 1))) ->
         getr r' 23 = Z_to_bv 64 (datad + 4 * wpld * (hd - 1 - (i + 1))) ->
         realizes SEGS (mkCfg (mkst r' (Z_to_bv 64 0x97908) m' al_rom) md) S) ->
      realizes SEGS (mkCfg (mkst r (Z_to_bv 64 0x97908) m al_rom) md) S).
  { clear r m i HW PM FT Hi Hn RA Q24 Q20 Q23.
    intros r m i HW PM FT Hi RA Q24 Q20 Q23 NXT.
    assert (R2 : getr r 2 = Z_to_bv 64 (s - 192)) by ccx_get.
    assert (R21 : getr r 21 = Z_to_bv 64 (datas + 4 * wpls * (wd - 1 - j))) by ccx_get.
    assert (R11 : getr r 11 = Z_to_bv 64 j) by ccx_get.
    assert (R8 : getr r 8 = Z_to_bv 64 datas) by ccx_get.
    assert (R16 : getr r 16 = Z_to_bv 64 1) by ccx_get.
    assert (R19 : getr r 19 = Z_to_bv 64 (- 2 ^ 31)) by ccx_get.
    pose proof (Z.div_mod i 32 ltac:(lia)) as Di. pose proof (Z.mod_pos_bound i 32 ltac:(lia)) as Mi.
    assert (Hk : (0 <= i / 32 < wpls)%Z) by lia.
    assert (N1 : (0 <= wpls * (wd - 1 - j))%Z) by (apply Z.mul_nonneg_nonneg; lia).
    assert (N2 : (0 <= wpld * (hd - 1 - i))%Z) by (apply Z.mul_nonneg_nonneg; lia).
    assert (N3 : (0 <= wpld * (i + 1))%Z) by (apply Z.mul_nonneg_nonneg; lia).
    destruct (r90w_src datas wpls wd (wd - 1 - j) (i / 32) ltac:(lia) ltac:(lia) Hk) as [SR1 SR2].
    destruct (r90w_cell datad (hd - 1 - i) (wd - 1 - j) wpld hd wd ltac:(lia) ltac:(lia) ltac:(lia) Hwd32) as [DC1 DC2].
    destruct (r90w_rd4_blk C A m md (Z_to_bv 64 datas) ks (datas + 4 * wpls * (wd - 1 - j) + 4 * (i / 32)) CK HW Ls
      ltac:(rewrite Uds; lia) ltac:(rewrite Uds; lia) ltac:(rewrite Uds; lia)) as (bs & v & RS & BS).
    destruct (r90w_rd4_blk C A m md (Z_to_bv 64 datad) kd (datad + 4 * wpld * (hd - 1 - i) + 4 * ((wd - 1 - j) / 32)) CK HW Ld
      ltac:(rewrite Udd; lia) ltac:(rewrite Udd; lia) ltac:(rewrite Udd; lia)) as (bt & vt & RT & BT).
    pose proof (r90w_sok_blk C A m md (Z_to_bv 64 datad) kd (datad + 4 * wpld * (hd - 1 - i) + 4 * ((wd - 1 - j) / 32)) 4 CK HW Ld
      ltac:(rewrite Udd; lia) ltac:(rewrite Udd; lia) ltac:(rewrite Udd; lia)) as SOK.
    edestruct (cc_T al_rom _ r m s (datas + 4 * wpls * (wd - 1 - j)) (datad + 4 * wpld * (hd - 1 - i)) i wd j datas bs v bt vt
      Hs192 Hs64 ltac:(lia) Hj ltac:(lia) ltac:(lia) (ccx_m4 datas wpls (wd - 1 - j) ALs) ltac:(lia) ltac:(lia)
      ltac:(lia) (ccx_m4 datad wpld (hd - 1 - i) ALd) ltac:(lia) RS BS eq_refl RT BT SOK (FTi_wd m FT)
      R2 Q24 R21 Q20 Q23 R11 R8 R16 R19) as (r1 & m1 & RUN & HM & S15 & RA1).
    assert (INV : W C A m1 md /\ POSTM C Ar s mB m1 /\ FTi m1).
    { revert HM. match goal with |- (if ?b then _ else _) -> _ => destruct b end; intros HM.
      - subst m1. exact (conj HW (conj PM FT)).
      - destruct HM as [wv ->]. exact (FTi_store m md _ wv HW PM FT DC1 DC2). }
    destruct INV as (HW1 & PM1 & FT1).
    ccx_go HW RUN.
    assert (RA1' : regs_agree (fun x => In x [9; 12; 15; 20; 23; 24; 25; 26; 31]%list) r0 r1) by ccx_ag RA RA1.
    assert (S2 : getr r1 2 = Z_to_bv 64 (s - 192)) by ccx_get.
    assert (S24 : getr r1 24 = Z_to_bv 64 i) by ccx_get.
    assert (S20 : getr r1 20 = Z_to_bv 64 (datad + 4 * wpld * (hd - 1 - i))) by ccx_get.
    assert (S23 : getr r1 23 = Z_to_bv 64 (datad + 4 * wpld * (hd - 1 - i))) by ccx_get.
    assert (S6 : getr r1 6 = Z_to_bv 64 (- (4 * wpld))) by ccx_get.
    assert (S7 : getr r1 7 = Z_to_bv 64 (- (4 * wpld))) by ccx_get.
    assert (S14 : getr r1 14 = Z_to_bv 64 (4 * wpld)) by ccx_get.
    assert (S22 : getr r1 22 = Z_to_bv 64 0) by ccx_get.
    destruct (Z.ltb_spec (i + 1) hd) as [LT|GE].
    - edestruct (cc_Tn al_rom r1 m1 s i hd (datad + 4 * wpld * (hd - 1 - i)) wpld Hs192 Hs64 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
        (FTi_hd m1 FT1) S2 S24 S20 S23 S15 S6 S7 S14 S22) as (r2 & RUN & T24 & T20 & T23 & T25 & RA2).
      ccx_go HW1 RUN.
      apply (NXT LT m1 r2 HW1 PM1 FT1); [ccx_ag RA1' RA2 | exact T24 | rewrite T20; f_equal; ring | rewrite T23; f_equal; ring].
    - edestruct (cc_Tx al_rom r1 m1 s i hd (datad + 4 * wpld * (hd - 1 - i)) wpld Hs192 Hs64 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
        (FTi_hd m1 FT1) S2 S24 S20 S23 S15 S6 S7 S14 S22) as (r2 & RUN & T25 & RA2).
      ccx_go HW1 RUN.
      apply (K m1 r2 HW1 PM1 FT1); [ccx_ag RA1' RA2 | exact T25]. }
  revert r m i HW PM FT Hi Hn RA Q24 Q20 Q23.
  induction n as [|n IH]; intros r m i HW PM FT Hi Hn RA Q24 Q20 Q23;
    apply (STEP r m i HW PM FT ltac:(lia) RA Q24 Q20 Q23); intros LT.
  - exfalso; lia.
  - intros m' r' HW' PM' FT' RA' Q24' Q20' Q23'.
    exact (IH r' m' (i + 1)%Z HW' PM' FT' ltac:(lia) ltac:(lia) RA' Q24' Q20' Q23').
Qed.

(* [comment removed for export] *)
Lemma cc_rows_W : forall (n : nat) (r0 r : bvmap 5 word) (m : word -> option byte) (j : Z),
  W C A m md -> POSTM C Ar s mB m -> FTi m -> (0 <= j)%Z -> (Z.of_nat n = wd - 1 - j)%Z ->
  regs_agree (fun x => In x [1; 9; 11; 12; 15; 20; 21; 22; 23; 24; 25; 26; 27; 31]%list) r0 r ->
  getr r0 2 = Z_to_bv 64 (s - 192) -> getr r0 10 = Z_to_bv 64 wpld -> getr r0 8 = Z_to_bv 64 datas ->
  getr r0 18 = Z_to_bv 64 wpls -> getr r0 13 = Z_to_bv 64 0x4000000 -> getr r0 5 = Z_to_bv 64 0x4000001 ->
  getr r0 6 = Z_to_bv 64 (- (4 * wpld)) -> getr r0 7 = Z_to_bv 64 (- (4 * wpld)) -> getr r0 14 = Z_to_bv 64 (4 * wpld) ->
  getr r0 28 = Z_to_bv 64 (- (128 * wpld)) -> getr r0 16 = Z_to_bv 64 1 -> getr r0 17 = Z_to_bv 64 32 ->
  getr r0 29 = Z_to_bv 64 0 -> getr r0 30 = Z_to_bv 64 (hd / 32) -> getr r0 19 = Z_to_bv 64 (- 2 ^ 31) ->
  getr r 11 = Z_to_bv 64 j -> getr r 9 = Z_to_bv 64 wd -> getr r 25 = Z_to_bv 64 hd ->
  (forall m' r', W C A m' md -> POSTM C Ar s mB m' -> FTi m' ->
     regs_agree (fun x => In x [1; 9; 11; 12; 15; 20; 21; 22; 23; 24; 25; 26; 27; 31]%list) r0 r' ->
     realizes SEGS (mkCfg (mkst r' (Z_to_bv 64 0x98a2c) m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst r (Z_to_bv 64 0x976d4) m al_rom) md) S.
Proof.
  intros n r0 r m j HW PM FT Hj Hn RA Q2 Q10 Q8 Q18 Q13 Q5 Q6 Q7 Q14 Q28 Q16 Q17 Q29 Q30 Q19 R11 R9 R25 K.
  assert (Uds : u (Z_to_bv 64 datas) = datas) by (apply u_Z2bv; lia).
  assert (P1 : (0 <= wpld * hd)%Z) by (apply Z.mul_nonneg_nonneg; lia).
  assert (P2 : (0 < wpls * wd)%Z) by (apply Z.mul_pos_pos; lia).
  assert (Hdk : (datad + 4 * wpld * hd < 2 ^ 64)%Z) by lia.
  assert (Hks64 : (datas + ks < 2 ^ 64)%Z).
  { destruct (blk_range C A m md (Z_to_bv 64 datas) ks CK HW Ls ltac:(lia)) as [_ BR]. rewrite Uds in BR.
    pose proof CK as [T1 T2 T3 T4 T5]. pose proof (u64_range (c_sp0 C)). lia. }
  assert (Hsk : (datas + 4 * wpls * wd < 2 ^ 64)%Z) by lia.
  assert (Hs192 : (192 <= s)%Z) by lia.
  pose proof (Z.div_mod hd 32 ltac:(lia)) as Dh. pose proof (Z.mod_pos_bound hd 32 ltac:(lia)) as Mh.
  assert (ROW : forall r m j, W C A m md -> POSTM C Ar s mB m -> FTi m -> (0 <= j < wd)%Z ->
      regs_agree (fun x => In x [1; 9; 11; 12; 15; 20; 21; 22; 23; 24; 25; 26; 27; 31]%list) r0 r ->
      getr r 11 = Z_to_bv 64 j -> getr r 9 = Z_to_bv 64 wd -> getr r 25 = Z_to_bv 64 hd ->
      (forall m' r', W C A m' md -> POSTM C Ar s mB m' -> FTi m' ->
         regs_agree (fun x => In x [1; 9; 11; 12; 15; 20; 21; 22; 23; 24; 25; 26; 27; 31]%list) r0 r' ->
         getr r' 11 = Z_to_bv 64 j -> getr r' 25 = Z_to_bv 64 hd ->
         realizes SEGS (mkCfg (mkst r' (Z_to_bv 64 0x976c4) m' al_rom) md) S) ->
      realizes SEGS (mkCfg (mkst r (Z_to_bv 64 0x976d4) m al_rom) md) S).
  { clear r m j HW PM FT Hj Hn RA R11 R9 R25.
    intros r m j HW PM FT Hj RA R11 R9 R25 E.
    assert (R2 : getr r 2 = Z_to_bv 64 (s - 192)) by ccx_get.
    assert (R18 : getr r 18 = Z_to_bv 64 wpls) by ccx_get.
    assert (R10 : getr r 10 = Z_to_bv 64 wpld) by ccx_get.
    assert (R8 : getr r 8 = Z_to_bv 64 datas) by ccx_get.
    assert (R16 : getr r 16 = Z_to_bv 64 1) by ccx_get.
    assert (R17 : getr r 17 = Z_to_bv 64 32) by ccx_get.
    assert (MID : forall m' r', W C A m' md -> POSTM C Ar s mB m' -> FTi m' ->
        regs_agree (fun x => In x [1; 9; 11; 12; 15; 20; 21; 22; 23; 24; 25; 26; 27; 31]%list) r0 r' ->
        getr r' 11 = Z_to_bv 64 j -> getr r' 25 = Z_to_bv 64 hd -> getr r' 22 = Z_to_bv 64 0 ->
        getr r' 20 = Z_to_bv 64 (datad + 4 * wpld * (hd - 1 - 32 * (hd / 32))) ->
        getr r' 21 = Z_to_bv 64 (datas + 4 * wpls * (wd - 1 - j)) ->
        realizes SEGS (mkCfg (mkst r' (Z_to_bv 64 0x978f8) m' al_rom) md) S).
    { intros m' r' HW' PM' FT' RA' S11 S25 S22 S20 S21.
      assert (S2 : getr r' 2 = Z_to_bv 64 (s - 192)) by ccx_get.
      destruct (Z_le_gt_dec hd (32 * (hd / 32))) as [LE|GT].
      - edestruct (cc_T0e al_rom r' m' s hd (32 * (hd / 32)) Hs192 Hs64 ltac:(lia) ltac:(lia) LE (FTi_a7 m' FT') S2 S25)
          as (r3 & RUN & RA3).
        ccx_go HW' RUN.
        apply (E m' r3 HW' PM' FT'); [ccx_ag RA' RA3 | ccx_get | ccx_get].
      - edestruct (cc_T0s al_rom r' m' s hd (32 * (hd / 32)) (datad + 4 * wpld * (hd - 1 - 32 * (hd / 32))) Hs192 Hs64
          ltac:(lia) ltac:(lia) ltac:(lia) (FTi_a7 m' FT') S2 S25 S20) as (r3 & RUN & T23 & T24 & RA3).
        ccx_go HW' RUN.
        assert (RA3' : regs_agree (fun x => In x [1; 9; 11; 12; 15; 20; 21; 22; 23; 24; 25; 26; 27; 31]%list) r0 r3)
          by ccx_ag RA' RA3.
        apply (cc_tail_W (Z.to_nat (hd - 1 - 32 * (hd / 32))) r3 r3 m' (32 * (hd / 32)) j HW' PM' FT' Hj ltac:(lia) ltac:(lia)
          (fun _ _ => eq_refl) T24); [ccx_get .. |].
        intros m'' r'' HW'' PM'' FT'' RA'' T25.
        apply (E m'' r'' HW'' PM'' FT''); [ccx_ag RA3' RA'' | ccx_get | exact T25]. }
    destruct (Z_le_gt_dec 32 hd) as [GE|LT].
    - edestruct (cc_Jw al_rom r m s wd hd datas wpls datad wpld j Hs192 Hs64 Hj ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hszd Hszs
        ltac:(lia) Hdk ltac:(lia) Hsk (FTi_dd m FT) (FTi_one m FT) (FTi_hd8 m FT) R2 R11 R9 R25 R18 R10 R8 R16 R17)
        as (r1 & RUN & J20 & J21 & J23 & J22 & RA1).
      ccx_go HW RUN.
      assert (RA1' : regs_agree (fun x => In x [1; 9; 11; 12; 15; 20; 21; 22; 23; 24; 25; 26; 27; 31]%list) r0 r1)
        by ccx_ag RA RA1.
      apply (cc_words_W (Z.to_nat (hd / 32 - 1)) r1 r1 m 0 j HW PM FT Hj ltac:(lia) ltac:(lia) (fun _ _ => eq_refl) J23 J21);
        [rewrite J20; f_equal; ring | ccx_get .. |].
      intros m' r' HW' PM' FT' RA'' W25 W20.
      apply (MID m' r' HW' PM' FT'); [ccx_ag RA1' RA'' | ccx_get | exact W25 | ccx_get | exact W20 | ccx_get].
    - edestruct (cc_Jt al_rom r m s wd hd datas wpls datad wpld j Hs192 Hs64 Hj ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hszd Hszs
        ltac:(lia) Hdk ltac:(lia) Hsk (FTi_dd m FT) (FTi_one m FT) (FTi_hd8 m FT) R2 R11 R9 R25 R18 R10 R8 R16 R17)
        as (r1 & RUN & J20 & J21 & J22 & RA1).
      ccx_go HW RUN.
      assert (Q0 : (hd / 32 = 0)%Z) by lia.
      apply (MID m r1 HW PM FT); [ccx_ag RA RA1 | ccx_get | ccx_get | exact J22 | rewrite J20, Q0; f_equal; ring | exact J21]. }
  revert r m j HW PM FT Hj Hn RA R11 R9 R25.
  induction n as [|n IH]; intros r m j HW PM FT Hj Hn RA R11 R9 R25;
    apply (ROW r m j HW PM FT ltac:(lia) RA R11 R9 R25); intros m' r' HW' PM' FT' RA' S11 S25;
    assert (S2 : getr r' 2 = Z_to_bv 64 (s - 192)) by ccx_get.
  - edestruct (cc_Rx al_rom r' m' s j wd Hs192 Hs64 Hj ltac:(lia) ltac:(lia) (FTi_wd m' FT') S2 S11) as (r2 & RUN & RA2).
    ccx_go HW' RUN.
    apply (K m' r2 HW' PM' FT'). ccx_ag RA' RA2.
  - edestruct (cc_Rn al_rom r' m' s j wd Hs192 Hs64 Hj ltac:(lia) (FTi_wd m' FT') S2 S11) as (r2 & RUN & N11 & N9 & RA2).
    ccx_go HW' RUN.
    apply (IH r2 m' (j + 1)%Z HW' PM' FT' ltac:(lia) ltac:(lia)); [ccx_ag RA' RA2 | exact N11 | exact N9 | ccx_get].
Qed.

(* [comment removed for export] *)
Lemma cc_arm_W : forall (r : bvmap 5 word),
  W C A mB md ->
  getr r 2 = Z_to_bv 64 (s - 192) -> getr r 10 = Z_to_bv 64 wpld -> getr r 8 = Z_to_bv 64 datas -> getr r 18 = Z_to_bv 64 wpls ->
  (forall m' r', W C A m' md -> POSTM C Ar s mB m' -> FTc m' ->
     regs_agree (fun x => In x [1; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%list) r r' ->
     realizes SEGS (mkCfg (mkst r' (0x98a2c : word) m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst r (0x9764c : word) mB al_rom) md) S.
Proof using CK SUB Ld Hkd Ldr Ld0 Ls Hks Hdd Hds Hwd Hhd Hwpld Hwpls Hwd32 Hhd32 Hs Hs64 Hbelow RWD RHD RDD ALd ALs Hd4k Hs4k Hszs Hstk Htop
  Hszd Hdw ks kd P16 PINS.
  intros r HW R2 R10 R8 R18 K. destruct ccw_s192 as [HP HS].
  destruct (SLW_W HW) as (SOK & HW1 & PM1 & HF1).
  replace (0x9764c : word) with (Z_to_bv 64 0x9764c) by (apply bv_eq; reflexivity).
  destruct (@cc_S fx al_rom r mB s wd hd wpld datad datas HS Hs64 ltac:(lia) ltac:(lia) Hwpld ltac:(lia) ltac:(lia)
              RWD RHD RDD SOK R2 R10 R8)
    as (r1 & RUN1 & S9 & S11 & S25 & S13 & S5 & S6 & S7 & S14 & S28 & S16 & S17 & S29 & S30 & S19 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  apply (cc_rows_W (Z.to_nat (wd - 1)) r1 r1 (SLW mB s hd) 0 HW1 PM1 HF1 ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia)
           (regs_agree_refl _ _));
    [ rewrite (AG1 2%bv) by notin_list; exact R2
    | rewrite (AG1 10%bv) by notin_list; exact R10
    | rewrite (AG1 8%bv) by notin_list; exact R8
    | rewrite (AG1 18%bv) by notin_list; exact R18
    | exact S13 | exact S5 | exact S6 | exact S7 | exact S14 | exact S28 | exact S16 | exact S17 | exact S29 | exact S30 | exact S19
    | exact S11 | exact S9 | exact S25 | ].
  intros m' r' HW' PM' HF' AG'.
  replace (Z_to_bv 64 0x98a2c) with (0x98a2c : word) by (apply bv_eq; reflexivity).
  apply K; [exact HW' | exact PM' | apply FTi_FTc; exact HF' |].
  eapply regs_agree_trans; [regs_agree_weaken AG1 | regs_agree_weaken AG'].
Qed.

End CCW.
End R90W.
