(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic PFLib LeptDefs LeptStructs LeptArith LeptArith2 LeptRoom LeptExecW.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptBase V23MemcpyBase V23Memcpy V23LeptRotTB.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section RotTBW.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V23Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Ltac in_kept := unfold callee_kept; cbn [In]; repeat (first [left; reflexivity | right]).

(* [comment removed for export] *)
Lemma tbw_rdn_blk : forall C A m md (p : word) (k a : Z) (n : nat), Cok C -> W C A m md -> live A p = Some k ->
  (u p <= a)%Z -> (a + Z.of_nat n <= u p + k)%Z -> (u p + k < 2 ^ 64)%Z ->
  exists bs, rdn SEGS m (Z_to_bv 64 a) n = Some bs /\ length bs = n.
Proof.
  intros C A m md p k a n CK HW L H1 H2 H3. pose proof (u64_range p).
  apply rdn_defined; [lia | lia |]. intros i Hi.
  apply (blk_byte C A m md p k (Z_to_bv 64 (a + i)) CK HW L). rewrite u_Z2bv by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma tbw_sok_blk : forall C A m md (p : word) (k a : Z) (n : nat), Cok C -> W C A m md -> live A p = Some k ->
  (u p <= a)%Z -> (a + Z.of_nat n <= u p + k)%Z -> (u p + k < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 a) n = true.
Proof.
  intros C A m md p k a n CK HW L H1 H2 H3. pose proof (u64_range p).
  apply (exW_sok_blk SEGS C A m md (u p) k a n p16_segs CK HW); [rewrite zbv_self; exact L | lia | lia | lia | lia].
Qed.

(* [comment removed for export] *)
Lemma tbw_apart : forall C A m md (p q : word) (n k : Z), Cok C -> W C A m md ->
  live A p = Some n -> live A q = Some k -> p <> q -> (0 <= n)%Z -> (0 <= k)%Z ->
  (u p + n <= u q \/ u q + k <= u p)%Z.
Proof.
  intros C A m md p q n k CK HW Lp Lq NE Hn Hk.
  destruct (ai_live_disjoint A m (m_vmmaps md) p n q k (w_inv _ _ _ _ HW) Lp Lq NE) as [X|X];
    [left; pose proof (round16_ge n Hn); lia | right; pose proof (round16_ge k Hk); lia].
Qed.

Ltac tbl_in := cbn [In]; repeat (first [left; reflexivity | right]).

Lemma tbl_regs : forall r r1 r2 r3 r4 r5 r6 r7 : bvmap 5 word,
  regs_agree (fun x => In x [1; 10; 11; 12; 21; 22; 27]%list) r r1 -> keeps r1 r2 ->
  regs_agree (fun x => In x [1; 10; 11; 12]%list) r2 r3 -> keeps r3 r4 ->
  regs_agree (fun x => In x [1; 10; 11; 12]%list) r4 r5 -> keeps r5 r6 ->
  regs_agree (fun x => In x [10; 23]%list) r6 r7 ->
  forall x, In x [2; 3; 4; 8; 9; 18; 19; 20; 24; 25; 26]%list -> getr r7 x = getr r x.
Proof.
  intros r r1 r2 r3 r4 r5 r6 r7 A1 K2 A3 K4 A5 K6 A7 x Hx. cbn [In] in Hx.
  repeat destruct Hx as [<- | Hx]; try contradiction;
    rewrite (A7 _), (K6 _), (A5 _), (K4 _), (A3 _), (K2 _), (A1 _); try reflexivity;
    first [solve [in_kept] | solve [cbn [In]; intuition discriminate]].
Qed.

(* [comment removed for export] *)
Lemma tb_loop_W : forall (n : nat) C Ar A m1 md (s data wpl h b kd : Z) (S : TSet) (r0 r : bvmap 5 word) (m : word -> option byte) (i : Z),
  Cok C -> W C A m md -> sub_live Ar A ->
  live A (Z_to_bv 64 data) = Some kd -> (4 * wpl * h <= kd)%Z -> live Ar (Z_to_bv 64 data) = None -> live (c_A0 C) (Z_to_bv 64 data) = None ->
  live A (Z_to_bv 64 b) = Some (wpl * 4)%Z -> live Ar (Z_to_bv 64 b) = None -> live (c_A0 C) (Z_to_bv 64 b) = None ->
  Z_to_bv 64 b <> Z_to_bv 64 data -> (1 <= b < 2 ^ 64)%Z -> (b mod 4 = 0)%Z ->
  (1 <= data)%Z -> (data + 4 * wpl * h < 2 ^ 63)%Z -> (data mod 4 = 0)%Z ->
  (1 <= wpl)%Z -> (1 <= h)%Z -> (4 * wpl * h <= 2 ^ 26)%Z -> (0 <= i)%Z -> (Z.of_nat n = h / 2 - i)%Z ->
  POSTM C Ar s m1 m ->
  (forall a : word, ~ (data <= u a < data + 4 * wpl * h)%Z -> ~ (b <= u a < b + 4 * wpl)%Z -> m a = m1 a) ->
  (forall x, In x [2; 3; 4; 8; 9; 18; 19; 20; 24; 25; 26]%list -> getr r x = getr r0 x) ->
  getr r 9 = Z_to_bv 64 data -> getr r 18 = Z_to_bv 64 wpl -> getr r 19 = Z_to_bv 64 b -> getr r 20 = Z_to_bv 64 (4 * wpl) ->
  getr r 23 = Z_to_bv 64 i -> getr r 24 = Z_to_bv 64 0 -> getr r 25 = Z_to_bv 64 (h / 2) -> getr r 26 = Z_to_bv 64 1 ->
  getr r 10 = Z_to_bv 64 (h - 1 - i) ->
  (forall m' r', W C A m' md -> POSTM C Ar s m1 m' ->
     (forall a : word, ~ (data <= u a < data + 4 * wpl * h)%Z -> ~ (b <= u a < b + 4 * wpl)%Z -> m' a = m1 a) ->
     (forall x, In x [2; 3; 4; 8; 9; 18; 19; 20; 24; 25; 26]%list -> getr r' x = getr r0 x) ->
     getr r' 1 = Z_to_bv 64 0x99a08 -> getr r' 10 = Z_to_bv 64 b ->
     realizes SEGS (mkCfg (mkst r' (Z_to_bv 64 0x10e818) m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst r (Z_to_bv 64 0x998e0) m al_rom) md) S.
Proof.
  induction n as [|n IH]; intros C Ar A m1 md s data wpl h b kd S r0 r m i CK HW SUB Ld Hkd Lrd L0d Lb Lrb L0b NE Hb Hbm
    Hd Hd2 Hdm Hw Hh Hwh Hi Hn PM FR RG R9 R18 R19 R20 R23 R24 R25 R26 R10 K;
    assert (H2h : (2 * (h / 2) <= h)%Z) by (apply Z.mul_div_le; lia);
    replace (Z_to_bv 64 0x998e0) with (0x998e0 : word) by (apply bv_eq; reflexivity).
  - assert (Ei : i = (h / 2)%Z) by lia. rewrite Ei in R23.
    destruct (tb_X al_rom r m h b R19 R23 R25) as (r1 & RUN1 & X1 & X10 & AG1).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
    replace (0x10e818 : word) with (Z_to_bv 64 0x10e818) by (apply bv_eq; reflexivity).
    apply K; [exact HW | exact PM | exact FR | | exact X1 | exact X10].
    intros x Hx. rewrite <- (RG x Hx). cbn [In] in Hx.
    repeat destruct Hx as [<- | Hx]; try contradiction; apply AG1; cbn [In]; intuition discriminate.
  - assert (Hih : (2 * i + 2 <= h)%Z) by lia.
    pose proof CK as [T1 T2 T3 T4 T5]. unfold LSTK in T1.
    assert (Hpos : (4 <= 4 * wpl * h)%Z) by nia.
    assert (Hh31 : (h <= 2 ^ 24)%Z) by nia.
    assert (Rr : (0 <= 4 * wpl * i)%Z /\ (4 * wpl * i + 4 * wpl <= 4 * wpl * (h - 1 - i))%Z /\
                 (4 * wpl * (h - 1 - i) + 4 * wpl <= 4 * wpl * h)%Z /\ (0 <= 4 * wpl * (h - 1 - i))%Z) by (repeat split; nia).
    destruct Rr as (Ra & Rb & Rc & Re).
    destruct (blk_range C A m md (Z_to_bv 64 data) kd CK HW Ld ltac:(lia)) as [Gd TOPd]. rewrite u_Z2bv in Gd, TOPd by lia.
    destruct (blk_range C A m md (Z_to_bv 64 b) (wpl * 4) CK HW Lb ltac:(lia)) as [Gb TOPb]. rewrite u_Z2bv in Gb, TOPb by lia.
    pose proof (tbw_apart C A m md (Z_to_bv 64 b) (Z_to_bv 64 data) (wpl * 4) kd CK HW Lb Ld NE ltac:(lia) ltac:(lia)) as AP.
    rewrite !u_Z2bv in AP by lia.
    destruct (tb_H al_rom r m h wpl data b i ltac:(lia) Hw Hwh Hd Hd2 Hdm Hb Hbm Hi Hih R9 R18 R19 R20 R23 R24 R25 R26 R10)
      as (r1 & RUN1 & Q1 & Q10 & Q11 & Q12 & Q21 & Q22 & Q27 & AG1).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
    destruct (tbw_rdn_blk C A m md (Z_to_bv 64 data) kd (data + 4 * wpl * i) (Z.to_nat (4 * wpl)) CK HW Ld) as (bs1 & Rb1 & Lb1);
      [rewrite u_Z2bv by lia; rewrite ?Z2Nat.id by lia; lia .. |].
    assert (SO1 : store_ok SEGS m (Z_to_bv 64 b) (length bs1) = true).
    { apply (tbw_sok_blk C A m md (Z_to_bv 64 b) (wpl * 4) b (length bs1) CK HW Lb); rewrite u_Z2bv by lia; rewrite ?Lb1, ?Z2Nat.id by lia; lia. }
    assert (HO1 : mcH m (Z_to_bv 64 b) (Z_to_bv 64 (data + 4 * wpl * i)) (4 * wpl) bs1).
    { constructor; rewrite ?u_Z2bv by lia; [lia | exact Lb1 | rewrite Lb1; exact Rb1 | exact SO1 | lia | lia | lia]. }
    destruct (ref_memcpy m _ _ (4 * wpl) bs1 al_rom HO1 r1 (Z_to_bv 64 0x9996c) ltac:(red; apply bv_eq; reflexivity) Q1 Q10 Q11 Q12)
      as (r2 & RUN2 & KP2).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN2 |].
    destruct (WP_blk C Ar A m1 m md (Z_to_bv 64 b) (Z_to_bv 64 b) (wpl * 4) bs1 s CK (conj HW PM) Lb Lrb L0b SUB) as [HW1 PM1];
      [rewrite !u_Z2bv by lia; lia | rewrite Lb1, Z2Nat.id, !u_Z2bv by lia; lia |].
    set (M1 := wbytes m (Z_to_bv 64 b) bs1) in *.
    replace (Z_to_bv 64 0x9996c) with (0x9996c : word) by (apply bv_eq; reflexivity).
    destruct (tb_L1 al_rom r2 M1) as (r3 & RUN3 & P1 & P10 & P11 & P12 & AG3).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN3 |].
    assert (E10 : getr r3 10 = Z_to_bv 64 (data + 4 * wpl * i)) by (rewrite P10, (KP2 21) by in_kept; exact Q21).
    assert (E11 : getr r3 11 = Z_to_bv 64 (data + 4 * wpl * (h - 1 - i))) by (rewrite P11, (KP2 22) by in_kept; exact Q22).
    assert (E12 : getr r3 12 = Z_to_bv 64 (4 * wpl)).
    { rewrite P12, (KP2 20) by in_kept. rewrite (AG1 20) by (cbn [In]; intuition discriminate). exact R20. }
    destruct (tbw_rdn_blk C A M1 md (Z_to_bv 64 data) kd (data + 4 * wpl * (h - 1 - i)) (Z.to_nat (4 * wpl)) CK HW1 Ld)
      as (bs2 & Rb2 & Lb2); [rewrite u_Z2bv by lia; rewrite ?Z2Nat.id by lia; lia .. |].
    assert (SO2 : store_ok SEGS M1 (Z_to_bv 64 (data + 4 * wpl * i)) (length bs2) = true).
    { apply (tbw_sok_blk C A M1 md (Z_to_bv 64 data) kd (data + 4 * wpl * i) (length bs2) CK HW1 Ld);
        rewrite u_Z2bv by lia; rewrite ?Lb2, ?Z2Nat.id by lia; lia. }
    assert (HO2 : mcH M1 (Z_to_bv 64 (data + 4 * wpl * i)) (Z_to_bv 64 (data + 4 * wpl * (h - 1 - i))) (4 * wpl) bs2).
    { constructor; rewrite ?u_Z2bv by lia; [lia | exact Lb2 | rewrite Lb2; exact Rb2 | exact SO2 | lia | lia | lia]. }
    destruct (ref_memcpy M1 _ _ (4 * wpl) bs2 al_rom HO2 r3 (Z_to_bv 64 0x9997c) ltac:(red; apply bv_eq; reflexivity) P1 E10 E11 E12)
      as (r4 & RUN4 & KP4).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN4 |].
    destruct (WP_blk C Ar A m1 M1 md (Z_to_bv 64 data) (Z_to_bv 64 (data + 4 * wpl * i)) kd bs2 s CK (conj HW1 PM1) Ld Lrd L0d SUB)
      as [HW2 PM2]; [rewrite !u_Z2bv by lia; lia | rewrite Lb2, Z2Nat.id, !u_Z2bv by lia; lia |].
    set (M2 := wbytes M1 (Z_to_bv 64 (data + 4 * wpl * i)) bs2) in *.
    replace (Z_to_bv 64 0x9997c) with (0x9997c : word) by (apply bv_eq; reflexivity).
    destruct (tb_L2 al_rom r4 M2) as (r5 & RUN5 & V1 & V10 & V11 & V12 & AG5).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact RUN5 |].
    assert (F10 : getr r5 10 = Z_to_bv 64 (data + 4 * wpl * (h - 1 - i))).
    { rewrite V10, (KP4 22) by in_kept. rewrite (AG3 22) by (cbn [In]; intuition discriminate). rewrite (KP2 22) by in_kept. exact Q22. }
    assert (F11 : getr r5 11 = Z_to_bv 64 b).
    { rewrite V11, (KP4 19) by in_kept. rewrite (AG3 19) by (cbn [In]; intuition discriminate). rewrite (KP2 19) by in_kept.
      rewrite (AG1 19) by (cbn [In]; intuition discriminate). exact R19. }
    assert (F12 : getr r5 12 = Z_to_bv 64 (4 * wpl)).
    { rewrite V12, (KP4 20) by in_kept. rewrite (AG3 20) by (cbn [In]; intuition discriminate). rewrite (KP2 20) by in_kept.
      rewrite (AG1 20) by (cbn [In]; intuition discriminate). exact R20. }
    destruct (tbw_rdn_blk C A M2 md (Z_to_bv 64 b) (wpl * 4) b (Z.to_nat (4 * wpl)) CK HW2 Lb) as (bs3 & Rb3 & Lb3);
      [rewrite u_Z2bv by lia; rewrite ?Z2Nat.id by lia; lia .. |].
    assert (SO3 : store_ok SEGS M2 (Z_to_bv 64 (data + 4 * wpl * (h - 1 - i))) (length bs3) = true).
    { apply (tbw_sok_blk C A M2 md (Z_to_bv 64 data) kd (data + 4 * wpl * (h - 1 - i)) (length bs3) CK HW2 Ld);
        rewrite u_Z2bv by lia; rewrite ?Lb3, ?Z2Nat.id by lia; lia. }
    assert (HO3 : mcH M2 (Z_to_bv 64 (data + 4 * wpl * (h - 1 - i))) (Z_to_bv 64 b) (4 * wpl) bs3).
    { constructor; rewrite ?u_Z2bv by lia; [lia | exact Lb3 | rewrite Lb3; exact Rb3 | exact SO3 | lia | lia | lia]. }
    destruct (ref_memcpy M2 _ _ (4 * wpl) bs3 al_rom HO3 r5 (Z_to_bv 64 0x9998c) ltac:(red; apply bv_eq; reflexivity) V1 F10 F11 F12)
      as (r6 & RUN6 & KP6).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact RUN6 |].
    destruct (WP_blk C Ar A m1 M2 md (Z_to_bv 64 data) (Z_to_bv 64 (data + 4 * wpl * (h - 1 - i))) kd bs3 s CK (conj HW2 PM2) Ld Lrd L0d SUB)
      as [HW3 PM3]; [rewrite !u_Z2bv by lia; lia | rewrite Lb3, Z2Nat.id, !u_Z2bv by lia; lia |].
    set (M3 := wbytes M2 (Z_to_bv 64 (data + 4 * wpl * (h - 1 - i))) bs3) in *.
    replace (Z_to_bv 64 0x9998c) with (0x9998c : word) by (apply bv_eq; reflexivity).
    assert (G27 : getr r6 27 = Z_to_bv 64 (h - 1 - i)).
    { rewrite (KP6 27) by in_kept. rewrite (AG5 27) by (cbn [In]; intuition discriminate). rewrite (KP4 27) by in_kept.
      rewrite (AG3 27) by (cbn [In]; intuition discriminate). rewrite (KP2 27) by in_kept. exact Q27. }
    assert (G23 : getr r6 23 = Z_to_bv 64 i).
    { rewrite (KP6 23) by in_kept. rewrite (AG5 23) by (cbn [In]; intuition discriminate). rewrite (KP4 23) by in_kept.
      rewrite (AG3 23) by (cbn [In]; intuition discriminate). rewrite (KP2 23) by in_kept.
      rewrite (AG1 23) by (cbn [In]; intuition discriminate). exact R23. }
    destruct (tb_L3 al_rom r6 M3 h i Hi Hih ltac:(lia) G27 G23) as (r7 & RUN7 & N10 & N23 & AG7).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW3)) | exact (mp_lazy _ (w_pure _ _ _ _ HW3)) | exact RUN7 |].
    replace (0x998e0 : word) with (Z_to_bv 64 0x998e0) by (apply bv_eq; reflexivity).
    pose proof (tbl_regs r r1 r2 r3 r4 r5 r6 r7 AG1 KP2 AG3 KP4 AG5 KP6 AG7) as GR7.
    assert (S9 : getr r7 9 = Z_to_bv 64 data) by (rewrite (GR7 9) by tbl_in; exact R9).
    assert (S18 : getr r7 18 = Z_to_bv 64 wpl) by (rewrite (GR7 18) by tbl_in; exact R18).
    assert (S19 : getr r7 19 = Z_to_bv 64 b) by (rewrite (GR7 19) by tbl_in; exact R19).
    assert (S20 : getr r7 20 = Z_to_bv 64 (4 * wpl)) by (rewrite (GR7 20) by tbl_in; exact R20).
    assert (S24 : getr r7 24 = Z_to_bv 64 0) by (rewrite (GR7 24) by tbl_in; exact R24).
    assert (S25 : getr r7 25 = Z_to_bv 64 (h / 2)) by (rewrite (GR7 25) by tbl_in; exact R25).
    assert (S26 : getr r7 26 = Z_to_bv 64 1) by (rewrite (GR7 26) by tbl_in; exact R26).
    assert (GR0 : forall x, In x [2; 3; 4; 8; 9; 18; 19; 20; 24; 25; 26]%list -> getr r7 x = getr r0 x)
      by (intros x Hx; rewrite (GR7 x Hx); exact (RG x Hx)).
    assert (FR3 : forall a : word, ~ (data <= u a < data + 4 * wpl * h)%Z -> ~ (b <= u a < b + 4 * wpl)%Z -> M3 a = m1 a).
    { intros a Ha1 Ha2. unfold M3, M2, M1.
      rewrite (wbytes_outside bs3) by (rewrite Lb3, Z2Nat.id, u_Z2bv by lia; lia).
      rewrite (wbytes_outside bs2) by (rewrite Lb2, Z2Nat.id, u_Z2bv by lia; lia).
      rewrite (wbytes_outside bs1) by (rewrite Lb1, Z2Nat.id, u_Z2bv by lia; lia).
      apply FR; assumption. }
    apply (IH C Ar A m1 md s data wpl h b kd S r0 r7 M3 (i + 1)%Z CK HW3 SUB Ld Hkd Lrd L0d Lb Lrb L0b NE Hb Hbm Hd Hd2 Hdm Hw Hh Hwh
             ltac:(lia) ltac:(lia) PM3 FR3 GR0 S9 S18 S19 S20 N23 S24 S25 S26 N10 K).
Qed.

Lemma tbw_al16 : forall C A m md (p : Z) (k : Z), W C A m md -> live A (Z_to_bv 64 p) = Some k -> (0 <= p < 2 ^ 64)%Z -> (p mod 16 = 0)%Z.
Proof.
  intros C A m md p k HW L Hp.
  destruct (ai_live_hull A m (m_vmmaps md) _ k (w_inv _ _ _ _ HW) L) as (_ & X & _). rewrite u_Z2bv in X by lia. exact X.
Qed.

Definition TBC (s : Z) (ret : word) (regs : bvmap 5 word) : list (Z * word) :=
  [(s - 8, ret); (s - 16, getr regs 8); (s - 24, getr regs 9); (s - 32, getr regs 18); (s - 40, getr regs 19); (s - 48, getr regs 20);
   (s - 56, getr regs 21); (s - 64, getr regs 22); (s - 72, getr regs 23); (s - 80, getr regs 24); (s - 88, getr regs 25); (s - 96, getr regs 26);
   (s - 104, getr regs 27)]%Z.

Ltac tbwA_sc := rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia.

Ltac tbwA_rd :=
  repeat first [ rewrite rdn_wbytes_hit8 by tbwA_sc | rewrite rdn_wbytes_hit4 by tbwA_sc | rewrite rdn_wbytes_out by tbwA_sc ];
  reflexivity.

Ltac tbwA_out a := pose proof (u64_range a); repeat (rewrite wbytes_outside by tbwA_sc); reflexivity.

Lemma MTB_A_out : forall m s pix v ret regs (a : word), (160 <= s < 2 ^ 64)%Z -> ~ (s - 160 <= u a < s)%Z ->
  MTB_A m s pix v ret regs a = m a.
Proof.
  intros m s pix v ret regs a Hs Ha. unfold MTB_A, PCFTB, DIMTB, FRTB. tbwA_out a.
Qed.

Lemma MTB_A_cells : forall m s pix v ret regs, (160 <= s < 2 ^ 64)%Z -> cellsZ (MTB_A m s pix v ret regs) (TBC s ret regs).
Proof.
  intros m s pix v ret regs Hs. unfold TBC. cbn [cellsZ]. unfold MTB_A, PCFTB, DIMTB, FRTB.
  repeat split; tbwA_rd.
Qed.

Lemma MTB_A_h : forall m s pix v ret regs, (160 <= s < 2 ^ 64)%Z ->
  rdn SEGS (MTB_A m s pix v ret regs) (Z_to_bv 64 (s - 108)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 (p_h v))).
Proof.
  intros m s pix v ret regs Hs. unfold MTB_A, PCFTB, DIMTB, FRTB. tbwA_rd.
Qed.

Lemma tbwD_livk : forall A m m' (q : word) (k : Z) (x : word), LIVK A m m' -> live A q = Some k ->
  (u q <= u x < u q + k)%Z -> m' x = m x.
Proof.
  intros A m m' q k x LV Lq Hx. pose proof (u64_range q). pose proof (u64_range x).
  pose proof (LV q k (u x - u q)%Z Lq ltac:(lia)) as E. unfold at_ in E.
  replace (u q + (u x - u q))%Z with (u x) in E by lia. rewrite zbv_self in E. exact E.
Qed.

Lemma tbwD_keep : forall m m' (s : Z) (ret : word) (regs : bvmap 5 word), (104 <= s < 2 ^ 64)%Z ->
  (forall x : word, (s - 104 <= u x < s)%Z -> m' x = m x) -> cellsZ m (TBC s ret regs) -> cellsZ m' (TBC s ret regs).
Proof.
  intros m m' s ret regs Hs OUT CE. apply (cellsZ_keep m m'); [| exact CE]. unfold TBC.
  repeat (apply Forall_cons; [cbn [fst]; split; [lia | split; [lia | intros x Hx; apply OUT; lia]] |]). apply Forall_nil.
Qed.

Lemma tbwD_frm : forall C s' m m' (s : Z) (ret : word) (regs : bvmap 5 word), Cok C -> FRM C s' m m' ->
  (c_top C - LSTK <= s')%Z -> (s' <= s - 104)%Z -> (s < 2 ^ 64)%Z -> cellsZ m (TBC s ret regs) -> cellsZ m' (TBC s ret regs).
Proof.
  intros C s' m m' s ret regs CK F Hlo Hs Hs2 CE. apply (cellsZ_frm C s' m m' _ CK F Hlo); [| exact CE]. unfold TBC.
  repeat (apply Forall_cons; [cbn [fst]; lia |]). apply Forall_nil.
Qed.

Definition TB_STACK : Z := 112 + CALLOC_STACK.

(* [comment removed for export] *)
Theorem pixFlipTB_inplace_W : forall C Ar A m md regs (s pix k : Z) (v : pixv) (ret : word) (S : TSet),
  Cok C -> W C A m md -> sub_live Ar A ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + TB_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x1381d0 ->
  getr regs 10 = Z_to_bv 64 pix -> getr regs 11 = Z_to_bv 64 pix ->
  PIXat m pix v -> p_d v = 1%Z -> live A (Z_to_bv 64 pix) = Some 64%Z -> Z_to_bv 64 pix <> Z_to_bv 64 (p_data v) ->
  (1 <= p_wpl v)%Z -> (1 <= p_h v)%Z -> (4 * (p_wpl v * p_h v) <= 67108864)%Z ->
  live A (Z_to_bv 64 (p_data v)) = Some k -> (4 * (p_wpl v * p_h v) <= k)%Z ->
  live Ar (Z_to_bv 64 (p_data v)) = None -> live (c_A0 C) (Z_to_bv 64 (p_data v)) = None ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (1 <= kR)%Z -> (alloc_margin (4 * p_wpl v) <= bR)%Z ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C Ar s m m' ->
     (forall q, live A' q = live A q) ->
     (forall q k' i, live A q = Some k' -> q <> Z_to_bv 64 (p_data v) -> (0 <= i < k')%Z -> m' (at_ q i) = m (at_ q i)) ->
     PIXat m' pix v -> getr regs' 10 = Z_to_bv 64 pix ->
     aroom A' vm' (kR - 1) (bR - alloc_margin (4 * p_wpl v)) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (0x997e0 : word) m al_rom) md) S.
Proof.
  intros C Ar A m md regs s pix k v ret S CK HW SUB H2 Hs16 Hlo Hhi H1 Hret H4 H10 H11 PX Hd Lpix NEpd Hwpl1 Hh1 Hwh Ld Hk Lrd L0d
    kR bR Hrm HkR HbR HK.
  unfold TB_STACK, CALLOC_STACK, ALLOC_STACK in Hlo.
  pose proof CK as [T1 T2 T3 T4 T5].
  pose proof PX as (Hp0 & Hp64 & WF & _).
  pose proof WF as [Fw Fh Fd _ Fwpl _ _ _ _ _ _ _ Fdat].
  assert (Hwh1 : (1 <= p_wpl v * p_h v)%Z) by nia.
  assert (Hwpl24 : (p_wpl v <= 2 ^ 24)%Z) by nia.
  assert (Hh24 : (p_h v <= 2 ^ 24)%Z) by nia.
  destruct (blk_range C A m md _ 64 CK HW Lpix ltac:(lia)) as [Gp1 Gp2]. rewrite u_Z2bv in Gp1 by lia. rewrite u_Z2bv in Gp2 by lia.
  destruct (blk_range C A m md _ k CK HW Ld ltac:(lia)) as [Gd1 Gd2]. rewrite u_Z2bv in Gd1 by lia. rewrite u_Z2bv in Gd2 by lia.
  assert (Hs48 : (s < 2 ^ 48)%Z) by lia.
  assert (Hpa : (pix mod 16 = 0)%Z) by exact (tbw_al16 C A m md pix 64 HW Lpix ltac:(lia)).
  assert (Hdm4 : (p_data v mod 4 = 0)%Z).
  { pose proof (tbw_al16 C A m md (p_data v) k HW Ld ltac:(lia)) as X. clear - X. Z.div_mod_to_equations. lia. }
  assert (SOK : store_ok SEGS m (Z_to_bv 64 (s - 160)) 160 = true) by (apply (W_sok_win C A m md); [exact CK | exact HW | lia | cbn; lia]).
  destruct (tb_A al_rom regs m s pix v ret ltac:(lia) ltac:(lia) Hs16 ltac:(lia) Hpa PX ltac:(lia) Hd ltac:(lia) ltac:(lia) SOK H2 H1 H10 H11)
    as (r1 & RUN1 & A2 & A1 & A10 & A11 & A8 & A9 & A18 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  assert (WP1 : W C A (MTB_A m s pix v ret regs) md /\ POSTM C Ar s m (MTB_A m s pix v ret regs)) by (unfold MTB_A, PCFTB, DIMTB, FRTB; wp_win CK).
  destruct WP1 as [HW1 PM1].
  pose proof (MTB_A_cells m s pix v ret regs ltac:(lia)) as CE1.
  pose proof (MTB_A_h m s pix v ret regs ltac:(lia)) as RH1.
  replace (0x10e6e0 : word) with (Z_to_bv 64 0x10e6e0) by (apply bv_eq; reflexivity).
  apply (W_calloc16_sure C A (MTB_A m s pix v ret regs) md r1 (p_wpl v) 4 kR bR _ (s - 112) S CK HW1 A10 A11 ltac:(lia) ltac:(lia) ltac:(lia)
           Hrm HkR ltac:(replace (p_wpl v * 4)%Z with (4 * p_wpl v)%Z by lia; exact HbR) ltac:(unfold ROOM_NMAX; lia)
           A1 ltac:(red; apply bv_eq; reflexivity) ltac:(csr; reflexivity) A2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)).
  intros A1' m2 vm1 r2 res HW2 Hres CS2 Hnz L0 L1 L00 LEQ ZERO AL16 TOP PM2 Hrm1. clear ZERO.
  assert (Hbuf : (1 <= u res)%Z /\ (u res + p_wpl v * 4 <= alloc_top (c_vm C))%Z).
  { pose proof (u64_range res). pose proof (round16_ge (p_wpl v * 4) ltac:(lia)). lia. }
  assert (Eres : res = Z_to_bv 64 (u res)) by (symmetry; apply zbv_self).
  set (buf := u res) in *. clearbody buf.
  rewrite Eres in Hres, L0, L1, L00, LEQ.
  assert (ALb : (buf mod 4 = 0)%Z) by (clear - AL16; Z.div_mod_to_equations; lia).
  assert (SUB1 : sub_live A A1') by (eapply sub_live_new; eassumption).
  assert (SUBr1 : sub_live Ar A1') by (exact (sub_live_trans _ _ _ SUB SUB1)).
  assert (Lbr : live Ar (Z_to_bv 64 buf) = None).
  { destruct (live Ar (Z_to_bv 64 buf)) eqn:E; [pose proof (SUB _ _ E) as E'; congruence | reflexivity]. }
  assert (Ld1 : live A1' (Z_to_bv 64 (p_data v)) = Some k) by (exact (SUB1 _ _ Ld)).
  assert (NEbd : Z_to_bv 64 buf <> Z_to_bv 64 (p_data v)) by (intros E; rewrite E, Ld in L0; discriminate).
  assert (PM2' : POSTM C Ar s m m2).
  { eapply POSTM_trans; [exact PM1 |]. apply (POSTM_sub C Ar A); [exact SUB |]. eapply POSTM_mono; [| exact PM2]. lia. }
  pose proof (tbwD_frm C (s - 112) _ m2 s ret regs CK (proj1 PM2) ltac:(lia) ltac:(lia) ltac:(lia) CE1) as CE2.
  assert (RH : rdn SEGS m2 (Z_to_bv 64 (s - 108)) 4 = Some (Z_to_le_bytes 4 (p_h v))).
  { rewrite (FRM_rdn16 C (s - 112) _ m2 (s - 108) 4 CK (proj1 PM2)) by (cbn; lia). rewrite RH1, w2l_Z4 by lia. reflexivity. }
  replace (Z_to_bv 64 0x99890) with (0x99890 : word) by (apply bv_eq; reflexivity).
  destruct (tb_B al_rom r2 m2 s (p_h v) (p_wpl v) (p_data v) buf ltac:(lia) ltac:(lia) Hh1 Hwpl1 ltac:(lia) ltac:(lia) ltac:(lia) ALb RH
              ltac:(csr; reflexivity) Hres ltac:(csr; reflexivity) ltac:(csr; reflexivity))
    as (r3 & RUN3 & B10 & B19 & B20 & B23 & B24 & B25 & B26 & AG3).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact RUN3 |].
  replace (0x998e0 : word) with (Z_to_bv 64 0x998e0) by (apply bv_eq; reflexivity).
  apply (tb_loop_W (Z.to_nat (p_h v / 2)) C Ar A1' m2 _ s (p_data v) (p_wpl v) (p_h v) buf k S r3 r3 m2 0
           CK HW2 SUBr1 Ld1 ltac:(lia) Lrd L0d L1 Lbr L00 NEbd ltac:(lia) ALb ltac:(lia) ltac:(lia) Hdm4 Hwpl1 Hh1 ltac:(lia) ltac:(lia)
           ltac:(rewrite Z2Nat.id by (apply Z.div_pos; lia); lia) (POSTM_refl _ _ _ _) (fun _ _ _ => eq_refl) (fun _ _ => eq_refl)
           ltac:(csr; reflexivity) ltac:(csr; reflexivity) B19 B20 B23 B24 B25 B26 ltac:(rewrite Z.sub_0_r; exact B10)).
  intros m3 r4 HW3 PM3 FR3 GR3 X1 X10.
  apply (W_free16 C A1' m3 _ r4 (Z_to_bv 64 buf) _ (p_wpl v * 4) (s - 112) S CK HW3 X10 L1 L00 X1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(unfold ALLOC_STACK; lia) ltac:(lia)).
  intros A3 m4 vm2 r5 HW4 CS5 L3b LEQ3 PM4 Rm3.
  rewrite with_vmmaps_twice in HW4 |- *.
  assert (SUBr3 : sub_live Ar A3).
  { intros q kq Lq. assert (NE : q <> Z_to_bv 64 buf) by (intros E; subst q; congruence). rewrite (LEQ3 _ NE). exact (SUBr1 _ _ Lq). }
  assert (PM3' : POSTM C Ar s m m3) by (exact (POSTM_trans _ _ _ _ _ _ PM2' PM3)).
  assert (PM4' : POSTM C Ar s m m4).
  { eapply POSTM_trans; [exact PM3' |]. apply (POSTM_sub C Ar A3); [exact SUBr3 |]. eapply POSTM_mono; [| exact PM4]. lia. }
  pose proof (tbwD_keep m2 m3 s ret regs ltac:(lia) ltac:(intros x Hx; apply FR3; lia) CE2) as CE3.
  pose proof (tbwD_frm C (s - 112) m3 m4 s ret regs CK (proj1 PM4) ltac:(lia) ltac:(lia) ltac:(lia) CE3) as CE4.
  replace (Z_to_bv 64 0x99a08) with (0x99a08 : word) by (apply bv_eq; reflexivity).
  destruct (tb_D al_rom r5 m4 s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22)
              (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) ltac:(lia) ltac:(lia) Hret CE4 ltac:(csr; reflexivity))
    as (r6 & RUN6 & G2 & G1 & G10 & G8 & G9 & G18 & G19 & G20 & G21 & G22 & G23 & G24 & G25 & G26 & G27 & AG6).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW4)) | exact (mp_lazy _ (w_pure _ _ _ _ HW4)) | exact RUN6 |].
  assert (KEEPx : forall (q : word) (k' : Z) (x : word), live A q = Some k' -> q <> Z_to_bv 64 (p_data v) -> (u q <= u x < u q + k')%Z -> m4 x = m x).
  { intros q k' x Lq NE Hx. pose proof (u64_range q). pose proof (u64_range x).
    destruct (blk_range C A m md q k' CK HW Lq ltac:(lia)) as [Q1 Q2].
    assert (NEb : q <> Z_to_bv 64 buf) by (intros E; subst q; congruence).
    pose proof (tbw_apart C A m md q _ k' k CK HW Lq Ld NE ltac:(lia) ltac:(lia)) as APd. rewrite u_Z2bv in APd by lia.
    pose proof (tbw_apart C A1' m2 _ q _ k' (p_wpl v * 4) CK HW2 (SUB1 _ _ Lq) L1 NEb ltac:(lia) ltac:(lia)) as APb. rewrite u_Z2bv in APb by lia.
    assert (LA3 : live A3 q = Some k') by (rewrite (LEQ3 _ NEb); exact (SUB1 _ _ Lq)).
    rewrite (tbwD_livk A3 m3 m4 q k' x (proj2 PM4) LA3 Hx).
    rewrite FR3 by lia.
    rewrite (tbwD_livk A _ m2 q k' x (proj2 PM2) Lq Hx). apply MTB_A_out; lia. }
  apply (HK A3 m4 vm2 r6 HW4).
  - apply cs_kept_intro; csr; reflexivity.
  - exact PM4'.
  - intros q. destruct (bv_eq_dec _ q (Z_to_bv 64 buf)) as [Eb | Nb].
    + subst q. rewrite L3b. symmetry. exact L0.
    + rewrite (LEQ3 _ Nb), (LEQ _ Nb). reflexivity.
  - intros q k' i Lq NE Hi. pose proof (u64_range q). destruct (blk_range C A m md q k' CK HW Lq ltac:(lia)) as [Q1 Q2].
    apply (KEEPx q k'); [exact Lq | exact NE |]. unfold at_. rewrite u_Z2bv by lia. lia.
  - apply (PIXat_frame m); [exact PX |]. intros x Hx. apply (KEEPx (Z_to_bv 64 pix) 64%Z); [exact Lpix | exact NEpd | rewrite u_Z2bv by lia; lia].
  - csr; reflexivity.
  - rewrite with_vmmaps_vmmaps in Rm3.
    assert (Hb0 : (0 <= bR - alloc_margin (p_wpl v * 4))%Z) by (replace (p_wpl v * 4)%Z with (4 * p_wpl v)%Z by lia; lia).
    pose proof (Rm3 _ _ Hrm1 ltac:(lia) Hb0) as Rf.
    rewrite !Z.sub_0_r in Rf. replace (p_wpl v * 4)%Z with (4 * p_wpl v)%Z in Rf by lia. exact Rf.
Qed.

End RotTBW.
