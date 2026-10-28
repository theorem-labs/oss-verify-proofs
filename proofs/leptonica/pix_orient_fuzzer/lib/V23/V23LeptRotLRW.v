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
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require Import O23LeptRotLR O23LeptRotLRW.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptBase V23MemcpyBase V23Memcpy V23LeptRotHip_iface V23LeptRotLR.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section RotLRW.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V23Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Ltac in_kept := unfold callee_kept; cbn [In]; repeat (first [left; reflexivity | right]).
Ltac lrw_agree AG1 AG2 := eapply regs_agree_trans; [eapply regs_agree_mono; [|exact AG1] | eapply regs_agree_mono; [|exact AG2]];
  intros q Hq; cbn [In] in Hq |- *; intuition.

(* [comment removed for export] *)
Lemma lrw_rdn_blk : forall C A m md (p : word) (k a : Z) (n : nat), Cok C -> W C A m md -> live A p = Some k ->
  (u p <= a)%Z -> (a + Z.of_nat n <= u p + k)%Z -> (u p + k < 2 ^ 64)%Z ->
  exists bs, rdn SEGS m (Z_to_bv 64 a) n = Some bs /\ length bs = n.
Proof.
  intros C A m md p k a n CK HW L H1 H2 H3. pose proof (u64_range p).
  apply rdn_defined; [lia | lia |]. intros i Hi.
  apply (blk_byte C A m md p k (Z_to_bv 64 (a + i)) CK HW L). rewrite u_Z2bv by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma lrw_rd1_blk : forall C A m md (p : word) (k a : Z), Cok C -> W C A m md -> live A p = Some k ->
  (u p <= a)%Z -> (a + 1 <= u p + k)%Z -> (u p + k < 2 ^ 64)%Z ->
  exists b, rdn SEGS m (Z_to_bv 64 a) 1 = Some [b].
Proof.
  intros C A m md p k a CK HW L H1 H2 H3.
  destruct (lrw_rdn_blk C A m md p k a 1 CK HW L H1 ltac:(cbn; lia) H3) as (bs & R & Lb).
  destruct bs as [|b [|]]; cbn in Lb; try discriminate. exists b. exact R.
Qed.

(* [comment removed for export] *)
Lemma lrw_sok_blk : forall C A m md (p : word) (k a : Z) (n : nat), Cok C -> W C A m md -> live A p = Some k ->
  (u p <= a)%Z -> (a + Z.of_nat n <= u p + k)%Z -> (u p + k < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 a) n = true.
Proof.
  intros C A m md p k a n CK HW L H1 H2 H3. pose proof (u64_range p).
  apply (exW_sok_blk SEGS C A m md (u p) k a n p16_segs CK HW); [rewrite zbv_self; exact L | lia | lia | lia | lia].
Qed.

(* [comment removed for export] *)
Lemma lrw_apart : forall C A m md (p q : word) (n k : Z), Cok C -> W C A m md ->
  live A p = Some n -> live A q = Some k -> p <> q -> (0 <= n)%Z -> (0 <= k)%Z ->
  (u p + n <= u q \/ u q + k <= u p)%Z.
Proof.
  intros C A m md p q n k CK HW Lp Lq NE Hn Hk.
  destruct (ai_live_disjoint A m (m_vmmaps md) p n q k (w_inv _ _ _ _ HW) Lp Lq NE) as [X|X];
    [left; pose proof (round16_ge n Hn); lia | right; pose proof (round16_ge k Hk); lia].
Qed.

(* [comment removed for export] *)
Lemma lrw_al16 : forall C A m md (p : Z) (k : Z), W C A m md -> live A (Z_to_bv 64 p) = Some k -> (0 <= p < 2 ^ 64)%Z -> (p mod 16 = 0)%Z.
Proof.
  intros C A m md p k HW L Hp.
  destruct (ai_live_hull A m (m_vmmaps md) _ k (w_inv _ _ _ _ HW) L) as (_ & X & _). rewrite u_Z2bv in X by lia. exact X.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma lr_tab_W : forall (n : nat) C Ar A m0 md (s tab wpl : Z) (S : TSet) (r0 r : bvmap 5 word) (m : word -> option byte) (i : Z),
  Cok C -> W C A m md -> sub_live Ar A ->
  live A (Z_to_bv 64 tab) = Some 256%Z -> live Ar (Z_to_bv 64 tab) = None -> live (c_A0 C) (Z_to_bv 64 tab) = None ->
  (4096 <= tab)%Z -> (tab + 256 < 2 ^ 48)%Z -> (0 <= i)%Z -> (Z.of_nat n = 255 - i)%Z ->
  POSTM C Ar s m0 m -> (forall a : word, ~ (tab <= u a < tab + 256)%Z -> m a = m0 a) ->
  regs_agree (fun x => In x [10; 12; 13; 14; 19]%list) r0 r ->
  getr r 9 = Z_to_bv 64 tab -> getr r 10 = Z_to_bv 64 i -> getr r 11 = Z_to_bv 64 1 ->
  getr r 12 = Z_to_bv 64 (tab + i) -> getr r 19 = Z_to_bv 64 (256 - i) -> getr r 18 = Z_to_bv 64 wpl ->
  (forall m' r', W C A m' md -> POSTM C Ar s m0 m' -> (forall a : word, ~ (tab <= u a < tab + 256)%Z -> m' a = m0 a) ->
     regs_agree (fun x => In x [1; 10; 11; 12; 13; 14; 19]%list) r0 r' ->
     getr r' 1 = Z_to_bv 64 0x98e94 -> getr r' 10 = Z_to_bv 64 wpl -> getr r' 11 = Z_to_bv 64 4 ->
     realizes SEGS (mkCfg (mkst r' (Z_to_bv 64 0x10e6e0) m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst r (Z_to_bv 64 0x98c70) m al_rom) md) S.
Proof.
  induction n as [|n IH]; intros C Ar A m0 md s tab wpl S r0 r m i CK HW SUB Lt Lrt L0t Ht Ht2 Hi Hn PM FR AG R9 R10 R11 R12 R19 R18 K.
  - assert (Hi' : i = 255%Z) by lia. subst i.
    assert (SOK : store_ok SEGS m (Z_to_bv 64 (tab + 255)) 1 = true).
    { eapply (lrw_sok_blk C A m md (Z_to_bv 64 tab) 256 (tab + 255) 1 CK HW Lt); rewrite u_Z2bv by lia; cbn; lia. }
    destruct (lr_T1x al_rom r m tab 255 wpl eq_refl Ht Ht2 SOK R9 R10 R11 R12 R19 R18) as (r' & x & RUN & P1 & P10 & P11 & AG').
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN |].
    destruct (WP_blk C Ar A m0 m md (Z_to_bv 64 tab) (Z_to_bv 64 (tab + 255)) 256 (word_to_le_bytes 1 x) s CK (conj HW PM) Lt Lrt L0t SUB)
      as [HW' PM']; [rewrite !u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia |].
    apply K; [exact HW' | exact PM' | | lrw_agree AG AG' | exact P1 | exact P10 | exact P11].
    intros a Ha. rewrite wbytes_outside; [apply FR; exact Ha | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia |].
    rewrite length_N_to_le_bytes, u_Z2bv by lia. cbn. lia.
  - assert (SOK : store_ok SEGS m (Z_to_bv 64 (tab + i)) 1 = true).
    { eapply (lrw_sok_blk C A m md (Z_to_bv 64 tab) 256 (tab + i) 1 CK HW Lt); rewrite u_Z2bv by lia; cbn; lia. }
    destruct (lr_T1n al_rom r m tab i Hi ltac:(lia) Ht Ht2 SOK R9 R10 R11 R12 R19) as (r' & x & RUN & P9 & P10 & P11 & P12 & P19 & AG').
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN |].
    destruct (WP_blk C Ar A m0 m md (Z_to_bv 64 tab) (Z_to_bv 64 (tab + i)) 256 (word_to_le_bytes 1 x) s CK (conj HW PM) Lt Lrt L0t SUB)
      as [HW' PM']; [rewrite !u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia |].
    apply (IH C Ar A m0 md s tab wpl S r0 r' _ (i + 1)%Z CK HW' SUB Lt Lrt L0t Ht Ht2 ltac:(lia) ltac:(lia) PM'); try assumption.
    + intros a Ha. rewrite wbytes_outside; [apply FR; exact Ha | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia |].
      rewrite length_N_to_le_bytes, u_Z2bv by lia. cbn. lia.
    + lrw_agree AG AG'.
    + rewrite (AG' 18) by (cbn [In]; intuition discriminate). exact R18.
Qed.

(* [comment removed for export] *)
Definition LRC (s : Z) (ret : word) (regs : bvmap 5 word) (pix : Z) : list (Z * word) :=
  [(s - 8, ret); (s - 16, getr regs 8); (s - 24, getr regs 9); (s - 32, getr regs 18); (s - 40, getr regs 19); (s - 48, getr regs 20);
   (s - 56, getr regs 21); (s - 64, getr regs 22); (s - 72, getr regs 23); (s - 80, getr regs 24); (s - 88, getr regs 25); (s - 96, getr regs 26);
   (s - 104, getr regs 27); (s - 112, Z_to_bv 64 pix)]%Z.

Ltac lrwfA_sc := rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia.

Ltac lrwfA_rd :=
  repeat first [ rewrite rdn_wbytes_hit8 by lrwfA_sc | rewrite rdn_wbytes_hit4 by lrwfA_sc | rewrite rdn_wbytes_out by lrwfA_sc ];
  reflexivity.

Ltac lrwfA_out a := pose proof (u64_range a); repeat (rewrite wbytes_outside by lrwfA_sc); reflexivity.

Lemma MLR_A_out : forall m s pix v ret regs (a : word), (208 <= s < 2 ^ 64)%Z -> ~ (s - 208 <= u a < s)%Z ->
  MLR_A m s pix v ret regs a = m a.
Proof.
  intros m s pix v ret regs a Hs Ha. unfold MLR_A, PCFLR, DIMLR, FRLR. lrwfA_out a.
Qed.

Lemma MLR_A_cells : forall m s pix v ret regs, (208 <= s < 2 ^ 64)%Z -> (0 <= pix < 2 ^ 64)%Z ->
  cellsZ (MLR_A m s pix v ret regs) (LRC s ret regs pix).
Proof.
  intros m s pix v ret regs Hs Hp. unfold LRC. cbn [cellsZ]. unfold MLR_A, PCFLR, DIMLR, FRLR.
  repeat split; lrwfA_rd.
Qed.

Lemma MLR_A_whd : forall m s pix v ret regs, (208 <= s < 2 ^ 64)%Z ->
  (0 <= p_w v < 2 ^ 31)%Z -> (0 <= p_h v < 2 ^ 31)%Z -> (0 <= p_d v < 2 ^ 31)%Z ->
  rdn SEGS (MLR_A m s pix v ret regs) (Z_to_bv 64 (s - 116)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 (p_w v))) /\
  rdn SEGS (MLR_A m s pix v ret regs) (Z_to_bv 64 (s - 120)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 (p_h v))) /\
  rdn SEGS (MLR_A m s pix v ret regs) (Z_to_bv 64 (s - 124)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 (p_d v))).
Proof.
  intros m s pix v ret regs Hs Hw Hh Hd. unfold MLR_A, PCFLR, DIMLR, FRLR.
  repeat split; lrwfA_rd.
Qed.

Lemma MLR_D_out : forall m s w (a : word), (208 <= s < 2 ^ 64)%Z -> ~ (s - 160 <= u a < s - 128)%Z -> MLR_D m s w a = m a.
Proof.
  intros m s w a Hs Ha. unfold MLR_D. lrwfA_out a.
Qed.

Lemma MLR_D_rd : forall m s w, (208 <= s < 2 ^ 64)%Z -> (1 <= w < 2 ^ 30)%Z ->
  rdn SEGS (MLR_D m s w) (Z_to_bv 64 (s - 160)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 ((w + 7) / 8))) /\
  rdn SEGS (MLR_D m s w) (Z_to_bv 64 (s - 152)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) /\
  rdn SEGS (MLR_D m s w) (Z_to_bv 64 (s - 144)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) /\
  rdn SEGS (MLR_D m s w) (Z_to_bv 64 (s - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (w + 7))).
Proof.
  intros m s w Hs Hw. unfold MLR_D.
  repeat split; lrwfA_rd.
Qed.

Lemma lrwfB_pre : forall C A m md (data kd buf tab wpl h line j db : Z),
  Cok C -> W C A m md ->
  live A (Z_to_bv 64 data) = Some kd -> (4 * wpl * h <= kd)%Z ->
  live A (Z_to_bv 64 buf) = Some (wpl * 4)%Z -> live A (Z_to_bv 64 tab) = Some 256%Z ->
  (4096 <= data)%Z -> (data + 4 * wpl * h < 2 ^ 48)%Z -> (4096 <= buf)%Z -> (buf + 4 * wpl < 2 ^ 48)%Z -> (buf mod 4 = 0)%Z ->
  (4096 <= tab)%Z -> (tab + 256 < 2 ^ 48)%Z -> (1 <= wpl)%Z -> (1 <= h)%Z ->
  (data <= line)%Z -> (line + 4 * wpl <= data + 4 * wpl * h)%Z -> (line mod 4 = 0)%Z ->
  (db <= 4 * wpl)%Z -> (0 <= j)%Z -> (j < db)%Z ->
  exists b1 b2, rdn SEGS m (Z_to_bv 64 (flip3 (buf + (4 * wpl - 1 - j)))) 1 = Some [b1]
    /\ rdn SEGS m (Z_to_bv 64 (tab + u b1)) 1 = Some [b2]
    /\ store_ok SEGS m (Z_to_bv 64 (flip3 (line + j))) 1 = true
    /\ (data <= flip3 (line + j) < data + 4 * wpl * h)%Z.
Proof.
  intros C A m md data kd buf tab wpl h line j db CK HW Ld Hkd Lb Lt Hd Hd2 Hb Hb2 Hbm Ht Ht2 Hw Hh Hl Hl2 Hlm Hdb Hj Hjd.
  pose proof CK as [T1 T2 T3 T4 T5]. unfold LSTK in T1.
  destruct (blk_range C A m md (Z_to_bv 64 data) kd CK HW Ld ltac:(nia)) as [Gd TOPd]. rewrite u_Z2bv in Gd, TOPd by lia.
  pose proof (lrw_flip buf wpl (buf + (4 * wpl - 1 - j)) Hbm ltac:(lia)) as FB.
  pose proof (lrw_flip line wpl (line + j) Hlm ltac:(lia)) as FL.
  destruct (lrw_rd1_blk C A m md (Z_to_bv 64 buf) (wpl * 4) (flip3 (buf + (4 * wpl - 1 - j))) CK HW Lb) as [b1 R1];
    [rewrite u_Z2bv by lia; lia .. |].
  pose proof (u8_range b1) as U1.
  destruct (lrw_rd1_blk C A m md (Z_to_bv 64 tab) 256 (tab + u b1) CK HW Lt) as [b2 R2]; [rewrite u_Z2bv by lia; lia .. |].
  exists b1, b2. split; [exact R1 | split; [exact R2 | split; [| lia]]].
  apply (lrw_sok_blk C A m md (Z_to_bv 64 data) kd (flip3 (line + j)) 1 CK HW Ld); rewrite u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat]; lia.
Qed.

(* [comment removed for export] *)
Lemma lr_bytes_W : forall (n : nat) C Ar A mB md (s data wpl h buf tab kd line : Z) (S : TSet) (r0 r : bvmap 5 word) (m : word -> option byte) (j db : Z),
  Cok C -> W C A m md -> sub_live Ar A ->
  live A (Z_to_bv 64 data) = Some kd -> (4 * wpl * h <= kd)%Z -> live Ar (Z_to_bv 64 data) = None -> live (c_A0 C) (Z_to_bv 64 data) = None ->
  live A (Z_to_bv 64 buf) = Some (wpl * 4)%Z -> live A (Z_to_bv 64 tab) = Some 256%Z ->
  (4096 <= data)%Z -> (data + 4 * wpl * h < 2 ^ 48)%Z -> (4096 <= buf)%Z -> (buf + 4 * wpl < 2 ^ 48)%Z -> (buf mod 4 = 0)%Z ->
  (4096 <= tab)%Z -> (tab + 256 < 2 ^ 48)%Z -> (1 <= wpl < 2 ^ 29)%Z -> (1 <= h)%Z -> (4 * wpl * h <= 2 ^ 26)%Z ->
  (data <= line)%Z -> (line + 4 * wpl <= data + 4 * wpl * h)%Z -> (line mod 4 = 0)%Z ->
  (1 <= db <= 4 * wpl)%Z -> (0 <= j)%Z -> (Z.of_nat n = db - 1 - j)%Z ->
  POSTM C Ar s mB m -> (forall a : word, ~ (data <= u a < data + 4 * wpl * h)%Z -> m a = mB a) ->
  regs_agree (fun x => In x [10; 11; 12; 13; 14; 15; 16]%list) r0 r ->
  getr r 9 = Z_to_bv 64 tab -> getr r 19 = Z_to_bv 64 buf -> getr r 21 = Z_to_bv 64 line ->
  getr r 22 = Z_to_bv 64 1 -> getr r 24 = Z_to_bv 64 3 -> getr r 25 = Z_to_bv 64 (4 * wpl - 1) -> getr r 27 = Z_to_bv 64 1 ->
  getr r 10 = Z_to_bv 64 j -> getr r 11 = Z_to_bv 64 (line + j) -> getr r 12 = Z_to_bv 64 (db - j) -> getr r 13 = Z_to_bv 64 (line + j) ->
  (forall m' r', W C A m' md -> POSTM C Ar s mB m' -> (forall a : word, ~ (data <= u a < data + 4 * wpl * h)%Z -> m' a = mB a) ->
     regs_agree (fun x => In x [10; 11; 12; 13; 14; 15; 16]%list) r0 r' ->
     realizes SEGS (mkCfg (mkst r' (Z_to_bv 64 0x99068) m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst r (Z_to_bv 64 0x98fe4) m al_rom) md) S.
Proof.
  induction n as [|n IH]; intros C Ar A mB md s data wpl h buf tab kd line S r0 r m j db CK HW SUB Ld Hkd Lrd L0d Lb Lt Hd Hd2 Hb Hb2 Hbm
    Ht Ht2 Hw Hh Hwh Hl Hl2 Hlm Hdb Hj Hn PM FR AG R9 R19 R21 R22 R24 R25 R27 R10 R11 R12 R13 K.
  - assert (Hjd : (j + 1 = db)%Z) by lia.
    destruct (lrwfB_pre C A m md data kd buf tab wpl h line j db CK HW Ld Hkd Lb Lt Hd Hd2 Hb Hb2 Hbm Ht Ht2 ltac:(lia) Hh Hl Hl2 Hlm
                ltac:(lia) Hj ltac:(lia)) as (b1 & b2 & Rd1 & Rd2 & SOK & FL).
    destruct (lr_E1e al_rom r m wpl buf tab line j db b1 b2 Hj Hjd ltac:(lia) Hw Hb Hb2 Ht Ht2 ltac:(lia) ltac:(lia) Rd1 Rd2 SOK
                R9 R19 R21 R22 R24 R25 R27 R10 R11 R12 R13) as (r' & bb & RUN & AG').
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN |].
    destruct (WP_blk C Ar A mB m md (Z_to_bv 64 data) (Z_to_bv 64 (flip3 (line + j))) kd [bb] s CK (conj HW PM) Ld Lrd L0d SUB)
      as [HW' PM']; [rewrite !u_Z2bv by lia; lia | cbn [length Z.of_nat Pos.of_succ_nat]; rewrite !u_Z2bv by lia; lia |].
    apply K; [exact HW' | exact PM' | | lrw_agree AG AG'].
    intros a Ha. rewrite wbytes_outside; [apply FR; exact Ha | |]; cbn [length Z.of_nat Pos.of_succ_nat]; rewrite u_Z2bv by lia; lia.
  - assert (Hjd : (j + 1 < db)%Z) by lia.
    destruct (lrwfB_pre C A m md data kd buf tab wpl h line j db CK HW Ld Hkd Lb Lt Hd Hd2 Hb Hb2 Hbm Ht Ht2 ltac:(lia) Hh Hl Hl2 Hlm
                ltac:(lia) Hj ltac:(lia)) as (b1 & b2 & Rd1 & Rd2 & SOK & FL).
    destruct (lr_E1n al_rom r m wpl buf tab line j db b1 b2 Hj Hjd ltac:(lia) Hw Hb Hb2 Ht Ht2 ltac:(lia) ltac:(lia) Rd1 Rd2 SOK
                R9 R19 R21 R22 R24 R25 R27 R10 R11 R12 R13) as (r' & bb & RUN & P10 & P11 & P12 & P13 & AG').
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN |].
    destruct (WP_blk C Ar A mB m md (Z_to_bv 64 data) (Z_to_bv 64 (flip3 (line + j))) kd [bb] s CK (conj HW PM) Ld Lrd L0d SUB)
      as [HW' PM']; [rewrite !u_Z2bv by lia; lia | cbn [length Z.of_nat Pos.of_succ_nat]; rewrite !u_Z2bv by lia; lia |].
    apply (IH C Ar A mB md s data wpl h buf tab kd line S r0 r' _ (j + 1)%Z db CK HW' SUB Ld Hkd Lrd L0d Lb Lt Hd Hd2 Hb Hb2 Hbm
             Ht Ht2 Hw Hh Hwh Hl Hl2 Hlm Hdb ltac:(lia) ltac:(lia) PM'); try assumption.
    all: first
      [ match goal with |- getr _ ?k = _ => rewrite (AG' k) by (cbn [In]; intuition discriminate); assumption end
      | solve [lrw_agree AG AG']
      | (intros a Ha; rewrite wbytes_outside; [apply FR; exact Ha | |]; cbn [length Z.of_nat Pos.of_succ_nat]; rewrite u_Z2bv by lia; lia) ].
Qed.

Ltac lrwfE_in := cbn [In]; repeat (first [left; reflexivity | right]).

Lemma lrwfE_rdn : forall (m m' : word -> option byte) (lo a : Z) (N : nat) bs,
  (forall x : word, (lo <= u x)%Z -> m' x = m x) -> (lo <= a)%Z -> (0 <= a)%Z -> (a + Z.of_nat N < 2 ^ 64)%Z ->
  rdn SEGS m (Z_to_bv 64 a) N = Some bs -> rdn SEGS m' (Z_to_bv 64 a) N = Some bs.
Proof.
  intros m m' lo a N bs E Hl H0 H1 R. rewrite <- R.
  apply rdn_ext; rewrite u_Z2bv by lia; [lia |]. intros x Hx. apply E. lia.
Qed.

Lemma lrwfE_regs : forall r r1 r2 r3 r4 : bvmap 5 word,
  regs_agree (fun x => In x [1; 10; 11; 12; 21]%list) r r1 -> keeps r1 r2 ->
  regs_agree (fun x => In x [10; 11; 12; 13]%list) r2 r3 ->
  regs_agree (fun x => In x [10; 11; 12; 13; 14; 15; 16]%list) r3 r4 ->
  forall x, In x [2; 3; 4; 8; 9; 18; 19; 20; 22; 23; 24; 25; 26; 27]%list -> getr r4 x = getr r x.
Proof.
  intros r r1 r2 r3 r4 A1 KP A3 A4 x Hx. cbn [In] in Hx.
  repeat destruct Hx as [<- | Hx]; try contradiction;
    rewrite (A4 _), (A3 _), (KP _), (A1 _); try reflexivity;
    first [solve [in_kept] | solve [cbn [In]; intuition discriminate]].
Qed.

Lemma lrwfE_fin : forall r0 r r4 r5 : bvmap 5 word,
  (forall x, In x [2; 3; 4; 8; 9; 18; 19; 20; 22; 24; 25; 27]%list -> getr r x = getr r0 x) ->
  (forall x, In x [2; 3; 4; 8; 9; 18; 19; 20; 22; 23; 24; 25; 26; 27]%list -> getr r4 x = getr r x) ->
  regs_agree (fun x => In x [1; 10; 11; 23; 26]%list) r4 r5 ->
  forall x, In x [2; 3; 4; 8; 9; 18; 19; 20; 22; 24; 25; 27]%list -> getr r5 x = getr r0 x.
Proof.
  intros r0 r r4 r5 RG GR AG x Hx. rewrite <- (RG x Hx). cbn [In] in Hx.
  repeat destruct Hx as [<- | Hx]; try contradiction;
    rewrite (AG _) by (cbn [In]; intuition discriminate); apply GR; lrwfE_in.
Qed.

Lemma lrwfE_row : forall C Ar A mB md (s w data wpl h buf tab kd : Z) (S : TSet) (r : bvmap 5 word) (m : word -> option byte) (i : Z),
  Cok C -> W C A m md -> sub_live Ar A ->
  live A (Z_to_bv 64 data) = Some kd -> (4 * wpl * h <= kd)%Z -> live Ar (Z_to_bv 64 data) = None -> live (c_A0 C) (Z_to_bv 64 data) = None ->
  live A (Z_to_bv 64 buf) = Some (wpl * 4)%Z -> live Ar (Z_to_bv 64 buf) = None -> live (c_A0 C) (Z_to_bv 64 buf) = None ->
  live A (Z_to_bv 64 tab) = Some 256%Z -> Z_to_bv 64 buf <> Z_to_bv 64 data ->
  (4096 <= data)%Z -> (data + 4 * wpl * h < 2 ^ 48)%Z -> (data mod 16 = 0)%Z ->
  (4096 <= buf)%Z -> (buf + 4 * wpl < 2 ^ 48)%Z -> (buf mod 16 = 0)%Z -> (4096 <= tab)%Z -> (tab + 256 < 2 ^ 48)%Z ->
  (1 <= wpl < 2 ^ 29)%Z -> (1 <= h < 2 ^ 31)%Z -> (4 * wpl * h <= 2 ^ 26)%Z -> (1 <= w < 2 ^ 30)%Z -> (w <= 32 * wpl)%Z ->
  (0 <= i < h)%Z -> (4096 + 208 <= s < 2 ^ 48)%Z -> (c_top C - LSTK + 208 <= s)%Z -> (s <= c_top C)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 160)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 ((w + 7) / 8))) ->
  rdn SEGS m (Z_to_bv 64 (s - 152)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  rdn SEGS m (Z_to_bv 64 (s - 144)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  rdn SEGS m (Z_to_bv 64 (s - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (w + 7))) ->
  POSTM C Ar s mB m -> (forall a : word, ~ (data <= u a < data + 4 * wpl * h)%Z -> ~ (buf <= u a < buf + 4 * wpl)%Z -> m a = mB a) ->
  getr r 2 = Z_to_bv 64 (s - 160) -> getr r 8 = Z_to_bv 64 data -> getr r 9 = Z_to_bv 64 tab -> getr r 18 = Z_to_bv 64 wpl ->
  getr r 19 = Z_to_bv 64 buf -> getr r 20 = Z_to_bv 64 (4 * wpl) -> getr r 22 = Z_to_bv 64 1 -> getr r 23 = Z_to_bv 64 (wpl * i) ->
  getr r 24 = Z_to_bv 64 3 -> getr r 25 = Z_to_bv 64 (4 * wpl - 1) -> getr r 26 = Z_to_bv 64 i -> getr r 27 = Z_to_bv 64 1 ->
  (forall m' r', W C A m' md -> POSTM C Ar s mB m' -> (forall x : word, (s - 208 <= u x)%Z -> m' x = m x) ->
     (forall a : word, ~ (data <= u a < data + 4 * wpl * h)%Z -> ~ (buf <= u a < buf + 4 * wpl)%Z -> m' a = mB a) ->
     (forall x, In x [2; 3; 4; 8; 9; 18; 19; 20; 22; 23; 24; 25; 26; 27]%list -> getr r' x = getr r x) ->
     realizes SEGS (mkCfg (mkst r' (Z_to_bv 64 0x99068) m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst r (Z_to_bv 64 0x98f6c) m al_rom) md) S.
Proof.
  intros C Ar A mB md s w data wpl h buf tab kd S r m i CK HW SUB Ld Hkd Lrd L0d Lb Lrb L0b Lt NE Hd Hd2 Hd16 Hb Hb2 Hb16 Ht Ht2
    Hw Hh Hwh Hww Hw32 Hi Hs Hct Hct2 Rdb R152 R144 R136 PM FR R2 R8 R9 R18 R19 R20 R22 R23 R24 R25 R26 R27 K.
  pose proof CK as [T1 T2 T3 T4 T5].
  assert (Hwh0 : (4 <= 4 * wpl * h)%Z) by nia.
  assert (Hwi : (0 <= wpl * i)%Z) by nia.
  assert (Hrow : (4 * wpl * i + 4 * wpl <= 4 * wpl * h)%Z) by nia.
  destruct (blk_range C A m md (Z_to_bv 64 data) kd CK HW Ld ltac:(lia)) as [Gd TOPd]. rewrite u_Z2bv in Gd, TOPd by lia.
  destruct (blk_range C A m md (Z_to_bv 64 buf) (wpl * 4) CK HW Lb ltac:(lia)) as [Gb TOPb]. rewrite u_Z2bv in Gb, TOPb by lia.
  assert (Hd4 : (data mod 4 = 0)%Z) by (clear - Hd16; Z.div_mod_to_equations; lia).
  assert (Hb4 : (buf mod 4 = 0)%Z) by (clear - Hb16; Z.div_mod_to_equations; lia).
  pose proof (lrw_mod4 data wpl i Hd4) as Hl4.
  pose proof (databpl_range w wpl ltac:(lia) Hw32) as DB.
  destruct (lr_H al_rom r m s wpl h data buf i ltac:(lia) ltac:(lia) Hwh Hd Hd2 Hd4 Hs R144 R2 R8 R18 R19 R20 R26 R27)
    as (r1 & RUN1 & Q1 & Q10 & Q11 & Q12 & Q21 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  destruct (lrw_rdn_blk C A m md (Z_to_bv 64 data) kd (data + 4 * wpl * i) (Z.to_nat (4 * wpl)) CK HW Ld) as (bs & Rbs & Lbs);
    [rewrite u_Z2bv by lia; rewrite ?Z2Nat.id by lia; lia .. |].
  assert (SOKb : store_ok SEGS m (Z_to_bv 64 buf) (length bs) = true).
  { apply (lrw_sok_blk C A m md (Z_to_bv 64 buf) (wpl * 4) buf (length bs) CK HW Lb); rewrite u_Z2bv by lia; rewrite ?Lbs, ?Z2Nat.id by lia; lia. }
  pose proof (lrw_apart C A m md (Z_to_bv 64 buf) (Z_to_bv 64 data) (wpl * 4) kd CK HW Lb Ld NE ltac:(lia) ltac:(lia)) as AP.
  rewrite !u_Z2bv in AP by lia.
  assert (HOKm : mcH m (Z_to_bv 64 buf) (Z_to_bv 64 (data + 4 * wpl * i)) (4 * wpl) bs).
  { constructor; rewrite ?u_Z2bv by lia; [lia | exact Lbs | rewrite Lbs; exact Rbs | exact SOKb | lia | lia | lia]. }
  destruct (ref_memcpy m _ _ (4 * wpl) bs al_rom HOKm r1 (Z_to_bv 64 0x98fc0) ltac:(red; apply bv_eq; reflexivity) Q1 Q10 Q11 Q12)
    as (r2 & RUN2 & KP2).
  replace (Z_to_bv 64 0x11e154) with (0x11e154 : word) by (apply bv_eq; reflexivity).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN2 |].
  destruct (WP_blk C Ar A mB m md (Z_to_bv 64 buf) (Z_to_bv 64 buf) (wpl * 4) bs s CK (conj HW PM) Lb Lrb L0b SUB) as [HW2 PM2];
    [rewrite !u_Z2bv by lia; lia | rewrite Lbs, Z2Nat.id, !u_Z2bv by lia; lia |].
  assert (OUTB : forall x : word, ~ (buf <= u x < buf + 4 * wpl)%Z -> wbytes m (Z_to_bv 64 buf) bs x = m x).
  { intros x Hx. apply wbytes_outside; rewrite Lbs, Z2Nat.id, u_Z2bv by lia; lia. }
  set (M2 := wbytes m (Z_to_bv 64 buf) bs) in *.
  assert (EXT2 : forall x : word, (s - 208 <= u x)%Z -> M2 x = m x) by (intros x Hx; apply OUTB; lia).
  pose proof (lrwfE_rdn m M2 (s - 208) (s - 160) 8 _ EXT2 ltac:(lia) ltac:(lia) ltac:(cbn; lia) Rdb) as Rdb2.
  pose proof (lrwfE_rdn m M2 (s - 208) (s - 152) 8 _ EXT2 ltac:(lia) ltac:(lia) ltac:(cbn; lia) R152) as R1522.
  pose proof (lrwfE_rdn m M2 (s - 208) (s - 136) 8 _ EXT2 ltac:(lia) ltac:(lia) ltac:(cbn; lia) R136) as R1362.
  pose proof (lrwfE_regs r r1 r2 r2 r2 AG1 KP2 (regs_agree_refl _ _) (regs_agree_refl _ _)) as GR2.
  assert (G2 : getr r2 2 = Z_to_bv 64 (s - 160)) by (rewrite (GR2 2) by (solve [lrwfE_in]); exact R2).
  assert (G8 : getr r2 8 = Z_to_bv 64 data) by (rewrite (GR2 8) by (solve [lrwfE_in]); exact R8).
  assert (G23 : getr r2 23 = Z_to_bv 64 (wpl * i)) by (rewrite (GR2 23) by (solve [lrwfE_in]); exact R23).
  destruct (lr_E0 al_rom r2 M2 s w ((w + 7) / 8) wpl data i Hs Hww Rdb2 R1522 R1362 G2 G8 G23) as (r3 & RUN3 & E10 & E11 & E12 & E13 & AG3).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact RUN3 |].
  pose proof (lrwfE_regs r r1 r2 r3 r3 AG1 KP2 AG3 (regs_agree_refl _ _)) as GR3.
  assert (G21 : getr r3 21 = Z_to_bv 64 (data + 4 * wpl * i)).
  { rewrite (AG3 21) by (cbn [In]; intuition discriminate). rewrite (KP2 21) by (solve [in_kept]). exact Q21. }
  assert (G9 : getr r3 9 = Z_to_bv 64 tab) by (rewrite (GR3 9) by (solve [lrwfE_in]); exact R9).
  assert (G19 : getr r3 19 = Z_to_bv 64 buf) by (rewrite (GR3 19) by (solve [lrwfE_in]); exact R19).
  assert (G22 : getr r3 22 = Z_to_bv 64 1) by (rewrite (GR3 22) by (solve [lrwfE_in]); exact R22).
  assert (G24 : getr r3 24 = Z_to_bv 64 3) by (rewrite (GR3 24) by (solve [lrwfE_in]); exact R24).
  assert (G25 : getr r3 25 = Z_to_bv 64 (4 * wpl - 1)) by (rewrite (GR3 25) by (solve [lrwfE_in]); exact R25).
  assert (G27 : getr r3 27 = Z_to_bv 64 1) by (rewrite (GR3 27) by (solve [lrwfE_in]); exact R27).
  assert (E11' : getr r3 11 = Z_to_bv 64 (data + 4 * wpl * i + 0)) by (rewrite Z.add_0_r; exact E11).
  assert (E12' : getr r3 12 = Z_to_bv 64 ((w + 7) / 8 - 0)) by (rewrite Z.sub_0_r; exact E12).
  assert (E13' : getr r3 13 = Z_to_bv 64 (data + 4 * wpl * i + 0)) by (rewrite Z.add_0_r; exact E13).
  assert (NB : Z.of_nat (Z.to_nat ((w + 7) / 8 - 1)) = ((w + 7) / 8 - 1 - 0)%Z) by (rewrite Z2Nat.id by lia; lia).
  apply (lr_bytes_W (Z.to_nat ((w + 7) / 8 - 1)) C Ar A M2 md s data wpl h buf tab kd (data + 4 * wpl * i) S r3 r3 M2 0 ((w + 7) / 8)
           CK HW2 SUB Ld Hkd Lrd L0d Lb Lt Hd Hd2 Hb Hb2 Hb4 Ht Ht2 Hw ltac:(lia) Hwh ltac:(lia) ltac:(lia) Hl4 DB ltac:(lia) NB
           (POSTM_refl _ _ _ _) (fun _ _ => eq_refl) (regs_agree_refl _ _) G9 G19 G21 G22 G24 G25 G27 E10 E11' E12' E13').
  intros m4 r4 HW4 PM4 FRb AG4.
  apply K; [exact HW4 | exact (POSTM_trans _ _ _ _ _ _ PM2 PM4) | | | exact (lrwfE_regs r r1 r2 r3 r4 AG1 KP2 AG3 AG4)].
  - intros x Hx. rewrite FRb by lia. apply EXT2. exact Hx.
  - intros a Ha1 Ha2. rewrite FRb by exact Ha1. rewrite OUTB by exact Ha2. apply FR; assumption.
Qed.

(* [comment removed for export] *)
Lemma lr_rows_W : forall (n : nat) C Ar A mB md (s w data wpl h buf tab kd : Z) (S : TSet) (r0 r : bvmap 5 word) (m : word -> option byte) (i : Z),
  Cok C -> W C A m md -> sub_live Ar A ->
  live A (Z_to_bv 64 data) = Some kd -> (4 * wpl * h <= kd)%Z -> live Ar (Z_to_bv 64 data) = None -> live (c_A0 C) (Z_to_bv 64 data) = None ->
  live A (Z_to_bv 64 buf) = Some (wpl * 4)%Z -> live Ar (Z_to_bv 64 buf) = None -> live (c_A0 C) (Z_to_bv 64 buf) = None ->
  live A (Z_to_bv 64 tab) = Some 256%Z -> Z_to_bv 64 buf <> Z_to_bv 64 data ->
  (4096 <= data)%Z -> (data + 4 * wpl * h < 2 ^ 48)%Z -> (data mod 16 = 0)%Z ->
  (4096 <= buf)%Z -> (buf + 4 * wpl < 2 ^ 48)%Z -> (buf mod 16 = 0)%Z -> (4096 <= tab)%Z -> (tab + 256 < 2 ^ 48)%Z ->
  (1 <= wpl < 2 ^ 29)%Z -> (1 <= h < 2 ^ 31)%Z -> (4 * wpl * h <= 2 ^ 26)%Z -> (1 <= w < 2 ^ 30)%Z -> (w <= 32 * wpl)%Z ->
  (0 <= i)%Z -> (Z.of_nat n = h - 1 - i)%Z -> (4096 + 208 <= s < 2 ^ 48)%Z -> (c_top C - LSTK + 208 <= s)%Z -> (s <= c_top C)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 120)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 h)) ->
  rdn SEGS m (Z_to_bv 64 (s - 160)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 ((w + 7) / 8))) ->
  rdn SEGS m (Z_to_bv 64 (s - 152)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  rdn SEGS m (Z_to_bv 64 (s - 144)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  rdn SEGS m (Z_to_bv 64 (s - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (w + 7))) ->
  POSTM C Ar s mB m -> (forall a : word, ~ (data <= u a < data + 4 * wpl * h)%Z -> ~ (buf <= u a < buf + 4 * wpl)%Z -> m a = mB a) ->
  (forall x, In x [2; 3; 4; 8; 9; 18; 19; 20; 22; 24; 25; 27]%list -> getr r x = getr r0 x) ->
  getr r 2 = Z_to_bv 64 (s - 160) -> getr r 8 = Z_to_bv 64 data -> getr r 9 = Z_to_bv 64 tab -> getr r 18 = Z_to_bv 64 wpl ->
  getr r 19 = Z_to_bv 64 buf -> getr r 20 = Z_to_bv 64 (4 * wpl) -> getr r 22 = Z_to_bv 64 1 -> getr r 23 = Z_to_bv 64 (wpl * i) ->
  getr r 24 = Z_to_bv 64 3 -> getr r 25 = Z_to_bv 64 (4 * wpl - 1) -> getr r 26 = Z_to_bv 64 i -> getr r 27 = Z_to_bv 64 1 ->
  (forall m' r', W C A m' md -> POSTM C Ar s mB m' ->
     (forall a : word, ~ (data <= u a < data + 4 * wpl * h)%Z -> ~ (buf <= u a < buf + 4 * wpl)%Z -> m' a = mB a) ->
     (forall x, In x [2; 3; 4; 8; 9; 18; 19; 20; 22; 24; 25; 27]%list -> getr r' x = getr r0 x) ->
     getr r' 1 = Z_to_bv 64 0x99790 -> getr r' 10 = Z_to_bv 64 buf ->
     realizes SEGS (mkCfg (mkst r' (Z_to_bv 64 0x10e818) m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst r (Z_to_bv 64 0x98f6c) m al_rom) md) S.
Proof.
  induction n as [|n IH]; intros C Ar A mB md s w data wpl h buf tab kd S r0 r m i CK HW SUB Ld Hkd Lrd L0d Lb Lrb L0b Lt NE Hd Hd2 Hd16
    Hb Hb2 Hb16 Ht Ht2 Hw Hh Hwh Hww Hw32 Hi Hn Hs Hct Hct2 Rh Rdb R152 R144 R136 PM FR RG R2 R8 R9 R18 R19 R20 R22 R23 R24 R25 R26 R27 K.
  all: apply (lrwfE_row C Ar A mB md s w data wpl h buf tab kd S r m i CK HW SUB Ld Hkd Lrd L0d Lb Lrb L0b Lt NE Hd Hd2 Hd16 Hb Hb2 Hb16
                Ht Ht2 Hw Hh Hwh Hww Hw32 ltac:(lia) Hs Hct Hct2 Rdb R152 R144 R136 PM FR R2 R8 R9 R18 R19 R20 R22 R23 R24 R25 R26 R27).
  all: intros m4 r4 HW4 PM4 EXT4 FR4 GR4.
  all: assert (MOV : forall (a : Z) (N : nat) bs, (s - 208 <= a)%Z -> (a + Z.of_nat N < 2 ^ 64)%Z ->
                       rdn SEGS m (Z_to_bv 64 a) N = Some bs -> rdn SEGS m4 (Z_to_bv 64 a) N = Some bs)
         by (intros a N bs Ha HN Rd; exact (lrwfE_rdn m m4 (s - 208) a N bs EXT4 Ha ltac:(lia) HN Rd)).
  all: pose proof (MOV (s - 120)%Z 4%nat _ ltac:(lia) ltac:(cbn; lia) Rh) as Rh4.
  all: assert (P2 : getr r4 2 = Z_to_bv 64 (s - 160)) by (rewrite (GR4 2) by (solve [lrwfE_in]); exact R2).
  all: assert (P18 : getr r4 18 = Z_to_bv 64 wpl) by (rewrite (GR4 18) by (solve [lrwfE_in]); exact R18).
  all: assert (P19 : getr r4 19 = Z_to_bv 64 buf) by (rewrite (GR4 19) by (solve [lrwfE_in]); exact R19).
  all: assert (P23 : getr r4 23 = Z_to_bv 64 (wpl * i)) by (rewrite (GR4 23) by (solve [lrwfE_in]); exact R23).
  all: assert (P26 : getr r4 26 = Z_to_bv 64 i) by (rewrite (GR4 26) by (solve [lrwfE_in]); exact R26).
  - destruct (lr_Rx al_rom r4 m4 s h i buf Hs Hi ltac:(lia) ltac:(lia) Rh4 P2 P26 P19) as (r5 & RUN5 & X1 & X10 & AG5).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW4)) | exact (mp_lazy _ (w_pure _ _ _ _ HW4)) | exact RUN5 |].
    exact (K m4 r5 HW4 PM4 FR4 (lrwfE_fin r0 r r4 r5 RG GR4 AG5) X1 X10).
  - destruct (lr_Rn al_rom r4 m4 s h i wpl Hs Hi ltac:(lia) Hw Hwh Rh4 P2 P18 P23 P26) as (r5 & RUN5 & N26 & N23 & AG5).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW4)) | exact (mp_lazy _ (w_pure _ _ _ _ HW4)) | exact RUN5 |].
    assert (AG5' : regs_agree (fun x => In x [1; 10; 11; 23; 26]%list) r4 r5)
      by (eapply regs_agree_mono; [| exact AG5]; intros q Hq; cbn [In] in Hq |- *; intuition).
    pose proof (lrwfE_fin r r r4 r5 (fun _ _ => eq_refl) GR4 AG5') as F5.
    assert (S2 : getr r5 2 = Z_to_bv 64 (s - 160)) by (rewrite (F5 2) by (solve [lrwfE_in]); exact R2).
    assert (S8 : getr r5 8 = Z_to_bv 64 data) by (rewrite (F5 8) by (solve [lrwfE_in]); exact R8).
    assert (S9 : getr r5 9 = Z_to_bv 64 tab) by (rewrite (F5 9) by (solve [lrwfE_in]); exact R9).
    assert (S18 : getr r5 18 = Z_to_bv 64 wpl) by (rewrite (F5 18) by (solve [lrwfE_in]); exact R18).
    assert (S19 : getr r5 19 = Z_to_bv 64 buf) by (rewrite (F5 19) by (solve [lrwfE_in]); exact R19).
    assert (S20 : getr r5 20 = Z_to_bv 64 (4 * wpl)) by (rewrite (F5 20) by (solve [lrwfE_in]); exact R20).
    assert (S22 : getr r5 22 = Z_to_bv 64 1) by (rewrite (F5 22) by (solve [lrwfE_in]); exact R22).
    assert (S24 : getr r5 24 = Z_to_bv 64 3) by (rewrite (F5 24) by (solve [lrwfE_in]); exact R24).
    assert (S25 : getr r5 25 = Z_to_bv 64 (4 * wpl - 1)) by (rewrite (F5 25) by (solve [lrwfE_in]); exact R25).
    assert (S27 : getr r5 27 = Z_to_bv 64 1) by (rewrite (F5 27) by (solve [lrwfE_in]); exact R27).
    apply (IH C Ar A mB md s w data wpl h buf tab kd S r0 r5 m4 (i + 1)%Z CK HW4 SUB Ld Hkd Lrd L0d Lb Lrb L0b Lt NE Hd Hd2 Hd16 Hb Hb2 Hb16
             Ht Ht2 Hw Hh Hwh Hww Hw32 ltac:(lia) ltac:(lia) Hs Hct Hct2 Rh4
             (MOV (s - 160)%Z 8%nat _ ltac:(lia) ltac:(cbn; lia) Rdb) (MOV (s - 152)%Z 8%nat _ ltac:(lia) ltac:(cbn; lia) R152)
             (MOV (s - 144)%Z 8%nat _ ltac:(lia) ltac:(cbn; lia) R144) (MOV (s - 136)%Z 8%nat _ ltac:(lia) ltac:(cbn; lia) R136)
             PM4 FR4 (lrwfE_fin r0 r r4 r5 RG GR4 AG5') S2 S8 S9 S18 S19 S20 S22 N23 S24 S25 N26 S27 K).
Qed.

Section WithHip.
Hypothesis HIP : rasteropHipLow_contract.

Definition LR_STACK : Z := 160 + CALLOC_STACK.

Lemma lrwfC_ag : forall (L : list reg) (r r' : bvmap 5 word), regs_agree (fun x => In x L) r r' ->
  (forall x, In x [2; 3; 4; 8; 9; 18]%list -> ~ In x L) ->
  forall x, In x [2; 3; 4; 8; 9; 18]%list -> getr r' x = getr r x.
Proof. intros L r r' AG D x Hx. apply AG. exact (D x Hx). Qed.

Lemma lrwfC_cs : forall (r r' : bvmap 5 word), cs_kept r r' -> forall x, In x [2; 3; 4; 8; 9; 18]%list -> getr r' x = getr r x.
Proof.
  intros r r' CS x Hx. apply (cs_kept_get r r' x CS). cbn [In] in Hx.
  destruct Hx as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; [exact cs2 | exact cs3 | exact cs4 | exact cs8 | exact cs9 | exact cs18].
Qed.

Ltac lrwfC_dis := let x := fresh "x" in let Hx := fresh "Hx" in
  intros x Hx; cbn [In] in Hx; destruct Hx as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn [In]; intuition discriminate.

Lemma lrwfC_s : forall C (s : Z), Cok C -> (c_top C - LSTK + LR_STACK <= s)%Z -> (4096 + 208 <= s)%Z.
Proof.
  intros C s CK H. pose proof (ck_top _ CK) as T1. pose proof (ck_img _ CK) as T5.
  cbn [fst snd ll_img LLU16] in T5. unfold LR_STACK, CALLOC_STACK, ALLOC_STACK in H. lia.
Qed.

Lemma lrwfC_tail : forall C Ar A md (s w h wpl data buf tab : Z) (S : TSet) (r0 r : bvmap 5 word) (m m1 : word -> option byte),
  Cok C -> W C A m1 md -> sub_live Ar A -> POSTM C Ar (s - 160) m m1 ->
  (forall a : word, ~ (data <= u a < data + 4 * wpl * h)%Z -> ~ scratch C (s - 160) a -> m1 a = m a) ->
  (4096 <= data)%Z -> (data + 4 * wpl * h < 2 ^ 48)%Z ->
  (4096 <= buf)%Z -> (buf + 4 * wpl < 2 ^ 48)%Z -> (buf mod 16 = 0)%Z -> (4096 <= tab)%Z -> (tab + 256 < 2 ^ 48)%Z ->
  (1 <= w < 2 ^ 30)%Z -> (1 <= h < 2 ^ 31)%Z -> (1 <= wpl < 2 ^ 29)%Z ->
  (c_top C - LSTK + LR_STACK <= s)%Z -> (s <= c_top C)%Z -> (s < 2 ^ 48)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 120)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 h)) ->
  (forall x, In x [2; 3; 4; 8; 9; 18]%list -> getr r x = getr r0 x) ->
  getr r 2 = Z_to_bv 64 (s - 160) -> getr r 8 = Z_to_bv 64 data -> getr r 9 = Z_to_bv 64 tab -> getr r 10 = Z_to_bv 64 w ->
  getr r 18 = Z_to_bv 64 wpl -> getr r 19 = Z_to_bv 64 buf -> getr r 20 = Z_to_bv 64 (4 * wpl) ->
  (forall m' r', W C A m' md -> POSTM C Ar s m m' ->
     (forall a : word, ~ (data <= u a < data + 4 * wpl * h)%Z -> ~ scratch C (s - 128) a -> m' a = m a) ->
     (forall x, In x [2; 3; 4; 8; 9; 18]%list -> getr r' x = getr r0 x) ->
     getr r' 19 = Z_to_bv 64 buf -> getr r' 20 = Z_to_bv 64 (4 * wpl) -> getr r' 22 = Z_to_bv 64 1 -> getr r' 23 = Z_to_bv 64 0 ->
     getr r' 24 = Z_to_bv 64 3 -> getr r' 25 = Z_to_bv 64 (4 * wpl - 1) -> getr r' 26 = Z_to_bv 64 0 -> getr r' 27 = Z_to_bv 64 1 ->
     rdn SEGS m' (Z_to_bv 64 (s - 120)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 h)) ->
     rdn SEGS m' (Z_to_bv 64 (s - 160)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 ((w + 7) / 8))) ->
     rdn SEGS m' (Z_to_bv 64 (s - 152)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
     rdn SEGS m' (Z_to_bv 64 (s - 144)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
     rdn SEGS m' (Z_to_bv 64 (s - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (w + 7))) ->
     realizes SEGS (mkCfg (mkst r' (Z_to_bv 64 0x98f6c) m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst r (Z_to_bv 64 0x98f10) m1 al_rom) md) S.
Proof.
  intros C Ar A md s w h wpl data buf tab S r0 r m m1 CK HW1 SUB PM FR Hd1 Hd2 Hb1 Hb2 Hb16 Ht1 Ht2 Hw Hh Hwpl Hslo Hshi Hs48 Rh RK
    H2 H8 H9 H10 H18 H19 H20 K.
  pose proof (lrwfC_s C s CK Hslo) as Hs1.
  unfold LR_STACK, CALLOC_STACK, ALLOC_STACK in Hslo.
  pose proof (lrw_mod16_4 buf Hb16) as Hb4.
  assert (Rh1 : rdn SEGS m1 (Z_to_bv 64 (s - 120)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 h))).
  { rewrite (FRM_rdn16 C (s - 160) m m1 (s - 120) 4 CK (proj1 PM)) by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia). exact Rh. }
  assert (SOK : store_ok SEGS m1 (Z_to_bv 64 (s - 208)) 208 = true).
  { apply (W_sok_win C A m1 md (s - 208) 208 CK HW1); cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia. }
  destruct (lr_D al_rom r m1 s w h wpl data buf tab Hs1 Hs48 Hw Hh Hwpl Hd1 Hd2 Ht1 Ht2 Hb1 Hb2 Hb4 SOK Rh1 H2 H8 H9 H10 H18 H19 H20)
    as (r' & RUN & P22 & P23 & P24 & P25 & P26 & P27 & AG).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN |].
  assert (HWD : W C A (MLR_D m1 s w) md).
  { unfold MLR_D.
    repeat (apply W_store_win; [exact CK | | rewrite ?u_Z2bv by lia; lia | rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia]).
    exact HW1. }
  assert (PMD : POSTM C Ar s m (MLR_D m1 s w)).
  { eapply POSTM_trans; [eapply POSTM_mono; [| exact PM]; lia |].
    apply (POSTM_sub C Ar A s m1 _ SUB).
    apply (POSTM_range C A m1 md (MLR_D m1 s w) (s - 160) (s - 128) s CK HW1); [| lia | lia | lia].
    intros a Ha. apply MLR_D_out; [lia | exact Ha]. }
  destruct (MLR_D_rd m1 s w ltac:(lia) Hw) as (R160 & R152 & R144 & R136).
  assert (Rh2 : rdn SEGS (MLR_D m1 s w) (Z_to_bv 64 (s - 120)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 h))).
  { rewrite <- Rh1. apply rdn_ext; [rewrite u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia |].
    intros x Hx. rewrite u_Z2bv in Hx by lia. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx. apply MLR_D_out; lia. }
  apply (K (MLR_D m1 s w) r' HWD PMD); try assumption.
  - intros a Ha Hsc. unfold scratch in Hsc. rewrite MLR_D_out by lia. apply FR; [exact Ha | unfold scratch; lia].
  - intros x Hx. rewrite (lrwfC_ag _ r r' AG ltac:(lrwfC_dis) x Hx). exact (RK x Hx).
  - rewrite (AG 19) by (cbn [In]; intuition discriminate). exact H19.
  - rewrite (AG 20) by (cbn [In]; intuition discriminate). exact H20.
Qed.

Lemma lr_pre_W : forall C Ar A md (s w h wpl data buf tab kd : Z) (S : TSet) (r : bvmap 5 word) (m : word -> option byte),
  Cok C -> W C A m md -> sub_live Ar A ->
  live A (Z_to_bv 64 data) = Some kd -> (4 * (wpl * h) <= kd)%Z -> live Ar (Z_to_bv 64 data) = None -> live (c_A0 C) (Z_to_bv 64 data) = None ->
  (4096 <= data)%Z -> (data + 4 * wpl * h < 2 ^ 48)%Z -> (data mod 16 = 0)%Z ->
  (4096 <= buf)%Z -> (buf + 4 * wpl < 2 ^ 48)%Z -> (buf mod 16 = 0)%Z -> (4096 <= tab)%Z -> (tab + 256 < 2 ^ 48)%Z ->
  (1 <= w < 2 ^ 30)%Z -> (w <= 32 * wpl)%Z -> (1 <= h < 2 ^ 31)%Z -> (1 <= wpl < 2 ^ 29)%Z -> (4 * (wpl * h) <= 67108864)%Z ->
  (s mod 16 = 0)%Z -> (c_top C - LSTK + LR_STACK <= s)%Z -> (s <= c_top C)%Z -> (s < 2 ^ 48)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 116)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 w)) ->
  rdn SEGS m (Z_to_bv 64 (s - 120)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 h)) ->
  rdn SEGS m (Z_to_bv 64 (s - 124)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 1)) ->
  getr r 2 = Z_to_bv 64 (s - 160) -> getr r 8 = Z_to_bv 64 data -> getr r 9 = Z_to_bv 64 tab -> getr r 10 = Z_to_bv 64 buf ->
  getr r 18 = Z_to_bv 64 wpl ->
  (forall m' r', W C A m' md -> POSTM C Ar s m m' ->
     (forall a : word, ~ (data <= u a < data + 4 * wpl * h)%Z -> ~ scratch C (s - 128) a -> m' a = m a) ->
     (forall x, In x [2; 3; 4; 8; 9; 18]%list -> getr r' x = getr r x) ->
     getr r' 19 = Z_to_bv 64 buf -> getr r' 20 = Z_to_bv 64 (4 * wpl) -> getr r' 22 = Z_to_bv 64 1 -> getr r' 23 = Z_to_bv 64 0 ->
     getr r' 24 = Z_to_bv 64 3 -> getr r' 25 = Z_to_bv 64 (4 * wpl - 1) -> getr r' 26 = Z_to_bv 64 0 -> getr r' 27 = Z_to_bv 64 1 ->
     rdn SEGS m' (Z_to_bv 64 (s - 120)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 h)) ->
     rdn SEGS m' (Z_to_bv 64 (s - 160)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 ((w + 7) / 8))) ->
     rdn SEGS m' (Z_to_bv 64 (s - 152)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
     rdn SEGS m' (Z_to_bv 64 (s - 144)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
     rdn SEGS m' (Z_to_bv 64 (s - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (w + 7))) ->
     realizes SEGS (mkCfg (mkst r' (Z_to_bv 64 0x98f6c) m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst r (Z_to_bv 64 0x98e94) m al_rom) md) S.
Proof.
  intros C Ar A md s w h wpl data buf tab kd S r m CK HW SUB Ld Hkd Lrd L0d Hd1 Hd2 Hd16 Hb1 Hb2 Hb16 Ht1 Ht2 Hw Hww Hh Hwpl Hhd
    Hs16 Hslo Hshi Hs48 Rw Rh Rd H2 H8 H9 H10 H18 K.
  pose proof (lrwfC_s C s CK Hslo) as Hs1.
  assert (RJ : rdn SEGS m (Z_to_bv 64 0x1f7e8) 4 = Some (Z_to_le_bytes 4 497396)).
  { assert (E : rdn SEGS (fun _ => None) (Z_to_bv 64 0x1f7e8) 4 = Some (Z_to_le_bytes 4 497396)) by vm_refl_bv.
    rewrite <- E. rewrite <- p16_segs. apply (W_rdn_ro C A m md); [exact HW | cbn [fst snd ll_ro LLU16]; lia | cbn [fst snd ll_ro LLU16 Z.of_nat Pos.of_succ_nat Pos.succ]; lia]. }
  destruct (Z.eq_dec (w mod 32) 0) as [Wz | Wnz].
  - destruct (lr_Bn al_rom r m s w wpl buf Hs1 Hs48 Hw Hwpl Hb1 Hb2 Wz Rw Rd RJ H2 H10 H18) as (r1 & RUN & P10 & P19 & P20 & AG).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN |].
    apply (lrwfC_tail C Ar A md s w h wpl data buf tab S r r1 m m CK HW SUB (POSTM_refl C Ar (s - 160) m) (fun a _ _ => eq_refl)
             Hd1 Hd2 Hb1 Hb2 Hb16 Ht1 Ht2 Hw Hh Hwpl Hslo Hshi Hs48 Rh); try assumption.
    + intros x Hx. exact (lrwfC_ag _ r r1 AG ltac:(lrwfC_dis) x Hx).
    + rewrite (AG 2) by (cbn [In]; intuition discriminate). exact H2.
    + rewrite (AG 8) by (cbn [In]; intuition discriminate). exact H8.
    + rewrite (AG 9) by (cbn [In]; intuition discriminate). exact H9.
    + rewrite (AG 18) by (cbn [In]; intuition discriminate). exact H18.
  - destruct (lr_Bh al_rom r m s w h wpl data buf tab Hs1 Hs48 Hw Hh Hwpl Hb1 Hb2 Wnz Rw Rh Rd RJ H2 H8 H9 H10 H18)
      as (r1 & RUN & P1 & P10 & P11 & P12 & P13 & P14 & P15 & B16 & P19 & P20 & AG1).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN |].
    assert (Y2 : getr r1 2 = Z_to_bv 64 (s - 160)) by (rewrite (AG1 2) by (cbn [In]; intuition discriminate); exact H2).
    pose proof (Z.mod_pos_bound w 32 ltac:(lia)) as Wm.
    unfold LR_STACK, CALLOC_STACK, ALLOC_STACK in Hslo.
    refine (HIP C Ar A m md r1 (s - 160)%Z data h wpl (32 - w mod 32)%Z kd (Z_to_bv 64 0x98f0c) S CK HW SUB Y2
              ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold HIP_STACK; lia) ltac:(lia) P1
              ltac:(red; apply bv_eq; reflexivity) P10 P11 P12 P13 P14 P15 B16 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hhd
              Ld Hkd Lrd L0d _).
    intros m1 r2 HW1 CS2 PM1 FR1.
    assert (Rw1 : rdn SEGS m1 (Z_to_bv 64 (s - 116)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 w))).
    { rewrite (FRM_rdn16 C (s - 160) m m1 (s - 116) 4 CK (proj1 PM1)) by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia). exact Rw. }
    assert (Z2 : getr r2 2 = Z_to_bv 64 (s - 160)) by (rewrite (cs_kept_get r1 r2 2 CS2 cs2); exact Y2).
    destruct (lr_C al_rom r2 m1 s w Hs1 Hs48 Hw Rw1 Z2) as (r3 & RUN3 & Q10 & AG3).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN3 |].
    assert (KP : forall x, In x [2; 3; 4; 8; 9; 18]%list -> getr r3 x = getr r x).
    { intros x Hx. rewrite (lrwfC_ag _ r2 r3 AG3 ltac:(lrwfC_dis) x Hx), (lrwfC_cs r1 r2 CS2 x Hx).
      exact (lrwfC_ag _ r r1 AG1 ltac:(lrwfC_dis) x Hx). }
    assert (FR1' : forall a : word, ~ (data <= u a < data + 4 * wpl * h)%Z -> ~ scratch C (s - 160) a -> m1 a = m a).
    { intros a Ha Hsc. apply FR1; [exact Hsc | nia]. }
    apply (lrwfC_tail C Ar A md s w h wpl data buf tab S r r3 m m1 CK HW1 SUB PM1 FR1'
             Hd1 Hd2 Hb1 Hb2 Hb16 Ht1 Ht2 Hw Hh Hwpl ltac:(unfold LR_STACK, CALLOC_STACK, ALLOC_STACK; lia) Hshi Hs48 Rh KP); try assumption.
    + rewrite (AG3 2) by (cbn [In]; intuition discriminate). exact Z2.
    + rewrite (AG3 8) by (cbn [In]; intuition discriminate). rewrite (cs_kept_get r1 r2 8 CS2 cs8).
      rewrite (AG1 8) by (cbn [In]; intuition discriminate). exact H8.
    + rewrite (AG3 9) by (cbn [In]; intuition discriminate). rewrite (cs_kept_get r1 r2 9 CS2 cs9).
      rewrite (AG1 9) by (cbn [In]; intuition discriminate). exact H9.
    + rewrite (AG3 18) by (cbn [In]; intuition discriminate). rewrite (cs_kept_get r1 r2 18 CS2 cs18).
      rewrite (AG1 18) by (cbn [In]; intuition discriminate). exact H18.
    + rewrite (AG3 19) by (cbn [In]; intuition discriminate). rewrite (cs_kept_get r1 r2 19 CS2 cs19). exact P19.
    + rewrite (AG3 20) by (cbn [In]; intuition discriminate). rewrite (cs_kept_get r1 r2 20 CS2 cs20). exact P20.
Qed.

Lemma lrwfD_livk : forall A m m' (q : word) (k : Z) (x : word), LIVK A m m' -> live A q = Some k ->
  (u q <= u x < u q + k)%Z -> m' x = m x.
Proof.
  intros A m m' q k x LV Lq Hx. pose proof (u64_range q). pose proof (u64_range x).
  pose proof (LV q k (u x - u q)%Z Lq ltac:(lia)) as E. unfold at_ in E.
  replace (u q + (u x - u q))%Z with (u x) in E by lia. rewrite zbv_self in E. exact E.
Qed.

Lemma lrwfD_keep : forall m m' (s : Z) (ret : word) (regs : bvmap 5 word) (pix : Z), (112 <= s < 2 ^ 64)%Z ->
  (forall x : word, (s - 112 <= u x < s)%Z -> m' x = m x) -> cellsZ m (LRC s ret regs pix) -> cellsZ m' (LRC s ret regs pix).
Proof.
  intros m m' s ret regs pix Hs OUT CE. apply (cellsZ_keep m m'); [| exact CE]. unfold LRC.
  repeat (apply Forall_cons; [cbn [fst]; split; [lia | split; [lia | intros x Hx; apply OUT; lia]] |]). apply Forall_nil.
Qed.

Lemma lrwfD_frm : forall C s' m m' (s : Z) (ret : word) (regs : bvmap 5 word) (pix : Z), Cok C -> FRM C s' m m' ->
  (c_top C - LSTK <= s')%Z -> (s' <= s - 112)%Z -> (s < 2 ^ 64)%Z -> cellsZ m (LRC s ret regs pix) -> cellsZ m' (LRC s ret regs pix).
Proof.
  intros C s' m m' s ret regs pix CK F Hlo Hs Hs2 CE. apply (cellsZ_frm C s' m m' _ CK F Hlo); [| exact CE]. unfold LRC.
  repeat (apply Forall_cons; [cbn [fst]; lia |]). apply Forall_nil.
Qed.

Lemma lrwfD_rd : forall C m1 m2 m3 m4 (s tab a : Z) (n : nat), Cok C -> FRM C (s - 160) m1 m2 ->
  (forall x : word, ~ (tab <= u x < tab + 256)%Z -> m3 x = m2 x) -> FRM C (s - 160) m3 m4 ->
  (c_top C - LSTK <= s - 160)%Z -> (s - 160 <= a)%Z -> (a + Z.of_nat n <= s)%Z -> (0 <= tab)%Z -> (tab + 256 <= s - 160)%Z ->
  (s < 2 ^ 64)%Z -> rdn SEGS m4 (Z_to_bv 64 a) n = rdn SEGS m1 (Z_to_bv 64 a) n.
Proof.
  intros C m1 m2 m3 m4 s tab a n CK F12 F23 F34 Hlo Ha Han Ht0 Ht Hs.
  rewrite (FRM_rdn16 C (s - 160) m3 m4 a n CK F34) by lia. rewrite <- (FRM_rdn16 C (s - 160) m1 m2 a n CK F12) by lia.
  apply rdn_ext; [rewrite u_Z2bv by lia; lia |]. intros x Hx. rewrite u_Z2bv in Hx by lia. apply F23. lia.
Qed.

(* [comment removed for export] *)
Theorem pixFlipLR_inplace_W : forall C Ar A m md regs (s pix k : Z) (v : pixv) (ret : word) (S : TSet),
  Cok C -> W C A m md -> sub_live Ar A ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + LR_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x1381d0 ->
  getr regs 10 = Z_to_bv 64 pix -> getr regs 11 = Z_to_bv 64 pix ->
  PIXat m pix v -> p_d v = 1%Z -> live A (Z_to_bv 64 pix) = Some 64%Z -> Z_to_bv 64 pix <> Z_to_bv 64 (p_data v) ->
  (1 <= p_w v)%Z -> (p_w v <= 32 * p_wpl v)%Z -> (1 <= p_wpl v)%Z -> (1 <= p_h v)%Z -> (4 * (p_wpl v * p_h v) <= 67108864)%Z ->
  live A (Z_to_bv 64 (p_data v)) = Some k -> (4 * (p_wpl v * p_h v) <= k)%Z ->
  live Ar (Z_to_bv 64 (p_data v)) = None -> live (c_A0 C) (Z_to_bv 64 (p_data v)) = None ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (2 <= kR)%Z -> (alloc_margin 256 + alloc_margin (4 * p_wpl v) <= bR)%Z ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C Ar s m m' ->
     (forall q, live A' q = live A q) ->
     (forall q k' i, live A q = Some k' -> q <> Z_to_bv 64 (p_data v) -> (0 <= i < k')%Z -> m' (at_ q i) = m (at_ q i)) ->
     PIXat m' pix v -> getr regs' 10 = Z_to_bv 64 pix ->
     aroom A' vm' (kR - 2) (bR - alloc_margin 256 - alloc_margin (4 * p_wpl v)) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (0x98b88 : word) m al_rom) md) S.
Proof.
  intros C Ar A m md regs s pix k v ret S CK HW SUB H2 Hs16 Hlo Hhi H1 Hret H4 H10 H11 PX Hd Lpix NEpd Hw1 Hw32 Hwpl1 Hh1 Hwh Ld Hk Lrd L0d
    kR bR Hrm HkR HbR HK.
  unfold LR_STACK, CALLOC_STACK, ALLOC_STACK in Hlo.
  pose proof CK as [T1 T2 T3 T4 T5].
  pose proof PX as (Hp0 & Hp64 & WF & _).
  pose proof WF as [Fw Fh Fd _ Fwpl _ _ _ _ _ _ _ Fdat].
  assert (Hwh1 : (1 <= p_wpl v * p_h v)%Z) by nia.
  assert (Hwpl24 : (p_wpl v <= 2 ^ 24)%Z) by nia.
  assert (Hh24 : (p_h v <= 2 ^ 24)%Z) by nia.
  destruct (blk_range C A m md _ 64 CK HW Lpix ltac:(lia)) as [Gp1 Gp2]. rewrite u_Z2bv in Gp1 by lia. rewrite u_Z2bv in Gp2 by lia.
  destruct (blk_range C A m md _ k CK HW Ld ltac:(lia)) as [Gd1 Gd2]. rewrite u_Z2bv in Gd1 by lia. rewrite u_Z2bv in Gd2 by lia.
  assert (Hs48 : (s < 2 ^ 48)%Z) by lia.
  assert (Hs0 : (4096 + 208 <= s)%Z) by lia.
  assert (Hpa : (pix mod 8 = 0)%Z).
  { pose proof (lrw_al16 C A m md pix 64 HW Lpix ltac:(lia)) as X. clear - X. Z.div_mod_to_equations. lia. }
  assert (Hdm16 : (p_data v mod 16 = 0)%Z) by exact (lrw_al16 C A m md (p_data v) k HW Ld ltac:(lia)).
  assert (SOK : store_ok SEGS m (Z_to_bv 64 (s - 208)) 208 = true) by (apply (W_sok_win C A m md); [exact CK | exact HW | lia | cbn; lia]).
  lazymatch goal with |- realizes _ (mkCfg (mkst _ ?pc _ _) _) _ => replace pc with (Z_to_bv 64 0x98b88) by (apply bv_eq; reflexivity) end.
  destruct (lr_A al_rom regs m s pix v ret ltac:(lia) Hs48 Hs16 Gp1 ltac:(lia) Hpa PX ltac:(lia) Hd Hw1 Hh1 Hwpl1 ltac:(lia) SOK H2 H1 H10 H11)
    as (r1 & RUN1 & A2 & A1 & A10 & A11 & A8 & A9 & A18 & A19 & A20 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  assert (WP1 : W C A (MLR_A m s pix v ret regs) md /\ POSTM C Ar s m (MLR_A m s pix v ret regs)) by (unfold MLR_A, PCFLR, DIMLR, FRLR; wp_win CK).
  destruct WP1 as [HW1 PM1].
  pose proof (MLR_A_cells m s pix v ret regs ltac:(lia) ltac:(lia)) as CE1.
  destruct (MLR_A_whd m s pix v ret regs ltac:(lia) Fw Fh Fd) as (WH1 & WH2 & WH3). rewrite Hd in WH3.
  apply (W_calloc16_sure C A (MLR_A m s pix v ret regs) md r1 256 1 kR bR _ (s - 160) S CK HW1 A10 A11 ltac:(lia) ltac:(lia) ltac:(lia)
           Hrm ltac:(lia) ltac:(pose proof (alloc_margin_ge (4 * p_wpl v) ltac:(lia)); change (256 * 1)%Z with 256%Z; lia) ltac:(unfold ROOM_NMAX; lia)
           A1 ltac:(red; apply bv_eq; reflexivity) ltac:(csr; reflexivity) A2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)).
  intros A1' m2 vm1 r2 res HW2 Hres CS2 Hnz L0 L1 L00 LEQ ZERO AL16 TOP PM2 Hrm1. clear ZERO.
  assert (Htab : (1 <= u res)%Z /\ (u res + 256 <= alloc_top (c_vm C))%Z).
  { pose proof (u64_range res). pose proof (round16_ge (256 * 1) ltac:(lia)). lia. }
  assert (Eres : res = Z_to_bv 64 (u res)) by (symmetry; apply zbv_self).
  set (tab := u res) in *. clearbody tab.
  rewrite Eres in Hres, L0, L1, L00, LEQ.
  change (256 * 1)%Z with 256%Z in L1.
  destruct (blk_range C A1' m2 _ (Z_to_bv 64 tab) 256 CK HW2 L1 ltac:(lia)) as [Gt1 _]. rewrite u_Z2bv in Gt1 by lia.
  assert (SUB1 : sub_live A A1') by (eapply sub_live_new; eassumption).
  assert (SUBr1 : sub_live Ar A1') by (exact (sub_live_trans _ _ _ SUB SUB1)).
  assert (Lrt : live Ar (Z_to_bv 64 tab) = None).
  { destruct (live Ar (Z_to_bv 64 tab)) eqn:E; [pose proof (SUB _ _ E) as E'; congruence | reflexivity]. }
  assert (PM2' : POSTM C Ar s m m2).
  { eapply POSTM_trans; [exact PM1 |]. apply (POSTM_sub C Ar A); [exact SUB |]. eapply POSTM_mono; [| exact PM2]. lia. }
  pose proof (lrwfD_frm C (s - 160) _ m2 s ret regs pix CK (proj1 PM2) ltac:(lia) ltac:(lia) ltac:(lia) CE1) as CE2.
  destruct (lr_T0 al_rom r2 m2 tab Gt1 ltac:(lia) Hres) as (r3 & RUN3 & T9 & T10 & T11 & T12 & AG3).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact RUN3 |].
  assert (R19 : getr r3 19 = Z_to_bv 64 (256 - 0)) by (csr; reflexivity).
  assert (R18 : getr r3 18 = Z_to_bv 64 (p_wpl v)) by (csr; reflexivity).
  apply (lr_tab_W 255 C Ar A1' m2 _ s tab (p_wpl v) S r3 r3 m2 0 CK HW2 SUBr1 L1 Lrt L00 Gt1 ltac:(lia) ltac:(lia) ltac:(reflexivity)
           (POSTM_refl _ _ _ _) (fun a _ => eq_refl) (regs_agree_refl _ _) T9 T10 T11 ltac:(rewrite Z.add_0_r; exact T12) R19 R18).
  intros m3 r4 HW3 PM3 FR3 AG4 B1 B10 B11.
  assert (PM3' : POSTM C Ar s m m3) by (exact (POSTM_trans _ _ _ _ _ _ PM2' PM3)).
  pose proof (lrwfD_keep m2 m3 s ret regs pix ltac:(lia) ltac:(intros x Hx; apply FR3; lia) CE2) as CE3.
  apply (W_calloc16_sure C A1' m3 _ r4 (p_wpl v) 4 (kR - 1) (bR - alloc_margin (256 * 1)) _ (s - 160) S CK HW3 B10 B11 ltac:(lia) ltac:(lia) ltac:(lia)
           ltac:(rewrite with_vmmaps_vmmaps; exact Hrm1) ltac:(lia)
           ltac:(replace (p_wpl v * 4)%Z with (4 * p_wpl v)%Z by lia; change (256 * 1)%Z with 256%Z; lia)
           ltac:(unfold ROOM_NMAX; lia) B1 ltac:(red; apply bv_eq; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity)
           ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)).
  intros A2' m4 vm2 r5 res2 HW4 Hres2 CS5 Hnz2 K0 K1 K00 KEQ ZERO2 AL16b TOP2 PM4 Hrm2. clear ZERO2.
  rewrite with_vmmaps_twice in HW4 |- *.
  assert (Hbuf : (1 <= u res2)%Z /\ (u res2 + p_wpl v * 4 <= alloc_top (c_vm C))%Z).
  { pose proof (u64_range res2). pose proof (round16_ge (p_wpl v * 4) ltac:(lia)). lia. }
  assert (Eres2 : res2 = Z_to_bv 64 (u res2)) by (symmetry; apply zbv_self).
  set (buf := u res2) in *. clearbody buf.
  rewrite Eres2 in Hres2, K0, K1, K00, KEQ.
  destruct (blk_range C A2' m4 _ (Z_to_bv 64 buf) (p_wpl v * 4) CK HW4 K1 ltac:(lia)) as [Gb1 _]. rewrite u_Z2bv in Gb1 by lia.
  assert (NEbt : Z_to_bv 64 buf <> Z_to_bv 64 tab) by (intros E; rewrite E in K0; congruence).
  assert (NEtb : Z_to_bv 64 tab <> Z_to_bv 64 buf) by (intros E; apply NEbt; symmetry; exact E).
  assert (Lt2 : live A2' (Z_to_bv 64 tab) = Some 256%Z) by (rewrite (KEQ _ NEtb); exact L1).
  assert (SUB2 : sub_live A1' A2') by (eapply sub_live_new; eassumption).
  assert (SUBA2 : sub_live A A2') by (exact (sub_live_trans _ _ _ SUB1 SUB2)).
  assert (SUBr2 : sub_live Ar A2') by (exact (sub_live_trans _ _ _ SUB SUBA2)).
  assert (Ld2 : live A2' (Z_to_bv 64 (p_data v)) = Some k) by (exact (SUBA2 _ _ Ld)).
  assert (LbA : live A (Z_to_bv 64 buf) = None) by (rewrite <- (LEQ _ NEbt); exact K0).
  assert (Lbr : live Ar (Z_to_bv 64 buf) = None).
  { destruct (live Ar (Z_to_bv 64 buf)) eqn:E; [pose proof (SUB _ _ E) as E'; congruence | reflexivity]. }
  assert (NEbd : Z_to_bv 64 buf <> Z_to_bv 64 (p_data v)) by (intros E; rewrite E in K0; rewrite (SUB1 _ _ Ld) in K0; discriminate).
  assert (PM4' : POSTM C Ar s m m4).
  { eapply POSTM_trans; [exact PM3' |]. apply (POSTM_sub C Ar A1'); [exact SUBr1 |]. eapply POSTM_mono; [| exact PM4]. lia. }
  pose proof (lrwfD_frm C (s - 160) m3 m4 s ret regs pix CK (proj1 PM4) ltac:(lia) ltac:(lia) ltac:(lia) CE3) as CE4.
  assert (RW : rdn SEGS m4 (Z_to_bv 64 (s - 116)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 (p_w v)))).
  { rewrite (lrwfD_rd C _ m2 m3 m4 s tab (s - 116) 4 CK (proj1 PM2) FR3 (proj1 PM4)) by (cbn; lia). exact WH1. }
  assert (RH : rdn SEGS m4 (Z_to_bv 64 (s - 120)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 (p_h v)))).
  { rewrite (lrwfD_rd C _ m2 m3 m4 s tab (s - 120) 4 CK (proj1 PM2) FR3 (proj1 PM4)) by (cbn; lia). exact WH2. }
  assert (RD : rdn SEGS m4 (Z_to_bv 64 (s - 124)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 1))).
  { rewrite (lrwfD_rd C _ m2 m3 m4 s tab (s - 124) 4 CK (proj1 PM2) FR3 (proj1 PM4)) by (cbn; lia). exact WH3. }
  apply (lr_pre_W C Ar A2' _ s (p_w v) (p_h v) (p_wpl v) (p_data v) buf tab k S r5 m4 CK HW4 SUBr2 Ld2 Hk Lrd L0d Gd1 ltac:(lia) Hdm16
           Gb1 ltac:(lia) AL16b Gt1 ltac:(lia) ltac:(lia) Hw32 ltac:(lia) ltac:(lia) ltac:(lia) Hs16
           ltac:(unfold LR_STACK, CALLOC_STACK, ALLOC_STACK; lia) Hhi Hs48 RW RH RD
           ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity) Hres2 ltac:(csr; reflexivity)).
  intros m5 r6 HW5 PM5 OUT5 KP6 P19 P20 P22 P23 P24 P25 P26 P27 Q120 Q160 Q152 Q144 Q136.
  assert (PM5' : POSTM C Ar s m m5) by (exact (POSTM_trans _ _ _ _ _ _ PM4' PM5)).
  pose proof (lrwfD_keep m4 m5 s ret regs pix ltac:(lia) ltac:(intros x Hx; apply OUT5; [lia | unfold scratch; lia]) CE4) as CE5.
  apply (lr_rows_W (Z.to_nat (p_h v - 1)) C Ar A2' m5 _ s (p_w v) (p_data v) (p_wpl v) (p_h v) buf tab k S r6 r6 m5 0
           CK HW5 SUBr2 Ld2 ltac:(lia) Lrd L0d K1 Lbr K00 Lt2 NEbd Gd1 ltac:(lia) Hdm16 Gb1 ltac:(lia) AL16b Gt1 ltac:(lia)
           ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hw32 ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia) ltac:(lia) ltac:(lia) Hhi
           Q120 Q160 Q152 Q144 Q136 (POSTM_refl _ _ _ _) (fun a _ _ => eq_refl) (fun x _ => eq_refl)
           ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity)
           P19 P20 P22 ltac:(rewrite Z.mul_0_r; exact P23) P24 P25 P26 P27).
  intros m7 r7 HW7 PM7 OUT7 KP7 S1 S10.
  assert (PM7' : POSTM C Ar s m m7) by (exact (POSTM_trans _ _ _ _ _ _ PM5' PM7)).
  pose proof (lrwfD_keep m5 m7 s ret regs pix ltac:(lia) ltac:(intros x Hx; apply OUT7; lia) CE5) as CE7.
  apply (W_free16 C A2' m7 _ r7 (Z_to_bv 64 buf) _ (p_wpl v * 4) (s - 160) S CK HW7 S10 K1 K00 S1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(unfold ALLOC_STACK; lia) ltac:(lia)).
  intros A3 m8 vm3 r8 HW8 CS8 L3b LEQ3 PM8 Rm3.
  rewrite with_vmmaps_twice in HW8 |- *.
  assert (SUBr3 : sub_live Ar A3).
  { intros q kq Lq. assert (NE : q <> Z_to_bv 64 buf) by (intros E; subst q; congruence). rewrite (LEQ3 _ NE). exact (SUBr2 _ _ Lq). }
  assert (PM8' : POSTM C Ar s m m8).
  { eapply POSTM_trans; [exact PM7' |]. apply (POSTM_sub C Ar A3); [exact SUBr3 |]. eapply POSTM_mono; [| exact PM8]. lia. }
  pose proof (lrwfD_frm C (s - 160) m7 m8 s ret regs pix CK (proj1 PM8) ltac:(lia) ltac:(lia) ltac:(lia) CE7) as CE8.
  destruct (lr_F al_rom r8 m8 tab Gt1 ltac:(lia) ltac:(csr; reflexivity)) as (r9 & RUN9 & F1 & F10 & AG9).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW8)) | exact (mp_lazy _ (w_pure _ _ _ _ HW8)) | exact RUN9 |].
  assert (Lt3 : live A3 (Z_to_bv 64 tab) = Some 256%Z) by (rewrite (LEQ3 _ NEtb); exact Lt2).
  apply (W_free16 C A3 m8 _ r9 (Z_to_bv 64 tab) _ 256 (s - 160) S CK HW8 F10 Lt3 L00 F1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(unfold ALLOC_STACK; lia) ltac:(lia)).
  intros A4 m9 vm4 r10 HW9 CS10 L4t LEQ4 PM9 Rm4.
  rewrite with_vmmaps_twice in HW9 |- *.
  assert (SUBr4 : sub_live Ar A4).
  { intros q kq Lq. assert (NE : q <> Z_to_bv 64 tab) by (intros E; subst q; congruence). rewrite (LEQ4 _ NE). exact (SUBr3 _ _ Lq). }
  assert (PM9' : POSTM C Ar s m m9).
  { eapply POSTM_trans; [exact PM8' |]. apply (POSTM_sub C Ar A4); [exact SUBr4 |]. eapply POSTM_mono; [| exact PM9]. lia. }
  pose proof (lrwfD_frm C (s - 160) m8 m9 s ret regs pix CK (proj1 PM9) ltac:(lia) ltac:(lia) ltac:(lia) CE8) as CE9.
  destruct (lr_G al_rom r10 m9 s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22)
              (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) (Z_to_bv 64 pix) ltac:(lia) Hret CE9 ltac:(csr; reflexivity))
    as (r11 & RUN11 & G2 & G1 & G10 & G8 & G9 & G18 & G19 & G20 & G21 & G22 & G23 & G24 & G25 & G26 & G27 & AG11).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW9)) | exact (mp_lazy _ (w_pure _ _ _ _ HW9)) | exact RUN11 |].
  assert (KEEPx : forall (q : word) (k' : Z) (x : word), live A q = Some k' -> q <> Z_to_bv 64 (p_data v) -> (u q <= u x < u q + k')%Z -> m9 x = m x).
  { intros q k' x Lq NE Hx. pose proof (u64_range q). pose proof (u64_range x).
    destruct (blk_range C A m md q k' CK HW Lq ltac:(lia)) as [Q1 Q2].
    assert (NEt : q <> Z_to_bv 64 tab) by (intros E; subst q; congruence).
    assert (NEb : q <> Z_to_bv 64 buf) by (intros E; subst q; congruence).
    pose proof (lrw_apart C A m md q _ k' k CK HW Lq Ld NE ltac:(lia) ltac:(lia)) as APd. rewrite u_Z2bv in APd by lia.
    pose proof (lrw_apart C A1' m2 _ q _ k' 256 CK HW2 (SUB1 _ _ Lq) L1 NEt ltac:(lia) ltac:(lia)) as APt. rewrite u_Z2bv in APt by lia.
    pose proof (lrw_apart C A2' m4 _ q _ k' (p_wpl v * 4) CK HW4 (SUBA2 _ _ Lq) K1 NEb ltac:(lia) ltac:(lia)) as APb. rewrite u_Z2bv in APb by lia.
    assert (LA3 : live A3 q = Some k') by (rewrite (LEQ3 _ NEb); exact (SUBA2 _ _ Lq)).
    assert (LA4 : live A4 q = Some k') by (rewrite (LEQ4 _ NEt); exact LA3).
    rewrite (lrwfD_livk A4 m8 m9 q k' x (proj2 PM9) LA4 Hx), (lrwfD_livk A3 m7 m8 q k' x (proj2 PM8) LA3 Hx).
    rewrite OUT7 by lia. rewrite OUT5 by (try unfold scratch; lia).
    rewrite (lrwfD_livk A1' m3 m4 q k' x (proj2 PM4) (SUB1 _ _ Lq) Hx). rewrite FR3 by lia.
    rewrite (lrwfD_livk A _ m2 q k' x (proj2 PM2) Lq Hx). apply MLR_A_out; lia. }
  apply (HK A4 m9 vm4 r11 HW9).
  - apply cs_kept_intro; csr; reflexivity.
  - exact PM9'.
  - intros q. destruct (bv_eq_dec _ q (Z_to_bv 64 tab)) as [Et | Nt].
    + subst q. rewrite L4t. symmetry. exact L0.
    + destruct (bv_eq_dec _ q (Z_to_bv 64 buf)) as [Eb | Nb].
      * subst q. rewrite (LEQ4 _ NEbt), L3b. symmetry. exact LbA.
      * rewrite (LEQ4 _ Nt), (LEQ3 _ Nb), (KEQ _ Nb), (LEQ _ Nt). reflexivity.
  - intros q k' i Lq NE Hi. pose proof (u64_range q). destruct (blk_range C A m md q k' CK HW Lq ltac:(lia)) as [Q1 Q2].
    apply (KEEPx q k'); [exact Lq | exact NE |]. unfold at_. rewrite u_Z2bv by lia. lia.
  - apply (PIXat_frame m); [exact PX |]. intros x Hx. apply (KEEPx (Z_to_bv 64 pix) 64%Z); [exact Lpix | exact NEpd | rewrite u_Z2bv by lia; lia].
  - exact G10.
  - rewrite with_vmmaps_vmmaps in Rm3, Rm4.
    assert (Hb0 : (0 <= bR - alloc_margin (256 * 1) - alloc_margin (p_wpl v * 4))%Z).
    { replace (p_wpl v * 4)%Z with (4 * p_wpl v)%Z by lia. change (256 * 1)%Z with 256%Z. lia. }
    pose proof (Rm4 _ _ (Rm3 _ _ Hrm2 ltac:(lia) Hb0) ltac:(lia) ltac:(lia)) as Rf.
    change (256 * 1)%Z with 256%Z in Rf. replace (p_wpl v * 4)%Z with (4 * p_wpl v)%Z in Rf by lia.
    rewrite !Z.sub_0_r in Rf. replace (kR - 1 - 1)%Z with (kR - 2)%Z in Rf by lia. exact Rf.
Qed.

End WithHip.

End RotLRW.
