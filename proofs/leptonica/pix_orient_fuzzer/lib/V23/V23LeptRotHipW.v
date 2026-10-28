(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic PFLib LeptDefs LeptStructs LeptArith LeptArith2 LeptExecW.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require Import O23LeptRotHip O23LeptRotHipW.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptBase V23LeptRotHip_iface V23LeptRotHip.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Lemma hipw_lmask_rd : forall j, (1 <= j <= 31)%Z ->
  exists bs, rdn SEGS (fun _ => None) (Z_to_bv 64 (0x1f4c4 + 4 * j)) 4 = Some bs /\ length bs = 4%nat.
Proof.
  intros j Hj.
  assert (Hc : (j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6 \/ j = 7 \/ j = 8 \/ j = 9 \/ j = 10 \/ j = 11 \/ j = 12 \/ j = 13 \/ j = 14 \/ j = 15 \/ j = 16 \/
               j = 17 \/ j = 18 \/ j = 19 \/ j = 20 \/ j = 21 \/ j = 22 \/ j = 23 \/ j = 24 \/ j = 25 \/ j = 26 \/ j = 27 \/ j = 28 \/ j = 29 \/ j = 30 \/ j = 31)%Z) by lia.
  repeat (destruct Hc as [Hc|Hc]; [subst j; eexists; split; [vm_compute; reflexivity | reflexivity] |]).
  subst j; eexists; split; [vm_compute; reflexivity | reflexivity].
Qed.

Section RotHipW.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V23Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Ltac hipw_agree AG1 AG2 := eapply regs_agree_trans; [eapply regs_agree_mono; [|exact AG1] | eapply regs_agree_mono; [|exact AG2]];
  intros q Hq; cbn [In] in Hq |- *; intuition.

(* [comment removed for export] *)
Lemma hipw_rd4_blk : forall C A m md (p : word) (k a : Z), Cok C -> W C A m md -> live A p = Some k ->
  (u p <= a)%Z -> (a + 4 <= u p + k)%Z -> (u p + k < 2 ^ 64)%Z ->
  exists (bs : list byte) (v : word), rdn SEGS m (Z_to_bv 64 a) 4 = Some bs /\ bytes_le_to_Z bs = u v.
Proof.
  intros C A m md p k a CK HW L H1 H2 H3. pose proof (u64_range p).
  destruct (rdn_defined SEGS m a 4) as (bs & R & Lb); [lia | cbn; lia | |].
  - intros i Hi. apply (blk_byte C A m md p k (Z_to_bv 64 (a + i)) CK HW L). rewrite u_Z2bv by (cbn in Hi; lia). cbn in Hi. lia.
  - destruct (hipw_le4 bs Lb) as [v Hv]. exists bs, v. split; [exact R | exact Hv].
Qed.

(* [comment removed for export] *)
Lemma hipw_sok_blk : forall C A m md (p : word) (k a : Z) (n : nat), Cok C -> W C A m md -> live A p = Some k ->
  (u p <= a)%Z -> (a + Z.of_nat n <= u p + k)%Z -> (u p + k < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 a) n = true.
Proof.
  intros C A m md p k a n CK HW L H1 H2 H3. pose proof (u64_range p).
  apply (exW_sok_blk SEGS C A m md (u p) k a n p16_segs CK HW); [rewrite zbv_self; exact L | lia | lia | lia | lia].
Qed.

Ltac hipw_sc := rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia.
Ltac hipw_rd :=
  repeat first [ rewrite rdn_wbytes_hit8 by hipw_sc | rewrite rdn_wbytes_out by hipw_sc ];
  reflexivity.
Ltac hipw_out a := pose proof (u64_range a); repeat (rewrite wbytes_outside by hipw_sc); reflexivity.

Lemma MHIP_A_out : forall m s data shift wpl ret regs (a : word), (240 <= s < 2 ^ 64)%Z -> ~ (s - 240 <= u a < s)%Z ->
  MHIP_A m s data shift wpl ret regs a = m a.
Proof.
  intros m s data shift wpl ret regs a Hs Ha. unfold MHIP_A, LOCHIP, FRHIP. hipw_out a.
Qed.

Lemma MHIP_A_cells : forall m s data shift wpl ret regs, (240 <= s < 2 ^ 64)%Z ->
  cellsZ (MHIP_A m s data shift wpl ret regs)
    [(s - 8, ret); (s - 16, getr regs 8); (s - 24, getr regs 9); (s - 32, getr regs 18); (s - 40, getr regs 19); (s - 48, getr regs 20);
     (s - 56, getr regs 21); (s - 64, getr regs 22); (s - 72, getr regs 23); (s - 80, getr regs 24); (s - 88, getr regs 25);
     (s - 96, getr regs 26); (s - 104, getr regs 27)]%Z.
Proof.
  intros m s data shift wpl ret regs Hs. cbn [cellsZ]. unfold MHIP_A, LOCHIP, FRHIP.
  repeat split; hipw_rd.
Qed.

Lemma MHIP_A_rd : forall m s data shift wpl ret regs, (240 <= s < 2 ^ 64)%Z ->
  rdn SEGS (MHIP_A m s data shift wpl ret regs) (Z_to_bv 64 (s - 112)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) /\
  rdn SEGS (MHIP_A m s data shift wpl ret regs) (Z_to_bv 64 (s - 120)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (4 * (wpl - 1)))) /\
  rdn SEGS (MHIP_A m s data shift wpl ret regs) (Z_to_bv 64 (s - 224)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (1 - wpl))) /\
  rdn SEGS (MHIP_A m s data shift wpl ret regs) (Z_to_bv 64 (s - 144)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (4 * shift))) /\
  rdn SEGS (MHIP_A m s data shift wpl ret regs) (Z_to_bv 64 (s - 152)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x1f4c4)) /\
  rdn SEGS (MHIP_A m s data shift wpl ret regs) (Z_to_bv 64 (s - 160)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (4 * shift + 0x1f4c4))).
Proof.
  intros m s data shift wpl ret regs Hs. unfold MHIP_A, LOCHIP, FRHIP.
  repeat split; hipw_rd.
Qed.

Lemma hipw_cell : forall mA m (data wpl h a : Z) (n : nat) bs,
  (forall x : word, ~ (data <= u x < data + 4 * wpl * h)%Z -> m x = mA x) -> (0 <= data)%Z -> (0 <= 4 * wpl * h)%Z ->
  (data + 4 * wpl * h <= a)%Z -> (a + Z.of_nat n < 2 ^ 64)%Z ->
  rdn SEGS mA (Z_to_bv 64 a) n = Some bs -> rdn SEGS m (Z_to_bv 64 a) n = Some bs.
Proof.
  intros mA m data wpl h a n bs FR H0 H1 H2 H3 R. rewrite <- R. apply rdn_ext; [rewrite u_Z2bv by lia; lia |].
  intros x Hx. rewrite u_Z2bv in Hx by lia. apply FR. lia.
Qed.

Lemma hipw_mask : forall C A m md (shift : Z), W C A m md -> (1 <= shift <= 31)%Z ->
  exists (bsm : list byte) (vm : word), rdn SEGS m (Z_to_bv 64 (4 * shift + 0x1f4c4)) 4 = Some bsm /\ bytes_le_to_Z bsm = u vm.
Proof.
  intros C A m md shift HW Hs. destruct (hipw_lmask_rd shift Hs) as (bs & R & Lb). destruct (hipw_le4 bs Lb) as [v Hv].
  exists bs, v. split; [| exact Hv]. replace (4 * shift + 0x1f4c4)%Z with (0x1f4c4 + 4 * shift)%Z by lia.
  rewrite <- p16_segs. rewrite (W_rdn_ro C A m md _ 4 HW); [rewrite p16_segs; exact R | cbv [ll_ro LLU16 fst snd]; lia | cbv [ll_ro LLU16 fst snd]; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia].
Qed.

(* [comment removed for export] *)
Lemma hip_inner_W : forall (n : nat) C Ar A mA md (s data wpl h kd line shift : Z) (S : TSet) (r0 r : bvmap 5 word) (m : word -> option byte) (k : Z),
  Cok C -> W C A m md -> sub_live Ar A ->
  live A (Z_to_bv 64 data) = Some kd -> (4 * wpl * h <= kd)%Z -> live Ar (Z_to_bv 64 data) = None -> live (c_A0 C) (Z_to_bv 64 data) = None ->
  (4096 <= data)%Z -> (data + 4 * wpl * h < 2 ^ 48)%Z -> (2 <= wpl < 2 ^ 25)%Z -> (1 <= h)%Z -> (1 <= shift <= 31)%Z ->
  (data <= line)%Z -> (line + 4 * wpl <= data + 4 * wpl * h)%Z ->
  (0 <= k)%Z -> (Z.of_nat n = wpl - 2 - k)%Z ->
  POSTM C Ar s mA m -> (forall a : word, ~ (data <= u a < data + 4 * wpl * h)%Z -> m a = mA a) ->
  regs_agree (fun x => In x [1; 7; 10; 12; 25; 27]%list) r0 r ->
  getr r 7 = Z_to_bv 64 (k + 1 - wpl) -> getr r 10 = Z_to_bv 64 (line + 4 * (wpl - 1 - k)) -> getr r 25 = Z_to_bv 64 (line + 4 * (wpl - 1 - k)) ->
  getr r 11 = Z_to_bv 64 shift -> getr r 9 = Z_to_bv 64 5 -> getr r 18 = Z_to_bv 64 0 -> getr r 20 = Z_to_bv 64 4 -> getr r 30 = Z_to_bv 64 shift ->
  (forall m' r', W C A m' md -> POSTM C Ar s mA m' -> (forall a : word, ~ (data <= u a < data + 4 * wpl * h)%Z -> m' a = mA a) ->
     regs_agree (fun x => In x [1; 7; 10; 12; 25; 27]%list) r0 r' ->
     getr r' 1 = Z_to_bv 64 line -> getr r' 10 = Z_to_bv 64 line -> getr r' 25 = Z_to_bv 64 line ->
     realizes SEGS (mkCfg (mkst r' (Z_to_bv 64 0x879b0) m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst r (Z_to_bv 64 0x87878) m al_rom) md) S.
Proof.
  induction n as [|n IH]; intros C Ar A mA md s data wpl h kd line shift S r0 r m k CK HW SUB Ld Hkd Lrd L0d Hd1 Hd2 Hw Hh Hsh Hl1 Hl2 Hk Hn
    PM FR AG R7 R10 R25 R11 R9 R18 R20 R30 K;
  (destruct (blk_range C A m md (Z_to_bv 64 data) kd CK HW Ld ltac:(nia)) as [Gd1 Gd2]; rewrite u_Z2bv in Gd1, Gd2 by lia;
   pose proof CK as [CK1 CK2 CK3 CK4 CK5]; pose proof LSTK_val as HLS;
   assert (Hmw : (0 < 4 * wpl * h)%Z) by nia;
   destruct (hipw_rd4_blk C A m md (Z_to_bv 64 data) kd (line + 4 * (wpl - 2 - k)) CK HW Ld) as (bs5 & v5 & R5 & E5);
     [rewrite u_Z2bv by lia; lia | rewrite u_Z2bv by lia; lia | rewrite u_Z2bv by lia; lia | ];
   destruct (hipw_rd4_blk C A m md (Z_to_bv 64 data) kd (line + 4 * (wpl - 1 - k)) CK HW Ld) as (bs2 & v2 & R2 & E2);
     [rewrite u_Z2bv by lia; lia | rewrite u_Z2bv by lia; lia | rewrite u_Z2bv by lia; lia | ];
   assert (SOK : store_ok SEGS m (Z_to_bv 64 (line + 4 * (wpl - 1 - k))) 4 = true)
     by (apply (hipw_sok_blk C A m md (Z_to_bv 64 data) kd _ 4 CK HW Ld); rewrite ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia)).
  - destruct (hip_I al_rom true r m line wpl shift k bs5 bs2 v5 v2 Hw Hsh Hk ltac:(cbn; lia) ltac:(lia) ltac:(lia) R5 E5 R2 E2 SOK
                R7 R10 R25 R11 R9 R18 R20 R30) as (r' & wv & RUN & P7 & P1 & P10 & P25 & AG').
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN |].
    destruct (WP_blk C Ar A mA m md (Z_to_bv 64 data) (Z_to_bv 64 (line + 4 * (wpl - 1 - k))) kd (word_to_le_bytes 4 wv) s CK (conj HW PM) Ld Lrd L0d SUB)
      as [HW' PM']; [rewrite !u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, !u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia |].
    apply K; [exact HW' | exact PM' | | hipw_agree AG AG' | | | ].
    + intros a Ha. rewrite wbytes_outside; [apply FR; exact Ha | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia |].
      pose proof (u64_range a). rewrite length_N_to_le_bytes, u_Z2bv by lia. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
    + rewrite P1. f_equal; lia.
    + rewrite P10. f_equal; lia.
    + rewrite P25. f_equal; lia.
  - destruct (hip_I al_rom false r m line wpl shift k bs5 bs2 v5 v2 Hw Hsh Hk ltac:(cbn; lia) ltac:(lia) ltac:(lia) R5 E5 R2 E2 SOK
                R7 R10 R25 R11 R9 R18 R20 R30) as (r' & wv & RUN & P7 & P1 & P10 & P25 & AG').
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN |].
    destruct (WP_blk C Ar A mA m md (Z_to_bv 64 data) (Z_to_bv 64 (line + 4 * (wpl - 1 - k))) kd (word_to_le_bytes 4 wv) s CK (conj HW PM) Ld Lrd L0d SUB)
      as [HW' PM']; [rewrite !u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, !u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia |].
    apply (IH C Ar A mA md s data wpl h kd line shift S r0 r' _ (k + 1)%Z CK HW' SUB Ld Hkd Lrd L0d Hd1 Hd2 Hw Hh Hsh Hl1 Hl2 ltac:(lia) ltac:(lia) PM');
      [ | hipw_agree AG AG' | | | | | | | | | exact K ].
    + intros a Ha. rewrite wbytes_outside; [apply FR; exact Ha | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia |].
      pose proof (u64_range a). rewrite length_N_to_le_bytes, u_Z2bv by lia. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
    + rewrite P7. f_equal; lia.
    + rewrite P10. f_equal; lia.
    + rewrite P25. f_equal; lia.
    + rewrite (AG' 11) by (cbn [In]; intuition discriminate). exact R11.
    + rewrite (AG' 9) by (cbn [In]; intuition discriminate). exact R9.
    + rewrite (AG' 18) by (cbn [In]; intuition discriminate). exact R18.
    + rewrite (AG' 20) by (cbn [In]; intuition discriminate). exact R20.
    + rewrite (AG' 30) by (cbn [In]; intuition discriminate). exact R30.
Qed.

Ltac hipw_in := cbn [In]; repeat (first [left; reflexivity | right]).
Ltac hipw_ni := cbn [In]; intuition discriminate.

Lemma hipw_pre_F : forall C Ar A mA md (s data wpl h shift kd i : Z) (S : TSet) (r : bvmap 5 word) (m : word -> option byte),
  Cok C -> W C A m md -> sub_live Ar A ->
  live A (Z_to_bv 64 data) = Some kd -> (4 * wpl * h <= kd)%Z -> live Ar (Z_to_bv 64 data) = None -> live (c_A0 C) (Z_to_bv 64 data) = None ->
  (4096 <= data)%Z -> (data mod 4 = 0)%Z -> (1 <= wpl < 2 ^ 25)%Z -> (1 <= h < 2 ^ 31)%Z -> (4 * wpl * h <= 2 ^ 26)%Z -> (1 <= shift <= 31)%Z ->
  (data + 4 * wpl * h <= s - 240)%Z -> (4096 + 240 <= s < 2 ^ 48)%Z -> (0 <= i < h)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 112)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  rdn SEGS m (Z_to_bv 64 (s - 120)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (4 * (wpl - 1)))) ->
  rdn SEGS m (Z_to_bv 64 (s - 224)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (1 - wpl))) ->
  POSTM C Ar s mA m -> (forall a : word, ~ (data <= u a < data + 4 * wpl * h)%Z -> m a = mA a) ->
  getr r 2 = Z_to_bv 64 (s - 240) -> getr r 8 = Z_to_bv 64 (wpl * i) -> getr r 9 = Z_to_bv 64 5 -> getr r 13 = Z_to_bv 64 wpl ->
  getr r 14 = Z_to_bv 64 i -> getr r 15 = Z_to_bv 64 0 -> getr r 16 = Z_to_bv 64 h -> getr r 17 = Z_to_bv 64 wpl ->
  getr r 19 = Z_to_bv 64 0 -> getr r 20 = Z_to_bv 64 4 -> getr r 21 = Z_to_bv 64 data -> getr r 22 = Z_to_bv 64 (wpl - 1) ->
  getr r 23 = Z_to_bv 64 0 -> getr r 24 = Z_to_bv 64 (4 * (wpl - 1)) -> getr r 26 = Z_to_bv 64 shift ->
  getr r 29 = Z_to_bv 64 (wpl - 1) -> getr r 30 = Z_to_bv 64 shift -> getr r 31 = Z_to_bv 64 0 ->
  (forall m' r', W C A m' md -> POSTM C Ar s mA m' -> (forall a : word, ~ (data <= u a < data + 4 * wpl * h)%Z -> m' a = mA a) ->
     regs_agree (fun x => In x [1; 7; 10; 11; 12; 18; 25; 27]%list) r r' ->
     getr r' 1 = Z_to_bv 64 (data + 4 * (wpl * i)) -> getr r' 10 = Z_to_bv 64 (data + 4 * (wpl * i)) ->
     getr r' 25 = Z_to_bv 64 (data + 4 * (wpl * i)) -> getr r' 11 = Z_to_bv 64 shift ->
     realizes SEGS (mkCfg (mkst r' (Z_to_bv 64 0x879b0) m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst r (Z_to_bv 64 0x877c4) m al_rom) md) S.
Proof.
  intros C Ar A mA md s data wpl h shift kd i S r m CK HW SUB Ld Hkd Lrd L0d Hd1 Hd4 Hw Hh Hmw Hsh Hds Hs Hi C112 C120 C224 PM FR
    R2 R8 R9 R13 R14 R15 R16 R17 R19 R20 R21 R22 R23 R24 R26 R29 R30 R31 K.
  assert (Hrow : (data <= data + 4 * (wpl * i))%Z /\ (data + 4 * (wpl * i) + 4 * wpl <= data + 4 * wpl * h)%Z) by nia.
  destruct (Z.eq_dec wpl 1) as [W1|W2].
  - destruct (hip_R1 al_rom r m s data wpl h shift i Hs W1 Hsh Hi Hmw Hd1 ltac:(lia) C112 C120
                R2 R8 R9 R13 R14 R15 R16 R17 R19 R20 R21 R22 R23 R24 R26 R29 R30 R31) as (r1 & RUN & P1 & P10 & P25 & P11 & AG1).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN |].
    exact (K m r1 HW PM FR AG1 P1 P10 P25 P11).
  - destruct (hip_R2 al_rom r m s data wpl h shift i Hs ltac:(lia) Hsh Hi Hmw Hd1 ltac:(lia) Hd4 C112 C120 C224
                R2 R8 R9 R13 R14 R15 R16 R17 R19 R20 R21 R22 R23 R24 R26 R29 R30 R31) as (r1 & RUN & P7 & P10 & P25 & P11 & P18 & AG1).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN |].
    apply (hip_inner_W (Z.to_nat (wpl - 2)) C Ar A mA md s data wpl h kd (data + 4 * (wpl * i)) shift S r1 r1 m 0 CK HW SUB Ld Hkd Lrd L0d
             Hd1 ltac:(lia) ltac:(lia) ltac:(lia) Hsh ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia) PM FR (regs_agree_refl _ _)).
    + rewrite P7. f_equal; lia.
    + rewrite P10. f_equal; lia.
    + rewrite P25. f_equal; lia.
    + exact P11.
    + rewrite (AG1 9) by hipw_ni. exact R9.
    + exact P18.
    + rewrite (AG1 20) by hipw_ni. exact R20.
    + rewrite (AG1 30) by hipw_ni. exact R30.
    + intros m' r' HW' PM' FR' AG' Q1 Q10 Q25. apply K; [exact HW' | exact PM' | exact FR' | hipw_agree AG1 AG' | exact Q1 | exact Q10 | exact Q25 |].
      rewrite (AG' 11) by hipw_ni. exact P11.
Qed.

(* [comment removed for export] *)
Lemma hip_row_W : forall (n : nat) C Ar A mA md (s data wpl h shift kd : Z) (S : TSet) (r0 r : bvmap 5 word) (m : word -> option byte) (i : Z),
  Cok C -> W C A m md -> sub_live Ar A ->
  live A (Z_to_bv 64 data) = Some kd -> (4 * wpl * h <= kd)%Z -> live Ar (Z_to_bv 64 data) = None -> live (c_A0 C) (Z_to_bv 64 data) = None ->
  (4096 <= data)%Z -> (1 <= wpl < 2 ^ 25)%Z -> (1 <= h < 2 ^ 31)%Z -> (4 * wpl * h <= 2 ^ 26)%Z -> (1 <= shift <= 31)%Z ->
  (data + 4 * wpl * h <= s - 240)%Z -> (data mod 4 = 0)%Z -> (data + 4 * wpl * h <= 0x1f4c4 \/ 0x1f4c4 + 128 <= data)%Z ->
  (4096 + 240 <= s < 2 ^ 48)%Z ->
  (0 <= i)%Z -> (Z.of_nat n = h - 1 - i)%Z ->
  rdn SEGS mA (Z_to_bv 64 (s - 112)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  rdn SEGS mA (Z_to_bv 64 (s - 120)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (4 * (wpl - 1)))) ->
  rdn SEGS mA (Z_to_bv 64 (s - 224)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (1 - wpl))) ->
  rdn SEGS mA (Z_to_bv 64 (s - 144)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (4 * shift))) ->
  rdn SEGS mA (Z_to_bv 64 (s - 152)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x1f4c4)) ->
  rdn SEGS mA (Z_to_bv 64 (s - 160)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (4 * shift + 0x1f4c4))) ->
  POSTM C Ar s mA m -> (forall a : word, ~ (data <= u a < data + 4 * wpl * h)%Z -> m a = mA a) ->
  (forall x, In x [2; 3; 4; 9; 13; 15; 16; 17; 19; 20; 21; 22; 23; 24; 26; 29; 30; 31]%list -> getr r x = getr r0 x) ->
  getr r0 2 = Z_to_bv 64 (s - 240) -> getr r0 9 = Z_to_bv 64 5 -> getr r0 13 = Z_to_bv 64 wpl -> getr r0 15 = Z_to_bv 64 0 ->
  getr r0 16 = Z_to_bv 64 h -> getr r0 17 = Z_to_bv 64 wpl -> getr r0 19 = Z_to_bv 64 0 -> getr r0 20 = Z_to_bv 64 4 ->
  getr r0 21 = Z_to_bv 64 data -> getr r0 22 = Z_to_bv 64 (wpl - 1) -> getr r0 23 = Z_to_bv 64 0 -> getr r0 24 = Z_to_bv 64 (4 * (wpl - 1)) ->
  getr r0 26 = Z_to_bv 64 shift -> getr r0 29 = Z_to_bv 64 (wpl - 1) -> getr r0 30 = Z_to_bv 64 shift -> getr r0 31 = Z_to_bv 64 0 ->
  getr r 14 = Z_to_bv 64 i -> getr r 8 = Z_to_bv 64 (wpl * i) ->
  (forall m' r', W C A m' md -> POSTM C Ar s mA m' -> (forall a : word, ~ (data <= u a < data + 4 * wpl * h)%Z -> m' a = mA a) ->
     (forall x, In x [2; 3; 4; 9; 13; 15; 16; 17; 19; 20; 21; 22; 23; 24; 26; 29; 30; 31]%list -> getr r' x = getr r0 x) ->
     realizes SEGS (mkCfg (mkst r' (Z_to_bv 64 0x87b80) m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst r (Z_to_bv 64 0x877c4) m al_rom) md) S.
Proof.
  induction n as [|n IH]; intros C Ar A mA md s data wpl h shift kd S r0 r m i CK HW SUB Ld Hkd Lrd L0d Hd1 Hw Hh Hmw Hsh Hds Hd4 Htb Hs Hi Hn
    C112 C120 C224 C144 C152 C160 PM FR KP E2 E9 E13 E15 E16 E17 E19 E20 E21 E22 E23 E24 E26 E29 E30 E31 R14 R8 K;
  (pose proof CK as [CK1 CK2 CK3 CK4 CK5]; pose proof LSTK_val as HLS;
   destruct (blk_range C A m md (Z_to_bv 64 data) kd CK HW Ld ltac:(nia)) as [Gd1 Gd2]; rewrite u_Z2bv in Gd1, Gd2 by lia;
   assert (Hrow : (data <= data + 4 * (wpl * i))%Z /\ (data + 4 * (wpl * i) + 4 * wpl <= data + 4 * wpl * h)%Z) by nia;
   assert (Hm0 : (0 <= 4 * wpl * h)%Z) by nia;
   assert (Q2 : getr r 2 = Z_to_bv 64 (s - 240)) by (rewrite (KP 2) by hipw_in; exact E2);
   assert (Q9 : getr r 9 = Z_to_bv 64 5) by (rewrite (KP 9) by hipw_in; exact E9);
   assert (Q13 : getr r 13 = Z_to_bv 64 wpl) by (rewrite (KP 13) by hipw_in; exact E13);
   assert (Q15 : getr r 15 = Z_to_bv 64 0) by (rewrite (KP 15) by hipw_in; exact E15);
   assert (Q16 : getr r 16 = Z_to_bv 64 h) by (rewrite (KP 16) by hipw_in; exact E16);
   assert (Q17 : getr r 17 = Z_to_bv 64 wpl) by (rewrite (KP 17) by hipw_in; exact E17);
   assert (Q19 : getr r 19 = Z_to_bv 64 0) by (rewrite (KP 19) by hipw_in; exact E19);
   assert (Q20 : getr r 20 = Z_to_bv 64 4) by (rewrite (KP 20) by hipw_in; exact E20);
   assert (Q21 : getr r 21 = Z_to_bv 64 data) by (rewrite (KP 21) by hipw_in; exact E21);
   assert (Q22 : getr r 22 = Z_to_bv 64 (wpl - 1)) by (rewrite (KP 22) by hipw_in; exact E22);
   assert (Q23 : getr r 23 = Z_to_bv 64 0) by (rewrite (KP 23) by hipw_in; exact E23);
   assert (Q24 : getr r 24 = Z_to_bv 64 (4 * (wpl - 1))) by (rewrite (KP 24) by hipw_in; exact E24);
   assert (Q26 : getr r 26 = Z_to_bv 64 shift) by (rewrite (KP 26) by hipw_in; exact E26);
   assert (Q29 : getr r 29 = Z_to_bv 64 (wpl - 1)) by (rewrite (KP 29) by hipw_in; exact E29);
   assert (Q30 : getr r 30 = Z_to_bv 64 shift) by (rewrite (KP 30) by hipw_in; exact E30);
   assert (Q31 : getr r 31 = Z_to_bv 64 0) by (rewrite (KP 31) by hipw_in; exact E31);
   pose proof (hipw_cell mA m data wpl h (s - 112) 8 _ FR ltac:(lia) Hm0 ltac:(lia) ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia) C112) as M112;
   pose proof (hipw_cell mA m data wpl h (s - 120) 8 _ FR ltac:(lia) Hm0 ltac:(lia) ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia) C120) as M120;
   pose proof (hipw_cell mA m data wpl h (s - 224) 8 _ FR ltac:(lia) Hm0 ltac:(lia) ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia) C224) as M224;
   apply (hipw_pre_F C Ar A mA md s data wpl h shift kd i S r m CK HW SUB Ld Hkd Lrd L0d Hd1 Hd4 Hw Hh Hmw Hsh Hds Hs ltac:(lia) M112 M120 M224 PM FR
            Q2 R8 Q9 Q13 R14 Q15 Q16 Q17 Q19 Q20 Q21 Q22 Q23 Q24 Q26 Q29 Q30 Q31);
   intros m1 r1 HW1 PM1 FR1 AG1 P1 P10 P25 P11;
   destruct (hipw_rd4_blk C A m1 md (Z_to_bv 64 data) kd (data + 4 * (wpl * i)) CK HW1 Ld) as (bs0 & v0 & B0 & V0);
     [rewrite u_Z2bv by lia; lia | rewrite u_Z2bv by lia; lia | rewrite u_Z2bv by lia; lia | ];
   destruct (hipw_mask C A m1 md shift HW1 Hsh) as (bsm & vm & BM & VM);
   assert (SOK : store_ok SEGS m1 (Z_to_bv 64 (data + 4 * (wpl * i))) 4 = true)
     by (apply (hipw_sok_blk C A m1 md (Z_to_bv 64 data) kd _ 4 CK HW1 Ld); rewrite ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia);
   pose proof (hipw_cell mA m1 data wpl h (s - 144) 8 _ FR1 ltac:(lia) Hm0 ltac:(lia) ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia) C144) as N144;
   pose proof (hipw_cell mA m1 data wpl h (s - 152) 8 _ FR1 ltac:(lia) Hm0 ltac:(lia) ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia) C152) as N152;
   pose proof (hipw_cell mA m1 data wpl h (s - 160) 8 _ FR1 ltac:(lia) Hm0 ltac:(lia) ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia) C160) as N160;
   assert (G2 : getr r1 2 = Z_to_bv 64 (s - 240)) by (rewrite (AG1 2) by hipw_ni; exact Q2);
   assert (G8 : getr r1 8 = Z_to_bv 64 (wpl * i)) by (rewrite (AG1 8) by hipw_ni; exact R8);
   assert (G9 : getr r1 9 = Z_to_bv 64 5) by (rewrite (AG1 9) by hipw_ni; exact Q9);
   assert (G13 : getr r1 13 = Z_to_bv 64 wpl) by (rewrite (AG1 13) by hipw_ni; exact Q13);
   assert (G14 : getr r1 14 = Z_to_bv 64 i) by (rewrite (AG1 14) by hipw_ni; exact R14);
   assert (G16 : getr r1 16 = Z_to_bv 64 h) by (rewrite (AG1 16) by hipw_ni; exact Q16);
   assert (G17 : getr r1 17 = Z_to_bv 64 wpl) by (rewrite (AG1 17) by hipw_ni; exact Q17);
   assert (G19 : getr r1 19 = Z_to_bv 64 0) by (rewrite (AG1 19) by hipw_ni; exact Q19);
   assert (G20 : getr r1 20 = Z_to_bv 64 4) by (rewrite (AG1 20) by hipw_ni; exact Q20);
   assert (G21 : getr r1 21 = Z_to_bv 64 data) by (rewrite (AG1 21) by hipw_ni; exact Q21);
   assert (G26 : getr r1 26 = Z_to_bv 64 shift) by (rewrite (AG1 26) by hipw_ni; exact Q26);
   assert (G30 : getr r1 30 = Z_to_bv 64 shift) by (rewrite (AG1 30) by hipw_ni; exact Q30)).
  - destruct (hip_F al_rom true r1 m1 s data wpl h shift i bs0 bsm v0 vm Hs Hw Hsh ltac:(lia) ltac:(cbn; lia) Hmw Hd1 Hds Hd4 Htb B0 V0 N144 N152 N160 BM VM SOK
                G2 P1 P10 P25 P11 G8 G9 G13 G14 G16 G17 G19 G20 G21 G26 G30) as (r2 & w1 & w2 & RUN & P8 & P14 & AG2).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN |].
    destruct (WP_blk C Ar A mA m1 md (Z_to_bv 64 data) (Z_to_bv 64 (data + 4 * (wpl * i))) kd (word_to_le_bytes 4 w1) s CK (conj HW1 PM1) Ld Lrd L0d SUB)
      as [HWa PMa]; [rewrite !u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, !u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia |].
    destruct (WP_blk C Ar A mA _ md (Z_to_bv 64 data) (Z_to_bv 64 (data + 4 * (wpl * i))) kd (word_to_le_bytes 4 w2) s CK (conj HWa PMa) Ld Lrd L0d SUB)
      as [HWb PMb]; [rewrite !u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, !u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia |].
    apply K; [exact HWb | exact PMb | |].
    + intros a Ha. pose proof (u64_range a).
      rewrite !wbytes_outside; [apply FR1; exact Ha | rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia .. ].
    + intros x Hx. rewrite (AG2 x), (AG1 x); [apply KP; exact Hx | |];
        intros Hc; cbn [In] in Hx, Hc; intuition (subst; discriminate).
  - destruct (hip_F al_rom false r1 m1 s data wpl h shift i bs0 bsm v0 vm Hs Hw Hsh ltac:(lia) ltac:(cbn; lia) Hmw Hd1 Hds Hd4 Htb B0 V0 N144 N152 N160 BM VM SOK
                G2 P1 P10 P25 P11 G8 G9 G13 G14 G16 G17 G19 G20 G21 G26 G30) as (r2 & w1 & w2 & RUN & P8 & P14 & AG2).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN |].
    destruct (WP_blk C Ar A mA m1 md (Z_to_bv 64 data) (Z_to_bv 64 (data + 4 * (wpl * i))) kd (word_to_le_bytes 4 w1) s CK (conj HW1 PM1) Ld Lrd L0d SUB)
      as [HWa PMa]; [rewrite !u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, !u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia |].
    destruct (WP_blk C Ar A mA _ md (Z_to_bv 64 data) (Z_to_bv 64 (data + 4 * (wpl * i))) kd (word_to_le_bytes 4 w2) s CK (conj HWa PMa) Ld Lrd L0d SUB)
      as [HWb PMb]; [rewrite !u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, !u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia |].
    apply (IH C Ar A mA md s data wpl h shift kd S r0 r2 _ (i + 1)%Z CK HWb SUB Ld Hkd Lrd L0d Hd1 Hw Hh Hmw Hsh Hds Hd4 Htb Hs ltac:(lia) ltac:(lia)
             C112 C120 C224 C144 C152 C160 PMb); [ | | exact E2 | exact E9 | exact E13 | exact E15 | exact E16 | exact E17 | exact E19 | exact E20
             | exact E21 | exact E22 | exact E23 | exact E24 | exact E26 | exact E29 | exact E30 | exact E31 | exact P14 | exact P8 | exact K ].
    + intros a Ha. pose proof (u64_range a).
      rewrite !wbytes_outside; [apply FR1; exact Ha | rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia .. ].
    + intros x Hx. rewrite (AG2 x), (AG1 x); [apply KP; exact Hx | |];
        intros Hc; cbn [In] in Hx, Hc; intuition (subst; discriminate).
Qed.

Lemma hipw_tab_apart : forall C A m md (d k : Z), Cok C -> W C A m md -> live A (Z_to_bv 64 d) = Some k ->
  (0 <= d)%Z -> (0 < k)%Z -> (d + k < 2 ^ 64)%Z -> (d + k <= 0x1f4c4 \/ 0x1f4c4 + 128 <= d)%Z.
Proof.
  intros C A m md d k CK HW L1 Hd Hk Hdk.
  destruct (Z_le_gt_dec (d + k) 0x1f4c4) as [X|X]; [left; exact X|].
  destruct (Z_le_gt_dec (0x1f4c4 + 128) d) as [Y|Y]; [right; exact Y|].
  exfalso.
  destruct (blk_byte C A m md (Z_to_bv 64 d) k (Z_to_bv 64 (Z.max d 0x1f4c4)) CK HW L1) as (_ & _ & NI & _);
    [rewrite !u_Z2bv by lia; lia |].
  apply NI. rewrite u_Z2bv by lia. unfold inZ. cbv [ll_img LLU16 fst snd]. lia.
Qed.

(* [comment removed for export] *)
Theorem rasteropHipLow_W : rasteropHipLow_contract.
Proof.
  unfold rasteropHipLow_contract.
  intros C Ar A m md regs s data h wpl shift kd ret S CK HW SUB H2 Hs16 Hlo Hhi H1 Hret H10 H11 H12 H13 H14 H15 H16
    Hd Hsh Hw Hh Hmw Ld Hkd Lrd L0d K.
  pose proof CK as [CK1 CK2 CK3 CK4 CK5]. pose proof LSTK_val as HLS. unfold HIP_STACK in Hlo.
  pose proof (u64_range (c_sp0 C)) as Hsp.
  assert (Hmw' : (0 < 4 * wpl * h)%Z) by nia.
  destruct (blk_range C A m md (Z_to_bv 64 data) kd CK HW Ld ltac:(nia)) as [Gd1 Gd2]. rewrite u_Z2bv in Gd1, Gd2 by lia.
  assert (Hd16 : (data mod 16 = 0)%Z).
  { destruct (ai_live_hull A m (m_vmmaps md) _ kd (w_inv _ _ _ _ HW) Ld) as (_ & X & _). rewrite u_Z2bv in X by lia. exact X. }
  assert (Htb : (data + 4 * wpl * h <= 0x1f4c4 \/ 0x1f4c4 + 128 <= data)%Z).
  { destruct (hipw_tab_apart C A m md data kd CK HW Ld ltac:(lia) ltac:(lia) ltac:(lia)) as [X|X]; [left; nia | right; exact X]. }
  assert (Hw25 : (wpl < 2 ^ 25)%Z) by nia. assert (Hh31 : (h < 2 ^ 31)%Z) by nia.
  assert (SOK : store_ok SEGS m (Z_to_bv 64 (s - 240)) 240 = true) by (apply (W_sok_win C A m md (s - 240) 240 CK HW); cbn [Z.of_nat]; lia).
  replace (Z_to_bv 64 PC_rasteropHipLow) with (Z_to_bv 64 PC_rasteropHipLowS) by reflexivity.
  destruct (hip_A al_rom regs m s data wpl h shift ret ltac:(lia) Hsh ltac:(lia) ltac:(lia) ltac:(lia) SOK H2 H1 H10 H11 H12 H13 H14 H15 H16)
    as (r1 & RUN & Z2 & Z8 & Z9 & Z13 & Z14 & Z15 & Z16 & Z17 & Z19 & Z20 & Z21 & Z22 & Z23 & Z24 & Z26 & Z29 & Z30 & Z31 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN |].
  set (mA := MHIP_A m s data shift wpl ret regs).
  assert (HWA : W C A mA md).
  { subst mA. unfold MHIP_A, LOCHIP, FRHIP.
    repeat (apply W_store_win; [exact CK | | rewrite u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia]).
    exact HW. }
  assert (PMA : POSTM C Ar s m mA).
  { apply (POSTM_sub C Ar A); [exact SUB|]. apply (POSTM_range C A m md mA (s - 240) s s CK HW); [| lia | lia | lia].
    intros a Ha. subst mA. apply MHIP_A_out; [lia | exact Ha]. }
  destruct (MHIP_A_rd m s data shift wpl ret regs ltac:(lia)) as (C112 & C120 & C224 & C144 & C152 & C160). fold mA in C112, C120, C224, C144, C152, C160.
  pose proof (MHIP_A_cells m s data shift wpl ret regs ltac:(lia)) as CE. fold mA in CE.
  apply (hip_row_W (Z.to_nat (h - 1)) C Ar A mA md s data wpl h shift kd S r1 r1 mA 0 CK HWA SUB Ld ltac:(lia) Lrd L0d
           ltac:(lia) ltac:(lia) ltac:(lia) ltac:(nia) Hsh ltac:(nia) ltac:(clear - Hd16; Z.div_mod_to_equations; lia) Htb ltac:(lia) ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia)
           C112 C120 C224 C144 C152 C160 (POSTM_refl C Ar s mA) (fun a _ => eq_refl) (fun x _ => eq_refl)
           Z2 Z9 Z13 Z15 Z16 Z17 Z19 Z20 Z21 Z22 Z23 Z24 Z26 Z29 Z30 Z31 Z14 ltac:(rewrite Z.mul_0_r; exact Z8)).
  intros m2 r2 HW2 PM2 FR2 KP2.
  assert (E2 : getr r2 2 = Z_to_bv 64 (s - 240)) by (rewrite (KP2 2) by hipw_in; exact Z2).
  assert (CE2 : cellsZ m2 [(s - 8, ret); (s - 16, getr regs 8); (s - 24, getr regs 9); (s - 32, getr regs 18); (s - 40, getr regs 19);
                           (s - 48, getr regs 20); (s - 56, getr regs 21); (s - 64, getr regs 22); (s - 72, getr regs 23); (s - 80, getr regs 24);
                           (s - 88, getr regs 25); (s - 96, getr regs 26); (s - 104, getr regs 27)]%Z).
  { apply (cellsZ_out mA m2 data (data + 4 * wpl * h)); [exact FR2 | | exact CE].
    repeat constructor; cbn [fst]; nia. }
  destruct (hip_E al_rom r2 m2 s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22)
              (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) ltac:(lia) Hret CE2 E2)
    as (r3 & RUN3 & Q2 & Q1 & Q8 & Q9 & Q18 & Q19 & Q20 & Q21 & Q22 & Q23 & Q24 & Q25 & Q26 & Q27 & AG3).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact RUN3 |].
  apply K; [exact HW2 | | exact (POSTM_trans C Ar s m mA m2 PMA PM2) | ].
  - apply cs_kept_intro; try assumption.
    + rewrite Q2, H2. reflexivity.
    + rewrite (AG3 3) by hipw_ni. rewrite (KP2 3) by hipw_in. rewrite (AG1 3) by hipw_ni. reflexivity.
    + rewrite (AG3 4) by hipw_ni. rewrite (KP2 4) by hipw_in. rewrite (AG1 4) by hipw_ni. reflexivity.
  - intros a Hsc Hrow. rewrite (FR2 a ltac:(intros X; apply Hrow; lia)). subst mA. apply MHIP_A_out; [lia |].
    unfold scratch in Hsc. lia.
Qed.

End RotHipW.
