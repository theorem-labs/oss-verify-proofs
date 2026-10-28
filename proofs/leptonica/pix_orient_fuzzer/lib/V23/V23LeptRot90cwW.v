(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic PFLib LeptDefs LeptStructs LeptArith LeptArith2.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require Import O23LeptCmap2 O23LeptRot90cwW.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require SeqExec.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptBase V23LeptRot90cw.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section R90W.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V23Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Lemma r90w_rd4_blk : forall C A m md (p : word) (k a : Z), Cok C -> W C A m md -> live A p = Some k ->
  (u p <= a)%Z -> (a + 4 <= u p + k)%Z -> (u p + k < 2 ^ 64)%Z ->
  exists (bs : list byte) (v : word), rdn SEGS m (Z_to_bv 64 a) 4 = Some bs /\ bytes_le_to_Z bs = u v.
Proof using PINS.
  intros C A m md p k a CK HW L Ha Hk Hpk. pose proof (u64_range p) as Up.
  assert (D : forall i, (0 <= i < Z.of_nat 4)%Z -> m (Z_to_bv 64 (a + i)) <> None).
  { intros i Hi.
    destruct (blk_byte C A m md p k (Z_to_bv 64 (a + i)) CK HW L ltac:(rewrite u_Z2bv by lia; lia)) as (_ & D & _).
    exact D. }
  destruct (rdn_defined' SEGS m a 4 ltac:(lia) ltac:(lia) D) as (bs & R & Len).
  destruct (r90w_le4 bs Len) as [v Hv]. exists bs, v. split; [exact R | exact Hv].
Qed.

Lemma r90w_sok_blk : forall C A m md (p : word) (k a : Z) (n : nat), Cok C -> W C A m md -> live A p = Some k ->
  (u p <= a)%Z -> (a + Z.of_nat n <= u p + k)%Z -> (u p + k < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 a) n = true.
Proof using P16 PINS.
  intros C A m md p k a n CK HW L Ha Hn Hpk. pose proof (u64_range p) as Up.
  rewrite <- p16_segs. apply store_ok_of_all; rewrite u_Z2bv by lia; [lia|]. intros x Hx.
  unfold wview. destruct (m x) eqn:E; [discriminate|]. exfalso.
  destruct (blk_byte C A m md p k x CK HW L ltac:(lia)) as (_ & D & _). exact (D E).
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma cww_d32 : forall x : Z, (0 <= x)%Z -> (0 <= x / 32 /\ 32 * (x / 32) <= x < 32 * (x / 32) + 32)%Z.
Proof. intros x Hx. lia. Qed.

Lemma cww_m4 : forall p a b : Z, (p mod 16 = 0)%Z -> ((p + 4 * a * b) mod 4 = 0)%Z.
Proof. intros p a b H. lia. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Local Ltac rz HW RUN :=
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN |].
Local Ltac rget :=
  repeat match goal with
  | |- getr ?R ?r = _ => match goal with E : getr R r = _ |- _ => rewrite E end
  | |- getr ?R ?r = _ => match goal with AG : regs_agree _ _ R |- _ => rewrite (AG r) by notin_lit end
  end;
  first [reflexivity | f_equal; lia].
Local Ltac incl := let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; cbn [In] in Hx |- *; tauto.
Local Ltac rchain :=
  lazymatch goal with
  | |- regs_agree ?P ?R0 ?R0 => apply regs_agree_refl
  | |- regs_agree ?P ?R0 ?R =>
      match goal with AG : regs_agree ?Q ?R1 R |- _ =>
        eapply regs_agree_trans; [| eapply regs_agree_mono; [| exact AG]; incl]; rchain end
  end.

Section CWW.
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

(* [comment removed for export] *)
Definition FTd (m : word -> option byte) : Prop :=
  forall a : word, ~ (datad <= u a < datad + 4 * wpld * hd)%Z -> ~ (s - 192 <= u a < s - 136)%Z -> m a = mB a.

Definition SLT (m : word -> option byte) : Prop :=
  rdn SEGS m (Z_to_bv 64 (s - 144)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 hd)).

Lemma cww_rng : (4288 <= s)%Z /\ (0 <= wpld * hd)%Z /\ (datad + 4 * wpld * hd <= s - 192)%Z /\ (datad + kd < 2 ^ 64)%Z /\ (0 <= kd)%Z.
Proof. assert (0 <= wpld * hd)%Z by (apply Z.mul_nonneg_nonneg; lia). lia. Qed.

Lemma cww_src : forall m, W C A m md -> (datas + ks < 2 ^ 64)%Z.
Proof.
  intros m HW. assert (0 < wpls * wd)%Z by (apply Z.mul_pos_pos; lia).
  destruct (blk_range C A m md (Z_to_bv 64 datas) ks CK HW Ls ltac:(lia)) as [_ T]. rewrite u_Z2bv in T by lia.
  pose proof CK as [T1 T2 T3 T4 T5]. pose proof (u64_range (c_sp0 C)) as T6. pose proof LSTK_val as T7. lia.
Qed.

Lemma FTd_cell : forall m (a : Z) (n : nat), FTd m -> (s - 136 <= a)%Z -> (a + Z.of_nat n <= s)%Z ->
  rdn SEGS m (Z_to_bv 64 a) n = rdn SEGS mB (Z_to_bv 64 a) n.
Proof.
  intros m a n F Ha Hn. destruct cww_rng as (G1 & G2 & G3 & G4 & G5).
  apply rdn_ext; [rewrite u_Z2bv by lia; lia |].
  intros x Hx. rewrite u_Z2bv in Hx by lia. apply F; lia.
Qed.

Lemma cww_rhd : forall m, FTd m -> rdn SEGS m (Z_to_bv 64 (s - 112)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 hd)).
Proof. intros m F. rewrite (FTd_cell m (s - 112) 4 F) by lia. exact RHD. Qed.

Lemma cww_rwd : forall m, FTd m -> rdn SEGS m (Z_to_bv 64 (s - 108)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 wd)).
Proof. intros m F. rewrite (FTd_cell m (s - 108) 4 F) by lia. exact RWD. Qed.

Lemma cww_rdd : forall m, FTd m -> rdn SEGS m (Z_to_bv 64 (s - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 datad)).
Proof. intros m F. rewrite (FTd_cell m (s - 136) 8 F) by lia. exact RDD. Qed.

(* [comment removed for export] *)
Lemma FTd_store : forall m md' (tgt : Z) (wv : word), W C A m md' -> POSTM C Ar s mB m -> FTd m -> SLT m ->
  (datad <= tgt)%Z -> (tgt + 4 <= datad + 4 * wpld * hd)%Z ->
  W C A (wbytes m (Z_to_bv 64 tgt) (word_to_le_bytes 4 wv)) md' /\ POSTM C Ar s mB (wbytes m (Z_to_bv 64 tgt) (word_to_le_bytes 4 wv))
  /\ FTd (wbytes m (Z_to_bv 64 tgt) (word_to_le_bytes 4 wv)) /\ SLT (wbytes m (Z_to_bv 64 tgt) (word_to_le_bytes 4 wv)).
Proof.
  intros m md' tgt wv HW PM F SL H1 H2. destruct cww_rng as (G1 & G2 & G3 & G4 & G5).
  pose proof (length_N_to_le_bytes 4 wv) as Ln.
  destruct (WP_blk C Ar A mB m md' (Z_to_bv 64 datad) (Z_to_bv 64 tgt) kd (word_to_le_bytes 4 wv) s CK (conj HW PM) Ld Ldr Ld0 SUB
    ltac:(rewrite !u_Z2bv by lia; lia) ltac:(rewrite Ln, !u_Z2bv by lia; lia)) as [HW' PM'].
  split; [exact HW' | split; [exact PM' | split]].
  - intros a Na Nf. rewrite wbytes_outside; [apply F; assumption | |]; rewrite ?Ln, ?u_Z2bv by lia; lia.
  - unfold SLT in *. rewrite rdn_wbytes_out; [exact SL | | |]; rewrite ?Ln, ?u_Z2bv by lia; lia.
Qed.

Lemma cw_bit_M : forall r m v k mm j, W C A m md -> POSTM C Ar s mB m -> FTd m -> SLT m ->
  (0 <= j < wd)%Z -> (0 <= k)%Z -> (32 * k + 32 <= hd)%Z -> (0 <= mm <= 31)%Z ->
  getr r 9 = v_lw v -> getr r 24 = Z_to_bv 64 mm ->
  getr r 21 = Z_to_bv 64 (datad + 4 * wpld * (32 * k + mm)) -> getr r 26 = Z_to_bv 64 (datad + 4 * wpld * (32 * k + mm)) ->
  getr r 19 = Z_to_bv 64 (4 * (j / 32)) -> getr r 25 = Z_to_bv 64 0 ->
  exists r1 m1, msteps SEGS (mkst r (0x97420 : word) m al_rom) (mkst r1 (0x9746c : word) m1 al_rom)
    /\ W C A m1 md /\ POSTM C Ar s mB m1 /\ FTd m1 /\ SLT m1
    /\ getr r1 27 = Z_to_bv 64 (datad + 4 * wpld * (32 * k + mm)) /\ regs_agree (fun x => In x [1; 5; 27]%list) r r1.
Proof.
  intros r m v k mm j HW PM F SL Hj Hk Hkh Hmm R9 R24 R21 R26 R19 R25.
  destruct cww_rng as (G1 & G2 & G3 & G4 & G5). destruct (cww_d32 j ltac:(lia)) as (E1 & E2 & E3).
  assert (P1 : (0 <= wpld * (32 * k + mm))%Z) by (apply Z.mul_nonneg_nonneg; lia).
  destruct (r90w_cell datad (32 * k + mm) j wpld hd wd ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [C1 C2].
  assert (Hu : u (Z_to_bv 64 datad) = datad) by (apply u_Z2bv; lia).
  destruct (r90w_rd4_blk C A m md (Z_to_bv 64 datad) kd (datad + 4 * wpld * (32 * k + mm) + 4 * (j / 32)) CK HW Ld
    ltac:(lia) ltac:(lia) ltac:(lia)) as (bt & vt & RT & VT).
  pose proof (r90w_sok_blk C A m md (Z_to_bv 64 datad) kd (datad + 4 * wpld * (32 * k + mm) + 4 * (j / 32)) 4 CK HW Ld
    ltac:(lia) ltac:(lia) ltac:(lia)) as SOK.
  destruct (cw_M al_rom _ r m (datad + 4 * wpld * (32 * k + mm)) (4 * (j / 32)) mm v bt vt eq_refl
    ltac:(lia) ltac:(lia) ltac:(lia) RT VT SOK R9 R24 R26 R21 R19 R25) as (r1 & m1 & RUN & HM & R127 & RA1).
  exists r1, m1. split; [exact RUN |].
  assert (INV : W C A m1 md /\ POSTM C Ar s mB m1 /\ FTd m1 /\ SLT m1).
  { revert HM. match goal with |- (if ?b then _ else _) -> _ => destruct b end; intros HM.
    - destruct HM as [wv ->]. apply FTd_store; [exact HW | exact PM | exact F | exact SL | lia | lia].
    - subst m1. tauto. }
  tauto.
Qed.

(* [comment removed for export] *)
Lemma cw_bits_W : forall (n : nat) (r0 r : bvmap 5 word) (m : word -> option byte) (v : word) (k mm j : Z),
  W C A m md -> POSTM C Ar s mB m -> FTd m -> SLT m ->
  (0 <= j < wd)%Z -> (0 <= k)%Z -> (32 * k + 32 <= hd)%Z -> (0 <= mm)%Z -> (Z.of_nat n = 31 - mm)%Z ->
  regs_agree (fun x => In x [1; 5; 13; 21; 24; 26; 27]%list) r0 r ->
  getr r 9 = v_lw v -> getr r 24 = Z_to_bv 64 mm ->
  getr r 21 = Z_to_bv 64 (datad + 4 * wpld * (32 * k + mm)) -> getr r 26 = Z_to_bv 64 (datad + 4 * wpld * (32 * k + mm)) ->
  getr r 19 = Z_to_bv 64 (4 * (j / 32)) -> getr r 15 = Z_to_bv 64 (4 * wpld) -> getr r 17 = Z_to_bv 64 32 ->
  getr r 20 = Z_to_bv 64 0 -> getr r 25 = Z_to_bv 64 0 ->
  (forall m' r', W C A m' md -> POSTM C Ar s mB m' -> FTd m' -> SLT m' -> regs_agree (fun x => In x [1; 5; 13; 21; 24; 26; 27]%list) r0 r' ->
     getr r' 21 = Z_to_bv 64 (datad + 4 * wpld * (32 * k + 32)) ->
     realizes SEGS (mkCfg (mkst r' (0x973c0 : word) m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst r (0x97420 : word) m al_rom) md) S.
Proof.
  induction n as [|n IH]; intros r0 r m v k mm j HW PM F SL Hj Hk Hkh Hmm Hn RA R9 R24 R21 R26 R19 R15 R17 R20 R25 K;
    destruct cww_rng as (G1 & G2 & G3 & G4 & G5);
    destruct (cw_bit_M r m v k mm j HW PM F SL Hj Hk Hkh ltac:(lia) R9 R24 R21 R26 R19 R25)
      as (r1 & m1 & RUN1 & HW1 & PM1 & F1 & SL1 & R127 & RA1);
    rz HW RUN1.
  - assert (Emm : mm = 31%Z) by lia. subst mm.
    assert (P2 : (wpld * (32 * k + 31 + 1) <= wpld * hd)%Z) by (apply Z.mul_le_mono_nonneg_l; lia).
    assert (P3 : (0 <= wpld * k)%Z) by (apply Z.mul_nonneg_nonneg; lia).
    destruct (cw_Mx al_rom r1 m1 31 (datad + 4 * wpld * (32 * k + 31)) wpld ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
      ltac:(rget) ltac:(rget) ltac:(rget) ltac:(rget) ltac:(rget) ltac:(rget) ltac:(rget)) as (r2 & RUN2 & R221 & RA2).
    rz HW1 RUN2.
    apply (K m1 r2 HW1 PM1 F1 SL1 ltac:(rchain)).
    rewrite R221. f_equal. lia.
  - assert (P2 : (wpld * (32 * k + mm + 1) <= wpld * hd)%Z) by (apply Z.mul_le_mono_nonneg_l; lia).
    assert (P3 : (0 <= wpld * (32 * k + mm))%Z) by (apply Z.mul_nonneg_nonneg; lia).
    destruct (cw_Mn al_rom r1 m1 mm (datad + 4 * wpld * (32 * k + mm)) wpld ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
      ltac:(rget) ltac:(rget) ltac:(rget) ltac:(rget) ltac:(rget) ltac:(rget) ltac:(rget)) as (r2 & RUN2 & R224 & R221 & R226 & RA2).
    rz HW1 RUN2.
    apply (IH r0 r2 m1 v k (mm + 1)%Z j HW1 PM1 F1 SL1 Hj Hk Hkh ltac:(lia) ltac:(lia) ltac:(rchain)
      ltac:(rget) ltac:(rget) ltac:(rget) ltac:(rget) ltac:(rget) ltac:(rget) ltac:(rget) ltac:(rget) ltac:(rget) K).
Qed.

Lemma cw_word1 : forall r m k j, W C A m md -> POSTM C Ar s mB m -> FTd m -> SLT m ->
  (0 <= j < wd)%Z -> (0 <= k)%Z -> (k < hd / 32)%Z ->
  getr r 22 = Z_to_bv 64 k -> getr r 31 = Z_to_bv 64 (datas + 4 * wpls * (wd - 1 - j)) ->
  getr r 21 = Z_to_bv 64 (datad + 4 * wpld * (32 * k)) ->
  getr r 19 = Z_to_bv 64 (4 * (j / 32)) -> getr r 7 = Z_to_bv 64 (128 * wpld) -> getr r 15 = Z_to_bv 64 (4 * wpld) ->
  getr r 17 = Z_to_bv 64 32 -> getr r 6 = Z_to_bv 64 0x4000001 -> getr r 14 = Z_to_bv 64 0x4000000 ->
  getr r 16 = Z_to_bv 64 1 -> getr r 8 = Z_to_bv 64 datas -> getr r 30 = Z_to_bv 64 0 -> getr r 20 = Z_to_bv 64 0 ->
  (forall m' r', W C A m' md -> POSTM C Ar s mB m' -> FTd m' -> SLT m' ->
     regs_agree (fun x => In x [1; 5; 9; 13; 21; 24; 25; 26; 27]%list) r r' ->
     getr r' 21 = Z_to_bv 64 (datad + 4 * wpld * (32 * k + 32)) ->
     realizes SEGS (mkCfg (mkst r' (0x973c0 : word) m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst r (0x973c8 : word) m al_rom) md) S.
Proof.
  intros r m k j HW PM F SL Hj Hk Hkn R22 R31 R21 R19 R7 R15 R17 R6 R14 R16 R8 R30 R20 K.
  destruct cww_rng as (G1 & G2 & G3 & G4 & G5). pose proof (cww_src m HW) as G6.
  destruct (cww_d32 hd ltac:(lia)) as (D1 & D2 & D3). destruct (cww_d32 j ltac:(lia)) as (E1 & E2 & E3).
  assert (P0 : (0 <= wpls * (wd - 1 - j))%Z) by (apply Z.mul_nonneg_nonneg; lia).
  assert (P1 : (wpld * (32 * k + 32) <= wpld * hd)%Z) by (apply Z.mul_le_mono_nonneg_l; lia).
  assert (P3 : (0 <= wpld * k)%Z) by (apply Z.mul_nonneg_nonneg; lia).
  destruct (r90w_src datas wpls wd (wd - 1 - j) k ltac:(lia) ltac:(lia) ltac:(lia)) as [S1 S2].
  assert (Hu : u (Z_to_bv 64 datas) = datas) by (apply u_Z2bv; lia).
  destruct (r90w_rd4_blk C A m md (Z_to_bv 64 datas) ks (datas + 4 * wpls * (wd - 1 - j) + 4 * k) CK HW Ls
    ltac:(lia) ltac:(lia) ltac:(lia)) as (bs & v & RS & VS).
  destruct (decide (v_lw v = Z_to_bv 64 0)) as [Z0 | NZ].
  - destruct (cw_Kz al_rom r m (datas + 4 * wpls * (wd - 1 - j)) (datad + 4 * wpld * (32 * k)) wpld k datas bs v RS VS Z0
      ltac:(lia) ltac:(lia) ltac:(lia) (cww_m4 datas wpls (wd - 1 - j) ALs) ltac:(lia) ltac:(lia) ltac:(lia)
      R22 R31 R21 R7 R16 R8 R30 R20) as (r1 & RUN1 & R121 & RA1).
    rz HW RUN1. apply (K m r1 HW PM F SL ltac:(rchain)).
    rewrite R121. f_equal. lia.
  - destruct (cw_Knz al_rom r m (datas + 4 * wpls * (wd - 1 - j)) (datad + 4 * wpld * (32 * k)) k datas bs v RS VS NZ
      ltac:(lia) ltac:(lia) ltac:(lia) (cww_m4 datas wpls (wd - 1 - j) ALs) ltac:(lia) (cww_m4 datad wpld (32 * k) ALd)
      R22 R31 R21 R16 R8 R6 R14) as (r1 & RUN1 & Q9 & Q24 & Q25 & Q26 & RA1).
    rz HW RUN1.
    apply (cw_bits_W 31 r1 r1 m v k 0 j HW PM F SL Hj Hk ltac:(lia) ltac:(lia) ltac:(lia) (regs_agree_refl _ _)
      ltac:(rget) ltac:(rget) ltac:(rget) ltac:(rget) ltac:(rget) ltac:(rget) ltac:(rget) ltac:(rget) ltac:(rget)).
    intros m' r' HW' PM' F' SL' RA' R'21. exact (K m' r' HW' PM' F' SL' ltac:(rchain) R'21).
Qed.

(* [comment removed for export] *)
Lemma cw_words_W : forall (n : nat) (r0 r : bvmap 5 word) (m : word -> option byte) (k j : Z),
  W C A m md -> POSTM C Ar s mB m -> FTd m -> SLT m ->
  (0 <= j < wd)%Z -> (0 <= k)%Z -> (Z.of_nat n = hd / 32 - 1 - k)%Z ->
  regs_agree (fun x => In x [1; 5; 9; 13; 21; 22; 24; 25; 26; 27]%list) r0 r ->
  getr r 22 = Z_to_bv 64 k -> getr r 31 = Z_to_bv 64 (datas + 4 * wpls * (wd - 1 - j)) ->
  getr r 21 = Z_to_bv 64 (datad + 4 * wpld * (32 * k)) ->
  getr r 19 = Z_to_bv 64 (4 * (j / 32)) -> getr r 7 = Z_to_bv 64 (128 * wpld) -> getr r 15 = Z_to_bv 64 (4 * wpld) ->
  getr r 17 = Z_to_bv 64 32 -> getr r 28 = Z_to_bv 64 (hd / 32) -> getr r 6 = Z_to_bv 64 0x4000001 -> getr r 14 = Z_to_bv 64 0x4000000 ->
  getr r 16 = Z_to_bv 64 1 -> getr r 8 = Z_to_bv 64 datas -> getr r 30 = Z_to_bv 64 0 -> getr r 20 = Z_to_bv 64 0 ->
  getr r 2 = Z_to_bv 64 (s - 192) ->
  (forall m' r', W C A m' md -> POSTM C Ar s mB m' -> FTd m' -> SLT m' ->
     regs_agree (fun x => In x [1; 5; 9; 13; 21; 22; 24; 25; 26; 27]%list) r0 r' ->
     getr r' 9 = Z_to_bv 64 hd -> getr r' 21 = Z_to_bv 64 (datad + 4 * wpld * (32 * (hd / 32))) ->
     realizes SEGS (mkCfg (mkst r' (0x974e4 : word) m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst r (0x973c8 : word) m al_rom) md) S.
Proof.
  induction n as [|n IH]; intros r0 r m k j HW PM F SL Hj Hk Hn RA R22 R31 R21 R19 R7 R15 R17 R28 R6 R14 R16 R8 R30 R20 R2 K;
    destruct cww_rng as (G1 & G2 & G3 & G4 & G5); destruct (cww_d32 hd ltac:(lia)) as (D1 & D2 & D3);
    apply (cw_word1 r m k j HW PM F SL Hj Hk ltac:(lia) R22 R31 R21 R19 R7 R15 R17 R6 R14 R16 R8 R30 R20);
    intros m1 r1 HW1 PM1 F1 SL1 RA1 R121.
  - destruct (cw_Kx al_rom r1 m1 s k (hd / 32) hd ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
      (cww_rhd m1 F1) ltac:(rget) ltac:(rget) ltac:(rget)) as (r2 & RUN2 & Q9 & Q22 & RA2).
    rz HW1 RUN2. apply (K m1 r2 HW1 PM1 F1 SL1 ltac:(rchain) Q9).
    rewrite (RA2 21%bv) by notin_lit. rewrite R121. replace (hd / 32)%Z with (k + 1)%Z by lia. f_equal. lia.
  - destruct (cw_Kn al_rom r1 m1 k (hd / 32) ltac:(lia) ltac:(lia) ltac:(rget) ltac:(rget)) as (r2 & RUN2 & Q22 & RA2).
    rz HW1 RUN2.
    apply (IH r0 r2 m1 (k + 1)%Z j HW1 PM1 F1 SL1 Hj ltac:(lia) ltac:(lia) ltac:(rchain)
      ltac:(rget) ltac:(rget) ltac:(rget) ltac:(rget) ltac:(rget) ltac:(rget) ltac:(rget) ltac:(rget) ltac:(rget) ltac:(rget)
      ltac:(rget) ltac:(rget) ltac:(rget) ltac:(rget) ltac:(rget) K).
Qed.

Lemma cw_tail1 : forall r m i j, W C A m md -> POSTM C Ar s mB m -> FTd m -> SLT m ->
  (0 <= j < wd)%Z -> (0 <= i < hd)%Z ->
  getr r 25 = Z_to_bv 64 i -> getr r 31 = Z_to_bv 64 (datas + 4 * wpls * (wd - 1 - j)) ->
  getr r 21 = Z_to_bv 64 (datad + 4 * wpld * i) -> getr r 24 = Z_to_bv 64 (datad + 4 * wpld * i) ->
  getr r 19 = Z_to_bv 64 (4 * (j / 32)) -> getr r 23 = Z_to_bv 64 0 -> getr r 16 = Z_to_bv 64 1 -> getr r 8 = Z_to_bv 64 datas ->
  exists r1 m1, msteps SEGS (mkst r (0x974fc : word) m al_rom) (mkst r1 (0x97598 : word) m1 al_rom)
    /\ W C A m1 md /\ POSTM C Ar s mB m1 /\ FTd m1 /\ SLT m1
    /\ getr r1 9 = Z_to_bv 64 (datad + 4 * wpld * i) /\ regs_agree (fun x => In x [5; 9; 13; 26]%list) r r1.
Proof.
  intros r m i j HW PM F SL Hj Hi R25 R31 R21 R24 R19 R23 R16 R8.
  destruct cww_rng as (G1 & G2 & G3 & G4 & G5). pose proof (cww_src m HW) as G6.
  destruct (cww_d32 j ltac:(lia)) as (E1 & E2 & E3). destruct (cww_d32 i ltac:(lia)) as (I1 & I2 & I3).
  assert (P0 : (0 <= wpls * (wd - 1 - j))%Z) by (apply Z.mul_nonneg_nonneg; lia).
  assert (P3 : (0 <= wpld * i)%Z) by (apply Z.mul_nonneg_nonneg; lia).
  destruct (r90w_src datas wpls wd (wd - 1 - j) (i / 32) ltac:(lia) ltac:(lia) ltac:(lia)) as [S1 S2].
  destruct (r90w_cell datad i j wpld hd wd ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [C1 C2].
  assert (Hus : u (Z_to_bv 64 datas) = datas) by (apply u_Z2bv; lia).
  assert (Hud : u (Z_to_bv 64 datad) = datad) by (apply u_Z2bv; lia).
  destruct (r90w_rd4_blk C A m md (Z_to_bv 64 datas) ks (datas + 4 * wpls * (wd - 1 - j) + 4 * (i / 32)) CK HW Ls
    ltac:(lia) ltac:(lia) ltac:(lia)) as (bs & v & RS & VS).
  destruct (r90w_rd4_blk C A m md (Z_to_bv 64 datad) kd (datad + 4 * wpld * i + 4 * (j / 32)) CK HW Ld
    ltac:(lia) ltac:(lia) ltac:(lia)) as (bt & vt & RT & VT).
  pose proof (r90w_sok_blk C A m md (Z_to_bv 64 datad) kd (datad + 4 * wpld * i + 4 * (j / 32)) 4 CK HW Ld
    ltac:(lia) ltac:(lia) ltac:(lia)) as SOK.
  destruct (cw_T al_rom _ r m (datas + 4 * wpls * (wd - 1 - j)) (datad + 4 * wpld * i) i (4 * (j / 32)) datas bs v bt vt
    ltac:(lia) ltac:(lia) ltac:(lia) (cww_m4 datas wpls (wd - 1 - j) ALs) ltac:(lia) ltac:(lia) ltac:(lia)
    RS VS eq_refl RT VT SOK R25 R31 R21 R24 R19 R23 R16 R8) as (r1 & m1 & RUN & HM & Q9 & RA1).
  exists r1, m1. split; [exact RUN |].
  assert (INV : W C A m1 md /\ POSTM C Ar s mB m1 /\ FTd m1 /\ SLT m1).
  { revert HM. match goal with |- (if ?b then _ else _) -> _ => destruct b end; intros HM.
    - subst m1. tauto.
    - destruct HM as [wv ->]. apply FTd_store; [exact HW | exact PM | exact F | exact SL | lia | lia]. }
  tauto.
Qed.

(* [comment removed for export] *)
Lemma cw_tail_W : forall (n : nat) (r0 r : bvmap 5 word) (m : word -> option byte) (i j : Z),
  W C A m md -> POSTM C Ar s mB m -> FTd m -> SLT m ->
  (0 <= j < wd)%Z -> (0 <= i)%Z -> (Z.of_nat n = hd - 1 - i)%Z ->
  regs_agree (fun x => In x [5; 9; 13; 21; 24; 25; 26]%list) r0 r ->
  getr r 25 = Z_to_bv 64 i -> getr r 31 = Z_to_bv 64 (datas + 4 * wpls * (wd - 1 - j)) ->
  getr r 21 = Z_to_bv 64 (datad + 4 * wpld * i) -> getr r 24 = Z_to_bv 64 (datad + 4 * wpld * i) ->
  getr r 19 = Z_to_bv 64 (4 * (j / 32)) -> getr r 23 = Z_to_bv 64 0 -> getr r 16 = Z_to_bv 64 1 -> getr r 8 = Z_to_bv 64 datas ->
  getr r 15 = Z_to_bv 64 (4 * wpld) -> getr r 20 = Z_to_bv 64 0 -> getr r 2 = Z_to_bv 64 (s - 192) ->
  (forall m' r', W C A m' md -> POSTM C Ar s mB m' -> FTd m' -> SLT m' ->
     regs_agree (fun x => In x [5; 9; 13; 21; 24; 25; 26]%list) r0 r' ->
     getr r' 9 = Z_to_bv 64 hd ->
     realizes SEGS (mkCfg (mkst r' (0x97328 : word) m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst r (0x974fc : word) m al_rom) md) S.
Proof.
  induction n as [|n IH]; intros r0 r m i j HW PM F SL Hj Hi Hn RA R25 R31 R21 R24 R19 R23 R16 R8 R15 R20 R2 K;
    destruct cww_rng as (G1 & G2 & G3 & G4 & G5);
    destruct (cw_tail1 r m i j HW PM F SL Hj ltac:(lia) R25 R31 R21 R24 R19 R23 R16 R8)
      as (r1 & m1 & RUN1 & HW1 & PM1 & F1 & SL1 & Q9 & RA1);
    rz HW RUN1;
    assert (P1 : (wpld * (i + 1) <= wpld * hd)%Z) by (apply Z.mul_le_mono_nonneg_l; lia);
    assert (P3 : (0 <= wpld * i)%Z) by (apply Z.mul_nonneg_nonneg; lia).
  - destruct (cw_Tx al_rom r1 m1 s i hd (datad + 4 * wpld * i) wpld ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
      ltac:(lia) ltac:(lia) ltac:(lia) (cww_rhd m1 F1) ltac:(rget) ltac:(rget) ltac:(rget) ltac:(rget) ltac:(rget) ltac:(rget)
      ltac:(rget)) as (r2 & RUN2 & Q29 & RA2).
    rz HW1 RUN2. exact (K m1 r2 HW1 PM1 F1 SL1 ltac:(rchain) Q29).
  - destruct (cw_Tn al_rom r1 m1 s i hd (datad + 4 * wpld * i) wpld ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
      ltac:(lia) ltac:(lia) ltac:(lia) (cww_rhd m1 F1) ltac:(rget) ltac:(rget) ltac:(rget) ltac:(rget) ltac:(rget) ltac:(rget)
      ltac:(rget)) as (r2 & RUN2 & Q25 & Q21 & Q24 & Q29 & RA2).
    rz HW1 RUN2.
    apply (IH r0 r2 m1 (i + 1)%Z j HW1 PM1 F1 SL1 Hj ltac:(lia) ltac:(lia) ltac:(rchain)
      ltac:(rget) ltac:(rget) ltac:(rget) ltac:(rget) ltac:(rget) ltac:(rget) ltac:(rget) ltac:(rget) ltac:(rget) ltac:(rget)
      ltac:(rget) K).
Qed.

Lemma cw_row1 : forall r0 r m j, W C A m md -> POSTM C Ar s mB m -> FTd m -> SLT m -> (0 <= j < wd)%Z ->
  regs_agree (fun x => In x [1; 5; 9; 11; 12; 13; 19; 20; 21; 22; 23; 24; 25; 26; 27; 31]%list) r0 r ->
  getr r0 7 = Z_to_bv 64 (128 * wpld) -> getr r0 15 = Z_to_bv 64 (4 * wpld) -> getr r0 17 = Z_to_bv 64 32 ->
  getr r0 28 = Z_to_bv 64 (hd / 32) -> getr r0 29 = Z_to_bv 64 (32 * (hd / 32)) ->
  getr r0 6 = Z_to_bv 64 0x4000001 -> getr r0 14 = Z_to_bv 64 0x4000000 -> getr r0 16 = Z_to_bv 64 1 -> getr r0 30 = Z_to_bv 64 0 ->
  getr r0 8 = Z_to_bv 64 datas -> getr r0 18 = Z_to_bv 64 wpls -> getr r0 10 = Z_to_bv 64 wpld -> getr r0 2 = Z_to_bv 64 (s - 192) ->
  getr r 11 = Z_to_bv 64 j -> getr r 12 = Z_to_bv 64 j -> getr r 31 = Z_to_bv 64 wd -> getr r 9 = Z_to_bv 64 hd ->
  (forall m' r', W C A m' md -> POSTM C Ar s mB m' -> FTd m' -> SLT m' ->
     regs_agree (fun x => In x [1; 5; 9; 13; 19; 20; 21; 22; 23; 24; 25; 26; 27; 31]%list) r r' ->
     getr r' 9 = Z_to_bv 64 hd ->
     realizes SEGS (mkCfg (mkst r' (0x97328 : word) m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst r (0x9733c : word) m al_rom) md) S.
Proof.
  intros r0 r m j HW PM F SL Hj RA Q7 Q15 Q17 Q28 Q29 Q6 Q14 Q16 Q30 Q8 Q18 Q10 Q2 R11 R12 R31 R9 K.
  destruct cww_rng as (G1 & G2 & G3 & G4 & G5). pose proof (cww_src m HW) as G6.
  destruct (cww_d32 hd ltac:(lia)) as (D1 & D2 & D3).
  assert (P5 : (wpls * wd <= 2 ^ 24)%Z) by lia.
  assert (TL : forall r2 m2, W C A m2 md -> POSTM C Ar s mB m2 -> FTd m2 -> SLT m2 ->
      regs_agree (fun x => In x [1; 5; 9; 13; 19; 20; 21; 22; 23; 24; 25; 26; 27; 31]%list) r r2 ->
      getr r2 9 = Z_to_bv 64 hd -> getr r2 21 = Z_to_bv 64 (datad + 4 * wpld * (32 * (hd / 32))) ->
      getr r2 19 = Z_to_bv 64 (4 * (j / 32)) -> getr r2 31 = Z_to_bv 64 (datas + 4 * wpls * (wd - 1 - j)) ->
      getr r2 20 = Z_to_bv 64 0 ->
      realizes SEGS (mkCfg (mkst r2 (0x974e4 : word) m2 al_rom) md) S).
  { intros r2 m2 HW2 PM2 F2 SL2 RA2 T9 T21 T19 T31 T20.
    assert (P6 : (0 <= wpld * (32 * (hd / 32)))%Z) by (apply Z.mul_nonneg_nonneg; lia).
    assert (P7 : (wpld * (32 * (hd / 32)) <= wpld * hd)%Z) by (apply Z.mul_le_mono_nonneg_l; lia).
    destruct (Z_le_gt_dec hd (32 * (hd / 32))) as [E0 | E0].
    - destruct (cw_T0e al_rom r2 m2 hd (32 * (hd / 32)) ltac:(lia) ltac:(lia) E0 ltac:(rget) T9) as (r3 & RUN3 & RA3).
      rz HW2 RUN3. exact (K m2 r3 HW2 PM2 F2 SL2 ltac:(rchain) ltac:(rget)).
    - destruct (cw_T0s al_rom r2 m2 hd (32 * (hd / 32)) (datad + 4 * wpld * (32 * (hd / 32))) ltac:(lia) ltac:(lia) ltac:(lia)
        ltac:(lia) (cww_m4 datad wpld (32 * (hd / 32)) ALd) ltac:(rget) T9 T21) as (r3 & RUN3 & U23 & U24 & U25 & RA3).
      rz HW2 RUN3.
      apply (cw_tail_W (Z.to_nat (hd - 1 - 32 * (hd / 32))) r3 r3 m2 (32 * (hd / 32)) j HW2 PM2 F2 SL2 Hj ltac:(lia) ltac:(lia)
        (regs_agree_refl _ _) U25 ltac:(rget) ltac:(rget) U24 ltac:(rget) U23 ltac:(rget) ltac:(rget) ltac:(rget) ltac:(rget)
        ltac:(rget)).
      intros m' r' HW' PM' F' SL' RA' R'9. exact (K m' r' HW' PM' F' SL' ltac:(rchain) R'9). }
  destruct (Z_le_gt_dec 32 hd) as [H32 | H32].
  - destruct (cw_Jw al_rom r m s wd hd datas wpls wpld datad j ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) SL (cww_rdd m F) ltac:(rget) R11 R12 R31 ltac:(rget) ltac:(rget) ltac:(rget)
      ltac:(rget) ltac:(rget)) as (r1 & RUN1 & J19 & J31 & J20 & J21 & J22 & RA1).
    rz HW RUN1.
    apply (cw_words_W (Z.to_nat (hd / 32 - 1)) r1 r1 m 0 j HW PM F SL Hj ltac:(lia) ltac:(lia) (regs_agree_refl _ _)
      J22 J31 ltac:(rget) J19 ltac:(rget) ltac:(rget) ltac:(rget) ltac:(rget) ltac:(rget) ltac:(rget) ltac:(rget) ltac:(rget)
      ltac:(rget) J20 ltac:(rget)).
    intros m' r' HW' PM' F' SL' RA' R'9 R'21.
    exact (TL r' m' HW' PM' F' SL' ltac:(rchain) R'9 R'21 ltac:(rget) ltac:(rget) ltac:(rget)).
  - assert (H0 : (hd / 32 = 0)%Z) by lia.
    destruct (cw_Jt al_rom r m s wd hd datas wpls wpld datad j ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) SL (cww_rdd m F) ltac:(rget) R11 R12 R31 ltac:(rget) ltac:(rget) ltac:(rget)
      ltac:(rget) ltac:(rget)) as (r1 & RUN1 & J19 & J31 & J20 & J21 & RA1).
    rz HW RUN1.
    exact (TL r1 m HW PM F SL ltac:(rchain) ltac:(rget) ltac:(rewrite H0; rget) J19 J31 J20).
Qed.

(* [comment removed for export] *)
Lemma cw_rows_W : forall (n : nat) (r0 r : bvmap 5 word) (m : word -> option byte) (j : Z),
  W C A m md -> POSTM C Ar s mB m -> FTd m -> SLT m -> (0 <= j)%Z -> (Z.of_nat n = wd - 1 - j)%Z ->
  regs_agree (fun x => In x [1; 5; 9; 11; 12; 13; 19; 20; 21; 22; 23; 24; 25; 26; 27; 31]%list) r0 r ->
  getr r0 7 = Z_to_bv 64 (128 * wpld) -> getr r0 15 = Z_to_bv 64 (4 * wpld) -> getr r0 17 = Z_to_bv 64 32 ->
  getr r0 28 = Z_to_bv 64 (hd / 32) -> getr r0 29 = Z_to_bv 64 (32 * (hd / 32)) ->
  getr r0 6 = Z_to_bv 64 0x4000001 -> getr r0 14 = Z_to_bv 64 0x4000000 -> getr r0 16 = Z_to_bv 64 1 -> getr r0 30 = Z_to_bv 64 0 ->
  getr r0 8 = Z_to_bv 64 datas -> getr r0 18 = Z_to_bv 64 wpls -> getr r0 10 = Z_to_bv 64 wpld -> getr r0 2 = Z_to_bv 64 (s - 192) ->
  getr r 11 = Z_to_bv 64 j -> getr r 12 = Z_to_bv 64 j -> getr r 31 = Z_to_bv 64 wd -> getr r 9 = Z_to_bv 64 hd ->
  (forall m' r', W C A m' md -> POSTM C Ar s mB m' -> FTd m' -> SLT m' ->
     regs_agree (fun x => In x [1; 5; 9; 11; 12; 13; 19; 20; 21; 22; 23; 24; 25; 26; 27; 31]%list) r0 r' ->
     realizes SEGS (mkCfg (mkst r' (0x98a2c : word) m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst r (0x9733c : word) m al_rom) md) S.
Proof.
  induction n as [|n IH]; intros r0 r m j HW PM F SL Hj Hn RA Q7 Q15 Q17 Q28 Q29 Q6 Q14 Q16 Q30 Q8 Q18 Q10 Q2 R11 R12 R31 R9 K;
    destruct cww_rng as (G1 & G2 & G3 & G4 & G5);
    apply (cw_row1 r0 r m j HW PM F SL ltac:(lia) RA Q7 Q15 Q17 Q28 Q29 Q6 Q14 Q16 Q30 Q8 Q18 Q10 Q2 R11 R12 R31 R9);
    intros m1 r1 HW1 PM1 F1 SL1 RA1 X9.
  - destruct (cw_Rx al_rom r1 m1 s j wd ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) (cww_rwd m1 F1)
      ltac:(rget) ltac:(rget) ltac:(rget)) as (r2 & RUN2 & RA2).
    rz HW1 RUN2. exact (K m1 r2 HW1 PM1 F1 SL1 ltac:(rchain)).
  - destruct (cw_Rn al_rom r1 m1 s j wd ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) (cww_rwd m1 F1)
      ltac:(rget) ltac:(rget) ltac:(rget)) as (r2 & RUN2 & X11 & X12 & X31 & RA2).
    rz HW1 RUN2.
    apply (IH r0 r2 m1 (j + 1)%Z HW1 PM1 F1 SL1 ltac:(lia) ltac:(lia) ltac:(rchain) Q7 Q15 Q17 Q28 Q29 Q6 Q14 Q16 Q30 Q8 Q18 Q10 Q2
      X11 X12 X31 ltac:(rget) K).
Qed.

(* [comment removed for export] *)
Lemma cw_arm_W : forall (r : bvmap 5 word),
  W C A mB md ->
  getr r 2 = Z_to_bv 64 (s - 192) -> getr r 10 = Z_to_bv 64 wpld -> getr r 8 = Z_to_bv 64 datas -> getr r 18 = Z_to_bv 64 wpls ->
  (forall m' r', W C A m' md -> POSTM C Ar s mB m' -> FTd m' ->
     regs_agree (fun x => In x [1; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%list) r r' ->
     realizes SEGS (mkCfg (mkst r' (0x98a2c : word) m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst r (0x9726c : word) mB al_rom) md) S.
Proof using CK SUB Ld Hkd Ldr Ld0 Ls Hks Hdd Hds Hwd Hhd Hwpld Hwpls Hwd32 Hhd32 Hs Hs64 Hbelow RWD RHD RDD ALd ALs Hd4k Hs4k Hszs Hstk Htop
  ks kd P16 PINS.
  intros r HW R2 R10 R8 R18 K.
  destruct cww_rng as (G1 & G2 & G3 & G4 & G5).
  pose proof (W_sok_win C A mB md (s - 144) 8 CK HW ltac:(lia) ltac:(lia)) as SOK.
  destruct (cw_S al_rom r mB s wd hd wpld datas ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) RWD RHD SOK R2 R10 R8)
    as (r1 & RUN1 & S31 & S11 & S12 & S9 & S14 & S15 & S7 & S16 & S17 & S6 & S30 & S28 & S29 & RA1).
  rz HW RUN1.
  pose proof (length_N_to_le_bytes 8 (Z_to_bv 64 hd)) as Ln.
  destruct (WP_win C A Ar mB mB md (Z_to_bv 64 (s - 144)) (word_to_le_bytes 8 (Z_to_bv 64 hd)) s CK (conj HW (POSTM_refl C Ar s mB)) SUB
    ltac:(rewrite u_Z2bv by lia; lia) ltac:(rewrite Ln, u_Z2bv by lia; lia) Htop) as [HW1 PM1].
  assert (F1 : FTd (wbytes mB (Z_to_bv 64 (s - 144)) (word_to_le_bytes 8 (Z_to_bv 64 hd)))).
  { intros a Na Nf. rewrite wbytes_outside; try reflexivity; rewrite ?Ln, ?u_Z2bv by lia; lia. }
  assert (SL1 : SLT (wbytes mB (Z_to_bv 64 (s - 144)) (word_to_le_bytes 8 (Z_to_bv 64 hd)))).
  { unfold SLT. apply SeqExec.rdn_wbytes_hit8. rewrite u_Z2bv by lia. lia. }
  apply (cw_rows_W (Z.to_nat (wd - 1)) r1 r1 _ 0 HW1 PM1 F1 SL1 ltac:(lia) ltac:(lia) (regs_agree_refl _ _)
    S7 S15 S17 S28 S29 S6 S14 S16 S30 ltac:(rget) ltac:(rget) ltac:(rget) ltac:(rget) S11 S12 S31 S9).
  intros m' r' HW' PM' F' SL' RA'. exact (K m' r' HW' PM' F' ltac:(rchain)).
Qed.

End CWW.

End R90W.
