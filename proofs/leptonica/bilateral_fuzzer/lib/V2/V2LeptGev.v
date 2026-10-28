(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.bilateral_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith DitherLib.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2LeptBase V2LeptPixHdr V2LeptUb V2LeptBl_iface V2LeptGevSegs.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Local Abbreviation SEGS := Ubsan.M.loaded_segments.

Lemma ag_keep : forall (L : list reg) regs regs' (r : reg) (v : word),
  regs_agree (fun x => In x L) regs regs' -> existsb (fun x => Z.eqb (bv_unsigned x) (bv_unsigned r)) L = false ->
  getr regs r = v -> getr regs' r = v.
Proof.
  intros L regs regs' r v AG E H. rewrite AG; [exact H|]. intros Hin.
  assert (T : existsb (fun x => Z.eqb (bv_unsigned x) (bv_unsigned r)) L = true).
  { apply existsb_exists. exists r. split; [exact Hin | apply Z.eqb_refl]. }
  congruence.
Qed.

Lemma ag_comp : forall (L1 L2 L : list reg) r1 r2 r3,
  regs_agree (fun x => In x L1) r1 r2 -> regs_agree (fun x => In x L2) r2 r3 ->
  forallb (fun x => existsb (fun y => Z.eqb (bv_unsigned y) (bv_unsigned x)) L) (L1 ++ L2) = true ->
  regs_agree (fun x => In x L) r1 r3.
Proof.
  intros L1 L2 L r1 r2 r3 A1 A2 B r Hr. rewrite forallb_forall in B.
  assert (IN : forall x, In x (L1 ++ L2) -> In x L).
  { intros x Hx. specialize (B x Hx). apply existsb_exists in B. destruct B as (y & Hy & E).
    apply Z.eqb_eq in E. apply bv_eq in E. subst. exact Hy. }
  rewrite A2, A1; [reflexivity | |].
  - intros Hin. apply Hr, IN, in_or_app. left. exact Hin.
  - intros Hin. apply Hr, IN, in_or_app. right. exact Hin.
Qed.

Lemma u_rng : forall x : word, (0 <= bv_unsigned x < 2 ^ 64)%Z.
Proof. intros x. pose proof (bv_unsigned_in_range 64 x) as H. unfold bv_modulus in H. exact H. Qed.

Lemma w2b_u : forall (k : nat) (x : word), word_to_le_bytes k x = Z_to_le_bytes k (bv_unsigned x).
Proof. intros k x. rewrite <- (w2b_Z k (bv_unsigned x)) by apply u_rng. rewrite Z_to_bv_bv_unsigned. reflexivity. Qed.

Lemma byte_rdn1 : forall (m : word -> option byte) (a : word) (b : byte),
  m a = Some b -> rdn SEGS m a 1 = Some (Z_to_le_bytes 1 (bv_unsigned b)).
Proof. intros m a b H. cbn [Z_to_le_bytes rdn]. rewrite H. rewrite Z_to_bv_bv_unsigned. reflexivity. Qed.

Lemma byte_rng : forall b : byte, (0 <= bv_unsigned b <= 255)%Z.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as H. unfold bv_modulus in H. cbn in H. lia. Qed.

Lemma bytea_row : forall line q n, (line mod 4 = 0)%Z -> (0 <= q < 4 * n)%Z -> (line <= bytea (line + q) < line + 4 * n)%Z.
Proof. intros line q n Hl Hq. apply bytea_bounds; [exact Hl | lia]. Qed.

Ltac agk AG H := apply (ag_keep _ _ _ _ _ AG); [vm_compute; reflexivity | exact H].
Ltac agc A1 A2 := eapply ag_comp; [exact A1 | exact A2 | vm_compute; reflexivity].

Section GevW.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V2Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
Lemma gv_col : forall k regs m (typ e w j line : Z),
  (4 <= typ <= 5)%Z -> gev_ok typ e -> (0 <= j < w)%Z -> Z.of_nat k = (w - j)%Z -> (w <= 20000)%Z ->
  (4096 <= line)%Z -> (line + 2 ^ 26 < 2 ^ 63)%Z ->
  (forall q, (j <= q < w)%Z -> exists vq, (0 <= vq <= 255)%Z /\ rdn SEGS m (Z_to_bv 64 (bytea (line + q))) 1 = Some (Z_to_le_bytes 1 vq)) ->
  getr regs 18 = Z_to_bv 64 (line + j) -> getr regs 19 = Z_to_bv 64 (line + j) -> getr regs 9 = Z_to_bv 64 j -> getr regs 31 = Z_to_bv 64 j ->
  getr regs 30 = Z_to_bv 64 line -> getr regs 28 = Z_to_bv 64 1 -> getr regs 29 = Z_to_bv 64 3 -> getr regs 15 = Z_to_bv 64 1 ->
  getr regs 5 = Z_to_bv 64 1 -> getr regs 11 = Z_to_bv 64 typ -> getr regs 20 = Z_to_bv 64 e -> getr regs 17 = Z_to_bv 64 w ->
  exists regs' (e' : Z),
    msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1efd0) m al_rom) (@mkst fx regs' (Z_to_bv 64 0x1f038) m al_rom)
    /\ getr regs' 12 = Z_to_bv 64 e' /\ (0 <= e' <= 255)%Z
    /\ regs_agree (fun x => In x [9; 12; 18; 19; 20; 21; 22; 23; 24; 31]%list) regs regs'.
Proof.
  induction k as [|k IH]; intros regs m typ e w j line Ht Hok Hj Hk Hw Hl1 Hl2 Hrd H18 H19 H9 H31 H30 H28 H29 H15 H5 H11 H20 H17.
  { cbn [Z.of_nat] in Hk. lia. }
  destruct (Hrd j ltac:(lia)) as (v & Hv & R).
  pose proof (gev_ok_range _ _ Hok) as He.
  destruct (gv_I1 al_rom fx regs m line j typ e v Hl1 Hl2 ltac:(lia) Ht He Hv R H18 H19 H9 H31 H30 H28 H29 H15 H11 H20)
    as (R1 & M1 & G22 & G12 & G21 & AG1).
  assert (K20 : getr R1 20 = Z_to_bv 64 e) by (agk AG1 H20).
  assert (K9 : getr R1 9 = Z_to_bv 64 j) by (agk AG1 H9).
  assert (K31 : getr R1 31 = Z_to_bv 64 j) by (agk AG1 H31).
  assert (K18 : getr R1 18 = Z_to_bv 64 (line + j)) by (agk AG1 H18).
  assert (K19 : getr R1 19 = Z_to_bv 64 (line + j)) by (agk AG1 H19).
  assert (K5 : getr R1 5 = Z_to_bv 64 1) by (agk AG1 H5).
  assert (K15 : getr R1 15 = Z_to_bv 64 1) by (agk AG1 H15).
  assert (K17 : getr R1 17 = Z_to_bv 64 w) by (agk AG1 H17).
  set (t := ((typ =? 4)%Z && (v <? e)%Z) || ((typ =? 5)%Z && (e <? v)%Z)) in *.
  assert (Estep : (if t then v else e) = gev_step typ e v) by reflexivity.
  pose proof (gev_step_byte typ e v ltac:(lia) Hok Hv) as Hb. rewrite <- Estep in Hb.
  destruct (Z.eq_dec (j + 1) w) as [Elast | Nlast].
  - destruct (gv_I2 al_rom t true fx R1 m j w (line + j) e v Hj ltac:(lia) ltac:(lia) ltac:(lia) Elast G22 G12 K20 G21 K9 K31 K18 K19 K5 K15 K17)
      as (R2 & M2 & F20 & F12 & F9 & F31 & F18 & F19 & F21 & AG2).
    exists R2, (if t then v else e). split; [eapply msteps_trans; [exact M1 | exact M2]|].
    split; [exact F12|]. split; [exact Hb|]. agc AG1 AG2.
  - destruct (gv_I2 al_rom t false fx R1 m j w (line + j) e v Hj ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbv beta iota; lia)
                G22 G12 K20 G21 K9 K31 K18 K19 K5 K15 K17)
      as (R2 & M2 & F20 & F12 & F9 & F31 & F18 & F19 & F21 & AG2).
    assert (AG12 : regs_agree (fun x => In x [9; 12; 18; 19; 20; 21; 22; 23; 24; 31]%list) regs R2) by (agc AG1 AG2).
    assert (F18' : getr R2 18 = Z_to_bv 64 (line + (j + 1))) by (rewrite F18; f_equal; lia).
    assert (F19' : getr R2 19 = Z_to_bv 64 (line + (j + 1))) by (rewrite F19; f_equal; lia).
    assert (L30 : getr R2 30 = Z_to_bv 64 line) by (agk AG12 H30).
    assert (L28 : getr R2 28 = Z_to_bv 64 1) by (agk AG12 H28).
    assert (L29 : getr R2 29 = Z_to_bv 64 3) by (agk AG12 H29).
    assert (L15 : getr R2 15 = Z_to_bv 64 1) by (agk AG12 H15).
    assert (L5 : getr R2 5 = Z_to_bv 64 1) by (agk AG12 H5).
    assert (L11 : getr R2 11 = Z_to_bv 64 typ) by (agk AG12 H11).
    assert (L17 : getr R2 17 = Z_to_bv 64 w) by (agk AG12 H17).
    destruct (IH R2 m typ (if t then v else e) w (j + 1)%Z line Ht (or_intror Hb) ltac:(lia) ltac:(lia) Hw Hl1 Hl2
                (fun q Hq => Hrd q ltac:(lia)) F18' F19' F9 F31 L30 L28 L29 L15 L5 L11 F20 L17)
      as (R3 & e' & M3 & K12 & He' & AG3).
    exists R3, e'. split; [eapply msteps_trans; [exact M1 | eapply msteps_trans; [exact M2 | exact M3]]|].
    split; [exact K12|]. split; [exact He'|]. agc AG12 AG3.
Qed.

(* [comment removed for export] *)
Lemma gv_rows : forall k regs m (typ e w h i data wpl : Z),
  (4 <= typ <= 5)%Z -> gev_ok typ e -> (0 <= i < h)%Z -> Z.of_nat k = (h - i)%Z -> (h <= 20000)%Z -> (1 <= w <= 20000)%Z ->
  (0 <= wpl)%Z -> (w <= 4 * wpl)%Z -> (4 * (wpl * h) <= 2 ^ 26)%Z -> (4096 <= data)%Z -> (data mod 4 = 0)%Z -> (data + 2 ^ 27 < 2 ^ 63)%Z ->
  (forall a, (data <= a < data + 4 * (wpl * h))%Z -> exists va, (0 <= va <= 255)%Z /\ rdn SEGS m (Z_to_bv 64 a) 1 = Some (Z_to_le_bytes 1 va)) ->
  getr regs 7 = Z_to_bv 64 i -> getr regs 16 = Z_to_bv 64 (i * wpl) -> getr regs 8 = Z_to_bv 64 data -> getr regs 10 = Z_to_bv 64 wpl ->
  getr regs 17 = Z_to_bv 64 w -> getr regs 28 = Z_to_bv 64 1 -> getr regs 29 = Z_to_bv 64 3 -> getr regs 12 = Z_to_bv 64 e ->
  getr regs 15 = Z_to_bv 64 1 -> getr regs 5 = Z_to_bv 64 1 -> getr regs 11 = Z_to_bv 64 typ -> getr regs 6 = Z_to_bv 64 wpl ->
  getr regs 13 = Z_to_bv 64 h ->
  exists regs' (e' : Z),
    msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1ef60) m al_rom) (@mkst fx regs' (Z_to_bv 64 0x1f050) m al_rom)
    /\ getr regs' 12 = Z_to_bv 64 e' /\ (0 <= e' <= 255)%Z
    /\ regs_agree (fun x => In x [7; 9; 12; 16; 18; 19; 20; 21; 22; 23; 24; 30; 31]%list) regs regs'.
Proof.
  induction k as [|k IH]; intros regs m typ e w h i data wpl Ht Hok Hi Hk Hh Hw Hwpl Hw4 Hwh Hd1 Hd4 Hd2 Hrd
    H7 H16 H8 H10 H17 H28 H29 H12 H15 H5 H11 H6 H13.
  { cbn [Z.of_nat] in Hk. lia. }
  pose proof (gev_ok_range _ _ Hok) as He.
  assert (Hiw : (0 <= i * wpl /\ (i + 1) * wpl <= wpl * h)%Z) by nia.
  destruct (gv_OH al_rom fx regs m i h w wpl data e Hi Hh ltac:(lia) Hwpl Hwh Hd1 ltac:(lia) He H7 H16 H8 H10 H17 H28 H12)
    as (R1 & M1 & G30 & G18 & G19 & G9 & G31 & G20 & AG1).
  assert (Hl4 : ((data + 4 * (i * wpl)) mod 4 = 0)%Z) by (rewrite Z.add_mod, Hd4 by lia; rewrite Z.mul_comm, Z.mod_mul by lia; reflexivity).
  assert (RD : forall q, (0 <= q < w)%Z -> exists vq, (0 <= vq <= 255)%Z /\
                 rdn SEGS m (Z_to_bv 64 (bytea (data + 4 * (i * wpl) + q))) 1 = Some (Z_to_le_bytes 1 vq)).
  { intros q Hq. pose proof (bytea_row (data + 4 * (i * wpl)) q wpl Hl4 ltac:(lia)) as Hb. apply Hrd. nia. }
  assert (G18' : getr R1 18 = Z_to_bv 64 (data + 4 * (i * wpl) + 0)) by (rewrite G18; f_equal; lia).
  assert (G19' : getr R1 19 = Z_to_bv 64 (data + 4 * (i * wpl) + 0)) by (rewrite G19; f_equal; lia).
  assert (K28 : getr R1 28 = Z_to_bv 64 1) by (agk AG1 H28).
  assert (K29 : getr R1 29 = Z_to_bv 64 3) by (agk AG1 H29).
  assert (K15 : getr R1 15 = Z_to_bv 64 1) by (agk AG1 H15).
  assert (K5 : getr R1 5 = Z_to_bv 64 1) by (agk AG1 H5).
  assert (K11 : getr R1 11 = Z_to_bv 64 typ) by (agk AG1 H11).
  assert (K17 : getr R1 17 = Z_to_bv 64 w) by (agk AG1 H17).
  destruct (gv_col (Z.to_nat w) R1 m typ e w 0 (data + 4 * (i * wpl)) Ht Hok ltac:(lia) ltac:(rewrite Z2Nat.id; lia) ltac:(lia)
              ltac:(lia) ltac:(lia) (fun q Hq => RD q ltac:(lia)) G18' G19' G9 G31 G30 K28 K29 K15 K5 K11 G20 K17)
    as (R2 & e1 & M2 & F12 & He1 & AG2).
  assert (AG12 : regs_agree (fun x => In x [7; 9; 12; 16; 18; 19; 20; 21; 22; 23; 24; 30; 31]%list) regs R2) by (agc AG1 AG2).
  assert (L7 : getr R2 7 = Z_to_bv 64 i) by (apply (ag_keep _ _ _ _ _ AG2); [vm_compute; reflexivity | agk AG1 H7]).
  assert (L15 : getr R2 15 = Z_to_bv 64 1) by (agk AG12 H15).
  assert (L16 : getr R2 16 = Z_to_bv 64 (i * wpl)) by (apply (ag_keep _ _ _ _ _ AG2); [vm_compute; reflexivity | agk AG1 H16]).
  assert (L6 : getr R2 6 = Z_to_bv 64 wpl) by (agk AG12 H6).
  assert (L13 : getr R2 13 = Z_to_bv 64 h) by (agk AG12 H13).
  destruct (Z.eq_dec (i + 1) h) as [Elast | Nlast].
  - destruct (gv_ON al_rom true fx R2 m i h wpl Hi Hh Hwpl Hwh Elast L7 L15 L16 L6 L13) as (R3 & M3 & N7 & N16 & AG3).
    exists R3, e1. split; [eapply msteps_trans; [exact M1 | eapply msteps_trans; [exact M2 | exact M3]]|].
    split; [agk AG3 F12|]. split; [exact He1|]. agc AG12 AG3.
  - destruct (gv_ON al_rom false fx R2 m i h wpl Hi Hh Hwpl Hwh ltac:(cbv beta iota; lia) L7 L15 L16 L6 L13) as (R3 & M3 & N7 & N16 & AG3).
    assert (AG123 : regs_agree (fun x => In x [7; 9; 12; 16; 18; 19; 20; 21; 22; 23; 24; 30; 31]%list) regs R3) by (agc AG12 AG3).
    assert (P8 : getr R3 8 = Z_to_bv 64 data) by (agk AG123 H8).
    assert (P10 : getr R3 10 = Z_to_bv 64 wpl) by (agk AG123 H10).
    assert (P17 : getr R3 17 = Z_to_bv 64 w) by (agk AG123 H17).
    assert (P28 : getr R3 28 = Z_to_bv 64 1) by (agk AG123 H28).
    assert (P29 : getr R3 29 = Z_to_bv 64 3) by (agk AG123 H29).
    assert (P12 : getr R3 12 = Z_to_bv 64 e1) by (agk AG3 F12).
    assert (P15 : getr R3 15 = Z_to_bv 64 1) by (agk AG123 H15).
    assert (P5 : getr R3 5 = Z_to_bv 64 1) by (agk AG123 H5).
    assert (P11 : getr R3 11 = Z_to_bv 64 typ) by (agk AG123 H11).
    assert (P6 : getr R3 6 = Z_to_bv 64 wpl) by (agk AG123 H6).
    assert (P13 : getr R3 13 = Z_to_bv 64 h) by (agk AG123 H13).
    destruct (IH R3 m typ e1 w h (i + 1)%Z data wpl Ht (or_intror He1) ltac:(lia) ltac:(lia) Hh Hw Hwpl Hw4 Hwh Hd1 Hd4 Hd2 Hrd
                N7 N16 P8 P10 P17 P28 P29 P12 P15 P5 P11 P6 P13)
      as (R4 & e' & M4 & K12 & He' & AG4).
    exists R4, e'. split; [eapply msteps_trans; [exact M1 | eapply msteps_trans; [exact M2 | eapply msteps_trans; [exact M3 | exact M4]]]|].
    split; [exact K12|]. split; [exact He'|]. agc AG123 AG4.
Qed.

Ltac wout := repeat (rewrite wbytes_outside by (rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia)).
Ltac rdout := repeat (rewrite rdn_wbytes_out_Z by (rewrite ?length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia)).

(* [comment removed for export] *)
Theorem pixGetExtremeValue_W : pixGetExtremeValue_contract.
Proof.
  intros C A m md regs s pixs typ cellp v ret S CK HW H2 Hs16 Hstk Hsc Hct Hc4 H1 Hret H10 H11 H12 H13 H14 H15 H16 SRC Htyp POST.
  destruct SRC as (PX & Hd & Hcm & Hhdr & Hw1 & Hh1 & Hwpl & Lp & Ld & Hxr & Hyr).
  destruct Hhdr as (_ & Hw20 & Hh20 & Hsz). rewrite <- Hwpl in Hsz.
  pose proof CK as [Ctop Csp0 Csp0hi Cal Cimg].
  pose proof LSTK_val as LS. unfold GEV_STACK in Hstk.
  pose proof PX as (Hp0 & Hp64 & WF & _).
  pose proof WF as [_ _ _ _ _ _ _ _ _ _ _ _ Hdat].
  pose proof HW as [WI WP _ _ _ _ _ _ _ _ _].
  set (w := p_w v) in *. set (h := p_h v) in *. set (wpl := p_wpl v) in *. set (data := p_data v) in *.
  assert (Hq : (1 <= wpl /\ w <= 4 * wpl)%Z).
  { rewrite Hwpl. unfold wpl_of. pose proof (Z.div_mod (w * 8 + 31) 32 ltac:(lia)). pose proof (Z.mod_pos_bound (w * 8 + 31) 32 ltac:(lia)). lia. }
  pose proof (blk_range C A m md (Z_to_bv 64 pixs) 64 CK HW Lp ltac:(lia)) as BRp. rewrite u_Z2bv in BRp by lia.
  pose proof (blk_range C A m md (Z_to_bv 64 data) _ CK HW Ld ltac:(nia)) as BRd. rewrite u_Z2bv in BRd by lia.
  pose proof (ai_live_hull _ _ _ _ _ WI Lp) as (_ & ALp & _ & _). rewrite u_Z2bv in ALp by lia.
  pose proof (ai_live_hull _ _ _ _ _ WI Ld) as (_ & ALd & _ & DEFd). rewrite u_Z2bv in ALd by lia.
  assert (Hwplb : (wpl <= 2 ^ 24)%Z) by nia.
  assert (Hpm8 : (pixs mod 8 = 0)%Z) by (apply al16_mod8; exact ALp).
  assert (Hdm4 : (data mod 4 = 0)%Z) by (apply mod16_mod4; exact ALd).
  assert (Htyp' : (4 <= typ <= 5)%Z) by lia.
  assert (SOKf : store_ok SEGS m (Z_to_bv 64 (s - 128)) 128 = true) by (apply (W_sok_win C A m md); [exact CK | exact HW | lia | cbn; lia]).
  assert (SOKc : store_ok SEGS m (Z_to_bv 64 cellp) 4 = true) by (apply (W_sok_win C A m md); [exact CK | exact HW | lia | cbn; lia]).
  assert (Ccm : rdn SEGS m (Z_to_bv 64 (pixs + 48)) 8 = Some (Z_to_le_bytes 8 0)) by (rewrite <- Hcm; eapply PIX_rd_cmap; exact PX).
  destruct (gv_A al_rom fx regs m s pixs typ cellp ltac:(lia) Hsc ltac:(lia) Hc4 ltac:(lia) ltac:(lia) Hpm8 Htyp' SOKf SOKc Ccm
              ltac:(lia) ltac:(lia) H2 H10 H11 H12 H13 H14 H15 H16)
    as (R1 & M1 & G2 & G9 & G18 & G23 & G19 & G20 & G21 & G22 & AG1).
  set (m1 := GVA m s cellp regs) in *.
  assert (W1 : W C A m1 md).
  { unfold m1, GVA, FRG.
    repeat (apply W_store_win; [exact CK | | rewrite u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia]).
    exact HW. }
  assert (PX1 : PIXat m1 pixs v).
  { eapply PIXat_frame; [exact PX|]. intros x Hx. unfold m1, GVA, FRG. wout. reflexivity. }
  assert (SOK1 : store_ok SEGS m1 (Z_to_bv 64 (s - 128)) 128 = true) by (apply (W_sok_win C A m1 md); [exact CK | exact W1 | lia | cbn; lia]).
  destruct (gv_B al_rom fx R1 m1 s pixs typ cellp w h wpl data ltac:(lia) Hs16 ltac:(lia) ltac:(lia) Hpm8 Htyp' ltac:(lia) ltac:(lia) ltac:(lia)
              ltac:(lia) ltac:(lia) SOK1 (PIX_rd_w SEGS _ _ _ PX1) (PIX_rd_h SEGS _ _ _ PX1)
              ltac:(pose proof (PIX_rd_d SEGS _ _ _ PX1) as X; rewrite Hd in X; exact X)
              (PIX_rd_wpl SEGS _ _ _ PX1) (PIX_rd_data SEGS _ _ _ PX1) ltac:(lia) G2 G9 G18 G23 G19 G20 G21 G22)
    as (R2 & M2 & F8 & F10 & F11 & F12 & F13 & F14 & F15 & F16 & F7 & F17 & F5 & F6 & F28 & F29 & AG2).
  set (m2 := GVB m1 s w h) in *.
  assert (W2 : W C A m2 md).
  { unfold m2, GVB.
    repeat (apply W_store_win; [exact CK | | rewrite u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia]).
    first [exact W1 | exact HW]. }
  assert (Hd0 : (0 <= data)%Z) by lia.
  assert (RD : forall a, (data <= a < data + 4 * (wpl * h))%Z -> exists va, (0 <= va <= 255)%Z /\ rdn SEGS m2 (Z_to_bv 64 a) 1 = Some (Z_to_le_bytes 1 va)).
  { intros a Ha.
    assert (Hr16 : (4 * (wpl * h) <= round16 (4 * (wpl * h)))%Z).
    { unfold round16. pose proof (Z.div_mod (4 * (wpl * h) + 15) 16 ltac:(lia)). pose proof (Z.mod_pos_bound (4 * (wpl * h) + 15) 16 ltac:(lia)). lia. }
    specialize (DEFd (a - data)%Z ltac:(lia)) as (_ & DEF & _). unfold at_ in DEF. rewrite u_Z2bv in DEF by lia.
    replace (data + (a - data))%Z with a in DEF by lia.
    assert (EQ : m2 (Z_to_bv 64 a) = m (Z_to_bv 64 a)) by (unfold m2, m1, GVB, GVA, FRG; wout; reflexivity).
    destruct (m (Z_to_bv 64 a)) as [b|] eqn:Eb; [|congruence].
    exists (bv_unsigned b). split; [apply byte_rng|]. apply byte_rdn1. exact EQ. }
  destruct (gv_rows (Z.to_nat h) R2 m2 typ (gev_init typ) w h 0 data wpl Htyp' (or_introl eq_refl) ltac:(lia) ltac:(rewrite Z2Nat.id; lia)
              ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hdm4 ltac:(lia) RD
              F7 F16 F8 F10 F17 F28 F29 F12 F15 F5 F11 F6 F13)
    as (R3 & e' & M3 & K12 & He' & AG3).
  assert (Hcp : (s <= cellp)%Z) by exact Hsc.
  assert (AG23 : regs_agree (fun x => In x [1; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 28; 29; 30; 31]%list) R1 R3)
    by (agc AG2 AG3).
  assert (L2 : getr R3 2 = Z_to_bv 64 (s - 128)) by (agk AG23 G2).
  assert (L14 : getr R3 14 = Z_to_bv 64 cellp) by (agk AG3 F14).
  assert (SOKc2 : store_ok SEGS m2 (Z_to_bv 64 cellp) 4 = true) by (apply (W_sok_win C A m2 md); [exact CK | exact W2 | lia | cbn; lia]).
  assert (SL : forall (k : reg) (o : Z), In (k, o) [(1%bv, 8%Z); (8%bv, 16%Z); (9%bv, 24%Z); (18%bv, 32%Z); (19%bv, 40%Z); (20%bv, 48%Z);
                                                   (21%bv, 56%Z); (22%bv, 64%Z); (23%bv, 72%Z); (24%bv, 80%Z); (25%bv, 88%Z); (26%bv, 96%Z);
                                                   (27%bv, 104%Z)] ->
               rdn SEGS m2 (Z_to_bv 64 (s - o)) 8 = Some (Z_to_le_bytes 8 (u (getr regs k)))).
  { intros k o Hin. cbn [In] in Hin.
    repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; unfold m2, m1, GVB, GVA, FRG; rdout;
                                        rewrite rdn_wbytes_hit8 by (rewrite u_Z2bv by lia; lia); rewrite w2b_u; reflexivity|]).
    destruct Hin. }
  destruct (gv_E al_rom fx R3 m2 s cellp e' (u (getr regs 1)) (u (getr regs 8)) (u (getr regs 9)) (u (getr regs 18)) (u (getr regs 19))
              (u (getr regs 20)) (u (getr regs 21)) (u (getr regs 22)) (u (getr regs 23)) (u (getr regs 24)) (u (getr regs 25))
              (u (getr regs 26)) (u (getr regs 27)) ltac:(lia) ltac:(lia) Hc4 ltac:(lia) He' ltac:(rewrite Z_to_bv_bv_unsigned, H1; exact Hret)
              (u_rng _) (u_rng _) (u_rng _) (u_rng _) (u_rng _) (u_rng _) (u_rng _) (u_rng _) (u_rng _) (u_rng _) (u_rng _) (u_rng _) (u_rng _)
               SOKc2 (SL 1%bv 8%Z ltac:(cbn [In]; repeat first [left; reflexivity | right])) (SL 8%bv 16%Z ltac:(cbn [In]; repeat first [left; reflexivity | right]))
               (SL 9%bv 24%Z ltac:(cbn [In]; repeat first [left; reflexivity | right])) (SL 18%bv 32%Z ltac:(cbn [In]; repeat first [left; reflexivity | right]))
               (SL 19%bv 40%Z ltac:(cbn [In]; repeat first [left; reflexivity | right])) (SL 20%bv 48%Z ltac:(cbn [In]; repeat first [left; reflexivity | right]))
               (SL 21%bv 56%Z ltac:(cbn [In]; repeat first [left; reflexivity | right])) (SL 22%bv 64%Z ltac:(cbn [In]; repeat first [left; reflexivity | right]))
               (SL 23%bv 72%Z ltac:(cbn [In]; repeat first [left; reflexivity | right])) (SL 24%bv 80%Z ltac:(cbn [In]; repeat first [left; reflexivity | right]))
               (SL 25%bv 88%Z ltac:(cbn [In]; repeat first [left; reflexivity | right])) (SL 26%bv 96%Z ltac:(cbn [In]; repeat first [left; reflexivity | right]))
               (SL 27%bv 104%Z ltac:(cbn [In]; repeat first [left; reflexivity | right])) L2 L14 K12)
    as (R4 & M4 & E2 & E1 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27 & E10 & AG4).
  rewrite Z_to_bv_bv_unsigned, H1 in M4.
  set (m4 := wbytes m2 (Z_to_bv 64 cellp) (word_to_le_bytes 4 (Z_to_bv 64 e'))) in *.
  assert (AGall : regs_agree (fun x => In x [1; 2; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%list) regs R4).
  { assert (AG13 : regs_agree (fun x => In x [1; 2; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 28; 29; 30; 31]%list) regs R3)
      by (agc AG1 AG23).
    agc AG13 AG4. }
  pose proof WP as [MH ML _].
  eapply rz_msteps; [exact MH | exact ML | |].
  { eapply msteps_trans; [exact M1|]. eapply msteps_trans; [exact M2|]. eapply msteps_trans; [exact M3|]. exact M4. }
  apply (POST m4 R4 e').
  - unfold m4, m2, m1, GVB, GVA, FRG.
    repeat (apply W_store_win; [exact CK | | rewrite u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia]).
    exact HW.
  - apply cs_kept_intro.
    + rewrite E2, H2; reflexivity.
    + agk AGall (eq_refl (getr regs 3)).
    + agk AGall (eq_refl (getr regs 4)).
    + rewrite E8, Z_to_bv_bv_unsigned; reflexivity.
    + rewrite E9, Z_to_bv_bv_unsigned; reflexivity.
    + rewrite E18, Z_to_bv_bv_unsigned; reflexivity.
    + rewrite E19, Z_to_bv_bv_unsigned; reflexivity.
    + rewrite E20, Z_to_bv_bv_unsigned; reflexivity.
    + rewrite E21, Z_to_bv_bv_unsigned; reflexivity.
    + rewrite E22, Z_to_bv_bv_unsigned; reflexivity.
    + rewrite E23, Z_to_bv_bv_unsigned; reflexivity.
    + rewrite E24, Z_to_bv_bv_unsigned; reflexivity.
    + rewrite E25, Z_to_bv_bv_unsigned; reflexivity.
    + rewrite E26, Z_to_bv_bv_unsigned; reflexivity.
    + rewrite E27, Z_to_bv_bv_unsigned; reflexivity.
  - exact He'.
  - unfold m4. rewrite rdn_wbytes_hit4 by (rewrite u_Z2bv by lia; lia). rewrite w2b_Z by lia. reflexivity.
  - intros a Hns Hnc. unfold scratch in Hns. unfold m4, m2, m1, GVB, GVA, FRG. wout. reflexivity.
Qed.

End GevW.
