(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.bilateral_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptArith2 GrayACELib.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2LeptStderr V2LeptBase V2LeptErr V2LeptPixHdr V2LeptPixCreate V2LeptPixCreateT2 V2LeptPixCreateST V2LeptCmap2 V2LeptPixCopy V2LeptGrayA
  V2LeptRgbcSegs V2LeptBl2_iface V2LeptPixCopyT.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import LeptRoom LeptRoomBL LeptRop2Arith LeptRgbLib.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2_code_pixGetRGBComponent.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import LeptExecW.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2LeptUb V2LeptGev.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac rc_rdout := repeat (rewrite rdn_wbytes_out_Z by (rewrite ?length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia)).

Section RgbcW.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V2Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
Lemma rc_col : forall k regs M (s j w lines lined comp dlo dhi : Z),
  (256 <= s < 2 ^ 63)%Z -> (0 <= j < w)%Z -> Z.of_nat k = (w - j)%Z -> (w <= 20000)%Z -> (0 <= comp <= 2)%Z ->
  (4096 <= lines)%Z -> (lines + 4 * w + 4 < 2 ^ 61)%Z -> (4096 <= lined)%Z -> (lined + w + 4 <= s - 96)%Z ->
  (0 <= dlo)%Z -> (dhi <= s - 96)%Z ->
  (forall q, (j <= q < w)%Z -> dlo <= xor3 (lined + q) /\ xor3 (lined + q) + 1 <= dhi)%Z ->
  (forall q, (j <= q < w)%Z -> ~ (dlo <= xor3 (lines + comp + 4 * q) < dhi))%Z ->
  (forall q, (j <= q < w)%Z -> exists v, (0 <= v <= 255)%Z /\ rdn SEGS M (Z_to_bv 64 (xor3 (lines + comp + 4 * q))) 1 = Some (Z_to_le_bytes 1 v)) ->
  store_ok SEGS M (Z_to_bv 64 dlo) (Z.to_nat (dhi - dlo)) = true ->
  rdn SEGS M (Z_to_bv 64 (s - 84)) 4 = Some (Z_to_le_bytes 4 w) ->
  getr regs 2 = Z_to_bv 64 (s - 96) -> getr regs 19 = Z_to_bv 64 lines -> getr regs 20 = Z_to_bv 64 (lines + comp) ->
  getr regs 21 = Z_to_bv 64 (lines + comp) -> getr regs 22 = Z_to_bv 64 (lined + j) -> getr regs 29 = Z_to_bv 64 (4 * j) ->
  getr regs 30 = Z_to_bv 64 j -> getr regs 31 = Z_to_bv 64 lined -> getr regs 7 = Z_to_bv 64 lines -> getr regs 28 = Z_to_bv 64 lined ->
  getr regs 14 = Z_to_bv 64 1 -> getr regs 15 = Z_to_bv 64 1 -> getr regs 5 = Z_to_bv 64 3 ->
  exists regs' M',
    msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1b874) M al_rom) (@mkst fx regs' (Z_to_bv 64 0x1b7cc) M' al_rom)
    /\ winside dlo dhi M M'
    /\ regs_agree (fun x => In x [22; 23; 24; 29; 30]%list) regs regs'.
Proof.
  induction k as [|k IH]; intros regs M s j w lines lined comp dlo dhi Hs Hj Hk Hw Hc Hl1 Hl2 Hd1 Hd2 Hlo Hhi Hdst Hsrc Hrd SOK Rw
    H2 H19 H20 H21 H22 H29 H30 H31 H7 H28 H14 H15 H5.
  { cbn [Z.of_nat] in Hk. lia. }
  destruct (Hrd j ltac:(lia)) as (v & Hv & R).
  destruct (Hdst j ltac:(lia)) as [Ha1 Ha2].
  assert (SOKj : store_ok SEGS M (Z_to_bv 64 (xor3 (lined + j))) 1 = true).
  { eapply store_ok_sub; [ | exact SOK | | ]; rewrite ?u_Z2bv by lia; rewrite ?Z2Nat.id by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia. }
  assert (WI1 : winside dlo dhi M (wbytes M (Z_to_bv 64 (xor3 (lined + j))) (word_to_le_bytes 1 (Z_to_bv 64 v)))).
  { apply winside_one; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia. }
  destruct (Z.eq_dec (j + 1) w) as [Elast | Nlast].
  - destruct (rc_I al_rom true fx regs M s lines lined comp j w v Hs Hl1 Hl2 Hd1 Hd2 Hc Hj Hw Hv Elast R SOKj Rw
                 H2 H19 H20 H21 H22 H29 H30 H31 H7 H28 H14 H15 H5) as (R1 & M1 & F22 & F29 & F30 & AG1).
    exists R1, (wbytes M (Z_to_bv 64 (xor3 (lined + j))) (word_to_le_bytes 1 (Z_to_bv 64 v))).
    split; [exact M1|]. split; [exact WI1 | exact AG1].
  - destruct (rc_I al_rom false fx regs M s lines lined comp j w v Hs Hl1 Hl2 Hd1 Hd2 Hc Hj Hw Hv
                 ltac:(cbv beta iota; lia) R SOKj Rw H2 H19 H20 H21 H22 H29 H30 H31 H7 H28 H14 H15 H5) as (R1 & M1 & F22 & F29 & F30 & AG1).
    assert (K2 : getr R1 2 = Z_to_bv 64 (s - 96)) by (agk AG1 H2).
    assert (K19 : getr R1 19 = Z_to_bv 64 lines) by (agk AG1 H19).
    assert (K20 : getr R1 20 = Z_to_bv 64 (lines + comp)) by (agk AG1 H20).
    assert (K21 : getr R1 21 = Z_to_bv 64 (lines + comp)) by (agk AG1 H21).
    assert (K31 : getr R1 31 = Z_to_bv 64 lined) by (agk AG1 H31).
    assert (K7 : getr R1 7 = Z_to_bv 64 lines) by (agk AG1 H7).
    assert (K28 : getr R1 28 = Z_to_bv 64 lined) by (agk AG1 H28).
    assert (K14 : getr R1 14 = Z_to_bv 64 1) by (agk AG1 H14).
    assert (K15 : getr R1 15 = Z_to_bv 64 1) by (agk AG1 H15).
    assert (K5 : getr R1 5 = Z_to_bv 64 3) by (agk AG1 H5).
    assert (Hrd' : forall q, (j + 1 <= q < w)%Z -> exists vq, (0 <= vq <= 255)%Z /\
               rdn SEGS (wbytes M (Z_to_bv 64 (xor3 (lined + j))) (word_to_le_bytes 1 (Z_to_bv 64 v)))
                   (Z_to_bv 64 (xor3 (lines + comp + 4 * q))) 1 = Some (Z_to_le_bytes 1 vq)).
    { intros q Hq. destruct (Hrd q ltac:(lia)) as (vq & Hvq & Rq). exists vq. split; [exact Hvq|].
      pose proof (Hsrc q ltac:(lia)) as Nq. pose proof (xor3_range (lines + comp + 4 * q) ltac:(lia)) as Xq.
      pose proof (Z.mod_pos_bound (lines + comp + 4 * q) 4 ltac:(lia)) as Mq.
      rewrite rdn_wbytes_out_Z; [exact Rq|]. rewrite length_N_to_le_bytes. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia. }
    assert (SOK1 : store_ok SEGS (wbytes M (Z_to_bv 64 (xor3 (lined + j))) (word_to_le_bytes 1 (Z_to_bv 64 v)))
                     (Z_to_bv 64 dlo) (Z.to_nat (dhi - dlo)) = true).
    { eapply store_ok_mono; [eapply winside_grows; exact WI1 | exact SOK]. }
    assert (Rw1 : rdn SEGS (wbytes M (Z_to_bv 64 (xor3 (lined + j))) (word_to_le_bytes 1 (Z_to_bv 64 v))) (Z_to_bv 64 (s - 84)) 4
                  = Some (Z_to_le_bytes 4 w)).
    { eapply winside_rdn; [exact WI1 | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | exact Rw]. }
    destruct (IH R1 _ s (j + 1)%Z w lines lined comp dlo dhi Hs ltac:(lia) ltac:(lia) Hw Hc Hl1 Hl2 Hd1 Hd2 Hlo Hhi
                 (fun q Hq => Hdst q ltac:(lia)) (fun q Hq => Hsrc q ltac:(lia)) Hrd' SOK1 Rw1
                 K2 K19 K20 K21 F22 F29 F30 K31 K7 K28 K14 K15 K5) as (R2 & M2 & MS2 & WI2 & AG2).
    exists R2, M2. split; [eapply msteps_trans; [exact M1 | exact MS2]|].
    split; [eapply winside_trans; [exact WI1 | exact WI2]|]. agc AG1 AG2.
Qed.

(* [comment removed for export] *)
Lemma rc_rows : forall k regs M (s i h w comp datas wpls datad wpld : Z),
  (256 <= s < 2 ^ 63)%Z -> (0 <= i < h)%Z -> Z.of_nat k = (h - i)%Z -> (h <= 20000)%Z -> (1 <= w <= 20000)%Z -> (0 <= comp <= 2)%Z ->
  (datas mod 4 = 0)%Z -> (4096 <= datas)%Z -> (w <= wpls)%Z -> (wpls * h <= 2 ^ 24)%Z -> (datas + 2 ^ 27 < 2 ^ 61)%Z ->
  (datad mod 4 = 0)%Z -> (4096 <= datad)%Z -> (0 <= wpld)%Z -> (w <= 4 * wpld)%Z -> (wpld * h <= 2 ^ 24)%Z -> (datad + 2 ^ 27 < 2 ^ 61)%Z ->
  (datad + 4 * (wpld * h) + 4 <= s - 96)%Z ->
  (datas + 4 * (wpls * h) <= datad \/ datad + 4 * (wpld * h) <= datas)%Z ->
  (forall a, (datas <= a < datas + 4 * (wpls * h))%Z -> exists v, (0 <= v <= 255)%Z /\ rdn SEGS M (Z_to_bv 64 a) 1 = Some (Z_to_le_bytes 1 v)) ->
  store_ok SEGS M (Z_to_bv 64 datad) (Z.to_nat (4 * (wpld * h))) = true ->
  rdn SEGS M (Z_to_bv 64 (s - 84)) 4 = Some (Z_to_le_bytes 4 w) ->
  rdn SEGS M (Z_to_bv 64 (s - 88)) 4 = Some (Z_to_le_bytes 4 h) ->
  getr regs 2 = Z_to_bv 64 (s - 96) -> getr regs 13 = Z_to_bv 64 i -> getr regs 11 = Z_to_bv 64 (i * wpls) -> getr regs 12 = Z_to_bv 64 (i * wpld) ->
  getr regs 8 = Z_to_bv 64 wpls -> getr regs 9 = Z_to_bv 64 wpld -> getr regs 18 = Z_to_bv 64 datas -> getr regs 10 = Z_to_bv 64 datad ->
  getr regs 14 = Z_to_bv 64 1 -> getr regs 15 = Z_to_bv 64 1 -> getr regs 17 = Z_to_bv 64 (datas + comp) -> getr regs 16 = Z_to_bv 64 comp ->
  getr regs 5 = Z_to_bv 64 3 ->
  exists regs' M',
    msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1b7e0) M al_rom) (@mkst fx regs' (Z_to_bv 64 0x1b8e4) M' al_rom)
    /\ winside datad (datad + 4 * (wpld * h)) M M'
    /\ regs_agree (fun x => In x [7; 11; 12; 13; 19; 20; 21; 22; 23; 24; 28; 29; 30; 31]%list) regs regs'.
Proof.
  induction k as [|k IH]; intros regs M s i h w comp datas wpls datad wpld Hs Hi Hk Hh Hw Hc Hs4 Hs1 Hws Hwsh Hs2 Hd4 Hd1 Hwd0 Hwd Hwdh Hd2
    Hdf Hdisj Hrd SOK Rw Rh H2 H13 H11 H12 H8 H9 H18 H10 H14 H15 H17 H16 H5.
  { cbn [Z.of_nat] in Hk. lia. }
  assert (Hiws : (0 <= i * wpls /\ (i + 1) * wpls <= wpls * h)%Z) by nia.
  assert (Hiwd : (0 <= i * wpld /\ (i + 1) * wpld <= wpld * h)%Z) by nia.
  destruct (rc_OH al_rom fx regs M s i h w wpls wpld datas datad comp Hs Hi Hh Hw ltac:(lia) Hwd0 Hwsh Hwdh Hs1 ltac:(lia) Hd1 ltac:(lia) Hc Rw
              H2 H13 H11 H12 H8 H9 H18 H10 H14 H15 H17 H16 H5)
    as (R1 & MS1 & G7 & G19 & G20 & G21 & G22 & G28 & G31 & G29 & G30 & AG1).
  assert (XD : forall q, (0 <= q < w)%Z ->
            (datad <= xor3 (datad + 4 * (i * wpld) + q) /\ xor3 (datad + 4 * (i * wpld) + q) + 1 <= datad + 4 * (wpld * h))%Z).
  { intros q Hq. pose proof (xor3_in_raster datad wpld h w i q Hd4 Hwd0 Hwd Hi Hq ltac:(lia)) as X.
    replace (datad + 4 * wpld * i + q)%Z with (datad + 4 * (i * wpld) + q)%Z in X by lia. lia. }
  assert (XS : forall q, (0 <= q < w)%Z ->
            (datas <= xor3 (datas + 4 * (i * wpls) + comp + 4 * q) /\ xor3 (datas + 4 * (i * wpls) + comp + 4 * q) + 1 <= datas + 4 * (wpls * h))%Z).
  { intros q Hq. pose proof (xor3c_in_raster datas wpls h i q comp Hs4 ltac:(lia) Hi ltac:(lia) ltac:(lia) ltac:(lia)) as X.
    unfold xor3. replace (datas + 4 * (i * wpls) + comp + 4 * q)%Z with (datas + 4 * wpls * i + 4 * q + comp)%Z by lia. lia. }
  assert (K2 : getr R1 2 = Z_to_bv 64 (s - 96)) by (agk AG1 H2).
  assert (K14 : getr R1 14 = Z_to_bv 64 1) by (agk AG1 H14).
  assert (K15 : getr R1 15 = Z_to_bv 64 1) by (agk AG1 H15).
  assert (K5 : getr R1 5 = Z_to_bv 64 3) by (agk AG1 H5).
  destruct (rc_col (Z.to_nat w) R1 M s 0 w (datas + 4 * (i * wpls)) (datad + 4 * (i * wpld)) comp datad (datad + 4 * (wpld * h))
              Hs ltac:(lia) ltac:(rewrite Z2Nat.id; lia) ltac:(lia) Hc ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
              (fun q Hq => XD q ltac:(lia))
              (fun q Hq => ltac:(pose proof (XS q ltac:(lia)); lia))
              (fun q Hq => Hrd (xor3 (datas + 4 * (i * wpls) + comp + 4 * q)) ltac:(pose proof (XS q ltac:(lia)); lia))
              ltac:(replace (datad + 4 * (wpld * h) - datad)%Z with (4 * (wpld * h))%Z by lia; exact SOK) Rw
              K2 G19 G20 G21 ltac:(rewrite G22; f_equal; lia) ltac:(rewrite G29; f_equal; lia) G30 G31 G7 G28 K14 K15 K5)
    as (R2 & M2 & MS2 & WI2 & AG2).
  assert (AG12 : regs_agree (fun x => In x [7; 19; 20; 21; 22; 23; 24; 28; 29; 30; 31]%list) regs R2) by (agc AG1 AG2).
  assert (L2 : getr R2 2 = Z_to_bv 64 (s - 96)) by (agk AG12 H2).
  assert (L13 : getr R2 13 = Z_to_bv 64 i) by (agk AG12 H13).
  assert (L8 : getr R2 8 = Z_to_bv 64 wpls) by (agk AG12 H8).
  assert (L9 : getr R2 9 = Z_to_bv 64 wpld) by (agk AG12 H9).
  assert (L11 : getr R2 11 = Z_to_bv 64 (i * wpls)) by (agk AG12 H11).
  assert (L12 : getr R2 12 = Z_to_bv 64 (i * wpld)) by (agk AG12 H12).
  assert (Rh2 : rdn SEGS M2 (Z_to_bv 64 (s - 88)) 4 = Some (Z_to_le_bytes 4 h)).
  { eapply winside_rdn; [exact WI2 | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | exact Rh]. }
  destruct (Z.eq_dec (i + 1) h) as [Elast | Nlast].
  - destruct (rc_ON al_rom true fx R2 M2 s i h wpls wpld Hs Hi Hh ltac:(lia) Hwd0 Hwsh Hwdh Elast Rh2 L2 L13 L8 L9 L11 L12)
      as (R3 & MS3 & _ & _ & _ & AG3).
    exists R3, M2. split; [eapply msteps_trans; [exact MS1 | eapply msteps_trans; [exact MS2 | exact MS3]]|].
    split; [exact WI2|]. agc AG12 AG3.
  - destruct (rc_ON al_rom false fx R2 M2 s i h wpls wpld Hs Hi Hh ltac:(lia) Hwd0 Hwsh Hwdh ltac:(cbv beta iota; lia) Rh2 L2 L13 L8 L9 L11 L12)
      as (R3 & MS3 & F13 & F11 & F12 & AG3).
    assert (AG123 : regs_agree (fun x => In x [7; 11; 12; 13; 19; 20; 21; 22; 23; 24; 28; 29; 30; 31]%list) regs R3) by (agc AG12 AG3).
    assert (Hrd' : forall a, (datas <= a < datas + 4 * (wpls * h))%Z -> exists v, (0 <= v <= 255)%Z /\ rdn SEGS M2 (Z_to_bv 64 a) 1 = Some (Z_to_le_bytes 1 v)).
    { intros a Ha. destruct (Hrd a Ha) as (va & Hva & Ra). exists va. split; [exact Hva|].
      eapply winside_rdn; [exact WI2 | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | exact Ra]. }
    assert (SOK2 : store_ok SEGS M2 (Z_to_bv 64 datad) (Z.to_nat (4 * (wpld * h))) = true).
    { eapply store_ok_mono; [eapply winside_grows; exact WI2 | exact SOK]. }
    assert (Rw2 : rdn SEGS M2 (Z_to_bv 64 (s - 84)) 4 = Some (Z_to_le_bytes 4 w)).
    { eapply winside_rdn; [exact WI2 | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | exact Rw]. }
    destruct (IH R3 M2 s (i + 1)%Z h w comp datas wpls datad wpld Hs ltac:(lia) ltac:(lia) Hh Hw Hc Hs4 Hs1 Hws Hwsh Hs2 Hd4 Hd1 Hwd0 Hwd Hwdh Hd2
                 Hdf Hdisj Hrd' SOK2 Rw2 Rh2
                 ltac:(agk AG123 H2) F13 F11 F12 ltac:(agk AG123 H8) ltac:(agk AG123 H9) ltac:(agk AG123 H18) ltac:(agk AG123 H10)
                 ltac:(agk AG123 H14) ltac:(agk AG123 H15) ltac:(agk AG123 H17) ltac:(agk AG123 H16) ltac:(agk AG123 H5))
      as (R4 & M4 & MS4 & WI4 & AG4).
    exists R4, M4. split.
    { eapply msteps_trans; [exact MS1|]. eapply msteps_trans; [exact MS2|]. eapply msteps_trans; [exact MS3 | exact MS4]. }
    split; [eapply winside_trans; [exact WI2 | exact WI4]|]. agc AG123 AG4.
Qed.

(* [comment removed for export] *)
Theorem pixGetRGBComponent_W : pixGetRGBComponent_contract.
Proof.
  unfold pixGetRGBComponent_contract.
  intros C A m md regs s pixs w h datas comp ret S CK HW H2 Hs16 Hstk Hsc H1 Hret H4 H10 H11 Hc PXs Hhdr Hw1 Hh1 Lps Lds kR bR Hrm Hrk Hrb HK.
  pose proof CK as [Ctop Csp0 Csp0hi Cal Cimg].
  pose proof LSTK_val as LS. unfold RGB_STACK, LSF in Hstk.
  pose proof Hhdr as (DV & Hw20 & Hh20 & Hsz).
  assert (Ws : wpl_of w 32 = w).
  { unfold wpl_of. rewrite Z.div_add_l by lia. change (31 / 32)%Z with 0%Z. lia. }
  rewrite Ws in Hsz, Lds.
  assert (Hwpd : (1 <= wpl_of w 8 /\ w <= 4 * wpl_of w 8 /\ wpl_of w 8 <= w)%Z).
  { unfold wpl_of. pose proof (Z.div_mod (w * 8 + 31) 32 ltac:(lia)). pose proof (Z.mod_pos_bound (w * 8 + 31) 32 ltac:(lia)). lia. }
  assert (Hwh : (w * h <= 2 ^ 24)%Z) by lia.
  assert (Hwdh : (wpl_of w 8 * h <= 2 ^ 24)%Z) by nia.
  assert (HOK8 : hdr_ok w h 8).
  { unfold hdr_ok. split; [right; right; right; left; reflexivity|]. split; [lia|]. split; [lia|]. nia. }
  assert (KEEP : forall M M' p v, LIVK A M M' -> live A (Z_to_bv 64 p) = Some 64%Z -> PIXat M p v -> PIXat M' p v).
  { intros M M' p v LK Lp PX. pose proof PX as (P0 & P64 & _). apply (PIXat_frame M); [exact PX|].
    intros x Hx. exact (LIVK_at A M M' p 64 x LK Lp ltac:(lia) ltac:(lia) Hx). }
  pose proof PXs as (Hps0 & Hps64 & WFs & _).
  pose proof (wf_data _ WFs) as Hds. cbn [p_data hdv] in Hds.
  pose proof HW as [WI WP _ _ _ _ _ _ _ _ _].
  pose proof (blk_range C A m md (Z_to_bv 64 pixs) 64 CK HW Lps ltac:(lia)) as BRps. rewrite u_Z2bv in BRps by lia.
  pose proof (blk_range C A m md (Z_to_bv 64 datas) _ CK HW Lds ltac:(nia)) as BRds. rewrite u_Z2bv in BRds by lia.
  pose proof (ai_live_hull _ _ _ _ _ WI Lps) as (_ & ALps & _ & _). rewrite u_Z2bv in ALps by lia.
  pose proof (ai_live_hull _ _ _ _ _ WI Lds) as (_ & ALds & _ & DEFs). rewrite u_Z2bv in ALds by lia.
  pose proof (round16_ge (4 * (w * h)) ltac:(nia)) as RGs.
  pose proof (round16_ge (4 * (wpl_of w 8 * h)) ltac:(nia)) as RGd.
  pose proof (round16_ge 64 ltac:(lia)) as RG64.
  assert (Hpm8s : (pixs mod 8 = 0)%Z) by (apply al16_mod8; exact ALps).
  assert (Hdm4s : (datas mod 4 = 0)%Z) by (apply mod16_mod4; exact ALds).
  assert (SOKf : store_ok SEGS m (Z_to_bv 64 (s - 96)) 96 = true) by (apply (W_sok_win C A m md); [exact CK | exact HW | lia | cbn; lia]).
  assert (Rcm : rdn SEGS m (Z_to_bv 64 (pixs + 48)) 8 = Some (Z_to_le_bytes 8 0))
    by (pose proof (PIX_rd_cmap SEGS _ _ _ PXs) as X; cbn [p_cmap hdv] in X; exact X).
  destruct (rc_A al_rom fx regs m s pixs comp w h ltac:(lia) Hs16 ltac:(lia) ltac:(lia) Hpm8s Hc ltac:(lia) ltac:(lia) SOKf
              ltac:(pose proof (PIX_rd_w SEGS _ _ _ PXs) as X; cbn [p_w hdv] in X; exact X)
              ltac:(pose proof (PIX_rd_h SEGS _ _ _ PXs) as X; cbn [p_h hdv] in X; exact X)
              ltac:(pose proof (PIX_rd_d SEGS _ _ _ PXs) as X; cbn [p_d hdv] in X; exact X)
              Rcm ltac:(lia) H2 H10 H11)
    as (R1 & MS1 & G2 & G1 & G10 & G11 & G12 & G18 & G19 & AG1).
  unfold PC_pixGetRGBComponent.
  eapply rz_msteps; [exact (mp_halted _ WP) | exact (mp_lazy _ WP) | exact MS1 |].
  set (M1 := DIMc (FRM10 m s regs) s w h).
  assert (WP1 : W C A M1 md /\ POSTM C A s m M1) by (subst M1; unfold DIMc, FRM10; wp_win CK).
  destruct WP1 as [HW1 PM1].
  assert (M1w : rdn SEGS M1 (Z_to_bv 64 (s - 84)) 4 = Some (Z_to_le_bytes 4 w)).
  { subst M1. unfold DIMc. rc_rdout. rewrite rdn_wbytes_hit4 by (rewrite u_Z2bv by lia; lia). rewrite w2b_u, u_Z2bv by lia. reflexivity. }
  assert (M1h : rdn SEGS M1 (Z_to_bv 64 (s - 88)) 4 = Some (Z_to_le_bytes 4 h)).
  { subst M1. unfold DIMc. rewrite rdn_wbytes_hit4 by (rewrite u_Z2bv by lia; lia). rewrite w2b_u, u_Z2bv by lia. reflexivity. }
  assert (T4 : getr R1 4 = Z_to_bv 64 0x56270) by (agk AG1 H4).
  replace (Z_to_bv 64 0x192d0) with (0x192d0 : word) by (apply bv_eq; reflexivity).
  apply (pixCreate_sureT_W C A M1 md R1 (s - 96) w h 8 (Z_to_bv 64 0x1b758) S CK HW1 G2
           ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold LSF; lia) ltac:(lia) G1 ltac:(red; apply bv_eq; reflexivity)
           T4 G10 G11 G12 Hw1 Hh1 HOK8 kR bR Hrm Hrk Hrb).
  intros A1 m1 vm1 R2 pixd datad HW2 CS2 PM2 R10 PN Hrm1.
  destruct PN as (Gp & TOPp & ALp & Gd & TOPd & ALd & NEpd & L0 & K0 & L00 & K00 & L1 & K1 & LEQ & PX1 & _).
  cbn [p_wpl p_h p_data set_data pix_hdr] in TOPd, K1.
  assert (SUB1 : sub_live A A1) by exact (sub_live_new2 _ _ _ _ _ _ L0 K0 L1 K1 LEQ).
  assert (ALp8 : (pixd mod 8 = 0)%Z) by (apply al16_mod8; exact ALp).
  assert (ALd4 : (datad mod 4 = 0)%Z) by (apply mod16_mod4; exact ALd).
  assert (B18 : getr R2 18 = Z_to_bv 64 pixs) by (csr; reflexivity).
  destruct (rc_B al_rom fx R2 m1 pixd pixs ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) R10 B18)
    as (R3 & MS3 & E1 & E10 & E11 & E20 & AG3).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact MS3 |].
  pose proof (KEEP M1 m1 pixs _ (proj2 PM2) Lps (KEEP m M1 pixs _ (proj2 PM1) Lps PXs)) as PXs2.
  replace (Z_to_bv 64 0x19bf4) with (0x19bf4 : word) by (apply bv_eq; reflexivity).
  destruct (pixCopyResolution_run al_rom R3 m1 pixd pixs (hdv w h 32 0 datas) (set_data (pix_hdr w h 8) datad) (Z_to_bv 64 0x1b768)
              ltac:(lia) ltac:(lia) ltac:(intros E; rewrite E in Lps; congruence) Hpm8s ALp8 PXs2 PX1 eq_refl eq_refl
              (blk_sok C A1 m1 (with_vmmaps vm1 md) pixd 64 CK HW2 L1 ltac:(lia) ltac:(lia) ltac:(lia))
              ltac:(red; apply bv_eq; reflexivity) E1 E10 E11) as (R4 & MS4 & F10 & AG4).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact MS4 |].
  set (M3 := wbytes m1 (Z_to_bv 64 (pixd + 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))).
  assert (WP3 : W C A1 M3 (with_vmmaps vm1 md) /\ POSTM C A (s - 96) m1 M3).
  { subst M3. apply (WP_blk C A A1 m1 m1 (with_vmmaps vm1 md) (Z_to_bv 64 pixd) (Z_to_bv 64 (pixd + 24)) 64 _ (s - 96) CK
                   (conj HW2 (POSTM_refl _ _ _ _)) L1 L0 L00 SUB1); rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; lia. }
  destruct WP3 as [HW3 PM3].
  assert (PXd3 : PIXat M3 pixd (set_data (pix_hdr w h 8) datad)) by (subst M3; exact (PIX_wr_res0 m1 pixd _ PX1 eq_refl eq_refl)).
  pose proof (KEEP m1 M3 pixs _ (proj2 PM3) Lps PXs2) as PXs3.
  assert (PMs : POSTM C A s m M3).
  { eapply POSTM_trans; [exact PM1|]. apply (POSTM_mono C A (s - 96) s); [lia|]. eapply POSTM_trans; [exact PM2 | exact PM3]. }
  assert (FR : forall (a : Z) (n : nat), (s - 96 <= a)%Z -> (a + Z.of_nat n <= 2 ^ 64)%Z ->
                 rdn SEGS M3 (Z_to_bv 64 a) n = rdn SEGS M1 (Z_to_bv 64 a) n).
  { intros a n Ha1 Ha2. rewrite (FRM_rdn16 C (s - 96) m1 M3 a n CK (proj1 PM3)) by lia.
    exact (FRM_rdn16 C (s - 96) M1 m1 a n CK (proj1 PM2) ltac:(lia) ltac:(lia) ltac:(lia)). }
  assert (M3w : rdn SEGS M3 (Z_to_bv 64 (s - 84)) 4 = Some (Z_to_le_bytes 4 w))
    by (rewrite FR by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia); exact M1w).
  assert (M3h : rdn SEGS M3 (Z_to_bv 64 (s - 88)) 4 = Some (Z_to_le_bytes 4 h))
    by (rewrite FR by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia); exact M1h).
  assert (F2 : getr R4 2 = Z_to_bv 64 (s - 96)) by (csr; reflexivity).
  assert (F18 : getr R4 18 = Z_to_bv 64 pixs) by (csr; reflexivity).
  assert (F20 : getr R4 20 = Z_to_bv 64 pixd) by (csr; reflexivity).
  assert (F19 : getr R4 19 = Z_to_bv 64 comp) by (csr; reflexivity).
  destruct (rc_C al_rom fx R4 M3 s pixs pixd comp h w (wpl_of w 8) datas datad ltac:(lia) ltac:(lia) ltac:(lia) Hpm8s ltac:(lia) ltac:(lia) ALp8 Hc
              ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
              ltac:(pose proof (PIX_rd_wpl SEGS _ _ _ PXd3) as X; cbn [p_wpl set_data pix_hdr] in X; exact X)
              ltac:(pose proof (PIX_rd_data SEGS _ _ _ PXd3) as X; cbn [p_data set_data pix_hdr] in X; exact X)
              ltac:(pose proof (PIX_rd_wpl SEGS _ _ _ PXs3) as X; cbn [p_wpl hdv] in X; rewrite Ws in X; exact X)
              ltac:(pose proof (PIX_rd_data SEGS _ _ _ PXs3) as X; cbn [p_data hdv] in X; exact X)
              M3h F2 F18 F20 F19)
    as (R5 & MS5 & J2 & J5 & J6 & J8 & J9 & J10 & J11 & J12 & J13 & J14 & J15 & J16 & J17 & J18 & AG5).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW3)) | exact (mp_lazy _ (w_pure _ _ _ _ HW3)) | exact MS5 |].
  assert (RD : forall a, (datas <= a < datas + 4 * (w * h))%Z -> exists v, (0 <= v <= 255)%Z /\ rdn SEGS M3 (Z_to_bv 64 a) 1 = Some (Z_to_le_bytes 1 v)).
  { intros a Ha.
    specialize (DEFs (a - datas)%Z ltac:(lia)) as (_ & DEF & _). unfold at_ in DEF. rewrite u_Z2bv in DEF by lia.
    replace (datas + (a - datas))%Z with a in DEF by lia.
    pose proof (proj2 PMs (Z_to_bv 64 datas) _ (a - datas)%Z Lds ltac:(lia)) as EQ. unfold at_ in EQ. rewrite u_Z2bv in EQ by lia.
    replace (datas + (a - datas))%Z with a in EQ by lia.
    destruct (m (Z_to_bv 64 a)) as [b|] eqn:Eb; [|congruence].
    exists (bv_unsigned b). split; [apply byte_rng|]. apply byte_rdn1. exact EQ. }
  assert (SOKd : store_ok SEGS M3 (Z_to_bv 64 datad) (Z.to_nat (4 * (wpl_of w 8 * h))) = true).
  { apply (exW_sok_blk SEGS C A1 M3 (with_vmmaps vm1 md) datad (4 * (wpl_of w 8 * h)) datad _ p16_segs CK HW3 K1); rewrite ?Z2Nat.id by nia; lia. }
  pose proof (ai_live_disjoint _ _ _ _ _ _ _ (w_inv _ _ _ _ HW3) (SUB1 _ _ Lds) K1 ltac:(intros E; rewrite E in Lds; congruence)) as DJsd.
  rewrite !u_Z2bv in DJsd by lia.
  pose proof (ai_live_disjoint _ _ _ _ _ _ _ (w_inv _ _ _ _ HW3) L1 K1 (zneq_w pixd datad ltac:(lia) ltac:(lia) NEpd)) as DJpd.
  rewrite !u_Z2bv in DJpd by lia.
  destruct (rc_rows (Z.to_nat h) R5 M3 s 0 h w comp datas w datad (wpl_of w 8) ltac:(lia) ltac:(lia) ltac:(rewrite Z2Nat.id; lia) Hh20 ltac:(lia) Hc
              Hdm4s ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
              ALd4 ltac:(lia) ltac:(lia) ltac:(lia) Hwdh ltac:(lia) ltac:(lia) ltac:(lia) RD SOKd M3w M3h
              J2 J13 ltac:(rewrite J11; f_equal; lia) ltac:(rewrite J12; f_equal; lia) J8 J9 J18 J10 J14 J15 J17 J16 J5)
    as (R6 & M4 & MS6 & WI4 & AG6).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW3)) | exact (mp_lazy _ (w_pure _ _ _ _ HW3)) | exact MS6 |].
  assert (WP4 : W C A1 M4 (with_vmmaps vm1 md) /\ POSTM C A s m M4).
  { apply (winside_WP C A A1 m M3 M4 (with_vmmaps vm1 md) (Z_to_bv 64 datad) (4 * (wpl_of w 8 * h)) datad (datad + 4 * (wpl_of w 8 * h)) s CK
             (conj HW3 PMs) K1 K0 K00 SUB1);
      [rewrite u_Z2bv by lia; lia | rewrite u_Z2bv by lia; lia | exact WI4]. }
  assert (SL : forall (k : reg) (o : Z), In (k, o) [(1%bv, 8%Z); (8%bv, 16%Z); (9%bv, 24%Z); (18%bv, 32%Z); (19%bv, 40%Z); (20%bv, 48%Z);
                                                   (21%bv, 56%Z); (22%bv, 64%Z); (23%bv, 72%Z); (24%bv, 80%Z)] ->
               rdn SEGS M4 (Z_to_bv 64 (s - o)) 8 = Some (Z_to_le_bytes 8 (u (getr regs k)))).
  { intros k o Hin. cbn [In] in Hin.
    repeat (destruct Hin as [Hin|Hin];
            [injection Hin as <- <-; eapply winside_rdn; [exact WI4 | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia
                                                          | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia |];
             rewrite FR by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia);
             subst M1; unfold DIMc, FRM10; rc_rdout;
             rewrite rdn_wbytes_hit8 by (rewrite u_Z2bv by lia; lia); rewrite w2b_u; reflexivity|]).
    destruct Hin. }
  assert (L2 : getr R6 2 = Z_to_bv 64 (s - 96)) by (agk AG6 J2).
  assert (L6 : getr R6 6 = Z_to_bv 64 pixd) by (agk AG6 J6).
  destruct (rc_E al_rom fx R6 M4 s pixd (u (getr regs 1)) (u (getr regs 8)) (u (getr regs 9)) (u (getr regs 18)) (u (getr regs 19))
              (u (getr regs 20)) (u (getr regs 21)) (u (getr regs 22)) (u (getr regs 23)) (u (getr regs 24))
              ltac:(lia) ltac:(lia) ltac:(rewrite Z_to_bv_bv_unsigned, H1; exact Hret)
              (u_rng _) (u_rng _) (u_rng _) (u_rng _) (u_rng _) (u_rng _) (u_rng _) (u_rng _) (u_rng _) (u_rng _)
              (SL 1%bv 8%Z ltac:(cbn [In]; repeat first [left; reflexivity | right])) (SL 8%bv 16%Z ltac:(cbn [In]; repeat first [left; reflexivity | right]))
              (SL 9%bv 24%Z ltac:(cbn [In]; repeat first [left; reflexivity | right])) (SL 18%bv 32%Z ltac:(cbn [In]; repeat first [left; reflexivity | right]))
              (SL 19%bv 40%Z ltac:(cbn [In]; repeat first [left; reflexivity | right])) (SL 20%bv 48%Z ltac:(cbn [In]; repeat first [left; reflexivity | right]))
              (SL 21%bv 56%Z ltac:(cbn [In]; repeat first [left; reflexivity | right])) (SL 22%bv 64%Z ltac:(cbn [In]; repeat first [left; reflexivity | right]))
              (SL 23%bv 72%Z ltac:(cbn [In]; repeat first [left; reflexivity | right])) (SL 24%bv 80%Z ltac:(cbn [In]; repeat first [left; reflexivity | right]))
              L2 L6)
    as (R7 & MS7 & Q2 & Q1 & Q8 & Q9 & Q18 & Q19 & Q20 & Q21 & Q22 & Q23 & Q24 & Q10 & AG7).
  rewrite Z_to_bv_bv_unsigned, H1 in MS7.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW3)) | exact (mp_lazy _ (w_pure _ _ _ _ HW3)) | exact MS7 |].
  apply (HK A1 M4 vm1 R7 pixd datad (proj1 WP4)).
  - apply cs_kept_intro.
    + rewrite Q2, H2; reflexivity.
    + csr; reflexivity.
    + csr; reflexivity.
    + rewrite Q8, Z_to_bv_bv_unsigned; reflexivity.
    + rewrite Q9, Z_to_bv_bv_unsigned; reflexivity.
    + rewrite Q18, Z_to_bv_bv_unsigned; reflexivity.
    + rewrite Q19, Z_to_bv_bv_unsigned; reflexivity.
    + rewrite Q20, Z_to_bv_bv_unsigned; reflexivity.
    + rewrite Q21, Z_to_bv_bv_unsigned; reflexivity.
    + rewrite Q22, Z_to_bv_bv_unsigned; reflexivity.
    + rewrite Q23, Z_to_bv_bv_unsigned; reflexivity.
    + rewrite Q24, Z_to_bv_bv_unsigned; reflexivity.
    + csr; reflexivity.
    + csr; reflexivity.
    + csr; reflexivity.
  - exact (proj2 WP4).
  - exact Q10.
  - assert (PXd4 : PIXat M4 pixd (set_data (pix_hdr w h 8) datad)).
    { eapply PIXat_frame; [exact PXd3|]. intros x Hx. rewrite (winside_out _ _ _ _ x WI4) by lia. reflexivity. }
    unfold pixr_new. cbn [p_wpl p_h p_data set_data pix_hdr].
    repeat (split; [first [assumption | lia] |]); first [exact PXd4 | reflexivity | assumption].
  - exact Hrm1.
Qed.

End RgbcW.
