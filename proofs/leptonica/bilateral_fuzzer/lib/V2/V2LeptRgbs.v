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
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2LeptStderr V2LeptBase V2LeptErr V2LeptPixHdr V2LeptPixCreate V2LeptPixCreateT2 V2LeptCmap2 V2LeptPixCopy V2LeptGrayA
  V2LeptRgbsSegs V2LeptPixCopyT.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import LeptRoom LeptRoomBL LeptRop2Arith LeptRgbLib.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2_code_pixSetRGBComponent.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import LeptExecW.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2LeptUb V2LeptGev.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition PC_pixSetRGBComponent : Z := 0x1b95c.
Definition RGBS_STACK : Z := 112.

Ltac rs_wout := repeat (rewrite wbytes_outside by (rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia)).
Ltac rs_rdout := repeat (rewrite rdn_wbytes_out_Z by (rewrite ?length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia)).
Ltac rs_wp CK SUB :=
  repeat (apply WP_win; [exact CK | | exact SUB | rewrite u_Z2bv by lia; lia
                        | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | lia]).

Section RgbsW.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V2Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
Lemma rs_col : forall k regs M (j w lines lined comp dlo dhi : Z),
  (0 <= j < w)%Z -> Z.of_nat k = (w - j)%Z -> (w <= 20000)%Z -> (0 <= comp <= 2)%Z ->
  (4096 <= lines)%Z -> (lines + w < 2 ^ 62)%Z -> (4096 <= lined)%Z -> (lined + 4 * w + 4 < 2 ^ 62)%Z ->
  (0 <= dlo)%Z -> (dhi <= 2 ^ 64)%Z ->
  (forall q, (j <= q < w)%Z -> dlo <= xor3 (lined + comp + 4 * q) /\ xor3 (lined + comp + 4 * q) + 1 <= dhi)%Z ->
  (forall q, (j <= q < w)%Z -> ~ (dlo <= xor3 (lines + q) < dhi))%Z ->
  (forall q, (j <= q < w)%Z -> exists v, (0 <= v <= 255)%Z /\ rdn SEGS M (Z_to_bv 64 (xor3 (lines + q))) 1 = Some (Z_to_le_bytes 1 v)) ->
  store_ok SEGS M (Z_to_bv 64 dlo) (Z.to_nat (dhi - dlo)) = true ->
  getr regs 29 = Z_to_bv 64 (4 * j) -> getr regs 23 = Z_to_bv 64 (lines + j) -> getr regs 31 = Z_to_bv 64 (lines + j) ->
  getr regs 7 = Z_to_bv 64 lines -> getr regs 30 = Z_to_bv 64 lined -> getr regs 28 = Z_to_bv 64 lined ->
  getr regs 19 = Z_to_bv 64 (lined + comp) -> getr regs 22 = Z_to_bv 64 (lined + comp) -> getr regs 14 = Z_to_bv 64 1 ->
  getr regs 15 = Z_to_bv 64 1 -> getr regs 6 = Z_to_bv 64 3 -> getr regs 17 = Z_to_bv 64 (4 * w) ->
  exists regs' M',
    msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1bc90) M al_rom) (@mkst fx regs' (Z_to_bv 64 0x1bbf4) M' al_rom)
    /\ winside dlo dhi M M'
    /\ regs_agree (fun x => In x [23; 24; 25; 29; 31]%list) regs regs'.
Proof.
  induction k as [|k IH]; intros regs M j w lines lined comp dlo dhi Hj Hk Hw Hc Hl1 Hl2 Hd1 Hd2 Hlo Hhi Hdst Hsrc Hrd SOK
    H29 H23 H31 H7 H30 H28 H19 H22 H14 H15 H6 H17.
  { cbn [Z.of_nat] in Hk. lia. }
  destruct (Hrd j ltac:(lia)) as (v & Hv & R).
  destruct (Hdst j ltac:(lia)) as [Ha1 Ha2].
  assert (SOKj : store_ok SEGS M (Z_to_bv 64 (xor3 (lined + comp + 4 * j))) 1 = true).
  { eapply store_ok_sub; [ | exact SOK | | ]; rewrite ?u_Z2bv by lia; rewrite ?Z2Nat.id by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia. }
  assert (WI1 : winside dlo dhi M (wbytes M (Z_to_bv 64 (xor3 (lined + comp + 4 * j))) (word_to_le_bytes 1 (Z_to_bv 64 v)))).
  { apply winside_one; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia. }
  destruct (Z.eq_dec (j + 1) w) as [Elast | Nlast].
  - destruct (rs_I al_rom true fx regs M lines lined comp j w v Hl1 ltac:(lia) Hd1 ltac:(lia) Hc ltac:(lia) Hw Hv Elast R SOKj
                 H29 H23 H31 H7 H30 H28 H19 H22 H14 H15 H6 H17) as (R1 & M1 & F29 & F23 & F31 & AG1).
    exists R1, (wbytes M (Z_to_bv 64 (xor3 (lined + comp + 4 * j))) (word_to_le_bytes 1 (Z_to_bv 64 v))).
    split; [exact M1|]. split; [exact WI1 | exact AG1].
  - destruct (rs_I al_rom false fx regs M lines lined comp j w v Hl1 ltac:(lia) Hd1 ltac:(lia) Hc ltac:(lia) Hw Hv
                 ltac:(cbv beta iota; lia) R SOKj H29 H23 H31 H7 H30 H28 H19 H22 H14 H15 H6 H17) as (R1 & M1 & F29 & F23 & F31 & AG1).
    assert (K7 : getr R1 7 = Z_to_bv 64 lines) by (agk AG1 H7).
    assert (K30 : getr R1 30 = Z_to_bv 64 lined) by (agk AG1 H30).
    assert (K28 : getr R1 28 = Z_to_bv 64 lined) by (agk AG1 H28).
    assert (K19 : getr R1 19 = Z_to_bv 64 (lined + comp)) by (agk AG1 H19).
    assert (K22 : getr R1 22 = Z_to_bv 64 (lined + comp)) by (agk AG1 H22).
    assert (K14 : getr R1 14 = Z_to_bv 64 1) by (agk AG1 H14).
    assert (K15 : getr R1 15 = Z_to_bv 64 1) by (agk AG1 H15).
    assert (K6 : getr R1 6 = Z_to_bv 64 3) by (agk AG1 H6).
    assert (K17 : getr R1 17 = Z_to_bv 64 (4 * w)) by (agk AG1 H17).
    assert (Hrd' : forall q, (j + 1 <= q < w)%Z -> exists vq, (0 <= vq <= 255)%Z /\
               rdn SEGS (wbytes M (Z_to_bv 64 (xor3 (lined + comp + 4 * j))) (word_to_le_bytes 1 (Z_to_bv 64 v)))
                   (Z_to_bv 64 (xor3 (lines + q))) 1 = Some (Z_to_le_bytes 1 vq)).
    { intros q Hq. destruct (Hrd q ltac:(lia)) as (vq & Hvq & Rq). exists vq. split; [exact Hvq|].
      pose proof (Hsrc q ltac:(lia)) as Nq. pose proof (xor3_range (lines + q) ltac:(lia)) as Xq.
      rewrite rdn_wbytes_out_Z; [exact Rq|]. rewrite length_N_to_le_bytes. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia. }
    assert (SOK1 : store_ok SEGS (wbytes M (Z_to_bv 64 (xor3 (lined + comp + 4 * j))) (word_to_le_bytes 1 (Z_to_bv 64 v)))
                     (Z_to_bv 64 dlo) (Z.to_nat (dhi - dlo)) = true).
    { eapply store_ok_mono; [eapply winside_grows; exact WI1 | exact SOK]. }
    destruct (IH R1 _ (j + 1)%Z w lines lined comp dlo dhi ltac:(lia) ltac:(lia) Hw Hc Hl1 Hl2 Hd1 Hd2 Hlo Hhi
                 (fun q Hq => Hdst q ltac:(lia)) (fun q Hq => Hsrc q ltac:(lia)) Hrd' SOK1
                 F29 F23 F31 K7 K30 K28 K19 K22 K14 K15 K6 K17) as (R2 & M2 & MS2 & WI2 & AG2).
    exists R2, M2. split; [eapply msteps_trans; [exact M1 | exact MS2]|].
    split; [eapply winside_trans; [exact WI1 | exact WI2]|]. agc AG1 AG2.
Qed.

(* [comment removed for export] *)
Lemma rs_rows : forall k regs M (i h w comp datas wpls datad : Z),
  (0 <= i < h)%Z -> Z.of_nat k = (h - i)%Z -> (h <= 20000)%Z -> (1 <= w <= 20000)%Z -> (0 <= comp <= 2)%Z ->
  (datas mod 4 = 0)%Z -> (4096 <= datas)%Z -> (0 <= wpls)%Z -> (w <= 4 * wpls)%Z -> (wpls * h <= 2 ^ 24)%Z -> (datas + 2 ^ 27 < 2 ^ 62)%Z ->
  (datad mod 4 = 0)%Z -> (4096 <= datad)%Z -> (w * h <= 2 ^ 24)%Z -> (datad + 2 ^ 27 < 2 ^ 62)%Z ->
  (datas + 4 * (wpls * h) <= datad \/ datad + 4 * (w * h) <= datas)%Z ->
  (forall a, (datas <= a < datas + 4 * (wpls * h))%Z -> exists v, (0 <= v <= 255)%Z /\ rdn SEGS M (Z_to_bv 64 a) 1 = Some (Z_to_le_bytes 1 v)) ->
  store_ok SEGS M (Z_to_bv 64 datad) (Z.to_nat (4 * (w * h))) = true ->
  getr regs 13 = Z_to_bv 64 i -> getr regs 11 = Z_to_bv 64 (i * wpls) -> getr regs 12 = Z_to_bv 64 (i * w) ->
  getr regs 18 = Z_to_bv 64 wpls -> getr regs 10 = Z_to_bv 64 w -> getr regs 8 = Z_to_bv 64 datas -> getr regs 9 = Z_to_bv 64 datad ->
  getr regs 14 = Z_to_bv 64 1 -> getr regs 15 = Z_to_bv 64 1 -> getr regs 5 = Z_to_bv 64 (datad + comp) -> getr regs 16 = Z_to_bv 64 comp ->
  getr regs 20 = Z_to_bv 64 w -> getr regs 21 = Z_to_bv 64 h -> getr regs 6 = Z_to_bv 64 3 -> getr regs 17 = Z_to_bv 64 (4 * w) ->
  exists regs' M',
    msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1bc04) M al_rom) (@mkst fx regs' (Z_to_bv 64 0x1bcf8) M' al_rom)
    /\ winside datad (datad + 4 * (w * h)) M M'
    /\ regs_agree (fun x => In x [7; 11; 12; 13; 19; 22; 23; 24; 25; 28; 29; 30; 31]%list) regs regs'.
Proof.
  induction k as [|k IH]; intros regs M i h w comp datas wpls datad Hi Hk Hh Hw Hc Hs4 Hs1 Hwp Hw4 Hwph Hs2 Hd4 Hd1 Hwh Hd2 Hdisj Hrd SOK
    H13 H11 H12 H18 H10 H8 H9 H14 H15 H5 H16 H20 H21 H6 H17.
  { cbn [Z.of_nat] in Hk. lia. }
  assert (Hiws : (0 <= i * wpls /\ (i + 1) * wpls <= wpls * h)%Z) by nia.
  assert (Hiw : (0 <= i * w /\ (i + 1) * w <= w * h)%Z) by nia.
  destruct (rs_OH al_rom fx regs M i h w wpls w datas datad comp Hi Hh Hw Hwp ltac:(lia) Hwph Hwh Hs1 ltac:(lia) Hd1 ltac:(lia) Hc
              H13 H11 H12 H18 H10 H8 H9 H14 H15 H5 H16 H20 H6) as (R1 & MS1 & G7 & G23 & G31 & G28 & G30 & G19 & G22 & G29 & AG1).
  assert (Hdst : forall q, (0 <= q < w)%Z ->
            (datad <= xor3 (datad + 4 * (i * w) + comp + 4 * q) /\ xor3 (datad + 4 * (i * w) + comp + 4 * q) + 1 <= datad + 4 * (w * h))%Z).
  { intros q Hq. pose proof (xor3_in_raster datad w h (4 * w) i (comp + 4 * q) Hd4 ltac:(lia) ltac:(lia) Hi ltac:(lia) ltac:(lia)) as X.
    replace (datad + 4 * w * i + (comp + 4 * q))%Z with (datad + 4 * (i * w) + comp + 4 * q)%Z in X by lia. lia. }
  assert (Hsrcr : forall q, (0 <= q < w)%Z ->
            (datas <= xor3 (datas + 4 * (i * wpls) + q) /\ xor3 (datas + 4 * (i * wpls) + q) + 1 <= datas + 4 * (wpls * h))%Z).
  { intros q Hq. pose proof (xor3_in_raster datas wpls h w i q Hs4 Hwp Hw4 Hi Hq ltac:(lia)) as X.
    replace (datas + 4 * wpls * i + q)%Z with (datas + 4 * (i * wpls) + q)%Z in X by lia. lia. }
  assert (K14 : getr R1 14 = Z_to_bv 64 1) by (agk AG1 H14).
  assert (K15 : getr R1 15 = Z_to_bv 64 1) by (agk AG1 H15).
  assert (K6 : getr R1 6 = Z_to_bv 64 3) by (agk AG1 H6).
  assert (K17 : getr R1 17 = Z_to_bv 64 (4 * w)) by (agk AG1 H17).
  destruct (rs_col (Z.to_nat w) R1 M 0 w (datas + 4 * (i * wpls)) (datad + 4 * (i * w)) comp datad (datad + 4 * (w * h))
              ltac:(lia) ltac:(rewrite Z2Nat.id; lia) ltac:(lia) Hc ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
              (fun q Hq => Hdst q ltac:(lia))
              (fun q Hq => ltac:(pose proof (Hsrcr q ltac:(lia)); lia))
              (fun q Hq => Hrd (xor3 (datas + 4 * (i * wpls) + q)) ltac:(pose proof (Hsrcr q ltac:(lia)); lia))
              ltac:(replace (datad + 4 * (w * h) - datad)%Z with (4 * (w * h))%Z by lia; exact SOK)
              ltac:(rewrite G29; f_equal; lia) ltac:(rewrite G23; f_equal; lia) ltac:(rewrite G31; f_equal; lia)
              G7 G30 G28 G19 G22 K14 K15 K6 K17) as (R2 & M2 & MS2 & WI2 & AG2).
  assert (AG12 : regs_agree (fun x => In x [7; 19; 22; 23; 24; 25; 28; 29; 30; 31]%list) regs R2) by (agc AG1 AG2).
  assert (L13 : getr R2 13 = Z_to_bv 64 i) by (agk AG12 H13).
  assert (L21 : getr R2 21 = Z_to_bv 64 h) by (agk AG12 H21).
  assert (L18 : getr R2 18 = Z_to_bv 64 wpls) by (agk AG12 H18).
  assert (L10 : getr R2 10 = Z_to_bv 64 w) by (agk AG12 H10).
  assert (L11 : getr R2 11 = Z_to_bv 64 (i * wpls)) by (agk AG12 H11).
  assert (L12 : getr R2 12 = Z_to_bv 64 (i * w)) by (agk AG12 H12).
  destruct (Z.eq_dec (i + 1) h) as [Elast | Nlast].
  - destruct (rs_ON al_rom true fx R2 M2 i h wpls w Hi Hh Hwp ltac:(lia) Hwph Hwh Elast L13 L21 L18 L10 L11 L12)
      as (R3 & MS3 & _ & _ & _ & AG3).
    exists R3, M2. split; [eapply msteps_trans; [exact MS1 | eapply msteps_trans; [exact MS2 | exact MS3]]|].
    split; [exact WI2|]. agc AG12 AG3.
  - destruct (rs_ON al_rom false fx R2 M2 i h wpls w Hi Hh Hwp ltac:(lia) Hwph Hwh ltac:(cbv beta iota; lia) L13 L21 L18 L10 L11 L12)
      as (R3 & MS3 & F13 & F11 & F12 & AG3).
    assert (AG123 : regs_agree (fun x => In x [7; 11; 12; 13; 19; 22; 23; 24; 25; 28; 29; 30; 31]%list) regs R3) by (agc AG12 AG3).
    assert (Hrd' : forall a, (datas <= a < datas + 4 * (wpls * h))%Z -> exists v, (0 <= v <= 255)%Z /\ rdn SEGS M2 (Z_to_bv 64 a) 1 = Some (Z_to_le_bytes 1 v)).
    { intros a Ha. destruct (Hrd a Ha) as (va & Hva & Ra). exists va. split; [exact Hva|].
      eapply winside_rdn; [exact WI2 | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | exact Ra]. }
    assert (SOK2 : store_ok SEGS M2 (Z_to_bv 64 datad) (Z.to_nat (4 * (w * h))) = true).
    { eapply store_ok_mono; [eapply winside_grows; exact WI2 | exact SOK]. }
    destruct (IH R3 M2 (i + 1)%Z h w comp datas wpls datad ltac:(lia) ltac:(lia) Hh Hw Hc Hs4 Hs1 Hwp Hw4 Hwph Hs2 Hd4 Hd1 Hwh Hd2 Hdisj Hrd' SOK2
                 F13 F11 F12 ltac:(agk AG123 H18) ltac:(agk AG123 H10) ltac:(agk AG123 H8) ltac:(agk AG123 H9)
                 ltac:(agk AG123 H14) ltac:(agk AG123 H15) ltac:(agk AG123 H5) ltac:(agk AG123 H16) ltac:(agk AG123 H20)
                 ltac:(agk AG123 H21) ltac:(agk AG123 H6) ltac:(agk AG123 H17)) as (R4 & M4 & MS4 & WI4 & AG4).
    exists R4, M4. split.
    { eapply msteps_trans; [exact MS1|]. eapply msteps_trans; [exact MS2|]. eapply msteps_trans; [exact MS3 | exact MS4]. }
    split; [eapply winside_trans; [exact WI2 | exact WI4]|]. agc AG123 AG4.
Qed.

(* [comment removed for export] *)
Lemma pixSetRGBComponent_W : forall C Ar A m md regs (s pixd pixs w h datas datad comp : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md -> sub_live Ar A ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + RGBS_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret ->
  getr regs 10 = Z_to_bv 64 pixd -> getr regs 11 = Z_to_bv 64 pixs -> getr regs 12 = Z_to_bv 64 comp -> (0 <= comp <= 2)%Z ->
  PIXat m pixd (set_data (pix_hdr w h 32) datad) -> PIXat m pixs (hdv w h 8 0 datas) -> hdr_ok w h 32 -> (1 <= w)%Z -> (1 <= h)%Z ->
  live A (Z_to_bv 64 pixd) = Some 64%Z -> live A (Z_to_bv 64 datad) = Some (4 * (wpl_of w 32 * h))%Z ->
  live A (Z_to_bv 64 pixs) = Some 64%Z -> live A (Z_to_bv 64 datas) = Some (4 * (wpl_of w 8 * h))%Z ->
  live Ar (Z_to_bv 64 datad) = None -> live (c_A0 C) (Z_to_bv 64 datad) = None ->
  Z_to_bv 64 pixs <> Z_to_bv 64 datad -> Z_to_bv 64 pixd <> Z_to_bv 64 datad -> Z_to_bv 64 datas <> Z_to_bv 64 datad ->
  (forall m' regs', W C A m' md -> cs_kept regs regs' -> POSTM C Ar s m m' -> getr regs' 10 = Z_to_bv 64 0 ->
     PIXat m' pixd (set_data (pix_hdr w h 32) datad) -> PIXat m' pixs (hdv w h 8 0 datas) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst regs (Z_to_bv 64 PC_pixSetRGBComponent) m al_rom) md) S.
Proof.
  intros C Ar A m md regs s pixd pixs w h datas datad comp ret S CK HW SUB H2 Hs16 Hstk Hsc H1 Hret H10 H11 H12 Hc
    PXd PXs Hhdr Hw1 Hh1 Lpd Ldd Lps Lds LrD L0D NEsd NEpd NEdd POST.
  destruct Hhdr as (_ & Hw20 & Hh20 & Hsz).
  assert (Wd : wpl_of w 32 = w).
  { unfold wpl_of. rewrite Z.div_add_l by lia. change (31 / 32)%Z with 0%Z. lia. }
  rewrite Wd in Hsz, Ldd.
  assert (Hwps : (1 <= wpl_of w 8 /\ w <= 4 * wpl_of w 8 /\ wpl_of w 8 <= w)%Z).
  { unfold wpl_of. pose proof (Z.div_mod (w * 8 + 31) 32 ltac:(lia)). pose proof (Z.mod_pos_bound (w * 8 + 31) 32 ltac:(lia)). lia. }
  assert (Hwh : (w * h <= 2 ^ 24)%Z) by lia.
  assert (Hwph : (wpl_of w 8 * h <= 2 ^ 24)%Z) by nia.
  pose proof CK as [Ctop Csp0 Csp0hi Cal Cimg].
  pose proof LSTK_val as LS. unfold RGBS_STACK in Hstk.
  pose proof PXd as (Hpd0 & Hpd64 & WFd & _). pose proof PXs as (Hps0 & Hps64 & WFs & _).
  pose proof (wf_data _ WFd) as Hdd. cbn [p_data set_data pix_hdr] in Hdd.
  pose proof (wf_data _ WFs) as Hds. cbn [p_data hdv] in Hds.
  pose proof HW as [WI WP _ _ _ _ _ _ _ _ _].
  pose proof (blk_range C A m md (Z_to_bv 64 pixd) 64 CK HW Lpd ltac:(lia)) as BRpd. rewrite u_Z2bv in BRpd by lia.
  pose proof (blk_range C A m md (Z_to_bv 64 pixs) 64 CK HW Lps ltac:(lia)) as BRps. rewrite u_Z2bv in BRps by lia.
  pose proof (blk_range C A m md (Z_to_bv 64 datad) _ CK HW Ldd ltac:(nia)) as BRdd. rewrite u_Z2bv in BRdd by lia.
  pose proof (blk_range C A m md (Z_to_bv 64 datas) _ CK HW Lds ltac:(nia)) as BRds. rewrite u_Z2bv in BRds by lia.
  pose proof (ai_live_hull _ _ _ _ _ WI Lpd) as (_ & ALpd & _ & _). rewrite u_Z2bv in ALpd by lia.
  pose proof (ai_live_hull _ _ _ _ _ WI Lps) as (_ & ALps & _ & _). rewrite u_Z2bv in ALps by lia.
  pose proof (ai_live_hull _ _ _ _ _ WI Ldd) as (_ & ALdd & _ & _). rewrite u_Z2bv in ALdd by lia.
  pose proof (ai_live_hull _ _ _ _ _ WI Lds) as (_ & ALds & _ & DEFs). rewrite u_Z2bv in ALds by lia.
  pose proof (ai_live_disjoint _ _ _ _ _ _ _ WI Lds Ldd NEdd) as DJsd. rewrite !u_Z2bv in DJsd by lia.
  pose proof (ai_live_disjoint _ _ _ _ _ _ _ WI Lpd Ldd NEpd) as DJpd. rewrite !u_Z2bv in DJpd by lia.
  pose proof (ai_live_disjoint _ _ _ _ _ _ _ WI Lps Ldd NEsd) as DJpsd. rewrite !u_Z2bv in DJpsd by lia.
  pose proof (round16_ge (4 * (wpl_of w 8 * h)) ltac:(nia)) as RGs. pose proof (round16_ge (4 * (w * h)) ltac:(nia)) as RGd.
  pose proof (round16_ge 64 ltac:(lia)) as RG64.
  assert (Hdisj : (datas + 4 * (wpl_of w 8 * h) <= datad \/ datad + 4 * (w * h) <= datas)%Z) by lia.
  assert (Hpm8d : (pixd mod 8 = 0)%Z) by (apply al16_mod8; exact ALpd).
  assert (Hpm8s : (pixs mod 8 = 0)%Z) by (apply al16_mod8; exact ALps).
  assert (Hdm4d : (datad mod 4 = 0)%Z) by (apply mod16_mod4; exact ALdd).
  assert (Hdm4s : (datas mod 4 = 0)%Z) by (apply mod16_mod4; exact ALds).
  assert (SOKf : store_ok SEGS m (Z_to_bv 64 (s - 112)) 112 = true) by (apply (W_sok_win C A m md); [exact CK | exact HW | lia | cbn; lia]).
  assert (Dd : rdn SEGS m (Z_to_bv 64 (pixd + 8)) 4 = Some (Z_to_le_bytes 4 32))
    by (pose proof (PIX_rd_d SEGS _ _ _ PXd) as X; cbn [p_d set_data pix_hdr] in X; exact X).
  assert (Sd : rdn SEGS m (Z_to_bv 64 (pixs + 8)) 4 = Some (Z_to_le_bytes 4 8))
    by (pose proof (PIX_rd_d SEGS _ _ _ PXs) as X; cbn [p_d hdv] in X; exact X).
  destruct (rs_A al_rom fx regs m s pixd pixs comp ltac:(lia) Hs16 ltac:(lia) ltac:(lia) Hpm8d ltac:(lia) ltac:(lia) Hpm8s Hc SOKf Dd Sd
              ltac:(lia) ltac:(lia) H2 H10 H11 H12) as (R1 & MS1 & G2 & G18 & G19 & G22 & AG1).
  set (m1 := FRM11 m s regs) in *.
  assert (WP1 : W C A m1 md /\ POSTM C Ar s m m1).
  { unfold m1, FRM11. rs_wp CK SUB. split; [exact HW | apply POSTM_refl]. }
  assert (PXd1 : PIXat m1 pixd (set_data (pix_hdr w h 32) datad)).
  { eapply PIXat_frame; [exact PXd|]. intros x Hx. unfold m1, FRM11. rs_wout. reflexivity. }
  assert (PXs1 : PIXat m1 pixs (hdv w h 8 0 datas)).
  { eapply PIXat_frame; [exact PXs|]. intros x Hx. unfold m1, FRM11. rs_wout. reflexivity. }
  assert (SOK1 : store_ok SEGS m1 (Z_to_bv 64 (s - 112)) 112 = true)
    by (apply (W_sok_win C A m1 md); [exact CK | exact (proj1 WP1) | lia | cbn; lia]).
  destruct (rs_B al_rom fx R1 m1 s pixd pixs comp w h ltac:(lia) Hs16 ltac:(lia) ltac:(lia) Hpm8d ltac:(lia) ltac:(lia) Hpm8s Hc
              ltac:(lia) ltac:(lia) SOK1
              ltac:(pose proof (PIX_rd_w SEGS _ _ _ PXd1) as X; cbn [p_w set_data pix_hdr] in X; exact X)
              ltac:(pose proof (PIX_rd_h SEGS _ _ _ PXd1) as X; cbn [p_h set_data pix_hdr] in X; exact X)
              ltac:(pose proof (PIX_rd_w SEGS _ _ _ PXs1) as X; cbn [p_w hdv] in X; exact X)
              ltac:(pose proof (PIX_rd_h SEGS _ _ _ PXs1) as X; cbn [p_h hdv] in X; exact X)
              ltac:(lia) ltac:(lia) G2 G18 G19 G22) as (R2 & MS2 & F2 & F18 & F19 & F22 & F20 & F21 & AG2).
  set (m2 := DIM2c (DIM2c m1 (s - 92) (s - 96) w h) (s - 100) (s - 104) w h) in *.
  assert (WP2 : W C A m2 md /\ POSTM C Ar s m m2).
  { unfold m2, DIM2c. rs_wp CK SUB. first [exact WP1 | split; [exact HW | apply POSTM_refl]]. }
  assert (PXd2 : PIXat m2 pixd (set_data (pix_hdr w h 32) datad)).
  { eapply PIXat_frame; [exact PXd1|]. intros x Hx. unfold m2, DIM2c. rs_wout. reflexivity. }
  assert (PXs2 : PIXat m2 pixs (hdv w h 8 0 datas)).
  { eapply PIXat_frame; [exact PXs1|]. intros x Hx. unfold m2, DIM2c. rs_wout. reflexivity. }
  destruct (rs_C al_rom fx R2 m2 s pixd pixs comp w h (wpl_of w 8) w datas datad ltac:(lia) ltac:(lia) Hpm8d ltac:(lia) ltac:(lia) Hpm8s Hc
              ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
              ltac:(pose proof (PIX_rd_wpl SEGS _ _ _ PXd2) as X; cbn [p_wpl set_data pix_hdr] in X; rewrite Wd in X; exact X)
              ltac:(pose proof (PIX_rd_data SEGS _ _ _ PXd2) as X; cbn [p_data set_data pix_hdr] in X; exact X)
              ltac:(pose proof (PIX_rd_wpl SEGS _ _ _ PXs2) as X; cbn [p_wpl hdv] in X; exact X)
              ltac:(pose proof (PIX_rd_data SEGS _ _ _ PXs2) as X; cbn [p_data hdv] in X; exact X)
              F2 F18 F19 F22 F20 F21)
    as (R3 & MS3 & E2 & E8 & E9 & E18 & E10 & E20 & E21 & E16 & E17 & E14 & E15 & E5 & E6 & E11 & E12 & E13 & AG3).
  assert (RD : forall a, (datas <= a < datas + 4 * (wpl_of w 8 * h))%Z -> exists va, (0 <= va <= 255)%Z /\ rdn SEGS m2 (Z_to_bv 64 a) 1 = Some (Z_to_le_bytes 1 va)).
  { intros a Ha.
    specialize (DEFs (a - datas)%Z ltac:(lia)) as (_ & DEF & _). unfold at_ in DEF. rewrite u_Z2bv in DEF by lia.
    replace (datas + (a - datas))%Z with a in DEF by lia.
    assert (EQ : m2 (Z_to_bv 64 a) = m (Z_to_bv 64 a)) by (unfold m2, m1, DIM2c, FRM11; rs_wout; reflexivity).
    destruct (m (Z_to_bv 64 a)) as [b|] eqn:Eb; [|congruence].
    exists (bv_unsigned b). split; [apply byte_rng|]. apply byte_rdn1. exact EQ. }
  assert (SOKd : store_ok SEGS m2 (Z_to_bv 64 datad) (Z.to_nat (4 * (w * h))) = true).
  { apply (exW_sok_blk SEGS C A m2 md datad (4 * (w * h)) datad _ p16_segs CK (proj1 WP2) Ldd); rewrite ?Z2Nat.id by nia; lia. }
  destruct (rs_rows (Z.to_nat h) R3 m2 0 h w comp datas (wpl_of w 8) datad ltac:(lia) ltac:(rewrite Z2Nat.id; lia) Hh20 ltac:(lia) Hc
              Hdm4s ltac:(lia) ltac:(lia) ltac:(lia) Hwph ltac:(lia) Hdm4d ltac:(lia) Hwh ltac:(lia) Hdisj RD SOKd
              E13 ltac:(rewrite E11; f_equal; lia) ltac:(rewrite E12; f_equal; lia) E18 E10 E8 E9 E14 E15 E5 E16 E20 E21 E6 E17)
    as (R4 & M4 & MS4 & WI4 & AG4).
  assert (WP4 : W C A M4 md /\ POSTM C Ar s m M4).
  { apply (winside_WP C Ar A m m2 M4 md (Z_to_bv 64 datad) (4 * (w * h)) datad (datad + 4 * (w * h)) s CK WP2 Ldd LrD L0D SUB);
      [rewrite u_Z2bv by lia; lia | rewrite u_Z2bv by lia; lia | exact WI4]. }
  assert (L2 : getr R4 2 = Z_to_bv 64 (s - 112)) by (agk AG4 E2).
  assert (SL : forall (k : reg) (o : Z), In (k, o) [(1%bv, 8%Z); (8%bv, 16%Z); (9%bv, 24%Z); (18%bv, 32%Z); (19%bv, 40%Z); (20%bv, 48%Z);
                                                   (21%bv, 56%Z); (22%bv, 64%Z); (23%bv, 72%Z); (24%bv, 80%Z); (25%bv, 88%Z)] ->
               rdn SEGS M4 (Z_to_bv 64 (s - o)) 8 = Some (Z_to_le_bytes 8 (u (getr regs k)))).
  { intros k o Hin. cbn [In] in Hin.
    repeat (destruct Hin as [Hin|Hin];
            [injection Hin as <- <-; eapply winside_rdn; [exact WI4 | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia
                                                          | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia |];
             unfold m2, m1, DIM2c, FRM11; rs_rdout;
             rewrite rdn_wbytes_hit8 by (rewrite u_Z2bv by lia; lia); rewrite w2b_u; reflexivity|]).
    destruct Hin. }
  destruct (rs_E al_rom fx R4 M4 s (u (getr regs 1)) (u (getr regs 8)) (u (getr regs 9)) (u (getr regs 18)) (u (getr regs 19))
              (u (getr regs 20)) (u (getr regs 21)) (u (getr regs 22)) (u (getr regs 23)) (u (getr regs 24)) (u (getr regs 25))
              ltac:(lia) ltac:(rewrite Z_to_bv_bv_unsigned, H1; exact Hret)
              (u_rng _) (u_rng _) (u_rng _) (u_rng _) (u_rng _) (u_rng _) (u_rng _) (u_rng _) (u_rng _) (u_rng _) (u_rng _)
              (SL 1%bv 8%Z ltac:(cbn [In]; repeat first [left; reflexivity | right])) (SL 8%bv 16%Z ltac:(cbn [In]; repeat first [left; reflexivity | right]))
              (SL 9%bv 24%Z ltac:(cbn [In]; repeat first [left; reflexivity | right])) (SL 18%bv 32%Z ltac:(cbn [In]; repeat first [left; reflexivity | right]))
              (SL 19%bv 40%Z ltac:(cbn [In]; repeat first [left; reflexivity | right])) (SL 20%bv 48%Z ltac:(cbn [In]; repeat first [left; reflexivity | right]))
              (SL 21%bv 56%Z ltac:(cbn [In]; repeat first [left; reflexivity | right])) (SL 22%bv 64%Z ltac:(cbn [In]; repeat first [left; reflexivity | right]))
              (SL 23%bv 72%Z ltac:(cbn [In]; repeat first [left; reflexivity | right])) (SL 24%bv 80%Z ltac:(cbn [In]; repeat first [left; reflexivity | right]))
              (SL 25%bv 88%Z ltac:(cbn [In]; repeat first [left; reflexivity | right])) L2)
    as (R5 & MS5 & K2 & K1 & K8 & K9 & K18 & K19 & K20 & K21 & K22 & K23 & K24 & K25 & K10 & AG5).
  rewrite Z_to_bv_bv_unsigned, H1 in MS5.
  assert (AGall : regs_agree (fun x => In x [1; 2; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 28; 29; 30; 31]%list) regs R5).
  { assert (A12 : regs_agree (fun x => In x [1; 2; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 28; 29; 30; 31]%list) regs R2)
      by (agc AG1 AG2).
    assert (A123 : regs_agree (fun x => In x [1; 2; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 28; 29; 30; 31]%list) regs R3)
      by (agc A12 AG3).
    assert (A1234 : regs_agree (fun x => In x [1; 2; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 28; 29; 30; 31]%list) regs R4)
      by (agc A123 AG4).
    agc A1234 AG5. }
  pose proof WP as [MH ML _].
  eapply rz_msteps; [exact MH | exact ML | |].
  { eapply msteps_trans; [exact MS1|]. eapply msteps_trans; [exact MS2|]. eapply msteps_trans; [exact MS3|].
    eapply msteps_trans; [exact MS4 | exact MS5]. }
  apply (POST M4 R5).
  - exact (proj1 WP4).
  - apply cs_kept_intro.
    + rewrite K2, H2; reflexivity.
    + agk AGall (eq_refl (getr regs 3)).
    + agk AGall (eq_refl (getr regs 4)).
    + rewrite K8, Z_to_bv_bv_unsigned; reflexivity.
    + rewrite K9, Z_to_bv_bv_unsigned; reflexivity.
    + rewrite K18, Z_to_bv_bv_unsigned; reflexivity.
    + rewrite K19, Z_to_bv_bv_unsigned; reflexivity.
    + rewrite K20, Z_to_bv_bv_unsigned; reflexivity.
    + rewrite K21, Z_to_bv_bv_unsigned; reflexivity.
    + rewrite K22, Z_to_bv_bv_unsigned; reflexivity.
    + rewrite K23, Z_to_bv_bv_unsigned; reflexivity.
    + rewrite K24, Z_to_bv_bv_unsigned; reflexivity.
    + rewrite K25, Z_to_bv_bv_unsigned; reflexivity.
    + agk AGall (eq_refl (getr regs 26)).
    + agk AGall (eq_refl (getr regs 27)).
  - exact (proj2 WP4).
  - exact K10.
  - eapply PIXat_frame; [exact PXd2|]. intros x Hx. rewrite (winside_out _ _ _ _ x WI4) by lia. reflexivity.
  - eapply PIXat_frame; [exact PXs2|]. intros x Hx. rewrite (winside_out _ _ _ _ x WI4) by lia. reflexivity.
Qed.

End RgbsW.
