(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import Tac Arr Bytes ZBridge InitMem.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import DrvAgree.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import ExecF Shadow.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AsanW Require Import AImg ABase RtCells AProto AMalloc_iface AH_fi_iface.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac retlitA := lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?n)] =>
  replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end.

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
#[using="Type"] Lemma wr_at_appA : forall segs m a n1 n2, 0 <= n1 -> 0 <= n2 ->
  wr_at segs m a (n1 + n2) <-> wr_at segs m a n1 /\ wr_at segs m (a + n1) n2.
Proof.
  intros segs m a n1 n2 H1 H2. unfold wr_at. split.
  - intros (Ha & Hb & H). Local Ltac2 Set LiaHints.tbl := fun () => "00>0>15538427734.1316044545734.1117101216130.1320927221579.1126981515745.1126983613675.144844197302.17 51508892605.1754736999318.1454743291548.1157036176010.1761783614061.1163513398541.137651745753.14 00000700>00E00L00P00T00Z00`00a00b00c00g00h00mS2H22HiS2H22HbS2H12HiS2H12HaS2HaS2HaS2Hi1HS2Hi1HFFSS2HbSS3Hb'".
repeat split; try lia.
    + intros i Hi. apply H. lia.
    + intros i Hi. replace (a + n1 + i) with (a + (n1 + i)) by lia. apply H. lia.
  - intros ((Ha & Hb & HA) & (Ha' & Hb' & HB)). repeat split; try lia.
    intros i Hi. destruct (Z.lt_ge_cases i n1).
    + apply HA. lia.
    + replace (a + i) with (a + n1 + (i - n1)) by lia. apply HB. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma cells_bytes_lengthA : forall cs, cells_wf cs -> length (cells_bytes cs) = cells_size cs.
Proof.
  induction cs as [|c cs IH]; cbn; intros H; [reflexivity|]. destruct H as [Hc Hcs].
  rewrite length_app, (IH Hcs). destruct c; cbn in *; rewrite ?length_le8, ?length_le4, ?length_le2; try lia.
Qed.
#[using="Type"] Lemma rw_cells_appA : forall segs m A cs1 cs2,
  rw_cells segs m A (cs1 ++ cs2) <-> rw_cells segs m A cs1 /\ rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros segs m A cs1 cs2. unfold rw_cells, cells_at.
  rewrite cells_wf_app, cells_bytes_app, cells_size_app, Nat2Z.inj_add.
  rewrite wr_at_appA by lia. rewrite bytes_at_app.
  split.
  - intros (((W1 & W2) & (B1 & B2)) & (R1 & R2)).
    rewrite (cells_bytes_lengthA cs1 W1) in B2. tauto.
  - intros (((W1 & B1) & R1) & ((W2 & B2) & R2)).
    rewrite <- (cells_bytes_lengthA cs1 W1) in B2. tauto.
Qed.


#[using="Type"] Lemma aca_monoA : forall CI LB LB' SP SP' a, aclient_addr CI LB SP a -> (forall b, In b LB -> In b LB') -> SP' <= SP -> aclient_addr CI LB' SP' a.
Proof.
  intros CI LB LB' SP SP' a Ha HL HS. unfold aclient_addr, in_block, in_fake in *.
  destruct Ha as [X|[X|[(b & Hb & Hr)|(a' & Ha' & ->)]]].
  - Local Ltac2 Set LiaHints.tbl := fun () => "0020>14192470228.1035713220113.11000006009S1X2HSS1X".
left; lia.
  - right; left; exact X.
  - right; right; left. exists b. split; [apply HL; exact Hb| exact Hr].
  - right; right; right. exists a'. split; [|reflexivity].
    destruct Ha' as [X|[X|(c & A & n & Hin & X)]]; [left; lia| right; left; exact X| right; right].
    exists c, A, n. split; [apply HL; exact Hin| exact X].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma cl_stack : forall CI LB SP a, SP <= a < 2^47 -> aclient_addr CI LB SP a.
Proof. intros CI LB SP a H. left. exact H. Qed.
#[using="Type"] Lemma cl_block : forall CI LB SP b a, In b LB -> ab_addr b <= a < ab_addr b + ab_size b -> aclient_addr CI LB SP a.
Proof. intros CI LB SP b a Hb Ha. right; right; left. exists b. split; [exact Hb| exact Ha]. Qed.
#[using="Type"] Lemma cl_shadow : forall CI LB SP a', ((ATOP <= a' < 2^47) \/ in_ranges CI a' \/ in_fake LB a') -> aclient_addr CI LB SP (shad a').
Proof. intros CI LB SP a' H. right; right; right. exists a'. split; [exact H| reflexivity]. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma app_not_client : forall CI LB SP R k a,
  (forall iv, In iv CI -> snd iv <= AIMG_HI) -> (forall iv, In iv CI -> 0 <= fst iv) ->
  ablk R (R + k) -> ATOP <= SP ->
  (forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b)) ->
  (forall b, In b LB -> R + k <= ab_addr b \/ ab_addr b + ab_size b <= R) ->
  R <= a < R + k -> ~ aclient_addr CI LB SP a.
Proof.
  intros CI LB SP R k a HCI HCI0 AR HSP HLB HD Ha. pose proof (ablk_lin _ _ AR) as (R1 & R2 & R3 & R4). pose proof atop_range as ATR.
  unfold aclient_addr, in_ranges, in_block, in_fake. intros [X|[(iv & Hiv & H1 & H2)|[(b & Hb & H1)|(a' & Ha' & E)]]].
  - Local Ltac2 Set LiaHints.tbl := fun () => "0060>40461521065.2240463667756.2740463674142.2759314873579.2359314873579.2459315137787.2000000700B00N00\00h015S3ATR1YS3ATR2Y12HBS2Y12Y21H2H0S2Ha2H11H2AR1ES2Ha2R12H21HS3HSP2Ha2R31X".
lia.
  - pose proof (HCI iv Hiv). unfold AIMG_HI in *. lia.
  - destruct (HD b Hb); lia.
  - unfold ablk, AIMG_HI, KLS in AR. rewrite shad_div in E. unfold ASHOFF in E.
    assert (0 <= a' < 2^47).
    { destruct Ha' as [Y|[(iv & Hiv & Y1 & Y2)|(c0 & A0 & n0 & Hin0 & Y1)]].
      - lia.
      - pose proof (HCI iv Hiv). pose proof (HCI0 iv Hiv). unfold AIMG_HI in *. lia.
      - pose proof (HLB _ Hin0) as HB. cbn in HB. apply ablk_lin in HB. lia. }
    OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma shadow_not_client : forall CI LB SP F a,
  (forall iv, In iv CI -> snd iv <= AIMG_HI) -> (forall iv, In iv CI -> 0 <= fst iv) ->
  ablk F (F + 64) -> F mod 64 = 0 -> ATOP <= SP ->
  (forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b)) ->
  (forall b, In b LB -> F + 64 <= ab_addr b \/ ab_addr b + ab_size b <= F) ->
  shad F <= a < shad F + 8 -> ~ aclient_addr CI LB SP a.
Proof.
  intros CI LB SP F a HCI HCI0 AF F64 HSP HLB HD Ha. pose proof (ablk_lin _ _ AF) as (F1 & F2 & F3 & F4). pose proof atop_range as ATR.
  rewrite shad_div in Ha. unfold ASHOFF in Ha.
  unfold aclient_addr, in_ranges, in_block, in_fake. intros [X|[(iv & Hiv & H1 & H2)|[(b & Hb & H1)|(a' & Ha' & E)]]].
  - unfold AIMG_HI in *. Local Ltac2 Set LiaHints.tbl := fun () => "0070>59308579027.2859308581345.2359308679520.2359314873579.2459314938599.2859315137787.208137034921.22 00000<00T00]00m01601G01QS2F12Y22FA1HS2AF3F642Ha2F33ATR2H12HBS2F31Y2FAS3F642Ha2F12H21HS2Y12FA1DS3HSP2Ha2F33ATR1XS3F642Ha1E".
OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
  - pose proof (HCI iv Hiv). unfold AIMG_HI in *. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
  - pose proof (HLB b Hb) as HB. unfold ablk, AIMG_HI, KLS in HB, AF. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
  - rewrite shad_div in E. unfold ASHOFF in E.
    assert (FA : F <= a' < F + 64) by (OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
    destruct Ha' as [Y|[(iv & Hiv & Y1 & Y2)|(c0 & A0 & n0 & Hin0 & Y1)]].
    + lia.
    + pose proof (HCI iv Hiv). pose proof (HCI0 iv Hiv). unfold AIMG_HI in *. lia.
    + destruct (HD _ Hin0) as [D|D]; cbn in D; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma shadow_not_clientN : forall CI LB SP F N a,
  (forall iv, In iv CI -> snd iv <= AIMG_HI) -> (forall iv, In iv CI -> 0 <= fst iv) ->
  ablk F (F + N) -> F mod 8 = 0 -> N mod 8 = 0 -> 0 <= N -> ATOP <= SP ->
  (forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b)) ->
  (forall b, In b LB -> F + N <= ab_addr b \/ ab_addr b + ab_size b <= F) ->
  shad F <= a < shad F + N / 8 -> ~ aclient_addr CI LB SP a.
Proof.
  intros CI LB SP F N a HCI HCI0 AF F8 N8 N0 HSP HLB HD Ha. pose proof (ablk_lin _ _ AF) as (F1 & F2 & F3 & F4). pose proof atop_range as ATR.
  rewrite shad_div in Ha. unfold ASHOFF in Ha.
  unfold aclient_addr, in_ranges, in_block, in_fake. intros [X|[(iv & Hiv & H1 & H2)|[(b & Hb & H1)|(a' & Ha' & E)]]].
  - unfold AIMG_HI in *. Local Ltac2 Set LiaHints.tbl := fun () => "0070>59308579027.3159308581345.2659308679520.2659314873579.2759314938599.3159315137787.2359564487763.2500000<00V00_00n01701N01ZS2F12Y22FA1HS2AF2F82N82Ha2F33ATR2H12HBS2F31Y2FAS2F82Ha2F12H21HS2Y12FA1DS2F82N83HSP2Ha2F33ATR1XS2F82N82Ha1E".
OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
  - pose proof (HCI iv Hiv). unfold AIMG_HI in *. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
  - pose proof (HLB b Hb) as HB. unfold ablk, AIMG_HI, KLS in HB, AF. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
  - rewrite shad_div in E. unfold ASHOFF in E.
    assert (FA : F <= a' < F + N) by (OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
    destruct Ha' as [Y|[(iv & Hiv & Y1 & Y2)|(c0 & A0 & n0 & Hin0 & Y1)]].
    + lia.
    + pose proof (HCI iv Hiv). pose proof (HCI0 iv Hiv). unfold AIMG_HI in *. lia.
    + destruct (HD _ Hin0) as [D|D]; cbn in D; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma stack_not_client : forall CI LB SP X a,
  (forall iv, In iv CI -> snd iv <= AIMG_HI) -> (forall iv, In iv CI -> 0 <= fst iv) ->
  (forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b)) ->
  ATOP <= X -> X <= a < SP -> ~ aclient_addr CI LB SP a.
Proof.
  intros CI LB SP X a HCI HCI0 HLB HX Ha. pose proof atop_range as ATR.
  unfold aclient_addr, in_ranges, in_block, in_fake. intros [Y|[(iv & Hiv & H1 & H2)|[(b & Hb & H1)|(a' & Ha' & E)]]].
  - Local Ltac2 Set LiaHints.tbl := fun () => "0070>40461521065.1540463667756.2040463674142.2059308581345.1659314873579.1659314873579.1759315154296.1300000700B00N00[00j01:01@S3ATR1YS3ATR2Y12HBS2Y12Y21H2H0S2HX2Ha2H12HBS2HX2Ha3ATR1E1HS2HX2Ha3ATR2H21HS2Ha1Y".
lia.
  - pose proof (HCI iv Hiv). unfold AIMG_HI in *. lia.
  - pose proof (HLB b Hb) as HB. apply ablk_lin in HB. lia.
  - rewrite shad_div in E. unfold ASHOFF in E.
    assert (0 <= a' < 2^47).
    { destruct Ha' as [Y|[(iv & Hiv & Y1 & Y2)|(c0 & A0 & n0 & Hin0 & Y1)]].
      - lia.
      - pose proof (HCI iv Hiv). pose proof (HCI0 iv Hiv). unfold AIMG_HI in *. lia.
      - pose proof (HLB _ Hin0) as HB. cbn in HB. apply ablk_lin in HB. lia. }
    OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma magree_munch_step : forall (P : Z -> Prop) m mx my W,
  magree asegs P m mx -> munch W mx my -> wmono asegs mx my -> (forall a, P a -> outside W a) -> magree asegs P m my.
Proof.
  intros P m mx my W MG MU WM HP. eapply magree_trans; [exact MG|].
  eapply magree_mono; [eapply magree_of_munch; [exact MU| exact WM]|]. exact HP.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma fcellA_mono : forall m LB LB' C k, fcellA m LB C k -> (forall b, In b LB -> In b LB') -> fcellA m LB' C k.
Proof.
  intros m LB LB' C k ((cls & FA & FN & Hin & H1 & H2 & H3 & H4) & U) HL. split; [|exact U].
  exists cls, FA, FN. split; [apply HL; exact Hin|]. auto.
Qed.
#[using="Type"] Lemma shullA_mono : forall RNG m LB LB' A n, shullA RNG m LB A n -> (forall b, In b LB -> In b LB') -> shullA RNG m LB' A n.
Proof.
  intros RNG m LB LB' A n (cls & FA & FN & Hin & R) HL. exists cls, FA, FN. split; [apply HL; exact Hin| exact R].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma unpoisoned_mg_fake : forall (P : Z -> Prop) m m' LB cls FA FN B n,
  magree asegs P m m' -> (forall a', in_fake LB a' -> P (shad a')) ->
  In (mkABlock (ABFake cls) FA FN) LB -> FA <= B -> B + n <= FA + FN -> FA mod 8 = 0 -> FA + FN <= 2^47 ->
  unpoisoned m B (B + n) -> unpoisoned m' B (B + n).
Proof.
  intros P m m' LB cls FA FN B n MG HPsh Hb H1 H2 H3 H4 U.
  pose proof U as (U0 & U1 & _).
  eapply unpoisoned_agree; [exact U|]. intros s Hs. Local Ltac2 Set LiaHints.tbl := fun () => "0020>18614817987.2230283160161.2200000=00JS2H22H42U02HsS2H12H22H32Hs".
apply MG; [rewrite !shad_div in Hs; unfold ASHOFF in Hs; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia|].
  replace s with (shad (8 * (s - ASHOFF))) by (apply shad_unshad). apply HPsh.
  exists cls, FA, FN. split; [exact Hb|]. rewrite !shad_div in Hs. unfold ASHOFF in Hs |- *. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma fcellA_mg : forall (P : Z -> Prop) m m' LB C k,
  magree asegs P m m' -> (forall a', in_fake LB a' -> P (shad a')) -> fcellA m LB C k -> fcellA m' LB C k.
Proof.
  intros P m m' LB C k MG HPsh [(cls & FA & FN & Hb & A1 & A2 & A3 & A4) U]. split; [exists cls, FA, FN; auto|].
  pose proof (ablk_lin _ _ A3) as (_ & _ & _ & A5).
  Local Ltac2 Set LiaHints.tbl := fun () => "0010>67874783780.19000004S2A5".
eapply unpoisoned_mg_fake; [exact MG| exact HPsh| exact Hb| exact A1| exact A2| exact A4| lia| exact U].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma shullA_mg : forall (P : Z -> Prop) RNG m m' LB A n,
  magree asegs P m m' -> (forall a', in_fake LB a' -> P (shad a')) -> shullA RNG m LB A n -> shullA RNG m' LB A n.
Proof.
  intros P RNG m m' LB A n MG HPsh (cls & FA & FN & Hb & A1 & A2 & A3 & A4 & A5 & A6 & W & R).
  exists cls, FA, FN. split; [exact Hb|]. do 6 (split; [assumption|]). split; [| exact R].
  eapply wr_at_magree; [exact MG| exact W|]. intros s Hs.
  replace s with (shad (8 * (s - ASHOFF))) by (apply shad_unshad). apply HPsh.
  exists cls, FA, FN. split; [exact Hb|]. rewrite !shad_div in Hs. unfold ASHOFF in Hs |- *. Local Ltac2 Set LiaHints.tbl := fun () => "0010>30283160161.24000007S2A32Hs".
OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma relro_wordA : forall m A v,
  (forall i, ARELRO_LO <= i < ARELRO_HI -> m (wa i) = None) ->
  ARELRO_LO <= A -> A + 8 <= ARELRO_HI -> rw_bytes_b asegs A (le8 (Z_to_bv 64 v)) = true ->
  rw_cells asegs m A [C8 (Z_to_bv 64 v)].
Proof.
  intros m A v R LO HI RB. unfold ARELRO_LO, ARELRO_HI in *.
  eapply rw_cells_recast; [apply (rw_cells_image0 asegs m A (le8 (Z_to_bv 64 v)));
    [ intros a Ha; rewrite <- (Z_to_bv_bv_unsigned a); apply R; rewrite length_le8 in Ha; lia
    | exact RB | lia | rewrite length_le8; lia ] | cbn; split; exact I | reflexivity | reflexivity].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma byte_of_c1A : forall m s b, rw_cells asegs m s [C1 b] -> 0x5f6000 <= s -> m (wa s) = Some b.
Proof.
  intros m s b [[_ (A & B & H)] _] Hs. cbn [cells_bytes cbytes app length] in B, H.
  Local Ltac2 Set LiaHints.tbl := fun () => "0040=11865735282.832192120219.838621375894.855686267042.800000500800;00>S1A1BS1BS1BS1B".
specialize (H 0%nat ltac:(lia)). cbn in H. rewrite Z.add_0_r in H.
  rewrite <- (mrd_no_image asegs m s (s + 1) s (no_image_asan s (s + 1) Hs)) by lia.
  rewrite H. cbn. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma mem_eq_singleA : forall mp m' A b, 0 <= A -> A + 1 <= 2^64 ->
  munch [(A, A + 1)] mp m' -> m' (wa A) = Some b -> forall x, m' x = write_to_mem mp (wa A) [b] x.
Proof.
  intros mp m' A b HA HB MU Hb x.
  Local Ltac2 Set LiaHints.tbl := fun () => "0070>22706589814.1224937311217.102529337836.12 28807582089.1237714619143.123805626308.10 59309037779.1400000600:00=00F00I00M00XS1R2NES2HAS1RS2HA2HB1RS1RS2HBS1R2NE1l2l0".
rewrite write_to_mem_spec by (cbn; lia). cbn [length]. change (Z.of_nat 1) with 1.
  pose proof (bv_unsigned_in_range 64 x) as R. unfold bv_modulus in R.
  destruct (Z.eq_dec (bv_unsigned x) A) as [E|NE].
  - replace x with (wa A) by (rewrite <- E; unfold wa; apply Z_to_bv_bv_unsigned). rewrite Hb, wa_unsigned by lia.
    replace (A <=? A) with true by (symmetry; apply Z.leb_le; lia). replace (A <? A + 1) with true by (symmetry; apply Z.ltb_lt; lia).
    cbn. rewrite Z.sub_diag. reflexivity.
  - rewrite MU by (cbn; lia).
    destruct (Z.leb_spec0 A (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (A + 1)); cbn [andb]; try reflexivity. exfalso; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma aheap_eqA : forall AI L RNG st LB m m', AHEAP AI L RNG st LB m -> (forall x, m' x = m x) -> AHEAP AI L RNG st LB m'.
Proof.
  intros AI L RNG st LB m m' AH E. eapply (AI_frame AI) with (W := []); [exact AH| | | constructor].
  - intros x _. apply E.
  - intros x Hx. unfold wview in *. rewrite E. exact Hx.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma res_sep : forall FF FLG A k FA FN,
  FA <= A -> A + k <= FA + FN -> ablk FA (FA + FN) -> 0 <= k ->
  (FF + 64 <= FA \/ FA + FN <= FF) -> (FLG + 1 <= FA \/ FA + FN <= FLG) ->
  2147450880 <= Z.shiftr FF 3 + 2147450880 -> Z.shiftr FF 3 + 2147450880 + 8 <= 17594333495296 ->
  disjoint_from [(Z.shiftr FF 3 + 2147450880, Z.shiftr FF 3 + 2147450880 + 8); (FF, FF + 8)] A k
  /\ disjoint_from [(FLG, FLG + 1)] A k.
Proof.
  intros FF FLG A k FA FN H1 H2 H3 H4 H5 H6 H7 H8. pose proof (ablk_disj_band _ _ H3) as HB. pose proof (ablk_lin _ _ H3) as HL.
  unfold KLS, AIMG_HI in *. cbn [disjoint_from]. Local Ltac2 Set LiaHints.tbl := fun () => "0010>44491373094.1800000FS2H12H22H52H62H72H82HB".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma ablock_shadow_blockR : forall m A n,
  ablock_shadow m A n -> A mod 8 = 0 -> 0 <= A -> 0 <= n -> A + n <= 2^64 -> shadow_block m A n.
Proof.
  intros m A n H HA A0 N0 AN. split; [exact HA|]. split; [exact A0|]. split; [exact N0|]. split; [exact AN|].
  split. { rewrite shad_div. unfold ASHOFF. Local Ltac2 Set LiaHints.tbl := fun () => "0050>33070983080.1136467336691.9 43142081584.1165463334282.9 9685746446.11 00000400;00<00C00GS2HsS2HA2A0SS2HA2ANS2Hs".
OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
  split. { rewrite shad_div, nshad_div. unfold ASHOFF. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
  intros s Hs. unfold ablock_shadow in H.
  specialize (H (s - shad A) ltac:(lia) ltac:(rewrite nshad_div in Hs; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia)).
  replace (shad A + (s - shad A)) with s in H by lia. rewrite H. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma ablock_unpoisonedR : forall m A n,
  ablock_shadow m A n -> A mod 8 = 0 -> 0 <= A -> 0 <= n -> A + n <= 2^64 -> unpoisoned m A (A + n).
Proof. intros. apply shadow_block_unpoisoned. apply ablock_shadow_blockR; assumption. Qed.

#[using="Type"] Lemma fcellA_block : forall m LB C k, fcellA m LB C k -> exists b, In b LB /\ ab_addr b <= C /\ C + k <= ab_addr b + ab_size b.
Proof. intros m LB C k [(cls & FA & FN & Hb & H1 & H2 & _) _]. exists (mkABlock (ABFake cls) FA FN). Local Ltac2 Set LiaHints.tbl := fun () => "0010=4931765030.11000007S2H12H2".
split; [exact Hb| cbn; lia]. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma u8arr_mg : forall (P : Z -> Prop) m m' A bs,
  magree asegs P m m' -> u8arr asegs m A bs -> (forall a, A <= a < A + Z.of_nat (length bs) -> P a) -> u8arr asegs m' A bs.
Proof.
  intros P m m' A bs MG [HB HW] HP. split; [eapply bytes_at_magree; eassumption| eapply wr_at_magree; eassumption].
Qed.

#[using="Type"] Lemma cl_range_block : forall CI LB SP b A k, In b LB -> ab_addr b <= A -> A + k <= ab_addr b + ab_size b ->
  forall a, A <= a < A + k -> aclient_addr CI LB SP a.
Proof. intros CI LB SP b A k Hb H1 H2 a Ha. apply (cl_block CI LB SP b a Hb). Local Ltac2 Set LiaHints.tbl := fun () => "0010>68189514523.1200000:S2H12H22Ha".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma blk_sepF : forall FF X k FA FN, FA <= X -> X + k <= FA + FN -> (FF + 64 <= FA \/ FA + FN <= FF) -> X + k <= FF \/ FF + 64 <= X.
Proof. Local Ltac2 Set LiaHints.tbl := fun () => "0010=37861381167.9000009S1H2H02H1".
intros; lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
Definition hull_loR (A : Z) : Z := A - A mod 64 - 64.
Definition hull_hiR (A n : Z) : Z := A + n + (- (A + n)) mod 64 + 64.

#[using="Type"] Lemma block_hullR : forall (RNG : footprint) m A n RLO RHI,
  0 <= n -> RLO mod 4096 = 0 -> RHI mod 4096 = 0 -> RLO + 64 <= A -> A + n + 64 <= RHI -> 64 <= A ->
  rng RNG (shad RLO) (shlen (RHI - RLO)) -> wr_at asegs m (shad RLO) (shlen (RHI - RLO)) ->
  rng RNG (shad (hull_loR A)) (shad (hull_hiR A n) - shad (hull_loR A))
  /\ wr_at asegs m (shad (hull_loR A)) (shad (hull_hiR A n) - shad (hull_loR A))
  /\ hull_loR A <= A /\ A + n <= hull_hiR A n /\ hull_loR A mod 64 = 0 /\ hull_hiR A n mod 64 = 0 /\ 0 <= hull_loR A
  /\ hull_hiR A n < A + n + 128.
Proof.
  intros RNG m A n RLO RHI Hn R1 R2 R3 R4 A64 RR WR.
  Local Ltac2 Set LiaHints.tbl := fun () => "00?0>12597282473.2714382445736.1316234743211.2716441136076.2917816388116.2918669783377.2721880378334.2721938745753.3129094230704.2729784547673.2738597515559.1542319785159.3143214357607.275410230825.16 60724487348.2700000400P00Z00a00k00o01301@01`01a01b01c01g024028S2P2S2Hn2R12R22P12P22P32P42Q12Q2S2S12S22S5S2W02S1S2W12S22S5S2P3S2P6S2S12S22S52HiS2Hn2R12R22R32R43A642P22P32P42P5SSSS2P1S2R12R22R32R4S2P4".
assert (P : hull_loR A <= A /\ A + n <= hull_hiR A n /\ hull_loR A mod 64 = 0 /\ hull_hiR A n mod 64 = 0
              /\ A - 128 < hull_loR A /\ hull_hiR A n < A + n + 128) by (unfold hull_loR, hull_hiR; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
  assert (Q : RLO <= hull_loR A /\ hull_hiR A n <= RHI) by (unfold hull_loR, hull_hiR; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
  destruct P as (P1 & P2 & P3 & P4 & P5 & P6). destruct Q as [Q1 Q2].
  assert (S : shad RLO <= shad (hull_loR A) /\ shad (hull_hiR A n) <= shad RHI /\ shad (hull_loR A) <= shad (hull_hiR A n)
              /\ shad RHI - shad RLO = (RHI - RLO) / 8).
  { rewrite !shad_div. clear - P1 P2 P3 P4 Q1 Q2 R1 R2 Hn. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
  destruct S as (S1 & S2 & S3 & S5).
  unfold shlen in RR, WR. rewrite Z.shiftr_div_pow2 in RR, WR by lia. change (2^3) with 8 in RR, WR.
  split; [| split; [| repeat split; lia]].
  - eapply rng_sub'; [exact RR| lia].
  - destruct WR as (W0 & W1 & W). split; [lia|]. split; [lia|]. intros i Hi.
    replace (shad (hull_loR A) + i) with (shad RLO + (shad (hull_loR A) - shad RLO + i)) by lia. apply W. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma c1z_unpoisonedR : forall m A k, rw_cells asegs m (Z.shiftr A 3 + 2147450880) [C1 (Z_to_bv 8 0)] -> A mod 8 = 0 ->
  0 <= A -> 0 <= k <= 8 -> A + 8 <= 2^47 -> unpoisoned m A (A + k).
Proof.
  intros m A k H A8 A0 K8 AH. Local Ltac2 Set LiaHints.tbl := fun () => "0060>15978983042.1224931955585.9 29784466269.1238005288389.1345622865929.1251442634548.9 00000700;00<00I00J00QS2A02H1S2A0SS2A82K82H12H2SS2K82AH".
split; [lia|]. split; [lia|]. intros G H0 H1 H2.
  assert (EG : G = A / 8) by (OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia). subst G.
  exists (Z_to_bv 8 0). split.
  - unfold ASHOFF. rewrite Z.shiftr_div_pow2 in H by lia. change (2^3) with 8 in H.
    replace (2147450880 + A / 8) with (A / 8 + 2147450880) by lia.
    apply (byte_of_c1A m _ _ H). OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
  - left. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma unpoisoned_join8 : forall m a b c, unpoisoned m a b -> unpoisoned m b c -> b mod 8 = 0 -> unpoisoned m a c.
Proof.
  intros m a b c (A1 & A2 & HA) (B1 & B2 & HB) Hb. Local Ltac2 Set LiaHints.tbl := fun () => "00;0>16744799925.1824569176901.1726829919813.1826983617675.1230990351072.1231246542388.1834109620604.2148371519445.1751284626989.205829942113.17 62464293315.1700000300700;00?00C00J00N00T00U00X00^S1LS2G2S2G1S2A1S2B2S2G12HGS2HGS2Hb1LSS1RS2G21R".
split; [lia|]. split; [lia|].
  intros G G0 G1 G2. destruct (Z.lt_ge_cases (8 * G) b) as [L|R].
  - assert (HG : 8 * G + 8 <= b) by (OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
    destruct (HA G ltac:(lia) ltac:(lia) ltac:(lia)) as (x & Hx & Hok). exists x. split; [exact Hx|].
    eapply gran_ok_mono; [exact Hok|]. lia.
  - destruct (HB G ltac:(lia) ltac:(lia) ltac:(lia)) as (x & Hx & Hok). exists x. split; [exact Hx|].
    eapply gran_ok_mono; [exact Hok|]. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma c1z_cells_unpoisoned : forall (k : nat) m A,
  rw_cells asegs m (Z.shiftr A 3 + 2147450880) (repeat (C1 (Z_to_bv 8 0)) k) -> A mod 8 = 0 -> 0 <= A ->
  A + 8 * Z.of_nat k <= 2^47 -> unpoisoned m A (A + 8 * Z.of_nat k).
Proof.
  induction k as [|k IH]; intros m A H A8 A0 AH.
  - cbn [Z.of_nat]. rewrite Z.mul_0_r, Z.add_0_r. apply unpoisoned_nil. Local Ltac2 Set LiaHints.tbl := fun () => "00;0>14603897098.1021462828627.1024931955585.1028611015001.1028813940230.7 29784317670.1045124616308.1052033238141.1053677454037.1064430108241.106865357147.10 00000700;00B00F00M00Q00X00_00f00j00nS2A02AHS2AHS2A02AHS2AHS2A02AHS2AHS2A82AHS2A82AHS2A82AHS2AHS2AH".
lia.
  - cbn [repeat] in H. change (C1 (Z_to_bv 8 0) :: repeat (C1 (Z_to_bv 8 0)) k) with ([C1 (Z_to_bv 8 0)] ++ repeat (C1 (Z_to_bv 8 0)) k) in H.
    apply (proj1 (rw_cells_appA _ _ _ _ _)) in H. destruct H as [H1 H2]. cbn [cells_size csize Nat.add] in H2.
    apply (unpoisoned_join8 m A (A + 8)).
    + apply (c1z_unpoisonedR m A 8 H1); lia.
    + replace (A + 8 * Z.of_nat (S k)) with ((A + 8) + 8 * Z.of_nat k) by lia. apply IH; [| OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia| lia| lia].
      replace (Z.shiftr (A + 8) 3 + 2147450880) with (Z.shiftr A 3 + 2147450880 + Z.of_nat 1); [exact H2|].
      rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
    + OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma app_vs_shadow : forall A k S n, ablk A (A + k) -> 2147450880 <= S -> S + n <= 17594333495296 -> A + k <= S \/ S + n <= A.
Proof. intros A k S n H H1 H2. pose proof (ablk_disj_band _ _ H) as B. unfold KLS in B. Local Ltac2 Set LiaHints.tbl := fun () => "0010=12268015016.9000009S2H12H21B".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
(* [comment removed for export] *)
#[using="Type"] Lemma hcoverA_unpoisoned : forall AI L RNG st LB m S n, AHEAP AI L RNG st LB m -> hcoverA LB S n -> 0 < n -> unpoisoned m S (S + n).
Proof.
  Local Ltac2 Set LiaHints.tbl := fun () => "0070>19844697028.2919957320638.2924938099585.28264007928.28  4510342635.28 45122846104.2759308586893.1200000400800=00A00F00J00QS2H2S2H1S3R1bS2HNS3R1dS2R4S2Z02Hn".
intros AI L RNG st LB m S n AH [Z0|(p & A & N & Hb & H1 & H2)] Hn; [exfalso; lia|].
  destruct (AI_block AI _ _ _ _ _ _ _ _ AH Hb) as (HN & (R1 & R2 & R3 & R4) & _ & _ & SHB & _).
  pose proof (ablk_lin _ _ R1) as (R1a & R1b & R1c & R1d).
  pose proof (ablock_unpoisonedR m A N SHB ltac:(OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia) ltac:(lia) ltac:(lia) ltac:(lia)) as U.
  eapply unpoisoned_sub; [exact U| lia| lia].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma hcoverA_block : forall LB S n, hcoverA LB S n -> 0 < n -> exists b, In b LB /\ ab_addr b <= S /\ S + n <= ab_addr b + ab_size b.
Proof.
  Local Ltac2 Set LiaHints.tbl := fun () => "0020>24054494491.1159308586893.6 00000700>S2H12H2S2Z02Hn".
intros LB S n [Z0|(p & A & N & Hb & H1 & H2)] Hn; [exfalso; lia|].
  exists (HB p A N). split; [exact Hb| cbn; lia].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC1.
