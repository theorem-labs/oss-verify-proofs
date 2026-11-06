(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode InitMem.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import ExecF ITreeA StepF.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AsanW Require Import AImg ABase ADepot_iface ARep ARepQ ARepFrame ARepKit AFreeRep AQConst.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Notation Wf sp t UB gq nodes store lst eb gl :=
  ([(sp - 4096, sp); (0x9db88, 0x9dbb0); (0xa2080, 0x1230b0); (0x130908, 0x13090c); (ADEPOT_LO, ADEPOT_HI);
    (t + 80, t + 112); (t + 2128, t + 2132); (t + 2784, t + 2792); (t + 2800, t + 3169);
    (UB - 16, UB + 8); (shad UB, shad UB + gq);
    (nodes, nodes + 1048576); (store, store + 8388608);
    (lst, lst + qsz lst); (eb, eb + 8192); (gl, gl + 8)]%Z) (only parsing).      (* [comment removed for export] *)

(* [comment removed for export] *)
Local Lemma sclr_int : forall a n, sclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof. intros a n H G1 G2. unfold sclr, KLS in H. destruct H; [exists 0 | exists 1]; lia. Qed.
Local Lemma iclr_int : forall a n, iclr a n -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ 4096 <= a /\ a + n <= 65536 + k * 18446744073709551616 /\ 6250496 * k <= a.
Proof. intros a n H G2. unfold iclr, AIMG_LO, AIMG_HI in H. Local Ltac2 Set LiaHints.tbl := fun () => "0020=24437255187.543957821123.500000900?S1H2H02G2S1H2H0".
destruct H as [? [?|?]]; [exists 0 | exists 1]; lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Local Lemma ablk_int {rc : runConstT} : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6250496 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. Local Ltac2 Set LiaHints.tbl := fun () => "0020=37386272180.657630483300.600000900BS1H2H12H0S1H2H12H0".
destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Local Ltac band_int H :=
  let k := fresh "k" H in let A := fresh "KA" H in let B := fresh "KB" H in let C := fresh "KC" H in let D := fresh "KD" H in
  let G1 := fresh "G" in let G2 := fresh "G" in
  lazymatch type of H with
  | sclr ?a ?n =>
      assert (G1 : 0 <= a) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia); assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (sclr_int a n H G1 G2) as (k & A & B & C); clear G1 G2
  | iclr ?a ?n =>
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (iclr_int a n H G2) as (k & A & B & C & D); clear G2
  | 4096 <= ?a /\ (?a + ?n <= _ \/ _ <= ?a) =>      (* [comment removed for export] *)
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (iclr_int a n H G2) as (k & A & B & C & D); clear G2
  | ablk ?lo ?hi => let E := fresh "KE" H in destruct (ablk_int lo hi H) as (k & A & B & E & C & D)
  end.

Section CANSEC1. Context {rc : runConstT}.
Section Kinds.
Variables (sp t AB S UB gq nodes store res ctx lo grz ssz lst eb gl : Z).
Definition kfactsF : Prop :=
     (ATOP <= lo /\ lo <= sp - 4096)
  /\ (sclr t 4096 /\ iclr t 4096 /\ 4096 <= t /\ t + 4096 <= ATOP)      (* [comment removed for export] *)
  /\ (17594333495296 <= res /\ res + 137439023104 <= ATOP)      (* [comment removed for export] *)
  /\ (res + 4096 <= AB /\ AB + S <= res + 137439023104 /\ AB + 16 <= UB /\ UB + 8 <= AB + S)
  /\ (2201439137792 <= shad AB /\ shad UB = shad AB + grz /\ 2 <= grz /\ 1 <= gq /\ shad UB + gq <= shad AB + ssz
      /\ shad AB + ssz <= 17594333495296)
  /\ (sclr nodes 1048576 /\ 6250496 <= nodes /\ nodes + 1048576 <= ATOP /\ sclr store 8388608 /\ 6250496 <= store /\ store + 8388608 <= ATOP)   (* [comment removed for export] *)
  /\ (sclr ctx 65536 /\ 6250496 <= ctx /\ ctx + 65536 <= ATOP)   (* [comment removed for export] *)
  /\ ((lst = 0 /\ qsz lst = 8) \/ (res + 4096 <= lst /\ lst + 8192 <= res + 137439023104 /\ qsz lst = 8192))   (* [comment removed for export] *)
  /\ (res + 4096 <= eb /\ eb + 8192 <= res + 137439023104)      (* [comment removed for export] *)
  /\ (gl = 0 \/ (res + 4096 <= gl /\ gl + 8192 <= res + 137439023104)).
Hypothesis KF : kfactsF.

Ltac kind := pose proof KF as KF'; unfold kfactsF, AIMG_HI in *;
  destruct KF' as (F_lo & (Ft1 & Ft2 & Ft3 & Ft4) & F_res & F_slot & F_sh & (Fn1 & Fn2 & Fn3 & Fs1 & Fs2 & Fs3) & (Fc1 & Fc2 & Fc3) & F_lst & F_eb & F_gl);
  band_int Ft1; band_int Ft2; band_int Fn1; band_int Fs1; band_int Fc1; clear Ft1 Ft2 Fn1 Fs1 Fc1;   (* [comment removed for export] *)
  cbn [disjoint_from]; repeat (split; [lia|]); first [lia | exact I].

#[using="rc AB S res ctx lo grz ssz KF"] Lemma KF_img : forall A k, 0x10000 <= A -> 0 <= k ->
  (A + k <= ADEPOT_LO /\ (A + k <= 0x9db88 \/ 0x9dbb0 <= A) /\ (A + k <= 0xa2080 \/ 0x1230b0 <= A) /\ (A + k <= 0x130908 \/ 0x13090c <= A))
  \/ (ADEPOT_HI <= A /\ A + k <= AIMG_HI) ->
  disjoint_from (Wf sp t UB gq nodes store lst eb gl) A k.
Proof. intros. Local Ltac2 Set LiaHints.tbl := fun () => "00J0>11169349241.6011504039797.601522040661.60 1700706087.57 21098690581.6025183398293.6028313900550.5435787602334.6035910890664.5840642650621.6041474017840.4443001635577.6043352378177.4543352378177.4844607328842.6046917644229.6049418906396.6153026768941.6254087654434.6057028652341.5359308579281.6061998677113.6062232544678.6064313637817.608816498898.60 9986598342.60 00000400Q01:01>01g02P02X03403<03[03_03c03k04304?04h04l05405Q05U05V05Z06406806T06nS2H1S2KF2H15F_res4F_sh5F_lst4F_glS2KF1H2H02H15F_res5F_lst4F_gl5KCFt25KDFt2S2KFS2KF1H2H02H15F_res5F_lst4F_gl5KCFt25KDFt2S2KF1H2H02H15F_res5F_lst4F_gl5KCFt25KDFt2S3Fn32H2S2KF2H15F_res3Fs25F_lst4F_glS3Fs32H2S2KF2H15F_res6F_slot5F_lst4F_glS2KFS2H1S3Ft42H2S3Ft42H2S2H14F_lo2H2S2KF1H2H02H15F_res5F_lst4F_gl5KCFt25KDFt2S2KFS3Fc32H2S2KF2H15F_res5F_lst4F_eb4F_glS2KFSS2H1S2KF1H2H15F_res5F_lst4F_glS2H1S2KF2H15F_res3Fn25F_lst4F_glS2KF1H2H15F_res5F_lst4F_gl".
kind. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="rc AB S res ctx lo grz ssz KF"] Lemma KF_low : forall A k, 2147450880 <= A -> A + k <= 2148232192 -> 0 <= k ->      (* [comment removed for export] *)
  disjoint_from (Wf sp t UB gq nodes store lst eb gl) A k.
Proof. intros. Local Ltac2 Set LiaHints.tbl := fun () => "00J0>11169349241.6011504039797.601522040661.60 1700706087.57 21098690581.6025183398293.6028313900550.5435787602334.6035910890664.5840642650621.6041474017840.4443001635577.6043352378177.4543352378177.4844607328842.6046917644229.6049418906396.6153026768941.6254087654434.6057028652341.5359308579281.6061998677113.6062232544678.6064313637817.608816498898.60 9986598342.60 00000300<00N00R00d01601>01P01X01i01m02002802@02L02^02b02j03903=03>03A03P03S03e044S1HS2H04F_shS1H2H05KBFt15KCFt1S2KFS1H2H05KBFt15KCFt1S1H2H05KBFt15KCFt1S3Fn32H2S1H2H05KBFs15KCFs1S3Fs32H2S2H05F_res6F_slotS2KFS1HS3Ft42H2S3Ft42H2S2H04F_lo2H2S1H2H05KBFt15KCFt1S2KFS3Fc32H2S2H05F_res4F_ebS2KFSS1HS2KF1H2H05F_resS1HS1H2H05KBFn15KCFn1S2KF1H2H05F_res".
kind. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="rc AB S res ctx lo grz ssz KF"] Lemma KF_hi : forall A k, sp <= A -> 0 <= k ->
  disjoint_from (Wf sp t UB gq nodes store lst eb gl) A k.
Proof. intros. Local Ltac2 Set LiaHints.tbl := fun () => "00J0>11169349368.5911504039924.591522040788.59 1700706214.56 21098690708.5925183398164.5928313900679.5335787602207.5935910890537.5740642650492.5941474017969.4343001635448.5943352378304.4443352378304.4744607328971.5946917644100.5949418906525.6053026769068.6154087654563.5957028652468.5259308579152.5961998677240.5962232544551.5964313637688.598816498771.59 9986598215.59 00000;00K00W00[00g01301;01G01O01d01h02302;02C02F02R02V02^03103503603A03U03`03l04@S1H4F_lo2H1S1H4F_lo4F_sh2H1S1H4F_lo3Ft4S2KFS1H4F_lo3Ft4S1H4F_lo3Ft4S3Fn32H1S1H4F_lo3Fs3S3Fs32H1S1H4F_lo5F_res6F_slotS2KFS1H4F_lo2H1S3Ft42H1S3Ft42H1S1HS1H4F_lo3Ft4S2KFS3Fc32H1S1H4F_lo5F_res4F_ebS2KFSS1H4F_lo2H1S2KF1H4F_lo5F_res2H1S1H4F_lo2H1S1H4F_lo3Fn3S2KF1H4F_lo5F_res2H1".
kind. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="rc AB S res ctx lo grz ssz KF"] Lemma KF_shad : forall A k, 2147446784 <= A -> A + k <= 17594333495296 -> 0 <= k ->      (* [comment removed for export] *)
  (A + k <= shad UB \/ shad UB + gq <= A) ->
  disjoint_from (Wf sp t UB gq nodes store lst eb gl) A k.
Proof. intros. Local Ltac2 Set LiaHints.tbl := fun () => "00J0>11169349118.6111504039154.611522040018.61 1700705440.58 21098691474.6125183398418.6128313900417.5535787602457.6135910891311.5940642650746.6141474017719.4543001635198.6143352377542.4643352377542.4944607328717.6146917643330.6149418905755.6253026769834.6354087655333.6157028652722.5459308579414.6161998678014.6162232544801.6164313636926.618816499541.61 9986598465.61 00000300700I00M00_01101901K01S01d01h01k02302;02G02Y02]02e03403803903<03K03N03`03oS1HS2H2S1H2H05KBFt15KCFt1S2KFS1H2H05KBFt15KCFt1S1H2H05KBFt15KCFt1S3Fn32H3S1H2H05KBFs15KCFs1S3Fs32H3S2H05F_res6F_slotS2KFS1HS3Ft42H3S3Ft42H3S2H04F_lo2H3S1H2H05KBFt15KCFt1S2KFS3Fc32H3S2H05F_res4F_ebS2KFSS1HS2KF1H2H05F_resS1HS1H2H05KBFn15KCFn1S2KF1H2H05F_res".
kind. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="rc AB S lo grz ssz KF"] Lemma KF_ctx :
  (ctx + 65536 <= t \/ t + 4096 <= ctx) -> (ctx + 65536 <= res \/ res + 137439023104 <= ctx) ->
  (ctx + 65536 <= nodes \/ nodes + 1048576 <= ctx) -> (ctx + 65536 <= store \/ store + 8388608 <= ctx) ->
  forall A k, ctx <= A -> A + k <= ctx + 65536 -> 0 <= k ->
  disjoint_from (Wf sp t UB gq nodes store lst eb gl) A k.
Proof. intros. Local Ltac2 Set LiaHints.tbl := fun () => "00J0>11169348733.6411504039281.641522040145.64 1700705571.61 21098691089.6425183398801.6428313900034.5835787602842.6435910891180.6240642651129.6441474017332.4843001635069.6443352377669.4943352377669.5244607328334.6446917643713.6449418905880.6553026769449.6654087654950.6457028652849.5759308579797.6461998677629.6462232545186.6464313637309.648816499414.64 9986598850.64 00000800P00m01101N01k02302Q02Y03>03B03J03R03Z03g04D04H04P05305705805@05j06206P07:S2H33Fc2S2H32H44F_sh5KBFc15KCFc1S2KF1H2H32H45F_res5F_lst4F_glS2KFS2KF1H2H32H45F_res5F_lst4F_glS2KF1H2H32H45F_res5F_lst4F_glS3Fn32H6S2KF2H22H32H45F_res5F_lst4F_glS3Fs32H6S2KF2H02H32H45F_res6F_slot5F_lst4F_glS2KFS2H33Fc2S3Ft42H6S3Ft42H6S2H44F_lo3Fc3S2KF1H2H32H45F_res5F_lst4F_glS2KFS3Fc32H6S2KF2H02H32H45F_res5F_lst4F_eb4F_glS2KFSS2H33Fc2S2KF2H02H32H45F_res3Fn23Fs23Fc25F_lst4F_glS2H33Fc2S2KF2H12H32H45F_res5F_lst4F_glS2KF2H02H32H45F_res3Fn23Fs23Fc25F_lst4F_gl".
kind. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="rc AB S ctx lo grz ssz KF"] Lemma KF_t :
  (t + 4096 <= res \/ res + 137439023104 <= t) -> (t + 4096 <= nodes \/ nodes + 1048576 <= t) -> (t + 4096 <= store \/ store + 8388608 <= t) ->
  forall A k, t <= A -> A + k <= t + 4096 -> 0 <= k ->
  (A + k <= t + 80 \/ t + 112 <= A) -> (A + k <= t + 2128 \/ t + 2132 <= A) -> (A + k <= t + 2784 \/ t + 2792 <= A) -> (A + k <= t + 2800 \/ t + 3169 <= A) ->
  disjoint_from (Wf sp t UB gq nodes store lst eb gl) A k.
Proof. intros. Local Ltac2 Set LiaHints.tbl := fun () => "00J0>11169348336.6711504038908.671522039772.67 1700705198.64 21098691740.6725183399196.6728313899663.6135787603223.6735910889505.6540642651508.6741474019001.5143001636464.6743352379336.5243352379336.5544607329987.6746917643084.6749418907541.6853026770084.6954087653547.6757028651452.6059308580184.6761998676208.6762232543535.6764313638704.678816499803.67 9986597199.67 00000C00[00_00c00g00k01301]01e02U02Y02l03403<03I03M03Q03Y04G04K04L04_05V05i06S07JS2H22H35KCFt25KDFt2S2H22H34F_sh5KBFt15KCFt1S2H6S2KFS2H5S2H7S3Fn32H9S2KF2H12H22H32H52H62H72H85F_res5F_lst4F_glS3Fs32H9S2KF1H2H22H32H52H62H72H85F_res6F_slot5F_lst4F_glS2KFS2H22H35KCFt25KDFt2S3Ft42H9S3Ft42H9S2H34F_lo3Ft4S2H8S2KFS3Fc32H9S2KF1H2H22H32H52H62H72H85F_res5F_lst4F_eb4F_glS2KFSS2H22H35KCFt25KDFt2S2KF1H2H22H32H52H62H72H85F_res3Fn23Fs25F_lst4F_gl5KBFt2S2H22H35KCFt25KDFt2S2KF2H02H22H32H52H62H72H85F_res5F_lst4F_glS2KF1H2H22H32H52H62H72H85F_res3Fn23Fs25F_lst4F_gl5KBFt2".
kind. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="rc AB S ctx lo grz ssz KF"] Lemma KF_res :
  (t + 4096 <= res \/ res + 137439023104 <= t) -> (nodes + 1048576 <= res \/ res + 137439023104 <= nodes) ->
  (store + 8388608 <= res \/ res + 137439023104 <= store) ->
  forall A k, res <= A -> A + k <= res + 137439023104 -> 0 <= k ->
  (A + k <= UB - 16 \/ UB + 8 <= A) ->
  (A + k <= lst \/ lst + 8192 <= A) -> (A + k <= eb \/ eb + 8192 <= A) -> (A + k <= gl \/ gl + 8 <= A) ->
  disjoint_from (Wf sp t UB gq nodes store lst eb gl) A k.
Proof. intros. Local Ltac2 Set LiaHints.tbl := fun () => "00J0>11169348336.6711504038908.671522039772.67 1700705198.64 21098691740.6725183399196.6728313899663.6135787603223.6735910889505.6540642651508.6741474019001.5143001636464.6743352379336.5243352379336.5544607329987.6746917643084.6749418907541.6853026770084.6954087653547.6757028651452.6059308580184.6761998676208.6762232543535.6764313638704.678816499803.67 9986597199.67 00000:00I01A01E02=03503=04604>04B04F04P04X04`04o05g05k06306706;06<06F06J06T07M08:S2H25F_resS2H25F_res4F_shS2KF1H2H22H32H42H52H62H72H85F_res6F_slot5F_lst4F_eb4F_glS2KFS2KF1H2H22H32H42H52H62H72H85F_res6F_slot5F_lst4F_eb4F_glS2KF1H2H22H32H42H52H62H72H85F_res6F_slot5F_lst4F_eb4F_glS3Fn32H9S2KF2H12H22H32H42H52H62H72H85F_res6F_slot5F_lst4F_eb4F_glS3Fs32H9S2H5S2KFS2H25F_resS3Ft42H9S3Ft42H9S2H34F_lo5F_resS2KF1H2H22H32H42H52H62H72H85F_res6F_slot5F_lst4F_eb4F_glS2KFS3Fc32H9S2H7S2KFSS2H25F_resS2H8S2H25F_resS2KF2H02H22H32H42H52H62H72H85F_res6F_slot5F_lst4F_eb4F_glS2KF2H22H42H62H85F_res6F_slot5F_lst4F_eb4F_gl".
kind. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="AB S ctx lo grz ssz KF"] Lemma KF_obj : forall A k, ((6250496 <= A /\ A + k <= 2147446784) \/ 17594333495296 <= A) -> A + k <= ATOP -> 0 <= k ->      (* [comment removed for export] *)
  (A + k <= t \/ t + 4096 <= A) -> (A + k <= res \/ res + 137439023104 <= A) ->
  (A + k <= nodes \/ nodes + 1048576 <= A) -> (A + k <= store \/ store + 8388608 <= A) ->
  disjoint_from (Wf sp t UB gq nodes store lst eb gl) A k.
Proof. intros. Local Ltac2 Set LiaHints.tbl := fun () => "00J0>11169348733.6411504039281.641522040145.64 1700705571.61 21098691089.6425183398801.6428313900034.5835787602842.6435910891180.6240642651129.6441474017332.4843001635069.6443352377669.4943352377669.5244607328334.6446917643713.6449418905880.6553026769449.6654087654950.6457028652849.5759308579797.6461998677629.6462232545186.6464313637309.648816499414.64 9986598850.64 00000300R00V00Z00^00b00j00n01601X01\01_01g01o02802<02@02H02h02l02m03003U03X03\04AS1HS2KF1H2H15F_res4F_sh5F_lst4F_glS2H2S2KFS2H2S2H2S3Fn32H6S2H5S3Fs32H6S2KF2H12H35F_res6F_slot5F_lst4F_glS2KFS1HS3Ft42H6S3Ft42H6S2H04F_loS2H2S2KFS3Fc32H6S2KF2H12H35F_res5F_lst4F_eb4F_glS2KFSS1HS2KF1H2H12H35F_res3Fn23Fs25F_lst4F_glS1HS2H4S2KF1H2H12H35F_res3Fn23Fs25F_lst4F_gl".
kind. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End Kinds.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Frames.
Variables (L : alayout) (W : list (Z * Z)) (m m' : amem).
Hypothesis MU : munch W m m'.
Hypothesis WM : wmono asegs m m'.

#[using="MU WM"] Lemma aslots_update_gen : forall st st' X X' c,
  aslots L st X m c ->
  ndist st' c = ndist st c ->
  c_allocated_user (get_cls st' c) = c_allocated_user (get_cls st c) ->
  c_mapped_user (get_cls st' c) = c_mapped_user (get_cls st c) ->
  (forall k, 0 <= k < ndist st c ->
       (busy_of X' c k = busy_of X c k /\ disjoint_from W (aslot_addr L c k) (size_of_class c)
          /\ (forall b, busy_of X c k = Some b -> xb_class b = c /\ xb_slot b = k /\ xb_fits b))
    \/ match busy_of X' c k with None => junk_at m' (aslot_addr L c k) (size_of_class c) | Some b => aslot_busy L m' b end) ->
  (0 < c_mapped_user (get_cls st c) - c_allocated_user (get_cls st c) ->
   disjoint_from W (aregion L c + c_allocated_user (get_cls st c)) (c_mapped_user (get_cls st c) - c_allocated_user (get_cls st c))) ->
  aslots L st' X' m' c.
Proof.
  intros st st' X X' c [SL UND] E0 E1 E2 OTH DU. unfold aslots. cbv zeta. rewrite E0, E1, E2. split.
  - intros k Hk. destruct (OTH k Hk) as [(EB & D & WFB)|NEW]; [| exact NEW].
    rewrite EB. specialize (SL k Hk). destruct (busy_of X c k) as [b|].
    + destruct (WFB b eq_refl) as (C1' & K1 & FIT1).
      eapply aslot_busy_frame; [exact MU| exact WM| exact SL | exact FIT1 |]. unfold xb_alloc. rewrite C1', K1. exact D.
    + eapply junk_frame; [exact SL | exact MU | exact WM | intros _; exact D].
  - eapply junk_frame; [exact UND | exact MU | exact WM | exact DU].
Qed.

#[using="MU WM"] Lemma aslot_shadow_update_gen : forall st st' X X' c,
  aslot_shadow L st X m c ->
  ndist st' c = ndist st c ->
  c_allocated_user (get_cls st' c) = c_allocated_user (get_cls st c) ->
  c_mapped_user (get_cls st' c) = c_mapped_user (get_cls st c) ->
  (forall k, 0 <= k < ndist st c ->
       (slot_shadow_bytes (size_of_class c) (busy_of X' c k) = slot_shadow_bytes (size_of_class c) (busy_of X c k)
          /\ disjoint_from W (shad (aslot_addr L c k)) (shlen (size_of_class c)))
    \/ rw_cells asegs m' (shad (aslot_addr L c k)) [CB (Z.to_nat (shlen (size_of_class c))) (slot_shadow_bytes (size_of_class c) (busy_of X' c k))]) ->
  (0 < shlen (c_mapped_user (get_cls st c) - c_allocated_user (get_cls st c)) ->
   disjoint_from W (shad (aregion L c + c_allocated_user (get_cls st c))) (shlen (c_mapped_user (get_cls st c) - c_allocated_user (get_cls st c)))) ->
  0 <= shlen (size_of_class c) ->
  aslot_shadow L st' X' m' c.
Proof.
  intros st st' X X' c [SL UND] E0 E1 E2 OTH DU POS. unfold aslot_shadow. cbv zeta. rewrite E0, E1, E2. split.
  - intros k Hk. destruct (OTH k Hk) as [[EB D]|NEW]; [| exact NEW].
    rewrite EB. specialize (SL k Hk).
    eapply cells_frame; [exact SL| exact MU| exact WM |]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by exact POS. exact D.
  - eapply fill_frame; [exact UND | exact MU | exact WM | exact DU].
Qed.
End Frames.

(* [comment removed for export] *)
#[using="Type"] Lemma slot_shadow_bbatch : forall S k24,
  2 <= shlen S -> slot_shadow_bytes S (Some (bbatch k24)) = repeat (Z_to_bv 8 0xfa) (Z.to_nat (shlen S)).
Proof.
  intros S k24 H. unfold slot_shadow_bytes, bbatch. cbn [xb_n xb_st].
  replace (rz_size 0) with 16 by reflexivity. replace (shlen 16) with 2 by reflexivity. replace (granules 0) with 0 by reflexivity.
  rewrite <- !repeat_app. f_equal. Local Ltac2 Set LiaHints.tbl := fun () => "0010=16592602015.4000003S1H".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC1.
