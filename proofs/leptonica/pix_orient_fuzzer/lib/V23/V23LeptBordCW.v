(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptArith2 GrayACELib.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require Import O23LeptPixHdr O23LeptPixCreate O23LeptCmapValid O23LeptCmap2 O23LeptPixCopyA O23LeptPixCopy O23LeptPixCopyAT O23LeptPixCreateT2 O23LeptRop_iface O23LeptRop O23LeptGrayA O23LeptRop2_iface O23LeptRop2 O23LeptRopClip O23LeptRop2C O23LeptRopUC O23LeptBord_iface O23LeptBordSegs O23LeptBordCW.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptStderr V23LeptBase V23LeptErr V23LeptPixHdr V23LeptPixCreate V23LeptCmapValid V23LeptCmap2 V23LeptPixCopyA V23LeptPixCopy V23LeptPixCopyAT V23LeptPixCreateT2 V23LeptRop_iface V23LeptRop V23LeptGrayA V23LeptRop2_iface V23LeptRop2 V23LeptRop2C V23LeptRopUC V23LeptBord_iface V23LeptBordSegs.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import LeptRoom LeptRoomPC LeptRoom14 LeptRoomBL LeptRop2Arith.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require O23LeptPixCopyT.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require V23LeptPixCopyT.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require LiaFast.
Local Ltac Stdlib.micromega.Lia.lia ::= first [ solve [LiaFast.flia2] | Zify.zify; xlia zchecker ].
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Section GrayBorderW.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V23Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Section WithRop.
Let ROPU : pixRasterop_uniclip_contract := pixRasterop_uniclip_W.
Let ROPS : pixRasterop_srcclip_contract := pixRasterop_srcclip_W.

(* [comment removed for export] *)
Lemma ab_uni_W : forall C A A2 M md regs (s' pixd data wd hd d cd x y rw rh op : Z) (ret : word) (S : TSet),
  Cok C -> W C A2 M md -> sub_live A A2 ->
  getr regs 2 = Z_to_bv 64 s' -> (s' mod 16 = 0)%Z -> (c_top C - LSTK + ROP_STACK <= s')%Z -> (s' + 8 <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret ->
  getr regs 10 = Z_to_bv 64 pixd -> getr regs 11 = Z_to_bv 64 x -> getr regs 12 = Z_to_bv 64 y -> getr regs 13 = Z_to_bv 64 rw ->
  getr regs 14 = Z_to_bv 64 rh -> getr regs 15 = Z_to_bv 64 op ->
  rdn SEGS M (Z_to_bv 64 s') 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  PIXat M pixd (hdv wd hd d cd data) -> hdr_ok wd hd d -> (1 <= wd)%Z -> (1 <= hd)%Z -> (d = 1 \/ d = 8)%Z -> d = 1%Z ->
  rop_rect wd hd x y rw rh -> (op = 0 \/ op = 15)%Z ->
  live A2 (Z_to_bv 64 pixd) = Some 64%Z -> Z_to_bv 64 pixd <> Z_to_bv 64 data ->
  live A2 (Z_to_bv 64 data) = Some (4 * (wpl_of wd d * hd))%Z -> live A (Z_to_bv 64 data) = None -> live (c_A0 C) (Z_to_bv 64 data) = None ->
  (forall m' regs', W C A2 m' md -> cs_kept regs regs' -> POSTM C A s' M m' -> PIXat m' pixd (hdv wd hd d cd data) ->
      (forall a : word, ~ scratch C s' a -> ~ (data <= bv_unsigned a < data + 4 * (wpl_of wd d * hd))%Z -> m' a = M a) ->
      getr regs' 10 = Z_to_bv 64 0 ->
      realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst regs (0x7f13c : word) M al_rom) md) S.
Proof.
  intros C A A2 M md regs s' pixd data wd hd d cd x y rw rh op ret S CK HW SUB H2 Hs16 Hlo Hhi H1 Hret H10 H11 H12 H13 H14 H15 Rsy PX HOK Hw Hh Hd Hd1 RECT Hop Lp NEpd Ld Ld0 Ld00 HK.
  pose proof HOK as (DV & Hw2 & Hh2 & Hsz). pose proof RECT as (Rx & Ry & Rw & Rh & Rxw & Ryh).
  replace (0x7f13c : word) with (Z_to_bv 64 PC_pixRasterop) by (apply bv_eq; reflexivity).
  exact (ROPU C A A2 M md regs s' pixd x y rw rh op (hdv wd hd d cd data) (Z_to_bv 64 0) ret S CK HW SUB H2 Hs16 Hlo Hhi H1 Hret H10 H11 H12 H13 H14 H15 Rsy
           PX Hd1 (hdr_rop_shape wd hd d HOK Hw Hh Hd) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hop Lp NEpd Ld Ld0 Ld00 HK).
Qed.

(* [comment removed for export] *)
Lemma ab_fills_W : forall C A A2 m m4 md2 regs r7 (K : word -> Prop) (s pixs pixd data w h d cm cd datas spp rc fmt spc txt left right top bot op : Z) (ret : word) (S : TSet),
  Cok C -> (s mod 16 = 0)%Z -> (c_top C - LSTK + ABG_STACK <= s)%Z -> (s <= c_top C)%Z -> ret_ok ret ->
  W C A2 m4 md2 -> POSTM C A s m m4 ->
  hdr_ok w h d -> (1 <= w)%Z -> (1 <= h)%Z -> (d = 1 \/ d = 8)%Z -> d = 1%Z -> (left mod 32 = 0)%Z ->
  (1 <= left <= 64)%Z -> (1 <= right <= 64)%Z -> (1 <= top <= 64)%Z -> (1 <= bot <= 64)%Z -> rop2_arm (left * d)%Z (0 * d)%Z (w * d)%Z (wpl_of w d) -> (op = 0 \/ op = 15)%Z ->
  hdr_ok (w + left + right) (h + top + bot) d ->
  pix_freshc C A A2 m4 pixd (w + left + right) (h + top + bot) d cd data ->
  (forall a : word, K a -> ~ scratch C s a /\ ~ (data <= bv_unsigned a < data + 4 * (wpl_of (w + left + right) d * (h + top + bot)))%Z) ->
  PIXat m4 pixs (hdvgc w h d cm datas spp rc fmt spc txt) -> live A (Z_to_bv 64 pixs) = Some 64%Z -> live A (Z_to_bv 64 datas) = Some (4 * (wpl_of w d * h))%Z ->
  abfr m4 s ret regs w h d ->
  getr r7 2 = Z_to_bv 64 (s - 112) -> getr r7 8 = Z_to_bv 64 pixs -> getr r7 18 = Z_to_bv 64 left -> getr r7 22 = Z_to_bv 64 right ->
  getr r7 9 = Z_to_bv 64 top -> getr r7 19 = Z_to_bv 64 bot -> getr r7 20 = Z_to_bv 64 pixd ->
  getr r7 21 = Z_to_bv 64 (w + left + right) -> getr r7 23 = Z_to_bv 64 (h + top + bot) ->
  getr r7 24 = Z_to_bv 64 op -> getr r7 3 = getr regs 3 -> getr r7 4 = getr regs 4 -> getr r7 25 = getr regs 25 -> getr r7 26 = getr regs 26 ->
  getr r7 27 = getr regs 27 -> getr regs 2 = Z_to_bv 64 s ->
  (forall m' regs', W C A2 m' md2 -> cs_kept regs regs' -> POSTM C A s m m' -> getr regs' 10 = Z_to_bv 64 pixd ->
      pix_freshc C A A2 m' pixd (w + left + right) (h + top + bot) d cd data -> (forall a : word, K a -> m' a = m4 a) ->
      realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md2) S) ->
  realizes SEGS (mkCfg (mkst r7 (0x710bc : word) m4 al_rom) md2) S.
Proof.
  intros C A A2 m m4 md2 regs r7 K s pixs pixd data w h d cm cd datas spp rc fmt spc txt left right top bot op ret S CK Hs16 Hlo Hhi Hret HW4 PM4 HOK Hw Hh Hd Hd1 Hl32 Hl Hr Ht Hb Hal Hop HOKd PF HKK
         PXs4 Lps Lds FR4 W2 W8 W18 W22 W9 W19 W20 W21 W23 W24 W3 W4 K25 K26 W27 H2 HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold ABG_STACK, O23LeptBase.LSF, LSF in *.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof HOK as (DV & Hw2 & Hh2 & Hsz). pose proof (wpl_of_range w d ltac:(lia) DV) as Hwpl.
  pose proof PXs4 as (Hs0 & Hs64' & WFs & _).
  set (wd := (w + left + right)%Z) in *. set (hd := (h + top + bot)%Z) in *.
  pose proof HOKd as (_ & Hwd2 & Hhd2 & Hszd). pose proof (wpl_of_range wd d ltac:(subst wd; lia) DV) as Hwpld.
  assert (Hnd : (0 <= wpl_of wd d * hd)%Z) by (apply Z.mul_nonneg_nonneg; subst hd; lia).
  pose proof PF as (Gp & TOPp & ALp & Gd & TOPd & ALd & NEpd & L0p & L0d & L00p & L00d & L2p & L2d & SUBb & PXd4).
  destruct (blk_range C A2 m4 _ (Z_to_bv 64 pixs) 64 CK HW4 (SUBb _ _ Lps) ltac:(lia)) as [Gps TOPps]. rewrite u_Z2bv in Gps, TOPps by lia.
  assert (NEsd : Z_to_bv 64 pixs <> Z_to_bv 64 data) by (intros E; rewrite E in Lps; rewrite Lps in L0d; discriminate).
  assert (NEdd : Z_to_bv 64 datas <> Z_to_bv 64 data) by (intros E; rewrite E in Lds; rewrite Lds in L0d; discriminate).
  assert (NEpdw : Z_to_bv 64 pixd <> Z_to_bv 64 data) by (apply zbv_ne2; lia).
  assert (Hs128 : (112 <= s)%Z) by lia. assert (Hs64 : (s < 2 ^ 64)%Z) by lia.
  assert (Hs16' : ((s - 112) mod 16 = 0)%Z) by (rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity).
  assert (Hlo' : (c_top C - LSTK + ROP_STACK <= s - 112)%Z) by (unfold ROP_STACK; lia).
  assert (Hhi' : (s - 112 + 8 <= c_top C)%Z) by lia.
  assert (Hwd1 : (1 <= wd)%Z) by (subst wd; lia). assert (Hhd1 : (1 <= hd)%Z) by (subst hd; lia).
  assert (KST : forall (mp N n : word -> option byte),
            (forall a : word, K a -> mp a = m4 a) ->
            (forall x : word, ~ (s - 112 <= u x < s - 104)%Z -> N x = mp x) ->
            (forall a : word, ~ scratch C (s - 112) a -> ~ (data <= u a < data + 4 * (wpl_of wd d * hd))%Z -> n a = N a) ->
            forall a : word, K a -> n a = m4 a).
  { intros mp N n Hmp HN Hn a Ka. destruct (HKK a Ka) as [S1 S2]. unfold scratch in S1.
    rewrite (Hn a ltac:(unfold scratch; lia) S2), (HN a ltac:(lia)). exact (Hmp a Ka). }
  destruct (ab_R1 al_rom r7 m4 s pixd left hd op ltac:(lia) ltac:(lia) (W_sok_win C A2 m4 _ (s - 112) 8 CK HW4 ltac:(lia) ltac:(cbn; lia)) W2 W20 W18 W23 W24)
    as (r8 & RUN8 & a1 & a10 & a11 & a12 & a13 & a14 & a15 & AG8).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW4)) | exact (mp_lazy _ (w_pure _ _ _ _ HW4)) | exact RUN8 |]. clear RUN8.
  set (N8 := wbytes m4 (Z_to_bv 64 (s - 112)) (word_to_le_bytes 8 (Z_to_bv 64 0))).
  assert (WP8 : W C A2 N8 md2 /\ POSTM C A s m N8) by (subst N8; wp_win CK).
  destruct WP8 as [HW8 PM8].
  assert (OUT8 : forall x : word, ~ (s - 112 <= u x < s - 104)%Z -> N8 x = m4 x).
  { intros x Hx. subst N8. apply (wbytes_out_Z _ _ 8); [rewrite length_N_to_le_bytes; reflexivity | clear - Hs128 Hs64; lia | clear - Hs128 Hs64; lia | clear - Hs128 Hs64 Hx; lia]. }
  pose proof (abfr_out m4 N8 _ _ s ret regs w h d OUT8 ltac:(lia) ltac:(lia) ltac:(lia) FR4) as FR8.
  assert (PXd8 : PIXat N8 pixd (hdv wd hd d cd data)) by (apply (PIXat_frame m4); [exact PXd4 | intros x Hx; apply OUT8; lia]).
  assert (PXs8 : PIXat N8 pixs (hdvgc w h d cm datas spp rc fmt spc txt)) by (apply (PIXat_frame m4); [exact PXs4 | intros x Hx; apply OUT8; lia]).
  apply (ab_uni_W C A A2 N8 _ r8 (s - 112) pixd data wd hd d cd 0 0 left hd op (Z_to_bv 64 0x710e4) S CK HW8 SUBb
           ltac:(csr; reflexivity) Hs16' Hlo' Hhi'
           a1 ltac:(red; apply bv_eq; reflexivity) a10 a11 a12 a13 a14 a15
           ltac:(subst N8; apply (rdn_wbytes_hit8 SEGS); rewrite u_Z2bv by lia; lia)
           PXd8 HOKd Hwd1 Hhd1 Hd Hd1 ltac:(unfold rop_rect; subst wd hd; lia) Hop L2p NEpdw L2d L0d L00d).
  intros n8 q8 HV8 CS8 PN8 PXe8 KP8 A10_8.
  replace (Z_to_bv 64 0x710e4) with (0x710e4 : word) by (apply bv_eq; reflexivity).
  assert (PO8 : POSTM C A s m n8) by (eapply POSTM_trans; [exact PM8 | eapply POSTM_mono; [|exact PN8]; lia]).
  pose proof (abfr_frm C (s - 112) N8 n8 s ret regs w h d CK (proj1 PN8) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) FR8) as FS8.
  assert (PXt8 : PIXat n8 pixs (hdvgc w h d cm datas spp rc fmt spc txt)).
  { apply (PIXat_frame N8); [exact PXs8|]. intros x Hx. exact (LIVK_at A N8 n8 pixs 64 x (proj2 PN8) Lps ltac:(lia) ltac:(lia) Hx). }
  assert (KK8 : forall a : word, K a -> n8 a = m4 a) by (apply (KST m4 N8 n8); [intros a _; reflexivity | exact OUT8 | exact KP8]).
  destruct (ab_R2 al_rom q8 n8 s pixd wd right hd op ltac:(lia) ltac:(lia) ltac:(subst wd; lia) ltac:(subst wd; lia) (W_sok_win C A2 n8 _ (s - 112) 8 CK HV8 ltac:(lia) ltac:(cbn; lia))
              ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity))
    as (r9 & RUN9 & b1 & b10 & b11 & b12 & b13 & b14 & b15 & AG9).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HV8)) | exact (mp_lazy _ (w_pure _ _ _ _ HV8)) | exact RUN9 |]. clear RUN9.
  set (N9 := wbytes n8 (Z_to_bv 64 (s - 112)) (word_to_le_bytes 8 (Z_to_bv 64 0))).
  assert (WP9 : W C A2 N9 md2 /\ POSTM C A s m N9) by (subst N9; wp_win CK).
  destruct WP9 as [HW9 PM9].
  assert (OUT9 : forall x : word, ~ (s - 112 <= u x < s - 104)%Z -> N9 x = n8 x).
  { intros x Hx. subst N9. apply (wbytes_out_Z _ _ 8); [rewrite length_N_to_le_bytes; reflexivity | clear - Hs128 Hs64; lia | clear - Hs128 Hs64; lia | clear - Hs128 Hs64 Hx; lia]. }
  pose proof (abfr_out n8 N9 _ _ s ret regs w h d OUT9 ltac:(lia) ltac:(lia) ltac:(lia) FS8) as FR9.
  assert (PXd9 : PIXat N9 pixd (hdv wd hd d cd data)) by (apply (PIXat_frame n8); [exact PXe8 | intros x Hx; apply OUT9; lia]).
  assert (PXs9 : PIXat N9 pixs (hdvgc w h d cm datas spp rc fmt spc txt)) by (apply (PIXat_frame n8); [exact PXt8 | intros x Hx; apply OUT9; lia]).
  apply (ab_uni_W C A A2 N9 _ r9 (s - 112) pixd data wd hd d cd (w + left) 0 right hd op (Z_to_bv 64 0x71118) S CK HW9 SUBb
           ltac:(csr; reflexivity) Hs16' Hlo' Hhi'
           b1 ltac:(red; apply bv_eq; reflexivity) b10 ltac:(rewrite b11; f_equal; subst wd; lia) b12 b13 b14 b15
           ltac:(subst N9; apply (rdn_wbytes_hit8 SEGS); rewrite u_Z2bv by lia; lia)
           PXd9 HOKd Hwd1 Hhd1 Hd Hd1 ltac:(unfold rop_rect; subst wd hd; lia) Hop L2p NEpdw L2d L0d L00d).
  intros n9 q9 HV9 CS9 PN9 PXe9 KP9 A10_9.
  replace (Z_to_bv 64 0x71118) with (0x71118 : word) by (apply bv_eq; reflexivity).
  assert (PO9 : POSTM C A s m n9) by (eapply POSTM_trans; [exact PM9 | eapply POSTM_mono; [|exact PN9]; lia]).
  pose proof (abfr_frm C (s - 112) N9 n9 s ret regs w h d CK (proj1 PN9) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) FR9) as FS9.
  assert (PXt9 : PIXat n9 pixs (hdvgc w h d cm datas spp rc fmt spc txt)).
  { apply (PIXat_frame N9); [exact PXs9|]. intros x Hx. exact (LIVK_at A N9 n9 pixs 64 x (proj2 PN9) Lps ltac:(lia) ltac:(lia) Hx). }
  assert (KK9 : forall a : word, K a -> n9 a = m4 a) by (apply (KST n8 N9 n9); [exact KK8 | exact OUT9 | exact KP9]).
  destruct (ab_R3 al_rom q9 n9 s pixd wd top op ltac:(lia) ltac:(lia) (W_sok_win C A2 n9 _ (s - 112) 8 CK HV9 ltac:(lia) ltac:(cbn; lia))
              ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity))
    as (r10 & RUN10 & c1 & c10 & c11 & c12 & c13 & c14 & c15 & AG10).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HV9)) | exact (mp_lazy _ (w_pure _ _ _ _ HV9)) | exact RUN10 |]. clear RUN10.
  set (N10 := wbytes n9 (Z_to_bv 64 (s - 112)) (word_to_le_bytes 8 (Z_to_bv 64 0))).
  assert (WP10 : W C A2 N10 md2 /\ POSTM C A s m N10) by (subst N10; wp_win CK).
  destruct WP10 as [HW10 PM10].
  assert (OUT10 : forall x : word, ~ (s - 112 <= u x < s - 104)%Z -> N10 x = n9 x).
  { intros x Hx. subst N10. apply (wbytes_out_Z _ _ 8); [rewrite length_N_to_le_bytes; reflexivity | clear - Hs128 Hs64; lia | clear - Hs128 Hs64; lia | clear - Hs128 Hs64 Hx; lia]. }
  pose proof (abfr_out n9 N10 _ _ s ret regs w h d OUT10 ltac:(lia) ltac:(lia) ltac:(lia) FS9) as FR10.
  assert (PXd10 : PIXat N10 pixd (hdv wd hd d cd data)) by (apply (PIXat_frame n9); [exact PXe9 | intros x Hx; apply OUT10; lia]).
  assert (PXs10 : PIXat N10 pixs (hdvgc w h d cm datas spp rc fmt spc txt)) by (apply (PIXat_frame n9); [exact PXt9 | intros x Hx; apply OUT10; lia]).
  apply (ab_uni_W C A A2 N10 _ r10 (s - 112) pixd data wd hd d cd 0 0 wd top op (Z_to_bv 64 0x71140) S CK HW10 SUBb
           ltac:(csr; reflexivity) Hs16' Hlo' Hhi'
           c1 ltac:(red; apply bv_eq; reflexivity) c10 c11 c12 c13 c14 c15
           ltac:(subst N10; apply (rdn_wbytes_hit8 SEGS); rewrite u_Z2bv by lia; lia)
           PXd10 HOKd Hwd1 Hhd1 Hd Hd1 ltac:(unfold rop_rect; subst wd hd; lia) Hop L2p NEpdw L2d L0d L00d).
  intros n10 q10 HV10 CS10 PN10 PXe10 KP10 A10_10.
  replace (Z_to_bv 64 0x71140) with (0x71140 : word) by (apply bv_eq; reflexivity).
  assert (PO10 : POSTM C A s m n10) by (eapply POSTM_trans; [exact PM10 | eapply POSTM_mono; [|exact PN10]; lia]).
  pose proof (abfr_frm C (s - 112) N10 n10 s ret regs w h d CK (proj1 PN10) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) FR10) as FS10.
  assert (PXt10 : PIXat n10 pixs (hdvgc w h d cm datas spp rc fmt spc txt)).
  { apply (PIXat_frame N10); [exact PXs10|]. intros x Hx. exact (LIVK_at A N10 n10 pixs 64 x (proj2 PN10) Lps ltac:(lia) ltac:(lia) Hx). }
  assert (KK10 : forall a : word, K a -> n10 a = m4 a) by (apply (KST n9 N10 n10); [exact KK9 | exact OUT10 | exact KP10]).
  destruct (ab_R4 al_rom q10 n10 s pixd hd wd bot op ltac:(lia) ltac:(lia) ltac:(subst hd; lia) ltac:(subst hd; lia) (W_sok_win C A2 n10 _ (s - 112) 8 CK HV10 ltac:(lia) ltac:(cbn; lia))
              ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity))
    as (r11 & RUN11 & d1 & d10 & d11 & d12 & d13 & d14 & d15 & AG11).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HV10)) | exact (mp_lazy _ (w_pure _ _ _ _ HV10)) | exact RUN11 |]. clear RUN11.
  set (N11 := wbytes n10 (Z_to_bv 64 (s - 112)) (word_to_le_bytes 8 (Z_to_bv 64 0))).
  assert (WP11 : W C A2 N11 md2 /\ POSTM C A s m N11) by (subst N11; wp_win CK).
  destruct WP11 as [HW11 PM11].
  assert (OUT11 : forall x : word, ~ (s - 112 <= u x < s - 104)%Z -> N11 x = n10 x).
  { intros x Hx. subst N11. apply (wbytes_out_Z _ _ 8); [rewrite length_N_to_le_bytes; reflexivity | clear - Hs128 Hs64; lia | clear - Hs128 Hs64; lia | clear - Hs128 Hs64 Hx; lia]. }
  pose proof (abfr_out n10 N11 _ _ s ret regs w h d OUT11 ltac:(lia) ltac:(lia) ltac:(lia) FS10) as FR11.
  assert (PXd11 : PIXat N11 pixd (hdv wd hd d cd data)) by (apply (PIXat_frame n10); [exact PXe10 | intros x Hx; apply OUT11; lia]).
  assert (PXs11 : PIXat N11 pixs (hdvgc w h d cm datas spp rc fmt spc txt)) by (apply (PIXat_frame n10); [exact PXt10 | intros x Hx; apply OUT11; lia]).
  apply (ab_uni_W C A A2 N11 _ r11 (s - 112) pixd data wd hd d cd 0 (h + top) wd bot op (Z_to_bv 64 0x71174) S CK HW11 SUBb
           ltac:(csr; reflexivity) Hs16' Hlo' Hhi'
           d1 ltac:(red; apply bv_eq; reflexivity) d10 d11 ltac:(rewrite d12; f_equal; subst hd; lia) d13 d14 d15
           ltac:(subst N11; apply (rdn_wbytes_hit8 SEGS); rewrite u_Z2bv by lia; lia)
           PXd11 HOKd Hwd1 Hhd1 Hd Hd1 ltac:(unfold rop_rect; subst wd hd; lia) Hop L2p NEpdw L2d L0d L00d).
  intros n11 q11 HV11 CS11 PN11 PXe11 KP11 A10_11.
  replace (Z_to_bv 64 0x71174) with (0x71174 : word) by (apply bv_eq; reflexivity).
  assert (PO11 : POSTM C A s m n11) by (eapply POSTM_trans; [exact PM11 | eapply POSTM_mono; [|exact PN11]; lia]).
  pose proof (abfr_frm C (s - 112) N11 n11 s ret regs w h d CK (proj1 PN11) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) FR11) as FS11.
  assert (PXt11 : PIXat n11 pixs (hdvgc w h d cm datas spp rc fmt spc txt)).
  { apply (PIXat_frame N11); [exact PXs11|]. intros x Hx. exact (LIVK_at A N11 n11 pixs 64 x (proj2 PN11) Lps ltac:(lia) ltac:(lia) Hx). }
  assert (KK11 : forall a : word, K a -> n11 a = m4 a) by (apply (KST n10 N11 n11); [exact KK10 | exact OUT11 | exact KP11]).
  destruct FS11 as (CE11 & Rw11 & Rh11 & Rd11).
  destruct (ab_R5 al_rom q11 n11 s pixd pixs left top w h ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) (W_sok_win C A2 n11 _ (s - 112) 8 CK HV11 ltac:(lia) ltac:(cbn; lia))
              Rw11 Rh11 ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity))
    as (r12 & RUN12 & e1 & e10 & e11 & e12 & e13 & e14 & e15 & e16 & e17 & AG12).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HV11)) | exact (mp_lazy _ (w_pure _ _ _ _ HV11)) | exact RUN12 |]. clear RUN12.
  set (N12 := wbytes n11 (Z_to_bv 64 (s - 112)) (word_to_le_bytes 8 (Z_to_bv 64 0))).
  assert (WP12 : W C A2 N12 md2 /\ POSTM C A s m N12) by (subst N12; wp_win CK).
  destruct WP12 as [HW12 PM12].
  assert (OUT12 : forall x : word, ~ (s - 112 <= u x < s - 104)%Z -> N12 x = n11 x).
  { intros x Hx. subst N12. apply (wbytes_out_Z _ _ 8); [rewrite length_N_to_le_bytes; reflexivity | clear - Hs128 Hs64; lia | clear - Hs128 Hs64; lia | clear - Hs128 Hs64 Hx; lia]. }
  pose proof (cellsZ_out n11 N12 _ _ _ OUT12 ltac:(eapply Forall_impl; [|exact (frameA_bounds s ret regs ltac:(lia) ltac:(lia))]; intros [a0 v0] [X Y]; cbn [fst snd] in *; lia) CE11) as CE12.
  assert (PXd12 : PIXat N12 pixd (hdv wd hd d cd data)) by (apply (PIXat_frame n11); [exact PXe11 | intros x Hx; apply OUT12; lia]).
  assert (PXs12 : PIXat N12 pixs (hdvgc w h d cm datas spp rc fmt spc txt)) by (apply (PIXat_frame n11); [exact PXt11 | intros x Hx; apply OUT12; lia]).
  destruct (clip_zero_s left ltac:(lia)) as [CD0 CS0].
  replace (0x7f13c : word) with (Z_to_bv 64 PC_pixRasterop) by (apply bv_eq; reflexivity).
  apply (ROPS C A A2 N12 _ r12 (s - 112)%Z pixd left top w h pixs 0%Z 0%Z (hdv wd hd d cd data) (hdvgc w h d cm datas spp rc fmt spc txt) (Z_to_bv 64 0x7119c) S CK HW12 SUBb
           ltac:(csr; reflexivity) Hs16' Hlo' Hhi'
           e1 ltac:(red; apply bv_eq; reflexivity) e10 e11 e12 e13 e14 e15 e16 e17
           ltac:(subst N12; apply (rdn_wbytes_hit8 SEGS); rewrite u_Z2bv by lia; lia)
           PXd12 PXs12 eq_refl Hd1 (hdr_rop_shape wd hd d HOKd Hwd1 Hhd1 Hd) (hdr_rop_shape w h d HOK Hw Hh Hd)
           ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
           ltac:(unfold rop2_clip_arm; left; rewrite CD0, CS0; split; [exact Hl32 | reflexivity])
           L2p (SUBb _ _ Lps) NEpdw NEsd L2d L0d L00d (SUBb _ _ Lds) NEdd).
  intros n12 q12 HV12 CS12 PN12 PXe12 PXse12 KP12 A10_12.
  replace (Z_to_bv 64 0x7119c) with (0x7119c : word) by (apply bv_eq; reflexivity).
  assert (PO12 : POSTM C A s m n12) by (eapply POSTM_trans; [exact PM12 | eapply POSTM_mono; [|exact PN12]; lia]).
  pose proof (cellsZ_frm C (s - 112) N12 n12 _ CK (proj1 PN12) ltac:(lia) ltac:(eapply Forall_impl; [|exact (frameA_bounds s ret regs ltac:(lia) ltac:(lia))]; intros [a0 v0] [X Y]; cbn [fst snd] in *; lia) CE12) as CE13.
  assert (KK12 : forall a : word, K a -> n12 a = m4 a) by (apply (KST n11 N12 n12); [exact KK11 | exact OUT12 | exact KP12]).
  destruct (ab_E al_rom q12 regs n12 s pixd ret ltac:(lia) ltac:(lia) Hret CE13 ltac:(csr; reflexivity) ltac:(csr; reflexivity)) as (r13 & RUN13 & Z2 & Z1 & Z10 & ZR & AG13).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HV12)) | exact (mp_lazy _ (w_pure _ _ _ _ HV12)) | exact RUN13 |]. clear RUN13.
  apply (HK n12 r13 HV12).
  - apply cs_kept_intro; first [solve [apply ZR; in_lit] | (csr; reflexivity)].
  - exact PO12.
  - exact Z10.
  - unfold pix_freshc. do 14 (split; [assumption|]). exact PXe12.
  - exact KK12.
Qed.

(* [comment removed for export] *)
Lemma pixCopyColormap_none_W : forall C Ar A m md regs (s pixd pixs : Z) (vd vs : pixv) (ret : word) (S : TSet),
  Cok C -> W C A m md -> sub_live Ar A ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 96 + 16 + LSF <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret ->
  getr regs 10 = Z_to_bv 64 pixd -> getr regs 11 = Z_to_bv 64 pixs ->
  PIXat m pixd vd -> PIXat m pixs vs -> p_d vd = p_d vs -> p_cmap vd = 0%Z -> pixd <> pixs -> p_cmap vs = 0%Z ->
  live A (Z_to_bv 64 pixd) = Some 64%Z -> live A (Z_to_bv 64 pixs) = Some 64%Z ->
  (forall m' regs', W C A m' md -> cs_kept regs regs' -> POSTM C Ar s m m' -> PIXat m' pixd vd ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst regs (0x6e4cc : word) m al_rom) md) S.
Proof.
  intros C Ar A m md regs s pixd pixs vd vs ret S CK HW SUB H2 Hs16 Hlo Hhi H1 Hret H10 H11 PXd PXs Hdd Hcd NE Hcs Lpd Lps HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold LSF in *.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof PXd as (Hd0 & Hd64 & WFd & _). pose proof PXs as (Hs0 & Hs64' & WFs & _).
  destruct (blk_range C A m md (Z_to_bv 64 pixd) 64 CK HW Lpd ltac:(lia)) as [Gpd TOPpd]. rewrite u_Z2bv in Gpd, TOPpd by lia.
  destruct (blk_range C A m md (Z_to_bv 64 pixs) 64 CK HW Lps ltac:(lia)) as [Gps TOPps]. rewrite u_Z2bv in Gps, TOPps by lia.
  assert (ALd16 : (pixd mod 16 = 0)%Z) by (pose proof (ai_live_hull A m _ _ _ (w_inv _ _ _ _ HW) Lpd) as (_ & X16 & _); rewrite u_Z2bv in X16 by lia; exact X16).
  assert (ALs16 : (pixs mod 16 = 0)%Z) by (pose proof (ai_live_hull A m _ _ _ (w_inv _ _ _ _ HW) Lps) as (_ & X16 & _); rewrite u_Z2bv in X16 by lia; exact X16).
  destruct (pcm_A al_rom regs m s pixd pixs vd vs ret ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) NE ALd16 ALs16 PXd PXs Hdd Hcd ltac:(lia) ltac:(lia)
              (W_sok_win C A m md (s - 48) 48 CK HW ltac:(lia) ltac:(cbn; lia)) H2 H1 H10 H11)
    as (r1 & RUN1 & Q2 & Q1 & Q10 & Q11 & Q8 & Q9 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |]. clear RUN1.
  assert (WP1 : W C A (FR4c m s ret regs) md /\ POSTM C A s m (FR4c m s ret regs)) by (unfold FR4c; wp_win CK).
  destruct WP1 as [HW1 PM1].
  rewrite Hcs in Q8.
  destruct (pcm_A0 al_rom r1 (FR4c m s ret regs) s ret (getr regs 8) (getr regs 9) ltac:(lia) ltac:(lia) Hret (cells3_FR4c m s ret regs ltac:(lia) ltac:(lia)) Q2 Q8)
    as (r2 & RUN2 & Z2 & Z1 & Z10 & Z8 & Z9 & AG2).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN2 |]. clear RUN2.
  apply (HK (FR4c m s ret regs) r2 HW1).
  - apply cs_kept_intro; csr; try reflexivity. all: rewrite ?Z8, ?Z9; reflexivity.
  - apply (POSTM_sub C Ar A); [exact SUB | exact PM1].
  - apply (PIXat_frame m); [exact PXd|]. intros x Hx. unfold FR4c. rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. reflexivity.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma ab_tailC_W : forall C A A2 m m4 md2 regs r6 (K : word -> Prop) (s pixs pixd data w h d cm cd datas spp rc fmt spc txt left right top bot val : Z) (ret : word) (S : TSet),
  Cok C -> (s mod 16 = 0)%Z -> (c_top C - LSTK + ABG_STACK <= s)%Z -> (s <= c_top C)%Z -> ret_ok ret ->
  W C A2 m4 md2 -> POSTM C A s m m4 ->
  hdr_ok w h d -> (1 <= w)%Z -> (1 <= h)%Z -> (d = 1 \/ d = 8)%Z -> d = 1%Z -> (left mod 32 = 0)%Z ->
  (1 <= left <= 64)%Z -> (1 <= right <= 64)%Z -> (1 <= top <= 64)%Z -> (1 <= bot <= 64)%Z -> rop2_arm (left * d)%Z (0 * d)%Z (w * d)%Z (wpl_of w d) ->
  (val = 0 \/ val = 2 ^ d - 1)%Z ->
  hdr_ok (w + left + right) (h + top + bot) d ->
  pix_freshc C A A2 m4 pixd (w + left + right) (h + top + bot) d cd data ->
  (forall a : word, K a -> ~ scratch C s a /\ ~ (data <= bv_unsigned a < data + 4 * (wpl_of (w + left + right) d * (h + top + bot)))%Z) ->
  PIXat m4 pixs (hdvgc w h d cm datas spp rc fmt spc txt) -> live A (Z_to_bv 64 pixs) = Some 64%Z -> live A (Z_to_bv 64 datas) = Some (4 * (wpl_of w d * h))%Z ->
  abfr m4 s ret regs w h d ->
  getr r6 2 = Z_to_bv 64 (s - 112) -> getr r6 8 = Z_to_bv 64 pixs -> getr r6 18 = Z_to_bv 64 left -> getr r6 22 = Z_to_bv 64 right -> getr r6 9 = Z_to_bv 64 top -> getr r6 19 = Z_to_bv 64 bot -> getr r6 20 = Z_to_bv 64 pixd -> getr r6 21 = Z_to_bv 64 (w + left + right) -> getr r6 23 = Z_to_bv 64 (h + top + bot) -> getr r6 24 = Z_to_bv 64 val -> getr r6 3 = getr regs 3 -> getr r6 4 = getr regs 4 -> getr r6 25 = getr regs 25 -> getr r6 26 = getr regs 26 -> getr r6 27 = getr regs 27 -> getr regs 2 = Z_to_bv 64 s ->
  (forall m' regs', W C A2 m' md2 -> cs_kept regs regs' -> POSTM C A s m m' -> getr regs' 10 = Z_to_bv 64 pixd ->
      pix_freshc C A A2 m' pixd (w + left + right) (h + top + bot) d cd data -> (forall a : word, K a -> m' a = m4 a) ->
      realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md2) S) ->
  realizes SEGS (mkCfg (mkst r6 (0x70fb0 : word) m4 al_rom) md2) S.
Proof.
  intros C A A2 m m4 md2 regs r6 K s pixs pixd data w h d cm cd datas spp rc fmt spc txt left right top bot val ret S CK Hs16 Hlo Hhi Hret HW4 PM4 HOK Hw Hh Hd Hd1 Hl32 Hl Hr Ht Hb Hal Hval HOKd PF HKK
         PXs4 Lps Lds FR4 W2 W8 W18 W22 W9 W19 W20 W21 W23 W24 W3 W4 K25 K26 W27 H2 HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  assert (Hs128 : (112 <= s)%Z) by (unfold ABG_STACK, O23LeptBase.LSF in Hlo; lia). assert (Hs64 : (s < 2 ^ 64)%Z) by lia.
  pose proof FR4 as (CE4 & Rw4 & Rh4 & Rd4).
  destruct (ab_C al_rom r6 m4 s d val Hs128 Hs64 Hd Hval Rd4 W2 W24) as (r7 & RUN7 & X24 & AG7).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW4)) | exact (mp_lazy _ (w_pure _ _ _ _ HW4)) | exact RUN7 |]. clear RUN7.
  apply (ab_fills_W C A A2 m m4 md2 regs r7 K s pixs pixd data w h d cm cd datas spp rc fmt spc txt left right top bot (if Z.eq_dec val 0 then 0 else 15)%Z ret S
           CK Hs16 Hlo Hhi Hret HW4 PM4 HOK Hw Hh Hd Hd1 Hl32 Hl Hr Ht Hb Hal ltac:(destruct (Z.eq_dec val 0); [left | right]; reflexivity)
           HOKd PF HKK PXs4 Lps Lds FR4); try exact HK; try exact X24; try exact H2; csr; reflexivity.
Qed.

(* [comment removed for export] *)
Definition pixAddBorderGeneralC_contract : Prop :=
  forall C A m md regs (s pixs w h d cm datas spp rc fmt spc txt left right top bot val : Z) (cv : cmapv) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + ABG_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x1381d0 ->
  getr regs 10 = Z_to_bv 64 pixs -> getr regs 11 = Z_to_bv 64 left -> getr regs 12 = Z_to_bv 64 right ->
  getr regs 13 = Z_to_bv 64 top -> getr regs 14 = Z_to_bv 64 bot -> getr regs 15 = Z_to_bv 64 val ->
  PIXat m pixs (hdvgc w h d cm datas spp rc fmt spc txt) -> hdr_ok w h d -> (1 <= w)%Z -> (1 <= h)%Z -> (d = 1 \/ d = 8)%Z -> d = 1%Z ->
  (left mod 32 = 0)%Z ->
  live A (Z_to_bv 64 pixs) = Some 64%Z -> live A (Z_to_bv 64 datas) = Some (4 * (wpl_of w d * h))%Z ->
  (cm = 0%Z \/ (CMAPat m cm cv /\ cmap_ok cv /\ live A (Z_to_bv 64 cm) = Some 24%Z /\ live A (Z_to_bv 64 (c_arr cv)) = Some (4 * c_nalloc cv)%Z)) ->
  (1 <= left <= 64)%Z -> (1 <= right <= 64)%Z -> (1 <= top <= 64)%Z -> (1 <= bot <= 64)%Z ->
  rop2_arm (left * d)%Z (0 * d)%Z (w * d)%Z (wpl_of w d) ->
  (val = 0 \/ val = 2 ^ d - 1)%Z -> ((w + left + right) * (h + top + bot) <= 400000000)%Z ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_pixcopy <= kR)%Z -> (RB_abg w h d left right top bot + RB_cmapT cm <= bR)%Z ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A s m m' ->
     ( (getr regs' 10 = Z_to_bv 64 0 /\ forall q, live A' q = live A q)
       \/ (exists pixd cd data, getr regs' 10 = Z_to_bv 64 pixd /\ hdr_ok (w + left + right) (h + top + bot) d /\
                             O23LeptPixCopyT.pixt_new C A A' m' pixd (w + left + right) (h + top + bot) d cd data cv) ) ->
     aroom A' vm' (kR - RK_pixcopy) (bR - (RB_abg w h d left right top bot + RB_cmapT cm)) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (Z_to_bv 64 PC_pixAddBorderGeneral) m al_rom) md) S.

Theorem pixAddBorderGeneralC_W : pixAddBorderGeneralC_contract.
Proof.
  unfold pixAddBorderGeneralC_contract.
  intros C A m md regs s pixs w h d cm datas spp rc fmt spc txt left right top bot val cv ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 H11 H12 H13 H14 H15
         PXs HOK Hw Hh Hd Hd1 Hl32 Lps Lds HCM Hl Hr Ht Hb Hal Hval Hprod kR bR Hrm Hrk Hrb HK.
  replace (Z_to_bv 64 PC_pixAddBorderGeneral) with (0x70ed8 : word) by (apply bv_eq; reflexivity).
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold ABG_STACK, O23LeptBase.LSF, LSF, RB_abg in *.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof HOK as (DV & Hw2 & Hh2 & Hsz). pose proof (wpl_of_range w d ltac:(lia) DV) as Hwpl.
  pose proof PXs as (Hs0 & Hs64' & WFs & _).
  pose proof (RB_cmapT_le cm) as RBc.
  destruct (blk_range C A m md (Z_to_bv 64 pixs) 64 CK HW Lps ltac:(lia)) as [Gps TOPps]. rewrite u_Z2bv in Gps, TOPps by lia.
  set (wd := (w + left + right)%Z) in *. set (hd := (h + top + bot)%Z) in *.
  assert (ALps8 : (pixs mod 8 = 0)%Z) by (pose proof (ai_live_hull A m _ _ _ (w_inv _ _ _ _ HW) Lps) as (_ & X16 & _); rewrite u_Z2bv in X16 by lia; apply mod16_mod8; exact X16).
  destruct (ab_A al_rom regs m s pixs left right top bot val (hdvgc w h d cm datas spp rc fmt spc txt) ret ltac:(lia) ltac:(lia) Hs16 ltac:(lia) ALps8 PXs ltac:(lia)
              ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia)
              (W_sok_win C A m md (s - 112) 112 CK HW ltac:(lia) ltac:(cbn; lia)) H2 H1 H10 H11 H12 H13 H14 H15)
    as (r1 & RUN1 & Q2 & Q1 & Q10 & Q11 & Q12 & Q8 & Q18 & Q22 & Q9 & Q19 & Q24 & Q21 & Q23 & AG1).
  cbn [p_w p_h p_d hdvgc] in RUN1, Q10, Q11, Q12, Q21, Q23. fold wd in Q10, Q21. fold hd in Q11, Q23.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |]. clear RUN1.
  set (M1 := DIMS (FRA m s ret regs) (s - 84) w h d) in *.
  assert (WP1 : W C A M1 md /\ POSTM C A s m M1) by (subst M1; unfold DIMS, FRA; wp_win CK).
  destruct WP1 as [HW1 PM1].
  pose proof (abfr_init m s ret regs w h d ltac:(lia) ltac:(lia)) as FR1. fold M1 in FR1.
  assert (OUT1 : forall x : word, ~ (s - 112 <= u x < s)%Z -> M1 x = m x).
  { intros x Hx. subst M1. rewrite DIMS_out by lia. apply FRA_out; lia. }
  assert (Q4 : getr r1 4 = Z_to_bv 64 0x1381d0) by (csr; reflexivity).
  apply (pixCreate_szT2_W C A M1 md r1 (s - 112) wd hd d (Z_to_bv 64 0x70f94) S CK HW1 Q2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(unfold LSF; lia) ltac:(lia) Q1 ltac:(red; apply bv_eq; reflexivity) Q4 Q10 Q11 Q12 ltac:(subst wd; lia) ltac:(subst hd; lia) Hprod
           ltac:(destruct Hd; lia)).
  intros A1 m1 vm1 r2 HWa CSa PMa OUTa HRTa.
  replace (Z_to_bv 64 0x70f94) with (0x70f94 : word) by (apply bv_eq; reflexivity).
  assert (PMa' : POSTM C A s m m1) by (eapply POSTM_trans; [exact PM1 | eapply POSTM_mono; [|exact PMa]; lia]).
  pose proof (abfr_frm C (s - 112) M1 m1 s ret regs w h d CK (proj1 PMa) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) FR1) as FR2.
  destruct OUTa as [[Hres0 LIVEQ] | (pixd & data & Hres & HOKd & PN)].
  - destruct (ab_F al_rom r2 m1 (W_sev_got C A1 m1 _ HWa) (W_sev C A1 m1 _ HWa) Hres0) as (r3 & RUN3 & V1 & V10 & V11 & V12 & AG3).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWa)) | exact (mp_lazy _ (w_pure _ _ _ _ HWa)) | exact RUN3 |]. clear RUN3.
    apply (returnErrorPtr_W C A1 m1 _ r3 (s - 112) 0x126da 0x17116 13 19 (Z_to_bv 64 0x71084) (Z_to_bv 64 0) S CK HWa ltac:(csr; reflexivity)
             ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold LSF; lia) ltac:(lia) V1 ltac:(red; apply bv_eq; reflexivity)
             V10 V11 V12 str_msg_pixd str_pixAddBorderGeneral).
    intros m4 r5 HW4 OUT4 GR4 CS4 A10. unfold LSF in OUT4.
    replace (Z_to_bv 64 0x71084) with (0x71084 : word) by (apply bv_eq; reflexivity).
    destruct (ab_F2 al_rom r5 m4 0 A10) as (r6 & RUN6 & X20 & AG6).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW4)) | exact (mp_lazy _ (w_pure _ _ _ _ HW4)) | exact RUN6 |]. clear RUN6.
    pose proof (abfr_out m1 m4 _ _ s ret regs w h d OUT4 ltac:(lia) ltac:(lia) ltac:(lia) FR2) as (CE4 & _).
    destruct (ab_E al_rom r6 regs m4 s 0 ret ltac:(lia) ltac:(lia) Hret CE4 ltac:(csr; reflexivity) X20) as (r7 & RUN7 & Z2 & Z1 & Z10 & ZR & AG7).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW4)) | exact (mp_lazy _ (w_pure _ _ _ _ HW4)) | exact RUN7 |]. clear RUN7.
    apply (HK A1 m4 vm1 r7 HW4).
    + apply cs_kept_intro; first [solve [apply ZR; in_lit] | (csr; reflexivity)].
    + eapply POSTM_trans; [exact PMa'|]. apply (POSTM_sub C A A1); [apply sub_live_eq; exact LIVEQ|].
      eapply (POSTM_range C A1 m1 _ m4); [exact CK | exact HWa | exact OUT4 | lia | lia | lia].
    + left. split; [exact Z10 | exact LIVEQ].
    + room_tac.
  - destruct PN as (Gp & TOPp & ALp & Gd & TOPd & ALd & NEpd & L0p & L0d & L00p & L00d & L1p & L1d & LEQ & PXd & _).
    change (data + 4 * (wpl_of wd d * hd) <= alloc_top (c_vm C))%Z in TOPd. change (live A1 (Z_to_bv 64 data) = Some (4 * (wpl_of wd d * hd))%Z) in L1d.
    change (PIXat m1 pixd (hdv wd hd d 0 data)) in PXd.
    pose proof HOKd as (_ & Hwd2 & Hhd2 & Hszd). pose proof (wpl_of_range wd d ltac:(subst wd; lia) DV) as Hwpld.
    assert (Hnd : (0 <= wpl_of wd d * hd)%Z) by (apply Z.mul_nonneg_nonneg; subst hd; lia).
    assert (NEsp : Z_to_bv 64 pixs <> Z_to_bv 64 pixd) by (intros E; rewrite E in Lps; rewrite Lps in L0p; discriminate).
    assert (NEsd : Z_to_bv 64 pixs <> Z_to_bv 64 data) by (intros E; rewrite E in Lps; rewrite Lps in L0d; discriminate).
    assert (NEdd : Z_to_bv 64 datas <> Z_to_bv 64 data) by (intros E; rewrite E in Lds; rewrite Lds in L0d; discriminate).
    assert (NEpdw : Z_to_bv 64 pixd <> Z_to_bv 64 data) by (apply zbv_ne2; lia).
    assert (SUBa : sub_live A A1) by (eapply sub_live_new2; [exact L0p | exact L0d | exact L1p | exact L1d | exact LEQ]).
    pose proof (SUBa _ _ Lps) as Lps1. pose proof (SUBa _ _ Lds) as Lds1.
    pose proof (blk_apart C A1 m1 _ _ _ _ _ CK HWa Lps1 L1p NEsp ltac:(lia) ltac:(lia)) as APsp. rewrite !u_Z2bv in APsp by lia.
    assert (PXs1 : PIXat m1 pixs (hdvgc w h d cm datas spp rc fmt spc txt)).
    { apply (PIXat_frame m); [exact PXs|]. intros x Hx. rewrite (LIVK_at A M1 m1 pixs 64 x (proj2 PMa) Lps ltac:(lia) ltac:(lia) Hx). apply OUT1. lia. }
    assert (HCM1 : cm = 0%Z \/ (CMAPat m1 cm cv /\ cmap_ok cv /\ live A1 (Z_to_bv 64 cm) = Some 24%Z /\ live A1 (Z_to_bv 64 (c_arr cv)) = Some (4 * c_nalloc cv)%Z)).
    { destruct HCM as [CM0 | (CM & CMOK & Lcm & Larr)]; [left; exact CM0 | right].
      pose proof CM as (Hc0 & Hc64 & _). destruct (blk_range C A m md (Z_to_bv 64 cm) 24 CK HW Lcm ltac:(lia)) as [Gcm TOPcm]. rewrite u_Z2bv in Gcm, TOPcm by lia.
      split; [| split; [exact CMOK | split; [exact (SUBa _ _ Lcm) | exact (SUBa _ _ Larr)]]].
      apply (CMAPat_frame m); [exact CM|]. intros x Hx. rewrite (LIVK_at A M1 m1 cm 24 x (proj2 PMa) Lcm ltac:(lia) ltac:(lia) Hx). apply OUT1. lia. }
    destruct (ab_B1 al_rom r2 m1 pixd pixs ltac:(lia) Hres ltac:(csr; reflexivity)) as (r3 & RUN3 & V1 & V10 & V11 & V20 & AG3).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWa)) | exact (mp_lazy _ (w_pure _ _ _ _ HWa)) | exact RUN3 |]. clear RUN3.
    destruct (pixCopyResolution_run al_rom r3 m1 pixd pixs (hdvgc w h d cm datas spp rc fmt spc txt) (hdv wd hd d 0 data) (Z_to_bv 64 0x70fa4) ltac:(lia) ltac:(lia)
                ltac:(intros E; apply NEsp; rewrite E; reflexivity) ALps8 (mod16_mod8 _ ALp) PXs1 PXd eq_refl eq_refl
                (blk_sok C A1 m1 _ pixd 64 CK HWa L1p ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(red; apply bv_eq; reflexivity) V1 V10 V11)
      as (r4 & RUN4 & X10 & AG4).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWa)) | exact (mp_lazy _ (w_pure _ _ _ _ HWa)) | exact RUN4 |]. clear RUN4.
    replace (Z_to_bv 64 0x70fa4) with (0x70fa4 : word) by (apply bv_eq; reflexivity).
    set (M3 := wbytes m1 (Z_to_bv 64 (pixd + 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))).
    assert (WP3 : W C A1 M3 (with_vmmaps vm1 md) /\ POSTM C A s m M3).
    { subst M3. apply (WP_blk C A A1 m _ _ (Z_to_bv 64 pixd) _ 64); [exact CK | | exact L1p | exact L0p | exact L00p | exact SUBa | rewrite !u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia].
      split; [exact HWa | exact PMa']. }
    destruct WP3 as [HW3 PM3].
    assert (OUT3 : forall x : word, ~ (pixd + 24 <= u x < pixd + 32)%Z -> M3 x = m1 x).
    { intros x Hx. subst M3. apply (wbytes_out_Z _ _ 8); [rewrite length_N_to_le_bytes; reflexivity | lia | lia | lia]. }
    assert (PXd3 : PIXat M3 pixd (hdv wd hd d 0 data)) by (subst M3; apply (O23LeptPixCopy.PIX_wr_res0 _ pixd (hdv wd hd d 0 data)); [exact PXd | reflexivity | reflexivity]).
    assert (PXs3 : PIXat M3 pixs (hdvgc w h d cm datas spp rc fmt spc txt)) by (apply (PIXat_frame m1); [exact PXs1 | intros x Hx; apply OUT3; lia]).
    pose proof (abfr_out m1 M3 _ _ s ret regs w h d OUT3 ltac:(lia) ltac:(lia) ltac:(lia) FR2) as FR3.
    assert (HCM3 : cm = 0%Z \/ (CMAPat M3 cm cv /\ cmap_ok cv /\ live A1 (Z_to_bv 64 cm) = Some 24%Z /\ live A1 (Z_to_bv 64 (c_arr cv)) = Some (4 * c_nalloc cv)%Z)).
    { destruct HCM1 as [CM0 | (CM & CMOK & Lcm & Larr)]; [left; exact CM0 | right].
      pose proof CM as (Hc0 & Hc64 & _).
      assert (NEcp : Z_to_bv 64 cm <> Z_to_bv 64 pixd) by (intros E; rewrite E in Lcm; congruence).
      pose proof (blk_apart C A1 m1 _ _ _ _ _ CK HWa Lcm L1p NEcp ltac:(lia) ltac:(lia)) as APcp. rewrite !u_Z2bv in APcp by lia.
      split; [| split; [exact CMOK | split; [exact Lcm | exact Larr]]].
      apply (CMAPat_frame m1); [exact CM|]. intros x Hx. apply OUT3. lia. }
    destruct (ab_B2 al_rom r4 M3 pixd pixs ltac:(csr; reflexivity) ltac:(csr; reflexivity)) as (r5 & RUN5 & Y1 & Y10 & Y11 & AG5).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW3)) | exact (mp_lazy _ (w_pure _ _ _ _ HW3)) | exact RUN5 |]. clear RUN5.
    apply (pixCopyColormap_szT_W C A A1 M3 _ r5 (s - 112) pixd pixs (hdv wd hd d 0 data) (hdvgc w h d cm datas spp rc fmt spc txt) cv (Z_to_bv 64 0x70fb0) S CK HW3 SUBa
             ltac:(csr; reflexivity) ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold LSF; lia) ltac:(lia) Y1 ltac:(red; apply bv_eq; reflexivity)
             ltac:(csr; reflexivity) Y10 Y11 PXd3 PXs3 eq_refl eq_refl ltac:(intros E; apply NEsp; rewrite E; reflexivity) L1p L0p L00p Lps1 HCM3
             (kR - RK_pix) (bR - RB_pixT (4 * (wpl_of wd d * hd))) ltac:(room_tac) ltac:(room_consts; lia) ltac:(cbn [p_cmap hdvgc]; lia)).
    intros A2 m5 vm2 r6 HWb CSb PMb OUTb Hrm2. rewrite with_vmmaps_twice in HWb |- *.
    replace (Z_to_bv 64 0x70fb0) with (0x70fb0 : word) by (apply bv_eq; reflexivity).
    cbn [p_cmap hdvgc] in Hrm2.
    assert (OUTc : exists cd, PIXat m5 pixd (hdv wd hd d cd data) /\ sub_live A1 A2 /\ O23LeptPixCopyT.cmres C A A2 m5 pixd data cd cv).
    { destruct OUTb as [[LIVEQ2 PXd5] | (cd & ad & CC & PXd5)].
      - exists 0%Z. split; [exact PXd5|]. split; [apply sub_live_eq; exact LIVEQ2|].
        left. split; [reflexivity|]. intros q N1 N2. rewrite LIVEQ2. apply LEQ; assumption.
      - exists cd. destruct CC as (CMOK & Gcd & TOPcd & ALcd & Gad & TOPad & ALad & NEcdad & L1cd & L1ad & L00cd & L00ad & L2cd & L2ad & LEQ2 & CM5).
        assert (NWcp : Z_to_bv 64 cd <> Z_to_bv 64 pixd) by (intros E; rewrite E in L1cd; congruence).
        assert (NWcd : Z_to_bv 64 cd <> Z_to_bv 64 data) by (intros E; rewrite E in L1cd; congruence).
        assert (NWap : Z_to_bv 64 ad <> Z_to_bv 64 pixd) by (intros E; rewrite E in L1ad; congruence).
        assert (NWad : Z_to_bv 64 ad <> Z_to_bv 64 data) by (intros E; rewrite E in L1ad; congruence).
        split; [exact PXd5|]. split; [exact (sub_live_new2 A1 A2 _ _ _ _ L1cd L1ad L2cd L2ad LEQ2)|].
        right. exists ad.
        split; [exact CMOK|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact NEcdad|].
        split; [intros E; apply NWcp; rewrite E; reflexivity|]. split; [intros E; apply NWcd; rewrite E; reflexivity|].
        split; [intros E; apply NWap; rewrite E; reflexivity|]. split; [intros E; apply NWad; rewrite E; reflexivity|].
        split; [rewrite <- (LEQ _ NWcp NWcd); exact L1cd|]. split; [rewrite <- (LEQ _ NWap NWad); exact L1ad|].
        split; [exact L00cd|]. split; [exact L00ad|]. split; [exact L2cd|]. split; [exact L2ad|]. split; [exact CM5|].
        intros q N1 N2 N3 N4. rewrite (LEQ2 q N3 N4). apply LEQ; assumption. }
    destruct OUTc as (cd & PXd5 & SUB12 & CMR5).
    assert (SUBb : sub_live A A2) by (eapply sub_live_trans; [exact SUBa | exact SUB12]).
    assert (L2p : live A2 (Z_to_bv 64 pixd) = Some 64%Z) by (exact (SUB12 _ _ L1p)).
    assert (L2d : live A2 (Z_to_bv 64 data) = Some (4 * (wpl_of wd d * hd))%Z) by (exact (SUB12 _ _ L1d)).
    assert (PMb' : POSTM C A s m m5) by (eapply POSTM_trans; [exact PM3 | eapply POSTM_mono; [|exact PMb]; lia]).
    pose proof (abfr_frm C (s - 112) M3 m5 s ret regs w h d CK (proj1 PMb) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) FR3) as FR5.
    assert (PXs5 : PIXat m5 pixs (hdvgc w h d cm datas spp rc fmt spc txt)).
    { apply (PIXat_frame M3); [exact PXs3|]. intros x Hx. exact (LIVK_at A M3 m5 pixs 64 x (proj2 PMb) Lps ltac:(lia) ltac:(lia) Hx). }
    assert (PF5 : pix_freshc C A A2 m5 pixd wd hd d cd data).
    { unfold pix_freshc. do 14 (split; [assumption|]). exact PXd5. }
    assert (HKK : forall a : word, (cd <= u a < cd + 24)%Z -> ~ scratch C s a /\ ~ (data <= u a < data + 4 * (wpl_of wd d * hd))%Z).
    { intros a Ka. unfold scratch.
      destruct CMR5 as [(CD0 & _) | (ad & CMOK & Gcd & TOPcd & Gad & TOPad & N1 & N2 & N3 & N4 & N5 & L0cd & L0ad & L00cd & L00ad & L2cd & L2ad & CM5 & LEQ5)].
      - rewrite CD0 in Ka. split; lia.
      - assert (NWcd : Z_to_bv 64 cd <> Z_to_bv 64 data) by (apply zbv_ne2; lia).
        pose proof (blk_apart C A2 m5 _ _ _ _ _ CK HWb L2cd L2d NWcd ltac:(lia) ltac:(lia)) as APcd. rewrite !u_Z2bv in APcd by lia.
        split; lia. }
    apply (ab_tailC_W C A A2 m m5 _ regs r6 (fun a : word => (cd <= u a < cd + 24)%Z) s pixs pixd data w h d cm cd datas spp rc fmt spc txt left right top bot val ret S
             CK Hs16 ltac:(unfold ABG_STACK, O23LeptBase.LSF; lia) Hhi Hret HWb PMb' HOK Hw Hh Hd Hd1 Hl32 Hl Hr Ht Hb Hal Hval HOKd PF5 HKK PXs5 Lps Lds FR5);
      try exact H2; [csr; reflexivity .. |].
    intros m' regs' X1 X2 X3 X4 X5 X6.
    apply (HK A2 m' vm2 regs' X1 X2 X3).
    + right. exists pixd, cd, data. split; [exact X4|]. split; [exact HOKd|].
      destruct X5 as (Gp' & TOPp' & ALp' & Gd' & TOPd' & ALd' & NEpd' & L0p' & L0d' & L00p' & L00d' & L2p' & L2d' & LEQ' & PXd').
      unfold O23LeptPixCopyT.pixt_new. do 13 (split; [assumption|]). split; [exact PXd'|].
      destruct CMR5 as [CL0 | (ad & CMOK & Gcd & TOPcd & Gad & TOPad & N1 & N2 & N3 & N4 & N5 & L0cd & L0ad & L00cd & L00ad & L2cd & L2ad & CM5 & LEQ5)];
        [left; exact CL0 | right].
      exists ad. do 16 (split; [assumption|]). split; [| exact LEQ5].
      apply (CMAPat_frame m5); [exact CM5|]. intros x Hx. apply X6. exact Hx.
    + room_tac.
Qed.



End WithRop.

End GrayBorderW.
