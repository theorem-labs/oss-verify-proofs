(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.fhmtgen_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptArith2 GrayACELib.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require Import V10LeptStderr V10LeptBase V10LeptUb.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require Import V10CL7a.
Import V10CL7a.V10LeptErr. Import V10CL7a.V10LeptRop_iface.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require Import V10CL8a.
Import V10CL8a.V10LeptPixHdr.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require Import V10LeptPixCreate V10LeptCmapValid V10LeptCmap2 V10LeptPixCopyA V10LeptPixCopy V10LeptPixT V10LeptPixCopyT V10LeptGrayA V10LeptGrayBorder.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require Import LeptRoom LeptRoomPC LeptRoom14 LeptRoom10.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require LiaFast.   (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= first [ solve [LiaFast.flia2] | Zify.zify; xlia zchecker ].
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Section GrayBorderW.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V10Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Section WithRop.
Hypothesis ROPU : pixRasterop_uni_contract.
Hypothesis ROPS : pixRasterop_src_contract.

(* [comment removed for export] *)
Lemma border_t1 : forall w h d, (1 <= w <= 20128)%Z -> (1 <= h <= 20128)%Z -> (d = 1 \/ d = 8)%Z -> (4 * (wpl_of w d * h) < 2 ^ 31)%Z.
Proof.
  intros w h d Hw Hh Hd. unfold wpl_of.
  assert (X : (0 <= (w * d + 31) / 32 <= 5032)%Z).
  { split; [apply Z.div_pos; destruct Hd as [-> | ->]; lia | enough ((w * d + 31) / 32 < 5033)%Z by lia; apply Z.div_lt_upper_bound; destruct Hd as [-> | ->]; lia]. }
  clear Hd. nia.
Qed.

(* [comment removed for export] *)
Lemma cmres_build : forall C A A1 A2 m4 md4 (s pixd data nb : Z) (vd : pixv) (cv : cmapv),
  Cok C -> W C A2 m4 md4 -> (s <= c_top C)%Z -> (c_top C - LSTK <= s)%Z ->
  (4096 <= pixd)%Z -> (4096 <= data)%Z -> (0 <= nb)%Z -> (data + nb <= alloc_top (c_vm C))%Z ->
  live A (Z_to_bv 64 pixd) = None -> live A (Z_to_bv 64 data) = None ->
  live A1 (Z_to_bv 64 pixd) = Some 64%Z -> live A1 (Z_to_bv 64 data) = Some nb ->
  (forall q, q <> Z_to_bv 64 pixd -> q <> Z_to_bv 64 data -> live A1 q = live A q) -> p_cmap vd = 0%Z ->
  ( ((forall q, live A2 q = live A1 q) /\ PIXat m4 pixd vd)
    \/ (exists cd ad : Z, cmap_copy C A1 A2 m4 cd ad cv /\ PIXat m4 pixd (set_cmap vd cd)) ) ->
  exists cd, PIXat m4 pixd (set_cmap vd cd) /\ sub_live A1 A2 /\
    live A2 (Z_to_bv 64 pixd) = Some 64%Z /\ live A2 (Z_to_bv 64 data) = Some nb /\
    (forall m' : word -> option byte, (forall a : word, ~ scratch C s a -> ~ (data <= u a < data + nb)%Z -> m' a = m4 a) -> cmres C A A2 m' pixd data cd cv).
Proof.
  intros C A A1 A2 m4 md4 s pixd data nb vd cv CK HW4 Hhi Hlo Gp Gd Hnb TOPd L0p L0d L1p L1d LEQ Ecm OUTb.
  pose proof CK as [T1 T2 T3 T4 T5]. pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  destruct OUTb as [[LIVEQ2 PXd4] | (cd & ad & CC & PXd4)].
  - exists 0%Z. split; [destruct vd; cbn [set_cmap LeptStructs.p_cmap] in *; subst; exact PXd4|]. split; [apply sub_live_eq; exact LIVEQ2|].
    split; [rewrite LIVEQ2; exact L1p|]. split; [rewrite LIVEQ2; exact L1d|].
    intros m' _. left. split; [reflexivity|]. intros q N1 N2. rewrite LIVEQ2. apply LEQ; assumption.
  - pose proof CC as (CMOKc & Gcd & TOPcd & ALcd & Gad & TOPad & ALad & NEcdad & LA1cd & LA1ad & L00cd & L00ad & L2cd & L2ad & LEQ2 & CM4).
    assert (NEcdp : Z_to_bv 64 cd <> Z_to_bv 64 pixd) by (intros E; rewrite E in LA1cd; rewrite L1p in LA1cd; discriminate).
    assert (NEadp : Z_to_bv 64 ad <> Z_to_bv 64 pixd) by (intros E; rewrite E in LA1ad; rewrite L1p in LA1ad; discriminate).
    assert (NEcdd : Z_to_bv 64 cd <> Z_to_bv 64 data) by (intros E; rewrite E in LA1cd; rewrite L1d in LA1cd; discriminate).
    assert (NEadd : Z_to_bv 64 ad <> Z_to_bv 64 data) by (intros E; rewrite E in LA1ad; rewrite L1d in LA1ad; discriminate).
    assert (SUBb : sub_live A1 A2) by (eapply sub_live_new2; [exact LA1cd | exact LA1ad | exact L2cd | exact L2ad | exact LEQ2]).
    exists cd. split; [exact PXd4|]. split; [exact SUBb|]. split; [exact (SUBb _ _ L1p)|]. split; [exact (SUBb _ _ L1d)|].
    intros m' FP. right. exists ad.
    split; [exact CMOKc|]. split; [exact Gcd|]. split; [exact TOPcd|]. split; [exact Gad|]. split; [exact TOPad|]. split; [exact NEcdad|].
    split; [intros E; apply NEcdp; rewrite E; reflexivity|]. split; [intros E; apply NEcdd; rewrite E; reflexivity|].
    split; [intros E; apply NEadp; rewrite E; reflexivity|]. split; [intros E; apply NEadd; rewrite E; reflexivity|].
    split; [rewrite <- (LEQ _ NEcdp NEcdd); exact LA1cd|]. split; [rewrite <- (LEQ _ NEadp NEadd); exact LA1ad|].
    split; [exact L00cd|]. split; [exact L00ad|]. split; [exact L2cd|]. split; [exact L2ad|]. split.
    + apply (CMAPat_frame m4); [exact CM4|]. intros x Hx. apply FP.
      * unfold scratch. lia.
      * pose proof (blk_apart C A2 m4 _ _ _ _ _ CK HW4 L2cd (SUBb _ _ L1d) NEcdd ltac:(lia) ltac:(lia)) as D. rewrite !u_Z2bv in D by lia. lia.
    + intros q N1 N2 N3 N4. rewrite (LEQ2 q N3 N4). apply LEQ; assumption.
Qed.

Lemma hdr_rop_shape : forall w h d, hdr_ok w h d -> (1 <= w)%Z -> (1 <= h)%Z -> (d = 1 \/ d = 8)%Z -> rop_shape w h d (wpl_of w d).
Proof. intros w h d (DV & Hw & Hh & Hsz) Hw1 Hh1 Hd. unfold rop_shape. repeat split; try assumption; lia. Qed.

(* [comment removed for export] *)
Lemma ab_uni_W : forall C A A2 M md regs (s' pixd data wd hd d cd x y rw rh op : Z) (ret : word) (S : TSet),
  Cok C -> W C A2 M md -> sub_live A A2 ->
  getr regs 2 = Z_to_bv 64 s' -> (s' mod 16 = 0)%Z -> (c_top C - LSTK + ROP_STACK <= s')%Z -> (s' + 8 <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret ->
  getr regs 10 = Z_to_bv 64 pixd -> getr regs 11 = Z_to_bv 64 x -> getr regs 12 = Z_to_bv 64 y -> getr regs 13 = Z_to_bv 64 rw ->
  getr regs 14 = Z_to_bv 64 rh -> getr regs 15 = Z_to_bv 64 op ->
  rdn SEGS M (Z_to_bv 64 s') 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  PIXat M pixd (hdv wd hd d cd data) -> hdr_ok wd hd d -> (1 <= wd)%Z -> (1 <= hd)%Z -> (d = 1 \/ d = 8)%Z ->
  rop_rect wd hd x y rw rh -> (op = 0 \/ op = 15)%Z ->
  live A2 (Z_to_bv 64 pixd) = Some 64%Z -> Z_to_bv 64 pixd <> Z_to_bv 64 data ->
  live A2 (Z_to_bv 64 data) = Some (4 * (wpl_of wd d * hd))%Z -> live A (Z_to_bv 64 data) = None -> live (c_A0 C) (Z_to_bv 64 data) = None ->
  (forall m' regs', W C A2 m' md -> cs_kept regs regs' -> POSTM C A s' M m' -> PIXat m' pixd (hdv wd hd d cd data) ->
      (forall a : word, ~ scratch C s' a -> ~ (data <= u a < data + 4 * (wpl_of wd d * hd))%Z -> m' a = M a) ->
      getr regs' 10 = Z_to_bv 64 0 ->
      realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst regs (0x1e488 : word) M al_rom) md) S.
Proof.
  intros C A A2 M md regs s' pixd data wd hd d cd x y rw rh op ret S CK HW SUB H2 Hs16 Hlo Hhi H1 Hret H10 H11 H12 H13 H14 H15 Rsy PX HOK Hw Hh Hd RECT Hop Lp NEpd Ld Ld0 Ld00 HK.
  replace (0x1e488 : word) with (Z_to_bv 64 PC_pixRasterop) by (apply bv_eq; reflexivity).
  exact (ROPU C A A2 M md regs s' pixd x y rw rh op (hdv wd hd d cd data) (Z_to_bv 64 0) ret S CK HW SUB H2 Hs16 Hlo Hhi H1 Hret H10 H11 H12 H13 H14 H15 Rsy
           PX (hdr_rop_shape wd hd d HOK Hw Hh Hd) RECT Hop Lp NEpd Ld Ld0 Ld00 HK).
Qed.

(* [comment removed for export] *)
Lemma ab_fills_W : forall C A A2 m m4 md2 regs r7 (s pixs pixd data w h d cm datas cd left right top bot op : Z) (ret : word) (S : TSet),
  Cok C -> (s mod 16 = 0)%Z -> (c_top C - LSTK + ABG_STACK <= s)%Z -> (s <= c_top C)%Z -> ret_ok ret ->
  W C A2 m4 md2 -> POSTM C A s m m4 ->
  hdr_ok w h d -> (1 <= w)%Z -> (1 <= h)%Z -> (d = 1 \/ d = 8)%Z ->
  (1 <= left <= 64)%Z -> (1 <= right <= 64)%Z -> (1 <= top <= 64)%Z -> (1 <= bot <= 64)%Z -> ((left * d) mod 32 = 0)%Z -> (op = 0 \/ op = 15)%Z ->
  hdr_ok (w + left + right) (h + top + bot) d -> sub_live A A2 ->
  (4096 <= pixd)%Z -> (pixd + 64 <= alloc_top (c_vm C))%Z -> (pixd mod 16 = 0)%Z ->
  (4096 <= data)%Z -> (data + 4 * (wpl_of (w + left + right) d * (h + top + bot)) <= alloc_top (c_vm C))%Z -> (data mod 16 = 0)%Z -> pixd <> data ->
  live A (Z_to_bv 64 pixd) = None -> live A (Z_to_bv 64 data) = None -> live (c_A0 C) (Z_to_bv 64 pixd) = None -> live (c_A0 C) (Z_to_bv 64 data) = None ->
  live A2 (Z_to_bv 64 pixd) = Some 64%Z -> live A2 (Z_to_bv 64 data) = Some (4 * (wpl_of (w + left + right) d * (h + top + bot)))%Z ->
  PIXat m4 pixd (hdv (w + left + right) (h + top + bot) d cd data) ->
  PIXat m4 pixs (hdv w h d cm datas) -> live A (Z_to_bv 64 pixs) = Some 64%Z -> live A (Z_to_bv 64 datas) = Some (4 * (wpl_of w d * h))%Z ->
  abfr m4 s ret regs w h d ->
  getr r7 2 = Z_to_bv 64 (s - 112) -> getr r7 8 = Z_to_bv 64 pixs -> getr r7 18 = Z_to_bv 64 left -> getr r7 22 = Z_to_bv 64 right ->
  getr r7 9 = Z_to_bv 64 top -> getr r7 19 = Z_to_bv 64 bot -> getr r7 20 = Z_to_bv 64 pixd ->
  getr r7 21 = Z_to_bv 64 (w + left + right) -> getr r7 23 = Z_to_bv 64 (h + top + bot) ->
  getr r7 24 = Z_to_bv 64 op -> getr r7 3 = getr regs 3 -> getr r7 4 = getr regs 4 -> getr r7 25 = getr regs 25 -> getr r7 26 = getr regs 26 ->
  getr r7 27 = getr regs 27 -> getr regs 2 = Z_to_bv 64 s ->
  (forall m' regs', W C A2 m' md2 -> cs_kept regs regs' -> POSTM C A s m m' -> getr regs' 10 = Z_to_bv 64 pixd ->
      PIXat m' pixd (hdv (w + left + right) (h + top + bot) d cd data) ->
      (forall a : word, ~ scratch C s a -> ~ (data <= u a < data + 4 * (wpl_of (w + left + right) d * (h + top + bot)))%Z -> m' a = m4 a) ->
      realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md2) S) ->
  realizes SEGS (mkCfg (mkst r7 (0x1819c : word) m4 al_rom) md2) S.
Proof.
  intros C A A2 m m4 md2 regs r7 s pixs pixd data w h d cm datas cd left right top bot op ret S CK Hs16 Hlo Hhi Hret HW4 PM4 HOK Hw Hh Hd Hl Hr Ht Hb Hal Hop HOKd SUBb Gp TOPp ALp Gd TOPd ALd NEpd L0p L0d L00p L00d L2p L2d PXd4
         PXs4 Lps Lds FR4 W2 W8 W18 W21 W9 W20 W19 W22 W25 W26 W3 W4 K25 K26 W27 H2 HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold ABG_STACK, LSF in *.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof HOK as (DV & Hw2 & Hh2 & Hsz). pose proof (wpl_of_range w d ltac:(lia) DV) as Hwpl.
  pose proof PXs4 as (Hs0 & Hs64' & WFs & _).
  set (wd := (w + left + right)%Z) in *. set (hd := (h + top + bot)%Z) in *.
  pose proof HOKd as (_ & Hwd2 & Hhd2 & Hszd). pose proof (wpl_of_range wd d ltac:(subst wd; lia) DV) as Hwpld.
  assert (Hnd : (0 <= wpl_of wd d * hd)%Z) by (apply Z.mul_nonneg_nonneg; subst hd; lia).
  assert (FP7 : forall a : word, ~ scratch C s a -> ~ (data <= u a < data + 4 * (wpl_of wd d * hd))%Z -> m4 a = m4 a) by (intros; reflexivity).
  destruct (blk_range C A2 m4 _ (Z_to_bv 64 pixs) 64 CK HW4 (SUBb _ _ Lps) ltac:(lia)) as [Gps TOPps]. rewrite u_Z2bv in Gps, TOPps by lia.
  assert (NEsd : Z_to_bv 64 pixs <> Z_to_bv 64 data) by (intros E; rewrite E in Lps; rewrite Lps in L0d; discriminate).
  assert (NEdd : Z_to_bv 64 datas <> Z_to_bv 64 data) by (intros E; rewrite E in Lds; rewrite Lds in L0d; discriminate).
  assert (NEpdw : Z_to_bv 64 pixd <> Z_to_bv 64 data) by (apply zbv_ne2; lia).
  assert (Hs128 : (112 <= s)%Z) by lia. assert (Hs64 : (s < 2 ^ 64)%Z) by lia.
  assert (Hs16' : ((s - 112) mod 16 = 0)%Z) by (rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity).
  assert (Hlo' : (c_top C - LSTK + ROP_STACK <= s - 112)%Z) by (unfold ROP_STACK; lia).
  assert (Hhi' : (s - 112 + 8 <= c_top C)%Z) by lia.
  assert (Hwd1 : (1 <= wd)%Z) by (subst wd; lia). assert (Hhd1 : (1 <= hd)%Z) by (subst hd; lia).
  (* [comment removed for export] *)
  destruct (ab_R1 al_rom r7 m4 s pixd left hd op ltac:(lia) ltac:(lia) (W_sok_win C A2 m4 _ (s - 112) 8 CK HW4 ltac:(lia) ltac:(cbn; lia)) W2 W19 W18 W25 W26)
    as (r8 & RUN8 & a1 & a10 & a11 & a12 & a13 & a14 & a15 & AG8).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW4)) | exact (mp_lazy _ (w_pure _ _ _ _ HW4)) | exact RUN8 |]. clear RUN8.
  set (N8 := wbytes m4 (Z_to_bv 64 (s - 112)) (word_to_le_bytes 8 (Z_to_bv 64 0))).
  assert (WP8 : W C A2 N8 md2 /\ POSTM C A s m N8) by (subst N8; wp_win CK).
  destruct WP8 as [HW8 PM8].
  assert (OUT8 : forall x : word, ~ (s - 112 <= u x < s - 104)%Z -> N8 x = m4 x).
  { intros x Hx. subst N8. apply (wbytes_out_Z _ _ 8); [rewrite length_N_to_le_bytes; reflexivity | clear - Hs128 Hs64; lia | clear - Hs128 Hs64; lia | clear - Hs128 Hs64 Hx; lia]. }
  pose proof (abfr_out m4 N8 _ _ s ret regs w h d OUT8 ltac:(lia) ltac:(lia) ltac:(lia) FR4) as FR8.
  assert (PXd8 : PIXat N8 pixd (hdv wd hd d cd data)) by (apply (PIXat_frame m4); [exact PXd4 | intros x Hx; apply OUT8; lia]).
  assert (PXs8 : PIXat N8 pixs (hdv w h d cm datas)) by (apply (PIXat_frame m4); [exact PXs4 | intros x Hx; apply OUT8; lia]).
  apply (ab_uni_W C A A2 N8 _ r8 (s - 112) pixd data wd hd d cd 0 0 left hd op (Z_to_bv 64 0x181c4) S CK HW8 SUBb
           ltac:(csr; reflexivity) Hs16' Hlo' Hhi'
           a1 ltac:(red; apply bv_eq; reflexivity) a10 a11 a12 a13 a14 a15
           ltac:(subst N8; apply (rdn_wbytes_hit8 SEGS); rewrite u_Z2bv by lia; lia)
           PXd8 HOKd Hwd1 Hhd1 Hd ltac:(unfold rop_rect; subst wd hd; lia) Hop L2p NEpdw L2d L0d L00d).
  intros n8 q8 HV8 CS8 PN8 PXe8 FPe8 A10_8.
  assert (FP8 : forall a : word, ~ scratch C s a -> ~ (data <= u a < data + 4 * (wpl_of wd d * hd))%Z -> n8 a = m4 a).
  { intros a Ha1 Ha2. rewrite (FPe8 a ltac:(clear - Ha1; unfold scratch in *; lia) Ha2). rewrite (OUT8 a) by (clear - Ha1 Hlo Hhi; unfold scratch in Ha1; lia). exact (FP7 a Ha1 Ha2). }
  replace (Z_to_bv 64 0x181c4) with (0x181c4 : word) by (apply bv_eq; reflexivity).
  assert (PO8 : POSTM C A s m n8) by (eapply POSTM_trans; [exact PM8 | eapply POSTM_mono; [|exact PN8]; lia]).
  pose proof (abfr_frm C (s - 112) N8 n8 s ret regs w h d CK (proj1 PN8) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) FR8) as FS8.
  assert (PXt8 : PIXat n8 pixs (hdv w h d cm datas)).
  { apply (PIXat_frame N8); [exact PXs8|]. intros x Hx. exact (LIVK_at A N8 n8 pixs 64 x (proj2 PN8) Lps ltac:(lia) ltac:(lia) Hx). }
  (* [comment removed for export] *)
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
  assert (PXs9 : PIXat N9 pixs (hdv w h d cm datas)) by (apply (PIXat_frame n8); [exact PXt8 | intros x Hx; apply OUT9; lia]).
  apply (ab_uni_W C A A2 N9 _ r9 (s - 112) pixd data wd hd d cd (w + left) 0 right hd op (Z_to_bv 64 0x181f8) S CK HW9 SUBb
           ltac:(csr; reflexivity) Hs16' Hlo' Hhi'
           b1 ltac:(red; apply bv_eq; reflexivity) b10 ltac:(rewrite b11; f_equal; subst wd; lia) b12 b13 b14 b15
           ltac:(subst N9; apply (rdn_wbytes_hit8 SEGS); rewrite u_Z2bv by lia; lia)
           PXd9 HOKd Hwd1 Hhd1 Hd ltac:(unfold rop_rect; subst wd hd; lia) Hop L2p NEpdw L2d L0d L00d).
  intros n9 q9 HV9 CS9 PN9 PXe9 FPe9 A10_9.
  assert (FP9 : forall a : word, ~ scratch C s a -> ~ (data <= u a < data + 4 * (wpl_of wd d * hd))%Z -> n9 a = m4 a).
  { intros a Ha1 Ha2. rewrite (FPe9 a ltac:(clear - Ha1; unfold scratch in *; lia) Ha2). rewrite (OUT9 a) by (clear - Ha1 Hlo Hhi; unfold scratch in Ha1; lia). exact (FP8 a Ha1 Ha2). }
  replace (Z_to_bv 64 0x181f8) with (0x181f8 : word) by (apply bv_eq; reflexivity).
  assert (PO9 : POSTM C A s m n9) by (eapply POSTM_trans; [exact PM9 | eapply POSTM_mono; [|exact PN9]; lia]).
  pose proof (abfr_frm C (s - 112) N9 n9 s ret regs w h d CK (proj1 PN9) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) FR9) as FS9.
  assert (PXt9 : PIXat n9 pixs (hdv w h d cm datas)).
  { apply (PIXat_frame N9); [exact PXs9|]. intros x Hx. exact (LIVK_at A N9 n9 pixs 64 x (proj2 PN9) Lps ltac:(lia) ltac:(lia) Hx). }
  (* [comment removed for export] *)
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
  assert (PXs10 : PIXat N10 pixs (hdv w h d cm datas)) by (apply (PIXat_frame n9); [exact PXt9 | intros x Hx; apply OUT10; lia]).
  apply (ab_uni_W C A A2 N10 _ r10 (s - 112) pixd data wd hd d cd 0 0 wd top op (Z_to_bv 64 0x18220) S CK HW10 SUBb
           ltac:(csr; reflexivity) Hs16' Hlo' Hhi'
           c1 ltac:(red; apply bv_eq; reflexivity) c10 c11 c12 c13 c14 c15
           ltac:(subst N10; apply (rdn_wbytes_hit8 SEGS); rewrite u_Z2bv by lia; lia)
           PXd10 HOKd Hwd1 Hhd1 Hd ltac:(unfold rop_rect; subst wd hd; lia) Hop L2p NEpdw L2d L0d L00d).
  intros n10 q10 HV10 CS10 PN10 PXe10 FPe10 A10_10.
  assert (FP10 : forall a : word, ~ scratch C s a -> ~ (data <= u a < data + 4 * (wpl_of wd d * hd))%Z -> n10 a = m4 a).
  { intros a Ha1 Ha2. rewrite (FPe10 a ltac:(clear - Ha1; unfold scratch in *; lia) Ha2). rewrite (OUT10 a) by (clear - Ha1 Hlo Hhi; unfold scratch in Ha1; lia). exact (FP9 a Ha1 Ha2). }
  replace (Z_to_bv 64 0x18220) with (0x18220 : word) by (apply bv_eq; reflexivity).
  assert (PO10 : POSTM C A s m n10) by (eapply POSTM_trans; [exact PM10 | eapply POSTM_mono; [|exact PN10]; lia]).
  pose proof (abfr_frm C (s - 112) N10 n10 s ret regs w h d CK (proj1 PN10) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) FR10) as FS10.
  assert (PXt10 : PIXat n10 pixs (hdv w h d cm datas)).
  { apply (PIXat_frame N10); [exact PXs10|]. intros x Hx. exact (LIVK_at A N10 n10 pixs 64 x (proj2 PN10) Lps ltac:(lia) ltac:(lia) Hx). }
  (* [comment removed for export] *)
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
  assert (PXs11 : PIXat N11 pixs (hdv w h d cm datas)) by (apply (PIXat_frame n10); [exact PXt10 | intros x Hx; apply OUT11; lia]).
  apply (ab_uni_W C A A2 N11 _ r11 (s - 112) pixd data wd hd d cd 0 (h + top) wd bot op (Z_to_bv 64 0x18254) S CK HW11 SUBb
           ltac:(csr; reflexivity) Hs16' Hlo' Hhi'
           d1 ltac:(red; apply bv_eq; reflexivity) d10 d11 ltac:(rewrite d12; f_equal; subst hd; lia) d13 d14 d15
           ltac:(subst N11; apply (rdn_wbytes_hit8 SEGS); rewrite u_Z2bv by lia; lia)
           PXd11 HOKd Hwd1 Hhd1 Hd ltac:(unfold rop_rect; subst wd hd; lia) Hop L2p NEpdw L2d L0d L00d).
  intros n11 q11 HV11 CS11 PN11 PXe11 FPe11 A10_11.
  assert (FP11 : forall a : word, ~ scratch C s a -> ~ (data <= u a < data + 4 * (wpl_of wd d * hd))%Z -> n11 a = m4 a).
  { intros a Ha1 Ha2. rewrite (FPe11 a ltac:(clear - Ha1; unfold scratch in *; lia) Ha2). rewrite (OUT11 a) by (clear - Ha1 Hlo Hhi; unfold scratch in Ha1; lia). exact (FP10 a Ha1 Ha2). }
  replace (Z_to_bv 64 0x18254) with (0x18254 : word) by (apply bv_eq; reflexivity).
  assert (PO11 : POSTM C A s m n11) by (eapply POSTM_trans; [exact PM11 | eapply POSTM_mono; [|exact PN11]; lia]).
  pose proof (abfr_frm C (s - 112) N11 n11 s ret regs w h d CK (proj1 PN11) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) FR11) as FS11.
  assert (PXt11 : PIXat n11 pixs (hdv w h d cm datas)).
  { apply (PIXat_frame N11); [exact PXs11|]. intros x Hx. exact (LIVK_at A N11 n11 pixs 64 x (proj2 PN11) Lps ltac:(lia) ltac:(lia) Hx). }
  (* [comment removed for export] *)
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
  assert (PXs12 : PIXat N12 pixs (hdv w h d cm datas)) by (apply (PIXat_frame n11); [exact PXt11 | intros x Hx; apply OUT12; lia]).
  replace (0x1e488 : word) with (Z_to_bv 64 PC_pixRasterop) by (apply bv_eq; reflexivity).
  apply (ROPS C A A2 N12 _ r12 (s - 112)%Z pixd left top w h pixs 0%Z 0%Z (hdv wd hd d cd data) (hdv w h d cm datas) (Z_to_bv 64 0x1827c) S CK HW12 SUBb
           ltac:(csr; reflexivity) Hs16' Hlo' Hhi'
           e1 ltac:(red; apply bv_eq; reflexivity) e10 e11 e12 e13 e14 e15 e16 e17
           ltac:(subst N12; apply (rdn_wbytes_hit8 SEGS); rewrite u_Z2bv by lia; lia)
           PXd12 PXs12 eq_refl (hdr_rop_shape wd hd d HOKd Hwd1 Hhd1 Hd) (hdr_rop_shape w h d HOK Hw Hh Hd)
           ltac:(cbn [hdv p_w p_h]; unfold rop_rect; subst wd hd; lia) ltac:(cbn [hdv p_w p_h]; unfold rop_rect; lia)
           ltac:(cbn [hdv p_d]; exact Hal) ltac:(cbn [hdv p_d]; reflexivity)
           L2p (SUBb _ _ Lps) NEpdw NEsd L2d L0d L00d (SUBb _ _ Lds) NEdd).
  intros n12 q12 HV12 CS12 PN12 PXe12 PXse12 FPe12 A10_12. cbn [hdv p_data p_wpl p_h] in FPe12.
  assert (FP12 : forall a : word, ~ scratch C s a -> ~ (data <= u a < data + 4 * (wpl_of wd d * hd))%Z -> n12 a = m4 a).
  { intros a Ha1 Ha2. rewrite (FPe12 a ltac:(clear - Ha1; unfold scratch in *; lia) Ha2). rewrite (OUT12 a) by (clear - Ha1 Hlo Hhi; unfold scratch in Ha1; lia). exact (FP11 a Ha1 Ha2). }
  replace (Z_to_bv 64 0x1827c) with (0x1827c : word) by (apply bv_eq; reflexivity).
  assert (PO12 : POSTM C A s m n12) by (eapply POSTM_trans; [exact PM12 | eapply POSTM_mono; [|exact PN12]; lia]).
  pose proof (cellsZ_frm C (s - 112) N12 n12 _ CK (proj1 PN12) ltac:(lia) ltac:(eapply Forall_impl; [|exact (frameA_bounds s ret regs ltac:(lia) ltac:(lia))]; intros [a0 v0] [X Y]; cbn [fst snd] in *; lia) CE12) as CE13.
  destruct (ab_E al_rom q12 regs n12 s pixd ret ltac:(lia) ltac:(lia) Hret CE13 ltac:(csr; reflexivity) ltac:(csr; reflexivity)) as (r13 & RUN13 & Z2 & Z1 & Z10 & ZR & AG13).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HV12)) | exact (mp_lazy _ (w_pure _ _ _ _ HV12)) | exact RUN13 |]. clear RUN13.
apply (HK n12 r13 HV12).
  - apply cs_kept_intro; first [solve [apply ZR; in_lit] | (csr; reflexivity)].
  - exact PO12.
  - exact Z10.
  - exact PXe12.
  - exact FP12.
Qed.

(* [comment removed for export] *)
Theorem pixAddBorderGeneral_W : pixAddBorderGeneral_contract.
Proof.
  unfold pixAddBorderGeneral_contract.
  intros C A m md regs s pixs w h d cm datas left right top bot val cv ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 H11 H12 H13 H14 H15
         PXs HOK Hw Hh Hd Lps Lds HCM Hl Hr Ht Hb Hal Hval kR bR Hrm Hrk Hrb HK.
  replace (Z_to_bv 64 PC_pixAddBorderGeneral) with (0x17fb8 : word) by (apply bv_eq; reflexivity).
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold ABG_STACK, LSF in *.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof HOK as (DV & Hw2 & Hh2 & Hsz). pose proof (wpl_of_range w d ltac:(lia) DV) as Hwpl.
  pose proof PXs as (Hs0 & Hs64' & WFs & _).
  destruct (blk_range C A m md (Z_to_bv 64 pixs) 64 CK HW Lps ltac:(lia)) as [Gps TOPps]. rewrite u_Z2bv in Gps, TOPps by lia.
  set (wd := (w + left + right)%Z) in *. set (hd := (h + top + bot)%Z) in *.
  assert (Hprod : (4 * (wpl_of wd d * hd) < 2 ^ 31)%Z) by (apply border_t1; [subst wd; lia | subst hd; lia | exact Hd]).
  assert (ALps8 : (pixs mod 8 = 0)%Z) by (pose proof (ai_live_hull A m _ _ _ (w_inv _ _ _ _ HW) Lps) as (_ & X16 & _); rewrite u_Z2bv in X16 by lia; apply mod16_mod8; exact X16).
  (* [comment removed for export] *)
  destruct (ab_A al_rom regs m s pixs left right top bot val (hdv w h d cm datas) ret ltac:(lia) ltac:(lia) Hs16 ltac:(lia) ALps8 PXs ltac:(lia)
              ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia)
              (W_sok_win C A m md (s - 112) 112 CK HW ltac:(lia) ltac:(cbn; lia)) H2 H1 H10 H11 H12 H13 H14 H15)
    as (r1 & RUN1 & Q2 & Q1 & Q10 & Q11 & Q12 & Q8 & Q18 & Q21 & Q9 & Q20 & Q26 & Q22 & Q25 & AG1).
  cbn [p_w p_h p_d hdv] in RUN1, Q10, Q11, Q12, Q22, Q25. fold wd in Q10, Q22. fold hd in Q11, Q25.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |]. clear RUN1.
  set (M1 := DIMS (FRA m s ret regs) (s - 84) w h d) in *.
  assert (WP1 : W C A M1 md /\ POSTM C A s m M1) by (subst M1; unfold DIMS, FRA; wp_win CK).
  destruct WP1 as [HW1 PM1].
  pose proof (abfr_init m s ret regs w h d ltac:(lia) ltac:(lia)) as FR1. fold M1 in FR1.
  assert (OUT1 : forall x : word, ~ (s - 112 <= u x < s)%Z -> M1 x = m x).
  { intros x Hx. subst M1. rewrite DIMS_out by lia. apply FRA_out; lia. }
  assert (Q4 : getr r1 4 = Z_to_bv 64 0x45480) by (csr; reflexivity).
  apply (pixCreate_T C A M1 md r1 (s - 112) wd hd d (Z_to_bv 64 0x18074) S CK HW1 Q2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(unfold LSF; lia) ltac:(lia) Q1 ltac:(red; apply bv_eq; reflexivity) Q4 Q10 Q11 Q12 ltac:(subst wd; lia) ltac:(subst hd; lia) Hprod
           ltac:(destruct Hd; lia)).
  intros A1 m1 vm1 r2 HWa CSa PMa OUTa HRTa.
  replace (Z_to_bv 64 0x18074) with (0x18074 : word) by (apply bv_eq; reflexivity).
  assert (PMa' : POSTM C A s m m1) by (eapply POSTM_trans; [exact PM1 | eapply POSTM_mono; [|exact PMa]; lia]).
  pose proof (abfr_frm C (s - 112) M1 m1 s ret regs w h d CK (proj1 PMa) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) FR1) as FR2.
  destruct OUTa as [[Hres0 LIVEQ] | (pixd & data & Hres & HOKd & PN)].
  - (* [comment removed for export] *)
    destruct (ab_F al_rom r2 m1 (W_sev_got C A1 m1 _ HWa) (W_sev C A1 m1 _ HWa) Hres0) as (r3 & RUN3 & V1 & V10 & V11 & V12 & AG3).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWa)) | exact (mp_lazy _ (w_pure _ _ _ _ HWa)) | exact RUN3 |]. clear RUN3.
    apply (returnErrorPtr_W C A1 m1 _ r3 (s - 112) 0x1054a 0x10cd9 13 19 (Z_to_bv 64 0x18164) (Z_to_bv 64 0) S CK HWa ltac:(csr; reflexivity)
             ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold LSF; lia) ltac:(lia) V1 ltac:(red; apply bv_eq; reflexivity)
             V10 V11 V12 str_msg_pixd str_pixAddBorderGeneral).
    intros m4 r5 HW4 OUT4 GR4 CS4 A10. unfold LSF in OUT4.
    replace (Z_to_bv 64 0x18164) with (0x18164 : word) by (apply bv_eq; reflexivity).
    destruct (ab_F2 al_rom r5 m4 0 A10) as (r6 & RUN6 & X19 & AG6).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW4)) | exact (mp_lazy _ (w_pure _ _ _ _ HW4)) | exact RUN6 |]. clear RUN6.
    pose proof (abfr_out m1 m4 _ _ s ret regs w h d OUT4 ltac:(lia) ltac:(lia) ltac:(lia) FR2) as (CE4 & _).
    destruct (ab_E al_rom r6 regs m4 s 0 ret ltac:(lia) ltac:(lia) Hret CE4 ltac:(csr; reflexivity) X19) as (r7 & RUN7 & Z2 & Z1 & Z10 & ZR & AG7).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW4)) | exact (mp_lazy _ (w_pure _ _ _ _ HW4)) | exact RUN7 |]. clear RUN7.
    apply (HK A1 m4 vm1 r7 HW4).
    + apply cs_kept_intro; first [solve [apply ZR; in_lit] | (csr; reflexivity)].
    + eapply POSTM_trans; [exact PMa'|]. apply (POSTM_sub C A A1); [apply sub_live_eq; exact LIVEQ|].
      eapply (POSTM_range C A1 m1 _ m4); [exact CK | exact HWa | exact OUT4 | lia | lia | lia].
    + left. split; [exact Z10 | exact LIVEQ].
    + room_tac.
  - (* [comment removed for export] *)
    destruct PN as (Gp & TOPp & ALp & Gd & TOPd & ALd & NEpd & L0p & L0d & L00p & L00d & L1p & L1d & LEQ & PXd & _).
    cbn [p_wpl p_h set_data pix_hdr] in TOPd, L1d.
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
    assert (PXs1 : PIXat m1 pixs (hdv w h d cm datas)).
    { apply (PIXat_frame m); [exact PXs|]. intros x Hx. rewrite (LIVK_at A M1 m1 pixs 64 x (proj2 PMa) Lps ltac:(lia) ltac:(lia) Hx). apply OUT1. lia. }
    destruct (ab_B1 al_rom r2 m1 pixd pixs ltac:(lia) Hres ltac:(csr; reflexivity)) as (r3 & RUN3 & V1 & V10 & V11 & V19 & AG3).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWa)) | exact (mp_lazy _ (w_pure _ _ _ _ HWa)) | exact RUN3 |]. clear RUN3.
    destruct (pixCopyResolution_run al_rom r3 m1 pixd pixs (hdv w h d cm datas) (hdv wd hd d 0 data) (Z_to_bv 64 0x18084) ltac:(lia) ltac:(lia)
                ltac:(intros E; apply NEsp; rewrite E; reflexivity) ALps8 (mod16_mod8 _ ALp) PXs1 PXd eq_refl eq_refl
                (blk_sok C A1 m1 _ pixd 64 CK HWa L1p ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(red; apply bv_eq; reflexivity) V1 V10 V11)
      as (r4 & RUN4 & X10 & AG4).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWa)) | exact (mp_lazy _ (w_pure _ _ _ _ HWa)) | exact RUN4 |]. clear RUN4.
    replace (Z_to_bv 64 0x18084) with (0x18084 : word) by (apply bv_eq; reflexivity).
    set (M3 := wbytes m1 (Z_to_bv 64 (pixd + 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))).
    assert (WP3 : W C A1 M3 (with_vmmaps vm1 md) /\ POSTM C A s m M3).
    { subst M3. apply (WP_blk C A A1 m _ _ (Z_to_bv 64 pixd) _ 64); [exact CK | | exact L1p | exact L0p | exact L00p | exact SUBa | rewrite !u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia].
      split; [exact HWa | exact PMa']. }
    destruct WP3 as [HW3 PM3].
    assert (OUT3 : forall x : word, ~ (pixd + 24 <= u x < pixd + 32)%Z -> M3 x = m1 x).
    { intros x Hx. subst M3. apply (wbytes_out_Z _ _ 8); [rewrite length_N_to_le_bytes; reflexivity | lia | lia | lia]. }
    assert (PXd3 : PIXat M3 pixd (hdv wd hd d 0 data)) by (subst M3; apply (PIX_wr_res0 _ pixd (hdv wd hd d 0 data)); [exact PXd | reflexivity | reflexivity]).
    assert (PXs3 : PIXat M3 pixs (hdv w h d cm datas)) by (apply (PIXat_frame m1); [exact PXs1 | intros x Hx; apply OUT3; lia]).
    pose proof (abfr_out m1 M3 _ _ s ret regs w h d OUT3 ltac:(lia) ltac:(lia) ltac:(lia) FR2) as FR3.
    destruct (ab_B2 al_rom r4 M3 pixd pixs ltac:(csr; reflexivity) ltac:(csr; reflexivity)) as (r5 & RUN5 & Y1 & Y10 & Y11 & AG5).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW3)) | exact (mp_lazy _ (w_pure _ _ _ _ HW3)) | exact RUN5 |]. clear RUN5.
    assert (HCMc : p_cmap (hdv w h d cm datas) = 0%Z \/ (CMAPat M3 (p_cmap (hdv w h d cm datas)) cv /\ cmap_ok cv /\ live A1 (Z_to_bv 64 (p_cmap (hdv w h d cm datas))) = Some 24%Z /\
                        live A1 (Z_to_bv 64 (c_arr cv)) = Some (4 * c_nalloc cv)%Z)).
    { cbn [p_cmap hdv]. destruct HCM as [CM0 | (CM & CMOK & Lcm & Larr)]; [left; exact CM0 | right].
      pose proof CM as (Hc0 & Hc64 & _). destruct (blk_range C A m md (Z_to_bv 64 cm) 24 CK HW Lcm ltac:(lia)) as [Gcm TOPcm]. rewrite u_Z2bv in Gcm, TOPcm by lia.
      pose proof (SUBa _ _ Lcm) as Lcm1.
      assert (NEcp : Z_to_bv 64 cm <> Z_to_bv 64 pixd) by (intros E; rewrite E in Lcm; rewrite Lcm in L0p; discriminate).
      pose proof (blk_apart C A1 m1 _ _ _ _ _ CK HWa Lcm1 L1p NEcp ltac:(lia) ltac:(lia)) as APcp. rewrite !u_Z2bv in APcp by lia.
      split; [| split; [exact CMOK | split; [exact Lcm1 | exact (SUBa _ _ Larr)]]].
      apply (CMAPat_frame m); [exact CM|]. intros x Hx. rewrite OUT3 by lia.
      rewrite (LIVK_at A M1 m1 cm 24 x (proj2 PMa) Lcm ltac:(lia) ltac:(lia) Hx). apply OUT1. lia. }
    apply (pixCopyColormap_T C A A1 M3 _ r5 (s - 112) pixd pixs (hdv wd hd d 0 data) (hdv w h d cm datas) cv (Z_to_bv 64 0x18090) S CK HW3 SUBa
             ltac:(csr; reflexivity) ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold LSF; lia) ltac:(lia) Y1 ltac:(red; apply bv_eq; reflexivity)
             ltac:(csr; reflexivity) Y10 Y11 PXd3 PXs3 eq_refl eq_refl ltac:(intros E; apply NEsp; rewrite E; reflexivity) L1p L0p L00p Lps1 HCMc
             (kR - RK_pix) (bR - RB10_pix (4 * (wpl_of wd d * hd))) ltac:(room_tac) ltac:(room_consts; lia) ltac:(room_consts; lia)).
    intros A2 m4 vm2 r6 HWb CSb PMb OUTb Hrm2. rewrite with_vmmaps_twice in HWb |- *.
    replace (Z_to_bv 64 0x18090) with (0x18090 : word) by (apply bv_eq; reflexivity).
    destruct (cmres_build C A A1 A2 m4 _ s pixd data (4 * (wpl_of wd d * hd)) (hdv wd hd d 0 data) cv CK HWb Hhi ltac:(lia) Gp Gd ltac:(lia) TOPd L0p L0d L1p L1d LEQ eq_refl OUTb)
      as (cd & PXd4 & SUB12 & L2p & L2d & BUILD). cbn [set_cmap hdv] in PXd4. change (PIXat m4 pixd (hdv wd hd d cd data)) in PXd4.
    assert (SUBb : sub_live A A2) by (eapply sub_live_trans; [exact SUBa | exact SUB12]).
    assert (PMb' : POSTM C A s m m4) by (eapply POSTM_trans; [exact PM3 | eapply POSTM_mono; [|exact PMb]; lia]).
    pose proof (abfr_frm C (s - 112) M3 m4 s ret regs w h d CK (proj1 PMb) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) FR3) as FR4.
    assert (PXs4 : PIXat m4 pixs (hdv w h d cm datas)).
    { apply (PIXat_frame M3); [exact PXs3|]. intros x Hx. exact (LIVK_at A M3 m4 pixs 64 x (proj2 PMb) Lps ltac:(lia) ltac:(lia) Hx). }
    (* [comment removed for export] *)
    assert (FIN : forall m' regs', W C A2 m' (with_vmmaps vm2 md) -> cs_kept regs regs' -> POSTM C A s m m' -> getr regs' 10 = Z_to_bv 64 pixd ->
              PIXat m' pixd (hdv wd hd d cd data) -> (forall a : word, ~ scratch C s a -> ~ (data <= u a < data + 4 * (wpl_of wd d * hd))%Z -> m' a = m4 a) ->
              realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm2 md)) S).
    { intros m' regs' X1 X2 X3 X4 X5 X6. apply (HK A2 m' vm2 regs' X1 X2 X3); [right; exists pixd, cd, data; split; [exact X4 | split; [exact HOKd |]] | room_tac].
      unfold pixt_new. repeat (split; [assumption|]). exact (BUILD m' X6). }
    assert (TAILR : forall r7 op, (op = 0 \/ op = 15)%Z -> getr r7 24 = Z_to_bv 64 op ->
              (forall x, In x [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 25; 26; 27]%bv -> getr r7 x = getr r6 x) ->
              realizes SEGS (mkCfg (mkst r7 (0x1819c : word) m4 al_rom) (with_vmmaps vm2 md)) S).
    { intros r7 op Hop W26 RR7.
      apply (ab_fills_W C A A2 m m4 _ regs r7 s pixs pixd data w h d cm datas cd left right top bot op ret S CK Hs16 ltac:(unfold ABG_STACK, LSF; lia) Hhi Hret HWb PMb'
               HOK Hw Hh Hd Hl Hr Ht Hb Hal Hop HOKd SUBb Gp TOPp ALp Gd TOPd ALd NEpd L0p L0d L00p L00d L2p L2d PXd4 PXs4 Lps Lds FR4); try exact FIN; try exact W26; try exact H2;
        rewrite RR7 by in_lit; csr; reflexivity. }
    destruct FR4 as (CE4 & Rw4 & Rh4 & Rd4).
    destruct (ab_C al_rom r6 m4 s d val ltac:(lia) ltac:(lia) Hd Hval Rd4 ltac:(csr; reflexivity) ltac:(csr; reflexivity)) as (r7 & RUN7 & W26 & AG7).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWb)) | exact (mp_lazy _ (w_pure _ _ _ _ HWb)) | exact RUN7 |]. clear RUN7.
    apply (TAILR r7 (if Z.eq_dec val 0 then 0 else 15)%Z ltac:(destruct (Z.eq_dec val 0); [left | right]; reflexivity) W26).
    intros x Hx. cbn [In] in Hx. repeat (destruct Hx as [<-|Hx]; [apply AG7; notin_lit|]). destruct Hx.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem pixRemoveBorderGeneral_null_W : pixRemoveBorderGeneral_null_contract.
Proof.
  unfold pixRemoveBorderGeneral_null_contract.
  intros C A m md regs s ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H10 HK.
  replace (Z_to_bv 64 PC_pixRemoveBorderGeneral) with (0x18304 : word) by (apply bv_eq; reflexivity).
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold RBG_STACK, LSF in *.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  destruct (rb_N1 al_rom regs m s ret ltac:(lia) ltac:(lia) (W_sok_win C A m md (s - 96) 96 CK HW ltac:(lia) ltac:(cbn; lia)) H2 H1 H10) as (r1 & RUN1 & Q2 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |]. clear RUN1.
  assert (WP1 : W C A (FRR m s ret regs) md /\ POSTM C A s m (FRR m s ret regs)) by (unfold FRR; wp_win CK).
  destruct WP1 as [HW1 PM1]. set (M1 := FRR m s ret regs) in *.
  destruct (rb_N2 al_rom r1 regs M1 s ret ltac:(lia) ltac:(lia) (W_sev_got C A M1 _ HW1) (W_sev C A M1 _ HW1) (cells_FRR m s ret regs ltac:(lia) ltac:(lia)) Q2)
    as (r2 & RUN2 & V2 & V1 & V10 & V11 & V12 & VR & AG2).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN2 |]. clear RUN2.
  apply (returnErrorPtr_W C A M1 md r2 s 0x10298 0x10e5b 16 22 ret (Z_to_bv 64 0) S CK HW1 V2 Hs16 ltac:(unfold LSF; lia) Hhi V1 Hret
           V10 V11 V12 str_msg_pixs_undef str_pixRemoveBorderGeneral).
  intros m4 r5 HW4 OUT4 GR4 CS4 A10. unfold LSF in OUT4.
  apply (HK m4 r5 HW4).
  - apply cs_kept_intro; csr; first [reflexivity | solve [apply VR; in_lit] | (rewrite H2; reflexivity)].
  - eapply POSTM_trans; [exact PM1|]. eapply (POSTM_range C A M1 _ m4); [exact CK | exact HW1 | exact OUT4 | lia | lia | lia].
  - exact A10.
Qed.

Theorem pixRemoveBorderGeneral_W : pixRemoveBorderGeneral_contract.
Proof.
  unfold pixRemoveBorderGeneral_contract.
  intros C A m md regs s pixs w h d cm datas left right top bot cv ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 H11 H12 H13 H14
         PXs HOK Hd Lps Lds HCM Hl Hr Ht Hb Hal Hwd Hhd kR bR Hrm Hrk Hrb HK.
  replace (Z_to_bv 64 PC_pixRemoveBorderGeneral) with (0x18304 : word) by (apply bv_eq; reflexivity).
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold RBG_STACK, LSF in *.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof HOK as (DV & Hw2 & Hh2 & Hsz). assert (Hw : (1 <= w)%Z) by lia. assert (Hh : (1 <= h)%Z) by lia.
  pose proof (wpl_of_range w d ltac:(lia) DV) as Hwpl.
  pose proof PXs as (Hs0 & Hs64' & WFs & _).
  destruct (blk_range C A m md (Z_to_bv 64 pixs) 64 CK HW Lps ltac:(lia)) as [Gps TOPps]. rewrite u_Z2bv in Gps, TOPps by lia.
  set (wd := (w - left - right)%Z) in *. set (hd := (h - top - bot)%Z) in *.
  assert (Hs96 : (96 <= s)%Z) by lia. assert (Hs64 : (s < 2 ^ 64)%Z) by lia.
  assert (ALps8 : (pixs mod 8 = 0)%Z) by (pose proof (ai_live_hull A m _ _ _ (w_inv _ _ _ _ HW) Lps) as (_ & X16 & _); rewrite u_Z2bv in X16 by lia; apply mod16_mod8; exact X16).
  (* [comment removed for export] *)
  destruct (rb_A al_rom regs m s pixs left right top bot (hdv w h d cm datas) ret Hs96 Hs64 Hs16 ltac:(lia) ALps8 PXs ltac:(lia)
              ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; subst wd; lia) ltac:(cbn; subst hd; lia)
              (W_sok_win C A m md (s - 96) 96 CK HW ltac:(lia) ltac:(cbn; lia)) H2 H1 H10 H11 H12 H13 H14)
    as (r1 & RUN1 & Q2 & Q1 & Q10 & Q11 & Q12 & Q8 & Q9 & Q18 & Q19 & Q20 & AG1).
  cbn [p_w p_h p_d hdv] in RUN1, Q10, Q11, Q12, Q19, Q20. fold wd in Q10, Q19. fold hd in Q11, Q20.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |]. clear RUN1.
  set (M1 := DIMS (FRR m s ret regs) (s - 68) w h d) in *.
  assert (WP1 : W C A M1 md /\ POSTM C A s m M1) by (subst M1; unfold DIMS, FRR; wp_win CK).
  destruct WP1 as [HW1 PM1].
  pose proof (rbfr_init m s ret regs w h d Hs96 Hs64) as FR1. fold M1 in FR1.
  assert (OUT1 : forall x : word, ~ (s - 96 <= u x < s)%Z -> M1 x = m x).
  { intros x Hx. subst M1. rewrite DIMS_out by lia. apply FRR_out; lia. }
  assert (Q4 : getr r1 4 = Z_to_bv 64 0x45480) by (csr; reflexivity).
  assert (Hprod : (4 * (wpl_of wd d * hd) < 2 ^ 31)%Z) by (apply border_t1; [subst wd; lia | subst hd; lia | exact Hd]).
  apply (pixCreate_T C A M1 md r1 (s - 96) wd hd d (Z_to_bv 64 0x183b8) S CK HW1 Q2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(unfold LSF; lia) ltac:(lia) Q1 ltac:(red; apply bv_eq; reflexivity) Q4 Q10 Q11 Q12 ltac:(subst wd; lia) ltac:(subst hd; lia) Hprod
           ltac:(destruct Hd; lia)).
  intros A1 m1 vm1 r2 HWa CSa PMa OUTa HRTa.
  replace (Z_to_bv 64 0x183b8) with (0x183b8 : word) by (apply bv_eq; reflexivity).
  assert (PMa' : POSTM C A s m m1) by (eapply POSTM_trans; [exact PM1 | eapply POSTM_mono; [|exact PMa]; lia]).
  pose proof (rbfr_frm C (s - 96) M1 m1 s ret regs w h d CK (proj1 PMa) ltac:(lia) ltac:(lia) Hs96 Hs64 FR1) as FR2.
  destruct OUTa as [[Hres0 LIVEQ] | (pixd & data & Hres & HOKd & PN)].
  - (* [comment removed for export] *)
    destruct (rb_F al_rom r2 m1 (W_sev_got C A1 m1 _ HWa) (W_sev C A1 m1 _ HWa) Hres0) as (r3 & RUN3 & V1 & V10 & V11 & V12 & AG3).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWa)) | exact (mp_lazy _ (w_pure _ _ _ _ HWa)) | exact RUN3 |]. clear RUN3.
    apply (returnErrorPtr_W C A1 m1 _ r3 (s - 96) 0x1054a 0x10e5b 13 22 (Z_to_bv 64 0x18544) (Z_to_bv 64 0) S CK HWa ltac:(csr; reflexivity)
             ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold LSF; lia) ltac:(lia) V1 ltac:(red; apply bv_eq; reflexivity)
             V10 V11 V12 str_msg_pixd str_pixRemoveBorderGeneral).
    intros m4 r5 HW4 OUT4 GR4 CS4 A10. unfold LSF in OUT4.
    replace (Z_to_bv 64 0x18544) with (0x18544 : word) by (apply bv_eq; reflexivity).
    destruct (rb_F2 al_rom r5 m4) as (r6 & RUN6 & AG6).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW4)) | exact (mp_lazy _ (w_pure _ _ _ _ HW4)) | exact RUN6 |]. clear RUN6.
    pose proof (rbfr_out m1 m4 _ _ s ret regs w h d OUT4 ltac:(lia) Hs96 Hs64 FR2) as (CE4 & _).
    destruct (rb_E al_rom r6 regs m4 s ret Hs96 Hs64 Hret CE4 ltac:(csr; reflexivity)) as (r7 & RUN7 & Z2 & Z1 & ZR & AG7).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW4)) | exact (mp_lazy _ (w_pure _ _ _ _ HW4)) | exact RUN7 |]. clear RUN7.
    apply (HK A1 m4 vm1 r7 HW4).
    + apply cs_kept_intro; first [solve [apply ZR; in_lit] | (csr; reflexivity)].
    + eapply POSTM_trans; [exact PMa'|]. apply (POSTM_sub C A A1); [apply sub_live_eq; exact LIVEQ|].
      eapply (POSTM_range C A1 m1 _ m4); [exact CK | exact HWa | exact OUT4 | lia | lia | lia].
    + left. split; [csr; reflexivity | exact LIVEQ].
    + room_tac.
  - (* [comment removed for export] *)
    destruct PN as (Gp & TOPp & ALp & Gd & TOPd & ALd & NEpd & L0p & L0d & L00p & L00d & L1p & L1d & LEQ & PXd & _).
    cbn [p_wpl p_h set_data pix_hdr] in TOPd, L1d.
    change (PIXat m1 pixd (hdv wd hd d 0 data)) in PXd.
    pose proof HOKd as (_ & Hwd2 & Hhd2 & Hszd). pose proof (wpl_of_range wd d ltac:(subst wd; lia) DV) as Hwpld.
    assert (Hnd : (0 <= wpl_of wd d * hd)%Z) by (apply Z.mul_nonneg_nonneg; subst hd; lia).
    assert (NEsp : Z_to_bv 64 pixs <> Z_to_bv 64 pixd) by (intros E; rewrite E in Lps; rewrite Lps in L0p; discriminate).
    assert (NEsd : Z_to_bv 64 pixs <> Z_to_bv 64 data) by (intros E; rewrite E in Lps; rewrite Lps in L0d; discriminate).
    assert (NEdd : Z_to_bv 64 datas <> Z_to_bv 64 data) by (intros E; rewrite E in Lds; rewrite Lds in L0d; discriminate).
    assert (NEpdw : Z_to_bv 64 pixd <> Z_to_bv 64 data) by (apply zbv_ne2; lia).
    assert (SUBa : sub_live A A1) by (eapply sub_live_new2; [exact L0p | exact L0d | exact L1p | exact L1d | exact LEQ]).
    pose proof (SUBa _ _ Lps) as Lps1.
    pose proof (blk_apart C A1 m1 _ _ _ _ _ CK HWa Lps1 L1p NEsp ltac:(lia) ltac:(lia)) as APsp. rewrite !u_Z2bv in APsp by lia.
    assert (PXs1 : PIXat m1 pixs (hdv w h d cm datas)).
    { apply (PIXat_frame m); [exact PXs|]. intros x Hx. rewrite (LIVK_at A M1 m1 pixs 64 x (proj2 PMa) Lps ltac:(lia) ltac:(lia) Hx). apply OUT1. lia. }
    pose proof (blk_sok C A1 m1 _ pixd 64 CK HWa L1p ltac:(lia) ltac:(lia) ltac:(lia)) as SOKd.
    (* [comment removed for export] *)
    destruct (rb_B1 al_rom r2 m1 pixd pixs ltac:(lia) Hres ltac:(csr; reflexivity)) as (r3 & RUN3 & V1 & V10 & V11 & V21 & AG3).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWa)) | exact (mp_lazy _ (w_pure _ _ _ _ HWa)) | exact RUN3 |]. clear RUN3.
    destruct (pixCopyResolution_run al_rom r3 m1 pixd pixs (hdv w h d cm datas) (hdv wd hd d 0 data) (Z_to_bv 64 0x183c8) ltac:(lia) ltac:(lia)
                ltac:(intros E; apply NEsp; rewrite E; reflexivity) ALps8 (mod16_mod8 _ ALp) PXs1 PXd eq_refl eq_refl SOKd ltac:(red; apply bv_eq; reflexivity) V1 V10 V11)
      as (r4 & RUN4 & X10 & AG4).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWa)) | exact (mp_lazy _ (w_pure _ _ _ _ HWa)) | exact RUN4 |]. clear RUN4.
    replace (Z_to_bv 64 0x183c8) with (0x183c8 : word) by (apply bv_eq; reflexivity).
    set (M3 := wbytes m1 (Z_to_bv 64 (pixd + 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))).
    assert (WP3 : W C A1 M3 (with_vmmaps vm1 md) /\ POSTM C A s m M3).
    { subst M3. apply (WP_blk C A A1 m _ _ (Z_to_bv 64 pixd) _ 64); [exact CK | | exact L1p | exact L0p | exact L00p | exact SUBa | rewrite !u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia].
      split; [exact HWa | exact PMa']. }
    destruct WP3 as [HW3 PM3].
    assert (OUT3 : forall x : word, ~ (pixd + 24 <= u x < pixd + 32)%Z -> M3 x = m1 x).
    { intros x Hx. subst M3. apply (wbytes_out_Z _ _ 8); [rewrite length_N_to_le_bytes; reflexivity | lia | lia | lia]. }
    assert (PXd3 : PIXat M3 pixd (hdv wd hd d 0 data)) by (subst M3; apply (PIX_wr_res0 _ pixd (hdv wd hd d 0 data)); [exact PXd | reflexivity | reflexivity]).
    assert (PXs3 : PIXat M3 pixs (hdv w h d cm datas)) by (apply (PIXat_frame m1); [exact PXs1 | intros x Hx; apply OUT3; lia]).
    pose proof (rbfr_out m1 M3 _ _ s ret regs w h d OUT3 ltac:(lia) Hs96 Hs64 FR2) as FR3.
    (* [comment removed for export] *)
    destruct (rb_B2 al_rom r4 M3 pixd pixs ltac:(csr; reflexivity) ltac:(csr; reflexivity)) as (r5 & RUN5 & Y1 & Y10 & Y11 & AG5).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW3)) | exact (mp_lazy _ (w_pure _ _ _ _ HW3)) | exact RUN5 |]. clear RUN5.
    destruct (pixCopySpp_run al_rom r5 M3 pixd pixs (hdv w h d cm datas) (hdv wd hd d 0 data) (Z_to_bv 64 0x183d4) ltac:(lia) ltac:(lia)
                ltac:(intros E; apply NEsp; rewrite E; reflexivity) ALps8 (mod16_mod8 _ ALp) PXs3 PXd3 (proj1 (spp_of_range d))
                (blk_sok C A1 M3 _ pixd 64 CK HW3 L1p ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(red; apply bv_eq; reflexivity) Y1 Y10 Y11)
      as (r6 & RUN6 & U10 & AG6).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW3)) | exact (mp_lazy _ (w_pure _ _ _ _ HW3)) | exact RUN6 |]. clear RUN6.
    replace (Z_to_bv 64 0x183d4) with (0x183d4 : word) by (apply bv_eq; reflexivity).
    cbn [p_spp hdv] in *.
    set (M4 := wbytes M3 (Z_to_bv 64 (pixd + 12)) (word_to_le_bytes 4 (Z_to_bv 64 (spp_of d)))).
    assert (WP4 : W C A1 M4 (with_vmmaps vm1 md) /\ POSTM C A s m M4).
    { subst M4. apply (WP_blk C A A1 m _ _ (Z_to_bv 64 pixd) _ 64); [exact CK | | exact L1p | exact L0p | exact L00p | exact SUBa | rewrite !u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia].
      split; [exact HW3 | exact PM3]. }
    destruct WP4 as [HW4 PM4].
    assert (OUT4 : forall x : word, ~ (pixd + 12 <= u x < pixd + 16)%Z -> M4 x = M3 x).
    { intros x Hx. subst M4. apply (wbytes_out_Z _ _ 4); [rewrite length_N_to_le_bytes; reflexivity | lia | lia | lia]. }
    assert (PXd4 : PIXat M4 pixd (hdv wd hd d 0 data)) by (subst M4; exact (PIX_wr_spp_same M3 pixd (hdv wd hd d 0 data) PXd3)).
    assert (PXs4 : PIXat M4 pixs (hdv w h d cm datas)) by (apply (PIXat_frame M3); [exact PXs3 | intros x Hx; apply OUT4; lia]).
    pose proof (rbfr_out M3 M4 _ _ s ret regs w h d OUT4 ltac:(lia) Hs96 Hs64 FR3) as FR4.
    (* [comment removed for export] *)
    destruct (rb_B3 al_rom r6 M4 pixd pixs ltac:(csr; reflexivity) ltac:(csr; reflexivity)) as (r7 & RUN7 & Z1 & Z10 & Z11 & AG7).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW4)) | exact (mp_lazy _ (w_pure _ _ _ _ HW4)) | exact RUN7 |]. clear RUN7.
    assert (HCMc : p_cmap (hdv w h d cm datas) = 0%Z \/ (CMAPat M4 (p_cmap (hdv w h d cm datas)) cv /\ cmap_ok cv /\ live A1 (Z_to_bv 64 (p_cmap (hdv w h d cm datas))) = Some 24%Z /\
                        live A1 (Z_to_bv 64 (c_arr cv)) = Some (4 * c_nalloc cv)%Z)).
    { cbn [p_cmap hdv]. destruct HCM as [CM0 | (CM & CMOK & Lcm & Larr)]; [left; exact CM0 | right].
      pose proof CM as (Hc0 & Hc64 & _). destruct (blk_range C A m md (Z_to_bv 64 cm) 24 CK HW Lcm ltac:(lia)) as [Gcm TOPcm]. rewrite u_Z2bv in Gcm, TOPcm by lia.
      pose proof (SUBa _ _ Lcm) as Lcm1.
      assert (NEcp : Z_to_bv 64 cm <> Z_to_bv 64 pixd) by (intros E; rewrite E in Lcm; rewrite Lcm in L0p; discriminate).
      pose proof (blk_apart C A1 m1 _ _ _ _ _ CK HWa Lcm1 L1p NEcp ltac:(lia) ltac:(lia)) as APcp. rewrite !u_Z2bv in APcp by lia.
      split; [| split; [exact CMOK | split; [exact Lcm1 | exact (SUBa _ _ Larr)]]].
      apply (CMAPat_frame m); [exact CM|]. intros x Hx. rewrite OUT4 by lia. rewrite OUT3 by lia.
      rewrite (LIVK_at A M1 m1 cm 24 x (proj2 PMa) Lcm ltac:(lia) ltac:(lia) Hx). apply OUT1. lia. }
    apply (pixCopyColormap_T C A A1 M4 _ r7 (s - 96) pixd pixs (hdv wd hd d 0 data) (hdv w h d cm datas) cv (Z_to_bv 64 0x183e0) S CK HW4 SUBa
             ltac:(csr; reflexivity) ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold LSF; lia) ltac:(lia) Z1 ltac:(red; apply bv_eq; reflexivity)
             ltac:(csr; reflexivity) Z10 Z11 PXd4 PXs4 eq_refl eq_refl ltac:(intros E; apply NEsp; rewrite E; reflexivity) L1p L0p L00p Lps1 HCMc
             (kR - RK_pix) (bR - RB10_pix (4 * (wpl_of wd d * hd))) ltac:(room_tac) ltac:(room_consts; lia) ltac:(room_consts; lia)).
    intros A2 m5 vm2 r8 HWb CSb PMb OUTb Hrm2. rewrite with_vmmaps_twice in HWb |- *.
    replace (Z_to_bv 64 0x183e0) with (0x183e0 : word) by (apply bv_eq; reflexivity).
    destruct (cmres_build C A A1 A2 m5 _ s pixd data (4 * (wpl_of wd d * hd)) (hdv wd hd d 0 data) cv CK HWb Hhi ltac:(lia) Gp Gd ltac:(lia) TOPd L0p L0d L1p L1d LEQ eq_refl OUTb)
      as (cd & PXd5 & SUB12 & L2p & L2d & BUILD). cbn [set_cmap hdv] in PXd5. change (PIXat m5 pixd (hdv wd hd d cd data)) in PXd5.
    assert (SUBb : sub_live A A2) by (eapply sub_live_trans; [exact SUBa | exact SUB12]).
    assert (PMb' : POSTM C A s m m5) by (eapply POSTM_trans; [exact PM4 | eapply POSTM_mono; [|exact PMb]; lia]).
    pose proof (rbfr_frm C (s - 96) M4 m5 s ret regs w h d CK (proj1 PMb) ltac:(lia) ltac:(lia) Hs96 Hs64 FR4) as FR5.
    assert (PXs5 : PIXat m5 pixs (hdv w h d cm datas)).
    { apply (PIXat_frame M4); [exact PXs4|]. intros x Hx. exact (LIVK_at A M4 m5 pixs 64 x (proj2 PMb) Lps ltac:(lia) ltac:(lia) Hx). }
    (* [comment removed for export] *)
    destruct (rb_R al_rom r8 m5 s pixd pixs left top wd hd Hs96 Hs64 (W_sok_win C A2 m5 _ (s - 96) 8 CK HWb ltac:(lia) ltac:(cbn; lia))
                ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity)
                ltac:(csr; reflexivity) ltac:(csr; reflexivity))
      as (r9 & RUN9 & e1 & e10 & e11 & e12 & e13 & e14 & e15 & e16 & e17 & e23 & AG9).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWb)) | exact (mp_lazy _ (w_pure _ _ _ _ HWb)) | exact RUN9 |]. clear RUN9.
    set (N6 := wbytes m5 (Z_to_bv 64 (s - 96)) (word_to_le_bytes 8 (Z_to_bv 64 top))).
    assert (WP6 : W C A2 N6 (with_vmmaps vm2 md) /\ POSTM C A s m N6) by (subst N6; wp_win CK).
    destruct WP6 as [HW6 PM6].
    assert (OUT6 : forall x : word, ~ (s - 96 <= u x < s - 88)%Z -> N6 x = m5 x).
    { intros x Hx. subst N6. apply (wbytes_out_Z _ _ 8); [rewrite length_N_to_le_bytes; reflexivity | clear - Hs96 Hs64; lia | clear - Hs96 Hs64; lia | clear - Hs96 Hs64 Hx; lia]. }
    pose proof (rbfr_out m5 N6 _ _ s ret regs w h d OUT6 ltac:(lia) Hs96 Hs64 FR5) as FR6.
    assert (PXd6 : PIXat N6 pixd (hdv wd hd d cd data)) by (apply (PIXat_frame m5); [exact PXd5 | intros x Hx; apply OUT6; lia]).
    assert (PXs6 : PIXat N6 pixs (hdv w h d cm datas)) by (apply (PIXat_frame m5); [exact PXs5 | intros x Hx; apply OUT6; lia]).
    replace (0x1e488 : word) with (Z_to_bv 64 PC_pixRasterop) by (apply bv_eq; reflexivity).
    apply (ROPS C A A2 N6 _ r9 (s - 96)%Z pixd 0%Z 0%Z wd hd pixs left top (hdv wd hd d cd data) (hdv w h d cm datas) (Z_to_bv 64 0x1840c) S CK HW6 SUBb
             ltac:(csr; reflexivity) ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ROP_STACK; lia) ltac:(lia)
             e1 ltac:(red; apply bv_eq; reflexivity) e10 e11 e12 e13 e14 e15 e16 e17
             ltac:(subst N6; apply (rdn_wbytes_hit8 SEGS); rewrite u_Z2bv by lia; lia)
             PXd6 PXs6 eq_refl (hdr_rop_shape wd hd d HOKd ltac:(subst wd; lia) ltac:(subst hd; lia) Hd) (hdr_rop_shape w h d HOK Hw Hh Hd)
             ltac:(cbn [hdv p_w p_h]; unfold rop_rect; subst wd hd; lia) ltac:(cbn [hdv p_w p_h]; unfold rop_rect; subst wd hd; lia)
             ltac:(cbn [hdv p_d]; reflexivity) ltac:(cbn [hdv p_d]; exact Hal)
             L2p (SUBb _ _ Lps) NEpdw NEsd L2d L0d L00d (SUBb _ _ Lds) NEdd).
    intros n7 q7 HV7 CS7 PN7 PXe7 PXse7 FPe7 A10_7. cbn [hdv p_data p_wpl p_h] in FPe7.
    assert (FP7 : forall a : word, ~ scratch C s a -> ~ (data <= u a < data + 4 * (wpl_of wd d * hd))%Z -> n7 a = m5 a).
    { intros a Ha1 Ha2. rewrite (FPe7 a ltac:(clear - Ha1; unfold scratch in *; lia) Ha2). apply OUT6. clear - Ha1 Hlo Hhi Hs96. unfold scratch in Ha1. lia. }
    replace (Z_to_bv 64 0x1840c) with (0x1840c : word) by (apply bv_eq; reflexivity).
    assert (PO7 : POSTM C A s m n7) by (eapply POSTM_trans; [exact PM6 | eapply POSTM_mono; [|exact PN7]; lia]).
    pose proof (rbfr_frm C (s - 96) N6 n7 s ret regs w h d CK (proj1 PN7) ltac:(lia) ltac:(lia) Hs96 Hs64 FR6) as (CE7 & _).
    (* [comment removed for export] *)
    destruct (rb_D al_rom q7 n7 pixs pixd (hdv w h d cm datas) ltac:(lia) ALps8 PXse7 ltac:(cbn; exact Hd) ltac:(csr; reflexivity) ltac:(csr; reflexivity))
      as (r10 & RUN10 & f10 & AG10).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HV7)) | exact (mp_lazy _ (w_pure _ _ _ _ HV7)) | exact RUN10 |]. clear RUN10.
    destruct (rb_E al_rom r10 regs n7 s ret Hs96 Hs64 Hret CE7 ltac:(csr; reflexivity)) as (r11 & RUN11 & g2 & g1 & gR & AG11).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HV7)) | exact (mp_lazy _ (w_pure _ _ _ _ HV7)) | exact RUN11 |]. clear RUN11.
    apply (HK A2 n7 vm2 r11 HV7).
    + apply cs_kept_intro; first [solve [apply gR; in_lit] | (csr; reflexivity)].
    + exact PO7.
    + right. exists pixd, cd, data. split; [csr; reflexivity|]. split; [exact HOKd|].
      unfold pixt_new. repeat (split; [assumption|]). exact (BUILD n7 FP7).
    + room_tac.
Qed.
End WithRop.

End GrayBorderW.
