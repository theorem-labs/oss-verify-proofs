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
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require Import O23LeptPixHdr O23LeptPixCreate O23LeptCmapValid O23LeptCmap2 O23LeptPixCopyA O23LeptPixCopy O23LeptPixCopyAT O23LeptPixCreateT2 O23LeptRop_iface O23LeptRop O23LeptGrayA O23LeptRop2_iface O23LeptRop2 O23LeptRopClip O23LeptRop2C O23LeptBordSegs O23LeptRbord O23LeptRbordW.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptStderr V23LeptBase V23LeptErr V23LeptPixHdr V23LeptPixCreate V23LeptCmapValid V23LeptCmap2 V23LeptPixCopyA V23LeptPixCopy V23LeptPixCopyAT V23LeptPixCreateT2 V23LeptRop_iface V23LeptRop V23LeptGrayA V23LeptRop2_iface V23LeptRop2 V23LeptRop2C V23LeptRbord.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import LeptRoom LeptRoomPC LeptRoom14 LeptRoomBL LeptRop2Arith.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require O23LeptPixCopyT.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require V23LeptPixCreateST V23LeptCloseIface.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require LiaFast.
Local Ltac Stdlib.micromega.Lia.lia ::= first [ solve [LiaFast.flia2] | Zify.zify; xlia zchecker ].
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section RbordW.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V23Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Definition pixRemoveBorderGeneralC_contract : Prop :=
  forall C A m md regs (s pixs w h cm datas left right top bot : Z) (cv : cmapv) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + V23LeptCloseIface.RBG32_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x1381d0 ->
  getr regs 10 = Z_to_bv 64 pixs -> getr regs 11 = Z_to_bv 64 left -> getr regs 12 = Z_to_bv 64 right ->
  getr regs 13 = Z_to_bv 64 top -> getr regs 14 = Z_to_bv 64 bot ->
  PIXat m pixs (O23LeptPixCopyT.hdv (w + left + right) (h + top + bot) 1 cm datas) ->
  hdr_ok (w + left + right) (h + top + bot) 1 -> hdr_ok w h 1 -> (1 <= w)%Z -> (1 <= h)%Z ->
  (left mod 32 = 0)%Z -> (1 <= left <= 64)%Z -> (1 <= right <= 64)%Z -> (1 <= top <= 64)%Z -> (1 <= bot <= 64)%Z ->
  live A (Z_to_bv 64 pixs) = Some 64%Z -> live A (Z_to_bv 64 datas) = Some (4 * (wpl_of (w + left + right) 1 * (h + top + bot)))%Z ->
  (cm = 0%Z \/ (CMAPat m cm cv /\ cmap_ok cv /\ live A (Z_to_bv 64 cm) = Some 24%Z /\ live A (Z_to_bv 64 (c_arr cv)) = Some (4 * c_nalloc cv)%Z)) ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_pixcopy <= kR)%Z -> ((RB_pixT (4 * (wpl_of w 1 * h)) + RB_cmapT cm) <= bR)%Z ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' ->
     (exists pixd cd data, getr regs' 10 = Z_to_bv 64 pixd /\ O23LeptPixCopyT.pixt_new C A A' m' pixd w h 1 cd data cv /\ POSTM C A s m m') ->
     aroom A' vm' (kR - RK_pixcopy) (bR - (RB_pixT (4 * (wpl_of w 1 * h)) + RB_cmapT cm)) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (0x71224 : word) m al_rom) md) S.

Theorem pixRemoveBorderGeneralC_W : pixRemoveBorderGeneralC_contract.
Proof.
  unfold pixRemoveBorderGeneralC_contract.
  intros C A m md regs s pixs w h cm datas left right top bot cv ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 H11 H12 H13 H14
         PXs HOKs HOK Hw Hh Hl32 Hl Hr Ht Hb Lps Lds HCM kR bR Hrm Hrk Hrb HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold V23LeptCloseIface.RBG32_STACK, LSF in *.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof HOKs as (DVs & HwS & HhS & HszS). pose proof HOK as (DV & Hw2 & Hh2 & Hsz).
  pose proof (wpl_of_range w 1 ltac:(lia) DV) as Hwpl.
  pose proof (wpl_of_range (w + left + right) 1 ltac:(lia) DVs) as HwplS.
  pose proof PXs as (Hs0 & Hs64' & WFs & _).
  pose proof (RB_cmapT_le cm) as RBc.
  destruct (blk_range C A m md (Z_to_bv 64 pixs) 64 CK HW Lps ltac:(lia)) as [Gps TOPps]. rewrite u_Z2bv in Gps, TOPps by lia.
  assert (Hs96 : (96 <= s)%Z) by lia. assert (Hs64 : (s < 2 ^ 64)%Z) by lia.
  assert (ALps8 : (pixs mod 8 = 0)%Z) by (pose proof (ai_live_hull A m _ _ _ (w_inv _ _ _ _ HW) Lps) as (_ & X16 & _); rewrite u_Z2bv in X16 by lia; apply mod16_mod8; exact X16).
  destruct (rb_A al_rom regs m s pixs left right top bot (O23LeptPixCopyT.hdv (w + left + right) (h + top + bot) 1 cm datas) ret Hs96 Hs64 Hs16 ltac:(lia) ALps8 PXs ltac:(lia)
              ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia)
              (W_sok_win C A m md (s - 96) 96 CK HW ltac:(lia) ltac:(cbn; lia)) H2 H1 H10 H11 H12 H13 H14)
    as (r1 & RUN1 & Q2 & Q1 & Q10 & Q11 & Q12 & Q8 & Q9 & Q18 & Q19 & Q20 & AG1).
  cbn [p_w p_h p_d O23LeptPixCopyT.hdv] in RUN1, Q10, Q11, Q12, Q19, Q20.
  assert (EW : (w + left + right - left - right = w)%Z) by lia. assert (EH : (h + top + bot - top - bot = h)%Z) by lia.
  rewrite EW in Q10, Q19. rewrite EH in Q11, Q20.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |]. clear RUN1.
  set (M1 := DIMS (FRR m s ret regs) (s - 68) (w + left + right) (h + top + bot) 1) in *.
  assert (WP1 : W C A M1 md /\ POSTM C A s m M1) by (subst M1; unfold DIMS, FRR; wp_win CK).
  destruct WP1 as [HW1 PM1].
  pose proof (rbfr_init m s ret regs (w + left + right) (h + top + bot) 1 Hs96 Hs64) as FR1. fold M1 in FR1.
  assert (OUT1 : forall x : word, ~ (s - 96 <= u x < s)%Z -> M1 x = m x).
  { intros x Hx. subst M1. rewrite DIMS_out by lia. apply FRR_out; lia. }
  assert (Q4 : getr r1 4 = Z_to_bv 64 0x1381d0) by (csr; reflexivity).
  apply (V23LeptPixCreateST.pixCreate_sureT_W C A M1 md r1 (s - 96) w h 1 (Z_to_bv 64 0x712d8) S CK HW1 Q2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(unfold LSF; lia) ltac:(lia) Q1 ltac:(red; apply bv_eq; reflexivity) Q4 Q10 Q11 Q12 Hw Hh HOK
           kR bR Hrm ltac:(room_consts; lia) ltac:(lia)).
  intros A1 m1 vm1 r2 pixd data HWa CSa PMa Hres PN Hrm1.
  replace (Z_to_bv 64 0x712d8) with (0x712d8 : word) by (apply bv_eq; reflexivity).
  destruct PN as (Gp & TOPp & ALp & Gd & TOPd & ALd & NEpd & L0p & L0d & L00p & L00d & L1p & L1d & LEQ & PXd & Edata).
  cbn [p_wpl p_h set_data pix_hdr] in TOPd, L1d.
  change (PIXat m1 pixd (O23LeptPixCopyT.hdv w h 1 0 data)) in PXd.
  assert (PMa' : POSTM C A s m m1) by (eapply POSTM_trans; [exact PM1 | eapply POSTM_mono; [|exact PMa]; lia]).
  pose proof (rbfr_frm C (s - 96) M1 m1 s ret regs (w + left + right) (h + top + bot) 1 CK (proj1 PMa) ltac:(lia) ltac:(lia) Hs96 Hs64 FR1) as FR2.
  assert (Hnd : (0 <= wpl_of w 1 * h)%Z) by (apply Z.mul_nonneg_nonneg; lia).
  assert (NEsp : Z_to_bv 64 pixs <> Z_to_bv 64 pixd) by (intros E; rewrite E in Lps; rewrite Lps in L0p; discriminate).
  assert (NEsd : Z_to_bv 64 pixs <> Z_to_bv 64 data) by (intros E; rewrite E in Lps; rewrite Lps in L0d; discriminate).
  assert (NEdd : Z_to_bv 64 datas <> Z_to_bv 64 data) by (intros E; rewrite E in Lds; rewrite Lds in L0d; discriminate).
  assert (NEpdw : Z_to_bv 64 pixd <> Z_to_bv 64 data) by (apply zbv_ne2; lia).
  assert (SUBa : sub_live A A1) by (eapply sub_live_new2; [exact L0p | exact L0d | exact L1p | exact L1d | exact LEQ]).
  pose proof (SUBa _ _ Lps) as Lps1.
  pose proof (blk_apart C A1 m1 _ _ _ _ _ CK HWa Lps1 L1p NEsp ltac:(lia) ltac:(lia)) as APsp. rewrite !u_Z2bv in APsp by lia.
  assert (PXs1 : PIXat m1 pixs (O23LeptPixCopyT.hdv (w + left + right) (h + top + bot) 1 cm datas)).
  { apply (PIXat_frame m); [exact PXs|]. intros x Hx. rewrite (LIVK_at A M1 m1 pixs 64 x (proj2 PMa) Lps ltac:(lia) ltac:(lia) Hx). apply OUT1. lia. }
  assert (HCM1 : cm = 0%Z \/ (CMAPat m1 cm cv /\ cmap_ok cv /\ live A1 (Z_to_bv 64 cm) = Some 24%Z /\ live A1 (Z_to_bv 64 (c_arr cv)) = Some (4 * c_nalloc cv)%Z)).
  { destruct HCM as [CM0 | (CM & CMOK & Lcm & Larr)]; [left; exact CM0 | right].
    pose proof CM as (Hc0 & Hc64 & _). destruct (blk_range C A m md (Z_to_bv 64 cm) 24 CK HW Lcm ltac:(lia)) as [Gcm TOPcm]. rewrite u_Z2bv in Gcm, TOPcm by lia.
    split; [| split; [exact CMOK | split; [exact (SUBa _ _ Lcm) | exact (SUBa _ _ Larr)]]].
    apply (CMAPat_frame m); [exact CM|]. intros x Hx. rewrite (LIVK_at A M1 m1 cm 24 x (proj2 PMa) Lcm ltac:(lia) ltac:(lia) Hx). apply OUT1. lia. }
  pose proof (blk_sok C A1 m1 _ pixd 64 CK HWa L1p ltac:(lia) ltac:(lia) ltac:(lia)) as SOKd.
  destruct (rb_B1 al_rom r2 m1 pixd pixs ltac:(lia) Hres ltac:(csr; reflexivity)) as (r3 & RUN3 & V1 & V10 & V11 & V21 & AG3).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWa)) | exact (mp_lazy _ (w_pure _ _ _ _ HWa)) | exact RUN3 |]. clear RUN3.
  destruct (pixCopyResolution_run al_rom r3 m1 pixd pixs (O23LeptPixCopyT.hdv (w + left + right) (h + top + bot) 1 cm datas) (O23LeptPixCopyT.hdv w h 1 0 data) (Z_to_bv 64 0x712e8) ltac:(lia) ltac:(lia)
              ltac:(intros E; apply NEsp; rewrite E; reflexivity) ALps8 (mod16_mod8 _ ALp) PXs1 PXd eq_refl eq_refl SOKd ltac:(red; apply bv_eq; reflexivity) V1 V10 V11)
    as (r4 & RUN4 & X10 & AG4).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWa)) | exact (mp_lazy _ (w_pure _ _ _ _ HWa)) | exact RUN4 |]. clear RUN4.
  replace (Z_to_bv 64 0x712e8) with (0x712e8 : word) by (apply bv_eq; reflexivity).
  set (M3 := wbytes m1 (Z_to_bv 64 (pixd + 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))).
  assert (WP3 : W C A1 M3 (with_vmmaps vm1 md) /\ POSTM C A s m M3).
  { subst M3. apply (WP_blk C A A1 m _ _ (Z_to_bv 64 pixd) _ 64); [exact CK | | exact L1p | exact L0p | exact L00p | exact SUBa | rewrite !u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia].
    split; [exact HWa | exact PMa']. }
  destruct WP3 as [HW3 PM3].
  assert (OUT3 : forall x : word, ~ (pixd + 24 <= u x < pixd + 32)%Z -> M3 x = m1 x).
  { intros x Hx. subst M3. apply (wbytes_out_Z _ _ 8); [rewrite length_N_to_le_bytes; reflexivity | lia | lia | lia]. }
  assert (PXd3 : PIXat M3 pixd (O23LeptPixCopyT.hdv w h 1 0 data)) by (subst M3; apply (O23LeptPixCopyT.PIX_wr_res0 _ pixd (O23LeptPixCopyT.hdv w h 1 0 data)); [exact PXd | reflexivity | reflexivity]).
  assert (PXs3 : PIXat M3 pixs (O23LeptPixCopyT.hdv (w + left + right) (h + top + bot) 1 cm datas)) by (apply (PIXat_frame m1); [exact PXs1 | intros x Hx; apply OUT3; lia]).
  pose proof (rbfr_out m1 M3 _ _ s ret regs (w + left + right) (h + top + bot) 1 OUT3 ltac:(lia) Hs96 Hs64 FR2) as FR3.
  destruct (rb_B2 al_rom r4 M3 pixd pixs ltac:(csr; reflexivity) ltac:(csr; reflexivity)) as (r5 & RUN5 & Y1 & Y10 & Y11 & AG5).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW3)) | exact (mp_lazy _ (w_pure _ _ _ _ HW3)) | exact RUN5 |]. clear RUN5.
  destruct (pixCopySpp_run al_rom r5 M3 pixd pixs (O23LeptPixCopyT.hdv (w + left + right) (h + top + bot) 1 cm datas) (O23LeptPixCopyT.hdv w h 1 0 data) (Z_to_bv 64 0x712f4) ltac:(lia) ltac:(lia)
              ltac:(intros E; apply NEsp; rewrite E; reflexivity) ALps8 (mod16_mod8 _ ALp) PXs3 PXd3 (proj1 (spp_of_range 1))
              (blk_sok C A1 M3 _ pixd 64 CK HW3 L1p ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(red; apply bv_eq; reflexivity) Y1 Y10 Y11)
    as (r6 & RUN6 & U10 & AG6).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW3)) | exact (mp_lazy _ (w_pure _ _ _ _ HW3)) | exact RUN6 |]. clear RUN6.
  replace (Z_to_bv 64 0x712f4) with (0x712f4 : word) by (apply bv_eq; reflexivity).
  cbn [p_spp O23LeptPixCopyT.hdv].
  set (M4 := wbytes M3 (Z_to_bv 64 (pixd + 12)) (word_to_le_bytes 4 (Z_to_bv 64 (spp_of 1)))).
  assert (WP4 : W C A1 M4 (with_vmmaps vm1 md) /\ POSTM C A s m M4).
  { subst M4. apply (WP_blk C A A1 m _ _ (Z_to_bv 64 pixd) _ 64); [exact CK | | exact L1p | exact L0p | exact L00p | exact SUBa | rewrite !u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia].
    split; [exact HW3 | exact PM3]. }
  destruct WP4 as [HW4 PM4].
  assert (OUT4 : forall x : word, ~ (pixd + 12 <= u x < pixd + 16)%Z -> M4 x = M3 x).
  { intros x Hx. subst M4. apply (wbytes_out_Z _ _ 4); [rewrite length_N_to_le_bytes; reflexivity | lia | lia | lia]. }
  assert (PXd4 : PIXat M4 pixd (O23LeptPixCopyT.hdv w h 1 0 data)) by (subst M4; exact (O23LeptPixCopyT.PIX_wr_spp_same M3 pixd (O23LeptPixCopyT.hdv w h 1 0 data) PXd3)).
  assert (PXs4 : PIXat M4 pixs (O23LeptPixCopyT.hdv (w + left + right) (h + top + bot) 1 cm datas)) by (apply (PIXat_frame M3); [exact PXs3 | intros x Hx; apply OUT4; lia]).
  pose proof (rbfr_out M3 M4 _ _ s ret regs (w + left + right) (h + top + bot) 1 OUT4 ltac:(lia) Hs96 Hs64 FR3) as FR4.
  assert (HCM4 : cm = 0%Z \/ (CMAPat M4 cm cv /\ cmap_ok cv /\ live A1 (Z_to_bv 64 cm) = Some 24%Z /\ live A1 (Z_to_bv 64 (c_arr cv)) = Some (4 * c_nalloc cv)%Z)).
  { destruct HCM1 as [CM0 | (CM & CMOK & Lcm & Larr)]; [left; exact CM0 | right].
    pose proof CM as (Hc0 & Hc64 & _).
    assert (NEcp : Z_to_bv 64 cm <> Z_to_bv 64 pixd) by (intros E; rewrite E in Lcm; congruence).
    pose proof (blk_apart C A1 m1 _ _ _ _ _ CK HWa Lcm L1p NEcp ltac:(lia) ltac:(lia)) as APcp. rewrite !u_Z2bv in APcp by lia.
    split; [| split; [exact CMOK | split; [exact Lcm | exact Larr]]].
    apply (CMAPat_frame m1); [exact CM|]. intros x Hx. rewrite OUT4 by lia. apply OUT3. lia. }
  destruct (rb_B3 al_rom r6 M4 pixd pixs ltac:(csr; reflexivity) ltac:(csr; reflexivity)) as (r7 & RUN7 & Z1 & Z10 & Z11 & AG7).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW4)) | exact (mp_lazy _ (w_pure _ _ _ _ HW4)) | exact RUN7 |]. clear RUN7.
  apply (pixCopyColormap_szT_W C A A1 M4 _ r7 (s - 96) pixd pixs (O23LeptPixCopyT.hdv w h 1 0 data) (O23LeptPixCopyT.hdv (w + left + right) (h + top + bot) 1 cm datas) cv (Z_to_bv 64 0x71300) S CK HW4 SUBa
           ltac:(csr; reflexivity) ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold LSF; lia) ltac:(lia) Z1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(csr; reflexivity) Z10 Z11 PXd4 PXs4 eq_refl eq_refl ltac:(intros E; apply NEsp; rewrite E; reflexivity) L1p L0p L00p Lps1 HCM4
           (kR - RK_pix) (bR - RB_pixT (4 * (wpl_of w 1 * h))) ltac:(room_tac) ltac:(room_consts; lia) ltac:(cbn [p_cmap O23LeptPixCopyT.hdv]; lia)).
  intros A2 m5 vm2 r8 HWb CSb PMb OUTb Hrm2. rewrite with_vmmaps_twice in HWb |- *.
  replace (Z_to_bv 64 0x71300) with (0x71300 : word) by (apply bv_eq; reflexivity).
  cbn [p_cmap O23LeptPixCopyT.hdv] in Hrm2.
  assert (OUTc : exists cd, PIXat m5 pixd (O23LeptPixCopyT.hdv w h 1 cd data) /\ sub_live A1 A2 /\ O23LeptPixCopyT.cmres C A A2 m5 pixd data cd cv).
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
  assert (L2d : live A2 (Z_to_bv 64 data) = Some (4 * (wpl_of w 1 * h))%Z) by (exact (SUB12 _ _ L1d)).
  assert (PMb' : POSTM C A s m m5) by (eapply POSTM_trans; [exact PM4 | eapply POSTM_mono; [|exact PMb]; lia]).
  pose proof (rbfr_frm C (s - 96) M4 m5 s ret regs (w + left + right) (h + top + bot) 1 CK (proj1 PMb) ltac:(lia) ltac:(lia) Hs96 Hs64 FR4) as FR5.
  assert (PXs5 : PIXat m5 pixs (O23LeptPixCopyT.hdv (w + left + right) (h + top + bot) 1 cm datas)).
  { apply (PIXat_frame M4); [exact PXs4|]. intros x Hx. exact (LIVK_at A M4 m5 pixs 64 x (proj2 PMb) Lps ltac:(lia) ltac:(lia) Hx). }
  destruct (rb_R al_rom r8 m5 s pixd pixs left top w h Hs96 Hs64 (W_sok_win C A2 m5 _ (s - 96) 8 CK HWb ltac:(lia) ltac:(cbn; lia))
              ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity)
              ltac:(csr; reflexivity) ltac:(csr; reflexivity))
    as (r9 & RUN9 & e1 & e10 & e11 & e12 & e13 & e14 & e15 & e16 & e17 & e23 & AG9).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWb)) | exact (mp_lazy _ (w_pure _ _ _ _ HWb)) | exact RUN9 |]. clear RUN9.
  set (N6 := wbytes m5 (Z_to_bv 64 (s - 96)) (word_to_le_bytes 8 (Z_to_bv 64 top))).
  assert (WP6 : W C A2 N6 (with_vmmaps vm2 md) /\ POSTM C A s m N6) by (subst N6; wp_win CK).
  destruct WP6 as [HW6 PM6].
  assert (OUT6 : forall x : word, ~ (s - 96 <= u x < s - 88)%Z -> N6 x = m5 x).
  { intros x Hx. subst N6. apply (wbytes_out_Z _ _ 8); [rewrite length_N_to_le_bytes; reflexivity | clear - Hs96 Hs64; lia | clear - Hs96 Hs64; lia | clear - Hs96 Hs64 Hx; lia]. }
  pose proof (rbfr_out m5 N6 _ _ s ret regs (w + left + right) (h + top + bot) 1 OUT6 ltac:(lia) Hs96 Hs64 FR5) as FR6.
  assert (PXd6 : PIXat N6 pixd (O23LeptPixCopyT.hdv w h 1 cd data)) by (apply (PIXat_frame m5); [exact PXd5 | intros x Hx; apply OUT6; lia]).
  assert (PXs6 : PIXat N6 pixs (O23LeptPixCopyT.hdv (w + left + right) (h + top + bot) 1 cm datas)) by (apply (PIXat_frame m5); [exact PXs5 | intros x Hx; apply OUT6; lia]).
  assert (CD0 : clip_d 0 left = 0%Z) by (unfold clip_d; lia).
  assert (CS0 : clip_s 0 left = left) by (unfold clip_s; lia).
  replace (0x7f13c : word) with (Z_to_bv 64 PC_pixRasterop) by (apply bv_eq; reflexivity).
  apply (pixRasterop_srcclip_W C A A2 N6 _ r9 (s - 96)%Z pixd 0%Z 0%Z w h pixs left top (O23LeptPixCopyT.hdv w h 1 cd data) (O23LeptPixCopyT.hdv (w + left + right) (h + top + bot) 1 cm datas) (Z_to_bv 64 0x7132c) S CK HW6 SUBb
           ltac:(csr; reflexivity) ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ROP_STACK; lia) ltac:(lia)
           e1 ltac:(red; apply bv_eq; reflexivity) e10 e11 e12 e13 e14 e15 e16 e17
           ltac:(subst N6; apply (rdn_wbytes_hit8 SEGS); rewrite u_Z2bv by lia; lia)
           PXd6 PXs6 eq_refl eq_refl (hdr_rop_shape1 w h HOK Hw Hh) (hdr_rop_shape1 (w + left + right) (h + top + bot) HOKs ltac:(lia) ltac:(lia))
           ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
           ltac:(unfold rop2_clip_arm; left; rewrite CD0, CS0; split; [reflexivity | exact Hl32])
           L2p (SUBb _ _ Lps) NEpdw NEsd L2d L0d L00d (SUBb _ _ Lds) NEdd).
  intros n7 q7 HV7 CS7 PN7 PXe7 PXse7 KEEP7 R10_7.
  replace (Z_to_bv 64 0x7132c) with (0x7132c : word) by (apply bv_eq; reflexivity).
  assert (PO7 : POSTM C A s m n7) by (eapply POSTM_trans; [exact PM6 | eapply POSTM_mono; [|exact PN7]; lia]).
  pose proof (rbfr_frm C (s - 96) N6 n7 s ret regs (w + left + right) (h + top + bot) 1 CK (proj1 PN7) ltac:(lia) ltac:(lia) Hs96 Hs64 FR6) as (CE7 & _).
  destruct (rb_D al_rom q7 n7 pixs pixd (O23LeptPixCopyT.hdv (w + left + right) (h + top + bot) 1 cm datas) ltac:(lia) ALps8 PXse7 ltac:(cbn; left; reflexivity)
              ltac:(csr; reflexivity) ltac:(csr; reflexivity))
    as (r10 & RUN10 & f10 & AG10).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HV7)) | exact (mp_lazy _ (w_pure _ _ _ _ HV7)) | exact RUN10 |]. clear RUN10.
  destruct (rb_E al_rom r10 regs n7 s ret Hs96 Hs64 Hret CE7 ltac:(csr; reflexivity)) as (r11 & RUN11 & g2 & g1 & gR & AG11).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HV7)) | exact (mp_lazy _ (w_pure _ _ _ _ HV7)) | exact RUN11 |]. clear RUN11.
  apply (HK A2 n7 vm2 r11 HV7).
  - apply cs_kept_intro; first [solve [apply gR; in_lit] | (csr; reflexivity)].
  - exists pixd, cd, data. split; [csr; reflexivity|]. split; [| exact PO7].
    unfold O23LeptPixCopyT.pixt_new. do 13 (split; [assumption|]). split; [exact PXe7|].
    destruct CMR5 as [CL0 | (ad & CMOK & Gcd & TOPcd & Gad & TOPad & N1 & N2 & N3 & N4 & N5 & L0cd & L0ad & L00cd & L00ad & L2cd & L2ad & CM5 & LEQ5)];
      [left; exact CL0 | right].
    exists ad. do 16 (split; [assumption|]). split; [| exact LEQ5].
    apply (CMAPat_frame m5); [exact CM5|].
    pose proof CM5 as (Hcd0 & Hcd64 & _).
    assert (NWcd : Z_to_bv 64 cd <> Z_to_bv 64 data) by (apply zbv_ne2; lia).
    pose proof (blk_apart C A2 n7 _ _ _ _ _ CK HV7 L2cd L2d NWcd ltac:(lia) ltac:(lia)) as APcd. rewrite !u_Z2bv in APcd by lia.
    cbn [p_data p_wpl p_h O23LeptPixCopyT.hdv] in KEEP7.
    intros x Hx. apply (keepK_stepR C (fun a : word => (cd <= bv_unsigned a < cd + 24)%Z) s data (4 * (wpl_of w 1 * h)) m5 N6 n7); [| exact OUT6 | lia | exact KEEP7 | exact Hx].
    intros a Ha. unfold scratch. split; lia.
  - room_tac.
Qed.

(* [comment removed for export] *)
Theorem pixRemoveBorder32_W : V23LeptCloseIface.pixRemoveBorder32_contract.
Proof.
  unfold V23LeptCloseIface.pixRemoveBorder32_contract.
  intros C A m md regs s pixs w h cm datas cv ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 H11 PXs HOKs HOK Hw Hh Lps Lds HCM kR bR Hrm Hrk Hrb HK.
  pose proof PXs as (Hs0 & Hs64' & _).
  destruct (blk_range C A m md (Z_to_bv 64 pixs) 64 CK HW Lps ltac:(lia)) as [Gps TOPps]. rewrite u_Z2bv in Gps, TOPps by lia.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  destruct (rbw_A al_rom regs m pixs 32 ltac:(lia) ltac:(lia) H10 H11) as (r1 & RUN1 & Q12 & Q13 & Q14 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |]. clear RUN1.
  assert (EW : (w + 64 = w + 32 + 32)%Z) by lia. assert (EH : (h + 64 = h + 32 + 32)%Z) by lia.
  rewrite EW, EH in PXs, HOKs, Lds.
  apply (pixRemoveBorderGeneralC_W C A m md r1 s pixs w h cm datas 32%Z 32%Z 32%Z 32%Z cv ret S CK HW ltac:(csr; reflexivity) Hs16 Hlo Hhi
           ltac:(csr; reflexivity) Hret ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity) Q12 Q13 Q14
           PXs HOKs HOK Hw Hh eq_refl ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Lps Lds HCM kR bR Hrm Hrk Hrb).
  intros A' m' vm' regs' HW' CS' EX' RM'.
  apply (HK A' m' vm' regs' HW'); [| exact EX' | exact RM'].
  apply cs_kept_intro; csr; reflexivity.
Qed.
End RbordW.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
