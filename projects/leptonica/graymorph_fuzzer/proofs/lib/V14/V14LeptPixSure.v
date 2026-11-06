(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.graymorph_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptArith2.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.V14 Require Import V14LeptStderr V14LeptBase V14LeptUb.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.V14 Require Import V14CL7a.
Import V14CL7a.V14LeptErr.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.V14 Require Import V14LeptPixHdr V14LeptPixCreate V14LeptPadBitsW V14LeptCmapValid V14LeptCmap2 V14LeptPixCopyA V14LeptPixCopy.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.V14 Require Import V14Kit.
Import V14Kit.V14MemcpyBase. Import V14Kit.V14Memcpy. Import V14Kit.V14Memset.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.V14 Require Import V14_code_15000_16000 V14_code_16000_17000 V14_code_17000_18000 V14_code_30000_31000 V14_code_31000_317ac.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica Require Import LeptRoom LeptRoomPC.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica Require Import LeptRoom14.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section PixSure.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V14Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Theorem pixCreateHeader_sure_W : forall C A m md regs (s w h d : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 48 + LSF <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x44140 ->
  getr regs 10 = Z_to_bv 64 w -> getr regs 11 = Z_to_bv 64 h -> getr regs 12 = Z_to_bv 64 d ->
  (1 <= w <= 1000000)%Z -> (1 <= h <= 1000000)%Z -> (w * h <= 400000000)%Z -> (0 <= d < 2 ^ 64)%Z ->
  hdr_ok w h d ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_hdr <= kR)%Z -> (RB_hdr <= bR)%Z ->
  (forall A' m' vm' regs' pix, W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A s m m' ->
     getr regs' 10 = Z_to_bv 64 pix -> pix_new C A A' m' pix (pix_hdr w h d) ->
     aroom A' vm' (kR - RK_hdr) (bR - RB_hdr) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (0x15984 : word) m al_rom) md) S.
Proof.
  intros C A m md regs s w h d ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 H11 H12 Hw Hh Hwh Hd HOKs kR bR Hrm Hrk Hrb HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold LSF in *.
  pose proof (W_sok_win C A m md (s - 48) 48 CK HW ltac:(lia) ltac:(cbn; lia)) as SOK.
  assert (RR0 : forall x, In x cs_rest -> getr regs x = getr regs x) by (intros; reflexivity).
  assert (DV : dval d) by exact (proj1 HOKs).
  { (* [comment removed for export] *)
    pose proof (dval_range d DV) as Hd32. pose proof (wpl_of_range w d ltac:(lia) DV) as Hwpl.
    destruct (ph_A al_rom regs m s w h d ret ltac:(lia) ltac:(lia) Hd DV SOK H2 H1 H10 H11 H12) as (r1 & RUN1 & Q2 & Q10 & Q11 & Q12 & AG1).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
    assert (WP1 : W C A (V14LeptPixHdr.FR6 m s ret regs) md /\ POSTM C A s m (V14LeptPixHdr.FR6 m s ret regs)) by (unfold V14LeptPixHdr.FR6; wp_win CK).
    destruct WP1 as [HW1 PM1]. set (M1 := V14LeptPixHdr.FR6 m s ret regs) in *.
    pose proof (V14LeptPixHdr.cells6_FR6 m s ret regs ltac:(lia) ltac:(lia)) as CE1. fold M1 in CE1.
    destruct (ph_B al_rom r1 M1 s w h d Hw Hh Hwh DV Q10 Q11 Q12) as (r2 & RUN2 & P13 & P14 & P8 & P10 & P11 & P12 & AG2).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN2 |].
    assert (RR2 : forall x, In x [3; 4; 18; 19; 21; 22; 23; 24; 25; 26; 27]%bv -> getr r2 x = getr regs x) by (unfold cs_rest in RR0; rest_solve).
    assert (P2 : getr r2 2 = Z_to_bv 64 (s - 48)) by (csr; reflexivity).
    assert (Hszhi : (4 * (wpl_of w d * h) < 2 ^ 64)%Z) by nia.
    destruct (Z_lt_ge_dec 67108864 (4 * (wpl_of w d * h))) as [BIG|SMALL].
    { exfalso. clear - BIG HOKs. destruct HOKs as (_ & X1 & X2 & X3). lia. }
    destruct (ph_C al_rom r2 M1 (4 * (wpl_of w d * h)) ltac:(lia) P13 P14) as (r3 & RUN3 & V13 & AG3).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN3 |].
    assert (RR3 : forall x, In x [3; 4; 18; 19; 21; 22; 23; 24; 25; 26; 27]%bv -> getr r3 x = getr regs x) by rest_solve.
    assert (V10 : getr r3 10 = Z_to_bv 64 w) by (csr; reflexivity).
    assert (V11 : getr r3 11 = Z_to_bv 64 h) by (csr; reflexivity).
    assert (V12 : getr r3 12 = Z_to_bv 64 d) by (csr; reflexivity).
    assert (V2 : getr r3 2 = Z_to_bv 64 (s - 48)) by (csr; reflexivity).
    destruct (Z_lt_ge_dec 20000 w) as [WBIG|WOK].
    { exfalso. clear - WBIG HOKs. destruct HOKs as (_ & X1 & X2 & X3). lia. }
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact (ph_D al_rom r3 M1 w ltac:(lia) V10 V13) |].
    destruct (Z_lt_ge_dec 20000 h) as [HBIG|HOK].
    { exfalso. clear - HBIG HOKs. destruct HOKs as (_ & X1 & X2 & X3). lia. }
    (* [comment removed for export] *)
    destruct (ph_E al_rom r3 M1 w h d ltac:(lia) V10 V11 V12 V13) as (r4 & RUN4 & X10 & X11 & X1 & X19 & X9 & X8 & AG4).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN4 |].
    assert (X4 : getr r4 4 = Z_to_bv 64 0x44140) by (csr; reflexivity).
    assert (X2 : getr r4 2 = Z_to_bv 64 (s - 48)) by (csr; reflexivity).
    assert (X20 : getr r4 20 = Z_to_bv 64 (wpl_of w d)) by (csr; reflexivity).
    replace (0x2a0e8 : word) with (Z_to_bv 64 0x2a0e8) by (apply bv_eq; reflexivity).
    apply (W_calloc16_sure C A M1 md r4 1 64 kR bR (Z_to_bv 64 0x15c10) (s - 48) S CK HW1 X10 X11 ltac:(lia) ltac:(lia) ltac:(lia) Hrm ltac:(room_consts; lia)
             ltac:(pose proof (alloc_margin_le (1 * 64)); room_consts; lia) ltac:(unfold ROOM_NMAX; lia) X1
             ltac:(red; apply bv_eq; reflexivity) X4 X2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
             ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)).
    intros A1 m1 vm1 r5 res HWa Hres CSa Hnz L0 L1 L00 LEQ ZERO AL16 TOP PMa HRTa.
    replace (Z_to_bv 64 0x15c10) with (0x15c10 : word) by (apply bv_eq; reflexivity).
    assert (PMa' : POSTM C A s m m1) by (eapply POSTM_trans; [exact PM1 | eapply POSTM_mono; [|exact PMa]; lia]).
    pose proof (V14LeptPixHdr.cells6_frm C (s - 48) M1 m1 s _ _ _ _ _ _ CK (proj1 PMa) ltac:(lia) ltac:(lia) ltac:(lia) CE1) as CE2.
    { (* [comment removed for export] *)
      assert (Hpx : (4096 <= u res)%Z /\ (u res + 64 <= alloc_top (c_vm C))%Z).
      { destruct (blk_range C A1 m1 _ res (1 * 64) CK HWa L1 ltac:(lia)) as [G1 G2]. lia. }
      pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
      assert (Eres : res = Z_to_bv 64 (u res)) by (symmetry; apply zbv_self).
      set (pix := u res) in *. clearbody pix.
      rewrite Eres in Hres, L0, L1, L00, LEQ, ZERO.
      assert (PX0 : PIXat m1 pix pix0).
      { apply PIXat_zero; [lia | lia |]. intros i Hi. unfold at_ in ZERO. rewrite u_Z2bv in ZERO by lia. apply ZERO. lia. }
      destruct CE2 as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6).
      assert (Y19 : getr r5 19 = Z_to_bv 64 w) by (csr; reflexivity).
      assert (Y9 : getr r5 9 = Z_to_bv 64 h) by (csr; reflexivity).
      assert (Y8 : getr r5 8 = Z_to_bv 64 d) by (csr; reflexivity).
      assert (Y20 : getr r5 20 = Z_to_bv 64 (wpl_of w d)) by (csr; reflexivity).
      assert (Y2 : getr r5 2 = Z_to_bv 64 (s - 48)) by (csr; reflexivity).
      assert (AL8 : (pix mod 8 = 0)%Z) by (rewrite <- (Z.add_0_r pix); apply mod16_plus_mod8; [exact AL16 | reflexivity]).
      destruct (ph_F al_rom r5 m1 s w h d pix (wpl_of w d) ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) ltac:(lia) ltac:(lia) Hret DV ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) AL8)
        as (r6 & RUN6 & V2' & V10' & V1' & V8' & V9' & V18' & V19' & V20' & AG6).
      { rewrite <- p16_segs. apply store_ok_of_all; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx.
        unfold wview. destruct (m1 x) eqn:E; [discriminate|]. exfalso. exact (PIXat_defined m1 pix pix0 x PX0 ltac:(lia) E). }
      { exact Z1. } { exact Z2. } { exact Z3. } { exact Z4. } { exact Z5. } { exact Z6. }
      { exact Y2. } { exact Hres. } { exact Y19. } { exact Y9. } { exact Y8. } { exact Y20. }
      eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWa)) | exact (mp_lazy _ (w_pure _ _ _ _ HWa)) | exact RUN6 |].
      assert (SUBa : sub_live A A1) by (eapply sub_live_new; eassumption).
      match goal with |- realizes _ (mkCfg (mkst _ _ ?MM _) _) _ => set (M7 := MM) end.
      assert (WP7 : W C A1 M7 (with_vmmaps vm1 md) /\ POSTM C A s m M7).
      { subst M7.
        repeat (apply (WP_blk C A A1 m _ _ (Z_to_bv 64 pix) _ 64); [exact CK | | exact L1 | exact L0 | exact L00 | exact SUBa | rewrite !u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia]).
        split; [exact HWa | exact PMa']. }
      destruct WP7 as [HW7 PM7].
      pose proof (spp_of_range d) as Hspp.
      assert (PX7 : PIXat M7 pix (pix_hdr w h d)).
      { subst M7. unfold pix_hdr.
        apply (PIX_wr_fmt _ pix (PIXV w h d (spp_of d) (wpl_of w d) 1 0 0 0 0 0 0 0) 0); [|lia].
        apply (PIX_wr_rc _ pix (PIXV w h d (spp_of d) (wpl_of w d) 0 0 0 0 0 0 0 0) 1); [|lia].
        apply (PIX_wr_spp _ pix (PIXV w h d 0 (wpl_of w d) 0 0 0 0 0 0 0 0) (spp_of d)); [|lia].
        apply (PIX_wr_wpl _ pix (PIXV w h d 0 0 0 0 0 0 0 0 0 0) (wpl_of w d)); [|lia].
        apply (PIX_wr_d _ pix (PIXV w h 0 0 0 0 0 0 0 0 0 0 0) d); [|lia].
        apply (PIX_wr_h _ pix (PIXV w 0 0 0 0 0 0 0 0 0 0 0 0) h); [|lia].
        apply (PIX_wr_w _ pix pix0 w); [exact PX0|lia]. }
      apply (HK A1 M7 vm1 r6 pix HW7).
      * apply cs_kept_of_rest; [csr; reflexivity | csr; reflexivity | csr; reflexivity |]. rest_solve.
      * exact PM7.
      * exact V10'.
      * unfold pix_new. do 7 (split; [first [assumption | lia] |]). exact PX7.
      * pose proof (alloc_margin_le (1 * 64)). room_tac.
  }
    }
Qed.

Theorem pixCreateNoInit_sure_W : forall C A m md regs (s w h d : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 96 + LSF <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x44140 ->
  getr regs 10 = Z_to_bv 64 w -> getr regs 11 = Z_to_bv 64 h -> getr regs 12 = Z_to_bv 64 d ->
  (1 <= w <= 1000000)%Z -> (1 <= h <= 1000000)%Z -> (w * h <= 400000000)%Z -> (0 <= d < 2 ^ 64)%Z ->
  hdr_ok w h d ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_pix <= kR)%Z -> (RB_pix14 <= bR)%Z ->
  (forall A' m' vm' regs' pix data, W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A s m m' ->
     getr regs' 10 = Z_to_bv 64 pix -> pixr_new C A A' m' pix data (set_data (pix_hdr w h d) data) ->
     aroom A' vm' (kR - RK_pix) (bR - RB_pix14) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (0x1583c : word) m al_rom) md) S.
Proof.
  intros C A m md regs s w h d ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 H11 H12 Hw Hh Hwh Hd HOKs kR bR Hrm Hrk Hrb HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold LSF in *.
  pose proof (W_sok_win C A m md (s - 32) 32 CK HW ltac:(lia) ltac:(cbn; lia)) as SOK.
  destruct (pn_A al_rom regs m s w h d ret ltac:(lia) ltac:(lia) SOK H2 H1 H10 H11 H12) as (r1 & RUN1 & Q2 & Q1 & Q10 & Q11 & Q12 & Q9 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  assert (WP1 : W C A (V14LeptPixCreate.FR4 m s ret regs) md /\ POSTM C A s m (V14LeptPixCreate.FR4 m s ret regs)) by (unfold V14LeptPixCreate.FR4; wp_win CK).
  destruct WP1 as [HW1 PM1]. set (M1 := V14LeptPixCreate.FR4 m s ret regs) in *.
  pose proof (V14LeptPixCreate.cells4_FR4 m s ret regs ltac:(lia) ltac:(lia)) as CE1. fold M1 in CE1.
  assert (Q4 : getr r1 4 = Z_to_bv 64 0x44140) by (csr; reflexivity).
  apply (pixCreateHeader_sure_W C A M1 md r1 (s - 32) w h d (Z_to_bv 64 0x15854) S CK HW1 Q2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(unfold LSF; lia) ltac:(lia) Q1 ltac:(red; apply bv_eq; reflexivity) Q4 Q10 Q11 Q12 Hw Hh Hwh Hd HOKs kR bR Hrm ltac:(room_consts; lia) ltac:(room_consts; lia)).
  intros A1 m1 vm1 r2 pix HWa CSa PMa Hres PN HRTa. pose proof HOKs as HOK.
  replace (Z_to_bv 64 0x15854) with (0x15854 : word) by (apply bv_eq; reflexivity).
  assert (PMa' : POSTM C A s m m1) by (eapply POSTM_trans; [exact PM1 | eapply POSTM_mono; [|exact PMa]; lia]).
  pose proof (V14LeptPixCreate.cells4_frm C (s - 32) M1 m1 s _ _ _ CK (proj1 PMa) ltac:(lia) ltac:(lia) ltac:(lia) CE1) as CE2.
  assert (E2 : getr r2 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
  assert (E9 : getr r2 9 = Z_to_bv 64 h) by (csr; reflexivity).
  assert (E4 : getr r2 4 = Z_to_bv 64 0x44140) by (csr; reflexivity).
  { (* [comment removed for export] *)
    destruct HOK as (DV & Hw2 & Hh2 & Hsz). destruct PN as (Gp & TOPp & ALp & L0 & L00 & L1 & LEQ & PX1).
    pose proof (dval_range d DV) as Hd32. pose proof (wpl_of_range w d ltac:(lia) DV) as Hwpl.
    pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
    assert (AL8 : (pix mod 8 = 0)%Z) by (rewrite <- (Z.add_0_r pix); apply mod16_plus_mod8; [exact ALp | reflexivity]).
    destruct (pn_B al_rom r2 m1 s h pix (pix_hdr w h d) PX1 eq_refl ltac:(lia) ltac:(cbn; lia) Gp AL8 (W_pmm_malloc C A1 m1 _ HWa) Hres E9)
      as (r3 & RUN3 & V10 & V1 & V8 & V9 & AG3).
    cbn [p_wpl pix_hdr] in V10.
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWa)) | exact (mp_lazy _ (w_pure _ _ _ _ HWa)) | exact RUN3 |].
    assert (V4 : getr r3 4 = Z_to_bv 64 0x44140) by (csr; reflexivity).
    assert (V2 : getr r3 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
    replace (0x2a360 : word) with (Z_to_bv 64 0x2a360) by (apply bv_eq; reflexivity).
    apply (W_malloc16_sure C A1 m1 _ r3 (4 * (wpl_of w d * h)) (kR - RK_hdr) (bR - RB_hdr) (Z_to_bv 64 0x1588c) (s - 32) S CK HWa V10 ltac:(lia)
             ltac:(rewrite with_vmmaps_vmmaps; exact HRTa) ltac:(room_consts; lia)
             ltac:(pose proof (alloc_margin_le (4 * (wpl_of w d * h))); room_consts; lia) ltac:(unfold ROOM_NMAX; lia) V1
             ltac:(red; apply bv_eq; reflexivity) V4 V2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)).
    intros A2 m2 vm2 r4 res HWb Hres2 CSb Hnz K0 K1 K00 KEQ AL16 TOP PMb HRTb. rewrite with_vmmaps_twice. rewrite with_vmmaps_twice in HWb.
    replace (Z_to_bv 64 0x1588c) with (0x1588c : word) by (apply bv_eq; reflexivity).
    assert (SUBa : sub_live A A1) by (eapply sub_live_new; eassumption).
    assert (PMb' : POSTM C A s m m2).
    { eapply POSTM_trans; [exact PMa'|]. apply (POSTM_sub C A A1 _ _ _ SUBa). eapply POSTM_mono; [|exact PMb]. lia. }
    pose proof (V14LeptPixCreate.cells4_frm C (s - 32) m1 m2 s _ _ _ CK (proj1 PMb) ltac:(lia) ltac:(lia) ltac:(lia) CE2) as CE3.
    assert (PX2 : PIXat m2 pix (pix_hdr w h d)).
    { apply (PIXat_frame m1); [exact PX1|]. intros x Hx. pose proof (proj2 PMb (Z_to_bv 64 pix) 64%Z (u x - pix)%Z L1 ltac:(lia)) as E.
      unfold at_ in E. rewrite u_Z2bv in E by lia. replace (pix + (u x - pix))%Z with (u x) in E by lia. rewrite zbv_self in E. exact E. }
    assert (X8 : getr r4 8 = Z_to_bv 64 pix) by (csr; reflexivity).
    assert (X2 : getr r4 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
    assert (X4 : getr r4 4 = Z_to_bv 64 0x44140) by (csr; reflexivity).
    assert (SOKp : store_ok SEGS m2 (Z_to_bv 64 pix) 64 = true).
    { rewrite <- p16_segs. apply store_ok_of_all; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx.
      unfold wview. destruct (m2 x) eqn:E; [discriminate|]. exfalso. exact (PIXat_defined m2 pix _ x PX2 ltac:(lia) E). }
    { (* [comment removed for export] *)
      assert (Hdat : (4096 <= u res)%Z /\ (u res + 4 * (wpl_of w d * h) <= alloc_top (c_vm C))%Z).
      { destruct (blk_range C A2 m2 _ res _ CK HWb K1 ltac:(lia)) as [G1 G2]. lia. }
      assert (Eres : res = Z_to_bv 64 (u res)) by (symmetry; apply zbv_self).
      set (data := u res) in *. clearbody data.
      rewrite Eres in Hres2, K0, K1, K00, KEQ.
      assert (NEpd : Z_to_bv 64 pix <> Z_to_bv 64 data) by (intros E; rewrite E in L1; congruence).
      assert (NEpd' : pix <> data) by (intros E; apply NEpd; rewrite E; reflexivity).
      assert (Lp2 : live A2 (Z_to_bv 64 pix) = Some 64%Z) by (rewrite (KEQ _ NEpd); exact L1).
      assert (LAd : live A (Z_to_bv 64 data) = None) by (rewrite <- (LEQ _ (not_eq_sym NEpd)); exact K0).
      assert (SUBb : sub_live A A2) by (eapply sub_live_trans; [exact SUBa | eapply sub_live_new; eassumption]).
      destruct (pn_C al_rom r4 m2 pix data Gp ltac:(lia) ltac:(lia) SOKp Hres2 X8) as (r5 & RUN5 & Y10 & Y11 & Y1 & Y8 & AG5).
      eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWb)) | exact (mp_lazy _ (w_pure _ _ _ _ HWb)) | exact RUN5 |].
      match goal with |- realizes _ (mkCfg (mkst _ _ ?MM _) _) _ => set (M3 := MM) end.
      assert (WP3 : W C A2 M3 (with_vmmaps vm2 md) /\ POSTM C A s m M3).
      { subst M3. apply (WP_blk C A A2 m _ _ (Z_to_bv 64 pix) _ 64); [exact CK | | exact Lp2 | exact L0 | exact L00 | exact SUBb | rewrite !u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia].
        split; [exact HWb | exact PMb']. }
      destruct WP3 as [HW3 PM3].
      assert (PX3 : PIXat M3 pix (set_data (pix_hdr w h d) data)) by (subst M3; apply PIX_wr_data; [exact PX2 | lia]).
      assert (Y2 : getr r5 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
      apply (padbits_W C A A2 M3 _ r5 (s - 32) pix (set_data (pix_hdr w h d) data) (Z_to_bv 64 0x158a0) S CK HW3 SUBb Y2
               ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold LSF; lia) ltac:(lia) Y1 ltac:(red; apply bv_eq; reflexivity) Y10 Y11
               PX3 DV ltac:(cbn; lia) ltac:(cbn; lia) eq_refl Lp2).
      { cbn. exact K1. } { cbn. exact LAd. } { cbn. exact K00. } { cbn. exact NEpd. }
      intros m5 r6 HW5 CS5 PM5 PX5 OUT5 A10.
      replace (Z_to_bv 64 0x158a0) with (0x158a0 : word) by (apply bv_eq; reflexivity).
      assert (CE5 : V14LeptPixCreate.cells4 m5 s ret (getr regs 8) (getr regs 9)).
      { apply (V14LeptPixCreate.cells4_frm C (s - 32) M3 m5 s); [exact CK | exact (proj1 PM5) | lia | lia | lia |].
        subst M3. destruct CE3 as (C1 & C2 & C3). unfold V14LeptPixCreate.cells4. repeat split; repeat rdn_peel1; assumption. }
      destruct CE5 as (C1 & C2 & C3).
      assert (W2 : getr r6 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
      assert (W8 : getr r6 8 = Z_to_bv 64 pix) by (csr; reflexivity).
      destruct (pn_D al_rom r6 m5 s pix ret _ _ ltac:(lia) ltac:(lia) Hret C1 C2 C3 W2 W8) as (r7 & RUN7 & U2 & U1 & U10 & U8 & U9 & AG7).
      eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW5)) | exact (mp_lazy _ (w_pure _ _ _ _ HW5)) | exact RUN7 |].
      apply (HK A2 m5 vm2 r7 pix data HW5).
      * apply cs_kept_intro; csr; try reflexivity.
      * eapply POSTM_trans; [exact PM3 | eapply POSTM_mono; [|exact PM5]; lia].
      * exact U10.
      * unfold pixr_new. cbn [p_wpl p_h p_data set_data pix_hdr].
        do 15 (try (split; [first [assumption | lia | idtac] |])).
        all: try assumption; try lia; try reflexivity.
        all: intros q N1 N2; rewrite (KEQ q N2); apply LEQ; exact N1.
      * pose proof (alloc_margin_le (4 * (wpl_of w d * h))). room_consts.
        apply (aroom_mono A2 vm2 _ _ _ _ HRTb); lia.
  }
    }
Qed.

(* [comment removed for export] *)
Definition TKs (C : lctx) (A : AS) (m : word -> option byte) (md : Model) (regs : bvmap 5 word) (s w h d : Z) (cv : cmapv) (ret : word) (S : TSet) (kR bR : Z) : Prop :=
  forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A s m m' ->
     (exists pixd cd data, getr regs' 10 = Z_to_bv 64 pixd /\ pixt_new C A A' m' pixd w h d cd data cv) ->
     aroom A' vm' (kR - RK_pixcopy) (bR - RB_pixcopy14) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S.

Lemma ptn_tail_sure_W : forall C A A2 m md m4 vm2 regs r4 (s pixs pixd w h d cm datas cd data : Z) (cv : cmapv) (ret : word) (S : TSet) (kR bR : Z),
  Cok C -> TKs C A m md regs s w h d cv ret S kR bR ->
  aroom A2 vm2 (kR - RK_pixcopy) (bR - RB_pixcopy14) ->
  (s mod 16 = 0)%Z -> (c_top C - LSTK + 128 + 16 + LSF <= s)%Z -> (s <= c_top C)%Z -> ret_ok ret ->
  W C A2 m4 (with_vmmaps vm2 md) -> POSTM C A s m m4 -> sub_live A A2 ->
  V14LeptPixCopy.cells4 m4 s ret (getr regs 8) (getr regs 9) (getr regs 18) ->
  getr r4 2 = Z_to_bv 64 (s - 32) -> getr r4 8 = Z_to_bv 64 pixd -> getr r4 9 = Z_to_bv 64 pixs ->
  (forall x, In x V14LeptPixCopy.tn_rest -> getr r4 x = getr regs x) -> getr regs 2 = Z_to_bv 64 s ->
  PIXat m4 pixs (hdv w h d cm datas) -> live A (Z_to_bv 64 pixs) = Some 64%Z ->
  hdr_ok w h d -> (1 <= w)%Z -> (1 <= h)%Z ->
  (4096 <= pixd)%Z -> (pixd + 64 <= alloc_top (c_vm C))%Z -> (pixd mod 16 = 0)%Z ->
  (4096 <= data)%Z -> (data + 4 * (wpl_of w d * h) <= alloc_top (c_vm C))%Z -> (data mod 16 = 0)%Z -> pixd <> data ->
  live A (Z_to_bv 64 pixd) = None -> live A (Z_to_bv 64 data) = None ->
  live (c_A0 C) (Z_to_bv 64 pixd) = None -> live (c_A0 C) (Z_to_bv 64 data) = None ->
  live A2 (Z_to_bv 64 pixd) = Some 64%Z -> live A2 (Z_to_bv 64 data) = Some (4 * (wpl_of w d * h))%Z ->
  PIXat m4 pixd (hdv w h d cd data) -> cmres C A A2 m4 pixd data cd cv ->
  realizes SEGS (mkCfg (mkst r4 (0x15fc0 : word) m4 al_rom) (with_vmmaps vm2 md)) S.
Proof.
  intros C A A2 m md m4 vm2 regs r4 s pixs pixd w h d cm datas cd data cv ret S kR bR CK HK Hrm2 Hs16 Hlo Hhi Hret HW4 PM4 SUB CE4 R2 R8 R9 RR H2 PXs Lps HOK Hw Hh
         Gp TOPp ALp Gd TOPd ALd NEpd LAp LAd L00p L00d L2p L2d PXd CMR.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold LSF in *.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  destruct HOK as (DV & Hw2 & Hh2 & Hsz). pose proof (dval_range d DV) as Hd32. pose proof (wpl_of_range w d ltac:(lia) DV) as Hwpl.
  pose proof PXs as (Hs0 & Hs64' & WFs & _).
  pose proof (SUB _ _ Lps) as Lps2.
  destruct (blk_range C A2 m4 _ (Z_to_bv 64 pixs) 64 CK HW4 Lps2 ltac:(lia)) as [Gps TOPps]. rewrite u_Z2bv in Gps, TOPps by lia.
  assert (NEsp : Z_to_bv 64 pixs <> Z_to_bv 64 pixd) by (intros E; rewrite E in Lps; rewrite Lps in LAp; discriminate).
  pose proof (blk_apart C A2 m4 _ _ _ _ _ CK HW4 Lps2 L2p NEsp ltac:(lia) ltac:(lia)) as APsp. rewrite !u_Z2bv in APsp by lia.
  destruct (ptn_C al_rom r4 m4 s pixs pixd (hdv w h d cm datas) (hdv w h d cd data) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ALp PXs PXd
              eq_refl eq_refl eq_refl APsp ltac:(lia) ltac:(lia) (blk_sok C A2 m4 _ pixd 64 CK HW4 L2p ltac:(lia) ltac:(lia) ltac:(lia))
              (W_sok_win C A2 m4 _ (s - 64) 32 CK HW4 ltac:(lia) ltac:(cbn; lia)) R2 R8 R9)
    as (r5 & RUN5 & Y2 & Y1 & Y10 & Y11 & Y8 & Y9 & AG5).
  apply box_i in APsp.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW4)) | exact (mp_lazy _ (w_pure _ _ _ _ HW4)) | exact RUN5 |].
  set (Mw := wbytes (wbytes (wbytes m4 (Z_to_bv 64 (s - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0x15fcc)))
                            (Z_to_bv 64 (s - 48)) (word_to_le_bytes 8 (Z_to_bv 64 pixd)))
                            (Z_to_bv 64 (s - 56)) (word_to_le_bytes 8 (Z_to_bv 64 pixs))).
  set (M5 := wbytes (wbytes Mw (Z_to_bv 64 (pixd + 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (pixd + 32)) (word_to_le_bytes 4 (Z_to_bv 64 0))).
  assert (WPw : W C A2 Mw (with_vmmaps vm2 md) /\ POSTM C A s m Mw) by (subst Mw; wp_win CK).
  assert (WP5 : W C A2 M5 (with_vmmaps vm2 md) /\ POSTM C A s m M5).
  { subst M5. do 2 (apply (WP_blk C A A2 m _ _ (Z_to_bv 64 pixd) _ 64); [exact CK | | exact L2p | exact LAp | exact L00p | exact SUB | rewrite !u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia]).
    exact WPw. }
  destruct WP5 as [HW5 PM5].
  assert (OUTw : forall x : word, ~ (s - 56 <= u x < s - 32)%Z -> Mw x = m4 x).
  { intros x Hx. subst Mw. rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. reflexivity. }
  assert (OUT5 : forall x : word, ~ (pixd + 32 <= u x < pixd + 48)%Z -> M5 x = Mw x).
  { intros x Hx. subst M5. rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. reflexivity. }
  assert (PXd5 : PIXat M5 pixd (hdv w h d cd data)).
  { subst M5. apply PIX_wr_fmt0; [|reflexivity]. apply PIX_wr_text0; [|reflexivity]. apply (PIXat_frame m4); [exact PXd|]. intros x Hx. apply OUTw. lia. }
  assert (CE5 : V14LeptPixCopy.cells4 M5 s ret (getr regs 8) (getr regs 9) (getr regs 18)).
  { eapply (V14LeptPixCopy.cells4_out Mw _ (pixd + 32) (pixd + 48)); [exact OUT5 | lia | lia | lia |].
    eapply (V14LeptPixCopy.cells4_out m4 _ (s - 56) (s - 32)); [exact OUTw | lia | lia | lia | exact CE4]. }
  assert (NEpdw : Z_to_bv 64 pixd <> Z_to_bv 64 data) by (apply zbv_ne2; lia).
  apply (padbits_W C A A2 M5 _ r5 (s - 32) pixd (hdv w h d cd data) (Z_to_bv 64 0x15fe0) S CK HW5 SUB Y2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(unfold LSF; lia) ltac:(lia) Y1 ltac:(red; apply bv_eq; reflexivity) Y10 Y11 PXd5 DV ltac:(cbn; lia) ltac:(cbn; lia) eq_refl L2p).
  { cbn. exact L2d. } { cbn. exact LAd. } { cbn. exact L00d. } { cbn. exact NEpdw. }
  intros m6 r6 HW6 CS6 PM6 PX6 OUT6 A10. cbn [p_data p_wpl p_h hdv] in OUT6. unfold LSF in OUT6.
  replace (Z_to_bv 64 0x15fe0) with (0x15fe0 : word) by (apply bv_eq; reflexivity).
  pose proof (V14LeptPixCopy.cells4_frm C (s - 32) M5 m6 s _ _ _ _ CK (proj1 PM6) ltac:(lia) ltac:(lia) ltac:(lia) CE5) as (C1 & C2 & C3 & C4).
  destruct (ptn_D al_rom r6 m6 s pixd ret _ _ _ ltac:(lia) ltac:(lia) Hret C1 C2 C3 C4 ltac:(csr; reflexivity) ltac:(csr; reflexivity))
    as (r7 & RUN7 & Z2 & Z1 & Z10 & Z8 & Z9 & Z18 & AG7).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW6)) | exact (mp_lazy _ (w_pure _ _ _ _ HW6)) | exact RUN7 |].
  apply (HK A2 m6 vm2 r7 HW6).
  - apply cs_kept_intro; csr; try reflexivity. all: rewrite ?Z8, ?Z9, ?Z18; try reflexivity. all: unfold V14LeptPixCopy.tn_rest in RR; csr; reflexivity.
  - eapply POSTM_trans; [exact PM5 | eapply POSTM_mono; [|exact PM6]; lia].
  - exists pixd, cd, data. split; [exact Z10|].
    unfold pixt_new. do 13 (split; [assumption|]). split; [exact PX6|].
    destruct CMR as [[CD0 LEQ] | (ad & CMOKc & Gcd & TOPcd & Gad & TOPad & NEcdad & NEcdp & NEcdd & NEadp & NEadd & LAcd & LAad & L00cd & L00ad & L2cd & L2ad & CM4 & LEQ)]; [left; split; [exact CD0 | exact LEQ] | right].
    exists ad. do 16 (split; [assumption|]). split; [| exact LEQ].
    assert (NEw1 : Z_to_bv 64 cd <> Z_to_bv 64 data) by (apply zbv_ne2; lia).
    pose proof (blk_apart C A2 m4 _ _ _ _ _ CK HW4 L2cd L2d NEw1 ltac:(lia) ltac:(lia)) as APcdd. rewrite !u_Z2bv in APcdd by lia.
    assert (NEw2 : Z_to_bv 64 cd <> Z_to_bv 64 pixd) by (apply zbv_ne2; lia).
    pose proof (blk_apart C A2 m4 _ _ _ _ _ CK HW4 L2cd L2p NEw2 ltac:(lia) ltac:(lia)) as APcdp. rewrite !u_Z2bv in APcdp by lia.
    apply (CMAPat_frame m4); [exact CM4|]. intros x Hx. rewrite OUT6 by lia. rewrite OUT5 by lia. apply OUTw. lia.
  - exact Hrm2.
Qed.

Theorem pixCreateTemplateNoInit_sure_W : forall C A m md regs (s pixs w h d cm datas : Z) (cv : cmapv) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 128 + 16 + LSF <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x44140 ->
  getr regs 10 = Z_to_bv 64 pixs ->
  PIXat m pixs (hdv w h d cm datas) -> hdr_ok w h d -> (1 <= w)%Z -> (1 <= h)%Z ->
  live A (Z_to_bv 64 pixs) = Some 64%Z ->
  (cm = 0%Z \/ (CMAPat m cm cv /\ cmap_ok cv /\ live A (Z_to_bv 64 cm) = Some 24%Z /\ live A (Z_to_bv 64 (c_arr cv)) = Some (4 * c_nalloc cv)%Z)) ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_pixcopy <= kR)%Z -> (RB_pixcopy14 <= bR)%Z ->
  TKs C A m md regs s w h d cv ret S kR bR ->
  realizes SEGS (mkCfg (mkst regs (0x15ea4 : word) m al_rom) md) S.
Proof.
  intros C A m md regs s pixs w h d cm datas cv ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 PXs HOK Hw Hh Lps HCM kR bR Hrm Hrk Hrb HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold LSF in *.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof HOK as (DV & Hw2 & Hh2 & Hsz). pose proof (dval_range d DV) as Hd32. pose proof (wpl_of_range w d ltac:(lia) DV) as Hwpl.
  pose proof PXs as (Hs0 & Hs64' & WFs & _).
  destruct (blk_range C A m md (Z_to_bv 64 pixs) 64 CK HW Lps ltac:(lia)) as [Gps TOPps]. rewrite u_Z2bv in Gps, TOPps by lia.
  (* [comment removed for export] *)
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lps) as (_ & ALps & _). rewrite u_Z2bv in ALps by lia.
  destruct (ptn_A al_rom regs m s pixs (hdv w h d cm datas) ret ltac:(lia) ltac:(lia) ltac:(lia) ALps PXs ltac:(lia)
              (W_sok_win C A m md (s - 32) 32 CK HW ltac:(lia) ltac:(cbn; lia)) H2 H1 H10)
    as (r1 & RUN1 & Q2 & Q1 & Q10 & Q11 & Q12 & Q9 & Q8 & AG1). cbn [p_w p_h p_d hdv] in Q10, Q11, Q12.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  assert (WP1 : W C A (V14LeptPixCopy.FR4 m s ret regs) md /\ POSTM C A s m (V14LeptPixCopy.FR4 m s ret regs)) by (unfold V14LeptPixCopy.FR4; wp_win CK).
  destruct WP1 as [HW1 PM1]. set (M1 := V14LeptPixCopy.FR4 m s ret regs) in *.
  pose proof (V14LeptPixCopy.cells4_FR4 m s ret regs ltac:(lia) ltac:(lia)) as CE1. fold M1 in CE1.
  assert (OUT1 : forall x : word, ~ (s - 32 <= u x < s)%Z -> M1 x = m x).
  { intros x Hx. subst M1. unfold V14LeptPixCopy.FR4. rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. reflexivity. }
  assert (Q4 : getr r1 4 = Z_to_bv 64 0x44140) by (rewrite (AG1 4) by (cbv; intuition discriminate); exact H4).
  assert (Hwh : (w * h <= 400000000)%Z) by (clear - Hw Hh Hw2 Hh2; nia).
  apply (pixCreateNoInit_sure_W C A M1 md r1 (s - 32) w h d (Z_to_bv 64 0x15ed8) S CK HW1 Q2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(unfold LSF; lia) ltac:(lia) Q1 ltac:(red; apply bv_eq; reflexivity) Q4 Q10 Q11 Q12 ltac:(lia) ltac:(lia) Hwh ltac:(lia) HOK kR bR Hrm ltac:(room_consts; lia) ltac:(room_consts; lia)).
  intros A1 m2 vm1 r2 pixd data HWa CSa PMa Hres PN HRTa.
  replace (Z_to_bv 64 0x15ed8) with (0x15ed8 : word) by (apply bv_eq; reflexivity).
  pose proof (V14LeptPixCopy.cells4_frm C (s - 32) M1 m2 s _ _ _ _ CK (proj1 PMa) ltac:(lia) ltac:(lia) ltac:(lia) CE1) as CE2.
  assert (PMa' : POSTM C A s m m2) by (eapply POSTM_trans; [exact PM1 | eapply POSTM_mono; [|exact PMa]; lia]).
  assert (PXs2 : PIXat m2 pixs (hdv w h d cm datas)).
  { apply (PIXat_frame m); [exact PXs|]. intros x Hx. rewrite (LIVK_byte C A M1 m2 md pixs 64 x CK HW1 (proj2 PMa) Lps ltac:(lia) TOPps Hx). apply OUT1. lia. }
  assert (E2 : getr r2 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
  assert (E9 : getr r2 9 = Z_to_bv 64 pixs) by (csr; reflexivity).
  assert (E4 : getr r2 4 = Z_to_bv 64 0x44140) by (csr; reflexivity).
  { (* [comment removed for export] *)
    destruct PN as (Gp & TOPp & ALp & Gd & TOPd & ALd & NEpd & L0p & L0d & L00p & L00d & L1p & L1d & LEQ & PXd & _).
    cbn [p_wpl p_h set_data pix_hdr] in TOPd, L1d.
    change (PIXat m2 pixd (hdv w h d 0 data)) in PXd.
    assert (NEsp : Z_to_bv 64 pixs <> Z_to_bv 64 pixd) by (intros E; rewrite E in Lps; rewrite Lps in L0p; discriminate).
    assert (SUBa : sub_live A A1) by (eapply sub_live_new2; [exact L0p | exact L0d | exact L1p | exact L1d | exact LEQ]).
    pose proof (SUBa _ _ Lps) as Lps1.
    pose proof (blk_apart C A1 m2 _ _ _ _ _ CK HWa Lps1 L1p NEsp ltac:(lia) ltac:(lia)) as APsp. rewrite !u_Z2bv in APsp by lia.
    destruct (ptn_B al_rom r2 m2 s pixs pixd (hdv w h d cm datas) (hdv w h d 0 data) ltac:(lia) ltac:(lia) ltac:(lia) ALp PXs2 PXd
                (proj1 (spp_of_range d)) eq_refl eq_refl eq_refl APsp (blk_sok C A1 m2 _ pixd 64 CK HWa L1p ltac:(lia) ltac:(lia) ltac:(lia)) E2 Hres E9)
      as (r3 & RUN3 & X2 & X1 & X10 & X11 & X8 & X9 & X18 & AG3).
    apply box_i in APsp.
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWa)) | exact (mp_lazy _ (w_pure _ _ _ _ HWa)) | exact RUN3 |].
    cbn [p_spp hdv] in *.
    set (M3 := wbytes (wbytes m2 (Z_to_bv 64 (pixd + 12)) (word_to_le_bytes 4 (Z_to_bv 64 (spp_of d)))) (Z_to_bv 64 (pixd + 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))).
    assert (WP3 : W C A1 M3 (with_vmmaps vm1 md) /\ POSTM C A s m M3).
    { subst M3. do 2 (apply (WP_blk C A A1 m _ _ (Z_to_bv 64 pixd) _ 64); [exact CK | | exact L1p | exact L0p | exact L00p | exact SUBa | rewrite !u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia]).
      split; [exact HWa | exact PMa']. }
    destruct WP3 as [HW3 PM3].
    assert (OUT3 : forall x : word, ~ (pixd + 12 <= u x < pixd + 32)%Z -> M3 x = m2 x).
    { intros x Hx. subst M3. rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. reflexivity. }
    assert (PXd3 : PIXat M3 pixd (hdv w h d 0 data)).
    { subst M3. apply (PIX_wr_res0 _ pixd (hdv w h d 0 data)); [| reflexivity | reflexivity].
      exact (PIX_wr_spp_same m2 pixd (hdv w h d 0 data) PXd). }
    assert (PXs3 : PIXat M3 pixs (hdv w h d cm datas)).
    { pose proof (box_e _ APsp) as U. apply (PIXat_frame m2); [exact PXs2|]. intros x Hx. apply OUT3. lia. }
    assert (CE3 : V14LeptPixCopy.cells4 M3 s ret (getr regs 8) (getr regs 9) (getr regs 18)) by (eapply (V14LeptPixCopy.cells4_out m2 _ (pixd + 12) (pixd + 32)); [exact OUT3 | lia | lia | lia | exact CE2]).
    assert (X4 : getr r3 4 = Z_to_bv 64 0x44140) by (rewrite (AG3 4) by (cbv; intuition discriminate); exact E4).
    assert (HCM3 : cm = 0%Z \/ (CMAPat M3 cm cv /\ cmap_ok cv /\ live A1 (Z_to_bv 64 cm) = Some 24%Z /\ live A1 (Z_to_bv 64 (c_arr cv)) = Some (4 * c_nalloc cv)%Z)).
    { destruct HCM as [CM0 | (CM & CMOK & Lcm & Larr)]; [left; exact CM0 | right].
      pose proof CM as (Hc0 & Hc64 & _).
      destruct (blk_range C A m md (Z_to_bv 64 cm) 24 CK HW Lcm ltac:(lia)) as [Gcm TOPcm]. rewrite u_Z2bv in Gcm, TOPcm by lia.
      pose proof (SUBa _ _ Lcm) as Lcm1.
      assert (NEcp : Z_to_bv 64 cm <> Z_to_bv 64 pixd) by (intros E; rewrite E in Lcm; rewrite Lcm in L0p; discriminate).
      pose proof (blk_apart C A1 m2 _ _ _ _ _ CK HWa Lcm1 L1p NEcp ltac:(lia) ltac:(lia)) as APcp. rewrite !u_Z2bv in APcp by lia.
      split; [| split; [exact CMOK | split; [exact Lcm1 | exact (SUBa _ _ Larr)]]].
      apply (CMAPat_frame m); [exact CM|]. intros x Hx. rewrite OUT3 by lia.
      rewrite (LIVK_byte C A M1 m2 md cm 24 x CK HW1 (proj2 PMa) Lcm ltac:(lia) TOPcm Hx). apply OUT1. lia. }
    apply (pixCopyColormap_W C A A1 M3 _ r3 (s - 32) pixd pixs (hdv w h d 0 data) (hdv w h d cm datas) cv (Z_to_bv 64 0x15fc0) S CK HW3 SUBa X2
             ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold LSF; lia) ltac:(lia) X1 ltac:(red; apply bv_eq; reflexivity) X4 X10 X11
             PXd3 PXs3 eq_refl eq_refl ltac:(pose proof (box_e _ APsp); lia) L1p L0p L00p Lps1 HCM3
             (kR - RK_pix) (bR - RB_pix14) ltac:(room_tac) ltac:(room_consts; lia) ltac:(room_consts; lia)).
    intros A2 m4 vm2 r4 HWb CSb PMb OUTb Hrm2. rewrite with_vmmaps_twice in HWb |- *.
    replace (Z_to_bv 64 0x15fc0) with (0x15fc0 : word) by (apply bv_eq; reflexivity).
    pose proof (V14LeptPixCopy.cells4_frm C (s - 32) M3 m4 s _ _ _ _ CK (proj1 PMb) ltac:(lia) ltac:(lia) ltac:(lia) CE3) as CE4.
    assert (PMb' : POSTM C A s m m4) by (eapply POSTM_trans; [exact PM3 | eapply POSTM_mono; [|exact PMb]; lia]).
    assert (PXs4 : PIXat m4 pixs (hdv w h d cm datas)).
    { apply (PIXat_frame M3); [exact PXs3|]. intros x Hx. exact (LIVK_at A M3 m4 pixs 64 x (proj2 PMb) Lps ltac:(lia) ltac:(lia) Hx). }
    assert (Y2 : getr r4 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
    assert (Y8 : getr r4 8 = Z_to_bv 64 pixd) by (csr; reflexivity).
    assert (Y9 : getr r4 9 = Z_to_bv 64 pixs) by (csr; reflexivity).
    assert (RR : forall x, In x V14LeptPixCopy.tn_rest -> getr r4 x = getr regs x) by (unfold V14LeptPixCopy.tn_rest; rest_solve).
    destruct OUTb as [[LIVEQ PXd4] | (cd & ad & CC & PXd4)].
    + apply (ptn_tail_sure_W C A A2 m md m4 vm2 regs r4 s pixs pixd w h d cm datas 0 data cv ret S kR bR CK HK ltac:(room_tac) Hs16 ltac:(unfold LSF; lia) Hhi Hret HWb PMb'
               (sub_live_trans _ _ _ SUBa (sub_live_eq _ _ LIVEQ)) CE4 Y2 Y8 Y9 RR H2 PXs4 Lps HOK Hw Hh Gp TOPp ALp Gd TOPd ALd NEpd L0p L0d L00p L00d
               ltac:(rewrite LIVEQ; exact L1p) ltac:(rewrite LIVEQ; exact L1d) PXd4).
      left. split; [reflexivity|]. intros q N1 N2. rewrite LIVEQ. apply LEQ; assumption.
    + pose proof CC as (CMOKc & Gcd & TOPcd & ALcd & Gad & TOPad & ALad & NEcdad & LA1cd & LA1ad & L00cd & L00ad & L2cd & L2ad & LEQ2 & CM4).
      assert (NEcdp : Z_to_bv 64 cd <> Z_to_bv 64 pixd) by (intros E; rewrite E in LA1cd; rewrite L1p in LA1cd; discriminate).
      assert (NEadp : Z_to_bv 64 ad <> Z_to_bv 64 pixd) by (intros E; rewrite E in LA1ad; rewrite L1p in LA1ad; discriminate).
      assert (NEcdd : Z_to_bv 64 cd <> Z_to_bv 64 data) by (intros E; rewrite E in LA1cd; rewrite L1d in LA1cd; discriminate).
      assert (NEadd : Z_to_bv 64 ad <> Z_to_bv 64 data) by (intros E; rewrite E in LA1ad; rewrite L1d in LA1ad; discriminate).
      assert (SUBb : sub_live A1 A2) by (eapply sub_live_new2; [exact LA1cd | exact LA1ad | exact L2cd | exact L2ad | exact LEQ2]).
      apply (ptn_tail_sure_W C A A2 m md m4 vm2 regs r4 s pixs pixd w h d cm datas cd data cv ret S kR bR CK HK ltac:(room_tac) Hs16 ltac:(unfold LSF; lia) Hhi Hret HWb PMb'
               (sub_live_trans _ _ _ SUBa SUBb) CE4 Y2 Y8 Y9 RR H2 PXs4 Lps HOK Hw Hh Gp TOPp ALp Gd TOPd ALd NEpd L0p L0d L00p L00d
               (SUBb _ _ L1p) (SUBb _ _ L1d) PXd4).
      right. exists ad.
      split; [exact CMOKc|]. split; [exact Gcd|]. split; [exact TOPcd|]. split; [exact Gad|]. split; [exact TOPad|]. split; [exact NEcdad|].
      split; [intros E; apply NEcdp; rewrite E; reflexivity|]. split; [intros E; apply NEcdd; rewrite E; reflexivity|].
      split; [intros E; apply NEadp; rewrite E; reflexivity|]. split; [intros E; apply NEadd; rewrite E; reflexivity|].
      split; [rewrite <- (LEQ _ NEcdp NEcdd); exact LA1cd|]. split; [rewrite <- (LEQ _ NEadp NEadd); exact LA1ad|].
      split; [exact L00cd|]. split; [exact L00ad|]. split; [exact L2cd|]. split; [exact L2ad|]. split; [exact CM4|].
      intros q N1 N2 N3 N4. rewrite (LEQ2 q N3 N4). apply LEQ; assumption.
  }
Qed.

End PixSure.
