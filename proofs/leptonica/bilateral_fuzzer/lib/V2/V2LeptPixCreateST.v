(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.bilateral_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import LeptRoomBL.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2LeptStderr V2LeptBase V2LeptErr V2LeptPixHdr V2LeptPadBitsW V2Memset V2LeptPixCreate V2LeptPixHdrST.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import LeptRoom.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import LeptRoom14.
Import ListNotations.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac sok_in SOK :=
  store_ok_peel;
  first [ exact SOK
        | eapply store_ok_sub; [ | exact SOK | | ]; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].

Section PixCreate.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V2Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
#[local] Abbreviation FR4 := (V2LeptPixCreate.FR4).

Theorem pixCreateNoInit_sureT_W : forall C A m md regs (s w h d : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 96 + LSF <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x56270 ->
  getr regs 10 = Z_to_bv 64 w -> getr regs 11 = Z_to_bv 64 h -> getr regs 12 = Z_to_bv 64 d ->
  (1 <= w)%Z -> (1 <= h)%Z -> hdr_ok w h d ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_pix <= kR)%Z -> ((RB_pixT (4 * (wpl_of w d * h))) <= bR)%Z ->
  (forall A' m' vm' regs' (pix data : Z), W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A s m m' ->
     getr regs' 10 = Z_to_bv 64 pix -> pixr_new C A A' m' pix data (set_data (pix_hdr w h d) data) ->
     aroom A' vm' (kR - RK_pix) (bR - (RB_pixT (4 * (wpl_of w d * h)))) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (0x19374 : word) m al_rom) md) S.
Proof.
  intros C A m md regs s w h d ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 H11 H12 Hw Hh HOK kR bR Hrm Hrk Hrb HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold LSF in *.
  pose proof HOK as (DV & Hw2 & Hh2 & Hsz).
  pose proof (dval_range d DV) as Hd32. pose proof (wpl_of_range w d ltac:(lia) DV) as Hwpl.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof (alloc_margin_le (4 * (wpl_of w d * h))) as HAM. pose proof (alloc_margin_ge (4 * (wpl_of w d * h)) ltac:(nia)) as HAG.
  unfold RB_pixT in Hrb, HK.
  pose proof (W_sok_win C A m md (s - 32) 32 CK HW ltac:(lia) ltac:(cbn; lia)) as SOK.
  destruct (pn_A al_rom regs m s w h d ret ltac:(lia) ltac:(lia) SOK H2 H1 H10 H11 H12) as (r1 & RUN1 & Q2 & Q1 & Q10 & Q11 & Q12 & Q9 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  assert (WP1 : W C A (FR4 m s ret regs) md /\ POSTM C A s m (FR4 m s ret regs)) by (unfold FR4; wp_win CK).
  destruct WP1 as [HW1 PM1]. set (M1 := FR4 m s ret regs) in *.
  pose proof (cells4_FR4 m s ret regs ltac:(lia) ltac:(lia)) as CE1. fold M1 in CE1.
  assert (Q4 : getr r1 4 = Z_to_bv 64 0x56270) by (csr; reflexivity).
  apply (pixCreateHeader_sureT_W C A M1 md r1 (s - 32) w h d (Z_to_bv 64 0x1938c) S CK HW1 Q2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(unfold LSF; lia) ltac:(lia) Q1 ltac:(red; apply bv_eq; reflexivity) Q4 Q10 Q11 Q12 Hw Hh HOK kR bR Hrm
           ltac:(room_consts; lia) ltac:(lia)).
  intros A1 m1 vm1 r2 pix HWa CSa PMa Hres PN Hrm1.
  replace (Z_to_bv 64 0x1938c) with (0x1938c : word) by (apply bv_eq; reflexivity).
  assert (PMa' : POSTM C A s m m1) by (eapply POSTM_trans; [exact PM1 | eapply POSTM_mono; [|exact PMa]; lia]).
  pose proof (cells4_frm C (s - 32) M1 m1 s _ _ _ CK (proj1 PMa) ltac:(lia) ltac:(lia) ltac:(lia) CE1) as CE2.
  assert (E2 : getr r2 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
  assert (E9 : getr r2 9 = Z_to_bv 64 h) by (csr; reflexivity).
  assert (E4 : getr r2 4 = Z_to_bv 64 0x56270) by (csr; reflexivity).
  destruct PN as (Gp & TOPp & ALp & L0 & L00 & L1 & LEQ & PX1).
  assert (AL8 : (pix mod 8 = 0)%Z) by (rewrite <- (Z.add_0_r pix); apply mod16_plus_mod8; [exact ALp | reflexivity]).
  destruct (pn_B al_rom r2 m1 s h pix (pix_hdr w h d) PX1 eq_refl ltac:(lia) ltac:(cbn; lia) Gp AL8 (W_pmm_malloc C A1 m1 _ HWa) Hres E9)
    as (r3 & RUN3 & V10 & V1 & V8 & V9 & AG3).
  cbn [p_wpl pix_hdr] in V10.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWa)) | exact (mp_lazy _ (w_pure _ _ _ _ HWa)) | exact RUN3 |].
  assert (V4 : getr r3 4 = Z_to_bv 64 0x56270) by (csr; reflexivity).
  assert (V2 : getr r3 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
  replace (0x3c370 : word) with (Z_to_bv 64 0x3c370) by (apply bv_eq; reflexivity).
  apply (W_malloc16_sure C A1 m1 _ r3 (4 * (wpl_of w d * h)) (kR - RK_hdr) (bR - RB_hdrT) (Z_to_bv 64 0x193c4) (s - 32) S CK HWa V10 ltac:(lia)
           ltac:(rewrite with_vmmaps_vmmaps; exact Hrm1) ltac:(room_consts; lia) ltac:(lia) ltac:(unfold ROOM_NMAX; lia) V1
           ltac:(red; apply bv_eq; reflexivity) V4 V2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)).
  intros A2 m2 vm2 r4 res HWb Hres2 CSb Hnz K0 K1 K00 KEQ AL16 TOP PMb Hrm2. rewrite with_vmmaps_twice. rewrite with_vmmaps_twice in HWb.
  replace (Z_to_bv 64 0x193c4) with (0x193c4 : word) by (apply bv_eq; reflexivity).
  assert (SUBa : sub_live A A1) by (eapply sub_live_new; eassumption).
  assert (PMb' : POSTM C A s m m2).
  { eapply POSTM_trans; [exact PMa'|]. apply (POSTM_sub C A A1 _ _ _ SUBa). eapply POSTM_mono; [|exact PMb]. lia. }
  pose proof (cells4_frm C (s - 32) m1 m2 s _ _ _ CK (proj1 PMb) ltac:(lia) ltac:(lia) ltac:(lia) CE2) as CE3.
  assert (PX2 : PIXat m2 pix (pix_hdr w h d)).
  { apply (PIXat_frame m1); [exact PX1|]. intros x Hx. pose proof (proj2 PMb (Z_to_bv 64 pix) 64%Z (u x - pix)%Z L1 ltac:(lia)) as E.
    unfold at_ in E. rewrite u_Z2bv in E by lia. replace (pix + (u x - pix))%Z with (u x) in E by lia. rewrite zbv_self in E. exact E. }
  assert (X8 : getr r4 8 = Z_to_bv 64 pix) by (csr; reflexivity).
  assert (X2 : getr r4 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
  assert (SOKp : store_ok SEGS m2 (Z_to_bv 64 pix) 64 = true).
  { rewrite <- p16_segs. apply store_ok_of_all; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx.
    unfold wview. destruct (m2 x) eqn:E; [discriminate|]. exfalso. exact (PIXat_defined m2 pix _ x PX2 ltac:(lia) E). }
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
  apply (padbits_W C A A2 M3 _ r5 (s - 32) pix (set_data (pix_hdr w h d) data) (Z_to_bv 64 0x193d8) S CK HW3 SUBb Y2
           ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold LSF; lia) ltac:(lia) Y1 ltac:(red; apply bv_eq; reflexivity) Y10 Y11
           PX3 DV ltac:(cbn; lia) ltac:(cbn; lia) eq_refl Lp2).
  { cbn. exact K1. } { cbn. exact LAd. } { cbn. exact K00. } { cbn. exact NEpd. }
  intros m5 r6 HW5 CS5 PM5 PX5 OUT5 A10.
  replace (Z_to_bv 64 0x193d8) with (0x193d8 : word) by (apply bv_eq; reflexivity).
  assert (CE5 : cells4 m5 s ret (getr regs 8) (getr regs 9)).
  { apply (cells4_frm C (s - 32) M3 m5 s); [exact CK | exact (proj1 PM5) | lia | lia | lia |].
    subst M3. destruct CE3 as (C1 & C2 & C3). unfold cells4. repeat split; repeat rdn_peel1; assumption. }
  destruct CE5 as (C1 & C2 & C3).
  assert (W2 : getr r6 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
  assert (W8 : getr r6 8 = Z_to_bv 64 pix) by (csr; reflexivity).
  destruct (pn_D al_rom r6 m5 s pix ret _ _ ltac:(lia) ltac:(lia) Hret C1 C2 C3 W2 W8) as (r7 & RUN7 & U2 & U1 & U10 & U8 & U9 & AG7).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW5)) | exact (mp_lazy _ (w_pure _ _ _ _ HW5)) | exact RUN7 |].
  apply (HK A2 m5 vm2 r7 pix data HW5).
  - apply cs_kept_intro; csr; try reflexivity.
  - eapply POSTM_trans; [exact PM3 | eapply POSTM_mono; [|exact PM5]; lia].
  - exact U10.
  - unfold pixr_new. cbn [p_wpl p_h p_data set_data pix_hdr].
    do 15 (try (split; [first [assumption | lia | idtac] |])).
    all: try assumption; try lia; try reflexivity.
    all: intros q N1 N2; rewrite (KEQ q N2); apply LEQ; exact N1.
  - apply (aroom_mono A2 vm2 _ _ _ _ Hrm2); room_consts; lia.
Qed.

Theorem pixCreate_sureT_W : forall C A m md regs (s w h d : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 112 + LSF <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x56270 ->
  getr regs 10 = Z_to_bv 64 w -> getr regs 11 = Z_to_bv 64 h -> getr regs 12 = Z_to_bv 64 d ->
  (1 <= w)%Z -> (1 <= h)%Z -> hdr_ok w h d ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_pix <= kR)%Z -> ((RB_pixT (4 * (wpl_of w d * h))) <= bR)%Z ->
  (forall A' m' vm' regs' (pix data : Z), W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A s m m' ->
     getr regs' 10 = Z_to_bv 64 pix -> pixr_new C A A' m' pix data (set_data (pix_hdr w h d) data) ->
     aroom A' vm' (kR - RK_pix) (bR - (RB_pixT (4 * (wpl_of w d * h)))) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (0x192d0 : word) m al_rom) md) S.
Proof.
  intros C A m md regs s w h d ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 H11 H12 Hw Hh HOK kR bR Hrm Hrk Hrb HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold LSF in *.
  pose proof (W_sok_win C A m md (s - 16) 16 CK HW ltac:(lia) ltac:(cbn; lia)) as SOK.
  destruct (pk_A al_rom regs m s ret ltac:(lia) ltac:(lia) SOK H2 H1) as (r1 & RUN1 & Q2 & Q1 & Q10 & Q11 & Q12 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  set (M1 := wbytes (wbytes m _ _) _ _).
  assert (WP1 : W C A M1 md /\ POSTM C A s m M1) by (subst M1; wp_win CK).
  destruct WP1 as [HW1 PM1].
  assert (Q4 : getr r1 4 = Z_to_bv 64 0x56270) by (csr; reflexivity).
  rewrite H10 in Q10. rewrite H11 in Q11. rewrite H12 in Q12.
  apply (pixCreateNoInit_sureT_W C A M1 md r1 (s - 16) w h d (Z_to_bv 64 0x192e0) S CK HW1 Q2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(unfold LSF; lia) ltac:(lia) Q1 ltac:(red; apply bv_eq; reflexivity) Q4 Q10 Q11 Q12 Hw Hh HOK kR bR Hrm Hrk Hrb).
  intros A1 m1 vm1 r2 pix data HWa CSa PMa Hres PN Hrm1.
  replace (Z_to_bv 64 0x192e0) with (0x192e0 : word) by (apply bv_eq; reflexivity).
  assert (PMa' : POSTM C A s m m1) by (eapply POSTM_trans; [exact PM1 | eapply POSTM_mono; [|exact PMa]; lia]).
  assert (R8 : rdn SEGS m1 (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret)).
  { rewrite (FRM_rdn16 C (s - 16) M1 m1 (s - 8) 8 CK (proj1 PMa)) by (cbn; lia). subst M1. rdn_solve. }
  assert (R16 : rdn SEGS m1 (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (getr regs 8))).
  { rewrite (FRM_rdn16 C (s - 16) M1 m1 (s - 16) 8 CK (proj1 PMa)) by (cbn; lia). subst M1. rdn_solve. }
  assert (E2 : getr r2 2 = Z_to_bv 64 (s - 16)) by (csr; reflexivity).
  pose proof HOK as (DV & Hw2 & Hh2 & Hsz).
  destruct PN as (Gp & TOPp & ALp & Gd & TOPd & ALd & NEpd & L0 & K0 & L00 & K00 & L1 & K1 & LEQ & PX1 & Hdata).
  cbn [p_wpl p_h p_data set_data pix_hdr] in TOPd, K1, Hdata.
  pose proof (dval_range d DV) as Hd32. pose proof (wpl_of_range w d ltac:(lia) DV) as Hwpl.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  assert (AL8 : (pix mod 8 = 0)%Z) by (rewrite <- (Z.add_0_r pix); apply mod16_plus_mod8; [exact ALp | reflexivity]).
  destruct (pk_B al_rom r2 m1 pix _ PX1 Gp ltac:(cbn; lia) ltac:(cbn; lia) AL8 Hres) as (r3 & RUN3 & V10 & V11 & V12 & V1 & V8 & AG3).
  cbn [p_wpl p_h p_data set_data pix_hdr] in V10, V12.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWa)) | exact (mp_lazy _ (w_pure _ _ _ _ HWa)) | exact RUN3 |].
  assert (SOKd : store_ok SEGS m1 (Z_to_bv 64 data) (Z.to_nat (4 * (wpl_of w d * h))) = true).
  { rewrite <- p16_segs. apply store_ok_of_all; rewrite u_Z2bv by lia; [lia|]. intros x Hx.
    unfold wview. destruct (m1 x) eqn:E; [discriminate|]. exfalso.
    destruct (blk_byte C A1 m1 _ (Z_to_bv 64 data) _ x CK HWa K1 ltac:(rewrite u_Z2bv by lia; lia)) as (_ & D & _). exact (D E). }
  apply (memset_at (with_vmmaps vm1 md) r3 m1 al_rom data (4 * (wpl_of w d * h)) (Z_to_bv 64 0x1931c) S
           (md_pure_with_vmmaps _ _ (w_pure _ _ _ _ HW)) ltac:(lia) ltac:(lia) ltac:(lia) SOKd ltac:(red; apply bv_eq; reflexivity) V1 V10 V11 V12).
  intros r4 A10' AG4.
  replace (Z_to_bv 64 0x1931c) with (0x1931c : word) by (apply bv_eq; reflexivity).
  set (M5 := zf m1 data [(0, 4 * (wpl_of w d * h))%Z]).
  assert (OUT5 : forall x : word, (u x < data \/ data + 4 * (wpl_of w d * h) <= u x)%Z -> M5 x = m1 x).
  { intros x Hx. subst M5. apply zf_outside. apply inzr_falseP. cbn [inzrP]. lia. }
  assert (CH : forall a, M5 a <> m1 a -> scratch C s a \/ (exists p n, live A1 p = Some n /\ live A p = None /\ (u p <= u a < u p + n)%Z)).
  { intros a NE. right. exists (Z_to_bv 64 data), (4 * (wpl_of w d * h))%Z. rewrite u_Z2bv by lia. split; [exact K1 | split; [exact K0|]].
    destruct (Z_lt_ge_dec (u a) data); [exfalso; apply NE; apply OUT5; lia|].
    destruct (Z_lt_ge_dec (u a) (data + 4 * (wpl_of w d * h))); [lia | exfalso; apply NE; apply OUT5; lia]. }
  assert (HW5 : W C A1 M5 (with_vmmaps vm1 md)).
  { apply (W_local C A1 m1 _ M5 s CK HWa Hhi); [| subst M5; apply zf_grows].
    intros a NE. destruct (CH a NE) as [X|(p & n & L & _ & R)]; [left; exact X | right; exists p, n]. split; [exact L | split; [| exact R]].
    destruct (bv_eq_dec _ p (Z_to_bv 64 data)) as [->|NE']; [exact K00|].
    exfalso. apply NE. apply OUT5.
    pose proof (ai_live_disjoint A1 m1 _ _ _ _ _ (w_inv _ _ _ _ HWa) L K1 NE') as D. rewrite u_Z2bv in D by lia.
    pose proof (ai_live_hull A1 m1 _ _ _ (w_inv _ _ _ _ HWa) L) as (Hn0 & _). pose proof (round16_ge n Hn0).
    pose proof (round16_ge (4 * (wpl_of w d * h)) ltac:(lia)). lia. }
  assert (PM5 : POSTM C A s m M5).
  { eapply POSTM_trans; [exact PMa'|]. exact (POSTM_local C A A1 m1 _ M5 s CK HWa (sub_live_new2 _ _ _ _ _ _ L0 K0 L1 K1 LEQ) CH). }
  assert (PX5 : PIXat M5 pix (set_data (pix_hdr w h d) data)).
  { apply (PIXat_frame m1); [exact PX1|]. intros x Hx. apply OUT5.
    pose proof (ai_live_disjoint A1 m1 _ _ _ _ _ (w_inv _ _ _ _ HWa) L1 K1 (zneq_w pix data ltac:(lia) ltac:(lia) NEpd)) as D. rewrite !u_Z2bv in D by lia.
    unfold round16 in D at 1. change ((64 + 15) / 16)%Z with 4%Z in D. pose proof (round16_ge (4 * (wpl_of w d * h)) ltac:(lia)). lia. }
  assert (W2 : getr r4 2 = Z_to_bv 64 (s - 16)) by (csr; reflexivity).
  assert (W8 : getr r4 8 = Z_to_bv 64 pix) by (csr; reflexivity).
  destruct (pk_C al_rom r4 M5 s pix ret (getr regs 8) ltac:(lia) ltac:(lia) Hret) as (r5 & RUN5 & U2 & U1 & U10 & U8 & AG5).
  { rewrite <- R8. apply rdn_ext; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx. apply OUT5. lia. }
  { rewrite <- R16. apply rdn_ext; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx. apply OUT5. lia. }
  { exact W2. } { exact W8. }
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW5)) | exact (mp_lazy _ (w_pure _ _ _ _ HW5)) | exact RUN5 |].
  apply (HK A1 M5 vm1 r5 pix data HW5).
  - apply cs_kept_intro; csr; try reflexivity.
  - exact PM5.
  - exact U10.
  - unfold pixr_new. cbn [p_wpl p_h p_data set_data pix_hdr]. repeat (split; [first [assumption | lia] |]); try assumption.
    all: first [exact PX5 | reflexivity | assumption].
  - exact Hrm1.
Qed.

End PixCreate.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
