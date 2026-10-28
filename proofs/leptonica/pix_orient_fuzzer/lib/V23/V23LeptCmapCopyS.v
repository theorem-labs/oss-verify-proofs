(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptStructs2 LeptArith LeptArith2 LeptRoom LeptRoomPC.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptStderr V23LeptBase V23LeptUb V23LeptErr V23LeptCmapValid V23MemcpyBase V23Memcpy V23_code_frontB_cmapcopy.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptCmap2.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require O23LeptCmapValid O23LeptCmap2.
Import ListNotations.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac sok_in SOK :=
  store_ok_peel;
  first [ exact SOK
        | eapply store_ok_sub; [ | exact SOK | | ]; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].
Ltac in_kept := unfold callee_kept; cbn [In]; repeat (first [left; reflexivity | right]).

Section CmapCopyS.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V23Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Theorem pixcmapCopy_sure_W : forall C A m md regs (s cm : Z) (cv : cmapv) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 48 + 16 + LSF <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x1381d0 ->
  getr regs 10 = Z_to_bv 64 cm ->
  CMAPat m cm cv -> O23LeptCmapValid.cmap_ok cv -> live A (Z_to_bv 64 cm) = Some 24%Z -> live A (Z_to_bv 64 (c_arr cv)) = Some (4 * c_nalloc cv)%Z ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_cmapcopy <= kR)%Z -> (RB_cmapcopy <= bR)%Z ->
  (forall A' m' vm' regs' (cd ad : Z), W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A s m m' ->
     getr regs' 10 = Z_to_bv 64 cd -> O23LeptCmap2.cmap_copy C A A' m' cd ad cv ->
     aroom A' vm' (kR - RK_cmapcopy) (bR - RB_cmapcopy) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (0x730dc : word) m al_rom) md) S.
Proof.
  intros C A m md regs s cm cv ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 CM CMOK Lcm Larr kR bR Hrm Hrk Hrb HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold LSF in *.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof CM as (Hc0 & Hc64 & CWF & _). pose proof CMOK as (Hcd & Hcna & Hcn & Hcarr).
  assert (Hpow : (2 <= c_nalloc cv <= 256)%Z) by (rewrite Hcna; destruct Hcd as [->|[->|[->| ->]]]; cbn; lia). clear Hcd.
  pose proof (cf_arr _ CWF) as Rarr.
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lcm) as (_ & ALcm & _). rewrite u_Z2bv in ALcm by lia.
  assert (ALcm8 : (cm mod 8 = 0)%Z) by (clear - ALcm; Z.div_mod_to_equations; lia).
  pose proof (alloc_margin_small (1 * 24) ltac:(lia)) as HAM1. pose proof (alloc_margin_small (1 * (4 * c_nalloc cv)) ltac:(lia)) as HAM2.
  pose proof (alloc_margin_ge (1 * 24) ltac:(lia)) as HAG1.
  unfold RK_cmapcopy in Hrk. unfold RB_cmapcopy in Hrb.
  destruct (blk_range C A m md (Z_to_bv 64 cm) 24 CK HW Lcm ltac:(lia)) as [Gcm TOPcm]. rewrite u_Z2bv in Gcm, TOPcm by lia.
  destruct (blk_range C A m md (Z_to_bv 64 (c_arr cv)) _ CK HW Larr ltac:(lia)) as [Garr TOParr]. rewrite u_Z2bv in Garr, TOParr by lia.
  destruct (pcc_A al_rom regs m s cm ret ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) (W_sok_win C A m md (s - 32) 32 CK HW ltac:(lia) ltac:(cbn; lia)) H2 H1 H10)
    as (r1 & RUN1 & Q2 & Q1 & Q10 & Q11 & Q12 & Q8 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  assert (WP1 : W C A (O23LeptCmap2.FRC3 m s ret regs) md /\ POSTM C A s m (O23LeptCmap2.FRC3 m s ret regs)) by (unfold O23LeptCmap2.FRC3; wp_win CK).
  destruct WP1 as [HW1 PM1]. set (M1 := O23LeptCmap2.FRC3 m s ret regs) in *.
  pose proof (cellsC3_FRC3 m s ret regs ltac:(lia) ltac:(lia)) as CE1. fold M1 in CE1.
  assert (CM1 : CMAPat M1 cm cv).
  { apply (CMAPat_frame m M1 _ _ CM). intros x Hx. subst M1. unfold O23LeptCmap2.FRC3. rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. reflexivity. }
  apply (pixcmapIsValid_null_W C A M1 md r1 (s - 32) cm (s - 28) cv (Z_to_bv 64 0x73100) S CK HW1 Q2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(lia) ltac:(lia) ltac:(lia) ltac:(apply sp_slot_al4'; [exact Hs16 | reflexivity]) Q1 ltac:(red; apply bv_eq; reflexivity) Q10 Q11 Q12 CM1 CMOK Lcm).
  intros m2 r2 HW2 CS2 PV2 A10.
  replace (Z_to_bv 64 0x73100) with (0x73100 : word) by (apply bv_eq; reflexivity).
  pose proof PV2 as [F2 L2].
  assert (PM2 : POSTM C A s m m2).
  { eapply POSTM_trans; [exact PM1|].
    unshelve (eapply (POSTM_absorb C A A M1 _ m2 s (s - 32) _ _ CK HW1 (sub_live_refl A) ltac:(lia) _ _ Hhi PV2)); rewrite ?length_N_to_le_bytes, u_Z2bv by lia; cbn; lia. }
  assert (Rv2 : rdn SEGS m2 (Z_to_bv 64 (s - 28)) 4 = Some (Z_to_le_bytes 4 1)).
  { rewrite (FRM_rdn16 C (s - 32) _ m2 (s - 28) 4 CK F2) by (cbn; lia). rewrite <- (w2l_Z4 1) by lia. apply rdn_wbytes_hit4. rewrite u_Z2bv by lia. lia. }
  assert (CE2 : cellsC3 m2 s ret (getr regs 8) (getr regs 9)).
  { apply (cellsC3_frm C (s - 32) (wbytes M1 (Z_to_bv 64 (s - 28)) (word_to_le_bytes 4 (Z_to_bv 64 1))) m2 s _ _ _ CK F2 ltac:(lia) ltac:(lia) ltac:(lia)).
    eapply (cellsC3_out M1 _ (s - 28) (s - 24)); [intros x Hx; apply wbytes_outside; rewrite ?length_N_to_le_bytes, u_Z2bv by lia; cbn; lia | lia | lia | lia | exact CE1]. }
  assert (CM2 : CMAPat m2 cm cv).
  { apply (CMAPat_frame M1); [exact CM1|]. intros x Hx.
    assert (HW1v : W C A (wbytes M1 (Z_to_bv 64 (s - 28)) (word_to_le_bytes 4 (Z_to_bv 64 1))) md).
    { apply (W_store_win C A M1 md _ _ CK HW1); rewrite ?length_N_to_le_bytes, u_Z2bv by lia; cbn; lia. }
    rewrite (LIVK_byte C A _ m2 md cm 24 x CK HW1v L2 Lcm ltac:(lia) TOPcm Hx).
    apply wbytes_outside; rewrite ?length_N_to_le_bytes, u_Z2bv by lia; cbn; lia. }
  assert (Y2 : getr r2 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
  destruct (pcc_B al_rom r2 m2 s ltac:(lia) ltac:(lia) Rv2 Y2) as (r3 & RUN3 & P2 & P1 & P10 & P11 & AG3).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact RUN3 |].
  assert (P4 : getr r3 4 = Z_to_bv 64 0x1381d0) by (rewrite (AG3 4) by (cbv; intuition discriminate); csr; reflexivity).
  assert (P8 : getr r3 8 = Z_to_bv 64 cm) by (rewrite (AG3 8) by (cbv; intuition discriminate); csr; reflexivity).
  replace (0x10e6e0 : word) with (Z_to_bv 64 0x10e6e0) by (apply bv_eq; reflexivity).
  apply (W_calloc16_sure C A m2 md r3 1 24 kR bR (Z_to_bv 64 0x73114) (s - 32) S CK HW2 P10 P11 ltac:(lia) ltac:(lia) ltac:(lia)
           Hrm ltac:(lia) ltac:(lia) ltac:(unfold ROOM_NMAX; lia) P1
           ltac:(red; apply bv_eq; reflexivity) P4 P2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)).
  intros A1 m3 vm1 r4 res HWa Hres CSa Hnz L0 L1 L00 LEQ ZERO AL16 TOP PMa Hrm1.
  replace (Z_to_bv 64 0x73114) with (0x73114 : word) by (apply bv_eq; reflexivity).
  assert (E2a : getr r4 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
  assert (E8a : getr r4 8 = Z_to_bv 64 cm) by (csr; reflexivity).
  assert (E4a : getr r4 4 = Z_to_bv 64 0x1381d0) by (csr; reflexivity).
  pose proof (cellsC3_frm C (s - 32) m2 m3 s _ _ _ CK (proj1 PMa) ltac:(lia) ltac:(lia) ltac:(lia) CE2) as CE3.
  assert (PMa' : POSTM C A s m m3) by (eapply POSTM_trans; [exact PM2 | eapply POSTM_mono; [|exact PMa]; lia]).
  assert (CM3 : CMAPat m3 cm cv).
  { apply (CMAPat_frame m2); [exact CM2|]. intros x Hx. exact (LIVK_byte C A m2 m3 md cm 24 x CK HW2 (proj2 PMa) Lcm ltac:(lia) TOPcm Hx). }
  assert (Hcdr : (1 <= u res)%Z /\ (u res + 32 <= alloc_top (c_vm C))%Z).
  { pose proof (u64_range res). unfold round16 in TOP. change ((1 * 24 + 15) / 16)%Z with 2%Z in TOP. lia. }
  assert (Eres : res = Z_to_bv 64 (u res)) by (symmetry; apply zbv_self).
  set (cd := u res) in *. clearbody cd.
  rewrite Eres in Hres, L0, L1, L00, LEQ, ZERO.
  destruct (blk_range C A1 m3 _ (Z_to_bv 64 cd) 24 CK HWa L1 ltac:(lia)) as [Gcd _]. rewrite u_Z2bv in Gcd by lia.
  assert (CD0 : CMAPat m3 cd cmap0).
  { apply CMAPat_zero; [lia | lia |]. intros i Hi. unfold at_ in ZERO. rewrite u_Z2bv in ZERO by lia. apply ZERO. lia. }
  assert (SUBa : sub_live A A1) by (eapply sub_live_new; eassumption).
  assert (NEcmcd : Z_to_bv 64 cm <> Z_to_bv 64 cd) by (intros E; rewrite <- E in L0; rewrite Lcm in L0; discriminate).
  pose proof (blk_apart C A1 m3 _ _ _ _ _ CK HWa (SUBa _ _ Lcm) L1 NEcmcd ltac:(lia) ltac:(lia)) as APcd. rewrite !u_Z2bv in APcd by lia. apply O23LeptCmap2.box_i in APcd.
  assert (ALcd8 : (cd mod 8 = 0)%Z) by (clear - AL16; Z.div_mod_to_equations; lia).
  destruct (pcc_C al_rom r4 m3 s cm cd cv ltac:(lia) ltac:(lia) CM3 ltac:(lia) ALcm8 E2a Hres E8a) as (r5 & RUN5 & V2 & V1 & V10 & V11 & V8 & V9 & AG5).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWa)) | exact (mp_lazy _ (w_pure _ _ _ _ HWa)) | exact RUN5 |].
  assert (V4 : getr r5 4 = Z_to_bv 64 0x1381d0) by (rewrite (AG5 4) by (cbv; intuition discriminate); exact E4a).
  replace (0x10e6e0 : word) with (Z_to_bv 64 0x10e6e0) by (apply bv_eq; reflexivity).
  apply (W_calloc16_sure C A1 m3 _ r5 1 (4 * c_nalloc cv) (kR - 1) (bR - alloc_margin (1 * 24)) (Z_to_bv 64 0x73130) (s - 32) S CK HWa V10 V11 ltac:(lia) ltac:(lia) ltac:(lia)
           ltac:(rewrite with_vmmaps_vmmaps; exact Hrm1) ltac:(lia) ltac:(lia) ltac:(unfold ROOM_NMAX; lia) V1
           ltac:(red; apply bv_eq; reflexivity) V4 V2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)).
  intros A2 m5 vm2 r6 res2 HWb Hres2 CSb Hnz2 K0 K1 K00 KEQ ZERO2 AL16b TOP2 PMb Hrm2. rewrite with_vmmaps_twice. rewrite with_vmmaps_twice in HWb.
  replace (Z_to_bv 64 0x73130) with (0x73130 : word) by (apply bv_eq; reflexivity).
  assert (E2b : getr r6 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
  assert (E8b : getr r6 8 = Z_to_bv 64 cm) by (csr; reflexivity).
  assert (E9b : getr r6 9 = Z_to_bv 64 cd) by (csr; reflexivity).
  assert (E4b : getr r6 4 = Z_to_bv 64 0x1381d0) by (csr; reflexivity).
  pose proof (cellsC3_frm C (s - 32) m3 m5 s _ _ _ CK (proj1 PMb) ltac:(lia) ltac:(lia) ltac:(lia) CE3) as CE5.
  assert (PMb' : POSTM C A s m m5).
  { eapply POSTM_trans; [exact PMa'|]. apply (POSTM_sub C A A1); [exact SUBa|]. eapply POSTM_mono; [|exact PMb]. lia. }
  assert (Lcm1 : live A1 (Z_to_bv 64 cm) = Some 24%Z) by (exact (SUBa _ _ Lcm)).
  assert (Larr1 : live A1 (Z_to_bv 64 (c_arr cv)) = Some (4 * c_nalloc cv)%Z) by (exact (SUBa _ _ Larr)).
  assert (CM5 : CMAPat m5 cm cv).
  { apply (CMAPat_frame m3); [exact CM3|]. intros x Hx. exact (LIVK_byte C A1 m3 m5 _ cm 24 x CK HWa (proj2 PMb) Lcm1 ltac:(lia) TOPcm Hx). }
  assert (CD5 : CMAPat m5 cd cmap0).
  { apply (CMAPat_frame m3); [exact CD0|]. intros x Hx. exact (LIVK_byte C A1 m3 m5 _ cd 24 x CK HWa (proj2 PMb) L1 ltac:(lia) ltac:(lia) Hx). }
  assert (Hadr : (1 <= u res2)%Z /\ (u res2 + 4 * c_nalloc cv <= alloc_top (c_vm C))%Z).
  { pose proof (u64_range res2). pose proof (round16_ge (1 * (4 * c_nalloc cv)) ltac:(lia)). lia. }
  assert (Eres2 : res2 = Z_to_bv 64 (u res2)) by (symmetry; apply zbv_self).
  set (ad := u res2) in *. clearbody ad.
  rewrite Eres2 in Hres2, K0, K1, K00, KEQ, ZERO2.
  replace (1 * (4 * c_nalloc cv))%Z with (4 * c_nalloc cv)%Z in K1 by lia.
  destruct (blk_range C A2 m5 _ (Z_to_bv 64 ad) _ CK HWb K1 ltac:(lia)) as [Gad _]. rewrite u_Z2bv in Gad by lia.
  assert (NEcdad : cd <> ad) by (intros E; rewrite <- E in K0; congruence).
  assert (NEw : Z_to_bv 64 cd <> Z_to_bv 64 ad) by (intros E; apply NEcdad; apply (f_equal bv_unsigned) in E; rewrite !u_Z2bv in E by lia; exact E).
  assert (L1c : live A2 (Z_to_bv 64 cd) = Some 24%Z) by (rewrite (KEQ _ NEw); exact L1).
  assert (SUBb : sub_live A A2) by (eapply sub_live_trans; [exact SUBa | eapply sub_live_new; eassumption]).
  assert (SUB12 : sub_live A1 A2) by (eapply sub_live_new; eassumption).
  assert (Larr2 : live A2 (Z_to_bv 64 (c_arr cv)) = Some (4 * c_nalloc cv)%Z) by (exact (SUB12 _ _ Larr1)).
  assert (Lcm2 : live A2 (Z_to_bv 64 cm) = Some 24%Z) by (exact (SUB12 _ _ Lcm1)).
  assert (NEarad : Z_to_bv 64 (c_arr cv) <> Z_to_bv 64 ad) by (intros E; rewrite <- E in K0; rewrite Larr1 in K0; discriminate).
  pose proof (blk_apart C A2 m5 _ _ _ _ _ CK HWb Larr2 K1 NEarad ltac:(lia) ltac:(lia)) as APad. rewrite !u_Z2bv in APad by lia. apply O23LeptCmap2.box_i in APad.
  assert (NEcmad : Z_to_bv 64 cm <> Z_to_bv 64 ad) by (intros E; rewrite <- E in K0; rewrite Lcm1 in K0; discriminate).
  pose proof (blk_apart C A2 m5 _ _ _ _ _ CK HWb Lcm2 K1 NEcmad ltac:(lia) ltac:(lia)) as APcmad. rewrite !u_Z2bv in APcmad by lia. apply O23LeptCmap2.box_i in APcmad.
  pose proof (blk_apart C A2 m5 _ _ _ _ _ CK HWb L1c K1 NEw ltac:(lia) ltac:(lia)) as APcdad. rewrite !u_Z2bv in APcdad by lia. apply O23LeptCmap2.box_i in APcdad.
  destruct (pcc_D al_rom r6 m5 s cm cd ad cv ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) CM5 (O23LeptCmap2.box_e _ APcd)
              (blk_sok C A2 m5 _ cd 24 CK HWb L1c ltac:(lia) ltac:(lia) ltac:(lia)) ALcd8 E2b Hres2 E8b E9b)
    as (r7 & RUN7 & X2 & X1 & X10 & X11 & X12 & X8 & X9 & AG7).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWb)) | exact (mp_lazy _ (w_pure _ _ _ _ HWb)) | exact RUN7 |].
  set (M7 := wbytes m5 (Z_to_bv 64 cd) (word_to_le_bytes 8 (Z_to_bv 64 ad))) in *.
  assert (WP7 : W C A2 M7 (with_vmmaps vm2 md) /\ POSTM C A s m M7).
  { subst M7. apply (WP_blk C A A2 m _ _ (Z_to_bv 64 cd) _ 24); [exact CK | | exact L1c | exact L0 | exact L00 | exact SUBb | rewrite !u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia].
    split; [exact HWb | exact PMb']. }
  destruct WP7 as [HW7 PM7].
  assert (OUT7 : forall x : word, ~ (cd <= u x < cd + 8)%Z -> M7 x = m5 x).
  { intros x Hx. subst M7. apply wbytes_outside; rewrite ?length_N_to_le_bytes, u_Z2bv by lia; cbn; lia. }
  set (n := (4 * c_n cv)%Z) in *. assert (En : n = (4 * c_n cv)%Z) by reflexivity. clearbody n.
  destruct (blk_rdn C A2 M7 _ (c_arr cv) (4 * c_nalloc cv) (Z.to_nat n) CK HW7 Larr2 ltac:(lia) ltac:(lia) ltac:(lia)) as (bs & Hsrc & Hlen).
  assert (Hdst : store_ok SEGS M7 (Z_to_bv 64 ad) (length bs) = true).
  { rewrite Hlen. pose proof (blk_sok C A2 M7 _ ad (4 * c_nalloc cv) CK HW7 K1 ltac:(lia) ltac:(lia) ltac:(lia)) as SK.
    rewrite <- p16_segs in SK |- *. eapply store_ok_sub; [| exact SK | |]; rewrite ?u_Z2bv by lia; lia. }
  assert (HOKm : mcH M7 (Z_to_bv 64 ad) (Z_to_bv 64 (c_arr cv)) n bs).
  { pose proof (O23LeptCmap2.box_e _ APad) as APad'. constructor; rewrite ?u_Z2bv by lia; [lia | exact Hlen | rewrite Hlen; exact Hsrc | exact Hdst | lia | lia | lia]. }
  destruct (ref_memcpy M7 _ _ n bs al_rom HOKm r7 (Z_to_bv 64 0x73150) ltac:(red; apply bv_eq; reflexivity) X1 X10 X11 X12) as (r8 & RUN8 & KP8).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW7)) | exact (mp_lazy _ (w_pure _ _ _ _ HW7)) | exact RUN8 |].
  replace (Z_to_bv 64 0x73150) with (0x73150 : word) by (apply bv_eq; reflexivity).
  set (M8 := wbytes M7 (Z_to_bv 64 ad) bs) in *.
  assert (K2 : getr r8 2 = getr r7 2) by (apply KP8; in_kept). assert (K8 : getr r8 8 = getr r7 8) by (apply KP8; in_kept).
  assert (K9 : getr r8 9 = getr r7 9) by (apply KP8; in_kept). assert (K18 : getr r8 18 = getr r7 18) by (apply KP8; in_kept).
  assert (K19 : getr r8 19 = getr r7 19) by (apply KP8; in_kept).
  assert (K3 : getr r8 3 = getr r7 3) by (apply KP8; in_kept). assert (K4 : getr r8 4 = getr r7 4) by (apply KP8; in_kept).
  assert (K20 : getr r8 20 = getr r7 20) by (apply KP8; in_kept). assert (K21 : getr r8 21 = getr r7 21) by (apply KP8; in_kept).
  assert (K22 : getr r8 22 = getr r7 22) by (apply KP8; in_kept). assert (K23 : getr r8 23 = getr r7 23) by (apply KP8; in_kept).
  assert (K24 : getr r8 24 = getr r7 24) by (apply KP8; in_kept). assert (K25 : getr r8 25 = getr r7 25) by (apply KP8; in_kept).
  assert (K26 : getr r8 26 = getr r7 26) by (apply KP8; in_kept). assert (K27 : getr r8 27 = getr r7 27) by (apply KP8; in_kept).
  assert (HW8 : W C A2 M8 (with_vmmaps vm2 md)).
  { subst M8. apply (W_store_blk C A2 M7 _ (Z_to_bv 64 ad) (Z_to_bv 64 ad) (4 * c_nalloc cv) bs CK HW7 K1 K00); rewrite ?u_Z2bv by lia; [lia | rewrite Hlen; lia]. }
  assert (LAad : live A (Z_to_bv 64 ad) = None) by (rewrite <- (LEQ _ (not_eq_sym NEw)); exact K0).
  assert (PM8 : POSTM C A s m M8).
  { eapply POSTM_trans; [exact PM7|]. subst M8. apply (POSTM_blk C A A2 M7 _ (Z_to_bv 64 ad) (Z_to_bv 64 ad) (4 * c_nalloc cv) bs s CK HW7 K1 LAad SUBb);
      rewrite ?u_Z2bv by lia; [lia | rewrite Hlen; lia]. }
  assert (OUT8 : forall x : word, ~ (ad <= u x < ad + n)%Z -> M8 x = M7 x).
  { intros x Hx. subst M8. apply wbytes_outside; rewrite Hlen, u_Z2bv by lia; lia. }
  assert (CM8 : CMAPat M8 cm cv).
  { pose proof (O23LeptCmap2.box_e _ APcmad) as U1. pose proof (O23LeptCmap2.box_e _ APcd) as U2. apply (CMAPat_frame m5); [exact CM5|]. intros x Hx. rewrite OUT8 by lia. apply OUT7. lia. }
  assert (CD8 : CMAPat M8 cd (CMAPV ad 0 0 0 0)).
  { pose proof (O23LeptCmap2.box_e _ APcdad) as U3. apply (CMAPat_frame M7); [| intros x Hx; apply OUT8; lia]. subst M7. apply (CMAP_wr_arr m5 cd cmap0 ad); [exact CD5 | lia]. }
  assert (CE8 : cellsC3 M8 s ret (getr regs 8) (getr regs 9)).
  { eapply (cellsC3_out M7 _ ad (ad + n)); [exact OUT8 | lia | lia | lia |].
    eapply (cellsC3_out m5 _ cd (cd + 8)); [exact OUT7 | lia | lia | lia | exact CE5]. }
  pose proof CE8 as (C1 & C2 & C3).
  assert (SOK8 : store_ok SEGS M8 (Z_to_bv 64 cd) 24 = true) by (exact (blk_sok C A2 M8 _ cd 24 CK HW8 L1c ltac:(lia) ltac:(lia) ltac:(lia))).
  destruct (pcc_E al_rom r8 M8 s cm cd cv ret _ _ ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hret CM8 (O23LeptCmap2.box_e _ APcd) SOK8 ltac:(lia) C1 C2 C3
              ltac:(rewrite K2; exact X2) ltac:(rewrite K8; exact X8) ltac:(rewrite K9; exact X9))
    as (r9 & RUN9 & Z2 & Z1 & Z10 & Z8 & Z9 & AG9).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW8)) | exact (mp_lazy _ (w_pure _ _ _ _ HW8)) | exact RUN9 |].
  set (M9 := wbytes (wbytes M8 _ _) _ _).
  assert (WP9 : W C A2 M9 (with_vmmaps vm2 md) /\ POSTM C A s m M9).
  { subst M9.
    do 2 (apply (WP_blk C A A2 m _ _ (Z_to_bv 64 cd) _ 24); [exact CK | | exact L1c | exact L0 | exact L00 | exact SUBb | rewrite !u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia]).
    split; [exact HW8 | exact PM8]. }
  destruct WP9 as [HW9 PM9].
  apply (HK A2 M9 vm2 r9 cd ad).
  - exact HW9.
  - apply cs_kept_intro; csr; try reflexivity.
    all: rewrite ?Z8, ?Z9; try reflexivity.
    all: rewrite ?K3, ?K4, ?K18, ?K19, ?K20, ?K21, ?K22, ?K23, ?K24, ?K25, ?K26, ?K27; csr; reflexivity.
  - exact PM9.
  - exact Z10.
  - unfold O23LeptCmap2.cmap_copy. split; [exact CMOK|]. split; [lia|]. split; [lia|]. split; [exact AL16|]. split; [lia|]. split; [lia|]. split; [exact AL16b|]. split; [exact NEcdad|].
    split; [exact L0|]. split; [exact LAad|]. split; [exact L00|]. split; [exact K00|]. split; [exact L1c|]. split; [exact K1|].
    split; [intros q N1 N2; rewrite (KEQ q N2); apply LEQ; exact N1|].
    subst M9. unfold c_dna.
    apply (CMAP_wr_dna _ cd (CMAPV ad 0 0 (c_n cv) 0) (c_d cv) (c_nalloc cv)); [| pose proof (cf_d _ CWF); lia | lia].
    apply (CMAP_wr_n M8 cd (CMAPV ad 0 0 0 0) (c_n cv)); [exact CD8 | pose proof (cf_n _ CWF); lia].
  -    apply (aroom_mono A2 vm2 (kR - 1 - 1) (bR - alloc_margin (1 * 24) - alloc_margin (1 * (4 * c_nalloc cv)))); [exact Hrm2 | unfold RK_cmapcopy; lia | unfold RB_cmapcopy; lia].
Qed.

End CmapCopyS.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
