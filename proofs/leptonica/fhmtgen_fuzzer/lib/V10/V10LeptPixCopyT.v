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
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptArith2.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require Import V10LeptStderr V10LeptBase V10LeptUb.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require Import V10CL7a.
Import V10CL7a.V10LeptErr. Import V10CL7a.V10LeptPadBitsW.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require Import V10CL8a.
Import V10CL8a.V10LeptPixHdr.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require Import V10LeptPixCreate V10LeptCmapValid V10LeptCmap2 V10LeptPixCopyA V10LeptPixCopy.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require Import V10Kit.
Import V10Kit.V10MemcpyBase. Import V10Kit.V10Memcpy. Import V10Kit.V10Memset.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require Import LeptRoom LeptRoomPC.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require Import LeptRoom14.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require Import V10LeptPixT.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require Import LeptStructs2 LeptRoom10.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac sok_in SOK :=
  store_ok_peel;
  first [ exact SOK
        | eapply store_ok_sub; [ | exact SOK | | ]; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].

Ltac in_kept := unfold callee_kept; cbn [In]; repeat (first [left; reflexivity | right]).

Section PixCopyT.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V10Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Theorem pixcmapCopy_T : forall C A m md regs (s cm : Z) (cv : cmapv) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 48 + 16 + LSF <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x45480 ->
  getr regs 10 = Z_to_bv 64 cm ->
  CMAPat m cm cv -> cmap_ok cv -> live A (Z_to_bv 64 cm) = Some 24%Z -> live A (Z_to_bv 64 (c_arr cv)) = Some (4 * c_nalloc cv)%Z ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_cmapcopy <= kR)%Z -> (RB10_cmapcopy <= bR)%Z ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A s m m' ->
     ( (getr regs' 10 = Z_to_bv 64 0 /\ forall q, live A' q = live A q)
       \/ (exists cd ad : Z, getr regs' 10 = Z_to_bv 64 cd /\ cmap_copy C A A' m' cd ad cv) ) ->
     aroom A' vm' (kR - RK_cmapcopy) (bR - RB10_cmapcopy) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (0x19418 : word) m al_rom) md) S.
Proof.
  intros C A m md regs s cm cv ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 CM CMOK Lcm Larr kR bR Hrm Hrk Hrb HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold LSF in *.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof CM as (Hc0 & Hc64 & CWF & _). pose proof CMOK as (Hcd & Hcna & Hcn & Hcarr).
  assert (Hpow : (2 <= c_nalloc cv <= 256)%Z) by (rewrite Hcna; destruct Hcd as [->|[->|[->| ->]]]; cbn; lia). clear Hcd.
  pose proof (cf_arr _ CWF) as Rarr.
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lcm) as (_ & ALcm & _). rewrite u_Z2bv in ALcm by lia.
  assert (ALcm8 : (cm mod 8 = 0)%Z) by (clear - ALcm; Z.div_mod_to_equations; lia).
  pose proof (alloc_margin_small_le (1 * 24) ltac:(lia)) as HAM1. pose proof (alloc_margin_small_le (1 * (4 * c_nalloc cv)) ltac:(lia)) as HAM2. unfold RB10_small in HAM1, HAM2.
  pose proof (alloc_margin_ge (1 * 24) ltac:(lia)) as HAG1.
  unfold RK_cmapcopy in Hrk. unfold RB10_cmapcopy in Hrb.
  destruct (blk_range C A m md (Z_to_bv 64 cm) 24 CK HW Lcm ltac:(lia)) as [Gcm TOPcm]. rewrite u_Z2bv in Gcm, TOPcm by lia.
  destruct (blk_range C A m md (Z_to_bv 64 (c_arr cv)) _ CK HW Larr ltac:(lia)) as [Garr TOParr]. rewrite u_Z2bv in Garr, TOParr by lia.
  (* [comment removed for export] *)
  destruct (pcc_A al_rom regs m s cm ret ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) (W_sok_win C A m md (s - 32) 32 CK HW ltac:(lia) ltac:(cbn; lia)) H2 H1 H10)
    as (r1 & RUN1 & Q2 & Q1 & Q10 & Q11 & Q12 & Q8 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  assert (WP1 : W C A (FRC3 m s ret regs) md /\ POSTM C A s m (FRC3 m s ret regs)) by (unfold FRC3; wp_win CK).
  destruct WP1 as [HW1 PM1]. set (M1 := FRC3 m s ret regs) in *.
  pose proof (cellsC3_FRC3 m s ret regs ltac:(lia) ltac:(lia)) as CE1. fold M1 in CE1.
  assert (CM1 : CMAPat M1 cm cv).
  { apply (CMAPat_frame m M1 _ _ CM). intros x Hx. subst M1. unfold FRC3. rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. reflexivity. }
  apply (pixcmapIsValid_null_W C A M1 md r1 (s - 32) cm (s - 28) cv (Z_to_bv 64 0x1943c) S CK HW1 Q2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(lia) ltac:(lia) ltac:(lia) ltac:(apply sp_slot_al4'; [exact Hs16 | reflexivity]) Q1 ltac:(red; apply bv_eq; reflexivity) Q10 Q11 Q12 CM1 CMOK Lcm).
  intros m2 r2 HW2 CS2 PV2 A10.
  replace (Z_to_bv 64 0x1943c) with (0x1943c : word) by (apply bv_eq; reflexivity).
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
  (* [comment removed for export] *)
  destruct (pcc_B al_rom r2 m2 s ltac:(lia) ltac:(lia) Rv2 Y2) as (r3 & RUN3 & P2 & P1 & P10 & P11 & AG3).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact RUN3 |].
  assert (P4 : getr r3 4 = Z_to_bv 64 0x45480) by (rewrite (AG3 4) by (cbv; intuition discriminate); csr; reflexivity).
  assert (P8 : getr r3 8 = Z_to_bv 64 cm) by (rewrite (AG3 8) by (cbv; intuition discriminate); csr; reflexivity).
  replace (0x2b0d0 : word) with (Z_to_bv 64 0x2b0d0) by (apply bv_eq; reflexivity).
  apply (W_calloc16_sure C A m2 md r3 1 24 kR bR (Z_to_bv 64 0x19450) (s - 32) S CK HW2 P10 P11 ltac:(lia) ltac:(lia) ltac:(lia)
           Hrm ltac:(lia) ltac:(lia) ltac:(unfold ROOM_NMAX; lia) P1
           ltac:(red; apply bv_eq; reflexivity) P4 P2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)).
  intros A1 m3 vm1 r4 res HWa Hres CSa Hnz L0 L1 L00 LEQ ZERO AL16 TOP PMa Hrm1.
  replace (Z_to_bv 64 0x19450) with (0x19450 : word) by (apply bv_eq; reflexivity).
  assert (E2a : getr r4 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
  assert (E8a : getr r4 8 = Z_to_bv 64 cm) by (csr; reflexivity).
  assert (E4a : getr r4 4 = Z_to_bv 64 0x45480) by (csr; reflexivity).
  pose proof (cellsC3_frm C (s - 32) m2 m3 s _ _ _ CK (proj1 PMa) ltac:(lia) ltac:(lia) ltac:(lia) CE2) as CE3.
  assert (PMa' : POSTM C A s m m3) by (eapply POSTM_trans; [exact PM2 | eapply POSTM_mono; [|exact PMa]; lia]).
  assert (CM3 : CMAPat m3 cm cv).
  { apply (CMAPat_frame m2); [exact CM2|]. intros x Hx. exact (LIVK_byte C A m2 m3 md cm 24 x CK HW2 (proj2 PMa) Lcm ltac:(lia) TOPcm Hx). }
  (* [comment removed for export] *)
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
  pose proof (blk_apart C A1 m3 _ _ _ _ _ CK HWa (SUBa _ _ Lcm) L1 NEcmcd ltac:(lia) ltac:(lia)) as APcd. rewrite !u_Z2bv in APcd by lia. apply box_i in APcd.
  assert (ALcd8 : (cd mod 8 = 0)%Z) by (clear - AL16; Z.div_mod_to_equations; lia).
  destruct (pcc_C al_rom r4 m3 s cm cd cv ltac:(lia) ltac:(lia) CM3 ltac:(lia) ALcm8 E2a Hres E8a) as (r5 & RUN5 & V2 & V1 & V10 & V11 & V8 & V9 & AG5).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWa)) | exact (mp_lazy _ (w_pure _ _ _ _ HWa)) | exact RUN5 |].
  assert (V4 : getr r5 4 = Z_to_bv 64 0x45480) by (rewrite (AG5 4) by (cbv; intuition discriminate); exact E4a).
  replace (0x2b0d0 : word) with (Z_to_bv 64 0x2b0d0) by (apply bv_eq; reflexivity).
  apply (W_calloc16_sure C A1 m3 _ r5 1 (4 * c_nalloc cv) (kR - 1) (bR - alloc_margin (1 * 24)) (Z_to_bv 64 0x1946c) (s - 32) S CK HWa V10 V11 ltac:(lia) ltac:(lia) ltac:(lia)
           ltac:(rewrite with_vmmaps_vmmaps; exact Hrm1) ltac:(lia) ltac:(lia) ltac:(unfold ROOM_NMAX; lia) V1
           ltac:(red; apply bv_eq; reflexivity) V4 V2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)).
  intros A2 m5 vm2 r6 res2 HWb Hres2 CSb Hnz2 K0 K1 K00 KEQ ZERO2 AL16b TOP2 PMb Hrm2. rewrite with_vmmaps_twice. rewrite with_vmmaps_twice in HWb.
  replace (Z_to_bv 64 0x1946c) with (0x1946c : word) by (apply bv_eq; reflexivity).
  assert (E2b : getr r6 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
  assert (E8b : getr r6 8 = Z_to_bv 64 cm) by (csr; reflexivity).
  assert (E9b : getr r6 9 = Z_to_bv 64 cd) by (csr; reflexivity).
  assert (E4b : getr r6 4 = Z_to_bv 64 0x45480) by (csr; reflexivity).
  pose proof (cellsC3_frm C (s - 32) m3 m5 s _ _ _ CK (proj1 PMb) ltac:(lia) ltac:(lia) ltac:(lia) CE3) as CE5.
  assert (PMb' : POSTM C A s m m5).
  { eapply POSTM_trans; [exact PMa'|]. apply (POSTM_sub C A A1); [exact SUBa|]. eapply POSTM_mono; [|exact PMb]. lia. }
  assert (Lcm1 : live A1 (Z_to_bv 64 cm) = Some 24%Z) by (exact (SUBa _ _ Lcm)).
  assert (Larr1 : live A1 (Z_to_bv 64 (c_arr cv)) = Some (4 * c_nalloc cv)%Z) by (exact (SUBa _ _ Larr)).
  assert (CM5 : CMAPat m5 cm cv).
  { apply (CMAPat_frame m3); [exact CM3|]. intros x Hx. exact (LIVK_byte C A1 m3 m5 _ cm 24 x CK HWa (proj2 PMb) Lcm1 ltac:(lia) TOPcm Hx). }
  assert (CD5 : CMAPat m5 cd cmap0).
  { apply (CMAPat_frame m3); [exact CD0|]. intros x Hx. exact (LIVK_byte C A1 m3 m5 _ cd 24 x CK HWa (proj2 PMb) L1 ltac:(lia) ltac:(lia) Hx). }
  (* [comment removed for export] *)
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
  pose proof (blk_apart C A2 m5 _ _ _ _ _ CK HWb Larr2 K1 NEarad ltac:(lia) ltac:(lia)) as APad. rewrite !u_Z2bv in APad by lia. apply box_i in APad.
  assert (NEcmad : Z_to_bv 64 cm <> Z_to_bv 64 ad) by (intros E; rewrite <- E in K0; rewrite Lcm1 in K0; discriminate).
  pose proof (blk_apart C A2 m5 _ _ _ _ _ CK HWb Lcm2 K1 NEcmad ltac:(lia) ltac:(lia)) as APcmad. rewrite !u_Z2bv in APcmad by lia. apply box_i in APcmad.
  pose proof (blk_apart C A2 m5 _ _ _ _ _ CK HWb L1c K1 NEw ltac:(lia) ltac:(lia)) as APcdad. rewrite !u_Z2bv in APcdad by lia. apply box_i in APcdad.
  destruct (pcc_D al_rom r6 m5 s cm cd ad cv ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) CM5 (box_e _ APcd)
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
  (* [comment removed for export] *)
  set (n := (4 * c_n cv)%Z) in *. assert (En : n = (4 * c_n cv)%Z) by reflexivity. clearbody n.
  destruct (blk_rdn C A2 M7 _ (c_arr cv) (4 * c_nalloc cv) (Z.to_nat n) CK HW7 Larr2 ltac:(lia) ltac:(lia) ltac:(lia)) as (bs & Hsrc & Hlen).
  assert (Hdst : store_ok SEGS M7 (Z_to_bv 64 ad) (length bs) = true).
  { rewrite Hlen. pose proof (blk_sok C A2 M7 _ ad (4 * c_nalloc cv) CK HW7 K1 ltac:(lia) ltac:(lia) ltac:(lia)) as SK.
    rewrite <- p16_segs in SK |- *. eapply store_ok_sub; [| exact SK | |]; rewrite ?u_Z2bv by lia; lia. }
  assert (HOKm : mcH M7 (Z_to_bv 64 ad) (Z_to_bv 64 (c_arr cv)) n bs).
  { pose proof (box_e _ APad) as APad'. constructor; rewrite ?u_Z2bv by lia; [lia | exact Hlen | rewrite Hlen; exact Hsrc | exact Hdst | lia | lia | lia]. }
  destruct (ref_memcpy M7 _ _ n bs al_rom HOKm r7 (Z_to_bv 64 0x1948c) ltac:(red; apply bv_eq; reflexivity) X1 X10 X11 X12) as (r8 & RUN8 & KP8).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW7)) | exact (mp_lazy _ (w_pure _ _ _ _ HW7)) | exact RUN8 |].
  replace (Z_to_bv 64 0x1948c) with (0x1948c : word) by (apply bv_eq; reflexivity).
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
  { pose proof (box_e _ APcmad) as U1. pose proof (box_e _ APcd) as U2. apply (CMAPat_frame m5); [exact CM5|]. intros x Hx. rewrite OUT8 by lia. apply OUT7. lia. }
  assert (CD8 : CMAPat M8 cd (CMAPV ad 0 0 0 0)).
  { pose proof (box_e _ APcdad) as U3. apply (CMAPat_frame M7); [| intros x Hx; apply OUT8; lia]. subst M7. apply (CMAP_wr_arr m5 cd cmap0 ad); [exact CD5 | lia]. }
  assert (CE8 : cellsC3 M8 s ret (getr regs 8) (getr regs 9)).
  { eapply (cellsC3_out M7 _ ad (ad + n)); [exact OUT8 | lia | lia | lia |].
    eapply (cellsC3_out m5 _ cd (cd + 8)); [exact OUT7 | lia | lia | lia | exact CE5]. }
  pose proof CE8 as (C1 & C2 & C3).
  assert (SOK8 : store_ok SEGS M8 (Z_to_bv 64 cd) 24 = true) by (exact (blk_sok C A2 M8 _ cd 24 CK HW8 L1c ltac:(lia) ltac:(lia) ltac:(lia))).
  destruct (pcc_E al_rom r8 M8 s cm cd cv ret _ _ ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hret CM8 (box_e _ APcd) SOK8 ltac:(lia) C1 C2 C3
              ltac:(rewrite K2; exact X2) ltac:(rewrite K8; exact X8) ltac:(rewrite K9; exact X9))
    as (r9 & RUN9 & Z2 & Z1 & Z10 & Z8 & Z9 & AG9).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW8)) | exact (mp_lazy _ (w_pure _ _ _ _ HW8)) | exact RUN9 |].
  set (M9 := wbytes (wbytes M8 _ _) _ _).
  assert (WP9 : W C A2 M9 (with_vmmaps vm2 md) /\ POSTM C A s m M9).
  { subst M9.
    do 2 (apply (WP_blk C A A2 m _ _ (Z_to_bv 64 cd) _ 24); [exact CK | | exact L1c | exact L0 | exact L00 | exact SUBb | rewrite !u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia]).
    split; [exact HW8 | exact PM8]. }
  destruct WP9 as [HW9 PM9].
  apply (HK A2 M9 vm2 r9).
  - exact HW9.
  - apply cs_kept_intro; csr; try reflexivity.
    all: rewrite ?Z8, ?Z9; try reflexivity.
    all: rewrite ?K3, ?K4, ?K18, ?K19, ?K20, ?K21, ?K22, ?K23, ?K24, ?K25, ?K26, ?K27; csr; reflexivity.
  - exact PM9.
  - right. exists cd, ad. split; [exact Z10|].
    unfold cmap_copy. split; [exact CMOK|]. split; [lia|]. split; [lia|]. split; [exact AL16|]. split; [lia|]. split; [lia|]. split; [exact AL16b|]. split; [exact NEcdad|].
    split; [exact L0|]. split; [exact LAad|]. split; [exact L00|]. split; [exact K00|]. split; [exact L1c|]. split; [exact K1|].
    split; [intros q N1 N2; rewrite (KEQ q N2); apply LEQ; exact N1|].
    subst M9. unfold c_dna.
    apply (CMAP_wr_dna _ cd (CMAPV ad 0 0 (c_n cv) 0) (c_d cv) (c_nalloc cv)); [| pose proof (cf_d _ CWF); lia | lia].
    apply (CMAP_wr_n M8 cd (CMAPV ad 0 0 0 0) (c_n cv)); [exact CD8 | pose proof (cf_n _ CWF); lia].
  - (* [comment removed for export] *)
    apply (aroom_mono A2 vm2 (kR - 1 - 1) (bR - alloc_margin (1 * 24) - alloc_margin (1 * (4 * c_nalloc cv)))); [exact Hrm2 | unfold RK_cmapcopy; lia | unfold RB10_cmapcopy; lia].
Qed.

Theorem pixCopyColormap_T : forall C Ar A m md regs (s pixd pixs : Z) (vd vs : pixv) (cv : cmapv) (ret : word) (S : TSet),
  Cok C -> W C A m md -> sub_live Ar A ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 96 + 16 + LSF <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x45480 ->
  getr regs 10 = Z_to_bv 64 pixd -> getr regs 11 = Z_to_bv 64 pixs ->
  PIXat m pixd vd -> PIXat m pixs vs -> p_d vd = p_d vs -> p_cmap vd = 0%Z -> pixd <> pixs ->
  live A (Z_to_bv 64 pixd) = Some 64%Z -> live Ar (Z_to_bv 64 pixd) = None -> live (c_A0 C) (Z_to_bv 64 pixd) = None ->
  live A (Z_to_bv 64 pixs) = Some 64%Z ->
  (p_cmap vs = 0%Z \/ (CMAPat m (p_cmap vs) cv /\ cmap_ok cv /\ live A (Z_to_bv 64 (p_cmap vs)) = Some 24%Z /\
                        live A (Z_to_bv 64 (c_arr cv)) = Some (4 * c_nalloc cv)%Z)) ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_cmapcopy <= kR)%Z -> (RB10_cmapcopy <= bR)%Z ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C Ar s m m' ->
     ( ((forall q, live A' q = live A q) /\ PIXat m' pixd vd)
       \/ (exists cd ad : Z, cmap_copy C A A' m' cd ad cv /\ PIXat m' pixd (set_cmap vd cd)) ) ->
     aroom A' vm' (kR - RK_cmapcopy) (bR - RB10_cmapcopy) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (0x16690 : word) m al_rom) md) S.
Proof.
  intros C Ar A m md regs s pixd pixs vd vs cv ret S CK HW SUB H2 Hs16 Hlo Hhi H1 Hret H4 H10 H11 PXd PXs Ed Ecm NEds Lpd Lpd0 Lpd00 Lps HCM kR bR Hrm Hrk Hrb HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold LSF in *.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof PXd as (Hd0 & Hd64 & WFd & _). pose proof PXs as (Hs0 & Hs64' & WFs & _). pose proof (wf_cmap _ WFs) as Rcm.
  destruct (blk_range C A m md (Z_to_bv 64 pixd) 64 CK HW Lpd ltac:(lia)) as [Gpd TOPpd]. rewrite u_Z2bv in Gpd, TOPpd by lia.
  destruct (blk_range C A m md (Z_to_bv 64 pixs) 64 CK HW Lps ltac:(lia)) as [Gps TOPps]. rewrite u_Z2bv in Gps, TOPps by lia.
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lpd) as (_ & ALpd & _). rewrite u_Z2bv in ALpd by lia.
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lps) as (_ & ALps & _). rewrite u_Z2bv in ALps by lia.
  (* [comment removed for export] *)
  destruct (pcm_A al_rom regs m s pixd pixs vd vs ret ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) NEds ALpd ALps PXd PXs Ed Ecm ltac:(lia) ltac:(lia)
              (W_sok_win C A m md (s - 48) 48 CK HW ltac:(lia) ltac:(cbn; lia)) H2 H1 H10 H11)
    as (r1 & RUN1 & Q2 & Q1 & Q10 & Q11 & Q8 & Q9 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  assert (WP1 : W C A (V10LeptPixCopyA.FR4c m s ret regs) md /\ POSTM C A s m (V10LeptPixCopyA.FR4c m s ret regs)) by (unfold V10LeptPixCopyA.FR4c; wp_win CK).
  destruct WP1 as [HW1 PM1]. set (M1 := V10LeptPixCopyA.FR4c m s ret regs) in *.
  pose proof (V10LeptPixCopyA.cells3_FR4c m s ret regs ltac:(lia) ltac:(lia)) as CE1. fold M1 in CE1.
  assert (OUT1 : forall x : word, ~ (s - 48 <= u x < s)%Z -> M1 x = m x).
  { intros x Hx. subst M1. unfold V10LeptPixCopyA.FR4c. rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. reflexivity. }
  assert (PXd1 : PIXat M1 pixd vd) by (apply (PIXat_frame m M1 _ _ PXd); intros x Hx; apply OUT1; lia).
  assert (Q4 : getr r1 4 = Z_to_bv 64 0x45480) by (rewrite (AG1 4) by (cbv; intuition discriminate); exact H4).
  destruct HCM as [CM0 | (CM & CMOK & Lcm & Larr)].
  - (* [comment removed for export] *)
    rewrite CM0 in Q8.
    destruct (pcm_A0 al_rom r1 M1 s ret (getr regs 8) (getr regs 9) ltac:(lia) ltac:(lia) Hret CE1 Q2 Q8) as (r2 & RUN2 & P2 & P1 & P10 & P8 & P9 & AG2).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN2 |].
    rewrite <- (with_vmmaps_same md). apply (HK A M1 (m_vmmaps md) r2).
    + rewrite with_vmmaps_same. exact HW1.
    + apply cs_kept_intro; csr; try reflexivity. all: rewrite ?P8, ?P9, ?Q9; reflexivity.
    + apply (POSTM_sub C Ar A); [exact SUB | exact PM1].
    + left. split; [intros q; reflexivity | exact PXd1].
    + room_tac.
  - (* [comment removed for export] *)
    pose proof CM as (Hc0 & Hc64 & CWF & _). set (cm := p_cmap vs) in *.
    destruct (blk_range C A m md (Z_to_bv 64 cm) 24 CK HW Lcm ltac:(lia)) as [Gcm TOPcm]. rewrite u_Z2bv in Gcm, TOPcm by lia.
    assert (CM1 : CMAPat M1 cm cv) by (apply (CMAPat_frame m M1 _ _ CM); intros x Hx; apply OUT1; lia).
    destruct (pcm_A1 al_rom r1 M1 s cm pixd ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Q2 Q8 Q10) as (r2 & RUN2 & P2 & P1 & P10 & P11 & P12 & P8 & P9 & AG2).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN2 |].
    apply (pixcmapIsValid_null_W C A M1 md r2 (s - 48) cm (s - 36) cv (Z_to_bv 64 0x1670c) S CK HW1 P2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
             ltac:(lia) ltac:(lia) ltac:(lia) ltac:(apply sp_slot_al4'; [exact Hs16 | reflexivity]) P1 ltac:(red; apply bv_eq; reflexivity) P10 P11 P12 CM1 CMOK Lcm).
    intros m2 r3 HW2 CS2 PV2 A10.
    replace (Z_to_bv 64 0x1670c) with (0x1670c : word) by (apply bv_eq; reflexivity).
    pose proof PV2 as [F2 L2].
    assert (PM2 : POSTM C A s m m2).
    { eapply POSTM_trans; [exact PM1|].
      unshelve (eapply (POSTM_absorb C A A M1 _ m2 s (s - 48) _ _ CK HW1 (sub_live_refl A) ltac:(lia) _ _ Hhi PV2)); rewrite ?length_N_to_le_bytes, u_Z2bv by lia; cbn; lia. }
    assert (Rv2 : rdn SEGS m2 (Z_to_bv 64 (s - 36)) 4 = Some (Z_to_le_bytes 4 1)).
    { rewrite (FRM_rdn16 C (s - 48) _ m2 (s - 36) 4 CK F2) by (cbn; lia). rewrite <- (w2l_Z4 1) by lia. apply rdn_wbytes_hit4. rewrite u_Z2bv by lia. lia. }
    assert (CE2 : V10LeptPixCopyA.cells3 m2 s ret (getr regs 8) (getr regs 9)).
    { apply (V10LeptPixCopyA.cells3_frm C (s - 48) (wbytes M1 (Z_to_bv 64 (s - 36)) (word_to_le_bytes 4 (Z_to_bv 64 1))) m2 s _ _ _ CK F2 ltac:(lia) ltac:(lia) ltac:(lia)).
      eapply (V10LeptPixCopyA.cells3_out M1 _ (s - 36) (s - 32)); [intros x Hx; apply wbytes_outside; rewrite ?length_N_to_le_bytes, u_Z2bv by lia; cbn; lia | lia | lia | lia | exact CE1]. }
    assert (HW1v : W C A (wbytes M1 (Z_to_bv 64 (s - 36)) (word_to_le_bytes 4 (Z_to_bv 64 1))) md).
    { apply (W_store_win C A M1 md _ _ CK HW1); rewrite ?length_N_to_le_bytes, u_Z2bv by lia; cbn; lia. }
    assert (EQ2 : forall (p k : Z) (x : word), live A (Z_to_bv 64 p) = Some k -> (0 <= p)%Z -> (p + k <= alloc_top (c_vm C))%Z -> (p <= u x < p + k)%Z -> m2 x = M1 x).
    { intros p k x L G0 TP Hx. rewrite (LIVK_byte C A _ m2 md p k x CK HW1v L2 L G0 TP Hx). apply wbytes_outside; rewrite ?length_N_to_le_bytes, u_Z2bv by lia; cbn; lia. }
    assert (PXd2 : PIXat m2 pixd vd) by (apply (PIXat_frame M1); [exact PXd1 | intros x Hx; exact (EQ2 pixd 64%Z x Lpd ltac:(lia) TOPpd Hx)]).
    assert (CM2 : CMAPat m2 cm cv) by (apply (CMAPat_frame M1); [exact CM1 | intros x Hx; exact (EQ2 cm 24%Z x Lcm ltac:(lia) TOPcm Hx)]).
    assert (Y2 : getr r3 2 = Z_to_bv 64 (s - 48)) by (csr; reflexivity).
    assert (Y8 : getr r3 8 = Z_to_bv 64 cm) by (csr; reflexivity).
    (* [comment removed for export] *)
    destruct (pcm_B al_rom r3 m2 s cm ltac:(lia) ltac:(lia) Rv2 Y2 Y8) as (r4 & RUN4 & X2 & X1 & X10 & AG4).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact RUN4 |].
    assert (X4 : getr r4 4 = Z_to_bv 64 0x45480) by (rewrite (AG4 4) by (cbv; intuition discriminate); csr; reflexivity).
    apply (pixcmapCopy_T C A m2 md r4 (s - 48) cm cv (Z_to_bv 64 0x1671c) S CK HW2 X2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
             ltac:(unfold LSF; lia) ltac:(lia) X1 ltac:(red; apply bv_eq; reflexivity) X4 X10 CM2 CMOK Lcm Larr kR bR Hrm Hrk Hrb).
    intros A1 m3 vm1 r5 HWa CSa PMa OUTa Hrm1.
    replace (Z_to_bv 64 0x1671c) with (0x1671c : word) by (apply bv_eq; reflexivity).
    pose proof (V10LeptPixCopyA.cells3_frm C (s - 48) m2 m3 s _ _ _ CK (proj1 PMa) ltac:(lia) ltac:(lia) ltac:(lia) CE2) as CE3.
    assert (PMa' : POSTM C A s m m3) by (eapply POSTM_trans; [exact PM2 | eapply POSTM_mono; [|exact PMa]; lia]).
    assert (PXd3 : PIXat m3 pixd vd) by (apply (PIXat_frame m2); [exact PXd2 | intros x Hx; exact (LIVK_byte C A m2 m3 md pixd 64 x CK HW2 (proj2 PMa) Lpd ltac:(lia) TOPpd Hx)]).
    assert (E2a : getr r5 2 = Z_to_bv 64 (s - 48)) by (csr; reflexivity).
    assert (E9a : getr r5 9 = Z_to_bv 64 pixd) by (csr; reflexivity).
    destruct OUTa as [[Hres0 LIVEQ] | (cd & ad & Hres & CC)].
    + (* [comment removed for export] *)
      destruct (pcm_C0 al_rom r5 m3 s (W_sev_got C A1 m3 _ HWa) (W_sev C A1 m3 _ HWa) E2a Hres0) as (r6 & RUN6 & V2 & V1 & V10 & V11 & V12 & AG6).
      eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWa)) | exact (mp_lazy _ (w_pure _ _ _ _ HWa)) | exact RUN6 |].
      apply (returnErrorInt_W C A1 m3 _ r6 (s - 48) 0x10558 0x1064b 14 15 (Z_to_bv 64 0x16870) (Z_to_bv 64 1) S CK HWa V2
               ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold LSF; lia) ltac:(lia) V1 ltac:(red; apply bv_eq; reflexivity)
               V10 V11 V12 V10LeptPixCopyA.str_cmapd_not_made' V10LeptPixCopyA.str_pixCopyColormap).
      intros m4 r7 HW4 OUT4 GR4 CS4 B10. unfold LSF in OUT4.
      replace (Z_to_bv 64 0x16870) with (0x16870 : word) by (apply bv_eq; reflexivity).
      pose proof (V10LeptPixCopyA.cells3_out m3 m4 _ _ s _ _ _ OUT4 ltac:(lia) ltac:(lia) ltac:(lia) CE3) as CE4.
      destruct (pcm_E al_rom r7 m4 s ret _ _ ltac:(lia) ltac:(lia) Hret CE4 ltac:(csr; reflexivity) B10) as (r8 & RUN8 & Z2 & Z1 & Z10 & Z8 & Z9 & AG8).
      eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW4)) | exact (mp_lazy _ (w_pure _ _ _ _ HW4)) | exact RUN8 |].
      apply (HK A1 m4 vm1 r8).
      * exact HW4.
      * apply cs_kept_intro; csr; try reflexivity. all: rewrite ?Z8, ?Z9, ?Q9; reflexivity.
      * apply (POSTM_sub C Ar A); [exact SUB|]. eapply POSTM_trans; [exact PMa'|]. apply (POSTM_sub C A A1); [apply sub_live_eq; exact LIVEQ|].
        eapply (POSTM_range C A1 m3 _ m4); [exact CK | exact HWa | exact OUT4 | lia | lia | lia].
      * left. split; [exact LIVEQ|]. apply (PIXat_frame m3); [exact PXd3|]. intros x Hx. apply OUT4. lia.
      * exact Hrm1.
    + (* [comment removed for export] *)
      pose proof CC as (CMOKc & Gcd & TOPcd & ALcd & Gad & TOPad & ALad & NEcdad & L0 & LA0 & L00 & LA00 & L1 & K1 & LEQ & CD3).
      assert (NEpdcd : Z_to_bv 64 pixd <> Z_to_bv 64 cd) by (intros E; rewrite E in Lpd; rewrite Lpd in L0; discriminate).
      assert (NEpdad : Z_to_bv 64 pixd <> Z_to_bv 64 ad) by (intros E; rewrite E in Lpd; rewrite Lpd in LA0; discriminate).
      assert (Lpd1 : live A1 (Z_to_bv 64 pixd) = Some 64%Z) by (rewrite (LEQ _ NEpdcd NEpdad); exact Lpd).
      assert (SUBa : sub_live A A1) by (eapply sub_live_new2; [exact L0 | exact LA0 | exact L1 | exact K1 | exact LEQ]).
      assert (SUBr : sub_live Ar A1) by (eapply sub_live_trans; [exact SUB | exact SUBa]).
      pose proof (blk_apart C A1 m3 _ _ _ _ _ CK HWa Lpd1 L1 NEpdcd ltac:(lia) ltac:(lia)) as APpdcd. rewrite !u_Z2bv in APpdcd by lia. apply box_i in APpdcd.
      destruct (pcm_C al_rom r5 m3 s cd pixd vd ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) PXd3 Ecm ltac:(lia)
                  (W_sok_win C A1 m3 _ (s - 48) 48 CK HWa ltac:(lia) ltac:(cbn; lia)) (blk_sok C A1 m3 _ pixd 64 CK HWa Lpd1 ltac:(lia) ltac:(lia) ltac:(lia)) E2a Hres E9a)
        as (r6 & RUN6 & V2 & V1 & V10 & V11 & V12 & V9 & AG6).
      eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWa)) | exact (mp_lazy _ (w_pure _ _ _ _ HWa)) | exact RUN6 |].
      set (M5 := wbytes m3 (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))).
      set (M6 := wbytes M5 (Z_to_bv 64 (pixd + 48)) (word_to_le_bytes 8 (Z_to_bv 64 cd))).
      assert (WP5 : W C A1 M5 (with_vmmaps vm1 md) /\ POSTM C Ar s m M5).
      { subst M5. apply (WP_win C A1 Ar m m3 _ _ _ s CK); [| exact SUBr | rewrite u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia | lia].
        split; [exact HWa | apply (POSTM_sub C Ar A); [exact SUB | exact PMa']]. }
      assert (WP6 : W C A1 M6 (with_vmmaps vm1 md) /\ POSTM C Ar s m M6).
      { subst M6. apply (WP_blk C Ar A1 m M5 _ (Z_to_bv 64 pixd) _ 64); [exact CK | exact WP5 | exact Lpd1 | exact Lpd0 | exact Lpd00 | exact SUBr | rewrite !u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia]. }
      destruct WP6 as [HW6 PM6].
      assert (OUT5 : forall x : word, ~ (s - 32 <= u x < s - 24)%Z -> M5 x = m3 x).
      { intros x Hx. subst M5. apply wbytes_outside; rewrite ?length_N_to_le_bytes, u_Z2bv by lia; cbn; lia. }
      assert (OUT6 : forall x : word, ~ (pixd + 48 <= u x < pixd + 56)%Z -> M6 x = M5 x).
      { intros x Hx. subst M6. apply wbytes_outside; rewrite ?length_N_to_le_bytes, u_Z2bv by lia; cbn; lia. }
      assert (PXd6 : PIXat M6 pixd (set_cmap vd cd)).
      { subst M6. apply PIX_wr_cmap; [|lia]. apply (PIXat_frame m3); [exact PXd3|]. intros x Hx. apply OUT5. lia. }
      set (cv' := CMAPV ad (c_d cv) (c_nalloc cv) (c_n cv) 0) in *.
      assert (CD6 : CMAPat M6 cd cv').
      { pose proof (box_e _ APpdcd) as U1. apply (CMAPat_frame m3); [exact CD3|]. intros x Hx. rewrite OUT6 by lia. apply OUT5. lia. }
      assert (CE6 : V10LeptPixCopyA.cells3 M6 s ret (getr regs 8) (getr regs 9)).
      { eapply (V10LeptPixCopyA.cells3_out M5 _ (pixd + 48) (pixd + 56)); [exact OUT6 | lia | lia | lia |].
        eapply (V10LeptPixCopyA.cells3_out m3 _ (s - 32) (s - 24)); [exact OUT5 | lia | lia | lia | exact CE3]. }
      pose proof (cmap_ok_copy cv ad CMOK ltac:(lia)) as CMOK'.
      apply (pixcmapIsValid_null_W C A1 M6 _ r6 (s - 48) cd (s - 32) cv' (Z_to_bv 64 0x16754) S CK HW6 V2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
               ltac:(lia) ltac:(lia) ltac:(lia) ltac:(apply sp_slot_al4'; [exact Hs16 | reflexivity]) V1 ltac:(red; apply bv_eq; reflexivity) V10 V11 V12 CD6 CMOK' L1).
      intros m7 r7 HW7 CS7 PV7 B10.
      replace (Z_to_bv 64 0x16754) with (0x16754 : word) by (apply bv_eq; reflexivity).
      pose proof PV7 as [F7 L7].
      assert (PM7 : POSTM C Ar s m m7).
      { eapply POSTM_trans; [exact PM6|].
        unshelve (eapply (POSTM_absorb C Ar A1 M6 _ m7 s (s - 48) _ _ CK HW6 SUBr ltac:(lia) _ _ Hhi PV7)); rewrite ?length_N_to_le_bytes, u_Z2bv by lia; cbn; lia. }
      assert (Rv7 : rdn SEGS m7 (Z_to_bv 64 (s - 32)) 4 = Some (Z_to_le_bytes 4 1)).
      { rewrite (FRM_rdn16 C (s - 48) _ m7 (s - 32) 4 CK F7) by (cbn; lia). rewrite <- (w2l_Z4 1) by lia. apply rdn_wbytes_hit4. rewrite u_Z2bv by lia. lia. }
      assert (CE7 : V10LeptPixCopyA.cells3 m7 s ret (getr regs 8) (getr regs 9)).
      { apply (V10LeptPixCopyA.cells3_frm C (s - 48) (wbytes M6 (Z_to_bv 64 (s - 32)) (word_to_le_bytes 4 (Z_to_bv 64 1))) m7 s _ _ _ CK F7 ltac:(lia) ltac:(lia) ltac:(lia)).
        eapply (V10LeptPixCopyA.cells3_out M6 _ (s - 32) (s - 28)); [intros x Hx; apply wbytes_outside; rewrite ?length_N_to_le_bytes, u_Z2bv by lia; cbn; lia | lia | lia | lia | exact CE6]. }
      assert (HW6v : W C A1 (wbytes M6 (Z_to_bv 64 (s - 32)) (word_to_le_bytes 4 (Z_to_bv 64 1))) (with_vmmaps vm1 md)).
      { apply (W_store_win C A1 M6 _ _ _ CK HW6); rewrite ?length_N_to_le_bytes, u_Z2bv by lia; cbn; lia. }
      assert (EQ7 : forall (p k : Z) (x : word), live A1 (Z_to_bv 64 p) = Some k -> (0 <= p)%Z -> (p + k <= alloc_top (c_vm C))%Z -> (p <= u x < p + k)%Z -> m7 x = M6 x).
      { intros p k x L G0 TP Hx. rewrite (LIVK_byte C A1 _ m7 _ p k x CK HW6v L7 L G0 TP Hx). apply wbytes_outside; rewrite ?length_N_to_le_bytes, u_Z2bv by lia; cbn; lia. }
      assert (Y2' : getr r7 2 = Z_to_bv 64 (s - 48)) by (csr; reflexivity).
      destruct (pcm_D al_rom r7 m7 s ret _ _ ltac:(lia) ltac:(lia) Hret CE7 Rv7 Y2') as (r8 & RUN8 & Z2 & Z1 & Z10 & Z8 & Z9 & AG8).
      eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW7)) | exact (mp_lazy _ (w_pure _ _ _ _ HW7)) | exact RUN8 |].
      apply (HK A1 m7 vm1 r8).
      * exact HW7.
      * apply cs_kept_intro; csr; try reflexivity. all: rewrite ?Z8, ?Z9, ?Q9; reflexivity.
      * exact PM7.
      * right. exists cd, ad. split.
        -- unfold cmap_copy. do 15 (split; [assumption|]). apply (CMAPat_frame M6); [exact CD6|]. intros x Hx. exact (EQ7 cd 24%Z x L1 ltac:(lia) ltac:(lia) Hx).
        -- apply (PIXat_frame M6); [exact PXd6|]. intros x Hx. exact (EQ7 pixd 64%Z x Lpd1 ltac:(lia) TOPpd Hx).
      * exact Hrm1.
Qed.

Definition TKt (C : lctx) (A : AS) (m : word -> option byte) (md : Model) (regs : bvmap 5 word) (s w h d : Z) (cv : cmapv) (ret : word) (S : TSet) (kR bR : Z) : Prop :=
  forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A s m m' ->
     ( (getr regs' 10 = Z_to_bv 64 0 /\ forall q, live A' q = live A q)
       \/ (exists pixd cd data, getr regs' 10 = Z_to_bv 64 pixd /\ pixt_new C A A' m' pixd w h d cd data cv) ) ->
     aroom A' vm' (kR - RK_pixcopy) (bR - (RB10_pixcopy (4 * (wpl_of w d * h)))) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S.

Lemma ptn_tail_T : forall C A A2 m md m4 vm2 regs r4 (s pixs pixd w h d cm datas cd data : Z) (cv : cmapv) (ret : word) (S : TSet) (kR bR : Z),
  Cok C -> TKt C A m md regs s w h d cv ret S kR bR ->
  aroom A2 vm2 (kR - RK_pixcopy) (bR - (RB10_pixcopy (4 * (wpl_of w d * h)))) ->
  (s mod 16 = 0)%Z -> (c_top C - LSTK + 128 + 16 + LSF <= s)%Z -> (s <= c_top C)%Z -> ret_ok ret ->
  W C A2 m4 (with_vmmaps vm2 md) -> POSTM C A s m m4 -> sub_live A A2 ->
  V10LeptPixCopy.cells4 m4 s ret (getr regs 8) (getr regs 9) (getr regs 18) ->
  getr r4 2 = Z_to_bv 64 (s - 32) -> getr r4 8 = Z_to_bv 64 pixd -> getr r4 9 = Z_to_bv 64 pixs ->
  (forall x, In x V10LeptPixCopy.tn_rest -> getr r4 x = getr regs x) -> getr regs 2 = Z_to_bv 64 s ->
  PIXat m4 pixs (hdv w h d cm datas) -> live A (Z_to_bv 64 pixs) = Some 64%Z ->
  hdr_ok w h d -> (1 <= w)%Z -> (1 <= h)%Z ->
  (4096 <= pixd)%Z -> (pixd + 64 <= alloc_top (c_vm C))%Z -> (pixd mod 16 = 0)%Z ->
  (4096 <= data)%Z -> (data + 4 * (wpl_of w d * h) <= alloc_top (c_vm C))%Z -> (data mod 16 = 0)%Z -> pixd <> data ->
  live A (Z_to_bv 64 pixd) = None -> live A (Z_to_bv 64 data) = None ->
  live (c_A0 C) (Z_to_bv 64 pixd) = None -> live (c_A0 C) (Z_to_bv 64 data) = None ->
  live A2 (Z_to_bv 64 pixd) = Some 64%Z -> live A2 (Z_to_bv 64 data) = Some (4 * (wpl_of w d * h))%Z ->
  PIXat m4 pixd (hdv w h d cd data) -> cmres C A A2 m4 pixd data cd cv ->
  realizes SEGS (mkCfg (mkst r4 (0x16428 : word) m4 al_rom) (with_vmmaps vm2 md)) S.
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
  set (Mw := wbytes (wbytes (wbytes m4 (Z_to_bv 64 (s - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0x16434)))
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
  assert (CE5 : V10LeptPixCopy.cells4 M5 s ret (getr regs 8) (getr regs 9) (getr regs 18)).
  { eapply (V10LeptPixCopy.cells4_out Mw _ (pixd + 32) (pixd + 48)); [exact OUT5 | lia | lia | lia |].
    eapply (V10LeptPixCopy.cells4_out m4 _ (s - 56) (s - 32)); [exact OUTw | lia | lia | lia | exact CE4]. }
  assert (NEpdw : Z_to_bv 64 pixd <> Z_to_bv 64 data) by (apply zbv_ne2; lia).
  apply (padbits_W C A A2 M5 _ r5 (s - 32) pixd (hdv w h d cd data) (Z_to_bv 64 0x16448) S CK HW5 SUB Y2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(unfold LSF; lia) ltac:(lia) Y1 ltac:(red; apply bv_eq; reflexivity) Y10 Y11 PXd5 DV ltac:(cbn; lia) ltac:(cbn; lia) eq_refl L2p).
  { cbn. exact L2d. } { cbn. exact LAd. } { cbn. exact L00d. } { cbn. exact NEpdw. }
  intros m6 r6 HW6 CS6 PM6 PX6 OUT6 A10. cbn [p_data p_wpl p_h hdv] in OUT6. unfold LSF in OUT6.
  replace (Z_to_bv 64 0x16448) with (0x16448 : word) by (apply bv_eq; reflexivity).
  pose proof (V10LeptPixCopy.cells4_frm C (s - 32) M5 m6 s _ _ _ _ CK (proj1 PM6) ltac:(lia) ltac:(lia) ltac:(lia) CE5) as (C1 & C2 & C3 & C4).
  destruct (ptn_D al_rom r6 m6 s pixd ret _ _ _ ltac:(lia) ltac:(lia) Hret C1 C2 C3 C4 ltac:(csr; reflexivity) ltac:(csr; reflexivity))
    as (r7 & RUN7 & Z2 & Z1 & Z10 & Z8 & Z9 & Z18 & AG7).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW6)) | exact (mp_lazy _ (w_pure _ _ _ _ HW6)) | exact RUN7 |].
  apply (HK A2 m6 vm2 r7 HW6).
  - apply cs_kept_intro; csr; try reflexivity. all: rewrite ?Z8, ?Z9, ?Z18; try reflexivity. all: unfold V10LeptPixCopy.tn_rest in RR; csr; reflexivity.
  - eapply POSTM_trans; [exact PM5 | eapply POSTM_mono; [|exact PM6]; lia].
  - right. exists pixd, cd, data. split; [exact Z10|].
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

Theorem pixCreateTemplateNoInit_T : forall C A m md regs (s pixs w h d cm datas : Z) (cv : cmapv) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 128 + 16 + LSF <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x45480 ->
  getr regs 10 = Z_to_bv 64 pixs ->
  PIXat m pixs (hdv w h d cm datas) -> hdr_ok w h d -> (1 <= w)%Z -> (1 <= h)%Z ->
  live A (Z_to_bv 64 pixs) = Some 64%Z ->
  (cm = 0%Z \/ (CMAPat m cm cv /\ cmap_ok cv /\ live A (Z_to_bv 64 cm) = Some 24%Z /\ live A (Z_to_bv 64 (c_arr cv)) = Some (4 * c_nalloc cv)%Z)) ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_pixcopy <= kR)%Z -> ((RB10_pixcopy (4 * (wpl_of w d * h))) <= bR)%Z ->
  TKt C A m md regs s w h d cv ret S kR bR ->
  realizes SEGS (mkCfg (mkst regs (0x1630c : word) m al_rom) md) S.
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
  assert (WP1 : W C A (V10LeptPixCopy.FR4 m s ret regs) md /\ POSTM C A s m (V10LeptPixCopy.FR4 m s ret regs)) by (unfold V10LeptPixCopy.FR4; wp_win CK).
  destruct WP1 as [HW1 PM1]. set (M1 := V10LeptPixCopy.FR4 m s ret regs) in *.
  pose proof (V10LeptPixCopy.cells4_FR4 m s ret regs ltac:(lia) ltac:(lia)) as CE1. fold M1 in CE1.
  assert (OUT1 : forall x : word, ~ (s - 32 <= u x < s)%Z -> M1 x = m x).
  { intros x Hx. subst M1. unfold V10LeptPixCopy.FR4. rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. reflexivity. }
  assert (Q4 : getr r1 4 = Z_to_bv 64 0x45480) by (rewrite (AG1 4) by (cbv; intuition discriminate); exact H4).
  assert (Hwh : (4 * (wpl_of w d * h) < 2 ^ 31)%Z) by lia.
  apply (pixCreateNoInit_T C A M1 md r1 (s - 32) w h d (Z_to_bv 64 0x16340) S CK HW1 Q2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(unfold LSF; lia) ltac:(lia) Q1 ltac:(red; apply bv_eq; reflexivity) Q4 Q10 Q11 Q12 ltac:(lia) ltac:(lia) Hwh ltac:(lia)).
  intros A1 m2 vm1 r2 HWa CSa PMa OUTa HRTa.
  replace (Z_to_bv 64 0x16340) with (0x16340 : word) by (apply bv_eq; reflexivity).
  pose proof (V10LeptPixCopy.cells4_frm C (s - 32) M1 m2 s _ _ _ _ CK (proj1 PMa) ltac:(lia) ltac:(lia) ltac:(lia) CE1) as CE2.
  assert (PMa' : POSTM C A s m m2) by (eapply POSTM_trans; [exact PM1 | eapply POSTM_mono; [|exact PMa]; lia]).
  assert (PXs2 : PIXat m2 pixs (hdv w h d cm datas)).
  { apply (PIXat_frame m); [exact PXs|]. intros x Hx. rewrite (LIVK_byte C A M1 m2 md pixs 64 x CK HW1 (proj2 PMa) Lps ltac:(lia) TOPps Hx). apply OUT1. lia. }
  assert (E2 : getr r2 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
  assert (E9 : getr r2 9 = Z_to_bv 64 pixs) by (csr; reflexivity).
  assert (E4 : getr r2 4 = Z_to_bv 64 0x45480) by (csr; reflexivity).
  destruct OUTa as [[Hres0 LIVEQ] | (pixd & data & Hres & _ & PN)].
  - (* [comment removed for export] *)
    destruct CE2 as (C1 & C2 & C3 & C4).
    destruct (ptn_F al_rom r2 m2 s ret _ _ _ ltac:(lia) ltac:(lia) (W_sev_got C A1 m2 _ HWa) (W_sev C A1 m2 _ HWa) C1 C2 C3 C4 E2 Hres0)
      as (r3 & RUN3 & V2 & V1 & V10 & V11 & V12 & V8 & V9 & V18 & AG3).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWa)) | exact (mp_lazy _ (w_pure _ _ _ _ HWa)) | exact RUN3 |].
    apply (returnErrorPtr_W C A1 m2 _ r3 s 0x1054a 0x11228 13 23 ret (Z_to_bv 64 0) S CK HWa V2 Hs16 ltac:(unfold LSF; lia) Hhi V1 Hret
             V10 V11 V12 str_msg_pixd V10LeptPixCopy.str_pixCreateTemplateNoInit).
    intros m4 r5 HW4 OUT4 GR4 CS4 A10. unfold LSF in OUT4.
    apply (HK A1 m4 vm1 r5).
    + exact HW4.
    + apply cs_kept_intro; csr; try reflexivity. all: rewrite ?V8, ?V9, ?V18, ?Q8; reflexivity.
    + eapply POSTM_trans; [exact PMa'|]. apply (POSTM_sub C A A1); [apply sub_live_eq; exact LIVEQ|].
      eapply (POSTM_range C A1 m2 _ m4); [exact CK | exact HWa | exact OUT4 | lia | lia | lia].
    + left. split; [exact A10 | exact LIVEQ].
    + room_tac.
  - (* [comment removed for export] *)
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
    assert (CE3 : V10LeptPixCopy.cells4 M3 s ret (getr regs 8) (getr regs 9) (getr regs 18)) by (eapply (V10LeptPixCopy.cells4_out m2 _ (pixd + 12) (pixd + 32)); [exact OUT3 | lia | lia | lia | exact CE2]).
    assert (X4 : getr r3 4 = Z_to_bv 64 0x45480) by (rewrite (AG3 4) by (cbv; intuition discriminate); exact E4).
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
    apply (pixCopyColormap_T C A A1 M3 _ r3 (s - 32) pixd pixs (hdv w h d 0 data) (hdv w h d cm datas) cv (Z_to_bv 64 0x16428) S CK HW3 SUBa X2
             ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold LSF; lia) ltac:(lia) X1 ltac:(red; apply bv_eq; reflexivity) X4 X10 X11
             PXd3 PXs3 eq_refl eq_refl ltac:(pose proof (box_e _ APsp); lia) L1p L0p L00p Lps1 HCM3
             (kR - RK_pix) (bR - RB10_pix (4 * (wpl_of w d * h))) ltac:(room_tac) ltac:(room_consts; lia) ltac:(room_consts; lia)).
    intros A2 m4 vm2 r4 HWb CSb PMb OUTb Hrm2. rewrite with_vmmaps_twice in HWb |- *.
    replace (Z_to_bv 64 0x16428) with (0x16428 : word) by (apply bv_eq; reflexivity).
    pose proof (V10LeptPixCopy.cells4_frm C (s - 32) M3 m4 s _ _ _ _ CK (proj1 PMb) ltac:(lia) ltac:(lia) ltac:(lia) CE3) as CE4.
    assert (PMb' : POSTM C A s m m4) by (eapply POSTM_trans; [exact PM3 | eapply POSTM_mono; [|exact PMb]; lia]).
    assert (PXs4 : PIXat m4 pixs (hdv w h d cm datas)).
    { apply (PIXat_frame M3); [exact PXs3|]. intros x Hx. exact (LIVK_at A M3 m4 pixs 64 x (proj2 PMb) Lps ltac:(lia) ltac:(lia) Hx). }
    assert (Y2 : getr r4 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
    assert (Y8 : getr r4 8 = Z_to_bv 64 pixd) by (csr; reflexivity).
    assert (Y9 : getr r4 9 = Z_to_bv 64 pixs) by (csr; reflexivity).
    assert (RR : forall x, In x V10LeptPixCopy.tn_rest -> getr r4 x = getr regs x) by (unfold V10LeptPixCopy.tn_rest; rest_solve).
    destruct OUTb as [[LIVEQ PXd4] | (cd & ad & CC & PXd4)].
    + apply (ptn_tail_T C A A2 m md m4 vm2 regs r4 s pixs pixd w h d cm datas 0 data cv ret S kR bR CK HK ltac:(room_tac) Hs16 ltac:(unfold LSF; lia) Hhi Hret HWb PMb'
               (sub_live_trans _ _ _ SUBa (sub_live_eq _ _ LIVEQ)) CE4 Y2 Y8 Y9 RR H2 PXs4 Lps HOK Hw Hh Gp TOPp ALp Gd TOPd ALd NEpd L0p L0d L00p L00d
               ltac:(rewrite LIVEQ; exact L1p) ltac:(rewrite LIVEQ; exact L1d) PXd4).
      left. split; [reflexivity|]. intros q N1 N2. rewrite LIVEQ. apply LEQ; assumption.
    + pose proof CC as (CMOKc & Gcd & TOPcd & ALcd & Gad & TOPad & ALad & NEcdad & LA1cd & LA1ad & L00cd & L00ad & L2cd & L2ad & LEQ2 & CM4).
      assert (NEcdp : Z_to_bv 64 cd <> Z_to_bv 64 pixd) by (intros E; rewrite E in LA1cd; rewrite L1p in LA1cd; discriminate).
      assert (NEadp : Z_to_bv 64 ad <> Z_to_bv 64 pixd) by (intros E; rewrite E in LA1ad; rewrite L1p in LA1ad; discriminate).
      assert (NEcdd : Z_to_bv 64 cd <> Z_to_bv 64 data) by (intros E; rewrite E in LA1cd; rewrite L1d in LA1cd; discriminate).
      assert (NEadd : Z_to_bv 64 ad <> Z_to_bv 64 data) by (intros E; rewrite E in LA1ad; rewrite L1d in LA1ad; discriminate).
      assert (SUBb : sub_live A1 A2) by (eapply sub_live_new2; [exact LA1cd | exact LA1ad | exact L2cd | exact L2ad | exact LEQ2]).
      apply (ptn_tail_T C A A2 m md m4 vm2 regs r4 s pixs pixd w h d cm datas cd data cv ret S kR bR CK HK ltac:(room_tac) Hs16 ltac:(unfold LSF; lia) Hhi Hret HWb PMb'
               (sub_live_trans _ _ _ SUBa SUBb) CE4 Y2 Y8 Y9 RR H2 PXs4 Lps HOK Hw Hh Gp TOPp ALp Gd TOPd ALd NEpd L0p L0d L00p L00d
               (SUBb _ _ L1p) (SUBb _ _ L1d) PXd4).
      right. exists ad.
      split; [exact CMOKc|]. split; [exact Gcd|]. split; [exact TOPcd|]. split; [exact Gad|]. split; [exact TOPad|]. split; [exact NEcdad|].
      split; [intros E; apply NEcdp; rewrite E; reflexivity|]. split; [intros E; apply NEcdd; rewrite E; reflexivity|].
      split; [intros E; apply NEadp; rewrite E; reflexivity|]. split; [intros E; apply NEadd; rewrite E; reflexivity|].
      split; [rewrite <- (LEQ _ NEcdp NEcdd); exact LA1cd|]. split; [rewrite <- (LEQ _ NEadp NEadd); exact LA1ad|].
      split; [exact L00cd|]. split; [exact L00ad|]. split; [exact L2cd|]. split; [exact L2ad|]. split; [exact CM4|].
      intros q N1 N2 N3 N4. rewrite (LEQ2 q N3 N4). apply LEQ; assumption.
Qed.

End PixCopyT.
