(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.bilateral_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic PFLib LeptDefs LeptStructs LeptArith LeptArith2 LeptRop LeptRop2Arith.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2LeptStderr V2LeptBase V2LeptRop_iface V2LeptRop V2LeptRop2_iface V2LeptRopLowA V2LeptRop2W.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Rop2W.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V2Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
Ltac grows_chain := repeat (eapply mem_grows_trans; [| apply wbytes_grows]); apply mem_grows_refl.

Theorem rasteropLow2_W : rasteropLow2_contract.
Proof.
  unfold rasteropLow2_contract, rasteropLow_arm_contract, rop2_arm.
  intros C Ar A m md regs s datad dpixw dpixh d dwpl dx dy dw dh datas spixw spixh swpl sx sy ret S
    CK HW SUB H2 Hs16 Hlo Hhi H1 Hret H10 H11 H12 H13 H14 H15 H16 H17 Rdh Rop Rdatas Rspw Rsph Rswpl Rsx Rsy
    Hdd Hds SHd SHs RCd RCs ARM Ld Ld0 Ld00 Ls HK.
  destruct ARM as [ARM | ARM].
  - exact (rasteropLow_al_W C Ar A m md regs s datad dpixw dpixh d dwpl dx dy dw dh datas spixw spixh swpl sx sy ret S
      CK HW SUB H2 Hs16 Hlo Hhi H1 Hret H10 H11 H12 H13 H14 H15 H16 H17 Rdh Rop Rdatas Rspw Rsph Rswpl Rsx Rsy
      Hdd Hds SHd SHs RCd RCs ARM Ld Ld0 Ld00 Ls HK).
  - exact (rasteropLow_gen_W C Ar A m md regs s datad dpixw dpixh d dwpl dx dy dw dh datas spixw spixh swpl sx sy ret S
      CK HW SUB H2 Hs16 Hlo Hhi H1 Hret H10 H11 H12 H13 H14 H15 H16 H17 Rdh Rop Rdatas Rspw Rsph Rswpl Rsx Rsy
      Hdd Hds SHd SHs RCd RCs ARM Ld Ld0 Ld00 Ls HK).
Qed.

Theorem pixRasterop_src2_W : pixRasterop_src2_contract.
Proof.
  unfold pixRasterop_src2_contract.
  intros C Ar A m md regs s pixd dx dy dw dh pixs sx sy vd vs ret S CK HW SUB H2 Hs16 Hlo Hhi H1 Hret H10 H11 H12 H13 H14 H15 H16 H17 Rsy
    PXd PXs Edd SHd SHs RCd RCs ARM Lpd Lps NEpd NEps Ld Ld0 Ld00 Ls HK.
  unfold PC_pixRasterop. replace (Z_to_bv 64 0x273f0) with (0x273f0 : word) by (apply bv_eq; reflexivity).
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold ROP_STACK in Hlo.
  pose proof (alloc_top_lt (c_vm C)) as AT. unfold two_pow_64 in AT.
  destruct (pix_facts C A m md pixd vd CK HW PXd SHd Lpd) as (Gpd & TOPpd & Hdatad & Hwpld).
  destruct (pix_facts C A m md pixs vs CK HW PXs SHs Lps) as (Gps & TOPps & Hdatas & Hwpls).
  assert (ALd8 : (pixd mod 8 = 0)%Z) by (pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lpd) as (_ & X16 & _); rewrite u_Z2bv in X16 by lia; apply mod16_mod8; exact X16).
  assert (ALs8 : (pixs mod 8 = 0)%Z) by (pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lps) as (_ & X16 & _); rewrite u_Z2bv in X16 by lia; apply mod16_mod8; exact X16).
  pose proof SHd as (Hdd & Hwd & Hhd & _ & Hszd). pose proof SHs as (_ & Hws & Hhs & _ & _).
  destruct RCd as (Hdx0 & Hdy0 & Hdw1 & Hdh1 & Hdxw & Hdyh). pose proof RCs as (Hsx0 & Hsy0 & _ & _ & Hsxw & Hsyh).
  set (nd := (4 * (p_wpl vd * p_h vd))%Z) in *.
  assert (Hnd : (0 < nd)%Z) by (subst nd; clear - Hwpld Hhd; nia).
  destruct (pr_A al_rom regs m s pixd 12 vd ret (Z_to_bv 64 sy) ltac:(lia) Hs16 ALd8 ltac:(lia) ltac:(lia) ltac:(lia) PXd ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
              (W_sok_win C A m md (s - 224) 224 CK HW ltac:(lia) ltac:(cbn; lia)) Rsy H2 H1 H10 H15)
    as (r1 & RUN1 & Q2 & Q19 & Q20 & Q21 & Q25 & Q22 & Q27 & Q18 & Q9 & Q8 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  set (M1 := PRM m s ret regs (p_w vd) (p_h vd) (p_d vd)).
  assert (WP1 : W C A M1 md /\ POSTM C Ar s m M1)
    by (apply (WP_range C Ar A m m M1 md s (s - 224) CK HW (POSTM_refl _ _ _ _) SUB); [lia | lia | intros a Ha; subst M1; apply PRM_outside; lia | subst M1; unfold PRM, RLF; grows_chain]).
  destruct WP1 as [HW1 PM1].
  assert (OUT1 : forall a : word, ~ (s - 224 <= u a < s)%Z -> M1 a = m a) by (intros a Ha; subst M1; apply PRM_outside; lia).
  assert (PXd1 : PIXat M1 pixd vd) by (apply (PIXat_frame m); [exact PXd | intros x Hx; apply OUT1; lia]).
  assert (PXs1 : PIXat M1 pixs vs) by (apply (PIXat_frame m); [exact PXs | intros x Hx; apply OUT1; lia]).
  assert (Rw1 : rdn SEGS M1 (Z_to_bv 64 (s - 108)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 (p_w vd))))
    by (subst M1; unfold PRM; repeat rdn_peel1; apply (rdn_wbytes_hit SEGS (word_to_le_bytes 4 (Z_to_bv 64 (p_w vd)))); zlen; unorm; lia).
  assert (Rh1 : rdn SEGS M1 (Z_to_bv 64 (s - 112)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 (p_h vd))))
    by (subst M1; unfold PRM; repeat rdn_peel1; apply (rdn_wbytes_hit SEGS (word_to_le_bytes 4 (Z_to_bv 64 (p_h vd)))); zlen; unorm; lia).
  assert (Rd1 : rdn SEGS M1 (Z_to_bv 64 (s - 116)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 (p_d vd))))
    by (subst M1; unfold PRM; repeat rdn_peel1; apply (rdn_wbytes_hit SEGS (word_to_le_bytes 4 (Z_to_bv 64 (p_d vd)))); zlen; unorm; lia).
  pose proof (rlcells_RLF m s ret regs ltac:(lia) ltac:(lia)) as CE0.
  assert (CE1 : rlcells M1 s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27)).
  { apply (rlcells_frame (RLF m s ret regs) M1 s); [lia | lia | exact CE0 |]. intros x Hx. subst M1. apply PRM_above; lia. }
  destruct (pr_Bs al_rom r1 M1 s pixd pixs dx dy dw dh sx sy vd vs ltac:(lia) Hs16 ALd8 ALs8 ltac:(lia) ltac:(lia) ltac:(lia) PXd1 ltac:(lia) ltac:(lia) PXs1 Edd
              ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hdatad ltac:(lia) ltac:(lia) ltac:(lia) Hdatas
              (W_sok_win C A M1 md (s - 224) 108 CK HW1 ltac:(lia) ltac:(cbn; lia)) Rw1 Rh1 Rd1
              Q2 Q19 Q20 ltac:(rewrite Q25; exact H16) ltac:(rewrite Q27; exact H14) ltac:(rewrite Q18; exact H11) ltac:(rewrite Q9; exact H12)
              ltac:(rewrite Q8; exact H13) ltac:(rewrite Q22; exact H17) Q21)
    as (r2 & RUN2 & P2 & P1 & P10 & P11 & P12 & P13 & P14 & P15 & P16' & P17 & AG2).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN2 |].
  set (M2 := PSM M1 s vd vs dh sx sy).
  assert (WP2 : W C A M2 md /\ POSTM C Ar s m M2)
    by (apply (WP_range C Ar A m M1 M2 md s (s - 224) CK HW1 PM1 SUB); [lia | lia | intros a Ha; subst M2; apply PSM_outside; lia | subst M2; unfold PSM; clearbody M1; grows_chain]).
  destruct WP2 as [HW2 PM2].
  assert (OUT2 : forall a : word, ~ (s - 224 <= u a < s)%Z -> M2 a = m a) by (intros a Ha; subst M2; rewrite PSM_outside by lia; apply OUT1; exact Ha).
  assert (CE2 : rlcells M2 s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27)).
  { apply (rlcells_frame M1 M2 s); [lia | lia | exact CE1 |]. intros x Hx. subst M2. apply PSM_above; lia. }
  replace (0x27f50 : word) with (Z_to_bv 64 PC_rasteropLow) by (apply bv_eq; reflexivity).
  apply (rasteropLow2_W C Ar A M2 md r2 (s - 224)%Z (p_data vd) (p_w vd) (p_h vd) (p_d vd) (p_wpl vd) dx dy dw dh (p_data vs) (p_w vs) (p_h vs) (p_wpl vs) sx sy
           (Z_to_bv 64 0x275f0) S CK HW2 SUB P2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ROPLOW_STACK; lia) ltac:(lia) P1
           ltac:(red; apply bv_eq; reflexivity) P10 P11 P12 P13 P14 P15 P16' P17).
  1-8: repeat match goal with |- context [Z_to_bv 64 (?b - 224 + ?k)%Z] => let c := eval cbv in (224 - k)%Z in replace (b - 224 + k)%Z with (b - c)%Z by lia end;
       subst M2; unfold PSM; rdn_chain.
  - exact Hdatad. - exact Hdatas. - exact SHd. - rewrite <- Edd. exact SHs.
  - repeat split; lia. - exact RCs. - exact ARM.
  - exact Ld. - exact Ld0. - exact Ld00. - exact Ls.
  - intros m3 r3 HW3 CS3 PM3 FT3.
    replace (Z_to_bv 64 0x275f0) with (0x275f0 : word) by (apply bv_eq; reflexivity).
    destruct (pr_J al_rom r3 m3) as (r4 & RUN4 & AG4).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW3)) | exact (mp_lazy _ (w_pure _ _ _ _ HW3)) | exact RUN4 |].
    destruct (blk_range C A m md (Z_to_bv 64 (p_data vd)) nd CK HW Ld Hnd) as [Gd TOPd]. rewrite u_Z2bv in Gd, TOPd by lia.
    assert (CE3 : rlcells m3 s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27)).
    { apply (rlcells_frame M2 m3 s); [lia | lia | exact CE2 |]. intros x Hx. apply FT3; [unfold scratch; lia | lia]. }
    destruct (pr_C al_rom r4 m3 s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) ltac:(lia) ltac:(lia) Hret CE3 ltac:(csr; reflexivity))
      as (r5 & RUN5 & Z2 & Z1 & Z10 & Y0 & Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10 & Y11 & AG5).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW3)) | exact (mp_lazy _ (w_pure _ _ _ _ HW3)) | exact RUN5 |].
    apply (HK m3 r5 HW3).
    + apply cs_kept_intro; first [ rewrite Z2; symmetry; exact H2 | assumption | csr; reflexivity ].
    + eapply POSTM_trans; [exact PM2 | eapply POSTM_mono; [| exact PM3]; lia].
    + apply (PIXat_frame m); [exact PXd|].
      apply (hdr_kept C A m md (s - 224) pixd (p_data vd) nd M2 m3 CK HW Lpd Ld NEpd ltac:(lia) Hdatad Hnd ltac:(lia) FT3).
      intros a NW. apply OUT2. intros X. apply NW. unfold win. lia.
    + apply (PIXat_frame m); [exact PXs|].
      apply (hdr_kept C A m md (s - 224) pixs (p_data vd) nd M2 m3 CK HW Lps Ld NEps ltac:(lia) Hdatad Hnd ltac:(lia) FT3).
      intros a NW. apply OUT2. intros X. apply NW. unfold win. lia.
    + exact Z10.
Qed.

End Rop2W.
