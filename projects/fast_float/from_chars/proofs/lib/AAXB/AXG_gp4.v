(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AxAsan AXG_put AXG_put2 AXG_np AXG_np2 AXG_np3 AXG_np4 AXG_nf1.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_gp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_gp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_gp3.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_gp3.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AxAsan OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_put OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_put2 OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_np OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_np2 OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_np3 OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_np4 OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_nf1 OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp.AXG_npb OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp3.AXG_gp2 OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp3.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_gp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_gp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_gp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_gp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_gp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_gp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_gp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_gp.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Abbreviation SEGS := AsanUbsan.M.loaded_segments.
Lemma ri_comm : forall c SB, 128 * c + (SB + 137438953472) = SB + 137438953472 + 128 * c.
Proof. intros. ring. Qed.

Section GR.
Context {fx : FPState}.
Variable rom : word -> option byte.
Variables (m : word -> option byte) (regs : bvmap 5 word) (CA ND c SB sz nc newc j SP : Z).
Hypothesis Hc : c = cls_of ND.
Hypothesis I : INV_G m CA SB c sz nc newc j.
Hypothesis Hj : j + 1 + nc <= newc.
Hypothesis HND : 1 <= ND <= 65536.
Hypothesis H2 : getr regs 2 = wa SP.
Hypothesis HSP : 2^46 + 4096 <= SP <= 2^47 /\ SP mod 16 = 0.
Hypothesis HSTK : stk_ok SEGS m (wa SP) 2048.
Hypothesis H10 : getr regs 10 = wa 929816.
Hypothesis H11 : getr regs 11 = wa CA.
Hypothesis H12 : getr regs 12 = wa ND.
Hypothesis H13 : getr regs 13 = wa 8.
Hypothesis HCA : ((4304 <= CA /\ CA + 3888 <= 65536) \/ 6537424 <= CA) /\ CA mod 16 = 0 /\ CA + 2592 <= SP - 2048.
Hypothesis HSB : 4194304 <= SB /\ SB mod 4096 = 0 /\ SB + 137438953472 + 4096 <= SP - 2048.
Hypothesis HSEP : CA + 2592 <= SB \/ SB + 137438953472 + 4096 <= CA.
Hypothesis HIMG : forall i, 65536 <= i < 143360 -> m (Z_to_bv 64 i) = None.

#[using="CA SB SP"] Lemma gsrlw1 : forall R V mc, nth 2 V 0 = mc -> 0 <= mc < 2^31 ->
  bv_unsigned (edenot (Ez R V) (EAluw ALU_SRL (EExt true 0 4 (EVar 34)) (ELit 1))) = mc / 2.
Proof. LiaFast.lf_pins (fun (CA SB SP : LiaFast.U) => LiaFast.u0).
  intros R V mc Hv Hm. cbn [edenot]. rewrite w_srlw. unfold v_srlw, ext_val.
  rewrite (zatom R V 34 mc eq_refl Hv) by lia. rewrite ext_Z_lo32_small by lia.
  change (bv_unsigned (Z_to_bv 64 1)) with 1. change (bv_unsigned (Z_to_bv 64 mc)) with (bv_unsigned (wa mc)). rewrite (u_wa_small mc) by lia.
  unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 32) with (2^32). rewrite (Z.mod_small mc) by lia.
  change (1 mod 32) with 1. rewrite Z.shiftr_div_pow2 by lia. change (2^1) with 2.
  change (32%N) with (8 * N.of_nat 4)%N. rewrite swrap32_small by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
  change (bv_unsigned (Z_to_bv 64 (mc / 2))) with (bv_unsigned (wa (mc / 2))).
  apply u_wa_small. split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia.
Qed.

#[using="ND Hc I Hj HND H2 HSP HSTK H10 H11 H12 H13 HCA HSB HSEP HIMG"] Lemma gp_refill : cnt_of nc j = 0 ->
  exists R m', msteps SEGS (mkst regs (wa 0x44004) m rom) (mkst R (wa 0x44224) m' rom) /\
    getr R (Z_to_bv 5 (Z.of_nat 2)) = wa SP /\
    (forall k, In k KCALLEE -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))) /\
    getr R 10 = wa (SB + c * 4294967296 + j * sz) /\
    INV_G m' CA SB c sz nc newc (j + 1) /\
    (forall x, 0 <= x < 2^64 -> ~ (SP - 2048 <= x < SP) -> ~ owned_C CA SB c x -> m' (wa x) = m (wa x)) /\ mem_grows m m'.
Proof. LiaFast.lf_pins (fun (ND Hc I Hj HND H2 HSP HSTK H10 H11 H12 H13 HCA HSB HSEP HIMG : LiaFast.U) => LiaFast.u0).
  intros Hcnt0.
  pose proof I as I0. destruct I0 as [Igeo ISB IRIB Icnt Imc Isz Ich Imu Inf Ina Ifa Ist Iwrec Iwri Iwst].
  destruct (refill_step nc j ltac:(slia) ltac:(slia) Hcnt0) as (Ej & Eb & Ec).
  pose proof (b_of_pos nc j ltac:(slia) ltac:(slia)) as Hb.
  rewrite Hcnt0 in Icnt. clear Ich.
  set (b := b_of nc j) in *. set (nf := newc - nc * b) in *.
  destruct Ist as (st & Hst & Rst). destruct Ina as (na & Hna & Rna).
  assert (Hcr5 : 1 <= c <= 30) by (destruct Igeo as (Hc1 & _); exact Hc1).
  assert (Hsz16 : sz = 16 * (sz / 16)) by (pose proof (Z.div_mod sz 16 ltac:(lia)); slia).
  assert (Hszr : 16 <= sz <= 262144) by (clear - Igeo; destruct Igeo as (_ & H1 & _ & H0 & H1' & H2' & H3 & _); nia).
  assert (Hjs : j * sz <= 262144) by (clear - Igeo Hj; destruct Igeo as (_ & H1 & _ & H0 & H1' & H2' & H3 & _); nia).
  assert (HZ : ((4304 <= CA /\ CA + 3888 <= 65536) \/ 6537424 <= CA) /\ CA mod 16 = 0 /\ CA + 2592 <= SP - 2048 /\ 4194304 <= SB /\ SB mod 4096 = 0 /\
               SB + 137438953472 + 4096 <= SP - 2048 /\ 2^46 + 4096 <= SP <= 2^47 /\ 1 <= c <= 30 /\ 1 <= ND <= 65536 /\
               1 <= nc <= 8 /\ 16 <= sz <= 262144 /\ nc <= nf <= newc /\ newc <= 16384 /\ 0 <= st < 2^64 /\ 0 <= na < 2^64 /\
               (CA + 2592 <= SB \/ SB + 137438953472 + 4096 <= CA) /\ j = nc * b /\ 1 <= j /\ j * sz <= 262144) by (unfold nf; slia).
  clear Igeo Hszr Hjs Hcr5 HCA HSB HSEP HND Hst Hna HSP.
  assert (HSPa : bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) = SP) by (rgz; rewrite H2, u_wa_small by (zlh HZ); reflexivity).
  (* [comment removed for export] *)
  destruct (gp_head rom m regs CA ND SP H2 ltac:(zlh HZ) HSTK H10 H11 H12 H13 ltac:(zlh HZ) ltac:(zlh HZ))
    as (R0 & Hms0 & A2 & A8 & _ & A10 & A11 & A13 & KK0).
  rewrite <- Hc in A8.
  set (m1 := m1c m SP (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 1)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 8)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 9)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 19)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 20))))).
  change (wchainS m SP (LHD (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 1)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 8)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 9)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 19)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 20)))))) with m1 in Hms0.
  assert (G1 : mem_grows m m1) by apply m1c_grows.
  assert (F1 : forall x, 0 <= x < 2^64 -> ~ (SP - 48 <= x < SP) -> m1 (wa x) = m (wa x)) by (intros x Hx H; apply m1c_frame; [(zlh HZ) | exact Hx | exact H]).
  assert (HSP0 : bv_unsigned (getr R0 (Z_to_bv 5 (Z.of_nat 2))) = SP - 48) by (rgz; rewrite A2, u_wa_small by (zlh HZ); reflexivity).
  assert (P0 : OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp.AXF_gnp0rtz.gnp0rt_pre R0 m1 CA c 0).
  { constructor; [exact A8 | exact A10 | exact A11 | exact A13 | (zlh HZ) | (zlh HZ) | (clear; lia) | (zlh HZ) | rewrite HSP0; (zlh HZ) | ].
    rewrite Z.add_0_r. apply (rd_frame m m1); [(zlh HZ) | lenq; (zlh HZ) | intros x Hx; znq; apply F1; clear - HZ Hx; lia | exact Icnt]. }
  destruct (OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp.AXF_gnp0rtz.gnp0rt_pnp0rt R0 m1 rom CA c 0 P0 (sc_gnp0rt R0 m1 (SP - 48) HSP0 CA c ltac:(zlh HZ)))
    as (R1 & Hms1' & B8 & B9 & B10 & B11 & B12 & B13 & B18 & B19 & B20 & KK1').
  clear P0. unfold OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp.AXF_gnp0rtz.gnp0rt_mem_pnp0rt in Hms1'.
  pose proof (msteps_trans SEGS _ _ _ Hms0 Hms1') as Hms1. clear Hms0 Hms1'.
  assert (B2 : getr R1 (Z_to_bv 5 (Z.of_nat 2)) = wa (SP - 48)) by (rewrite (KK1' 2%nat ltac:(cbn; memb')); rgz; exact A2).
  assert (KK1 : forall k, In k [1; 3; 4; 7; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R1 (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
  { intros k Hk. rewrite (KK1' k ltac:(clear - Hk; cbn [In] in *; intuition)). apply KK0. clear - Hk. cbn [KHD In] in *. intuition. }
  regzH B8. regzH B9. regzH B18. regzH B19. regzH B20.
  assert (HSP1 : bv_unsigned (getr R1 (Z_to_bv 5 (Z.of_nat 2))) = SP - 48) by (rewrite B2, u_wa_small by (zlh HZ); reflexivity).
  (* [comment removed for export] *)
  assert (P1 : OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp.AXF_gnprz.gnpr_pre R1 m1 CA c (2 * nc)).
  { constructor; [exact B10 | exact B11 | exact B12 | exact B13 | | (zlh HZ) | (zlh HZ) | (zlh HZ) | (zlh HZ) | rewrite HSP1; (zlh HZ) | ].
    - replace (getr R1 2) with (wa (SP - 48)) by (rgz; rewrite B2; reflexivity).
      apply (stk_ok_move m1 SP (SP - 48) 1024); [(zlh HZ) | (zlh HZ) | exact (stk_ok_grows m m1 (wa SP) 2048 G1 HSTK) | (zlh HZ) | (zlh HZ) | (zlh HZ)].
    - apply (rd_frame m m1); [(zlh HZ) | lenq; (zlh HZ) | intros x Hx; znq; apply F1; clear - HZ Hx; lia | exact Imc]. }
  destruct (OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp.AXF_gnprz.gnpr_pnpr R1 m1 rom CA c (2 * nc) P1 (sc_gnpr R1 m1 (SP - 48) HSP1 CA c (2 * nc) ltac:((zlh HZ))))
    as (R2 & Hms2 & C1 & C2 & C8 & C9 & C10 & C11 & C12 & C13 & C14 & KK2).
  clear P1 C1.
  pose proof (msteps_trans SEGS _ _ _ Hms1 Hms2) as Hms12. clear Hms1 Hms2.
  regzH C2. regzH C8. regzH C9.
  assert (Vn : bv_unsigned (edenot (Ez R1 (OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp.AXF_gnprz.VALS_gnpr CA c (2 * nc))) (EAluw ALU_SRL (EExt true 0 4 (EVar 34)) (ELit 1))) = nc).
  { rewrite (gsrlw1 R1 (OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp.AXF_gnprz.VALS_gnpr CA c (2 * nc)) (2 * nc) eq_refl ltac:((zlh HZ))). replace (2 * nc) with (nc * 2) by ring. apply Z.div_mul. lia. }
  rewrite Vn in C9, C14.
  assert (V18 : bv_unsigned (getr R1 (Z_to_bv 5 (Z.of_nat 8))) = c) by (rewrite B8, u_wa_small by (zlh HZ); reflexivity).
  assert (V19 : bv_unsigned (getr R1 (Z_to_bv 5 (Z.of_nat 9))) = CA + 80 * c) by (rewrite B9, u_wa_small by (zlh HZ); reflexivity).
  set (m2 := m2c m1 SP c (CA + 80 * c)).
  assert (EM2 : OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp.AXF_gnprz.gnpr_mem_pnpr m1 R1 CA c (2 * nc) = m2) by (unfold m2, m2c, OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp.AXF_gnprz.gnpr_mem_pnpr; rewrite HSP1, V18, V19; nsub; reflexivity).
  rewrite EM2 in Hms12. clear EM2.
  assert (HSP2 : bv_unsigned (getr R2 (Z_to_bv 5 (Z.of_nat 2))) = SP - 80) by (rewrite C2, HSP1, u_wa_small by (zlh HZ); ring).
  assert (G2 : mem_grows m m2) by (exact (mem_grows_trans _ _ _ G1 (m2c_grows m1 SP c (CA + 80 * c)))).
  assert (F12 : forall x, 0 <= x < 2^64 -> ~ (SP - 72 <= x < SP) -> m2 (wa x) = m (wa x)).
  { intros x Hx H. unfold m2. rewrite m2c_frame by (clear - HZ Hx H; lia). apply F1; clear - HZ Hx H; lia. }
  (* [comment removed for export] *)
  assert (P2 : OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp.AXF_gng0z.gng0_pre R2 m2 CA c nc SB (SB + 137438953472) nf).
  { constructor; [exact C10 | exact C11 | exact C12 | exact C13 | exact C14 | | (zlh HZ) | (zlh HZ) | (zlh HZ) | (zlh HZ) | (zlh HZ) | (zlh HZ) | (zlh HZ) | rewrite HSP2; (zlh HZ) | (zlh HZ) | | | | | | ].
    - rewrite ?(ri_comm c SB). replace (getr R2 2) with (wa (SP - 80)) by (rgz; rewrite C2, HSP1; f_equal; ring).
      apply (stk_ok_move m2 SP (SP - 80) 1024); [(zlh HZ) | (zlh HZ) | exact (stk_ok_grows m m2 (wa SP) 2048 G2 HSTK) | (zlh HZ) | (zlh HZ) | (zlh HZ)].
    - rewrite ?(ri_comm c SB). apply (rd_frame m m2); [(zlh HZ) | lenq; (zlh HZ) | intros x Hx; znq; apply F12; clear - HZ Hx; lia | exact ISB].
    - rewrite ?(ri_comm c SB). apply (rd_frame m m2); [(zlh HZ) | lenq; (zlh HZ) | intros x Hx; znq; apply F12; clear - HZ Hx; lia | exact IRIB].
    - rewrite ?(ri_comm c SB). rewrite Z.add_0_r. apply (rd_frame m m2); [(zlh HZ) | lenq; (zlh HZ) | intros x Hx; znq; apply F12; clear - HZ Hx; lia | exact Imu].
    - rewrite ?(ri_comm c SB). intros d k Hd Hk. rewrite Z.add_0_r. apply (store_ok_mono SEGS k m m2 _ G2). apply Iwri; (clear - HZ Hd Hk; lia).
    - rewrite ?(ri_comm c SB). apply (rd_frame m m2); [(zlh HZ) | lenq; (zlh HZ) | intros x Hx; znq; apply F12; clear - HZ Hx; lia | exact Inf].
    - rewrite ?(ri_comm c SB). intros d k Hd Hk. apply (store_ok_mono SEGS k m m2 _ G2). replace (SB + 137438953472 + 128 * c + 16 + d) with (SB + 137438953472 + 128 * c + (16 + d)) by ring. apply Iwri; (clear - HZ Hd Hk; lia). }
  destruct (OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp.AXF_gng0z.gng0_png0 R2 m2 rom CA c nc SB (SB + 137438953472) nf P2
              (sc_gng0 R2 m2 (SP - 80) HSP2 CA c nc SB (SB + 137438953472) nf ltac:((zlh HZ))))
    as (R3 & Hms3 & D1 & D2 & D5 & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13 & D14 & D15 & D16 & D17 & D19 & D20 & D21 & D22 & D23 & D24 & D25 & KK3).
  clear P2 D1 D5 D6 D7 D9 D10 D12 D15 D16 D17 D21 D22 D23 D24 D25.
  pose proof (msteps_trans SEGS _ _ _ Hms12 Hms3) as Hms13. clear Hms12 Hms3.
  assert (V28 : bv_unsigned (getr R2 (Z_to_bv 5 (Z.of_nat 8))) = CA + 80 * c) by (rewrite C8, u_wa_small by (zlh HZ); reflexivity).
  assert (V29 : bv_unsigned (getr R2 (Z_to_bv 5 (Z.of_nat 9))) = nc) by (rewrite C9, u_wa_small by (zlh HZ); reflexivity).
  assert (V218 : bv_unsigned (getr R2 (Z_to_bv 5 (Z.of_nat 18))) = 8) by (rewrite (KK2 18%nat ltac:(cbn; memb')), B18, u_wa_small by (zlh HZ); reflexivity).
  assert (V219 : bv_unsigned (getr R2 (Z_to_bv 5 (Z.of_nat 19))) = CA) by (rewrite (KK2 19%nat ltac:(cbn; memb')), B19, u_wa_small by (zlh HZ); reflexivity).
  assert (V220 : bv_unsigned (getr R2 (Z_to_bv 5 (Z.of_nat 20))) = 929816) by (rewrite (KK2 20%nat ltac:(cbn; memb')), B20, u_wa_small by (zlh HZ); reflexivity).
  assert (W21 : getr R2 (Z_to_bv 5 (Z.of_nat 21)) = getr regs (Z_to_bv 5 (Z.of_nat 21))) by (rewrite (KK2 21%nat ltac:(cbn; memb')), (KK1 21%nat ltac:(cbn; memb')); reflexivity).
  assert (W22 : getr R2 (Z_to_bv 5 (Z.of_nat 22)) = getr regs (Z_to_bv 5 (Z.of_nat 22))) by (rewrite (KK2 22%nat ltac:(cbn; memb')), (KK1 22%nat ltac:(cbn; memb')); reflexivity).
  assert (W23 : getr R2 (Z_to_bv 5 (Z.of_nat 23)) = getr regs (Z_to_bv 5 (Z.of_nat 23))) by (rewrite (KK2 23%nat ltac:(cbn; memb')), (KK1 23%nat ltac:(cbn; memb')); reflexivity).
  assert (W24 : getr R2 (Z_to_bv 5 (Z.of_nat 24)) = getr regs (Z_to_bv 5 (Z.of_nat 24))) by (rewrite (KK2 24%nat ltac:(cbn; memb')), (KK1 24%nat ltac:(cbn; memb')); reflexivity).
  assert (W25 : getr R2 (Z_to_bv 5 (Z.of_nat 25)) = getr regs (Z_to_bv 5 (Z.of_nat 25))) by (rewrite (KK2 25%nat ltac:(cbn; memb')), (KK1 25%nat ltac:(cbn; memb')); reflexivity).
  assert (W26 : getr R2 (Z_to_bv 5 (Z.of_nat 26)) = getr regs (Z_to_bv 5 (Z.of_nat 26))) by (rewrite (KK2 26%nat ltac:(cbn; memb')), (KK1 26%nat ltac:(cbn; memb')); reflexivity).
  assert (W27 : getr R2 (Z_to_bv 5 (Z.of_nat 27)) = getr regs (Z_to_bv 5 (Z.of_nat 27))) by (rewrite (KK2 27%nat ltac:(cbn; memb')), (KK1 27%nat ltac:(cbn; memb')); reflexivity).

  set (m3 := m3c m2 SP (CA + 80 * c) nc CA (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 21)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 22)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 23)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 24)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 25)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 26)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 27)))) (SB + 137438953472 + 128 * c) nf).
  assert (EM3 : OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp.AXF_gng0z.gng0_mem_png0 m2 R2 CA c nc SB (SB + 137438953472) nf = m3).
  { unfold m3, m3c, OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp.AXF_gng0z.gng0_mem_png0. rewrite ?(ri_comm c SB). rewrite HSP2, V28, V29, V218, V219, V220, W21, W22, W23, W24, W25, W26, W27. nsub. rewrite ?Z.add_0_r. reflexivity. }
  rewrite EM3 in Hms13. clear EM3 V28 V29 V218 V219 V220 W21 W22 W23 W24 W25 W26 W27 C8 C9 C10 C11 C12 C13 C14.
  assert (G3 : mem_grows m m3) by (exact (mem_grows_trans _ _ _ G2 (m3c_grows _ _ _ _ _ _ _ _ _ _ _ _ _ _))).
  assert (F13 : forall x, 0 <= x < 2^64 -> ~ (SP - 184 <= x < SP) -> ~ (SB + 137438953472 + 128 * c <= x < SB + 137438953472 + 128 * c + 24) -> m3 (wa x) = m (wa x)).
  { intros x Hx H1 H3. unfold m3. rewrite m3c_frame by (clear - HZ Hx H1 H3; lia). apply F12; clear - HZ Hx H1 H3; lia. }
  destruct (m3c_RI m2 SP (CA + 80 * c) nc CA (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 21)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 22)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 23)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 24)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 25)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 26)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 27)))) (SB + 137438953472 + 128 * c) nf ltac:((zlh HZ)) ltac:((zlh HZ))) as [R3mu R3nf].
  fold m3 in R3mu, R3nf.
  (* [comment removed for export] *)
  regzH D2. regzH D8. regzH D14. regzH D19. rewrite ?(ri_comm c SB) in D8.
  assert (L11 : getr R3 11 = wa (CA + 80 * c + 16 + 4 * Z.of_nat (Z.to_nat nc))) by (rewrite D11, Z2Nat.id by (zlh HZ); f_equal; ring).
  assert (L13 : getr R3 13 = wa (CA + 80 * c + 16)) by (rewrite D13; reflexivity).
  assert (L20 : getr R3 20 = wa (SB + c * 4294967296 + 3758096384 + 4 * (nf - nc))) by (rewrite D20; f_equal; ring).
  clear D11 D13 D20.
  assert (LW : forall i, 0 <= i < Z.of_nat (Z.to_nat nc) -> 0 <= (newc - 1 - (nf - nc + i)) * (sz / 16) < 2^31 /\
                 rd m3 (SB + c * 4294967296 + 3758096384 + 4 * (nf - nc) + 4 * i) 4 ((newc - 1 - (nf - nc + i)) * (sz / 16))).
  { intros i Hi. rewrite Z2Nat.id in Hi by (zlh HZ). split.
    - assert (0 <= sz / 16 <= 16384) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; (zlh HZ)). clear - HZ Hi H. nia.
    - pose proof (Ifa (nf - nc + i) ltac:(clear - HZ Hi; lia)) as Rf. replace (SB + c * 4294967296 + 3758096384 + 4 * (nf - nc) + 4 * i) with (SB + c * 4294967296 + 3758096384 + 4 * (nf - nc + i)) by ring.
      apply (rd_frame m m3); [clear - HZ Hi; lia | lenq; clear - HZ Hi; lia | intros x Hx; znq; apply F13; clear - HZ Hi Hx; lia | exact Rf]. }
  assert (LWR : wr m3 (CA + 80 * c + 16) (4 * Z.of_nat (Z.to_nat nc))).
  { intros d k Hd Hk. rewrite Z2Nat.id in Hk by (clear - HZ Hd Hk; lia). apply (store_ok_mono SEGS k m m3 _ G3). replace (CA + 80 * c + 16 + d) with (CA + 80 * c + (16 + d)) by ring. apply Iwrec; clear - HZ Hd Hk; lia. }
  destruct (ngl_loop rom (Z.to_nat nc) R3 m3 (SB + c * 4294967296 + 3758096384 + 4 * (nf - nc)) (CA + 80 * c + 16)
              (fun i => (newc - 1 - (nf - nc + i)) * (sz / 16)) ltac:((zlh HZ)) L11 L13 L20
              ltac:((zlh HZ)) ltac:(rewrite Z2Nat.id by (zlh HZ); (zlh HZ)) ltac:((zlh HZ)) ltac:(rewrite Z2Nat.id by (zlh HZ); (zlh HZ)) ltac:(rewrite Z2Nat.id by (zlh HZ); (zlh HZ)) LW LWR)
    as (R4 & m4 & Hms4 & E13 & E20 & KK4 & RD4 & F4 & G4).
  rewrite Z2Nat.id in RD4, F4 by (zlh HZ). clear LW LWR L11 L13 L20 E13 E20.
  pose proof (msteps_trans SEGS _ _ _ Hms13 Hms4) as Hms14. clear Hms13 Hms4.
  assert (G14 : mem_grows m m4) by exact (mem_grows_trans _ _ _ G3 G4).
  assert (F14 : forall x, 0 <= x < 2^64 -> ~ (SP - 184 <= x < SP) -> ~ (SB + 137438953472 + 128 * c <= x < SB + 137438953472 + 128 * c + 24) ->
                  ~ (CA + 80 * c + 16 <= x < CA + 80 * c + 16 + 4 * nc) -> m4 (wa x) = m (wa x)).
  { intros x Hx H1 H3 H4. rewrite F4 by assumption. apply F13; assumption. }
  (* [comment removed for export] *)
  assert (HSP4 : bv_unsigned (getr R4 (Z_to_bv 5 (Z.of_nat 2))) = SP - 208) by (rewrite (KK4 2%nat ltac:(cbn; memb')), D2, HSP2, u_wa_small by (zlh HZ); ring).
  set (cp := (newc - nf) * (sz / 16)).
  assert (Hcp : 0 <= cp <= 16384).
  { assert (E : cp = j * (sz / 16)) by (unfold cp, nf; destruct HZ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ejb & _); rewrite Ejb; ring).
    rewrite E. assert (Hq : 1 <= sz / 16) by (apply Z.div_le_lower_bound; (zlh HZ)). clear - HZ Hsz16 Hq. set (q := sz / 16) in *.
    destruct HZ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hj1 & Hjs). rewrite Hsz16 in Hjs. nia. }
  destruct (slots_ok m SP (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 1)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 8)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 9)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 19)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 20)))) c (CA + 80 * c) nc CA (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 21)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 22)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 23)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 24)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 25)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 26)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 27)))) (SB + 137438953472 + 128 * c) nf ltac:((zlh HZ)) ltac:((zlh HZ)))
    as (S10 & S11 & S12 & S13 & S14 & S15 & S16 & S17 & S18 & S19 & S20 & S21 & S22 & S23 & S24 & S25 & S26 & S27 & S28 & S29 & S30 & S31).
  fold m1 m2 m3 in S10, S11, S12, S13, S14, S15, S16, S17, S18, S19, S20, S21, S22, S23, S24, S25, S26, S27, S28, S29, S30, S31.
  Ltac f4 F4 H := apply (rd_frame _ _); [clear - H; lia | lenq; clear - H; lia | intros x Hx; znq; apply F4; clear - H Hx; lia | ].
  assert (HZ4 : 2^46 + 4096 <= SP <= 2^47 /\ ((4304 <= CA /\ CA + 3888 <= 65536) \/ 6537424 <= CA) /\ CA + 2592 <= SP - 2048 /\ 1 <= c <= 30 /\ 1 <= nc <= 8) by (zlh HZ).
  assert (P4 : OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp.AXF_gngtz.gngt_pre R4 m4 CA c nc SB (SB + 137438953472) na cp sz st 0 0 0 0 (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 21)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 22)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 23)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 24)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 25)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 26)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 27)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 9)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 19)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 20)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 8)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 1))))).
  { constructor.
    all: try ((zlh HZ) || apply u_rng64 || (rewrite HSP4; (zlh HZ))).
    - rewrite ?(ri_comm c SB). regzG. rewrite (KK4 8%nat ltac:(cbn; memb')). exact D8.
    - rewrite ?(ri_comm c SB). regzG. rewrite (KK4 14%nat ltac:(cbn; memb')). exact D14.
    - rewrite ?(ri_comm c SB). regzG. rewrite (KK4 19%nat ltac:(cbn; memb')). exact D19.
    - rewrite ?(ri_comm c SB). replace (getr R4 2) with (wa (SP - 208)) by (regzG; rewrite (KK4 2%nat ltac:(cbn; memb')), D2, HSP2; f_equal; ring).
      apply (stk_ok_move m4 SP (SP - 208) 1024); [(zlh HZ) | (zlh HZ) | exact (stk_ok_grows m m4 (wa SP) 2048 G14 HSTK) | (zlh HZ) | (zlh HZ) | (zlh HZ)].
    - rewrite ?(ri_comm c SB). apply (rd_frame m m4); [(zlh HZ) | lenq; (zlh HZ) | intros x Hx; znq; apply F14; clear - HZ Hx; lia | exact Rna].
    - rewrite ?(ri_comm c SB). intros d k Hd Hk. apply (store_ok_mono SEGS k m m4 _ G14). replace (SB + 137438953472 + 128 * c + 72 + d) with (SB + 137438953472 + 128 * c + (72 + d)) by ring. apply Iwri; clear - HZ Hd Hk; lia.
    - rewrite ?(ri_comm c SB). rewrite Z.add_0_r. apply (rd_frame m3 m4); [(zlh HZ) | lenq; (zlh HZ) | intros x Hx; znq; apply F4; clear - HZ Hx; lia | exact R3mu].
    - rewrite ?(ri_comm c SB). intros d k Hd Hk. rewrite Z.add_0_r. apply (store_ok_mono SEGS k m m4 _ G14). apply Iwri; clear - HZ Hd Hk; lia.
    - rewrite ?(ri_comm c SB). rewrite HSP4. apply (rd_frame m3 m4); [clear - HZ4; lia | lenq; clear - HZ4; lia | intros x Hx; znq; apply F4; clear - HZ4 Hx; lia | exact S10].
    - rewrite ?(ri_comm c SB). rewrite HSP4. apply (rd_frame m3 m4); [clear - HZ4; lia | lenq; clear - HZ4; lia | intros x Hx; znq; apply F4; clear - HZ4 Hx; lia | exact S11].
    - rewrite ?(ri_comm c SB). rewrite HSP4. apply (rd_frame m3 m4); [clear - HZ4; lia | lenq; clear - HZ4; lia | intros x Hx; znq; apply F4; clear - HZ4 Hx; lia | exact S12].
    - rewrite ?(ri_comm c SB). rewrite HSP4. apply (rd_frame m3 m4); [clear - HZ4; lia | lenq; clear - HZ4; lia | intros x Hx; znq; apply F4; clear - HZ4 Hx; lia | exact S13].
    - rewrite ?(ri_comm c SB). rewrite HSP4. apply (rd_frame m3 m4); [clear - HZ4; lia | lenq; clear - HZ4; lia | intros x Hx; znq; apply F4; clear - HZ4 Hx; lia | exact S14].
    - rewrite ?(ri_comm c SB). rewrite HSP4. apply (rd_frame m3 m4); [clear - HZ4; lia | lenq; clear - HZ4; lia | intros x Hx; znq; apply F4; clear - HZ4 Hx; lia | exact S15].
    - rewrite ?(ri_comm c SB). rewrite HSP4. apply (rd_frame m3 m4); [clear - HZ4; lia | lenq; clear - HZ4; lia | intros x Hx; znq; apply F4; clear - HZ4 Hx; lia | exact S16].
    - rewrite ?(ri_comm c SB). rewrite HSP4. apply (rd_frame m3 m4); [clear - HZ4; lia | lenq; clear - HZ4; lia | intros x Hx; znq; apply F4; clear - HZ4 Hx; lia | exact S17].
    - rewrite ?(ri_comm c SB). rewrite HSP4. apply (rd_frame m3 m4); [clear - HZ4; lia | lenq; clear - HZ4; lia | intros x Hx; znq; apply F4; clear - HZ4 Hx; lia | exact S18].
    - rewrite ?(ri_comm c SB). rewrite HSP4. apply (rd_frame m3 m4); [clear - HZ4; lia | lenq; clear - HZ4; lia | intros x Hx; znq; apply F4; clear - HZ4 Hx; lia | exact S19].
    - rewrite ?(ri_comm c SB). rewrite HSP4. apply (rd_frame m3 m4); [clear - HZ4; lia | lenq; clear - HZ4; lia | intros x Hx; znq; apply F4; clear - HZ4 Hx; lia | exact S20].
    - rewrite ?(ri_comm c SB). rewrite HSP4. apply (rd_frame m3 m4); [clear - HZ4; lia | lenq; clear - HZ4; lia | intros x Hx; znq; apply F4; clear - HZ4 Hx; lia | exact S21].
    - rewrite ?(ri_comm c SB). rewrite HSP4. apply (rd_frame m3 m4); [clear - HZ4; lia | lenq; clear - HZ4; lia | intros x Hx; znq; apply F4; clear - HZ4 Hx; lia | exact S22].
    - rewrite ?(ri_comm c SB). rewrite HSP4. apply (rd_frame m3 m4); [clear - HZ4; lia | lenq; clear - HZ4; lia | intros x Hx; znq; apply F4; clear - HZ4 Hx; lia | exact S23].
    - rewrite ?(ri_comm c SB). rewrite HSP4. apply (rd_frame m3 m4); [clear - HZ4; lia | lenq; clear - HZ4; lia | intros x Hx; znq; apply F4; clear - HZ4 Hx; lia | exact S24].
    - rewrite ?(ri_comm c SB). rewrite HSP4. apply (rd_frame m3 m4); [clear - HZ4; lia | lenq; clear - HZ4; lia | intros x Hx; znq; apply F4; clear - HZ4 Hx; lia | exact S25].
    - rewrite ?(ri_comm c SB). rewrite HSP4. apply (rd_frame m3 m4); [clear - HZ4; lia | lenq; clear - HZ4; lia | intros x Hx; znq; apply F4; clear - HZ4 Hx; lia | exact S26].
    - rewrite ?(ri_comm c SB). rewrite HSP4. apply (rd_frame m3 m4); [clear - HZ4; lia | lenq; clear - HZ4; lia | intros x Hx; znq; apply F4; clear - HZ4 Hx; lia | exact S27].
    - rewrite ?(ri_comm c SB). rewrite HSP4. apply (rd_frame m3 m4); [clear - HZ4; lia | lenq; clear - HZ4; lia | intros x Hx; znq; apply F4; clear - HZ4 Hx; lia | exact S28].
    - rewrite ?(ri_comm c SB). rewrite HSP4. apply (rd_frame m3 m4); [clear - HZ4; lia | lenq; clear - HZ4; lia | intros x Hx; znq; apply F4; clear - HZ4 Hx; lia | exact S29].
    - rewrite ?(ri_comm c SB). rewrite HSP4. apply (rd_frame m3 m4); [clear - HZ4; lia | lenq; clear - HZ4; lia | intros x Hx; znq; apply F4; clear - HZ4 Hx; lia | exact S30].
    - rewrite ?(ri_comm c SB). rewrite HSP4. apply (rd_frame m3 m4); [clear - HZ4; lia | lenq; clear - HZ4; lia | intros x Hx; znq; apply F4; clear - HZ4 Hx; lia | exact S31].
    - rewrite ?(ri_comm c SB). intros d k Hd Hk. rewrite Z.add_0_r. apply (store_ok_mono SEGS k m m4 _ G14). apply Iwrec; clear - HZ Hd Hk; lia.
    - rewrite ?(ri_comm c SB). apply (rd_frame m m4); [(zlh HZ) | lenq; (zlh HZ) | intros x Hx; znq; apply F14; clear - HZ Hx; lia | exact Isz].
    - rewrite ?(ri_comm c SB). rewrite chp_off by (zlh HZ). pose proof (RD4 (nc - 1) ltac:((zlh HZ))) as R7.
      replace (CA + 80 * c + 16 + 4 * (nc - 1)) with (CA + (80 * c + 4 * (nc - 1)) + 16) in R7 by ring.
      replace ((newc - 1 - (nf - nc + (nc - 1))) * (sz / 16)) with cp in R7 by (unfold cp; ring). exact R7.
    - rewrite ?(ri_comm c SB). apply (rd_frame m m4); [(zlh HZ) | lenq; (zlh HZ) | intros x Hx; znq; apply F14; clear - HZ Hx; lia | exact ISB].
    - rewrite ?(ri_comm c SB). apply (rd_frame m m4); [(zlh HZ) | lenq; (zlh HZ) | intros x Hx; znq; apply F14; clear - HZ Hx; lia | exact Rst].
    - rewrite ?(ri_comm c SB). intros d k Hd Hk. apply (store_ok_mono SEGS k m m4 _ G14). replace (CA + 2576 + d) with (CA + 2560 + (16 + d)) by ring. apply Iwst; clear - HZ Hd Hk; lia.
    - rewrite ?(ri_comm c SB). intros i Hi. change (Z_to_bv 64 i) with (wa i). rewrite F14 by (clear - HZ Hi; lia). apply HIMG. exact Hi. }
  destruct (OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp.AXF_gngtz.gngt_pngt R4 m4 rom CA c nc SB (SB + 137438953472) na cp sz st 0 0 0 0 (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 21)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 22)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 23)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 24)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 25)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 26)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 27)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 9)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 19)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 20)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 8)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 1)))) P4
              (sc_gngt R4 m4 (SP - 208) HSP4 CA c nc SB (SB + 137438953472) na cp sz st 0 0 0 0 (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 21)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 22)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 23)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 24)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 25)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 26)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 27)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 9)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 19)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 20)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 8)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 1)))) ltac:((zlh HZ))))
    as (R5 & Hms5 & T1 & T2 & T5 & T6 & T7 & T8 & T9 & T10 & T11 & T12 & T13 & T14 & T15 & T16 & T17 & T18 & T19 & T20 & T21 & T22 & T23 & T24 & T25 & T26 & T27 & T28 & KK5).
  clear P4 T5 T6 T7 T11 T12 T13 T14 T15 T16 T17 T28.
  pose proof (msteps_trans SEGS _ _ _ Hms14 Hms5) as Hms. clear Hms14 Hms5.
  set (m5 := m5c m4 (SB + 137438953472 + 128 * c) (CA + 80 * c) CA nc na sz st).
  assert (EM5 : OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp.AXF_gngtz.gngt_mem_pngt m4 R4 CA c nc SB (SB + 137438953472) na cp sz st 0 0 0 0 (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 21)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 22)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 23)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 24)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 25)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 26)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 27)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 9)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 19)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 20)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 8)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 1)))) = m5).
  { unfold m5, m5c, OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp.AXF_gngtz.gngt_mem_pngt. rewrite ?(ri_comm c SB). rewrite ext_Z_lo32_small by (zlh HZ). rewrite ?Z.add_0_r, ?addneg. reflexivity. }
  rewrite EM5 in Hms. clear EM5.
  assert (G5 : mem_grows m m5) by (exact (mem_grows_trans _ _ _ G14 (m5c_grows _ _ _ _ _ _ _ _))).
  assert (FX5 : forall x, 0 <= x < 2^64 -> ~ (SP - 184 <= x < SP) -> ~ (SB + 137438953472 + 128 * c <= x < SB + 137438953472 + 128 * c + 24) ->
                  ~ (SB + 137438953472 + 128 * c + 72 <= x < SB + 137438953472 + 128 * c + 80) -> ~ (CA + 80 * c <= x < CA + 80 * c + 4) ->
                  ~ (CA + 80 * c + 16 <= x < CA + 80 * c + 16 + 4 * nc) -> ~ (CA + 2576 <= x < CA + 2584) -> m5 (wa x) = m (wa x)).
  { intros x Hx Q1 Q2 Q3 Q4 Q5 Q6. unfold m5. rewrite m5c_frame by (clear - HZ Hx Q1 Q2 Q3 Q4 Q5 Q6; lia). apply F14; assumption. }
  destruct (m5c_rd m4 (SB + 137438953472 + 128 * c) (CA + 80 * c) CA nc na sz st ltac:((zlh HZ)) ltac:((zlh HZ)) ltac:((zlh HZ)) ltac:((zlh HZ)) ltac:((zlh HZ)) ltac:((zlh HZ)) ltac:((zlh HZ)))
    as (Rc5 & Rmu5 & Rna5 & Rst5).
  fold m5 in Rc5, Rmu5, Rna5, Rst5.
  exists R5, m5. split; [exact Hms|].
  regzH T2. regzH T8. regzH T9. regzH T10. regzH T18. regzH T19. regzH T20. regzH T21. regzH T22. regzH T23. regzH T24. regzH T25. regzH T26. regzH T27. regzH T1.
  split; [rewrite T2, HSP4; f_equal; ring|].
  split.
  { intros k Hk. cbn [KCALLEE In] in Hk. repeat (destruct Hk as [<-|Hk]; [first [ (match goal with T : getr R5 (Z_to_bv 5 (Z.of_nat ?k)) = wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat ?k)))) |- getr R5 (Z_to_bv 5 (Z.of_nat ?k)) = _ => rewrite T; apply wa_u end)
                                                                          | (lazymatch goal with |- getr R5 (Z_to_bv 5 (Z.of_nat ?k)) = _ => rewrite (KK5 k ltac:(cbn; memb')), (KK4 k ltac:(cbn; memb')), (KK3 k ltac:(cbn; memb')), (KK2 k ltac:(cbn; memb')), (KK1 k ltac:(cbn; memb')); reflexivity end) ] |]).
    destruct Hk. }
  split.
  { regzG. rewrite T10, ext_Z_u32 by (zlh HZ). f_equal. unfold cp, nf.
    destruct HZ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ejb & _). rewrite Hsz16 at 2. rewrite Ejb. ring. }
  assert (HZI : ((4304 <= CA /\ CA + 3888 <= 65536) \/ 6537424 <= CA) /\ CA + 2592 <= SP - 2048) by (zlh HZ).
  assert (HZS : 4194304 <= SB /\ SB + 137438953472 + 4096 <= SP - 2048 /\ SP <= 2^47) by (zlh HZ).
  assert (HZP : CA + 2592 <= SB \/ SB + 137438953472 + 4096 <= CA) by (zlh HZ).
  split.
  { apply (inv_refill m m5 CA SB c sz nc newc j SP I Hj HZI HZS HZP G5 Hcnt0).
    - intros x Hx Q1 Q2. unfold owned_C in Q2. apply FX5; clear - HZ Hx Q1 Q2; lia.
    - exact Rc5.
    - apply (rd_frame m m5); [(zlh HZ) | lenq; (zlh HZ) | intros x Hx; znq; apply FX5; clear - HZ Hx; lia | exact Imc].
    - apply (rd_frame m m5); [(zlh HZ) | lenq; (zlh HZ) | intros x Hx; znq; apply FX5; clear - HZ Hx; lia | exact Isz].
    - intros i Hi. pose proof (RD4 i Hi) as Ri. replace ((newc - 1 - (nf - nc + i)) * (sz / 16)) with ((j + nc - 1 - i) * (sz / 16)) in Ri.
      2: { unfold nf. destruct HZ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ejb & _). rewrite Ejb. ring. }
      replace (CA + 80 * c + 16 + 4 * i) with (CA + 80 * c + 16 + 4 * i) in Ri by ring.
      apply (rd_frame m4 m5); [clear - HZ Hi; lia | lenq; clear - HZ Hi; lia | intros x Hx; znq; unfold m5; apply m5c_frame; clear - HZ Hi Hx; lia | exact Ri].
    - exact Rmu5.
    - replace (newc - nc * b_of nc j - nc) with (-1 * nc + nf) by (unfold nf, b; ring).
      apply (rd_frame m3 m5); [(zlh HZ) | lenq; (zlh HZ) | intros x Hx; znq; unfold m5; rewrite m5c_frame by (clear - HZ Hx; lia); apply F4; clear - HZ Hx; lia | exact R3nf].
    - exists ((nc + na) mod 2^64). split; [apply Z.mod_pos_bound; lia|]. unfold rd. rewrite (wa_eqm ((nc + na) mod 2^64) (nc + na)) by (apply Z.mod_mod; lia). exact Rna5.
    - exists ((sz + st) mod 2^64). split; [apply Z.mod_pos_bound; lia|]. unfold rd. rewrite (wa_eqm ((sz + st) mod 2^64) (sz + st)) by (apply Z.mod_mod; lia). exact Rst5. }
  split; [|exact G5].
  intros x Hx Q1 Q2. unfold owned_C in Q2. apply FX5; clear - HZ Hx Q1 Q2; lia.
Qed.

End GR.

(* [comment removed for export] *)
Theorem gpop_contract : forall {fx : FPState} rom m regs CA ND c SB sz nc newc j SP,
  c = cls_of ND -> INV_G m CA SB c sz nc newc j -> j + 1 + nc <= newc -> 1 <= ND <= 65536 ->
  getr regs 2 = wa SP -> 2^46 + 4096 <= SP <= 2^47 /\ SP mod 16 = 0 -> stk_ok SEGS m (wa SP) 2048 ->
  getr regs 10 = wa 929816 -> getr regs 11 = wa CA -> getr regs 12 = wa ND -> getr regs 13 = wa 8 ->
  ((4304 <= CA /\ CA + 3888 <= 65536) \/ 6537424 <= CA) /\ CA mod 16 = 0 /\ CA + 2592 <= SP - 2048 ->
  4194304 <= SB /\ SB mod 4096 = 0 /\ SB + 137438953472 + 4096 <= SP - 2048 ->
  (CA + 2592 <= SB \/ SB + 137438953472 + 4096 <= CA) ->
  (forall i, 65536 <= i < 143360 -> m (Z_to_bv 64 i) = None) ->
  exists R m', msteps SEGS (mkst regs (wa 0x44004) m rom) (mkst R (wa 0x44224) m' rom) /\
    getr R (Z_to_bv 5 (Z.of_nat 2)) = wa SP /\
    (forall k, In k KCALLEE -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))) /\
    getr R 10 = wa (SB + c * 4294967296 + j * sz) /\
    INV_G m' CA SB c sz nc newc (j + 1) /\
    (forall x, 0 <= x < 2^64 -> ~ (SP - 2048 <= x < SP) -> ~ owned_C CA SB c x -> m' (wa x) = m (wa x)) /\ mem_grows m m'.
Proof.
  intros fx rom m regs CA ND c SB sz nc newc j SP Hc I Hj HND H2 HSP HSTK H10 H11 H12 H13 HCA HSB HSEP HIMG.
  pose proof (cnt_of_range nc j ltac:(destruct I as [Igeo]; lia) ltac:(destruct I as [Igeo]; lia)) as Hcr.
  destruct (Z.eq_dec (cnt_of nc j) 0) as [E0|E0].
  - eapply gp_refill; eassumption.
  - eapply gp_pop; try eassumption. lia.
Qed.
(* [comment removed for export] *)
