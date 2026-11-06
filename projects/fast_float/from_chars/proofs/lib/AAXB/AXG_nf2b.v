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
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_nf2.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AxAsan OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_put OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_put2 OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_np OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_np2 OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_np3 OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_np4 OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_nf1 OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_nf2.AXG_nfsc.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_np3.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_nf2.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_nf2.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_np3.AXG_npscp OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_nf2.AXG_nfscp OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_nf2.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_np.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_np.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_np.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_np.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_nf2.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_nf2.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXF_mf0z.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXF_mf0z.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Abbreviation SEGS := AsanUbsan.M.loaded_segments.
Ltac zlh H := clear - H; lia.
Ltac memb' := first [ AxSymRun3.memb_refl | repeat first [left; reflexivity | right] ].      (* [comment removed for export] *)
Ltac lenq' := rewrite ?length_N_to_le_bytes; try change (Z.of_nat 4) with 4 in *; try change (Z.of_nat 8) with 8 in *; try change (Z.of_nat 1) with 1 in *.

(* [comment removed for export] *)
Definition mAd (m : word -> option byte) (SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 g21 g22 g23 g24 g25 g26 g27 : Z) : word -> option byte :=
  wchainS (wbytes (wchainS (wchainS m SP (L1a c CA v1 v8 v9 v18 v19 v20)) SP (L2a c CA n g21 g22 g23 g24 g25 g26 g27))
                  (wa RI) (word_to_le_bytes 8 (wa 1152921504606846976))) SP (L3a c CA n RI RB FA).

Section SAB.
Context {fx : FPState}.
Variable rom : word -> option byte.
Variables (m : word -> option byte) (regs : bvmap 5 word) (CA ND c SB SP sz0 st : Z).
Hypothesis Hc : c = (ND + 31) / 32.
Hypothesis HND : 33 <= ND <= 512.
Hypothesis H2 : getr regs 2 = wa SP.
Hypothesis HSP : 2^46 + 4096 <= SP <= 2^47 /\ SP mod 16 = 0.
Hypothesis HSTK : stk_ok SEGS m (wa SP) 2048.
Hypothesis H10 : getr regs 10 = wa 929816.
Hypothesis H11 : getr regs 11 = wa CA.
Hypothesis H12 : getr regs 12 = wa ND.
Hypothesis H13 : getr regs 13 = wa 8.
Hypothesis HCA : ((4304 <= CA /\ CA + 3888 <= 65536) \/ 6537424 <= CA) /\ CA mod 16 = 0 /\ CA + 4096 <= SP - 2048.
Hypothesis HSB : 17594333495296 <= SB /\ SB mod 4096 = 0 /\ SB + 137438953472 + 4096 <= SP - 2048.
Hypothesis HSEP : CA + 2592 <= SB \/ SB + 137438953472 + 4096 <= CA.
Hypothesis Hszst : 0 <= sz0 < 2^64 /\ 0 <= st < 2^64.
Hypothesis Icnt : rd m (CA + 80 * c) 4 0.
Hypothesis Imc : rd m (CA + 80 * c + 4) 4 (mc_tbl c).
Hypothesis Isz : rd m (CA + 80 * c + 8) 8 sz0.
Hypothesis Ist : rd m (CA + 2576) 8 st.
Hypothesis Iwc : wr m CA 2592.
Hypothesis ISB : rd m 929848 8 SB.
Hypothesis IRIB : rd m 929864 8 (SB + 137438953472).
Hypothesis Irtoi : rd m 929856 4 4294967295.
Hypothesis Iprem : rd m 929872 1 0.
Hypothesis Imu : rd m (SB + 137438953472 + 128 * c) 8 0.
Hypothesis Inf0 : rd m (SB + 137438953472 + 128 * c + 16) 8 0.
Hypothesis Iau : rd m (SB + 137438953472 + 128 * c + 32) 8 0.
Hypothesis Imapu : rd m (SB + 137438953472 + 128 * c + 48) 8 0.
Hypothesis Imeta : rd m (SB + 137438953472 + 128 * c + 56) 8 0.
Hypothesis Iwri : wr m (SB + 137438953472 + 128 * c) 128.
Hypothesis Igot : rd m 910448 8 1532192.
Hypothesis Ipsz : rd m 1532192 8 4096.
Hypothesis Icf : rd m 910464 8 1540520.
Hypothesis Idpm : rd m 1540780 1 0.

#[using="ND sz0 st Hc HND H2 HSP HSTK H10 H11 H12 H13 HCA HSB HSEP Hszst Icnt Imc Isz Ist Iwc ISB IRIB Irtoi Iprem Imu Inf0 Iau Imapu Imeta Iwri Igot Ipsz Icf Idpm"] Lemma segA' : exists R mA, msteps SEGS (mkst regs (wa 0x44004) m rom) (mkst R (wa 0x73c38) mA rom) /\
  getr R (Z_to_bv 5 (Z.of_nat 1)) = wa 481784 /\ getr R (Z_to_bv 5 (Z.of_nat 2)) = wa (SP - 400) /\
  getr R (Z_to_bv 5 (Z.of_nat 8)) = wa 262144 /\ getr R (Z_to_bv 5 (Z.of_nat 10)) = wa (SB + 4294967296 * c) /\
  getr R (Z_to_bv 5 (Z.of_nat 11)) = wa 262144 /\ getr R (Z_to_bv 5 (Z.of_nat 12)) = wa 3 /\ getr R (Z_to_bv 5 (Z.of_nat 13)) = wa 50 /\
  getr R (Z_to_bv 5 (Z.of_nat 14)) = wa 18446744073709551615 /\ getr R (Z_to_bv 5 (Z.of_nat 15)) = wa 0 /\
  getr R (Z_to_bv 5 (Z.of_nat 17)) = wa 222 /\ getr R (Z_to_bv 5 (Z.of_nat 21)) = wa (32 * c) /\ getr R (Z_to_bv 5 (Z.of_nat 22)) = wa 929816 /\
  (forall k, In k [3; 4]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))) /\
  mA = mAd m SP CA c (mc_tbl c / 2) (SB + 137438953472 + 128 * c) (SB + 4294967296 * c) (SB + 4294967296 * c + 3758096384)
         (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 1)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 8)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 9))))
         (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 19)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 20))))
         (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 21)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 22)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 23))))
         (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 24)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 25)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 26))))
         (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 27)))).
Proof. LiaFast.lf_pins (fun (ND sz0 st Hc HND H2 HSP HSTK H10 H11 H12 H13 HCA HSB HSEP Hszst Icnt Imc Isz Ist Iwc ISB IRIB Irtoi Iprem Imu Inf0 Iau Imapu Imeta Iwri Igot Ipsz Icf Idpm : LiaFast.U) => LiaFast.u0).
  assert (HC5 : Z.shiftr ((ND + 31) mod 2^64) 5 = c) by (rewrite Hc; apply c_of_nd; exact HND).
  pose proof (c_of_nd_range ND HND) as Hcr5. rewrite <- Hc in Hcr5.
  assert (HZ : ((4304 <= CA /\ CA + 3888 <= 65536) \/ 6537424 <= CA) /\ CA mod 16 = 0 /\ CA + 4096 <= SP - 2048 /\ 17594333495296 <= SB /\ SB mod 4096 = 0 /\
               SB + 137438953472 + 4096 <= SP - 2048 /\ 2^46 + 4096 <= SP <= 2^47 /\ 2 <= c <= 16 /\ 33 <= ND <= 512 /\
               (CA + 2592 <= SB \/ SB + 137438953472 + 4096 <= CA) /\ 0 <= sz0 < 2^64 /\ 0 <= st < 2^64) by (clear - HCA HSB HSP Hcr5 HND HSEP Hszst; lia).
  clear HCA HSB HSP Hcr5 HSEP Hszst.
  assert (HSPa : bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) = SP) by (rgz; rewrite H2, u_wa_small by (zlh HZ); reflexivity).
  (* [comment removed for export] *)
  assert (P0 : OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_np.AXF_np0rz.np0r_pre regs m CA ND 0 sz0 SB st).
  { constructor; [exact H10 | exact H11 | exact H12 | exact H13 | | (zlh HZ) | (zlh HZ) | (zlh HZ) | (zlh HZ) | (zlh HZ) | (zlh HZ) | (zlh HZ) | rewrite HSPa; (zlh HZ) | | | | | | ].
    - rewrite H2. apply (stk_ok_shrink m (wa SP) 2048 1024); [(zlh HZ) | exact HSTK].
    - rewrite HC5, Z.add_0_r. exact Icnt.
    - intros d k Hd Hk. rewrite HC5, Z.add_0_r. replace (CA + 80 * c + d) with (CA + (80 * c + d)) by ring. apply Iwc; clear - HZ Hd Hk; lia.
    - rewrite HC5. exact Isz.
    - exact ISB.
    - exact Ist.
    - intros d k Hd Hk. replace (CA + 2576 + d) with (CA + (2576 + d)) by ring. apply Iwc; clear - HZ Hd Hk; lia. }
  destruct (OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_np.AXF_np0rz.np0r_pnp0r regs m rom CA ND 0 sz0 SB st P0 (sc_np0r_p regs m SP CA ND SB HSPa ltac:((zlh HZ)) ltac:(unfold ca_place; (zlh HZ)) sz0 st))
    as (R1 & Hms1 & B2 & B8 & B9 & B10 & B11 & B12 & B13 & B14 & B15 & B18 & B19 & B20 & KK1).
  clear P0 B14 B15.
  set (m1 := OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_np.AXF_np0rz.np0r_mem_pnp0r m regs CA ND 0 sz0 SB st) in *.
  assert (EM1 : m1 = wchainS m SP [(-48, 8%nat, bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 20)))); (-40, 8%nat, bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 19))));
                                     (-32, 8%nat, bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18)))); (-24, 8%nat, bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 9))));
                                     (-16, 8%nat, bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 8)))); (-8, 8%nat, bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 1))))]).
  { unfold m1, OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_np.AXF_np0rz.np0r_mem_pnp0r. rewrite HSPa. reflexivity. }
  clearbody m1.
  assert (G1 : mem_grows m m1) by (rewrite EM1; apply wchainS_grows).
  assert (F1 : forall x, 0 <= x < 2^64 -> ~ (SP - 48 <= x < SP) -> m1 (wa x) = m (wa x)).
  { intros x Hx H. rewrite EM1. apply (wchainS_frame_in _ m SP (-48) 0); [(zlh HZ) | (zlh HZ) | vm_compute; reflexivity | vm_compute; reflexivity | exact Hx | rewrite Z.add_0_r; exact H]. }
  regzH B2. regzH B8. regzH B9. regzH B18. regzH B19. regzH B20.
  assert (HSP1 : bv_unsigned (getr R1 (Z_to_bv 5 (Z.of_nat 2))) = SP - 48) by (rewrite B2, HSPa, u_wa_small by (zlh HZ); ring).
  (* [comment removed for export] *)
  set (n := mc_tbl c / 2).
  destruct (mc_tbl_rng c ltac:((zlh HZ))) as [Hmc1 Hmc2].
  assert (Hn : 2 <= n <= 8 /\ mc_tbl c = 2 * n) by (unfold n; pose proof (Z.div_mod (mc_tbl c) 2 ltac:(lia)); lia).
  assert (P1 : OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_np.AXF_nprz.npr_pre R1 m1 CA ND (mc_tbl c)).
  { constructor; [exact B10 | exact B11 | exact B12 | exact B13 | | first [(zlh HZ) | (zlh Hmc1)] | first [(zlh HZ) | (zlh Hmc1)] | first [(zlh HZ) | (zlh Hmc1)]
                 | first [(zlh HZ) | (zlh Hmc1)] | first [rewrite HSP1; (zlh HZ) | (zlh HZ) | (zlh Hmc1)] | ].
    - replace (getr R1 2) with (wa (SP - 48)) by (rgz; rewrite B2, HSPa; f_equal; ring).
      apply (stk_ok_move m1 SP (SP - 48) 1024); [(zlh HZ) | (zlh HZ) | exact (stk_ok_grows m m1 (wa SP) 2048 G1 HSTK) | (zlh HZ) | (zlh HZ) | (zlh HZ)].
    - rewrite HC5. apply (rd_frame m m1); [(zlh HZ) | lenq; (zlh HZ) | intros x Hx; znq; apply F1; clear - HZ Hx; lia | exact Imc]. }
  destruct (OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_np.AXF_nprz.npr_pnpr R1 m1 rom CA ND (mc_tbl c) P1 (sc_npr_p R1 m1 (SP - 48) CA ND HSP1 ltac:((zlh HZ)) ltac:(unfold ca_place; (zlh HZ)) (mc_tbl c) ltac:((zlh Hmc1))))
    as (R2 & Hms2 & C1 & C2 & C8 & C9 & C10 & C11 & C12 & C13 & C14 & KK2).
  clear P1 C1.
  pose proof (msteps_trans SEGS _ _ _ Hms1 Hms2) as Hms. clear Hms1 Hms2.
  regzH C2. regzH C8. regzH C9.
  assert (Vn : bv_unsigned (edenot (Ez R1 (OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_np.AXF_nprz.VALS_npr CA ND (mc_tbl c))) (EAluw ALU_SRL (EExt true 0 4 (EVar 34)) (ELit 1))) = n).
  { rewrite (srlw1 0 0 0 0 R1 (OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_np.AXF_nprz.VALS_npr CA ND (mc_tbl c)) (mc_tbl c) eq_refl ltac:(lia)). reflexivity. }
  rewrite Vn in C9, C14.
  assert (V18 : bv_unsigned (getr R1 (Z_to_bv 5 (Z.of_nat 8))) = c) by (rewrite B8, HC5, u_wa_small by (zlh HZ); reflexivity).
  assert (V19 : bv_unsigned (getr R1 (Z_to_bv 5 (Z.of_nat 9))) = CA + 80 * c) by (rewrite B9, HC5, u_wa_small by (zlh HZ); reflexivity).
  set (m2 := OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_np.AXF_nprz.npr_mem_pnpr m1 R1 CA ND (mc_tbl c)) in *.
  assert (EM2 : m2 = wchainS m1 SP [(-72, 8%nat, CA + 80 * c); (-64, 8%nat, c); (-56, 8%nat, 279220)]).
  { unfold m2, OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_np.AXF_nprz.npr_mem_pnpr. rewrite HSP1, V18, V19, ?sub_add_lit. reflexivity. }
  clearbody m2.
  assert (HSP3 : bv_unsigned (getr R2 (Z_to_bv 5 (Z.of_nat 2))) = SP - 80) by (rewrite C2, HSP1, u_wa_small by (zlh HZ); ring).
  assert (G2 : mem_grows m m2).
  { rewrite EM2. exact (mem_grows_trans m m1 _ G1 (wchainS_grows _ m1 SP)). }
  assert (F12 : forall x, 0 <= x < 2^64 -> ~ (SP - 2048 <= x < SP) -> ~ (CA <= x < CA + 4096) -> m2 (wa x) = m (wa x)).
  { intros x Hx Q1 Q2. rewrite EM2.
    rewrite (wchainS_frame_in [(-72, 8%nat, CA + 80 * c); (-64, 8%nat, c); (-56, 8%nat, 279220)] m1 SP (-72) (-48)); [| clear - HZ; lia | clear - HZ; lia | reflexivity | reflexivity | clear - Hx; lia | clear - HZ Q1; lia]. apply F1; clear - HZ Hx Q1; lia. }
  (* [comment removed for export] *)
  assert (P3 : OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_nf2.AXF_ng0pz.ng0p_pre R2 m2 CA ND n SB (SB + 137438953472)).
  { constructor; [exact C10 | exact C11 | exact C12 | exact C13 | exact C14
                 | (replace (getr R2 2) with (wa (SP - 80)) by (regzG; rewrite C2, HSP1; f_equal; ring);
                    apply (stk_ok_move m2 SP (SP - 80) 1024); [(zlh HZ) | (zlh HZ) | exact (stk_ok_grows m m2 (wa SP) 2048 G2 HSTK) | (zlh HZ) | (zlh HZ) | (zlh HZ)])
                 | (zlh HZ) | (zlh HZ) | (zlh Hn) | (zlh HZ) | (zlh HZ) | (zlh HZ)
                 | rewrite HSP3; (zlh HZ) | (zlh HZ) | (zlh HZ) | | | | | | | | | | ].
    all: try rewrite HC5, ?Z.add_0_r.
    all: first [ (apply (rd_frame m m2); [(zlh HZ) | lenq; (zlh HZ) | intros x Hx; znq; apply F12; clear - HZ Hx; lia | assumption])
               | (intros d k Hd Hk; apply (store_ok_mono SEGS k m m2 _ G2); apply Iwri; clear - HZ Hd Hk; lia) ]. }
  destruct (OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_nf2.AXF_ng0pz.ng0p_png0p R2 m2 rom CA ND n SB (SB + 137438953472) P3
              (sc_ng0p_p R2 m2 (SP - 80) CA ND n SB (SB + 137438953472) HSP3 ltac:(unfold ca_place; clear - HZ Hn; lia)))
    as (R4 & Hms4 & E1 & E2 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & KK4).
  clear P3 E5 E6 E7 E10 E14 E15 E16 E17 E23 E24 E25.
  pose proof (msteps_trans SEGS _ _ _ Hms Hms4) as Hms'. clear Hms Hms4. rename Hms' into Hms.
  regzH C8. regzH C9.
  assert (V38 : bv_unsigned (getr R2 (Z_to_bv 5 (Z.of_nat 8))) = CA + 80 * c) by (rewrite C8, HC5, u_wa_small by (zlh HZ); reflexivity).
  assert (V39 : bv_unsigned (getr R2 (Z_to_bv 5 (Z.of_nat 9))) = n) by (rewrite C9, u_wa_small by (zlh Hn); reflexivity).
  assert (V318 : bv_unsigned (getr R2 (Z_to_bv 5 (Z.of_nat 18))) = 8) by (rewrite (KK2 18%nat ltac:(cbn; memb')), B18, u_wa_small by (zlh HZ); reflexivity).
  assert (V319 : bv_unsigned (getr R2 (Z_to_bv 5 (Z.of_nat 19))) = CA) by (rewrite (KK2 19%nat ltac:(cbn; memb')), B19, u_wa_small by (zlh HZ); reflexivity).
  assert (V320 : bv_unsigned (getr R2 (Z_to_bv 5 (Z.of_nat 20))) = 929816) by (rewrite (KK2 20%nat ltac:(cbn; memb')), B20, u_wa_small by (zlh HZ); reflexivity).
  assert (W21 : getr R2 (Z_to_bv 5 (Z.of_nat 21)) = getr regs (Z_to_bv 5 (Z.of_nat 21))) by (rewrite (KK2 21%nat ltac:(cbn; memb')), (KK1 21%nat ltac:(cbn; memb')); reflexivity).
  assert (W22 : getr R2 (Z_to_bv 5 (Z.of_nat 22)) = getr regs (Z_to_bv 5 (Z.of_nat 22))) by (rewrite (KK2 22%nat ltac:(cbn; memb')), (KK1 22%nat ltac:(cbn; memb')); reflexivity).
  assert (W23 : getr R2 (Z_to_bv 5 (Z.of_nat 23)) = getr regs (Z_to_bv 5 (Z.of_nat 23))) by (rewrite (KK2 23%nat ltac:(cbn; memb')), (KK1 23%nat ltac:(cbn; memb')); reflexivity).
  assert (W24 : getr R2 (Z_to_bv 5 (Z.of_nat 24)) = getr regs (Z_to_bv 5 (Z.of_nat 24))) by (rewrite (KK2 24%nat ltac:(cbn; memb')), (KK1 24%nat ltac:(cbn; memb')); reflexivity).
  assert (W25 : getr R2 (Z_to_bv 5 (Z.of_nat 25)) = getr regs (Z_to_bv 5 (Z.of_nat 25))) by (rewrite (KK2 25%nat ltac:(cbn; memb')), (KK1 25%nat ltac:(cbn; memb')); reflexivity).
  assert (W26 : getr R2 (Z_to_bv 5 (Z.of_nat 26)) = getr regs (Z_to_bv 5 (Z.of_nat 26))) by (rewrite (KK2 26%nat ltac:(cbn; memb')), (KK1 26%nat ltac:(cbn; memb')); reflexivity).
  assert (W27 : getr R2 (Z_to_bv 5 (Z.of_nat 27)) = getr regs (Z_to_bv 5 (Z.of_nat 27))) by (rewrite (KK2 27%nat ltac:(cbn; memb')), (KK1 27%nat ltac:(cbn; memb')); reflexivity).
  set (m3 := OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_nf2.AXF_ng0pz.ng0p_mem_png0p m2 R2 CA ND n SB (SB + 137438953472)) in *.
  assert (EM3 : m3 = wchainS (wbytes (wchainS m2 SP (L2a c CA n (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 21)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 22)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 23)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 24)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 25)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 26)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 27))))))
                               (wa (SB + 137438953472 + 128 * c)) (word_to_le_bytes 8 (wa 1152921504606846976)))
                             SP [(-272, 8%nat, n); (-264, 8%nat, CA + 80 * c + 16); (-256, 8%nat, SB + 4294967296 * c + 3758096384); (-248, 8%nat, 2305843009213693952);
                                 (-240, 8%nat, SB + 137438953472 + 128 * c + 8); (-232, 8%nat, 929816); (-224, 8%nat, SB + 137438953472 + 128 * c); (-216, 8%nat, 281360)]).
  { unfold m3, OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_nf2.AXF_ng0pz.ng0p_mem_png0p, L2a. rewrite HSP3, V38, V39, V318, V319, V320, W21, W22, W23, W24, W25, W26, W27, HC5, ?sub_add_lit, ?Z.add_0_r. reflexivity. }
  clearbody m3.
  assert (G3 : mem_grows m m3).
  { rewrite EM3. exact (mem_grows_trans _ _ _ G2 (mem_grows_trans _ _ _ (wchainS_grows (L2a c CA n (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 21)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 22)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 23)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 24)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 25)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 26)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 27))))) m2 SP)
                          (mem_grows_trans _ _ _ (wbytes_grows _ _ _) (wchainS_grows _ _ SP)))). }
  assert (F13 : forall x, 0 <= x < 2^64 -> ~ (SP - 2048 <= x < SP) -> ~ (CA <= x < CA + 4096) -> ~ (SB + 137438953472 + 128 * c <= x < SB + 137438953472 + 128 * c + 8) ->
                  m3 (wa x) = m (wa x)).
  { intros x Hx Q1 Q2 Q3. rewrite EM3.
    rewrite (wchainS_frame_in [(-272, 8%nat, n); (-264, 8%nat, CA + 80 * c + 16); (-256, 8%nat, SB + 4294967296 * c + 3758096384); (-248, 8%nat, 2305843009213693952);
                                 (-240, 8%nat, SB + 137438953472 + 128 * c + 8); (-232, 8%nat, 929816); (-224, 8%nat, SB + 137438953472 + 128 * c); (-216, 8%nat, 281360)] _ SP (-272) (-208));
      [| clear - HZ; lia | clear - HZ; lia | reflexivity | reflexivity | clear - Hx; lia | clear - HZ Q1; lia].
    rewrite wb_other by first [exact Hx | (lenq'; clear - HZ Hn; lia) | (lenq'; clear - HZ Hn Q3; lia)].
    rewrite (wchainS_frame_in (L2a c CA n (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 21)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 22)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 23)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 24)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 25)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 26)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 27))))) m2 SP (-184) (-80));
      [| clear - HZ; lia | clear - HZ; lia | reflexivity | reflexivity | clear - Hx; lia | clear - HZ Q1; lia].
    apply F12; assumption. }
  (* [comment removed for export] *)
  regzH E2. regzH E8. regzH E9. regzH E11. regzH E12. regzH E13. regzH E18. regzH E19. regzH E20. regzH E21. regzH E22. regzH E1.
  assert (HSP4 : bv_unsigned (getr R4 (Z_to_bv 5 (Z.of_nat 2))) = SP - 272) by (rewrite E2, HSP3, u_wa_small by (zlh HZ); ring).
  assert (Esz : 262144 * Z.shiftr ((32 * Z.shiftr ((ND + 31) mod 2^64) 5 * n + -1) mod 2^64) 18 + 262144 = 262144).
  { rewrite HC5. assert (64 <= 32 * c * n <= 4096) by (clear - HZ Hn; nia). rewrite Z.mod_small by lia. rewrite shr18' by lia. ring. }
  rewrite Esz in E12, E19.
  assert (P4 : AXF_mf0z.mf0_pre R4 m3 (SB + 4294967296 * c) 262144 96426 1540520).
  { constructor; [regzG; rewrite E11, HC5; reflexivity | regzG; exact E12 | regzG; exact E13
                 | (replace (getr R4 2) with (wa (SP - 272)) by (regzG; rewrite E2, HSP3; f_equal; ring);
                    apply (stk_ok_move m3 SP (SP - 272) 1024); [(zlh HZ) | (zlh HZ) | exact (stk_ok_grows m m3 (wa SP) 2048 G3 HSTK) | (zlh HZ) | (zlh HZ) | (zlh HZ)])
                 | (zlh HZ) | (zlh HZ) | (zlh HZ) | (zlh HZ) | (zlh HZ) | (zlh HZ) | rewrite HSP4; (zlh HZ) | | | | ].
    all: apply (rd_frame m m3); [(zlh HZ) | lenq; (zlh HZ) | intros x Hx; znq; apply F13; clear - HZ Hx; lia | assumption]. }
  destruct (AXF_mf0z.mf0_pmf0 R4 m3 rom (SB + 4294967296 * c) 262144 96426 1540520 P4
              (sc_mf0 R4 m3 (SP - 272) (SB + 4294967296 * c) 262144 96426 1540520 HSP4 ltac:((zlh HZ))))
    as (R5 & Hms5 & F1' & F2' & F8 & F9 & F10 & F11 & F12' & F13' & F14 & F15 & F17 & F18 & F19 & F20 & KK5).
  clear P4.
  pose proof (msteps_trans SEGS _ _ _ Hms Hms5) as Hms'. clear Hms Hms5. rename Hms' into Hms.
  assert (EM4 : AXF_mf0z.mf0_mem_pmf0 m3 R4 (SB + 4294967296 * c) 262144 96426 1540520 =
                wchainS m3 SP [(-456, 8%nat, 32 * c); (-448, 8%nat, 1532192); (-440, 8%nat, 96426); (-432, 8%nat, SB + 4294967296 * c); (-424, 8%nat, 1);
                               (-416, 8%nat, 262144); (-408, 8%nat, 481756); (-400, 4%nat, 50); (-352, 8%nat, SB + 4294967296 * c); (-344, 8%nat, 262144);
                               (-336, 8%nat, SB + 4294967296 * c); (-328, 8%nat, SB + 4294967296 * c); (-320, 8%nat, 262144); (-312, 8%nat, 514992);
                               (-304, 8%nat, SB + 4294967296 * c); (-296, 8%nat, CA + 2560); (-288, 8%nat, SB + 137438953472 + 128 * c); (-280, 8%nat, 281724)]).
  { unfold AXF_mf0z.mf0_mem_pmf0. rewrite HSP4, E1, E8, E9, E18, E19, E20, E21, HC5, ?u_wa_small by (zlh HZ). rewrite ?sub_add_lit. reflexivity. }
  rewrite EM4 in Hms. clear EM4.
  eexists R5, _. split; [exact Hms|].
  split; [regzH F1'; exact F1'|]. split; [regzH F2'; rewrite F2', HSP4; f_equal; ring|].
  split; [regzH F8; exact F8|]. split; [regzH F10; exact F10|]. split; [regzH F11; exact F11|]. split; [regzH F12'; exact F12'|].
  split; [regzH F13'; exact F13'|]. split; [regzH F14; exact F14|]. split; [regzH F15; exact F15|]. split; [regzH F17; exact F17|].
  split; [rewrite (KK5 21%nat ltac:(cbn; memb')), E21, HC5; reflexivity|].
  split; [rewrite (KK5 22%nat ltac:(cbn; memb')); exact E22|].
  split; [intros k Hk; cbn in Hk; destruct Hk as [<-|[<-|[]]]; lazymatch goal with |- getr R5 (Z_to_bv 5 (Z.of_nat ?k)) = _ => rewrite (KK5 k ltac:(cbn; memb')), (KK4 k ltac:(cbn; memb')), (KK2 k ltac:(cbn; memb')), (KK1 k ltac:(cbn; memb')); reflexivity end|].
  rewrite EM3, EM2, EM1. unfold mAd, L3a. rewrite <- wchainS_app. unfold L1a. rewrite <- wchainS_app. reflexivity.
Qed.
End SAB.
(* [comment removed for export] *)
