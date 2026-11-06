(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AxAsan AXG_put AXG_put2 AXG_np AXG_np2 AXG_np3 AXG_np4 AXG_nf1.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_nf2.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_np3.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_nf2.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_nf2 AXG_nf2b AXG_gp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_gp3.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_gp3 AXG_gf1.

Module AXG_gf2.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AxAsan AXG_put AXG_put2 AXG_np AXG_np2 AXG_np3 AXG_np4 AXG_nf1.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_nf2.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_np3.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_nf2.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_nf2 AXG_gp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_gp3.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_gp3 AXG_gf1.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AxAsan OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_put OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_put2 OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_np OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_np2 OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_np3 OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_np4 OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_nf1 OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_nf2.AXG_nfsc OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_np3.AXG_npscp OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_nf2.AXG_nfscp OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_nf2 OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp3.AXG_gp2 OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp3 OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gf1.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_gp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_gp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_gp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_gp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_gp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_gp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_gp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_gp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_gp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_gp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXF_mf0z.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXF_mf0z.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := AsanUbsan.M.loaded_segments.
Lemma ri_comm : forall c SB, 128 * c + (SB + 137438953472) = SB + 137438953472 + 128 * c.
Proof. intros. ring. Qed.
Lemma rb_comm : forall c SB, 4294967296 * c + SB = SB + 4294967296 * c.
Proof. intros. ring. Qed.

Section GSA.
Context {fx : FPState}.
Variable rom : word -> option byte.
Variables (m : word -> option byte) (regs : bvmap 5 word) (CA ND c SB SP sz0 st : Z).
Hypothesis Hc : c = cls_of ND.
Hypothesis HND : 1 <= ND <= 65536.
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
Hypothesis Imc : rd m (CA + 80 * c + 4) 4 0.
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

Lemma gsegA : exists R mA, msteps SEGS (mkst regs (wa 0x44004) m rom) (mkst R (wa 0x73c38) mA rom) /\
  getr R (Z_to_bv 5 (Z.of_nat 1)) = wa 481784 /\ getr R (Z_to_bv 5 (Z.of_nat 2)) = wa (SP - 400) /\
  getr R (Z_to_bv 5 (Z.of_nat 8)) = wa 262144 /\ getr R (Z_to_bv 5 (Z.of_nat 10)) = wa (SB + 4294967296 * c) /\
  getr R (Z_to_bv 5 (Z.of_nat 11)) = wa 262144 /\ getr R (Z_to_bv 5 (Z.of_nat 12)) = wa 3 /\ getr R (Z_to_bv 5 (Z.of_nat 13)) = wa 50 /\
  getr R (Z_to_bv 5 (Z.of_nat 14)) = wa 18446744073709551615 /\ getr R (Z_to_bv 5 (Z.of_nat 15)) = wa 0 /\
  getr R (Z_to_bv 5 (Z.of_nat 17)) = wa 222 /\ getr R (Z_to_bv 5 (Z.of_nat 21)) = wa (sz_tbl c) /\ getr R (Z_to_bv 5 (Z.of_nat 22)) = wa 929816 /\
  (forall k, In k [3; 4]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))) /\
  mA = gmAc m SP CA c (mc_tbl c / 2) (SB + 137438953472 + 128 * c) (SB + 4294967296 * c) (SB + 4294967296 * c + 3758096384)
         (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 1)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 8)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 9))))
         (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 19)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 20))))
         (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 21)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 22)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 23))))
         (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 24)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 25)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 26))))
         (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 27)))).
Proof using All.
  assert (Hcr5 : 1 <= c <= 30) by (rewrite Hc; apply cls_of_rng; exact HND).
  assert (HZ : ((4304 <= CA /\ CA + 3888 <= 65536) \/ 6537424 <= CA) /\ CA mod 16 = 0 /\ CA + 4096 <= SP - 2048 /\ 17594333495296 <= SB /\ SB mod 4096 = 0 /\
               SB + 137438953472 + 4096 <= SP - 2048 /\ 2^46 + 4096 <= SP <= 2^47 /\ 1 <= c <= 30 /\ 1 <= ND <= 65536 /\
               (CA + 2592 <= SB \/ SB + 137438953472 + 4096 <= CA) /\ 0 <= sz0 < 2^64 /\ 0 <= st < 2^64) by (clear - HCA HSB HSP Hcr5 HND HSEP Hszst; lia).
  clear HCA HSB HSP Hcr5 HSEP Hszst.
  assert (HSPa : bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) = SP) by (rgz; rewrite H2, u_wa_small by (zlh HZ); reflexivity).
  (* [comment removed for export] *)
  destruct (gp_head rom m regs CA ND SP H2 ltac:(zlh HZ) HSTK H10 H11 H12 H13 ltac:(zlh HZ) ltac:(zlh HZ))
    as (R0 & Hms0 & A2 & A8 & _ & A10 & A11 & A13 & KK0).
  rewrite <- Hc in A8.
  set (m1 := wchainS m SP (LHD (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 1)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 8)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 9)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 19)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 20)))))) in *.
  assert (EM1 : m1 = wchainS m SP [(-48, 8%nat, bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 20)))); (-40, 8%nat, bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 19))));
                                     (-32, 8%nat, bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18)))); (-24, 8%nat, bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 9))));
                                     (-16, 8%nat, bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 8)))); (-8, 8%nat, bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 1))))]) by reflexivity.
  clearbody m1.
  assert (G1 : mem_grows m m1) by (rewrite EM1; apply wchainS_grows).
  assert (F1 : forall x, 0 <= x < 2^64 -> ~ (SP - 48 <= x < SP) -> m1 (wa x) = m (wa x)).
  { intros x Hx H. rewrite EM1. apply (wchainS_frame_in _ m SP (-48) 0); [(zlh HZ) | (zlh HZ) | vm_compute; reflexivity | vm_compute; reflexivity | exact Hx | rewrite Z.add_0_r; exact H]. }
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
  assert (P1 : OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp.AXF_gnriz.gnri_pre R1 m1 CA c).
  { constructor; [exact B10 | exact B11 | exact B12 | exact B13 | | (zlh HZ) | (zlh HZ) | (zlh HZ) | rewrite HSP1; (zlh HZ) | | ].
    - replace (getr R1 2) with (wa (SP - 48)) by (rgz; rewrite B2; reflexivity).
      apply (stk_ok_move m1 SP (SP - 48) 1024); [(zlh HZ) | (zlh HZ) | exact (stk_ok_grows m m1 (wa SP) 2048 G1 HSTK) | (zlh HZ) | (zlh HZ) | (zlh HZ)].
    - apply (rd_frame m m1); [(zlh HZ) | lenq; (zlh HZ) | intros x Hx; znq; apply F1; clear - HZ Hx; lia | exact Imc].
    - intros d k Hd Hk. apply (store_ok_mono SEGS k m m1 _ G1). replace (CA + 84 + d) with (CA + (84 + d)) by ring. apply Iwc; clear - HZ Hd Hk; lia. }
  destruct (OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp.AXF_gnriz.gnri_pnri R1 m1 rom CA c P1 (sc_gnri R1 m1 (SP - 48) HSP1 CA c ltac:((zlh HZ))))
    as (R2 & Hms2 & C1 & C2 & C5 & C6 & C7 & C8 & C10 & C11 & C12 & C13 & C14 & C15 & C16 & C17 & C28 & C29 & C30 & KK2).
  clear P1 C5 C6 C7 C15 C16 C17 C28 C29 C30.
  pose proof (msteps_trans SEGS _ _ _ Hms1 Hms2) as Hms. clear Hms1 Hms2.
  assert (V18 : bv_unsigned (getr R1 (Z_to_bv 5 (Z.of_nat 8))) = c) by (rewrite B8, u_wa_small by (zlh HZ); reflexivity).
  assert (V19 : bv_unsigned (getr R1 (Z_to_bv 5 (Z.of_nat 9))) = CA + 80 * c) by (rewrite B9, u_wa_small by (zlh HZ); reflexivity).
  set (m2 := OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp.AXF_gnriz.gnri_mem_pnri m1 R1 CA c) in *.
  assert (EM2 : m2 = ic_mem (wchainS m1 SP [(-72, 8%nat, CA + 80 * c); (-64, 8%nat, c); (-56, 8%nat, 279220)]) CA).
  { unfold m2, OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp.AXF_gnriz.gnri_mem_pnri, ic_mem. rewrite HSP1, V18, V19, ?sub_add_lit. reflexivity. }
  clearbody m2.
  set (n := mc_tbl c / 2).
  destruct (gmc_rng c ltac:((zlh HZ))) as [Hmc1 Hmc2].
  assert (Hn : 1 <= n <= 8 /\ mc_tbl c = 2 * n) by (unfold n; pose proof (Z.div_mod (mc_tbl c) 2 ltac:(lia)); lia).
  (* [comment removed for export] *)
  destruct (ic_rd (wchainS m1 SP [(-72, 8%nat, CA + 80 * c); (-64, 8%nat, c); (-56, 8%nat, 279220)]) CA c ltac:((zlh HZ)) ltac:((zlh HZ)) ltac:((zlh HZ))) as [Rmc Rsz].
  rewrite <- EM2 in Rmc, Rsz.
  assert (P2 : OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp.AXF_gnri2z.gnri2_pre R2 m2 CA c (mc_tbl c)).
  { constructor; [exact C8 | exact C10 | exact C12 | exact C14 | (zlh HZ) | (zlh HZ) | (zlh Hmc1) | (zlh HZ) | exact Rmc]. }
  destruct (OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp.AXF_gnri2z.gnri2_pnri2 R2 m2 rom CA c (mc_tbl c) P2 ltac:(cbn [OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp.AXF_gnri2.RES_pnri2 fst snd]; constructor))
    as (R3 & Hms3 & D8 & D9 & D10 & D11 & D12 & D13 & D14 & KK3).
  clear P2.
  assert (Em3 : OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp.AXF_gnri2z.gnri2_mem_pnri2 m2 R2 CA c (mc_tbl c) = m2) by reflexivity. rewrite Em3 in Hms3. clear Em3.
  pose proof (msteps_trans SEGS _ _ _ Hms Hms3) as Hms'. clear Hms Hms3. rename Hms' into Hms.
  assert (Vn : bv_unsigned (edenot (Ez R2 (OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp.AXF_gnri2z.VALS_gnri2 CA c (mc_tbl c))) (EAluw ALU_SRL (EExt true 0 4 (EVar 34)) (ELit 1))) = n).
  { rewrite (gsrlw1 R2 (OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp.AXF_gnri2z.VALS_gnri2 CA c (mc_tbl c)) (mc_tbl c) eq_refl ltac:(lia)). reflexivity. }
  rewrite Vn in D9, D14.
  regzH C2.
  assert (HSP3 : bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 2))) = SP - 80).
  { rewrite (KK3 2%nat ltac:(cbn; memb')), C2, HSP1, u_wa_small by (zlh HZ); ring. }
  assert (G2 : mem_grows m m2).
  { rewrite EM2. set (L := [(-72, 8%nat, CA + 80 * c); (-64, 8%nat, c); (-56, 8%nat, 279220)]).
    exact (mem_grows_trans m m1 (ic_mem (wchainS m1 SP L) CA) G1 (mem_grows_trans m1 (wchainS m1 SP L) (ic_mem (wchainS m1 SP L) CA) (wchainS_grows L m1 SP) (ic_grows (wchainS m1 SP L) CA))). }
  assert (F12 : forall x, 0 <= x < 2^64 -> ~ (SP - 2048 <= x < SP) -> ~ (CA <= x < CA + 4096) -> m2 (wa x) = m (wa x)).
  { intros x Hx Q1 Q2. rewrite EM2, ic_frame by (clear - HZ Hx Q2; lia).
    rewrite (wchainS_frame_in [(-72, 8%nat, CA + 80 * c); (-64, 8%nat, c); (-56, 8%nat, 279220)] m1 SP (-72) (-48)); [| clear - HZ; lia | clear - HZ; lia | reflexivity | reflexivity | clear - Hx; lia | clear - HZ Q1; lia]. apply F1; clear - HZ Hx Q1; lia. }
  (* [comment removed for export] *)
  regzH D8. regzH D9.
  assert (V38 : bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 8))) = CA + 80 * c) by (rewrite D8, u_wa_small by (zlh HZ); reflexivity).
  assert (V39 : bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 9))) = n) by (rewrite D9, u_wa_small by (zlh Hn); reflexivity).
  assert (V318 : bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 18))) = 8) by (rewrite (KK3 18%nat ltac:(cbn; memb')), (KK2 18%nat ltac:(cbn; memb')), B18, u_wa_small by (zlh HZ); reflexivity).
  assert (V319 : bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 19))) = CA) by (rewrite (KK3 19%nat ltac:(cbn; memb')), (KK2 19%nat ltac:(cbn; memb')), B19, u_wa_small by (zlh HZ); reflexivity).
  assert (V320 : bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 20))) = 929816) by (rewrite (KK3 20%nat ltac:(cbn; memb')), (KK2 20%nat ltac:(cbn; memb')), B20, u_wa_small by (zlh HZ); reflexivity).
  assert (W21 : getr R3 (Z_to_bv 5 (Z.of_nat 21)) = getr regs (Z_to_bv 5 (Z.of_nat 21))) by (rewrite (KK3 21%nat ltac:(cbn; memb')), (KK2 21%nat ltac:(cbn; memb')), (KK1 21%nat ltac:(cbn; memb')); reflexivity).
  assert (W22 : getr R3 (Z_to_bv 5 (Z.of_nat 22)) = getr regs (Z_to_bv 5 (Z.of_nat 22))) by (rewrite (KK3 22%nat ltac:(cbn; memb')), (KK2 22%nat ltac:(cbn; memb')), (KK1 22%nat ltac:(cbn; memb')); reflexivity).
  assert (W23 : getr R3 (Z_to_bv 5 (Z.of_nat 23)) = getr regs (Z_to_bv 5 (Z.of_nat 23))) by (rewrite (KK3 23%nat ltac:(cbn; memb')), (KK2 23%nat ltac:(cbn; memb')), (KK1 23%nat ltac:(cbn; memb')); reflexivity).
  assert (W24 : getr R3 (Z_to_bv 5 (Z.of_nat 24)) = getr regs (Z_to_bv 5 (Z.of_nat 24))) by (rewrite (KK3 24%nat ltac:(cbn; memb')), (KK2 24%nat ltac:(cbn; memb')), (KK1 24%nat ltac:(cbn; memb')); reflexivity).
  assert (W25 : getr R3 (Z_to_bv 5 (Z.of_nat 25)) = getr regs (Z_to_bv 5 (Z.of_nat 25))) by (rewrite (KK3 25%nat ltac:(cbn; memb')), (KK2 25%nat ltac:(cbn; memb')), (KK1 25%nat ltac:(cbn; memb')); reflexivity).
  assert (W26 : getr R3 (Z_to_bv 5 (Z.of_nat 26)) = getr regs (Z_to_bv 5 (Z.of_nat 26))) by (rewrite (KK3 26%nat ltac:(cbn; memb')), (KK2 26%nat ltac:(cbn; memb')), (KK1 26%nat ltac:(cbn; memb')); reflexivity).
  assert (W27 : getr R3 (Z_to_bv 5 (Z.of_nat 27)) = getr regs (Z_to_bv 5 (Z.of_nat 27))) by (rewrite (KK3 27%nat ltac:(cbn; memb')), (KK2 27%nat ltac:(cbn; memb')), (KK1 27%nat ltac:(cbn; memb')); reflexivity).
  destruct (gsz_rng c ltac:((zlh HZ))) as (Hsz1 & Hsz2 & Hsz3).
  assert (STEP : exists R4 m3, msteps SEGS (mkst R3 (wa 0x44790) m2 rom) (mkst R4 (wa 0x7db84) m3 rom) /\
     m3 = wchainS (wbytes (wchainS m2 SP (L2a c CA n (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 21)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 22)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 23)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 24)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 25)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 26)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 27))))))
                               (wa (SB + 137438953472 + 128 * c)) (word_to_le_bytes 8 (wa 1152921504606846976)))
                             SP [(-272, 8%nat, n); (-264, 8%nat, CA + 80 * c + 16); (-256, 8%nat, SB + 4294967296 * c + 3758096384); (-248, 8%nat, 2305843009213693952);
                                 (-240, 8%nat, SB + 137438953472 + 128 * c + 8); (-232, 8%nat, 929816); (-224, 8%nat, SB + 137438953472 + 128 * c); (-216, 8%nat, 281360)] /\
     getr R4 1 = wa 281724 /\ getr R4 2 = wa (SP - 272) /\ getr R4 8 = wa (SB + 137438953472 + 128 * c) /\ getr R4 9 = wa (CA + 2560) /\
     getr R4 11 = wa (SB + 4294967296 * c) /\ getr R4 12 = wa 262144 /\ getr R4 13 = wa 96426 /\ getr R4 18 = wa (SB + 4294967296 * c) /\
     getr R4 19 = wa 262144 /\ getr R4 20 = wa (SB + 4294967296 * c) /\ getr R4 21 = wa (sz_tbl c) /\ getr R4 22 = wa 929816 /\
     (forall k, In k [3; 4; 26; 27; 28; 29; 30; 31]%nat -> getr R4 (Z_to_bv 5 (Z.of_nat k)) = getr R3 (Z_to_bv 5 (Z.of_nat k)))).
  { destruct (Z.le_gt_cases c 16) as [Hsm|Hbg].
    - (* [comment removed for export] *)
      assert (P3 : OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp.AXF_gng0psz.gng0ps_pre R3 m2 CA c n SB (SB + 137438953472)).
      { constructor; [exact D10 | exact D11 | exact D12 | exact D13 | exact D14
                     | (replace (getr R3 2) with (wa (SP - 80)) by (regzG; rewrite (KK3 2%nat ltac:(cbn; memb')), C2, HSP1; f_equal; ring);
                        apply (stk_ok_move m2 SP (SP - 80) 1024); [(zlh HZ) | (zlh HZ) | exact (stk_ok_grows m m2 (wa SP) 2048 G2 HSTK) | (zlh HZ) | (zlh HZ) | (zlh HZ)])
                     | (zlh HZ) | (clear - Hsm HZ; lia) | (zlh Hn) | (zlh HZ) | (zlh HZ) | (zlh HZ)
                     | rewrite HSP3; (zlh HZ) | (zlh HZ) | (zlh HZ) | | | | | | | | | | ].
        all: rewrite ?(ri_comm c SB), ?Z.add_0_r.
        all: first [ (apply (rd_frame m m2); [(zlh HZ) | lenq; (zlh HZ) | intros x Hx; znq; apply F12; clear - HZ Hx; lia | assumption])
                   | (intros d k Hd Hk; apply (store_ok_mono SEGS k m m2 _ G2); apply Iwri; clear - HZ Hd Hk; lia) ]. }
      destruct (OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp.AXF_gng0psz.gng0ps_png0ps R3 m2 rom CA c n SB (SB + 137438953472) P3
                  (sc_gng0ps R3 m2 (SP - 80) HSP3 CA c n SB (SB + 137438953472) ltac:(unfold gp_ok; clear - HZ Hn; lia) ltac:(clear - Hsm HZ; lia) ltac:(zlh Hn)))
        as (R4 & Hms4 & E1 & E2 & _ & _ & _ & E8 & E9 & _ & E11 & E12 & E13 & _ & _ & _ & _ & E18 & E19 & E20 & E21 & E22 & _ & _ & _ & KK4).
      assert (Esz : 262144 * Z.shiftr ((32 * c * n + -1) mod 2^64) 18 + 262144 = 262144).
      { assert (32 <= 32 * c * n <= 4096) by (clear - Hsm HZ Hn; nia). rewrite Z.mod_small by lia. rewrite shr18' by lia. ring. }
      rewrite Esz in E12, E19. rewrite <- (gsz_small c ltac:(clear - Hsm HZ; lia)) in E21.
      exists R4, (OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp.AXF_gng0psz.gng0ps_mem_png0ps m2 R3 CA c n SB (SB + 137438953472)). split; [exact Hms4|]. split.
      { unfold OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp.AXF_gng0psz.gng0ps_mem_png0ps, L2a. rewrite HSP3, V38, V39, V318, V319, V320, W21, W22, W23, W24, W25, W26, W27, ?(ri_comm c SB), ?(rb_comm c SB), ?sub_add_lit, ?Z.add_0_r. reflexivity. }
      regzH E2. replace (128 * c + (SB + 137438953472)) with (SB + 137438953472 + 128 * c) in E8 by ring.
      replace (4294967296 * c + SB) with (SB + 4294967296 * c) in E11, E18, E20 by ring.
      repeat split; try assumption. regzG. rewrite E2, HSP3. f_equal. ring.
    - (* [comment removed for export] *)
      assert (Hn1 : n = 1) by (destruct Hn as [_ Hn2]; rewrite (gmc_big c ltac:(clear - Hbg HZ; lia)) in Hn2; lia).
      assert (P3 : OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp.AXF_gng0pbz.gng0pb_pre R3 m2 CA c n SB (SB + 137438953472)).
      { constructor; [exact D10 | exact D11 | exact D12 | exact D13 | (rewrite <- Hn1; exact D14)
                     | (replace (getr R3 2) with (wa (SP - 80)) by (regzG; rewrite (KK3 2%nat ltac:(cbn; memb')), C2, HSP1; f_equal; ring);
                        apply (stk_ok_move m2 SP (SP - 80) 1024); [(zlh HZ) | (zlh HZ) | exact (stk_ok_grows m m2 (wa SP) 2048 G2 HSTK) | (zlh HZ) | (zlh HZ) | (zlh HZ)])
                     | (zlh HZ) | (clear - Hbg HZ; lia) | (zlh Hn) | (zlh HZ) | (zlh HZ) | (zlh HZ)
                     | rewrite HSP3; (zlh HZ) | (zlh HZ) | (zlh HZ) | | | | | | | | | | ].
        all: rewrite ?(ri_comm c SB), ?Z.add_0_r.
        all: first [ (apply (rd_frame m m2); [(zlh HZ) | lenq; (zlh HZ) | intros x Hx; znq; apply F12; clear - HZ Hx; lia | assumption])
                   | (intros d k Hd Hk; apply (store_ok_mono SEGS k m m2 _ G2); apply Iwri; clear - HZ Hd Hk; lia) ]. }
      destruct (OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp.AXF_gng0pbz.gng0pb_png0pb R3 m2 rom CA c n SB (SB + 137438953472) P3
                  (sc_gng0pb R3 m2 (SP - 80) HSP3 CA c n SB (SB + 137438953472) ltac:(unfold gp_ok; clear - HZ Hn; lia) ltac:(clear - Hbg HZ; lia) ltac:(zlh Hn)))
        as (R4 & Hms4 & E1 & E2 & _ & _ & _ & E8 & E9 & _ & E11 & E12 & E13 & _ & _ & _ & _ & E18 & E19 & E20 & E21 & E22 & _ & _ & _ & KK4).
      fold BIGSZ_E in E21. rewrite (bigsz_eval R3 (OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp.AXF_gng0pbz.VALS_gng0pb CA c n SB (SB + 137438953472)) c eq_refl ltac:(clear - Hbg HZ; lia)) in E21.
      exists R4, (OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp.AXF_gng0pbz.gng0pb_mem_png0pb m2 R3 CA c n SB (SB + 137438953472)). split; [exact Hms4|]. split.
      { unfold OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp.AXF_gng0pbz.gng0pb_mem_png0pb, L2a. rewrite HSP3, V38, V39, V318, V319, V320, W21, W22, W23, W24, W25, W26, W27, ?(ri_comm c SB), ?(rb_comm c SB), ?sub_add_lit, ?Z.add_0_r, ?Hn1. reflexivity. }
      regzH E2. replace (128 * c + (SB + 137438953472)) with (SB + 137438953472 + 128 * c) in E8 by ring.
      replace (4294967296 * c + SB) with (SB + 4294967296 * c) in E11, E18, E20 by ring.
      repeat split; try assumption. regzG. rewrite E2, HSP3. f_equal. ring. }
  destruct STEP as (R4 & m3 & Hms4 & EM3 & E1 & E2 & E8 & E9 & E11 & E12 & E13 & E18 & E19 & E20 & E21 & E22 & KK4).
  pose proof (msteps_trans SEGS _ _ _ Hms Hms4) as Hms'. clear Hms Hms4. rename Hms' into Hms.
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
  assert (HSP4 : bv_unsigned (getr R4 (Z_to_bv 5 (Z.of_nat 2))) = SP - 272) by (rewrite E2, u_wa_small by (zlh HZ); reflexivity).
  assert (P4 : AXF_mf0z.mf0_pre R4 m3 (SB + 4294967296 * c) 262144 96426 1540520).
  { constructor; [regzG; rewrite E11; reflexivity | regzG; exact E12 | regzG; exact E13
                 | (replace (getr R4 2) with (wa (SP - 272)) by (regzG; rewrite E2; reflexivity);
                    apply (stk_ok_move m3 SP (SP - 272) 1024); [(zlh HZ) | (zlh HZ) | exact (stk_ok_grows m m3 (wa SP) 2048 G3 HSTK) | (zlh HZ) | (zlh HZ) | (zlh HZ)])
                 | (zlh HZ) | (zlh HZ) | (zlh HZ) | (zlh HZ) | (zlh HZ) | (zlh HZ) | rewrite HSP4; (zlh HZ) | | | | ].
    all: apply (rd_frame m m3); [(zlh HZ) | lenq; (zlh HZ) | intros x Hx; znq; apply F13; clear - HZ Hx; lia | assumption]. }
  destruct (AXF_mf0z.mf0_pmf0 R4 m3 rom (SB + 4294967296 * c) 262144 96426 1540520 P4
              (sc_mf0 R4 m3 (SP - 272) (SB + 4294967296 * c) 262144 96426 1540520 HSP4 ltac:((zlh HZ))))
    as (R5 & Hms5 & F1' & F2' & F8 & F9 & F10 & F11 & F12' & F13' & F14 & F15 & F17 & F18 & F19 & F20 & KK5).
  clear P4.
  pose proof (msteps_trans SEGS _ _ _ Hms Hms5) as Hms'. clear Hms Hms5. rename Hms' into Hms.
  assert (EM4 : AXF_mf0z.mf0_mem_pmf0 m3 R4 (SB + 4294967296 * c) 262144 96426 1540520 =
                wchainS m3 SP [(-456, 8%nat, sz_tbl c); (-448, 8%nat, 1532192); (-440, 8%nat, 96426); (-432, 8%nat, SB + 4294967296 * c); (-424, 8%nat, 1);
                               (-416, 8%nat, 262144); (-408, 8%nat, 481756); (-400, 4%nat, 50); (-352, 8%nat, SB + 4294967296 * c); (-344, 8%nat, 262144);
                               (-336, 8%nat, SB + 4294967296 * c); (-328, 8%nat, SB + 4294967296 * c); (-320, 8%nat, 262144); (-312, 8%nat, 514992);
                               (-304, 8%nat, SB + 4294967296 * c); (-296, 8%nat, CA + 2560); (-288, 8%nat, SB + 137438953472 + 128 * c); (-280, 8%nat, 281724)]).
  { unfold AXF_mf0z.mf0_mem_pmf0. rewrite HSP4, E1, E8, E9, E18, E19, E20, E21, ?u_wa_small by (first [(zlh HZ) | (zlh Hsz1)]). rewrite ?sub_add_lit. reflexivity. }
  rewrite EM4 in Hms. clear EM4.
  eexists R5, _. split; [exact Hms|].
  split; [regzH F1'; exact F1'|]. split; [regzH F2'; rewrite F2', HSP4; f_equal; ring|].
  split; [regzH F8; exact F8|]. split; [regzH F10; exact F10|]. split; [regzH F11; exact F11|]. split; [regzH F12'; exact F12'|].
  split; [regzH F13'; exact F13'|]. split; [regzH F14; exact F14|]. split; [regzH F15; exact F15|]. split; [regzH F17; exact F17|].
  split; [rewrite (KK5 21%nat ltac:(cbn; memb')), E21; reflexivity|].
  split; [rewrite (KK5 22%nat ltac:(cbn; memb')); exact E22|].
  split; [intros k Hk; cbn in Hk; destruct Hk as [<-|[<-|[]]]; lazymatch goal with |- getr R5 (Z_to_bv 5 (Z.of_nat ?k)) = _ => rewrite (KK5 k ltac:(cbn; memb')), (KK4 k ltac:(cbn; memb')), (KK3 k ltac:(cbn; memb')), (KK2 k ltac:(cbn; memb')), (KK1 k ltac:(cbn; memb')); reflexivity end|].
  rewrite EM3, EM2, EM1. unfold gmAc, gL3a. rewrite <- wchainS_app. unfold L1a. rewrite <- wchainS_app. reflexivity.
Qed.
End GSA.
(* [comment removed for export] *)
End AXG_gf2.

Import OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AxAsan OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_put OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_put2 OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_np OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_np2 OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_np3 OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_np4 OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_nf1 OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_nf2.AXG_nfsc OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_np3.AXG_npscp OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_nf2.AXG_nfscp OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_nf2 OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_nf2b OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp3.AXG_gp2 OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp3 OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gf1 OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gf2b.AXG_gf2.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_gp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_gp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_gp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_gp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_gp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_gp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_gp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_gp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXF_mf0z.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXF_mf0z.
Import ListNotations AX2 AX2S.

Module AXG_gf5.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AxAsan AXG_put AXG_put2 AXG_np AXG_np2 AXG_np3 AXG_np4 AXG_nf1.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_nf2.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_nf2.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_np2.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AxAsan OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_put OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_put2 OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_np OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_np2 OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_np3 OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_np4 OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_nf1 OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_nf2.AXG_nfsc OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_nf2 OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_np2.AXG_pfl.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_np3.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_nf2.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_np3.AXG_npscp OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_nf2.AXG_nfscp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_nf2.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_nf2.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_np.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_np.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_gp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_gp3.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_gf1.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp3.AXG_gp2 OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gf1.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_gp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_gp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_gp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_gp.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := AsanUbsan.M.loaded_segments.
Ltac zlh H := clear - H; lia.
Ltac memb' := first [ AxSymRun3.memb_refl | repeat first [left; reflexivity | right] ].      (* [comment removed for export] *)
Ltac lenq' := rewrite ?length_N_to_le_bytes; try change (Z.of_nat 4) with 4 in *; try change (Z.of_nat 8) with 8 in *; try change (Z.of_nat 1) with 1 in *.

Lemma b_of_1 : forall nc, 1 <= nc -> b_of nc 1 = 1.
Proof. intros nc H. apply b_of_unique; lia. Qed.
Lemma cnt_of_1 : forall nc, 1 <= nc -> cnt_of nc 1 = nc - 1.
Proof. intros nc H. unfold cnt_of. rewrite b_of_1 by exact H. ring. Qed.
Lemma div16_32c : forall k c, k * (32 * c) / 16 = k * (2 * c).
Proof. intros k c. replace (k * (32 * c)) with (k * (2 * c) * 16) by ring. apply Z.div_mul. lia. Qed.


Lemma ri_comm : forall c SB, 128 * c + (SB + 137438953472) = SB + 137438953472 + 128 * c.
Proof. intros. ring. Qed.
Lemma gdiv16 : forall k c, 1 <= c <= 30 -> k * sz_tbl c / 16 = k * (sz_tbl c / 16).
Proof.
  intros k c H. destruct (gsz_rng c H) as (_ & Hm & _). pose proof (Z.div_mod (sz_tbl c) 16 ltac:(lia)) as E. rewrite Hm, Z.add_0_r in E.
  rewrite E at 1. replace (k * (16 * (sz_tbl c / 16))) with (k * (sz_tbl c / 16) * 16) by ring. apply Z.div_mul. lia.
Qed.

Section GSC2.
Context {fx : FPState}.
Variable rom : word -> option byte.
Variables (m : word -> option byte) (R : bvmap 5 word) (CA ND c SB SP na st v1 v8 v9 v18 v19 v20 g21 g22 g23 g24 g25 g26 g27 : Z).
Hypothesis Hc : c = cls_of ND.
Hypothesis HND : 1 <= ND <= 65536.
Hypothesis HSP : 2^46 + 4096 <= SP <= 2^47 /\ SP mod 16 = 0.
Hypothesis HCA : ((4304 <= CA /\ CA + 3888 <= 65536) \/ 6537424 <= CA) /\ CA mod 16 = 0 /\ CA + 4096 <= SP - 2048.
Hypothesis HSB : 17594333495296 <= SB /\ SB mod 4096 = 0 /\ SB + 137438953472 + 4096 <= SP - 2048.
Hypothesis HSEP : CA + 2592 <= SB \/ SB + 137438953472 + 4096 <= CA.
Hypothesis Hvals : 0 <= na < 2^64 /\ 0 <= st < 2^64.
Hypothesis R2 : getr R 2 = wa (SP - 272).
Hypothesis R8 : getr R 8 = wa (SB + 137438953472 + 128 * c).
Hypothesis R10 : getr R 10 = wa 0.
Hypothesis R11 : getr R 11 = wa (SB + 4294967296 * c + 3758096384 + 4 * (262144 / (sz_tbl c))).
Hypothesis R12 : getr R 12 = wa 0.
Hypothesis R13 : getr R 13 = wa 0.
Hypothesis R19 : getr R 19 = wa (262144 / (sz_tbl c)).
Hypothesis R21 : getr R 21 = wa (sz_tbl c).
Hypothesis HSTK : stk_ok SEGS m (wa SP) 2048.
(* [comment removed for export] *)
Hypothesis Q56 : rd m (SP - 216) 8 281360.
Hypothesis Q48 : rd m (SP - 224) 8 (SB + 137438953472 + 128 * c).
Hypothesis Q40 : rd m (SP - 232) 8 929816.
Hypothesis Q32 : rd m (SP - 240) 8 (SB + 137438953472 + 128 * c + 8).
Hypothesis Q24 : rd m (SP - 248) 8 2305843009213693952.
Hypothesis Q16 : rd m (SP - 256) 8 (SB + 4294967296 * c + 3758096384).
Hypothesis Q8 : rd m (SP - 264) 8 (CA + 80 * c + 16).
Hypothesis Q0 : rd m (SP - 272) 8 (mc_tbl c / 2).
(* [comment removed for export] *)
Hypothesis G120 : rd m (SP - 88) 8 280468.
Hypothesis G112 : rd m (SP - 96) 8 (CA + 80 * c).
Hypothesis G104 : rd m (SP - 104) 8 (mc_tbl c / 2).
Hypothesis G96 : rd m (SP - 112) 8 8.
Hypothesis G88 : rd m (SP - 120) 8 CA.
Hypothesis G80 : rd m (SP - 128) 8 929816.
Hypothesis G72 : rd m (SP - 136) 8 g21.
Hypothesis G64 : rd m (SP - 144) 8 g22.
Hypothesis G56 : rd m (SP - 152) 8 g23.
Hypothesis G48 : rd m (SP - 160) 8 g24.
Hypothesis G40 : rd m (SP - 168) 8 g25.
Hypothesis G32 : rd m (SP - 176) 8 g26.
Hypothesis G24 : rd m (SP - 184) 8 g27.
Hypothesis C136 : rd m (SP - 72) 8 (CA + 80 * c).
Hypothesis C144 : rd m (SP - 64) 8 c.
Hypothesis C152 : rd m (SP - 56) 8 279220.
Hypothesis C160 : rd m (SP - 48) 8 v20.
Hypothesis C168 : rd m (SP - 40) 8 v19.
Hypothesis C176 : rd m (SP - 32) 8 v18.
Hypothesis C184 : rd m (SP - 24) 8 v9.
Hypothesis C192 : rd m (SP - 16) 8 v8.
Hypothesis C200 : rd m (SP - 8) 8 v1.
Hypothesis Hgv : (0 <= g21 < 2^64 /\ 0 <= g22 < 2^64 /\ 0 <= g23 < 2^64 /\ 0 <= g24 < 2^64 /\ 0 <= g25 < 2^64 /\ 0 <= g26 < 2^64 /\ 0 <= g27 < 2^64) /\
                 (0 <= v1 < 2^64 /\ 0 <= v8 < 2^64 /\ 0 <= v9 < 2^64 /\ 0 <= v18 < 2^64 /\ 0 <= v19 < 2^64 /\ 0 <= v20 < 2^64).
(* [comment removed for export] *)
Hypothesis Imu : rd m (SB + 137438953472 + 128 * c) 8 1152921504606846976.
Hypothesis Inf0 : rd m (SB + 137438953472 + 128 * c + 16) 8 0.
Hypothesis Iau : rd m (SB + 137438953472 + 128 * c + 32) 8 0.
Hypothesis Iau40 : rd m (SB + 137438953472 + 128 * c + 40) 8 0.
Hypothesis Imapu : rd m (SB + 137438953472 + 128 * c + 48) 8 262144.
Hypothesis Imeta : rd m (SB + 137438953472 + 128 * c + 56) 8 0.
Hypothesis Ina : rd m (SB + 137438953472 + 128 * c + 72) 8 na.
Hypothesis Iwri : wr m (SB + 137438953472 + 128 * c) 128.
Hypothesis Imc : rd m (CA + 80 * c + 4) 4 (mc_tbl c).
Hypothesis Isz : rd m (CA + 80 * c + 8) 8 (sz_tbl c).
Hypothesis Iwc : wr m CA 2592.
Hypothesis ISB : rd m 929848 8 SB.
Hypothesis IRIB : rd m 929864 8 (SB + 137438953472).
Hypothesis Ist : rd m (CA + 2576) 8 st.
Hypothesis Iwfa : wr m (SB + 4294967296 * c + 3758096384) 262144.
Hypothesis HIMG : forall i, 65536 <= i < 143360 -> m (Z_to_bv 64 i) = None.

#[using="ND na st Hc HND HSP HCA HSB HSEP Hvals R2 R8 R10 R11 R12 R13 R19 R21 HSTK Q56 Q48 Q40 Q32 Q24 Q16 Q8 Q0 G120 G112 G104 G96 G88 G80 G72 G64 G56 G48 G40 G32 G24 C136 C144 C152 C160 C168 C176 C184 C192 C200 Hgv Imu Inf0 Iau Iau40 Imapu Imeta Ina Iwri Imc Isz Iwc ISB IRIB Ist Iwfa HIMG"] Lemma gsegC2 : exists R' m', msteps SEGS (mkst R (wa 0x44d18) m rom) (mkst R' (wa 0x44224) m' rom) /\
  getr R' (Z_to_bv 5 (Z.of_nat 2)) = wa SP /\ getr R' (Z_to_bv 5 (Z.of_nat 10)) = wa (SB + 4294967296 * c) /\
  getr R' (Z_to_bv 5 (Z.of_nat 1)) = wa v1 /\ getr R' (Z_to_bv 5 (Z.of_nat 8)) = wa v8 /\ getr R' (Z_to_bv 5 (Z.of_nat 9)) = wa v9 /\
  getr R' (Z_to_bv 5 (Z.of_nat 18)) = wa v18 /\ getr R' (Z_to_bv 5 (Z.of_nat 19)) = wa v19 /\ getr R' (Z_to_bv 5 (Z.of_nat 20)) = wa v20 /\
  getr R' (Z_to_bv 5 (Z.of_nat 21)) = wa g21 /\ getr R' (Z_to_bv 5 (Z.of_nat 22)) = wa g22 /\ getr R' (Z_to_bv 5 (Z.of_nat 23)) = wa g23 /\
  getr R' (Z_to_bv 5 (Z.of_nat 24)) = wa g24 /\ getr R' (Z_to_bv 5 (Z.of_nat 25)) = wa g25 /\ getr R' (Z_to_bv 5 (Z.of_nat 26)) = wa g26 /\
  getr R' (Z_to_bv 5 (Z.of_nat 27)) = wa g27 /\
  (forall k, In k [3; 4]%nat -> getr R' (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k))) /\
  INV_G m' CA SB c (sz_tbl c) (mc_tbl c / 2) (262144 / (sz_tbl c)) 1 /\
  (forall x, 0 <= x < 2^64 -> ~ (SB + 4294967296 * c + 3758096384 <= x < SB + 4294967296 * c + 3758096384 + 262144) ->
     ~ owned_C CA SB c x -> m' (wa x) = m (wa x)) /\ mem_grows m m'.
Proof. LiaFast.lf_pins (fun (ND na st Hc HND HSP HCA HSB HSEP Hvals R2 R8 R10 R11 R12 R13 R19 R21 HSTK Q56 Q48 Q40 Q32 Q24 Q16 Q8 Q0 G120 G112 G104 G96 G88 G80 G72 G64 G56 G48 G40 G32 G24 C136 C144 C152 C160 C168 C176 C184 C192 C200 Hgv Imu Inf0 Iau Iau40 Imapu Imeta Ina Iwri Imc Isz Iwc ISB IRIB Ist Iwfa HIMG : LiaFast.U) => LiaFast.u0).
  assert (Hcr5 : 1 <= c <= 30) by (rewrite Hc; apply cls_of_rng; exact HND).
  pose proof (gmc_rng c Hcr5) as [Hmc Hmc2].
  destruct (gsz_rng c Hcr5) as (Hsz1 & Hsz2 & Hsz3).
  assert (HS16 : 16 * (sz_tbl c / 16) = sz_tbl c) by (clear - Hsz2; pose proof (Z.div_mod (sz_tbl c) 16 ltac:(lia)); lia).
  assert (HS16r : 2 <= sz_tbl c / 16 <= 4096) by (clear - Hsz1 HS16; lia).
  set (nc := mc_tbl c / 2) in *.
  assert (Hnc : 1 <= nc <= 8 /\ mc_tbl c = 2 * nc).
  { unfold nc. pose proof (Z.div_mod (mc_tbl c) 2 ltac:(lia)) as E. rewrite Hmc2, Z.add_0_r in E. lia. }
  set (RB := SB + 4294967296 * c) in *. set (RI := SB + 137438953472 + 128 * c) in *.
  replace (SB + 4294967296 * c + 3758096384) with (RB + 3758096384) in * by (unfold RB; ring).
  set (FA := RB + 3758096384) in *. set (REC := CA + 80 * c) in *.
  pose proof (gnew_rng c Hcr5) as HNEW.
  set (NEW := 262144 / (sz_tbl c)) in *.
  assert (Hncn : nc <= NEW) by (unfold nc, NEW; apply gnc_le_new; exact Hcr5).
  assert (Hncn1 : nc + 1 <= NEW) by (unfold nc, NEW; apply gnc_lt_new; exact Hcr5).
  assert (HZ : 2^46 + 4096 <= SP <= 2^47 /\ 1 <= c <= 30 /\ 1 <= ND <= 65536 /\ ((4304 <= CA /\ CA + 3888 <= 65536) \/ 6537424 <= CA) /\ CA mod 16 = 0 /\ CA + 4096 <= SP - 2048 /\
               17594333495296 <= SB /\ SB mod 4096 = 0 /\ SB + 137438953472 + 4096 <= SP - 2048 /\
               (CA + 2592 <= SB \/ SB + 137438953472 + 4096 <= CA) /\
               RB = SB + 4294967296 * c /\ RI = SB + 137438953472 + 128 * c /\ FA = RB + 3758096384 /\ REC = CA + 80 * c /\
               0 <= na < 2^64 /\ 0 <= st < 2^64 /\ 4 <= NEW <= 8192 /\ 32 <= sz_tbl c <= 65536 /\ 2 <= sz_tbl c / 16 <= 4096 /\ NEW * (sz_tbl c) <= 262144 /\ 1 <= nc <= 8 /\ nc <= NEW)
    by (clear - HSP Hcr5 HND HCA HSB HSEP Hvals HNEW Hnc Hncn Hsz1 HS16r; unfold FA, RB, RI, REC in *; lia).
  assert (HY : 2^46 + 4096 <= SP <= 2^47 /\ 1 <= c <= 30 /\ 1 <= ND <= 65536 /\ ((4304 <= CA /\ CA + 3888 <= 65536) \/ 6537424 <= CA) /\ CA + 4096 <= SP - 2048 /\
               17594333495296 <= SB /\ SB + 137438953472 + 4096 <= SP - 2048 /\
               (CA + 2592 <= SB \/ SB + 137438953472 + 4096 <= CA) /\
               RB = SB + 4294967296 * c /\ RI = SB + 137438953472 + 128 * c /\ FA = RB + 3758096384 /\ REC = CA + 80 * c /\
               0 <= na < 2^64 /\ 0 <= st < 2^64 /\ 4 <= NEW <= 8192 /\ 32 <= sz_tbl c <= 65536 /\ 2 <= sz_tbl c / 16 <= 4096 /\ 1 <= nc <= 8 /\ nc <= NEW) by (clear - HZ; lia).
  assert (HS : 2^46 + 4096 <= SP <= 2^47) by (zlh HY).
  assert (HOB : 4096 <= FA /\ FA + 262144 <= RI /\ RI + 128 <= SP - 2048 /\ 4304 <= CA /\ CA + 4096 <= SP - 2048 /\ CA + 80 <= REC /\
                REC + 80 <= CA + 2480 /\ 1 <= nc <= 8 /\ (CA + 4096 <= FA \/ RI + 128 <= CA) /\ SP <= 2^47) by (zlh HY).
  clear HSP HCA HSB HSEP Hvals.
  assert (HSPa : bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 2))) = SP - 272) by (rgz; rewrite R2, u_wa_small by (zlh HY); reflexivity).
  (* [comment removed for export] *)
  destruct (pfa_loop rom (Z.to_nat NEW) R m FA NEW 0 (sz_tbl c) ltac:((zlh HY)) R10
              ltac:(rewrite R11; reflexivity) R12 ltac:(rewrite Z2Nat.id by (zlh HY); exact R19) R21
              ltac:((zlh HY)) ltac:((zlh HY)) ltac:(rewrite Z2Nat.id by (zlh HY); lia) ltac:(lia) ltac:(rewrite Z2Nat.id by (zlh HY); (zlh HY)) ltac:((zlh HY)))
    as (Ra & m1 & Hms & A10 & A12 & KKa & RD1 & F1 & G1).
  { rewrite Z2Nat.id by (zlh HY). replace (FA + 4 * (NEW - NEW)) with (FA + 0) by ring. intros d k Hd Hk. rewrite Z.add_0_r.
    apply Iwfa; [exact Hd | clear - HY Hk; lia]. }
  rewrite Z2Nat.id in A10, A12, RD1, F1 by (zlh HY).
  assert (F1' : forall x, 0 <= x < 2^64 -> ~ (FA <= x < FA + 262144) -> m1 (wa x) = m (wa x)).
  { intros x Hx Q. apply F1; [exact Hx | clear - HY Q; lia]. }
  assert (FW1 : forall x, SP - 2048 <= x < SP -> m1 (wa x) = m (wa x)) by (intros x Hx; apply F1'; clear - HOB Hx; lia).
  assert (FR1 : forall x, RI <= x < RI + 128 -> m1 (wa x) = m (wa x)) by (intros x Hx; apply F1'; clear - HOB Hx; lia).
  (* [comment removed for export] *)
  assert (HSPb : bv_unsigned (getr Ra (Z_to_bv 5 (Z.of_nat 2))) = SP - 272) by (rewrite (KKa 2%nat ltac:(cbn; memb')); exact HSPa).
  assert (V13 : bv_unsigned (getr Ra (Z_to_bv 5 (Z.of_nat 13))) = 0) by (rewrite (KKa 13%nat ltac:(cbn; memb')); regzH R13; rewrite R13; reflexivity).
  regzH R8. regzH R19. regzH R21. regzH A10.
  assert (P2 : OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp.AXF_gpc2z.gpc2_pre Ra m1 RI (sz_tbl c / 16) NEW FA (REC + 16) nc).
  { constructor; [regzG; rewrite (KKa 8%nat ltac:(cbn; memb')); exact R8 | regzG; exact A10
                 | regzG; rewrite (KKa 19%nat ltac:(cbn; memb')); exact R19 | regzG; rewrite (KKa 21%nat ltac:(cbn; memb')); rewrite HS16; exact R21
                 | (replace (getr Ra 2) with (wa (SP - 272)) by (regzG; rewrite (KKa 2%nat ltac:(cbn; memb')); regzH R2; rewrite R2; reflexivity);
                    apply (stk_ok_move m1 SP (SP - 272) 1024); [(zlh HY) | (zlh HY) | exact (stk_ok_grows m m1 (wa SP) 2048 G1 HSTK) | (zlh HY) | (zlh HY) | (zlh HY)])
                 | .. ].
    all: try (zlh HY).
    all: try (zlh HZ).
    all: try (rewrite HSPb; (zlh HY)).
    all: try (rewrite HSPb; replace (SP - 272 + 56) with (SP - 216) by ring; replace (SP - 272 + 48) with (SP - 224) by ring;
              replace (SP - 272 + 40) with (SP - 232) by ring; replace (SP - 272 + 32) with (SP - 240) by ring; replace (SP - 272 + 24) with (SP - 248) by ring;
              replace (SP - 272 + 16) with (SP - 256) by ring; replace (SP - 272 + 8) with (SP - 264) by ring; replace (SP - 272 + 0) with (SP - 272) by ring).
    all: first [ (apply (rd_frame m m1); [clear - HS; lia | lenq'; clear - HS; lia | intros x Hx; lenq'; apply FW1; clear - HS Hx; lia | first [assumption | (replace (RI + 8) with (SB + 137438953472 + 128 * c + 8) by (unfold RI; ring); assumption)]])
               | (apply (rd_frame m m1); [clear - HOB; lia | lenq'; clear - HOB; lia | intros x Hx; lenq'; apply FR1; clear - Hx; lia | assumption])
               | (intros d k Hd Hk; apply (store_ok_mono SEGS k m m1 _ G1);
                  first [ (replace (RI + 16 + d) with (RI + (16 + d)) by ring; apply Iwri; clear - Hd Hk; lia)
                        | (replace (RI + 32 + d) with (RI + (32 + d)) by ring; apply Iwri; clear - Hd Hk; lia)
                        | (replace (RI + 68 + d) with (RI + (68 + d)) by ring; apply Iwri; clear - Hd Hk; lia) ]) ]. }
  destruct (OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp.AXF_gpc2z.gpc2_ppc2 Ra m1 rom RI (sz_tbl c / 16) NEW FA (REC + 16) nc P2
              (sc_gpc2 Ra m1 (SP - 272) HSPb RI (sz_tbl c / 16) NEW FA (REC + 16) nc V13 ltac:(rewrite HS16; (zlh HZ))))
    as (Rb & Hms2 & B1 & B2 & B8 & B9 & B10 & B11 & B13 & B14 & B15 & B18 & B19 & B20 & B21 & B22 & KKb).
  clear P2 B1 B9 B10 B15 B18 B21 B22.
  pose proof (msteps_trans SEGS _ _ _ Hms Hms2) as Hms'. clear Hms Hms2. rename Hms' into Hms.
  set (m2 := OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp.AXF_gpc2z.gpc2_mem_ppc2 m1 Ra RI (sz_tbl c / 16) NEW FA (REC + 16) nc) in *.
  assert (EM2 : m2 = wbytes (wbytes (wbytes (wbytes m1 (wa (RI + 16)) (word_to_le_bytes 8 (wa NEW))) (wa (RI + 32)) (word_to_le_bytes 8 (wa (NEW * (sz_tbl c)))))
                        (wa (RI + 68)) (word_to_le_bytes 1 (wa 0))) (wa (RI + 16)) (word_to_le_bytes 8 (wa (NEW + -1 * nc)))).
  { unfold m2, OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp.AXF_gpc2z.gpc2_mem_ppc2. rewrite V13, Z.add_0_l, ?HS16. reflexivity. }
  clearbody m2.
  assert (G2 : mem_grows m m2) by (apply (mem_grows_trans _ m1 _ G1); rewrite EM2; repeat apply grows_wb; apply mem_grows_refl).
  assert (F2 : forall x, 0 <= x < 2^64 -> ~ (FA <= x < FA + 262144) -> ~ (RI + 16 <= x < RI + 24) -> ~ (RI + 32 <= x < RI + 40) -> ~ (RI + 68 <= x < RI + 69) ->
                 m2 (wa x) = m (wa x)).
  { intros x Hx Q1 Q2 Q3 Q4. rewrite EM2. repeat (rewrite wb_other by first [exact Hx | (lenq'; clear - HY; lia) | (lenq'; clear - HY Q2 Q3 Q4; lia)]).
    apply F1'; assumption. }
  assert (Rnf2 : rd m2 (RI + 16) 8 (NEW + -1 * nc)) by (rewrite EM2; apply wb_rd_hit; lenq'; (zlh HY)).
  (* [comment removed for export] *)
  regzH B2. regzH B8. regzH B11. regzH B13. regzH B14. regzH B19. regzH B20.
  assert (HSPc : bv_unsigned (getr Rb (Z_to_bv 5 (Z.of_nat 2))) = SP - 208) by (rewrite B2, HSPb, u_wa_small by (zlh HY); ring).
  assert (L11 : getr Rb 11 = wa (REC + 16 + 4 * Z.of_nat (Z.to_nat nc))) by (regzG; rewrite B11, Z2Nat.id by (zlh HY); reflexivity).
  assert (L13 : getr Rb 13 = wa (REC + 16)) by (regzG; exact B13).
  assert (L20 : getr Rb 20 = wa (FA + 4 * (NEW - nc))) by (regzG; rewrite B20; f_equal; ring).
  assert (LW : forall i, 0 <= i < Z.of_nat (Z.to_nat nc) -> 0 <= (nc - 1 - i) * (sz_tbl c / 16) < 2^31 /\
                 rd m2 (FA + 4 * (NEW - nc) + 4 * i) 4 ((nc - 1 - i) * (sz_tbl c / 16))).
  { intros i Hi. rewrite Z2Nat.id in Hi by (zlh HY).
      split; [assert (Hq1 : 0 <= nc - 1 - i <= 7) by (clear - HOB Hi; lia); assert (Hq2 : 2 <= sz_tbl c / 16 <= 4096) by (zlh HY); clear - Hq1 Hq2; nia|].
    pose proof (RD1 (nc - 1 - i) ltac:(clear - HY Hi; lia)) as Rf. rewrite Z.add_0_l, (gdiv16 _ c Hcr5) in Rf.
    replace (FA + 4 * (NEW - 1 - (nc - 1 - i))) with (FA + 4 * (NEW - nc) + 4 * i) in Rf by ring.
    apply (rd_frame m1 m2); [clear - HY Hi; lia | lenq'; clear - HY Hi; lia | | exact Rf].
    intros x Hx. lenq'. rewrite EM2. repeat (rewrite wb_other by first [(clear - HY Hi Hx; lia) | (lenq'; clear - HY; lia) | (lenq'; clear - HY Hi Hx; lia)]). reflexivity. }
  assert (LWR : wr m2 (REC + 16) (4 * Z.of_nat (Z.to_nat nc))).
  { intros d k Hd Hk. rewrite Z2Nat.id in Hk by (clear - HY; lia). apply (store_ok_mono SEGS k m m2 _ G2).
    replace (REC + 16 + d) with (CA + (80 * c + 16 + d)) by (unfold REC; ring). apply Iwc; clear - HY Hd Hk; lia. }
  destruct (ngl_loop rom (Z.to_nat nc) Rb m2 (FA + 4 * (NEW - nc)) (REC + 16) (fun i => (nc - 1 - i) * (sz_tbl c / 16)) ltac:((zlh HY)) L11 L13 L20
              ltac:((zlh HY)) ltac:(rewrite Z2Nat.id by (zlh HY); (zlh HY)) ltac:((zlh HY)) ltac:(rewrite Z2Nat.id by (zlh HY); (zlh HY)) ltac:(rewrite Z2Nat.id by (zlh HY); (zlh HY)) LW LWR)
    as (Rc & m3 & Hms3 & E13 & E20 & KKc & RD3 & F3 & G3).
  rewrite Z2Nat.id in RD3, F3 by (zlh HY). clear LW LWR L11 L13 L20 E13 E20.
  pose proof (msteps_trans SEGS _ _ _ Hms Hms3) as Hms'. clear Hms Hms3. rename Hms' into Hms.
  assert (G13 : mem_grows m m3) by exact (mem_grows_trans _ _ _ G2 G3).
  assert (F13 : forall x, 0 <= x < 2^64 -> ~ (FA <= x < FA + 262144) -> ~ (RI + 16 <= x < RI + 24) -> ~ (RI + 32 <= x < RI + 40) -> ~ (RI + 68 <= x < RI + 69) ->
                  ~ (REC + 16 <= x < REC + 16 + 4 * nc) -> m3 (wa x) = m (wa x)).
  { intros x Hx Q1 Q2 Q3 Q4 Q5. rewrite F3 by assumption. apply F2; assumption. }
  assert (FW3 : forall x, SP - 2048 <= x < SP -> m3 (wa x) = m (wa x)) by (intros x Hx; apply F13; clear - HOB Hx; lia).
  assert (HS2 : 8192 <= SP - 2048 /\ SP <= 2^47) by (zlh HS).
  (* [comment removed for export] *)
  assert (HSPd : bv_unsigned (getr Rc (Z_to_bv 5 (Z.of_nat 2))) = SP - 208) by (rewrite (KKc 2%nat ltac:(cbn; memb')); exact HSPc).
  assert (P4 : OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp.AXF_gngtz.gngt_pre Rc m3 CA c nc SB (SB + 137438953472) na 0 (sz_tbl c) st 0 0 0 0 g21 g22 g23 g24 g25 g26 g27 v9 v18 v19 v20 v8 v1).
  { constructor.
    all: try (clear - Hgv; lia).
    all: try (zlh HY).
    all: try (rewrite HSPd; (zlh HS)).
    all: try (zlh HZ).
    - rewrite ?(ri_comm c SB). regzG. rewrite (KKc 8%nat ltac:(cbn; memb')), B8. reflexivity.
    - rewrite ?(ri_comm c SB). regzG. rewrite (KKc 14%nat ltac:(cbn; memb')). exact B14.
    - rewrite ?(ri_comm c SB). regzG. rewrite (KKc 19%nat ltac:(cbn; memb')). exact B19.
    - rewrite ?(ri_comm c SB). replace (getr Rc 2) with (wa (SP - 208)) by (regzG; rewrite (KKc 2%nat ltac:(cbn; memb')), B2, HSPb; f_equal; ring).
      apply (stk_ok_move m3 SP (SP - 208) 1024); [(zlh HY) | (zlh HY) | exact (stk_ok_grows m m3 (wa SP) 2048 G13 HSTK) | (zlh HY) | (zlh HY) | (zlh HY)].
    - rewrite ?(ri_comm c SB). apply (rd_frame m m3); [(zlh HY) | lenq'; (zlh HY) | intros x Hx; lenq'; apply F13; clear - HY Hx; lia | exact Ina].
    - rewrite ?(ri_comm c SB). intros d k Hd Hk. apply (store_ok_mono SEGS k m m3 _ G13). replace (SB + 137438953472 + 128 * c + 72 + d) with (RI + (72 + d)) by (unfold RI; ring). apply Iwri; clear - HY Hd Hk; lia.
    - rewrite ?(ri_comm c SB). rewrite Z.add_0_r. apply (rd_frame m m3); [(zlh HY) | lenq'; (zlh HY) | intros x Hx; lenq'; apply F13; clear - HY Hx; lia | exact Imu].
    - rewrite ?(ri_comm c SB). intros d k Hd Hk. rewrite Z.add_0_r. apply (store_ok_mono SEGS k m m3 _ G13). apply Iwri; clear - HY Hd Hk; lia.
    - rewrite ?(ri_comm c SB). rewrite HSPd. replace (SP - 208 + 120) with (SP - 88) by ring. apply (rd_frame m m3); [clear - HS2; lia | lenq'; clear - HS2; lia | intros x Hx; lenq'; apply FW3; clear - HS2 Hx; lia | exact G120].
    - rewrite ?(ri_comm c SB). rewrite HSPd. replace (SP - 208 + 112) with (SP - 96) by ring. apply (rd_frame m m3); [clear - HS2; lia | lenq'; clear - HS2; lia | intros x Hx; lenq'; apply FW3; clear - HS2 Hx; lia | exact G112].
    - rewrite ?(ri_comm c SB). rewrite HSPd. replace (SP - 208 + 104) with (SP - 104) by ring. apply (rd_frame m m3); [clear - HS2; lia | lenq'; clear - HS2; lia | intros x Hx; lenq'; apply FW3; clear - HS2 Hx; lia | exact G104].
    - rewrite ?(ri_comm c SB). rewrite HSPd. replace (SP - 208 + 96) with (SP - 112) by ring. apply (rd_frame m m3); [clear - HS2; lia | lenq'; clear - HS2; lia | intros x Hx; lenq'; apply FW3; clear - HS2 Hx; lia | exact G96].
    - rewrite ?(ri_comm c SB). rewrite HSPd. replace (SP - 208 + 88) with (SP - 120) by ring. apply (rd_frame m m3); [clear - HS2; lia | lenq'; clear - HS2; lia | intros x Hx; lenq'; apply FW3; clear - HS2 Hx; lia | exact G88].
    - rewrite ?(ri_comm c SB). rewrite HSPd. replace (SP - 208 + 80) with (SP - 128) by ring. apply (rd_frame m m3); [clear - HS2; lia | lenq'; clear - HS2; lia | intros x Hx; lenq'; apply FW3; clear - HS2 Hx; lia | exact G80].
    - rewrite ?(ri_comm c SB). rewrite HSPd. replace (SP - 208 + 72) with (SP - 136) by ring. apply (rd_frame m m3); [clear - HS2; lia | lenq'; clear - HS2; lia | intros x Hx; lenq'; apply FW3; clear - HS2 Hx; lia | exact G72].
    - rewrite ?(ri_comm c SB). rewrite HSPd. replace (SP - 208 + 64) with (SP - 144) by ring. apply (rd_frame m m3); [clear - HS2; lia | lenq'; clear - HS2; lia | intros x Hx; lenq'; apply FW3; clear - HS2 Hx; lia | exact G64].
    - rewrite ?(ri_comm c SB). rewrite HSPd. replace (SP - 208 + 56) with (SP - 152) by ring. apply (rd_frame m m3); [clear - HS2; lia | lenq'; clear - HS2; lia | intros x Hx; lenq'; apply FW3; clear - HS2 Hx; lia | exact G56].
    - rewrite ?(ri_comm c SB). rewrite HSPd. replace (SP - 208 + 48) with (SP - 160) by ring. apply (rd_frame m m3); [clear - HS2; lia | lenq'; clear - HS2; lia | intros x Hx; lenq'; apply FW3; clear - HS2 Hx; lia | exact G48].
    - rewrite ?(ri_comm c SB). rewrite HSPd. replace (SP - 208 + 40) with (SP - 168) by ring. apply (rd_frame m m3); [clear - HS2; lia | lenq'; clear - HS2; lia | intros x Hx; lenq'; apply FW3; clear - HS2 Hx; lia | exact G40].
    - rewrite ?(ri_comm c SB). rewrite HSPd. replace (SP - 208 + 32) with (SP - 176) by ring. apply (rd_frame m m3); [clear - HS2; lia | lenq'; clear - HS2; lia | intros x Hx; lenq'; apply FW3; clear - HS2 Hx; lia | exact G32].
    - rewrite ?(ri_comm c SB). rewrite HSPd. replace (SP - 208 + 24) with (SP - 184) by ring. apply (rd_frame m m3); [clear - HS2; lia | lenq'; clear - HS2; lia | intros x Hx; lenq'; apply FW3; clear - HS2 Hx; lia | exact G24].
    - rewrite ?(ri_comm c SB). rewrite HSPd. replace (SP - 208 + 136) with (SP - 72) by ring. apply (rd_frame m m3); [clear - HS2; lia | lenq'; clear - HS2; lia | intros x Hx; lenq'; apply FW3; clear - HS2 Hx; lia | exact C136].
    - rewrite ?(ri_comm c SB). rewrite HSPd. replace (SP - 208 + 144) with (SP - 64) by ring. apply (rd_frame m m3); [clear - HS2; lia | lenq'; clear - HS2; lia | intros x Hx; lenq'; apply FW3; clear - HS2 Hx; lia | exact C144].
    - rewrite ?(ri_comm c SB). rewrite HSPd. replace (SP - 208 + 152) with (SP - 56) by ring. apply (rd_frame m m3); [clear - HS2; lia | lenq'; clear - HS2; lia | intros x Hx; lenq'; apply FW3; clear - HS2 Hx; lia | exact C152].
    - rewrite ?(ri_comm c SB). rewrite HSPd. replace (SP - 208 + 160) with (SP - 48) by ring. apply (rd_frame m m3); [clear - HS2; lia | lenq'; clear - HS2; lia | intros x Hx; lenq'; apply FW3; clear - HS2 Hx; lia | exact C160].
    - rewrite ?(ri_comm c SB). rewrite HSPd. replace (SP - 208 + 168) with (SP - 40) by ring. apply (rd_frame m m3); [clear - HS2; lia | lenq'; clear - HS2; lia | intros x Hx; lenq'; apply FW3; clear - HS2 Hx; lia | exact C168].
    - rewrite ?(ri_comm c SB). rewrite HSPd. replace (SP - 208 + 176) with (SP - 32) by ring. apply (rd_frame m m3); [clear - HS2; lia | lenq'; clear - HS2; lia | intros x Hx; lenq'; apply FW3; clear - HS2 Hx; lia | exact C176].
    - rewrite ?(ri_comm c SB). rewrite HSPd. replace (SP - 208 + 184) with (SP - 24) by ring. apply (rd_frame m m3); [clear - HS2; lia | lenq'; clear - HS2; lia | intros x Hx; lenq'; apply FW3; clear - HS2 Hx; lia | exact C184].
    - rewrite ?(ri_comm c SB). rewrite HSPd. replace (SP - 208 + 192) with (SP - 16) by ring. apply (rd_frame m m3); [clear - HS2; lia | lenq'; clear - HS2; lia | intros x Hx; lenq'; apply FW3; clear - HS2 Hx; lia | exact C192].
    - rewrite ?(ri_comm c SB). rewrite HSPd. replace (SP - 208 + 200) with (SP - 8) by ring. apply (rd_frame m m3); [clear - HS2; lia | lenq'; clear - HS2; lia | intros x Hx; lenq'; apply FW3; clear - HS2 Hx; lia | exact C200].
    - rewrite ?(ri_comm c SB). intros d k Hd Hk. rewrite Z.add_0_r. apply (store_ok_mono SEGS k m m3 _ G13). replace (CA + 80 * c + d) with (CA + (80 * c + d)) by ring. apply Iwc; clear - HY Hd Hk; lia.
    - rewrite ?(ri_comm c SB). apply (rd_frame m m3); [(zlh HY) | lenq'; (zlh HY) | intros x Hx; lenq'; apply F13; clear - HY Hx; lia | exact Isz].
    - rewrite ?(ri_comm c SB). rewrite chp_off by (zlh HY). pose proof (RD3 (nc - 1) ltac:((zlh HY))) as R7.
      replace (REC + 16 + 4 * (nc - 1)) with (CA + (80 * c + 4 * (nc - 1)) + 16) in R7 by (unfold REC; ring).
      replace ((nc - 1 - (nc - 1)) * (sz_tbl c / 16)) with 0 in R7 by ring. exact R7.
    - rewrite ?(ri_comm c SB). apply (rd_frame m m3); [(zlh HY) | lenq'; (zlh HY) | intros x Hx; lenq'; apply F13; clear - HY Hx; lia | exact ISB].
    - rewrite ?(ri_comm c SB). apply (rd_frame m m3); [(zlh HY) | lenq'; (zlh HY) | intros x Hx; lenq'; apply F13; clear - HY Hx; lia | exact Ist].
    - rewrite ?(ri_comm c SB). intros d k Hd Hk. apply (store_ok_mono SEGS k m m3 _ G13). replace (CA + 2576 + d) with (CA + (2576 + d)) by ring. apply Iwc; clear - HY Hd Hk; lia.
    - rewrite ?(ri_comm c SB). intros i Hi. change (Z_to_bv 64 i) with (wa i). rewrite F13 by (clear - HY Hi; lia). apply HIMG. exact Hi. }
  destruct (OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp.AXF_gngtz.gngt_pngt Rc m3 rom CA c nc SB (SB + 137438953472) na 0 (sz_tbl c) st 0 0 0 0 g21 g22 g23 g24 g25 g26 g27 v9 v18 v19 v20 v8 v1 P4
              (sc_gngt Rc m3 (SP - 208) HSPd CA c nc SB (SB + 137438953472) na 0 (sz_tbl c) st 0 0 0 0 g21 g22 g23 g24 g25 g26 g27 v9 v18 v19 v20 v8 v1 ltac:((zlh HY))))
    as (Rd & Hms5 & T1 & T2 & T5 & T6 & T7 & T8 & T9 & T10 & T11 & T12 & T13 & T14 & T15 & T16 & T17 & T18 & T19 & T20 & T21 & T22 & T23 & T24 & T25 & T26 & T27 & T28 & KKd).
  clear P4 T5 T6 T7 T11 T12 T13 T14 T15 T16 T17 T28.
  pose proof (msteps_trans SEGS _ _ _ Hms Hms5) as Hms'. clear Hms Hms5. rename Hms' into Hms.
  set (m5 := m5c m3 RI REC CA nc na (sz_tbl c) st).
  assert (EM5 : OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp.AXF_gngtz.gngt_mem_pngt m3 Rc CA c nc SB (SB + 137438953472) na 0 (sz_tbl c) st 0 0 0 0 g21 g22 g23 g24 g25 g26 g27 v9 v18 v19 v20 v8 v1 = m5).
  { unfold m5, m5c, OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp.AXF_gngtz.gngt_mem_pngt, RI, REC. rewrite ?(ri_comm c SB). rewrite ext_Z_lo32_small by (zlh HY). rewrite ?Z.add_0_r, ?addneg. reflexivity. }
  rewrite EM5 in Hms. clear EM5.
  assert (G5 : mem_grows m m5) by (exact (mem_grows_trans _ _ _ G13 (m5c_grows _ _ _ _ _ _ _ _))).
  assert (FX5 : forall x, 0 <= x < 2^64 -> ~ (FA <= x < FA + 262144) -> ~ (RI <= x < RI + 128) -> ~ (REC <= x < REC + 80) -> ~ (CA + 2576 <= x < CA + 2584) ->
                  m5 (wa x) = m (wa x)).
  { intros x Hx Q1 Q2 Q3 Q4. unfold m5.
    rewrite m5c_frame; [| clear - HOB; lia | clear - HOB; lia | clear - HOB; lia | clear - HOB; lia | clear - HOB; lia | clear - HOB; lia | exact Hx
                        | clear - Q2; lia | clear - Q2; lia | clear - Q3; lia | exact Q4].
    apply F13; [exact Hx | exact Q1 | clear - Q2; lia | clear - Q2; lia | clear - Q2; lia | clear - HOB Q3; lia]. }
  destruct (m5c_rd m3 RI REC CA nc na (sz_tbl c) st ltac:((zlh HY)) ltac:((zlh HY)) ltac:((zlh HY)) ltac:((zlh HY)) ltac:((zlh HY)) ltac:((zlh HY)) ltac:((zlh HY)))
    as (Rc5 & Rmu5 & Rna5 & Rst5).
  fold m5 in Rc5, Rmu5, Rna5, Rst5.
  exists Rd, m5. split; [exact Hms|].
  regzH T2. regzH T8. regzH T9. regzH T10. regzH T18. regzH T19. regzH T20. regzH T21. regzH T22. regzH T23. regzH T24. regzH T25. regzH T26. regzH T27. regzH T1.
  split; [rewrite T2, HSPd; f_equal; ring|].
  split; [rewrite T10, ext_Z_u32 by lia; f_equal; unfold RB; ring|].
  split; [exact T1|]. split; [exact T8|]. split; [exact T9|]. split; [exact T18|]. split; [exact T19|]. split; [exact T20|].
  split; [exact T21|]. split; [exact T22|]. split; [exact T23|]. split; [exact T24|]. split; [exact T25|]. split; [exact T26|]. split; [exact T27|].
  split.
  { intros k Hk. cbn [In] in Hk. destruct Hk as [<-|[<-|[]]].
    - rewrite (KKd 3%nat ltac:(cbn; memb')), (KKc 3%nat ltac:(cbn; memb')), (KKb 3%nat ltac:(cbn; memb')), (KKa 3%nat ltac:(cbn; memb')). reflexivity.
    - rewrite (KKd 4%nat ltac:(cbn; memb')), (KKc 4%nat ltac:(cbn; memb')), (KKb 4%nat ltac:(cbn; memb')), (KKa 4%nat ltac:(cbn; memb')). reflexivity. }
  assert (Hsz16 : sz_tbl c / 16 = sz_tbl c / 16) by reflexivity.
  split.
  { constructor.
    - clear - HY HZ Hsz2 Hcr5 Hncn1. lia.
    - apply (rd_frame m m5); [lia | lenq'; lia | intros x Hx; lenq'; apply FX5; clear - HY Hx; lia | exact ISB].
    - apply (rd_frame m m5); [lia | lenq'; lia | intros x Hx; lenq'; apply FX5; clear - HY Hx; lia | exact IRIB].
    - rewrite cnt_of_1 by (zlh HY). exact Rc5.
    - replace (2 * nc) with (mc_tbl c) by (clear - Hnc; lia).
      apply (rd_frame m3 m5); [(zlh HY) | lenq'; (zlh HY) | intros x Hx; lenq'; unfold m5; apply m5c_frame; clear - HY Hx; lia |].
      apply (rd_frame m m3); [(zlh HY) | lenq'; (zlh HY) | intros x Hx; lenq'; apply F13; clear - HY Hx; lia | exact Imc].
    - apply (rd_frame m3 m5); [(zlh HY) | lenq'; (zlh HY) | intros x Hx; lenq'; unfold m5; apply m5c_frame; clear - HY Hx; lia |].
      apply (rd_frame m m3); [(zlh HY) | lenq'; (zlh HY) | intros x Hx; lenq'; apply F13; clear - HY Hx; lia | exact Isz].
    - intros i Hi. rewrite cnt_of_1 in Hi |- * by (zlh HY). replace (1 + (nc - 1) - 1 - i) with (nc - 1 - i) by ring.
      pose proof (RD3 i ltac:(clear - HY Hi; lia)) as Ri. cbv beta in Ri.
      apply (rd_frame m3 m5); [clear - HY Hi; lia | lenq'; clear - HY Hi; lia | intros x Hx; lenq'; unfold m5; apply m5c_frame; clear - HY Hi Hx; lia | exact Ri].
    - exact Rmu5.
    - rewrite b_of_1 by (zlh HY). replace (NEW - nc * 1) with (NEW + -1 * nc) by ring.
      apply (rd_frame m3 m5); [(zlh HY) | lenq'; (zlh HY) | intros x Hx; lenq'; unfold m5; apply m5c_frame; clear - HY Hx; lia |].
      apply (rd_frame m2 m3); [(zlh HY) | lenq'; (zlh HY) | intros x Hx; lenq'; apply F3; clear - HY Hx; lia | exact Rnf2].
    - exists ((nc + na) mod 2^64). split; [apply Z.mod_pos_bound; lia|]. unfold rd. rewrite (wa_eqm ((nc + na) mod 2^64) (nc + na)) by (apply Z.mod_mod; lia). exact Rna5.
    - intros k Hk. rewrite b_of_1 in Hk by (zlh HY).
      pose proof (RD1 (NEW - 1 - k) ltac:(clear - HY Hk; lia)) as Rf. rewrite Z.add_0_l, (gdiv16 _ c Hcr5) in Rf.
      replace (FA + 4 * (NEW - 1 - (NEW - 1 - k))) with (SB + c * 4294967296 + 3758096384 + 4 * k) in Rf by (unfold FA, RB; ring).
      apply (rd_frame m3 m5); [clear - HY Hk; lia | lenq'; clear - HY Hk; lia | intros x Hx; lenq'; unfold m5; apply m5c_frame; clear - HY Hk Hx; lia |].
      apply (rd_frame m2 m3); [clear - HY Hk; lia | lenq'; clear - HY Hk; lia | intros x Hx; lenq'; apply F3; clear - HY Hk Hx; lia |].
      apply (rd_frame m1 m2); [clear - HY Hk; lia | lenq'; clear - HY Hk; lia | | exact Rf].
      intros x Hx. lenq'. rewrite EM2. repeat (rewrite wb_other by first [(clear - HY Hk Hx; lia) | (lenq'; clear - HY; lia) | (lenq'; clear - HY Hk Hx; lia)]). reflexivity.
    - exists ((sz_tbl c + st) mod 2^64). split; [apply Z.mod_pos_bound; lia|]. unfold rd. rewrite (wa_eqm ((sz_tbl c + st) mod 2^64) (sz_tbl c + st)) by (apply Z.mod_mod; lia). exact Rst5.
    - intros d k Hd Hk. apply (store_ok_mono SEGS k m m5 _ G5). replace (CA + 80 * c + d) with (CA + (80 * c + d)) by ring. apply Iwc; clear - HY Hd Hk; lia.
    - intros d k Hd Hk. apply (store_ok_mono SEGS k m m5 _ G5). apply Iwri; assumption.
    - intros d k Hd Hk. apply (store_ok_mono SEGS k m m5 _ G5). replace (CA + 2560 + d) with (CA + (2560 + d)) by ring. apply Iwc; clear - HY Hd Hk; lia. }
  split; [|exact G5].
  intros x Hx Q1 Q2. unfold owned_C in Q2. fold RI REC in Q2. apply FX5; [exact Hx | exact Q1 | | |]; clear - Q2; lia.
Qed.
End GSC2.
(* [comment removed for export] *)
End AXG_gf5.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Abbreviation SEGS := AsanUbsan.M.loaded_segments.
(* [comment removed for export] *)
Definition gmAd (m : word -> option byte) (SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 g21 g22 g23 g24 g25 g26 g27 : Z) : word -> option byte :=
  wchainS (wbytes (wchainS (wchainS m SP (L1a c CA v1 v8 v9 v18 v19 v20)) SP (L2a c CA n g21 g22 g23 g24 g25 g26 g27))
                  (wa RI) (word_to_le_bytes 8 (wa 1152921504606846976))) SP (gL3a c CA n RI RB FA).

Section GSB.
Context {fx : FPState}.
Variable rom : word -> option byte.
Variables (m : word -> option byte) (regs : bvmap 5 word) (CA ND c SB SP sz0 st : Z).
Hypothesis Hc : c = cls_of ND.
Hypothesis HND : 1 <= ND <= 65536.
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

Lemma gsegA' : exists R mA, msteps SEGS (mkst regs (wa 0x44004) m rom) (mkst R (wa 0x73c38) mA rom) /\
  getr R (Z_to_bv 5 (Z.of_nat 1)) = wa 481784 /\ getr R (Z_to_bv 5 (Z.of_nat 2)) = wa (SP - 400) /\
  getr R (Z_to_bv 5 (Z.of_nat 8)) = wa 262144 /\ getr R (Z_to_bv 5 (Z.of_nat 10)) = wa (SB + 4294967296 * c) /\
  getr R (Z_to_bv 5 (Z.of_nat 11)) = wa 262144 /\ getr R (Z_to_bv 5 (Z.of_nat 12)) = wa 3 /\ getr R (Z_to_bv 5 (Z.of_nat 13)) = wa 50 /\
  getr R (Z_to_bv 5 (Z.of_nat 14)) = wa 18446744073709551615 /\ getr R (Z_to_bv 5 (Z.of_nat 15)) = wa 0 /\
  getr R (Z_to_bv 5 (Z.of_nat 17)) = wa 222 /\ getr R (Z_to_bv 5 (Z.of_nat 21)) = wa (sz_tbl c) /\ getr R (Z_to_bv 5 (Z.of_nat 22)) = wa 929816 /\
  (forall k, In k [3; 4]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))) /\
  mA = gmAd m SP CA c (mc_tbl c / 2) (SB + 137438953472 + 128 * c) (SB + 4294967296 * c) (SB + 4294967296 * c + 3758096384)
         (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 1)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 8)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 9))))
         (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 19)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 20))))
         (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 21)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 22)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 23))))
         (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 24)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 25)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 26))))
         (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 27)))).
Proof using All.
  assert (Hcr5 : 1 <= c <= 30) by (rewrite Hc; apply cls_of_rng; exact HND).
  assert (HZ : ((4304 <= CA /\ CA + 3888 <= 65536) \/ 6537424 <= CA) /\ CA mod 16 = 0 /\ CA + 4096 <= SP - 2048 /\ 17594333495296 <= SB /\ SB mod 4096 = 0 /\
               SB + 137438953472 + 4096 <= SP - 2048 /\ 2^46 + 4096 <= SP <= 2^47 /\ 1 <= c <= 30 /\ 1 <= ND <= 65536 /\
               (CA + 2592 <= SB \/ SB + 137438953472 + 4096 <= CA) /\ 0 <= sz0 < 2^64 /\ 0 <= st < 2^64) by (clear - HCA HSB HSP Hcr5 HND HSEP Hszst; lia).
  clear HCA HSB HSP Hcr5 HSEP Hszst.
  assert (HSPa : bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) = SP) by (rgz; rewrite H2, u_wa_small by (zlh HZ); reflexivity).
  (* [comment removed for export] *)
  destruct (gp_head rom m regs CA ND SP H2 ltac:(zlh HZ) HSTK H10 H11 H12 H13 ltac:(zlh HZ) ltac:(zlh HZ))
    as (R0 & Hms0 & A2 & A8 & _ & A10 & A11 & A13 & KK0).
  rewrite <- Hc in A8.
  set (m1 := wchainS m SP (LHD (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 1)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 8)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 9)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 19)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 20)))))) in *.
  assert (EM1 : m1 = wchainS m SP [(-48, 8%nat, bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 20)))); (-40, 8%nat, bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 19))));
                                     (-32, 8%nat, bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18)))); (-24, 8%nat, bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 9))));
                                     (-16, 8%nat, bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 8)))); (-8, 8%nat, bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 1))))]) by reflexivity.
  clearbody m1.
  assert (G1 : mem_grows m m1) by (rewrite EM1; apply wchainS_grows).
  assert (F1 : forall x, 0 <= x < 2^64 -> ~ (SP - 48 <= x < SP) -> m1 (wa x) = m (wa x)).
  { intros x Hx H. rewrite EM1. apply (wchainS_frame_in _ m SP (-48) 0); [(zlh HZ) | (zlh HZ) | vm_compute; reflexivity | vm_compute; reflexivity | exact Hx | rewrite Z.add_0_r; exact H]. }
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
  set (n := mc_tbl c / 2).
  destruct (gmc_rng c ltac:((zlh HZ))) as [Hmc1 Hmc2].
  assert (Hn : 1 <= n <= 8 /\ mc_tbl c = 2 * n) by (unfold n; pose proof (Z.div_mod (mc_tbl c) 2 ltac:(lia)); lia).
  assert (P1 : OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp.AXF_gnprz.gnpr_pre R1 m1 CA c (mc_tbl c)).
  { constructor; [exact B10 | exact B11 | exact B12 | exact B13 | | first [(zlh HZ) | (zlh Hmc1)] | first [(zlh HZ) | (zlh Hmc1)] | first [(zlh HZ) | (zlh Hmc1)]
                 | first [(zlh HZ) | (zlh Hmc1)] | first [rewrite HSP1; (zlh HZ) | (zlh HZ) | (zlh Hmc1)] | ].
    - replace (getr R1 2) with (wa (SP - 48)) by (rgz; rewrite B2; reflexivity).
      apply (stk_ok_move m1 SP (SP - 48) 1024); [(zlh HZ) | (zlh HZ) | exact (stk_ok_grows m m1 (wa SP) 2048 G1 HSTK) | (zlh HZ) | (zlh HZ) | (zlh HZ)].
    - apply (rd_frame m m1); [(zlh HZ) | lenq; (zlh HZ) | intros x Hx; znq; apply F1; clear - HZ Hx; lia | exact Imc]. }
  destruct (OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp.AXF_gnprz.gnpr_pnpr R1 m1 rom CA c (mc_tbl c) P1 (sc_gnpr R1 m1 (SP - 48) HSP1 CA c (mc_tbl c) ltac:(clear - HZ Hmc1; lia)))
    as (R2 & Hms2 & C1 & C2 & C8 & C9 & C10 & C11 & C12 & C13 & C14 & KK2).
  clear P1 C1.
  pose proof (msteps_trans SEGS _ _ _ Hms1 Hms2) as Hms. clear Hms1 Hms2.
  regzH C2. regzH C8. regzH C9.
  assert (Vn : bv_unsigned (edenot (Ez R1 (OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp.AXF_gnprz.VALS_gnpr CA c (mc_tbl c))) (EAluw ALU_SRL (EExt true 0 4 (EVar 34)) (ELit 1))) = n).
  { rewrite (gsrlw1 R1 (OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp.AXF_gnprz.VALS_gnpr CA c (mc_tbl c)) (mc_tbl c) eq_refl ltac:(lia)). reflexivity. }
  rewrite Vn in C9, C14.
  assert (V18 : bv_unsigned (getr R1 (Z_to_bv 5 (Z.of_nat 8))) = c) by (rewrite B8, u_wa_small by (zlh HZ); reflexivity).
  assert (V19 : bv_unsigned (getr R1 (Z_to_bv 5 (Z.of_nat 9))) = CA + 80 * c) by (rewrite B9, u_wa_small by (zlh HZ); reflexivity).
  set (m2 := OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp.AXF_gnprz.gnpr_mem_pnpr m1 R1 CA c (mc_tbl c)) in *.
  assert (EM2 : m2 = wchainS m1 SP [(-72, 8%nat, CA + 80 * c); (-64, 8%nat, c); (-56, 8%nat, 279220)]).
  { unfold m2, OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp.AXF_gnprz.gnpr_mem_pnpr. rewrite HSP1, V18, V19, ?sub_add_lit. reflexivity. }
  clearbody m2.
  assert (HSP3 : bv_unsigned (getr R2 (Z_to_bv 5 (Z.of_nat 2))) = SP - 80) by (rewrite C2, HSP1, u_wa_small by (zlh HZ); ring).
  assert (G2 : mem_grows m m2).
  { rewrite EM2. exact (mem_grows_trans m m1 _ G1 (wchainS_grows _ m1 SP)). }
  assert (F12 : forall x, 0 <= x < 2^64 -> ~ (SP - 2048 <= x < SP) -> ~ (CA <= x < CA + 4096) -> m2 (wa x) = m (wa x)).
  { intros x Hx Q1 Q2. rewrite EM2.
    rewrite (wchainS_frame_in [(-72, 8%nat, CA + 80 * c); (-64, 8%nat, c); (-56, 8%nat, 279220)] m1 SP (-72) (-48)); [| clear - HZ; lia | clear - HZ; lia | reflexivity | reflexivity | clear - Hx; lia | clear - HZ Q1; lia]. apply F1; clear - HZ Hx Q1; lia. }
  (* [comment removed for export] *)
  regzH C8. regzH C9.
  assert (V38 : bv_unsigned (getr R2 (Z_to_bv 5 (Z.of_nat 8))) = CA + 80 * c) by (rewrite C8, u_wa_small by (zlh HZ); reflexivity).
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
  destruct (gsz_rng c ltac:((zlh HZ))) as (Hsz1 & Hsz2 & Hsz3).
  assert (STEP : exists R4 m3, msteps SEGS (mkst R2 (wa 0x44790) m2 rom) (mkst R4 (wa 0x7db84) m3 rom) /\
     m3 = wchainS (wbytes (wchainS m2 SP (L2a c CA n (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 21)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 22)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 23)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 24)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 25)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 26)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 27))))))
                               (wa (SB + 137438953472 + 128 * c)) (word_to_le_bytes 8 (wa 1152921504606846976)))
                             SP [(-272, 8%nat, n); (-264, 8%nat, CA + 80 * c + 16); (-256, 8%nat, SB + 4294967296 * c + 3758096384); (-248, 8%nat, 2305843009213693952);
                                 (-240, 8%nat, SB + 137438953472 + 128 * c + 8); (-232, 8%nat, 929816); (-224, 8%nat, SB + 137438953472 + 128 * c); (-216, 8%nat, 281360)] /\
     getr R4 1 = wa 281724 /\ getr R4 2 = wa (SP - 272) /\ getr R4 8 = wa (SB + 137438953472 + 128 * c) /\ getr R4 9 = wa (CA + 2560) /\
     getr R4 11 = wa (SB + 4294967296 * c) /\ getr R4 12 = wa 262144 /\ getr R4 13 = wa 96426 /\ getr R4 18 = wa (SB + 4294967296 * c) /\
     getr R4 19 = wa 262144 /\ getr R4 20 = wa (SB + 4294967296 * c) /\ getr R4 21 = wa (sz_tbl c) /\ getr R4 22 = wa 929816 /\
     (forall k, In k [3; 4; 26; 27; 28; 29; 30; 31]%nat -> getr R4 (Z_to_bv 5 (Z.of_nat k)) = getr R2 (Z_to_bv 5 (Z.of_nat k)))).
  { destruct (Z.le_gt_cases c 16) as [Hsm|Hbg].
    - (* [comment removed for export] *)
      assert (P3 : OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp.AXF_gng0psz.gng0ps_pre R2 m2 CA c n SB (SB + 137438953472)).
      { constructor; [exact C10 | exact C11 | exact C12 | exact C13 | exact C14
                     | (replace (getr R2 2) with (wa (SP - 80)) by (regzG; rewrite C2, HSP1; f_equal; ring);
                        apply (stk_ok_move m2 SP (SP - 80) 1024); [(zlh HZ) | (zlh HZ) | exact (stk_ok_grows m m2 (wa SP) 2048 G2 HSTK) | (zlh HZ) | (zlh HZ) | (zlh HZ)])
                     | (zlh HZ) | (clear - Hsm HZ; lia) | (zlh Hn) | (zlh HZ) | (zlh HZ) | (zlh HZ)
                     | rewrite HSP3; (zlh HZ) | (zlh HZ) | (zlh HZ) | | | | | | | | | | ].
        all: rewrite ?(ri_comm c SB), ?Z.add_0_r.
        all: first [ (apply (rd_frame m m2); [(zlh HZ) | lenq; (zlh HZ) | intros x Hx; znq; apply F12; clear - HZ Hx; lia | assumption])
                   | (intros d k Hd Hk; apply (store_ok_mono SEGS k m m2 _ G2); apply Iwri; clear - HZ Hd Hk; lia) ]. }
      destruct (OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp.AXF_gng0psz.gng0ps_png0ps R2 m2 rom CA c n SB (SB + 137438953472) P3
                  (sc_gng0ps R2 m2 (SP - 80) HSP3 CA c n SB (SB + 137438953472) ltac:(unfold gp_ok; clear - HZ Hn; lia) ltac:(clear - Hsm HZ; lia) ltac:(zlh Hn)))
        as (R4 & Hms4 & E1 & E2 & _ & _ & _ & E8 & E9 & _ & E11 & E12 & E13 & _ & _ & _ & _ & E18 & E19 & E20 & E21 & E22 & _ & _ & _ & KK4).
      assert (Esz : 262144 * Z.shiftr ((32 * c * n + -1) mod 2^64) 18 + 262144 = 262144).
      { assert (32 <= 32 * c * n <= 4096) by (clear - Hsm HZ Hn; nia). rewrite Z.mod_small by lia. rewrite shr18' by lia. ring. }
      rewrite Esz in E12, E19. rewrite <- (gsz_small c ltac:(clear - Hsm HZ; lia)) in E21.
      exists R4, (OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp.AXF_gng0psz.gng0ps_mem_png0ps m2 R2 CA c n SB (SB + 137438953472)). split; [exact Hms4|]. split.
      { unfold OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp.AXF_gng0psz.gng0ps_mem_png0ps, L2a. rewrite HSP3, V38, V39, V318, V319, V320, W21, W22, W23, W24, W25, W26, W27, ?(ri_comm c SB), ?(rb_comm c SB), ?sub_add_lit, ?Z.add_0_r. reflexivity. }
      regzH E2. replace (128 * c + (SB + 137438953472)) with (SB + 137438953472 + 128 * c) in E8 by ring.
      replace (4294967296 * c + SB) with (SB + 4294967296 * c) in E11, E18, E20 by ring.
      repeat split; try assumption. regzG. rewrite E2, HSP3. f_equal. ring.
    - (* [comment removed for export] *)
      assert (Hn1 : n = 1) by (destruct Hn as [_ Hn2]; rewrite (gmc_big c ltac:(clear - Hbg HZ; lia)) in Hn2; lia).
      assert (P3 : OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp.AXF_gng0pbz.gng0pb_pre R2 m2 CA c n SB (SB + 137438953472)).
      { constructor; [exact C10 | exact C11 | exact C12 | exact C13 | (rewrite <- Hn1; exact C14)
                     | (replace (getr R2 2) with (wa (SP - 80)) by (regzG; rewrite C2, HSP1; f_equal; ring);
                        apply (stk_ok_move m2 SP (SP - 80) 1024); [(zlh HZ) | (zlh HZ) | exact (stk_ok_grows m m2 (wa SP) 2048 G2 HSTK) | (zlh HZ) | (zlh HZ) | (zlh HZ)])
                     | (zlh HZ) | (clear - Hbg HZ; lia) | (zlh Hn) | (zlh HZ) | (zlh HZ) | (zlh HZ)
                     | rewrite HSP3; (zlh HZ) | (zlh HZ) | (zlh HZ) | | | | | | | | | | ].
        all: rewrite ?(ri_comm c SB), ?Z.add_0_r.
        all: first [ (apply (rd_frame m m2); [(zlh HZ) | lenq; (zlh HZ) | intros x Hx; znq; apply F12; clear - HZ Hx; lia | assumption])
                   | (intros d k Hd Hk; apply (store_ok_mono SEGS k m m2 _ G2); apply Iwri; clear - HZ Hd Hk; lia) ]. }
      destruct (OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp.AXF_gng0pbz.gng0pb_png0pb R2 m2 rom CA c n SB (SB + 137438953472) P3
                  (sc_gng0pb R2 m2 (SP - 80) HSP3 CA c n SB (SB + 137438953472) ltac:(unfold gp_ok; clear - HZ Hn; lia) ltac:(clear - Hbg HZ; lia) ltac:(zlh Hn)))
        as (R4 & Hms4 & E1 & E2 & _ & _ & _ & E8 & E9 & _ & E11 & E12 & E13 & _ & _ & _ & _ & E18 & E19 & E20 & E21 & E22 & _ & _ & _ & KK4).
      fold BIGSZ_E in E21. rewrite (bigsz_eval R2 (OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp.AXF_gng0pbz.VALS_gng0pb CA c n SB (SB + 137438953472)) c eq_refl ltac:(clear - Hbg HZ; lia)) in E21.
      exists R4, (OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp.AXF_gng0pbz.gng0pb_mem_png0pb m2 R2 CA c n SB (SB + 137438953472)). split; [exact Hms4|]. split.
      { unfold OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp.AXF_gng0pbz.gng0pb_mem_png0pb, L2a. rewrite HSP3, V38, V39, V318, V319, V320, W21, W22, W23, W24, W25, W26, W27, ?(ri_comm c SB), ?(rb_comm c SB), ?sub_add_lit, ?Z.add_0_r, ?Hn1. reflexivity. }
      regzH E2. replace (128 * c + (SB + 137438953472)) with (SB + 137438953472 + 128 * c) in E8 by ring.
      replace (4294967296 * c + SB) with (SB + 4294967296 * c) in E11, E18, E20 by ring.
      repeat split; try assumption. regzG. rewrite E2, HSP3. f_equal. ring. }
  destruct STEP as (R4 & m3 & Hms4 & EM3 & E1 & E2 & E8 & E9 & E11 & E12 & E13 & E18 & E19 & E20 & E21 & E22 & KK4).
  pose proof (msteps_trans SEGS _ _ _ Hms Hms4) as Hms'. clear Hms Hms4. rename Hms' into Hms.
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
  assert (HSP4 : bv_unsigned (getr R4 (Z_to_bv 5 (Z.of_nat 2))) = SP - 272) by (rewrite E2, u_wa_small by (zlh HZ); reflexivity).
  assert (P4 : AXF_mf0z.mf0_pre R4 m3 (SB + 4294967296 * c) 262144 96426 1540520).
  { constructor; [regzG; rewrite E11; reflexivity | regzG; exact E12 | regzG; exact E13
                 | (replace (getr R4 2) with (wa (SP - 272)) by (regzG; rewrite E2; reflexivity);
                    apply (stk_ok_move m3 SP (SP - 272) 1024); [(zlh HZ) | (zlh HZ) | exact (stk_ok_grows m m3 (wa SP) 2048 G3 HSTK) | (zlh HZ) | (zlh HZ) | (zlh HZ)])
                 | (zlh HZ) | (zlh HZ) | (zlh HZ) | (zlh HZ) | (zlh HZ) | (zlh HZ) | rewrite HSP4; (zlh HZ) | | | | ].
    all: apply (rd_frame m m3); [(zlh HZ) | lenq; (zlh HZ) | intros x Hx; znq; apply F13; clear - HZ Hx; lia | assumption]. }
  destruct (AXF_mf0z.mf0_pmf0 R4 m3 rom (SB + 4294967296 * c) 262144 96426 1540520 P4
              (sc_mf0 R4 m3 (SP - 272) (SB + 4294967296 * c) 262144 96426 1540520 HSP4 ltac:((zlh HZ))))
    as (R5 & Hms5 & F1' & F2' & F8 & F9 & F10 & F11 & F12' & F13' & F14 & F15 & F17 & F18 & F19 & F20 & KK5).
  clear P4.
  pose proof (msteps_trans SEGS _ _ _ Hms Hms5) as Hms'. clear Hms Hms5. rename Hms' into Hms.
  assert (EM4 : AXF_mf0z.mf0_mem_pmf0 m3 R4 (SB + 4294967296 * c) 262144 96426 1540520 =
                wchainS m3 SP [(-456, 8%nat, sz_tbl c); (-448, 8%nat, 1532192); (-440, 8%nat, 96426); (-432, 8%nat, SB + 4294967296 * c); (-424, 8%nat, 1);
                               (-416, 8%nat, 262144); (-408, 8%nat, 481756); (-400, 4%nat, 50); (-352, 8%nat, SB + 4294967296 * c); (-344, 8%nat, 262144);
                               (-336, 8%nat, SB + 4294967296 * c); (-328, 8%nat, SB + 4294967296 * c); (-320, 8%nat, 262144); (-312, 8%nat, 514992);
                               (-304, 8%nat, SB + 4294967296 * c); (-296, 8%nat, CA + 2560); (-288, 8%nat, SB + 137438953472 + 128 * c); (-280, 8%nat, 281724)]).
  { unfold AXF_mf0z.mf0_mem_pmf0. rewrite HSP4, E1, E8, E9, E18, E19, E20, E21, ?u_wa_small by (first [(zlh HZ) | (zlh Hsz1)]). rewrite ?sub_add_lit. reflexivity. }
  rewrite EM4 in Hms. clear EM4.
  eexists R5, _. split; [exact Hms|].
  split; [regzH F1'; exact F1'|]. split; [regzH F2'; rewrite F2', HSP4; f_equal; ring|].
  split; [regzH F8; exact F8|]. split; [regzH F10; exact F10|]. split; [regzH F11; exact F11|]. split; [regzH F12'; exact F12'|].
  split; [regzH F13'; exact F13'|]. split; [regzH F14; exact F14|]. split; [regzH F15; exact F15|]. split; [regzH F17; exact F17|].
  split; [rewrite (KK5 21%nat ltac:(cbn; memb')), E21; reflexivity|].
  split; [rewrite (KK5 22%nat ltac:(cbn; memb')); exact E22|].
  split; [intros k Hk; cbn in Hk; destruct Hk as [<-|[<-|[]]]; lazymatch goal with |- getr R5 (Z_to_bv 5 (Z.of_nat ?k)) = _ => rewrite (KK5 k ltac:(cbn; memb')), (KK4 k ltac:(cbn; memb')), (KK2 k ltac:(cbn; memb')), (KK1 k ltac:(cbn; memb')); reflexivity end|].
  rewrite EM3, EM2, EM1. unfold gmAd, gL3a. rewrite <- wchainS_app. unfold L1a. rewrite <- wchainS_app. reflexivity.
Qed.
End GSB.
(* [comment removed for export] *)
