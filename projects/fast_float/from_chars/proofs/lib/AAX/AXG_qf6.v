(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AxAsan AXG_put AXG_put2 AXG_np AXG_np2 AXG_np3 AXG_np4 AXG_nf1.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_nf2.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_npscp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_nf2.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_nf2 AXG_nf2b AXG_nf3.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_nf6.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_nf6.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_npf AXG_nf6.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AxAsan OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_put OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_put2 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_np OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_np2 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_np3 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_np4 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_nf1 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_nf2.AXG_nfsc OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_npscp OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_nf2.AXG_nfscp OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_nf2 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_nf2b OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_nf3 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_nf6.AXG_nf4 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_nf6.AXG_nf5 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_npf OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_nf6.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_gp AXG_gp2 AXG_gf1.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_gf2b.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_gf2b AXG_gf3 AXG_gf4.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_gf2b.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_q1.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_q3.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_q3.

Module AXG_qf2.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AxAsan AXG_put AXG_put2 AXG_np AXG_np2 AXG_np3 AXG_np4 AXG_nf1.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_nf2.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_npscp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_nf2.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_nf2 AXG_gp AXG_gp2 AXG_gp3 AXG_gf1.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_gf2b.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_q1.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_q3.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_q3.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AxAsan OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_put OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_put2 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_np OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_np2 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_np3 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_np4 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_nf1 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_nf2.AXG_nfsc OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_npscp OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_nf2.AXG_nfscp OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_nf2 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_gp OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_gp2 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_gp3 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_gf1 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_gf2b.AXG_gf2 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_q1 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_q3.AXG_q2 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_q3.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_q1.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_q1.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_q1.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_q1.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_gp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_gp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_gp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_gp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_gp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_gp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXF_mf0z.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXF_mf0z.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Asan.M.loaded_segments.
Lemma add_add_lit : forall S a b, S + a + b = S + (a + b).
Proof. intros. ring. Qed.

(* [comment removed for export] *)
Definition qL1a (c CA v1 v8 v9 v18 v19 v20 v21 : Z) : list (Z * nat * Z) :=
  [(-72, 8%nat, CA); (-64, 8%nat, CA + 80 * c); (-56, 8%nat, 277592);
   (-40, 8%nat, v21); (-32, 8%nat, v20); (-24, 8%nat, v19); (-16, 8%nat, v18); (-8, 8%nat, v9); (0, 8%nat, v8); (8, 8%nat, v1)].
Definition qL2a (c CA n h18 h19 h20 g21 g22 g23 g24 g25 g26 g27 : Z) : list (Z * nat * Z) :=
  [(-184, 8%nat, g27); (-176, 8%nat, g26); (-168, 8%nat, g25); (-160, 8%nat, g24); (-152, 8%nat, g23); (-144, 8%nat, g22); (-136, 8%nat, g21);
   (-128, 8%nat, h20); (-120, 8%nat, h19); (-112, 8%nat, h18); (-104, 8%nat, n); (-96, 8%nat, CA + 80 * c); (-88, 8%nat, 279672)].
Definition qmAc (m : word -> option byte) (SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 v21 h18 h19 h20 g21 g22 g23 g24 g25 g26 g27 : Z) : word -> option byte :=
  wchainS (wbytes (wchainS (ic_mem (wchainS m SP (qL1a c CA v1 v8 v9 v18 v19 v20 v21)) CA) SP (qL2a c CA n h18 h19 h20 g21 g22 g23 g24 g25 g26 g27))
                  (wa RI) (word_to_le_bytes 8 (wa 1152921504606846976))) SP (gL3a c CA n RI RB FA).

Section QSA.
Context {fx : FPState}.
Variable rom : word -> option byte.
Variables (m : word -> option byte) (regs : bvmap 5 word) (QC CA c SB SP sz0 st fsz mp : Z).
Hypothesis Hc24 : c = 24.
Hypothesis H2 : getr regs 2 = wa (SP + 16).
Hypothesis HSP : 2^46 + 4096 <= SP /\ SP + 16 <= 2^47 /\ SP mod 16 = 0.
Hypothesis HSTK16 : stk_ok SEGS m (wa (SP + 16)) 2064.
Hypothesis H10 : getr regs 10 = wa QC.
Hypothesis H11 : getr regs 11 = wa CA.
Hypothesis H13 : getr regs 13 = wa mp.
Hypothesis H14 : getr regs 14 = wa fsz.
Hypothesis HQC : QC = CA - 128.
Hypothesis Hfm : 0 <= fsz <= 2^40 /\ 0 <= mp < 2^64.
Hypothesis Rq0 : rd m QC 8 0.
Hypothesis HCA : ((4304 <= CA /\ CA + 3888 <= 65536) \/ 6529232 <= CA) /\ CA mod 16 = 0 /\ CA + 4096 <= SP - 2048.
Hypothesis HSB : 17594333495296 <= SB /\ SB mod 4096 = 0 /\ SB + 137438953472 + 4096 <= SP - 2048.
Hypothesis HSEP : CA + 2592 <= SB \/ SB + 137438953472 + 4096 <= CA.
Hypothesis Hszst : 0 <= sz0 < 2^64 /\ 0 <= st < 2^64.
Hypothesis Icnt : rd m (CA + 80 * c) 4 0.
Hypothesis Imc : rd m (CA + 80 * c + 4) 4 0.
Hypothesis Isz : rd m (CA + 80 * c + 8) 8 sz0.
Hypothesis Ist : rd m (CA + 2576) 8 st.
Hypothesis Iwc : wr m CA 2592.
Hypothesis ISB : rd m 923512 8 SB.
Hypothesis IRIB : rd m 923528 8 (SB + 137438953472).
Hypothesis Irtoi : rd m 923520 4 4294967295.
Hypothesis Iprem : rd m 923536 1 0.
Hypothesis Imu : rd m (SB + 137438953472 + 128 * c) 8 0.
Hypothesis Inf0 : rd m (SB + 137438953472 + 128 * c + 16) 8 0.
Hypothesis Iau : rd m (SB + 137438953472 + 128 * c + 32) 8 0.
Hypothesis Imapu : rd m (SB + 137438953472 + 128 * c + 48) 8 0.
Hypothesis Imeta : rd m (SB + 137438953472 + 128 * c + 56) 8 0.
Hypothesis Iwri : wr m (SB + 137438953472 + 128 * c) 128.
Hypothesis Igot : rd m 904176 8 1525856.
Hypothesis Ipsz : rd m 1525856 8 4096.
Hypothesis Icf : rd m 904192 8 1534184.
Hypothesis Idpm : rd m 1534444 1 0.

Lemma qsegA : exists R mA, msteps SEGS (mkst regs (wa 0x43b04) m rom) (mkst R (wa 0x73c44) mA rom) /\
  getr R (Z_to_bv 5 (Z.of_nat 1)) = wa 481796 /\ getr R (Z_to_bv 5 (Z.of_nat 2)) = wa (SP - 400) /\
  getr R (Z_to_bv 5 (Z.of_nat 8)) = wa 262144 /\ getr R (Z_to_bv 5 (Z.of_nat 10)) = wa (SB + 4294967296 * c) /\
  getr R (Z_to_bv 5 (Z.of_nat 11)) = wa 262144 /\ getr R (Z_to_bv 5 (Z.of_nat 12)) = wa 3 /\ getr R (Z_to_bv 5 (Z.of_nat 13)) = wa 50 /\
  getr R (Z_to_bv 5 (Z.of_nat 14)) = wa 18446744073709551615 /\ getr R (Z_to_bv 5 (Z.of_nat 15)) = wa 0 /\
  getr R (Z_to_bv 5 (Z.of_nat 17)) = wa 222 /\ getr R (Z_to_bv 5 (Z.of_nat 21)) = wa (sz_tbl c) /\ getr R (Z_to_bv 5 (Z.of_nat 22)) = wa 923480 /\
  (forall k, In k [3; 4]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))) /\
  mA = qmAc m SP CA c (mc_tbl c / 2) (SB + 137438953472 + 128 * c) (SB + 4294967296 * c) (SB + 4294967296 * c + 3758096384)
         (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 1)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 8)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 9)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 19)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 20)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 21)))) mp QC (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 12)))) fsz (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 22)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 23)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 24)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 25)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 26)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 27)))).
Proof using All.
  assert (Hcr5 : 1 <= c <= 30) by lia.
  assert (HZ : ((4304 <= CA /\ CA + 3888 <= 65536) \/ 6529232 <= CA) /\ CA mod 16 = 0 /\ CA + 4096 <= SP - 2048 /\ 17594333495296 <= SB /\ SB mod 4096 = 0 /\
               SB + 137438953472 + 4096 <= SP - 2048 /\ 2^46 + 4096 <= SP <= 2^47 - 16 /\ 1 <= c <= 30 /\ c = 24 /\ QC = CA - 128 /\
               (CA + 2592 <= SB \/ SB + 137438953472 + 4096 <= CA) /\ 0 <= sz0 < 2^64 /\ 0 <= st < 2^64 /\ 0 <= fsz <= 2^40 /\ 0 <= mp < 2^64) by (clear - HCA HSB HSP Hcr5 Hc24 HQC HSEP Hszst Hfm; lia).
  clear HCA HSB HSP Hcr5 HSEP Hszst Hfm.
  assert (HSTK : stk_ok SEGS m (wa SP) 2048).
  { intros a k A1 A2. apply HSTK16; rewrite u_wa_small in * by (zlh HZ); lia. }
  assert (HSPa : bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) = SP + 16) by (rgz; rewrite H2, u_wa_small by (zlh HZ); reflexivity).
  set (v12 := (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 12))))) in *.
  (* [comment removed for export] *)
  assert (P0 : OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_q1.AXF_qheadz.qhead_pre regs m QC CA fsz mp).
  { constructor; try assumption; try (zlh HZ).
    - rewrite H2. apply (stk_ok_shrink m (wa (SP + 16)) 2064 1024); [lia | exact HSTK16].
    - rewrite HSPa. zlh HZ.
    - rewrite Z.add_0_r. exact Rq0.
    - replace (CA + 1920) with (CA + 80 * c) by (zlh HZ). exact Icnt. }
  destruct (OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_q1.AXF_qheadz.qhead_phead regs m rom QC CA fsz mp P0 (sc_qhead regs m (SP + 16) HSPa QC CA fsz mp ltac:(zlh HZ)))
    as (R1 & Hms1 & A2 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A18 & A19 & A20 & A21 & KK0).
  clear P0.
  set (m1 := OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_q1.AXF_qheadz.qhead_mem_phead m regs QC CA fsz mp) in *.
  assert (EM1 : m1 = wchainS m SP [(-40, 8%nat, (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 21))))); (-32, 8%nat, (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 20))))); (-24, 8%nat, (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 19))))); (-16, 8%nat, (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18))))); (-8, 8%nat, (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 9))))); (0, 8%nat, (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 8))))); (8, 8%nat, (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 1)))))]).
  { unfold m1, OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_q1.AXF_qheadz.qhead_mem_phead. cbn [wchainS]. rewrite HSPa, ?add_add_lit. reflexivity. }
  clearbody m1.
  assert (G1 : mem_grows m m1) by (rewrite EM1; apply wchainS_grows).
  assert (F1 : forall x, 0 <= x < 2^64 -> ~ (SP - 48 <= x < SP + 16) -> m1 (wa x) = m (wa x)).
  { intros x Hx H. rewrite EM1. apply (wchainS_frame_in _ m SP (-48) 16); [(zlh HZ) | (zlh HZ) | vm_compute; reflexivity | vm_compute; reflexivity | exact Hx | exact H]. }
  assert (HSP1 : bv_unsigned (getr R1 (Z_to_bv 5 (Z.of_nat 2))) = SP - 48) by (rgz; rewrite A2, HSPa, u_wa_small by (zlh HZ); ring).
  assert (B2 : getr R1 (Z_to_bv 5 (Z.of_nat 2)) = wa (SP - 48)) by (rgz; rewrite A2, HSPa; f_equal; ring).
  regzH A8. regzH A9. regzH A18. regzH A19. regzH A20. regzH A21.
  (* [comment removed for export] *)
  assert (P1 : OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_q1.AXF_qnriz.qnri_pre R1 m1 CA c).
  { constructor; [exact A10 | rewrite A11; f_equal; (zlh HZ) | exact A12 | rewrite A13; f_equal; (zlh HZ) | | (zlh HZ) | (zlh HZ) | (zlh HZ) | rewrite HSP1; (zlh HZ) | | ].
    - replace (getr R1 2) with (wa (SP - 48)) by (rgz; rewrite B2; reflexivity).
      apply (stk_ok_move m1 SP (SP - 48) 1024); [(zlh HZ) | (zlh HZ) | exact (stk_ok_grows m m1 (wa SP) 2048 G1 HSTK) | (zlh HZ) | (zlh HZ) | (zlh HZ)].
    - apply (rd_frame m m1); [(zlh HZ) | lenq; (zlh HZ) | intros x Hx; znq; apply F1; clear - HZ Hx; lia | exact Imc].
    - intros d k Hd Hk. apply (store_ok_mono SEGS k m m1 _ G1). replace (CA + 84 + d) with (CA + (84 + d)) by ring. apply Iwc; clear - HZ Hd Hk; lia. }
  destruct (OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_q1.AXF_qnriz.qnri_pnri R1 m1 rom CA c P1 (sc_qnri R1 m1 (SP - 48) HSP1 CA c ltac:((zlh HZ))))
    as (R2 & Hms2 & C1 & C2 & C5 & C6 & C7 & C8 & C10 & C11 & C12 & C13 & C14 & C15 & C16 & C17 & C28 & C29 & C30 & KK2).
  clear P1 C5 C6 C7 C15 C16 C17 C28 C29 C30.
  pose proof (msteps_trans SEGS _ _ _ Hms1 Hms2) as Hms. clear Hms1 Hms2.
  assert (V18 : bv_unsigned (getr R1 (Z_to_bv 5 (Z.of_nat 8))) = CA + 80 * c) by (rewrite A8, u_wa_small by (zlh HZ); (zlh HZ)).
  assert (V19 : bv_unsigned (getr R1 (Z_to_bv 5 (Z.of_nat 9))) = CA) by (rewrite A9, u_wa_small by (zlh HZ); reflexivity).
  set (m2 := OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_q1.AXF_qnriz.qnri_mem_pnri m1 R1 CA c) in *.
  assert (EM2 : m2 = ic_mem (wchainS m1 SP [(-72, 8%nat, CA); (-64, 8%nat, CA + 80 * c); (-56, 8%nat, 277592)]) CA).
  { unfold m2, OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_q1.AXF_qnriz.qnri_mem_pnri, ic_mem. rewrite HSP1, V18, V19, ?sub_add_lit. reflexivity. }
  clearbody m2.
  set (n := mc_tbl c / 2).
  destruct (gmc_rng c ltac:((zlh HZ))) as [Hmc1 Hmc2].
  assert (Hn : 1 <= n <= 8 /\ mc_tbl c = 2 * n) by (unfold n; pose proof (Z.div_mod (mc_tbl c) 2 ltac:(lia)); lia).
  (* [comment removed for export] *)
  destruct (ic_rd (wchainS m1 SP [(-72, 8%nat, CA); (-64, 8%nat, CA + 80 * c); (-56, 8%nat, 277592)]) CA c ltac:((zlh HZ)) ltac:((zlh HZ)) ltac:((zlh HZ))) as [Rmc Rsz].
  rewrite <- EM2 in Rmc, Rsz.
  assert (P2 : OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_gp.AXF_gnri2z.gnri2_pre R2 m2 CA c (mc_tbl c)).
  { constructor; [exact C8 | exact C10 | exact C12 | exact C14 | (zlh HZ) | (zlh HZ) | (zlh Hmc1) | (zlh HZ) | exact Rmc]. }
  destruct (OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_gp.AXF_gnri2z.gnri2_pnri2 R2 m2 rom CA c (mc_tbl c) P2 ltac:(cbn [OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_gp.AXF_gnri2.RES_pnri2 fst snd]; constructor))
    as (R3 & Hms3 & D8 & D9 & D10 & D11 & D12 & D13 & D14 & KK3).
  clear P2.
  assert (Em3 : OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_gp.AXF_gnri2z.gnri2_mem_pnri2 m2 R2 CA c (mc_tbl c) = m2) by reflexivity. rewrite Em3 in Hms3. clear Em3.
  pose proof (msteps_trans SEGS _ _ _ Hms Hms3) as Hms'. clear Hms Hms3. rename Hms' into Hms.
  assert (Vn : bv_unsigned (edenot (Ez R2 (OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_gp.AXF_gnri2z.VALS_gnri2 CA c (mc_tbl c))) (EAluw ALU_SRL (EExt true 0 4 (EVar 34)) (ELit 1))) = n).
  { rewrite (gsrlw1 R2 (OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_gp.AXF_gnri2z.VALS_gnri2 CA c (mc_tbl c)) (mc_tbl c) eq_refl ltac:(lia)). reflexivity. }
  rewrite Vn in D9, D14.
  regzH C2.
  assert (HSP3 : bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 2))) = SP - 80).
  { rewrite (KK3 2%nat ltac:(cbn; memb')), C2, HSP1, u_wa_small by (zlh HZ); ring. }
  assert (G2 : mem_grows m m2).
  { rewrite EM2. set (L := [(-72, 8%nat, CA); (-64, 8%nat, CA + 80 * c); (-56, 8%nat, 277592)]).
    exact (mem_grows_trans m m1 (ic_mem (wchainS m1 SP L) CA) G1 (mem_grows_trans m1 (wchainS m1 SP L) (ic_mem (wchainS m1 SP L) CA) (wchainS_grows L m1 SP) (ic_grows (wchainS m1 SP L) CA))). }
  assert (F12 : forall x, 0 <= x < 2^64 -> ~ (SP - 2048 <= x < SP + 16) -> ~ (CA <= x < CA + 4096) -> m2 (wa x) = m (wa x)).
  { intros x Hx Q1 Q2. rewrite EM2, ic_frame by (clear - HZ Hx Q2; lia).
    rewrite (wchainS_frame_in [(-72, 8%nat, CA); (-64, 8%nat, CA + 80 * c); (-56, 8%nat, 277592)] m1 SP (-72) (-48)); [| clear - HZ; lia | clear - HZ; lia | reflexivity | reflexivity | clear - Hx; lia | clear - HZ Q1; lia]. apply F1; clear - HZ Hx Q1; lia. }
  (* [comment removed for export] *)
  regzH D8. regzH D9.
  assert (V38 : bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 8))) = CA + 80 * c) by (rewrite D8, u_wa_small by (zlh HZ); reflexivity).
  assert (V39 : bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 9))) = n) by (rewrite D9, u_wa_small by (zlh Hn); reflexivity).
  assert (V318 : bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 18))) = mp) by (rewrite (KK3 18%nat ltac:(cbn; memb')), (KK2 18%nat ltac:(cbn; memb')), A18, u_wa_small by (zlh HZ); reflexivity).
  assert (V319 : bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 19))) = QC) by (rewrite (KK3 19%nat ltac:(cbn; memb')), (KK2 19%nat ltac:(cbn; memb')), A19, u_wa_small by (zlh HZ); reflexivity).
  assert (V320 : bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 20))) = v12) by (rewrite (KK3 20%nat ltac:(cbn; memb')), (KK2 20%nat ltac:(cbn; memb')), A20; apply u_wa_small; unfold v12; pose proof (u_rng64 (getr regs (Z_to_bv 5 (Z.of_nat 12)))); lia).
  assert (W21 : bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 21))) = fsz) by (rewrite (KK3 21%nat ltac:(cbn; memb')), (KK2 21%nat ltac:(cbn; memb')), A21, u_wa_small by (zlh HZ); reflexivity).
  assert (W22 : getr R3 (Z_to_bv 5 (Z.of_nat 22)) = getr regs (Z_to_bv 5 (Z.of_nat 22))) by (rewrite (KK3 22%nat ltac:(cbn; memb')), (KK2 22%nat ltac:(cbn; memb')), (KK0 22%nat ltac:(cbn; memb')); reflexivity).
  assert (W23 : getr R3 (Z_to_bv 5 (Z.of_nat 23)) = getr regs (Z_to_bv 5 (Z.of_nat 23))) by (rewrite (KK3 23%nat ltac:(cbn; memb')), (KK2 23%nat ltac:(cbn; memb')), (KK0 23%nat ltac:(cbn; memb')); reflexivity).
  assert (W24 : getr R3 (Z_to_bv 5 (Z.of_nat 24)) = getr regs (Z_to_bv 5 (Z.of_nat 24))) by (rewrite (KK3 24%nat ltac:(cbn; memb')), (KK2 24%nat ltac:(cbn; memb')), (KK0 24%nat ltac:(cbn; memb')); reflexivity).
  assert (W25 : getr R3 (Z_to_bv 5 (Z.of_nat 25)) = getr regs (Z_to_bv 5 (Z.of_nat 25))) by (rewrite (KK3 25%nat ltac:(cbn; memb')), (KK2 25%nat ltac:(cbn; memb')), (KK0 25%nat ltac:(cbn; memb')); reflexivity).
  assert (W26 : getr R3 (Z_to_bv 5 (Z.of_nat 26)) = getr regs (Z_to_bv 5 (Z.of_nat 26))) by (rewrite (KK3 26%nat ltac:(cbn; memb')), (KK2 26%nat ltac:(cbn; memb')), (KK0 26%nat ltac:(cbn; memb')); reflexivity).
  assert (W27 : getr R3 (Z_to_bv 5 (Z.of_nat 27)) = getr regs (Z_to_bv 5 (Z.of_nat 27))) by (rewrite (KK3 27%nat ltac:(cbn; memb')), (KK2 27%nat ltac:(cbn; memb')), (KK0 27%nat ltac:(cbn; memb')); reflexivity).
  destruct (gsz_rng c ltac:((zlh HZ))) as (Hsz1 & Hsz2 & Hsz3).
  assert (STEP : exists R4 m3, msteps SEGS (mkst R3 (wa 0x44474) m2 rom) (mkst R4 (wa 0x7db90) m3 rom) /\
     m3 = wchainS (wbytes (wchainS m2 SP (qL2a c CA n mp QC v12 fsz (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 22)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 23)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 24)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 25)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 26)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 27))))))
                               (wa (SB + 137438953472 + 128 * c)) (word_to_le_bytes 8 (wa 1152921504606846976)))
                             SP [(-272, 8%nat, n); (-264, 8%nat, CA + 80 * c + 16); (-256, 8%nat, SB + 4294967296 * c + 3758096384); (-248, 8%nat, 2305843009213693952);
                                 (-240, 8%nat, SB + 137438953472 + 128 * c + 8); (-232, 8%nat, 923480); (-224, 8%nat, SB + 137438953472 + 128 * c); (-216, 8%nat, 280564)] /\
     getr R4 1 = wa 280928 /\ getr R4 2 = wa (SP - 272) /\ getr R4 8 = wa (SB + 137438953472 + 128 * c) /\ getr R4 9 = wa (CA + 2560) /\
     getr R4 11 = wa (SB + 4294967296 * c) /\ getr R4 12 = wa 262144 /\ getr R4 13 = wa 96458 /\ getr R4 18 = wa (SB + 4294967296 * c) /\
     getr R4 19 = wa 262144 /\ getr R4 20 = wa (SB + 4294967296 * c) /\ getr R4 21 = wa (sz_tbl c) /\ getr R4 22 = wa 923480 /\
     (forall k, In k [3; 4; 26; 27; 28; 29; 30; 31]%nat -> getr R4 (Z_to_bv 5 (Z.of_nat k)) = getr R3 (Z_to_bv 5 (Z.of_nat k)))).
  { destruct (Z.le_gt_cases c 16) as [Hsm|Hbg].
    - (* [comment removed for export] *) exfalso. clear - Hsm HZ. lia.
    - (* [comment removed for export] *)
      assert (Hn1 : n = 1) by (destruct Hn as [_ Hn2]; rewrite (gmc_big c ltac:(clear - Hbg HZ; lia)) in Hn2; lia).
      assert (P3 : OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_gp.AXF_gng0pbz.gng0pb_pre R3 m2 CA c n SB (SB + 137438953472)).
      { constructor; [exact D10 | exact D11 | exact D12 | exact D13 | (rewrite <- Hn1; exact D14)
                     | (replace (getr R3 2) with (wa (SP - 80)) by (regzG; rewrite (KK3 2%nat ltac:(cbn; memb')), C2, HSP1; f_equal; ring);
                        apply (stk_ok_move m2 SP (SP - 80) 1024); [(zlh HZ) | (zlh HZ) | exact (stk_ok_grows m m2 (wa SP) 2048 G2 HSTK) | (zlh HZ) | (zlh HZ) | (zlh HZ)])
                     | (zlh HZ) | (clear - Hbg HZ; lia) | (zlh Hn) | (zlh HZ) | (zlh HZ) | (zlh HZ)
                     | rewrite HSP3; (zlh HZ) | (zlh HZ) | (zlh HZ) | | | | | | | | | | ].
        all: rewrite ?(ri_comm c SB), ?Z.add_0_r.
        all: first [ (apply (rd_frame m m2); [(zlh HZ) | lenq; (zlh HZ) | intros x Hx; znq; apply F12; clear - HZ Hx; lia | assumption])
                   | (intros d k Hd Hk; apply (store_ok_mono SEGS k m m2 _ G2); apply Iwri; clear - HZ Hd Hk; lia) ]. }
      destruct (OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_gp.AXF_gng0pbz.gng0pb_png0pb R3 m2 rom CA c n SB (SB + 137438953472) P3
                  (sc_gng0pb R3 m2 (SP - 80) HSP3 CA c n SB (SB + 137438953472) ltac:(unfold gp_ok; clear - HZ Hn; lia) ltac:(clear - Hbg HZ; lia) ltac:(zlh Hn)))
        as (R4 & Hms4 & E1 & E2 & _ & _ & _ & E8 & E9 & _ & E11 & E12 & E13 & _ & _ & _ & _ & E18 & E19 & E20 & E21 & E22 & _ & _ & _ & KK4).
      fold BIGSZ_E in E21. rewrite (bigsz_eval R3 (OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_gp.AXF_gng0pbz.VALS_gng0pb CA c n SB (SB + 137438953472)) c eq_refl ltac:(clear - Hbg HZ; lia)) in E21.
      exists R4, (OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_gp.AXF_gng0pbz.gng0pb_mem_png0pb m2 R3 CA c n SB (SB + 137438953472)). split; [exact Hms4|]. split.
      { unfold OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_gp.AXF_gng0pbz.gng0pb_mem_png0pb, L2a. rewrite HSP3, V38, V39, V318, V319, V320, W21, W22, W23, W24, W25, W26, W27, ?(ri_comm c SB), ?(rb_comm c SB), ?sub_add_lit, ?Z.add_0_r, ?Hn1. reflexivity. }
      regzH E2. replace (128 * c + (SB + 137438953472)) with (SB + 137438953472 + 128 * c) in E8 by ring.
      replace (4294967296 * c + SB) with (SB + 4294967296 * c) in E11, E18, E20 by ring.
      repeat split; try assumption. regzG. rewrite E2, HSP3. f_equal. ring. }
  destruct STEP as (R4 & m3 & Hms4 & EM3 & E1 & E2 & E8 & E9 & E11 & E12 & E13 & E18 & E19 & E20 & E21 & E22 & KK4).
  pose proof (msteps_trans SEGS _ _ _ Hms Hms4) as Hms'. clear Hms Hms4. rename Hms' into Hms.
  assert (G3 : mem_grows m m3).
  { rewrite EM3. exact (mem_grows_trans _ _ _ G2 (mem_grows_trans _ _ _ (wchainS_grows (qL2a c CA n mp QC v12 fsz (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 22)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 23)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 24)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 25)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 26)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 27))))) m2 SP)
                          (mem_grows_trans _ _ _ (wbytes_grows _ _ _) (wchainS_grows _ _ SP)))). }
  assert (F13 : forall x, 0 <= x < 2^64 -> ~ (SP - 2048 <= x < SP + 16) -> ~ (CA <= x < CA + 4096) -> ~ (SB + 137438953472 + 128 * c <= x < SB + 137438953472 + 128 * c + 8) ->
                  m3 (wa x) = m (wa x)).
  { intros x Hx Q1 Q2 Q3. rewrite EM3.
    rewrite (wchainS_frame_in [(-272, 8%nat, n); (-264, 8%nat, CA + 80 * c + 16); (-256, 8%nat, SB + 4294967296 * c + 3758096384); (-248, 8%nat, 2305843009213693952);
                                 (-240, 8%nat, SB + 137438953472 + 128 * c + 8); (-232, 8%nat, 923480); (-224, 8%nat, SB + 137438953472 + 128 * c); (-216, 8%nat, 280564)] _ SP (-272) (-208));
      [| clear - HZ; lia | clear - HZ; lia | reflexivity | reflexivity | clear - Hx; lia | clear - HZ Q1; lia].
    rewrite wb_other by first [exact Hx | (lenq'; clear - HZ Hn; lia) | (lenq'; clear - HZ Hn Q3; lia)].
    rewrite (wchainS_frame_in (qL2a c CA n mp QC v12 fsz (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 22)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 23)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 24)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 25)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 26)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 27))))) m2 SP (-184) (-80));
      [| clear - HZ; lia | clear - HZ; lia | reflexivity | reflexivity | clear - Hx; lia | clear - HZ Q1; lia].
    apply F12; assumption. }
  (* [comment removed for export] *)
  regzH E2. regzH E8. regzH E9. regzH E11. regzH E12. regzH E13. regzH E18. regzH E19. regzH E20. regzH E21. regzH E22. regzH E1.
  assert (HSP4 : bv_unsigned (getr R4 (Z_to_bv 5 (Z.of_nat 2))) = SP - 272) by (rewrite E2, u_wa_small by (zlh HZ); reflexivity).
  assert (P4 : AXF_mf0z.mf0_pre R4 m3 (SB + 4294967296 * c) 262144 96458 1534184).
  { constructor; [regzG; rewrite E11; reflexivity | regzG; exact E12 | regzG; exact E13
                 | (replace (getr R4 2) with (wa (SP - 272)) by (regzG; rewrite E2; reflexivity);
                    apply (stk_ok_move m3 SP (SP - 272) 1024); [(zlh HZ) | (zlh HZ) | exact (stk_ok_grows m m3 (wa SP) 2048 G3 HSTK) | (zlh HZ) | (zlh HZ) | (zlh HZ)])
                 | (zlh HZ) | (zlh HZ) | (zlh HZ) | (zlh HZ) | (zlh HZ) | (zlh HZ) | rewrite HSP4; (zlh HZ) | | | | ].
    all: apply (rd_frame m m3); [(zlh HZ) | lenq; (zlh HZ) | intros x Hx; znq; apply F13; clear - HZ Hx; lia | assumption]. }
  destruct (AXF_mf0z.mf0_pmf0 R4 m3 rom (SB + 4294967296 * c) 262144 96458 1534184 P4
              (sc_mf0 R4 m3 (SP - 272) (SB + 4294967296 * c) 262144 96458 1534184 HSP4 ltac:((zlh HZ))))
    as (R5 & Hms5 & F1' & F2' & F8 & F9 & F10 & F11 & F12' & F13' & F14 & F15 & F17 & F18 & F19 & F20 & KK5).
  clear P4.
  pose proof (msteps_trans SEGS _ _ _ Hms Hms5) as Hms'. clear Hms Hms5. rename Hms' into Hms.
  assert (EM4 : AXF_mf0z.mf0_mem_pmf0 m3 R4 (SB + 4294967296 * c) 262144 96458 1534184 =
                wchainS m3 SP [(-456, 8%nat, sz_tbl c); (-448, 8%nat, 1525856); (-440, 8%nat, 96458); (-432, 8%nat, SB + 4294967296 * c); (-424, 8%nat, 1);
                               (-416, 8%nat, 262144); (-408, 8%nat, 481768); (-400, 4%nat, 50); (-352, 8%nat, SB + 4294967296 * c); (-344, 8%nat, 262144);
                               (-336, 8%nat, SB + 4294967296 * c); (-328, 8%nat, SB + 4294967296 * c); (-320, 8%nat, 262144); (-312, 8%nat, 515004);
                               (-304, 8%nat, SB + 4294967296 * c); (-296, 8%nat, CA + 2560); (-288, 8%nat, SB + 137438953472 + 128 * c); (-280, 8%nat, 280928)]).
  { unfold AXF_mf0z.mf0_mem_pmf0. rewrite HSP4, E1, E8, E9, E18, E19, E20, E21, ?u_wa_small by (first [(zlh HZ) | (zlh Hsz1)]). rewrite ?sub_add_lit. reflexivity. }
  rewrite EM4 in Hms. clear EM4.
  eexists R5, _. split; [exact Hms|].
  split; [regzH F1'; exact F1'|]. split; [regzH F2'; rewrite F2', HSP4; f_equal; ring|].
  split; [regzH F8; exact F8|]. split; [regzH F10; exact F10|]. split; [regzH F11; exact F11|]. split; [regzH F12'; exact F12'|].
  split; [regzH F13'; exact F13'|]. split; [regzH F14; exact F14|]. split; [regzH F15; exact F15|]. split; [regzH F17; exact F17|].
  split; [rewrite (KK5 21%nat ltac:(cbn; memb')), E21; reflexivity|].
  split; [rewrite (KK5 22%nat ltac:(cbn; memb')); exact E22|].
  split; [intros k Hk; cbn in Hk; destruct Hk as [<-|[<-|[]]]; lazymatch goal with |- getr R5 (Z_to_bv 5 (Z.of_nat ?k)) = _ => rewrite (KK5 k ltac:(cbn; memb')), (KK4 k ltac:(cbn; memb')), (KK3 k ltac:(cbn; memb')), (KK2 k ltac:(cbn; memb')), (KK0 k ltac:(cbn; memb')); reflexivity end|].
  rewrite EM3, EM2, EM1. unfold qmAc, gL3a. rewrite <- wchainS_app. unfold qL1a. rewrite <- wchainS_app. reflexivity.
Qed.
End QSA.
End AXG_qf2.


Module AXG_qf2b.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AxAsan AXG_put AXG_put2 AXG_np AXG_np2 AXG_np3 AXG_np4 AXG_nf1.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_nf2.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_npscp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_nf2.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_nf2 AXG_nf2b AXG_gp AXG_gp2 AXG_gp3 AXG_gf1.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_gf2b.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_q1.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_q3.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_q3.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AxAsan OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_put OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_put2 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_np OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_np2 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_np3 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_np4 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_nf1 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_nf2.AXG_nfsc OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_npscp OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_nf2.AXG_nfscp OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_nf2 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_nf2b OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_gp OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_gp2 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_gp3 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_gf1 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_gf2b.AXG_gf2 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_q1 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_q3.AXG_q2 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_q3 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_qf6.AXG_qf2.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_q1.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_q1.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_q1.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_q1.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_gp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_gp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_gp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_gp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXF_mf0z.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXF_mf0z.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Asan.M.loaded_segments.
Definition qmAd (m : word -> option byte) (SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 v21 h18 h19 h20 g21 g22 g23 g24 g25 g26 g27 : Z) : word -> option byte :=
  wchainS (wbytes (wchainS (wchainS m SP (qL1a c CA v1 v8 v9 v18 v19 v20 v21)) SP (qL2a c CA n h18 h19 h20 g21 g22 g23 g24 g25 g26 g27))
                  (wa RI) (word_to_le_bytes 8 (wa 1152921504606846976))) SP (gL3a c CA n RI RB FA).

Section QSB.
Context {fx : FPState}.
Variable rom : word -> option byte.
Variables (m : word -> option byte) (regs : bvmap 5 word) (QC CA c SB SP sz0 st fsz mp : Z).
Hypothesis Hc24 : c = 24.
Hypothesis H2 : getr regs 2 = wa (SP + 16).
Hypothesis HSP : 2^46 + 4096 <= SP /\ SP + 16 <= 2^47 /\ SP mod 16 = 0.
Hypothesis HSTK16 : stk_ok SEGS m (wa (SP + 16)) 2064.
Hypothesis H10 : getr regs 10 = wa QC.
Hypothesis H11 : getr regs 11 = wa CA.
Hypothesis H13 : getr regs 13 = wa mp.
Hypothesis H14 : getr regs 14 = wa fsz.
Hypothesis HQC : QC = CA - 128.
Hypothesis Hfm : 0 <= fsz <= 2^40 /\ 0 <= mp < 2^64.
Hypothesis Rq0 : rd m QC 8 0.
Hypothesis HCA : ((4304 <= CA /\ CA + 3888 <= 65536) \/ 6529232 <= CA) /\ CA mod 16 = 0 /\ CA + 4096 <= SP - 2048.
Hypothesis HSB : 17594333495296 <= SB /\ SB mod 4096 = 0 /\ SB + 137438953472 + 4096 <= SP - 2048.
Hypothesis HSEP : CA + 2592 <= SB \/ SB + 137438953472 + 4096 <= CA.
Hypothesis Hszst : 0 <= sz0 < 2^64 /\ 0 <= st < 2^64.
Hypothesis Icnt : rd m (CA + 80 * c) 4 0.
Hypothesis Imc : rd m (CA + 80 * c + 4) 4 (mc_tbl c).
Hypothesis Isz : rd m (CA + 80 * c + 8) 8 sz0.
Hypothesis Ist : rd m (CA + 2576) 8 st.
Hypothesis Iwc : wr m CA 2592.
Hypothesis ISB : rd m 923512 8 SB.
Hypothesis IRIB : rd m 923528 8 (SB + 137438953472).
Hypothesis Irtoi : rd m 923520 4 4294967295.
Hypothesis Iprem : rd m 923536 1 0.
Hypothesis Imu : rd m (SB + 137438953472 + 128 * c) 8 0.
Hypothesis Inf0 : rd m (SB + 137438953472 + 128 * c + 16) 8 0.
Hypothesis Iau : rd m (SB + 137438953472 + 128 * c + 32) 8 0.
Hypothesis Imapu : rd m (SB + 137438953472 + 128 * c + 48) 8 0.
Hypothesis Imeta : rd m (SB + 137438953472 + 128 * c + 56) 8 0.
Hypothesis Iwri : wr m (SB + 137438953472 + 128 * c) 128.
Hypothesis Igot : rd m 904176 8 1525856.
Hypothesis Ipsz : rd m 1525856 8 4096.
Hypothesis Icf : rd m 904192 8 1534184.
Hypothesis Idpm : rd m 1534444 1 0.

Lemma qsegA' : exists R mA, msteps SEGS (mkst regs (wa 0x43b04) m rom) (mkst R (wa 0x73c44) mA rom) /\
  getr R (Z_to_bv 5 (Z.of_nat 1)) = wa 481796 /\ getr R (Z_to_bv 5 (Z.of_nat 2)) = wa (SP - 400) /\
  getr R (Z_to_bv 5 (Z.of_nat 8)) = wa 262144 /\ getr R (Z_to_bv 5 (Z.of_nat 10)) = wa (SB + 4294967296 * c) /\
  getr R (Z_to_bv 5 (Z.of_nat 11)) = wa 262144 /\ getr R (Z_to_bv 5 (Z.of_nat 12)) = wa 3 /\ getr R (Z_to_bv 5 (Z.of_nat 13)) = wa 50 /\
  getr R (Z_to_bv 5 (Z.of_nat 14)) = wa 18446744073709551615 /\ getr R (Z_to_bv 5 (Z.of_nat 15)) = wa 0 /\
  getr R (Z_to_bv 5 (Z.of_nat 17)) = wa 222 /\ getr R (Z_to_bv 5 (Z.of_nat 21)) = wa (sz_tbl c) /\ getr R (Z_to_bv 5 (Z.of_nat 22)) = wa 923480 /\
  (forall k, In k [3; 4]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))) /\
  mA = qmAd m SP CA c (mc_tbl c / 2) (SB + 137438953472 + 128 * c) (SB + 4294967296 * c) (SB + 4294967296 * c + 3758096384)
         (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 1)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 8)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 9)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 19)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 20)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 21)))) mp QC (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 12)))) fsz (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 22)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 23)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 24)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 25)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 26)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 27)))).
Proof using All.
  assert (Hcr5 : 1 <= c <= 30) by lia.
  assert (HZ : ((4304 <= CA /\ CA + 3888 <= 65536) \/ 6529232 <= CA) /\ CA mod 16 = 0 /\ CA + 4096 <= SP - 2048 /\ 17594333495296 <= SB /\ SB mod 4096 = 0 /\
               SB + 137438953472 + 4096 <= SP - 2048 /\ 2^46 + 4096 <= SP <= 2^47 - 16 /\ 1 <= c <= 30 /\ c = 24 /\ QC = CA - 128 /\
               (CA + 2592 <= SB \/ SB + 137438953472 + 4096 <= CA) /\ 0 <= sz0 < 2^64 /\ 0 <= st < 2^64 /\ 0 <= fsz <= 2^40 /\ 0 <= mp < 2^64) by (clear - HCA HSB HSP Hcr5 Hc24 HQC HSEP Hszst Hfm; lia).
  clear HCA HSB HSP Hcr5 HSEP Hszst Hfm.
  assert (HSTK : stk_ok SEGS m (wa SP) 2048).
  { intros a k A1 A2. apply HSTK16; rewrite u_wa_small in * by (zlh HZ); lia. }
  assert (HSPa : bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) = SP + 16) by (rgz; rewrite H2, u_wa_small by (zlh HZ); reflexivity).
  set (v12 := (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 12))))) in *.
  (* [comment removed for export] *)
  assert (P0 : OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_q1.AXF_qheadz.qhead_pre regs m QC CA fsz mp).
  { constructor; try assumption; try (zlh HZ).
    - rewrite H2. apply (stk_ok_shrink m (wa (SP + 16)) 2064 1024); [lia | exact HSTK16].
    - rewrite HSPa. zlh HZ.
    - rewrite Z.add_0_r. exact Rq0.
    - replace (CA + 1920) with (CA + 80 * c) by (zlh HZ). exact Icnt. }
  destruct (OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_q1.AXF_qheadz.qhead_phead regs m rom QC CA fsz mp P0 (sc_qhead regs m (SP + 16) HSPa QC CA fsz mp ltac:(zlh HZ)))
    as (R1 & Hms1 & A2 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A18 & A19 & A20 & A21 & KK0).
  clear P0.
  set (m1 := OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_q1.AXF_qheadz.qhead_mem_phead m regs QC CA fsz mp) in *.
  assert (EM1 : m1 = wchainS m SP [(-40, 8%nat, (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 21))))); (-32, 8%nat, (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 20))))); (-24, 8%nat, (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 19))))); (-16, 8%nat, (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18))))); (-8, 8%nat, (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 9))))); (0, 8%nat, (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 8))))); (8, 8%nat, (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 1)))))]).
  { unfold m1, OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_q1.AXF_qheadz.qhead_mem_phead. cbn [wchainS]. rewrite HSPa, ?add_add_lit. reflexivity. }
  clearbody m1.
  assert (G1 : mem_grows m m1) by (rewrite EM1; apply wchainS_grows).
  assert (F1 : forall x, 0 <= x < 2^64 -> ~ (SP - 48 <= x < SP + 16) -> m1 (wa x) = m (wa x)).
  { intros x Hx H. rewrite EM1. apply (wchainS_frame_in _ m SP (-48) 16); [(zlh HZ) | (zlh HZ) | vm_compute; reflexivity | vm_compute; reflexivity | exact Hx | exact H]. }
  assert (HSP1 : bv_unsigned (getr R1 (Z_to_bv 5 (Z.of_nat 2))) = SP - 48) by (rgz; rewrite A2, HSPa, u_wa_small by (zlh HZ); ring).
  assert (B2 : getr R1 (Z_to_bv 5 (Z.of_nat 2)) = wa (SP - 48)) by (rgz; rewrite A2, HSPa; f_equal; ring).
  regzH A8. regzH A9. regzH A18. regzH A19. regzH A20. regzH A21.
  (* [comment removed for export] *)
  set (n := mc_tbl c / 2).
  destruct (gmc_rng c ltac:((zlh HZ))) as [Hmc1 Hmc2].
  assert (Hn : 1 <= n <= 8 /\ mc_tbl c = 2 * n) by (unfold n; pose proof (Z.div_mod (mc_tbl c) 2 ltac:(lia)); lia).
  assert (P1 : OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_q1.AXF_qnprz.qnpr_pre R1 m1 CA c (mc_tbl c)).
  { constructor; [exact A10 | rewrite A11; f_equal; (zlh HZ) | exact A12 | rewrite A13; f_equal; (zlh HZ) | | first [(zlh HZ) | (zlh Hmc1)] | first [(zlh HZ) | (zlh Hmc1)] | first [(zlh HZ) | (zlh Hmc1)]
                 | first [(zlh HZ) | (zlh Hmc1)] | first [rewrite HSP1; (zlh HZ) | (zlh HZ) | (zlh Hmc1)] | ].
    - replace (getr R1 2) with (wa (SP - 48)) by (rgz; rewrite B2; reflexivity).
      apply (stk_ok_move m1 SP (SP - 48) 1024); [(zlh HZ) | (zlh HZ) | exact (stk_ok_grows m m1 (wa SP) 2048 G1 HSTK) | (zlh HZ) | (zlh HZ) | (zlh HZ)].
    - apply (rd_frame m m1); [(zlh HZ) | lenq; (zlh HZ) | intros x Hx; znq; apply F1; clear - HZ Hx; lia | exact Imc]. }
  destruct (OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_q1.AXF_qnprz.qnpr_pnpr R1 m1 rom CA c (mc_tbl c) P1 (sc_qnpr R1 m1 (SP - 48) HSP1 CA c (mc_tbl c) ltac:(clear - HZ Hmc1; lia)))
    as (R2 & Hms2 & C1 & C2 & C8 & C9 & C10 & C11 & C12 & C13 & C14 & KK2).
  clear P1 C1.
  pose proof (msteps_trans SEGS _ _ _ Hms1 Hms2) as Hms. clear Hms1 Hms2.
  regzH C2. regzH C8. regzH C9.
  assert (Vn : bv_unsigned (edenot (Ez R1 (OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_q1.AXF_qnprz.VALS_qnpr CA c (mc_tbl c))) (EAluw ALU_SRL (EExt true 0 4 (EVar 34)) (ELit 1))) = n).
  { rewrite (AXG_gf1.gsrlw1 R1 (OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_q1.AXF_qnprz.VALS_qnpr CA c (mc_tbl c)) (mc_tbl c) eq_refl ltac:(lia)). reflexivity. }
  rewrite Vn in C9, C14.
  assert (V18 : bv_unsigned (getr R1 (Z_to_bv 5 (Z.of_nat 8))) = CA + 80 * c) by (rewrite A8, u_wa_small by (zlh HZ); (zlh HZ)).
  assert (V19 : bv_unsigned (getr R1 (Z_to_bv 5 (Z.of_nat 9))) = CA) by (rewrite A9, u_wa_small by (zlh HZ); reflexivity).
  set (m2 := OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_q1.AXF_qnprz.qnpr_mem_pnpr m1 R1 CA c (mc_tbl c)) in *.
  assert (EM2 : m2 = wchainS m1 SP [(-72, 8%nat, CA); (-64, 8%nat, CA + 80 * c); (-56, 8%nat, 277592)]).
  { unfold m2, OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_q1.AXF_qnprz.qnpr_mem_pnpr. rewrite HSP1, V18, V19, ?sub_add_lit. reflexivity. }
  clearbody m2.
  assert (HSP3 : bv_unsigned (getr R2 (Z_to_bv 5 (Z.of_nat 2))) = SP - 80) by (rewrite C2, HSP1, u_wa_small by (zlh HZ); ring).
  assert (G2 : mem_grows m m2).
  { rewrite EM2. exact (mem_grows_trans m m1 _ G1 (wchainS_grows _ m1 SP)). }
  assert (F12 : forall x, 0 <= x < 2^64 -> ~ (SP - 2048 <= x < SP + 16) -> ~ (CA <= x < CA + 4096) -> m2 (wa x) = m (wa x)).
  { intros x Hx Q1 Q2. rewrite EM2.
    rewrite (wchainS_frame_in [(-72, 8%nat, CA); (-64, 8%nat, CA + 80 * c); (-56, 8%nat, 277592)] m1 SP (-72) (-48)); [| clear - HZ; lia | clear - HZ; lia | reflexivity | reflexivity | clear - Hx; lia | clear - HZ Q1; lia]. apply F1; clear - HZ Hx Q1; lia. }
  (* [comment removed for export] *)
  regzH C8. regzH C9.
  assert (V38 : bv_unsigned (getr R2 (Z_to_bv 5 (Z.of_nat 8))) = CA + 80 * c) by (rewrite C8, u_wa_small by (zlh HZ); reflexivity).
  assert (V39 : bv_unsigned (getr R2 (Z_to_bv 5 (Z.of_nat 9))) = n) by (rewrite C9, u_wa_small by (zlh Hn); reflexivity).
  assert (V318 : bv_unsigned (getr R2 (Z_to_bv 5 (Z.of_nat 18))) = mp) by (rewrite (KK2 18%nat ltac:(cbn; memb')), A18, u_wa_small by (zlh HZ); reflexivity).
  assert (V319 : bv_unsigned (getr R2 (Z_to_bv 5 (Z.of_nat 19))) = QC) by (rewrite (KK2 19%nat ltac:(cbn; memb')), A19, u_wa_small by (zlh HZ); reflexivity).
  assert (V320 : bv_unsigned (getr R2 (Z_to_bv 5 (Z.of_nat 20))) = v12) by (rewrite (KK2 20%nat ltac:(cbn; memb')), A20; apply u_wa_small; unfold v12; pose proof (u_rng64 (getr regs (Z_to_bv 5 (Z.of_nat 12)))); lia).
  assert (W21 : bv_unsigned (getr R2 (Z_to_bv 5 (Z.of_nat 21))) = fsz) by (rewrite (KK2 21%nat ltac:(cbn; memb')), A21, u_wa_small by (zlh HZ); reflexivity).
  assert (W22 : getr R2 (Z_to_bv 5 (Z.of_nat 22)) = getr regs (Z_to_bv 5 (Z.of_nat 22))) by (rewrite (KK2 22%nat ltac:(cbn; memb')), (KK0 22%nat ltac:(cbn; memb')); reflexivity).
  assert (W23 : getr R2 (Z_to_bv 5 (Z.of_nat 23)) = getr regs (Z_to_bv 5 (Z.of_nat 23))) by (rewrite (KK2 23%nat ltac:(cbn; memb')), (KK0 23%nat ltac:(cbn; memb')); reflexivity).
  assert (W24 : getr R2 (Z_to_bv 5 (Z.of_nat 24)) = getr regs (Z_to_bv 5 (Z.of_nat 24))) by (rewrite (KK2 24%nat ltac:(cbn; memb')), (KK0 24%nat ltac:(cbn; memb')); reflexivity).
  assert (W25 : getr R2 (Z_to_bv 5 (Z.of_nat 25)) = getr regs (Z_to_bv 5 (Z.of_nat 25))) by (rewrite (KK2 25%nat ltac:(cbn; memb')), (KK0 25%nat ltac:(cbn; memb')); reflexivity).
  assert (W26 : getr R2 (Z_to_bv 5 (Z.of_nat 26)) = getr regs (Z_to_bv 5 (Z.of_nat 26))) by (rewrite (KK2 26%nat ltac:(cbn; memb')), (KK0 26%nat ltac:(cbn; memb')); reflexivity).
  assert (W27 : getr R2 (Z_to_bv 5 (Z.of_nat 27)) = getr regs (Z_to_bv 5 (Z.of_nat 27))) by (rewrite (KK2 27%nat ltac:(cbn; memb')), (KK0 27%nat ltac:(cbn; memb')); reflexivity).
  destruct (gsz_rng c ltac:((zlh HZ))) as (Hsz1 & Hsz2 & Hsz3).
  assert (STEP : exists R4 m3, msteps SEGS (mkst R2 (wa 0x44474) m2 rom) (mkst R4 (wa 0x7db90) m3 rom) /\
     m3 = wchainS (wbytes (wchainS m2 SP (qL2a c CA n mp QC v12 fsz (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 22)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 23)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 24)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 25)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 26)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 27))))))
                               (wa (SB + 137438953472 + 128 * c)) (word_to_le_bytes 8 (wa 1152921504606846976)))
                             SP [(-272, 8%nat, n); (-264, 8%nat, CA + 80 * c + 16); (-256, 8%nat, SB + 4294967296 * c + 3758096384); (-248, 8%nat, 2305843009213693952);
                                 (-240, 8%nat, SB + 137438953472 + 128 * c + 8); (-232, 8%nat, 923480); (-224, 8%nat, SB + 137438953472 + 128 * c); (-216, 8%nat, 280564)] /\
     getr R4 1 = wa 280928 /\ getr R4 2 = wa (SP - 272) /\ getr R4 8 = wa (SB + 137438953472 + 128 * c) /\ getr R4 9 = wa (CA + 2560) /\
     getr R4 11 = wa (SB + 4294967296 * c) /\ getr R4 12 = wa 262144 /\ getr R4 13 = wa 96458 /\ getr R4 18 = wa (SB + 4294967296 * c) /\
     getr R4 19 = wa 262144 /\ getr R4 20 = wa (SB + 4294967296 * c) /\ getr R4 21 = wa (sz_tbl c) /\ getr R4 22 = wa 923480 /\
     (forall k, In k [3; 4; 26; 27; 28; 29; 30; 31]%nat -> getr R4 (Z_to_bv 5 (Z.of_nat k)) = getr R2 (Z_to_bv 5 (Z.of_nat k)))).
  { destruct (Z.le_gt_cases c 16) as [Hsm|Hbg].
    - (* [comment removed for export] *) exfalso. clear - Hsm HZ. lia.
    - (* [comment removed for export] *)
      assert (Hn1 : n = 1) by (destruct Hn as [_ Hn2]; rewrite (gmc_big c ltac:(clear - Hbg HZ; lia)) in Hn2; lia).
      assert (P3 : OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_gp.AXF_gng0pbz.gng0pb_pre R2 m2 CA c n SB (SB + 137438953472)).
      { constructor; [exact C10 | exact C11 | exact C12 | exact C13 | (rewrite <- Hn1; exact C14)
                     | (replace (getr R2 2) with (wa (SP - 80)) by (regzG; rewrite C2, HSP1; f_equal; ring);
                        apply (stk_ok_move m2 SP (SP - 80) 1024); [(zlh HZ) | (zlh HZ) | exact (stk_ok_grows m m2 (wa SP) 2048 G2 HSTK) | (zlh HZ) | (zlh HZ) | (zlh HZ)])
                     | (zlh HZ) | (clear - Hbg HZ; lia) | (zlh Hn) | (zlh HZ) | (zlh HZ) | (zlh HZ)
                     | rewrite HSP3; (zlh HZ) | (zlh HZ) | (zlh HZ) | | | | | | | | | | ].
        all: rewrite ?(ri_comm c SB), ?Z.add_0_r.
        all: first [ (apply (rd_frame m m2); [(zlh HZ) | lenq; (zlh HZ) | intros x Hx; znq; apply F12; clear - HZ Hx; lia | assumption])
                   | (intros d k Hd Hk; apply (store_ok_mono SEGS k m m2 _ G2); apply Iwri; clear - HZ Hd Hk; lia) ]. }
      destruct (OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_gp.AXF_gng0pbz.gng0pb_png0pb R2 m2 rom CA c n SB (SB + 137438953472) P3
                  (sc_gng0pb R2 m2 (SP - 80) HSP3 CA c n SB (SB + 137438953472) ltac:(unfold gp_ok; clear - HZ Hn; lia) ltac:(clear - Hbg HZ; lia) ltac:(zlh Hn)))
        as (R4 & Hms4 & E1 & E2 & _ & _ & _ & E8 & E9 & _ & E11 & E12 & E13 & _ & _ & _ & _ & E18 & E19 & E20 & E21 & E22 & _ & _ & _ & KK4).
      fold BIGSZ_E in E21. rewrite (bigsz_eval R2 (OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_gp.AXF_gng0pbz.VALS_gng0pb CA c n SB (SB + 137438953472)) c eq_refl ltac:(clear - Hbg HZ; lia)) in E21.
      exists R4, (OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_gp.AXF_gng0pbz.gng0pb_mem_png0pb m2 R2 CA c n SB (SB + 137438953472)). split; [exact Hms4|]. split.
      { unfold OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_gp.AXF_gng0pbz.gng0pb_mem_png0pb, L2a. rewrite HSP3, V38, V39, V318, V319, V320, W21, W22, W23, W24, W25, W26, W27, ?(ri_comm c SB), ?(rb_comm c SB), ?sub_add_lit, ?Z.add_0_r, ?Hn1. reflexivity. }
      regzH E2. replace (128 * c + (SB + 137438953472)) with (SB + 137438953472 + 128 * c) in E8 by ring.
      replace (4294967296 * c + SB) with (SB + 4294967296 * c) in E11, E18, E20 by ring.
      repeat split; try assumption. regzG. rewrite E2, HSP3. f_equal. ring. }
  destruct STEP as (R4 & m3 & Hms4 & EM3 & E1 & E2 & E8 & E9 & E11 & E12 & E13 & E18 & E19 & E20 & E21 & E22 & KK4).
  pose proof (msteps_trans SEGS _ _ _ Hms Hms4) as Hms'. clear Hms Hms4. rename Hms' into Hms.
  assert (G3 : mem_grows m m3).
  { rewrite EM3. exact (mem_grows_trans _ _ _ G2 (mem_grows_trans _ _ _ (wchainS_grows (qL2a c CA n mp QC v12 fsz (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 22)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 23)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 24)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 25)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 26)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 27))))) m2 SP)
                          (mem_grows_trans _ _ _ (wbytes_grows _ _ _) (wchainS_grows _ _ SP)))). }
  assert (F13 : forall x, 0 <= x < 2^64 -> ~ (SP - 2048 <= x < SP + 16) -> ~ (CA <= x < CA + 4096) -> ~ (SB + 137438953472 + 128 * c <= x < SB + 137438953472 + 128 * c + 8) ->
                  m3 (wa x) = m (wa x)).
  { intros x Hx Q1 Q2 Q3. rewrite EM3.
    rewrite (wchainS_frame_in [(-272, 8%nat, n); (-264, 8%nat, CA + 80 * c + 16); (-256, 8%nat, SB + 4294967296 * c + 3758096384); (-248, 8%nat, 2305843009213693952);
                                 (-240, 8%nat, SB + 137438953472 + 128 * c + 8); (-232, 8%nat, 923480); (-224, 8%nat, SB + 137438953472 + 128 * c); (-216, 8%nat, 280564)] _ SP (-272) (-208));
      [| clear - HZ; lia | clear - HZ; lia | reflexivity | reflexivity | clear - Hx; lia | clear - HZ Q1; lia].
    rewrite wb_other by first [exact Hx | (lenq'; clear - HZ Hn; lia) | (lenq'; clear - HZ Hn Q3; lia)].
    rewrite (wchainS_frame_in (qL2a c CA n mp QC v12 fsz (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 22)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 23)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 24)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 25)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 26)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 27))))) m2 SP (-184) (-80));
      [| clear - HZ; lia | clear - HZ; lia | reflexivity | reflexivity | clear - Hx; lia | clear - HZ Q1; lia].
    apply F12; assumption. }
  (* [comment removed for export] *)
  regzH E2. regzH E8. regzH E9. regzH E11. regzH E12. regzH E13. regzH E18. regzH E19. regzH E20. regzH E21. regzH E22. regzH E1.
  assert (HSP4 : bv_unsigned (getr R4 (Z_to_bv 5 (Z.of_nat 2))) = SP - 272) by (rewrite E2, u_wa_small by (zlh HZ); reflexivity).
  assert (P4 : AXF_mf0z.mf0_pre R4 m3 (SB + 4294967296 * c) 262144 96458 1534184).
  { constructor; [regzG; rewrite E11; reflexivity | regzG; exact E12 | regzG; exact E13
                 | (replace (getr R4 2) with (wa (SP - 272)) by (regzG; rewrite E2; reflexivity);
                    apply (stk_ok_move m3 SP (SP - 272) 1024); [(zlh HZ) | (zlh HZ) | exact (stk_ok_grows m m3 (wa SP) 2048 G3 HSTK) | (zlh HZ) | (zlh HZ) | (zlh HZ)])
                 | (zlh HZ) | (zlh HZ) | (zlh HZ) | (zlh HZ) | (zlh HZ) | (zlh HZ) | rewrite HSP4; (zlh HZ) | | | | ].
    all: apply (rd_frame m m3); [(zlh HZ) | lenq; (zlh HZ) | intros x Hx; znq; apply F13; clear - HZ Hx; lia | assumption]. }
  destruct (AXF_mf0z.mf0_pmf0 R4 m3 rom (SB + 4294967296 * c) 262144 96458 1534184 P4
              (sc_mf0 R4 m3 (SP - 272) (SB + 4294967296 * c) 262144 96458 1534184 HSP4 ltac:((zlh HZ))))
    as (R5 & Hms5 & F1' & F2' & F8 & F9 & F10 & F11 & F12' & F13' & F14 & F15 & F17 & F18 & F19 & F20 & KK5).
  clear P4.
  pose proof (msteps_trans SEGS _ _ _ Hms Hms5) as Hms'. clear Hms Hms5. rename Hms' into Hms.
  assert (EM4 : AXF_mf0z.mf0_mem_pmf0 m3 R4 (SB + 4294967296 * c) 262144 96458 1534184 =
                wchainS m3 SP [(-456, 8%nat, sz_tbl c); (-448, 8%nat, 1525856); (-440, 8%nat, 96458); (-432, 8%nat, SB + 4294967296 * c); (-424, 8%nat, 1);
                               (-416, 8%nat, 262144); (-408, 8%nat, 481768); (-400, 4%nat, 50); (-352, 8%nat, SB + 4294967296 * c); (-344, 8%nat, 262144);
                               (-336, 8%nat, SB + 4294967296 * c); (-328, 8%nat, SB + 4294967296 * c); (-320, 8%nat, 262144); (-312, 8%nat, 515004);
                               (-304, 8%nat, SB + 4294967296 * c); (-296, 8%nat, CA + 2560); (-288, 8%nat, SB + 137438953472 + 128 * c); (-280, 8%nat, 280928)]).
  { unfold AXF_mf0z.mf0_mem_pmf0. rewrite HSP4, E1, E8, E9, E18, E19, E20, E21, ?u_wa_small by (first [(zlh HZ) | (zlh Hsz1)]). rewrite ?sub_add_lit. reflexivity. }
  rewrite EM4 in Hms. clear EM4.
  eexists R5, _. split; [exact Hms|].
  split; [regzH F1'; exact F1'|]. split; [regzH F2'; rewrite F2', HSP4; f_equal; ring|].
  split; [regzH F8; exact F8|]. split; [regzH F10; exact F10|]. split; [regzH F11; exact F11|]. split; [regzH F12'; exact F12'|].
  split; [regzH F13'; exact F13'|]. split; [regzH F14; exact F14|]. split; [regzH F15; exact F15|]. split; [regzH F17; exact F17|].
  split; [rewrite (KK5 21%nat ltac:(cbn; memb')), E21; reflexivity|].
  split; [rewrite (KK5 22%nat ltac:(cbn; memb')); exact E22|].
  split; [intros k Hk; cbn in Hk; destruct Hk as [<-|[<-|[]]]; lazymatch goal with |- getr R5 (Z_to_bv 5 (Z.of_nat ?k)) = _ => rewrite (KK5 k ltac:(cbn; memb')), (KK4 k ltac:(cbn; memb')), (KK2 k ltac:(cbn; memb')), (KK0 k ltac:(cbn; memb')); reflexivity end|].
  rewrite EM3, EM2, EM1. unfold qmAd, gL3a. rewrite <- wchainS_app. unfold qL1a. rewrite <- wchainS_app. reflexivity.
Qed.
End QSB.
End AXG_qf2b.


Module AXG_qf5.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AxAsan AXG_put AXG_put2 AXG_np AXG_np2 AXG_np3 AXG_np4 AXG_nf1.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_nf2.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_nf2.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_np2.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AxAsan OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_put OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_put2 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_np OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_np2 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_np3 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_np4 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_nf1 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_nf2.AXG_nfsc OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_nf2 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_np2.AXG_pfl.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_npscp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_nf2.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_npscp OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_nf2.AXG_nfscp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_gp AXG_gp2 AXG_gf1 AXG_q1.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_q3.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_q3.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_gp OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_gp2 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_gf1 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_q1 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_q3.AXG_q2 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_q3.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_gp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_gp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_q1.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_q1.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Asan.M.loaded_segments.
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

Section QSC2.
Context {fx : FPState}.
Variable rom : word -> option byte.
Variables (m : word -> option byte) (R : bvmap 5 word) (QC CA c SB SP na st fsz mp mx stk v8 v18 v19 v20 v21 g23 g24 g25 g26 g27 : Z).
Hypothesis Hc24 : c = 24.
Hypothesis HSP : 2^46 + 4096 <= SP <= 2^47 /\ SP mod 16 = 0.
Hypothesis HSP16 : SP + 16 <= 2^47.
Hypothesis HCA : ((4304 <= CA /\ CA + 3888 <= 65536) \/ 6529232 <= CA) /\ CA mod 16 = 0 /\ CA + 4096 <= SP - 2048.
Hypothesis HSB : 17594333495296 <= SB /\ SB mod 4096 = 0 /\ SB + 137438953472 + 4096 <= SP - 2048.
Hypothesis HSEP : CA + 2592 <= SB \/ SB + 137438953472 + 4096 <= CA.
Hypothesis HQC : QC = CA - 128.
Hypothesis HSEPQ : CA + 2592 <= SB \/ SB + 137438953472 + 4096 <= QC.
Hypothesis Hvals : 0 <= na < 2^64 /\ 0 <= st < 2^64.
Hypothesis Hfm : 0 <= fsz <= 2^40 /\ 0 <= mp < 2^64 /\ 0 <= mx < 2^62 /\ fsz + 8192 <= mx.
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
Hypothesis Q56 : rd m (SP - 216) 8 280564.
Hypothesis Q48 : rd m (SP - 224) 8 (SB + 137438953472 + 128 * c).
Hypothesis Q40 : rd m (SP - 232) 8 923480.
Hypothesis Q32 : rd m (SP - 240) 8 (SB + 137438953472 + 128 * c + 8).
Hypothesis Q24 : rd m (SP - 248) 8 2305843009213693952.
Hypothesis Q16 : rd m (SP - 256) 8 (SB + 4294967296 * c + 3758096384).
Hypothesis Q8 : rd m (SP - 264) 8 (CA + 80 * c + 16).
Hypothesis Q0 : rd m (SP - 272) 8 (mc_tbl c / 2).
(* [comment removed for export] *)
Hypothesis G120 : rd m (SP - 88) 8 279672.
Hypothesis G112 : rd m (SP - 96) 8 (CA + 80 * c).
Hypothesis G104 : rd m (SP - 104) 8 (mc_tbl c / 2).
Hypothesis G96 : rd m (SP - 112) 8 mp.
Hypothesis G88 : rd m (SP - 120) 8 QC.
Hypothesis G80 : rd m (SP - 128) 8 stk.
Hypothesis G72 : rd m (SP - 136) 8 fsz.
Hypothesis G64 : rd m (SP - 144) 8 mx.
Hypothesis G56 : rd m (SP - 152) 8 g23.
Hypothesis G48 : rd m (SP - 160) 8 g24.
Hypothesis G40 : rd m (SP - 168) 8 g25.
Hypothesis G32 : rd m (SP - 176) 8 g26.
Hypothesis G24 : rd m (SP - 184) 8 g27.
Hypothesis C136 : rd m (SP - 72) 8 CA.
Hypothesis C144 : rd m (SP - 64) 8 (CA + 80 * c).
Hypothesis C152 : rd m (SP - 56) 8 277592.
Hypothesis C168 : rd m (SP - 40) 8 v21.
Hypothesis C176 : rd m (SP - 32) 8 v20.
Hypothesis C184 : rd m (SP - 24) 8 v19.
Hypothesis C192 : rd m (SP - 16) 8 v18.
Hypothesis C200 : rd m (SP - 8) 8 QC.
Hypothesis C208 : rd m SP 8 v8.
Hypothesis C216 : rd m (SP + 8) 8 277240.
Hypothesis Hgv : (0 <= g23 < 2^64 /\ 0 <= g24 < 2^64 /\ 0 <= g25 < 2^64 /\ 0 <= g26 < 2^64 /\ 0 <= g27 < 2^64) /\
                 (0 <= stk < 2^64 /\ 0 <= v8 < 2^64 /\ 0 <= v18 < 2^64 /\ 0 <= v19 < 2^64 /\ 0 <= v20 < 2^64 /\ 0 <= v21 < 2^64).
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
Hypothesis ISB : rd m 923512 8 SB.
Hypothesis IRIB : rd m 923528 8 (SB + 137438953472).
Hypothesis Ist : rd m (CA + 2576) 8 st.
Hypothesis Iwfa : wr m (SB + 4294967296 * c + 3758096384) 262144.
Hypothesis HIMG : forall i, 65536 <= i < 143360 -> m (Z_to_bv 64 i) = None.

(* [comment removed for export] *)
Hypothesis Rq0 : rd m QC 8 0.
Hypothesis Rqb : rd m (QC + 24) 8 0.
Hypothesis Hwq : wr m QC 32.
Hypothesis Hwb : wr m (SB + 4294967296 * c) 8192.

#[using="na st stk Hc24 HSP HSP16 HCA HSB HSEP HQC HSEPQ Hvals Hfm R2 R8 R10 R11 R12 R13 R19 R21 HSTK Q56 Q48 Q40 Q32 Q24 Q16 Q8 Q0 G120 G112 G104 G96 G88 G80 G72 G64 G56 G48 G40 G32 G24 C136 C144 C152 C168 C176 C184 C192 C200 C208 C216 Hgv Imu Inf0 Iau Iau40 Imapu Imeta Ina Iwri Imc Isz Iwc ISB IRIB Ist Iwfa HIMG Rq0 Rqb Hwq Hwb"] Lemma qsegC2 : exists R' m', msteps SEGS (mkst R (wa 0x449fc) m rom) (mkst R' (wa 0x43a30) m' rom) /\
  getr R' (Z_to_bv 5 (Z.of_nat 2)) = wa (SP + 16) /\
  getr R' (Z_to_bv 5 (Z.of_nat 1)) = wa 277240 /\ getr R' (Z_to_bv 5 (Z.of_nat 8)) = wa v8 /\ getr R' (Z_to_bv 5 (Z.of_nat 9)) = wa QC /\
  getr R' (Z_to_bv 5 (Z.of_nat 18)) = wa v18 /\ getr R' (Z_to_bv 5 (Z.of_nat 19)) = wa v19 /\ getr R' (Z_to_bv 5 (Z.of_nat 20)) = wa v20 /\
  getr R' (Z_to_bv 5 (Z.of_nat 21)) = wa v21 /\ getr R' (Z_to_bv 5 (Z.of_nat 22)) = wa mx /\ getr R' (Z_to_bv 5 (Z.of_nat 23)) = wa g23 /\
  getr R' (Z_to_bv 5 (Z.of_nat 24)) = wa g24 /\ getr R' (Z_to_bv 5 (Z.of_nat 25)) = wa g25 /\ getr R' (Z_to_bv 5 (Z.of_nat 26)) = wa g26 /\
  getr R' (Z_to_bv 5 (Z.of_nat 27)) = wa g27 /\
  (forall k, In k [3; 4]%nat -> getr R' (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k))) /\
  q_inv m' QC SB 0 1 (fsz + 8192) /\
  INV_G m' CA SB c (sz_tbl c) (mc_tbl c / 2) (262144 / (sz_tbl c)) 1 /\
  rd m' (SB + 4294967296 * c) 8 0 /\ rd m' (SB + 4294967296 * c + 24) 8 mp /\
  (forall x, 0 <= x < 2^64 -> ~ (SB + 4294967296 * c + 3758096384 <= x < SB + 4294967296 * c + 3758096384 + 262144) ->
     ~ owned_C CA SB c x -> ~ (QC <= x < QC + 32) -> ~ (SB + 4294967296 * c <= x < SB + 4294967296 * c + 32) -> m' (wa x) = m (wa x)) /\ mem_grows m m'.
Proof. LiaFast.lf_pins (fun (na st stk Hc24 HSP HSP16 HCA HSB HSEP HQC HSEPQ Hvals Hfm R2 R8 R10 R11 R12 R13 R19 R21 HSTK Q56 Q48 Q40 Q32 Q24 Q16 Q8 Q0 G120 G112 G104 G96 G88 G80 G72 G64 G56 G48 G40 G32 G24 C136 C144 C152 C168 C176 C184 C192 C200 C208 C216 Hgv Imu Inf0 Iau Iau40 Imapu Imeta Ina Iwri Imc Isz Iwc ISB IRIB Ist Iwfa HIMG Rq0 Rqb Hwq Hwb : LiaFast.U) => LiaFast.u0).
  assert (Hcr5 : 1 <= c <= 30) by (clear - Hc24; lia).
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
  assert (HZ : 2^46 + 4096 <= SP <= 2^47 /\ 1 <= c <= 30 /\ ((4304 <= CA /\ CA + 3888 <= 65536) \/ 6529232 <= CA) /\ CA mod 16 = 0 /\ CA + 4096 <= SP - 2048 /\
               17594333495296 <= SB /\ SB mod 4096 = 0 /\ SB + 137438953472 + 4096 <= SP - 2048 /\
               (CA + 2592 <= SB \/ SB + 137438953472 + 4096 <= CA) /\
               RB = SB + 4294967296 * c /\ RI = SB + 137438953472 + 128 * c /\ FA = RB + 3758096384 /\ REC = CA + 80 * c /\
               0 <= na < 2^64 /\ 0 <= st < 2^64 /\ 4 <= NEW <= 8192 /\ 32 <= sz_tbl c <= 65536 /\ 2 <= sz_tbl c / 16 <= 4096 /\ NEW * (sz_tbl c) <= 262144 /\ 1 <= nc <= 8 /\ nc <= NEW)
    by (clear - HSP Hcr5 HCA HSB HSEP Hvals HNEW Hnc Hncn Hsz1 HS16r; unfold FA, RB, RI, REC in *; lia).
  assert (HY : 2^46 + 4096 <= SP <= 2^47 /\ 1 <= c <= 30 /\ ((4304 <= CA /\ CA + 3888 <= 65536) \/ 6529232 <= CA) /\ CA + 4096 <= SP - 2048 /\
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
  assert (P2 : OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_gp.AXF_gpc2z.gpc2_pre Ra m1 RI (sz_tbl c / 16) NEW FA (REC + 16) nc).
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
  destruct (OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_gp.AXF_gpc2z.gpc2_ppc2 Ra m1 rom RI (sz_tbl c / 16) NEW FA (REC + 16) nc P2
              (sc_gpc2 Ra m1 (SP - 272) HSPb RI (sz_tbl c / 16) NEW FA (REC + 16) nc V13 ltac:(rewrite HS16; (zlh HZ))))
    as (Rb & Hms2 & B1 & B2 & B8 & B9 & B10 & B11 & B13 & B14 & B15 & B18 & B19 & B20 & B21 & B22 & KKb).
  clear P2 B1 B9 B10 B15 B18 B21 B22.
  pose proof (msteps_trans SEGS _ _ _ Hms Hms2) as Hms'. clear Hms Hms2. rename Hms' into Hms.
  set (m2 := OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_gp.AXF_gpc2z.gpc2_mem_ppc2 m1 Ra RI (sz_tbl c / 16) NEW FA (REC + 16) nc) in *.
  assert (EM2 : m2 = wbytes (wbytes (wbytes (wbytes m1 (wa (RI + 16)) (word_to_le_bytes 8 (wa NEW))) (wa (RI + 32)) (word_to_le_bytes 8 (wa (NEW * (sz_tbl c)))))
                        (wa (RI + 68)) (word_to_le_bytes 1 (wa 0))) (wa (RI + 16)) (word_to_le_bytes 8 (wa (NEW + -1 * nc)))).
  { unfold m2, OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_gp.AXF_gpc2z.gpc2_mem_ppc2. rewrite V13, Z.add_0_l, ?HS16. reflexivity. }
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
  assert (Esz : sz_tbl c = 8192) by (rewrite Hc24; reflexivity).
  assert (HQ : 2^46 + 4096 <= SP /\ SP + 16 <= 2^47 /\ c = 24 /\ QC = CA - 128 /\ ((4304 <= CA /\ CA + 3888 <= 65536) \/ 6529232 <= CA) /\ CA + 4096 <= SP - 2048 /\
               17594333495296 <= SB /\ SB mod 4096 = 0 /\ SB + 137438953472 + 4096 <= SP - 2048 /\ (CA + 2592 <= SB \/ SB + 137438953472 + 4096 <= QC) /\
               RB = SB + 4294967296 * c /\ RI = SB + 137438953472 + 128 * c /\ FA = RB + 3758096384 /\ REC = CA + 80 * c /\
               0 <= na < 2^64 /\ 0 <= st < 2^64 /\ 1 <= nc <= 8 /\ 0 <= fsz <= 2^40 /\ 0 <= mp < 2^64 /\ 0 <= mx < 2^62 /\ fsz + 8192 <= mx)
    by (clear - HY HSP16 Hc24 HQC HSEPQ Hfm HZ; lia).
  assert (FW3q : forall x, SP - 2048 <= x < SP + 16 -> m3 (wa x) = m (wa x)) by (intros x Hx; apply F13; clear - HOB HSP16 Hx; lia).
  assert (SL : forall a v, SP - 2048 <= a -> a + 8 <= SP + 16 -> rd m a 8 v -> rd m3 a 8 v).
  { intros a v Ha1 Ha2 Hr. apply (rd_frame m m3); [clear - HS Ha1; lia | lenq'; clear - HS HSP16 Ha2; lia | intros x Hx; lenq'; apply FW3q; clear - Ha1 Ha2 Hx; lia | exact Hr]. }
  assert (P4 : OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_q1.AXF_qngtz.qngt_pre Rc m3 CA QC nc SB (SB + 137438953472) na 0 (sz_tbl c) st 0 fsz mp mx stk g23 g24 g25 g26 g27 v8 v18 v19 v20 v21).
  { constructor.
    all: try (clear - Hgv; lia).
    all: try (zlh HQ).
    all: try (zlh HZ).
    all: try (rewrite HSPd; (zlh HS)).
    all: try (rewrite Esz; clear; lia).
    - regzG. rewrite (KKc 8%nat ltac:(cbn; memb')), B8. f_equal. (zlh HQ).
    - regzG. rewrite (KKc 14%nat ltac:(cbn; memb')). exact B14.
    - regzG. rewrite (KKc 19%nat ltac:(cbn; memb')). exact B19.
    - replace (getr Rc 2) with (wa (SP - 208)) by (regzG; rewrite (KKc 2%nat ltac:(cbn; memb')), B2, HSPb; f_equal; ring).
      apply (stk_ok_move m3 SP (SP - 208) 1024); [(zlh HY) | (zlh HY) | exact (stk_ok_grows m m3 (wa SP) 2048 G13 HSTK) | (zlh HY) | (zlh HY) | (zlh HY)].
    - replace (SB + 137438953472 + 3144) with (RI + 72) by (zlh HQ).
      apply (rd_frame m m3); [(zlh HY) | lenq'; (zlh HY) | intros x Hx; lenq'; apply F13; clear - HY Hx; lia | exact Ina].
    - intros d k Hd Hk. apply (store_ok_mono SEGS k m m3 _ G13). replace (SB + 137438953472 + 3144 + d) with (RI + (72 + d)) by (zlh HQ). apply Iwri; clear - Hd Hk; lia.
    - replace (SB + 137438953472 + 3072) with RI by (zlh HQ).
      apply (rd_frame m m3); [(zlh HY) | lenq'; (zlh HY) | intros x Hx; lenq'; apply F13; clear - HY Hx; lia | exact Imu].
    - intros d k Hd Hk. apply (store_ok_mono SEGS k m m3 _ G13). replace (SB + 137438953472 + 3072 + d) with (RI + d) by (zlh HQ). apply Iwri; clear - Hd Hk; lia.
    - rewrite HSPd. replace (SP - 208 + 120) with (SP - 88) by ring. apply SL; [clear; lia | clear; lia | exact G120].
    - rewrite HSPd. replace (SP - 208 + 112) with (SP - 96) by ring. replace (CA + 1920) with (CA + 80 * c) by (zlh HQ). apply SL; [clear; lia | clear; lia | exact G112].
    - rewrite HSPd. replace (SP - 208 + 104) with (SP - 104) by ring. apply SL; [clear; lia | clear; lia | exact G104].
    - rewrite HSPd. replace (SP - 208 + 96) with (SP - 112) by ring. apply SL; [clear; lia | clear; lia | exact G96].
    - rewrite HSPd. replace (SP - 208 + 88) with (SP - 120) by ring. apply SL; [clear; lia | clear; lia | exact G88].
    - rewrite HSPd. replace (SP - 208 + 80) with (SP - 128) by ring. apply SL; [clear; lia | clear; lia | exact G80].
    - rewrite HSPd. replace (SP - 208 + 72) with (SP - 136) by ring. apply SL; [clear; lia | clear; lia | exact G72].
    - rewrite HSPd. replace (SP - 208 + 64) with (SP - 144) by ring. apply SL; [clear; lia | clear; lia | exact G64].
    - rewrite HSPd. replace (SP - 208 + 56) with (SP - 152) by ring. apply SL; [clear; lia | clear; lia | exact G56].
    - rewrite HSPd. replace (SP - 208 + 48) with (SP - 160) by ring. apply SL; [clear; lia | clear; lia | exact G48].
    - rewrite HSPd. replace (SP - 208 + 40) with (SP - 168) by ring. apply SL; [clear; lia | clear; lia | exact G40].
    - rewrite HSPd. replace (SP - 208 + 32) with (SP - 176) by ring. apply SL; [clear; lia | clear; lia | exact G32].
    - rewrite HSPd. replace (SP - 208 + 24) with (SP - 184) by ring. apply SL; [clear; lia | clear; lia | exact G24].
    - rewrite HSPd. replace (SP - 208 + 136) with (SP - 72) by ring. apply SL; [clear; lia | clear; lia | exact C136].
    - rewrite HSPd. replace (SP - 208 + 144) with (SP - 64) by ring. replace (CA + 1920) with (CA + 80 * c) by (zlh HQ). apply SL; [clear; lia | clear; lia | exact C144].
    - rewrite HSPd. replace (SP - 208 + 152) with (SP - 56) by ring. apply SL; [clear; lia | clear; lia | exact C152].
    - rewrite HSPd. replace (SP - 208 + 168) with (SP - 40) by ring. apply SL; [clear; lia | clear; lia | exact C168].
    - rewrite HSPd. replace (SP - 208 + 176) with (SP - 32) by ring. apply SL; [clear; lia | clear; lia | exact C176].
    - rewrite HSPd. replace (SP - 208 + 184) with (SP - 24) by ring. apply SL; [clear; lia | clear; lia | exact C184].
    - rewrite HSPd. replace (SP - 208 + 192) with (SP - 16) by ring. apply SL; [clear; lia | clear; lia | exact C192].
    - rewrite HSPd. replace (SP - 208 + 200) with (SP - 8) by ring. apply SL; [clear; lia | clear; lia | exact C200].
    - rewrite HSPd. replace (SP - 208 + 208) with SP by ring. apply SL; [clear; lia | clear; lia | exact C208].
    - rewrite HSPd. replace (SP - 208 + 216) with (SP + 8) by ring. apply SL; [clear; lia | clear; lia | exact C216].
    - intros d k Hd Hk. apply (store_ok_mono SEGS k m m3 _ G13). replace (CA + 1920 + d) with (CA + (80 * c + d)) by (zlh HQ). apply Iwc; clear - HY Hd Hk; lia.
    - replace (CA + 1928) with (CA + 80 * c + 8) by (zlh HQ). apply (rd_frame m m3); [(zlh HY) | lenq'; (zlh HY) | intros x Hx; lenq'; apply F13; clear - HY Hx; lia | exact Isz].
    - rewrite chp_off by (zlh HY). pose proof (RD3 (nc - 1) ltac:((zlh HY))) as R7.
      replace (REC + 16 + 4 * (nc - 1)) with (CA + 4 * (nc - 1) + 1936) in R7 by (zlh HQ).
      replace ((nc - 1 - (nc - 1)) * (sz_tbl c / 16)) with 0 in R7 by ring. exact R7.
    - apply (rd_frame m m3); [(zlh HY) | lenq'; (zlh HY) | intros x Hx; lenq'; apply F13; clear - HY Hx; lia | exact ISB].
    - apply (rd_frame m m3); [(zlh HY) | lenq'; (zlh HY) | intros x Hx; lenq'; apply F13; clear - HY Hx; lia | exact Ist].
    - intros d k Hd Hk. apply (store_ok_mono SEGS k m m3 _ G13). replace (CA + 2576 + d) with (CA + (2576 + d)) by ring. apply Iwc; clear - HY Hd Hk; lia.
    - rewrite Z.add_0_r. apply (rd_frame m m3); [(zlh HQ) | lenq'; (zlh HQ) | intros x Hx; lenq'; apply F13; clear - HQ Hx; lia | exact Rq0].
    - apply (rd_frame m m3); [(zlh HQ) | lenq'; (zlh HQ) | intros x Hx; lenq'; apply F13; clear - HQ Hx; lia | exact Rqb].
    - intros d k Hd Hk. rewrite Z.add_0_r. apply (store_ok_mono SEGS k m m3 _ G13). apply Hwq; assumption.
    - intros d k Hd Hk. rewrite ext_Z_u32 by (clear; lia). apply (store_ok_mono SEGS k m m3 _ G13).
      replace (SB + 16 * 0 + 103079215104 + d) with (SB + 4294967296 * c + d) by (zlh HQ). apply Hwb; assumption.
    - intros i Hi. change (Z_to_bv 64 i) with (wa i). rewrite F13 by (clear - HY Hi; lia). apply HIMG. exact Hi. }
  destruct (OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_q1.AXF_qngtz.qngt_pngt Rc m3 rom CA QC nc SB (SB + 137438953472) na 0 (sz_tbl c) st 0 fsz mp mx stk g23 g24 g25 g26 g27 v8 v18 v19 v20 v21 P4
              (sc_qngt Rc m3 (SP - 208) HSPd CA QC nc SB (SB + 137438953472) na 0 (sz_tbl c) st 0 fsz mp mx stk g23 g24 g25 g26 g27 v8 v18 v19 v20 v21 ltac:((zlh HQ))))
    as (Rd & Hms5 & T1 & T2 & _ & _ & _ & T8 & T9 & _ & _ & _ & _ & _ & _ & _ & _ & T18 & T19 & T20 & T21 & T22 & T23 & T24 & T25 & T26 & T27 & _ & KKd).
  clear P4.
  pose proof (msteps_trans SEGS _ _ _ Hms Hms5) as Hms'. clear Hms Hms5. rename Hms' into Hms.
  set (m5 := m5q m3 RI REC CA nc na st RB fsz mp QC).
  assert (EM5 : OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_q1.AXF_qngtz.qngt_mem_pngt m3 Rc CA QC nc SB (SB + 137438953472) na 0 (sz_tbl c) st 0 fsz mp mx stk g23 g24 g25 g26 g27 v8 v18 v19 v20 v21 = m5).
  { unfold m5, m5q, OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_q1.AXF_qngtz.qngt_mem_pngt. rewrite ext_Z_lo32_small, ext_Z_u32 by (first [zlh HY | (clear; lia)]). rewrite ?addneg, Esz.
    replace (SB + 137438953472 + 3144) with (RI + 72) by (zlh HQ). replace (SB + 137438953472 + 3072) with RI by (zlh HQ).
    replace (CA + 1920) with REC by (zlh HQ).
    replace (SB + 16 * 0 + 103079215104) with RB by (zlh HQ). replace (SB + 16 * 0 + 103079215112) with (RB + 8) by (zlh HQ).
    replace (SB + 16 * 0 + 103079215120) with (RB + 16) by (zlh HQ). replace (SB + 16 * 0 + 103079215128) with (RB + 24) by (zlh HQ).
    replace (0 + fsz + 8192) with (fsz + 8192) by ring. reflexivity. }
  rewrite EM5 in Hms. clear EM5.
  set (m5a := m5c m3 RI REC CA nc na (sz_tbl c) st).
  assert (E5a : m5 = wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m5a (wa RB) (word_to_le_bytes 8 (wa 0))) (wa (RB + 8)) (word_to_le_bytes 8 (wa (fsz + 8192))))
                       (wa (RB + 16)) (word_to_le_bytes 8 (wa 1))) (wa (RB + 24)) (word_to_le_bytes 8 (wa mp))) (wa (QC + 8)) (word_to_le_bytes 8 (wa RB)))
                       (wa (QC + 0)) (word_to_le_bytes 8 (wa 1))) (wa (QC + 16)) (word_to_le_bytes 8 (wa RB))) (wa (QC + 24)) (word_to_le_bytes 8 (wa (fsz + 8192))))
    by (unfold m5, m5q, m5a, m5c; rewrite Esz; reflexivity).
  assert (G5a : mem_grows m m5a) by (exact (mem_grows_trans _ _ _ G13 (m5c_grows _ _ _ _ _ _ _ _))).
  assert (G5b : mem_grows m5a m5) by (rewrite E5a; do 8 apply grows_wb; apply mem_grows_refl).
  assert (G5 : mem_grows m m5) by (exact (mem_grows_trans _ _ _ G5a G5b)).
  assert (FXa : forall x, 0 <= x < 2^64 -> ~ (FA <= x < FA + 262144) -> ~ (RI <= x < RI + 128) -> ~ (REC <= x < REC + 80) -> ~ (CA + 2576 <= x < CA + 2584) ->
                  m5a (wa x) = m (wa x)).
  { intros x Hx Q1 Q2 Q3 Q4. unfold m5a.
    rewrite m5c_frame; [| clear - HOB; lia | clear - HOB; lia | clear - HOB; lia | clear - HOB; lia | clear - HOB; lia | clear - HOB; lia | exact Hx
                        | clear - Q2; lia | clear - Q2; lia | clear - Q3; lia | exact Q4].
    apply F13; [exact Hx | exact Q1 | clear - Q2; lia | clear - Q2; lia | clear - Q2; lia | clear - HOB Q3; lia]. }
  assert (FXb : forall x, 0 <= x < 2^64 -> ~ (RB <= x < RB + 32) -> ~ (QC <= x < QC + 32) -> m5 (wa x) = m5a (wa x)).
  { intros x Hx Q1 Q2. rewrite E5a. repeat (rewrite wb_other by first [exact Hx | (lenq'; zlh HQ) | (lenq'; clear - HQ Q1 Q2; lia)]). reflexivity. }
  destruct (m5c_rd m3 RI REC CA nc na (sz_tbl c) st ltac:((zlh HY)) ltac:((zlh HY)) ltac:((zlh HY)) ltac:((zlh HY)) ltac:((zlh HY)) ltac:((zlh HY)) ltac:((zlh HY)))
    as (Rc5 & Rmu5 & Rna5 & Rst5).
  fold m5a in Rc5, Rmu5, Rna5, Rst5.
  assert (IGa : INV_G m5a CA SB c (sz_tbl c) nc NEW 1).
  { constructor.
    - clear - HY HZ Hsz2 Hcr5 Hncn1. lia.
    - apply (rd_frame m m5a); [lia | lenq'; lia | intros x Hx; lenq'; apply FXa; clear - HY Hx; lia | exact ISB].
    - apply (rd_frame m m5a); [lia | lenq'; lia | intros x Hx; lenq'; apply FXa; clear - HY Hx; lia | exact IRIB].
    - rewrite cnt_of_1 by (zlh HY). exact Rc5.
    - replace (2 * nc) with (mc_tbl c) by (clear - Hnc; lia).
      apply (rd_frame m3 m5a); [(zlh HY) | lenq'; (zlh HY) | intros x Hx; lenq'; unfold m5a; apply m5c_frame; clear - HY Hx; lia |].
      apply (rd_frame m m3); [(zlh HY) | lenq'; (zlh HY) | intros x Hx; lenq'; apply F13; clear - HY Hx; lia | exact Imc].
    - apply (rd_frame m3 m5a); [(zlh HY) | lenq'; (zlh HY) | intros x Hx; lenq'; unfold m5a; apply m5c_frame; clear - HY Hx; lia |].
      apply (rd_frame m m3); [(zlh HY) | lenq'; (zlh HY) | intros x Hx; lenq'; apply F13; clear - HY Hx; lia | exact Isz].
    - intros i Hi. rewrite cnt_of_1 in Hi |- * by (zlh HY). replace (1 + (nc - 1) - 1 - i) with (nc - 1 - i) by ring.
      pose proof (RD3 i ltac:(clear - HY Hi; lia)) as Ri. cbv beta in Ri.
      apply (rd_frame m3 m5a); [clear - HY Hi; lia | lenq'; clear - HY Hi; lia | intros x Hx; lenq'; unfold m5a; apply m5c_frame; clear - HY Hi Hx; lia | exact Ri].
    - exact Rmu5.
    - rewrite b_of_1 by (zlh HY). replace (NEW - nc * 1) with (NEW + -1 * nc) by ring.
      apply (rd_frame m3 m5a); [(zlh HY) | lenq'; (zlh HY) | intros x Hx; lenq'; unfold m5a; apply m5c_frame; clear - HY Hx; lia |].
      apply (rd_frame m2 m3); [(zlh HY) | lenq'; (zlh HY) | intros x Hx; lenq'; apply F3; clear - HY Hx; lia | exact Rnf2].
    - exists ((nc + na) mod 2^64). split; [apply Z.mod_pos_bound; lia|]. unfold rd. rewrite (wa_eqm ((nc + na) mod 2^64) (nc + na)) by (apply Z.mod_mod; lia). exact Rna5.
    - intros k Hk. rewrite b_of_1 in Hk by (zlh HY).
      pose proof (RD1 (NEW - 1 - k) ltac:(clear - HY Hk; lia)) as Rf. rewrite Z.add_0_l, (gdiv16 _ c Hcr5) in Rf.
      replace (FA + 4 * (NEW - 1 - (NEW - 1 - k))) with (SB + c * 4294967296 + 3758096384 + 4 * k) in Rf by (unfold FA, RB; ring).
      apply (rd_frame m3 m5a); [clear - HY Hk; lia | lenq'; clear - HY Hk; lia | intros x Hx; lenq'; unfold m5a; apply m5c_frame; clear - HY Hk Hx; lia |].
      apply (rd_frame m2 m3); [clear - HY Hk; lia | lenq'; clear - HY Hk; lia | intros x Hx; lenq'; apply F3; clear - HY Hk Hx; lia |].
      apply (rd_frame m1 m2); [clear - HY Hk; lia | lenq'; clear - HY Hk; lia | | exact Rf].
      intros x Hx. lenq'. rewrite EM2. repeat (rewrite wb_other by first [(clear - HY Hk Hx; lia) | (lenq'; clear - HY; lia) | (lenq'; clear - HY Hk Hx; lia)]). reflexivity.
    - exists ((sz_tbl c + st) mod 2^64). split; [apply Z.mod_pos_bound; lia|]. unfold rd. rewrite (wa_eqm ((sz_tbl c + st) mod 2^64) (sz_tbl c + st)) by (apply Z.mod_mod; lia). exact Rst5.
    - intros d k Hd Hk. apply (store_ok_mono SEGS k m m5a _ G5a). replace (CA + 80 * c + d) with (CA + (80 * c + d)) by ring. apply Iwc; clear - HY Hd Hk; lia.
    - intros d k Hd Hk. apply (store_ok_mono SEGS k m m5a _ G5a). apply Iwri; assumption.
    - intros d k Hd Hk. apply (store_ok_mono SEGS k m m5a _ G5a). replace (CA + 2560 + d) with (CA + (2560 + d)) by ring. apply Iwc; clear - HY Hd Hk; lia. }
  exists Rd, m5. split; [exact Hms|].
  regzH T2. regzH T8. regzH T9. regzH T18. regzH T19. regzH T20. regzH T21. regzH T22. regzH T23. regzH T24. regzH T25. regzH T26. regzH T27. regzH T1.
  split; [rewrite T2, HSPd; f_equal; ring|].
  split; [exact T1|]. split; [exact T8|]. split; [exact T9|]. split; [exact T18|]. split; [exact T19|]. split; [exact T20|].
  split; [exact T21|]. split; [exact T22|]. split; [exact T23|]. split; [exact T24|]. split; [exact T25|]. split; [exact T26|]. split; [exact T27|].
  split.
  { intros k Hk. cbn [In] in Hk. destruct Hk as [<-|[<-|[]]].
    - rewrite (KKd 3%nat ltac:(cbn; memb')), (KKc 3%nat ltac:(cbn; memb')), (KKb 3%nat ltac:(cbn; memb')), (KKa 3%nat ltac:(cbn; memb')). reflexivity.
    - rewrite (KKd 4%nat ltac:(cbn; memb')), (KKc 4%nat ltac:(cbn; memb')), (KKb 4%nat ltac:(cbn; memb')), (KKa 4%nat ltac:(cbn; memb')). reflexivity. }
  split.
  { unfold q_inv. replace (SB + 103079215104 + 8192 * 0) with RB by (zlh HQ). split; [zlh HQ|]. split.
    { rewrite E5a. apply wb_rd_hit; [lia | zlh HQ | lenq'; zlh HQ]. }
    right. split; [lia|]. split; [lia|].
    split.
    { rewrite E5a. do 2 (apply wb_rd_other; [zlh HQ | lenq'; zlh HQ | zlh HQ | lenq'; zlh HQ | lenq'; zlh HQ|]).
      rewrite (Z.add_0_r QC). apply wb_rd_hit; [lia | zlh HQ | lenq'; zlh HQ]. }
    split.
    { rewrite E5a. do 3 (apply wb_rd_other; [zlh HQ | lenq'; zlh HQ | zlh HQ | lenq'; zlh HQ | lenq'; zlh HQ|]).
      apply wb_rd_hit; [lia | zlh HQ | lenq'; zlh HQ]. }
    split.
    { rewrite E5a. apply wb_rd_other; [zlh HQ | lenq'; zlh HQ | zlh HQ | lenq'; zlh HQ | lenq'; zlh HQ|].
      apply wb_rd_hit; [lia | zlh HQ | lenq'; zlh HQ]. }
    split.
    { rewrite E5a. do 6 (apply wb_rd_other; [zlh HQ | lenq'; zlh HQ | zlh HQ | lenq'; zlh HQ | lenq'; zlh HQ|]).
      apply wb_rd_hit; [lia | zlh HQ | lenq'; zlh HQ]. }
    split.
    { rewrite E5a. do 5 (apply wb_rd_other; [zlh HQ | lenq'; zlh HQ | zlh HQ | lenq'; zlh HQ | lenq'; zlh HQ|]).
      apply wb_rd_hit; [lia | zlh HQ | lenq'; zlh HQ]. }
    intros d k Hd Hk. apply (store_ok_mono SEGS k m m5 _ G5). replace (RB + d) with (SB + 4294967296 * c + d) by (zlh HQ). apply Hwb; assumption. }
  split.
  { apply (INV_G_frame m5a m5 CA SB c (sz_tbl c) nc NEW 1); [zlh HQ | zlh HQ | zlh HQ | zlh HQ | exact G5b | | exact IGa].
    intros x Hx. apply FXb; unfold foot_G in Hx; clear - HQ HY Hx; lia. }
  split.
  { rewrite E5a. do 7 (apply wb_rd_other; [zlh HQ | lenq'; zlh HQ | zlh HQ | lenq'; zlh HQ | lenq'; zlh HQ|]).
    apply wb_rd_hit; [lia | zlh HQ | lenq'; zlh HQ]. }
  split.
  { rewrite E5a. do 4 (apply wb_rd_other; [zlh HQ | lenq'; zlh HQ | zlh HQ | lenq'; zlh HQ | lenq'; zlh HQ|]).
    apply wb_rd_hit; [lia | zlh HQ | lenq'; zlh HQ]. }
  split; [|exact G5].
  intros x Hx Q1 Q2 Q3 Q4. unfold owned_C in Q2. fold RI REC in Q2. rewrite FXb by (first [exact Hx | exact Q4 | exact Q3]).
  apply FXa; [exact Hx | exact Q1 | | |]; clear - Q2; lia.
Qed.
End QSC2.
End AXG_qf5.

Import OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_gp OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_gp2 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_gf1 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_gf2b.AXG_gf2 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_gf2b OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_gf3 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_gf4 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_gf2b.AXG_gf5 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_q1 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_q3.AXG_q2 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_q3 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_qf6.AXG_qf2 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_qf6.AXG_qf2b OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_qf6.AXG_qf5.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Abbreviation SEGS := Asan.M.loaded_segments.

Lemma qmAc_frame : forall m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 v21 h18 h19 h20 g21 g22 g23 g24 g25 g26 g27 x,
  2^46 <= SP <= 2^47 -> 0 <= CA -> CA + 4096 <= 2^63 -> 0 <= RI -> RI + 128 <= 2^63 -> 0 <= x < 2^64 ->
  ~ (SP - 2048 <= x < SP + 16) -> ~ (CA <= x < CA + 2592) -> ~ (RI <= x < RI + 8) ->
  qmAc m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 v21 h18 h19 h20 g21 g22 g23 g24 g25 g26 g27 (wa x) = m (wa x).
Proof.
  intros m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 v21 h18 h19 h20 g21 g22 g23 g24 g25 g26 g27 x HSP H1 H2 H3 H4 Hx Q1 Q2 Q3. unfold qmAc.
  rewrite (wchainS_frame_in (gL3a c CA n RI RB FA) _ SP (-2048) 0); [| lia | lia | reflexivity | reflexivity | exact Hx | lia].
  rewrite wb_other; [| exact Hx | lia | rewrite length_N_to_le_bytes; lia | rewrite length_N_to_le_bytes; lia].
  rewrite (wchainS_frame_in (qL2a c CA n h18 h19 h20 g21 g22 g23 g24 g25 g26 g27) _ SP (-2048) 0); [| lia | lia | reflexivity | reflexivity | exact Hx | lia].
  rewrite ic_keep; [| lia | lia | exact Hx | intros i Hi; lia].
  rewrite (wchainS_frame_in (qL1a c CA v1 v8 v9 v18 v19 v20 v21) _ SP (-2048) 16); [| lia | lia | reflexivity | reflexivity | exact Hx | lia].
  reflexivity.
Qed.
Lemma qmAc_grows : forall m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 v21 h18 h19 h20 g21 g22 g23 g24 g25 g26 g27,
  mem_grows m (qmAc m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 v21 h18 h19 h20 g21 g22 g23 g24 g25 g26 g27).
Proof.
  intros. unfold qmAc.
  apply (mem_grows_trans _ _ _ (wchainS_grows (qL1a c CA v1 v8 v9 v18 v19 v20 v21) m SP)).
  apply (mem_grows_trans _ _ _ (ic_grows _ CA)).
  apply (mem_grows_trans _ _ _ (wchainS_grows (qL2a c CA n h18 h19 h20 g21 g22 g23 g24 g25 g26 g27) _ SP)).
  apply (mem_grows_trans _ (wbytes (wchainS (ic_mem (wchainS m SP (qL1a c CA v1 v8 v9 v18 v19 v20 v21)) CA) SP (qL2a c CA n h18 h19 h20 g21 g22 g23 g24 g25 g26 g27)) (wa RI) (word_to_le_bytes 8 (wa 1152921504606846976)))).
  - apply grows_wb. apply mem_grows_refl.
  - apply wchainS_grows.
Qed.

(* [comment removed for export] *)
Lemma qmAc_rd3 : forall m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 v21 h18 h19 h20 g21 g22 g23 g24 g25 g26 g27 k v,
  2^46 <= SP <= 2^47 -> wl_chk (gL3a c CA n RI RB FA) k 8 = Some v -> -2048 <= k -> k + 8 <= 0 ->
  rd (qmAc m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 v21 h18 h19 h20 g21 g22 g23 g24 g25 g26 g27) (SP + k) 8 v.
Proof. intros. unfold qmAc. apply rd_wchainS; [lia | lia | reflexivity | lia | cbn; lia | lia | assumption]. Qed.
Lemma qmAc_rd2 : forall m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 v21 h18 h19 h20 g21 g22 g23 g24 g25 g26 g27 k v,
  2^46 <= SP <= 2^47 -> 0 <= RI -> RI + 128 <= SP - 2048 -> wl_chk (qL2a c CA n h18 h19 h20 g21 g22 g23 g24 g25 g26 g27) k 8 = Some v -> -208 <= k -> k + 8 <= 0 ->
  rd (qmAc m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 v21 h18 h19 h20 g21 g22 g23 g24 g25 g26 g27) (SP + k) 8 v.
Proof.
  intros m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 v21 h18 h19 h20 g21 g22 g23 g24 g25 g26 g27 k v HSP H1 H2 Hc Hk1 Hk2. unfold qmAc.
  apply (rd_frame (wchainS (ic_mem (wchainS m SP (qL1a c CA v1 v8 v9 v18 v19 v20 v21)) CA) SP (qL2a c CA n h18 h19 h20 g21 g22 g23 g24 g25 g26 g27))); [lia | cbn; lia | |].
  - intros x Hx. cbn in Hx.
    rewrite (wchainS_frame_in (gL3a c CA n RI RB FA) _ SP (-2048) (-208)); [| lia | lia | reflexivity | reflexivity | lia | lia].
    apply wb_other; [lia | lia | rewrite length_N_to_le_bytes; lia | rewrite length_N_to_le_bytes; lia].
  - apply rd_wchainS; [lia | lia | reflexivity | lia | cbn; lia | lia | exact Hc].
Qed.
Lemma qmAc_rd1 : forall m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 v21 h18 h19 h20 g21 g22 g23 g24 g25 g26 g27 k v,
  2^46 <= SP <= 2^47 -> 0 <= RI -> RI + 128 <= SP - 2048 -> 0 <= CA -> CA + 4096 <= SP - 2048 ->
  wl_chk (qL1a c CA v1 v8 v9 v18 v19 v20 v21) k 8 = Some v -> -80 <= k -> k + 8 <= 16 ->
  rd (qmAc m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 v21 h18 h19 h20 g21 g22 g23 g24 g25 g26 g27) (SP + k) 8 v.
Proof.
  intros m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 v21 h18 h19 h20 g21 g22 g23 g24 g25 g26 g27 k v HSP H1 H2 H3 H4 Hc Hk1 Hk2. unfold qmAc.
  apply (rd_frame (wchainS m SP (qL1a c CA v1 v8 v9 v18 v19 v20 v21))); [lia | cbn; lia | |].
  - intros x Hx. cbn in Hx.
    rewrite (wchainS_frame_in (gL3a c CA n RI RB FA) _ SP (-2048) (-208)); [| lia | lia | reflexivity | reflexivity | lia | lia].
    rewrite wb_other; [| lia | lia | rewrite length_N_to_le_bytes; lia | rewrite length_N_to_le_bytes; lia].
    rewrite (wchainS_frame_in (qL2a c CA n h18 h19 h20 g21 g22 g23 g24 g25 g26 g27) _ SP (-208) (-80)); [| lia | lia | reflexivity | reflexivity | lia | lia].
    apply ic_keep; [lia | lia | lia | intros i Hi; lia].
  - apply rd_wchainS; [lia | lia | reflexivity | lia | cbn; lia | lia | exact Hc].
Qed.

(* [comment removed for export] *)
Lemma qmAc_frame_f : forall m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 v21 h18 h19 h20 g21 g22 g23 g24 g25 g26 g27 x,
  2^46 <= SP <= 2^47 -> 0 <= CA -> CA + 4096 <= 2^63 -> 0 <= RI -> RI + 128 <= 2^63 -> 0 <= x < 2^64 ->
  ~ (SP - 2048 <= x < SP + 16) -> (forall i, 1 <= i <= 31 -> ~ (CA + 80 * i + 4 <= x < CA + 80 * i + 16)) -> ~ (RI <= x < RI + 8) ->
  qmAc m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 v21 h18 h19 h20 g21 g22 g23 g24 g25 g26 g27 (wa x) = m (wa x).
Proof.
  intros m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 v21 h18 h19 h20 g21 g22 g23 g24 g25 g26 g27 x HSP H1 H2 H3 H4 Hx Q1 Q2 Q3. unfold qmAc.
  rewrite (wchainS_frame_in (gL3a c CA n RI RB FA) _ SP (-2048) 0); [| lia | lia | reflexivity | reflexivity | exact Hx | lia].
  rewrite wb_other; [| exact Hx | lia | rewrite length_N_to_le_bytes; lia | rewrite length_N_to_le_bytes; lia].
  rewrite (wchainS_frame_in (qL2a c CA n h18 h19 h20 g21 g22 g23 g24 g25 g26 g27) _ SP (-2048) 0); [| lia | lia | reflexivity | reflexivity | exact Hx | lia].
  rewrite ic_keep; [| lia | lia | exact Hx | exact Q2].
  rewrite (wchainS_frame_in (qL1a c CA v1 v8 v9 v18 v19 v20 v21) _ SP (-2048) 16); [| lia | lia | reflexivity | reflexivity | exact Hx | lia].
  reflexivity.
Qed.
(* [comment removed for export] *)
Lemma qmAc_rdRI : forall m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 v21 h18 h19 h20 g21 g22 g23 g24 g25 g26 g27,
  2^46 <= SP <= 2^47 -> 0 <= RI -> RI + 128 <= SP - 2048 ->
  rd (qmAc m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 v21 h18 h19 h20 g21 g22 g23 g24 g25 g26 g27) RI 8 1152921504606846976.
Proof.
  intros. unfold qmAc.
  apply (rd_frame (wbytes (wchainS (ic_mem (wchainS m SP (qL1a c CA v1 v8 v9 v18 v19 v20 v21)) CA) SP (qL2a c CA n h18 h19 h20 g21 g22 g23 g24 g25 g26 g27)) (wa RI) (word_to_le_bytes 8 (wa 1152921504606846976)))); [lia | cbn; lia | |].
  - intros x Hx. cbn in Hx. apply (wchainS_frame_in (gL3a c CA n RI RB FA) _ SP (-2048) 0); [lia | lia | reflexivity | reflexivity | lia | lia].
  - apply wb_rd_hit; [lia | lia | cbn; lia].
Qed.
Lemma qmAc_rd_ic : forall m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 v21 h18 h19 h20 g21 g22 g23 g24 g25 g26 g27 i,
  2^46 <= SP <= 2^47 -> 0 <= RI -> RI + 128 <= SP - 2048 -> 0 <= CA -> CA + 4096 <= SP - 2048 -> (CA + 4096 <= RI \/ RI + 128 <= CA) -> 1 <= i <= 31 ->
  rd (qmAc m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 v21 h18 h19 h20 g21 g22 g23 g24 g25 g26 g27) (CA + 80 * i + 4) 4 (mc_tbl i) /\
  rd (qmAc m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 v21 h18 h19 h20 g21 g22 g23 g24 g25 g26 g27) (CA + 80 * i + 8) 8 (sz_tbl i).
Proof.
  intros m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 v21 h18 h19 h20 g21 g22 g23 g24 g25 g26 g27 i HSP H1 H2 H3 H4 H5 Hi. unfold qmAc.
  destruct (ic_rd (wchainS m SP (qL1a c CA v1 v8 v9 v18 v19 v20 v21)) CA i ltac:(lia) ltac:(lia) Hi) as [X1 X2].
  assert (FR : forall x, CA + 80 * i + 4 <= x < CA + 80 * i + 16 ->
            wchainS (wbytes (wchainS (ic_mem (wchainS m SP (qL1a c CA v1 v8 v9 v18 v19 v20 v21)) CA) SP (qL2a c CA n h18 h19 h20 g21 g22 g23 g24 g25 g26 g27)) (wa RI) (word_to_le_bytes 8 (wa 1152921504606846976))) SP (gL3a c CA n RI RB FA) (wa x) =
            ic_mem (wchainS m SP (qL1a c CA v1 v8 v9 v18 v19 v20 v21)) CA (wa x)).
  { intros x Hx.
    rewrite (wchainS_frame_in (gL3a c CA n RI RB FA) _ SP (-2048) 0); [| lia | lia | reflexivity | reflexivity | lia | lia].
    rewrite wb_other; [| lia | lia | rewrite length_N_to_le_bytes; lia | rewrite length_N_to_le_bytes; lia].
    apply (wchainS_frame_in (qL2a c CA n h18 h19 h20 g21 g22 g23 g24 g25 g26 g27) _ SP (-2048) 0); [lia | lia | reflexivity | reflexivity | lia | lia]. }
  split; [apply (rd_frame (ic_mem (wchainS m SP (qL1a c CA v1 v8 v9 v18 v19 v20 v21)) CA)); [lia | cbn; lia | intros x Hx; cbn in Hx; apply FR; lia | exact X1]
         | apply (rd_frame (ic_mem (wchainS m SP (qL1a c CA v1 v8 v9 v18 v19 v20 v21)) CA)); [lia | cbn; lia | intros x Hx; cbn in Hx; apply FR; lia | exact X2]].
Qed.

(* [comment removed for export] *)
Definition qMA_OK (m mA0 : word -> option byte) (regs : bvmap 5 word) (SP CA c RI RB FA QC fsz mp : Z) : Prop :=
  (forall k v, wl_chk (gL3a c CA (mc_tbl c / 2) RI RB FA) k 8 = Some v -> -2048 <= k -> k + 8 <= 0 -> rd mA0 (SP + k) 8 v) /\
  (forall k v, wl_chk (qL2a c CA (mc_tbl c / 2) mp QC (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 12)))) fsz (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 22)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 23)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 24)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 25)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 26)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 27))))) k 8 = Some v ->
      -208 <= k -> k + 8 <= 0 -> rd mA0 (SP + k) 8 v) /\
  (forall k v, wl_chk (qL1a c CA (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 1)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 8)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 9)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 19)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 20)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 21))))) k 8 = Some v ->
      -80 <= k -> k + 8 <= 16 -> rd mA0 (SP + k) 8 v) /\
  (forall x, 0 <= x < 2^64 -> ~ (SP - 2048 <= x < SP + 16) -> (forall i, 1 <= i <= 31 -> ~ (CA + 80 * i + 4 <= x < CA + 80 * i + 16)) ->
     ~ (RI <= x < RI + 8) -> mA0 (wa x) = m (wa x)) /\
  rd mA0 RI 8 1152921504606846976 /\
  (rd mA0 (CA + 80 * c + 4) 4 (mc_tbl c) /\ rd mA0 (CA + 80 * c + 8) 8 (sz_tbl c)) /\
  mem_grows m mA0.

(* [comment removed for export] *)
Section FU.
Context {fx : FPState}.
Variable rom : word -> option byte.
Variables (m mA0 : word -> option byte) (regs : bvmap 5 word) (QC CA c SB SP st st2 TP K TSDA PT T mm1 mm2 fsz mp mx : Z).
Let RIv := SB + 137438953472 + 128 * c.
Let RBv := SB + 4294967296 * c.
Let FAv := SB + 4294967296 * c + 3758096384.
Let SHv := Z.shiftr (SB + 4294967296 * c) 3 + 2147450880.
Let SHFv := Z.shiftr (SB + 4294967296 * c + 3758096384) 3 + 2147450880.
(* [comment removed for export] *)
Definition qCHC (x : Z) : Prop :=
  SP - 2048 <= x < SP + 16 \/ CA - 128 <= x < CA + 2592 \/ RIv <= x < RIv + 128 \/ T + 2872 <= x < T + 2888 \/ RBv <= x < RBv + 262144 \/
  FAv <= x < FAv + 262144 \/ SHv <= x < SHv + 32768 \/ SHFv <= x < SHFv + 32768.
Definition qENVC (x : Z) : Prop :=
  65536 <= x < 143360 \/ 904176 <= x < 904248 \/ 912208 <= x < 912216 \/ 923512 <= x < 923537 \/ 935452 <= x < 935464 \/ 937400 <= x < 937408 \/
  940704 <= x < 940728 \/ 1525856 <= x < 1525864 \/ 1534328 <= x < 1534336 \/ 1534444 <= x < 1534445 \/
  TP - 88 <= x < TP - 80 \/ TSDA + 8 * K <= x < TSDA + 8 * K + 8 \/ PT + 152 <= x < PT + 160.
Definition qCELLS_B (x : Z) : Prop :=
  SP - 2048 <= x < SP + 16 \/ CA - 128 <= x < CA + 2592 \/ RIv <= x < RIv + 128 \/ T + 2872 <= x < T + 2888 \/
  SHv <= x < SHv + 32768 \/ SHFv <= x < SHFv + 32768 \/ qENVC x.
Definition qCELLS_C (x : Z) : Prop := qCELLS_B x \/ FAv <= x < FAv + 262144.

Hypothesis Hc24 : c = 24.
Hypothesis H2 : getr regs 2 = wa (SP + 16).
Hypothesis HSP : 2^46 + 4096 <= SP <= 2^47 /\ SP mod 16 = 0.
Hypothesis HSP16 : SP + 16 <= 2^47.
Hypothesis HSTK : stk_ok SEGS m (wa SP) 2048.
Hypothesis HSTK16 : stk_ok SEGS m (wa (SP + 16)) 2064.
Hypothesis H1 : getr regs 1 = wa 277240.
Hypothesis H9 : getr regs 9 = wa QC.
Hypothesis H10 : getr regs 10 = wa QC.
Hypothesis H11 : getr regs 11 = wa CA.
Hypothesis H13 : getr regs 13 = wa mp.
Hypothesis H14 : getr regs 14 = wa fsz.
Hypothesis H22 : getr regs 22 = wa mx.
Hypothesis HQC : QC = CA - 128.
Hypothesis HSEPQ : CA + 2592 <= SB \/ SB + 137438953472 + 4096 <= QC.
Hypothesis Hfm : 0 <= fsz <= 2^40 /\ 0 <= mp < 2^64 /\ 0 <= mx < 2^62 /\ fsz + 8192 <= mx.
Hypothesis Rq0 : rd m QC 8 0.
Hypothesis Rqb : rd m (QC + 24) 8 0.
Hypothesis Hwq : wr m QC 32.
Hypothesis H4 : getr regs 4 = wa TP.
Hypothesis HCA : ((4304 <= CA /\ CA + 3888 <= 65536) \/ 6529232 <= CA) /\ CA mod 16 = 0 /\ CA + 4096 <= SP - 2048.
Hypothesis HCT : CA = T + 208.
Hypothesis HSB : 17594333495296 <= SB /\ SB mod 4096 = 0 /\ SB + 137438953472 + 4096 <= SP - 2048.
Hypothesis HSEP : CA + 2592 <= SB \/ SB + 137438953472 + 4096 <= CA.
Hypothesis HO : objs_ok_p (SP - 2048) T RIv TP TSDA PT.
Hypothesis HK : 0 <= K <= 1023.
Hypothesis Hvals : 0 <= st < 2^64 /\ 0 <= st2 < 2^64 /\ 0 <= mm1 < 2^64 /\ 0 <= mm2 < 2^64.
Hypothesis HENV : forall x, qENVC x -> ~ qCHC x.
Hypothesis HSHs : shsep T RIv TP TSDA PT SHv.
Hypothesis HSHF : shsep T RIv TP TSDA PT SHFv.
(* [comment removed for export] *)
Hypothesis Ist : rd m (CA + 2576) 8 st.
Hypothesis Ist2 : rd m (CA + 2584) 8 st2.
Hypothesis Iwc : wr m CA 2592.
Hypothesis Iri : forall i, 0 <= i < 16 -> rd m (RIv + 8 * i) 8 0.
Hypothesis Iwri : wr m RIv 128.
Hypothesis Imm1 : rd m (T + 2872) 8 mm1.
Hypothesis Imm2 : rd m (T + 2880) 8 mm2.
Hypothesis Iwt : wr m (T + 2872) 16.
Hypothesis Iwsh : wr m SHv 32768.
Hypothesis Iwshf : wr m SHFv 32768.
(* [comment removed for export] *)
Hypothesis ISB : rd m 923512 8 SB.
Hypothesis IRIB : rd m 923528 8 (SB + 137438953472).
Hypothesis Irtoi : rd m 923520 4 4294967295.
Hypothesis Iprem : rd m 923536 1 0.
Hypothesis Igot : rd m 904176 8 1525856.
Hypothesis Ipsz : rd m 1525856 8 4096.
Hypothesis Icf : rd m 904192 8 1534184.
Hypothesis Icf144 : rd m 1534328 8 0.
Hypothesis Idpm : rd m 1534444 1 0.
Hypothesis Ips1 : rd m 935452 1 1.
Hypothesis Ips2 : rd m 904208 8 937400.
Hypothesis Ips3 : rd m 937400 8 2147450880.
Hypothesis Ips4 : rd m 904216 8 940712.
Hypothesis Ips5 : rd m 940712 8 0.
Hypothesis Ips6 : rd m 904224 8 940720.
Hypothesis Ips7 : rd m 940720 8 0.
Hypothesis Ips8 : rd m 904232 8 940704.
Hypothesis Ips9 : rd m 940704 8 140737488355327.
Hypothesis Ips10 : rd m 904240 8 912208.
Hypothesis Ips11 : rd m 912208 8 864392.
Hypothesis Itls1 : rd m 935456 1 1.
Hypothesis Itls2 : rd m 935460 4 K.
Hypothesis Itls3 : rd m (TP - 88) 8 TSDA.
Hypothesis Itls4 : rd m (TSDA + 8 * K) 8 PT.
Hypothesis Itls5 : rd m (PT + 152) 8 T.
Hypothesis HIMG : forall i, 65536 <= i < 143360 -> m (Z_to_bv 64 i) = None.
(* [comment removed for export] *)
Hypothesis HMA : qMA_OK m mA0 regs SP CA c RIv RBv FAv QC fsz mp.

(* [comment removed for export] *)
#[using="Hc24 HSP HSP16 HQC HSEPQ HCA HCT HSB HSEP HO HK"] Lemma qfu_geo : 2^46 + 4096 <= SP <= 2^47 /\ 1 <= c <= 30 /\ 4304 <= CA /\ CA + 4096 <= SP - 2048 /\ CA = T + 208 /\
  17594333495296 <= SB /\ SB + 137438953472 + 4096 <= SP - 2048 /\
  RIv = SB + 137438953472 + 128 * c /\ RBv = SB + 4294967296 * c /\ FAv = RBv + 3758096384 /\
  8 * (SHv - 2147450880) = RBv /\ 8 * (SHFv - 2147450880) = FAv /\
  4096 <= T /\ T + 4096 <= SP - 2048 - 256 /\ 4096 <= TP /\ TP <= SP - 2048 - 256 /\
  1 <= TSDA /\ TSDA + 8192 <= SP - 2048 - 256 /\ 1 <= PT /\ PT + 160 <= SP - 2048 - 256 /\ 0 <= K <= 1023 /\
  QC = CA - 128 /\ SP + 16 <= 2^47 /\ c = 24.
Proof. LiaFast.lf_pins (fun (Hc24 HSP HSP16 HQC HSEPQ HCA HCT HSB HSEP HO HK : LiaFast.U) => LiaFast.u0).
  assert (Hcr5 : 1 <= c <= 30) by (clear - Hc24; lia).
  assert (E3 : RBv mod 8 = 0).
  { unfold RBv. destruct HSB as (_ & Hm & _). pose proof (Z.div_mod SB 4096 ltac:(lia)) as E. rewrite Hm, Z.add_0_r in E. rewrite E.
    replace (4096 * (SB / 4096) + 4294967296 * c) with ((512 * (SB / 4096) + 536870912 * c) * 8) by ring. apply Z.mod_mul. lia. }
  assert (E1 : 8 * (SHv - 2147450880) = RBv).
  { unfold SHv. fold RBv. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. pose proof (Z.div_mod RBv 8 ltac:(lia)) as E. rewrite E3 in E. lia. }
  assert (E2 : 8 * (SHFv - 2147450880) = FAv).
  { unfold SHFv. fold FAv. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
    assert (E4 : FAv mod 8 = 0).
    { unfold FAv. fold RBv. replace (RBv + 3758096384) with (RBv + 469762048 * 8) by ring. rewrite Z.mod_add by lia. exact E3. }
    pose proof (Z.div_mod FAv 8 ltac:(lia)) as E. rewrite E4 in E. lia. }
  unfold objs_ok_p, t_place in HO. unfold FAv, RBv in *. clear - Hcr5 HSP HCA HCT HSB E1 E2 HO HK HQC HSP16 Hc24. unfold RIv in *. lia.
Qed.
(* [comment removed for export] *)
#[using="SP TP TSDA PT HO"] Lemma qfu_d_ri_t : RIv + 128 <= T \/ T + 4096 <= RIv.
Proof. LiaFast.lf_pins (fun (SP TP TSDA PT HO : LiaFast.U) => LiaFast.u0). unfold objs_ok_p in HO. clear - HO. tauto. Qed.

Ltac zg := let G := fresh "G" in pose proof qfu_geo as G; clear - G; lia.
Ltac zg1 H := let G := fresh "G" in pose proof qfu_geo as G; clear - G H; lia.
Ltac zg2 H1 H2 := let G := fresh "G" in pose proof qfu_geo as G; clear - G H1 H2; lia.
Ltac zg3 H1 H2 H3 := let G := fresh "G" in pose proof qfu_geo as G; clear - G H1 H2 H3; lia.
(* [comment removed for export] *)
Ltac pick := first [ lia | left; lia | right; pick ].
Ltac envc Hx := unfold qENVC; let G := fresh "G" in pose proof qfu_geo as G; clear - G Hx; pick.


(* [comment removed for export] *)
Definition qmB0 : word -> option byte := kz mA0 RBv 262144.

#[using="regs QC fsz mp FAv HMA"] Lemma qmB0_frame : forall x, 0 <= x < 2^64 -> ~ (SP - 2048 <= x < SP + 16) -> (forall i, 1 <= i <= 31 -> ~ (CA + 80 * i + 4 <= x < CA + 80 * i + 16)) ->
  ~ (RIv <= x < RIv + 8) -> ~ (RBv <= x < RBv + 262144) -> qmB0 (wa x) = m (wa x).
Proof. LiaFast.lf_pins (fun (regs QC fsz mp FAv HMA : LiaFast.U) => LiaFast.u0).
  intros x Hx Q1 Q2 Q3 Q4. unfold qmB0. rewrite kz_out by assumption.
  destruct HMA as (_ & _ & _ & FR & _). exact (FR x Hx Q1 Q2 Q3).
Qed.
#[using="regs QC TP K TSDA PT fsz mp Hc24 HSP HSP16 HQC HSEPQ HCA HCT HSB HSEP HO HK HMA"] Lemma qmB0_env : forall x, 0 <= x < 2^64 -> ~ qCHC x -> qmB0 (wa x) = m (wa x).
Proof. LiaFast.lf_pins (fun (regs QC TP K TSDA PT fsz mp Hc24 HSP HSP16 HQC HSEPQ HCA HCT HSB HSEP HO HK HMA : LiaFast.U) => LiaFast.u0).
  intros x Hx Q. unfold qCHC in Q. apply qmB0_frame; [exact Hx | zg1 Q | intros i Hi; zg2 Q Hi | zg1 Q | zg1 Q].
Qed.
#[using="regs QC CA SP fsz mp RIv FAv HMA"] Lemma qmB0_grows : mem_grows m qmB0.
Proof. LiaFast.lf_pins (fun (regs QC CA SP fsz mp RIv FAv HMA : LiaFast.U) => LiaFast.u0). unfold qmB0. destruct HMA as (_ & _ & _ & _ & _ & _ & GA). exact (mem_grows_trans _ _ _ GA (kz_grows _ _ _)). Qed.
(* [comment removed for export] *)
#[using="m regs QC TP K TSDA PT T fsz mp SHv SHFv Hc24 HSP HSP16 HQC HSEPQ HCA HCT HSB HSEP HO HK HMA"] Lemma qmB0_slot3 : forall k v, wl_chk (gL3a c CA (mc_tbl c / 2) RIv RBv FAv) k 8 = Some v -> -2048 <= k -> k + 8 <= 0 -> rd qmB0 (SP + k) 8 v.
Proof. LiaFast.lf_pins (fun (m regs QC TP K TSDA PT T fsz mp SHv SHFv Hc24 HSP HSP16 HQC HSEPQ HCA HCT HSB HSEP HO HK HMA : LiaFast.U) => LiaFast.u0).
  intros k v Hk K1 K2. unfold qmB0. apply (rd_frame mA0); [zg2 K1 K2 | cbn; zg2 K1 K2 | intros x Hx; cbn in Hx; apply kz_out; zg3 K1 K2 Hx |].
  destruct HMA as (S3 & _). exact (S3 k v Hk K1 K2).
Qed.
#[using="m TP K TSDA PT T RIv FAv SHv SHFv Hc24 HSP HSP16 HQC HSEPQ HCA HCT HSB HSEP HO HK HMA"] Lemma qmB0_slot2 : forall k v, wl_chk (qL2a c CA (mc_tbl c / 2) mp QC (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 12)))) fsz (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 22)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 23)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 24)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 25)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 26)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 27))))) k 8 = Some v ->
  -208 <= k -> k + 8 <= 0 -> rd qmB0 (SP + k) 8 v.
Proof. LiaFast.lf_pins (fun (m TP K TSDA PT T RIv FAv SHv SHFv Hc24 HSP HSP16 HQC HSEPQ HCA HCT HSB HSEP HO HK HMA : LiaFast.U) => LiaFast.u0).
  intros k v Hk K1 K2. unfold qmB0. apply (rd_frame mA0); [zg2 K1 K2 | cbn; zg2 K1 K2 | intros x Hx; cbn in Hx; apply kz_out; zg3 K1 K2 Hx |].
  destruct HMA as (_ & S2 & _). exact (S2 k v Hk K1 K2).
Qed.
#[using="m QC TP K TSDA PT T fsz mp RIv FAv SHv SHFv Hc24 HSP HSP16 HQC HSEPQ HCA HCT HSB HSEP HO HK HMA"] Lemma qmB0_slot1 : forall k v, wl_chk (qL1a c CA (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 1)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 8)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 9)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 19)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 20)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 21))))) k 8 = Some v ->
  -80 <= k -> k + 8 <= 16 -> rd qmB0 (SP + k) 8 v.
Proof. LiaFast.lf_pins (fun (m QC TP K TSDA PT T fsz mp RIv FAv SHv SHFv Hc24 HSP HSP16 HQC HSEPQ HCA HCT HSB HSEP HO HK HMA : LiaFast.U) => LiaFast.u0).
  intros k v Hk K1 K2. unfold qmB0. apply (rd_frame mA0); [zg2 K1 K2 | cbn; zg2 K1 K2 | intros x Hx; cbn in Hx; apply kz_out; zg3 K1 K2 Hx |].
  destruct HMA as (_ & _ & S1 & _). exact (S1 k v Hk K1 K2).
Qed.
(* [comment removed for export] *)
#[using="regs QC CA SP T fsz mp RIv FAv SHv SHFv Hc24 HSP HSP16 HQC HSEPQ HCA HCT HSB HSEP HO HK HENV HMA"] Lemma qmB0_envrd : forall a w v, 0 <= a -> (forall x, a <= x < a + Z.of_nat w -> qENVC x) -> a + Z.of_nat w <= 2^64 -> rd m a w v -> rd qmB0 a w v.
Proof. LiaFast.lf_pins (fun (regs QC CA SP T fsz mp RIv FAv SHv SHFv Hc24 HSP HSP16 HQC HSEPQ HCA HCT HSB HSEP HO HK HENV HMA : LiaFast.U) => LiaFast.u0).
  intros a w v Ha HE Hw H. apply (rd_frame m qmB0); [exact Ha | exact Hw | | exact H].
  intros x Hx. apply qmB0_env; [lia | apply HENV; exact (HE x Hx)].
Qed.
(* [comment removed for export] *)
#[using="regs QC SP TP K TSDA PT fsz mp FAv SHv SHFv Hc24 HSP HSP16 HQC HSEPQ HCA HCT HSB HSEP HO HK HMA"] Lemma qmB0_keep : forall a w v, 0 <= a -> a + Z.of_nat w <= 2^63 ->
  (T + 2872 <= a /\ a + Z.of_nat w <= T + 2888) \/ (CA + 2576 <= a /\ a + Z.of_nat w <= CA + 2592) \/ (RIv + 8 <= a /\ a + Z.of_nat w <= RIv + 128) ->
  rd m a w v -> rd qmB0 a w v.
Proof. LiaFast.lf_pins (fun (regs QC SP TP K TSDA PT fsz mp FAv SHv SHFv Hc24 HSP HSP16 HQC HSEPQ HCA HCT HSB HSEP HO HK HMA : LiaFast.U) => LiaFast.u0).
  intros a w v Ha Hw Hr H. pose proof qfu_d_ri_t as D1. pose proof HSEP as D2.
  apply (rd_frame m qmB0); [exact Ha | lia | | exact H].
  intros x Hx. apply qmB0_frame; [lia | | | | ].
  - pose proof qfu_geo as G. clear - G Hr Hx D1 D2. lia.
  - intros i Hi. pose proof qfu_geo as G. clear - G Hr Hx D1 D2 Hi. lia.
  - pose proof qfu_geo as G. clear - G Hr Hx D1 D2. lia.
  - pose proof qfu_geo as G. clear - G Hr Hx D1 D2. lia.
Qed.
(* [comment removed for export] *)
#[using="m regs QC CA SP TP K TSDA PT T fsz mp FAv SHv SHFv Hc24 HSP HSP16 HQC HSEPQ HCA HCT HSB HSEP HO HK HMA"] Lemma qmB0_mu : rd qmB0 RIv 8 1152921504606846976.
Proof. LiaFast.lf_pins (fun (m regs QC CA SP TP K TSDA PT T fsz mp FAv SHv SHFv Hc24 HSP HSP16 HQC HSEPQ HCA HCT HSB HSEP HO HK HMA : LiaFast.U) => LiaFast.u0).
  unfold qmB0. apply (rd_frame mA0); [zg | cbn; zg | intros x Hx; cbn in Hx; apply kz_out; zg1 Hx |].
  destruct HMA as (_ & _ & _ & _ & MU & _). exact MU.
Qed.
#[using="m regs QC SP TP K TSDA PT T fsz mp RIv FAv SHv SHFv Hc24 HSP HSP16 HQC HSEPQ HCA HCT HSB HSEP HO HK HMA"] Lemma qmB0_ic : rd qmB0 (CA + 80 * c + 4) 4 (mc_tbl c) /\ rd qmB0 (CA + 80 * c + 8) 8 (sz_tbl c).
Proof. LiaFast.lf_pins (fun (m regs QC SP TP K TSDA PT T fsz mp RIv FAv SHv SHFv Hc24 HSP HSP16 HQC HSEPQ HCA HCT HSB HSEP HO HK HMA : LiaFast.U) => LiaFast.u0).
  pose proof HSEP as D. destruct HMA as (_ & _ & _ & _ & _ & (X1 & X2) & _). unfold qmB0.
  split; [apply (rd_frame mA0); [zg | cbn; zg | intros x Hx; cbn in Hx; apply kz_out; [zg1 Hx | pose proof qfu_geo as G; clear - G D Hx; lia] | exact X1]
         | apply (rd_frame mA0); [zg | cbn; zg | intros x Hx; cbn in Hx; apply kz_out; [zg1 Hx | pose proof qfu_geo as G; clear - G D Hx; lia] | exact X2]].
Qed.

(* [comment removed for export] *)
Definition qPB (mB : word -> option byte) : Prop :=
  (forall x, SHv <= x < SHv + 32768 -> mB (wa x) = Some (Z_to_bv 8 250)) /\
  rd mB (SP - 448 + 88) 8 515004 /\ rd mB (SP - 448 + 80) 8 262144 /\ rd mB (SP - 448 + 72) 8 FAv /\
  rd mB (SP - 448 + 64) 8 262144 /\ rd mB (SP - 448 + 56) 8 RIv /\ rd mB (SP - 448 + 48) 8 262144 /\
  rd mB (SP - 352 + 24) 8 271780 /\ rd mB (SP - 352 + 16) 8 262144 /\ rd mB (SP - 352 + 8) 8 FAv /\ rd mB (SP - 352 + 0) 8 262144 /\
  rd mB (SP - 280) 8 281044 /\ rd mB (SP - 288) 8 RIv /\ rd mB (SP - 296) 8 (262144 / (sz_tbl c)) /\
  rd mB (SP - 304) 8 RBv /\ rd mB (SP - 312) 8 (262144 / (sz_tbl c)) /\
  rd mB (RIv + 48) 8 262144 /\ rd mB (T + 2872) 8 (mm1 + 1) /\ rd mB (T + 2880) 8 (mm2 + 262144) /\ rd mB (CA + 2584) 8 (st2 + 262144).
Definition qFRB (m0 mB : word -> option byte) : Prop :=
  (forall x, 0 <= x < 2^64 -> ~ (SP - 2048 <= x < SP - 272) -> ~ (SHv <= x < SHv + 32768) -> ~ (RIv + 48 <= x < RIv + 56) ->
     ~ (CA + 2584 <= x < CA + 2592) -> ~ (T + 2872 <= x < T + 2888) -> mB (wa x) = m0 (wa x)) /\ mem_grows m0 mB.

Section SB.
Variable mB0' : word -> option byte.
Hypothesis HB0 : agree_on qCELLS_B mB0' qmB0.

#[using="FAv HB0"] Lemma qb_rd : forall a w v, 0 <= a -> a + Z.of_nat w <= 2^63 -> (forall x, a <= x < a + Z.of_nat w -> qCELLS_B x) -> rd qmB0 a w v -> rd mB0' a w v.
Proof. LiaFast.lf_pins (fun (FAv HB0 : LiaFast.U) => LiaFast.u0). intros a w v Ha Hw HS H. apply (rd_agree qCELLS_B mB0' qmB0); [exact HB0 | exact Ha | lia | exact HS | exact H]. Qed.
#[using="mA0 regs QC fsz mp RBv FAv HMA HB0"] Lemma qb_wr : forall a n, 0 <= a -> a + n <= 2^63 -> (forall x, a <= x < a + n -> qCELLS_B x) -> wr m a n -> wr mB0' a n.
Proof. LiaFast.lf_pins (fun (mA0 regs QC fsz mp RBv FAv HMA HB0 : LiaFast.U) => LiaFast.u0).
  intros a n Ha Hn HS H. apply (wr_agree qCELLS_B mB0' qmB0); [exact HB0 | exact Ha | lia | exact HS |].
  exact (wr_grows m qmB0 _ _ qmB0_grows H).
Qed.
#[using="mA0 regs QC CA c SB SP T fsz mp RIv RBv FAv SHv SHFv Hc24 HSP HSP16 HQC HSEPQ HCA HCT HSB HSEP HO HK HENV HMA HB0"] Lemma qb_env : forall a w v, 0 <= a -> a + Z.of_nat w <= 2^63 -> (forall x, a <= x < a + Z.of_nat w -> qENVC x) -> rd m a w v -> rd mB0' a w v.
Proof. LiaFast.lf_pins (fun (mA0 regs QC CA c SB SP T fsz mp RIv RBv FAv SHv SHFv Hc24 HSP HSP16 HQC HSEPQ HCA HCT HSB HSEP HO HK HENV HMA HB0 : LiaFast.U) => LiaFast.u0).
  intros a w v Ha Hw HE H. apply qb_rd; [exact Ha | exact Hw | intros x Hx; unfold qCELLS_B; do 6 right; exact (HE x Hx) |].
  apply qmB0_envrd; [exact Ha | exact HE | lia | exact H].
Qed.
#[using="m mA0 regs QC TP K TSDA PT T fsz mp SHv SHFv Hc24 HSP HSP16 HQC HSEPQ HCA HCT HSB HSEP HO HK HMA HB0"] Lemma qb_slot3 : forall k v, wl_chk (gL3a c CA (mc_tbl c / 2) RIv RBv FAv) k 8 = Some v -> -2048 <= k -> k + 8 <= 0 -> rd mB0' (SP + k) 8 v.
Proof. LiaFast.lf_pins (fun (m mA0 regs QC TP K TSDA PT T fsz mp SHv SHFv Hc24 HSP HSP16 HQC HSEPQ HCA HCT HSB HSEP HO HK HMA HB0 : LiaFast.U) => LiaFast.u0).
  intros k v Hk K1 K2. apply qb_rd; [zg2 K1 K2 | cbn; zg2 K1 K2 | intros x Hx; cbn in Hx; unfold qCELLS_B; left; zg3 K1 K2 Hx |].
  apply qmB0_slot3; assumption.
Qed.
#[using="m mA0 SB TP K TSDA PT T RIv RBv FAv SHv SHFv Hc24 HSP HSP16 HQC HSEPQ HCA HCT HSB HSEP HO HK HMA HB0"] Lemma qb_slot2 : forall k v, wl_chk (qL2a c CA (mc_tbl c / 2) mp QC (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 12)))) fsz (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 22)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 23)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 24)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 25)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 26)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 27))))) k 8 = Some v ->
  -208 <= k -> k + 8 <= 0 -> rd mB0' (SP + k) 8 v.
Proof. LiaFast.lf_pins (fun (m mA0 SB TP K TSDA PT T RIv RBv FAv SHv SHFv Hc24 HSP HSP16 HQC HSEPQ HCA HCT HSB HSEP HO HK HMA HB0 : LiaFast.U) => LiaFast.u0).
  intros k v Hk K1 K2. apply qb_rd; [zg2 K1 K2 | cbn; zg2 K1 K2 | intros x Hx; cbn in Hx; unfold qCELLS_B; left; zg3 K1 K2 Hx |].
  apply qmB0_slot2; assumption.
Qed.
#[using="m mA0 QC SB TP K TSDA PT T fsz mp RIv RBv FAv SHv SHFv Hc24 HSP HSP16 HQC HSEPQ HCA HCT HSB HSEP HO HK HMA HB0"] Lemma qb_slot1 : forall k v, wl_chk (qL1a c CA (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 1)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 8)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 9)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 19)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 20)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 21))))) k 8 = Some v ->
  -80 <= k -> k + 8 <= 16 -> rd mB0' (SP + k) 8 v.
Proof. LiaFast.lf_pins (fun (m mA0 QC SB TP K TSDA PT T fsz mp RIv RBv FAv SHv SHFv Hc24 HSP HSP16 HQC HSEPQ HCA HCT HSB HSEP HO HK HMA HB0 : LiaFast.U) => LiaFast.u0).
  intros k v Hk K1 K2. apply qb_rd; [zg2 K1 K2 | cbn; zg2 K1 K2 | intros x Hx; cbn in Hx; unfold qCELLS_B; left; zg3 K1 K2 Hx |].
  apply qmB0_slot1; assumption.
Qed.
#[using="m mA0 regs QC CA SP TP K TSDA PT T fsz mp RBv FAv SHv SHFv Hc24 HSP HSP16 HQC HSEPQ HCA HCT HSB HSEP HO HK HMA HB0"] Lemma qb_mu : rd mB0' RIv 8 1152921504606846976.
Proof. LiaFast.lf_pins (fun (m mA0 regs QC CA SP TP K TSDA PT T fsz mp RBv FAv SHv SHFv Hc24 HSP HSP16 HQC HSEPQ HCA HCT HSB HSEP HO HK HMA HB0 : LiaFast.U) => LiaFast.u0). apply qb_rd; [zg | cbn; zg | intros x Hx; cbn in Hx; unfold qCELLS_B; do 2 right; left; clear - Hx; lia | exact qmB0_mu]. Qed.
#[using="m mA0 regs QC SB SP TP K TSDA PT T fsz mp RIv RBv FAv SHv SHFv Hc24 HSP HSP16 HQC HSEPQ HCA HCT HSB HSEP HO HK HMA HB0"] Lemma qb_ic : rd mB0' (CA + 80 * c + 4) 4 (mc_tbl c) /\ rd mB0' (CA + 80 * c + 8) 8 (sz_tbl c).
Proof. LiaFast.lf_pins (fun (m mA0 regs QC SB SP TP K TSDA PT T fsz mp RIv RBv FAv SHv SHFv Hc24 HSP HSP16 HQC HSEPQ HCA HCT HSB HSEP HO HK HMA HB0 : LiaFast.U) => LiaFast.u0).
  assert (Hcr5 : 1 <= c <= 30) by (clear - Hc24; lia).
  destruct qmB0_ic as [X1 X2].
  split; (apply qb_rd; [zg | cbn; zg | intros x Hx; cbn in Hx; unfold qCELLS_B; right; left; clear - Hx Hcr5; lia | assumption]).
Qed.
#[using="mA0 regs QC SP TP K TSDA PT fsz mp RBv FAv SHv SHFv Hc24 HSP HSP16 HQC HSEPQ HCA HCT HSB HSEP HO HK HMA HB0"] Lemma qb_keep : forall a w v, 0 <= a -> a + Z.of_nat w <= 2^63 ->
  (T + 2872 <= a /\ a + Z.of_nat w <= T + 2888) \/ (CA + 2576 <= a /\ a + Z.of_nat w <= CA + 2592) \/ (RIv + 8 <= a /\ a + Z.of_nat w <= RIv + 128) ->
  rd m a w v -> rd mB0' a w v.
Proof. LiaFast.lf_pins (fun (mA0 regs QC SP TP K TSDA PT fsz mp RBv FAv SHv SHFv Hc24 HSP HSP16 HQC HSEPQ HCA HCT HSB HSEP HO HK HMA HB0 : LiaFast.U) => LiaFast.u0).
  intros a w v Ha Hw Hr H. apply qb_rd; [exact Ha | exact Hw | | apply qmB0_keep; assumption].
  intros x Hx. unfold qCELLS_B. pose proof qfu_geo as G. clear - G Hr Hx. destruct Hr as [Hr|[Hr|Hr]]; [do 3 right; left; lia | right; left; lia | do 2 right; left; lia].
Qed.
#[using="m mA0 regs QC CA c SB TP K TSDA PT T fsz mp RIv RBv FAv SHv SHFv Hc24 HSP HSP16 HSTK HQC HSEPQ HCA HCT HSB HSEP HO HK HMA HB0"] Lemma qb_stk : stk_ok SEGS mB0' (wa SP) 2048.
Proof. LiaFast.lf_pins (fun (m mA0 regs QC CA c SB TP K TSDA PT T fsz mp RIv RBv FAv SHv SHFv Hc24 HSP HSP16 HSTK HQC HSEPQ HCA HCT HSB HSEP HO HK HMA HB0 : LiaFast.U) => LiaFast.u0).
  apply (stk_ok_agree qCELLS_B mB0' qmB0); [exact HB0 | zg | zg | intros x Hx; unfold qCELLS_B; left; clear - Hx; lia |].
  exact (stk_ok_grows m qmB0 (wa SP) 2048 qmB0_grows HSTK).
Qed.

Ltac benv H := apply qb_env; [zg | cbn; zg | intros x Hx; cbn in Hx; envc Hx | exact H].

#[using="m mA0 regs QC st K TSDA PT fsz mp SHFv Hc24 HSP HSP16 HSTK HQC HSEPQ HCA HCT HSB HSEP HO HK Hvals HENV HSHs Ist2 Iwc Iri Iwri Imm1 Imm2 Iwt Iwsh Iprem Igot Ipsz Icf Icf144 Idpm Ips1 Ips2 Ips3 Ips4 Ips5 Ips6 Ips7 Ips8 Ips9 Ips10 Ips11 Itls1 Itls2 Itls3 Itls4 Itls5 HMA HB0"] Lemma qstageB : forall R1', getr R1' 1 = wa 481796 -> getr R1' 2 = wa (SP - 400) -> getr R1' 4 = wa TP -> getr R1' 8 = wa 262144 ->
  getr R1' 10 = wa RBv -> getr R1' 21 = wa (sz_tbl c) -> getr R1' 22 = wa 923480 ->
  exists R2 mB, msteps SEGS (mkst R1' (wa 0x73c48) mB0' rom) (mkst R2 (wa 0x73c44) mB rom) /\
    EC R2 FAv /\ getr R2 (Z_to_bv 5 (Z.of_nat 1)) = wa 481796 /\ getr R2 (Z_to_bv 5 (Z.of_nat 2)) = wa (SP - 448) /\
    getr R2 (Z_to_bv 5 (Z.of_nat 8)) = wa 262144 /\ getr R2 (Z_to_bv 5 (Z.of_nat 21)) = wa (sz_tbl c) /\ getr R2 (Z_to_bv 5 (Z.of_nat 22)) = wa 923480 /\
    getr R2 (Z_to_bv 5 (Z.of_nat 4)) = wa TP /\ getr R2 (Z_to_bv 5 (Z.of_nat 3)) = getr R1' (Z_to_bv 5 (Z.of_nat 3)) /\
    qPB mB /\ qFRB mB0' mB.
Proof. LiaFast.lf_pins (fun (m mA0 regs QC st K TSDA PT fsz mp SHFv Hc24 HSP HSP16 HSTK HQC HSEPQ HCA HCT HSB HSEP HO HK Hvals HENV HSHs Ist2 Iwc Iri Iwri Imm1 Imm2 Iwt Iwsh Iprem Igot Ipsz Icf Icf144 Idpm Ips1 Ips2 Ips3 Ips4 Ips5 Ips6 Ips7 Ips8 Ips9 Ips10 Ips11 Itls1 Itls2 Itls3 Itls4 Itls5 HMA HB0 : LiaFast.U) => LiaFast.u0).
  intros R1' Q1 Q2 Q4 Q8 Q10 Q21 Q22.
  assert (Hcr5 : 1 <= c <= 30) by (clear - Hc24; lia).
  assert (Hst3 : 0 <= mm1 < 2^64 /\ 0 <= mm2 < 2^64 /\ 0 <= st2 < 2^64) by (clear - Hvals; lia).
  assert (FRI : forall i, 1 <= i < 16 -> rd mB0' (RIv + 8 * i) 8 0).
  { intros i Hi. apply qb_keep; [zg1 Hi | cbn; zg1 Hi | right; right; cbn; zg1 Hi | exact (Iri i ltac:(lia))]. }
  destruct (gsegB rom mB0' R1' CA c SB SP TP K TSDA PT T mm1 mm2 st2 Hcr5 HSP HCT HO HSB HK ltac:(clear - HCA; lia) HSHs Hst3 Q1 Q2 Q4 Q8 Q10 Q21 Q22)
    as (R2 & mB & Hms & B1 & B2 & B8 & B10 & B11 & B12 & B13 & B14 & B15 & B17 & B21 & B22 & B4 & B3 & BSH & S88 & S80 & S72 & S64 & S56 & S48 &
        N24 & N16 & N8 & N0 & E40 & E32 & E24 & E16 & E8 & BRI48 & BM1 & BM2 & BST2 & BFR & BG).
  - exact qb_stk.
  - replace (SP - 400 + 88) with (SP + -312) by ring. apply qb_slot3; [reflexivity | lia | lia].
  - replace (SP - 400 + 80) with (SP + -320) by ring. apply qb_slot3; [reflexivity | lia | lia].
  - replace (SP - 400 + 72) with (SP + -328) by ring. apply qb_slot3; [reflexivity | lia | lia].
  - replace (SP - 400 + 64) with (SP + -336) by ring. apply qb_slot3; [reflexivity | lia | lia].
  - replace (SP - 400 + 56) with (SP + -344) by ring. apply qb_slot3; [reflexivity | lia | lia].
  - replace (SP - 400 + 48) with (SP + -352) by ring. apply qb_slot3; [reflexivity | lia | lia].
  - replace (SP - 304 + 24) with (SP + -280) by ring. apply qb_slot3; [reflexivity | lia | lia].
  - replace (SP - 304 + 16) with (SP + -288) by ring. apply qb_slot3; [reflexivity | lia | lia].
  - replace (SP - 304 + 8) with (SP + -296) by ring. apply qb_slot3; [reflexivity | lia | lia].
  - replace (SP - 304 + 0) with (SP + -304) by ring. apply qb_slot3; [reflexivity | lia | lia].
  - benv Icf.
  - benv Icf144.
  - benv Idpm.
  - benv Igot.
  - benv Ipsz.
  - benv Ips1.
  - benv Ips2.
  - benv Ips3.
  - benv Ips4.
  - benv Ips5.
  - benv Ips6.
  - benv Ips7.
  - benv Ips8.
  - benv Ips9.
  - benv Ips10.
  - benv Ips11.
  - benv Itls1.
  - benv Itls2.
  - benv Itls3.
  - benv Itls4.
  - benv Itls5.
  - apply qb_keep; [zg | cbn; zg | left; cbn; lia | exact Imm1].
  - apply qb_keep; [zg | cbn; zg | left; cbn; lia | exact Imm2].
  - apply qb_keep; [zg | cbn; zg | right; left; cbn; lia | exact Ist2].
  - apply qb_wr; [zg | zg | intros x Hx; unfold qCELLS_B; do 3 right; left; clear - Hx; lia | exact Iwt].
  - apply qb_wr; [zg | zg | intros x Hx; unfold qCELLS_B; right; left; clear - Hx; lia |].
    intros d k Hd Hk. replace (CA + 2584 + d) with (CA + (2584 + d)) by ring. apply Iwc; lia.
  - exact (FRI 2 ltac:(lia)).
  - exact (FRI 3 ltac:(lia)).
  - exact (FRI 4 ltac:(lia)).
  - exact (FRI 6 ltac:(lia)).
  - apply qb_wr; [zg | zg | intros x Hx; unfold qCELLS_B; do 2 right; left; clear - Hx; lia | exact Iwri].
  - benv Iprem.
  - apply qb_wr; [zg | zg | intros x Hx; unfold qCELLS_B; do 4 right; left; clear - Hx; lia | exact Iwsh].
  - exists R2, mB. split; [exact Hms|]. split; [unfold EC; repeat split; first [assumption | (rewrite B10; f_equal; unfold FAv; ring)]|].
    split; [exact B1|]. split; [exact B2|]. split; [exact B8|]. split; [exact B21|]. split; [exact B22|]. split; [exact B4|]. split; [exact B3|].
    split; [|split; [exact BFR | exact BG]].
    unfold qPB. split; [exact BSH|].
    split; [exact S88|]. split; [exact S80|]. split; [exact S72|]. split; [exact S64|]. split; [exact S56|]. split; [exact S48|].
    split; [exact N24|]. split; [exact N16|]. split; [exact N8|]. split; [exact N0|].
    split; [exact E40|]. split; [exact E32|]. split; [exact E24|]. split; [exact E16|]. split; [exact E8|].
    split; [exact BRI48|]. split; [exact BM1|]. split; [exact BM2|]. exact BST2.
Qed.

(* [comment removed for export] *)
Definition qCHB (x : Z) : Prop :=
  SP - 2048 <= x < SP - 272 \/ SHv <= x < SHv + 32768 \/ RIv + 48 <= x < RIv + 56 \/ CA + 2584 <= x < CA + 2592 \/ T + 2872 <= x < T + 2888.
#[using="Type"] Lemma qchb_chc : forall x, qCHB x -> qCHC x.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros x H. unfold qCHB in H. unfold qCHC. destruct H as [H|[H|[H|[H|H]]]].
  - left. clear - H. lia.
  - do 6 right. left. exact H.
  - do 2 right. left. clear - H. lia.
  - right. left. clear - H. lia.
  - do 3 right. left. exact H.
Qed.
#[using="QC RBv Hc24 HSP HSP16 HQC HSEPQ HCA HCT HSB HSEP HO HK HENV"] Lemma qfa_sep : forall x, qCELLS_B x -> ~ (FAv <= x < FAv + 262144).
Proof. LiaFast.lf_pins (fun (QC RBv Hc24 HSP HSP16 HQC HSEPQ HCA HCT HSB HSEP HO HK HENV : LiaFast.U) => LiaFast.u0).
  intros x Hx. unfold qCELLS_B in Hx. destruct Hx as [Hx|[Hx|[Hx|[Hx|[Hx|[Hx|Hx]]]]]].
  - zg1 Hx.
  - pose proof HSEP as D. pose proof qfu_geo as G. clear - G D Hx. lia.
  - zg1 Hx.
  - pose proof HSEP as D. pose proof qfu_geo as G. clear - G D Hx. lia.
  - zg1 Hx.
  - zg1 Hx.
  - intro F. apply (HENV x Hx). unfold qCHC. do 5 right. left. exact F.
Qed.

Section SC.
Variables (mB mC0' : word -> option byte).
Hypothesis HPB : qPB mB.
Hypothesis HFB : qFRB mB0' mB.
Hypothesis HC0 : agree_on qCELLS_C mC0' (kz mB FAv 262144).

#[using="QC RBv FAv Hc24 HSP HSP16 HQC HSEPQ HCA HCT HSB HSEP HO HK HENV HC0"] Lemma qc_of_mB : forall a w v, 0 <= a -> a + Z.of_nat w <= 2^63 -> (forall x, a <= x < a + Z.of_nat w -> qCELLS_B x) -> rd mB a w v -> rd mC0' a w v.
Proof. LiaFast.lf_pins (fun (QC RBv FAv Hc24 HSP HSP16 HQC HSEPQ HCA HCT HSB HSEP HO HK HENV HC0 : LiaFast.U) => LiaFast.u0).
  intros a w v Ha Hw HS H. apply (rd_agree qCELLS_C mC0' (kz mB FAv 262144)); [exact HC0 | exact Ha | lia | intros x Hx; left; exact (HS x Hx) |].
  apply (rd_frame mB); [exact Ha | lia | intros x Hx; apply kz_out; [lia | exact (qfa_sep x (HS x Hx))] | exact H].
Qed.
#[using="QC RBv FAv Hc24 HSP HSP16 HQC HSEPQ HCA HCT HSB HSEP HO HK HENV mB HFB HC0"] Lemma qc_of_mB0' : forall a w v, 0 <= a -> a + Z.of_nat w <= 2^63 -> (forall x, a <= x < a + Z.of_nat w -> qCELLS_B x /\ ~ qCHB x) -> rd mB0' a w v -> rd mC0' a w v.
Proof. LiaFast.lf_pins (fun (QC RBv FAv Hc24 HSP HSP16 HQC HSEPQ HCA HCT HSB HSEP HO HK HENV mB HFB HC0 : LiaFast.U) => LiaFast.u0).
  intros a w v Ha Hw HS H. apply qc_of_mB; [exact Ha | exact Hw | intros x Hx; exact (proj1 (HS x Hx)) |].
  destruct HFB as [FR _]. apply (rd_frame mB0'); [exact Ha | lia | | exact H].
  intros x Hx. destruct (HS x Hx) as [_ N]. unfold qCHB in N.
  apply FR; [lia | intro F; apply N; left; exact F | intro F; apply N; right; left; exact F | intro F; apply N; do 2 right; left; exact F
            | intro F; apply N; do 3 right; left; exact F | intro F; apply N; do 4 right; exact F].
Qed.
#[using="mA0 regs QC CA c SB SP T fsz mp RIv RBv FAv SHv SHFv Hc24 HSP HSP16 HQC HSEPQ HCA HCT HSB HSEP HO HK HENV HMA mB0' HB0 mB HFB HC0"] Lemma qc_env : forall a w v, 0 <= a -> a + Z.of_nat w <= 2^63 -> (forall x, a <= x < a + Z.of_nat w -> qENVC x) -> rd m a w v -> rd mC0' a w v.
Proof. LiaFast.lf_pins (fun (mA0 regs QC CA c SB SP T fsz mp RIv RBv FAv SHv SHFv Hc24 HSP HSP16 HQC HSEPQ HCA HCT HSB HSEP HO HK HENV HMA mB0' HB0 mB HFB HC0 : LiaFast.U) => LiaFast.u0).
  intros a w v Ha Hw HE H. apply qc_of_mB0'; [exact Ha | exact Hw | | apply qb_env; assumption].
  intros x Hx. split; [unfold qCELLS_B; do 6 right; exact (HE x Hx) | intro F; exact (HENV x (HE x Hx) (qchb_chc x F))].
Qed.
(* [comment removed for export] *)
#[using="QC CA c SB TP K TSDA PT T RIv RBv FAv SHv SHFv Hc24 HSP HSP16 HQC HSEPQ HCA HCT HSB HSEP HO HK HENV mB HFB HC0"] Lemma qc_slot : forall k v, -272 <= k -> k + 8 <= 0 -> rd mB0' (SP + k) 8 v -> rd mC0' (SP + k) 8 v.
Proof. LiaFast.lf_pins (fun (QC CA c SB TP K TSDA PT T RIv RBv FAv SHv SHFv Hc24 HSP HSP16 HQC HSEPQ HCA HCT HSB HSEP HO HK HENV mB HFB HC0 : LiaFast.U) => LiaFast.u0).
  intros k v K1 K2 H. apply qc_of_mB0'; [zg2 K1 K2 | cbn; zg2 K1 K2 | | exact H].
  intros x Hx. cbn in Hx. split; [unfold qCELLS_B; left; zg3 K1 K2 Hx | unfold qCHB; zg3 K1 K2 Hx].
Qed.
(* [comment removed for export] *)
#[using="m mA0 regs QC CA SP TP K TSDA PT T fsz mp RBv FAv SHv SHFv Hc24 HSP HSP16 HQC HSEPQ HCA HCT HSB HSEP HO HK HENV HSHs Iri HMA mB0' HB0 mB HFB HC0"] Lemma qc_ri : forall i, 1 <= i < 16 -> i <> 6 -> rd mC0' (RIv + 8 * i) 8 0.
Proof. LiaFast.lf_pins (fun (m mA0 regs QC CA SP TP K TSDA PT T fsz mp RBv FAv SHv SHFv Hc24 HSP HSP16 HQC HSEPQ HCA HCT HSB HSEP HO HK HENV HSHs Iri HMA mB0' HB0 mB HFB HC0 : LiaFast.U) => LiaFast.u0).
  intros i Hi Hi6. pose proof qfu_d_ri_t as D1. pose proof HSEP as D2.
  assert (D3 : RIv + 128 <= SHv \/ SHv + 32768 <= RIv) by (unfold shsep in HSHs; clear - HSHs; tauto).
  apply qc_of_mB0'; [zg1 Hi | cbn; zg1 Hi | |].
  - intros x Hx. cbn in Hx. split; [unfold qCELLS_B; do 2 right; left; clear - Hi Hx; lia |].
    unfold qCHB. pose proof qfu_geo as G. clear - G Hi Hi6 Hx D1 D2 D3. lia.
  - apply qb_keep; [zg1 Hi | cbn; zg1 Hi | right; right; cbn; zg1 Hi | exact (Iri i ltac:(lia))].
Qed.
#[using="mA0 regs QC fsz mp RBv FAv HMA mB0' HB0 mB HFB HC0"] Lemma qc_wr : forall a n, 0 <= a -> a + n <= 2^63 -> (forall x, a <= x < a + n -> qCELLS_B x) -> wr m a n -> wr mC0' a n.
Proof. LiaFast.lf_pins (fun (mA0 regs QC fsz mp RBv FAv HMA mB0' HB0 mB HFB HC0 : LiaFast.U) => LiaFast.u0).
  intros a n Ha Hn HS H. apply (wr_agree qCELLS_C mC0' (kz mB FAv 262144)); [exact HC0 | exact Ha | lia | intros x Hx; left; exact (HS x Hx) |].
  apply (wr_grows mB); [apply kz_grows|]. apply (wr_grows mB0'); [exact (proj2 HFB)|]. apply qb_wr; assumption.
Qed.
#[using="m mA0 regs QC CA c SB TP K TSDA PT T fsz mp RIv RBv FAv SHv SHFv Hc24 HSP HSP16 HSTK HQC HSEPQ HCA HCT HSB HSEP HO HK HMA mB0' HB0 mB HFB HC0"] Lemma qc_stk : stk_ok SEGS mC0' (wa SP) 2048.
Proof. LiaFast.lf_pins (fun (m mA0 regs QC CA c SB TP K TSDA PT T fsz mp RIv RBv FAv SHv SHFv Hc24 HSP HSP16 HSTK HQC HSEPQ HCA HCT HSB HSEP HO HK HMA mB0' HB0 mB HFB HC0 : LiaFast.U) => LiaFast.u0).
  apply (stk_ok_agree qCELLS_C mC0' (kz mB FAv 262144)); [exact HC0 | zg | zg | intros x Hx; left; unfold qCELLS_B; left; clear - Hx; lia |].
  apply (stk_ok_grows mB); [apply kz_grows|]. apply (stk_ok_grows mB0'); [exact (proj2 HFB)|]. exact qb_stk.
Qed.
#[using="QC CA SP TP K TSDA PT T RIv RBv SHv SHFv Hc24 HSP HSP16 HQC HSEPQ HCA HCT HSB HSEP HO HK mB HC0"] Lemma qc_wfa : wr mC0' FAv 262144.
Proof. LiaFast.lf_pins (fun (QC CA SP TP K TSDA PT T RIv RBv SHv SHFv Hc24 HSP HSP16 HQC HSEPQ HCA HCT HSB HSEP HO HK mB HC0 : LiaFast.U) => LiaFast.u0).
  apply (wr_agree qCELLS_C mC0' (kz mB FAv 262144)); [exact HC0 | zg | zg | intros x Hx; right; exact Hx |].
  apply kz_wr; zg.
Qed.
#[using="m mA0 regs QC CA c SB SP TP K TSDA PT T fsz mp RIv RBv FAv SHv SHFv Hc24 HSP HSP16 HQC HSEPQ HCA HCT HSB HSEP HO HK HENV HIMG HMA mB0' HB0 mB HFB HC0"] Lemma qc_img : forall i, 65536 <= i < 143360 -> mC0' (Z_to_bv 64 i) = None.
Proof. LiaFast.lf_pins (fun (m mA0 regs QC CA c SB SP TP K TSDA PT T fsz mp RIv RBv FAv SHv SHFv Hc24 HSP HSP16 HQC HSEPQ HCA HCT HSB HSEP HO HK HENV HIMG HMA mB0' HB0 mB HFB HC0 : LiaFast.U) => LiaFast.u0).
  intros i Hi. assert (HE : qENVC i) by (unfold qENVC; left; exact Hi).
  assert (HCB : qCELLS_B i) by (unfold qCELLS_B; do 6 right; exact HE).
  apply (agree_none qCELLS_C mC0' (kz mB FAv 262144)); [exact HC0 | clear - Hi; lia | left; exact HCB |].
  change (Z_to_bv 64 i) with (wa i). rewrite kz_out; [| clear - Hi; lia | exact (qfa_sep i HCB)].
  destruct HFB as [FR _].
  assert (N : ~ qCHB i) by (intro F; exact (HENV i HE (qchb_chc i F))). unfold qCHB in N.
  rewrite FR; [| clear - Hi; lia | intro F; apply N; left; exact F | intro F; apply N; right; left; exact F | intro F; apply N; do 2 right; left; exact F
               | intro F; apply N; do 3 right; left; exact F | intro F; apply N; do 4 right; exact F].
  rewrite (HB0 i ltac:(clear - Hi; lia) HCB). rewrite qmB0_env; [| clear - Hi; lia | exact (HENV i HE)]. exact (HIMG i Hi).
Qed.

(* [comment removed for export] *)
#[using="QC CA SP TP K TSDA PT T RBv FAv SHv SHFv Hc24 HSP HSP16 HQC HSEPQ HCA HCT HSB HSEP HO HK HENV HSHs mB HFB HC0"] Lemma qc_riw : forall i v, 0 <= i < 16 -> i <> 6 -> rd mB0' (RIv + 8 * i) 8 v -> rd mC0' (RIv + 8 * i) 8 v.
Proof. LiaFast.lf_pins (fun (QC CA SP TP K TSDA PT T RBv FAv SHv SHFv Hc24 HSP HSP16 HQC HSEPQ HCA HCT HSB HSEP HO HK HENV HSHs mB HFB HC0 : LiaFast.U) => LiaFast.u0).
  intros i v Hi Hi6 H. pose proof qfu_d_ri_t as D1. pose proof HSEP as D2.
  assert (D3 : RIv + 128 <= SHv \/ SHv + 32768 <= RIv) by (unfold shsep in HSHs; clear - HSHs; tauto).
  apply qc_of_mB0'; [zg1 Hi | cbn; zg1 Hi | | exact H].
  intros x Hx. cbn in Hx. split; [unfold qCELLS_B; do 2 right; left; clear - Hi Hx; lia |].
  unfold qCHB. pose proof qfu_geo as G. clear - G Hi Hi6 Hx D1 D2 D3. lia.
Qed.
(* [comment removed for export] *)
#[using="QC c SB SP TP K TSDA PT T RIv RBv FAv SHv SHFv Hc24 HSP HSP16 HQC HSEPQ HCA HCT HSB HSEP HO HK HENV HSHs mB HFB HC0"] Lemma qc_cache : forall a w v, CA <= a -> a + Z.of_nat w <= CA + 2584 -> rd mB0' a w v -> rd mC0' a w v.
Proof. LiaFast.lf_pins (fun (QC c SB SP TP K TSDA PT T RIv RBv FAv SHv SHFv Hc24 HSP HSP16 HQC HSEPQ HCA HCT HSB HSEP HO HK HENV HSHs mB HFB HC0 : LiaFast.U) => LiaFast.u0).
  intros a w v K1 K2 H. pose proof qfu_d_ri_t as D1. pose proof HSEP as D2.
  assert (D4 : T + 4096 <= SHv \/ SHv + 32768 <= T) by (unfold shsep in HSHs; clear - HSHs; tauto).
  apply qc_of_mB0'; [zg2 K1 K2 | zg2 K1 K2 | | exact H].
  intros x Hx. split; [unfold qCELLS_B; right; left; clear - K1 K2 Hx; lia |].
  unfold qCHB. pose proof qfu_geo as G. clear - G K1 K2 Hx D1 D2 D4. lia.
Qed.

Ltac zc := cbv; let X := fresh in intro X; discriminate X.
Ltac cenv H := apply qc_env; [zg | cbn; zg | intros x Hx; cbn in Hx; envc Hx | exact H].

(* [comment removed for export] *)
Hypothesis HWB : wr mC0' RBv 8192.
#[using="QC CA c SB TP K TSDA PT T RIv RBv FAv SHv SHFv Hc24 HSP HSP16 HQC HSEPQ HCA HCT HSB HSEP HO HK HENV mB HFB HC0"] Lemma qc_slot16 : forall k v, -272 <= k -> k + 8 <= 16 -> rd mB0' (SP + k) 8 v -> rd mC0' (SP + k) 8 v.
Proof. LiaFast.lf_pins (fun (QC CA c SB TP K TSDA PT T RIv RBv FAv SHv SHFv Hc24 HSP HSP16 HQC HSEPQ HCA HCT HSB HSEP HO HK HENV mB HFB HC0 : LiaFast.U) => LiaFast.u0).
  intros k v K1 K2 H. apply qc_of_mB0'; [zg2 K1 K2 | cbn; zg2 K1 K2 | | exact H].
  intros x Hx. cbn in Hx. split; [unfold qCELLS_B; left; zg3 K1 K2 Hx | unfold qCHB; zg3 K1 K2 Hx].
Qed.
#[using="mA0 regs QC c SB SP TP K TSDA PT T fsz mp RIv RBv FAv SHv SHFv Hc24 HSP HSP16 HQC HSEPQ HCA HCT HSB HSEP HO HK HENV HSHs HMA mB0' HB0 mB HFB HC0"] Lemma qc_qc : forall a w v, CA - 128 <= a -> a + Z.of_nat w <= CA - 96 -> rd m a w v -> rd mC0' a w v.
Proof. LiaFast.lf_pins (fun (mA0 regs QC c SB SP TP K TSDA PT T fsz mp RIv RBv FAv SHv SHFv Hc24 HSP HSP16 HQC HSEPQ HCA HCT HSB HSEP HO HK HENV HSHs HMA mB0' HB0 mB HFB HC0 : LiaFast.U) => LiaFast.u0).
  intros a w v K1 K2 H. pose proof qfu_d_ri_t as D1. pose proof HSEP as D2. pose proof HSEPQ as D2q.
  assert (D4 : T + 4096 <= SHv \/ SHv + 32768 <= T) by (unfold shsep in HSHs; clear - HSHs; tauto).
  apply qc_of_mB0'; [zg2 K1 K2 | zg2 K1 K2 | |].
  - intros x Hx. split; [unfold qCELLS_B; right; left; clear - K1 K2 Hx; lia |].
    unfold qCHB. pose proof qfu_geo as G. clear - G K1 K2 Hx D1 D2 D2q D4. lia.
  - apply qb_rd; [zg2 K1 K2 | zg2 K1 K2 | intros x Hx; unfold qCELLS_B; right; left; clear - K1 K2 Hx; lia |].
    apply (rd_frame m qmB0); [zg2 K1 K2 | zg2 K1 K2 | | exact H].
    intros x Hx. apply qmB0_frame; [zg3 K1 K2 Hx | | | |].
    + pose proof qfu_geo as G. clear - G K1 K2 Hx. lia.
    + intros i Hi. clear - K1 K2 Hx Hi. lia.
    + pose proof qfu_geo as G. clear - G K1 K2 Hx D1 D2 D2q. lia.
    + pose proof qfu_geo as G. clear - G K1 K2 Hx D1 D2 D2q. lia.
Qed.

#[using="m mA0 st st2 K TSDA PT mm1 mm2 mx RIv SHv Hc24 HSP HSP16 HSTK H1 H9 H22 HQC HSEPQ Hfm Rq0 Rqb Hwq HCA HCT HSB HSEP HO HK Hvals HENV HSHs HSHF Ist Iwc Iri Iwri Iwt Iwshf ISB IRIB Icf Icf144 Ips1 Ips2 Ips3 Ips4 Ips5 Ips6 Ips7 Ips8 Ips9 Ips10 Ips11 Itls1 Itls2 Itls3 Itls4 Itls5 HIMG HMA mB0' HB0 mB HPB HFB HC0 HWB"] Lemma qstageC : forall R2', getr R2' 1 = wa 481796 -> getr R2' 2 = wa (SP - 448) -> getr R2' 4 = wa TP -> getr R2' 8 = wa 262144 ->
  getr R2' 10 = wa FAv -> getr R2' 21 = wa (sz_tbl c) -> getr R2' 22 = wa 923480 ->
  exists R3 m3, msteps SEGS (mkst R2' (wa 0x73c48) mC0' rom) (mkst R3 (wa 0x43a30) m3 rom) /\
    getr R3 (Z_to_bv 5 (Z.of_nat 2)) = wa (SP + 16) /\
    (forall k, In k [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R3 (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))) /\
    (forall k, In k [3; 4]%nat -> getr R3 (Z_to_bv 5 (Z.of_nat k)) = getr R2' (Z_to_bv 5 (Z.of_nat k))) /\
    q_inv m3 QC SB 0 1 (fsz + 8192) /\
    INV_G m3 CA SB c (sz_tbl c) (mc_tbl c / 2) (262144 / (sz_tbl c)) 1 /\
    rd m3 RBv 8 0 /\ rd m3 (RBv + 24) 8 mp /\
    (forall x, 0 <= x < 2^64 -> ~ (SP - 2048 <= x < SP + 16) -> ~ (SHFv <= x < SHFv + 32768) -> ~ (T + 2872 <= x < T + 2888) ->
        ~ (FAv <= x < FAv + 262144) -> ~ owned_C CA SB c x -> ~ (QC <= x < QC + 32) -> ~ (RBv <= x < RBv + 32) -> m3 (wa x) = mC0' (wa x)) /\ mem_grows mC0' m3.
Proof. LiaFast.lf_pins (fun (m mA0 st st2 K TSDA PT mm1 mm2 mx RIv SHv Hc24 HSP HSP16 HSTK H1 H9 H22 HQC HSEPQ Hfm Rq0 Rqb Hwq HCA HCT HSB HSEP HO HK Hvals HENV HSHs HSHF Ist Iwc Iri Iwri Iwt Iwshf ISB IRIB Icf Icf144 Ips1 Ips2 Ips3 Ips4 Ips5 Ips6 Ips7 Ips8 Ips9 Ips10 Ips11 Itls1 Itls2 Itls3 Itls4 Itls5 HIMG HMA mB0' HB0 mB HPB HFB HC0 HWB : LiaFast.U) => LiaFast.u0).
  intros R2' Q1 Q2 Q4 Q8 Q10 Q21 Q22.
  assert (Hcr5 : 1 <= c <= 30) by (clear - Hc24; lia).
  destruct HPB as (BSH & S88 & S80 & S72 & S64 & S56 & S48 & N24 & N16 & N8 & N0 & E40 & E32 & E24 & E16 & E8 & BRI48 & BM1 & BM2 & BST2).
  set (mm1' := (mm1 + 1) mod 2^64). set (mm2' := (mm2 + 262144) mod 2^64).
  assert (Hst' : 0 <= mm1' < 2^64 /\ 0 <= mm2' < 2^64) by (unfold mm1', mm2'; split; apply Z.mod_pos_bound; lia).
  assert (W : forall a v, SP - 2048 <= a -> a + 8 <= SP -> rd mB a 8 v -> rd mC0' a 8 v).
  { intros a v K1 K2 H. apply qc_of_mB; [zg2 K1 K2 | cbn; zg2 K1 K2 | intros x Hx; cbn in Hx; unfold qCELLS_B; left; clear - K1 K2 Hx; lia | exact H]. }
  assert (WT : forall a v, T + 2872 <= a -> a + 8 <= T + 2888 -> rd mB a 8 v -> rd mC0' a 8 v).
  { intros a v K1 K2 H. apply qc_of_mB; [zg2 K1 K2 | cbn; zg2 K1 K2 | intros x Hx; cbn in Hx; unfold qCELLS_B; do 3 right; left; clear - K1 K2 Hx; lia | exact H]. }
  destruct (gsegC1 rom mC0' R2' c SB SP TP K TSDA PT T mm1' mm2' Hcr5 HSP HO HSB HK HSHF Hst' Q1 Q2 Q4 Q8 Q10 Q21 Q22)
    as (R3' & mC1 & Hms1 & C2r & C4 & C8 & C10 & C11 & C12 & C13 & C18 & C19 & C21 & C22 & C3 & CSHF & CRI24 & CM1 & CM2 & CFR & CG).
  - exact qc_stk.
  - apply W; [clear; lia | clear; lia | exact S88].
  - apply W; [clear; lia | clear; lia | exact S80].
  - apply W; [clear; lia | clear; lia | exact S72].
  - apply W; [clear; lia | clear; lia | exact S64].
  - apply W; [clear; lia | clear; lia | exact S56].
  - apply W; [clear; lia | clear; lia | exact S48].
  - apply W; [clear; lia | clear; lia | exact N24].
  - apply W; [clear; lia | clear; lia | exact N16].
  - apply W; [clear; lia | clear; lia | exact N8].
  - apply W; [clear; lia | clear; lia | exact N0].
  - apply W; [clear; lia | clear; lia | exact E40].
  - apply W; [clear; lia | clear; lia | exact E32].
  - apply W; [clear; lia | clear; lia | exact E24].
  - apply W; [clear; lia | clear; lia | exact E16].
  - apply W; [clear; lia | clear; lia | exact E8].
  - cenv Icf.
  - cenv Icf144.
  - cenv Ips1.
  - cenv Ips2.
  - cenv Ips3.
  - cenv Ips4.
  - cenv Ips5.
  - cenv Ips6.
  - cenv Ips7.
  - cenv Ips8.
  - cenv Ips9.
  - cenv Ips10.
  - cenv Ips11.
  - cenv Itls1.
  - cenv Itls2.
  - cenv Itls3.
  - cenv Itls4.
  - cenv Itls5.
  - apply WT; [clear; lia | clear; lia | unfold mm1'; apply rd_mod64; exact BM1].
  - apply WT; [clear; lia | clear; lia | unfold mm2'; apply rd_mod64; exact BM2].
  - apply qc_wr; [zg | zg | intros x Hx; unfold qCELLS_B; do 3 right; left; clear - Hx; lia | exact Iwt].
  - pose proof (qc_ri 4 ltac:(lia) ltac:(lia)) as X. replace (RIv + 8 * 4) with (RIv + 32) in X by ring. exact X.
  - apply qc_wr; [zg | zg | intros x Hx; unfold qCELLS_B; do 2 right; left; clear - Hx; lia | exact Iwri].
  - apply qc_wr; [zg | zg | intros x Hx; unfold qCELLS_B; do 5 right; left; clear - Hx; lia | exact Iwshf].
  - (* [comment removed for export] *)
    pose proof qfu_d_ri_t as D1. pose proof HSEP as D2.
    assert (D3f : RIv + 128 <= SHFv \/ SHFv + 32768 <= RIv) by (unfold shsep in HSHF; clear - HSHF; tauto).
    assert (D4f : T + 4096 <= SHFv \/ SHFv + 32768 <= T) by (unfold shsep in HSHF; clear - HSHF; tauto).
    assert (K1 : forall a w v, 0 <= a -> a + Z.of_nat w <= 2^63 ->
              (forall x, a <= x < a + Z.of_nat w -> ~ (SP - 2048 <= x < SP - 320) /\ ~ (SHFv <= x < SHFv + 32768) /\ ~ (RIv + 24 <= x < RIv + 32) /\ ~ (T + 2872 <= x < T + 2888)) ->
              rd mC0' a w v -> rd mC1 a w v).
    { intros a w v Ha Hw HS H. apply (rd_frame mC0'); [exact Ha | clear - Hw; lia | | exact H].
      intros x Hx. destruct (HS x Hx) as (N1 & N2 & N3 & N4). apply CFR; [clear - Ha Hw Hx; lia | exact N1 | exact N2 | exact N3 | exact N4]. }
    assert (KS : forall k v, -272 <= k -> k + 8 <= 16 -> rd mB0' (SP + k) 8 v -> rd mC1 (SP + k) 8 v).
    { intros k v K1' K2' H. apply K1; [zg2 K1' K2' | cbn; zg2 K1' K2' | | apply qc_slot16; assumption].
      intros x Hx. cbn in Hx. pose proof qfu_geo as G. clear - G K1' K2' Hx. lia. }
    assert (KE : forall a w v, 0 <= a -> a + Z.of_nat w <= 2^63 -> (forall x, a <= x < a + Z.of_nat w -> qENVC x) -> rd m a w v -> rd mC1 a w v).
    { intros a w v Ha Hw HE H. apply K1; [exact Ha | exact Hw | | apply qc_env; assumption].
      intros x Hx. pose proof (HENV x (HE x Hx)) as N. unfold qCHC in N.
      split; [intro F; apply N; left; clear - F; lia|]. split; [intro F; apply N; do 7 right; exact F|].
      split; [intro F; apply N; do 2 right; left; clear - F; lia | intro F; apply N; do 3 right; left; exact F]. }
    assert (KR : forall i v, 0 <= i < 16 -> i <> 6 -> i <> 3 -> rd mB0' (RIv + 8 * i) 8 v -> rd mC1 (RIv + 8 * i) 8 v).
    { intros i v Hi H6 H3 H. apply K1; [zg1 Hi | cbn; zg1 Hi | | apply qc_riw; assumption].
      intros x Hx. cbn in Hx. pose proof qfu_geo as G. clear - G Hi H3 Hx D1 D3f. lia. }
    assert (KR0 : forall i, 1 <= i < 16 -> i <> 6 -> i <> 3 -> rd mC1 (RIv + 8 * i) 8 0).
    { intros i Hi H6 H3. apply KR; [clear - Hi; lia | exact H6 | exact H3 |].
      apply qb_keep; [zg1 Hi | cbn; zg1 Hi | right; right; cbn; zg1 Hi | exact (Iri i ltac:(lia))]. }
    assert (KC : forall a w v, CA <= a -> a + Z.of_nat w <= CA + 2584 -> rd mB0' a w v -> rd mC1 a w v).
    { intros a w v K1' K2' H. apply K1; [zg2 K1' K2' | zg2 K1' K2' | | apply qc_cache; assumption].
      intros x Hx. pose proof qfu_geo as G. clear - G K1' K2' Hx D1 D2 D4f. lia. }
    assert (KW : forall a n, wr mC0' a n -> wr mC1 a n) by (intros a n H; exact (wr_grows mC0' mC1 a n CG H)).
    destruct qb_ic as [BIC1 BIC2].
    assert (Eg1 : (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 1)))) = 277240) by (pose proof H1 as X; regzH X; rewrite X; apply u_wa_small; clear; lia).
    assert (Eg9 : (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 9)))) = QC) by (pose proof H9 as X; regzH X; rewrite X; apply u_wa_small; zg).
    assert (Eg22 : (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 22)))) = mx) by (pose proof H22 as X; regzH X; rewrite X; apply u_wa_small; clear - Hfm; lia).
    assert (D4s : T + 4096 <= SHv \/ SHv + 32768 <= T) by (unfold shsep in HSHs; clear - HSHs; tauto).
    assert (KQ : forall a w v, CA - 128 <= a -> a + Z.of_nat w <= CA - 96 -> rd m a w v -> rd mC1 a w v).
    { intros a w v K1' K2' H. apply K1; [zg2 K1' K2' | zg2 K1' K2' | | apply qc_qc; assumption].
      intros x Hx. pose proof qfu_geo as G. pose proof HSEPQ as D2q. clear - G K1' K2' Hx D1 D2 D2q D4f. lia. }
    destruct (qsegC2 rom mC1 R3' QC CA c SB SP 0 st fsz mp mx (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 12)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 8)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 19)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 20)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 21)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 23)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 24)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 25)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 26)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 27))))
                Hc24 HSP HSP16 HCA HSB HSEP HQC HSEPQ ltac:(clear - Hvals; lia) Hfm
                ltac:(regzG; exact C2r) ltac:(regzG; exact C8) ltac:(regzG; exact C10) ltac:(regzG; exact C11) ltac:(regzG; exact C12) ltac:(regzG; exact C13)
                ltac:(regzG; exact C19) ltac:(regzG; exact C21))
      as (R3 & m3 & Hms2 & F2 & F1 & F8 & F9 & F18 & F19 & F20 & F21 & F22 & F23 & F24 & F25 & F26 & F27 & FK & FQI & FINV & FB0 & FB24 & FFR & FG).
    + exact (stk_ok_grows mC0' mC1 (wa SP) 2048 CG qc_stk).
    + replace (SP - 216) with (SP + -216) by ring. apply KS; [zc | zc | apply qb_slot3; [reflexivity | zc | zc]].
    + replace (SP - 224) with (SP + -224) by ring. apply KS; [zc | zc | apply qb_slot3; [reflexivity | zc | zc]].
    + replace (SP - 232) with (SP + -232) by ring. apply KS; [zc | zc | apply qb_slot3; [reflexivity | zc | zc]].
    + replace (SP - 240) with (SP + -240) by ring. apply KS; [zc | zc | apply qb_slot3; [reflexivity | zc | zc]].
    + replace (SP - 248) with (SP + -248) by ring. apply KS; [zc | zc | apply qb_slot3; [reflexivity | zc | zc]].
    + replace (SP - 256) with (SP + -256) by ring. apply KS; [zc | zc | apply qb_slot3; [reflexivity | zc | zc]].
    + replace (SP - 264) with (SP + -264) by ring. apply KS; [zc | zc | apply qb_slot3; [reflexivity | zc | zc]].
    + replace (SP - 272) with (SP + -272) by ring. apply KS; [zc | zc | apply qb_slot3; [reflexivity | zc | zc]].
    + replace (SP - 88) with (SP + -88) by ring. apply KS; [zc | zc | apply qb_slot2; [reflexivity | zc | zc]].
    + replace (SP - 96) with (SP + -96) by ring. apply KS; [zc | zc | apply qb_slot2; [reflexivity | zc | zc]].
    + replace (SP - 104) with (SP + -104) by ring. apply KS; [zc | zc | apply qb_slot2; [reflexivity | zc | zc]].
    + replace (SP - 112) with (SP + -112) by ring. apply KS; [zc | zc | apply qb_slot2; [reflexivity | zc | zc]].
    + replace (SP - 120) with (SP + -120) by ring. apply KS; [zc | zc | apply qb_slot2; [reflexivity | zc | zc]].
    + replace (SP - 128) with (SP + -128) by ring. apply KS; [zc | zc | apply qb_slot2; [reflexivity | zc | zc]].
    + replace (SP - 136) with (SP + -136) by ring. apply KS; [zc | zc | apply qb_slot2; [reflexivity | zc | zc]].
    + rewrite <- Eg22. replace (SP - 144) with (SP + -144) by ring. apply KS; [zc | zc | apply qb_slot2; [reflexivity | zc | zc]].
    + replace (SP - 152) with (SP + -152) by ring. apply KS; [zc | zc | apply qb_slot2; [reflexivity | zc | zc]].
    + replace (SP - 160) with (SP + -160) by ring. apply KS; [zc | zc | apply qb_slot2; [reflexivity | zc | zc]].
    + replace (SP - 168) with (SP + -168) by ring. apply KS; [zc | zc | apply qb_slot2; [reflexivity | zc | zc]].
    + replace (SP - 176) with (SP + -176) by ring. apply KS; [zc | zc | apply qb_slot2; [reflexivity | zc | zc]].
    + replace (SP - 184) with (SP + -184) by ring. apply KS; [zc | zc | apply qb_slot2; [reflexivity | zc | zc]].
    + replace (SP - 72) with (SP + -72) by ring. apply KS; [zc | zc | apply qb_slot1; [reflexivity | zc | zc]].
    + replace (SP - 64) with (SP + -64) by ring. apply KS; [zc | zc | apply qb_slot1; [reflexivity | zc | zc]].
    + replace (SP - 56) with (SP + -56) by ring. apply KS; [zc | zc | apply qb_slot1; [reflexivity | zc | zc]].
    + replace (SP - 40) with (SP + -40) by ring. apply KS; [zc | zc | apply qb_slot1; [reflexivity | zc | zc]].
    + replace (SP - 32) with (SP + -32) by ring. apply KS; [zc | zc | apply qb_slot1; [reflexivity | zc | zc]].
    + replace (SP - 24) with (SP + -24) by ring. apply KS; [zc | zc | apply qb_slot1; [reflexivity | zc | zc]].
    + replace (SP - 16) with (SP + -16) by ring. apply KS; [zc | zc | apply qb_slot1; [reflexivity | zc | zc]].
    + rewrite <- Eg9. replace (SP - 8) with (SP + -8) by ring. apply KS; [zc | zc | apply qb_slot1; [reflexivity | zc | zc]].
    + replace SP with (SP + 0) at 1 by ring. apply KS; [zc | zc | apply qb_slot1; [reflexivity | zc | zc]].
    + rewrite <- Eg1. apply KS; [zc | zc | apply qb_slot1; [reflexivity | zc | zc]].
    + repeat match goal with |- _ /\ _ => split end; first [exact (proj1 (bvu_rng _)) | exact (proj2 (bvu_rng _))].
    + pose proof (KR 0 1152921504606846976 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)) as X. rewrite Z.add_0_r in X. apply X. exact qb_mu.
    + exact (KR0 2 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)).
    + exact (KR0 4 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)).
    + exact (KR0 5 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)).
    + apply K1; [zg | cbn; zg | |].
      * intros x Hx. cbn in Hx. pose proof qfu_geo as G. clear - G Hx D1 D3f. lia.
      * apply qc_of_mB; [zg | cbn; zg | intros x Hx; cbn in Hx; unfold qCELLS_B; do 2 right; left; clear - Hx; lia | exact BRI48].
    + exact (KR0 7 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)).
    + exact (KR0 9 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)).
    + apply KW. apply qc_wr; [zg | zg | intros x Hx; unfold qCELLS_B; do 2 right; left; clear - Hx; lia | exact Iwri].
    + apply KC; [clear - Hcr5; lia | cbn; clear - Hcr5; lia | exact BIC1].
    + apply KC; [clear - Hcr5; lia | cbn; clear - Hcr5; lia | exact BIC2].
    + apply KW. apply qc_wr; [zg | zg | intros x Hx; unfold qCELLS_B; right; left; clear - Hx; lia | exact Iwc].
    + apply KE; [clear; lia | cbn; clear; lia | intros x Hx; cbn in Hx; envc Hx | exact ISB].
    + apply KE; [clear; lia | cbn; clear; lia | intros x Hx; cbn in Hx; envc Hx | exact IRIB].
    + apply KC; [clear; lia | cbn; clear; lia |]. apply qb_keep; [zg | cbn; zg | right; left; cbn; clear; lia | exact Ist].
    + apply KW. exact qc_wfa.
    + intros i Hi. change (Z_to_bv 64 i) with (wa i).
      assert (HE : qENVC i) by (unfold qENVC; left; exact Hi). pose proof (HENV i HE) as N. unfold qCHC in N.
      rewrite CFR; [exact (qc_img i Hi) | clear - Hi; lia | intro F; apply N; left; clear - F; lia | intro F; apply N; do 7 right; exact F
                   | intro F; apply N; do 2 right; left; clear - F; lia | intro F; apply N; do 3 right; left; exact F].
    + apply KQ; [clear - HQC; lia | cbn; clear - HQC; lia | exact Rq0].
    + apply KQ; [clear - HQC; lia | cbn; clear - HQC; lia | exact Rqb].
    + apply KW. apply qc_wr; [zg | zg | intros x Hx; unfold qCELLS_B; right; left; clear - HQC Hx; lia | exact Hwq].
    + apply KW. exact HWB.
    + exists R3, m3. split; [exact (msteps_trans SEGS _ _ _ Hms1 Hms2)|].
      split; [exact F2|].
      split.
      { intros k Hk. cbn [In] in Hk.
        destruct Hk as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]];
          first [rewrite F1, <- Eg1 | rewrite F8 | rewrite F9, <- Eg9 | rewrite F18 | rewrite F19 | rewrite F20 | rewrite F21 | rewrite F22, <- Eg22 | rewrite F23
                | rewrite F24 | rewrite F25 | rewrite F26 | rewrite F27]; apply wa_u. }
      split.
      { intros k Hk. cbn [In] in Hk. destruct Hk as [<-|[<-|[]]].
        - rewrite (FK 3%nat ltac:(left; reflexivity)). exact C3.
        - rewrite (FK 4%nat ltac:(right; left; reflexivity)). rewrite C4. symmetry. regzH Q4. exact Q4. }
      split; [exact FQI|]. split; [exact FINV|]. split; [exact FB0|]. split; [exact FB24|].
      split; [| exact (mem_grows_trans _ _ _ CG FG)].
      intros x Hx N1 N2 N3 N4 N5 N6 N7. rewrite FFR; [| exact Hx | exact N4 | exact N5 | exact N6 | exact N7].
      apply CFR; [exact Hx | intro F; apply N1; clear - F; lia | exact N2 | | exact N3].
      intro F. apply N5. unfold owned_C. right. left. clear - F. lia.
Qed.
End SC.
End SB.
End FU.

(* [comment removed for export] *)
Section VA.
Context {fx : FPState}.
Variable rom : word -> option byte.
Variables (m : word -> option byte) (regs : bvmap 5 word) (QC CA c SB SP sz0 st fsz mp : Z).
Let RIv := SB + 137438953472 + 128 * c.
Let RBv := SB + 4294967296 * c.
Let FAv := SB + 4294967296 * c + 3758096384.
Hypothesis Hc24 : c = 24.
Hypothesis H2 : getr regs 2 = wa (SP + 16).
Hypothesis HSP : 2^46 + 4096 <= SP /\ SP + 16 <= 2^47 /\ SP mod 16 = 0.
Hypothesis HSTK16 : stk_ok SEGS m (wa (SP + 16)) 2064.
Hypothesis H10 : getr regs 10 = wa QC.
Hypothesis H11 : getr regs 11 = wa CA.
Hypothesis H13 : getr regs 13 = wa mp.
Hypothesis H14 : getr regs 14 = wa fsz.
Hypothesis HQC : QC = CA - 128.
Hypothesis Hfm : 0 <= fsz <= 2^40 /\ 0 <= mp < 2^64.
Hypothesis Rq0 : rd m QC 8 0.
Hypothesis HCA : ((4304 <= CA /\ CA + 3888 <= 65536) \/ 6529232 <= CA) /\ CA mod 16 = 0 /\ CA + 4096 <= SP - 2048.
Hypothesis HSB : 17594333495296 <= SB /\ SB mod 4096 = 0 /\ SB + 137438953472 + 4096 <= SP - 2048.
Hypothesis HSEP : CA + 2592 <= SB \/ SB + 137438953472 + 4096 <= CA.
Hypothesis Hvals : 0 <= sz0 < 2^64 /\ 0 <= st < 2^64.
Hypothesis Icnt : rd m (CA + 80 * c) 4 0.
Hypothesis Imc : rd m (CA + 80 * c + 4) 4 0.
Hypothesis Isz : rd m (CA + 80 * c + 8) 8 sz0.
Hypothesis Ist : rd m (CA + 2576) 8 st.
Hypothesis Iwc : wr m CA 2592.
Hypothesis Iri : forall i, 0 <= i < 16 -> rd m (RIv + 8 * i) 8 0.
Hypothesis Iwri : wr m RIv 128.
Hypothesis ISB : rd m 923512 8 SB.
Hypothesis IRIB : rd m 923528 8 (SB + 137438953472).
Hypothesis Irtoi : rd m 923520 4 4294967295.
Hypothesis Iprem : rd m 923536 1 0.
Hypothesis Igot : rd m 904176 8 1525856.
Hypothesis Ipsz : rd m 1525856 8 4096.
Hypothesis Icf : rd m 904192 8 1534184.
Hypothesis Idpm : rd m 1534444 1 0.

#[using="sz0 st Hc24 H2 HSP HSTK16 H10 H11 H13 H14 HQC Hfm Rq0 HCA HSB HSEP Hvals Icnt Imc Isz Ist Iwc Iri Iwri ISB IRIB Irtoi Iprem Igot Ipsz Icf Idpm"] Lemma qstageA : exists R1 mA, msteps SEGS (mkst regs (wa 0x43b04) m rom) (mkst R1 (wa 0x73c44) mA rom) /\
  EC R1 RBv /\ getr R1 (Z_to_bv 5 (Z.of_nat 1)) = wa 481796 /\ getr R1 (Z_to_bv 5 (Z.of_nat 2)) = wa (SP - 400) /\
  getr R1 (Z_to_bv 5 (Z.of_nat 8)) = wa 262144 /\ getr R1 (Z_to_bv 5 (Z.of_nat 21)) = wa (sz_tbl c) /\ getr R1 (Z_to_bv 5 (Z.of_nat 22)) = wa 923480 /\
  (forall k, In k [3; 4]%nat -> getr R1 (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))) /\
  qMA_OK m mA regs SP CA c RIv RBv FAv QC fsz mp /\
  (forall i, 1 <= i <= 31 -> rd mA (CA + 80 * i + 4) 4 (mc_tbl i) /\ rd mA (CA + 80 * i + 8) 8 (sz_tbl i)) /\
  (forall x, 0 <= x < 2^64 -> ~ (SP - 2048 <= x < SP + 16) -> (forall i, 1 <= i <= 31 -> ~ (CA + 80 * i + 4 <= x < CA + 80 * i + 16)) ->
     ~ (RIv <= x < RIv + 8) -> mA (wa x) = m (wa x)).
Proof. LiaFast.lf_pins (fun (sz0 st Hc24 H2 HSP HSTK16 H10 H11 H13 H14 HQC Hfm Rq0 HCA HSB HSEP Hvals Icnt Imc Isz Ist Iwc Iri Iwri ISB IRIB Irtoi Iprem Igot Ipsz Icf Idpm : LiaFast.U) => LiaFast.u0).
  assert (Hcr5 : 1 <= c <= 30) by (clear - Hc24; lia).
  assert (G : 2^46 <= SP <= 2^47 /\ 0 <= CA /\ CA + 4096 <= SP - 2048 /\ 0 <= RIv /\ RIv + 128 <= SP - 2048 /\ (CA + 4096 <= RIv \/ RIv + 128 <= CA))
    by (unfold RIv; clear - Hcr5 HSP HCA HSB HSEP; lia).
  destruct (qsegA rom m regs QC CA c SB SP sz0 st fsz mp Hc24 H2 HSP HSTK16 H10 H11 H13 H14 HQC Hfm Rq0 HCA HSB HSEP Hvals Icnt Imc Isz Ist Iwc ISB IRIB Irtoi Iprem
              ltac:(pose proof (Iri 0 ltac:(lia)) as X; rewrite Z.add_0_r in X; exact X)
              ltac:(pose proof (Iri 2 ltac:(lia)) as X; exact X) ltac:(pose proof (Iri 4 ltac:(lia)) as X; exact X)
              ltac:(pose proof (Iri 6 ltac:(lia)) as X; exact X) ltac:(pose proof (Iri 7 ltac:(lia)) as X; exact X)
              Iwri Igot Ipsz Icf Idpm)
    as (R1 & mA & Hms & A1 & A2 & A8 & A10 & A11 & A12 & A13 & A14 & A15 & A17 & A21 & A22 & AK & EMA).
  exists R1, mA. split; [exact Hms|]. split; [unfold EC; repeat split; assumption|].
  split; [exact A1|]. split; [exact A2|]. split; [exact A8|]. split; [exact A21|]. split; [exact A22|]. split; [exact AK|].
  fold RIv RBv FAv in EMA. rewrite EMA. clear - G Hcr5.
  split; [|split].
  - unfold qMA_OK. split; [|split; [|split; [|split; [|split; [|split]]]]].
    + intros k v Hk K1 K2. apply qmAc_rd3; [lia | exact Hk | exact K1 | exact K2].
    + intros k v Hk K1 K2. apply qmAc_rd2; [lia | lia | lia | exact Hk | exact K1 | exact K2].
    + intros k v Hk K1 K2. apply qmAc_rd1; [lia | lia | lia | lia | lia | exact Hk | exact K1 | exact K2].
    + intros x Hx Q1 Q2 Q3. apply qmAc_frame_f; [lia | lia | lia | lia | lia | exact Hx | exact Q1 | exact Q2 | exact Q3].
    + apply qmAc_rdRI; lia.
    + apply qmAc_rd_ic; [lia | lia | lia | lia | lia | tauto | lia].
    + apply qmAc_grows.
  - intros i Hi. apply qmAc_rd_ic; [lia | lia | lia | lia | lia | tauto | exact Hi].
  - intros x Hx Q1 Q2 Q3. apply qmAc_frame_f; [lia | lia | lia | lia | lia | exact Hx | exact Q1 | exact Q2 | exact Q3].
Qed.
End VA.

(* [comment removed for export] *)
Lemma qmAd_grows : forall m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 v21 h18 h19 h20 g21 g22 g23 g24 g25 g26 g27,
  mem_grows m (qmAd m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 v21 h18 h19 h20 g21 g22 g23 g24 g25 g26 g27).
Proof.
  intros. unfold qmAd.
  apply (mem_grows_trans _ _ _ (wchainS_grows (qL1a c CA v1 v8 v9 v18 v19 v20 v21) m SP)).
  apply (mem_grows_trans _ _ _ (wchainS_grows (qL2a c CA n h18 h19 h20 g21 g22 g23 g24 g25 g26 g27) _ SP)).
  apply (mem_grows_trans _ (wbytes (wchainS (wchainS m SP (qL1a c CA v1 v8 v9 v18 v19 v20 v21)) SP (qL2a c CA n h18 h19 h20 g21 g22 g23 g24 g25 g26 g27)) (wa RI) (word_to_le_bytes 8 (wa 1152921504606846976)))).
  - apply grows_wb. apply mem_grows_refl.
  - apply wchainS_grows.
Qed.
Lemma qmAd_rd3 : forall m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 v21 h18 h19 h20 g21 g22 g23 g24 g25 g26 g27 k v,
  2^46 <= SP <= 2^47 -> wl_chk (gL3a c CA n RI RB FA) k 8 = Some v -> -2048 <= k -> k + 8 <= 0 ->
  rd (qmAd m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 v21 h18 h19 h20 g21 g22 g23 g24 g25 g26 g27) (SP + k) 8 v.
Proof. intros. unfold qmAd. apply rd_wchainS; [lia | lia | reflexivity | lia | cbn; lia | lia | assumption]. Qed.
Lemma qmAd_rd2 : forall m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 v21 h18 h19 h20 g21 g22 g23 g24 g25 g26 g27 k v,
  2^46 <= SP <= 2^47 -> 0 <= RI -> RI + 128 <= SP - 2048 -> wl_chk (qL2a c CA n h18 h19 h20 g21 g22 g23 g24 g25 g26 g27) k 8 = Some v -> -208 <= k -> k + 8 <= 0 ->
  rd (qmAd m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 v21 h18 h19 h20 g21 g22 g23 g24 g25 g26 g27) (SP + k) 8 v.
Proof.
  intros m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 v21 h18 h19 h20 g21 g22 g23 g24 g25 g26 g27 k v HSP H1 H2 Hc Hk1 Hk2. unfold qmAd.
  apply (rd_frame (wchainS (wchainS m SP (qL1a c CA v1 v8 v9 v18 v19 v20 v21)) SP (qL2a c CA n h18 h19 h20 g21 g22 g23 g24 g25 g26 g27))); [lia | cbn; lia | |].
  - intros x Hx. cbn in Hx.
    rewrite (wchainS_frame_in (gL3a c CA n RI RB FA) _ SP (-2048) (-208)); [| lia | lia | reflexivity | reflexivity | lia | lia].
    apply wb_other; [lia | lia | rewrite length_N_to_le_bytes; lia | rewrite length_N_to_le_bytes; lia].
  - apply rd_wchainS; [lia | lia | reflexivity | lia | cbn; lia | lia | exact Hc].
Qed.
Lemma qmAd_rd1 : forall m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 v21 h18 h19 h20 g21 g22 g23 g24 g25 g26 g27 k v,
  2^46 <= SP <= 2^47 -> 0 <= RI -> RI + 128 <= SP - 2048 ->
  wl_chk (qL1a c CA v1 v8 v9 v18 v19 v20 v21) k 8 = Some v -> -80 <= k -> k + 8 <= 16 ->
  rd (qmAd m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 v21 h18 h19 h20 g21 g22 g23 g24 g25 g26 g27) (SP + k) 8 v.
Proof.
  intros m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 v21 h18 h19 h20 g21 g22 g23 g24 g25 g26 g27 k v HSP H1 H2 Hc Hk1 Hk2. unfold qmAd.
  apply (rd_frame (wchainS m SP (qL1a c CA v1 v8 v9 v18 v19 v20 v21))); [lia | cbn; lia | |].
  - intros x Hx. cbn in Hx.
    rewrite (wchainS_frame_in (gL3a c CA n RI RB FA) _ SP (-2048) (-208)); [| lia | lia | reflexivity | reflexivity | lia | lia].
    rewrite wb_other; [| lia | lia | rewrite length_N_to_le_bytes; lia | rewrite length_N_to_le_bytes; lia].
    apply (wchainS_frame_in (qL2a c CA n h18 h19 h20 g21 g22 g23 g24 g25 g26 g27) _ SP (-208) (-80)); [lia | lia | reflexivity | reflexivity | lia | lia].
  - apply rd_wchainS; [lia | lia | reflexivity | lia | cbn; lia | lia | exact Hc].
Qed.
Lemma qmAd_frame_f : forall m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 v21 h18 h19 h20 g21 g22 g23 g24 g25 g26 g27 x,
  2^46 <= SP <= 2^47 -> 0 <= RI -> RI + 128 <= 2^63 -> 0 <= x < 2^64 -> ~ (SP - 2048 <= x < SP + 16) -> ~ (RI <= x < RI + 8) ->
  qmAd m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 v21 h18 h19 h20 g21 g22 g23 g24 g25 g26 g27 (wa x) = m (wa x).
Proof.
  intros m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 v21 h18 h19 h20 g21 g22 g23 g24 g25 g26 g27 x HSP H3 H4 Hx Q1 Q3. unfold qmAd.
  rewrite (wchainS_frame_in (gL3a c CA n RI RB FA) _ SP (-2048) 0); [| lia | lia | reflexivity | reflexivity | exact Hx | lia].
  rewrite wb_other; [| exact Hx | lia | rewrite length_N_to_le_bytes; lia | rewrite length_N_to_le_bytes; lia].
  rewrite (wchainS_frame_in (qL2a c CA n h18 h19 h20 g21 g22 g23 g24 g25 g26 g27) _ SP (-2048) 0); [| lia | lia | reflexivity | reflexivity | exact Hx | lia].
  rewrite (wchainS_frame_in (qL1a c CA v1 v8 v9 v18 v19 v20 v21) _ SP (-2048) 16); [| lia | lia | reflexivity | reflexivity | exact Hx | lia].
  reflexivity.
Qed.
Lemma qmAd_rdRI : forall m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 v21 h18 h19 h20 g21 g22 g23 g24 g25 g26 g27,
  2^46 <= SP <= 2^47 -> 0 <= RI -> RI + 128 <= SP - 2048 ->
  rd (qmAd m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 v21 h18 h19 h20 g21 g22 g23 g24 g25 g26 g27) RI 8 1152921504606846976.
Proof.
  intros. unfold qmAd.
  apply (rd_frame (wbytes (wchainS (wchainS m SP (qL1a c CA v1 v8 v9 v18 v19 v20 v21)) SP (qL2a c CA n h18 h19 h20 g21 g22 g23 g24 g25 g26 g27)) (wa RI) (word_to_le_bytes 8 (wa 1152921504606846976)))); [lia | cbn; lia | |].
  - intros x Hx. cbn in Hx. apply (wchainS_frame_in (gL3a c CA n RI RB FA) _ SP (-2048) 0); [lia | lia | reflexivity | reflexivity | lia | lia].
  - apply wb_rd_hit; [lia | lia | cbn; lia].
Qed.

Section VB.
Context {fx : FPState}.
Variable rom : word -> option byte.
Variables (m : word -> option byte) (regs : bvmap 5 word) (QC CA c SB SP st fsz mp : Z).
Let RIv := SB + 137438953472 + 128 * c.
Let RBv := SB + 4294967296 * c.
Let FAv := SB + 4294967296 * c + 3758096384.
Hypothesis Hc24 : c = 24.
Hypothesis H2 : getr regs 2 = wa (SP + 16).
Hypothesis HSP : 2^46 + 4096 <= SP /\ SP + 16 <= 2^47 /\ SP mod 16 = 0.
Hypothesis HSTK16 : stk_ok SEGS m (wa (SP + 16)) 2064.
Hypothesis H10 : getr regs 10 = wa QC.
Hypothesis H11 : getr regs 11 = wa CA.
Hypothesis H13 : getr regs 13 = wa mp.
Hypothesis H14 : getr regs 14 = wa fsz.
Hypothesis HQC : QC = CA - 128.
Hypothesis Hfm : 0 <= fsz <= 2^40 /\ 0 <= mp < 2^64.
Hypothesis Rq0 : rd m QC 8 0.
Hypothesis HCA : ((4304 <= CA /\ CA + 3888 <= 65536) \/ 6529232 <= CA) /\ CA mod 16 = 0 /\ CA + 4096 <= SP - 2048.
Hypothesis HSB : 17594333495296 <= SB /\ SB mod 4096 = 0 /\ SB + 137438953472 + 4096 <= SP - 2048.
Hypothesis HSEP : CA + 2592 <= SB \/ SB + 137438953472 + 4096 <= CA.
Hypothesis Hvals : 0 <= st < 2^64.
Hypothesis Icnt : rd m (CA + 80 * c) 4 0.
Hypothesis Imc : rd m (CA + 80 * c + 4) 4 (mc_tbl c).
Hypothesis Isz : rd m (CA + 80 * c + 8) 8 (sz_tbl c).
Hypothesis Ist : rd m (CA + 2576) 8 st.
Hypothesis Iwc : wr m CA 2592.
Hypothesis Iri : forall i, 0 <= i < 16 -> rd m (RIv + 8 * i) 8 0.
Hypothesis Iwri : wr m RIv 128.
Hypothesis ISB : rd m 923512 8 SB.
Hypothesis IRIB : rd m 923528 8 (SB + 137438953472).
Hypothesis Irtoi : rd m 923520 4 4294967295.
Hypothesis Iprem : rd m 923536 1 0.
Hypothesis Igot : rd m 904176 8 1525856.
Hypothesis Ipsz : rd m 1525856 8 4096.
Hypothesis Icf : rd m 904192 8 1534184.
Hypothesis Idpm : rd m 1534444 1 0.

#[using="st Hc24 H2 HSP HSTK16 H10 H11 H13 H14 HQC Hfm Rq0 HCA HSB HSEP Hvals Icnt Imc Isz Ist Iwc Iri Iwri ISB IRIB Irtoi Iprem Igot Ipsz Icf Idpm"] Lemma qstageA' : exists R1 mA, msteps SEGS (mkst regs (wa 0x43b04) m rom) (mkst R1 (wa 0x73c44) mA rom) /\
  EC R1 RBv /\ getr R1 (Z_to_bv 5 (Z.of_nat 1)) = wa 481796 /\ getr R1 (Z_to_bv 5 (Z.of_nat 2)) = wa (SP - 400) /\
  getr R1 (Z_to_bv 5 (Z.of_nat 8)) = wa 262144 /\ getr R1 (Z_to_bv 5 (Z.of_nat 21)) = wa (sz_tbl c) /\ getr R1 (Z_to_bv 5 (Z.of_nat 22)) = wa 923480 /\
  (forall k, In k [3; 4]%nat -> getr R1 (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))) /\
  qMA_OK m mA regs SP CA c RIv RBv FAv QC fsz mp /\
  (forall x, 0 <= x < 2^64 -> ~ (SP - 2048 <= x < SP + 16) -> ~ (RIv <= x < RIv + 8) -> mA (wa x) = m (wa x)).
Proof. LiaFast.lf_pins (fun (st Hc24 H2 HSP HSTK16 H10 H11 H13 H14 HQC Hfm Rq0 HCA HSB HSEP Hvals Icnt Imc Isz Ist Iwc Iri Iwri ISB IRIB Irtoi Iprem Igot Ipsz Icf Idpm : LiaFast.U) => LiaFast.u0).
  assert (Hcr5 : 1 <= c <= 30) by (clear - Hc24; lia).
  assert (G : 2^46 <= SP <= 2^47 /\ 0 <= CA /\ CA + 4096 <= SP - 2048 /\ 0 <= RIv /\ RIv + 128 <= SP - 2048 /\ (CA + 4096 <= RIv \/ RIv + 128 <= CA))
    by (unfold RIv; clear - Hcr5 HSP HCA HSB HSEP; lia).
  assert (Hsz : 0 <= sz_tbl c < 2^64) by (destruct (gsz_rng c Hcr5) as (Hq & _); clear - Hq; lia).
  destruct (qsegA' rom m regs QC CA c SB SP (sz_tbl c) st fsz mp Hc24 H2 HSP HSTK16 H10 H11 H13 H14 HQC Hfm Rq0 HCA HSB HSEP (conj Hsz Hvals) Icnt Imc Isz Ist Iwc ISB IRIB Irtoi Iprem
              ltac:(pose proof (Iri 0 ltac:(lia)) as X; rewrite Z.add_0_r in X; exact X)
              ltac:(pose proof (Iri 2 ltac:(lia)) as X; exact X) ltac:(pose proof (Iri 4 ltac:(lia)) as X; exact X)
              ltac:(pose proof (Iri 6 ltac:(lia)) as X; exact X) ltac:(pose proof (Iri 7 ltac:(lia)) as X; exact X)
              Iwri Igot Ipsz Icf Idpm)
    as (R1 & mA & Hms & A1 & A2 & A8 & A10 & A11 & A12 & A13 & A14 & A15 & A17 & A21 & A22 & AK & EMA).
  exists R1, mA. split; [exact Hms|]. split; [unfold EC; repeat split; assumption|].
  split; [exact A1|]. split; [exact A2|]. split; [exact A8|]. split; [exact A21|]. split; [exact A22|]. split; [exact AK|].
  fold RIv RBv FAv in EMA. rewrite EMA.
  assert (FRd : forall x, 0 <= x < 2^64 -> ~ (SP - 2048 <= x < SP + 16) -> ~ (RIv <= x < RIv + 8) ->
            qmAd m SP CA c (mc_tbl c / 2) RIv RBv FAv (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 1)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 8)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 9)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 19)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 20)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 21)))) mp QC (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 12)))) fsz (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 22)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 23)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 24)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 25)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 26)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 27)))) (wa x) = m (wa x)).
  { intros x Hx Q1 Q3. apply qmAd_frame_f; [clear - G; lia | clear - G; lia | clear - G; lia | exact Hx | exact Q1 | exact Q3]. }
  split; [|exact FRd].
  unfold qMA_OK. split; [|split; [|split; [|split; [|split; [|split]]]]].
  - intros k v Hk K1 K2. apply qmAd_rd3; [clear - G; lia | exact Hk | exact K1 | exact K2].
  - intros k v Hk K1 K2. apply qmAd_rd2; [clear - G; lia | clear - G; lia | clear - G; lia | exact Hk | exact K1 | exact K2].
  - intros k v Hk K1 K2. apply qmAd_rd1; [clear - G; lia | clear - G; lia | clear - G; lia | exact Hk | exact K1 | exact K2].
  - intros x Hx Q1 _ Q3. exact (FRd x Hx Q1 Q3).
  - apply qmAd_rdRI; clear - G; lia.
  - split.
    + apply (rd_frame m); [clear - G Hcr5; lia | cbn; clear - G Hcr5; lia | | exact Imc].
      intros x Hx. cbn in Hx. apply FRd; [clear - G Hcr5 Hx; lia | clear - G Hcr5 Hx; lia | clear - G Hcr5 Hx; lia].
    + apply (rd_frame m); [clear - G Hcr5; lia | cbn; clear - G Hcr5; lia | | exact Isz].
      intros x Hx. cbn in Hx. apply FRd; [clear - G Hcr5 Hx; lia | clear - G Hcr5 Hx; lia | clear - G Hcr5 Hx; lia].
  - apply qmAd_grows.
Qed.
End VB.
