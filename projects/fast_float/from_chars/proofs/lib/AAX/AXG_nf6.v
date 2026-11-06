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

Module AXG_nf4.
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
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_np.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_np.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AxAsan OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_put OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_put2 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_np OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_np2 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_np3 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_np4 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_nf1 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_nf2.AXG_nfsc OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_nf2 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_np.AXG_ms2 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_np.AXG_msc3.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_npscp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_nf2.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_npscp OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_nf2.AXG_nfscp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_nf2.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_nf2.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXF_pc1a AXF_pc1az.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXF_pc1az.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXF_pc1az.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_nf2.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_nf2.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Asan.M.loaded_segments.
Ltac zlh H := clear - H; lia.
Ltac memb' := first [ AxSymRun3.memb_refl | repeat first [left; reflexivity | right] ].      (* [comment removed for export] *)
Ltac lenq' := rewrite ?length_N_to_le_bytes; try change (Z.of_nat 4) with 4 in *; try change (Z.of_nat 8) with 8 in *; try change (Z.of_nat 1) with 1 in *.

Section SC1.
Context {fx : FPState}.
Variable rom : word -> option byte.
Variables (mC : word -> option byte) (R : bvmap 5 word) (c SB SP TP K TSDA PT T mm1 mm2 : Z).
Hypothesis Hc : 2 <= c <= 16.
Hypothesis HSP : 2^46 + 4096 <= SP <= 2^47 /\ SP mod 16 = 0.
Hypothesis HO : objs_ok_p (SP - 2048) T (SB + 137438953472 + 128 * c) TP TSDA PT.
Hypothesis HSB : 17594333495296 <= SB /\ SB mod 4096 = 0 /\ SB + 137438953472 + 4096 <= SP - 2048.
Hypothesis HK : 0 <= K <= 1023.
Hypothesis HSHs : (T + 4096 <= Z.shiftr (SB + 4294967296 * c + 3758096384) 3 + 2147450880 \/ Z.shiftr (SB + 4294967296 * c + 3758096384) 3 + 2147450880 + 32768 <= T) /\
                  (SB + 137438953472 + 128 * c + 128 <= Z.shiftr (SB + 4294967296 * c + 3758096384) 3 + 2147450880 \/ Z.shiftr (SB + 4294967296 * c + 3758096384) 3 + 2147450880 + 32768 <= SB + 137438953472 + 128 * c) /\
                  (TP <= Z.shiftr (SB + 4294967296 * c + 3758096384) 3 + 2147450880 \/ Z.shiftr (SB + 4294967296 * c + 3758096384) 3 + 2147450880 + 32768 <= TP - 88) /\
                  (TSDA + 8192 <= Z.shiftr (SB + 4294967296 * c + 3758096384) 3 + 2147450880 \/ Z.shiftr (SB + 4294967296 * c + 3758096384) 3 + 2147450880 + 32768 <= TSDA) /\
                  (PT + 160 <= Z.shiftr (SB + 4294967296 * c + 3758096384) 3 + 2147450880 \/ Z.shiftr (SB + 4294967296 * c + 3758096384) 3 + 2147450880 + 32768 <= PT).
Hypothesis Hst : 0 <= mm1 < 2^64 /\ 0 <= mm2 < 2^64.
Hypothesis R1 : getr R 1 = wa 481796.
Hypothesis R2 : getr R 2 = wa (SP - 448).
Hypothesis R4 : getr R 4 = wa TP.
Hypothesis R8 : getr R 8 = wa 262144.
Hypothesis R10 : getr R 10 = wa (SB + 4294967296 * c + 3758096384).
Hypothesis R21 : getr R 21 = wa (32 * c).
Hypothesis R22 : getr R 22 = wa 923480.
Hypothesis HSTK : stk_ok SEGS mC (wa SP) 2048.
Hypothesis S88 : rd mC (SP - 448 + 88) 8 515004.
Hypothesis S80 : rd mC (SP - 448 + 80) 8 262144.
Hypothesis S72 : rd mC (SP - 448 + 72) 8 (SB + 4294967296 * c + 3758096384).
Hypothesis S64 : rd mC (SP - 448 + 64) 8 262144.
Hypothesis S56 : rd mC (SP - 448 + 56) 8 (SB + 137438953472 + 128 * c).
Hypothesis S48 : rd mC (SP - 448 + 48) 8 262144.
Hypothesis M24 : rd mC (SP - 352 + 24) 8 271780.
Hypothesis M16 : rd mC (SP - 352 + 16) 8 262144.
Hypothesis M8 : rd mC (SP - 352 + 8) 8 (SB + 4294967296 * c + 3758096384).
Hypothesis M0 : rd mC (SP - 352 + 0) 8 262144.
Hypothesis E40 : rd mC (SP - 280) 8 281044.
Hypothesis E32 : rd mC (SP - 288) 8 (SB + 137438953472 + 128 * c).
Hypothesis E24 : rd mC (SP - 296) 8 (262144 / (32 * c)).
Hypothesis E16 : rd mC (SP - 304) 8 (SB + 4294967296 * c).
Hypothesis E8 : rd mC (SP - 312) 8 (262144 / (32 * c)).
Hypothesis Icf : rd mC 904192 8 1534184.
Hypothesis Icf144 : rd mC (1534184 + 144) 8 0.
Hypothesis Ips1 : rd mC 935452 1 1.
Hypothesis Ips2 : rd mC 904208 8 937400.
Hypothesis Ips3 : rd mC 937400 8 2147450880.
Hypothesis Ips4 : rd mC 904216 8 940712.
Hypothesis Ips5 : rd mC 940712 8 0.
Hypothesis Ips6 : rd mC 904224 8 940720.
Hypothesis Ips7 : rd mC 940720 8 0.
Hypothesis Ips8 : rd mC 904232 8 940704.
Hypothesis Ips9 : rd mC 940704 8 140737488355327.
Hypothesis Ips10 : rd mC 904240 8 912208.
Hypothesis Ips11 : rd mC 912208 8 864392.
Hypothesis Itls1 : rd mC 935456 1 1.
Hypothesis Itls2 : rd mC 935460 4 K.
Hypothesis Itls3 : rd mC (TP - 88) 8 TSDA.
Hypothesis Itls4 : rd mC (TSDA + 8 * K) 8 PT.
Hypothesis Itls5 : rd mC (PT + 152) 8 T.
Hypothesis Imm1 : rd mC (T + 2872) 8 mm1.
Hypothesis Imm2 : rd mC (T + 2880) 8 mm2.
Hypothesis Iwt : wr mC (T + 2872) 16.
Hypothesis Iau : rd mC (SB + 137438953472 + 128 * c + 32) 8 0.
Hypothesis Iwri : wr mC (SB + 137438953472 + 128 * c) 128.
Hypothesis Iwsh : wr mC (Z.shiftr (SB + 4294967296 * c + 3758096384) 3 + 2147450880) 32768.

#[using="K TSDA PT Hc HSP HO HSB HK HSHs Hst R1 R2 R4 R8 R10 R21 R22 HSTK S88 S80 S72 S64 S56 S48 M24 M16 M8 M0 E40 E32 E24 E16 E8 Icf Icf144 Ips1 Ips2 Ips3 Ips4 Ips5 Ips6 Ips7 Ips8 Ips9 Ips10 Ips11 Itls1 Itls2 Itls3 Itls4 Itls5 Imm1 Imm2 Iwt Iau Iwri Iwsh"] Lemma segC1 : exists R' m', msteps SEGS (mkst R (wa 0x73c48) mC rom) (mkst R' (wa 0x449fc) m' rom) /\
  getr R' (Z_to_bv 5 (Z.of_nat 2)) = wa (SP - 272) /\ getr R' (Z_to_bv 5 (Z.of_nat 4)) = wa TP /\
  getr R' (Z_to_bv 5 (Z.of_nat 8)) = wa (SB + 137438953472 + 128 * c) /\ getr R' (Z_to_bv 5 (Z.of_nat 10)) = wa 0 /\
  getr R' (Z_to_bv 5 (Z.of_nat 11)) = wa (SB + 4294967296 * c + 3758096384 + 4 * (262144 / (32 * c))) /\
  getr R' (Z_to_bv 5 (Z.of_nat 12)) = wa 0 /\ getr R' (Z_to_bv 5 (Z.of_nat 13)) = wa 0 /\
  getr R' (Z_to_bv 5 (Z.of_nat 18)) = wa (SB + 4294967296 * c) /\ getr R' (Z_to_bv 5 (Z.of_nat 19)) = wa (262144 / (32 * c)) /\
  getr R' (Z_to_bv 5 (Z.of_nat 21)) = wa (32 * c) /\ getr R' (Z_to_bv 5 (Z.of_nat 22)) = wa 923480 /\
  getr R' (Z_to_bv 5 (Z.of_nat 3)) = getr R (Z_to_bv 5 (Z.of_nat 3)) /\
  (forall x, Z.shiftr (SB + 4294967296 * c + 3758096384) 3 + 2147450880 <= x < Z.shiftr (SB + 4294967296 * c + 3758096384) 3 + 2147450880 + 32768 -> m' (wa x) = Some (Z_to_bv 8 250)) /\
  rd m' (SB + 137438953472 + 128 * c + 24) 8 262144 /\ rd m' (T + 2872) 8 (mm1 + 1) /\ rd m' (T + 2880) 8 (mm2 + 262144) /\
  (forall x, 0 <= x < 2^64 -> ~ (SP - 2048 <= x < SP - 320) ->
     ~ (Z.shiftr (SB + 4294967296 * c + 3758096384) 3 + 2147450880 <= x < Z.shiftr (SB + 4294967296 * c + 3758096384) 3 + 2147450880 + 32768) ->
     ~ (SB + 137438953472 + 128 * c + 24 <= x < SB + 137438953472 + 128 * c + 32) -> ~ (T + 2872 <= x < T + 2888) ->
     m' (wa x) = mC (wa x)) /\ mem_grows mC m'.
Proof. LiaFast.lf_pins (fun (K TSDA PT Hc HSP HO HSB HK HSHs Hst R1 R2 R4 R8 R10 R21 R22 HSTK S88 S80 S72 S64 S56 S48 M24 M16 M8 M0 E40 E32 E24 E16 E8 Icf Icf144 Ips1 Ips2 Ips3 Ips4 Ips5 Ips6 Ips7 Ips8 Ips9 Ips10 Ips11 Itls1 Itls2 Itls3 Itls4 Itls5 Imm1 Imm2 Iwt Iau Iwri Iwsh : LiaFast.U) => LiaFast.u0).
  set (RB := SB + 4294967296 * c) in *. set (RI := SB + 137438953472 + 128 * c) in *.
  replace (SB + 4294967296 * c + 3758096384) with (RB + 3758096384) in * by (unfold RB; ring).
  set (FA := RB + 3758096384) in *.
  set (SH := Z.shiftr FA 3 + 2147450880) in *.
  assert (HSH : SH = FA / 8 + 2147450880) by (unfold SH; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  unfold objs_ok_p, t_place in HO.
  pose proof (new_rng c Hc) as HNEW.
  set (NEW := 262144 / (32 * c)) in *.
  assert (HZ : 2^46 + 4096 <= SP <= 2^47 /\ 2 <= c <= 16 /\ 17594333495296 <= SB /\ SB mod 4096 = 0 /\
               SB + 137438953472 + 4096 <= SP - 2048 /\ RB = SB + 4294967296 * c /\ RI = SB + 137438953472 + 128 * c /\ FA = RB + 3758096384 /\
               SH = FA / 8 + 2147450880 /\
               ((4096 <= T /\ T + 4096 <= 65536) \/ 6529024 <= T) /\ T + 4096 <= SP - 2048 - 256 /\ 4096 <= TP /\ TP <= SP - 2048 - 256 /\
               1 <= TSDA /\ TSDA + 8192 <= SP - 2048 - 256 /\ 1 <= PT /\ PT + 160 <= SP - 2048 - 256 /\ 0 <= K <= 1023 /\
               0 <= mm1 < 2^64 /\ 0 <= mm2 < 2^64 /\ 512 <= NEW <= 4096) by (clear - Hc HSP HO HSB HK Hst HSH HNEW; unfold FA, RB, RI, NEW in *; lia).
  assert (HD1 : RI + 128 <= T \/ T + 4096 <= RI) by (clear - HO; unfold RI; tauto).
  assert (HD2 : T + 4096 <= SH \/ SH + 32768 <= T) by (clear - HSHs; tauto).
  assert (HD3 : RI + 128 <= SH \/ SH + 32768 <= RI) by (clear - HSHs; tauto).
  assert (HD4 : TP <= SH \/ SH + 32768 <= TP - 88) by (clear - HSHs; tauto).
  assert (HD5 : TSDA + 8192 <= SH \/ SH + 32768 <= TSDA) by (clear - HSHs; tauto).
  assert (HD6 : PT + 160 <= SH \/ SH + 32768 <= PT) by (clear - HSHs; tauto).
  clear HSP HO HSB HK Hst HSHs HSH.
  assert (HSPa : bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 2))) = SP - 448) by (rgz; rewrite R2, u_wa_small by (zlh HZ); reflexivity).
  (* [comment removed for export] *)
  assert (P1 : OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_nf2.AXF_mf1z.mf1_pre R mC FA 262144 1534184 515004 262144 FA 262144 RI 262144).
  { constructor; [exact R1 | exact R8 | exact R10
                 | (rewrite R2; apply (stk_ok_move mC SP (SP - 448) 1024); [(zlh HZ) | (zlh HZ) | exact HSTK | (zlh HZ) | (zlh HZ) | (zlh HZ)])
                 | (zlh HZ) | (zlh HZ) | (zlh HZ) | (zlh HZ) | (zlh HZ) | (zlh HZ) | (zlh HZ) | (zlh HZ) | (zlh HZ) | (zlh HZ) | rewrite HSPa; (zlh HZ) | | | | | | | | | ].
    all: try (rewrite HSPa; assumption).
    - intros d k Hd Hk. rewrite HSPa. apply HSTK; rewrite !u_wa_small; clear - HZ Hd Hk; lia.
    - exact Icf.
    - exact Icf144. }
  destruct (OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_nf2.AXF_mf1z.mf1_pmf1 R mC rom FA 262144 1534184 515004 262144 FA 262144 RI 262144 P1
              (sc_mf1 R mC (SP - 448) FA 262144 1534184 515004 262144 FA 262144 RI 262144 HSPa ltac:((zlh HZ))))
    as (Ra & Hms & A1 & A2 & A8 & A9 & A10 & A11 & A12 & A13 & A18 & A19 & A20 & KKa).
  clear P1 A11 A12 A13.
  set (m1 := OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_nf2.AXF_mf1z.mf1_mem_pmf1 mC R FA 262144 1534184 515004 262144 FA 262144 RI 262144) in *.
  assert (EM1 : m1 = wchainS mC SP [(-404, 4%nat, 18446744072277895850)]) by (unfold m1, OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_nf2.AXF_mf1z.mf1_mem_pmf1; rewrite HSPa, sub_add_lit; reflexivity).
  clearbody m1.
  assert (G1 : mem_grows mC m1) by (rewrite EM1; apply wchainS_grows).
  assert (F1 : forall x, 0 <= x < 2^64 -> ~ (SP - 2048 <= x < SP - 320) -> m1 (wa x) = mC (wa x)).
  { intros x Hx Q. rewrite EM1. apply (wchainS_frame_in _ mC SP (-404) (-400)); [(zlh HZ) | (zlh HZ) | reflexivity | reflexivity | exact Hx | clear - HZ Q; lia]. }
  assert (F1' : forall x, 0 <= x < 2^64 -> ~ (SP - 404 <= x < SP - 400) -> m1 (wa x) = mC (wa x)).
  { intros x Hx Q. rewrite EM1. apply (wchainS_frame_in _ mC SP (-404) (-400)); [(zlh HZ) | (zlh HZ) | reflexivity | reflexivity | exact Hx | clear - HZ Q; lia]. }
  regzH A1. regzH A2. regzH A8. regzH A9. regzH A10. regzH A18. regzH A19. regzH A20.
  assert (HSPb : bv_unsigned (getr Ra (Z_to_bv 5 (Z.of_nat 2))) = SP - 352) by (rewrite A2, HSPa, u_wa_small by (zlh HZ); ring).
  (* [comment removed for export] *)
  assert (P2 : AXF_pc1az.pc1a_pre Ra m1 FA 262144 262144).
  { constructor; [regzG; exact A1 | regzG; exact A10
                 | (replace (getr Ra 2) with (wa (SP - 352)) by (regzG; rewrite A2, HSPa; f_equal; ring);
                    apply (stk_ok_move m1 SP (SP - 352) 1024); [(zlh HZ) | (zlh HZ) | exact (stk_ok_grows mC m1 (wa SP) 2048 G1 HSTK) | (zlh HZ) | (zlh HZ) | (zlh HZ)])
                 | (zlh HZ) | (zlh HZ) | (zlh HZ) | (zlh HZ) | (zlh HZ) | rewrite HSPb; (zlh HZ) | | | | | | | | | | | | | | | | ].
    all: try (rewrite HSPb; apply (rd_frame mC m1); [(zlh HZ) | lenq'; (zlh HZ) | intros x Hx; lenq'; apply F1'; clear - HZ Hx; lia | assumption]).
    all: try (apply (rd_frame mC m1); [(zlh HZ) | lenq'; (zlh HZ) | intros x Hx; lenq'; apply F1; clear - HZ Hx; lia | assumption]).
    intros d k Hd Hk. rewrite HSPb. apply (store_ok_mono SEGS k mC m1 _ G1). apply HSTK; rewrite !u_wa_small; clear - HZ Hd Hk; lia. }
  destruct (AXF_pc1az.pc1a_ppc1a Ra m1 rom FA 262144 262144 P2 ltac:(cbn [AXF_pc1a.RES_ppc1a fst snd]; constructor))
    as (Rb & Hms2 & B1 & B2 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12 & B13 & B14 & B15 & B16 & B17 & B18 & B28 & KKb).
  clear P2 B5 B6 B7 B13 B14 B15 B16 B17 B28.
  pose proof (msteps_trans SEGS _ _ _ Hms Hms2) as Hms'. clear Hms Hms2. rename Hms' into Hms.
  set (m2 := AXF_pc1az.pc1a_mem_ppc1a m1 Ra FA 262144 262144) in *.
  assert (V21 : bv_unsigned (getr Ra (Z_to_bv 5 (Z.of_nat 21))) = 32 * c) by (rewrite (KKa 21%nat ltac:(cbn; memb')); regzH R21; rewrite R21, u_wa_small by (zlh HZ); reflexivity).
  assert (EM2 : m2 = wchainS m1 SP [(-376, 8%nat, 32 * c); (-368, 8%nat, 262144); (-360, 8%nat, RI); (-352, 8%nat, 262144); (-344, 8%nat, FA); (-336, 8%nat, 262144); (-328, 8%nat, 271808)]).
  { unfold m2, AXF_pc1az.pc1a_mem_ppc1a. rewrite HSPb, A19, A20, V21, ?u_wa_small by (zlh HZ). rewrite ?sub_add_lit. reflexivity. }
  clearbody m2.
  assert (G2 : mem_grows mC m2) by (rewrite EM2; exact (mem_grows_trans _ _ _ G1 (wchainS_grows _ m1 SP))).
  assert (F2 : forall x, 0 <= x < 2^64 -> ~ (SP - 2048 <= x < SP - 320) -> m2 (wa x) = mC (wa x)).
  { intros x Hx Q. rewrite EM2. rewrite (wchainS_frame_in [(-376, 8%nat, 32 * c); (-368, 8%nat, 262144); (-360, 8%nat, RI); (-352, 8%nat, 262144); (-344, 8%nat, FA); (-336, 8%nat, 262144); (-328, 8%nat, 271808)] m1 SP (-376) (-320));
      [| clear - HZ; lia | clear - HZ; lia | reflexivity | reflexivity | exact Hx | clear - HZ Q; lia]. apply F1; assumption. }
  (* [comment removed for export] *)
  regzH B10. regzH B11. regzH B12. regzH B1. regzH B9. regzH B18.
  assert (B12' : getr Rb (Z_to_bv 5 (Z.of_nat 12)) = wa 32768).
  { rewrite B12. f_equal. rewrite Z.mod_small by (zlh HZ). rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
    assert (HF8 : FA mod 8 = 0).
    { destruct HZ as (_ & _ & _ & HSBm & _ & HRB & _ & HFA & _). rewrite HFA, HRB. clear - HSBm.
      pose proof (Z.div_mod SB 4096 ltac:(lia)) as E. rewrite HSBm, Z.add_0_r in E. rewrite E.
      replace (4096 * (SB / 4096) + 4294967296 * c + 3758096384) with ((512 * (SB / 4096) + 536870912 * c + 469762048) * 8) by ring. apply Z.mod_mul. lia. }
    assert (E8d : (FA + 262144 + -8) / 8 = FA / 8 + 32767) by (rewrite (Z.div_mod FA 8) at 1 by lia; rewrite HF8; replace (8 * (FA / 8) + 0 + 262144 + -8) with ((FA / 8 + 32767) * 8) by ring; apply Z.div_mul; lia).
    rewrite E8d. ring. }
  destruct (memsetck_contract rom Rb m2 SH 32768 ltac:(regzG; rewrite B10; unfold SH; reflexivity) ltac:(regzG; exact B12') ltac:((zlh HZ)) ltac:(lia) ltac:((zlh HZ)))
    as (Rc & m3 & Hms3 & KKc & MS1 & MS2 & G3).
  { intros d k Hd Hk. apply (store_ok_mono SEGS k mC m2 _ G2). apply Iwsh; clear - Hd Hk; lia. }
  regzH MS1. rewrite B11 in MS1. change (bv_unsigned (wa 250) mod 256) with 250 in MS1.
  pose proof (msteps_trans SEGS _ _ _ Hms Hms3) as Hms'. clear Hms Hms3. rename Hms' into Hms.
  (* [comment removed for export] *)
  assert (P4 : OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXF_pc1az.AXF_rt2z.rt2_pre Rc m3 0) by (constructor; [regzG; rewrite (KKc 1%nat ltac:(cbn; memb')); exact B1 | lia]).
  destruct (OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXF_pc1az.AXF_rt2z.rt2_prt2 Rc m3 rom 0 P4 ltac:(cbn [OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXF_pc1az.AXF_rt2.RES_prt2 fst snd]; constructor)) as (Rd & Hms4 & C1 & KKd).
  assert (Em4 : OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXF_pc1az.AXF_rt2z.rt2_mem_prt2 m3 Rc 0 = m3) by reflexivity. rewrite Em4 in Hms4. clear Em4 P4.
  pose proof (msteps_trans SEGS _ _ _ Hms Hms4) as Hms'. clear Hms Hms4. rename Hms' into Hms.
  assert (F3 : forall x, 0 <= x < 2^64 -> ~ (SP - 2048 <= x < SP - 320) -> ~ (SH <= x < SH + 32768) -> m3 (wa x) = mC (wa x)).
  { intros x Hx Q1 Q2. rewrite MS2 by assumption. apply F2; assumption. }
  (* [comment removed for export] *)
  assert (KR : forall k, In k [2; 3; 4; 8; 9; 18; 19; 20; 21; 22]%nat -> getr Rd (Z_to_bv 5 (Z.of_nat k)) = getr Rb (Z_to_bv 5 (Z.of_nat k))).
  { intros k Hk. rewrite (KKd k ltac:(clear - Hk; cbn in Hk |- *; repeat (destruct Hk as [<-|Hk]; [memb'|]); destruct Hk)).
    apply KKc. clear - Hk; cbn in Hk |- *; repeat (destruct Hk as [<-|Hk]; [memb'|]); destruct Hk. }
  regzH B2. regzH B8.
  assert (KRb : forall k, In k [3; 4; 19; 20; 21; 22]%nat -> getr Rb (Z_to_bv 5 (Z.of_nat k)) = getr Ra (Z_to_bv 5 (Z.of_nat k))).
  { intros k Hk. apply KKb. clear - Hk; cbn in Hk |- *; repeat (destruct Hk as [<-|Hk]; [memb'|]); destruct Hk. }
  assert (HSPd : bv_unsigned (getr Rd (Z_to_bv 5 (Z.of_nat 2))) = SP - 320) by (rewrite (KR 2%nat ltac:(cbn; memb')), B2, HSPb, u_wa_small by (zlh HZ); ring).
  regzH R4. regzH R21. regzH R22.
  assert (P5 : OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_nf2.AXF_pc1bz.pc1b_pre Rd m3 RI RB (32 * c) NEW TP K TSDA PT T mm1 mm2).
  { constructor; [regzG; rewrite (KR 4%nat ltac:(cbn; memb')), (KRb 4%nat ltac:(cbn; memb')), (KKa 4%nat ltac:(cbn; memb')); exact R4
                 | regzG; rewrite (KR 8%nat ltac:(cbn; memb')); exact B8
                 | regzG; rewrite (KR 9%nat ltac:(cbn; memb')); exact B9
                 | regzG; rewrite (KR 18%nat ltac:(cbn; memb')); exact B18
                 | regzG; rewrite (KR 19%nat ltac:(cbn; memb')), (KRb 19%nat ltac:(cbn; memb')); exact A19
                 | regzG; rewrite (KR 20%nat ltac:(cbn; memb')), (KRb 20%nat ltac:(cbn; memb')); exact A20
                 | regzG; rewrite (KR 21%nat ltac:(cbn; memb')), (KRb 21%nat ltac:(cbn; memb')), (KKa 21%nat ltac:(cbn; memb')); exact R21
                 | regzG; rewrite (KR 22%nat ltac:(cbn; memb')), (KRb 22%nat ltac:(cbn; memb')), (KKa 22%nat ltac:(cbn; memb')); exact R22
                 | (replace (getr Rd 2) with (wa (SP - 320)) by (regzG; rewrite (KR 2%nat ltac:(cbn; memb')), B2, HSPb; f_equal; ring);
                    apply (stk_ok_move m3 SP (SP - 320) 1024); [(zlh HZ) | (zlh HZ) | exact (stk_ok_grows mC m3 (wa SP) 2048 (mem_grows_trans _ _ _ G2 G3) HSTK) | (zlh HZ) | (zlh HZ) | (zlh HZ)])
                 | .. ].
    all: try (zlh HZ).
    all: try (rewrite HSPd; (zlh HZ)).
    all: try (rewrite hko by (zlh HZ); rewrite Z.add_0_r).
    all: try (rewrite HSPd; replace (SP - 320 + 40) with (SP - 280) by ring; replace (SP - 320 + 32) with (SP - 288) by ring;
              replace (SP - 320 + 24) with (SP - 296) by ring; replace (SP - 320 + 16) with (SP - 304) by ring; replace (SP - 320 + 8) with (SP - 312) by ring).
    all: first [ (apply (rd_frame mC m3); [(zlh HZ) | lenq'; (zlh HZ) | intros x Hx; lenq'; apply F3; [clear - HZ Hx; lia | clear - HZ Hx; lia | first [clear - HZ Hx; lia | clear - HZ HD2 Hx; lia | clear - HZ HD3 Hx; lia | clear - HZ HD4 Hx; lia | clear - HZ HD5 Hx; lia | clear - HZ HD6 Hx; lia]] | assumption])
               | (intros d k Hd Hk; apply (store_ok_mono SEGS k mC m3 _ (mem_grows_trans _ _ _ G2 G3));
                  first [ (replace (T + 2872 + d) with (T + 2872 + (0 + d)) by ring; apply Iwt; clear - Hd Hk; lia)
                        | (replace (T + 2880 + d) with (T + 2872 + (8 + d)) by ring; apply Iwt; clear - Hd Hk; lia)
                        | (replace (RI + 24 + d) with (RI + (24 + d)) by ring; apply Iwri; clear - Hd Hk; lia) ]) ]. }
  destruct (OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_nf2.AXF_pc1bz.pc1b_ppc1b Rd m3 rom RI RB (32 * c) NEW TP K TSDA PT T mm1 mm2 P5
              (sc_pc1b_p Rd m3 (SP - 320) RI RB (32 * c) NEW TP K TSDA PT T mm1 mm2 HSPd ltac:(unfold objs_ok_p, t_place; clear - HZ HD1; lia) ltac:((zlh HZ))))
    as (Re & Hms5 & D1 & D2 & D4 & D8 & D9 & D10 & D11 & D12 & D13 & D18 & D19 & D20 & D21 & D22 & KKe).
  clear P5.
  pose proof (msteps_trans SEGS _ _ _ Hms Hms5) as Hms'. clear Hms Hms5. rename Hms' into Hms.
  set (m4 := OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_nf2.AXF_pc1bz.pc1b_mem_ppc1b m3 Rd RI RB (32 * c) NEW TP K TSDA PT T mm1 mm2) in *.
  assert (EM4 : m4 = wbytes (wbytes (wbytes (wchainS m3 SP [(-344, 8%nat, 436892); (-328, 8%nat, 271812)])
                        (wa (T + 2872)) (word_to_le_bytes 8 (wa (mm1 + 1)))) (wa (T + 2880)) (word_to_le_bytes 8 (wa (mm2 + 262144))))
                        (wa (RI + 24)) (word_to_le_bytes 8 (wa 262144))).
  { unfold m4, OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_nf2.AXF_pc1bz.pc1b_mem_ppc1b. rewrite HSPd, ?sub_add_lit. reflexivity. }
  clearbody m4.
  assert (G4 : mem_grows mC m4).
  { apply (mem_grows_trans _ m3 _ (mem_grows_trans _ _ _ G2 G3)). rewrite EM4.
    repeat apply grows_wb. first [apply wchainS_grows | apply mem_grows_refl]. }
  assert (F4 : forall x, 0 <= x < 2^64 -> ~ (SP - 2048 <= x < SP - 320) -> ~ (SH <= x < SH + 32768) -> ~ (RI + 24 <= x < RI + 32) ->
                 ~ (T + 2872 <= x < T + 2888) -> m4 (wa x) = mC (wa x)).
  { intros x Hx Q1 Q2 Q3 Q5. rewrite EM4.
    repeat (rewrite wb_other by first [exact Hx | (lenq'; clear - HZ; lia) | (lenq'; clear - HZ Q3 Q5; lia)]).
    rewrite (wchainS_frame_in [(-344, 8%nat, 436892); (-328, 8%nat, 271812)] _ SP (-344) (-320));
      [| clear - HZ; lia | clear - HZ; lia | reflexivity | reflexivity | exact Hx | clear - HZ Q1; lia].
    apply F3; assumption. }
  regzH D2. regzH D4. regzH D8. regzH D10. regzH D11. regzH D12. regzH D13. regzH D18. regzH D19. regzH D21. regzH D22.
  exists Re, m4. split; [exact Hms|].
  split; [rewrite D2, HSPd; f_equal; ring|]. split; [exact D4|]. split; [exact D8|]. split; [exact D10|].
  split; [rewrite D11; f_equal; unfold FA; ring|]. split; [exact D12|]. split; [exact D13|]. split; [exact D18|]. split; [exact D19|].
  split; [exact D21|]. split; [exact D22|].
  split; [rewrite (KKe 3%nat ltac:(cbn; memb')), (KKd 3%nat ltac:(cbn; memb')), (KKc 3%nat ltac:(cbn; memb')), (KKb 3%nat ltac:(cbn; memb')), (KKa 3%nat ltac:(cbn; memb')); reflexivity|].
  split.
  { intros x Hx. rewrite EM4.
    repeat (rewrite wb_other by first [(clear - HZ Hx; lia) | (lenq'; clear - HZ; lia) | (lenq'; clear - HZ HD2 HD3 Hx; lia)]).
    rewrite (wchainS_frame_in [(-344, 8%nat, 436892); (-328, 8%nat, 271812)] _ SP (-344) (-320));
      [| clear - HZ; lia | clear - HZ; lia | reflexivity | reflexivity | clear - HZ Hx; lia | clear - HZ Hx; lia].
    apply MS1. exact Hx. }
  split; [rewrite EM4; apply wb_rd_hit; lenq'; (zlh HZ)|].
  split.
  { rewrite EM4. apply (rd_frame (wbytes (wchainS m3 SP [(-344, 8%nat, 436892); (-328, 8%nat, 271812)]) (wa (T + 2872)) (word_to_le_bytes 8 (wa (mm1 + 1)))));
      [(zlh HZ) | cbn; (zlh HZ) | intros x Hx; cbn in Hx; repeat (rewrite wb_other by first [(clear - HZ Hx; lia) | (lenq'; clear - HZ; lia) | (lenq'; clear - HZ HD1 Hx; lia)]); reflexivity |].
    apply wb_rd_hit; lenq'; (zlh HZ). }
  split.
  { rewrite EM4. apply (rd_frame (wbytes (wbytes (wchainS m3 SP [(-344, 8%nat, 436892); (-328, 8%nat, 271812)]) (wa (T + 2872)) (word_to_le_bytes 8 (wa (mm1 + 1)))) (wa (T + 2880)) (word_to_le_bytes 8 (wa (mm2 + 262144)))));
      [(zlh HZ) | cbn; (zlh HZ) | intros x Hx; cbn in Hx; repeat (rewrite wb_other by first [(clear - HZ Hx; lia) | (lenq'; clear - HZ; lia) | (lenq'; clear - HZ HD1 Hx; lia)]); reflexivity |].
    apply wb_rd_hit; lenq'; (zlh HZ). }
  split; [exact F4 | exact G4].
Qed.
End SC1.
End AXG_nf4.


Module AXG_nf5.
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
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_nf2.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_nf2.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXF_ngtz.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXF_ngtz.
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

Section SC2.
Context {fx : FPState}.
Variable rom : word -> option byte.
Variables (m : word -> option byte) (R : bvmap 5 word) (CA ND c SB SP na st v1 v8 v9 v18 v19 v20 g21 g22 g23 g24 g25 g26 g27 : Z).
Hypothesis Hc : c = (ND + 31) / 32.
Hypothesis HND : 33 <= ND <= 512.
Hypothesis HSP : 2^46 + 4096 <= SP <= 2^47 /\ SP mod 16 = 0.
Hypothesis HCA : ((4304 <= CA /\ CA + 3888 <= 65536) \/ 6529232 <= CA) /\ CA mod 16 = 0 /\ CA + 4096 <= SP - 2048.
Hypothesis HSB : 17594333495296 <= SB /\ SB mod 4096 = 0 /\ SB + 137438953472 + 4096 <= SP - 2048.
Hypothesis HSEP : CA + 2592 <= SB \/ SB + 137438953472 + 4096 <= CA.
Hypothesis Hvals : 0 <= na < 2^64 /\ 0 <= st < 2^64.
Hypothesis R2 : getr R 2 = wa (SP - 272).
Hypothesis R8 : getr R 8 = wa (SB + 137438953472 + 128 * c).
Hypothesis R10 : getr R 10 = wa 0.
Hypothesis R11 : getr R 11 = wa (SB + 4294967296 * c + 3758096384 + 4 * (262144 / (32 * c))).
Hypothesis R12 : getr R 12 = wa 0.
Hypothesis R13 : getr R 13 = wa 0.
Hypothesis R19 : getr R 19 = wa (262144 / (32 * c)).
Hypothesis R21 : getr R 21 = wa (32 * c).
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
Hypothesis G96 : rd m (SP - 112) 8 8.
Hypothesis G88 : rd m (SP - 120) 8 CA.
Hypothesis G80 : rd m (SP - 128) 8 923480.
Hypothesis G72 : rd m (SP - 136) 8 g21.
Hypothesis G64 : rd m (SP - 144) 8 g22.
Hypothesis G56 : rd m (SP - 152) 8 g23.
Hypothesis G48 : rd m (SP - 160) 8 g24.
Hypothesis G40 : rd m (SP - 168) 8 g25.
Hypothesis G32 : rd m (SP - 176) 8 g26.
Hypothesis G24 : rd m (SP - 184) 8 g27.
Hypothesis C136 : rd m (SP - 72) 8 (CA + 80 * c).
Hypothesis C144 : rd m (SP - 64) 8 c.
Hypothesis C152 : rd m (SP - 56) 8 278424.
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
Hypothesis Isz : rd m (CA + 80 * c + 8) 8 (32 * c).
Hypothesis Iwc : wr m CA 2592.
Hypothesis ISB : rd m 923512 8 SB.
Hypothesis IRIB : rd m 923528 8 (SB + 137438953472).
Hypothesis Ist : rd m (CA + 2576) 8 st.
Hypothesis Iwfa : wr m (SB + 4294967296 * c + 3758096384) 262144.
Hypothesis HIMG : forall i, 65536 <= i < 143360 -> m (Z_to_bv 64 i) = None.

#[using="ND na st Hc HND HSP HCA HSB HSEP Hvals R2 R8 R10 R11 R12 R13 R19 R21 HSTK Q56 Q48 Q40 Q32 Q24 Q16 Q8 Q0 G120 G112 G104 G96 G88 G80 G72 G64 G56 G48 G40 G32 G24 C136 C144 C152 C160 C168 C176 C184 C192 C200 Hgv Imu Inf0 Iau Iau40 Imapu Imeta Ina Iwri Imc Isz Iwc ISB IRIB Ist Iwfa HIMG"] Lemma segC2 : exists R' m', msteps SEGS (mkst R (wa 0x449fc) m rom) (mkst R' (wa 0x43f08) m' rom) /\
  getr R' (Z_to_bv 5 (Z.of_nat 2)) = wa SP /\ getr R' (Z_to_bv 5 (Z.of_nat 10)) = wa (SB + 4294967296 * c) /\
  getr R' (Z_to_bv 5 (Z.of_nat 1)) = wa v1 /\ getr R' (Z_to_bv 5 (Z.of_nat 8)) = wa v8 /\ getr R' (Z_to_bv 5 (Z.of_nat 9)) = wa v9 /\
  getr R' (Z_to_bv 5 (Z.of_nat 18)) = wa v18 /\ getr R' (Z_to_bv 5 (Z.of_nat 19)) = wa v19 /\ getr R' (Z_to_bv 5 (Z.of_nat 20)) = wa v20 /\
  getr R' (Z_to_bv 5 (Z.of_nat 21)) = wa g21 /\ getr R' (Z_to_bv 5 (Z.of_nat 22)) = wa g22 /\ getr R' (Z_to_bv 5 (Z.of_nat 23)) = wa g23 /\
  getr R' (Z_to_bv 5 (Z.of_nat 24)) = wa g24 /\ getr R' (Z_to_bv 5 (Z.of_nat 25)) = wa g25 /\ getr R' (Z_to_bv 5 (Z.of_nat 26)) = wa g26 /\
  getr R' (Z_to_bv 5 (Z.of_nat 27)) = wa g27 /\
  (forall k, In k [3; 4]%nat -> getr R' (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k))) /\
  INV_C m' CA SB c (32 * c) (mc_tbl c / 2) (262144 / (32 * c)) 1 /\
  (forall x, 0 <= x < 2^64 -> ~ (SB + 4294967296 * c + 3758096384 <= x < SB + 4294967296 * c + 3758096384 + 262144) ->
     ~ owned_C CA SB c x -> m' (wa x) = m (wa x)) /\ mem_grows m m'.
Proof. LiaFast.lf_pins (fun (ND na st Hc HND HSP HCA HSB HSEP Hvals R2 R8 R10 R11 R12 R13 R19 R21 HSTK Q56 Q48 Q40 Q32 Q24 Q16 Q8 Q0 G120 G112 G104 G96 G88 G80 G72 G64 G56 G48 G40 G32 G24 C136 C144 C152 C160 C168 C176 C184 C192 C200 Hgv Imu Inf0 Iau Iau40 Imapu Imeta Ina Iwri Imc Isz Iwc ISB IRIB Ist Iwfa HIMG : LiaFast.U) => LiaFast.u0).
  assert (HC5 : Z.shiftr ((ND + 31) mod 2^64) 5 = c) by (rewrite Hc; apply c_of_nd; exact HND).
  pose proof (c_of_nd_range ND HND) as Hcr5. rewrite <- Hc in Hcr5.
  pose proof (mc_tbl_rng c Hcr5) as [Hmc Hmc2].
  set (nc := mc_tbl c / 2) in *.
  assert (Hnc : 2 <= nc <= 8 /\ mc_tbl c = 2 * nc).
  { unfold nc. pose proof (Z.div_mod (mc_tbl c) 2 ltac:(lia)) as E. rewrite Hmc2, Z.add_0_r in E. lia. }
  set (RB := SB + 4294967296 * c) in *. set (RI := SB + 137438953472 + 128 * c) in *.
  replace (SB + 4294967296 * c + 3758096384) with (RB + 3758096384) in * by (unfold RB; ring).
  set (FA := RB + 3758096384) in *. set (REC := CA + 80 * c) in *.
  pose proof (new_rng c Hcr5) as HNEW.
  set (NEW := 262144 / (32 * c)) in *.
  assert (HZ : 2^46 + 4096 <= SP <= 2^47 /\ 2 <= c <= 16 /\ 33 <= ND <= 512 /\ ((4304 <= CA /\ CA + 3888 <= 65536) \/ 6529232 <= CA) /\ CA mod 16 = 0 /\ CA + 4096 <= SP - 2048 /\
               17594333495296 <= SB /\ SB mod 4096 = 0 /\ SB + 137438953472 + 4096 <= SP - 2048 /\
               (CA + 2592 <= SB \/ SB + 137438953472 + 4096 <= CA) /\
               RB = SB + 4294967296 * c /\ RI = SB + 137438953472 + 128 * c /\ FA = RB + 3758096384 /\ REC = CA + 80 * c /\
               0 <= na < 2^64 /\ 0 <= st < 2^64 /\ 512 <= NEW <= 4096 /\ NEW * (32 * c) <= 262144 /\ 2 <= nc <= 8)
    by (clear - HSP Hcr5 HND HCA HSB HSEP Hvals HNEW Hnc; unfold FA, RB, RI, REC in *; lia).
  assert (HY : 2^46 + 4096 <= SP <= 2^47 /\ 2 <= c <= 16 /\ 33 <= ND <= 512 /\ ((4304 <= CA /\ CA + 3888 <= 65536) \/ 6529232 <= CA) /\ CA + 4096 <= SP - 2048 /\
               17594333495296 <= SB /\ SB + 137438953472 + 4096 <= SP - 2048 /\
               (CA + 2592 <= SB \/ SB + 137438953472 + 4096 <= CA) /\
               RB = SB + 4294967296 * c /\ RI = SB + 137438953472 + 128 * c /\ FA = RB + 3758096384 /\ REC = CA + 80 * c /\
               0 <= na < 2^64 /\ 0 <= st < 2^64 /\ 512 <= NEW <= 4096 /\ 2 <= nc <= 8) by (clear - HZ; lia).
  assert (HS : 2^46 + 4096 <= SP <= 2^47) by (zlh HY).
  assert (HOB : 4096 <= FA /\ FA + 262144 <= RI /\ RI + 128 <= SP - 2048 /\ 4304 <= CA /\ CA + 4096 <= SP - 2048 /\ CA + 160 <= REC /\
                REC + 80 <= CA + 1360 /\ 2 <= nc <= 8 /\ (CA + 4096 <= FA \/ RI + 128 <= CA) /\ SP <= 2^47) by (zlh HY).
  clear HSP HCA HSB HSEP Hvals Hcr5.
  assert (HSPa : bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 2))) = SP - 272) by (rgz; rewrite R2, u_wa_small by (zlh HY); reflexivity).
  (* [comment removed for export] *)
  destruct (pfa_loop rom (Z.to_nat NEW) R m FA NEW 0 (32 * c) ltac:((zlh HY)) R10
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
  assert (P2 : OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_nf2.AXF_pc2z.pc2_pre Ra m1 RI (32 * c) NEW FA (REC + 16) nc).
  { constructor; [regzG; rewrite (KKa 8%nat ltac:(cbn; memb')); exact R8 | regzG; exact A10
                 | regzG; rewrite (KKa 19%nat ltac:(cbn; memb')); exact R19 | regzG; rewrite (KKa 21%nat ltac:(cbn; memb')); exact R21
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
  destruct (OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_nf2.AXF_pc2z.pc2_ppc2 Ra m1 rom RI (32 * c) NEW FA (REC + 16) nc P2
              (sc_pc2 Ra m1 (SP - 272) RI (32 * c) NEW FA (REC + 16) nc HSPb V13 ltac:((zlh HZ))))
    as (Rb & Hms2 & B1 & B2 & B8 & B9 & B10 & B11 & B13 & B14 & B15 & B18 & B19 & B20 & B21 & B22 & KKb).
  clear P2 B1 B9 B10 B15 B18 B21 B22.
  pose proof (msteps_trans SEGS _ _ _ Hms Hms2) as Hms'. clear Hms Hms2. rename Hms' into Hms.
  set (m2 := OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_nf2.AXF_pc2z.pc2_mem_ppc2 m1 Ra RI (32 * c) NEW FA (REC + 16) nc) in *.
  assert (EM2 : m2 = wbytes (wbytes (wbytes (wbytes m1 (wa (RI + 16)) (word_to_le_bytes 8 (wa NEW))) (wa (RI + 32)) (word_to_le_bytes 8 (wa (NEW * (32 * c)))))
                        (wa (RI + 68)) (word_to_le_bytes 1 (wa 0))) (wa (RI + 16)) (word_to_le_bytes 8 (wa (NEW + -1 * nc)))).
  { unfold m2, OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_nf2.AXF_pc2z.pc2_mem_ppc2. rewrite V13, Z.add_0_l. reflexivity. }
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
  assert (LW : forall i, 0 <= i < Z.of_nat (Z.to_nat nc) -> 0 <= (nc - 1 - i) * (2 * c) < 2^31 /\
                 rd m2 (FA + 4 * (NEW - nc) + 4 * i) 4 ((nc - 1 - i) * (2 * c))).
  { intros i Hi. rewrite Z2Nat.id in Hi by (zlh HY).
      split; [assert (Hq1 : 0 <= nc - 1 - i <= 7) by (clear - HOB Hi; lia); assert (Hq2 : 4 <= 2 * c <= 32) by (zlh HY); clear - Hq1 Hq2; nia|].
    pose proof (RD1 (nc - 1 - i) ltac:(clear - HY Hi; lia)) as Rf. rewrite Z.add_0_l, div16_32c in Rf.
    replace (FA + 4 * (NEW - 1 - (nc - 1 - i))) with (FA + 4 * (NEW - nc) + 4 * i) in Rf by ring.
    apply (rd_frame m1 m2); [clear - HY Hi; lia | lenq'; clear - HY Hi; lia | | exact Rf].
    intros x Hx. lenq'. rewrite EM2. repeat (rewrite wb_other by first [(clear - HY Hi Hx; lia) | (lenq'; clear - HY; lia) | (lenq'; clear - HY Hi Hx; lia)]). reflexivity. }
  assert (LWR : wr m2 (REC + 16) (4 * Z.of_nat (Z.to_nat nc))).
  { intros d k Hd Hk. rewrite Z2Nat.id in Hk by (clear - HY; lia). apply (store_ok_mono SEGS k m m2 _ G2).
    replace (REC + 16 + d) with (CA + (80 * c + 16 + d)) by (unfold REC; ring). apply Iwc; clear - HY Hd Hk; lia. }
  destruct (ngl_loop rom (Z.to_nat nc) Rb m2 (FA + 4 * (NEW - nc)) (REC + 16) (fun i => (nc - 1 - i) * (2 * c)) ltac:((zlh HY)) L11 L13 L20
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
  assert (P4 : AXF_ngtz.ngt_pre Rc m3 CA ND nc SB (SB + 137438953472) na 0 (32 * c) st 0 0 0 0 g21 g22 g23 g24 g25 g26 g27 v9 v18 v19 v20 v8 v1).
  { constructor.
    all: try (clear - Hgv; lia).
    all: try (zlh HY).
    all: try (rewrite HSPd; (zlh HS)).
    all: try (zlh HZ).
    - regzG. rewrite (KKc 8%nat ltac:(cbn; memb')), B8, HC5. reflexivity.
    - regzG. rewrite (KKc 14%nat ltac:(cbn; memb')). exact B14.
    - regzG. rewrite (KKc 19%nat ltac:(cbn; memb')). exact B19.
    - replace (getr Rc 2) with (wa (SP - 208)) by (regzG; rewrite (KKc 2%nat ltac:(cbn; memb')), B2, HSPb; f_equal; ring).
      apply (stk_ok_move m3 SP (SP - 208) 1024); [(zlh HY) | (zlh HY) | exact (stk_ok_grows m m3 (wa SP) 2048 G13 HSTK) | (zlh HY) | (zlh HY) | (zlh HY)].
    - rewrite HC5. apply (rd_frame m m3); [(zlh HY) | lenq'; (zlh HY) | intros x Hx; lenq'; apply F13; clear - HY Hx; lia | exact Ina].
    - intros d k Hd Hk. rewrite HC5. apply (store_ok_mono SEGS k m m3 _ G13). replace (SB + 137438953472 + 128 * c + 72 + d) with (RI + (72 + d)) by (unfold RI; ring). apply Iwri; clear - HY Hd Hk; lia.
    - rewrite HC5, Z.add_0_r. apply (rd_frame m m3); [(zlh HY) | lenq'; (zlh HY) | intros x Hx; lenq'; apply F13; clear - HY Hx; lia | exact Imu].
    - intros d k Hd Hk. rewrite HC5, Z.add_0_r. apply (store_ok_mono SEGS k m m3 _ G13). apply Iwri; clear - HY Hd Hk; lia.
    - rewrite HSPd. replace (SP - 208 + 120) with (SP - 88) by ring. apply (rd_frame m m3); [clear - HS2; lia | lenq'; clear - HS2; lia | intros x Hx; lenq'; apply FW3; clear - HS2 Hx; lia | exact G120].
    - rewrite HSPd, ?HC5. replace (SP - 208 + 112) with (SP - 96) by ring. apply (rd_frame m m3); [clear - HS2; lia | lenq'; clear - HS2; lia | intros x Hx; lenq'; apply FW3; clear - HS2 Hx; lia | exact G112].
    - rewrite HSPd. replace (SP - 208 + 104) with (SP - 104) by ring. apply (rd_frame m m3); [clear - HS2; lia | lenq'; clear - HS2; lia | intros x Hx; lenq'; apply FW3; clear - HS2 Hx; lia | exact G104].
    - rewrite HSPd. replace (SP - 208 + 96) with (SP - 112) by ring. apply (rd_frame m m3); [clear - HS2; lia | lenq'; clear - HS2; lia | intros x Hx; lenq'; apply FW3; clear - HS2 Hx; lia | exact G96].
    - rewrite HSPd. replace (SP - 208 + 88) with (SP - 120) by ring. apply (rd_frame m m3); [clear - HS2; lia | lenq'; clear - HS2; lia | intros x Hx; lenq'; apply FW3; clear - HS2 Hx; lia | exact G88].
    - rewrite HSPd. replace (SP - 208 + 80) with (SP - 128) by ring. apply (rd_frame m m3); [clear - HS2; lia | lenq'; clear - HS2; lia | intros x Hx; lenq'; apply FW3; clear - HS2 Hx; lia | exact G80].
    - rewrite HSPd. replace (SP - 208 + 72) with (SP - 136) by ring. apply (rd_frame m m3); [clear - HS2; lia | lenq'; clear - HS2; lia | intros x Hx; lenq'; apply FW3; clear - HS2 Hx; lia | exact G72].
    - rewrite HSPd. replace (SP - 208 + 64) with (SP - 144) by ring. apply (rd_frame m m3); [clear - HS2; lia | lenq'; clear - HS2; lia | intros x Hx; lenq'; apply FW3; clear - HS2 Hx; lia | exact G64].
    - rewrite HSPd. replace (SP - 208 + 56) with (SP - 152) by ring. apply (rd_frame m m3); [clear - HS2; lia | lenq'; clear - HS2; lia | intros x Hx; lenq'; apply FW3; clear - HS2 Hx; lia | exact G56].
    - rewrite HSPd. replace (SP - 208 + 48) with (SP - 160) by ring. apply (rd_frame m m3); [clear - HS2; lia | lenq'; clear - HS2; lia | intros x Hx; lenq'; apply FW3; clear - HS2 Hx; lia | exact G48].
    - rewrite HSPd. replace (SP - 208 + 40) with (SP - 168) by ring. apply (rd_frame m m3); [clear - HS2; lia | lenq'; clear - HS2; lia | intros x Hx; lenq'; apply FW3; clear - HS2 Hx; lia | exact G40].
    - rewrite HSPd. replace (SP - 208 + 32) with (SP - 176) by ring. apply (rd_frame m m3); [clear - HS2; lia | lenq'; clear - HS2; lia | intros x Hx; lenq'; apply FW3; clear - HS2 Hx; lia | exact G32].
    - rewrite HSPd. replace (SP - 208 + 24) with (SP - 184) by ring. apply (rd_frame m m3); [clear - HS2; lia | lenq'; clear - HS2; lia | intros x Hx; lenq'; apply FW3; clear - HS2 Hx; lia | exact G24].
    - rewrite HSPd, ?HC5. replace (SP - 208 + 136) with (SP - 72) by ring. apply (rd_frame m m3); [clear - HS2; lia | lenq'; clear - HS2; lia | intros x Hx; lenq'; apply FW3; clear - HS2 Hx; lia | exact C136].
    - rewrite HSPd, ?HC5. replace (SP - 208 + 144) with (SP - 64) by ring. apply (rd_frame m m3); [clear - HS2; lia | lenq'; clear - HS2; lia | intros x Hx; lenq'; apply FW3; clear - HS2 Hx; lia | exact C144].
    - rewrite HSPd. replace (SP - 208 + 152) with (SP - 56) by ring. apply (rd_frame m m3); [clear - HS2; lia | lenq'; clear - HS2; lia | intros x Hx; lenq'; apply FW3; clear - HS2 Hx; lia | exact C152].
    - rewrite HSPd. replace (SP - 208 + 160) with (SP - 48) by ring. apply (rd_frame m m3); [clear - HS2; lia | lenq'; clear - HS2; lia | intros x Hx; lenq'; apply FW3; clear - HS2 Hx; lia | exact C160].
    - rewrite HSPd. replace (SP - 208 + 168) with (SP - 40) by ring. apply (rd_frame m m3); [clear - HS2; lia | lenq'; clear - HS2; lia | intros x Hx; lenq'; apply FW3; clear - HS2 Hx; lia | exact C168].
    - rewrite HSPd. replace (SP - 208 + 176) with (SP - 32) by ring. apply (rd_frame m m3); [clear - HS2; lia | lenq'; clear - HS2; lia | intros x Hx; lenq'; apply FW3; clear - HS2 Hx; lia | exact C176].
    - rewrite HSPd. replace (SP - 208 + 184) with (SP - 24) by ring. apply (rd_frame m m3); [clear - HS2; lia | lenq'; clear - HS2; lia | intros x Hx; lenq'; apply FW3; clear - HS2 Hx; lia | exact C184].
    - rewrite HSPd. replace (SP - 208 + 192) with (SP - 16) by ring. apply (rd_frame m m3); [clear - HS2; lia | lenq'; clear - HS2; lia | intros x Hx; lenq'; apply FW3; clear - HS2 Hx; lia | exact C192].
    - rewrite HSPd. replace (SP - 208 + 200) with (SP - 8) by ring. apply (rd_frame m m3); [clear - HS2; lia | lenq'; clear - HS2; lia | intros x Hx; lenq'; apply FW3; clear - HS2 Hx; lia | exact C200].
    - intros d k Hd Hk. rewrite HC5, Z.add_0_r. apply (store_ok_mono SEGS k m m3 _ G13). replace (CA + 80 * c + d) with (CA + (80 * c + d)) by ring. apply Iwc; clear - HY Hd Hk; lia.
    - rewrite HC5. apply (rd_frame m m3); [(zlh HY) | lenq'; (zlh HY) | intros x Hx; lenq'; apply F13; clear - HY Hx; lia | exact Isz].
    - rewrite HC5, chp_off by (zlh HY). pose proof (RD3 (nc - 1) ltac:((zlh HY))) as R7.
      replace (REC + 16 + 4 * (nc - 1)) with (CA + (80 * c + 4 * (nc - 1)) + 16) in R7 by (unfold REC; ring).
      replace ((nc - 1 - (nc - 1)) * (2 * c)) with 0 in R7 by ring. exact R7.
    - apply (rd_frame m m3); [(zlh HY) | lenq'; (zlh HY) | intros x Hx; lenq'; apply F13; clear - HY Hx; lia | exact ISB].
    - apply (rd_frame m m3); [(zlh HY) | lenq'; (zlh HY) | intros x Hx; lenq'; apply F13; clear - HY Hx; lia | exact Ist].
    - intros d k Hd Hk. apply (store_ok_mono SEGS k m m3 _ G13). replace (CA + 2576 + d) with (CA + (2576 + d)) by ring. apply Iwc; clear - HY Hd Hk; lia.
    - intros i Hi. change (Z_to_bv 64 i) with (wa i). rewrite F13 by (clear - HY Hi; lia). apply HIMG. exact Hi. }
  destruct (AXF_ngtz.ngt_pngt Rc m3 rom CA ND nc SB (SB + 137438953472) na 0 (32 * c) st 0 0 0 0 g21 g22 g23 g24 g25 g26 g27 v9 v18 v19 v20 v8 v1 P4
              (sc_ngt_p Rc m3 (SP - 208) CA ND SB (SB + 137438953472) HSPd ltac:((zlh HY)) ltac:(unfold ca_place; (zlh HY)) ltac:((zlh HY)) ltac:((zlh HY))
                 nc na 0 (32 * c) st 0 0 0 0 g21 g22 g23 g24 g25 g26 g27 v9 v18 v19 v20 v8 v1 ltac:((zlh HY))))
    as (Rd & Hms5 & T1 & T2 & T5 & T6 & T7 & T8 & T9 & T10 & T11 & T12 & T13 & T14 & T15 & T16 & T17 & T18 & T19 & T20 & T21 & T22 & T23 & T24 & T25 & T26 & T27 & T28 & KKd).
  clear P4 T5 T6 T7 T11 T12 T13 T14 T15 T16 T17 T28.
  pose proof (msteps_trans SEGS _ _ _ Hms Hms5) as Hms'. clear Hms Hms5. rename Hms' into Hms.
  set (m5 := m5c m3 RI REC CA nc na (32 * c) st).
  assert (EM5 : AXF_ngtz.ngt_mem_pngt m3 Rc CA ND nc SB (SB + 137438953472) na 0 (32 * c) st 0 0 0 0 g21 g22 g23 g24 g25 g26 g27 v9 v18 v19 v20 v8 v1 = m5).
  { unfold m5, m5c, AXF_ngtz.ngt_mem_pngt, RI, REC. rewrite HC5, ext_Z_lo32_small by (zlh HY). rewrite ?Z.add_0_r, ?addneg. reflexivity. }
  rewrite EM5 in Hms. clear EM5.
  assert (G5 : mem_grows m m5) by (exact (mem_grows_trans _ _ _ G13 (m5c_grows _ _ _ _ _ _ _ _))).
  assert (FX5 : forall x, 0 <= x < 2^64 -> ~ (FA <= x < FA + 262144) -> ~ (RI <= x < RI + 128) -> ~ (REC <= x < REC + 80) -> ~ (CA + 2576 <= x < CA + 2584) ->
                  m5 (wa x) = m (wa x)).
  { intros x Hx Q1 Q2 Q3 Q4. unfold m5.
    rewrite m5c_frame; [| clear - HOB; lia | clear - HOB; lia | clear - HOB; lia | clear - HOB; lia | clear - HOB; lia | clear - HOB; lia | exact Hx
                        | clear - Q2; lia | clear - Q2; lia | clear - Q3; lia | exact Q4].
    apply F13; [exact Hx | exact Q1 | clear - Q2; lia | clear - Q2; lia | clear - Q2; lia | clear - HOB Q3; lia]. }
  destruct (m5c_rd m3 RI REC CA nc na (32 * c) st ltac:((zlh HY)) ltac:((zlh HY)) ltac:((zlh HY)) ltac:((zlh HY)) ltac:((zlh HY)) ltac:((zlh HY)) ltac:((zlh HY)))
    as (Rc5 & Rmu5 & Rna5 & Rst5).
  fold m5 in Rc5, Rmu5, Rna5, Rst5.
  exists Rd, m5. split; [exact Hms|].
  regzH T2. regzH T8. regzH T9. regzH T10. regzH T18. regzH T19. regzH T20. regzH T21. regzH T22. regzH T23. regzH T24. regzH T25. regzH T26. regzH T27. regzH T1.
  split; [rewrite T2, HSPd; f_equal; ring|].
  split; [rewrite T10, HC5, ext_Z_u32 by lia; f_equal; unfold RB; ring|].
  split; [exact T1|]. split; [exact T8|]. split; [exact T9|]. split; [exact T18|]. split; [exact T19|]. split; [exact T20|].
  split; [exact T21|]. split; [exact T22|]. split; [exact T23|]. split; [exact T24|]. split; [exact T25|]. split; [exact T26|]. split; [exact T27|].
  split.
  { intros k Hk. cbn [In] in Hk. destruct Hk as [<-|[<-|[]]].
    - rewrite (KKd 3%nat ltac:(cbn; memb')), (KKc 3%nat ltac:(cbn; memb')), (KKb 3%nat ltac:(cbn; memb')), (KKa 3%nat ltac:(cbn; memb')). reflexivity.
    - rewrite (KKd 4%nat ltac:(cbn; memb')), (KKc 4%nat ltac:(cbn; memb')), (KKb 4%nat ltac:(cbn; memb')), (KKa 4%nat ltac:(cbn; memb')). reflexivity. }
  assert (Hsz16 : 32 * c / 16 = 2 * c) by (replace (32 * c) with (2 * c * 16) by ring; apply Z.div_mul; lia).
  split.
  { constructor.
    - rewrite Z.mod_eq by lia. rewrite Hsz16. clear - HY. lia.
    - apply (rd_frame m m5); [lia | lenq'; lia | intros x Hx; lenq'; apply FX5; clear - HY Hx; lia | exact ISB].
    - apply (rd_frame m m5); [lia | lenq'; lia | intros x Hx; lenq'; apply FX5; clear - HY Hx; lia | exact IRIB].
    - rewrite cnt_of_1 by (zlh HY). exact Rc5.
    - replace (2 * nc) with (mc_tbl c) by (clear - Hnc; lia).
      apply (rd_frame m3 m5); [(zlh HY) | lenq'; (zlh HY) | intros x Hx; lenq'; unfold m5; apply m5c_frame; clear - HY Hx; lia |].
      apply (rd_frame m m3); [(zlh HY) | lenq'; (zlh HY) | intros x Hx; lenq'; apply F13; clear - HY Hx; lia | exact Imc].
    - apply (rd_frame m3 m5); [(zlh HY) | lenq'; (zlh HY) | intros x Hx; lenq'; unfold m5; apply m5c_frame; clear - HY Hx; lia |].
      apply (rd_frame m m3); [(zlh HY) | lenq'; (zlh HY) | intros x Hx; lenq'; apply F13; clear - HY Hx; lia | exact Isz].
    - intros i Hi. rewrite cnt_of_1 in Hi |- * by (zlh HY). rewrite Hsz16. replace (1 + (nc - 1) - 1 - i) with (nc - 1 - i) by ring.
      pose proof (RD3 i ltac:(clear - HY Hi; lia)) as Ri. cbv beta in Ri.
      apply (rd_frame m3 m5); [clear - HY Hi; lia | lenq'; clear - HY Hi; lia | intros x Hx; lenq'; unfold m5; apply m5c_frame; clear - HY Hi Hx; lia | exact Ri].
    - exact Rmu5.
    - rewrite b_of_1 by (zlh HY). replace (NEW - nc * 1) with (NEW + -1 * nc) by ring.
      apply (rd_frame m3 m5); [(zlh HY) | lenq'; (zlh HY) | intros x Hx; lenq'; unfold m5; apply m5c_frame; clear - HY Hx; lia |].
      apply (rd_frame m2 m3); [(zlh HY) | lenq'; (zlh HY) | intros x Hx; lenq'; apply F3; clear - HY Hx; lia | exact Rnf2].
    - exists ((nc + na) mod 2^64). split; [apply Z.mod_pos_bound; lia|]. unfold rd. rewrite (wa_eqm ((nc + na) mod 2^64) (nc + na)) by (apply Z.mod_mod; lia). exact Rna5.
    - intros k Hk. rewrite b_of_1 in Hk by (zlh HY). rewrite Hsz16.
      pose proof (RD1 (NEW - 1 - k) ltac:(clear - HY Hk; lia)) as Rf. rewrite Z.add_0_l, div16_32c in Rf.
      replace (FA + 4 * (NEW - 1 - (NEW - 1 - k))) with (SB + c * 4294967296 + 3758096384 + 4 * k) in Rf by (unfold FA, RB; ring).
      apply (rd_frame m3 m5); [clear - HY Hk; lia | lenq'; clear - HY Hk; lia | intros x Hx; lenq'; unfold m5; apply m5c_frame; clear - HY Hk Hx; lia |].
      apply (rd_frame m2 m3); [clear - HY Hk; lia | lenq'; clear - HY Hk; lia | intros x Hx; lenq'; apply F3; clear - HY Hk Hx; lia |].
      apply (rd_frame m1 m2); [clear - HY Hk; lia | lenq'; clear - HY Hk; lia | | exact Rf].
      intros x Hx. lenq'. rewrite EM2. repeat (rewrite wb_other by first [(clear - HY Hk Hx; lia) | (lenq'; clear - HY; lia) | (lenq'; clear - HY Hk Hx; lia)]). reflexivity.
    - exists ((32 * c + st) mod 2^64). split; [apply Z.mod_pos_bound; lia|]. unfold rd. rewrite (wa_eqm ((32 * c + st) mod 2^64) (32 * c + st)) by (apply Z.mod_mod; lia). exact Rst5.
    - intros d k Hd Hk. apply (store_ok_mono SEGS k m m5 _ G5). replace (CA + 80 * c + d) with (CA + (80 * c + d)) by ring. apply Iwc; clear - HY Hd Hk; lia.
    - intros d k Hd Hk. apply (store_ok_mono SEGS k m m5 _ G5). apply Iwri; assumption.
    - intros d k Hd Hk. apply (store_ok_mono SEGS k m m5 _ G5). replace (CA + 2560 + d) with (CA + (2560 + d)) by ring. apply Iwc; clear - HY Hd Hk; lia. }
  split; [|exact G5].
  intros x Hx Q1 Q2. unfold owned_C in Q2. fold RI REC in Q2. apply FX5; [exact Hx | exact Q1 | | |]; clear - Q2; lia.
Qed.
End SC2.
End AXG_nf5.

From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_npf.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AxAsan OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_put OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_put2 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_np OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_np2 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_np3 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_np4 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_nf1 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_nf2.AXG_nfsc OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_npscp OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_nf2.AXG_nfscp OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_nf2 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_nf2b OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_nf3 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_nf6.AXG_nf4 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_nf6.AXG_nf5 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_npf.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Abbreviation SEGS := Asan.M.loaded_segments.

(* [comment removed for export] *)
Definition kz (m : word -> option byte) (a n : Z) : word -> option byte :=
  fun w => if (Z.leb a (bv_unsigned w) && Z.ltb (bv_unsigned w) (a + n))%bool then Some (Z_to_bv 8 0) else m w.
Lemma kz_in : forall m a n x, 0 <= x < 2^64 -> a <= x < a + n -> kz m a n (wa x) = Some (Z_to_bv 8 0).
Proof.
  intros m a n x Hx H. unfold kz. rewrite u_wa_small by lia.
  rewrite (proj2 (Z.leb_le a x)) by lia. rewrite (proj2 (Z.ltb_lt x (a + n))) by lia. reflexivity.
Qed.
Lemma kz_out : forall m a n x, 0 <= x < 2^64 -> ~ (a <= x < a + n) -> kz m a n (wa x) = m (wa x).
Proof.
  intros m a n x Hx H. unfold kz. rewrite u_wa_small by lia.
  destruct (Z.leb a x) eqn:E1; [|reflexivity]. destruct (Z.ltb x (a + n)) eqn:E2; [|reflexivity].
  apply Z.leb_le in E1. apply Z.ltb_lt in E2. exfalso. apply H. lia.
Qed.
Lemma kz_grows : forall m a n, mem_grows m (kz m a n).
Proof. intros m a n x Hx. unfold kz. destruct (Z.leb a (bv_unsigned x) && Z.ltb (bv_unsigned x) (a + n))%bool; [discriminate | exact Hx]. Qed.
Lemma kz_wr : forall m a n, 0 <= a -> a + n <= 2^64 -> wr (kz m a n) a n.
Proof.
  intros m a n Ha Hn d k Hd Hk. destruct k as [|k]; [reflexivity|]. rewrite Nat2Z.inj_succ in Hk.
  apply store_ok_of_all; [rewrite u_wa_small by lia; rewrite Nat2Z.inj_succ; lia|]. rewrite Nat2Z.inj_succ.
  intros x Hx. rewrite u_wa_small in Hx by lia. pose proof (bv_unsigned_in_range _ x) as Rx. unfold bv_modulus in Rx.
  unfold wview. rewrite <- (wa_u x). rewrite kz_in by (change (2 ^ Z.of_N 64) with (2^64) in Rx; lia). discriminate.
Qed.

(* [comment removed for export] *)
Lemma wchainR_other : forall L m B x, 0 <= B -> B + 4096 <= 2^64 -> wl_ok L = true -> 0 <= x < 2^64 ->
  (forall k w v, In (k, w, v) L -> ~ (B + k <= x < B + k + Z.of_nat w)) -> wchainR m B L (wa x) = m (wa x).
Proof.
  induction L as [|[[k' w'] v'] L IH]; intros m B x HB1 HB2 Hwf Hx H; [reflexivity|].
  cbn [wl_ok forallb] in Hwf. apply andb_prop in Hwf as [Hw1 Hwf].
  repeat match type of Hw1 with (_ && _)%bool = true => apply andb_prop in Hw1 as [Hw1 ?] end.
  repeat match goal with X : Z.leb _ _ = true |- _ => apply Z.leb_le in X | X : Nat.leb _ _ = true |- _ => apply Nat.leb_le in X end.
  pose proof (H k' w' v' (or_introl eq_refl)) as Hk0.
  cbn [wchainR]. rewrite wb_other; [apply IH; [assumption | assumption | assumption | assumption | intros k w v Hin; apply (H k w v); right; exact Hin]
                                   | exact Hx | lia | rewrite length_N_to_le_bytes; lia | rewrite length_N_to_le_bytes; lia].
Qed.
Lemma ic_cells : forall k w v, In (k, w, v) ic_list -> exists i, 1 <= i <= 31 /\ 80 * i + 4 <= k /\ k + Z.of_nat w <= 80 * i + 16.
Proof.
  assert (Hb : forallb (fun e : Z * nat * Z => let '(k, w, v) := e in
            existsb (fun i => (Z.leb (80 * i + 4) k && Z.leb (k + Z.of_nat w) (80 * i + 16))%bool) (List.map Z.of_nat (seq 1 31))) ic_list = true) by (vm_compute; reflexivity).
  intros k w v Hin. rewrite forallb_forall in Hb. specialize (Hb _ Hin). cbv beta iota in Hb.
  apply existsb_exists in Hb as (i & Hi & Hc). apply in_map_iff in Hi as (n & <- & Hn). apply in_seq in Hn.
  apply andb_prop in Hc as [C1 C2]. apply Z.leb_le in C1, C2. exists (Z.of_nat n). lia.
Qed.
Lemma ic_wl_ok : wl_ok ic_list = true. Proof. vm_compute. reflexivity. Qed.
Lemma ic_keep : forall m CA x, 0 <= CA -> CA + 4096 <= 2^64 -> 0 <= x < 2^64 ->
  (forall i, 1 <= i <= 31 -> ~ (CA + 80 * i + 4 <= x < CA + 80 * i + 16)) -> ic_mem m CA (wa x) = m (wa x).
Proof.
  intros m CA x H1 H2 Hx H. unfold ic_mem. apply wchainR_other; [exact H1 | exact H2 | exact ic_wl_ok | exact Hx |].
  intros k w v Hin. destruct (ic_cells k w v Hin) as (i & Hi & C1 & C2). specialize (H i Hi). lia.
Qed.

(* [comment removed for export] *)
Lemma mAc_frame : forall m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 g21 g22 g23 g24 g25 g26 g27 x,
  2^46 <= SP <= 2^47 -> 0 <= CA -> CA + 4096 <= 2^63 -> 0 <= RI -> RI + 128 <= 2^63 -> 0 <= x < 2^64 ->
  ~ (SP - 2048 <= x < SP) -> ~ (CA <= x < CA + 2592) -> ~ (RI <= x < RI + 8) ->
  mAc m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 g21 g22 g23 g24 g25 g26 g27 (wa x) = m (wa x).
Proof.
  intros m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 g21 g22 g23 g24 g25 g26 g27 x HSP H1 H2 H3 H4 Hx Q1 Q2 Q3. unfold mAc.
  rewrite (wchainS_frame_in (L3a c CA n RI RB FA) _ SP (-2048) 0); [| lia | lia | reflexivity | reflexivity | exact Hx | lia].
  rewrite wb_other; [| exact Hx | lia | rewrite length_N_to_le_bytes; lia | rewrite length_N_to_le_bytes; lia].
  rewrite (wchainS_frame_in (L2a c CA n g21 g22 g23 g24 g25 g26 g27) _ SP (-2048) 0); [| lia | lia | reflexivity | reflexivity | exact Hx | lia].
  rewrite ic_keep; [| lia | lia | exact Hx | intros i Hi; lia].
  rewrite (wchainS_frame_in (L1a c CA v1 v8 v9 v18 v19 v20) _ SP (-2048) 0); [| lia | lia | reflexivity | reflexivity | exact Hx | lia].
  reflexivity.
Qed.
Lemma mAc_grows : forall m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 g21 g22 g23 g24 g25 g26 g27,
  mem_grows m (mAc m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 g21 g22 g23 g24 g25 g26 g27).
Proof.
  intros. unfold mAc.
  apply (mem_grows_trans _ _ _ (wchainS_grows (L1a c CA v1 v8 v9 v18 v19 v20) m SP)).
  apply (mem_grows_trans _ _ _ (ic_grows _ CA)).
  apply (mem_grows_trans _ _ _ (wchainS_grows (L2a c CA n g21 g22 g23 g24 g25 g26 g27) _ SP)).
  apply (mem_grows_trans _ (wbytes (wchainS (ic_mem (wchainS m SP (L1a c CA v1 v8 v9 v18 v19 v20)) CA) SP (L2a c CA n g21 g22 g23 g24 g25 g26 g27)) (wa RI) (word_to_le_bytes 8 (wa 1152921504606846976)))).
  - apply grows_wb. apply mem_grows_refl.
  - apply wchainS_grows.
Qed.

(* [comment removed for export] *)
Lemma mAc_rd3 : forall m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 g21 g22 g23 g24 g25 g26 g27 k v,
  2^46 <= SP <= 2^47 -> wl_chk (L3a c CA n RI RB FA) k 8 = Some v -> -2048 <= k -> k + 8 <= 0 ->
  rd (mAc m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 g21 g22 g23 g24 g25 g26 g27) (SP + k) 8 v.
Proof. intros. unfold mAc. apply rd_wchainS; [lia | lia | reflexivity | lia | cbn; lia | lia | assumption]. Qed.
Lemma mAc_rd2 : forall m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 g21 g22 g23 g24 g25 g26 g27 k v,
  2^46 <= SP <= 2^47 -> 0 <= RI -> RI + 128 <= SP - 2048 -> wl_chk (L2a c CA n g21 g22 g23 g24 g25 g26 g27) k 8 = Some v -> -208 <= k -> k + 8 <= 0 ->
  rd (mAc m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 g21 g22 g23 g24 g25 g26 g27) (SP + k) 8 v.
Proof.
  intros m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 g21 g22 g23 g24 g25 g26 g27 k v HSP H1 H2 Hc Hk1 Hk2. unfold mAc.
  apply (rd_frame (wchainS (ic_mem (wchainS m SP (L1a c CA v1 v8 v9 v18 v19 v20)) CA) SP (L2a c CA n g21 g22 g23 g24 g25 g26 g27))); [lia | cbn; lia | |].
  - intros x Hx. cbn in Hx.
    rewrite (wchainS_frame_in (L3a c CA n RI RB FA) _ SP (-2048) (-208)); [| lia | lia | reflexivity | reflexivity | lia | lia].
    apply wb_other; [lia | lia | rewrite length_N_to_le_bytes; lia | rewrite length_N_to_le_bytes; lia].
  - apply rd_wchainS; [lia | lia | reflexivity | lia | cbn; lia | lia | exact Hc].
Qed.
Lemma mAc_rd1 : forall m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 g21 g22 g23 g24 g25 g26 g27 k v,
  2^46 <= SP <= 2^47 -> 0 <= RI -> RI + 128 <= SP - 2048 -> 0 <= CA -> CA + 4096 <= SP - 2048 ->
  wl_chk (L1a c CA v1 v8 v9 v18 v19 v20) k 8 = Some v -> -80 <= k -> k + 8 <= 0 ->
  rd (mAc m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 g21 g22 g23 g24 g25 g26 g27) (SP + k) 8 v.
Proof.
  intros m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 g21 g22 g23 g24 g25 g26 g27 k v HSP H1 H2 H3 H4 Hc Hk1 Hk2. unfold mAc.
  apply (rd_frame (wchainS m SP (L1a c CA v1 v8 v9 v18 v19 v20))); [lia | cbn; lia | |].
  - intros x Hx. cbn in Hx.
    rewrite (wchainS_frame_in (L3a c CA n RI RB FA) _ SP (-2048) (-208)); [| lia | lia | reflexivity | reflexivity | lia | lia].
    rewrite wb_other; [| lia | lia | rewrite length_N_to_le_bytes; lia | rewrite length_N_to_le_bytes; lia].
    rewrite (wchainS_frame_in (L2a c CA n g21 g22 g23 g24 g25 g26 g27) _ SP (-208) (-80)); [| lia | lia | reflexivity | reflexivity | lia | lia].
    apply ic_keep; [lia | lia | lia | intros i Hi; lia].
  - apply rd_wchainS; [lia | lia | reflexivity | lia | cbn; lia | lia | exact Hc].
Qed.

(* [comment removed for export] *)
Lemma mAc_frame_f : forall m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 g21 g22 g23 g24 g25 g26 g27 x,
  2^46 <= SP <= 2^47 -> 0 <= CA -> CA + 4096 <= 2^63 -> 0 <= RI -> RI + 128 <= 2^63 -> 0 <= x < 2^64 ->
  ~ (SP - 2048 <= x < SP) -> (forall i, 1 <= i <= 31 -> ~ (CA + 80 * i + 4 <= x < CA + 80 * i + 16)) -> ~ (RI <= x < RI + 8) ->
  mAc m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 g21 g22 g23 g24 g25 g26 g27 (wa x) = m (wa x).
Proof.
  intros m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 g21 g22 g23 g24 g25 g26 g27 x HSP H1 H2 H3 H4 Hx Q1 Q2 Q3. unfold mAc.
  rewrite (wchainS_frame_in (L3a c CA n RI RB FA) _ SP (-2048) 0); [| lia | lia | reflexivity | reflexivity | exact Hx | lia].
  rewrite wb_other; [| exact Hx | lia | rewrite length_N_to_le_bytes; lia | rewrite length_N_to_le_bytes; lia].
  rewrite (wchainS_frame_in (L2a c CA n g21 g22 g23 g24 g25 g26 g27) _ SP (-2048) 0); [| lia | lia | reflexivity | reflexivity | exact Hx | lia].
  rewrite ic_keep; [| lia | lia | exact Hx | exact Q2].
  rewrite (wchainS_frame_in (L1a c CA v1 v8 v9 v18 v19 v20) _ SP (-2048) 0); [| lia | lia | reflexivity | reflexivity | exact Hx | lia].
  reflexivity.
Qed.
(* [comment removed for export] *)
Lemma mAc_rdRI : forall m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 g21 g22 g23 g24 g25 g26 g27,
  2^46 <= SP <= 2^47 -> 0 <= RI -> RI + 128 <= SP - 2048 ->
  rd (mAc m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 g21 g22 g23 g24 g25 g26 g27) RI 8 1152921504606846976.
Proof.
  intros. unfold mAc.
  apply (rd_frame (wbytes (wchainS (ic_mem (wchainS m SP (L1a c CA v1 v8 v9 v18 v19 v20)) CA) SP (L2a c CA n g21 g22 g23 g24 g25 g26 g27)) (wa RI) (word_to_le_bytes 8 (wa 1152921504606846976)))); [lia | cbn; lia | |].
  - intros x Hx. cbn in Hx. apply (wchainS_frame_in (L3a c CA n RI RB FA) _ SP (-2048) 0); [lia | lia | reflexivity | reflexivity | lia | lia].
  - apply wb_rd_hit; [lia | lia | cbn; lia].
Qed.
Lemma mAc_rd_ic : forall m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 g21 g22 g23 g24 g25 g26 g27 i,
  2^46 <= SP <= 2^47 -> 0 <= RI -> RI + 128 <= SP - 2048 -> 0 <= CA -> CA + 4096 <= SP - 2048 -> (CA + 4096 <= RI \/ RI + 128 <= CA) -> 1 <= i <= 31 ->
  rd (mAc m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 g21 g22 g23 g24 g25 g26 g27) (CA + 80 * i + 4) 4 (mc_tbl i) /\
  rd (mAc m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 g21 g22 g23 g24 g25 g26 g27) (CA + 80 * i + 8) 8 (sz_tbl i).
Proof.
  intros m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 g21 g22 g23 g24 g25 g26 g27 i HSP H1 H2 H3 H4 H5 Hi. unfold mAc.
  destruct (ic_rd (wchainS m SP (L1a c CA v1 v8 v9 v18 v19 v20)) CA i ltac:(lia) ltac:(lia) Hi) as [X1 X2].
  assert (FR : forall x, CA + 80 * i + 4 <= x < CA + 80 * i + 16 ->
            wchainS (wbytes (wchainS (ic_mem (wchainS m SP (L1a c CA v1 v8 v9 v18 v19 v20)) CA) SP (L2a c CA n g21 g22 g23 g24 g25 g26 g27)) (wa RI) (word_to_le_bytes 8 (wa 1152921504606846976))) SP (L3a c CA n RI RB FA) (wa x) =
            ic_mem (wchainS m SP (L1a c CA v1 v8 v9 v18 v19 v20)) CA (wa x)).
  { intros x Hx.
    rewrite (wchainS_frame_in (L3a c CA n RI RB FA) _ SP (-2048) 0); [| lia | lia | reflexivity | reflexivity | lia | lia].
    rewrite wb_other; [| lia | lia | rewrite length_N_to_le_bytes; lia | rewrite length_N_to_le_bytes; lia].
    apply (wchainS_frame_in (L2a c CA n g21 g22 g23 g24 g25 g26 g27) _ SP (-2048) 0); [lia | lia | reflexivity | reflexivity | lia | lia]. }
  split; [apply (rd_frame (ic_mem (wchainS m SP (L1a c CA v1 v8 v9 v18 v19 v20)) CA)); [lia | cbn; lia | intros x Hx; cbn in Hx; apply FR; lia | exact X1]
         | apply (rd_frame (ic_mem (wchainS m SP (L1a c CA v1 v8 v9 v18 v19 v20)) CA)); [lia | cbn; lia | intros x Hx; cbn in Hx; apply FR; lia | exact X2]].
Qed.
Lemma wr_grows : forall m m' a n, mem_grows m m' -> wr m a n -> wr m' a n.
Proof. intros m m' a n G W d k Hd Hk. apply (store_ok_mono SEGS k m m' _ G). exact (W d k Hd Hk). Qed.

(* [comment removed for export] *)
Definition agree_on (S : Z -> Prop) (m1 m2 : word -> option byte) : Prop :=
  forall x, 0 <= x < 2^64 -> S x -> m1 (wa x) = m2 (wa x).
Lemma rd_agree : forall (S : Z -> Prop) m1 m2 a w v, agree_on S m1 m2 -> 0 <= a -> a + Z.of_nat w <= 2^64 ->
  (forall x, a <= x < a + Z.of_nat w -> S x) -> rd m2 a w v -> rd m1 a w v.
Proof. intros S m1 m2 a w v HA H1 H2 HS H. apply (rd_frame m2 m1); [exact H1 | exact H2 | intros x Hx; apply HA; [lia | exact (HS x Hx)] | exact H]. Qed.
Lemma wr_agree : forall (S : Z -> Prop) m1 m2 a n, agree_on S m1 m2 -> 0 <= a -> a + n <= 2^64 ->
  (forall x, a <= x < a + n -> S x) -> wr m2 a n -> wr m1 a n.
Proof. intros S m1 m2 a n HA H1 H2 HS H. apply (wr_frame m2 m1); [exact H1 | exact H2 | intros x Hx; apply HA; [lia | exact (HS x Hx)] | exact H]. Qed.
Lemma stk_ok_agree : forall (S : Z -> Prop) m1 m2 SP K, agree_on S m1 m2 -> 0 <= K <= SP -> SP <= 2^63 ->
  (forall x, SP - K <= x < SP -> S x) -> stk_ok SEGS m2 (wa SP) K -> stk_ok SEGS m1 (wa SP) K.
Proof.
  intros S m1 m2 SP K HA HK HSP HS H a n H1 H2. rewrite (u_wa_small SP) in H1, H2 by lia.
  pose proof (bv_unsigned_in_range _ a) as Ha. unfold bv_modulus in Ha. change (2 ^ Z.of_N 64) with (2^64) in Ha.
  rewrite <- (wa_u a). rewrite (store_ok_frame n m2 m1 (bv_unsigned a)); [| lia | lia | intros x Hx; apply HA; [lia | apply HS; lia]].
  rewrite wa_u. apply H; rewrite (u_wa_small SP) by lia; assumption.
Qed.
Lemma agree_none : forall (S : Z -> Prop) m1 m2 i, agree_on S m1 m2 -> 0 <= i < 2^64 -> S i -> m2 (Z_to_bv 64 i) = None -> m1 (Z_to_bv 64 i) = None.
Proof. intros S m1 m2 i HA Hi HS H. change (Z_to_bv 64 i) with (wa i) in *. rewrite (HA i Hi HS). exact H. Qed.

Lemma bvu_rng : forall w : word, 0 <= bv_unsigned w < 2^64.
Proof. intros w. pose proof (bv_unsigned_in_range _ w) as H. unfold bv_modulus in H. change (2 ^ Z.of_N 64) with (2^64) in H. exact H. Qed.
Lemma rd_mod64 : forall (mm : word -> option byte) a (w : nat) v, rd mm a w v -> rd mm a w (v mod 2^64).
Proof. intros mm a w v H. unfold rd in *. rewrite (wa_eqm (v mod 2^64) v) by (apply Z.mod_mod; lia). exact H. Qed.
Lemma sz_tbl_small : forall c0, 2 <= c0 <= 16 -> sz_tbl c0 = 32 * c0.
Proof.
  intros c0 H. assert (Hcs : c0 = 2 \/ c0 = 3 \/ c0 = 4 \/ c0 = 5 \/ c0 = 6 \/ c0 = 7 \/ c0 = 8 \/ c0 = 9 \/ c0 = 10 \/ c0 = 11 \/ c0 = 12 \/ c0 = 13 \/ c0 = 14 \/ c0 = 15 \/ c0 = 16) by lia.
  clear H. repeat (destruct Hcs as [->|Hcs]; [reflexivity|]). subst c0. reflexivity.
Qed.

(* [comment removed for export] *)
Definition shsep (T RI TP TSDA PT SHx : Z) : Prop :=
  (T + 4096 <= SHx \/ SHx + 32768 <= T) /\ (RI + 128 <= SHx \/ SHx + 32768 <= RI) /\ (TP <= SHx \/ SHx + 32768 <= TP - 88) /\
  (TSDA + 8192 <= SHx \/ SHx + 32768 <= TSDA) /\ (PT + 160 <= SHx \/ SHx + 32768 <= PT).
(* [comment removed for export] *)
Definition EC (R : bvmap 5 word) (ad : Z) : Prop :=
  getr R (Z_to_bv 5 (Z.of_nat 10)) = wa ad /\ getr R (Z_to_bv 5 (Z.of_nat 11)) = wa 262144 /\ getr R (Z_to_bv 5 (Z.of_nat 12)) = wa 3 /\
  getr R (Z_to_bv 5 (Z.of_nat 13)) = wa 50 /\ getr R (Z_to_bv 5 (Z.of_nat 14)) = wa 18446744073709551615 /\
  getr R (Z_to_bv 5 (Z.of_nat 15)) = wa 0 /\ getr R (Z_to_bv 5 (Z.of_nat 17)) = wa 222.

(* [comment removed for export] *)
Definition MA_OK (m mA0 : word -> option byte) (regs : bvmap 5 word) (SP CA c RI RB FA : Z) : Prop :=
  (forall k v, wl_chk (L3a c CA (mc_tbl c / 2) RI RB FA) k 8 = Some v -> -2048 <= k -> k + 8 <= 0 -> rd mA0 (SP + k) 8 v) /\
  (forall k v, wl_chk (L2a c CA (mc_tbl c / 2) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 21)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 22))))
      (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 23)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 24)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 25))))
      (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 26)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 27))))) k 8 = Some v ->
      -208 <= k -> k + 8 <= 0 -> rd mA0 (SP + k) 8 v) /\
  (forall k v, wl_chk (L1a c CA (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 1)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 8))))
      (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 9)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 19))))
      (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 20))))) k 8 = Some v ->
      -80 <= k -> k + 8 <= 0 -> rd mA0 (SP + k) 8 v) /\
  (forall x, 0 <= x < 2^64 -> ~ (SP - 2048 <= x < SP) -> (forall i, 1 <= i <= 31 -> ~ (CA + 80 * i + 4 <= x < CA + 80 * i + 16)) ->
     ~ (RI <= x < RI + 8) -> mA0 (wa x) = m (wa x)) /\
  rd mA0 RI 8 1152921504606846976 /\
  (rd mA0 (CA + 80 * c + 4) 4 (mc_tbl c) /\ rd mA0 (CA + 80 * c + 8) 8 (sz_tbl c)) /\
  mem_grows m mA0.

(* [comment removed for export] *)
Section FU.
Context {fx : FPState}.
Variable rom : word -> option byte.
Variables (m mA0 : word -> option byte) (regs : bvmap 5 word) (CA ND c SB SP st st2 TP K TSDA PT T mm1 mm2 : Z).
Let RIv := SB + 137438953472 + 128 * c.
Let RBv := SB + 4294967296 * c.
Let FAv := SB + 4294967296 * c + 3758096384.
Let SHv := Z.shiftr (SB + 4294967296 * c) 3 + 2147450880.
Let SHFv := Z.shiftr (SB + 4294967296 * c + 3758096384) 3 + 2147450880.
(* [comment removed for export] *)
Definition CHC (x : Z) : Prop :=
  SP - 2048 <= x < SP \/ CA <= x < CA + 2592 \/ RIv <= x < RIv + 128 \/ T + 2872 <= x < T + 2888 \/ RBv <= x < RBv + 262144 \/
  FAv <= x < FAv + 262144 \/ SHv <= x < SHv + 32768 \/ SHFv <= x < SHFv + 32768.
Definition ENVC (x : Z) : Prop :=
  65536 <= x < 143360 \/ 904176 <= x < 904248 \/ 912208 <= x < 912216 \/ 923512 <= x < 923537 \/ 935452 <= x < 935464 \/ 937400 <= x < 937408 \/
  940704 <= x < 940728 \/ 1525856 <= x < 1525864 \/ 1534328 <= x < 1534336 \/ 1534444 <= x < 1534445 \/
  TP - 88 <= x < TP - 80 \/ TSDA + 8 * K <= x < TSDA + 8 * K + 8 \/ PT + 152 <= x < PT + 160.
Definition CELLS_B (x : Z) : Prop :=
  SP - 2048 <= x < SP \/ CA <= x < CA + 2592 \/ RIv <= x < RIv + 128 \/ T + 2872 <= x < T + 2888 \/
  SHv <= x < SHv + 32768 \/ SHFv <= x < SHFv + 32768 \/ ENVC x.
Definition CELLS_C (x : Z) : Prop := CELLS_B x \/ FAv <= x < FAv + 262144.

Hypothesis Hc : c = (ND + 31) / 32.
Hypothesis HND : 33 <= ND <= 512.
Hypothesis H2 : getr regs 2 = wa SP.
Hypothesis HSP : 2^46 + 4096 <= SP <= 2^47 /\ SP mod 16 = 0.
Hypothesis HSTK : stk_ok SEGS m (wa SP) 2048.
Hypothesis H10 : getr regs 10 = wa 923480.
Hypothesis H11 : getr regs 11 = wa CA.
Hypothesis H12 : getr regs 12 = wa ND.
Hypothesis H13 : getr regs 13 = wa 8.
Hypothesis H4 : getr regs 4 = wa TP.
Hypothesis HCA : ((4304 <= CA /\ CA + 3888 <= 65536) \/ 6529232 <= CA) /\ CA mod 16 = 0 /\ CA + 4096 <= SP - 2048.
Hypothesis HCT : CA = T + 208.
Hypothesis HSB : 17594333495296 <= SB /\ SB mod 4096 = 0 /\ SB + 137438953472 + 4096 <= SP - 2048.
Hypothesis HSEP : CA + 2592 <= SB \/ SB + 137438953472 + 4096 <= CA.
Hypothesis HO : objs_ok_p (SP - 2048) T RIv TP TSDA PT.
Hypothesis HK : 0 <= K <= 1023.
Hypothesis Hvals : 0 <= st < 2^64 /\ 0 <= st2 < 2^64 /\ 0 <= mm1 < 2^64 /\ 0 <= mm2 < 2^64.
Hypothesis HENV : forall x, ENVC x -> ~ CHC x.
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
Hypothesis HMA : MA_OK m mA0 regs SP CA c RIv RBv FAv.

(* [comment removed for export] *)
#[using="ND Hc HND HSP HCA HCT HSB HO HK"] Lemma fu_geo : 2^46 + 4096 <= SP <= 2^47 /\ 2 <= c <= 16 /\ 4304 <= CA /\ CA + 4096 <= SP - 2048 /\ CA = T + 208 /\
  17594333495296 <= SB /\ SB + 137438953472 + 4096 <= SP - 2048 /\
  RIv = SB + 137438953472 + 128 * c /\ RBv = SB + 4294967296 * c /\ FAv = RBv + 3758096384 /\
  8 * (SHv - 2147450880) = RBv /\ 8 * (SHFv - 2147450880) = FAv /\
  4096 <= T /\ T + 4096 <= SP - 2048 - 256 /\ 4096 <= TP /\ TP <= SP - 2048 - 256 /\
  1 <= TSDA /\ TSDA + 8192 <= SP - 2048 - 256 /\ 1 <= PT /\ PT + 160 <= SP - 2048 - 256 /\ 0 <= K <= 1023.
Proof. LiaFast.lf_pins (fun (ND Hc HND HSP HCA HCT HSB HO HK : LiaFast.U) => LiaFast.u0).
  pose proof (c_of_nd_range ND HND) as Hcr5. rewrite <- Hc in Hcr5.
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
  unfold objs_ok_p, t_place in HO. unfold FAv, RBv in *. clear - Hcr5 HSP HCA HCT HSB E1 E2 HO HK. unfold RIv in *. lia.
Qed.
(* [comment removed for export] *)
#[using="SP TP TSDA PT HO"] Lemma fu_d_ri_t : RIv + 128 <= T \/ T + 4096 <= RIv.
Proof. LiaFast.lf_pins (fun (SP TP TSDA PT HO : LiaFast.U) => LiaFast.u0). unfold objs_ok_p in HO. clear - HO. tauto. Qed.

Ltac zg := let G := fresh "G" in pose proof fu_geo as G; clear - G; lia.
Ltac zg1 H := let G := fresh "G" in pose proof fu_geo as G; clear - G H; lia.
Ltac zg2 H1 H2 := let G := fresh "G" in pose proof fu_geo as G; clear - G H1 H2; lia.
Ltac zg3 H1 H2 H3 := let G := fresh "G" in pose proof fu_geo as G; clear - G H1 H2 H3; lia.
(* [comment removed for export] *)
Ltac pick := first [ lia | left; lia | right; pick ].
Ltac envc Hx := unfold ENVC; let G := fresh "G" in pose proof fu_geo as G; clear - G Hx; pick.


(* [comment removed for export] *)
Definition mB0 : word -> option byte := kz mA0 RBv 262144.

#[using="regs FAv HMA"] Lemma mB0_frame : forall x, 0 <= x < 2^64 -> ~ (SP - 2048 <= x < SP) -> (forall i, 1 <= i <= 31 -> ~ (CA + 80 * i + 4 <= x < CA + 80 * i + 16)) ->
  ~ (RIv <= x < RIv + 8) -> ~ (RBv <= x < RBv + 262144) -> mB0 (wa x) = m (wa x).
Proof. LiaFast.lf_pins (fun (regs FAv HMA : LiaFast.U) => LiaFast.u0).
  intros x Hx Q1 Q2 Q3 Q4. unfold mB0. rewrite kz_out by assumption.
  destruct HMA as (_ & _ & _ & FR & _). exact (FR x Hx Q1 Q2 Q3).
Qed.
#[using="regs ND TP K TSDA PT Hc HND HSP HCA HCT HSB HO HK HMA"] Lemma mB0_env : forall x, 0 <= x < 2^64 -> ~ CHC x -> mB0 (wa x) = m (wa x).
Proof. LiaFast.lf_pins (fun (regs ND TP K TSDA PT Hc HND HSP HCA HCT HSB HO HK HMA : LiaFast.U) => LiaFast.u0).
  intros x Hx Q. unfold CHC in Q. apply mB0_frame; [exact Hx | zg1 Q | intros i Hi; zg2 Q Hi | zg1 Q | zg1 Q].
Qed.
#[using="regs CA SP RIv FAv HMA"] Lemma mB0_grows : mem_grows m mB0.
Proof. LiaFast.lf_pins (fun (regs CA SP RIv FAv HMA : LiaFast.U) => LiaFast.u0). unfold mB0. destruct HMA as (_ & _ & _ & _ & _ & _ & GA). exact (mem_grows_trans _ _ _ GA (kz_grows _ _ _)). Qed.
(* [comment removed for export] *)
#[using="m regs ND TP K TSDA PT T SHv SHFv Hc HND HSP HCA HCT HSB HO HK HMA"] Lemma mB0_slot3 : forall k v, wl_chk (L3a c CA (mc_tbl c / 2) RIv RBv FAv) k 8 = Some v -> -2048 <= k -> k + 8 <= 0 -> rd mB0 (SP + k) 8 v.
Proof. LiaFast.lf_pins (fun (m regs ND TP K TSDA PT T SHv SHFv Hc HND HSP HCA HCT HSB HO HK HMA : LiaFast.U) => LiaFast.u0).
  intros k v Hk K1 K2. unfold mB0. apply (rd_frame mA0); [zg2 K1 K2 | cbn; zg2 K1 K2 | intros x Hx; cbn in Hx; apply kz_out; zg3 K1 K2 Hx |].
  destruct HMA as (S3 & _). exact (S3 k v Hk K1 K2).
Qed.
#[using="m ND TP K TSDA PT T RIv FAv SHv SHFv Hc HND HSP HCA HCT HSB HO HK HMA"] Lemma mB0_slot2 : forall k v, wl_chk (L2a c CA (mc_tbl c / 2) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 21)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 22))))
      (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 23)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 24)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 25))))
      (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 26)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 27))))) k 8 = Some v ->
  -208 <= k -> k + 8 <= 0 -> rd mB0 (SP + k) 8 v.
Proof. LiaFast.lf_pins (fun (m ND TP K TSDA PT T RIv FAv SHv SHFv Hc HND HSP HCA HCT HSB HO HK HMA : LiaFast.U) => LiaFast.u0).
  intros k v Hk K1 K2. unfold mB0. apply (rd_frame mA0); [zg2 K1 K2 | cbn; zg2 K1 K2 | intros x Hx; cbn in Hx; apply kz_out; zg3 K1 K2 Hx |].
  destruct HMA as (_ & S2 & _). exact (S2 k v Hk K1 K2).
Qed.
#[using="m ND TP K TSDA PT T RIv FAv SHv SHFv Hc HND HSP HCA HCT HSB HO HK HMA"] Lemma mB0_slot1 : forall k v, wl_chk (L1a c CA (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 1)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 8))))
      (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 9)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 19))))
      (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 20))))) k 8 = Some v ->
  -80 <= k -> k + 8 <= 0 -> rd mB0 (SP + k) 8 v.
Proof. LiaFast.lf_pins (fun (m ND TP K TSDA PT T RIv FAv SHv SHFv Hc HND HSP HCA HCT HSB HO HK HMA : LiaFast.U) => LiaFast.u0).
  intros k v Hk K1 K2. unfold mB0. apply (rd_frame mA0); [zg2 K1 K2 | cbn; zg2 K1 K2 | intros x Hx; cbn in Hx; apply kz_out; zg3 K1 K2 Hx |].
  destruct HMA as (_ & _ & S1 & _). exact (S1 k v Hk K1 K2).
Qed.
(* [comment removed for export] *)
#[using="regs CA ND SP T RIv FAv SHv SHFv Hc HND HSP HCA HCT HSB HO HK HENV HMA"] Lemma mB0_envrd : forall a w v, 0 <= a -> (forall x, a <= x < a + Z.of_nat w -> ENVC x) -> a + Z.of_nat w <= 2^64 -> rd m a w v -> rd mB0 a w v.
Proof. LiaFast.lf_pins (fun (regs CA ND SP T RIv FAv SHv SHFv Hc HND HSP HCA HCT HSB HO HK HENV HMA : LiaFast.U) => LiaFast.u0).
  intros a w v Ha HE Hw H. apply (rd_frame m mB0); [exact Ha | exact Hw | | exact H].
  intros x Hx. apply mB0_env; [lia | apply HENV; exact (HE x Hx)].
Qed.
(* [comment removed for export] *)
#[using="regs ND SP TP K TSDA PT FAv SHv SHFv Hc HND HSP HCA HCT HSB HSEP HO HK HMA"] Lemma mB0_keep : forall a w v, 0 <= a -> a + Z.of_nat w <= 2^63 ->
  (T + 2872 <= a /\ a + Z.of_nat w <= T + 2888) \/ (CA + 2576 <= a /\ a + Z.of_nat w <= CA + 2592) \/ (RIv + 8 <= a /\ a + Z.of_nat w <= RIv + 128) ->
  rd m a w v -> rd mB0 a w v.
Proof. LiaFast.lf_pins (fun (regs ND SP TP K TSDA PT FAv SHv SHFv Hc HND HSP HCA HCT HSB HSEP HO HK HMA : LiaFast.U) => LiaFast.u0).
  intros a w v Ha Hw Hr H. pose proof fu_d_ri_t as D1. pose proof HSEP as D2.
  apply (rd_frame m mB0); [exact Ha | lia | | exact H].
  intros x Hx. apply mB0_frame; [lia | | | | ].
  - pose proof fu_geo as G. clear - G Hr Hx D1 D2. lia.
  - intros i Hi. pose proof fu_geo as G. clear - G Hr Hx D1 D2 Hi. lia.
  - pose proof fu_geo as G. clear - G Hr Hx D1 D2. lia.
  - pose proof fu_geo as G. clear - G Hr Hx D1 D2. lia.
Qed.
(* [comment removed for export] *)
#[using="m regs CA ND SP TP K TSDA PT T FAv SHv SHFv Hc HND HSP HCA HCT HSB HO HK HMA"] Lemma mB0_mu : rd mB0 RIv 8 1152921504606846976.
Proof. LiaFast.lf_pins (fun (m regs CA ND SP TP K TSDA PT T FAv SHv SHFv Hc HND HSP HCA HCT HSB HO HK HMA : LiaFast.U) => LiaFast.u0).
  unfold mB0. apply (rd_frame mA0); [zg | cbn; zg | intros x Hx; cbn in Hx; apply kz_out; zg1 Hx |].
  destruct HMA as (_ & _ & _ & _ & MU & _). exact MU.
Qed.
#[using="m regs ND SP TP K TSDA PT T RIv FAv SHv SHFv Hc HND HSP HCA HCT HSB HSEP HO HK HMA"] Lemma mB0_ic : rd mB0 (CA + 80 * c + 4) 4 (mc_tbl c) /\ rd mB0 (CA + 80 * c + 8) 8 (sz_tbl c).
Proof. LiaFast.lf_pins (fun (m regs ND SP TP K TSDA PT T RIv FAv SHv SHFv Hc HND HSP HCA HCT HSB HSEP HO HK HMA : LiaFast.U) => LiaFast.u0).
  pose proof HSEP as D. destruct HMA as (_ & _ & _ & _ & _ & (X1 & X2) & _). unfold mB0.
  split; [apply (rd_frame mA0); [zg | cbn; zg | intros x Hx; cbn in Hx; apply kz_out; [zg1 Hx | pose proof fu_geo as G; clear - G D Hx; lia] | exact X1]
         | apply (rd_frame mA0); [zg | cbn; zg | intros x Hx; cbn in Hx; apply kz_out; [zg1 Hx | pose proof fu_geo as G; clear - G D Hx; lia] | exact X2]].
Qed.

(* [comment removed for export] *)
Definition PB (mB : word -> option byte) : Prop :=
  (forall x, SHv <= x < SHv + 32768 -> mB (wa x) = Some (Z_to_bv 8 250)) /\
  rd mB (SP - 448 + 88) 8 515004 /\ rd mB (SP - 448 + 80) 8 262144 /\ rd mB (SP - 448 + 72) 8 FAv /\
  rd mB (SP - 448 + 64) 8 262144 /\ rd mB (SP - 448 + 56) 8 RIv /\ rd mB (SP - 448 + 48) 8 262144 /\
  rd mB (SP - 352 + 24) 8 271780 /\ rd mB (SP - 352 + 16) 8 262144 /\ rd mB (SP - 352 + 8) 8 FAv /\ rd mB (SP - 352 + 0) 8 262144 /\
  rd mB (SP - 280) 8 281044 /\ rd mB (SP - 288) 8 RIv /\ rd mB (SP - 296) 8 (262144 / (32 * c)) /\
  rd mB (SP - 304) 8 RBv /\ rd mB (SP - 312) 8 (262144 / (32 * c)) /\
  rd mB (RIv + 48) 8 262144 /\ rd mB (T + 2872) 8 (mm1 + 1) /\ rd mB (T + 2880) 8 (mm2 + 262144) /\ rd mB (CA + 2584) 8 (st2 + 262144).
Definition FRB (m0 mB : word -> option byte) : Prop :=
  (forall x, 0 <= x < 2^64 -> ~ (SP - 2048 <= x < SP - 272) -> ~ (SHv <= x < SHv + 32768) -> ~ (RIv + 48 <= x < RIv + 56) ->
     ~ (CA + 2584 <= x < CA + 2592) -> ~ (T + 2872 <= x < T + 2888) -> mB (wa x) = m0 (wa x)) /\ mem_grows m0 mB.

Section SB.
Variable mB0' : word -> option byte.
Hypothesis HB0 : agree_on CELLS_B mB0' mB0.

#[using="ND FAv HB0"] Lemma b_rd : forall a w v, 0 <= a -> a + Z.of_nat w <= 2^63 -> (forall x, a <= x < a + Z.of_nat w -> CELLS_B x) -> rd mB0 a w v -> rd mB0' a w v.
Proof. LiaFast.lf_pins (fun (ND FAv HB0 : LiaFast.U) => LiaFast.u0). intros a w v Ha Hw HS H. apply (rd_agree CELLS_B mB0' mB0); [exact HB0 | exact Ha | lia | exact HS | exact H]. Qed.
#[using="mA0 regs ND RBv FAv HMA HB0"] Lemma b_wr : forall a n, 0 <= a -> a + n <= 2^63 -> (forall x, a <= x < a + n -> CELLS_B x) -> wr m a n -> wr mB0' a n.
Proof. LiaFast.lf_pins (fun (mA0 regs ND RBv FAv HMA HB0 : LiaFast.U) => LiaFast.u0).
  intros a n Ha Hn HS H. apply (wr_agree CELLS_B mB0' mB0); [exact HB0 | exact Ha | lia | exact HS |].
  exact (wr_grows m mB0 _ _ mB0_grows H).
Qed.
#[using="mA0 regs CA ND c SB SP T RIv RBv FAv SHv SHFv Hc HND HSP HCA HCT HSB HO HK HENV HMA HB0"] Lemma b_env : forall a w v, 0 <= a -> a + Z.of_nat w <= 2^63 -> (forall x, a <= x < a + Z.of_nat w -> ENVC x) -> rd m a w v -> rd mB0' a w v.
Proof. LiaFast.lf_pins (fun (mA0 regs CA ND c SB SP T RIv RBv FAv SHv SHFv Hc HND HSP HCA HCT HSB HO HK HENV HMA HB0 : LiaFast.U) => LiaFast.u0).
  intros a w v Ha Hw HE H. apply b_rd; [exact Ha | exact Hw | intros x Hx; unfold CELLS_B; do 6 right; exact (HE x Hx) |].
  apply mB0_envrd; [exact Ha | exact HE | lia | exact H].
Qed.
#[using="m mA0 regs ND TP K TSDA PT T SHv SHFv Hc HND HSP HCA HCT HSB HO HK HMA HB0"] Lemma b_slot3 : forall k v, wl_chk (L3a c CA (mc_tbl c / 2) RIv RBv FAv) k 8 = Some v -> -2048 <= k -> k + 8 <= 0 -> rd mB0' (SP + k) 8 v.
Proof. LiaFast.lf_pins (fun (m mA0 regs ND TP K TSDA PT T SHv SHFv Hc HND HSP HCA HCT HSB HO HK HMA HB0 : LiaFast.U) => LiaFast.u0).
  intros k v Hk K1 K2. apply b_rd; [zg2 K1 K2 | cbn; zg2 K1 K2 | intros x Hx; cbn in Hx; unfold CELLS_B; left; zg3 K1 K2 Hx |].
  apply mB0_slot3; assumption.
Qed.
#[using="m mA0 ND SB TP K TSDA PT T RIv RBv FAv SHv SHFv Hc HND HSP HCA HCT HSB HO HK HMA HB0"] Lemma b_slot2 : forall k v, wl_chk (L2a c CA (mc_tbl c / 2) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 21)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 22))))
      (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 23)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 24)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 25))))
      (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 26)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 27))))) k 8 = Some v ->
  -208 <= k -> k + 8 <= 0 -> rd mB0' (SP + k) 8 v.
Proof. LiaFast.lf_pins (fun (m mA0 ND SB TP K TSDA PT T RIv RBv FAv SHv SHFv Hc HND HSP HCA HCT HSB HO HK HMA HB0 : LiaFast.U) => LiaFast.u0).
  intros k v Hk K1 K2. apply b_rd; [zg2 K1 K2 | cbn; zg2 K1 K2 | intros x Hx; cbn in Hx; unfold CELLS_B; left; zg3 K1 K2 Hx |].
  apply mB0_slot2; assumption.
Qed.
#[using="m mA0 ND SB TP K TSDA PT T RIv RBv FAv SHv SHFv Hc HND HSP HCA HCT HSB HO HK HMA HB0"] Lemma b_slot1 : forall k v, wl_chk (L1a c CA (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 1)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 8))))
      (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 9)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 19))))
      (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 20))))) k 8 = Some v ->
  -80 <= k -> k + 8 <= 0 -> rd mB0' (SP + k) 8 v.
Proof. LiaFast.lf_pins (fun (m mA0 ND SB TP K TSDA PT T RIv RBv FAv SHv SHFv Hc HND HSP HCA HCT HSB HO HK HMA HB0 : LiaFast.U) => LiaFast.u0).
  intros k v Hk K1 K2. apply b_rd; [zg2 K1 K2 | cbn; zg2 K1 K2 | intros x Hx; cbn in Hx; unfold CELLS_B; left; zg3 K1 K2 Hx |].
  apply mB0_slot1; assumption.
Qed.
#[using="m mA0 regs CA ND SP TP K TSDA PT T RBv FAv SHv SHFv Hc HND HSP HCA HCT HSB HO HK HMA HB0"] Lemma b_mu : rd mB0' RIv 8 1152921504606846976.
Proof. LiaFast.lf_pins (fun (m mA0 regs CA ND SP TP K TSDA PT T RBv FAv SHv SHFv Hc HND HSP HCA HCT HSB HO HK HMA HB0 : LiaFast.U) => LiaFast.u0). apply b_rd; [zg | cbn; zg | intros x Hx; cbn in Hx; unfold CELLS_B; do 2 right; left; clear - Hx; lia | exact mB0_mu]. Qed.
#[using="m mA0 regs ND SB SP TP K TSDA PT T RIv RBv FAv SHv SHFv Hc HND HSP HCA HCT HSB HSEP HO HK HMA HB0"] Lemma b_ic : rd mB0' (CA + 80 * c + 4) 4 (mc_tbl c) /\ rd mB0' (CA + 80 * c + 8) 8 (sz_tbl c).
Proof. LiaFast.lf_pins (fun (m mA0 regs ND SB SP TP K TSDA PT T RIv RBv FAv SHv SHFv Hc HND HSP HCA HCT HSB HSEP HO HK HMA HB0 : LiaFast.U) => LiaFast.u0).
  pose proof (c_of_nd_range ND HND) as Hcr5. rewrite <- Hc in Hcr5.
  destruct mB0_ic as [X1 X2].
  split; (apply b_rd; [zg | cbn; zg | intros x Hx; cbn in Hx; unfold CELLS_B; right; left; clear - Hx Hcr5; lia | assumption]).
Qed.
#[using="mA0 regs ND SP TP K TSDA PT RBv FAv SHv SHFv Hc HND HSP HCA HCT HSB HSEP HO HK HMA HB0"] Lemma b_keep : forall a w v, 0 <= a -> a + Z.of_nat w <= 2^63 ->
  (T + 2872 <= a /\ a + Z.of_nat w <= T + 2888) \/ (CA + 2576 <= a /\ a + Z.of_nat w <= CA + 2592) \/ (RIv + 8 <= a /\ a + Z.of_nat w <= RIv + 128) ->
  rd m a w v -> rd mB0' a w v.
Proof. LiaFast.lf_pins (fun (mA0 regs ND SP TP K TSDA PT RBv FAv SHv SHFv Hc HND HSP HCA HCT HSB HSEP HO HK HMA HB0 : LiaFast.U) => LiaFast.u0).
  intros a w v Ha Hw Hr H. apply b_rd; [exact Ha | exact Hw | | apply mB0_keep; assumption].
  intros x Hx. unfold CELLS_B. pose proof fu_geo as G. clear - G Hr Hx. destruct Hr as [Hr|[Hr|Hr]]; [do 3 right; left; lia | right; left; lia | do 2 right; left; lia].
Qed.
#[using="m mA0 regs CA ND c SB TP K TSDA PT T RIv RBv FAv SHv SHFv Hc HND HSP HSTK HCA HCT HSB HO HK HMA HB0"] Lemma b_stk : stk_ok SEGS mB0' (wa SP) 2048.
Proof. LiaFast.lf_pins (fun (m mA0 regs CA ND c SB TP K TSDA PT T RIv RBv FAv SHv SHFv Hc HND HSP HSTK HCA HCT HSB HO HK HMA HB0 : LiaFast.U) => LiaFast.u0).
  apply (stk_ok_agree CELLS_B mB0' mB0); [exact HB0 | zg | zg | intros x Hx; unfold CELLS_B; left; exact Hx |].
  exact (stk_ok_grows m mB0 (wa SP) 2048 mB0_grows HSTK).
Qed.

Ltac benv H := apply b_env; [zg | cbn; zg | intros x Hx; cbn in Hx; envc Hx | exact H].

#[using="m mA0 regs ND st K TSDA PT SHFv Hc HND HSP HSTK HCA HCT HSB HSEP HO HK Hvals HENV HSHs Ist2 Iwc Iri Iwri Imm1 Imm2 Iwt Iwsh Iprem Igot Ipsz Icf Icf144 Idpm Ips1 Ips2 Ips3 Ips4 Ips5 Ips6 Ips7 Ips8 Ips9 Ips10 Ips11 Itls1 Itls2 Itls3 Itls4 Itls5 HMA HB0"] Lemma stageB : forall R1', getr R1' 1 = wa 481796 -> getr R1' 2 = wa (SP - 400) -> getr R1' 4 = wa TP -> getr R1' 8 = wa 262144 ->
  getr R1' 10 = wa RBv -> getr R1' 21 = wa (32 * c) -> getr R1' 22 = wa 923480 ->
  exists R2 mB, msteps SEGS (mkst R1' (wa 0x73c48) mB0' rom) (mkst R2 (wa 0x73c44) mB rom) /\
    EC R2 FAv /\ getr R2 (Z_to_bv 5 (Z.of_nat 1)) = wa 481796 /\ getr R2 (Z_to_bv 5 (Z.of_nat 2)) = wa (SP - 448) /\
    getr R2 (Z_to_bv 5 (Z.of_nat 8)) = wa 262144 /\ getr R2 (Z_to_bv 5 (Z.of_nat 21)) = wa (32 * c) /\ getr R2 (Z_to_bv 5 (Z.of_nat 22)) = wa 923480 /\
    getr R2 (Z_to_bv 5 (Z.of_nat 4)) = wa TP /\ getr R2 (Z_to_bv 5 (Z.of_nat 3)) = getr R1' (Z_to_bv 5 (Z.of_nat 3)) /\
    PB mB /\ FRB mB0' mB.
Proof. LiaFast.lf_pins (fun (m mA0 regs ND st K TSDA PT SHFv Hc HND HSP HSTK HCA HCT HSB HSEP HO HK Hvals HENV HSHs Ist2 Iwc Iri Iwri Imm1 Imm2 Iwt Iwsh Iprem Igot Ipsz Icf Icf144 Idpm Ips1 Ips2 Ips3 Ips4 Ips5 Ips6 Ips7 Ips8 Ips9 Ips10 Ips11 Itls1 Itls2 Itls3 Itls4 Itls5 HMA HB0 : LiaFast.U) => LiaFast.u0).
  intros R1' Q1 Q2 Q4 Q8 Q10 Q21 Q22.
  pose proof (c_of_nd_range ND HND) as Hcr5. rewrite <- Hc in Hcr5.
  assert (Hst3 : 0 <= mm1 < 2^64 /\ 0 <= mm2 < 2^64 /\ 0 <= st2 < 2^64) by (clear - Hvals; lia).
  assert (FRI : forall i, 1 <= i < 16 -> rd mB0' (RIv + 8 * i) 8 0).
  { intros i Hi. apply b_keep; [zg1 Hi | cbn; zg1 Hi | right; right; cbn; zg1 Hi | exact (Iri i ltac:(lia))]. }
  destruct (segB rom mB0' R1' CA c SB SP TP K TSDA PT T mm1 mm2 st2 Hcr5 HSP HCT HO HSB HK ltac:(clear - HCA; lia) HSHs Hst3 Q1 Q2 Q4 Q8 Q10 Q21 Q22)
    as (R2 & mB & Hms & B1 & B2 & B8 & B10 & B11 & B12 & B13 & B14 & B15 & B17 & B21 & B22 & B4 & B3 & BSH & S88 & S80 & S72 & S64 & S56 & S48 &
        N24 & N16 & N8 & N0 & E40 & E32 & E24 & E16 & E8 & BRI48 & BM1 & BM2 & BST2 & BFR & BG).
  - exact b_stk.
  - replace (SP - 400 + 88) with (SP + -312) by ring. apply b_slot3; [reflexivity | lia | lia].
  - replace (SP - 400 + 80) with (SP + -320) by ring. apply b_slot3; [reflexivity | lia | lia].
  - replace (SP - 400 + 72) with (SP + -328) by ring. apply b_slot3; [reflexivity | lia | lia].
  - replace (SP - 400 + 64) with (SP + -336) by ring. apply b_slot3; [reflexivity | lia | lia].
  - replace (SP - 400 + 56) with (SP + -344) by ring. apply b_slot3; [reflexivity | lia | lia].
  - replace (SP - 400 + 48) with (SP + -352) by ring. apply b_slot3; [reflexivity | lia | lia].
  - replace (SP - 304 + 24) with (SP + -280) by ring. apply b_slot3; [reflexivity | lia | lia].
  - replace (SP - 304 + 16) with (SP + -288) by ring. apply b_slot3; [reflexivity | lia | lia].
  - replace (SP - 304 + 8) with (SP + -296) by ring. apply b_slot3; [reflexivity | lia | lia].
  - replace (SP - 304 + 0) with (SP + -304) by ring. apply b_slot3; [reflexivity | lia | lia].
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
  - apply b_keep; [zg | cbn; zg | left; cbn; lia | exact Imm1].
  - apply b_keep; [zg | cbn; zg | left; cbn; lia | exact Imm2].
  - apply b_keep; [zg | cbn; zg | right; left; cbn; lia | exact Ist2].
  - apply b_wr; [zg | zg | intros x Hx; unfold CELLS_B; do 3 right; left; clear - Hx; lia | exact Iwt].
  - apply b_wr; [zg | zg | intros x Hx; unfold CELLS_B; right; left; clear - Hx; lia |].
    intros d k Hd Hk. replace (CA + 2584 + d) with (CA + (2584 + d)) by ring. apply Iwc; lia.
  - exact (FRI 2 ltac:(lia)).
  - exact (FRI 3 ltac:(lia)).
  - exact (FRI 4 ltac:(lia)).
  - exact (FRI 6 ltac:(lia)).
  - apply b_wr; [zg | zg | intros x Hx; unfold CELLS_B; do 2 right; left; clear - Hx; lia | exact Iwri].
  - benv Iprem.
  - apply b_wr; [zg | zg | intros x Hx; unfold CELLS_B; do 4 right; left; clear - Hx; lia | exact Iwsh].
  - exists R2, mB. split; [exact Hms|]. split; [unfold EC; repeat split; first [assumption | (rewrite B10; f_equal; unfold FAv; ring)]|].
    split; [exact B1|]. split; [exact B2|]. split; [exact B8|]. split; [exact B21|]. split; [exact B22|]. split; [exact B4|]. split; [exact B3|].
    split; [|split; [exact BFR | exact BG]].
    unfold PB. split; [exact BSH|].
    split; [exact S88|]. split; [exact S80|]. split; [exact S72|]. split; [exact S64|]. split; [exact S56|]. split; [exact S48|].
    split; [exact N24|]. split; [exact N16|]. split; [exact N8|]. split; [exact N0|].
    split; [exact E40|]. split; [exact E32|]. split; [exact E24|]. split; [exact E16|]. split; [exact E8|].
    split; [exact BRI48|]. split; [exact BM1|]. split; [exact BM2|]. exact BST2.
Qed.

(* [comment removed for export] *)
Definition CHB (x : Z) : Prop :=
  SP - 2048 <= x < SP - 272 \/ SHv <= x < SHv + 32768 \/ RIv + 48 <= x < RIv + 56 \/ CA + 2584 <= x < CA + 2592 \/ T + 2872 <= x < T + 2888.
#[using="Type"] Lemma chb_chc : forall x, CHB x -> CHC x.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros x H. unfold CHB in H. unfold CHC. destruct H as [H|[H|[H|[H|H]]]].
  - left. clear - H. lia.
  - do 6 right. left. exact H.
  - do 2 right. left. clear - H. lia.
  - right. left. clear - H. lia.
  - do 3 right. left. exact H.
Qed.
#[using="ND RBv Hc HND HSP HCA HCT HSB HSEP HO HK HENV"] Lemma fa_sep : forall x, CELLS_B x -> ~ (FAv <= x < FAv + 262144).
Proof. LiaFast.lf_pins (fun (ND RBv Hc HND HSP HCA HCT HSB HSEP HO HK HENV : LiaFast.U) => LiaFast.u0).
  intros x Hx. unfold CELLS_B in Hx. destruct Hx as [Hx|[Hx|[Hx|[Hx|[Hx|[Hx|Hx]]]]]].
  - zg1 Hx.
  - pose proof HSEP as D. pose proof fu_geo as G. clear - G D Hx. lia.
  - zg1 Hx.
  - pose proof HSEP as D. pose proof fu_geo as G. clear - G D Hx. lia.
  - zg1 Hx.
  - zg1 Hx.
  - intro F. apply (HENV x Hx). unfold CHC. do 5 right. left. exact F.
Qed.

Section SC.
Variables (mB mC0' : word -> option byte).
Hypothesis HPB : PB mB.
Hypothesis HFB : FRB mB0' mB.
Hypothesis HC0 : agree_on CELLS_C mC0' (kz mB FAv 262144).

#[using="ND RBv FAv Hc HND HSP HCA HCT HSB HSEP HO HK HENV HC0"] Lemma c_of_mB : forall a w v, 0 <= a -> a + Z.of_nat w <= 2^63 -> (forall x, a <= x < a + Z.of_nat w -> CELLS_B x) -> rd mB a w v -> rd mC0' a w v.
Proof. LiaFast.lf_pins (fun (ND RBv FAv Hc HND HSP HCA HCT HSB HSEP HO HK HENV HC0 : LiaFast.U) => LiaFast.u0).
  intros a w v Ha Hw HS H. apply (rd_agree CELLS_C mC0' (kz mB FAv 262144)); [exact HC0 | exact Ha | lia | intros x Hx; left; exact (HS x Hx) |].
  apply (rd_frame mB); [exact Ha | lia | intros x Hx; apply kz_out; [lia | exact (fa_sep x (HS x Hx))] | exact H].
Qed.
#[using="ND RBv FAv Hc HND HSP HCA HCT HSB HSEP HO HK HENV mB HFB HC0"] Lemma c_of_mB0' : forall a w v, 0 <= a -> a + Z.of_nat w <= 2^63 -> (forall x, a <= x < a + Z.of_nat w -> CELLS_B x /\ ~ CHB x) -> rd mB0' a w v -> rd mC0' a w v.
Proof. LiaFast.lf_pins (fun (ND RBv FAv Hc HND HSP HCA HCT HSB HSEP HO HK HENV mB HFB HC0 : LiaFast.U) => LiaFast.u0).
  intros a w v Ha Hw HS H. apply c_of_mB; [exact Ha | exact Hw | intros x Hx; exact (proj1 (HS x Hx)) |].
  destruct HFB as [FR _]. apply (rd_frame mB0'); [exact Ha | lia | | exact H].
  intros x Hx. destruct (HS x Hx) as [_ N]. unfold CHB in N.
  apply FR; [lia | intro F; apply N; left; exact F | intro F; apply N; right; left; exact F | intro F; apply N; do 2 right; left; exact F
            | intro F; apply N; do 3 right; left; exact F | intro F; apply N; do 4 right; exact F].
Qed.
#[using="mA0 regs CA ND c SB SP T RIv RBv FAv SHv SHFv Hc HND HSP HCA HCT HSB HSEP HO HK HENV HMA mB0' HB0 mB HFB HC0"] Lemma c_env : forall a w v, 0 <= a -> a + Z.of_nat w <= 2^63 -> (forall x, a <= x < a + Z.of_nat w -> ENVC x) -> rd m a w v -> rd mC0' a w v.
Proof. LiaFast.lf_pins (fun (mA0 regs CA ND c SB SP T RIv RBv FAv SHv SHFv Hc HND HSP HCA HCT HSB HSEP HO HK HENV HMA mB0' HB0 mB HFB HC0 : LiaFast.U) => LiaFast.u0).
  intros a w v Ha Hw HE H. apply c_of_mB0'; [exact Ha | exact Hw | | apply b_env; assumption].
  intros x Hx. split; [unfold CELLS_B; do 6 right; exact (HE x Hx) | intro F; exact (HENV x (HE x Hx) (chb_chc x F))].
Qed.
(* [comment removed for export] *)
#[using="CA ND c SB TP K TSDA PT T RIv RBv FAv SHv SHFv Hc HND HSP HCA HCT HSB HSEP HO HK HENV mB HFB HC0"] Lemma c_slot : forall k v, -272 <= k -> k + 8 <= 0 -> rd mB0' (SP + k) 8 v -> rd mC0' (SP + k) 8 v.
Proof. LiaFast.lf_pins (fun (CA ND c SB TP K TSDA PT T RIv RBv FAv SHv SHFv Hc HND HSP HCA HCT HSB HSEP HO HK HENV mB HFB HC0 : LiaFast.U) => LiaFast.u0).
  intros k v K1 K2 H. apply c_of_mB0'; [zg2 K1 K2 | cbn; zg2 K1 K2 | | exact H].
  intros x Hx. cbn in Hx. split; [unfold CELLS_B; left; zg3 K1 K2 Hx | unfold CHB; zg3 K1 K2 Hx].
Qed.
(* [comment removed for export] *)
#[using="m mA0 regs CA ND SP TP K TSDA PT T RBv FAv SHv SHFv Hc HND HSP HCA HCT HSB HSEP HO HK HENV HSHs Iri HMA mB0' HB0 mB HFB HC0"] Lemma c_ri : forall i, 1 <= i < 16 -> i <> 6 -> rd mC0' (RIv + 8 * i) 8 0.
Proof. LiaFast.lf_pins (fun (m mA0 regs CA ND SP TP K TSDA PT T RBv FAv SHv SHFv Hc HND HSP HCA HCT HSB HSEP HO HK HENV HSHs Iri HMA mB0' HB0 mB HFB HC0 : LiaFast.U) => LiaFast.u0).
  intros i Hi Hi6. pose proof fu_d_ri_t as D1. pose proof HSEP as D2.
  assert (D3 : RIv + 128 <= SHv \/ SHv + 32768 <= RIv) by (unfold shsep in HSHs; clear - HSHs; tauto).
  apply c_of_mB0'; [zg1 Hi | cbn; zg1 Hi | |].
  - intros x Hx. cbn in Hx. split; [unfold CELLS_B; do 2 right; left; clear - Hi Hx; lia |].
    unfold CHB. pose proof fu_geo as G. clear - G Hi Hi6 Hx D1 D2 D3. lia.
  - apply b_keep; [zg1 Hi | cbn; zg1 Hi | right; right; cbn; zg1 Hi | exact (Iri i ltac:(lia))].
Qed.
#[using="mA0 regs ND RBv FAv HMA mB0' HB0 mB HFB HC0"] Lemma c_wr : forall a n, 0 <= a -> a + n <= 2^63 -> (forall x, a <= x < a + n -> CELLS_B x) -> wr m a n -> wr mC0' a n.
Proof. LiaFast.lf_pins (fun (mA0 regs ND RBv FAv HMA mB0' HB0 mB HFB HC0 : LiaFast.U) => LiaFast.u0).
  intros a n Ha Hn HS H. apply (wr_agree CELLS_C mC0' (kz mB FAv 262144)); [exact HC0 | exact Ha | lia | intros x Hx; left; exact (HS x Hx) |].
  apply (wr_grows mB); [apply kz_grows|]. apply (wr_grows mB0'); [exact (proj2 HFB)|]. apply b_wr; assumption.
Qed.
#[using="m mA0 regs CA ND c SB TP K TSDA PT T RIv RBv FAv SHv SHFv Hc HND HSP HSTK HCA HCT HSB HO HK HMA mB0' HB0 mB HFB HC0"] Lemma c_stk : stk_ok SEGS mC0' (wa SP) 2048.
Proof. LiaFast.lf_pins (fun (m mA0 regs CA ND c SB TP K TSDA PT T RIv RBv FAv SHv SHFv Hc HND HSP HSTK HCA HCT HSB HO HK HMA mB0' HB0 mB HFB HC0 : LiaFast.U) => LiaFast.u0).
  apply (stk_ok_agree CELLS_C mC0' (kz mB FAv 262144)); [exact HC0 | zg | zg | intros x Hx; left; unfold CELLS_B; left; exact Hx |].
  apply (stk_ok_grows mB); [apply kz_grows|]. apply (stk_ok_grows mB0'); [exact (proj2 HFB)|]. exact b_stk.
Qed.
#[using="CA ND SP TP K TSDA PT T RIv RBv SHv SHFv Hc HND HSP HCA HCT HSB HO HK mB HC0"] Lemma c_wfa : wr mC0' FAv 262144.
Proof. LiaFast.lf_pins (fun (CA ND SP TP K TSDA PT T RIv RBv SHv SHFv Hc HND HSP HCA HCT HSB HO HK mB HC0 : LiaFast.U) => LiaFast.u0).
  apply (wr_agree CELLS_C mC0' (kz mB FAv 262144)); [exact HC0 | zg | zg | intros x Hx; right; exact Hx |].
  apply kz_wr; zg.
Qed.
#[using="m mA0 regs CA ND c SB SP TP K TSDA PT T RIv RBv FAv SHv SHFv Hc HND HSP HCA HCT HSB HSEP HO HK HENV HIMG HMA mB0' HB0 mB HFB HC0"] Lemma c_img : forall i, 65536 <= i < 143360 -> mC0' (Z_to_bv 64 i) = None.
Proof. LiaFast.lf_pins (fun (m mA0 regs CA ND c SB SP TP K TSDA PT T RIv RBv FAv SHv SHFv Hc HND HSP HCA HCT HSB HSEP HO HK HENV HIMG HMA mB0' HB0 mB HFB HC0 : LiaFast.U) => LiaFast.u0).
  intros i Hi. assert (HE : ENVC i) by (unfold ENVC; left; exact Hi).
  assert (HCB : CELLS_B i) by (unfold CELLS_B; do 6 right; exact HE).
  apply (agree_none CELLS_C mC0' (kz mB FAv 262144)); [exact HC0 | clear - Hi; lia | left; exact HCB |].
  change (Z_to_bv 64 i) with (wa i). rewrite kz_out; [| clear - Hi; lia | exact (fa_sep i HCB)].
  destruct HFB as [FR _].
  assert (N : ~ CHB i) by (intro F; exact (HENV i HE (chb_chc i F))). unfold CHB in N.
  rewrite FR; [| clear - Hi; lia | intro F; apply N; left; exact F | intro F; apply N; right; left; exact F | intro F; apply N; do 2 right; left; exact F
               | intro F; apply N; do 3 right; left; exact F | intro F; apply N; do 4 right; exact F].
  rewrite (HB0 i ltac:(clear - Hi; lia) HCB). rewrite mB0_env; [| clear - Hi; lia | exact (HENV i HE)]. exact (HIMG i Hi).
Qed.

(* [comment removed for export] *)
#[using="CA ND SP TP K TSDA PT T RBv FAv SHv SHFv Hc HND HSP HCA HCT HSB HSEP HO HK HENV HSHs mB HFB HC0"] Lemma c_riw : forall i v, 0 <= i < 16 -> i <> 6 -> rd mB0' (RIv + 8 * i) 8 v -> rd mC0' (RIv + 8 * i) 8 v.
Proof. LiaFast.lf_pins (fun (CA ND SP TP K TSDA PT T RBv FAv SHv SHFv Hc HND HSP HCA HCT HSB HSEP HO HK HENV HSHs mB HFB HC0 : LiaFast.U) => LiaFast.u0).
  intros i v Hi Hi6 H. pose proof fu_d_ri_t as D1. pose proof HSEP as D2.
  assert (D3 : RIv + 128 <= SHv \/ SHv + 32768 <= RIv) by (unfold shsep in HSHs; clear - HSHs; tauto).
  apply c_of_mB0'; [zg1 Hi | cbn; zg1 Hi | | exact H].
  intros x Hx. cbn in Hx. split; [unfold CELLS_B; do 2 right; left; clear - Hi Hx; lia |].
  unfold CHB. pose proof fu_geo as G. clear - G Hi Hi6 Hx D1 D2 D3. lia.
Qed.
(* [comment removed for export] *)
#[using="ND c SB SP TP K TSDA PT T RIv RBv FAv SHv SHFv Hc HND HSP HCA HCT HSB HSEP HO HK HENV HSHs mB HFB HC0"] Lemma c_cache : forall a w v, CA <= a -> a + Z.of_nat w <= CA + 2584 -> rd mB0' a w v -> rd mC0' a w v.
Proof. LiaFast.lf_pins (fun (ND c SB SP TP K TSDA PT T RIv RBv FAv SHv SHFv Hc HND HSP HCA HCT HSB HSEP HO HK HENV HSHs mB HFB HC0 : LiaFast.U) => LiaFast.u0).
  intros a w v K1 K2 H. pose proof fu_d_ri_t as D1. pose proof HSEP as D2.
  assert (D4 : T + 4096 <= SHv \/ SHv + 32768 <= T) by (unfold shsep in HSHs; clear - HSHs; tauto).
  apply c_of_mB0'; [zg2 K1 K2 | zg2 K1 K2 | | exact H].
  intros x Hx. split; [unfold CELLS_B; right; left; clear - K1 K2 Hx; lia |].
  unfold CHB. pose proof fu_geo as G. clear - G K1 K2 Hx D1 D2 D4. lia.
Qed.

Ltac zc := cbv; let X := fresh in intro X; discriminate X.
Ltac cenv H := apply c_env; [zg | cbn; zg | intros x Hx; cbn in Hx; envc Hx | exact H].

#[using="m mA0 ND st st2 K TSDA PT mm1 mm2 RIv SHv Hc HND HSP HSTK HCA HCT HSB HSEP HO HK Hvals HENV HSHs HSHF Ist Iwc Iri Iwri Iwt Iwshf ISB IRIB Icf Icf144 Ips1 Ips2 Ips3 Ips4 Ips5 Ips6 Ips7 Ips8 Ips9 Ips10 Ips11 Itls1 Itls2 Itls3 Itls4 Itls5 HIMG HMA mB0' HB0 mB HPB HFB HC0"] Lemma stageC : forall R2', getr R2' 1 = wa 481796 -> getr R2' 2 = wa (SP - 448) -> getr R2' 4 = wa TP -> getr R2' 8 = wa 262144 ->
  getr R2' 10 = wa FAv -> getr R2' 21 = wa (32 * c) -> getr R2' 22 = wa 923480 ->
  exists R3 m3, msteps SEGS (mkst R2' (wa 0x73c48) mC0' rom) (mkst R3 (wa 0x43f08) m3 rom) /\
    getr R3 (Z_to_bv 5 (Z.of_nat 2)) = wa SP /\ getr R3 (Z_to_bv 5 (Z.of_nat 10)) = wa RBv /\
    (forall k, In k [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R3 (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))) /\
    (forall k, In k [3; 4]%nat -> getr R3 (Z_to_bv 5 (Z.of_nat k)) = getr R2' (Z_to_bv 5 (Z.of_nat k))) /\
    INV_C m3 CA SB c (32 * c) (mc_tbl c / 2) (262144 / (32 * c)) 1 /\
    (forall x, 0 <= x < 2^64 -> ~ (SP - 2048 <= x < SP) -> ~ (SHFv <= x < SHFv + 32768) -> ~ (T + 2872 <= x < T + 2888) ->
        ~ (FAv <= x < FAv + 262144) -> ~ owned_C CA SB c x -> m3 (wa x) = mC0' (wa x)) /\ mem_grows mC0' m3.
Proof. LiaFast.lf_pins (fun (m mA0 ND st st2 K TSDA PT mm1 mm2 RIv SHv Hc HND HSP HSTK HCA HCT HSB HSEP HO HK Hvals HENV HSHs HSHF Ist Iwc Iri Iwri Iwt Iwshf ISB IRIB Icf Icf144 Ips1 Ips2 Ips3 Ips4 Ips5 Ips6 Ips7 Ips8 Ips9 Ips10 Ips11 Itls1 Itls2 Itls3 Itls4 Itls5 HIMG HMA mB0' HB0 mB HPB HFB HC0 : LiaFast.U) => LiaFast.u0).
  intros R2' Q1 Q2 Q4 Q8 Q10 Q21 Q22.
  pose proof (c_of_nd_range ND HND) as Hcr5. rewrite <- Hc in Hcr5.
  destruct HPB as (BSH & S88 & S80 & S72 & S64 & S56 & S48 & N24 & N16 & N8 & N0 & E40 & E32 & E24 & E16 & E8 & BRI48 & BM1 & BM2 & BST2).
  set (mm1' := (mm1 + 1) mod 2^64). set (mm2' := (mm2 + 262144) mod 2^64).
  assert (Hst' : 0 <= mm1' < 2^64 /\ 0 <= mm2' < 2^64) by (unfold mm1', mm2'; split; apply Z.mod_pos_bound; lia).
  assert (W : forall a v, SP - 2048 <= a -> a + 8 <= SP -> rd mB a 8 v -> rd mC0' a 8 v).
  { intros a v K1 K2 H. apply c_of_mB; [zg2 K1 K2 | cbn; zg2 K1 K2 | intros x Hx; cbn in Hx; unfold CELLS_B; left; clear - K1 K2 Hx; lia | exact H]. }
  assert (WT : forall a v, T + 2872 <= a -> a + 8 <= T + 2888 -> rd mB a 8 v -> rd mC0' a 8 v).
  { intros a v K1 K2 H. apply c_of_mB; [zg2 K1 K2 | cbn; zg2 K1 K2 | intros x Hx; cbn in Hx; unfold CELLS_B; do 3 right; left; clear - K1 K2 Hx; lia | exact H]. }
  destruct (segC1 rom mC0' R2' c SB SP TP K TSDA PT T mm1' mm2' Hcr5 HSP HO HSB HK HSHF Hst' Q1 Q2 Q4 Q8 Q10 Q21 Q22)
    as (R3' & mC1 & Hms1 & C2r & C4 & C8 & C10 & C11 & C12 & C13 & C18 & C19 & C21 & C22 & C3 & CSHF & CRI24 & CM1 & CM2 & CFR & CG).
  - exact c_stk.
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
  - apply c_wr; [zg | zg | intros x Hx; unfold CELLS_B; do 3 right; left; clear - Hx; lia | exact Iwt].
  - pose proof (c_ri 4 ltac:(lia) ltac:(lia)) as X. replace (RIv + 8 * 4) with (RIv + 32) in X by ring. exact X.
  - apply c_wr; [zg | zg | intros x Hx; unfold CELLS_B; do 2 right; left; clear - Hx; lia | exact Iwri].
  - apply c_wr; [zg | zg | intros x Hx; unfold CELLS_B; do 5 right; left; clear - Hx; lia | exact Iwshf].
  - (* [comment removed for export] *)
    pose proof fu_d_ri_t as D1. pose proof HSEP as D2.
    assert (D3f : RIv + 128 <= SHFv \/ SHFv + 32768 <= RIv) by (unfold shsep in HSHF; clear - HSHF; tauto).
    assert (D4f : T + 4096 <= SHFv \/ SHFv + 32768 <= T) by (unfold shsep in HSHF; clear - HSHF; tauto).
    assert (K1 : forall a w v, 0 <= a -> a + Z.of_nat w <= 2^63 ->
              (forall x, a <= x < a + Z.of_nat w -> ~ (SP - 2048 <= x < SP - 320) /\ ~ (SHFv <= x < SHFv + 32768) /\ ~ (RIv + 24 <= x < RIv + 32) /\ ~ (T + 2872 <= x < T + 2888)) ->
              rd mC0' a w v -> rd mC1 a w v).
    { intros a w v Ha Hw HS H. apply (rd_frame mC0'); [exact Ha | clear - Hw; lia | | exact H].
      intros x Hx. destruct (HS x Hx) as (N1 & N2 & N3 & N4). apply CFR; [clear - Ha Hw Hx; lia | exact N1 | exact N2 | exact N3 | exact N4]. }
    assert (KS : forall k v, -272 <= k -> k + 8 <= 0 -> rd mB0' (SP + k) 8 v -> rd mC1 (SP + k) 8 v).
    { intros k v K1' K2' H. apply K1; [zg2 K1' K2' | cbn; zg2 K1' K2' | | apply c_slot; assumption].
      intros x Hx. cbn in Hx. pose proof fu_geo as G. clear - G K1' K2' Hx. lia. }
    assert (KE : forall a w v, 0 <= a -> a + Z.of_nat w <= 2^63 -> (forall x, a <= x < a + Z.of_nat w -> ENVC x) -> rd m a w v -> rd mC1 a w v).
    { intros a w v Ha Hw HE H. apply K1; [exact Ha | exact Hw | | apply c_env; assumption].
      intros x Hx. pose proof (HENV x (HE x Hx)) as N. unfold CHC in N.
      split; [intro F; apply N; left; clear - F; lia|]. split; [intro F; apply N; do 7 right; exact F|].
      split; [intro F; apply N; do 2 right; left; clear - F; lia | intro F; apply N; do 3 right; left; exact F]. }
    assert (KR : forall i v, 0 <= i < 16 -> i <> 6 -> i <> 3 -> rd mB0' (RIv + 8 * i) 8 v -> rd mC1 (RIv + 8 * i) 8 v).
    { intros i v Hi H6 H3 H. apply K1; [zg1 Hi | cbn; zg1 Hi | | apply c_riw; assumption].
      intros x Hx. cbn in Hx. pose proof fu_geo as G. clear - G Hi H3 Hx D1 D3f. lia. }
    assert (KR0 : forall i, 1 <= i < 16 -> i <> 6 -> i <> 3 -> rd mC1 (RIv + 8 * i) 8 0).
    { intros i Hi H6 H3. apply KR; [clear - Hi; lia | exact H6 | exact H3 |].
      apply b_keep; [zg1 Hi | cbn; zg1 Hi | right; right; cbn; zg1 Hi | exact (Iri i ltac:(lia))]. }
    assert (KC : forall a w v, CA <= a -> a + Z.of_nat w <= CA + 2584 -> rd mB0' a w v -> rd mC1 a w v).
    { intros a w v K1' K2' H. apply K1; [zg2 K1' K2' | zg2 K1' K2' | | apply c_cache; assumption].
      intros x Hx. pose proof fu_geo as G. clear - G K1' K2' Hx D1 D2 D4f. lia. }
    assert (KW : forall a n, wr mC0' a n -> wr mC1 a n) by (intros a n H; exact (wr_grows mC0' mC1 a n CG H)).
    destruct b_ic as [BIC1 BIC2]. rewrite (sz_tbl_small c Hcr5) in BIC2.
    destruct (segC2 rom mC1 R3' CA ND c SB SP 0 st
                (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 1)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 8)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 9))))
                (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 19)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 20))))
                (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 21)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 22)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 23))))
                (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 24)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 25)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 26))))
                (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 27))))
                Hc HND HSP HCA HSB HSEP ltac:(clear - Hvals; lia)
                ltac:(regzG; exact C2r) ltac:(regzG; exact C8) ltac:(regzG; exact C10) ltac:(regzG; exact C11) ltac:(regzG; exact C12) ltac:(regzG; exact C13)
                ltac:(regzG; exact C19) ltac:(regzG; exact C21))
      as (R3 & m3 & Hms2 & F2 & F10 & F1 & F8 & F9 & F18 & F19 & F20 & F21 & F22 & F23 & F24 & F25 & F26 & F27 & FK & FINV & FFR & FG).
    + exact (stk_ok_grows mC0' mC1 (wa SP) 2048 CG c_stk).
    + replace (SP - 216) with (SP + -216) by ring. apply KS; [zc | zc | apply b_slot3; [reflexivity | zc | zc]].
    + replace (SP - 224) with (SP + -224) by ring. apply KS; [zc | zc | apply b_slot3; [reflexivity | zc | zc]].
    + replace (SP - 232) with (SP + -232) by ring. apply KS; [zc | zc | apply b_slot3; [reflexivity | zc | zc]].
    + replace (SP - 240) with (SP + -240) by ring. apply KS; [zc | zc | apply b_slot3; [reflexivity | zc | zc]].
    + replace (SP - 248) with (SP + -248) by ring. apply KS; [zc | zc | apply b_slot3; [reflexivity | zc | zc]].
    + replace (SP - 256) with (SP + -256) by ring. apply KS; [zc | zc | apply b_slot3; [reflexivity | zc | zc]].
    + replace (SP - 264) with (SP + -264) by ring. apply KS; [zc | zc | apply b_slot3; [reflexivity | zc | zc]].
    + replace (SP - 272) with (SP + -272) by ring. apply KS; [zc | zc | apply b_slot3; [reflexivity | zc | zc]].
    + replace (SP - 88) with (SP + -88) by ring. apply KS; [zc | zc | apply b_slot2; [reflexivity | zc | zc]].
    + replace (SP - 96) with (SP + -96) by ring. apply KS; [zc | zc | apply b_slot2; [reflexivity | zc | zc]].
    + replace (SP - 104) with (SP + -104) by ring. apply KS; [zc | zc | apply b_slot2; [reflexivity | zc | zc]].
    + replace (SP - 112) with (SP + -112) by ring. apply KS; [zc | zc | apply b_slot2; [reflexivity | zc | zc]].
    + replace (SP - 120) with (SP + -120) by ring. apply KS; [zc | zc | apply b_slot2; [reflexivity | zc | zc]].
    + replace (SP - 128) with (SP + -128) by ring. apply KS; [zc | zc | apply b_slot2; [reflexivity | zc | zc]].
    + replace (SP - 136) with (SP + -136) by ring. apply KS; [zc | zc | apply b_slot2; [reflexivity | zc | zc]].
    + replace (SP - 144) with (SP + -144) by ring. apply KS; [zc | zc | apply b_slot2; [reflexivity | zc | zc]].
    + replace (SP - 152) with (SP + -152) by ring. apply KS; [zc | zc | apply b_slot2; [reflexivity | zc | zc]].
    + replace (SP - 160) with (SP + -160) by ring. apply KS; [zc | zc | apply b_slot2; [reflexivity | zc | zc]].
    + replace (SP - 168) with (SP + -168) by ring. apply KS; [zc | zc | apply b_slot2; [reflexivity | zc | zc]].
    + replace (SP - 176) with (SP + -176) by ring. apply KS; [zc | zc | apply b_slot2; [reflexivity | zc | zc]].
    + replace (SP - 184) with (SP + -184) by ring. apply KS; [zc | zc | apply b_slot2; [reflexivity | zc | zc]].
    + replace (SP - 72) with (SP + -72) by ring. apply KS; [zc | zc | apply b_slot1; [reflexivity | zc | zc]].
    + replace (SP - 64) with (SP + -64) by ring. apply KS; [zc | zc | apply b_slot1; [reflexivity | zc | zc]].
    + replace (SP - 56) with (SP + -56) by ring. apply KS; [zc | zc | apply b_slot1; [reflexivity | zc | zc]].
    + replace (SP - 48) with (SP + -48) by ring. apply KS; [zc | zc | apply b_slot1; [reflexivity | zc | zc]].
    + replace (SP - 40) with (SP + -40) by ring. apply KS; [zc | zc | apply b_slot1; [reflexivity | zc | zc]].
    + replace (SP - 32) with (SP + -32) by ring. apply KS; [zc | zc | apply b_slot1; [reflexivity | zc | zc]].
    + replace (SP - 24) with (SP + -24) by ring. apply KS; [zc | zc | apply b_slot1; [reflexivity | zc | zc]].
    + replace (SP - 16) with (SP + -16) by ring. apply KS; [zc | zc | apply b_slot1; [reflexivity | zc | zc]].
    + replace (SP - 8) with (SP + -8) by ring. apply KS; [zc | zc | apply b_slot1; [reflexivity | zc | zc]].
    + repeat match goal with |- _ /\ _ => split end; first [exact (proj1 (bvu_rng _)) | exact (proj2 (bvu_rng _))].
    + pose proof (KR 0 1152921504606846976 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)) as X. rewrite Z.add_0_r in X. apply X. exact b_mu.
    + exact (KR0 2 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)).
    + exact (KR0 4 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)).
    + exact (KR0 5 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)).
    + apply K1; [zg | cbn; zg | |].
      * intros x Hx. cbn in Hx. pose proof fu_geo as G. clear - G Hx D1 D3f. lia.
      * apply c_of_mB; [zg | cbn; zg | intros x Hx; cbn in Hx; unfold CELLS_B; do 2 right; left; clear - Hx; lia | exact BRI48].
    + exact (KR0 7 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)).
    + exact (KR0 9 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)).
    + apply KW. apply c_wr; [zg | zg | intros x Hx; unfold CELLS_B; do 2 right; left; clear - Hx; lia | exact Iwri].
    + apply KC; [clear - Hcr5; lia | cbn; clear - Hcr5; lia | exact BIC1].
    + apply KC; [clear - Hcr5; lia | cbn; clear - Hcr5; lia | exact BIC2].
    + apply KW. apply c_wr; [zg | zg | intros x Hx; unfold CELLS_B; right; left; clear - Hx; lia | exact Iwc].
    + apply KE; [clear; lia | cbn; clear; lia | intros x Hx; cbn in Hx; envc Hx | exact ISB].
    + apply KE; [clear; lia | cbn; clear; lia | intros x Hx; cbn in Hx; envc Hx | exact IRIB].
    + apply KC; [clear; lia | cbn; clear; lia |]. apply b_keep; [zg | cbn; zg | right; left; cbn; clear; lia | exact Ist].
    + apply KW. exact c_wfa.
    + intros i Hi. change (Z_to_bv 64 i) with (wa i).
      assert (HE : ENVC i) by (unfold ENVC; left; exact Hi). pose proof (HENV i HE) as N. unfold CHC in N.
      rewrite CFR; [exact (c_img i Hi) | clear - Hi; lia | intro F; apply N; left; clear - F; lia | intro F; apply N; do 7 right; exact F
                   | intro F; apply N; do 2 right; left; clear - F; lia | intro F; apply N; do 3 right; left; exact F].
    + exists R3, m3. split; [exact (msteps_trans SEGS _ _ _ Hms1 Hms2)|].
      split; [exact F2|]. split; [exact F10|].
      split.
      { intros k Hk. cbn [In] in Hk.
        destruct Hk as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]];
          first [rewrite F1 | rewrite F8 | rewrite F9 | rewrite F18 | rewrite F19 | rewrite F20 | rewrite F21 | rewrite F22 | rewrite F23
                | rewrite F24 | rewrite F25 | rewrite F26 | rewrite F27]; apply wa_u. }
      split.
      { intros k Hk. cbn [In] in Hk. destruct Hk as [<-|[<-|[]]].
        - rewrite (FK 3%nat ltac:(left; reflexivity)). exact C3.
        - rewrite (FK 4%nat ltac:(right; left; reflexivity)). rewrite C4. symmetry. regzH Q4. exact Q4. }
      split; [exact FINV|].
      split; [| exact (mem_grows_trans _ _ _ CG FG)].
      intros x Hx N1 N2 N3 N4 N5. rewrite FFR; [| exact Hx | exact N4 | exact N5].
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
Variables (m : word -> option byte) (regs : bvmap 5 word) (CA ND c SB SP sz0 st : Z).
Let RIv := SB + 137438953472 + 128 * c.
Let RBv := SB + 4294967296 * c.
Let FAv := SB + 4294967296 * c + 3758096384.
Hypothesis Hc : c = (ND + 31) / 32.
Hypothesis HND : 33 <= ND <= 512.
Hypothesis H2 : getr regs 2 = wa SP.
Hypothesis HSP : 2^46 + 4096 <= SP <= 2^47 /\ SP mod 16 = 0.
Hypothesis HSTK : stk_ok SEGS m (wa SP) 2048.
Hypothesis H10 : getr regs 10 = wa 923480.
Hypothesis H11 : getr regs 11 = wa CA.
Hypothesis H12 : getr regs 12 = wa ND.
Hypothesis H13 : getr regs 13 = wa 8.
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

#[using="ND sz0 st Hc HND H2 HSP HSTK H10 H11 H12 H13 HCA HSB HSEP Hvals Icnt Imc Isz Ist Iwc Iri Iwri ISB IRIB Irtoi Iprem Igot Ipsz Icf Idpm"] Lemma stageA : exists R1 mA, msteps SEGS (mkst regs (wa 0x43ce8) m rom) (mkst R1 (wa 0x73c44) mA rom) /\
  EC R1 RBv /\ getr R1 (Z_to_bv 5 (Z.of_nat 1)) = wa 481796 /\ getr R1 (Z_to_bv 5 (Z.of_nat 2)) = wa (SP - 400) /\
  getr R1 (Z_to_bv 5 (Z.of_nat 8)) = wa 262144 /\ getr R1 (Z_to_bv 5 (Z.of_nat 21)) = wa (32 * c) /\ getr R1 (Z_to_bv 5 (Z.of_nat 22)) = wa 923480 /\
  (forall k, In k [3; 4]%nat -> getr R1 (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))) /\
  MA_OK m mA regs SP CA c RIv RBv FAv /\
  (forall i, 1 <= i <= 31 -> rd mA (CA + 80 * i + 4) 4 (mc_tbl i) /\ rd mA (CA + 80 * i + 8) 8 (sz_tbl i)) /\
  (forall x, 0 <= x < 2^64 -> ~ (SP - 2048 <= x < SP) -> (forall i, 1 <= i <= 31 -> ~ (CA + 80 * i + 4 <= x < CA + 80 * i + 16)) ->
     ~ (RIv <= x < RIv + 8) -> mA (wa x) = m (wa x)).
Proof. LiaFast.lf_pins (fun (ND sz0 st Hc HND H2 HSP HSTK H10 H11 H12 H13 HCA HSB HSEP Hvals Icnt Imc Isz Ist Iwc Iri Iwri ISB IRIB Irtoi Iprem Igot Ipsz Icf Idpm : LiaFast.U) => LiaFast.u0).
  pose proof (c_of_nd_range ND HND) as Hcr5. rewrite <- Hc in Hcr5.
  assert (G : 2^46 <= SP <= 2^47 /\ 0 <= CA /\ CA + 4096 <= SP - 2048 /\ 0 <= RIv /\ RIv + 128 <= SP - 2048 /\ (CA + 4096 <= RIv \/ RIv + 128 <= CA))
    by (unfold RIv; clear - Hcr5 HSP HCA HSB HSEP; lia).
  destruct (segA rom m regs CA ND c SB SP sz0 st Hc HND H2 HSP HSTK H10 H11 H12 H13 HCA HSB HSEP Hvals Icnt Imc Isz Ist Iwc ISB IRIB Irtoi Iprem
              ltac:(pose proof (Iri 0 ltac:(lia)) as X; rewrite Z.add_0_r in X; exact X)
              ltac:(pose proof (Iri 2 ltac:(lia)) as X; exact X) ltac:(pose proof (Iri 4 ltac:(lia)) as X; exact X)
              ltac:(pose proof (Iri 6 ltac:(lia)) as X; exact X) ltac:(pose proof (Iri 7 ltac:(lia)) as X; exact X)
              Iwri Igot Ipsz Icf Idpm)
    as (R1 & mA & Hms & A1 & A2 & A8 & A10 & A11 & A12 & A13 & A14 & A15 & A17 & A21 & A22 & AK & EMA).
  exists R1, mA. split; [exact Hms|]. split; [unfold EC; repeat split; assumption|].
  split; [exact A1|]. split; [exact A2|]. split; [exact A8|]. split; [exact A21|]. split; [exact A22|]. split; [exact AK|].
  fold RIv RBv FAv in EMA. rewrite EMA. clear - G Hcr5.
  split; [|split].
  - unfold MA_OK. split; [|split; [|split; [|split; [|split; [|split]]]]].
    + intros k v Hk K1 K2. apply mAc_rd3; [lia | exact Hk | exact K1 | exact K2].
    + intros k v Hk K1 K2. apply mAc_rd2; [lia | lia | lia | exact Hk | exact K1 | exact K2].
    + intros k v Hk K1 K2. apply mAc_rd1; [lia | lia | lia | lia | lia | exact Hk | exact K1 | exact K2].
    + intros x Hx Q1 Q2 Q3. apply mAc_frame_f; [lia | lia | lia | lia | lia | exact Hx | exact Q1 | exact Q2 | exact Q3].
    + apply mAc_rdRI; lia.
    + apply mAc_rd_ic; [lia | lia | lia | lia | lia | tauto | lia].
    + apply mAc_grows.
  - intros i Hi. apply mAc_rd_ic; [lia | lia | lia | lia | lia | tauto | exact Hi].
  - intros x Hx Q1 Q2 Q3. apply mAc_frame_f; [lia | lia | lia | lia | lia | exact Hx | exact Q1 | exact Q2 | exact Q3].
Qed.
End VA.

(* [comment removed for export] *)
Lemma mAd_grows : forall m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 g21 g22 g23 g24 g25 g26 g27,
  mem_grows m (mAd m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 g21 g22 g23 g24 g25 g26 g27).
Proof.
  intros. unfold mAd.
  apply (mem_grows_trans _ _ _ (wchainS_grows (L1a c CA v1 v8 v9 v18 v19 v20) m SP)).
  apply (mem_grows_trans _ _ _ (wchainS_grows (L2a c CA n g21 g22 g23 g24 g25 g26 g27) _ SP)).
  apply (mem_grows_trans _ (wbytes (wchainS (wchainS m SP (L1a c CA v1 v8 v9 v18 v19 v20)) SP (L2a c CA n g21 g22 g23 g24 g25 g26 g27)) (wa RI) (word_to_le_bytes 8 (wa 1152921504606846976)))).
  - apply grows_wb. apply mem_grows_refl.
  - apply wchainS_grows.
Qed.
Lemma mAd_rd3 : forall m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 g21 g22 g23 g24 g25 g26 g27 k v,
  2^46 <= SP <= 2^47 -> wl_chk (L3a c CA n RI RB FA) k 8 = Some v -> -2048 <= k -> k + 8 <= 0 ->
  rd (mAd m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 g21 g22 g23 g24 g25 g26 g27) (SP + k) 8 v.
Proof. intros. unfold mAd. apply rd_wchainS; [lia | lia | reflexivity | lia | cbn; lia | lia | assumption]. Qed.
Lemma mAd_rd2 : forall m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 g21 g22 g23 g24 g25 g26 g27 k v,
  2^46 <= SP <= 2^47 -> 0 <= RI -> RI + 128 <= SP - 2048 -> wl_chk (L2a c CA n g21 g22 g23 g24 g25 g26 g27) k 8 = Some v -> -208 <= k -> k + 8 <= 0 ->
  rd (mAd m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 g21 g22 g23 g24 g25 g26 g27) (SP + k) 8 v.
Proof.
  intros m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 g21 g22 g23 g24 g25 g26 g27 k v HSP H1 H2 Hc Hk1 Hk2. unfold mAd.
  apply (rd_frame (wchainS (wchainS m SP (L1a c CA v1 v8 v9 v18 v19 v20)) SP (L2a c CA n g21 g22 g23 g24 g25 g26 g27))); [lia | cbn; lia | |].
  - intros x Hx. cbn in Hx.
    rewrite (wchainS_frame_in (L3a c CA n RI RB FA) _ SP (-2048) (-208)); [| lia | lia | reflexivity | reflexivity | lia | lia].
    apply wb_other; [lia | lia | rewrite length_N_to_le_bytes; lia | rewrite length_N_to_le_bytes; lia].
  - apply rd_wchainS; [lia | lia | reflexivity | lia | cbn; lia | lia | exact Hc].
Qed.
Lemma mAd_rd1 : forall m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 g21 g22 g23 g24 g25 g26 g27 k v,
  2^46 <= SP <= 2^47 -> 0 <= RI -> RI + 128 <= SP - 2048 ->
  wl_chk (L1a c CA v1 v8 v9 v18 v19 v20) k 8 = Some v -> -80 <= k -> k + 8 <= 0 ->
  rd (mAd m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 g21 g22 g23 g24 g25 g26 g27) (SP + k) 8 v.
Proof.
  intros m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 g21 g22 g23 g24 g25 g26 g27 k v HSP H1 H2 Hc Hk1 Hk2. unfold mAd.
  apply (rd_frame (wchainS m SP (L1a c CA v1 v8 v9 v18 v19 v20))); [lia | cbn; lia | |].
  - intros x Hx. cbn in Hx.
    rewrite (wchainS_frame_in (L3a c CA n RI RB FA) _ SP (-2048) (-208)); [| lia | lia | reflexivity | reflexivity | lia | lia].
    rewrite wb_other; [| lia | lia | rewrite length_N_to_le_bytes; lia | rewrite length_N_to_le_bytes; lia].
    apply (wchainS_frame_in (L2a c CA n g21 g22 g23 g24 g25 g26 g27) _ SP (-208) (-80)); [lia | lia | reflexivity | reflexivity | lia | lia].
  - apply rd_wchainS; [lia | lia | reflexivity | lia | cbn; lia | lia | exact Hc].
Qed.
Lemma mAd_frame_f : forall m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 g21 g22 g23 g24 g25 g26 g27 x,
  2^46 <= SP <= 2^47 -> 0 <= RI -> RI + 128 <= 2^63 -> 0 <= x < 2^64 -> ~ (SP - 2048 <= x < SP) -> ~ (RI <= x < RI + 8) ->
  mAd m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 g21 g22 g23 g24 g25 g26 g27 (wa x) = m (wa x).
Proof.
  intros m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 g21 g22 g23 g24 g25 g26 g27 x HSP H3 H4 Hx Q1 Q3. unfold mAd.
  rewrite (wchainS_frame_in (L3a c CA n RI RB FA) _ SP (-2048) 0); [| lia | lia | reflexivity | reflexivity | exact Hx | lia].
  rewrite wb_other; [| exact Hx | lia | rewrite length_N_to_le_bytes; lia | rewrite length_N_to_le_bytes; lia].
  rewrite (wchainS_frame_in (L2a c CA n g21 g22 g23 g24 g25 g26 g27) _ SP (-2048) 0); [| lia | lia | reflexivity | reflexivity | exact Hx | lia].
  rewrite (wchainS_frame_in (L1a c CA v1 v8 v9 v18 v19 v20) _ SP (-2048) 0); [| lia | lia | reflexivity | reflexivity | exact Hx | lia].
  reflexivity.
Qed.
Lemma mAd_rdRI : forall m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 g21 g22 g23 g24 g25 g26 g27,
  2^46 <= SP <= 2^47 -> 0 <= RI -> RI + 128 <= SP - 2048 ->
  rd (mAd m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 g21 g22 g23 g24 g25 g26 g27) RI 8 1152921504606846976.
Proof.
  intros. unfold mAd.
  apply (rd_frame (wbytes (wchainS (wchainS m SP (L1a c CA v1 v8 v9 v18 v19 v20)) SP (L2a c CA n g21 g22 g23 g24 g25 g26 g27)) (wa RI) (word_to_le_bytes 8 (wa 1152921504606846976)))); [lia | cbn; lia | |].
  - intros x Hx. cbn in Hx. apply (wchainS_frame_in (L3a c CA n RI RB FA) _ SP (-2048) 0); [lia | lia | reflexivity | reflexivity | lia | lia].
  - apply wb_rd_hit; [lia | lia | cbn; lia].
Qed.

Section VB.
Context {fx : FPState}.
Variable rom : word -> option byte.
Variables (m : word -> option byte) (regs : bvmap 5 word) (CA ND c SB SP st : Z).
Let RIv := SB + 137438953472 + 128 * c.
Let RBv := SB + 4294967296 * c.
Let FAv := SB + 4294967296 * c + 3758096384.
Hypothesis Hc : c = (ND + 31) / 32.
Hypothesis HND : 33 <= ND <= 512.
Hypothesis H2 : getr regs 2 = wa SP.
Hypothesis HSP : 2^46 + 4096 <= SP <= 2^47 /\ SP mod 16 = 0.
Hypothesis HSTK : stk_ok SEGS m (wa SP) 2048.
Hypothesis H10 : getr regs 10 = wa 923480.
Hypothesis H11 : getr regs 11 = wa CA.
Hypothesis H12 : getr regs 12 = wa ND.
Hypothesis H13 : getr regs 13 = wa 8.
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

#[using="ND st Hc HND H2 HSP HSTK H10 H11 H12 H13 HCA HSB HSEP Hvals Icnt Imc Isz Ist Iwc Iri Iwri ISB IRIB Irtoi Iprem Igot Ipsz Icf Idpm"] Lemma stageA' : exists R1 mA, msteps SEGS (mkst regs (wa 0x43ce8) m rom) (mkst R1 (wa 0x73c44) mA rom) /\
  EC R1 RBv /\ getr R1 (Z_to_bv 5 (Z.of_nat 1)) = wa 481796 /\ getr R1 (Z_to_bv 5 (Z.of_nat 2)) = wa (SP - 400) /\
  getr R1 (Z_to_bv 5 (Z.of_nat 8)) = wa 262144 /\ getr R1 (Z_to_bv 5 (Z.of_nat 21)) = wa (32 * c) /\ getr R1 (Z_to_bv 5 (Z.of_nat 22)) = wa 923480 /\
  (forall k, In k [3; 4]%nat -> getr R1 (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))) /\
  MA_OK m mA regs SP CA c RIv RBv FAv /\
  (forall x, 0 <= x < 2^64 -> ~ (SP - 2048 <= x < SP) -> ~ (RIv <= x < RIv + 8) -> mA (wa x) = m (wa x)).
Proof. LiaFast.lf_pins (fun (ND st Hc HND H2 HSP HSTK H10 H11 H12 H13 HCA HSB HSEP Hvals Icnt Imc Isz Ist Iwc Iri Iwri ISB IRIB Irtoi Iprem Igot Ipsz Icf Idpm : LiaFast.U) => LiaFast.u0).
  pose proof (c_of_nd_range ND HND) as Hcr5. rewrite <- Hc in Hcr5.
  assert (G : 2^46 <= SP <= 2^47 /\ 0 <= CA /\ CA + 4096 <= SP - 2048 /\ 0 <= RIv /\ RIv + 128 <= SP - 2048 /\ (CA + 4096 <= RIv \/ RIv + 128 <= CA))
    by (unfold RIv; clear - Hcr5 HSP HCA HSB HSEP; lia).
  assert (Hsz : 0 <= sz_tbl c < 2^64) by (rewrite (sz_tbl_small c Hcr5); clear - Hcr5; lia).
  destruct (segA' rom m regs CA ND c SB SP (sz_tbl c) st Hc HND H2 HSP HSTK H10 H11 H12 H13 HCA HSB HSEP (conj Hsz Hvals) Icnt Imc Isz Ist Iwc ISB IRIB Irtoi Iprem
              ltac:(pose proof (Iri 0 ltac:(lia)) as X; rewrite Z.add_0_r in X; exact X)
              ltac:(pose proof (Iri 2 ltac:(lia)) as X; exact X) ltac:(pose proof (Iri 4 ltac:(lia)) as X; exact X)
              ltac:(pose proof (Iri 6 ltac:(lia)) as X; exact X) ltac:(pose proof (Iri 7 ltac:(lia)) as X; exact X)
              Iwri Igot Ipsz Icf Idpm)
    as (R1 & mA & Hms & A1 & A2 & A8 & A10 & A11 & A12 & A13 & A14 & A15 & A17 & A21 & A22 & AK & EMA).
  exists R1, mA. split; [exact Hms|]. split; [unfold EC; repeat split; assumption|].
  split; [exact A1|]. split; [exact A2|]. split; [exact A8|]. split; [exact A21|]. split; [exact A22|]. split; [exact AK|].
  fold RIv RBv FAv in EMA. rewrite EMA.
  assert (FRd : forall x, 0 <= x < 2^64 -> ~ (SP - 2048 <= x < SP) -> ~ (RIv <= x < RIv + 8) ->
            mAd m SP CA c (mc_tbl c / 2) RIv RBv FAv
              (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 1)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 8)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 9))))
              (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 19)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 20))))
              (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 21)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 22)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 23))))
              (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 24)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 25)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 26))))
              (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 27)))) (wa x) = m (wa x)).
  { intros x Hx Q1 Q3. apply mAd_frame_f; [clear - G; lia | clear - G; lia | clear - G; lia | exact Hx | exact Q1 | exact Q3]. }
  split; [|exact FRd].
  unfold MA_OK. split; [|split; [|split; [|split; [|split; [|split]]]]].
  - intros k v Hk K1 K2. apply mAd_rd3; [clear - G; lia | exact Hk | exact K1 | exact K2].
  - intros k v Hk K1 K2. apply mAd_rd2; [clear - G; lia | clear - G; lia | clear - G; lia | exact Hk | exact K1 | exact K2].
  - intros k v Hk K1 K2. apply mAd_rd1; [clear - G; lia | clear - G; lia | clear - G; lia | exact Hk | exact K1 | exact K2].
  - intros x Hx Q1 _ Q3. exact (FRd x Hx Q1 Q3).
  - apply mAd_rdRI; clear - G; lia.
  - split.
    + apply (rd_frame m); [clear - G Hcr5; lia | cbn; clear - G Hcr5; lia | | exact Imc].
      intros x Hx. cbn in Hx. apply FRd; [clear - G Hcr5 Hx; lia | clear - G Hcr5 Hx; lia | clear - G Hcr5 Hx; lia].
    + apply (rd_frame m); [clear - G Hcr5; lia | cbn; clear - G Hcr5; lia | | exact Isz].
      intros x Hx. cbn in Hx. apply FRd; [clear - G Hcr5 Hx; lia | clear - G Hcr5 Hx; lia | clear - G Hcr5 Hx; lia].
  - apply mAd_grows.
Qed.
End VB.
