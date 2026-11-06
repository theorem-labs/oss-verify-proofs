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
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_nf2.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_np2.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_np2.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AxAsan OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_put OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_put2 OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_np OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_np2 OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_np3 OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_np4 OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_nf1 OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_nf2.AXG_nfsc OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_nf2 OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_np2.AXG_ms2 OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_np2.AXG_msc3.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_np3.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_nf2.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_np3.AXG_npscp OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_nf2.AXG_nfscp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_nf2.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_nf2.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXF_pc1a AXF_pc1az.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXF_pc1az.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXF_pc1az.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_nf2.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_nf2.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require Import AXG_gp AXG_gf1.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_gp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_gp.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Abbreviation SEGS := AsanUbsan.M.loaded_segments.
Ltac zlh H := clear - H; lia.
Ltac memb' := first [ AxSymRun3.memb_refl | repeat first [left; reflexivity | right] ].      (* [comment removed for export] *)
Ltac lenq' := rewrite ?length_N_to_le_bytes; try change (Z.of_nat 4) with 4 in *; try change (Z.of_nat 8) with 8 in *; try change (Z.of_nat 1) with 1 in *.


Section GSC1.
Context {fx : FPState}.
Variable rom : word -> option byte.
Variables (mC : word -> option byte) (R : bvmap 5 word) (c SB SP TP K TSDA PT T mm1 mm2 : Z).
Hypothesis Hc : 1 <= c <= 30.
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
Hypothesis R1 : getr R 1 = wa 481784.
Hypothesis R2 : getr R 2 = wa (SP - 448).
Hypothesis R4 : getr R 4 = wa TP.
Hypothesis R8 : getr R 8 = wa 262144.
Hypothesis R10 : getr R 10 = wa (SB + 4294967296 * c + 3758096384).
Hypothesis R21 : getr R 21 = wa (sz_tbl c).
Hypothesis R22 : getr R 22 = wa 929816.
Hypothesis HSTK : stk_ok SEGS mC (wa SP) 2048.
Hypothesis S88 : rd mC (SP - 448 + 88) 8 514992.
Hypothesis S80 : rd mC (SP - 448 + 80) 8 262144.
Hypothesis S72 : rd mC (SP - 448 + 72) 8 (SB + 4294967296 * c + 3758096384).
Hypothesis S64 : rd mC (SP - 448 + 64) 8 262144.
Hypothesis S56 : rd mC (SP - 448 + 56) 8 (SB + 137438953472 + 128 * c).
Hypothesis S48 : rd mC (SP - 448 + 48) 8 262144.
Hypothesis M24 : rd mC (SP - 352 + 24) 8 272576.
Hypothesis M16 : rd mC (SP - 352 + 16) 8 262144.
Hypothesis M8 : rd mC (SP - 352 + 8) 8 (SB + 4294967296 * c + 3758096384).
Hypothesis M0 : rd mC (SP - 352 + 0) 8 262144.
Hypothesis E40 : rd mC (SP - 280) 8 281840.
Hypothesis E32 : rd mC (SP - 288) 8 (SB + 137438953472 + 128 * c).
Hypothesis E24 : rd mC (SP - 296) 8 (262144 / (sz_tbl c)).
Hypothesis E16 : rd mC (SP - 304) 8 (SB + 4294967296 * c).
Hypothesis E8 : rd mC (SP - 312) 8 (262144 / (sz_tbl c)).
Hypothesis Icf : rd mC 910464 8 1540520.
Hypothesis Icf144 : rd mC (1540520 + 144) 8 0.
Hypothesis Ips1 : rd mC 941788 1 1.
Hypothesis Ips2 : rd mC 910480 8 943736.
Hypothesis Ips3 : rd mC 943736 8 2147450880.
Hypothesis Ips4 : rd mC 910488 8 947048.
Hypothesis Ips5 : rd mC 947048 8 0.
Hypothesis Ips6 : rd mC 910496 8 947056.
Hypothesis Ips7 : rd mC 947056 8 0.
Hypothesis Ips8 : rd mC 910504 8 947040.
Hypothesis Ips9 : rd mC 947040 8 140737488355327.
Hypothesis Ips10 : rd mC 910512 8 918480.
Hypothesis Ips11 : rd mC 918480 8 870660.
Hypothesis Itls1 : rd mC 941792 1 1.
Hypothesis Itls2 : rd mC 941796 4 K.
Hypothesis Itls3 : rd mC (TP - 88) 8 TSDA.
Hypothesis Itls4 : rd mC (TSDA + 8 * K) 8 PT.
Hypothesis Itls5 : rd mC (PT + 152) 8 T.
Hypothesis Imm1 : rd mC (T + 2872) 8 mm1.
Hypothesis Imm2 : rd mC (T + 2880) 8 mm2.
Hypothesis Iwt : wr mC (T + 2872) 16.
Hypothesis Iau : rd mC (SB + 137438953472 + 128 * c + 32) 8 0.
Hypothesis Iwri : wr mC (SB + 137438953472 + 128 * c) 128.
Hypothesis Iwsh : wr mC (Z.shiftr (SB + 4294967296 * c + 3758096384) 3 + 2147450880) 32768.

#[using="K TSDA PT Hc HSP HO HSB HK HSHs Hst R1 R2 R4 R8 R10 R21 R22 HSTK S88 S80 S72 S64 S56 S48 M24 M16 M8 M0 E40 E32 E24 E16 E8 Icf Icf144 Ips1 Ips2 Ips3 Ips4 Ips5 Ips6 Ips7 Ips8 Ips9 Ips10 Ips11 Itls1 Itls2 Itls3 Itls4 Itls5 Imm1 Imm2 Iwt Iau Iwri Iwsh"] Lemma gsegC1 : exists R' m', msteps SEGS (mkst R (wa 0x73c3c) mC rom) (mkst R' (wa 0x44d18) m' rom) /\
  getr R' (Z_to_bv 5 (Z.of_nat 2)) = wa (SP - 272) /\ getr R' (Z_to_bv 5 (Z.of_nat 4)) = wa TP /\
  getr R' (Z_to_bv 5 (Z.of_nat 8)) = wa (SB + 137438953472 + 128 * c) /\ getr R' (Z_to_bv 5 (Z.of_nat 10)) = wa 0 /\
  getr R' (Z_to_bv 5 (Z.of_nat 11)) = wa (SB + 4294967296 * c + 3758096384 + 4 * (262144 / (sz_tbl c))) /\
  getr R' (Z_to_bv 5 (Z.of_nat 12)) = wa 0 /\ getr R' (Z_to_bv 5 (Z.of_nat 13)) = wa 0 /\
  getr R' (Z_to_bv 5 (Z.of_nat 18)) = wa (SB + 4294967296 * c) /\ getr R' (Z_to_bv 5 (Z.of_nat 19)) = wa (262144 / (sz_tbl c)) /\
  getr R' (Z_to_bv 5 (Z.of_nat 21)) = wa (sz_tbl c) /\ getr R' (Z_to_bv 5 (Z.of_nat 22)) = wa 929816 /\
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
  pose proof (gnew_rng c Hc) as HNEW.
  destruct (gsz_rng c Hc) as (Hsz1 & Hsz2 & _).
  assert (HS16 : 16 * (sz_tbl c / 16) = sz_tbl c) by (clear - Hsz2; pose proof (Z.div_mod (sz_tbl c) 16 ltac:(lia)); lia).
  assert (HS16r : 2 <= sz_tbl c / 16 <= 4096) by (clear - Hsz1 HS16; lia).
  set (NEW := 262144 / (sz_tbl c)) in *.
  assert (HZ : 2^46 + 4096 <= SP <= 2^47 /\ 1 <= c <= 30 /\ 17594333495296 <= SB /\ SB mod 4096 = 0 /\
               SB + 137438953472 + 4096 <= SP - 2048 /\ RB = SB + 4294967296 * c /\ RI = SB + 137438953472 + 128 * c /\ FA = RB + 3758096384 /\
               SH = FA / 8 + 2147450880 /\
               ((4096 <= T /\ T + 4096 <= 65536) \/ 6537216 <= T) /\ T + 4096 <= SP - 2048 - 256 /\ 4096 <= TP /\ TP <= SP - 2048 - 256 /\
               1 <= TSDA /\ TSDA + 8192 <= SP - 2048 - 256 /\ 1 <= PT /\ PT + 160 <= SP - 2048 - 256 /\ 0 <= K <= 1023 /\
               0 <= mm1 < 2^64 /\ 0 <= mm2 < 2^64 /\ 4 <= NEW <= 8192 /\ 32 <= sz_tbl c <= 65536) by (clear - Hc HSP HO HSB HK Hst HSH HNEW Hsz1; unfold FA, RB, RI, NEW in *; lia).
  assert (HD1 : RI + 128 <= T \/ T + 4096 <= RI) by (clear - HO; unfold RI; tauto).
  assert (HD2 : T + 4096 <= SH \/ SH + 32768 <= T) by (clear - HSHs; tauto).
  assert (HD3 : RI + 128 <= SH \/ SH + 32768 <= RI) by (clear - HSHs; tauto).
  assert (HD4 : TP <= SH \/ SH + 32768 <= TP - 88) by (clear - HSHs; tauto).
  assert (HD5 : TSDA + 8192 <= SH \/ SH + 32768 <= TSDA) by (clear - HSHs; tauto).
  assert (HD6 : PT + 160 <= SH \/ SH + 32768 <= PT) by (clear - HSHs; tauto).
  clear HSP HO HSB HK Hst HSHs HSH.
  assert (HSPa : bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 2))) = SP - 448) by (rgz; rewrite R2, u_wa_small by (zlh HZ); reflexivity).
  (* [comment removed for export] *)
  assert (P1 : OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_nf2.AXF_mf1z.mf1_pre R mC FA 262144 1540520 514992 262144 FA 262144 RI 262144).
  { constructor; [exact R1 | exact R8 | exact R10
                 | (rewrite R2; apply (stk_ok_move mC SP (SP - 448) 1024); [(zlh HZ) | (zlh HZ) | exact HSTK | (zlh HZ) | (zlh HZ) | (zlh HZ)])
                 | (zlh HZ) | (zlh HZ) | (zlh HZ) | (zlh HZ) | (zlh HZ) | (zlh HZ) | (zlh HZ) | (zlh HZ) | (zlh HZ) | (zlh HZ) | rewrite HSPa; (zlh HZ) | | | | | | | | | ].
    all: try (rewrite HSPa; assumption).
    - intros d k Hd Hk. rewrite HSPa. apply HSTK; rewrite !u_wa_small; clear - HZ Hd Hk; lia.
    - exact Icf.
    - exact Icf144. }
  destruct (OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_nf2.AXF_mf1z.mf1_pmf1 R mC rom FA 262144 1540520 514992 262144 FA 262144 RI 262144 P1
              (sc_mf1 R mC (SP - 448) FA 262144 1540520 514992 262144 FA 262144 RI 262144 HSPa ltac:((zlh HZ))))
    as (Ra & Hms & A1 & A2 & A8 & A9 & A10 & A11 & A12 & A13 & A18 & A19 & A20 & KKa).
  clear P1 A11 A12 A13.
  set (m1 := OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_nf2.AXF_mf1z.mf1_mem_pmf1 mC R FA 262144 1540520 514992 262144 FA 262144 RI 262144) in *.
  assert (EM1 : m1 = wchainS mC SP [(-404, 4%nat, 18446744072277895850)]) by (unfold m1, OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_nf2.AXF_mf1z.mf1_mem_pmf1; rewrite HSPa, sub_add_lit; reflexivity).
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
  assert (V21 : bv_unsigned (getr Ra (Z_to_bv 5 (Z.of_nat 21))) = sz_tbl c) by (rewrite (KKa 21%nat ltac:(cbn; memb')); regzH R21; rewrite R21, u_wa_small by (zlh HZ); reflexivity).
  assert (EM2 : m2 = wchainS m1 SP [(-376, 8%nat, sz_tbl c); (-368, 8%nat, 262144); (-360, 8%nat, RI); (-352, 8%nat, 262144); (-344, 8%nat, FA); (-336, 8%nat, 262144); (-328, 8%nat, 272604)]).
  { unfold m2, AXF_pc1az.pc1a_mem_ppc1a. rewrite HSPb, A19, A20, V21, ?u_wa_small by (zlh HZ). rewrite ?sub_add_lit. reflexivity. }
  clearbody m2.
  assert (G2 : mem_grows mC m2) by (rewrite EM2; exact (mem_grows_trans _ _ _ G1 (wchainS_grows _ m1 SP))).
  assert (F2 : forall x, 0 <= x < 2^64 -> ~ (SP - 2048 <= x < SP - 320) -> m2 (wa x) = mC (wa x)).
  { intros x Hx Q. rewrite EM2. rewrite (wchainS_frame_in [(-376, 8%nat, sz_tbl c); (-368, 8%nat, 262144); (-360, 8%nat, RI); (-352, 8%nat, 262144); (-344, 8%nat, FA); (-336, 8%nat, 262144); (-328, 8%nat, 272604)] m1 SP (-376) (-320));
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
  assert (P4 : OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXF_pc1az.AXF_rt2z.rt2_pre Rc m3 0) by (constructor; [regzG; rewrite (KKc 1%nat ltac:(cbn; memb')); exact B1 | lia]).
  destruct (OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXF_pc1az.AXF_rt2z.rt2_prt2 Rc m3 rom 0 P4 ltac:(cbn [OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXF_pc1az.AXF_rt2.RES_prt2 fst snd]; constructor)) as (Rd & Hms4 & C1 & KKd).
  assert (Em4 : OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXF_pc1az.AXF_rt2z.rt2_mem_prt2 m3 Rc 0 = m3) by reflexivity. rewrite Em4 in Hms4. clear Em4 P4.
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
  assert (P5 : OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp.AXF_gpc1bz.gpc1b_pre Rd m3 RI RB (sz_tbl c / 16) NEW TP K TSDA PT T mm1 mm2).
  { constructor; [regzG; rewrite (KR 4%nat ltac:(cbn; memb')), (KRb 4%nat ltac:(cbn; memb')), (KKa 4%nat ltac:(cbn; memb')); exact R4
                 | regzG; rewrite (KR 8%nat ltac:(cbn; memb')); exact B8
                 | regzG; rewrite (KR 9%nat ltac:(cbn; memb')); exact B9
                 | regzG; rewrite (KR 18%nat ltac:(cbn; memb')); exact B18
                 | regzG; rewrite (KR 19%nat ltac:(cbn; memb')), (KRb 19%nat ltac:(cbn; memb')); exact A19
                 | regzG; rewrite (KR 20%nat ltac:(cbn; memb')), (KRb 20%nat ltac:(cbn; memb')); exact A20
                 | regzG; rewrite (KR 21%nat ltac:(cbn; memb')), (KRb 21%nat ltac:(cbn; memb')), (KKa 21%nat ltac:(cbn; memb')); rewrite HS16; exact R21
                 | regzG; rewrite (KR 22%nat ltac:(cbn; memb')), (KRb 22%nat ltac:(cbn; memb')), (KKa 22%nat ltac:(cbn; memb')); exact R22
                 | (replace (getr Rd 2) with (wa (SP - 320)) by (regzG; rewrite (KR 2%nat ltac:(cbn; memb')), B2, HSPb; f_equal; ring);
                    apply (stk_ok_move m3 SP (SP - 320) 1024); [(zlh HZ) | (zlh HZ) | exact (stk_ok_grows mC m3 (wa SP) 2048 (mem_grows_trans _ _ _ G2 G3) HSTK) | (zlh HZ) | (zlh HZ) | (zlh HZ)])
                 | .. ].
    all: try (zlh HZ).
    all: try (zlh HS16r).
    all: try (rewrite HSPd; (zlh HZ)).
    all: try (rewrite hko by (zlh HZ); rewrite Z.add_0_r).
    all: try (rewrite HSPd; replace (SP - 320 + 40) with (SP - 280) by ring; replace (SP - 320 + 32) with (SP - 288) by ring;
              replace (SP - 320 + 24) with (SP - 296) by ring; replace (SP - 320 + 16) with (SP - 304) by ring; replace (SP - 320 + 8) with (SP - 312) by ring).
    all: first [ (apply (rd_frame mC m3); [(zlh HZ) | lenq'; (zlh HZ) | intros x Hx; lenq'; apply F3; [clear - HZ Hx; lia | clear - HZ Hx; lia | first [clear - HZ Hx; lia | clear - HZ HD2 Hx; lia | clear - HZ HD3 Hx; lia | clear - HZ HD4 Hx; lia | clear - HZ HD5 Hx; lia | clear - HZ HD6 Hx; lia]] | assumption])
               | (intros d k Hd Hk; apply (store_ok_mono SEGS k mC m3 _ (mem_grows_trans _ _ _ G2 G3));
                  first [ (replace (T + 2872 + d) with (T + 2872 + (0 + d)) by ring; apply Iwt; clear - Hd Hk; lia)
                        | (replace (T + 2880 + d) with (T + 2872 + (8 + d)) by ring; apply Iwt; clear - Hd Hk; lia)
                        | (replace (RI + 24 + d) with (RI + (24 + d)) by ring; apply Iwri; clear - Hd Hk; lia) ]) ]. }
  destruct (OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp.AXF_gpc1bz.gpc1b_ppc1b Rd m3 rom RI RB (sz_tbl c / 16) NEW TP K TSDA PT T mm1 mm2 P5
              (sc_gpc1b Rd m3 (SP - 320) HSPd RI RB (sz_tbl c / 16) NEW TP K TSDA PT T mm1 mm2 ltac:(unfold objs_ok; clear - HZ HD1; lia) ltac:((zlh HZ)) HS16r ltac:((zlh HZ))))
    as (Re & Hms5 & D1 & D2 & D4 & D8 & D9 & D10 & D11 & D12 & D13 & D18 & D19 & D20 & D21 & D22 & KKe).
  clear P5.
  pose proof (msteps_trans SEGS _ _ _ Hms Hms5) as Hms'. clear Hms Hms5. rename Hms' into Hms.
  set (m4 := OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp.AXF_gpc1bz.gpc1b_mem_ppc1b m3 Rd RI RB (sz_tbl c / 16) NEW TP K TSDA PT T mm1 mm2) in *.
  assert (EM4 : m4 = wbytes (wbytes (wbytes (wchainS m3 SP [(-344, 8%nat, 436880); (-328, 8%nat, 272608)])
                        (wa (T + 2872)) (word_to_le_bytes 8 (wa (mm1 + 1)))) (wa (T + 2880)) (word_to_le_bytes 8 (wa (mm2 + 262144))))
                        (wa (RI + 24)) (word_to_le_bytes 8 (wa 262144))).
  { unfold m4, OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp.AXF_gpc1bz.gpc1b_mem_ppc1b. rewrite HSPd, ?sub_add_lit. reflexivity. }
  clearbody m4.
  assert (G4 : mem_grows mC m4).
  { apply (mem_grows_trans _ m3 _ (mem_grows_trans _ _ _ G2 G3)). rewrite EM4.
    repeat apply grows_wb. first [apply wchainS_grows | apply mem_grows_refl]. }
  assert (F4 : forall x, 0 <= x < 2^64 -> ~ (SP - 2048 <= x < SP - 320) -> ~ (SH <= x < SH + 32768) -> ~ (RI + 24 <= x < RI + 32) ->
                 ~ (T + 2872 <= x < T + 2888) -> m4 (wa x) = mC (wa x)).
  { intros x Hx Q1 Q2 Q3 Q5. rewrite EM4.
    repeat (rewrite wb_other by first [exact Hx | (lenq'; clear - HZ; lia) | (lenq'; clear - HZ Q3 Q5; lia)]).
    rewrite (wchainS_frame_in [(-344, 8%nat, 436880); (-328, 8%nat, 272608)] _ SP (-344) (-320));
      [| clear - HZ; lia | clear - HZ; lia | reflexivity | reflexivity | exact Hx | clear - HZ Q1; lia].
    apply F3; assumption. }
  regzH D2. regzH D4. regzH D8. regzH D10. regzH D11. regzH D12. regzH D13. regzH D18. regzH D19. regzH D21. regzH D22. rewrite HS16 in D21.
  exists Re, m4. split; [exact Hms|].
  split; [rewrite D2, HSPd; f_equal; ring|]. split; [exact D4|]. split; [exact D8|]. split; [exact D10|].
  split; [rewrite D11; f_equal; unfold FA; ring|]. split; [exact D12|]. split; [exact D13|]. split; [exact D18|]. split; [exact D19|].
  split; [exact D21|]. split; [exact D22|].
  split; [rewrite (KKe 3%nat ltac:(cbn; memb')), (KKd 3%nat ltac:(cbn; memb')), (KKc 3%nat ltac:(cbn; memb')), (KKb 3%nat ltac:(cbn; memb')), (KKa 3%nat ltac:(cbn; memb')); reflexivity|].
  split.
  { intros x Hx. rewrite EM4.
    repeat (rewrite wb_other by first [(clear - HZ Hx; lia) | (lenq'; clear - HZ; lia) | (lenq'; clear - HZ HD2 HD3 Hx; lia)]).
    rewrite (wchainS_frame_in [(-344, 8%nat, 436880); (-328, 8%nat, 272608)] _ SP (-344) (-320));
      [| clear - HZ; lia | clear - HZ; lia | reflexivity | reflexivity | clear - HZ Hx; lia | clear - HZ Hx; lia].
    apply MS1. exact Hx. }
  split; [rewrite EM4; apply wb_rd_hit; lenq'; (zlh HZ)|].
  split.
  { rewrite EM4. apply (rd_frame (wbytes (wchainS m3 SP [(-344, 8%nat, 436880); (-328, 8%nat, 272608)]) (wa (T + 2872)) (word_to_le_bytes 8 (wa (mm1 + 1)))));
      [(zlh HZ) | cbn; (zlh HZ) | intros x Hx; cbn in Hx; repeat (rewrite wb_other by first [(clear - HZ Hx; lia) | (lenq'; clear - HZ; lia) | (lenq'; clear - HZ HD1 Hx; lia)]); reflexivity |].
    apply wb_rd_hit; lenq'; (zlh HZ). }
  split.
  { rewrite EM4. apply (rd_frame (wbytes (wbytes (wchainS m3 SP [(-344, 8%nat, 436880); (-328, 8%nat, 272608)]) (wa (T + 2872)) (word_to_le_bytes 8 (wa (mm1 + 1)))) (wa (T + 2880)) (word_to_le_bytes 8 (wa (mm2 + 262144)))));
      [(zlh HZ) | cbn; (zlh HZ) | intros x Hx; cbn in Hx; repeat (rewrite wb_other by first [(clear - HZ Hx; lia) | (lenq'; clear - HZ; lia) | (lenq'; clear - HZ HD1 Hx; lia)]); reflexivity |].
    apply wb_rd_hit; lenq'; (zlh HZ). }
  split; [exact F4 | exact G4].
Qed.
End GSC1.
(* [comment removed for export] *)
