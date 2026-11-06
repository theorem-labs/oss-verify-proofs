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
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXF_pb1 AXF_pb1z.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXF_pb1z.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXF_pb1z.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_nf2.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_nf2.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXF_mf0z.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXF_mf0z.
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

Lemma gdivu_lit : forall R V s, nth 3 V 0 = s -> 2 <= s <= 4096 ->
  bv_unsigned (edenot (Ez R V) (EMd M_DIVU (ELit 262144) (EMd M_MUL (ELit 16) (EVar 35)))) = 262144 / (16 * s).
Proof.
  intros R V s Hv Hr. cbn [edenot].
  assert (E0 : bv_unsigned (ev (Ez R V) 35) = s) by (apply zatom; [reflexivity | exact Hv | lia]).
  assert (E1 : bv_unsigned (mul_div M_MUL (Z_to_bv 64 16) (ev (Ez R V) 35)) = 16 * s).
  { unfold mul_div. rewrite bv_mul_unsigned, E0. change (bv_unsigned (Z_to_bv 64 16)) with 16. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^64). apply Z.mod_small. lia. }
  unfold mul_div at 1. rewrite E1, (proj2 (Z.eqb_neq (16 * s) 0)) by lia. rewrite bv_divu_unsigned, E1.
  change (bv_unsigned (Z_to_bv 64 262144)) with 262144. reflexivity.
Qed.

Section GSB3.
Context {fx : FPState}.
Variable rom : word -> option byte.
Variables (mB : word -> option byte) (R : bvmap 5 word) (CA c SB SP TP K TSDA PT T mm1 mm2 st2 : Z).
Hypothesis Hc : 1 <= c <= 30.
Hypothesis HSP : 2^46 + 4096 <= SP <= 2^47 /\ SP mod 16 = 0.
Hypothesis HCT : CA = T + 208.
Hypothesis HO : objs_ok_p (SP - 2048) T (SB + 137438953472 + 128 * c) TP TSDA PT.
Hypothesis HSB : 17594333495296 <= SB /\ SB mod 4096 = 0 /\ SB + 137438953472 + 4096 <= SP - 2048.
Hypothesis HK : 0 <= K <= 1023.
Hypothesis HCA16 : CA mod 16 = 0.
Hypothesis HSHs : (T + 4096 <= Z.shiftr (SB + 4294967296 * c) 3 + 2147450880 \/ Z.shiftr (SB + 4294967296 * c) 3 + 2147450880 + 32768 <= T) /\
                  (SB + 137438953472 + 128 * c + 128 <= Z.shiftr (SB + 4294967296 * c) 3 + 2147450880 \/ Z.shiftr (SB + 4294967296 * c) 3 + 2147450880 + 32768 <= SB + 137438953472 + 128 * c) /\
                  (TP <= Z.shiftr (SB + 4294967296 * c) 3 + 2147450880 \/ Z.shiftr (SB + 4294967296 * c) 3 + 2147450880 + 32768 <= TP - 88) /\
                  (TSDA + 8192 <= Z.shiftr (SB + 4294967296 * c) 3 + 2147450880 \/ Z.shiftr (SB + 4294967296 * c) 3 + 2147450880 + 32768 <= TSDA) /\
                  (PT + 160 <= Z.shiftr (SB + 4294967296 * c) 3 + 2147450880 \/ Z.shiftr (SB + 4294967296 * c) 3 + 2147450880 + 32768 <= PT).
Hypothesis Hst : 0 <= mm1 < 2^64 /\ 0 <= mm2 < 2^64 /\ 0 <= st2 < 2^64.
Hypothesis R1 : getr R 1 = wa 481784.
Hypothesis R2 : getr R 2 = wa (SP - 400).
Hypothesis R4 : getr R 4 = wa TP.
Hypothesis R8 : getr R 8 = wa 262144.
Hypothesis R10 : getr R 10 = wa (SB + 4294967296 * c).
Hypothesis R21 : getr R 21 = wa (sz_tbl c).
Hypothesis R22 : getr R 22 = wa 929816.
Hypothesis HSTK : stk_ok SEGS mB (wa SP) 2048.
Hypothesis S88 : rd mB (SP - 400 + 88) 8 514992.
Hypothesis S80 : rd mB (SP - 400 + 80) 8 262144.
Hypothesis S72 : rd mB (SP - 400 + 72) 8 (SB + 4294967296 * c).
Hypothesis S64 : rd mB (SP - 400 + 64) 8 (SB + 4294967296 * c).
Hypothesis S56 : rd mB (SP - 400 + 56) 8 262144.
Hypothesis S48 : rd mB (SP - 400 + 48) 8 (SB + 4294967296 * c).
Hypothesis M24 : rd mB (SP - 304 + 24) 8 281724.
Hypothesis M16 : rd mB (SP - 304 + 16) 8 (SB + 137438953472 + 128 * c).
Hypothesis M8 : rd mB (SP - 304 + 8) 8 (CA + 2560).
Hypothesis M0 : rd mB (SP - 304 + 0) 8 (SB + 4294967296 * c).
Hypothesis Icf : rd mB 910464 8 1540520.
Hypothesis Icf144 : rd mB (1540520 + 144) 8 0.
Hypothesis Icf260 : rd mB (1540520 + 260) 1 0.
Hypothesis Igot : rd mB 910448 8 1532192.
Hypothesis Ipsz : rd mB 1532192 8 4096.
Hypothesis Ips1 : rd mB 941788 1 1.
Hypothesis Ips2 : rd mB 910480 8 943736.
Hypothesis Ips3 : rd mB 943736 8 2147450880.
Hypothesis Ips4 : rd mB 910488 8 947048.
Hypothesis Ips5 : rd mB 947048 8 0.
Hypothesis Ips6 : rd mB 910496 8 947056.
Hypothesis Ips7 : rd mB 947056 8 0.
Hypothesis Ips8 : rd mB 910504 8 947040.
Hypothesis Ips9 : rd mB 947040 8 140737488355327.
Hypothesis Ips10 : rd mB 910512 8 918480.
Hypothesis Ips11 : rd mB 918480 8 870660.
Hypothesis Itls1 : rd mB 941792 1 1.
Hypothesis Itls2 : rd mB 941796 4 K.
Hypothesis Itls3 : rd mB (TP - 88) 8 TSDA.
Hypothesis Itls4 : rd mB (TSDA + 8 * K) 8 PT.
Hypothesis Itls5 : rd mB (PT + 152) 8 T.
Hypothesis Imm1 : rd mB (T + 2872) 8 mm1.
Hypothesis Imm2 : rd mB (T + 2880) 8 mm2.
Hypothesis Ist2 : rd mB (CA + 2584) 8 st2.
Hypothesis Iwt : wr mB (T + 2872) 16.
Hypothesis Iwst : wr mB (CA + 2584) 8.
Hypothesis Inf0 : rd mB (SB + 137438953472 + 128 * c + 16) 8 0.
Hypothesis Imfa : rd mB (SB + 137438953472 + 128 * c + 24) 8 0.
Hypothesis Iau : rd mB (SB + 137438953472 + 128 * c + 32) 8 0.
Hypothesis Imapu : rd mB (SB + 137438953472 + 128 * c + 48) 8 0.
Hypothesis Iwri : wr mB (SB + 137438953472 + 128 * c) 128.
Hypothesis Iprem : rd mB 929872 1 0.
Hypothesis Iwsh : wr mB (Z.shiftr (SB + 4294967296 * c) 3 + 2147450880) 32768.

#[using="K TSDA PT Hc HSP HCT HO HSB HK HCA16 HSHs Hst R1 R2 R4 R8 R10 R21 R22 HSTK S88 S80 S72 S64 S56 S48 M24 M16 M8 M0 Icf Icf144 Icf260 Igot Ipsz Ips1 Ips2 Ips3 Ips4 Ips5 Ips6 Ips7 Ips8 Ips9 Ips10 Ips11 Itls1 Itls2 Itls3 Itls4 Itls5 Imm1 Imm2 Ist2 Iwt Iwst Inf0 Imfa Iau Imapu Iwri Iprem Iwsh"] Lemma gsegB : exists R' mB', msteps SEGS (mkst R (wa 0x73c3c) mB rom) (mkst R' (wa 0x73c38) mB' rom) /\
  getr R' (Z_to_bv 5 (Z.of_nat 1)) = wa 481784 /\ getr R' (Z_to_bv 5 (Z.of_nat 2)) = wa (SP - 448) /\
  getr R' (Z_to_bv 5 (Z.of_nat 8)) = wa 262144 /\ getr R' (Z_to_bv 5 (Z.of_nat 10)) = wa (SB + 4294967296 * c + 3758096384) /\
  getr R' (Z_to_bv 5 (Z.of_nat 11)) = wa 262144 /\ getr R' (Z_to_bv 5 (Z.of_nat 12)) = wa 3 /\ getr R' (Z_to_bv 5 (Z.of_nat 13)) = wa 50 /\
  getr R' (Z_to_bv 5 (Z.of_nat 14)) = wa 18446744073709551615 /\ getr R' (Z_to_bv 5 (Z.of_nat 15)) = wa 0 /\
  getr R' (Z_to_bv 5 (Z.of_nat 17)) = wa 222 /\ getr R' (Z_to_bv 5 (Z.of_nat 21)) = wa (sz_tbl c) /\ getr R' (Z_to_bv 5 (Z.of_nat 22)) = wa 929816 /\
  getr R' (Z_to_bv 5 (Z.of_nat 4)) = wa TP /\ getr R' (Z_to_bv 5 (Z.of_nat 3)) = getr R (Z_to_bv 5 (Z.of_nat 3)) /\
  (forall x, Z.shiftr (SB + 4294967296 * c) 3 + 2147450880 <= x < Z.shiftr (SB + 4294967296 * c) 3 + 2147450880 + 32768 -> mB' (wa x) = Some (Z_to_bv 8 250)) /\
  rd mB' (SP - 448 + 88) 8 514992 /\ rd mB' (SP - 448 + 80) 8 262144 /\ rd mB' (SP - 448 + 72) 8 (SB + 4294967296 * c + 3758096384) /\
  rd mB' (SP - 448 + 64) 8 262144 /\ rd mB' (SP - 448 + 56) 8 (SB + 137438953472 + 128 * c) /\ rd mB' (SP - 448 + 48) 8 262144 /\
  rd mB' (SP - 352 + 24) 8 272576 /\ rd mB' (SP - 352 + 16) 8 262144 /\ rd mB' (SP - 352 + 8) 8 (SB + 4294967296 * c + 3758096384) /\
  rd mB' (SP - 352 + 0) 8 262144 /\
  rd mB' (SP - 280) 8 281840 /\ rd mB' (SP - 288) 8 (SB + 137438953472 + 128 * c) /\ rd mB' (SP - 296) 8 (262144 / (sz_tbl c)) /\
  rd mB' (SP - 304) 8 (SB + 4294967296 * c) /\ rd mB' (SP - 312) 8 (262144 / (sz_tbl c)) /\
  rd mB' (SB + 137438953472 + 128 * c + 48) 8 262144 /\
  rd mB' (T + 2872) 8 (mm1 + 1) /\ rd mB' (T + 2880) 8 (mm2 + 262144) /\ rd mB' (CA + 2584) 8 (st2 + 262144) /\
  (forall x, 0 <= x < 2^64 -> ~ (SP - 2048 <= x < SP - 272) -> ~ (Z.shiftr (SB + 4294967296 * c) 3 + 2147450880 <= x < Z.shiftr (SB + 4294967296 * c) 3 + 2147450880 + 32768) ->
     ~ (SB + 137438953472 + 128 * c + 48 <= x < SB + 137438953472 + 128 * c + 56) -> ~ (CA + 2584 <= x < CA + 2592) -> ~ (T + 2872 <= x < T + 2888) ->
     mB' (wa x) = mB (wa x)) /\ mem_grows mB mB'.
Proof. LiaFast.lf_pins (fun (K TSDA PT Hc HSP HCT HO HSB HK HCA16 HSHs Hst R1 R2 R4 R8 R10 R21 R22 HSTK S88 S80 S72 S64 S56 S48 M24 M16 M8 M0 Icf Icf144 Icf260 Igot Ipsz Ips1 Ips2 Ips3 Ips4 Ips5 Ips6 Ips7 Ips8 Ips9 Ips10 Ips11 Itls1 Itls2 Itls3 Itls4 Itls5 Imm1 Imm2 Ist2 Iwt Iwst Inf0 Imfa Iau Imapu Iwri Iprem Iwsh : LiaFast.U) => LiaFast.u0).
  set (RB := SB + 4294967296 * c) in *. set (RI := SB + 137438953472 + 128 * c) in *.
  set (SH := Z.shiftr RB 3 + 2147450880) in *.
  assert (HSH : SH = RB / 8 + 2147450880) by (unfold SH; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  unfold objs_ok_p, t_place in HO.
  pose proof (gnew_rng c Hc) as HNEW.
  destruct (gsz_rng c Hc) as (Hsz1 & Hsz2 & _).
  assert (HS16 : 16 * (sz_tbl c / 16) = sz_tbl c) by (clear - Hsz2; pose proof (Z.div_mod (sz_tbl c) 16 ltac:(lia)); lia).
  assert (HS16r : 2 <= sz_tbl c / 16 <= 4096) by (clear - Hsz1 HS16; lia).
  set (NEW := 262144 / (sz_tbl c)) in *.
  assert (HZ : 2^46 + 4096 <= SP <= 2^47 /\ 1 <= c <= 30 /\ CA = T + 208 /\ CA mod 16 = 0 /\ 17594333495296 <= SB /\ SB mod 4096 = 0 /\
               SB + 137438953472 + 4096 <= SP - 2048 /\ RB = SB + 4294967296 * c /\ RI = SB + 137438953472 + 128 * c /\ SH = RB / 8 + 2147450880 /\
               ((4096 <= T /\ T + 4096 <= 65536) \/ 6537216 <= T) /\ T + 4096 <= SP - 2048 - 256 /\ 4096 <= TP /\ TP <= SP - 2048 - 256 /\
               1 <= TSDA /\ TSDA + 8192 <= SP - 2048 - 256 /\ 1 <= PT /\ PT + 160 <= SP - 2048 - 256 /\ 0 <= K <= 1023 /\
               0 <= mm1 < 2^64 /\ 0 <= mm2 < 2^64 /\ 0 <= st2 < 2^64 /\ 4 <= NEW <= 8192 /\ 32 <= sz_tbl c <= 65536) by (clear - Hc HSP HCT HO HSB HK Hst HCA16 HSH HNEW Hsz1; unfold RB, RI, NEW in *; lia).
  assert (HD1 : RI + 128 <= T \/ T + 4096 <= RI) by (clear - HO; unfold RI; tauto).
  assert (HD2 : T + 4096 <= SH \/ SH + 32768 <= T) by (clear - HSHs; unfold SH, RB in *; tauto).
  assert (HD3 : RI + 128 <= SH \/ SH + 32768 <= RI) by (clear - HSHs; unfold SH, RB, RI in *; tauto).
  assert (HD4 : TP <= SH \/ SH + 32768 <= TP - 88) by (clear - HSHs; unfold SH, RB in *; tauto).
  assert (HD5 : TSDA + 8192 <= SH \/ SH + 32768 <= TSDA) by (clear - HSHs; unfold SH, RB in *; tauto).
  assert (HD6 : PT + 160 <= SH \/ SH + 32768 <= PT) by (clear - HSHs; unfold SH, RB in *; tauto).
  clear HSP HCT HO HSB HK Hst HCA16 HSHs HSH.
  assert (HSPa : bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 2))) = SP - 400) by (rgz; rewrite R2, u_wa_small by (zlh HZ); reflexivity).
  (* [comment removed for export] *)
  assert (P1 : OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_nf2.AXF_mf1z.mf1_pre R mB RB 262144 1540520 514992 262144 RB RB 262144 RB).
  { constructor; [exact R1 | exact R8 | exact R10
                 | (rewrite R2; apply (stk_ok_move mB SP (SP - 400) 1024); [(zlh HZ) | (zlh HZ) | exact HSTK | (zlh HZ) | (zlh HZ) | (zlh HZ)])
                 | (zlh HZ) | (zlh HZ) | (zlh HZ) | (zlh HZ) | (zlh HZ) | (zlh HZ) | (zlh HZ) | (zlh HZ) | (zlh HZ) | (zlh HZ) | rewrite HSPa; (zlh HZ) | | | | | | | | | ].
    all: try (rewrite HSPa; assumption).
    - intros d k Hd Hk. rewrite HSPa. apply HSTK; rewrite !u_wa_small; clear - HZ Hd Hk; lia.
    - exact Icf.
    - exact Icf144. }
  destruct (OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_nf2.AXF_mf1z.mf1_pmf1 R mB rom RB 262144 1540520 514992 262144 RB RB 262144 RB P1
              (sc_mf1 R mB (SP - 400) RB 262144 1540520 514992 262144 RB RB 262144 RB HSPa ltac:((zlh HZ))))
    as (Ra & Hms & A1 & A2 & A8 & A9 & A10 & A11 & A12 & A13 & A18 & A19 & A20 & KKa).
  clear P1 A11 A12 A13.
  set (m1 := OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_nf2.AXF_mf1z.mf1_mem_pmf1 mB R RB 262144 1540520 514992 262144 RB RB 262144 RB) in *.
  assert (EM1 : m1 = wchainS mB SP [(-356, 4%nat, 18446744072277895850)]) by (unfold m1, OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_nf2.AXF_mf1z.mf1_mem_pmf1; rewrite HSPa, sub_add_lit; reflexivity).
  clearbody m1.
  assert (G1 : mem_grows mB m1) by (rewrite EM1; apply wchainS_grows).
  assert (F1 : forall x, 0 <= x < 2^64 -> ~ (SP - 2048 <= x < SP - 272) -> m1 (wa x) = mB (wa x)).
  { intros x Hx Q. rewrite EM1. apply (wchainS_frame_in _ mB SP (-356) (-352)); [(zlh HZ) | (zlh HZ) | reflexivity | reflexivity | exact Hx | clear - HZ Q; lia]. }
  assert (F1' : forall x, 0 <= x < 2^64 -> ~ (SP - 356 <= x < SP - 352) -> m1 (wa x) = mB (wa x)).
  { intros x Hx Q. rewrite EM1. apply (wchainS_frame_in _ mB SP (-356) (-352)); [(zlh HZ) | (zlh HZ) | reflexivity | reflexivity | exact Hx | clear - HZ Q; lia]. }
  regzH A1. regzH A2. regzH A8. regzH A9. regzH A10. regzH A18. regzH A19. regzH A20.
  assert (HSPb : bv_unsigned (getr Ra (Z_to_bv 5 (Z.of_nat 2))) = SP - 304) by (rewrite A2, HSPa, u_wa_small by (zlh HZ); ring).
  (* [comment removed for export] *)
  assert (P2 : AXF_pb1z.pb1_pre Ra m1 RB 262144 RI (CA + 2560) RB).
  { constructor; [regzG; exact A1 | regzG; exact A10 | regzG; exact A19 | regzG; exact A20
                 | (replace (getr Ra 2) with (wa (SP - 304)) by (regzG; rewrite A2, HSPa; f_equal; ring);
                    apply (stk_ok_move m1 SP (SP - 304) 1024); [(zlh HZ) | (zlh HZ) | exact (stk_ok_grows mB m1 (wa SP) 2048 G1 HSTK) | (zlh HZ) | (zlh HZ) | (zlh HZ)])
                 | (zlh HZ) | (zlh HZ) | (zlh HZ) | (zlh HZ) | (zlh HZ) | (zlh HZ) | (zlh HZ) | rewrite HSPb; (zlh HZ) | | | | | | | | | | | | | | | | ].
    all: try (rewrite HSPb; apply (rd_frame mB m1); [(zlh HZ) | lenq'; (zlh HZ) | intros x Hx; lenq'; apply F1'; clear - HZ Hx; lia | assumption]).
    all: try (apply (rd_frame mB m1); [(zlh HZ) | lenq'; (zlh HZ) | intros x Hx; lenq'; apply F1; clear - HZ Hx; lia | assumption]).
    intros d k Hd Hk. rewrite HSPb. apply (store_ok_mono SEGS k mB m1 _ G1). apply HSTK; rewrite !u_wa_small; clear - HZ Hd Hk; lia. }
  destruct (AXF_pb1z.pb1_ppb1 Ra m1 rom RB 262144 RI (CA + 2560) RB P2 ltac:(cbn [AXF_pb1.RES_ppb1 fst snd]; constructor))
    as (Rb & Hms2 & B1 & B2 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12 & B13 & B14 & B15 & B16 & B17 & B18 & B19 & B20 & B28 & KKb).
  clear P2 B5 B6 B7 B13 B14 B15 B16 B17 B28.
  pose proof (msteps_trans SEGS _ _ _ Hms Hms2) as Hms'. clear Hms Hms2. rename Hms' into Hms.
  set (m2 := AXF_pb1z.pb1_mem_ppb1 m1 Ra RB 262144 RI (CA + 2560) RB) in *.
  assert (V21 : bv_unsigned (getr Ra (Z_to_bv 5 (Z.of_nat 21))) = sz_tbl c) by (rewrite (KKa 21%nat ltac:(cbn; memb')); regzH R21; rewrite R21, u_wa_small by (zlh HZ); reflexivity).
  assert (EM2 : m2 = wchainS m1 SP [(-328, 8%nat, sz_tbl c); (-320, 8%nat, RB); (-312, 8%nat, 262144); (-304, 8%nat, RB); (-296, 8%nat, CA + 2560); (-288, 8%nat, RI); (-280, 8%nat, 281752)]).
  { unfold m2, AXF_pb1z.pb1_mem_ppb1. rewrite HSPb, V21, ?u_wa_small by (zlh HZ). rewrite ?sub_add_lit. reflexivity. }
  clearbody m2.
  assert (G2 : mem_grows mB m2) by (rewrite EM2; exact (mem_grows_trans _ _ _ G1 (wchainS_grows _ m1 SP))).
  assert (F2 : forall x, 0 <= x < 2^64 -> ~ (SP - 2048 <= x < SP - 272) -> m2 (wa x) = mB (wa x)).
  { intros x Hx Q. rewrite EM2. rewrite (wchainS_frame_in [(-328, 8%nat, sz_tbl c); (-320, 8%nat, RB); (-312, 8%nat, 262144); (-304, 8%nat, RB); (-296, 8%nat, CA + 2560); (-288, 8%nat, RI); (-280, 8%nat, 281752)] m1 SP (-328) (-272));
      [| clear - HZ; lia | clear - HZ; lia | reflexivity | reflexivity | exact Hx | clear - HZ Q; lia]. apply F1; assumption. }
  (* [comment removed for export] *)
  regzH B10. regzH B11. regzH B12. regzH B1.
  assert (Hsh8 : Z.shiftr RB 3 = RB / 8) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (B12' : getr Rb (Z_to_bv 5 (Z.of_nat 12)) = wa 32768).
  { rewrite B12. f_equal. rewrite Z.mod_small by (zlh HZ). rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
    destruct HZ as (_ & _ & _ & _ & _ & HSBm & _ & HRB & _). assert (RB mod 8 = 0) by (rewrite HRB; clear - HSBm; lia).
    assert (E8 : (RB + 262144 + -8) / 8 = RB / 8 + 32767) by (rewrite (Z.div_mod RB 8) at 1 by lia; rewrite H; replace (8 * (RB / 8) + 0 + 262144 + -8) with ((RB / 8 + 32767) * 8) by ring; apply Z.div_mul; lia).
    rewrite E8. ring. }
  destruct (memsetck_contract rom Rb m2 SH 32768 ltac:(regzG; rewrite B10; unfold SH; reflexivity) ltac:(regzG; exact B12') ltac:((zlh HZ)) ltac:(lia) ltac:((zlh HZ)))
    as (Rc & m3 & Hms3 & KKc & MS1 & MS2 & G3).
  { intros d k Hd Hk. apply (store_ok_mono SEGS k mB m2 _ G2). apply Iwsh; clear - Hd Hk; lia. }
  regzH MS1. rewrite B11 in MS1. change (bv_unsigned (wa 250) mod 256) with 250 in MS1.
  pose proof (msteps_trans SEGS _ _ _ Hms Hms3) as Hms'. clear Hms Hms3. rename Hms' into Hms.
  (* [comment removed for export] *)
  assert (P4 : OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXF_pb1z.AXF_rt1z.rt1_pre Rc m3 0) by (constructor; [regzG; rewrite (KKc 1%nat ltac:(cbn; memb')); exact B1 | lia]).
  destruct (OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXF_pb1z.AXF_rt1z.rt1_prt1 Rc m3 rom 0 P4 ltac:(cbn [OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXF_pb1z.AXF_rt1.RES_prt1 fst snd]; constructor)) as (Rd & Hms4 & C1 & KKd).
  assert (Em4 : OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXF_pb1z.AXF_rt1z.rt1_mem_prt1 m3 Rc 0 = m3) by reflexivity. rewrite Em4 in Hms4. clear Em4 P4.
  pose proof (msteps_trans SEGS _ _ _ Hms Hms4) as Hms'. clear Hms Hms4. rename Hms' into Hms.
  assert (F3 : forall x, 0 <= x < 2^64 -> ~ (SP - 2048 <= x < SP - 272) -> ~ (SH <= x < SH + 32768) -> m3 (wa x) = mB (wa x)).
  { intros x Hx Q1 Q2. rewrite MS2 by assumption. apply F2; assumption. }
  (* [comment removed for export] *)
  assert (KR : forall k, In k [2; 3; 4; 8; 9; 18; 21; 22]%nat -> getr Rd (Z_to_bv 5 (Z.of_nat k)) = getr Rb (Z_to_bv 5 (Z.of_nat k))).
  { intros k Hk. rewrite (KKd k ltac:(clear - Hk; cbn in Hk |- *; repeat (destruct Hk as [<-|Hk]; [memb'|]); destruct Hk)).
    apply KKc. clear - Hk; cbn in Hk |- *; repeat (destruct Hk as [<-|Hk]; [memb'|]); destruct Hk. }
  regzH B2. regzH B8. regzH B9. regzH B18.
  assert (KRb : forall k, In k [3; 4; 21; 22]%nat -> getr Rb (Z_to_bv 5 (Z.of_nat k)) = getr Ra (Z_to_bv 5 (Z.of_nat k))).
  { intros k Hk. apply KKb. clear - Hk; cbn in Hk |- *; repeat (destruct Hk as [<-|Hk]; [memb'|]); destruct Hk. }
  assert (HSPd : bv_unsigned (getr Rd (Z_to_bv 5 (Z.of_nat 2))) = SP - 272) by (rewrite (KR 2%nat ltac:(cbn; memb')), B2, HSPb, u_wa_small by (zlh HZ); ring).
  regzH R4. regzH R21. regzH R22.
  assert (P5 : OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp.AXF_gpb2z.gpb2_pre Rd m3 CA RI RB (sz_tbl c / 16) TP K TSDA PT T mm1 mm2 st2).
  { constructor; [regzG; rewrite (KR 4%nat ltac:(cbn; memb')), (KRb 4%nat ltac:(cbn; memb')), (KKa 4%nat ltac:(cbn; memb')); exact R4
                 | regzG; rewrite (KR 8%nat ltac:(cbn; memb')); exact B8
                 | regzG; rewrite (KR 9%nat ltac:(cbn; memb')); exact B9
                 | regzG; rewrite (KR 18%nat ltac:(cbn; memb')); exact B18
                 | regzG; rewrite (KKd 19%nat ltac:(cbn; memb')), (KKc 19%nat ltac:(cbn; memb')); regzH B19; exact B19
                 | regzG; rewrite (KKd 20%nat ltac:(cbn; memb')), (KKc 20%nat ltac:(cbn; memb')); regzH B20; exact B20
                 | regzG; rewrite (KR 21%nat ltac:(cbn; memb')), (KRb 21%nat ltac:(cbn; memb')), (KKa 21%nat ltac:(cbn; memb')); rewrite HS16; exact R21
                 | regzG; rewrite (KR 22%nat ltac:(cbn; memb')), (KRb 22%nat ltac:(cbn; memb')), (KKa 22%nat ltac:(cbn; memb')); exact R22
                 | (replace (getr Rd 2) with (wa (SP - 272)) by (regzG; rewrite (KR 2%nat ltac:(cbn; memb')), B2, HSPb; f_equal; ring);
                    apply (stk_ok_move m3 SP (SP - 272) 1024); [(zlh HZ) | (zlh HZ) | exact (stk_ok_grows mB m3 (wa SP) 2048 (mem_grows_trans _ _ _ G2 G3) HSTK) | (zlh HZ) | (zlh HZ) | (zlh HZ)])
                 | .. ].
    all: try (zlh HZ).
    all: try (zlh HS16r).
    all: try (rewrite HSPd; (zlh HZ)).
    all: try (rewrite hko by (zlh HZ); rewrite Z.add_0_r).
    all: first [ (apply (rd_frame mB m3); [(zlh HZ) | lenq'; (zlh HZ) | intros x Hx; lenq'; apply F3; [clear - HZ Hx; lia | clear - HZ Hx; lia | first [clear - HZ Hx; lia | clear - HZ HD2 Hx; lia | clear - HZ HD3 Hx; lia | clear - HZ HD4 Hx; lia | clear - HZ HD5 Hx; lia | clear - HZ HD6 Hx; lia]] | assumption])
               | (intros d k Hd Hk; apply (store_ok_mono SEGS k mB m3 _ (mem_grows_trans _ _ _ G2 G3));
                  first [ (replace (T + 2872 + d) with (T + 2872 + (0 + d)) by ring; apply Iwt; clear - Hd Hk; lia)
                        | (replace (T + 2880 + d) with (T + 2872 + (8 + d)) by ring; apply Iwt; clear - Hd Hk; lia)
                        | (apply Iwst; clear - Hd Hk; lia)
                        | (replace (RI + 48 + d) with (RI + (48 + d)) by ring; apply Iwri; clear - Hd Hk; lia) ]) ]. }
  destruct (OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp.AXF_gpb2z.gpb2_ppb2 Rd m3 rom CA RI RB (sz_tbl c / 16) TP K TSDA PT T mm1 mm2 st2 P5
              (sc_gpb2 Rd m3 (SP - 272) HSPd CA RI RB (sz_tbl c / 16) TP K TSDA PT T mm1 mm2 st2 ltac:(unfold objs_ok; clear - HZ HD1; lia) ltac:((zlh HZ)) ltac:((zlh HZ)) HS16r))
    as (Re & Hms5 & D1 & D2 & D4 & D8 & D9 & D10 & D11 & D12 & D13 & D14 & D15 & D18 & D19 & D20 & D21 & D22 & KKe).
  clear P5 D10 D14 D15.
  pose proof (msteps_trans SEGS _ _ _ Hms Hms5) as Hms'. clear Hms Hms5. rename Hms' into Hms.
  assert (VNEW : bv_unsigned (edenot (Ez Rd (OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp.AXF_gpb2z.VALS_gpb2 CA RI RB (sz_tbl c / 16) TP K TSDA PT T mm1 mm2 st2)) (EMd M_DIVU (ELit 262144) (EMd M_MUL (ELit 16) (EVar 35)))) = NEW).
  { rewrite (gdivu_lit Rd (OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp.AXF_gpb2z.VALS_gpb2 CA RI RB (sz_tbl c / 16) TP K TSDA PT T mm1 mm2 st2) (sz_tbl c / 16) eq_refl HS16r), HS16. reflexivity. }
  set (m4 := OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp.AXF_gpb2z.gpb2_mem_ppb2 m3 Rd CA RI RB (sz_tbl c / 16) TP K TSDA PT T mm1 mm2 st2) in *.
  assert (EM4 : m4 = wchainS (wbytes (wbytes (wbytes (wbytes (wchainS m3 SP [(-296, 8%nat, 436880); (-280, 8%nat, 281756)])
                        (wa (T + 2872)) (word_to_le_bytes 8 (wa (mm1 + 1)))) (wa (T + 2880)) (word_to_le_bytes 8 (wa (mm2 + 262144))))
                        (wa (CA + 2584)) (word_to_le_bytes 8 (wa (st2 + 262144)))) (wa (RI + 48)) (word_to_le_bytes 8 (wa 262144)))
                     SP [(-312, 8%nat, NEW); (-304, 8%nat, RB); (-296, 8%nat, NEW); (-288, 8%nat, RI); (-280, 8%nat, 281840)]).
  { unfold m4, OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp.AXF_gpb2z.gpb2_mem_ppb2. rewrite HSPd, VNEW, ?sub_add_lit. reflexivity. }
  clearbody m4.
  assert (G4 : mem_grows mB m4).
  { apply (mem_grows_trans _ m3 _ (mem_grows_trans _ _ _ G2 G3)). rewrite EM4.
    match goal with |- mem_grows _ (wchainS ?X SP ?L) => apply (mem_grows_trans _ X _); [|apply (wchainS_grows L X SP)] end.
    repeat apply grows_wb. apply mem_grows_refl. }
  assert (F4 : forall x, 0 <= x < 2^64 -> ~ (SP - 2048 <= x < SP - 272) -> ~ (SH <= x < SH + 32768) -> ~ (RI + 48 <= x < RI + 56) ->
                 ~ (CA + 2584 <= x < CA + 2592) -> ~ (T + 2872 <= x < T + 2888) -> m4 (wa x) = mB (wa x)).
  { intros x Hx Q1 Q2 Q3 Q4 Q5. rewrite EM4.
    rewrite (wchainS_frame_in [(-312, 8%nat, NEW); (-304, 8%nat, RB); (-296, 8%nat, NEW); (-288, 8%nat, RI); (-280, 8%nat, 281840)] _ SP (-312) (-272));
      [| clear - HZ; lia | clear - HZ; lia | reflexivity | reflexivity | exact Hx | clear - HZ Q1; lia].
    repeat (rewrite wb_other by first [exact Hx | (lenq'; clear - HZ; lia) | (lenq'; clear - HZ Q3 Q4 Q5; lia)]).
    rewrite (wchainS_frame_in [(-296, 8%nat, 436880); (-280, 8%nat, 281756)] _ SP (-296) (-272));
      [| clear - HZ; lia | clear - HZ; lia | reflexivity | reflexivity | exact Hx | clear - HZ Q1; lia].
    apply F3; assumption. }
  (* [comment removed for export] *)
  regzH D1. regzH D2. regzH D4. regzH D8. regzH D9. regzH D11. regzH D12. regzH D13. regzH D18. regzH D19. regzH D20. regzH D21. regzH D22. rewrite HS16 in D21.
  assert (HSPe : bv_unsigned (getr Re (Z_to_bv 5 (Z.of_nat 2))) = SP - 320) by (rewrite D2, HSPd, u_wa_small by (zlh HZ); ring).
  assert (P6 : AXF_mf0z.mf0_pre Re m4 (RB + 3758096384) 262144 104102 1540520).
  { constructor; [regzG; exact D11 | regzG; exact D12 | regzG; exact D13
                 | (replace (getr Re 2) with (wa (SP - 320)) by (regzG; rewrite D2, HSPd; f_equal; ring);
                    apply (stk_ok_move m4 SP (SP - 320) 1024); [(zlh HZ) | (zlh HZ) | exact (stk_ok_grows mB m4 (wa SP) 2048 G4 HSTK) | (zlh HZ) | (zlh HZ) | (zlh HZ)])
                 | (zlh HZ) | (zlh HZ) | (zlh HZ) | (zlh HZ) | (zlh HZ) | (zlh HZ) | rewrite HSPe; (zlh HZ) | | | | ].
    all: apply (rd_frame mB m4); [(zlh HZ) | lenq'; (zlh HZ) | intros x Hx; lenq'; apply F4; clear - HZ Hx; lia | assumption]. }
  destruct (AXF_mf0z.mf0_pmf0 Re m4 rom (RB + 3758096384) 262144 104102 1540520 P6
              (sc_mf0 Re m4 (SP - 320) (RB + 3758096384) 262144 104102 1540520 HSPe ltac:((zlh HZ))))
    as (Rf & Hms6 & E1 & E2 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E17 & E18 & E19 & E20 & KKf).
  clear P6.
  pose proof (msteps_trans SEGS _ _ _ Hms Hms6) as Hms'. clear Hms Hms6. rename Hms' into Hms.
  assert (EM5 : AXF_mf0z.mf0_mem_pmf0 m4 Re (RB + 3758096384) 262144 104102 1540520 =
                wchainS m4 SP [(-504, 8%nat, sz_tbl c); (-496, 8%nat, 1532192); (-488, 8%nat, 104102); (-480, 8%nat, RB + 3758096384); (-472, 8%nat, 1);
                               (-464, 8%nat, 262144); (-456, 8%nat, 481756); (-448, 4%nat, 50); (-400, 8%nat, 262144); (-392, 8%nat, RI);
                               (-384, 8%nat, 262144); (-376, 8%nat, RB + 3758096384); (-368, 8%nat, 262144); (-360, 8%nat, 514992);
                               (-352, 8%nat, 262144); (-344, 8%nat, RB + 3758096384); (-336, 8%nat, 262144); (-328, 8%nat, 272576)]).
  { unfold AXF_mf0z.mf0_mem_pmf0. rewrite HSPe, D1, D8, D9, D18, D19, D20, D21, ?u_wa_small by (zlh HZ). rewrite ?sub_add_lit. reflexivity. }
  rewrite EM5 in Hms. clear EM5.
  set (L5 := [(-504, 8%nat, sz_tbl c); (-496, 8%nat, 1532192); (-488, 8%nat, 104102); (-480, 8%nat, RB + 3758096384); (-472, 8%nat, 1);
              (-464, 8%nat, 262144); (-456, 8%nat, 481756); (-448, 4%nat, 50); (-400, 8%nat, 262144); (-392, 8%nat, RI);
              (-384, 8%nat, 262144); (-376, 8%nat, RB + 3758096384); (-368, 8%nat, 262144); (-360, 8%nat, 514992);
              (-352, 8%nat, 262144); (-344, 8%nat, RB + 3758096384); (-336, 8%nat, 262144); (-328, 8%nat, 272576)]) in *.
  assert (F5 : forall x, 0 <= x < 2^64 -> ~ (SP - 504 <= x < SP - 320) -> wchainS m4 SP L5 (wa x) = m4 (wa x)).
  { intros x Hx Q. apply (wchainS_frame_in L5 m4 SP (-504) (-320)); [clear - HZ; lia | clear - HZ; lia | reflexivity | reflexivity | exact Hx | clear - HZ Q; lia]. }
  exists Rf, (wchainS m4 SP L5). split; [exact Hms|].
  split; [regzH E1; exact E1|]. split; [regzH E2; rewrite E2, HSPe; f_equal; ring|]. split; [regzH E8; exact E8|].
  split; [regzH E10; exact E10|]. split; [regzH E11; exact E11|]. split; [regzH E12; exact E12|]. split; [regzH E13; exact E13|].
  split; [regzH E14; exact E14|]. split; [regzH E15; exact E15|]. split; [regzH E17; exact E17|].
  split; [rewrite (KKf 21%nat ltac:(cbn; memb')); exact D21|]. split; [rewrite (KKf 22%nat ltac:(cbn; memb')); exact D22|].
  split; [rewrite (KKf 4%nat ltac:(cbn; memb')); exact D4|].
  split; [rewrite (KKf 3%nat ltac:(cbn; memb')), (KKe 3%nat ltac:(cbn; memb')), (KKd 3%nat ltac:(cbn; memb')), (KKc 3%nat ltac:(cbn; memb')), (KKb 3%nat ltac:(cbn; memb')), (KKa 3%nat ltac:(cbn; memb')); reflexivity|].
  split.
  { intros x Hx. rewrite F5 by (clear - HZ Hx; lia). rewrite EM4.
    rewrite (wchainS_frame_in [(-312, 8%nat, NEW); (-304, 8%nat, RB); (-296, 8%nat, NEW); (-288, 8%nat, RI); (-280, 8%nat, 281840)] _ SP (-312) (-272));
      [| clear - HZ; lia | clear - HZ; lia | reflexivity | reflexivity | clear - HZ Hx; lia | clear - HZ Hx; lia].
    repeat (rewrite wb_other by first [(clear - HZ Hx; lia) | (lenq'; clear - HZ; lia) | (lenq'; clear - HZ HD2 HD3 Hx; lia)]).
    rewrite (wchainS_frame_in [(-296, 8%nat, 436880); (-280, 8%nat, 281756)] _ SP (-296) (-272));
      [| clear - HZ; lia | clear - HZ; lia | reflexivity | reflexivity | clear - HZ Hx; lia | clear - HZ Hx; lia].
    apply MS1. exact Hx. }
  assert (RL5 : forall k v, wl_chk L5 k 8 = Some v -> -504 <= k -> k + 8 <= -320 -> rd (wchainS m4 SP L5) (SP + k) 8 v).
  { intros k v H H1 H2. apply rd_wchainS; [(zlh HZ) | (zlh HZ) | reflexivity | lia | cbn; lia | lia | exact H]. }
  split; [replace (SP - 448 + 88) with (SP + -360) by ring; apply RL5; [reflexivity | lia | lia]|].
  split; [replace (SP - 448 + 80) with (SP + -368) by ring; apply RL5; [reflexivity | lia | lia]|].
  split; [replace (SP - 448 + 72) with (SP + -376) by ring; apply RL5; [reflexivity | lia | lia]|].
  split; [replace (SP - 448 + 64) with (SP + -384) by ring; apply RL5; [reflexivity | lia | lia]|].
  split; [replace (SP - 448 + 56) with (SP + -392) by ring; apply RL5; [reflexivity | lia | lia]|].
  split; [replace (SP - 448 + 48) with (SP + -400) by ring; apply RL5; [reflexivity | lia | lia]|].
  split; [replace (SP - 352 + 24) with (SP + -328) by ring; apply RL5; [reflexivity | lia | lia]|].
  split; [replace (SP - 352 + 16) with (SP + -336) by ring; apply RL5; [reflexivity | lia | lia]|].
  split; [replace (SP - 352 + 8) with (SP + -344) by ring; apply RL5; [reflexivity | lia | lia]|].
  split; [replace (SP - 352 + 0) with (SP + -352) by ring; apply RL5; [reflexivity | lia | lia]|].
  assert (RL4 : forall k v, wl_chk [(-312, 8%nat, NEW); (-304, 8%nat, RB); (-296, 8%nat, NEW); (-288, 8%nat, RI); (-280, 8%nat, 281840)] k 8 = Some v ->
                  -312 <= k -> k + 8 <= -272 -> rd (wchainS m4 SP L5) (SP + k) 8 v).
  { intros k v H H1 H2. apply (rd_frame m4); [clear - HZ H1 H2; lia | cbn; clear - HZ H1 H2; lia | intros x Hx; cbn in Hx; apply F5; clear - HZ Hx H1 H2; lia |].
    rewrite EM4. apply rd_wchainS; [(zlh HZ) | (zlh HZ) | reflexivity | lia | cbn; lia | lia | exact H]. }
  split; [replace (SP - 280) with (SP + -280) by ring; apply RL4; [reflexivity | lia | lia]|].
  split; [replace (SP - 288) with (SP + -288) by ring; apply RL4; [reflexivity | lia | lia]|].
  split; [replace (SP - 296) with (SP + -296) by ring; apply RL4; [reflexivity | lia | lia]|].
  split; [replace (SP - 304) with (SP + -304) by ring; apply RL4; [reflexivity | lia | lia]|].
  split; [replace (SP - 312) with (SP + -312) by ring; apply RL4; [reflexivity | lia | lia]|].
  split.
  { apply (rd_frame m4); [(zlh HZ) | cbn; (zlh HZ) | intros x Hx; cbn in Hx; apply F5; clear - HZ Hx; lia |]. rewrite EM4.
    apply (rd_frame (wbytes (wbytes (wbytes (wbytes (wchainS m3 SP [(-296, 8%nat, 436880); (-280, 8%nat, 281756)])
                        (wa (T + 2872)) (word_to_le_bytes 8 (wa (mm1 + 1)))) (wa (T + 2880)) (word_to_le_bytes 8 (wa (mm2 + 262144))))
                        (wa (CA + 2584)) (word_to_le_bytes 8 (wa (st2 + 262144)))) (wa (RI + 48)) (word_to_le_bytes 8 (wa 262144))));
      [(zlh HZ) | cbn; (zlh HZ) | intros x Hx; cbn in Hx; apply (wchainS_frame_in _ _ SP (-312) (-272)); [clear - HZ; lia | clear - HZ; lia | reflexivity | reflexivity | clear - HZ Hx; lia | clear - HZ Hx; lia] |].
    apply wb_rd_hit; lenq'; (zlh HZ). }
  split.
  { apply (rd_frame m4); [(zlh HZ) | cbn; (zlh HZ) | intros x Hx; cbn in Hx; apply F5; clear - HZ Hx; lia |]. rewrite EM4.
    apply (rd_frame (wbytes (wchainS m3 SP [(-296, 8%nat, 436880); (-280, 8%nat, 281756)]) (wa (T + 2872)) (word_to_le_bytes 8 (wa (mm1 + 1))))); [(zlh HZ) | cbn; (zlh HZ) | | apply wb_rd_hit; lenq'; (zlh HZ)].
    intros x Hx; cbn in Hx.
    rewrite (wchainS_frame_in [(-312, 8%nat, NEW); (-304, 8%nat, RB); (-296, 8%nat, NEW); (-288, 8%nat, RI); (-280, 8%nat, 281840)] _ SP (-312) (-272));
      [| clear - HZ; lia | clear - HZ; lia | reflexivity | reflexivity | clear - HZ Hx; lia | clear - HZ Hx; lia].
    repeat (rewrite wb_other by first [(clear - HZ Hx; lia) | (lenq'; clear - HZ; lia) | (lenq'; clear - HZ HD1 Hx; lia)]). reflexivity. }
  split.
  { apply (rd_frame m4); [(zlh HZ) | cbn; (zlh HZ) | intros x Hx; cbn in Hx; apply F5; clear - HZ Hx; lia |]. rewrite EM4.
    apply (rd_frame (wbytes (wbytes (wchainS m3 SP [(-296, 8%nat, 436880); (-280, 8%nat, 281756)]) (wa (T + 2872)) (word_to_le_bytes 8 (wa (mm1 + 1)))) (wa (T + 2880)) (word_to_le_bytes 8 (wa (mm2 + 262144))))); [(zlh HZ) | cbn; (zlh HZ) | | apply wb_rd_hit; lenq'; (zlh HZ)].
    intros x Hx; cbn in Hx.
    rewrite (wchainS_frame_in [(-312, 8%nat, NEW); (-304, 8%nat, RB); (-296, 8%nat, NEW); (-288, 8%nat, RI); (-280, 8%nat, 281840)] _ SP (-312) (-272));
      [| clear - HZ; lia | clear - HZ; lia | reflexivity | reflexivity | clear - HZ Hx; lia | clear - HZ Hx; lia].
    repeat (rewrite wb_other by first [(clear - HZ Hx; lia) | (lenq'; clear - HZ; lia) | (lenq'; clear - HZ HD1 Hx; lia)]). reflexivity. }
  split.
  { apply (rd_frame m4); [(zlh HZ) | cbn; (zlh HZ) | intros x Hx; cbn in Hx; apply F5; clear - HZ Hx; lia |]. rewrite EM4.
    apply (rd_frame (wbytes (wbytes (wbytes (wchainS m3 SP [(-296, 8%nat, 436880); (-280, 8%nat, 281756)]) (wa (T + 2872)) (word_to_le_bytes 8 (wa (mm1 + 1)))) (wa (T + 2880)) (word_to_le_bytes 8 (wa (mm2 + 262144)))) (wa (CA + 2584)) (word_to_le_bytes 8 (wa (st2 + 262144))))); [(zlh HZ) | cbn; (zlh HZ) | | apply wb_rd_hit; lenq'; (zlh HZ)].
    intros x Hx; cbn in Hx.
    rewrite (wchainS_frame_in [(-312, 8%nat, NEW); (-304, 8%nat, RB); (-296, 8%nat, NEW); (-288, 8%nat, RI); (-280, 8%nat, 281840)] _ SP (-312) (-272));
      [| clear - HZ; lia | clear - HZ; lia | reflexivity | reflexivity | clear - HZ Hx; lia | clear - HZ Hx; lia].
    repeat (rewrite wb_other by first [(clear - HZ Hx; lia) | (lenq'; clear - HZ; lia) | (lenq'; clear - HZ HD1 Hx; lia)]). reflexivity. }
  split.
  { intros x Hx Q1 Q2 Q3 Q4 Q5. rewrite F5 by (clear - HZ Hx Q1; lia). apply F4; assumption. }
  exact (mem_grows_trans _ _ _ G4 (wchainS_grows L5 m4 SP)).
Qed.
End GSB3.
(* [comment removed for export] *)
