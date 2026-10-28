(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas FseAbs FseReaderRT FseReadSound.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseRdKit FseRdKit2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg ABase RtCells AF_fse_rd_base AF_fse_rd_mem AF_fse_rd_loop
     AF_fse_rd_hdr AF_fse_rd_err.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKitF.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Warnings "-notation-for-abbreviation".
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_enrich ::= rewrite ?shad_div in *; rewrite ?nshad_div in *; unfold ASHOFF, KLOW, KHIGH, KEND in *; rewrite ?Z.shiftr_div_pow2 in * by lia.
Local Ltac acc_hint ::= rdA_acc_hint.

Section CANSEC1. Context {rc : runConstT}.
Section Hdr.
  Variable C : rdctxA.
  Variable RNG : footprint.
  Hypothesis OK : rd_okA C.
  Hypothesis SH : rd_shA C.
  Hypothesis RNGS : rd_rngA C RNG.

  Notation buf := (a_buf C).
  Notation msv1 := (a_msv0 C + 1).
  Notation BUF := (a_BUF C).
  Notation NC := (a_NC C).
  Notation MSVP := (a_MSVP C).
  Notation TLP := (a_TLP C).
  Notation SPA := (a_SPA C).
  Notation FF := (a_FF C).
  Ltac cbnR := cbn [r_nc r_ip r_bitStream r_bitCount r_charnum r_remaining r_threshold r_nbBits r_previous0] in *.
  Ltac zify_lts K :=
    unfold bv_lts in K; rewrite ?land7_mod in K;
    rewrite !signed_lit_small64 in K by (Z.div_mod_to_equations; lia);
    zify_bool K.

  Definition ERRX (sF : rstate) (e : Z) : Prop :=
    (r_remaining sF <> 1 /\ e = 20) \/ (r_remaining sF = 1 /\ msv1 < r_charnum sF /\ e = 48)
    \/ (r_remaining sF = 1 /\ r_charnum sF <= msv1 /\ 32 < r_bitCount sF /\ e = 20).

#[using="Type"] Lemma errinv_pro : forall m1 tl0 j0 j8 j16 j32 j40 j48 j64,
u8arr bsegs m1 NC (u16s (map (Z_to_bv 64) (zero_prefix (Z.to_nat msv1) (a_rt0 C)))) ->
rw_cells bsegs m1 MSVP [C4 (Z_to_bv 64 (a_msv0 C))] -> rw_cells bsegs m1 TLP [C4 tl0] ->
rw_cells bsegs m1 SPA (FRA_pro C j0 j8 j16 j32 j40 j48 j64) ->
stk bsegs m1 (a_lo C) SPA -> munch (rd_WA C) (a_m C) m1 -> wmono bsegs (a_m C) m1 -> mem_inv bsegs m1 ->
rd_errinvA C m1.
Proof.
intros m1 tl0 j0 j8 j16 j32 j40 j48 j64 ARR HMSV HTL FR ST MU WM MI.
split; [exists (zero_prefix (Z.to_nat msv1) (a_rt0 C)); split; [exact ARR| apply zero_prefix_length]|].
split; [eexists; exact HMSV|]. split; [eexists; exact HTL|].
split; [| exact (conj ST (conj MU (conj WM MI)))].
unfold FRA_pro in FR.
lazymatch type of FR with rw_cells ?sg ?mm ?AA [?c0; ?c1; ?c2; ?c3; ?c4; ?c5; ?c6; ?c7; ?c8; ?c9] =>
  change (rw_cells sg mm AA ([c0; c1; c2; c3] ++ [c4; c5; c6; c7; c8; c9] ++ [])) in FR;
  apply rw_cells_merge in FR;
  change (rw_cells sg mm AA ([] ++ [c0; c1; c2] ++ (c3 :: [CB (cells_size [c4; c5; c6; c7; c8; c9])
    (cells_bytes [c4; c5; c6; c7; c8; c9])]))) in FR;
  apply rw_cells_merge in FR; cbn [app cells_size csize Nat.add] in FR
end.
do 2 eexists. exact FR.
Qed.
  (* [comment removed for export] *)
#[using="rc OK SH RNGS"] Lemma hd_tail_errA : forall m1 tl0 sF e j0 j8 j32 j40 j48 j64 (x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x20 x28 x29 x30 x31 : word),
u8arr bsegs m1 NC (u16s (map (Z_to_bv 64) (zero_prefix (Z.to_nat msv1) (a_rt0 C)))) ->
rw_cells bsegs m1 MSVP [C4 (Z_to_bv 64 (a_msv0 C))] -> rw_cells bsegs m1 TLP [C4 tl0] ->
bytes_at bsegs m1 BUF (map (Z_to_bv 8) buf) -> rw_cells bsegs m1 SPA (FRA_mid C j0 j8 j32 j40 j48 j64) ->
stk bsegs m1 (a_lo C) SPA -> munch (rd_WA C) (a_m C) m1 -> wmono bsegs (a_m C) m1 -> mem_inv bsegs m1 ->
Z.land (le32 buf 0) 15 <= 10 ->
rloop buf msv1 (S (Z.to_nat msv1)) (rd_s0 buf msv1 (a_rt0 C)) = Ok sF ->
ERRX sF e ->
evtF bsegs RNG (rd_mainA_errpost C e)
(MS (mkR x1 (Z_to_bv 64 SPA) (a_gp C) (a_tp C) x5 x6 x7 (Z_to_bv 64 (a_SP C)) (Z_to_bv 64 SPA)
(Z_to_bv 64 (Z.land (le32 buf 0) 15)) (Z_to_bv 64 (le32 buf 0)) x12 x13 x14 x15 x16 x17
(Z_to_bv 64 (Z.shiftr MSVP 3 + 2147450880)) (Z_to_bv 64 (BUF + zlen buf)) x20 (Z_to_bv 64 NC) (Z_to_bv 64 TLP) (Z_to_bv 64 msv1)
(Z_to_bv 64 2147450880) (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 BUF) x28 x29 x30 x31)
(a_F C) (Z_to_bv 64 0x96c58) (a_fc C) None m1 (seg_rom bsegs)).
Proof.
intros m1 tl0 sF e j0 j8 j32 j40 j48 j64 x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x20 x28 x29 x30 x31 ARR HMSV HTL HBUF FRM ST MU WM MI HX RL EX.
pose proof OK as OK'. destruct OK' as (HH & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SNT & _ & SMT & _ & STB & _).
pose proof (okA_lin C OK) as (HH' & HM0 & HM1 & HRT & SP16 & SPK & LO & LOA & SPA12 & SPA3 & NC0 & NC1 & N8 & MS0 & MS1 & M4
& TL0 & TL1 & T4 & BF0 & BF1 & B8 & FF0 & FF1 & F64).
pose proof RNGS as RNGS'. destruct RNGS' as (RI & RSTK & RN & RNS & RM & RMS & RT & RTS & RB & RBS).
pose proof atop_range as ATR. unfold RDA_CALLEE, KHIGH, AIMG_HI, KEND in *.
unfold FRA_mid, ASHB in FRM. unfold rd_WA, RDA_CALLEE in MU.
destruct (rd_s0_inv buf msv1 (a_rt0 C) (buf_all_bytesA C OK) (proj1 HH) ltac:(lia) HX) as (HC0 & HP0 & HB0').
pose proof (le32_range buf 0 (buf_all_bytesA C OK)) as RW.
set (W := le32 buf 0) in *.
remember (Z.land W 15) as x eqn:Ex.
assert (X0 : 0 <= x) by (subst x; rewrite land_15; apply Z.mod_pos_bound; lia).
assert (P5 : 32 <= 2 ^ (x + 5) <= 32768).
{ split; [change 32 with (2^5)| change 32768 with (2^15)]; apply Z.pow_le_mono_r; lia. }
assert (LWS : length (map (Z_to_bv 64) (zero_prefix (Z.to_nat msv1) (a_rt0 C))) = length (a_rt0 C))
by (rewrite length_map; apply zero_prefix_length).
zstep. zstep. zstep. zstep. zstep.
zstep. zstep. zstep.
zstep.
zstep. replace (0 <? NC) with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z].
do 7 zstep.
zstep.
zstep.
zstep. rewrite ?(Z.mod_small x 32) by lia. rewrite Z.shiftl_mul_pow2 by lia.
replace (32 * 2 ^ x) with (2 ^ (x + 5)) by (rewrite Z.pow_add_r by lia; change (2^5) with 32; lia).
rewrite (FseWalkKit.swrap32_small (2 ^ (x + 5))) by lia.
zstep. zstep.
zstep. zstep. zstep. zstep. zstep.
zstep.
zstep. rewrite (FseWalkKit.swrap32_small (2 ^ (x + 5) + 1)) by lia.
zstep. zstep. zstep. zstep. if_false.
replace (Z_to_bv 64 (-2147483648)) with (Z_to_bv 64 18446744071562067968) by (apply bv_eq; reflexivity).
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
assert (INV0 : rd_invA C mm (r_nc (rd_s0 buf msv1 (a_rt0 C))) (Z_to_bv 64 (a_msv0 C)) (Z_to_bv 64 (x + 5))) end.
{ unfold rd_s0. cbv zeta. cbnR. unfold rd_invA.
split; [eassumption|]. split; [apply zero_prefix_length|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
split; [do 2 eexists; unfold FRA_main, ASHB; eassumption|]. split; [eassumption|]. split; [eassumption|]. split; eassumption. }
pose proof (loop_runQ' C RNG OK SH RNGS (x + 5) ltac:(lia) (rd_mainA_errpost C e) (S (Z.to_nat msv1)) (rd_s0 buf msv1 (a_rt0 C)) sF m (Z_to_bv 64 (a_msv0 C)) 0x96cdc) as LR.
unfold rd_lstA in LR.
eapply LR; try eassumption; try reflexivity.
all: try (intros m3 z1 z6 z7 z12 z18 z20 z22 z29 INV3 BK; unfold ERRX in EX; eapply exit_run_errA; first [eassumption | lia]).
all: unfold rd_s0; cbv zeta; cbnR; fold W; rewrite <- ?Ex.
all: try (f_equal; lia).
all: try reflexivity.
rewrite ?(Z.shiftr_div_pow2 W 4) by lia. f_equal. symmetry. apply FseWalkKit.swrap32_small.
assert (0 <= W / 2^4 < 2^28) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]). lia.
Qed.
#[using="rc OK SH RNGS"] Lemma hd_tlp_errA : forall m1 tl0 sF e j0 j8 j16 j32 j40 j48 j64 (x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x20 x28 x29 x30 x31 : word),
u8arr bsegs m1 NC (u16s (map (Z_to_bv 64) (zero_prefix (Z.to_nat msv1) (a_rt0 C)))) ->
rw_cells bsegs m1 MSVP [C4 (Z_to_bv 64 (a_msv0 C))] -> rw_cells bsegs m1 TLP [C4 tl0] ->
bytes_at bsegs m1 BUF (map (Z_to_bv 8) buf) -> rw_cells bsegs m1 SPA (FRA_pro C j0 j8 j16 j32 j40 j48 j64) ->
stk bsegs m1 (a_lo C) SPA -> munch (rd_WA C) (a_m C) m1 -> wmono bsegs (a_m C) m1 -> mem_inv bsegs m1 ->
Z.land (le32 buf 0) 15 <= 10 ->
rloop buf msv1 (S (Z.to_nat msv1)) (rd_s0 buf msv1 (a_rt0 C)) = Ok sF ->
ERRX sF e ->
evtF bsegs RNG (rd_mainA_errpost C e)
(MS (mkR x1 (Z_to_bv 64 SPA) (a_gp C) (a_tp C) x5 x6 x7 (Z_to_bv 64 (a_SP C)) (Z_to_bv 64 SPA)
(Z_to_bv 64 (Z.land (le32 buf 0) 15)) (Z_to_bv 64 (le32 buf 0)) x12 x13 x14 x15 x16 x17
(Z_to_bv 64 (Z.shiftr MSVP 3 + 2147450880)) (Z_to_bv 64 (BUF + zlen buf)) x20 (Z_to_bv 64 NC) (Z_to_bv 64 TLP) (Z_to_bv 64 msv1)
(Z_to_bv 64 2147450880) (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 BUF) x28 x29 x30 x31)
(a_F C) (Z_to_bv 64 0x96c38) (a_fc C) None m1 (seg_rom bsegs)).
Proof.
intros m1 tl0 sF e j0 j8 j16 j32 j40 j48 j64 x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x20 x28 x29 x30 x31 ARR HMSV HTL HBUF FRM ST MU WM MI HX RL EX.
pose proof (okA_lin C OK) as (HH & HM0 & HM1 & HRT & SP16 & SPK & LO & LOA & SPA12 & SPA3 & NC0 & NC1 & N8 & MS0 & MS1 & M4
& TL0 & TL1 & T4 & BF0 & BF1 & B8 & FF0 & FF1 & F64).
pose proof RNGS as RNGS'. destruct RNGS' as (RI & RSTK & RN & RNS & RM & RMS & RT & RTS & RB & RBS).
pose proof atop_range as ATR. unfold RDA_CALLEE, KHIGH, AIMG_HI, KEND in *.
unfold FRA_pro, ASHB in FRM. unfold rd_WA, RDA_CALLEE in MU.
assert (LWS : length (map (Z_to_bv 64) (zero_prefix (Z.to_nat msv1) (a_rt0 C))) = length (a_rt0 C))
by (rewrite length_map; apply zero_prefix_length).
assert (LBS : length (map (Z_to_bv 8) buf) = length buf) by apply length_map.
pose proof (hd_tail_errA) as TAIL.
zstep.
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => remember mm as m2 eqn:Hm2 end.
assert (MU2 : munch (rd_WA C) (a_m C) m2) by (unfold rd_WA, RDA_CALLEE; assumption).
destruct (inv_shadowA C m2 OK SH MU2) as (_ & _ & UT & _).
destruct (chk1A m2 TLP (TLP + 4) TLP 4 UT ltac:(lia) ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as (bt & RDBT & CKT & SRT).
zstep. if_cases G1; zify_cond G1; [exfalso; lia|].
zstep. replace (Z.land TLP 3) with 0
by (change 3 with (2^2 - 1); rewrite land_ones_mod by lia; change (2^2) with 4; symmetry; Z.div_mod_to_equations; lia).
zstep. if_false.
zstep. zstep. zstep. rewrite sxb_sval.
assert (J3 : forall (y12 y13 : word),
evtF bsegs RNG (rd_mainA_errpost C e)
(MS (mkR x1 (Z_to_bv 64 SPA) (a_gp C) (a_tp C) x5 x6 x7 (Z_to_bv 64 (a_SP C)) (Z_to_bv 64 SPA)
(Z_to_bv 64 (Z.land (le32 buf 0) 15)) (Z_to_bv 64 (le32 buf 0)) y12 y13 x14 x15 x16 x17
(Z_to_bv 64 (Z.shiftr MSVP 3 + 2147450880)) (Z_to_bv 64 (BUF + zlen buf)) x20 (Z_to_bv 64 NC) (Z_to_bv 64 TLP) (Z_to_bv 64 msv1)
(Z_to_bv 64 2147450880) (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 BUF) x28 x29 x30 x31)
(a_F C) (Z_to_bv 64 0x96c58) (a_fc C) None m2 (seg_rom bsegs))).
{ intros y12 y13. clear RDBT CKT SRT. eapply TAIL; try eassumption; unfold FRA_mid, ASHB; eassumption. }
zstep. if_cases G; zify_cond G.
- zstep. zstep. zstep. if_cases G'; zify_lts G'; [| exfalso; Z.div_mod_to_equations; lia]. apply J3.
- apply J3.
Qed.
#[using="rc OK SH RNGS"] Lemma hd_chk_err1A : forall m1 tl0 j0 j8 j16 j32 j40 j48 j64 (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x28 x29 x30 x31 : word),
u8arr bsegs m1 NC (u16s (map (Z_to_bv 64) (zero_prefix (Z.to_nat msv1) (a_rt0 C)))) ->
rw_cells bsegs m1 MSVP [C4 (Z_to_bv 64 (a_msv0 C))] -> rw_cells bsegs m1 TLP [C4 tl0] ->
bytes_at bsegs m1 BUF (map (Z_to_bv 8) buf) -> rw_cells bsegs m1 SPA (FRA_pro C j0 j8 j16 j32 j40 j48 j64) ->
stk bsegs m1 (a_lo C) SPA -> munch (rd_WA C) (a_m C) m1 -> wmono bsegs (a_m C) m1 -> mem_inv bsegs m1 ->
10 < Z.land (le32 buf 0) 15 ->
evtF bsegs RNG (rd_mainA_errpost C 44)
(MS (mkR x1 (Z_to_bv 64 SPA) (a_gp C) (a_tp C) x5 x6 x7 (Z_to_bv 64 (a_SP C)) (Z_to_bv 64 SPA)
(Z_to_bv 64 NC) x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 (Z.shiftr MSVP 3 + 2147450880)) (Z_to_bv 64 (BUF + zlen buf)) x20 (Z_to_bv 64 NC) (Z_to_bv 64 TLP) (Z_to_bv 64 msv1)
(Z_to_bv 64 2147450880) (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 BUF) x28 x29 x30 x31)
(a_F C) (Z_to_bv 64 0x96bd4) (a_fc C) None m1 (seg_rom bsegs)).
Proof.
intros m1 tl0 j0 j8 j16 j32 j40 j48 j64 x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x28 x29 x30 x31 ARR HMSV HTL HBUF FRM ST MU WM MI HX.
pose proof (okA_lin C OK) as (HH & HM0 & HM1 & HRT & SP16 & SPK & LO & LOA & SPA12 & SPA3 & NC0 & NC1 & N8 & MS0 & MS1 & M4
& TL0 & TL1 & T4 & BF0 & BF1 & B8 & FF0 & FF1 & F64).
pose proof RNGS as RNGS'. destruct RNGS' as (RI & RSTK & RN & RNS & RM & RMS & RT & RTS & RB & RBS).
pose proof atop_range as ATR. unfold RDA_CALLEE, KHIGH, AIMG_HI, KEND in *.
destruct (inv_shadowA C m1 OK SH MU) as (_ & _ & UT & UB).
destruct (chkB m1 BUF (BUF + zlen buf) BUF UB ltac:(lia) ltac:(lia)) as (b0 & RDB0 & CK0 & SR0).
destruct (chkB m1 BUF (BUF + zlen buf) (BUF + 3) UB ltac:(lia) ltac:(lia)) as (b3 & RDB3 & CK3 & SR3).
destruct (buf_rdA C OK m1 0 HBUF ltac:(lia)) as [RD0 R0].
destruct (buf_rdA C OK m1 1 HBUF ltac:(lia)) as [RD1 R1].
destruct (buf_rdA C OK m1 2 HBUF ltac:(lia)) as [RD2 R2].
destruct (buf_rdA C OK m1 3 HBUF ltac:(lia)) as [RD3 R3].
rewrite Z.add_0_r in RD0.
assert (J1 : forall (y10 y11 y12 : word),
evtF bsegs RNG (rd_mainA_errpost C 44)
(MS (mkR x1 (Z_to_bv 64 SPA) (a_gp C) (a_tp C) x5 x6 x7 (Z_to_bv 64 (a_SP C)) (Z_to_bv 64 SPA)
y10 y11 y12 x13 x14 x15 x16 x17
(Z_to_bv 64 (Z.shiftr MSVP 3 + 2147450880)) (Z_to_bv 64 (BUF + zlen buf)) x20 (Z_to_bv 64 NC) (Z_to_bv 64 TLP) (Z_to_bv 64 msv1)
(Z_to_bv 64 2147450880) (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 BUF) x28 x29 x30 x31)
(a_F C) (Z_to_bv 64 0x96bfc) (a_fc C) None m1 (seg_rom bsegs))).
{ intros y10 y11 y12. clear RDB0 CK0 SR0 RDB3 CK3 SR3.
zstep. cbv beta. zstep. cbv beta. zstep. cbv beta. zstep. cbv beta.
zstep. zstep. zstep. zstep. zstep. zstep.
rewrite le32_lbu_raw by assumption.
change (Znth 0 buf + 2 ^ 8 * Znth 1 buf + 2 ^ 16 * Znth 2 buf + 2 ^ 24 * Znth 3 buf) with (le32 buf 0).
pose proof (le32_range buf 0 (buf_all_bytesA C OK)) as RW.
zstep. zstep. zstep.
if_cases K; zify_cond K; rewrite ?(Z.mod_small (le32 buf 0) 18446744073709551616) in * by lia; [exfalso; lia|].
zstep. zstep.
apply evtF_done. unfold rd_mainA_errpost. eexists. do 23 eexists. split; [reflexivity|].
eapply errinv_pro; eassumption. }
assert (J0 : forall (y10 y11 : word),
evtF bsegs RNG (rd_mainA_errpost C 44)
(MS (mkR x1 (Z_to_bv 64 SPA) (a_gp C) (a_tp C) x5 x6 x7 (Z_to_bv 64 (a_SP C)) (Z_to_bv 64 SPA)
y10 y11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 (Z.shiftr MSVP 3 + 2147450880)) (Z_to_bv 64 (BUF + zlen buf)) x20 (Z_to_bv 64 NC) (Z_to_bv 64 TLP) (Z_to_bv 64 msv1)
(Z_to_bv 64 2147450880) (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 BUF) x28 x29 x30 x31)
(a_F C) (Z_to_bv 64 0x96be8) (a_fc C) None m1 (seg_rom bsegs))).
{ intros y10 y11. clear RDB0 CK0 SR0.
zstep. zstep. zstep. zstep. rewrite sxb_sval.
zstep. if_cases G; zify_cond G.
- zstep. zstep. if_cases G'; zify_lts G'; [| exfalso; lia]. apply J1.
- apply J1. }
clear J1.
zstep. if_cases G0; zify_cond G0; [exfalso; lia|].
zstep. zstep. zstep. rewrite sxb_sval.
zstep. if_cases G; zify_cond G.
- zstep. zstep. if_cases G'; zify_lts G'; [| exfalso; lia]. apply J0.
- apply J0.
Qed.
#[using="rc OK SH RNGS"] Lemma hd_chk_err2A : forall m1 tl0 sF e j0 j8 j16 j32 j40 j48 j64 (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x28 x29 x30 x31 : word),
u8arr bsegs m1 NC (u16s (map (Z_to_bv 64) (zero_prefix (Z.to_nat msv1) (a_rt0 C)))) ->
rw_cells bsegs m1 MSVP [C4 (Z_to_bv 64 (a_msv0 C))] -> rw_cells bsegs m1 TLP [C4 tl0] ->
bytes_at bsegs m1 BUF (map (Z_to_bv 8) buf) -> rw_cells bsegs m1 SPA (FRA_pro C j0 j8 j16 j32 j40 j48 j64) ->
stk bsegs m1 (a_lo C) SPA -> munch (rd_WA C) (a_m C) m1 -> wmono bsegs (a_m C) m1 -> mem_inv bsegs m1 ->
Z.land (le32 buf 0) 15 <= 10 ->
rloop buf msv1 (S (Z.to_nat msv1)) (rd_s0 buf msv1 (a_rt0 C)) = Ok sF ->
ERRX sF e ->
evtF bsegs RNG (rd_mainA_errpost C e)
(MS (mkR x1 (Z_to_bv 64 SPA) (a_gp C) (a_tp C) x5 x6 x7 (Z_to_bv 64 (a_SP C)) (Z_to_bv 64 SPA)
(Z_to_bv 64 NC) x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 (Z.shiftr MSVP 3 + 2147450880)) (Z_to_bv 64 (BUF + zlen buf)) x20 (Z_to_bv 64 NC) (Z_to_bv 64 TLP) (Z_to_bv 64 msv1)
(Z_to_bv 64 2147450880) (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 BUF) x28 x29 x30 x31)
(a_F C) (Z_to_bv 64 0x96bd4) (a_fc C) None m1 (seg_rom bsegs)).
Proof.
intros m1 tl0 sF e j0 j8 j16 j32 j40 j48 j64 x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x28 x29 x30 x31 ARR HMSV HTL HBUF FRM ST MU WM MI HX RL EX.
pose proof (okA_lin C OK) as (HH & HM0 & HM1 & HRT & SP16 & SPK & LO & LOA & SPA12 & SPA3 & NC0 & NC1 & N8 & MS0 & MS1 & M4
& TL0 & TL1 & T4 & BF0 & BF1 & B8 & FF0 & FF1 & F64).
pose proof RNGS as RNGS'. destruct RNGS' as (RI & RSTK & RN & RNS & RM & RMS & RT & RTS & RB & RBS).
pose proof atop_range as ATR. unfold RDA_CALLEE, KHIGH, AIMG_HI, KEND in *.
destruct (inv_shadowA C m1 OK SH MU) as (_ & _ & UT & UB).
destruct (chkB m1 BUF (BUF + zlen buf) BUF UB ltac:(lia) ltac:(lia)) as (b0 & RDB0 & CK0 & SR0).
destruct (chkB m1 BUF (BUF + zlen buf) (BUF + 3) UB ltac:(lia) ltac:(lia)) as (b3 & RDB3 & CK3 & SR3).
destruct (buf_rdA C OK m1 0 HBUF ltac:(lia)) as [RD0 R0].
destruct (buf_rdA C OK m1 1 HBUF ltac:(lia)) as [RD1 R1].
destruct (buf_rdA C OK m1 2 HBUF ltac:(lia)) as [RD2 R2].
destruct (buf_rdA C OK m1 3 HBUF ltac:(lia)) as [RD3 R3].
rewrite Z.add_0_r in RD0.
pose proof (hd_tlp_errA m1 tl0 sF e j0 j8 j16 j32 j40 j48 j64) as TLPK.
assert (J2 : forall (y12 y13 y14 y15 : word),
evtF bsegs RNG (rd_mainA_errpost C e)
(MS (mkR x1 (Z_to_bv 64 SPA) (a_gp C) (a_tp C) x5 x6 x7 (Z_to_bv 64 (a_SP C)) (Z_to_bv 64 SPA)
(Z_to_bv 64 (Z.land (le32 buf 0) 15)) (Z_to_bv 64 (le32 buf 0)) y12 y13 y14 y15 x16 x17
(Z_to_bv 64 (Z.shiftr MSVP 3 + 2147450880)) (Z_to_bv 64 (BUF + zlen buf)) x20 (Z_to_bv 64 NC) (Z_to_bv 64 TLP) (Z_to_bv 64 msv1)
(Z_to_bv 64 2147450880) (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 BUF) x28 x29 x30 x31)
(a_F C) (Z_to_bv 64 0x96c38) (a_fc C) None m1 (seg_rom bsegs))).
{ intros y12 y13 y14 y15. eapply TLPK; eassumption. }
clear TLPK.
assert (J1 : forall (y10 y11 y12 : word),
evtF bsegs RNG (rd_mainA_errpost C e)
(MS (mkR x1 (Z_to_bv 64 SPA) (a_gp C) (a_tp C) x5 x6 x7 (Z_to_bv 64 (a_SP C)) (Z_to_bv 64 SPA)
y10 y11 y12 x13 x14 x15 x16 x17
(Z_to_bv 64 (Z.shiftr MSVP 3 + 2147450880)) (Z_to_bv 64 (BUF + zlen buf)) x20 (Z_to_bv 64 NC) (Z_to_bv 64 TLP) (Z_to_bv 64 msv1)
(Z_to_bv 64 2147450880) (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 BUF) x28 x29 x30 x31)
(a_F C) (Z_to_bv 64 0x96bfc) (a_fc C) None m1 (seg_rom bsegs))).
{ intros y10 y11 y12. clear RDB0 CK0 SR0 RDB3 CK3 SR3.
zstep. cbv beta. zstep. cbv beta. zstep. cbv beta. zstep. cbv beta.
zstep. zstep. zstep. zstep. zstep. zstep.
rewrite le32_lbu_raw by assumption.
change (Znth 0 buf + 2 ^ 8 * Znth 1 buf + 2 ^ 16 * Znth 2 buf + 2 ^ 24 * Znth 3 buf) with (le32 buf 0).
pose proof (le32_range buf 0 (buf_all_bytesA C OK)) as RW.
zstep. zstep. zstep.
if_cases K; zify_cond K; rewrite ?(Z.mod_small (le32 buf 0) 18446744073709551616) in * by lia; [| exfalso; lia].
apply J2. }
clear J2.
assert (J0 : forall (y10 y11 : word),
evtF bsegs RNG (rd_mainA_errpost C e)
(MS (mkR x1 (Z_to_bv 64 SPA) (a_gp C) (a_tp C) x5 x6 x7 (Z_to_bv 64 (a_SP C)) (Z_to_bv 64 SPA)
y10 y11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 (Z.shiftr MSVP 3 + 2147450880)) (Z_to_bv 64 (BUF + zlen buf)) x20 (Z_to_bv 64 NC) (Z_to_bv 64 TLP) (Z_to_bv 64 msv1)
(Z_to_bv 64 2147450880) (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 BUF) x28 x29 x30 x31)
(a_F C) (Z_to_bv 64 0x96be8) (a_fc C) None m1 (seg_rom bsegs))).
{ intros y10 y11. clear RDB0 CK0 SR0.
zstep. zstep. zstep. zstep. rewrite sxb_sval.
zstep. if_cases G; zify_cond G.
- zstep. zstep. if_cases G'; zify_lts G'; [| exfalso; lia]. apply J1.
- apply J1. }
clear J1.
zstep. if_cases G0; zify_cond G0; [exfalso; lia|].
zstep. zstep. zstep. rewrite sxb_sval.
zstep. if_cases G; zify_cond G.
- zstep. zstep. if_cases G'; zify_lts G'; [| exfalso; lia]. apply J0.
- apply J0.
Qed.
#[using="rc OK SH RNGS"] Theorem rd_mainA_err : forall e (tl0 : word) (j0 j8 j16 j32 j40 j48 j64 : list byte) (RLO RHI : Z)
(x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x23 x28 x29 x30 x31 : word),
u8arr bsegs (a_m C) NC (u16s (map (Z_to_bv 64) (a_rt0 C))) ->
rw_cells bsegs (a_m C) MSVP [C4 (Z_to_bv 64 (a_msv0 C))] ->
rw_cells bsegs (a_m C) TLP [C4 tl0] ->
bytes_at bsegs (a_m C) BUF (map (Z_to_bv 8) buf) ->
rw_cells bsegs (a_m C) SPA (FRA_pro C j0 j8 j16 j32 j40 j48 j64) ->
stk bsegs (a_m C) (a_lo C) SPA -> mem_inv bsegs (a_m C) ->
rt_got (a_m C) -> rt_got_ric (a_m C) -> rt_shbase (a_m C) -> rt_inited (a_m C) -> rt_layout (a_m C) -> rt_real_mem (a_m C) ->
(RLO <= NC /\ NC + 2 * zlen (a_rt0 C) <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0 /\ 0 <= RLO /\ RHI <= KEND) ->
wr_at bsegs (a_m C) (shad RLO) (shad RHI - shad RLO) -> rng RNG (shad RLO) (shad RHI - shad RLO) ->
read_ncount_body8 buf msv1 (a_rt0 C) = Err e ->
evtF bsegs RNG (rd_mainA_errpost C e)
(MS (mkR x1 (Z_to_bv 64 SPA) (a_gp C) (a_tp C) x5 x6 x7 (Z_to_bv 64 (a_SP C)) (Z_to_bv 64 SPA)
x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 (Z.shiftr MSVP 3 + 2147450880)) (Z_to_bv 64 (BUF + zlen buf)) x20 (Z_to_bv 64 NC) (Z_to_bv 64 TLP) x23
(Z_to_bv 64 2147450880) (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 BUF) x28 x29 x30 x31)
(a_F C) (Z_to_bv 64 0x96bb4) (a_fc C) None (a_m C) (seg_rom bsegs)).
Proof.
intros e tl0 j0 j8 j16 j32 j40 j48 j64 RLO RHI x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x23 x28 x29 x30 x31
ARR HMSV HTL HBUF FRA0 ST MI GOT RIC SHB INI LAY REAL HULL WRH RSH RB.
pose proof (okA_lin C OK) as (HH & HM0 & HM1 & HRT & SP16 & SPK & LO & LOA & SPA12 & SPA3 & NC0 & NC1 & N8 & MS0 & MS1 & M4
& TL0 & TL1 & T4 & BF0 & BF1 & B8 & FF0 & FF1 & F64).
pose proof RNGS as RNGS'. destruct RNGS' as (RI & RSTK & RN & RNS & RM & RMS & RT & RTS & RB' & RBS).
pose proof atop_range as ATR. unfold RDA_CALLEE, KHIGH, AIMG_HI, KEND in *.
pose proof (read_body8_err_inv buf msv1 (a_rt0 C) e (buf_all_bytesA C OK) (proj1 HH) ltac:(lia) RB) as HE.
pose proof (munch_refl (rd_WA C) (a_m C)) as MU. pose proof (wmono_refl bsegs (a_m C)) as WM. unfold rd_WA, RDA_CALLEE in MU.
pose proof SH as (UN & UM & UT & UB).
assert (LWS : length (map (Z_to_bv 64) (a_rt0 C)) = length (a_rt0 C)) by apply length_map.
unfold FRA_pro in FRA0.
remember (a_m C) as m eqn:Em.
zstep.
zstep. rewrite (sx32_small (a_msv0 C)) by lia.
zstep. rewrite ?(FseWalkKit.swrap32_small msv1) by lia.
zstep. zstep. rewrite (shl32_shr31 msv1) by lia.
zstep. zstep. zstep.
set (bsA := u16s (map (Z_to_bv 64) (a_rt0 C))) in *.
assert (LA : length bsA = (2 * length (a_rt0 C))%nat) by (subst bsA; rewrite u16s_length, LWS; reflexivity).
set (n1 := Z.to_nat (2 * msv1)).
pose proof (rw_cells_of_u8arr _ _ _ _ ARR) as RA. clear ARR.
pose proof (rw_cells_split_CB bsegs _ NC [] _ bsA [] [n1; (length bsA - n1)%nat] RA ltac:(cbn [sum_nat]; lia)) as RS.
cbn [app mk_CB_cells] in RS. clear RA.
change [CB n1 (firstn n1 bsA); CB (length bsA - n1) (firstn (length bsA - n1) (skipn n1 bsA))]
with ([CB n1 (firstn n1 bsA)] ++ [CB (length bsA - n1) (firstn (length bsA - n1) (skipn n1 bsA))]) in RS.
apply rd_rw_cells_appA in RS. destruct RS as [R1 R2]. cbn [cells_size csize Nat.add] in R2.
assert (LBS : Z.of_nat (length (map (Z_to_bv 8) buf)) = zlen buf) by (rewrite length_map; reflexivity).
assert (UN1 : unpoisoned m NC (NC + 2 * msv1)) by (eapply unpoisoned_sub; [exact UN| lia| lia]).
pose proof OK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & BN & _ & _ & _ & _ & _ & _ & _ & _ & SNM & SNT & SNB & _).
destruct HULL as (HU1 & HU2 & HU3 & HU4 & HU5 & HU6).
call (amemset_specZ NC (2 * msv1) 0 SPA).
all: first [ lazymatch goal with
| |- evtF _ _ _ _ => idtac
| |- mem_inv _ _ => assumption
| |- stk _ _ _ _ => eassumption
| |- rw_cells _ _ NC _ => exact R1
| |- rw_cells _ _ _ _ => assumption
| |- app_blk _ _ => apply ablk_app_blk; [eapply ablk_sub; [exact BN| lia| lia]| lia]
| |- unpoisoned _ _ _ => exact UN1
| |- wr_at _ _ _ _ => eassumption
| |- rng _ _ _ => eapply rng_sub'; [exact RSTK| lia]
| |- Z_to_bv 64 _ = Z_to_bv 64 _ => reflexivity
| |- _ => unfold KHIGH, KEND in *; lia
end | lazymatch goal with |- ?G => idtac "FAILED:" G end ].
lazymatch goal with
| P : rw_cells bsegs ?mm NC [CB (Z.to_nat (2 * msv1)) (repeat (Z_to_bv 8 0) (Z.to_nat (2 * msv1)))] |- _ =>
rename mm into m2; rename P into P0
end.
assert (ARR : u8arr bsegs m2 NC (u16s (map (Z_to_bv 64) (zero_prefix (Z.to_nat msv1) (a_rt0 C))))).
{ pose proof (proj2 (rd_rw_cells_appA bsegs m2 NC [CB n1 (repeat (Z_to_bv 8 0) n1)]
[CB (length bsA - n1) (firstn (length bsA - n1) (skipn n1 bsA))]) (conj P0 R2)) as RJ.
pose proof (rw_cells_merge bsegs m2 NC [] [CB n1 (repeat (Z_to_bv 8 0) n1); CB (length bsA - n1) (firstn (length bsA - n1) (skipn n1 bsA))] [] RJ) as RMg.
cbn [app] in RMg.
apply u8arr_of_rw_cells in RMg. cbn [cells_bytes cbytes app] in RMg. rewrite app_nil_r in RMg.
rewrite firstn_all2 in RMg by (rewrite length_skipn; lia).
replace n1 with (2 * Z.to_nat msv1)%nat in RMg by (subst n1; lia).
subst bsA. rewrite u16s_zero_prefix in RMg by lia. exact RMg. }
clear R2 P0.
destruct HE as [(HX & ->) | (HX & sF & RL & EX)];
[eapply (hd_chk_err1A m2 tl0 j0 j8 j16 j32 j40 j48 j64) | eapply (hd_chk_err2A m2 tl0 sF e j0 j8 j16 j32 j40 j48 j64)];
try eassumption.
all: try (unfold rd_WA, RDA_CALLEE; rewrite <- Em; eassumption).
all: try (rewrite <- Em; eassumption).
Qed.
End Hdr.
End CANSEC1.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
