(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas FseReadSound.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKit FseRdKit FseRdKit2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RF_huf_tbl_iface RF_huf_rnc_base RF_huf_rnc_base2 RF_huf_rnc_loop.
Import ListNotations.
Open Scope Z_scope.

Section Hdr.
  Variable C : rdctx.
  Hypothesis OK : rd_ok C.

  Notation buf := (c_buf C).
  Notation msv1 := (c_msv0 C + 1).
  Notation BUF := (c_BUF C).
  Notation NC := (c_NC C).
  Ltac rd_err_epi e :=
    repeat zstep;
    lazymatch goal with FR : rw_cells _ _ (c_SP C + -128) _, ST : stk _ _ _ (c_SP C + -128) |- _ =>
      release_frame FR ST (c_SP C) end;
    let ne := eval vm_compute in (- e) in
    replace (Z_to_bv 64 ne) with (Z_to_bv 64 (2^64 - e)) by (apply Z_to_bv_eqm; reflexivity);
    apply evt_done; unfold rd_body_posth, rd_W, RD_STACK;
    do 14 eexists; exists (2^64 - e); eexists; split; [reflexivity|];
    split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|];
    unfold rd_res_ok, rd_exit_model; cbn [r_remaining r_charnum r_bitCount r_nc r_ip].
  Ltac cbnR := cbn [r_nc r_ip r_bitStream r_bitCount r_charnum r_remaining r_threshold r_nbBits r_previous0] in *.

  (* [comment removed for export] *)
  Lemma rd_header : forall m1 tl0 junk (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    u8arr usegs m1 NC (u16s (map (Z_to_bv 64) (zero_prefix (Z.to_nat msv1) (c_rt0 C)))) ->
    bytes_at usegs m1 BUF (map (Z_to_bv 8) buf) ->
    rw_cells usegs m1 (c_MSVP C) [C4 (Z_to_bv 64 (c_msv0 C))] -> rw_cells usegs m1 (c_TLP C) [C4 tl0] ->
    rw_cells usegs m1 (c_SP C + -128) [CB 24 junk; C8 (c_s11 C); C8 (c_s10 C); C8 (c_s9 C); C8 (c_s8 C); C8 (c_s7 C); C8 (c_s6 C);
    C8 (c_s5 C); C8 (c_s4 C); C8 (c_s3 C); C8 (c_s2 C); C8 (c_s1 C); C8 (c_s0 C); C8 (c_ra C)] ->
    stk usegs m1 (c_lo C) (c_SP C + -128) -> munch (rd_W C) (c_m C) m1 -> wmono usegs (c_m C) m1 -> mem_inv usegs m1 ->
    evt usegs (rd_body_posth C (read_ncount_body8 buf msv1 (c_rt0 C)))
    (MS (mkR x1 (Z_to_bv 64 (c_SP C + -128)) (c_gp C) (c_tp C) x5 x6 x7 (Z_to_bv 64 BUF) (Z_to_bv 64 (c_MSVP C))
    x10 x11 x12 x13 x14 x15 x16 x17
    (Z_to_bv 64 NC) (Z_to_bv 64 (c_TLP C)) (Z_to_bv 64 msv1) (Z_to_bv 64 (BUF + zlen buf)) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
    (c_F C) (Z_to_bv 64 0x1e898) (c_fc C) None m1 (seg_rom usegs)).
Proof.
intros m1 tl0 junk x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 ARR HBUF HMSV HTL FR ST MU WM MI.
pose proof OK as OK'. destruct OK' as (HH & FBY & HM0 & HM1 & RSP & LO & LO0 & (HN0 & HN1) & (HB0 & HB1) & (HV0 & HV1) & (HT0 & HT1) & SNS & SMS & STS & SBS & SNM & SNT & SNB & SMT & SMB & STB & (HNP & HNA) & (HVP & HVA) & (HTP & HTA) & HBP).
unfold RD_STACK in *.
assert (LNC : length (zero_prefix (Z.to_nat msv1) (c_rt0 C)) = length (c_rt0 C))
by (generalize (Z.to_nat msv1) (c_rt0 C); intros n; induction n as [|n IH]; intros [|a l]; cbn; try reflexivity; rewrite IH; reflexivity).
unfold rd_W, RD_STACK in MU.
remember (read_ncount_body8 buf msv1 (c_rt0 C)) as R eqn:ER.
rewrite (body8_eq buf msv1 (c_rt0 C)) in ER by lia.
destruct (buf_rd C OK m1 0 HBUF ltac:(lia)) as [RD0 R0].
destruct (buf_rd C OK m1 1 HBUF ltac:(lia)) as [RD1 R1].
destruct (buf_rd C OK m1 2 HBUF ltac:(lia)) as [RD2 R2].
destruct (buf_rd C OK m1 3 HBUF ltac:(lia)) as [RD3 R3].
rewrite Z.add_0_r in RD0.
zstep. cbv beta. zstep. cbv beta. zstep. cbv beta. zstep. cbv beta.
zstep. zstep. zstep. zstep. zstep. zstep.
rewrite le32_lbu_raw by assumption.
change (Znth 0 buf + 2 ^ 8 * Znth 1 buf + 2 ^ 16 * Znth 2 buf + 2 ^ 24 * Znth 3 buf) with (le32 buf 0).
pose proof (le32_range buf 0 (buf_all_bytes C OK)) as RW.
set (W := le32 buf 0) in *.
zstep.
remember (Z.land W 15) as x eqn:Ex.
assert (X0 : 0 <= x < 16) by (subst x; rewrite land_15; apply Z.mod_pos_bound; lia).
zstep. zstep.
if_cases K; zify_cond K.
2:{ assert (E10 : (10 <? x) = true) by (apply Z.ltb_lt; lia). rewrite E10 in ER. subst R.
rd_err_epi 44. split; [lia|]. cbv iota. unfold ZSTD_error_tableLog_tooLarge. lia. }
assert (P5 : 32 <= 2 ^ (x + 5) <= 32768).
{ split; [change 32 with (2^5)| change 32768 with (2^15)]; apply Z.pow_le_mono_r; lia. }
zstep. if_cases G; zify_cond G; [exfalso; lia|].
assert (LT3 : Z.land (c_TLP C) 3 = c_TLP C mod 4) by (change 3 with (Z.ones 2); apply Z.land_ones; lia).
zstep. zstep. if_cases G2; zify_cond G2; [exfalso; lia|].
do 18 zstep.
zstep.
zstep. rewrite ?(Z.mod_small x 32) by lia. rewrite Z.shiftl_mul_pow2 by lia.
replace (32 * 2 ^ x) with (2 ^ (x + 5)) by (rewrite Z.pow_add_r by lia; change (2^5) with 32; lia).
rewrite (swrap32_small (2 ^ (x + 5))) by lia.
do 6 zstep. rewrite (swrap32_small (2 ^ (x + 5) + 1)) by lia.
zstep. zstep. zstep. zstep. if_false.
replace (Z_to_bv 64 (-2147483648)) with (Z_to_bv 64 18446744071562067968) by (apply bv_eq; reflexivity).
subst x.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
assert (INV0 : rd_inv C mm (r_nc (rd_s0 buf msv1 (c_rt0 C))) (Z_to_bv 64 (c_msv0 C)) (Z_to_bv 64 (Z.land W 15 + 5))) end.
{ unfold rd_s0. cbv zeta. cbnR. unfold rd_inv, rd_W, RD_STACK.
split; [exact ARR|]. split; [exact LNC|]. split; [exact HBUF|]. split; [exact HMSV|]. split; [exact HTL|].
split; [do 2 eexists; exact FR|]. split; [exact ST|]. split; [exact MU|]. split; [exact WM| exact MI]. }
assert (HX : Z.land W 15 <= 10) by lia.
destruct (rd_s0_inv buf msv1 (c_rt0 C) (buf_all_bytes C OK) (proj1 HH) ltac:(lia) HX) as (HC0 & HP0 & HB0').
destruct (rloop_total buf (buf_all_bytes C OK) ltac:(unfold FseNCount.Zlength; lia) msv1 (c_rt0 C) ltac:(unfold FseNCount.Zlength; lia) (Z.land W 15 + 5) ltac:(lia)
(S (Z.to_nat msv1)) (rd_s0 buf msv1 (c_rt0 C)) HC0 HP0 HB0' ltac:(unfold rd_s0; cbn [r_charnum]; lia)) as (sF & RL & _).
assert (E10 : (10 <? Z.land W 15) = false) by (apply Z.ltb_ge; lia). rewrite E10, RL in ER. cbn [bind] in ER. subst R.
eapply (loop_run' C OK (Z.land W 15 + 5) ltac:(lia) (S (Z.to_nat msv1)) (rd_s0 buf msv1 (c_rt0 C)) sF _ (Z_to_bv 64 (c_msv0 C)));
try eassumption; try reflexivity.
all: unfold rd_s0; cbv zeta; cbnR; fold W.
all: try (f_equal; lia).
rewrite Z.shiftr_div_pow2 by lia. f_equal. symmetry. apply swrap32_small.
assert (0 <= W / 2^4 < 2^28) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]). lia.
Qed.
End Hdr.
