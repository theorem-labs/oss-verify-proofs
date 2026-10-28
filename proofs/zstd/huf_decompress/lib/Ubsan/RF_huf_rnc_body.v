(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas FseAbs FseReaderRT FseReadSound.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKit FseRdKit FseRdKit2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RF_huf_tbl_iface RF_huf_rnc_base RF_huf_rnc_base2 RF_huf_rnc_mem RF_huf_rnc_loop RF_huf_rnc_hdr.
Import ListNotations.
Open Scope Z_scope.

Section Body.
  Variable C : rdctx.
  Hypothesis OK : rd_ok C.

  Notation buf := (c_buf C).
  Notation msv1 := (c_msv0 C + 1).
  Notation BUF := (c_BUF C).
  Notation NC := (c_NC C).
  Ltac cbnR := cbn [r_nc r_ip r_bitStream r_bitCount r_charnum r_remaining r_threshold r_nbBits r_previous0] in *.

  (* [comment removed for export] *)
  Theorem rd_body8 : forall (tl0 : word) (t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 : word),
    u8arr usegs (c_m C) NC (u16s (map (Z_to_bv 64) (c_rt0 C))) ->
    rw_cells usegs (c_m C) (c_MSVP C) [C4 (Z_to_bv 64 (c_msv0 C))] ->
    rw_cells usegs (c_m C) (c_TLP C) [C4 tl0] ->
    bytes_at usegs (c_m C) BUF (map (Z_to_bv 8) buf) ->
    stk usegs (c_m C) (c_lo C) (c_SP C) -> mem_inv usegs (c_m C) ->
    evt usegs (rd_body_posth C (read_ncount_body8 buf msv1 (c_rt0 C)))
      (MS (mkR (c_ra C) (Z_to_bv 64 (c_SP C)) (c_gp C) (c_tp C) t0 t1 t2 (c_s0 C) (c_s1 C)
               (Z_to_bv 64 NC) (Z_to_bv 64 (c_MSVP C)) (Z_to_bv 64 (c_TLP C)) (Z_to_bv 64 BUF) (Z_to_bv 64 (zlen buf)) a5 a6 a7
               (c_s2 C) (c_s3 C) (c_s4 C) (c_s5 C) (c_s6 C) (c_s7 C) (c_s8 C) (c_s9 C) (c_s10 C) (c_s11 C) t3 t4 t5 t6)
          (c_F C) (Z_to_bv 64 0x1e7b8) (c_fc C) None (c_m C) (seg_rom usegs)).
Proof.
intros tl0 t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 ARR HMSV HTL HBUF ST MI.
pose proof OK as OK'. destruct OK' as (HH & FBY & HM0 & HM1 & RSP & LO & LO0 & (HN0 & HN1) & (HB0 & HB1) & (HV0 & HV1) & (HT0 & HT1) & SNS & SMS & STS & SBS & SNM & SNT & SNB & SMT & SMB & STB & (HNP & HNA) & (HVP & HVA) & (HTP & HTA) & HBP).
unfold RD_STACK in *.
pose proof (munch_refl (rd_W C) (c_m C)) as MU. pose proof (wmono_refl usegs (c_m C)) as WM. unfold rd_W, RD_STACK in MU.
assert (LWS : length (map (Z_to_bv 64) (c_rt0 C)) = length (c_rt0 C)) by apply length_map.
assert (LBS : zlen (map (Z_to_bv 8) buf) = zlen buf) by (rewrite length_map; reflexivity).
remember (c_m C) as m eqn:Em.
carve_frame 128%nat ST.
do 14 zstep.
zstep. zstep. if_cases K0; zify_cond K0; [exfalso; lia|].
do 6 zstep.
zstep. if_cases K1; zify_cond K1;
[exfalso; rewrite (proj2 (Z.ltb_lt 0 BUF) ltac:(lia)), (proj2 (Z.ltb_ge (BUF + zlen buf) 1) ltac:(lia)) in K1; vm_compute in K1; discriminate K1|].
zstep. if_cases K2; zify_cond K2; [exfalso; lia|].
assert (LV3 : Z.land (c_MSVP C) 3 = c_MSVP C mod 4) by (change 3 with (Z.ones 2); apply Z.land_ones; lia).
zstep. zstep. if_cases K3; zify_cond K3; [exfalso; lia|].
do 3 zstep.
if_cases K; zify_cond K; [| exfalso; lia].
zstep. rewrite (sx32_small (c_msv0 C)) by lia.
zstep. rewrite (swrap32_small msv1) by lia.
zstep. zstep. rewrite (shl32_shr31 msv1) by lia.
zstep. zstep. zstep.
set (bsA := u16s (map (Z_to_bv 64) (c_rt0 C))) in *.
assert (LA : length bsA = (2 * length (c_rt0 C))%nat) by (subst bsA; rewrite u16s_length, LWS; reflexivity).
set (n1 := Z.to_nat (2 * msv1)).
pose proof (rw_cells_of_u8arr _ _ _ _ ARR) as RA. clear ARR.
pose proof (rw_cells_split_CB usegs _ NC [] _ bsA [] [n1; (length bsA - n1)%nat] RA ltac:(cbn [sum_nat]; lia)) as RS.
cbn [app mk_CB_cells] in RS. clear RA.
change [CB n1 (firstn n1 bsA); CB (length bsA - n1) (firstn (length bsA - n1) (skipn n1 bsA))]
with ([CB n1 (firstn n1 bsA)] ++ [CB (length bsA - n1) (firstn (length bsA - n1) (skipn n1 bsA))]) in RS.
apply rd_rw_cells_app in RS. destruct RS as [R1 R2]. cbn [cells_size csize Nat.add] in R2.
call (rd_memset_specZ NC (2 * msv1) 0); [exact R1 | exact MI | reflexivity | reflexivity | reflexivity | lia | lia | lia |].
assert (ARR : u8arr usegs x13 NC (u16s (map (Z_to_bv 64) (zero_prefix (Z.to_nat msv1) (c_rt0 C))))).
{ pose proof (proj2 (rd_rw_cells_app usegs x13 NC [CB n1 (repeat (Z_to_bv 8 0) n1)]
[CB (length bsA - n1) (firstn (length bsA - n1) (skipn n1 bsA))]) (conj POST R2)) as RJ.
pose proof (rw_cells_merge usegs x13 NC [] [CB n1 (repeat (Z_to_bv 8 0) n1); CB (length bsA - n1) (firstn (length bsA - n1) (skipn n1 bsA))] [] RJ) as RM. cbn [app] in RM.
apply u8arr_of_rw_cells in RM. cbn [cells_bytes cbytes app] in RM. rewrite app_nil_r in RM.
rewrite firstn_all2 in RM by (rewrite length_skipn; lia).
replace n1 with (2 * Z.to_nat msv1)%nat in RM by (subst n1; lia).
subst bsA. rewrite u16s_zero_prefix in RM by lia. exact RM. }
clear POST R2.
zstep. if_cases K4; zify_cond K4; [exfalso; lia|].
subst m.
eapply (rd_header C OK x13 tl0); try eassumption.
Qed.
End Body.
