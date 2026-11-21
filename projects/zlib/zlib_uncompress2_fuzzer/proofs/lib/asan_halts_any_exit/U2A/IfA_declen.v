(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.Lib Require Import Arr Bytes ZBridge.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.AsanW Require Import AImg.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.zspec.zmodel Require Import ZIface InflateState Inftrees InflateInv InflateInvTab.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.U2A Require Import U2AShadow U2AArr U2AKit U2AObj InfATables ItAKit IfAPure IfA_base IfAKit.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= first [ solve_load_base | solve_load_sh0 | solve_load_image ].
Local Ltac acc_hint ::= first [ acc_hint_sh | acc_hint_var ].

Section CANSEC1. Context {rc : runConstT}.
Section P.
  Variables (RNG : footprint) (FR : bvmap 5 word) (fc : bv 32) (gp tp : word).
  Variables (SP lo Zs S D n OB osz Wd wsz whave wnext lb db la na da nd bo : Z) (rdL rdD fw : Z -> Z) (payload : list Z) (m1 : amem).
  Hypothesis CX : if_ctx RNG SP lo Zs S D n OB osz Wd wsz whave wnext lb db la na da nd bo rdL rdD fw payload m1.
  Notation ST := (fms SP Zs S D n OB osz lb la da gp tp FR fc).

  Definition declen_post (m : amem) (ci co B : Z) : machine_state -> Prop :=
    fun ms' => exists (x1 x6 x10 x13 x15 x16 x21 : word) (k hold' bits' : Z),
      0 <= k < na /\ 0 <= bits' /\ 1 <= B - bits' <= 15 /\ 0 <= hold' < 2 ^ bits' /\
      ((ms' = ST x1 x6 x10 (Z_to_bv 64 (la + 4 * k)) x13 x15 x16 x21 ci co hold' bits' 0x96dac m
        /\ code_val (rdL k) < 256)
       \/ (ms' = ST x1 x6 x10 (Z_to_bv 64 (la + 4 * k)) (Z_to_bv 64 (code_op (rdL k))) x15 x16 x21 ci co hold' bits' 0x96dec m
           /\ 16 <= code_op (rdL k) <= 21 /\ 3 <= code_val (rdL k) /\ code_val (rdL k) + 2 ^ (code_op (rdL k) - 16) - 1 <= 258)
       \/ (exists op, ms' = ST x1 x6 x10 (Z_to_bv 64 (la + 4 * k)) (Z_to_bv 64 op) x15 x16 x21 ci co hold' bits' 0x9775c m
           /\ 0 <= op < 256)).

  Lemma if_dolen : forall (m : amem) (v0 v24 v48 v56 : word) (sd : sdc) (id : idc) (ni ai no ao msg mode hw bw : word) (fo : Z -> Z)
      (x1 x6 x10 x15 x16 x21 : word) (ci co hold bits B k maxb : Z),
    if_inv SP Zs S OB osz bo wsz whave wnext Wd la da lb db m1 m v0 v24 v48 v56 sd id ni ai no ao msg mode hw bw fo ->
    0 <= k < na -> term_ok LENS maxb (rdL k) = true ->
    code_bits (rdL k) <= bits -> bits <= B -> B - bits + maxb <= 15 -> bits <= 40 -> 0 <= hold < 2 ^ bits ->
    evtF asegs RNG (declen_post m ci co B)
      (ST x1 x6 x10 (Z_to_bv 64 (la + 4 * k)) (Z_to_bv 64 (code_bits (rdL k))) x15 x16 x21 ci co hold bits 0x96d04 m).
  Proof using All.
    intros until maxb. intros INV HK TM CB BB BM B40 HOLD.
    open_fctx CX. open_finv INV. unfold fms, declen_post.
    clear ZSD ZOD SOD WSZ WNX WIN TOKL TOKD SANE FWR WH WN BO0 DB OSZ Z0 ZL S0 SL OB0 OBL D1 DL D8 PAYB PAYR PAYN UNP DJD DJP RD RSD
          TDB TD4 TD0 TDN0 TDHI RTD TDR DJTD SHTD RSTD DJSTD TDS1 TDS2 SHO DJO ROB RSOB FRM STRM SSC OUT FOR SHZ DJZ SHS DJS RZ RSZ RS RSS.
    assert (TLC : bytes_at asegs m la (u32s (fws rdL (Z.to_nat na)))).
    { eapply bytes_at_transport; [exact TLB| exact MU|]. rewrite u32s_length, fws_length.
      replace (Z.of_nat (4 * Z.to_nat na)) with (4 * na) by lia. exact DJTL. }
    pose proof (TLR k HK) as RK.
    pose proof (code_op_range (rdL k)) as ROP. pose proof (code_bits_range (rdL k)) as RCB. pose proof (code_val_range (rdL k)) as RCV.
    apply term_ok_LENS in TM as (TB & CL).
    pose proof (pow2_40 bits ltac:(lia)) as P40.
    pose proof (code_read_op asegs m la (fws rdL (Z.to_nat na)) k (rdL k) TLC (f32arr_nth rdL (Z.to_nat na) k ltac:(lia)) ltac:(lia) RK) as RDOP.
    zs. cbv beta. rewrite (u8_val _ ROP).
    zs. setreg 22 (Z_to_bv 64 (hold / 2 ^ code_bits (rdL k))) ltac:(rewrite srl_div by lia; reflexivity).
    zs. setreg 23 (Z_to_bv 64 (bits - code_bits (rdL k))) ltac:(rewrite swrap32_small by lia; reflexivity).
    pose proof (drop_bound hold bits (code_bits (rdL k)) ltac:(lia) HOLD) as HB.
    destruct CL as [(Hop0 & Hv) | [(Hop16 & Hv3 & Hv258 & Hop21) | (H64 & H16)]].
    -
      rewrite Hop0. zs.
      apply evtF_done. do 7 eexists. exists k, (hold / 2 ^ code_bits (rdL k)), (bits - code_bits (rdL k)).
      split; [lia|]. split; [lia|]. split; [lia|]. split; [exact HB|]. left. split; [reflexivity| exact Hv].
    -
      pose proof (op_base_tests (code_op (rdL k)) ltac:(lia)) as (T16 & T64 & T32 & T240 & T15 & Tnz).
      rewrite Z.shiftl_1_l in Hv258.
      zs. zbr K0.
      zs. rewrite T16. zs. rewrite (land_255_id _ ROP). zs.
      apply evtF_done. do 3 eexists. exists (Z_to_bv 64 0). do 3 eexists. exists k, (hold / 2 ^ code_bits (rdL k)), (bits - code_bits (rdL k)).
      split; [lia|]. split; [lia|]. split; [lia|]. split; [exact HB|]. right. left. split; [reflexivity| lia].
    -
      assert (Tnz : code_op (rdL k) <> 0) by (intros E; rewrite E in H64; apply H64; reflexivity).
      zs. zbr K0.
      zs. rewrite H16. zs. rewrite (land_255_id _ ROP). zs. zs. zs. zbr K1.
      apply evtF_done. do 3 eexists. exists (Z_to_bv 64 0). do 3 eexists. exists k, (hold / 2 ^ code_bits (rdL k)), (bits - code_bits (rdL k)).
      split; [lia|]. split; [lia|]. split; [lia|]. split; [exact HB|]. right. right. exists (code_op (rdL k)). split; [reflexivity| exact ROP].
  Qed.

  Lemma if_declen : forall (m : amem) (v0 v24 v48 v56 : word) (sd : sdc) (id : idc) (ni ai no ao msg mode hw bw : word) (fo : Z -> Z)
      (x1 x6 x10 x11 x13 x15 x16 x21 : word) (ci co hold bits : Z),
    if_inv SP Zs S OB osz bo wsz whave wnext Wd la da lb db m1 m v0 v24 v48 v56 sd id ni ai no ao msg mode hw bw fo ->
    15 <= bits <= 40 -> 0 <= hold < 2 ^ bits ->
    evtF asegs RNG (declen_post m ci co bits) (ST x1 x6 x10 x11 x13 x15 x16 x21 ci co hold bits 0x96cd0 m).
  Proof using All.
    intros until bits. intros INV BITS HOLD. pose proof INV as INV0.
    open_fctx CX. open_finv INV. unfold fms.
    clear ZSD ZOD SOD WSZ WNX WIN TOKD SANE FWR WH WN BO0 DB OSZ Z0 ZL S0 SL OB0 OBL D1 DL D8 PAYB PAYR PAYN UNP DJD DJP RD RSD
          TDB TD4 TD0 TDN0 TDHI RTD TDR DJTD SHTD RSTD DJSTD TDS1 TDS2 SHO DJO ROB RSOB FRM STRM SSC OUT FOR SHZ DJZ SHS DJS RZ RSZ RS RSS.
    assert (TLC : bytes_at asegs m la (u32s (fws rdL (Z.to_nat na)))).
    { eapply bytes_at_transport; [exact TLB| exact MU|]. rewrite u32s_length, fws_length.
      replace (Z.of_nat (4 * Z.to_nat na)) with (4 * na) by lia. exact DJTL. }
    pose proof (pow2_40 bits ltac:(lia)) as P40. pose proof (pow2_15 lb ltac:(lia)) as PLB.
    pose proof (mod_pow2_bound hold lb ltac:(lia)) as RI1.
    remember (hold mod 2 ^ lb) as i1 eqn:EI1.
    pose proof (tab_root_entry LENS rdL lb na i1 TOKL RI1) as (HB1 & _ & HEXT & CASES).
    assert (HK : 0 <= i1 < na) by lia.
    pose proof (TLR i1 HK) as RK.
    pose proof (code_op_range (rdL i1)) as ROP. pose proof (code_bits_range (rdL i1)) as RCB. pose proof (code_val_range (rdL i1)) as RCV.
    zs. setreg 10 (Z_to_bv 64 i1) ltac:(rewrite land_mask_mod by lia; rewrite EI1; reflexivity). clear EI1.
    zs. setreg 10 (Z_to_bv 64 (4 * i1)) ltac:(rewrite shl2; reflexivity).
    zs.
    pose proof (code_read_bits asegs m la (fws rdL (Z.to_nat na)) i1 (rdL i1) TLC (f32arr_nth rdL (Z.to_nat na) i1 ltac:(lia)) ltac:(lia) RK) as RDB.
    zrunb [0x96d00]. cbv beta. rewrite (u8_val _ RCB). zs.
    destruct CASES as [[NL TM] | (L1 & L2 & L3 & L4 & SUB)].
    -
      eapply (if_dolen m v0 v24 v48 v56 sd id ni ai no ao msg mode hw bw fo _ _ _ _ _ _ ci co hold bits bits i1 lb INV0 HK TM); lia.
    -
      pose proof (op_link_tests (code_op (rdL i1)) ltac:(lia)) as (T16 & T64 & T240 & Tnz).
      pose proof (pow2_15 (code_op (rdL i1)) ltac:(lia)) as HPO.
      pose proof (code_read_op asegs m la (fws rdL (Z.to_nat na)) i1 (rdL i1) TLC (f32arr_nth rdL (Z.to_nat na) i1 ltac:(lia)) ltac:(lia) RK) as RDOP.
      pose proof (code_read_val asegs m la (fws rdL (Z.to_nat na)) i1 (rdL i1) TLC (f32arr_nth rdL (Z.to_nat na) i1 ltac:(lia)) ltac:(lia) RK) as RDV.
      zs. cbv beta. rewrite (u8_val _ ROP).
      pose proof (drop_bound hold bits (code_bits (rdL i1)) ltac:(lia) HOLD) as HB.
      remember (hold / 2 ^ code_bits (rdL i1)) as h1 eqn:EH1.
      zs. setreg 22 (Z_to_bv 64 h1) ltac:(rewrite srl_div by lia; rewrite EH1; reflexivity). clear EH1.
      zs. setreg 23 (Z_to_bv 64 (bits - code_bits (rdL i1))) ltac:(rewrite swrap32_small by lia; reflexivity).
      zs. zbr K0.
      zs. rewrite T16. zs. rewrite (land_255_id _ ROP). zs. zs. rewrite T64. zs.
      zrunb [0x96d40]. rewrite zx16_small by lia.
      zs. zs. rewrite mask_sllw by lia.
      pose proof (mod_pow2_bound h1 (code_op (rdL i1)) ltac:(lia)) as RJ.
      remember (h1 mod 2 ^ code_op (rdL i1)) as j eqn:EJ.
      pose proof (pow2_40 (bits - code_bits (rdL i1)) ltac:(lia)) as P40'.
      zs. setreg 11 (Z_to_bv 64 j) ltac:(rewrite land_mask_mod by lia; rewrite ?(Z.mod_small h1 18446744073709551616) by lia; rewrite EJ; reflexivity). clear EJ.
      zs. rewrite shl2. zs. rewrite shl2. zs. zs.
      destruct (SUB j RJ) as [NL2 TM2].
      assert (HK2 : 0 <= code_val (rdL i1) + j < na) by lia.
      remember (code_val (rdL i1) + j) as k2 eqn:EK2.
      setreg 11 (Z_to_bv 64 (la + 4 * k2)) ltac:(f_equal; lia).
      pose proof (TLR _ HK2) as RK2. pose proof (code_bits_range (rdL k2)) as RCB2.
      pose proof (term_ok_bits _ _ _ TM2) as TB2.
      pose proof (code_read_bits asegs m la (fws rdL (Z.to_nat na)) k2 (rdL k2) TLC (f32arr_nth rdL (Z.to_nat na) k2 ltac:(lia)) ltac:(lia) RK2) as RDB2.
      assert (F1 : code_bits (rdL k2) <= bits - code_bits (rdL i1)) by lia.
      assert (F2 : bits - (bits - code_bits (rdL i1)) + (15 - lb) <= 15) by lia.
      clear EK2 SUB RJ L1 L2 L3 L4 T16 T64 T240 Tnz HPO RDOP RDV RDB K0 HEXT RK ROP RCB RCV NL2 PLB P40 P40' RI1.
      zrunb [0x96d80]. cbv beta. rewrite (u8_val _ RCB2). zs.
      eapply (if_dolen m v0 v24 v48 v56 sd id ni ai no ao msg mode hw bw fo _ _ _ _ _ _ ci co _ _ bits _ (15 - lb) INV0 HK2 TM2); lia.
  Qed.
End P.
End CANSEC1.
