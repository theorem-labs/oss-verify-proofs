(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Lib Require Import Arr Bytes ZBridge.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.BothW Require Import BImg.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel Require Import ZIface InflateState Inftrees InflateInv InflateInvTab.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2A Require Import U2AShadow U2AArr U2AKit ItAKit IfAPure IfAStore.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2A Require Import U2AObj.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U3B Require Import U2BObj InfBTables IfBTac IfB_base IfBKit IfB_lenb.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
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
  Variables (sd : sdc) (id : idc) (ni ai no ao msg mode hw bw : word).
  Hypothesis CX : if_ctx RNG SP lo Zs S D n OB osz Wd wsz whave wnext lb db la na da nd bo rdL rdD fw payload m1.
  Notation LST := (lst FR fc gp tp SP Zs S D n OB osz la da).
  Notation INV m fo := (if_inv SP Zs S OB osz bo wsz whave wnext Wd la da lb db m1 m sd id ni ai no ao msg mode hw bw fo).

  Definition decdist_post (m : amem) (len ci co B : Z) : machine_state -> Prop :=
    fun ms' => exists (x5 x6 x7 x10 x11 x14 x24 x28 x29 x30 : word) (hold' bits' : Z),
      0 <= bits' /\ 1 <= B - bits' <= 15 /\ 0 <= hold' < 2 ^ bits' /\
      ((exists k, ms' = LST x5 x6 x7 x10 (Z_to_bv 64 (da + 4 * k)) (Z_to_bv 64 (code_op (rdD k))) x24 x28 x29 x30 len ci co hold' bits' 0x984f4 m
                  /\ x11 = Z_to_bv 64 (da + 4 * k) /\ x14 = Z_to_bv 64 (code_op (rdD k)) /\ 0 <= k < nd
                  /\ 16 <= code_op (rdD k) <= 29 /\ 1 <= code_val (rdD k) /\ code_val (rdD k) + 2 ^ (code_op (rdD k) - 16) - 1 <= 32768)
       \/ ms' = LST x5 x6 x7 x10 x11 x14 x24 x28 x29 x30 len ci co hold' bits' 0x98d20 m).

  Local Ltac dodist_prefix RCB ROP :=
    zs; zs; zs; zs; zs;
    zs; cbv beta; rewrite (u8_val _ RCB);
    zs; pc_dec_ub;
    zs; zs; zs; zs;
    zs; cbv beta; rewrite (u8_val _ ROP).

  Lemma if_dodist : forall (m : amem) (fo : Z -> Z) (x5 x6 x7 x10 x14 x24 x28 x29 x30 : word) (len ci co hold bits B k maxb : Z),
    INV m fo ->
    0 <= k < nd -> term_ok DISTS maxb (rdD k) = true ->
    code_bits (rdD k) <= bits -> bits <= B -> B - bits + maxb <= 15 -> bits <= 40 -> 0 <= hold < 2 ^ bits ->
    evtF bsegs RNG (decdist_post m len ci co B)
      (LST x5 x6 x7 x10 (Z_to_bv 64 (da + 4 * k)) x14 x24 x28 x29 x30 len ci co hold bits 0x98434 m).
  Proof using All.
    intros until maxb. intros INV HK TM CB BB BM B40 HOLD.
    open_fctx CX. open_finv INV. unfold lst, gms, xms, decdist_post.
    clear ZSD ZOD SOD WSZ WNX WIN TOKL TOKD SANE FWR WH WN BO0 LB OSZ Z0 ZL S0 SL OB0 OBL D1 DL D8 PAYB PAYR PAYN UNP DJD DJP RD RSD
          TLB TL4 TL0 TLN0 TLHI RTL TLR DJTL SHTL RSTL DJSTL TLS1 TLS2 SHO DJO ROB RSOB FRM STRM SSC OUT FOR SHZ DJZ SHS DJS RZ RSZ RS RSS.
    assert (TDC : bytes_at bsegs m da (u32s (fws rdD (Z.to_nat nd)))).
    { eapply bytes_at_transport; [exact TDB| exact MU|]. rewrite u32s_length, fws_length.
      replace (Z.of_nat (4 * Z.to_nat nd)) with (4 * nd) by lia. exact DJTD. }
    pose proof (TDR k HK) as RK.
    pose proof (code_op_range (rdD k)) as ROP. pose proof (code_bits_range (rdD k)) as RCB. pose proof (code_val_range (rdD k)) as RCV.
    apply term_ok_DISTS in TM as (TB & CL).
    pose proof (pow2_40 bits ltac:(lia)) as P40.
    pose proof (code_read_bits bsegs m da (fws rdD (Z.to_nat nd)) k (rdD k) TDC (f32arr_nth rdD (Z.to_nat nd) k ltac:(lia)) ltac:(lia) RK) as RDB.
    pose proof (code_read_op bsegs m da (fws rdD (Z.to_nat nd)) k (rdD k) TDC (f32arr_nth rdD (Z.to_nat nd) k ltac:(lia)) ltac:(lia) RK) as RDOP.
    pose proof (drop_bound hold bits (code_bits (rdD k)) ltac:(lia) HOLD) as HB.
    dodist_prefix RCB ROP.
    zs. setreg 25 (Z_to_bv 64 (hold / 2 ^ code_bits (rdD k))) ltac:(rewrite srl_div by lia; reflexivity).
    zs. zs. setreg 26 (Z_to_bv 64 (bits - code_bits (rdD k))) ltac:(rewrite swrap32_small by lia; reflexivity).
    destruct CL as [(Hop16 & Hv1 & Hv & Hop29) | (H64 & H16 & H32)].
    -
      pose proof (op_base_tests (code_op (rdD k)) ltac:(lia)) as (T16 & T64 & T32 & T240 & T15 & Tnz).
      rewrite Z.shiftl_1_l in Hv. rewrite T16. zs.
      apply evtF_done. do 10 eexists. exists (hold / 2 ^ code_bits (rdD k)), (bits - code_bits (rdD k)).
      split; [lia|]. split; [lia|]. split; [exact HB|]. left. exists k.
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. lia.
    -
      rewrite H16. zs. zs. zs. zbr K1.
      apply evtF_done. do 10 eexists. exists (hold / 2 ^ code_bits (rdD k)), (bits - code_bits (rdD k)).
      split; [lia|]. split; [lia|]. split; [exact HB|]. right. reflexivity.
  Qed.

  Lemma if_decdist : forall (m : amem) (fo : Z -> Z) (x5 x6 x7 x10 x11 x14 x24 x28 x29 x30 : word) (len ci co hold bits : Z),
    INV m fo ->
    15 <= bits <= 40 -> 0 <= hold < 2 ^ bits ->
    evtF bsegs RNG (decdist_post m len ci co bits) (LST x5 x6 x7 x10 x11 x14 x24 x28 x29 x30 len ci co hold bits 0x98404 m).
  Proof using All.
    intros until bits. intros INV BITS HOLD. pose proof INV as INV0.
    open_fctx CX. open_finv INV. unfold lst, gms, xms.
    clear ZSD ZOD SOD WSZ WNX WIN TOKL SANE FWR WH WN BO0 LB OSZ Z0 ZL S0 SL OB0 OBL D1 DL D8 PAYB PAYR PAYN UNP DJD DJP RD RSD
          TLB TL4 TL0 TLN0 TLHI RTL TLR DJTL SHTL RSTL DJSTL TLS1 TLS2 SHO DJO ROB RSOB STRM SSC OUT FOR SHZ DJZ SHS DJS RZ RSZ RS RSS.
    assert (TDC : bytes_at bsegs m da (u32s (fws rdD (Z.to_nat nd)))).
    { eapply bytes_at_transport; [exact TDB| exact MU|]. rewrite u32s_length, fws_length.
      replace (Z.of_nat (4 * Z.to_nat nd)) with (4 * nd) by lia. exact DJTD. }
    pose proof (pow2_40 bits ltac:(lia)) as P40. pose proof (pow2_15 db ltac:(lia)) as PDB.
    pose proof (mod_pow2_bound hold db ltac:(lia)) as RI1.
    remember (hold mod 2 ^ db) as i1 eqn:EI1.
    pose proof (tab_root_entry DISTS rdD db nd i1 TOKD RI1) as (HB1 & _ & HEXT & CASES).
    assert (HK : 0 <= i1 < nd) by lia.
    pose proof (TDR i1 HK) as RK.
    pose proof (code_op_range (rdD i1)) as ROP. pose proof (code_bits_range (rdD i1)) as RCB. pose proof (code_val_range (rdD i1)) as RCV.
    zs.
    zs. setreg 10 (Z_to_bv 64 i1) ltac:(rewrite land_mask_mod by lia; rewrite EI1; reflexivity). clear EI1 FRM.
    zs. setreg 10 (Z_to_bv 64 (4 * i1)) ltac:(rewrite shl2; reflexivity).
    zs. setreg 11 (Z_to_bv 64 (da + 4 * i1)) ltac:(f_equal; lia).
    zs. pc_dec_ub. zsb. zsb. zs. zs. zs. zs. pc_dec_ub. zs. pc_dec_ub.
    destruct CASES as [[NL TM] | (L1 & L2 & L3 & L4 & SUB)].
    -
      eapply (if_dodist m fo _ _ _ _ _ _ _ _ _ len ci co hold bits bits i1 db INV0 HK TM); lia.
    -
      pose proof (op_link_tests (code_op (rdD i1)) ltac:(lia)) as (T16 & T64 & T240 & Tnz).
      pose proof (pow2_15 (code_op (rdD i1)) ltac:(lia)) as HPO.
      pose proof (code_read_bits bsegs m da (fws rdD (Z.to_nat nd)) i1 (rdD i1) TDC (f32arr_nth rdD (Z.to_nat nd) i1 ltac:(lia)) ltac:(lia) RK) as RDB.
      pose proof (code_read_op bsegs m da (fws rdD (Z.to_nat nd)) i1 (rdD i1) TDC (f32arr_nth rdD (Z.to_nat nd) i1 ltac:(lia)) ltac:(lia) RK) as RDOP.
      pose proof (code_read_val bsegs m da (fws rdD (Z.to_nat nd)) i1 (rdD i1) TDC (f32arr_nth rdD (Z.to_nat nd) i1 ltac:(lia)) ltac:(lia) RK) as RDV.
      pose proof (drop_bound hold bits (code_bits (rdD i1)) ltac:(lia) HOLD) as HB.
      remember (hold / 2 ^ code_bits (rdD i1)) as h1 eqn:EH1.
      dodist_prefix RCB ROP.
      zs. setreg 25 (Z_to_bv 64 h1) ltac:(rewrite srl_div by lia; rewrite EH1; reflexivity). clear EH1.
      zs. rewrite T16.
      zs. setreg 26 (Z_to_bv 64 (bits - code_bits (rdD i1))) ltac:(rewrite swrap32_small by lia; reflexivity).
      zs. zs. rewrite T64. zs.
      zs. zs. zs. zs. zs.
      zs. rewrite zx16_small by lia.
      zs. rewrite shl2.
      zs. pc_dec_ub. zs. pc_dec_ub.
      zs.
      zs. zs. rewrite mask_sllw by lia.
      pose proof (mod_pow2_bound h1 (code_op (rdD i1)) ltac:(lia)) as RJ.
      remember (h1 mod 2 ^ code_op (rdD i1)) as j eqn:EJ.
      pose proof (pow2_40 (bits - code_bits (rdD i1)) ltac:(lia)) as P40'.
      zs. setreg 10 (Z_to_bv 64 j) ltac:(rewrite land_mask_mod by lia; rewrite ?(Z.mod_small h1 18446744073709551616) by lia; rewrite EJ; reflexivity). clear EJ.
      zs. rewrite shl2.
      zs. zs. pc_dec_ub.
      zs.
      destruct (SUB j RJ) as [NL2 TM2].
      assert (HK2 : 0 <= code_val (rdD i1) + j < nd) by lia.
      remember (code_val (rdD i1) + j) as k2 eqn:EK2.
      setreg 11 (Z_to_bv 64 (da + 4 * k2)) ltac:(f_equal; lia).
      zs. zs. pc_dec_ub.
      pose proof (term_ok_bits _ _ _ TM2) as TB2.
      assert (F1 : code_bits (rdD k2) <= bits - code_bits (rdD i1)) by lia.
      assert (F2 : bits - (bits - code_bits (rdD i1)) + (15 - db) <= 15) by lia.
      eapply (if_dodist m fo _ _ _ _ _ _ _ _ _ len ci co _ _ bits k2 (15 - db) INV0 HK2 TM2); lia.
  Qed.
End P.
End CANSEC1.
