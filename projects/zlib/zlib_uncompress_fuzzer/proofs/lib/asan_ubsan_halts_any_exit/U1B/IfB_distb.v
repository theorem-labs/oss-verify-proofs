(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.Lib Require Import Arr Bytes ZBridge.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.BothW Require Import BImg.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.zspec.zmodel Require Import ZIface InflateState Inftrees InflateInv InflateInvTab.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.U2A Require Import U2AShadow U2AArr U2AKit ItAKit IfAPure IfAStore.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.U2A Require Import U2AObj.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.U1B Require Import U2BObj InfBTables IfBTac IfB_base IfBKit IfB_wdefs IfB_lenb.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.Common Require Import RunDraw.
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
  Notation GST := (gms SP Zs S D n OB osz la da gp tp FR fc).
  Notation WST := (wst FR fc gp tp SP Zs S D n OB osz wnext la da).
  Notation INV m fo := (if_inv SP Zs S OB osz bo wsz whave wnext Wd la da lb db m1 m sd id ni ai no ao msg mode hw bw fo).
  Definition dst (x5 x6 x7 x10 x11 x14 x24 x28 x29 : word) (len dist ci co hold bits pc : Z) (m : amem) : machine_state :=
    GST x5 x6 x7 x10 x11 x14 (Z_to_bv 64 len) x24 x28 x29 (Z_to_bv 64 dist) ci co hold bits pc m.

  Definition distb_post (m : amem) (len ci co hold bits : Z) : machine_state -> Prop :=
    fun ms' => exists (x5 x6 x7 x10 x11 x14 x24 x28 x29 : word) (dist ci' hold' bits' : Z),
      1 <= dist <= 32768 /\ ci <= ci' <= ci + 2 /\ 0 <= bits' <= 40 /\ 0 <= hold' < 2 ^ bits'
      /\ 8 * (n - ci') + bits' <= 8 * (n - ci) + bits /\ 8 * ci - bits <= 8 * ci' - bits' /\ ci' <= n /\
      ((ms' = dst x5 x6 x7 x10 x11 x14 x24 x28 x29 len dist ci' co hold' bits' 0x98308 m /\ dist <= co - bo)
       \/ (ms' = WST x5 x6 x7 x10 x11 x24 x29 len dist (dist - (co - bo)) ci' co hold' bits' 0x9823c m
           /\ x14 = Z_to_bv 64 wnext /\ x28 = Z_to_bv 64 (dist - (co - bo)) /\ co - bo < dist /\ dist - (co - bo) <= whave)
       \/ (ms' = dst x5 x6 x7 x10 x11 x14 x24 x28 x29 len dist ci' co hold' bits' 0x98b34 m /\ whave < dist - (co - bo))).

  Lemma if_distb : forall (m : amem) (fo : Z -> Z) (x5 x6 x7 x10 x24 x28 x29 x30 : word) (len ci co hold bits k : Z),
    INV m fo ->
    0 <= k < nd -> 16 <= code_op (rdD k) <= 29 -> 1 <= code_val (rdD k) -> code_val (rdD k) + 2 ^ (code_op (rdD k) - 16) - 1 <= 32768 ->
    0 <= ci <= n -> 0 <= bits <= 40 -> 0 <= hold < 2 ^ bits -> 13 <= 8 * (n - ci) + bits -> bo <= co <= osz ->
    evtF bsegs RNG (distb_post m len ci co hold bits)
      (LST x5 x6 x7 x10 (Z_to_bv 64 (da + 4 * k)) (Z_to_bv 64 (code_op (rdD k))) x24 x28 x29 x30 len ci co hold bits 0x98168 m).
  Proof using All.
    intros until k. intros INV0 HK HOP HV1 HV CI BITS HOLD HA CO.
    open_fctx CX. open_finv INV0. unfold lst, gms, xms.
    assert (SANEC : rw_cells bsegs m (S + 7160) [C4 (Z_to_bv 64 1)]).
    { eapply rw_cells_transport; [exact SANE| exact MU| exact WM|]. cbn [disjoint_from cells_size csize Nat.add]. repeat split; try exact I; lia. }
    assert (WB : whave <= 32768 /\ wnext <= 32768) by lia.
    clear ZSD ZOD SOD WSZ WNX WIN TOKL TOKD SANE FWR DB LB
          TLB TL4 TL0 TLN0 TLHI RTL TLR DJTL SHTL RSTL DJSTL TLS1 TLS2 SHZ DJZ RZ RSZ SHO DJO ROB RSOB STRM SSC OUT FOR.
    pose proof (TDR k HK) as RK. pose proof (code_val_range (rdD k)) as RCV. pose proof (code_op_range (rdD k)) as ROP.
    pose proof (op_base_tests (code_op (rdD k)) ltac:(lia)) as (T16 & T64 & T32 & T240 & T15 & Tnz).
    pose proof (pow2_40 bits BITS) as P40.
    assert (TDC : bytes_at bsegs m da (u32s (fws rdD (Z.to_nat nd)))).
    { eapply bytes_at_transport; [exact TDB| exact MU|]. rewrite u32s_length, fws_length.
      replace (Z.of_nat (4 * Z.to_nat nd)) with (4 * nd) by lia. exact DJTD. }
    pose proof (code_read_val bsegs m da (fws rdD (Z.to_nat nd)) k (rdD k) TDC (f32arr_nth rdD (Z.to_nat nd) k ltac:(lia)) ltac:(lia) RK) as RDV.
    zs. zs. zs. zs. zs.
    zs. rewrite zx16_small by lia.
    zs. rewrite T15.
    remember (code_op (rdD k) - 16) as e eqn:EE.
    assert (ER : 0 <= e <= 13) by lia.
    pose proof (pow2_15 e ltac:(lia)) as PE.
    assert (TAIL : forall (y6 y7 y10 y11 y14 : word) (ci' hold' bits' : Z),
              e <= bits' <= 40 -> 0 <= hold' < 2 ^ bits' -> ci <= ci' <= ci + 2 -> ci' <= n ->
              8 * (n - ci') + bits' = 8 * (n - ci) + bits -> 8 * ci - bits = 8 * ci' - bits' ->
              evtF bsegs RNG (distb_post m len ci co hold bits)
                (dst (Z_to_bv 64 e) y6 y7 y10 y11 y14 x24 x28 x29 len (code_val (rdD k)) ci' co hold' bits' 0x981e8 m)).
    { intros y6 y7 y10 y11 y14 ci' hold' bits' B' H' C' N' A' Q'. unfold dst, gms, xms, distb_post.
      pose proof (pow2_40 bits' ltac:(lia)) as P40'.
      zs. zs. zs. rewrite mask_sllw by lia.
      zs. zs. zs. zs. zs.
      setreg 25 (Z_to_bv 64 (hold' / 2 ^ e)) ltac:(rewrite srl_div by lia; reflexivity).
      setreg 26 (Z_to_bv 64 (bits' - e)) ltac:(rewrite swrap32_small by lia; reflexivity).
      setreg 30 (Z_to_bv 64 (code_val (rdD k) + hold' mod 2 ^ e)) ltac:(rewrite land_mask_mod by lia; f_equal; lia).
      setreg 10 (Z_to_bv 64 (co - bo)) ltac:(replace (OB + co - (OB + bo)) with (co - bo) by lia; rewrite swrap32_small by lia; reflexivity).
      pose proof (drop_bound hold' bits' e ltac:(lia) H') as HB. pose proof (mod_pow2_bound hold' e ltac:(lia)) as MB.
      remember (code_val (rdD k) + hold' mod 2 ^ e) as dist eqn:EDIST.
      zs. zbr KD.
      - apply evtF_done. do 9 eexists. exists dist, ci', (hold' / 2 ^ e), (bits' - e).
        split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
        left. split; [unfold dst, gms, xms; reflexivity| lia].
      - zs. zs.
        setreg 28 (Z_to_bv 64 (dist - (co - bo))) ltac:(replace (dist - (OB + co - (OB + bo))) with (dist - (co - bo)) by lia; rewrite swrap32_small by lia; reflexivity).
        zs. zs. zs. zs. zbr KW.
        +
          apply evtF_done. do 5 eexists. exists (Z_to_bv 64 wnext). eexists. exists (Z_to_bv 64 (dist - (co - bo))). eexists.
          exists dist, ci', (hold' / 2 ^ e), (bits' - e).
          split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
          right. left. split; [unfold wst, gms, xms; reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. lia.
        +
          zrunb [0x98b34].
          apply evtF_done. do 9 eexists. exists dist, ci', (hold' / 2 ^ e), (bits' - e).
          split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
          right. right. split; [unfold dst, gms, xms; reflexivity| lia]. }
    zs. zbr K.
    -
      eapply TAIL; lia.
    -
      assert (CIN : ci + 1 <= n) by lia.
      assert (PAYC : bytes_at bsegs m D (map (Z_to_bv 8) payload)).
      { eapply bytes_at_transport; [exact PAYB| exact MU|]. rewrite length_map, PAYN. exact DJD. }
      destruct (unp_check_mu bsegs _ _ _ _ _ (D + ci) 1 UNP MU DJP ltac:(lia) ltac:(lia) ltac:(lia) (mod8_room1 _)) as (b0 & RDB0 & CK0).
      zs. zs. pc_dec_ub.
      zs. zs. zs. rewrite sxb_sval.
      ck_branchJ 14 0x981a0 CK0.
      pose proof (pay_read bsegs _ D payload ci PAYC ltac:(lia)) as RDP0. fold (bz payload ci) in RDP0.
      pose proof (bz_range payload ci PAYR) as BZ0.
      zs. cbv beta. rewrite (bz_val payload ci PAYR).
      zs. zs. rewrite ?(swrap32_small (bits + 8)) by lia. zs.
      setreg 25 (Z_to_bv 64 (hold + bz payload ci * 2 ^ bits)) ltac:(rewrite shl_byte by lia; f_equal; lia).
      pose proof (pull_bound hold bits (bz payload ci) ltac:(lia) HOLD BZ0) as PB1.
      zs. zbr K2.
      +
        zs. zs.
        setreg 13 (Z_to_bv 64 (D + (ci + 1))) ltac:(f_equal; lia).
        eapply TAIL; lia.
      +
        assert (CIN2 : ci + 2 <= n) by lia.
        destruct (unp_check_mu bsegs _ _ _ _ _ (D + ci + 1) 1 UNP MU DJP ltac:(lia) ltac:(lia) ltac:(lia) (mod8_room1 _)) as (b1 & RDB1 & CK1).
        zs. pc_dec_ub.
        zs. zs. zs. rewrite sxb_sval.
        ck_branchJ 6 0x981c8 CK1.
        pose proof (pay_read bsegs _ D payload (ci + 1) PAYC ltac:(lia)) as RDP1. fold (bz payload (ci + 1)) in RDP1.
        replace (D + (ci + 1)) with (D + ci + 1) in RDP1 by lia.
        pose proof (bz_range payload (ci + 1) PAYR) as BZ1.
        zs. cbv beta. rewrite (bz_val payload (ci + 1) PAYR).
        zs. zs. zs. zs. zs.
        setreg 25 (Z_to_bv 64 (hold + bz payload ci * 2 ^ bits + bz payload (ci + 1) * 2 ^ (bits + 8))) ltac:(rewrite shl_byte by lia; f_equal; lia).
        setreg 13 (Z_to_bv 64 (D + (ci + 2))) ltac:(f_equal; lia).
        pose proof (pull2_bound hold bits (bz payload ci) (bz payload (ci + 1)) ltac:(lia) HOLD BZ0 BZ1) as PB2.
        eapply TAIL; lia.
  Qed.
End P.
End CANSEC1.
