(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* inflate_state arrays at their 1.4 offsets (lens 168, work 808, codes 1384, sane 7160; 1.3.1: 152, 792, 1368, 7144) *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.Lib Require Import Arr Bytes ZBridge.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.AsanW Require Import AImg.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.zspec.zmodel Require Import ZIface InflateState Inftrees InflateInv InflateInvTab.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.U2A Require Import U2AShadow U2AArr U2AKit U2AObj InfATables ItAKit IfAPure IfA_base IfAKit IfAStore IfA_lenb.
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
  Variables (sd : sdc) (id : idc) (ni ai no ao msg mode hw bw : word).
  Hypothesis CX : if_ctx RNG SP lo Zs S D n OB osz Wd wsz whave wnext lb db la na da nd bo rdL rdD fw payload m1.
  Notation LST := (lst FR fc gp tp SP Zs S D n OB osz lb la da).
  Notation LINV m v0 v24 fo := (if_inv SP Zs S OB osz bo wsz whave wnext Wd la da lb db m1 m v0 v24
                                  (Z_to_bv 64 (Z.shiftr (Zs + 32) 3 + 2147450880)) (Z_to_bv 64 (Zs + 24)) sd id ni ai no ao msg mode hw bw fo).
  Definition dst (x1 x6 x10 x13 x16 x21 : word) (len dist ci co hold bits pc : Z) (m : amem) : machine_state :=
    gms SP Zs S D n OB osz lb la da gp tp FR fc x1 x6 (Z_to_bv 64 (Zs + 8)) (Z_to_bv 64 len) x10 (Z_to_bv 64 (S + 7160)) x13 (Z_to_bv 64 (OB + bo)) x16
        (Z_to_bv 64 dist) x21 (Z_to_bv 64 (Zs + 32)) (Z_to_bv 64 (Zs + 24)) (Z_to_bv 64 (Z.shiftr (Zs + 8) 3 + 2147450880))
        ci co hold bits pc m.
  Notation DINV m v0 fo := (if_inv SP Zs S OB osz bo wsz whave wnext Wd la da lb db m1 m v0 (Z_to_bv 64 (Z.shiftr Zs 3 + 2147450880))
                              (Z_to_bv 64 (Z.shiftr (Zs + 32) 3 + 2147450880)) (Z_to_bv 64 (Zs + 24)) sd id ni ai no ao msg mode hw bw fo).

  Definition distb_post (fo : Z -> Z) (len ci co hold bits : Z) : machine_state -> Prop :=
    fun ms' => exists (m' : amem) (x1 x6 x13 x16 x21 v0 : word) (dist ci' hold' bits' : Z),
      DINV m' v0 fo /\ 1 <= dist <= 32768 /\ ci <= ci' <= ci + 2 /\ 0 <= bits' <= 40 /\ 0 <= hold' < 2 ^ bits'
      /\ 8 * (n - ci') + bits' <= 8 * (n - ci) + bits /\ 8 * ci - bits <= 8 * ci' - bits' /\ ci' <= n /\
      ((ms' = dst x1 x6 (Z_to_bv 64 (co - bo)) x13 x16 x21 len dist ci' co hold' bits' 0x970fc m' /\ dist <= co - bo)
       \/ (ms' = dst x1 x6 (Z_to_bv 64 (co - bo)) x13 x16 x21 len dist ci' co hold' bits' 0x97028 m' /\ co - bo < dist)).

  Lemma if_distb : forall (m : amem) (v0 v24 : word) (fo : Z -> Z) (x1 x6 x10 x15 x16 x21 : word) (len ci co hold bits k : Z),
    LINV m v0 v24 fo ->
    0 <= k < nd -> 16 <= code_op (rdD k) <= 29 -> 1 <= code_val (rdD k) -> code_val (rdD k) + 2 ^ (code_op (rdD k) - 16) - 1 <= 32768 ->
    0 <= ci <= n -> 0 <= bits <= 40 -> 0 <= hold < 2 ^ bits -> 13 <= 8 * (n - ci) + bits -> bo <= co <= osz ->
    evtF asegs RNG (distb_post fo len ci co hold bits)
      (LST x1 x6 x10 (Z_to_bv 64 (da + 4 * k)) (Z_to_bv 64 (code_op (rdD k))) x15 x16 x21 len ci co hold bits 0x96f7c m).
  Proof using All.
    intros until k. intros INV0 HK HOP HV1 HV CI BITS HOLD HA CO.
    open_fctx CX. open_finv INV0. unfold lst, gms, distb_post.
    clear ZSD ZOD SOD WSZ WNX WIN TOKL TOKD SANE FWR WH WN DB LB
          TLB TL4 TL0 TLN0 TLHI RTL TLR DJTL SHTL RSTL DJSTL TLS1 TLS2 SHZ DJZ SHS DJS RZ RSZ RS RSS SHO DJO ROB RSOB.
    pose proof (TDR k HK) as RK. pose proof (code_val_range (rdD k)) as RCV. pose proof (code_op_range (rdD k)) as ROP.
    pose proof (op_base_tests (code_op (rdD k)) ltac:(lia)) as (T16 & T64 & T32 & T240 & T15 & Tnz).
    pose proof (pow2_40 bits BITS) as P40.
    zs.
    lazymatch goal with MUx : munch _ m1 ?mx |- _ =>
      assert (TDC : bytes_at asegs mx da (u32s (fws rdD (Z.to_nat nd))));
      [ eapply bytes_at_transport; [exact TDB| exact MUx|]; rewrite u32s_length, fws_length;
        replace (Z.of_nat (4 * Z.to_nat nd)) with (4 * nd) by lia; exact DJTD |] end.
    lazymatch type of TDC with bytes_at _ ?mx _ _ =>
      pose proof (code_read_val asegs mx da (fws rdD (Z.to_nat nd)) k (rdD k) TDC (f32arr_nth rdD (Z.to_nat nd) k ltac:(lia)) ltac:(lia) RK) as RDV end.
    zrunb [0x96f98]. rewrite zx16_small by lia.
    zs. rewrite T15.
    lazymatch goal with H : rw_cells asegs _ (SP + -240) _ |- _ => rename H into FRM' end.
    lazymatch goal with H : rw_cells asegs _ Zs _ |- _ => rename H into STRM' end.
    lazymatch goal with H : rw_cells asegs _ S _ |- _ => rename H into SSC' end.
    lazymatch goal with H : f8arr asegs _ OB _ _ |- _ => rename H into OUT' end.
    lazymatch goal with H : mem_inv asegs _ |- _ => rename H into MI' end.
    lazymatch type of TDC with bytes_at _ ?mx _ _ => set (m' := mx) in * end.
    assert (INV' : DINV m' v0 fo) by close_finv.
    remember (code_op (rdD k) - 16) as e eqn:EE.
    assert (ER : 0 <= e <= 13) by lia.
    pose proof (pow2_15 e ltac:(lia)) as PE.
    assert (TAIL : forall (y10 y16 : word) (ci' hold' bits' : Z),
              e <= bits' <= 40 -> 0 <= hold' < 2 ^ bits' -> ci <= ci' <= ci + 2 -> ci' <= n ->
              8 * (n - ci') + bits' = 8 * (n - ci) + bits -> 8 * ci - bits = 8 * ci' - bits' ->
              evtF asegs RNG (distb_post fo len ci co hold bits)
                (dst x1 x6 y10 (Z_to_bv 64 e) y16 x21 len (code_val (rdD k)) ci' co hold' bits' 0x97008 m')).
    { intros y10 y16 ci' hold' bits' B' H' C' N' A' Q'. unfold dst, gms, distb_post.
      pose proof (pow2_40 bits' ltac:(lia)) as P40'.
      zs. zs. rewrite mask_sllw by lia.
      zs. zs. zs. zs. zs.
      setreg 22 (Z_to_bv 64 (hold' / 2 ^ e)) ltac:(rewrite srl_div by lia; reflexivity).
      setreg 23 (Z_to_bv 64 (bits' - e)) ltac:(rewrite swrap32_small by lia; reflexivity).
      setreg 18 (Z_to_bv 64 (code_val (rdD k) + hold' mod 2 ^ e)) ltac:(rewrite land_mask_mod by lia; f_equal; lia).
      setreg 10 (Z_to_bv 64 (co - bo)) ltac:(replace (OB + co - (OB + bo)) with (co - bo) by lia; rewrite swrap32_small by lia; reflexivity).
      pose proof (drop_bound hold' bits' e ltac:(lia) H') as HB. pose proof (mod_pow2_bound hold' e ltac:(lia)) as MB.
      zs. zbr0 KD.
      - apply evtF_done. exists m'. do 6 eexists. exists (code_val (rdD k) + hold' mod 2 ^ e), ci', (hold' / 2 ^ e), (bits' - e).
        split; [exact INV'|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
        left. split; [unfold dst, gms; reflexivity| lia].
      - apply evtF_done. exists m'. do 6 eexists. exists (code_val (rdD k) + hold' mod 2 ^ e), ci', (hold' / 2 ^ e), (bits' - e).
        split; [exact INV'|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
        right. split; [unfold dst, gms; reflexivity| lia]. }
    zs. zbr0 K.
    -
      zs. zs. zs. eapply TAIL; lia.
    -
      assert (CIN : ci + 1 <= n) by lia.
      assert (PAYC : bytes_at asegs m' D (map (Z_to_bv 8) payload)).
      { eapply bytes_at_transport; [exact PAYB| eassumption|]. rewrite length_map, PAYN. exact DJD. }
      lazymatch goal with MUx : munch _ m1 m' |- _ =>
        destruct (unp_check_mu asegs _ _ _ _ _ (D + ci) 1 UNP MUx DJP ltac:(lia) ltac:(lia) ltac:(lia) (mod8_room1 _)) as (b0 & RDB0 & CK0) end.
      zs. zs. zs. rewrite sxb_sval. zs.
      ck_branchJ 11 0x96fb4 CK0.
      pose proof (pay_read asegs _ D payload ci PAYC ltac:(lia)) as RDP0. fold (bz payload ci) in RDP0.
      pose proof (bz_range payload ci PAYR) as BZ0.
      zs. cbv beta. rewrite (bz_val payload ci PAYR).
      zs. rewrite swrap32_small by lia. zs. zs. zs.
      setreg 22 (Z_to_bv 64 (hold + bz payload ci * 2 ^ bits)) ltac:(rewrite shl_byte by lia; f_equal; lia).
      pose proof (pull_bound hold bits (bz payload ci) ltac:(lia) HOLD BZ0) as PB1.
      zs. zbr0 K2.
      +
        zs. zs. zs.
        setreg 14 (Z_to_bv 64 (D + (ci + 1))) ltac:(f_equal; lia).
        eapply TAIL; lia.
      +
        assert (CIN2 : ci + 2 <= n) by lia.
        lazymatch goal with MUx : munch _ m1 m' |- _ =>
          destruct (unp_check_mu asegs _ _ _ _ _ (D + ci + 1) 1 UNP MUx DJP ltac:(lia) ltac:(lia) ltac:(lia) (mod8_room1 _)) as (b1 & RDB1 & CK1) end.
        zs. zs. zs. rewrite sxb_sval.
        ck_branchJ 16 0x96fdc CK1.
        pose proof (pay_read asegs _ D payload (ci + 1) PAYC ltac:(lia)) as RDP1. fold (bz payload (ci + 1)) in RDP1.
        replace (D + (ci + 1)) with (D + ci + 1) in RDP1 by lia.
        pose proof (bz_range payload (ci + 1) PAYR) as BZ1.
        zs. cbv beta. rewrite (bz_val payload (ci + 1) PAYR).
        zs. zs. zs. zs.
        setreg 22 (Z_to_bv 64 (hold + bz payload ci * 2 ^ bits + bz payload (ci + 1) * 2 ^ (bits + 8))) ltac:(rewrite shl_byte by lia; f_equal; lia).
        setreg 14 (Z_to_bv 64 (D + (ci + 2))) ltac:(f_equal; lia).
        pose proof (pull2_bound hold bits (bz payload ci) (bz payload (ci + 1)) ltac:(lia) HOLD BZ0 BZ1) as PB2.
        zs. zs. zs.
        eapply TAIL; lia.
  Qed.
End P.
End CANSEC1.
