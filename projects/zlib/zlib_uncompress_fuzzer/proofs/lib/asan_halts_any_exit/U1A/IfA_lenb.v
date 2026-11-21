(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.Lib Require Import Arr Bytes ZBridge.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.AsanW Require Import AImg.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.zspec.zmodel Require Import ZIface InflateState Inftrees InflateInv InflateInvTab.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.U2A Require Import U2AShadow U2AArr U2AKit ItAKit IfAPure IfAStore.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.U1A Require Import U2AObj InfATables IfA_base IfAKit.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.Common Require Import RunDraw.
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
  Notation ST := (fms SP Zs S D n OB osz lb la da gp tp FR fc).
  Notation INV m v0 v24 v48 v56 fo := (if_inv SP Zs S OB osz bo wsz whave wnext Wd la da lb db m1 m v0 v24 v48 v56 sd id ni ai no ao msg mode hw bw fo).
  Definition lst (x1 x6 x10 x11 x13 x15 x16 x21 : word) (len ci co hold bits pc : Z) (m : amem) : machine_state :=
    gms SP Zs S D n OB osz lb la da gp tp FR fc x1 x6 (Z_to_bv 64 (Zs + 8)) (Z_to_bv 64 len) x10 x11 x13 x15 x16
        (Z_to_bv 64 (Z.shiftr Zs 3 + 2147450880)) x21 (Z_to_bv 64 (Zs + 32)) (Z_to_bv 64 (Zs + 24)) (Z_to_bv 64 (Z.shiftr (Zs + 8) 3 + 2147450880))
        ci co hold bits pc m.
  Notation LINV m v0 v24 fo := (INV m v0 v24 (Z_to_bv 64 (Z.shiftr (Zs + 32) 3 + 2147450880)) (Z_to_bv 64 (Zs + 24)) fo).

  Definition lenx_post (fo : Z -> Z) (ci co hold bits pc : Z) : machine_state -> Prop :=
    fun ms' => exists (m' : amem) (x1 x6 x10 x11 x13 x15 x16 x21 v0 v24 : word) (len ci' hold' bits' : Z),
      ms' = lst x1 x6 x10 x11 x13 x15 x16 x21 len ci' co hold' bits' pc m' /\ LINV m' v0 v24 fo
      /\ 3 <= len <= 258 /\ ci <= ci' <= ci + 1 /\ 0 <= bits' <= 40 /\ 0 <= hold' < 2 ^ bits'
      /\ 8 * (n - ci') + bits' <= 8 * (n - ci) + bits /\ 8 * (n - ci) + bits - 5 <= 8 * (n - ci') + bits'
      /\ 8 * ci - bits <= 8 * ci' - bits' /\ ci' <= n.

  Lemma if_lenx : forall (m : amem) (v0 v24 v48 v56 : word) (fo : Z -> Z) (x1 x6 x10 x15 x16 x21 : word) (ci co hold bits k : Z),
    INV m v0 v24 v48 v56 fo ->
    0 <= k < na -> 16 <= code_op (rdL k) <= 21 -> 3 <= code_val (rdL k) -> code_val (rdL k) + 2 ^ (code_op (rdL k) - 16) - 1 <= 258 ->
    0 <= ci <= n -> 0 <= bits <= 40 -> 0 <= hold < 2 ^ bits -> 33 <= 8 * (n - ci) + bits ->
    evtF asegs RNG (lenx_post fo ci co hold bits 0x96bc0)
      (ST x1 x6 x10 (Z_to_bv 64 (la + 4 * k)) (Z_to_bv 64 (code_op (rdL k))) x15 x16 x21 ci co hold bits 0x96b58 m).
  Proof using All.
    intros until k. intros INV0 HK HOP HV3 HV258 CI0 BITS HOLD HA.
    open_fctx CX. open_finv INV0. unfold fms, lenx_post.
    clear ZSD ZOD SOD WSZ WNX WIN TOKL TOKD SANE FWR WH WN BO0 DB LB
          TDB TD4 TD0 TDN0 TDHI RTD TDR DJTD SHTD RSTD DJSTD TDS1 TDS2 SHZ DJZ SHS DJS RZ RSZ RS RSS SHO DJO ROB RSOB.
    pose proof (TLR k HK) as RK. pose proof (code_val_range (rdL k)) as RCV. pose proof (code_op_range (rdL k)) as ROP.
    pose proof (op_base_tests (code_op (rdL k)) ltac:(lia)) as (T16 & T64 & T32 & T240 & T15 & Tnz).
    pose proof (pow2_40 bits BITS) as P40.
    zs. zs.
    lazymatch goal with MUx : munch _ m1 ?mx |- _ =>
      assert (TLC : bytes_at asegs mx la (u32s (fws rdL (Z.to_nat na))));
      [ eapply bytes_at_transport; [exact TLB| exact MUx|]; rewrite u32s_length, fws_length;
        replace (Z.of_nat (4 * Z.to_nat na)) with (4 * na) by lia; exact DJTL |] end.
    lazymatch type of TLC with bytes_at _ ?mx _ _ =>
      pose proof (code_read_val asegs mx la (fws rdL (Z.to_nat na)) k (rdL k) TLC (f32arr_nth rdL (Z.to_nat na) k ltac:(lia)) ltac:(lia) RK) as RDV end.
    zrunb [0x96b78]. rewrite zx16_small by lia.
    zs. rewrite T15.
    lazymatch goal with H : rw_cells asegs _ (SP + -240) _ |- _ => rename H into FRM' end.
    lazymatch goal with H : rw_cells asegs _ Zs _ |- _ => rename H into STRM' end.
    lazymatch goal with H : rw_cells asegs _ S _ |- _ => rename H into SSC' end.
    lazymatch goal with H : f8arr asegs _ OB _ _ |- _ => rename H into OUT' end.
    lazymatch goal with H : mem_inv asegs _ |- _ => rename H into MI' end.
    lazymatch type of TLC with bytes_at _ ?mx _ _ => set (m' := mx) in * end.
    assert (INV' : LINV m' v0 v24 fo) by close_finv.
    remember (code_op (rdL k) - 16) as e eqn:EE.
    assert (ER : 0 <= e <= 5) by lia.
    pose proof (pow2_15 e ltac:(lia)) as PE.
    assert (TAIL : forall (y10 y13 : word) (ci' hold' bits' : Z),
              e <= bits' <= 40 -> 0 <= hold' < 2 ^ bits' -> ci <= ci' <= ci + 1 -> ci' <= n ->
              8 * (n - ci') + bits' = 8 * (n - ci) + bits -> 8 * ci - bits = 8 * ci' - bits' ->
              evtF asegs RNG (lenx_post fo ci co hold bits 0x96bc0)
                (lst x1 x6 y10 (Z_to_bv 64 e) y13 x15 x16 x21 (code_val (rdL k)) ci' co hold' bits' 0x96ba8 m')).
    { intros y10 y13 ci' hold' bits' B' H' C' N' A' Q'. unfold lst, gms, lenx_post.
      pose proof (pow2_40 bits' ltac:(lia)) as P40'.
      zs. zs. rewrite mask_sllw by lia.
      zs. zs. zs. zs.
      setreg 22 (Z_to_bv 64 (hold' / 2 ^ e)) ltac:(rewrite srl_div by lia; reflexivity).
      setreg 23 (Z_to_bv 64 (bits' - e)) ltac:(rewrite swrap32_small by lia; reflexivity).
      setreg 8 (Z_to_bv 64 (code_val (rdL k) + hold' mod 2 ^ e)) ltac:(rewrite land_mask_mod by lia; f_equal; lia).
      pose proof (drop_bound hold' bits' e ltac:(lia) H') as HB. pose proof (mod_pow2_bound hold' e ltac:(lia)) as MB.
      apply evtF_done. exists m'. do 10 eexists. exists (code_val (rdL k) + hold' mod 2 ^ e), ci', (hold' / 2 ^ e), (bits' - e).
      split; [unfold lst, gms; reflexivity|]. split; [exact INV'|]. lia. }
    zs. zbr0 K.
    -
      apply evtF_done. exists m'. do 10 eexists. exists (code_val (rdL k)), ci, hold, bits.
      split; [unfold lst, gms; reflexivity|]. split; [exact INV'|]. lia.
    - zs. zbr0 K2.
      +
        eapply TAIL; lia.
      +
        assert (CIN : ci + 1 <= n) by lia.
        assert (PAYC : bytes_at asegs m' D (map (Z_to_bv 8) payload)).
        { eapply bytes_at_transport; [exact PAYB| eassumption|]. rewrite length_map, PAYN. exact DJD. }
        lazymatch goal with MUx : munch _ m1 m' |- _ =>
          destruct (unp_check_mu asegs _ _ _ _ _ (D + ci) 1 UNP MUx DJP ltac:(lia) ltac:(lia) ltac:(lia) (mod8_room1 _)) as (b0 & RDB0 & CK0) end.
        zs. zs. zs. rewrite sxb_sval.
        ck_branchJ 13 0x96b94 CK0.
        pose proof (pay_read asegs _ D payload ci PAYC ltac:(lia)) as RDP0. fold (bz payload ci) in RDP0.
        pose proof (bz_range payload ci PAYR) as BZ0.
        zs. cbv beta. rewrite (bz_val payload ci PAYR).
        zs. zs. zs. zs.
        setreg 22 (Z_to_bv 64 (hold + bz payload ci * 2 ^ bits)) ltac:(rewrite shl_byte by lia; f_equal; lia).
        setreg 14 (Z_to_bv 64 (D + (ci + 1))) ltac:(f_equal; lia).
        pose proof (pull_bound hold bits (bz payload ci) ltac:(lia) HOLD BZ0) as PB1.
        eapply TAIL; lia.
  Qed.

  Definition pull2d_post (m : amem) (len ci co hold bits : Z) : machine_state -> Prop :=
    fun ms' => exists (x1 x6 x10 x11 x13 x15 x16 x21 : word) (ci' hold' bits' : Z),
      ms' = lst x1 x6 x10 x11 x13 x15 x16 x21 len ci' co hold' bits' 0x96c10 m
      /\ ci <= ci' <= ci + 2 /\ 15 <= bits' <= 40 /\ 0 <= hold' < 2 ^ bits'
      /\ 8 * (n - ci') + bits' = 8 * (n - ci) + bits /\ 8 * ci - bits = 8 * ci' - bits' /\ ci' <= n.

  Lemma if_pull2d : forall (m : amem) (v0 v24 : word) (fo : Z -> Z) (x1 x6 x10 x11 x13 x15 x16 x21 : word) (len ci co hold bits : Z),
    LINV m v0 v24 fo ->
    0 <= ci <= n -> 0 <= bits <= 40 -> 0 <= hold < 2 ^ bits -> 28 <= 8 * (n - ci) + bits ->
    evtF asegs RNG (pull2d_post m len ci co hold bits) (lst x1 x6 x10 x11 x13 x15 x16 x21 len ci co hold bits 0x96bc0 m).
  Proof using All.
    intros until bits. intros INV0 CI0 BITS HOLD HA.
    open_fctx CX. open_finv INV0. unfold lst, gms, pull2d_post.
    clear ZSD ZOD SOD WSZ WNX WIN TOKL TOKD SANE FWR WH WN BO0 LB DB OSZ Z0 ZL S0 SL OB0 OBL
          TLB TL4 TL0 TLN0 TLHI RTL TLR DJTL SHTL RSTL DJSTL TLS1 TLS2 TDB TD4 TD0 TDN0 TDHI RTD TDR DJTD SHTD RSTD DJSTD TDS1 TDS2
          SHO DJO ROB RSOB FRM STRM SSC OUT FOR.
    pose proof (pow2_40 bits BITS) as P40.
    zs. zs. zbr0 K.
    - apply evtF_done. do 8 eexists. exists ci, hold, bits. split; [unfold lst, gms; reflexivity|]. lia.
    - assert (CIN : ci + 2 <= n) by lia.
      assert (PAYC : bytes_at asegs m D (map (Z_to_bv 8) payload)).
      { eapply bytes_at_transport; [exact PAYB| exact MU|]. rewrite length_map, PAYN. exact DJD. }
      destruct (unp_check_mu asegs _ _ _ _ _ (D + ci) 1 UNP MU DJP ltac:(lia) ltac:(lia) ltac:(lia) (mod8_room1 _)) as (b0 & RDB0 & CK0).
      zs. zs. zs. rewrite sxb_sval.
      ck_branchJ 11 0x96bd8 CK0.
      destruct (unp_check_mu asegs _ _ _ _ _ (D + ci + 1) 1 UNP MU DJP ltac:(lia) ltac:(lia) ltac:(lia) (mod8_room1 _)) as (b1 & RDB1 & CK1).
      pose proof (pay_read asegs _ D payload ci PAYC ltac:(lia)) as RDP0. fold (bz payload ci) in RDP0.
      pose proof (bz_range payload ci PAYR) as BZ0.
      zs. zs. zs. zs. rewrite sxb_sval. zs. cbv beta. rewrite (bz_val payload ci PAYR).
      ck_branchJ 15 0x96bf0 CK1.
      pose proof (pay_read asegs _ D payload (ci + 1) PAYC ltac:(lia)) as RDP1. fold (bz payload (ci + 1)) in RDP1.
      replace (D + (ci + 1)) with (D + ci + 1) in RDP1 by lia.
      pose proof (bz_range payload (ci + 1) PAYR) as BZ1.
      zs. zs. cbv beta. rewrite (bz_val payload (ci + 1) PAYR).
      zrunb [0x96c10].
      setreg 22 (Z_to_bv 64 (hold + bz payload ci * 2 ^ bits + bz payload (ci + 1) * 2 ^ (bits + 8))) ltac:(rewrite !shl_byte by lia; f_equal; lia).
      setreg 23 (Z_to_bv 64 (bits + 16)) ltac:(rewrite lor_16 by lia; reflexivity).
      setreg 14 (Z_to_bv 64 (D + (ci + 2))) ltac:(f_equal; lia).
      pose proof (pull2_bound hold bits (bz payload ci) (bz payload (ci + 1)) ltac:(lia) HOLD BZ0 BZ1) as PB2.
      apply evtF_done. do 8 eexists. exists (ci + 2), (hold + bz payload ci * 2 ^ bits + bz payload (ci + 1) * 2 ^ (bits + 8)), (bits + 16).
      split; [unfold lst, gms; reflexivity|]. lia.
  Qed.
End P.
End CANSEC1.
