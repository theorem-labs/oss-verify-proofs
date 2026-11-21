(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.Lib Require Import Arr Bytes ZBridge Tac InitMem StoreFast.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.Spec Require Import AsanCtrl.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.BothW Require Import BImg RtCells ABase ABytes AMalloc_iface AUri_kit.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.IK Require Import IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.U2A Require Import U2AShadow U2AKit U2AArr U2AStore InfAGlue InfPure InfPure_w7 InfPure_w7d InfPure_w7e InfPure_w7f InfPure_w7h InfAGlue_w7 InfAGlue_w7b.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.U2A Require Import U2AObj.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.U1B Require Import U2BObj U2BClient U2BIface InfBBase InfBKit InfBTables InfB_w7base InfB_w7tab InfB_w7tab16 InfB_w7pull InfB_w7ltab InfB_w7lenr InfB_len13S.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.U1B Require Import U2BKit U2BKit_p04 InfBTraps.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load_hyp :=
  match goal with
  | |- context [ov_read_bytes ?segs ?m ?a ?n] => match goal with HR : ov_read_bytes segs m a n = Some _ |- _ => rewrite HR end
  end; load_post.
Local Ltac solve_load ::= first [ solve_load_hyp | solve_load_sh0 | solve_load_shlit | solve_load_base | solve_load_image ].
Local Ltac acc_hint_hyp := lazymatch goal with |- acc_in ?R ?x => match goal with HA : acc_in R x |- _ => exact HA end end.
Local Ltac acc_hint ::= first [ acc_hint_hyp | acc_hint_sh ].
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= farr_store_extra m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= farr_call_extra segs W m m' MU WM.
Local Ltac ub_is_trap pc ::= ub_in_traps inf_traps pc.

Section CANSEC1. Context {rc : runConstT}.
Section R.
  Variables (RNG : footprint) (POST : machine_state -> Prop).
  Lemma len_pull1 : forall (x1 x2 x3 x4 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x25 x26 x27 x28 x29 x30 x31 : word) (FR : bvmap 5 word) (fc : bv 32) (m : amem) (H B bz : Z),
    0 <= B <= 40 -> 0 <= H < 2 ^ B -> 0 <= bz < 256 ->
    evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 (Z_to_bv 64 B) x6 x7 x8 x9 (Z_to_bv 64 (Z.shiftl bz (B mod 64))) x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x25 x22 (Z_to_bv 64 (H + bz * 2 ^ B)) x20 x23 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x916a8) fc None m (seg_rom bsegs)) ->
    evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 (Z_to_bv 64 B) x6 x7 x8 x9 (Z_to_bv 64 bz) x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x25 x22 (Z_to_bv 64 H) x20 x23 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x916a0) fc None m (seg_rom bsegs)).
  Proof.
    intros until bz. intros BR HH BZ K.
    pose proof (pow2_le_40 B ltac:(lia)) as P40.
    pose proof (pull_bound H B bz ltac:(lia) ltac:(lia) BZ) as PB.
    pose proof (Z.pow_le_mono_r 2 (B + 8) 48 ltac:(lia) ltac:(lia)) as P48. change (2 ^ 48) with 281474976710656 in P48.
    zs. zs.
    rewrite (pull_hold H bz B) by lia.
    exact K.
  Time Qed.
End R.
Section S.
  Variable AI : AMallocIface.
  Variables (L : alayout) (RNG : footprint) (stA : astate) (LB : list ablock).
  Variables (gp tp : word) (FR : bvmap 5 word) (fc : bv 32) (POST : machine_state -> Prop).
  Variables (LBc : list ablock) (m0 : amem) (payload : list Z) (fw : Z -> Z) (saved fk fksh : list cell).

  Notation KALLB cx ly B := (KALL cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh B).
  Notation VIS cx ly st lf cf wf fo v0 v8 v16 v24 v240 v328 v512 j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m :=
    (inf_vis cx ly st lf cf wf fo payload v0 v8 v16 v24 v240 v328 v512 j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m).
  Notation HIDm cx ly m := (inf_hid cx ly AI L RNG stA LB LBc m0 fw saved fk fksh m).

  Lemma l_loop1 : forall (N : nat) (cx : ictx) (ly : ilay) (st : ist) (lf cf wf fo : Z -> Z) (v0 v8 v16 v24 v240 v328 j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word)
      (x10 x13 x23 x26 x29 x30 : word) (m : amem) (k : ltk) (nd : Z) (ci H B : Z),
    inf_ctx cx ly AI RNG LB -> Forall (fun c => 0 <= c < 256) payload -> Z.of_nat (length payload) = c_n cx ->
    t_mode st = LEN -> sinv cx st lf cf -> inf_arr_ok cx wf fo ->
    VIS cx ly st lf cf wf fo v0 v8 v16 v24 v240 v328 (Z_to_bv 64 (Z.shiftr (c_p cx + 108) 3)) j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m -> HIDm cx ly m -> KALLB cx ly (meas cx st) ->
    lt_ok k nd -> tab_ok LENS (lt_rd cf k) (t_lb st) nd = true -> nd <= 65536 ->
    (forall ci' H' B' x10' x13' x23' x26', t_cin st <= ci' <= c_n cx -> B' = t_bits st + 8 * (ci' - t_cin st) -> 0 <= H' < 2 ^ B' ->
       code_bits (lt_rd cf k (H' mod 2 ^ t_lb st)) <= B' -> B' <= 40 ->
       evtF bsegs RNG POST (L_E1 gp tp FR fc cx ly st k (lt_rd cf k (H' mod 2 ^ t_lb st)) ci' H' B' x10' x13' x23' x26' m)) ->
    c_n cx - ci < Z.of_nat N ->
    t_cin st <= ci <= c_n cx -> B = t_bits st + 8 * (ci - t_cin st) -> 0 <= H < 2 ^ B -> B <= 40 ->
    evtF bsegs RNG POST (L_L1 gp tp FR fc cx ly st k ci H B x10 x13 x23 x26 x29 x30 m).
  Proof.
    induction N as [|N IH]; intros until B; intros CTX PAYR PLEN MODE SI ARR VIS HID KA LOK TOK ND16 KE1 HN HC HBE HH HB40; [exfalso; clear - HN HC; lia|].
    pose proof KA as (KD & KB & KL & KLV).
    pose proof (sinv_bits_facts _ _ _ _ SI) as (CIN0 & CINN & BITS0 & BLE & HOLD0).
    destruct (tab_ok_root _ _ _ _ TOK) as (LB15 & NDR & ROOT).
    unfold L_L1. unfold L_E1 in KE1.
    revert IH KE1. inf_arm_open. intros IH KE1.
    destruct (lt_facts RNG m S cf k nd LOK CODES RN MI SHS SHLF S8 RS RSS RI RISH SB) as (DT & DT16 & SBT & XT8 & XT0 & XTL & XTH & RXT & RTA & TAP & TAH).
    set (TA := lt_TA S k) in *. set (rd := lt_rd cf k) in *. set (XT := lt_XT S k) in *. set (NS := lt_NS k) in *.
    pose proof (pow2_le_15 lb ltac:(clear - LB15; lia)) as P15. pose proof (pow2_le_40 B ltac:(clear - HB40 HBE BITS0 HC; lia)) as P40.
    assert (IDX : 0 <= H mod 2 ^ lb < 2 ^ lb) by (apply mod_pow2_bound; clear - LB15; lia).
    pose proof (ROOT _ IDX) as ROK.
    assert (CBE : 1 <= code_bits (rd (H mod 2 ^ lb)) <= 15).
    { destruct (root_term_or_link InflateState.LENS rd lb nd _ ltac:(clear - LB15; lia) ROK) as [(TERM & _)|(_ & EB & _)].
      - pose proof (term_ok_bits _ _ _ TERM) as TBB. clear - TBB LB15. lia.
      - clear - EB LB15. lia. }
    assert (JND : 0 <= H mod 2 ^ lb < nd) by (clear - IDX NDR; lia).
    remember (H mod 2 ^ lb) as I0 eqn:EI0. apply w7hide_in in EI0.
    destruct (DT I0 JND) as (RDR & RD0 & RD1 & RD2). pose proof (DT16 I0 JND) as RD16.
    set (c1 := rd I0) in *.
    pose proof (tab_sh0 m XT NS (TA + 4 * I0) SBT XT8 ltac:(clear - JND XTL XTH; lia) ltac:(exact XT0)) as RDS0.
    pose proof (tab_sh_acc RNG XT NS (TA + 4 * I0) RXT XT8 ltac:(clear - JND XTL XTH; lia) ltac:(exact XT0)) as ACS0.
    pose proof (tab_sh0 m XT NS (TA + 4 * I0 + 3) SBT XT8 ltac:(clear - JND XTL XTH; lia) ltac:(exact XT0)) as RDS3.
    pose proof (tab_sh_acc RNG XT NS (TA + 4 * I0 + 3) RXT XT8 ltac:(clear - JND XTL XTH; lia) ltac:(exact XT0)) as ACS3.
    zs. rewrite shl2. zs.
    zrung [0x9164c].
    pose proof (code_val_range c1) as VALR1.
    assert (LO1 : 0 <= Z.land c1 65535 < 65536) by (change 65535 with (Z.ones 16); rewrite Z.land_ones by (clear; lia); apply Z.mod_pos_bound; clear; lia).
    zs. cbv beta. rewrite (zx16_small (code_val c1)) by (clear - VALR1; lia).
    zs. cbv beta. rewrite (zx16_small (Z.land c1 65535)) by (clear - LO1; lia).
    eapply (len_join1 RNG POST) with (c := c1); [exact RDR|].
    zs. zbr0 KE.
    -
      apply w7hide_out in EI0. subst c1. subst I0.
      eapply (KE1 ci H B); [gcbn; exact HC| gcbn; exact HBE| exact HH| gcbn; clear - KE; lia| exact HB40].
    -
      zs. zbr0 KH.
      +
        assert (CIR : 0 <= ci < n) by (clear - CIN0 HC KH; lia).
        destruct (pull_facts RNG _ m m D n payload ci UNP MU DJP RD RSD PAYB PAYR PLEN D16 D1 CIR) as (b & RDB & CK & ACP & RDP & ACB & BZR).
        zrung [0x9168c].
        zs. zs. zs. rewrite sxb_sval.
        eapply (len_ck1 RNG POST) with (A := D + ci) (sb := sval b); [clear - D1 CIR DL2; lia| exact CK| intros y].
        zs. cbv beta. rewrite (bz_val payload ci PAYR).
        eapply (len_pull1 RNG POST) with (H := H) (B := B) (bz := bz payload ci); [clear - HB40 HBE BITS0 HC; lia| exact HH| exact BZR|].
        pose proof (pull_bound H B (bz payload ci) ltac:(clear - HB40 HBE BITS0 HC; lia) HH BZR) as PB.
        remember (H + bz payload ci * 2 ^ B) as H1 eqn:EH1.
        pose proof (Z.pow_le_mono_r 2 (B + 8) 48 ltac:(clear; lia) ltac:(clear - HB40; lia)) as P48. change (2 ^ 48) with 281474976710656 in P48.
        eapply (len_root_b RNG POST) with (TA := TA) (lb := lb) (H := H1) (NX := D + ci) (B := B) (T1 := n - ci) (T2 := 8 * (n - ci)) (HV := n - ci);
          [clear - PB P48; lia| exact LB15| clear - TAP TAH NDR P15; lia| clear - D1 CIR DL2; lia| clear - HB40 HBE BITS0 HC; lia
          | clear - CIR NR; lia| clear - CIR NR; lia| clear - CIR NR; lia|].
        replace (D + ci + 1) with (D + (ci + 1)) by (clear; lia). replace (n - ci + -1) with (n - (ci + 1)) by (clear; lia).
        replace (8 * (n - ci) + -8) with (8 * (n - (ci + 1))) by (clear; lia).
        apply w7hide_out in EI0. subst H1.
        eapply (IH (ICX u S D n 6341056 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo)
          with (k := k) (nd := nd) (ci := ci + 1) (H := H + bz payload ci * 2 ^ B) (B := B + 8);
          [exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| exact VISf| exact HID| exact KA
          | exact LOK| exact TOK| exact ND16| exact KE1
          | gcbn; clear - HN CIR; lia| gcbn; clear - HC CIR; lia| gcbn; clear - HBE; lia| exact PB| clear - KE CBE EI0; subst c1 I0; lia].
      +
        zrung [0x933c4].
        assert (ECI : ci = n) by (clear - KH HC; lia).
        replace ((n - cin) ≪ 3 + bits) with B by (rewrite Z.shiftl_mul_pow2 by (clear; lia); clear - HBE ECI; lia).
        replace (D + cin + (n - cin) mod 4294967296) with (D + n) in * by (rewrite Z.mod_small by (clear - CIN0 CINN NR; lia); clear; lia).
        destruct (sinv_pull _ _ lf cf n H B SI ltac:(gcbn; clear - CINN; lia) ltac:(gcbn; clear; lia) ltac:(clear - HBE BITS0 HC; lia) ltac:(exact HB40) ltac:(clear - HH; lia) ltac:(clear - HH; lia)
                    ltac:(clear - HBE BLE HC ECI; lia) ltac:(gcbn; clear - HBE ECI; lia)) as (SI1 & _).
        st_norm SI1.
        eapply (KL (IST mode last flags n cout H B out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo);
          [exact SI1| exact ARR| reflexivity| inf_vis_close| inf_hid_close].
    (* [U14B] A2 2026-11-12: v24 is a vestige binder at 1.4 (InfBBase's inf_locals no longer holds it), so eapply leaves
       it as a shelved word; any value does (G's U1A cure for v240) *)
    Unshelve. all: exact (Z_to_bv 64 0).
  Time Qed.
End S.
End CANSEC1.
