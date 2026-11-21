(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.Lib Require Import Arr Bytes ZBridge Tac InitMem StoreFast.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.Spec Require Import AsanCtrl.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.BothW Require Import BImg RtCells ABase ABytes AMalloc_iface AUri_kit.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.IK Require Import IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.U2A Require Import U2AShadow U2AKit U2AArr U2AObj U2AStore InfAGlue InfPure InfPure_w7 InfPure_w7d InfPure_w7e InfPure_w7f InfPure_w7h InfAGlue_w7 InfAGlue_w7b.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.U2B Require Import U2BObj U2BClient U2BIface InfBBase InfBKit InfBTables InfB_w7base InfB_w7tab InfB_w7tab16 InfB_w7pull InfB_w7ltab InfB_w7lenr InfB_len13S InfB_len2 InfB_len4 InfB_len5 InfB_len5b.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.U2B Require Import U2BKit U2BKit_p04 InfBTraps.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.Common Require Import RunDraw.
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
Section S.
  Variable AI : AMallocIface.
  Variables (L : alayout) (RNG : footprint) (stA : astate) (LB : list ablock).
  Variables (gp tp : word) (FR : bvmap 5 word) (fc : bv 32) (POST : machine_state -> Prop).
  Variables (LBc : list ablock) (m0 : amem) (payload : list Z) (fw : Z -> Z) (saved fk fksh : list cell).

  Notation KALLB cx ly B := (KALL cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh B).
  Notation VIS cx ly st lf cf wf fo v0 v8 v16 v24 v240 v328 v512 j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m :=
    (inf_vis cx ly st lf cf wf fo payload v0 v8 v16 v24 v240 v328 v512 j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m).
  Notation HIDm cx ly m := (inf_hid cx ly AI L RNG stA LB LBc m0 fw saved fk fksh m).
  Notation LXB cx ly := (LXB_STMT AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh cx ly).
  Notation LXZ cx ly := (LXZ_STMT AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh cx ly).

  Notation SIX val rb op H := (H mod 2 ^ (rb + op) / 2 ^ rb + val).



  Lemma l_root : forall (cx : ictx) (ly : ilay) (st : ist) (lf cf wf fo : Z -> Z) (v0 v8 v16 v24 v240 j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits was pad : word)
      (x10 x13 x23 x26 : word) (m : amem) (k : ltk) (nd : Z) (ci H B : Z),
    LXB cx ly -> LXZ cx ly ->
    inf_ctx cx ly AI RNG LB -> Forall (fun c => 0 <= c < 256) payload -> Z.of_nat (length payload) = c_n cx ->
    t_mode st = LEN -> sinv cx st lf cf -> inf_arr_ok cx wf fo ->
    VIS cx ly st lf cf wf fo v0 v8 v16 v24 v240 (Z_to_bv 64 (Z.shiftr (c_p cx + 7164) 3 + 2147450880)) (Z_to_bv 64 (Z.shiftr (c_p cx + 108) 3)) j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits (Z_to_bv 64 0) was pad m -> HIDm cx ly m -> KALLB cx ly (meas cx st) ->
    lt_ok k nd -> tab_ok LENS (lt_rd cf k) (t_lb st) nd = true -> nd <= 65536 ->
    t_cin st <= ci <= c_n cx -> B = t_bits st + 8 * (ci - t_cin st) -> 0 <= H < 2 ^ B -> code_bits (lt_rd cf k (H mod 2 ^ t_lb st)) <= B -> B <= 40 ->
    evtF bsegs RNG POST (L_E1 gp tp FR fc cx ly st k (lt_rd cf k (H mod 2 ^ t_lb st)) ci H B x10 x13 x23 x26 m).
  Proof.
    intros until B. intros HLXB HLXZ CTX PAYR PLEN MODE SI ARR VIS HID KA LOK TOK ND16 HC HBE HH HEB HB40.
    destruct (tab_ok_root _ _ _ _ TOK) as (LB15 & NDR & ROOT).
    pose proof (sinv_bits_facts _ _ _ _ SI) as (CIN0 & CINN & BITS0 & BLE & HOLD0).
    pose proof (proj1 SI) as RN1. unfold IDefs.RNG in RN1.
    assert (CFR : forall i, 0 <= i < N_CODES -> 0 <= cf i < 4294967296) by (repeat (destruct RN1 as [_ RN1]); exact RN1). clear RN1.
    unfold L_E1.
    inf_arm_open.
    destruct (lt_facts RNG m S cf k nd LOK CODES CFR MI SHS SHLF S8 RS RSS RI RISH SB) as (DT & _).
    pose proof (pow2_le_15 lb ltac:(clear - LB15; lia)) as P15.
    assert (IDX : 0 <= H mod 2 ^ lb < 2 ^ lb) by (apply mod_pow2_bound; clear - LB15; lia).
    pose proof (ROOT _ IDX) as ROK.
    assert (IND : 0 <= H mod 2 ^ lb < nd) by (clear - IDX NDR; lia).
    destruct (DT _ IND) as (RDR & _). clear DT.
    remember (lt_rd cf k (H mod 2 ^ lb)) as c eqn:EC. apply w7hide_in in EC.
    pose proof (code_op_range c) as OPR. pose proof (code_val_range c) as VALR. pose proof (code_bits_range c) as BITR.
    pose proof (pow2_le_40 B ltac:(clear - HB40 HBE HC BITS0; lia)) as P40.
    pose proof atop_range as ATR.
    zs. change (Z.land c 255) with (code_op c).
    zs. zs. zs. zbr0 KOP.
    -
      destruct (root_term_or_link InflateState.LENS (lt_rd cf k) lb nd c ltac:(clear - LB15; lia) ROK) as [(TERM & _)|(LINK & _)]; [| exfalso; destruct (op_m1_taken _ OPR KOP) as [OPZ|OPZ]; clear - LINK OPZ; lia].
      destruct (term_lens _ _ TERM) as (TB & TCASE).
      zrung [0x91b70].
      destruct (sinv_pull _ _ lf cf ci H B SI ltac:(gcbn; clear - HC; lia) ltac:(gcbn; clear - HC; lia) ltac:(clear - HBE HC BITS0; lia) ltac:(exact HB40)
                  ltac:(clear - HH; lia) ltac:(clear - HH; lia) ltac:(clear - HBE HC BLE; lia) ltac:(gcbn; clear - HBE; lia)) as (SI1 & ME1).
      st_norm SI1. st_norm ME1.
      eapply (l_term AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh
                (ICX u S D n 6341696 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) (IST mode last flags ci cout H B out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo)
        with (c := c) (bk := 0);
        [exact HLXB| exact HLXZ| exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI1| exact ARR| inf_vis_close| inf_hid_close| eapply KALL_mono; [| exact KA]; exact ME1
        | exact RDR| gcbn; clear - TB HEB; lia| clear - TB LB15; lia| clear; lia| exact TCASE].
    -
      pose proof (op_m1_not _ OPR KOP) as LINKOP.
      destruct (root_term_or_link InflateState.LENS (lt_rd cf k) lb nd c ltac:(clear - LB15; lia) ROK) as [(_ & NL)|(_ & EB & OPL & VLO & VHI & SUB)]; [exfalso; exact (NL LINKOP)|].
      eapply (l_sub AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh
                (ICX u S D n 6341696 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo)
        with (k := k) (nd := nd) (c1 := c) (ci := ci) (H := H) (B := B);
        [exact HLXB| exact HLXZ| exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| exact VISf| exact HID| exact KA| exact LOK
        | gcbn; exact HC| gcbn; exact HBE| exact HH| exact HEB| exact HB40| exact RDR
        | clear - EB LB15; lia| clear - LINKOP; lia| clear - OPL EB; lia| clear - VHI; lia| exact ND16
        | intros j Hj; rewrite EB; exact (proj1 (SUB j Hj))].
    (* [U14B] A2 2026-11-12: v24 is a vestige binder at 1.4 (InfBBase's inf_locals no longer holds it), so eapply leaves
       it as a shelved word; any value does (G's U1A cure for v240) *)
    Unshelve. all: exact (Z_to_bv 64 0).
  Time Qed.
End S.
End CANSEC1.
