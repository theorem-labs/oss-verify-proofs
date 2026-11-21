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
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.U1B Require Import U2BObj U2BClient U2BIface InfBBase InfBKit InfBTables InfB_w7base InfB_w7tab InfB_w7tab16 InfB_w7pull InfB_w7dsrc InfB_w7distr InfB_dist2 InfB_dist4 InfB_dist5 InfB_dist3 InfB_dist1 InfB_distx.
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
Section S.
  Variable AI : AMallocIface.
  Variables (L : alayout) (RNG : footprint) (stA : astate) (LB : list ablock).
  Variables (gp tp : word) (FR : bvmap 5 word) (fc : bv 32) (POST : machine_state -> Prop).
  Variables (LBc : list ablock) (m0 : amem) (payload : list Z) (fw : Z -> Z) (saved fk fksh : list cell).

  Notation KALLB cx ly B := (KALL cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh B).
  Notation VIS cx ly st lf cf wf fo v0 v8 v16 v24 v240 v328 v512 j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m :=
    (inf_vis cx ly st lf cf wf fo payload v0 v8 v16 v24 v240 v328 v512 j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m).
  Notation HIDm cx ly m := (inf_hid cx ly AI L RNG stA LB LBc m0 fw saved fk fksh m).
  Notation GARM cx ly Lb X := (garm_stmtA cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh Lb X).
  Notation DXS cx ly := (DX_STMT AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh cx ly).

  Notation SIX val rb op H := (H mod 2 ^ (rb + op) / 2 ^ rb + val).

  Lemma dist_entry : forall (cx : ictx) (ly : ilay) (st : ist) (lf cf wf fo : Z -> Z) (v0 v8 v16 v24 v240 v328 j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits was pad : word)
      (x6 x7 x10 x11 x12 x13 x14 x16 x19 x21 x22 x23 x26 x28 x29 x30 x31 : word) (m : amem) (TA nd XT NS : Z) (rd : Z -> Z) (bk : Z),
    DXS cx ly ->
    inf_ctx cx ly AI RNG LB -> Forall (fun c => 0 <= c < 256) payload -> Z.of_nat (length payload) = c_n cx ->
    t_mode st = DIST -> sinv cx st lf cf -> inf_arr_ok cx wf fo ->
    VIS cx ly st lf cf wf fo v0 v8 v16 v24 v240 v328 (Z_to_bv 64 (Z.shiftr (c_p cx + 108) 3)) j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits (Z_to_bv 64 bk) was pad m -> HIDm cx ly m -> KALLB cx ly (meas cx st) ->
    cp_addrA (c_p cx) (t_dc st) = TA ->
    dist_src (c_p cx) cf TA nd XT NS rd -> XT mod 8 = 0 -> 0 <= XT -> XT <= TA -> TA + 4 * nd <= XT + 8 * NS ->
    rng RNG (Z.shiftr XT 3 + 2147450880) NS -> rng RNG TA (4 * nd) -> 0 < TA -> TA + 4 * nd < 140737488355328 ->
    tab_ok DISTS rd (t_db st) nd = true -> nd <= 65536 -> 0 <= bk <= 45 ->
    evtF bsegs RNG POST (GARM_MS cx ly gp tp FR fc 0x91a10 st x6 x7 x10 x11 x12 x13 x14 x16 x19 x21 x22 x23 x26 x28 x29 x30 x31 m).
  Proof.
    intros until bk. intros HDX CTX PAYR PLEN MODE SI ARR VIS HID KA ETA TS XT8 XT0 XTL XTH RXT RTA TAP TAH TOK ND16 HBK.
    destruct (tab_ok_root _ _ _ _ TOK) as (DB15 & NDR & ROOT).
    pose proof (sinv_bits_facts _ _ _ _ SI) as (CIN0 & CINN & BITS0 & BLE & HOLD0).
    unfold GARM_MS.
    inf_arm_open.
    rewrite ETA in SSC.
    zrung [0x91a4c].
    rewrite (zx32_small db) by (clear - DB15; lia).
    pose proof (pow2_le_40 bits ltac:(clear - BITS0; lia)) as P40.
    eapply (dist_root_a RNG POST) with (TA := TA) (db := db) (H := hold) (B0 := bits) (HV0 := n - cin);
      [clear - HOLD0 P40; lia| exact DB15| clear - TAP TAH NDR DB15; pose proof (pow2_le_15 db ltac:(lia)); lia| exact BITS0| clear - CIN0 CINN NR; lia|].
    zs. zs.
    eapply (d_loop1 AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh (Datatypes.S (Z.to_nat (n - cin)))
              (ICX u S D n 6341056 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo)
      with (TA := TA) (nd := nd) (XT := XT) (NS := NS) (rd := rd) (ci := cin) (H := hold) (B := bits) (bk := bk);
      [exact HDX| exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| exact VISf| exact HID| exact KA
      | exact TS| exact XT8| exact XT0| exact XTL| exact XTH| exact RXT| exact RTA| exact TAP| exact TAH
      | exact TOK| exact ND16| exact HBK
      | gcbn; clear - CINN; lia| gcbn; clear - CIN0 CINN; lia| gcbn; clear; lia| gcbn; exact HOLD0| gcbn; clear - BITS0; lia].
  Time Qed.

  Theorem dist_garm : forall cx ly, GARM cx ly 0x91f8c MATCH -> GARM cx ly 0x91a10 DIST.
  Proof.
    intros cx ly HMATCH. unfold garm_stmtA. intros until m. intros CTX PAYR PLEN MODE SI ARR VIS HID KA.
    assert (HDX : DXS cx ly).
    { unfold DX_STMT. intros. eapply (distx_body AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh cx ly); eassumption. }
    assert (LIVE : codes_liveP (t_mode st)) by (rewrite MODE; exact codes_live_DIST).
    pose proof CTX as (S16 & SB & _ & _ & _ & _ & _ & _ & _ & RS & RSS & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RI & RISH & _).
    pose proof VIS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & BKOK0).
    unfold back_ok in BKOK0. destruct BKOK0 as [_ BKD]. destruct (BKD MODE) as (bk & EBK & BKR). subst back.
    pose proof (ablk_lin _ _ SB) as (SB1 & SB2 & SB3 & SB4). unfold AIMG_HI in SB1. change (2 ^ 47) with 140737488355328 in SB4.
    pose proof (proj1 SI) as RN0. unfold IDefs.RNG in RN0.
    assert (CFR : forall i, 0 <= i < N_CODES -> 0 <= cf i < 4294967296) by (repeat (destruct RN0 as [_ RN0]); exact RN0).
    destruct (sinv_tabs_cases _ _ _ _ SI LIVE) as [(o & ELC & EDC & LB15 & DB15 & O0 & ONX & NX & TL & TD)|(ELC & EDC & ELB & EDB & TL & TD)].
    -
      eapply (dist_entry cx ly st lf cf wf fo) with (TA := c_p cx + 1384 + 4 * o) (nd := t_nx st - o) (XT := c_p cx) (NS := 897) (rd := rdc cf (CDyn o)) (bk := bk);
        [exact HDX| exact CTX| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| exact VIS| exact HID| exact KA
        | rewrite EDC; reflexivity
        | apply dist_src_dyn; [exact CFR| lia| lia| lia]
        | clear - S16; Z.div_mod_to_equations; lia| lia| lia| lia| exact RSS
        | eapply rng_sub'; [exact RS| lia] | lia| lia| exact TD| lia| exact BKR].
    -
      eapply (dist_entry cx ly st lf cf wf fo) with (TA := 152160) (nd := 32) (XT := 152160) (NS := 16) (rd := rdc (fun _ => 0) CDistfix) (bk := bk);
        [exact HDX| exact CTX| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| exact VIS| exact HID| exact KA
        | rewrite EDC; reflexivity
        | apply dist_src_fix
        | reflexivity| lia| lia| lia
        | eapply rng_sub'; [exact RISH| cbv; split; discriminate]
        | eapply rng_sub'; [exact RI| cbv; split; discriminate] | lia| lia| rewrite EDB; exact TD| lia| exact BKR].
  Qed.
End S.
End CANSEC1.
