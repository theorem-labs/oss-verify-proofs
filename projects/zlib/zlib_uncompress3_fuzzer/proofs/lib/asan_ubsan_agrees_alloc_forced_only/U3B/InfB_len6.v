(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Lib Require Import Arr Bytes ZBridge Tac InitMem StoreFast.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Spec Require Import AsanCtrl.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.BothW Require Import BImg RtCells ABase ABytes AMalloc_iface AUri_kit.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.IK Require Import IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2A Require Import U2AShadow U2AKit U2AArr U2AStore InfAGlue InfPure InfPure_w7 InfPure_w7d InfPure_w7e InfPure_w7f InfPure_w7h InfAGlue_w7 InfAGlue_w7b.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2A Require Import U2AObj.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U3B Require Import U2BObj U2BClient U2BIface InfBBase InfBKit InfBTables InfB_w7base InfB_w7tab InfB_w7tab16 InfB_w7pull InfB_w7ltab InfB_w7lenr InfB_len13S InfB_len2 InfB_len4 InfB_len5 InfB_len5b InfB_len3 InfB_len1 InfB_lenx InfB_lenFS.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U3B Require Import U2BKit U2BKit_p04 InfBTraps.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
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



  Notation GARM cx ly Lb X := (garm_stmtA cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh Lb X).
  Notation LFAST cx ly := (LFAST_STMT AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh cx ly).

  Lemma len_slow_k : forall (cx : ictx) (ly : ilay) (st : ist) (lf cf wf fo : Z -> Z) (v0 v8 v16 v24 v240 v328 j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word)
      (x6 x7 x10 x11 x12 x13 x14 x16 x19 x21 x22 x23 x26 x28 x29 x30 x31 : word) (m : amem) (k : ltk) (nd : Z),
    LXB cx ly -> LXZ cx ly ->
    inf_ctx cx ly AI RNG LB -> Forall (fun c => 0 <= c < 256) payload -> Z.of_nat (length payload) = c_n cx ->
    t_mode st = LEN -> sinv cx st lf cf -> inf_arr_ok cx wf fo ->
    VIS cx ly st lf cf wf fo v0 v8 v16 v24 v240 v328 (Z_to_bv 64 (Z.shiftr (c_p cx + 108) 3)) j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m -> HIDm cx ly m -> KALLB cx ly (meas cx st) ->
    lt_ok k nd -> cp_addrA (c_p cx) (t_lc st) = lt_TA (c_p cx) k -> tab_ok LENS (lt_rd cf k) (t_lb st) nd = true -> nd <= 65536 ->
    evtF bsegs RNG POST (GARM_MS cx ly gp tp FR fc 0x918e8 st x6 x7 x10 x11 x12 x13 x14 x16 x19 x21 x22 x23 x26 x28 x29 x30 x31 m).
  Proof.
    intros until nd. intros HLXB HLXZ CTX PAYR PLEN MODE SI ARR VIS HID KA LOK ETA TOK ND16.
    destruct (tab_ok_root _ _ _ _ TOK) as (LB15 & NDR & ROOT).
    pose proof (sinv_bits_facts _ _ _ _ SI) as (CIN0 & CINN & BITS0 & BLE & HOLD0).
    pose proof (proj1 SI) as RN1. unfold IDefs.RNG in RN1.
    assert (CFR : forall i, 0 <= i < N_CODES -> 0 <= cf i < 4294967296) by (repeat (destruct RN1 as [_ RN1]); exact RN1). clear RN1.
    unfold GARM_MS.
    inf_arm_open.
    destruct (lt_facts RNG m S cf k nd LOK CODES CFR MI SHS SHLF S8 RS RSS RI RISH SB) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & TAP & TAH).
    rewrite ETA in SSC.
    remember (lt_TA S k) as TA eqn:ETA'.
    zrung [0x91944].
    zs. rewrite (zx32_small lb) by (clear - LB15; lia).
    zrung [0x91954].
    pose proof (pow2_le_40 bits ltac:(clear - BITS0; lia)) as P40. pose proof (pow2_le_15 lb ltac:(clear - LB15; lia)) as P15.
    eapply (len_root_a RNG POST) with (H := hold) (lb := lb) (TA := TA); [clear - HOLD0 P40; lia| exact LB15| clear - TAP TAH NDR P15; lia|].
    eapply (len_prep RNG POST) with (B := bits) (HV := n - cin); [clear - BITS0; lia| clear - CIN0 CINN NR; lia|].
    zrung [0x919ac].
    subst TA.
    repeat match goal with HS : rw_cells _ _ _ _ |- _ => rewrite <- ETA in HS end.
    eapply (l_loop1 AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh (Datatypes.S (Z.to_nat (n - cin)))
              (ICX u S D n 6341952 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo)
      with (k := k) (nd := nd) (ci := cin) (H := hold) (B := bits);
      [exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| inf_vis_close| inf_hid_close| exact KA| exact LOK| exact TOK| exact ND16
      | | gcbn; clear - CIN0 CINN; lia| gcbn; clear - CIN0 CINN; lia| gcbn; clear; lia| exact HOLD0| clear - BITS0; lia].
    intros ci' H' B' x10' x13' x23' x26' HC' HBE' HH' HEB' HB40'.
    eapply (l_root AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh
              (ICX u S D n 6341952 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo)
      with (k := k) (nd := nd) (ci := ci') (H := H') (B := B');
      [exact HLXB| exact HLXZ| exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| inf_vis_close| inf_hid_close| exact KA| exact LOK| exact TOK| exact ND16
      | exact HC'| exact HBE'| exact HH'| exact HEB'| exact HB40'].
    (* [U14B] A2 2026-11-12: v24 is a vestige binder at 1.4 (InfBBase's inf_locals no longer holds it), so eapply leaves
       it as a shelved word; any value does (G's U1A cure for v240) *)
    Unshelve. all: exact (Z_to_bv 64 0).
  Time Qed.

  Lemma len_slow : forall (cx : ictx) (ly : ilay) (st : ist) (lf cf wf fo : Z -> Z) (v0 v8 v16 v24 v240 v328 j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word)
      (x6 x7 x10 x11 x12 x13 x14 x16 x19 x21 x22 x23 x26 x28 x29 x30 x31 : word) (m : amem),
    LXB cx ly -> LXZ cx ly ->
    inf_ctx cx ly AI RNG LB -> Forall (fun c => 0 <= c < 256) payload -> Z.of_nat (length payload) = c_n cx ->
    t_mode st = LEN -> sinv cx st lf cf -> inf_arr_ok cx wf fo ->
    VIS cx ly st lf cf wf fo v0 v8 v16 v24 v240 v328 (Z_to_bv 64 (Z.shiftr (c_p cx + 108) 3)) j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m -> HIDm cx ly m -> KALLB cx ly (meas cx st) ->
    evtF bsegs RNG POST (GARM_MS cx ly gp tp FR fc 0x918e8 st x6 x7 x10 x11 x12 x13 x14 x16 x19 x21 x22 x23 x26 x28 x29 x30 x31 m).
  Proof.
    intros until m. intros HLXB HLXZ CTX PAYR PLEN MODE SI ARR VIS HID KA.
    assert (LIVE : codes_liveP (t_mode st)) by (rewrite MODE; exact codes_live_LEN).
    destruct (sinv_tabs_cases _ _ _ _ SI LIVE) as [(o & ELC & EDC & LB15 & DB15 & O0 & ONX & NX & TL & TD)|(ELC & EDC & ELB & EDB & TL & TD)].
    -
      eapply (len_slow_k cx ly st lf cf wf fo) with (k := LTDyn 0) (nd := o);
        [exact HLXB| exact HLXZ| exact CTX| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| exact VIS| exact HID| exact KA
        | cbn [lt_ok]; clear - O0 ONX NX; lia| rewrite ELC; reflexivity| exact TL| clear - ONX NX; lia].
    -
      eapply (len_slow_k cx ly st lf cf wf fo) with (k := LTFix) (nd := 512);
        [exact HLXB| exact HLXZ| exact CTX| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| exact VIS| exact HID| exact KA
        | reflexivity| rewrite ELC; reflexivity| rewrite ELB; exact TL| clear; lia].
  Qed.

  Theorem len_garm : forall cx ly, GARM cx ly 0x91d9c DIST -> LFAST cx ly -> GARM cx ly 0x9174c LEN.
  Proof.
    intros cx ly HDIST HFAST.
    assert (HLXB : LXB cx ly) by (unfold LXB_STMT; intros; eapply (lenx_body AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh cx ly); eassumption).
    assert (HLXZ : LXZ cx ly) by (unfold LXZ_STMT; intros; eapply (lenx_zero AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh cx ly); eassumption).
    unfold garm_stmtA. intros until m. intros CTX PAYR PLEN MODE SI ARR VIS HID KA.
    pose proof (sinv_bits_facts _ _ _ _ SI) as (CIN0 & CINN & BITS0 & BLE & HOLD0).
    unfold GARM_MS.
    inf_arm_open.
    zs. zs. zbr0 K6.
    - eapply (len_slow (ICX u S D n 6341952 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo);
        [exact HLXB| exact HLXZ| exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| exact VISf| exact HID| exact KA].
    - zs. zs. zs. zbr0 K258.
      + eapply (len_slow (ICX u S D n 6341952 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo);
          [exact HLXB| exact HLXZ| exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| exact VISf| exact HID| exact KA].
      + (* [U14B] A2 2026-11-12: 1.4's third test, bits > 7 -> the slow path. LFAST_STMT keeps its statement (no bits premise is needed by InfB_lenF). *)
        zs. zs. zbr0 K7.
        * eapply (len_slow (ICX u S D n 6341952 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo);
            [exact HLXB| exact HLXZ| exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| exact VISf| exact HID| exact KA].
        * eapply (HFAST (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo);
            [exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| exact VISf| exact HID| exact KA| clear - K6; gcbn; lia| clear - K258; gcbn; lia].
  Time Qed.
End S.
End CANSEC1.
