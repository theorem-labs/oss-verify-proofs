(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Lib Require Import Arr Bytes ZBridge Tac InitMem StoreFast.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Spec Require Import AsanCtrl.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.BothW Require Import BImg RtCells ABase ABytes AMalloc_iface AUri_kit.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.IK Require Import IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2A Require Import U2AShadow U2AKit U2AArr U2AObj U2AStore InfAGlue InfPure InfPure_w7 InfPure_w7d InfPure_w7e InfPure_w7f InfPure_w7h InfAGlue_w7 InfAGlue_w7b.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2B Require Import U2BObj U2BClient U2BIface InfBBase InfBKit InfBTables InfB_w7base InfB_w7tab InfB_w7tab16 InfB_w7pull InfB_w7dsrc InfB_w7distr InfB_dist2 InfB_dist4 InfB_dist5.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2B Require Import U2BKit U2BKit_p04 InfBTraps.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
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
  Notation DXS cx ly := (DX_STMT AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh cx ly).

  Notation SIX val rb op H := (H mod 2 ^ (rb + op) / 2 ^ rb + val).

  Definition D_E2 (cx : ictx) (ly : ilay) (st : ist) (TA c1 ci H B : Z) (x10 x13 x19 x21 x22 x23 x26 x31 : word) (m : amem) : machine_state :=
    MS (mkR (Z_to_bv 64 (l_F0 ly)) (Z_to_bv 64 (l_SPA ly)) gp tp (Z_to_bv 64 (c_n cx - ci)) (Z_to_bv 64 (8 * (c_n cx - ci))) (Z_to_bv 64 (c_q cx + ci)) (Z_to_bv 64 (l_SP ly)) (Z_to_bv 64 (l_SPA ly))
            x10 (Z_to_bv 64 (c_q cx + ci)) (Z_to_bv 64 c1) x13 (Z_to_bv 64 B) (Z_to_bv 64 TA) (Z_to_bv 64 1) (Z_to_bv 64 B)
            (Z_to_bv 64 (l_Zs ly)) x19 x21 (Z_to_bv 64 2147450880) x22 (Z_to_bv 64 H)
            (Z_to_bv 64 (Z.shiftr (l_F0 ly) 3 + 2147450880)) x23 x26 (Z_to_bv 64 (l_F0 ly)) (Z_to_bv 64 (Z.shiftr c1 8)) (Z_to_bv 64 (code_bits c1)) (Z_to_bv 64 (c_n cx - ci)) x31)
       FR (Z_to_bv 64 0x91e48) fc None m (seg_rom bsegs).

  Lemma d_sub : forall (cx : ictx) (ly : ilay) (st : ist) (lf cf wf fo : Z -> Z) (v0 v8 v16 v24 v240 v328 j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits was pad : word)
      (x10 x13 x19 x21 x22 x23 x26 x31 : word) (m : amem) (TA nd XT NS : Z) (rd : Z -> Z) (c1 ci H B bk : Z),
    DXS cx ly ->
    inf_ctx cx ly AI RNG LB -> Forall (fun c => 0 <= c < 256) payload -> Z.of_nat (length payload) = c_n cx ->
    t_mode st = DIST -> sinv cx st lf cf -> inf_arr_ok cx wf fo ->
    VIS cx ly st lf cf wf fo v0 v8 v16 v24 v240 v328 (Z_to_bv 64 (Z.shiftr (c_p cx + 108) 3)) j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits (Z_to_bv 64 bk) was pad m -> HIDm cx ly m -> KALLB cx ly (meas cx st) ->
    dist_src (c_p cx) cf TA nd XT NS rd -> XT mod 8 = 0 -> 0 <= XT -> XT <= TA -> TA + 4 * nd <= XT + 8 * NS ->
    rng RNG (Z.shiftr XT 3 + 2147450880) NS -> rng RNG TA (4 * nd) -> 0 < TA -> TA + 4 * nd < 140737488355328 ->
    t_cin st <= ci <= c_n cx -> B = t_bits st + 8 * (ci - t_cin st) -> 0 <= H < 2 ^ B -> code_bits c1 <= B -> B <= 40 -> 0 <= bk <= 45 ->
    0 <= c1 < 4294967296 -> 1 <= code_bits c1 <= 15 -> 1 <= code_op c1 -> code_op c1 <= 15 - code_bits c1 -> code_val c1 + 2 ^ code_op c1 <= nd -> nd <= 65536 ->
    (forall j, 0 <= j < 2 ^ code_op c1 -> term_ok DISTS (15 - code_bits c1) (rd (code_val c1 + j)) = true) ->
    evtF bsegs RNG POST (D_E2 cx ly st TA c1 ci H B x10 x13 x19 x21 x22 x23 x26 x31 m).
  Proof.
    intros until bk. intros HDX CTX PAYR PLEN MODE SI ARR VIS HID KA TS XT8 XT0 XTL XTH RXT RTA TAP TAH HC HBE HH HRB HB40 HBK HC1 RB15 OP1 OP15 VND ND16 SUB.
    pose proof (sinv_bits_facts _ _ _ _ SI) as (CIN0 & CINN & BITS0 & BLE & HOLD0).
    pose proof (code_val_range c1) as VALR.
    unfold D_E2.
    inf_arm_open.
    pose proof (pow2_le_40 B ltac:(lia)) as P40. pose proof (pow2_le_15 (code_bits c1 + code_op c1) ltac:(lia)) as P15. pose proof (pow2_le_15 (code_bits c1) ltac:(lia)) as PRB. pose proof (pow2_le_15 (code_op c1) ltac:(lia)) as POP.
    pose proof (sidx_range (code_bits c1) (code_op c1) H ltac:(lia) ltac:(lia)) as JR.
    eapply (dist_six_a1 RNG POST) with (c1 := c1) (H := H); [clear - HH P40; lia| exact HC1| exact RB15| exact OP1| clear - OP15; lia|].
    zs.
    eapply (dist_six_a2 RNG POST) with (TA := TA) (J := H mod 2 ^ (code_bits c1 + code_op c1) / 2 ^ code_bits c1) (val := code_val c1) (rb := code_bits c1) (B := B);
      [clear - JR POP; lia| exact VALR| clear - TAP TAH VND VALR POP; lia|].
    zs. zs.
    destruct (sinv_pull _ _ lf cf ci H B SI ltac:(gcbn; clear - HC; lia) ltac:(gcbn; clear - HC; lia) ltac:(clear - HBE BITS0 HC; lia) ltac:(exact HB40) ltac:(clear - HH; lia) ltac:(clear - HH; lia)
                ltac:(clear - HBE BLE HC; lia) ltac:(gcbn; clear - HBE; lia)) as (SI1 & ME1).
    st_norm SI1. st_norm ME1.
    eapply (d_loop2 AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh (Datatypes.S (Z.to_nat (n - ci)))
              (ICX u S D n 6341696 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) (IST mode last flags ci cout H B out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo)
      with (TA := TA) (nd := nd) (XT := XT) (NS := NS) (rd := rd) (c1 := c1) (A4 := B) (T6 := code_bits c1) (T0 := n - ci) (T1 := 8 * (n - ci)) (T2 := D + ci) (T7 := B) (bk := bk);
      [exact HDX| exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI1| exact ARR| inf_vis_close| inf_hid_close| eapply KALL_mono; [| exact KA]; exact ME1
      | exact TS| exact XT8| exact XT0| exact XTL| exact XTH| exact RXT| exact RTA| exact TAP| exact TAH
      | exact HC1| exact RB15| exact OP1| exact OP15| exact VND| exact ND16| exact SUB
      | gcbn; clear - HC; lia| gcbn; clear; lia| clear - HB40 HBE BITS0 HC; lia| gcbn; exact HRB| exact HBK
      | gcbn; clear; lia| gcbn; clear; lia| clear - HC NR CIN0; lia| clear - HC NR CIN0; lia| clear - D1 HC DL2 CIN0; lia| clear - HB40 HBE BITS0 HC; lia].
    (* [U14B] A2 2026-11-12: v24 is a vestige binder at 1.4 (InfBBase's inf_locals no longer holds it), so eapply leaves
       it as a shelved word; any value does (G's U1A cure for v240) *)
    Unshelve. all: exact (Z_to_bv 64 0).
  Time Qed.

  Definition D_E1 (cx : ictx) (ly : ilay) (st : ist) (TA c1 ci H B : Z) (x10 x13 x19 x21 x22 x23 x26 x31 : word) (m : amem) : machine_state :=
    MS (mkR (Z_to_bv 64 (l_F0 ly)) (Z_to_bv 64 (l_SPA ly)) gp tp (Z_to_bv 64 (c_n cx - ci)) (Z_to_bv 64 (8 * (c_n cx - ci))) (Z_to_bv 64 (c_q cx + ci)) (Z_to_bv 64 (l_SP ly)) (Z_to_bv 64 (l_SPA ly))
            x10 (Z_to_bv 64 (c_q cx + ci)) (Z_to_bv 64 c1) x13 (Z_to_bv 64 B) (Z_to_bv 64 TA) (Z_to_bv 64 1) (Z_to_bv 64 B)
            (Z_to_bv 64 (l_Zs ly)) x19 x21 (Z_to_bv 64 2147450880) x22 (Z_to_bv 64 H)
            (Z_to_bv 64 (Z.shiftr (l_F0 ly) 3 + 2147450880)) x23 x26 (Z_to_bv 64 (l_F0 ly)) (Z_to_bv 64 (Z.shiftr c1 8)) (Z_to_bv 64 (code_bits c1)) (Z_to_bv 64 (c_n cx - ci)) x31)
       FR (Z_to_bv 64 0x91e3c) fc None m (seg_rom bsegs).

  Lemma d_root : forall (cx : ictx) (ly : ilay) (st : ist) (lf cf wf fo : Z -> Z) (v0 v8 v16 v24 v240 v328 j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits was pad : word)
      (x10 x13 x19 x21 x22 x23 x26 x31 : word) (m : amem) (TA nd XT NS : Z) (rd : Z -> Z) (c1 ci H B bk : Z),
    DXS cx ly ->
    inf_ctx cx ly AI RNG LB -> Forall (fun c => 0 <= c < 256) payload -> Z.of_nat (length payload) = c_n cx ->
    t_mode st = DIST -> sinv cx st lf cf -> inf_arr_ok cx wf fo ->
    VIS cx ly st lf cf wf fo v0 v8 v16 v24 v240 v328 (Z_to_bv 64 (Z.shiftr (c_p cx + 108) 3)) j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits (Z_to_bv 64 bk) was pad m -> HIDm cx ly m -> KALLB cx ly (meas cx st) ->
    dist_src (c_p cx) cf TA nd XT NS rd -> XT mod 8 = 0 -> 0 <= XT -> XT <= TA -> TA + 4 * nd <= XT + 8 * NS ->
    rng RNG (Z.shiftr XT 3 + 2147450880) NS -> rng RNG TA (4 * nd) -> 0 < TA -> TA + 4 * nd < 140737488355328 ->
    t_cin st <= ci <= c_n cx -> B = t_bits st + 8 * (ci - t_cin st) -> 0 <= H < 2 ^ B -> code_bits c1 <= B -> B <= 40 -> 0 <= bk <= 45 ->
    0 <= c1 < 4294967296 -> 1 <= t_db st <= 15 -> root_ok DISTS rd (t_db st) nd c1 = true -> nd <= 65536 ->
    evtF bsegs RNG POST (D_E1 cx ly st TA c1 ci H B x10 x13 x19 x21 x22 x23 x26 x31 m).
  Proof.
    intros until bk. intros HDX CTX PAYR PLEN MODE SI ARR VIS HID KA TS XT8 XT0 XTL XTH RXT RTA TAP TAH HC HBE HH HRB HB40 HBK HC1 DB15 ROK ND16.
    pose proof (sinv_bits_facts _ _ _ _ SI) as (CIN0 & CINN & BITS0 & BLE & HOLD0).
    pose proof (code_op_range c1) as OPR.
    unfold D_E1.
    inf_arm_open.
    zs. rewrite ?(Z.mod_small c1 18446744073709551616) by (clear - HC1; lia). change (Z.land c1 255) with (code_op c1).
    zs. zs. zbr0 KOP.
    -
      destruct (root_term_or_link DISTS rd db nd c1 ltac:(clear - DB15; lia) ROK) as [(TERM & _)|(LINK & _)]; [| exfalso; clear - LINK KOP; lia].
      destruct (term_dists _ _ TERM) as (TB & TCASE).
      zrung [0x92030].
      destruct (sinv_pull _ _ lf cf ci H B SI ltac:(gcbn; clear - HC; lia) ltac:(gcbn; clear - HC; lia) ltac:(clear - HBE BITS0 HC; lia) ltac:(exact HB40) ltac:(clear - HH; lia) ltac:(clear - HH; lia)
                  ltac:(clear - HBE BLE HC; lia) ltac:(gcbn; clear - HBE; lia)) as (SI1 & ME1).
      st_norm SI1. st_norm ME1.
      eapply (d_term AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh
                (ICX u S D n 6341696 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) (IST mode last flags ci cout H B out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo)
        with (c := c1) (bk := bk);
        [exact HDX| exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI1| exact ARR| inf_vis_close| inf_hid_close| eapply KALL_mono; [| exact KA]; exact ME1
        | exact HC1| gcbn; clear - TB HRB; lia| clear - TB DB15; lia| clear - HBK; lia| exact TCASE].
    -
      destruct (root_term_or_link DISTS rd db nd c1 ltac:(clear - DB15; lia) ROK) as [(TERM & _)|(LINK & EB & OPL & VLO & VHI & SUBJ)].
      + exfalso. destruct (term_dists _ _ TERM) as (_ & [(O1 & _)|O64]); [clear - O1 KOP; lia|].
        apply O64. clear - KOP OPR. assert (C : 0 <= code_op c1 <= 15) by lia. revert C. generalize (code_op c1). intros op C. zcases op 0 15; reflexivity.
      + eapply (d_sub (ICX u S D n 6341696 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo)
          with (TA := TA) (nd := nd) (XT := XT) (NS := NS) (rd := rd) (c1 := c1) (ci := ci) (H := H) (B := B) (bk := bk);
          [exact HDX| exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| exact VISf| exact HID| exact KA
          | exact TS| exact XT8| exact XT0| exact XTL| exact XTH| exact RXT| exact RTA| exact TAP| exact TAH
          | gcbn; exact HC| gcbn; exact HBE| exact HH| exact HRB| exact HB40| exact HBK
          | exact HC1| clear - EB DB15; lia| clear - LINK; lia| clear - OPL EB; lia| exact VHI| exact ND16
          | intros j Hj; rewrite EB; exact (proj1 (SUBJ j Hj))].
    (* [U14B] A2 2026-11-12: v24 is a vestige binder at 1.4 (InfBBase's inf_locals no longer holds it), so eapply leaves
       it as a shelved word; any value does (G's U1A cure for v240) *)
    Unshelve. all: exact (Z_to_bv 64 0).
  Time Qed.
End S.
End CANSEC1.
