(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Lib Require Import Arr Bytes ZBridge Tac InitMem StoreFast.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Spec Require Import AsanCtrl.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.BothW Require Import BImg RtCells ABase ABytes AMalloc_iface AUri_kit.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.IK Require Import IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2A Require Import U2AShadow U2AKit U2AArr U2AStore InfAGlue InfPure InfPure_w7 InfPure_w7d InfPure_w7e InfPure_w7f InfPure_w7h InfAGlue_w7 InfAGlue_w7b.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2A Require Import U2AObj.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U1B Require Import U2BObj U2BClient U2BIface InfBBase InfBKit InfBTables InfB_w7base InfB_w7tab InfB_w7tab16 InfB_w7pull InfB_w7dsrc InfB_w7distr InfB_dist2 InfB_dist4.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U1B Require Import U2BKit U2BKit_p04 InfBTraps.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
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

  Definition D_L2 (cx : ictx) (ly : ilay) (st : ist) (TA c1 A4 T6 T0 T1 T2 T7 : Z) (x10 x12 x23 x26 x30 : word) (m : amem) : machine_state :=
    MS (mkR (Z_to_bv 64 (l_F0 ly)) (Z_to_bv 64 (l_SPA ly)) gp tp (Z_to_bv 64 T0) (Z_to_bv 64 T1) (Z_to_bv 64 T2) (Z_to_bv 64 (l_SP ly)) (Z_to_bv 64 (l_SPA ly))
            x10 (Z_to_bv 64 (c_q cx + t_cin st)) x12 (Z_to_bv 64 (SIX (code_val c1) (code_bits c1) (code_op c1) (t_hold st))) (Z_to_bv 64 A4) (Z_to_bv 64 TA) (Z_to_bv 64 1) (Z_to_bv 64 T7)
            (Z_to_bv 64 (l_Zs ly)) (Z_to_bv 64 (c_n cx - t_cin st)) (Z_to_bv 64 (2 ^ (code_bits c1 + code_op c1) - 1)) (Z_to_bv 64 2147450880) (Z_to_bv 64 (t_bits st)) (Z_to_bv 64 (t_hold st))
            (Z_to_bv 64 (Z.shiftr (l_F0 ly) 3 + 2147450880)) x23 x26 (Z_to_bv 64 (l_F0 ly)) (Z_to_bv 64 (Z.shiftr c1 8)) (Z_to_bv 64 (code_bits c1)) x30 (Z_to_bv 64 T6))
       FR (Z_to_bv 64 0x91c24) fc None m (seg_rom bsegs).

  Lemma d_loop2 : forall (N : nat) (cx : ictx) (ly : ilay) (st : ist) (lf cf wf fo : Z -> Z) (v0 v8 v16 v24 v240 j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits was pad : word)
      (x10 x12 x23 x26 x30 : word) (m : amem) (TA nd XT NS : Z) (rd : Z -> Z) (c1 A4 T6 T0 T1 T2 T7 bk : Z),
    DXS cx ly ->
    inf_ctx cx ly AI RNG LB -> Forall (fun c => 0 <= c < 256) payload -> Z.of_nat (length payload) = c_n cx ->
    t_mode st = DIST -> sinv cx st lf cf -> inf_arr_ok cx wf fo ->
    VIS cx ly st lf cf wf fo v0 v8 v16 v24 v240 (Z_to_bv 64 (code_val c1)) (Z_to_bv 64 (Z.shiftr (c_p cx + 108) 3)) j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits (Z_to_bv 64 bk) was pad m -> HIDm cx ly m -> KALLB cx ly (meas cx st) ->
    dist_src (c_p cx) cf TA nd XT NS rd -> XT mod 8 = 0 -> 0 <= XT -> XT <= TA -> TA + 4 * nd <= XT + 8 * NS ->
    rng RNG (Z.shiftr XT 3 + 2147450880) NS -> rng RNG TA (4 * nd) -> 0 < TA -> TA + 4 * nd < 140737488355328 ->
    0 <= c1 < 4294967296 -> 1 <= code_bits c1 <= 15 -> 1 <= code_op c1 -> code_op c1 <= 15 - code_bits c1 -> code_val c1 + 2 ^ code_op c1 <= nd -> nd <= 65536 ->
    (forall j, 0 <= j < 2 ^ code_op c1 -> term_ok DISTS (15 - code_bits c1) (rd (code_val c1 + j)) = true) ->
    c_n cx - t_cin st < Z.of_nat N ->
    A4 - T6 = t_bits st - code_bits c1 -> 0 <= A4 <= 40 -> code_bits c1 <= t_bits st -> 0 <= bk <= 45 ->
    T2 + T0 = c_q cx + c_n cx -> T1 + T7 = t_bits st + 8 * (c_n cx - t_cin st) -> 0 <= T0 < 67108864 -> 0 <= T1 < 536870912 -> 0 < T2 < 140737488355328 -> 0 <= T7 <= 64 ->
    evtF bsegs RNG POST (D_L2 cx ly st TA c1 A4 T6 T0 T1 T2 T7 x10 x12 x23 x26 x30 m).
  Proof.
    induction N as [|N IH]; intros until bk; intros HDX CTX PAYR PLEN MODE SI ARR VIS HID KA TS XT8 XT0 XTL XTH RXT RTA TAP TAH HC1 RB15 OP1 OP15 VND ND16 SUB HN HAS HA4 HRB HBK HT20 HT17 HT0 HT1 HT2 HT7.
    { exfalso. pose proof (sinv_bits_facts _ _ _ _ SI) as (CIN0 & CINN & _). clear - HN CINN. lia. }
    pose proof KA as (KD & KB & KL & KLV).
    pose proof (sinv_bits_facts _ _ _ _ SI) as (CIN0 & CINN & BITS0 & BLE & HOLD0).
    pose proof (code_val_range c1) as VALR.
    unfold D_L2.
    remember (code_bits c1) as rb eqn:ERB. remember (code_op c1) as op eqn:EOP. remember (code_val c1) as val eqn:EVAL.
    revert IH. inf_arm_open. intros IH.
    destruct (TS m CODES MI SHS SHDF) as (DT & DT16 & SBT).
    pose proof (pow2_le_40 bits ltac:(lia)) as P40. pose proof (pow2_le_15 (rb + op) ltac:(lia)) as P15. pose proof (pow2_le_15 rb ltac:(lia)) as PRB. pose proof (pow2_le_15 op ltac:(lia)) as POP.
    pose proof (sidx_range rb op hold ltac:(lia) ltac:(lia)) as JR.
    assert (JND : 0 <= SIX val rb op hold < nd) by (clear - JR VND VALR; lia).
    assert (TOK : term_ok InflateState.DISTS (15 - rb) (rd (SIX val rb op hold)) = true) by (replace (SIX val rb op hold) with (val + hold mod 2 ^ (rb + op) / 2 ^ rb) by (clear; lia); apply SUB; exact JR).
    destruct (term_dists _ _ TOK) as (TB & TCASE).
    remember (SIX val rb op hold) as I0 eqn:EI0. apply w7hide_in in EI0.
    destruct (DT I0 JND) as (RDR & RD0 & RD1 & RD2). pose proof (DT16 I0 JND) as RD16.
    set (c2 := rd I0) in *.
    pose proof (tab_sh0 m XT NS (TA + 4 * I0) SBT XT8 ltac:(clear - JND XTL XTH; lia) ltac:(exact XT0)) as RDS0.
    pose proof (tab_sh_acc RNG XT NS (TA + 4 * I0) RXT XT8 ltac:(clear - JND XTL XTH; lia) ltac:(exact XT0)) as ACS0.
    pose proof (tab_sh0 m XT NS (TA + 4 * I0 + 3) SBT XT8 ltac:(clear - JND XTL XTH; lia) ltac:(exact XT0)) as RDS3.
    pose proof (tab_sh_acc RNG XT NS (TA + 4 * I0 + 3) RXT XT8 ltac:(clear - JND XTL XTH; lia) ltac:(exact XT0)) as ACS3.
    zs. rewrite shl2. zs.
    zrung [0x91c50].
    pose proof (code_val_range c2) as VALR2.
    assert (LO2 : 0 <= Z.land c2 65535 < 65536) by (change 65535 with (Z.ones 16); rewrite Z.land_ones by (clear; lia); apply Z.mod_pos_bound; clear; lia).
    zs. cbv beta. rewrite (zx16_small (code_val c2)) by (clear - VALR2; lia).
    zs. cbv beta. rewrite (zx16_small (Z.land c2 65535)) by (clear - LO2; lia).
    eapply (dist_join2 RNG POST) with (c := c2) (rb := rb); [exact RDR| exact RB15|].
    zs. zbr0 KE.
    -
      apply w7hide_out in EI0. subst rb op val.
      eapply (d_fin2 AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh
                (ICX u S D n 6341056 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo)
        with (c1 := c1) (c2 := c2) (A4 := A4) (T6 := T6) (bk := bk);
        [exact HDX| exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| exact VISf| exact HID| exact KA| exact HC1| exact RDR
        | exact RB15| clear - TB RB15; lia| clear - KE; gcbn; lia| exact HAS| exact HBK| exact TCASE].
    -
      zs. zbr0 KH.
      +
        assert (CIR : 0 <= cin < n) by (clear - CIN0 CINN KH; lia).
        destruct (pull_facts RNG _ m m D n payload cin UNP MU DJP RD RSD PAYB PAYR PLEN D16 D1 CIR) as (b & RDB & CK & ACP & RDP & ACB & BZR).
        zrung [0x91c94].
        zs. zs. zs. rewrite sxb_sval.
        eapply (dist_ck2 RNG POST) with (A := D + cin) (sb := sval b); [clear - D1 CIR DL2; lia| exact CK| intros y].
        zs. zs. cbv beta. rewrite (bz_val payload cin PAYR).
        eapply (dist_six_b1 RNG POST) with (H := hold) (B := bits) (bz := bz payload cin) (rb := rb) (op := op);
          [clear - BITS0; lia| exact HOLD0| exact BZR| exact RB15| exact OP1| clear - OP15; lia|].
        pose proof (pull_bound hold bits (bz payload cin) ltac:(clear - BITS0; lia) HOLD0 BZR) as PB.
        remember (hold + bz payload cin * 2 ^ bits) as H1 eqn:EH1.
        pose proof (sidx_range rb op H1 ltac:(clear - RB15; lia) ltac:(clear - OP1; lia)) as JR1.
        zs.
        eapply (dist_six_b2 RNG POST) with (TA := TA) (J := H1 mod 2 ^ (rb + op) / 2 ^ rb) (val := val);
          [clear - JR1 VALR POP; lia| exact VALR| clear - TAP TAH VND VALR POP; lia|].
        assert (I1R : 0 <= SIX val rb op H1 < 4294967296) by (clear - JR1 VALR POP; lia).
        remember (SIX val rb op H1) as I1 eqn:EI1. apply w7hide_in in EI1.
        zs. zs. zs.
        eapply (dist_six_c RNG POST) with (TA := TA) (idx := I1) (B := bits) (T6 := T6) (HV := n - cin) (NX1 := D + cin + 1);
          [clear - BITS0; lia| exact I1R| clear - TAP TAH VND VALR POP; lia| clear - CIR NR; lia| clear - D1 CIR DL2; lia| clear - HAS HA4 RB15 BITS0; lia|].
        replace (D + cin + 1) with (D + (cin + 1)) in * by (clear; lia). replace (n - cin + -1) with (n - (cin + 1)) by (clear; lia).
        destruct (sinv_pull _ _ lf cf (cin + 1) H1 (bits + 8) SI ltac:(gcbn; clear; lia) ltac:(gcbn; clear - CIR; lia) ltac:(clear - BITS0; lia) ltac:(clear - KE TB RB15; lia)
                    ltac:(clear - PB; lia) ltac:(clear - PB; lia) ltac:(clear - BLE; lia) ltac:(gcbn; clear; lia)) as (SI1 & ME1).
        st_norm SI1. st_norm ME1.
        apply w7hide_out in EI1. subst I1 H1 rb op val.
        eapply (IH (ICX u S D n 6341056 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) (IST mode last flags (cin + 1) cout (hold + bz payload cin * 2 ^ bits) (bits + 8) out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo)
          with (TA := TA) (nd := nd) (XT := XT) (NS := NS) (rd := rd) (c1 := c1) (A4 := A4) (T6 := T6 + -8) (T0 := T0) (T1 := T1) (T2 := T2) (T7 := T7) (bk := bk);
          [exact HDX| exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI1| exact ARR| inf_vis_close| inf_hid_close| eapply KALL_mono; [| exact KA]; exact ME1
          | exact TS| exact XT8| exact XT0| exact XTL| exact XTH| exact RXT| exact RTA| exact TAP| exact TAH
          | exact HC1| exact RB15| exact OP1| exact OP15| exact VND| exact ND16
          | exact SUB
          | gcbn; clear - HN CIR; lia| gcbn; clear - HAS; lia| exact HA4| gcbn; clear - HRB; lia| exact HBK
          | gcbn; exact HT20| gcbn; clear - HT17; lia| exact HT0| exact HT1| exact HT2| exact HT7].
      +
        zrung [0x933cc].
        assert (ECI : cin = n) by (clear - KH CINN; lia).
        replace (T1 + T7) with bits by (clear - HT17 ECI; icx_cbn; lia).
        replace (T2 + T0) with (D + cin) in * by (clear - HT20 ECI; icx_cbn; lia).
        replace (Z_to_bv 64 0) with (Z_to_bv 64 (n - cin)) by (f_equal; clear - ECI; lia).
        eapply (KLV (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) ret lf cf wf fo);
          [exact SI| exact ARR| inf_vis_close| inf_hid_close].
    (* [U14B] A2 2026-11-12: v24 is a vestige binder at 1.4 (InfBBase's inf_locals no longer holds it), so eapply leaves
       it as a shelved word; any value does (G's U1A cure for v240) *)
    Unshelve. all: exact (Z_to_bv 64 0).
  Time Qed.
End S.
End CANSEC1.
