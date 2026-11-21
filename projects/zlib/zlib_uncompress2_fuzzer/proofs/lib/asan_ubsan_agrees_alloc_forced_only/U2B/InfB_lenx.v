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
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2A Require Import U2AShadow U2AKit U2AArr U2AObj U2AStore InfAGlue InfPure InfPure_w7 InfPure_w7e InfAGlue_w7.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2B Require Import U2BObj U2BClient U2BIface InfBBase InfBKit InfBTables InfB_w7base InfB_w7tab InfB_w7tab16 InfB_w7pull InfB_w7lenr.
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
  Notation GARM cx ly Lb X := (garm_stmtA cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh Lb X).

  Lemma lenx_tail : forall (cx : ictx) (ly : ilay) (st : ist) (lf cf wf fo : Z -> Z) (v0 v8 v16 v24 v240 v328 j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word)
      (x5 x6 x7 x10 x11 x16 x17 x19 x21 x22 x23 x26 x28 x29 x30 x31 : word) (m : amem) (ci H B : Z),
    GARM cx ly 0x91cb0 DIST ->
    inf_ctx cx ly AI RNG LB -> Forall (fun c => 0 <= c < 256) payload -> Z.of_nat (length payload) = c_n cx ->
    t_mode st = LENEXT -> sinv cx st lf cf -> inf_arr_ok cx wf fo ->
    VIS cx ly st lf cf wf fo v0 v8 v16 v24 v240 v328 (Z_to_bv 64 (Z.shiftr (c_p cx + 108) 3)) j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m -> HIDm cx ly m -> KALLB cx ly (meas cx st) ->
    t_cin st <= ci <= c_n cx -> 1 <= t_extra st <= B -> B <= 40 -> 0 <= H < 2 ^ B -> B <= 8 * ci ->
    8 * (c_n cx - ci) + B = 8 * (c_n cx - t_cin st) + t_bits st ->
    evtF bsegs RNG POST
      (MS (mkR (Z_to_bv 64 (l_F0 ly)) (Z_to_bv 64 (l_SPA ly)) gp tp x5 x6 x7 (Z_to_bv 64 (l_SP ly)) (Z_to_bv 64 (l_SPA ly)) x10 x11
               (Z_to_bv 64 (c_n cx - ci)) (Z_to_bv 64 (t_extra st)) (Z_to_bv 64 (c_q cx + ci)) (Z_to_bv 64 B) x16 x17
               (Z_to_bv 64 (l_Zs ly)) x19 x21 (Z_to_bv 64 2147450880) x22 (Z_to_bv 64 H)
               (Z_to_bv 64 (Z.shiftr (l_F0 ly) 3 + 2147450880)) x23 x26 (Z_to_bv 64 (l_F0 ly)) x28 x29 x30 x31)
          FR (Z_to_bv 64 0x90160) fc None m (seg_rom bsegs)).
  Proof.
    intros until B. intros HDIST CTX PAYR PLEN MODE SI ARR VIS HID KA HC HE HB HH HBC HW.
    destruct (sinv_lenext_facts _ _ _ _ SI MODE) as (EX15 & LEN1 & LEN2).
    inf_arm_open.
    destruct (proj1 BKOK MODE) as (bk & EBK & BKR). clear BKOK. subst back.
    pose proof (pow2_le_40 B ltac:(lia)) as P40. pose proof (pow2_le_15 extra ltac:(lia)) as P15.
    pose proof (mod_pow2_bound H extra ltac:(lia)) as MB. pose proof (drop_bound H B extra ltac:(lia) HH) as DB.
    Time zrung [0x90198].
    rewrite (bits_mask_sllw H extra) by lia.
    Time zrung [0x901c4].
    rewrite (srl_div H extra) by lia.
    Time zrung [0x91cb0].
    destruct (sinv_pull _ _ lf cf ci (H / 2 ^ extra) (B - extra) SI ltac:(icx_cbn; lia) ltac:(icx_cbn; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(icx_cbn; lia)) as (SI1 & ME1).
    destruct (sinv_to_dist _ _ lf cf (len + H mod 2 ^ extra) SI1 MODE ltac:(lia) ltac:(lia)) as (SI2 & ME2).
    st_norm SI1. st_norm ME1. st_norm SI2. st_norm ME2.
    eapply (HDIST (IST DIST last flags ci cout (H / 2 ^ extra) (B - extra) out ret (len + H mod 2 ^ extra) offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo);
      [exact CTX0| exact PAYR| exact PLEN| reflexivity| exact SI2| exact ARR| change DIST with 16202; inf_vis_close_bk ltac:(unfold back_ok; cbn [t_mode]; split; intros E; [exfalso; lazy in E; discriminate E| eexists; split; [reflexivity| clear - BKR EX15 HE; lia]])| inf_hid_close| eapply KALL_mono; [| exact KA]; lia].
    (* [U14B] A2 2026-11-12: v24 is a vestige binder at 1.4 (InfBBase's inf_locals no longer holds it), so eapply leaves
       it as a shelved word; any value does (G's U1A cure for v240) *)
    Unshelve. all: exact (Z_to_bv 64 0).
  Time Qed.

  Lemma lenx_loop : forall (N : nat) (cx : ictx) (ly : ilay) (st : ist) (lf cf wf fo : Z -> Z) (v0 v8 v16 v24 v240 v328 j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word)
      (x6 x10 x14 x19 x21 x22 x23 x26 x29 x30 x31 : word) (m : amem) (ci H B : Z),
    GARM cx ly 0x91cb0 DIST ->
    inf_ctx cx ly AI RNG LB -> Forall (fun c => 0 <= c < 256) payload -> Z.of_nat (length payload) = c_n cx ->
    t_mode st = LENEXT -> sinv cx st lf cf -> inf_arr_ok cx wf fo ->
    VIS cx ly st lf cf wf fo v0 v8 v16 v24 v240 v328 (Z_to_bv 64 (Z.shiftr (c_p cx + 108) 3)) j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m -> HIDm cx ly m -> KALLB cx ly (meas cx st) ->
    c_n cx - ci < Z.of_nat N ->
    t_cin st <= ci <= c_n cx -> B = t_bits st + 8 * (ci - t_cin st) -> B < t_extra st -> 0 <= H < 2 ^ B ->
    evtF bsegs RNG POST
      (MS (mkR (Z_to_bv 64 (l_F0 ly)) (Z_to_bv 64 (l_SPA ly)) gp tp (Z_to_bv 64 (c_q cx + ci)) x6 (Z_to_bv 64 (c_n cx - t_cin st)) (Z_to_bv 64 (l_SP ly)) (Z_to_bv 64 (l_SPA ly))
               x10 (Z_to_bv 64 (c_q cx + ci)) (Z_to_bv 64 (c_n cx - ci)) (Z_to_bv 64 (t_extra st)) x14 (Z_to_bv 64 B) (Z_to_bv 64 B) (Z_to_bv 64 (t_extra st))
               (Z_to_bv 64 (l_Zs ly)) x19 x21 (Z_to_bv 64 2147450880) x22 (Z_to_bv 64 H)
               (Z_to_bv 64 (Z.shiftr (l_F0 ly) 3 + 2147450880)) x23 x26 (Z_to_bv 64 (l_F0 ly)) (Z_to_bv 64 (t_bits st)) x29 x30 x31)
          FR (Z_to_bv 64 0x8e6b8) fc None m (seg_rom bsegs)).
  Proof.
    induction N as [|N IH]; intros until B; intros HDIST CTX PAYR PLEN MODE SI ARR VIS HID KA HN HC HBE HBX HH; [lia|].
    pose proof KA as (KD & KB & KL & KLV).
    pose proof (sinv_bits_facts _ _ _ _ SI) as (CIN0 & CINN & BITS0 & BLE & HOLD0).
    destruct (sinv_lenext_facts _ _ _ _ SI MODE) as (EX15 & LEN1 & LEN2).
    inf_arm_open.
    pose proof (pow2_le_40 B ltac:(lia)) as P40.
    zs. zbr0 KH.
    -
      zrung [0x8e6dc].
      assert (CIR : 0 <= ci < n) by (clear - KH HC CIN0; lia).
      destruct (pull_facts RNG _ m m D n payload ci UNP MU DJP RD RSD PAYB PAYR PLEN D16 D1 CIR) as (b & RDB & CK & ACP & RDP & ACB & BZR).
      zs. zs. zs. rewrite (sxb_sval b).
      pose proof atop_range as ATR.
      eapply (lenx_ck RNG POST) with (A := D + ci) (sb := sval b); [clear - D1 CIR DL2 ATR; lia| exact CK| intros y10].
      zs. cbv beta. rewrite (bz_val payload ci PAYR).
      zrung [0x8e710].
      setreg 23 (Z_to_bv 64 (H + bz payload ci * 2 ^ B)) ltac:(rewrite pull_hold by lia; reflexivity).
      pose proof (pull_bound H B (bz payload ci) ltac:(lia) ltac:(lia) BZR) as PB.
      replace (D + ci + 1) with (D + (ci + 1)) by lia. replace (n - ci + -1) with (n - (ci + 1)) by lia.
      zs. zbr0 KB2.
      +
        eapply (IH (ICX u S D n 6341696 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo
                  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m (ci + 1) (H + bz payload ci * 2 ^ B) (B + 8));
          [exact HDIST| exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| exact VISf| exact HID| exact KA| | | | | ]; icx_cbn; lia.
      +
        zs.
        eapply (lenx_tail (ICX u S D n 6341696 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo
                  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m (ci + 1) (H + bz payload ci * 2 ^ B) (B + 8));
          [exact HDIST| exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| exact VISf| exact HID| exact KA| | | | | | ]; icx_cbn; lia.
    -
      zrung [0x93664].
      assert (ECI : ci = n) by lia. subst ci.
      destruct (sinv_pull _ _ lf cf n H B SI ltac:(icx_cbn; lia) ltac:(icx_cbn; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(icx_cbn; lia) ltac:(icx_cbn; lia)) as (SI1 & _).
      st_norm SI1.
      replace (Z.shiftl (n - cin) 3 + bits) with B by (rewrite Z.shiftl_mul_pow2 by lia; change (2 ^ 3) with 8; lia).
      replace (D + cin + (n - cin) mod 4294967296) with (D + n) in * by (rewrite Z.mod_small by lia; lia).
      eapply (KL (IST mode last flags n cout H B out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo);
        [exact SI1| exact ARR| reflexivity| inf_vis_close| inf_hid_close].
    (* [U14B] A2 2026-11-12: v24 is a vestige binder at 1.4 (InfBBase's inf_locals no longer holds it), so eapply leaves
       it as a shelved word; any value does (G's U1A cure for v240) *)
    Unshelve. all: exact (Z_to_bv 64 0).
  Time Qed.

  Lemma lenx_body : forall (cx : ictx) (ly : ilay) (st : ist) (lf cf wf fo : Z -> Z) (v0 v8 v16 v24 v240 v328 j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word)
      (x6 x7 x10 x11 x12 x14 x16 x19 x21 x22 x23 x26 x28 x29 x30 x31 : word) (m : amem),
    GARM cx ly 0x91cb0 DIST ->
    inf_ctx cx ly AI RNG LB -> Forall (fun c => 0 <= c < 256) payload -> Z.of_nat (length payload) = c_n cx ->
    t_mode st = LENEXT -> sinv cx st lf cf -> inf_arr_ok cx wf fo ->
    VIS cx ly st lf cf wf fo v0 v8 v16 v24 v240 v328 (Z_to_bv 64 (Z.shiftr (c_p cx + 108) 3)) j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m -> HIDm cx ly m -> KALLB cx ly (meas cx st) ->
    t_extra st <> 0 ->
    evtF bsegs RNG POST (GARM_MS cx ly gp tp FR fc 0x8e684 st x6 x7 x10 x11 x12 (Z_to_bv 64 (t_extra st)) x14 x16 x19 x21 x22 x23 x26 x28 x29 x30 x31 m).
  Proof.
    intros until m. intros HDIST CTX PAYR PLEN MODE SI ARR VIS HID KA KX. unfold GARM_MS.
    destruct (sinv_lenext_facts _ _ _ _ SI MODE) as (EX15 & LEN1 & LEN2).
    inf_arm_open.
    pose proof (pow2_le_40 bits ltac:(lia)) as P40.
    zs. zbr0 KB1.
    -
      zrung [0x8e6b8].
      rewrite (Z.mod_small bits 4294967296) by lia. rewrite (Z.mod_small extra 4294967296) by lia.
      eapply (lenx_loop (Z.to_nat (n - cin) + 1) (ICX u S D n 6341696 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo
                _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m cin hold bits);
        [exact HDIST| exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| exact VISf| exact HID| exact KA| | | | | ]; icx_cbn; lia.
    -
      zrung [0x90160].
      eapply (lenx_tail (ICX u S D n 6341696 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo
                _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m cin hold bits);
        [exact HDIST| exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| exact VISf| exact HID| exact KA| | | | | | ]; icx_cbn; lia.
  Time Qed.

  Lemma lenx_zero : forall (cx : ictx) (ly : ilay) (st : ist) (lf cf wf fo : Z -> Z) (v0 v8 v16 v24 v240 v328 j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word)
      (x6 x7 x10 x11 x12 x13 x14 x16 x19 x21 x22 x23 x26 x28 x29 x30 x31 : word) (m : amem),
    GARM cx ly 0x91cb0 DIST ->
    inf_ctx cx ly AI RNG LB -> Forall (fun c => 0 <= c < 256) payload -> Z.of_nat (length payload) = c_n cx ->
    t_mode st = LENEXT -> sinv cx st lf cf -> inf_arr_ok cx wf fo ->
    VIS cx ly st lf cf wf fo v0 v8 v16 v24 v240 v328 (Z_to_bv 64 (Z.shiftr (c_p cx + 108) 3)) j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m -> HIDm cx ly m -> KALLB cx ly (meas cx st) ->
    evtF bsegs RNG POST (GARM_MS cx ly gp tp FR fc 0x91c4c st x6 x7 x10 x11 x12 x13 x14 x16 x19 x21 x22 x23 x26 x28 x29 x30 x31 m).
  Proof.
    intros until m. intros HDIST CTX PAYR PLEN MODE SI ARR VIS HID KA. unfold GARM_MS.
    destruct (sinv_lenext_facts _ _ _ _ SI MODE) as (EX15 & LEN1 & LEN2).
    inf_arm_open.
    destruct (proj1 BKOK MODE) as (bk & EBK & BKR). clear BKOK. subst back.
    zrung [0x91cb0].
    destruct (sinv_to_dist _ _ lf cf len SI MODE ltac:(icx_cbn; lia) ltac:(icx_cbn; lia)) as (SI2 & ME2).
    st_norm SI2. st_norm ME2.
    eapply (HDIST (IST DIST last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo);
      [exact CTX0| exact PAYR| exact PLEN| reflexivity| exact SI2| exact ARR| change DIST with 16202; inf_vis_close_bk ltac:(unfold back_ok; cbn [t_mode]; split; intros E; [exfalso; lazy in E; discriminate E| eexists; split; [reflexivity| clear - BKR; lia]])| inf_hid_close| eapply KALL_mono; [| exact KA]; lia].
    (* [U14B] A2 2026-11-12: v24 is a vestige binder at 1.4 (InfBBase's inf_locals no longer holds it), so eapply leaves
       it as a shelved word; any value does (G's U1A cure for v240) *)
    Unshelve. all: exact (Z_to_bv 64 0).
  Time Qed.

  Theorem lenx_garm : forall cx ly, GARM cx ly 0x91cb0 DIST -> GARM cx ly 0x8e660 LENEXT.
  Proof.
    intros cx ly HDIST. unfold garm_stmtA, GARM_MS. intros until m. intros CTX PAYR PLEN MODE SI ARR VIS HID KA.
    destruct (sinv_lenext_facts _ _ _ _ SI MODE) as (EX15 & LEN1 & LEN2).
    inf_arm_open.
    zrung [0x8e67c].
    zs. zbr0 KX.
    -
      eapply (lenx_body (ICX u S D n 6341696 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo);
        [exact HDIST| exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| exact VISf| exact HID| exact KA| icx_cbn; lia].
    -
      zs.
      eapply (lenx_zero (ICX u S D n 6341696 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo);
        [exact HDIST| exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| exact VISf| exact HID| exact KA].
  Time Qed.
End S.
End CANSEC1.
