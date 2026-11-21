(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.Lib Require Import Arr Bytes ZBridge Tac InitMem StoreFast.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.Spec Require Import AsanCtrl.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.AsanW Require Import AImg RtCells ABase ABytes AMalloc_iface AUri_kit.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.IK Require Import IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.U2A Require Import U2AShadow U2AKit U2AArr U2AStore InfAGlue InfPure InfPure_w7 InfAGlue_w7.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.U1A Require Import U2AObj U2AClient U2AIface InfABase InfAKit InfATables InfA_w7base.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.U1A Require Import InfA_garmv. (* garmV, slot 504 free down the LEN -> MATCH chain *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load_hyp :=
  match goal with
  | |- context [ov_read_bytes ?segs ?m ?a ?n] => match goal with HR : ov_read_bytes segs m a n = Some _ |- _ => rewrite HR end
  end; load_post.
Local Ltac solve_load ::= first [ solve_load_hyp | solve_load_sh0 | solve_load_shlit | solve_load_base | solve_load_image ].
Local Ltac acc_hint ::= acc_hint_sh.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= farr_store_extra m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= farr_call_extra segs W m m' MU WM.

Section CANSEC1. Context {rc : runConstT}.
Section S.
  Variable AI : AMallocIface.
  Variables (L : alayout) (RNG : footprint) (stA : astate) (LB : list ablock).
  Variables (gp tp : word) (FR : bvmap 5 word) (fc : bv 32) (POST : machine_state -> Prop).
  Variables (LBc : list ablock) (m0 : amem) (payload : list Z) (fw : Z -> Z) (saved fk fksh : list cell).

  Notation KALLB cx ly B := (KALL cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh B).
  Notation VIS cx ly st lf cf wf fo v0 v8 v16 v240 v504 vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m :=
    (inf_vis cx ly st lf cf wf fo payload v0 v8 v16 v240 v504 vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m).
  Notation HIDm cx ly m := (inf_hid cx ly AI L RNG stA LB LBc m0 fw saved fk fksh m).
  Notation GARM cx ly Lb X := (garmv_stmtA cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh Lb X).

  (* the 1.3.1 register homes of lenx_body, lenx_loop, lenx_tail moved to 1.4 by tools/regmap_text_gr.py (ra>s6 t2>ra s4>s8 s5>s10 s6>t5 s7>s9 s8>s11 s9>s5 s10>s4 s11>s7 t3>t6 t4>t3 t5>t4 t6>t2) *)
  Lemma lenx_tail : forall (cx : ictx) (ly : ilay) (st : ist) (lf cf wf fo : Z -> Z) (v0 v8 v240 vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word)
      (x1 x6 x11 x16 x17 x19 x21 x24 x27 : word) (m : amem) (ci H B : Z),
    GARM cx ly 0x90ec4 DIST ->
    inf_ctx cx ly AI RNG LB -> Forall (fun c => 0 <= c < 256) payload -> Z.of_nat (length payload) = c_n cx ->
    t_mode st = LENEXT -> sinv cx st lf cf -> inf_arr_ok cx wf fo ->
    VIS cx ly st lf cf wf fo v0 v8 (Z_to_bv 64 (Z.shiftr (c_p cx + 108) 3)) (Z_to_bv 64 (Z.shiftr (c_p cx + 56) 3)) v240 vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m -> HIDm cx ly m -> KALLB cx ly (meas cx st) ->
    t_cin st <= ci <= c_n cx -> 1 <= t_extra st <= B -> B <= 40 -> 0 <= H < 2 ^ B -> B <= 8 * ci ->
    8 * (c_n cx - ci) + B = 8 * (c_n cx - t_cin st) + t_bits st ->
    evtF asegs RNG POST
      (MS (mkR (Z_to_bv 64 (c_p cx + 8)) (Z_to_bv 64 (l_SPA ly)) gp tp (Z_to_bv 64 (c_p cx + 7164)) x6 (Z_to_bv 64 (c_p cx + 56)) (Z_to_bv 64 (l_SP ly)) (Z_to_bv 64 (l_SPA ly))
               (Z_to_bv 64 (l_F0 ly)) x11 (Z_to_bv 64 (c_n cx - ci)) (Z_to_bv 64 (t_extra st)) (Z_to_bv 64 (c_q cx + ci)) (Z_to_bv 64 B) x16 x17
               (Z_to_bv 64 (l_Zs ly)) x19 (Z_to_bv 64 H) (Z_to_bv 64 2147450880)
               x1 x27 (Z_to_bv 64 (Z.shiftr (l_F0 ly) 3 + 2147450880)) (Z_to_bv 64 (l_F0 ly))
               x21 x24 (Z_to_bv 64 (c_p cx + 28)) (Z_to_bv 64 (c_osz cx - t_cout st)) (Z_to_bv 64 (Z.shiftr (c_p cx + 8) 3 + 2147450880))
               (Z_to_bv 64 (c_p cx + 108)))
          FR (Z_to_bv 64 0x8f848) fc None m (seg_rom asegs)).
  Proof.
    intros until B. intros HDIST CTX PAYR PLEN MODE SI ARR VIS HID KA HC HE HB HH HBC HW.
    destruct (sinv_lenext_facts _ _ _ _ SI MODE) as (EX15 & LEN1 & LEN2).
    inf_arm_open.
    pose proof (pow2_le_40 B ltac:(lia)) as P40. pose proof (pow2_le_15 extra ltac:(lia)) as P15.
    pose proof (mod_pow2_bound H extra ltac:(lia)) as MB. pose proof (drop_bound H B extra ltac:(lia) HH) as DB.
    Time zrunb [0x8f874].
    rewrite (bits_mask_sllw H extra) by lia.
    Time zrunb [0x8f898].
    rewrite (srl_div H extra) by lia.
    Time zrunb [0x90ec4].
    destruct (sinv_pull _ _ lf cf ci (H / 2 ^ extra) (B - extra) SI ltac:(icx_cbn; lia) ltac:(icx_cbn; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(icx_cbn; lia)) as (SI1 & ME1).
    destruct (sinv_to_dist _ _ lf cf (len + H mod 2 ^ extra) SI1 MODE ltac:(lia) ltac:(lia)) as (SI2 & ME2).
    st_norm SI1. st_norm ME1. st_norm SI2. st_norm ME2.
    eapply (HDIST (IST DIST last flags ci cout (H / 2 ^ extra) (B - extra) out ret (len + H mod 2 ^ extra) offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo);
      [exact CTX0| exact PAYR| exact PLEN| reflexivity| exact SI2| exact ARR| change DIST with 16202; inf_vis_close| inf_hid_close| eapply KALL_mono; [| exact KA]; lia].
    Unshelve. all: try exact (Z_to_bv 64 0).   (* the v240 vestige binder *)
  Time Qed.

  Lemma lenx_loop : forall (N : nat) (cx : ictx) (ly : ilay) (st : ist) (lf cf wf fo : Z -> Z) (v0 v8 v240 vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word)
      (x1 x6 x14 x17 x27 : word) (m : amem) (ci H B : Z),
    GARM cx ly 0x90ec4 DIST ->
    inf_ctx cx ly AI RNG LB -> Forall (fun c => 0 <= c < 256) payload -> Z.of_nat (length payload) = c_n cx ->
    t_mode st = LENEXT -> sinv cx st lf cf -> inf_arr_ok cx wf fo ->
    VIS cx ly st lf cf wf fo v0 v8 (Z_to_bv 64 (Z.shiftr (c_p cx + 108) 3)) (Z_to_bv 64 (Z.shiftr (c_p cx + 56) 3)) v240 vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m -> HIDm cx ly m -> KALLB cx ly (meas cx st) ->
    c_n cx - ci < Z.of_nat N ->
    t_cin st <= ci <= c_n cx -> B = t_bits st + 8 * (ci - t_cin st) -> B < t_extra st -> 0 <= H < 2 ^ B ->
    evtF asegs RNG POST
      (MS (mkR (Z_to_bv 64 (c_p cx + 8)) (Z_to_bv 64 (l_SPA ly)) gp tp (Z_to_bv 64 (c_p cx + 7164)) x6 (Z_to_bv 64 (c_p cx + 56)) (Z_to_bv 64 (l_SP ly)) (Z_to_bv 64 (l_SPA ly))
               (Z_to_bv 64 (l_F0 ly)) (Z_to_bv 64 (c_q cx + ci)) (Z_to_bv 64 (c_n cx - ci)) (Z_to_bv 64 (t_extra st)) x14 (Z_to_bv 64 B) (Z_to_bv 64 (c_q cx + ci)) x17
               (Z_to_bv 64 (l_Zs ly)) (Z_to_bv 64 (t_bits st)) (Z_to_bv 64 H) (Z_to_bv 64 2147450880)
               x1 x27 (Z_to_bv 64 (Z.shiftr (l_F0 ly) 3 + 2147450880)) (Z_to_bv 64 (l_F0 ly))
               (Z_to_bv 64 (c_q cx + t_cin st)) (Z_to_bv 64 (c_n cx - t_cin st)) (Z_to_bv 64 (c_p cx + 28)) (Z_to_bv 64 (c_osz cx - t_cout st)) (Z_to_bv 64 (Z.shiftr (c_p cx + 8) 3 + 2147450880))
               (Z_to_bv 64 (c_p cx + 108)))
          FR (Z_to_bv 64 0x8e130) fc None m (seg_rom asegs)).
  Proof.
    induction N as [|N IH]; intros until B; intros HDIST CTX PAYR PLEN MODE SI ARR VIS HID KA HN HC HBE HBX HH; [lia|].
    pose proof KA as (KD & KB & KL & KLV).
    destruct (sinv_lenext_facts _ _ _ _ SI MODE) as (EX15 & LEN1 & LEN2).
    inf_arm_open.
    pose proof (pow2_le_40 B ltac:(lia)) as P40.
    zs. zbr0 KH.
    -
      destruct (unp_check_mu asegs _ _ _ _ _ (D + ci) 1 UNP MU DJP ltac:(lia) ltac:(lia) ltac:(lia) (mod8_room1 _)) as (b & RDB & CK).
      zs. zs. zs. rewrite sxb_sval.
      ck_branchJ 17 0x8e148 CK.
      pose proof (pay_read asegs _ D payload ci PAYB ltac:(lia)) as RDP. fold (bz payload ci) in RDP.
      pose proof (bz_range payload ci PAYR) as BZR.
      zs. cbv beta. rewrite (bz_val payload ci PAYR).
      zrunb [0x8e168].
      rewrite (pull_hold H (bz payload ci) B) by lia.
      pose proof (pull_bound H B (bz payload ci) ltac:(lia) ltac:(lia) BZR) as PB.
      replace (D + ci + 1) with (D + (ci + 1)) by lia. replace (n - ci + -1) with (n - (ci + 1)) by lia.
      idtac "BEFORE-BLTU". show_mkR.
      zs. zbr0 KB2.
      +
        eapply (IH (ICX u S D n 6335680 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo
                  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m (ci + 1) (H + bz payload ci * 2 ^ B) (B + 8));
          [exact HDIST| exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| exact VISf| exact HID| exact KA| | | | | ]; icx_cbn; lia.
      +
        zs.
        eapply (lenx_tail (ICX u S D n 6335680 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo
                  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m (ci + 1) (H + bz payload ci * 2 ^ B) (B + 8));
          [exact HDIST| exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| exact VISf| exact HID| exact KA| | | | | | ]; icx_cbn; lia.
    -
      zrunb [0x9266c].
      assert (ECI : ci = n) by lia. subst ci.
      replace (bits + Z.shiftl (n - cin) 3) with B by (rewrite Z.shiftl_mul_pow2 by lia; lia).
      replace (D + cin + (n - cin) mod 4294967296) with (D + n) by (rewrite Z.mod_small by lia; lia).
      replace (Z_to_bv 64 0) with (Z_to_bv 64 (n - n)) by (f_equal; lia).
      destruct (sinv_pull _ _ lf cf n H B SI ltac:(icx_cbn; lia) ltac:(icx_cbn; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(icx_cbn; lia) ltac:(icx_cbn; lia)) as (SI1 & _).
      st_norm SI1.
      eapply (KLV (IST mode last flags n cout H B out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) ret lf cf wf fo);
        [exact SI1| exact ARR| inf_vis_close| exact HID].
    Unshelve. all: try exact (Z_to_bv 64 0).   (* the v240 vestige binder *)
  Time Qed.

  Lemma lenx_body : forall (cx : ictx) (ly : ilay) (st : ist) (lf cf wf fo : Z -> Z) (v0 v8 v240 vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word)
      (x1 x6 x11 x12 x14 x15 x16 x17 x27 : word) (m : amem),
    GARM cx ly 0x90ec4 DIST ->
    inf_ctx cx ly AI RNG LB -> Forall (fun c => 0 <= c < 256) payload -> Z.of_nat (length payload) = c_n cx ->
    t_mode st = LENEXT -> sinv cx st lf cf -> inf_arr_ok cx wf fo ->
    VIS cx ly st lf cf wf fo v0 v8 (Z_to_bv 64 (Z.shiftr (c_p cx + 108) 3)) (Z_to_bv 64 (Z.shiftr (c_p cx + 56) 3)) v240 vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m -> HIDm cx ly m -> KALLB cx ly (meas cx st) ->
    t_extra st <> 0 ->
    evtF asegs RNG POST
      (MS (mkR (Z_to_bv 64 (c_p cx + 8)) (Z_to_bv 64 (l_SPA ly)) gp tp (Z_to_bv 64 (c_p cx + 7164)) x6 (Z_to_bv 64 (c_p cx + 56)) (Z_to_bv 64 (l_SP ly)) (Z_to_bv 64 (l_SPA ly))
               (Z_to_bv 64 (l_F0 ly)) x11 x12 (Z_to_bv 64 (t_extra st)) x14 x15 x16 x17
               (Z_to_bv 64 (l_Zs ly)) (Z_to_bv 64 (t_bits st)) (Z_to_bv 64 (t_hold st)) (Z_to_bv 64 2147450880)
               x1 x27 (Z_to_bv 64 (Z.shiftr (l_F0 ly) 3 + 2147450880)) (Z_to_bv 64 (l_F0 ly))
               (Z_to_bv 64 (c_q cx + t_cin st)) (Z_to_bv 64 (c_n cx - t_cin st)) (Z_to_bv 64 (c_p cx + 28)) (Z_to_bv 64 (c_osz cx - t_cout st)) (Z_to_bv 64 (Z.shiftr (c_p cx + 8) 3 + 2147450880))
               (Z_to_bv 64 (c_p cx + 108)))
          FR (Z_to_bv 64 0x8e118) fc None m (seg_rom asegs)).
  Proof.
    intros until m. intros HDIST CTX PAYR PLEN MODE SI ARR VIS HID KA KX.
    destruct (sinv_lenext_facts _ _ _ _ SI MODE) as (EX15 & LEN1 & LEN2).
    inf_arm_open.
    pose proof (pow2_le_40 bits ltac:(lia)) as P40.
    zs. zbr0 KB1.
    -
      zrunb [0x8e130].
      eapply (lenx_loop (Z.to_nat (n - cin) + 1) (ICX u S D n 6335680 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo
                _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m cin hold bits);
        [exact HDIST| exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| exact VISf| exact HID| exact KA| | | | | ]; icx_cbn; lia.
    -
      zrunb [0x8f848].
      eapply (lenx_tail (ICX u S D n 6335680 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo
                _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m cin hold bits);
        [exact HDIST| exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| exact VISf| exact HID| exact KA| | | | | | ]; icx_cbn; lia.
    Unshelve. all: try exact (Z_to_bv 64 0).   (* the v240 vestige binder *)
  Time Qed.

  Lemma lenx_zero : forall (cx : ictx) (ly : ilay) (st : ist) (lf cf wf fo : Z -> Z) (v0 v8 v240 vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word)
      (x1 x5 x6 x11 x12 x13 x14 x15 x16 x17 x27 : word) (m : amem),
    GARM cx ly 0x90ec4 DIST ->
    inf_ctx cx ly AI RNG LB -> Forall (fun c => 0 <= c < 256) payload -> Z.of_nat (length payload) = c_n cx ->
    t_mode st = LENEXT -> sinv cx st lf cf -> inf_arr_ok cx wf fo ->
    VIS cx ly st lf cf wf fo v0 v8 (Z_to_bv 64 (Z.shiftr (c_p cx + 108) 3)) (Z_to_bv 64 (Z.shiftr (c_p cx + 56) 3)) v240 vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m -> HIDm cx ly m -> KALLB cx ly (meas cx st) ->
    evtF asegs RNG POST (GARM_MS cx ly gp tp FR fc 0x90e74 st x1 x5 x6 x11 x12 x13 x14 x15 x16 x17 x27 m).
  Proof.
    intros until m. intros HDIST CTX PAYR PLEN MODE SI ARR VIS HID KA. unfold GARM_MS.
    destruct (sinv_lenext_facts _ _ _ _ SI MODE) as (EX15 & LEN1 & LEN2).
    inf_arm_open.
    zrunb [0x90ec4].
    destruct (sinv_to_dist _ _ lf cf len SI MODE ltac:(icx_cbn; lia) ltac:(icx_cbn; lia)) as (SI2 & ME2).
    st_norm SI2. st_norm ME2.
    eapply (HDIST (IST DIST last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo);
      [exact CTX0| exact PAYR| exact PLEN| reflexivity| exact SI2| exact ARR| change DIST with 16202; inf_vis_close| inf_hid_close| eapply KALL_mono; [| exact KA]; lia].
    Unshelve. all: try exact (Z_to_bv 64 0).   (* the v240 vestige binder *)
  Time Qed.

  Theorem lenx_garm : forall cx ly, GARM cx ly 0x90ec4 DIST -> GARM cx ly 0x8e0f0 LENEXT.
  Proof.
    intros cx ly HDIST. unfold garmv_stmtA, GARM_MS. intros until m. intros CTX PAYR PLEN MODE SI ARR VIS HID KA.
    destruct (sinv_lenext_facts _ _ _ _ SI MODE) as (EX15 & LEN1 & LEN2).
    inf_arm_open.
    zrunb [0x8e110].
    zs. zbr0 KX.
    -
      eapply (lenx_body (ICX u S D n 6335680 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo);
        [exact HDIST| exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| exact VISf| exact HID| exact KA| icx_cbn; lia].
    -
      zs.
      eapply (lenx_zero (ICX u S D n 6335680 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo);
        [exact HDIST| exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| exact VISf| exact HID| exact KA].
    Unshelve. all: try exact (Z_to_bv 64 0).   (* the v240 vestige binder *)
  Time Qed.
End S.
End CANSEC1.
