(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* inflate_state arrays at their 1.4 offsets (lens 168, work 808, codes 1384, sane 7160; 1.3.1: 152, 792, 1368, 7144) *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.Lib Require Import Arr Bytes ZBridge Tac InitMem StoreFast.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.Spec Require Import AsanCtrl.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.AsanW Require Import AImg RtCells ABase ABytes AMalloc_iface AUri_kit.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.IK Require Import IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.U2A Require Import U2AShadow U2AKit U2AArr U2AStore InfAGlue InfPure InfPure_w7 InfPure_w7d InfPure_w7e InfPure_w7f InfAGlue_w7 InfAGlue_w7b.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.U1A Require Import U2AObj U2AClient U2AIface InfABase InfAKit InfATables InfA_w7base InfA_w7tab InfA_w7pull.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.U1A Require Import InfA_garmc InfA_garmv.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.U1A Require Import InfA_w7lenr InfA_lenx InfA_len2 InfA_len4 InfA_len5 InfA_len3 InfA_len1.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.Common Require Import RunDraw.
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
  Notation GARM cx ly Lb X := (garm_stmtA cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh Lb X).
  (* LEN is stated against garmC (t2 and slot 504 free), its DIST
     continuation against garmV (slot 504 free, t2 = S+56) *)
  Notation GARMC cx ly Lb X := (garmc_stmtA cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh Lb X).
  Notation GARMV cx ly Lb X := (garmv_stmtA cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh Lb X).

  Notation LXB cx ly := (LXB_STMT AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh cx ly).
  Notation LXZ cx ly := (LXZ_STMT AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh cx ly).

  Definition LFAST_STMT (cx : ictx) (ly : ilay) : Prop :=
    forall (st : ist) (lf cf wf fo : Z -> Z) (v0 v8 v240 vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word)
      (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x22 x23 : word) (m : amem),
    inf_ctx cx ly AI RNG LB -> Forall (fun c => 0 <= c < 256) payload -> Z.of_nat (length payload) = c_n cx ->
    t_mode st = LEN -> sinv cx st lf cf -> inf_arr_ok cx wf fo ->
    VIS cx ly st lf cf wf fo v0 v8 (Z_to_bv 64 (Z.shiftr (c_p cx + 108) 3)) (Z_to_bv 64 (Z.shiftr (c_p cx + 56) 3)) v240 vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m -> HIDm cx ly m -> KALLB cx ly (meas cx st) ->
    (* 1.4 enters inflate_fast inline at 0x9092c, and only when bits <= 7 too (0x90924) *)
    6 <= c_n cx - t_cin st -> 258 <= c_osz cx - t_cout st -> t_bits st <= 7 ->
    (* garmC's state (t2 free); the fast path reloads t2 from slot 480 at 0x909f8 *)
    evtF asegs RNG POST (GARMC_MS cx ly gp tp FR fc 0x9097c st x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x22 x23 m).

  Lemma len_entry2 : forall (cx : ictx) (ly : ilay) (st : ist) (lf cf wf fo : Z -> Z) (v0 v8 v240 vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word)
      (x5 x6 x7 x11 x12 x13 x15 x16 x17 x22 x23 : word) (m : amem) (TA nd XT NS : Z) (rd : Z -> Z),
    LXB cx ly -> LXZ cx ly ->
    inf_ctx cx ly AI RNG LB -> Forall (fun c => 0 <= c < 256) payload -> Z.of_nat (length payload) = c_n cx ->
    t_mode st = LEN -> sinv cx st lf cf -> inf_arr_ok cx wf fo ->
    VIS cx ly st lf cf wf fo v0 v8 (Z_to_bv 64 (Z.shiftr (c_p cx + 108) 3)) (Z_to_bv 64 (Z.shiftr (c_p cx + 56) 3)) v240 vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m -> HIDm cx ly m -> KALLB cx ly (meas cx st) ->
    cp_addrA (c_p cx) (t_lc st) = TA ->
    dtab m TA nd rd -> tab_ok LENS rd (t_lb st) nd = true -> nd <= 65536 ->
    shadow_bytes m (Z.shiftr XT 3 + 2147450880) (Z.shiftr XT 3 + 2147450880 + NS) (fun _ => 0) -> XT mod 8 = 0 -> 0 <= XT -> XT <= TA -> TA + 4 * nd <= XT + 8 * NS ->
    rng RNG (Z.shiftr XT 3 + 2147450880) NS -> rng RNG TA (4 * nd) -> 0 < TA -> TA + 4 * nd < 140737488355328 ->
    (* the 1.4 LEN table lookup starts at 0x90ac0, after the slow path's state->back = 0 *)
    (* garmC's state (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s6 s7; t2 free, written at 0x90b04
       before any read); a4 = the shadow of &state->back, which the slow path checks before its store *)
    evtF asegs RNG POST (GARMC_MS cx ly gp tp FR fc 0x90b10 st x5 x6 x7 x11 x12 x13 (Z_to_bv 64 (Z.shiftr (c_p cx + 7164) 3 + 2147450880)) x15 x16 x17 x22 x23 m).
  Proof.
    intros until rd. intros HLXB HLXZ CTX PAYR PLEN MODE SI ARR VIS HID KA ETA DT TOK ND16 SBT XT8 XT0 XTL XTH RXT RTA TAP TAH.
    destruct (tab_ok_root _ _ _ _ TOK) as (LB15 & NDR & ROOT).
    pose proof (sinv_bits_facts _ _ _ _ SI) as (CIN0 & CINN & BITS0 & BLE & HOLD0).
    unfold GARMC_MS.
    inf_arm_open.
    rewrite ETA in SSC.
    zrunb [0x90b48].
    zs. rewrite (zx32_small lb) by (clear - LB15; lia).
    pose proof (pow2_le_40 bits ltac:(clear - BITS0; lia)) as P40. pose proof (pow2_le_15 lb ltac:(clear - LB15; lia)) as P15.
    eapply (len_root_a RNG POST) with (H := hold) (lb := lb) (TA := TA); [clear - HOLD0 P40; lia| exact LB15| clear - TAP TAH NDR P15; lia|].
    assert (IDX : 0 <= hold mod 2 ^ lb < 2 ^ lb) by (apply mod_pow2_bound; clear - LB15; lia).
    assert (IND : 0 <= hold mod 2 ^ lb < nd) by (clear - IDX NDR; lia).
    remember (hold mod 2 ^ lb) as i0 eqn:EI0. apply w7hide_in in EI0.
    destruct (DT i0 IND) as (RDR & RD0 & RD1 & RD2).
    pose proof (tab_sh0 m XT NS (TA + 4 * i0 + 1) SBT XT8 ltac:(clear - IND XTL XTH; lia) ltac:(exact XT0)) as RDS.
    pose proof (tab_sh_acc RNG XT NS (TA + 4 * i0 + 1) RXT XT8 ltac:(clear - IND XTL XTH; lia) ltac:(exact XT0)) as ACS.
    zs. zs. zs. zs. zs.
    cbv beta.
    rewrite u8_lit by (apply code_bits_range).
    pose proof (code_bits_range (rd i0)) as CBR0.
    set (hb0 := code_bits (rd i0)) in *.
    zs. zbr0 KNP.
    -
      zrunb [0x90c34].
      apply w7hide_out in EI0. subst hb0 i0.
      eapply (l_root AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh
                (ICX u S D n 6335680 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo
                _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m TA nd XT NS rd cin hold bits);
        [exact HLXB| exact HLXZ| exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| exact VISf| exact HID| exact KA| exact DT| exact TOK| exact ND16| exact SBT| exact XT8| exact XT0| exact XTL| exact XTH| exact RXT| exact RTA| exact TAP| exact TAH
        | | | | | ]; clear - CIN0 CINN BITS0 BLE HOLD0 KNP; gcbn; lia.
    -
      zrunb [0x90b98].
      apply w7hide_out in EI0. subst hb0 i0.
      eapply (l_loop1 AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh (Datatypes.S (Z.to_nat (n - cin))) (ICX u S D n 6335680 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo
                _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m TA nd XT NS rd cin hold bits);
        [exact HLXB| exact HLXZ| exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| exact VISf| exact HID| exact KA| exact DT| exact TOK| exact ND16| exact SBT| exact XT8| exact XT0| exact XTL| exact XTH| exact RXT| exact RTA| exact TAP| exact TAH
        | | | | | ]; clear - CIN0 CINN BITS0 BLE HOLD0 KNP; gcbn; lia.
    Unshelve. all: try exact (Z_to_bv 64 0).   (* the v240 vestige binder *)
  Time Qed.
  Lemma len_slow : forall (cx : ictx) (ly : ilay) (st : ist) (lf cf wf fo : Z -> Z) (v0 v8 v240 vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word)
      (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x22 x23 : word) (m : amem),
    LXB cx ly -> LXZ cx ly ->
    inf_ctx cx ly AI RNG LB -> Forall (fun c => 0 <= c < 256) payload -> Z.of_nat (length payload) = c_n cx ->
    t_mode st = LEN -> sinv cx st lf cf -> inf_arr_ok cx wf fo ->
    VIS cx ly st lf cf wf fo v0 v8 (Z_to_bv 64 (Z.shiftr (c_p cx + 108) 3)) (Z_to_bv 64 (Z.shiftr (c_p cx + 56) 3)) v240 vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m -> HIDm cx ly m -> KALLB cx ly (meas cx st) ->
    (* the 1.4 slow path (have < 6, left < 258 or bits > 7) starts at 0x90aa4 *)
    evtF asegs RNG POST (GARMC_MS cx ly gp tp FR fc 0x90af4 st x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x22 x23 m).
  Proof.
    intros until m. intros HLXB HLXZ CTX PAYR PLEN MODE SI ARR VIS HID KA.
    assert (LIVE : codes_liveP (t_mode st)) by (rewrite MODE; exact codes_live_LEN).
    pose proof (proj1 SI) as RN1. unfold IDefs.RNG in RN1.
    assert (CFR : forall i, 0 <= i < N_CODES -> 0 <= cf i < 4294967296) by (repeat (destruct RN1 as [_ RN1]); exact RN1). clear RN1.
    destruct (sinv_tabs_cases _ _ _ _ SI LIVE) as [(o & ELC & EDC & LB15 & DB15 & O0 & ONX & NX & TL & TD)|(ELC & EDC & ELB & EDB & TL & TD)].
    -
      unfold GARMC_MS.
      inf_arm_open.
      pose proof (ablk_lin _ _ SB) as (SB1 & SB2 & SB3 & SB4). unfold AIMG_HI in SB1. change (2 ^ 47) with 140737488355328 in SB4.
      zrunb [0x90b10].
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => assert (HID1 : HIDm (ICX u S D n 6335680 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) mm) by inf_hid_close end.
      pose proof HID1 as (_ & _ & SHS1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SHLF1 & _).
      eapply (len_entry2 (ICX u S D n 6335680 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo
                _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (S + 1384 + 4 * 0) o S 897 (rdc cf (CDyn 0)));
        [exact HLXB| exact HLXZ| exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| inf_vis_close| exact HID1| exact KA
        | gcbn; rewrite ELC; reflexivity
        | apply dtab_dyn; [eassumption| exact CFR| clear; lia| exact O0| clear - ONX NX; lia]
        | exact TL| clear - ONX NX; lia| exact SHS1| exact S8| clear - SB2; lia| clear; lia| clear - ONX NX; lia| exact RSS
        | eapply rng_sub'; [exact RS| clear - O0 ONX NX; lia] | clear - SB1; lia| clear - SB4 ONX NX; lia].
    -
      unfold GARMC_MS.
      inf_arm_open.
      pose proof (ablk_lin _ _ SB) as (SB1 & SB2 & SB3 & SB4). unfold AIMG_HI in SB1. change (2 ^ 47) with 140737488355328 in SB4.
      zrunb [0x90b10].
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => assert (HID1 : HIDm (ICX u S D n 6335680 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) mm) by inf_hid_close end.
      pose proof HID1 as (_ & _ & SHS1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SHLF1 & _).
      eapply (len_entry2 (ICX u S D n 6335680 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo
                _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 149600 512 149600 256 (rdc (fun _ => 0) CLenfix));
        [exact HLXB| exact HLXZ| exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| inf_vis_close| exact HID1| exact KA
        | gcbn; rewrite ELC; reflexivity
        | apply dtab_lenfix; eassumption
        | gcbn; rewrite ELB; exact TL| clear; lia| exact SHLF1| reflexivity| clear; lia| clear; lia| clear; lia
        | eapply rng_sub'; [exact RISH| cbv; split; discriminate]
        | eapply rng_sub'; [exact RI| cbv; split; discriminate] | clear; lia| clear; lia].
    Unshelve. all: try exact (Z_to_bv 64 0).   (* the v240 vestige binder *)
  Time Qed.

  Theorem len_garm : forall cx ly, GARMV cx ly 0x90ec4 DIST -> LFAST_STMT cx ly -> GARMC cx ly 0x90964 LEN.
  Proof.
    intros cx ly HDIST HFAST.
    assert (HLXB : LXB cx ly) by (unfold LXB_STMT; intros; eapply (lenx_body AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh cx ly); eassumption).
    assert (HLXZ : LXZ cx ly) by (unfold LXZ_STMT; intros; eapply (lenx_zero AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh cx ly); eassumption).
    unfold garmc_stmtA. intros until m. intros CTX PAYR PLEN MODE SI ARR VIS HID KA.
    pose proof (sinv_bits_facts _ _ _ _ SI) as (CIN0 & CINN & BITS0 & BLE & HOLD0).
    pose proof (proj1 SI) as RN0. unfold IDefs.RNG in RN0. destruct RN0 as (_ & _ & COUT0 & COUTN & _).
    unfold GARMC_MS.
    inf_arm_open.
    zs. zs. zbr0 K6.
    - eapply (len_slow (ICX u S D n 6335680 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo);
        [exact HLXB| exact HLXZ| exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| exact VISf| exact HID| exact KA].
    - zs. zs. zbr0 K258.
      + eapply (len_slow (ICX u S D n 6335680 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo);
          [exact HLXB| exact HLXZ| exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| exact VISf| exact HID| exact KA].
      + (* 1.4's third test, bits > 7 -> the slow path (0x90924) *)
        zs. zs. zbr0 K7.
        * eapply (len_slow (ICX u S D n 6335680 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo);
            [exact HLXB| exact HLXZ| exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| exact VISf| exact HID| exact KA].
        * eapply (HFAST (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo);
            [exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| exact VISf| exact HID| exact KA| clear - K6; gcbn; lia| clear - K258; gcbn; lia| clear - K7 BITS0 BLE; gcbn; lia].
    Unshelve. all: try exact (Z_to_bv 64 0).   (* the v240 vestige binder *)
  Time Qed.
End S.
End CANSEC1.
