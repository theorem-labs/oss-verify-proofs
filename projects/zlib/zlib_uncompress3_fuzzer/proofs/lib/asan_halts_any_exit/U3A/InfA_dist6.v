(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.Lib Require Import Arr Bytes ZBridge Tac InitMem StoreFast.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.Spec Require Import AsanCtrl.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.AsanW Require Import AImg RtCells ABase ABytes AMalloc_iface AUri_kit.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.IK Require Import IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.U2A Require Import U2AShadow U2AKit U2AArr U2AStore InfAGlue InfPure InfPure_w7 InfPure_w7d InfAGlue_w7.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.U3A Require Import U2AObj U2AClient U2AIface InfABase InfAKit InfATables InfA_w7base InfA_w7tab.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.U2A Require Import InfPure_w7e InfAGlue_w7b.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.U3A Require Import InfA_w7six InfA_w7pull InfA_w7root InfA_distx InfA_dist1 InfA_dist2 InfA_dist3 InfA_dist4 InfA_dist5.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.U3A Require Import InfA_garmv.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.Common Require Import RunDraw.
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
  (* the DIST / MATCH arms are stated with slot 504 free (garmV) *)
  Notation GARMV cx ly Lb X := (garmv_stmtA cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh Lb X).

  Notation DXS cx ly := (DX_STMT AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh cx ly).

  Lemma d_at_e1 : forall (cx : ictx) (ly : ilay) (st : ist) (lf cf wf fo : Z -> Z) (v0 v8 v16 v240 vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word)
      (x6 x7 x12 x13 : word) (m : amem) (TA nd XT NS : Z) (rd : Z -> Z) (ci H B : Z),
    DXS cx ly ->
    inf_ctx cx ly AI RNG LB -> Forall (fun c => 0 <= c < 256) payload -> Z.of_nat (length payload) = c_n cx ->
    t_mode st = DIST -> sinv cx st lf cf -> inf_arr_ok cx wf fo ->
    VIS cx ly st lf cf wf fo v0 v8 (Z_to_bv 64 (Z.shiftr (c_p cx + 108) 3)) (Z_to_bv 64 (Z.shiftr (c_p cx + 56) 3)) v240 vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m -> HIDm cx ly m -> KALLB cx ly (meas cx st) ->
    dtab m TA nd rd -> tab_ok DISTS rd (t_db st) nd = true -> nd <= 65536 ->
    shadow_bytes m (Z.shiftr XT 3 + 2147450880) (Z.shiftr XT 3 + 2147450880 + NS) (fun _ => 0) -> XT mod 8 = 0 -> 0 <= XT -> XT <= TA -> TA + 4 * nd <= XT + 8 * NS ->
    rng RNG (Z.shiftr XT 3 + 2147450880) NS -> rng RNG TA (4 * nd) -> 0 < TA -> TA + 4 * nd < 140737488355328 ->
    t_cin st <= ci <= c_n cx -> B = t_bits st + 8 * (ci - t_cin st) -> 0 <= H < 2 ^ B -> code_bits (rd (H mod 2 ^ t_db st)) <= B -> B <= 40 ->
    evtF asegs RNG POST (D_E1 gp tp FR fc cx ly st TA rd ci H B x6 x7 x12 x13 m).
  Proof.
    intros until B. intros HDX CTX PAYR PLEN MODE SI ARR VIS HID KA DT TOK ND16 SBT XT8 XT0 XTL XTH RXT RTA TAP TAH HC HBE HH HEB HB40.
    eapply (d_root AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh cx ly st lf cf wf fo v0 v8 v240 vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad x6 x7 x12 x13 m TA nd XT NS rd ci H B); try eassumption.
    intros x7' x13' LINKOP.
    destruct (tab_ok_root _ _ _ _ TOK) as (DB15 & NDR & ROOT).
    assert (IDX : 0 <= H mod 2 ^ t_db st < 2 ^ t_db st) by (apply mod_pow2_bound; lia).
    destruct (root_term_or_link DISTS rd (t_db st) nd _ ltac:(lia) (ROOT _ IDX)) as [(_ & NL)|(_ & EB & OPL & VLO & VHI & SUB)]; [exfalso; exact (NL LINKOP)|].
    pose proof (code_val_range (rd (H mod 2 ^ t_db st))) as VALR.
    eapply (d_sub AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh cx ly st lf cf wf fo v0 v8 v240 vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad x7' x13' m TA nd XT NS rd); try eassumption; try lia.
    intros j Hj. rewrite EB. exact (proj1 (SUB j Hj)).
    Unshelve. all: try exact (Z_to_bv 64 0).   (* the v240 vestige binder *)
  Qed.

  Lemma dist_entry : forall (cx : ictx) (ly : ilay) (st : ist) (lf cf wf fo : Z -> Z) (v0 v8 v240 vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word)
      (x1 x5 x6 x11 x12 x13 x14 x15 x16 x17 x27 : word) (m : amem) (TA nd XT NS : Z) (rd : Z -> Z),
    DXS cx ly ->
    inf_ctx cx ly AI RNG LB -> Forall (fun c => 0 <= c < 256) payload -> Z.of_nat (length payload) = c_n cx ->
    t_mode st = DIST -> sinv cx st lf cf -> inf_arr_ok cx wf fo ->
    VIS cx ly st lf cf wf fo v0 v8 (Z_to_bv 64 (Z.shiftr (c_p cx + 108) 3)) (Z_to_bv 64 (Z.shiftr (c_p cx + 56) 3)) v240 vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m -> HIDm cx ly m -> KALLB cx ly (meas cx st) ->
    cp_addrA (c_p cx) (t_dc st) = TA ->
    dtab m TA nd rd -> tab_ok DISTS rd (t_db st) nd = true -> nd <= 65536 ->
    shadow_bytes m (Z.shiftr XT 3 + 2147450880) (Z.shiftr XT 3 + 2147450880 + NS) (fun _ => 0) -> XT mod 8 = 0 -> 0 <= XT -> XT <= TA -> TA + 4 * nd <= XT + 8 * NS ->
    rng RNG (Z.shiftr XT 3 + 2147450880) NS -> rng RNG TA (4 * nd) -> 0 < TA -> TA + 4 * nd < 140737488355328 ->
    evtF asegs RNG POST (GARM_MS cx ly gp tp FR fc 0x91224 st x1 x5 x6 x11 x12 x13 x14 x15 x16 x17 x27 m).
  Proof.
    intros until rd. intros HDX CTX PAYR PLEN MODE SI ARR VIS HID KA ETA DT TOK ND16 SBT XT8 XT0 XTL XTH RXT RTA TAP TAH.
    destruct (tab_ok_root _ _ _ _ TOK) as (DB15 & NDR & ROOT).
    pose proof (proj1 (proj1 SI)) as CIN0.
    unfold GARM_MS.
    inf_arm_open.
    rewrite ETA in SSC.
    zrunb [0x91258].
    rewrite (zx32_small db) by lia.
    pose proof (pow2_le_40 bits ltac:(lia)) as P40. pose proof (pow2_le_15 db ltac:(lia)) as P15.
    eapply (root_c RNG POST) with (H := hold) (db := db) (TA := TA); [lia| lia| lia|].
    assert (IDX : 0 <= hold mod 2 ^ db < 2 ^ db) by (apply mod_pow2_bound; lia).
    assert (CBE : 1 <= code_bits (rd (hold mod 2 ^ db)) <= 15).
    { pose proof (ROOT _ IDX) as ROK. destruct (root_term_or_link DISTS rd db nd _ ltac:(lia) ROK) as [(TERM & _)|(_ & EB & _)].
      - pose proof (term_ok_bits _ _ _ TERM). lia.
      - lia. }
    assert (CB15 : forall i, 0 <= i < 2 ^ db -> code_bits (rd i) <= 15).
    { intros i Hi. pose proof (ROOT _ Hi) as ROK. destruct (root_term_or_link DISTS rd db nd _ ltac:(lia) ROK) as [(TERM & _)|(_ & EB & _)].
      - pose proof (term_ok_bits _ _ _ TERM). lia.
      - lia. }
    remember (hold mod 2 ^ db) as i0 eqn:EI0. apply w7hide_in in EI0.
    destruct (DT i0 ltac:(lia)) as (RDR & RD0 & RD1 & RD2).
    pose proof (tab_sh0 m XT NS (TA + 4 * i0 + 1) SBT XT8 ltac:(lia) ltac:(lia)) as RDS.
    pose proof (tab_sh_acc RNG XT NS (TA + 4 * i0 + 1) RXT XT8 ltac:(lia) ltac:(lia)) as ACS.
    zs. zs. zs. zs. zs.
    cbv beta.
    rewrite u8_lit by (apply code_bits_range).
    set (hb0 := code_bits (rd i0)) in *.
    zs. zs. zbr0 KNP.
    -
      zrunb [0x91338].
      apply w7hide_out in EI0. subst hb0 i0.
      eapply (d_at_e1 (ICX u S D n 6336512 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m TA nd XT NS rd cin hold bits);
        [exact HDX| exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| exact VISf| exact HID| exact KA| exact DT| exact TOK| exact ND16| exact SBT| exact XT8| exact XT0| exact XTL| exact XTH| exact RXT| exact RTA| exact TAP| exact TAH
        | | | | | ]; icx_cbn; lia.
    -
      zrunb [0x912a4].
      apply w7hide_out in EI0. subst hb0 i0.
      eapply (d_loop1 AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh (Datatypes.S (Z.to_nat (n - cin))) (ICX u S D n 6336512 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m TA nd XT NS rd cin hold bits); (* d_loop1 binds s6 (x22) too *)
        [exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| exact VISf| exact HID| exact KA| exact DT| exact DB15| exact NDR| exact CB15| exact SBT| exact XT8| exact XT0| exact XTL| exact XTH| exact RXT| exact RTA| exact TAP| exact TAH
        | | | | | | ]; try (icx_cbn; lia).
      intros ci' H' B' x6' x7' x12' x13' HC' HBE' HH' HEB' HB40'.
      eapply (d_at_e1 (ICX u S D n 6336512 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m TA nd XT NS rd ci' H' B');
        [exact HDX| exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| exact VISf| exact HID| exact KA| exact DT| exact TOK| exact ND16| exact SBT| exact XT8| exact XT0| exact XTL| exact XTH| exact RXT| exact RTA| exact TAP| exact TAH
        | | | | | ]; icx_cbn; lia.
    Unshelve. all: try exact (Z_to_bv 64 0).   (* the v240 vestige binder *)
  Time Qed.
  Theorem dist_garm : forall cx ly, GARMV cx ly 0x91680 MATCH -> GARMV cx ly 0x91224 DIST.
  Proof.
    intros cx ly HMATCH. unfold garmv_stmtA. intros until m. intros CTX PAYR PLEN MODE SI ARR VIS HID KA.
    assert (HDX : DXS cx ly).
    { unfold DX_STMT. intros. eapply (distx_body AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh cx ly); eassumption. }
    assert (LIVE : codes_liveP (t_mode st)) by (rewrite MODE; exact codes_live_DIST).
    pose proof CTX as (S16 & SB & _ & _ & _ & _ & _ & _ & _ & RS & RSS & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RI & RISH & _).
    pose proof HID as (_ & _ & SHS & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SHDF & _).
    pose proof VIS as (_ & _ & _ & _ & _ & CODES & _ & _ & _ & _ & MI & _).
    pose proof (ablk_lin _ _ SB) as (SB1 & SB2 & SB3 & SB4). unfold AIMG_HI in SB1. change (2 ^ 47) with 140737488355328 in SB4.
    pose proof (proj1 SI) as RN0. unfold IDefs.RNG in RN0.
    assert (CFR : forall i, 0 <= i < N_CODES -> 0 <= cf i < 4294967296) by (repeat (destruct RN0 as [_ RN0]); exact RN0).
    destruct (sinv_tabs_cases _ _ _ _ SI LIVE) as [(o & ELC & EDC & LB15 & DB15 & O0 & ONX & NX & TL & TD)|(ELC & EDC & ELB & EDB & TL & TD)].
    -
      eapply (dist_entry cx ly st lf cf wf fo v0 v8 v240 vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad x5 x6 x11 x12 x13 x14 x15 x16 x17 x22 x23 m (c_p cx + 1384 + 4 * o) (t_nx st - o) (c_p cx) 897 (rdc cf (CDyn o)));
        [exact HDX| exact CTX| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| exact VIS| exact HID| exact KA
        | rewrite EDC; reflexivity
        | apply dtab_dyn; [exact CODES| exact CFR| lia| lia| lia]
        | exact TD| lia| exact SHS| clear - S16; Z.div_mod_to_equations; lia| lia| lia| lia| exact RSS
        | eapply rng_sub'; [exact RS| lia] | lia| lia].
    -
      eapply (dist_entry cx ly st lf cf wf fo v0 v8 v240 vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad x5 x6 x11 x12 x13 x14 x15 x16 x17 x22 x23 m 152160 32 152160 16 (rdc (fun _ => 0) CDistfix));
        [exact HDX| exact CTX| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| exact VIS| exact HID| exact KA
        | rewrite EDC; reflexivity
        | exact (dtab_distfix m MI)
        | rewrite EDB; exact TD| lia| exact SHDF| reflexivity| lia| lia| lia
        | eapply rng_sub'; [exact RISH| cbv; split; discriminate]
        | eapply rng_sub'; [exact RI| cbv; split; discriminate] | lia| lia].
    Unshelve. all: try exact (Z_to_bv 64 0).   (* the v240 vestige binder *)
  Qed.
End S.
End CANSEC1.
