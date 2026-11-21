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
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2A Require Import U2AShadow U2AKit U2AArr U2AStore InfAGlue InfPure InfPure_w7 InfPure_w7d InfPure_w7e InfPure_w7f InfAGlue_w7 InfAGlue_w7b.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2A Require Import U2AObj.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U1B Require Import U2BObj U2BClient U2BIface InfBBase InfBKit InfBTables InfB_w7base InfB_w7tab InfB_w7pull.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U1B Require Import U2BCall U2BIface_fit2_draft IfB_tabs InfB_lenFS.
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

Lemma bv8_mod256 : forall x, Z_to_bv 8 (x mod 256) = Z_to_bv 8 x.
Proof.
  intros x. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. rewrite Z.mod_mod by lia. reflexivity.
Qed.

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


  Hypothesis IFAST : inflate_fast_stmtA.

  Lemma f8arr_mod256 : forall m A n f, f8arr bsegs m A n f -> f8arr bsegs m A n (fun i => f i mod 256).
  Proof.
    intros m A n f H. unfold f8arr in *. erewrite map_ext; [exact H|]. intros a. cbv beta. apply bv8_mod256.
  Qed.

  Lemma lfast_walk : forall (cx : ictx) (ly : ilay) (st : ist) (lf cf wf fo : Z -> Z) (v0 v8 v16 v24 v240 v328 j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word)
      (x6 x7 x10 x11 x12 x13 x14 x16 x19 x21 x22 x23 x26 x28 x29 x30 x31 : word) (m : amem),
    inf_ctx cx ly AI RNG LB -> Forall (fun c => 0 <= c < 256) payload -> Z.of_nat (length payload) = c_n cx ->
    t_mode st = LEN -> sinv cx st lf cf -> inf_arr_ok cx wf fo ->
    VIS cx ly st lf cf wf fo v0 v8 v16 v24 v240 v328 (Z_to_bv 64 (Z.shiftr (c_p cx + 108) 3)) j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m -> HIDm cx ly m -> KALLB cx ly (meas cx st) ->
    6 <= c_n cx - t_cin st -> 258 <= c_osz cx - t_cout st ->
    evtF bsegs RNG POST (GARM_MS cx ly gp tp FR fc 0x913dc st x6 x7 x10 x11 x12 x13 x14 x16 x19 x21 x22 x23 x26 x28 x29 x30 x31 m).
  Proof.
    intros until m. intros CTX PAYR PLEN MODE SI ARR VIS HID KA H6 H258.
    pose proof KA as (KD & KB & KL & KLV).
    pose proof (sinv_bits_facts _ _ _ _ SI) as (CIN0 & CINN & BITS0 & BLE & HOLD0).
    assert (LIVE : codes_liveP (t_mode st)) by (rewrite MODE; exact codes_live_LEN).
    pose proof (sinv_tabs_cases _ _ _ _ SI LIVE) as TCASES.
    pose proof (proj1 SI) as RN1. unfold IDefs.RNG in RN1.
    assert (CFR : forall i, 0 <= i < 1444 -> 0 <= cf i < 4294967296) by (repeat (destruct RN1 as [_ RN1]); exact RN1).
    destruct RN1 as (_ & _ & COUT0 & COUTN & _ & _ & _ & _ & _ & _ & OUT1 & OUT2 & OUT3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NX0 & NXN & _ & _ & WH0 & WN0 & _).
    pose proof (proj1 (proj2 SI)) as WINF. unfold WIN in WINF. destruct WINF as (WINF0 & WINF1).
    pose proof HID as (AH0 & _). pose proof (AI_rtcells AI _ _ _ _ _ AH0) as ART. unfold artcells in ART.
    destruct ART as (_ & RTG & _ & _ & RTS & _).
    pose proof CTX as (_ & _ & (ps & HPS & DCASE) & _).
    unfold GARM_MS.
    inf_arm_open. subst mode.
    assert (LAYF : 6811648 <= S /\ S + 7176 <= ATOP /\ 6811648 <= Fu /\ Fu + 256 <= ATOP /\ 6341024 <= D /\ D + n <= ATOP /\ Zs = Fu + 32
                   /\ 0 <= bS <= 1 /\ S + 7176 <= 2147446784 + bS * 140737479966720 /\ 17594333495296 * bS <= S
                   /\ 0 <= bU <= 1 /\ Fu + 256 <= 2147446784 + bU * 140737479966720 /\ 17594333495296 * bU <= Fu
                   /\ 0 <= cSU <= 1 /\ S + 7176 <= Fu + cSU * 2 ^ 48 /\ Fu + 256 <= S + (1 - cSU) * 2 ^ 48
                   /\ 0 <= cSD <= 1 /\ S + 7176 <= D + cSD * 2 ^ 48 /\ D + n <= S + (1 - cSD) * 2 ^ 48
                   /\ 0 <= cUD <= 1 /\ Fu + 256 <= D + cUD * 2 ^ 48 /\ D + n <= Fu + (1 - cUD) * 2 ^ 48
                   /\ ATOP + 4096 <= lo /\ lo + 8192 <= SPA /\ SP - 688 <= SPA <= SP - 672 /\ SP + 16 < 140737488355328 /\ 0 <= n < 67108864 /\ 1 <= D /\ 1 <= osz <= 262144)
      by (repeat split; first [assumption | lia]).
    assert (DLAY : (n = 0 /\ D = 6341024) \/ 6811648 <= D).
    { destruct DCASE as [(pd & HPD & NPOS & _)|(N0 & DE)]; [right| left; split; [exact N0| exact DE]].
      pose proof (AI_block_bounds AI _ _ _ _ _ (HB pd D n) AH0 HPD) as (DB1 & _). cbn [ab_addr] in DB1. unfold AIMG_HI in DB1. exact DB1. }
    zrung [0x91478].
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => assert (HID1 : HIDm (ICX u S D n 6341056 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) mm) by inf_hid_close end.
    pose proof HID1 as (AH1 & SHZ1 & SHS1 & SHO1 & WIN1 & UNP1 & _ & _ & _ & _ & _ & _ & _ & _ & SHLF1 & SHDF1 & _).
    cbn [c_w c_p c_q c_n c_ob c_osz l_Zs] in SHZ1, SHS1, SHO1, WIN1, UNP1.
    assert (WDF : Wd = 0 \/ (Wd <> 0 /\ 6811648 <= Wd /\ Wd + 32768 <= ATOP /\ (Wd + 32768 <= Fu \/ Fu + 256 <= Wd) /\ (Wd + 32768 <= S \/ S + 7176 <= Wd)
                          /\ Wd mod 16 = 0 /\ rng RNG Wd 32768 /\ rng RNG (Z.shiftr Wd 3 + 2147450880) 4096 /\ app_band Wd 32768)).
    { destruct WDC as [W0E|(W16 & WAB & (pw & HPW) & RW & RWS)]; [left; exact W0E| right].
      pose proof (AI_block_bounds AI _ _ _ _ _ (HB pw Wd 32768) AH1 HPW) as (WB1 & _ & WB3). cbn [ab_addr ab_size] in WB1, WB3. unfold AIMG_HI in WB1.
      pose proof (AI_blocks_disjoint AI _ _ _ _ _ (HB pw Wd 32768) (mkABlock (ABFake 2) Fu 256) AH1 HPW HFU ltac:(discriminate)) as DWU. cbn [ab_addr ab_size] in DWU.
      pose proof (AI_blocks_disjoint AI _ _ _ _ _ (HB pw Wd 32768) (HB ps S 7176) AH1 HPW HPS ltac:(intros Y; inversion Y)) as DWS. cbn [ab_addr ab_size] in DWS.
      assert (WBAND : app_band Wd 32768) by (unfold app_band; clear - WAB; unfold ablk, AIMG_HI, KLS in WAB; pose proof atop_range; lia).
      split; [lia|]. split; [lia|]. split; [lia|]. split; [exact DWU|]. split; [exact DWS|]. split; [exact W16|]. split; [exact RW|]. split; [exact RWS| exact WBAND]. }
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (CT : exists la na da nd rdL rdD, la = cp_addrA S lc /\ da = cp_addrA S dc
               /\ ctab_at RNG mm la na rdL /\ ctab_at RNG mm da nd rdD /\ 1 <= lb <= 15 /\ 1 <= db <= 15
               /\ tab_ok InflateState.LENS rdL lb na = true /\ tab_ok DISTS rdD db nd = true
               /\ ((6811648 <= S /\ S + 1384 <= la /\ la + 4 * na <= S + 7160 /\ S + 1384 <= da /\ da + 4 * nd <= S + 7160) \/ (la + 4 * na <= 152288 /\ da + 4 * nd <= 152288 /\ 0 <= la /\ 0 <= da /\ 0 <= na /\ 0 <= nd))) end.
    { pose proof (ablk_lin _ _ SB) as (_ & SBl & _ & SBh). change (2 ^ 47) with 140737488355328 in SBh.
      destruct TCASES as [(o & ELC & EDC & LB15 & DB15 & O0 & ONX & NX & TL & TD)|(ELC & EDC & ELB & EDB & TL & TD)].
      - exists (S + 1384 + 4 * 0), o, (S + 1384 + 4 * o), (nx - o), (fun i => cf (0 + i)), (fun i => cf (o + i)).
        subst lc dc. split; [reflexivity|]. split; [reflexivity|].
        split; [apply ctab_of_codes; first [eassumption | exact CFR | split; [exact SHS1| split; [exact RS| exact RSS]] | lia]|].
        split; [apply ctab_of_codes; first [eassumption | exact CFR | split; [exact SHS1| split; [exact RS| exact RSS]] | lia]|].
        split; [exact LB15|]. split; [exact DB15|]. split; [exact TL|]. split; [exact TD|]. left. clear - LAYF O0 ONX NX. lia.
      - exists 149600, 512, 152160, 32, (arr_get lenfix_a), (arr_get distfix_a).
        subst lc dc lb db. split; [reflexivity|]. split; [reflexivity|].
        split; [apply ctab_lenfix; assumption|]. split; [apply ctab_distfix; assumption|].
        split; [lia|]. split; [lia|]. split; [exact TL|]. split; [exact TD|]. right. lia. }
    destruct CT as (la & na & da & nd & rdL & rdD & ELA & EDA & CTL & CTD & LB15 & DB15 & TOKL & TOKD & TLAY).
    rewrite <- ELA, <- EDA in SSC.
    zs.
    eapply evtF_cut; [eapply (IFAST RNG) with (Zs := Zs) (S := S) (D := D) (n := n) (OB := 6341056) (osz := osz) (Wd := Wd) (lo := lo)
                         (cin := cin) (cout := cout) (hold := hold) (bits := bits) (out := out) (whave := whave) (wnext := wnext) (lb := lb) (db := db)
                         (la := la) (na := na) (da := da) (nd := nd) (rdL := rdL) (rdD := rdD)
                         (fo := fo) (fw := fun i => fw i mod 256) (payload := payload)|];
      rewrite ?(unsigned_lit SPA) by (clear - LAYF; pose proof atop_range; lia).
    all: lazymatch goal with
         | |- forall ms' : machine_state, _ => idtac
         | |- mem_inv _ _ => exact MI
         | |- stk _ _ _ _ => exact STK
         | |- rw_cells _ _ _ _ => eassumption
         | |- Z_to_bv 64 _ = Z_to_bv 64 _ => reflexivity
         | |- state_sh _ _ _ => split; [exact SHS1| split; [exact RS| exact RSS]]
         | |- ctab_at _ _ _ _ _ => assumption
         | |- tab_ok _ _ _ _ = true => assumption
         | |- bytes_at _ _ _ _ => exact PAYB
         | |- Forall _ _ => exact PAYR
         | |- unpoisoned _ _ _ => exact UNP1
         | |- f8arr _ _ _ _ _ => exact OUT
         | |- forall i, _ -> 0 <= _ mod 256 < 256 => intros i _; apply Z.mod_pos_bound; lia
         | |- forall i, _ -> 0 <= _ < 256 => exact (proj2 ARR)
         | |- shadow_bytes _ _ _ _ => first [exact SHZ1 | eapply shadow_bytes_sub; [exact SHO1| |]; clear - LAYF; Z.div_mod_to_equations; lia]
         | |- rng_aimg _ => exact RI
         | |- rng _ _ _ => first [exact RZ | exact RSZ | exact RD | exact RSD
                                 | eapply rng_sub'; [exact ROB| clear - LAYF; lia]
                                 | eapply rng_sub'; [exact ROBS| clear - LAYF; Z.div_mod_to_equations; lia]
                                 | eapply rng_sub'; [exact RSTK| clear - LAYF; lia]]
         | |- app_band _ _ => unfold app_band; clear - LAYF; lia
         | |- _ = 0 -> _ => exact WINF0
         | |- _ <> 0 -> _ => exact WINF1
         | |- Z.of_nat (length _) = _ => exact PLEN
         | |- _ mod 8 = 0 => first [exact Z8 | reflexivity | clear - D16; Z.div_mod_to_equations; lia]
         | |- _ mod 16 = 0 => exact S16
         | |- _ => idtac
         end.
    all: lazymatch goal with
         | |- forall ms' : machine_state, _ => idtac
         | |- _ \/ f8arr _ _ _ _ _ /\ _ =>
             destruct WDF as [W0E|(WNZ & _ & _ & _ & _ & W16 & RW & RWS & _)]; [left; exact W0E| right];
             destruct (WIN1 WNZ) as (SHW & FW);
             split; [apply f8arr_mod256; exact FW|]; split; [exact W16|]; split; [exact RW|]; split; [exact RWS| exact SHW]
         | |- _ \/ disjoint_from _ _ _ =>
             destruct WDF as [W0E|WDF']; [left; exact W0E| right]; unfold ifast_W, IFAST_STACK; cbn [disjoint_from]; clear - LAYF WDF'; pose proof atop_range; lia
         | |- disjoint_from _ _ _ => unfold ifast_W, IFAST_STACK; cbn [disjoint_from]; clear - LAYF TLAY DLAY; pose proof atop_range; lia
         | |- _ => unfold KHIGH, KEND, IFAST_STACK; clear - LAYF TLAY DLAY WDF CIN0 CINN BITS0 BLE HOLD0 COUT0 COUTN OUT1 OUT2 OUT3 WH0 WN0 H6 H258 LB15 DB15; pose proof atop_range; lia
         end.
    intros ms' PO.
    destruct PO as (cin' & cout' & hold' & bits' & mode' & fo' & zmsg' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m'
                    & EQ & MUc & WMc & MIc & STKc & CI' & CO' & BI' & HO' & BL' & W1' & W2' & MD' & STRM' & SSC' & OUT' & FOR').
    subst ms'. rewrite ?(unsigned_lit SPA) in MUc, STKc by (clear - LAYF; pose proof atop_range; lia).
    Local Ltac dj LAYF TLAY DLAY := unfold ifast_W, IFAST_STACK; cbn [disjoint_from]; clear - LAYF TLAY DLAY; pose proof atop_range; lia.
    pose proof (rw_cells_transport bsegs _ _ _ _ _ FRM MUc WMc ltac:(match goal with |- context [Z.of_nat (cells_size ?l)] => change (Z.of_nat (cells_size l)) with 568 end; dj LAYF TLAY DLAY)) as FRM'.
    pose proof (rw_cells_transport bsegs _ _ _ _ _ TAIL MUc WMc ltac:(match goal with |- context [Z.of_nat (cells_size ?l)] => change (Z.of_nat (cells_size l)) with 16 end; dj LAYF TLAY DLAY)) as TAIL'.
    pose proof (f16arr_transport bsegs _ _ _ _ _ _ LENS MUc WMc ltac:(change (Z.of_nat 320) with 320; dj LAYF TLAY DLAY)) as LENS'.
    pose proof (f16arr_transport bsegs _ _ _ _ _ _ WORK MUc WMc ltac:(change (Z.of_nat 288) with 288; dj LAYF TLAY DLAY)) as WORK'.
    pose proof (f32arr_transport bsegs _ _ _ _ _ _ CODES MUc WMc ltac:(change (Z.of_nat 1444) with 1444; dj LAYF TLAY DLAY)) as CODES'.
    pose proof (bytes_at_transport bsegs _ _ _ _ _ PAYB MUc ltac:(rewrite PL; dj LAYF TLAY DLAY)) as PAYB'.
    assert (MU' : munch [(lo, SPA + 568); (Zs, Zs + 112); (S, S + 7176); (6341056, 6341056 + osz)] m m').
    { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MUc]. unfold sub_fp, ifast_W, IFAST_STACK. intros x Hx. cbn [outside] in *. clear - Hx LAYF. lia. }
    pose proof (wmono_trans bsegs _ _ _ WM WMc) as WM'.
    clear FRM TAIL LENS WORK CODES PAYB MU WM STRM SSC OUT MI STK RTG RTS MUc WMc HID1 AH1 SHZ1 SHS1 SHO1 WIN1 UNP1 SHLF1 SHDF1 CTL CTD.
    rename FRM' into FRM, TAIL' into TAIL, LENS' into LENS, WORK' into WORK, CODES' into CODES, PAYB' into PAYB, MU' into MU, WM' into WM, STRM' into STRM, SSC' into SSC, OUT' into OUT, MIc into MI, STKc into STK.
    unfold strm_cells in STRM. unfold istate_cells in SSC.
    replace (ret_pc (Z_to_bv 64 595068)) with (Z_to_bv 64 595068) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    subst la da.
    assert (ARR' : inf_arr_ok (ICX u S D n 6341056 osz Wd cin0 cout0 W0 K0 zc) wf fo') by (split; [exact (proj1 ARR)| exact FOR']).
    assert (SAF : forall md, (md = LEN \/ md = TYPE \/ md = BAD) ->
              sinv (ICX u S D n 6341056 osz Wd cin0 cout0 W0 K0 zc) (IST md last flags cin' cout' hold' bits' out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf
              /\ meas (ICX u S D n 6341056 osz Wd cin0 cout0 W0 K0 zc) (IST md last flags cin' cout' hold' bits' out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                 < meas (ICX u S D n 6341056 osz Wd cin0 cout0 W0 K0 zc) (IST LEN last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)).
    { intros md HMD.
      pose proof (sinv_after_fast _ _ lf cf md cin' cout' hold' bits' SI eq_refl ltac:(clear - CI'; lia) ltac:(gcbn; clear - CI'; lia) ltac:(gcbn; clear - CO'; lia) ltac:(gcbn; clear - CO'; lia)
                    ltac:(clear - BI'; lia) ltac:(clear - BI'; lia) ltac:(clear - HO'; lia) ltac:(clear - HO'; lia) BL' ltac:(gcbn; exact W1') ltac:(gcbn; exact W2') HMD) as SAF0.
      unfold st_fast in SAF0. exact SAF0. }
    zrung [0x91524].
    destruct MD' as [EM|[EM|EM]]; subst mode'.
    -
      destruct (SAF LEN ltac:(left; reflexivity)) as (SI2 & ME2).
      change LEN with 16200 in SSC.
      zrung [0x8e260].
      eapply (KD (IST LEN last flags cin' cout' hold' bits' out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo');
        [exact SI2| exact ME2| exact ARR'| change LEN with 16200; inf_vis_close| inf_hid_close].
    -
      destruct (SAF TYPE ltac:(right; left; reflexivity)) as (SI2 & ME2).
      change TYPE with 16191 in SSC.
      zrung [0x8e260].
      eapply (KD (IST TYPE last flags cin' cout' hold' bits' out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo');
        [exact SI2| exact ME2| exact ARR'| change TYPE with 16191; inf_vis_close| inf_hid_close].
    -
      destruct (SAF BAD ltac:(right; right; reflexivity)) as (SI2 & ME2).
      change BAD with 16209 in SSC.
      zrung [0x8e260].
      eapply (KD (IST BAD last flags cin' cout' hold' bits' out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo');
        [exact SI2| exact ME2| exact ARR'| change BAD with 16209; inf_vis_close| inf_hid_close].
    (* [U14B] A2 2026-11-12: v24 is a vestige binder at 1.4 (InfBBase's inf_locals no longer holds it), so eapply leaves
       it as a shelved word; any value does (G's U1A cure for v240) *)
    Unshelve. all: exact (Z_to_bv 64 0).
  Time Qed.

  Theorem lfast : forall cx ly, LFAST_STMT AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh cx ly.
  Proof. intros cx ly. unfold LFAST_STMT. intros. eapply lfast_walk; eassumption. Qed.
End S.
End CANSEC1.
