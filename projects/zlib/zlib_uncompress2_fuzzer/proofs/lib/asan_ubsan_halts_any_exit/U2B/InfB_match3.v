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
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.U2A Require Import U2AShadow U2AKit U2AArr U2AObj U2AStore InfAGlue InfPure InfPure_w7 InfPure_w7d InfPure_w7e InfPure_w7f InfAGlue_w7 InfAGlue_w7b.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.U2B Require Import U2BObj U2BClient U2BIface InfBBase InfBKit InfBTables InfB_w7base InfB_w7tab InfB_w7pull.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.U2A Require Import InfPure_w7g.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.U2B Require Import InfBGlue_p04 U2BCall InfB_match1 InfB_match2.
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
Local Ltac ub_is_trap pc ::= ub_in_traps inf_traps pc.
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
  Notation VIS cx ly st lf cf wf fo v0 v8 v16 v24 v240 v328 v512 j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m :=
    (inf_vis cx ly st lf cf wf fo payload v0 v8 v16 v24 v240 v328 v512 j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m).
  Notation HIDm cx ly m := (inf_hid cx ly AI L RNG stA LB LBc m0 fw saved fk fksh m).
  Notation GARM cx ly Lb X := (garm_stmtA cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh Lb X).

  Definition M_J (cx : ictx) (ly : ilay) (st : ist) (from c : Z) (x5 x6 x10 x11 x12 x15 x16 x17 x19 x21 x22 x23 x26 x29 x30 x31 : word) (m : amem) : machine_state :=
    MS (mkR (Z_to_bv 64 (l_F0 ly)) (Z_to_bv 64 (l_SPA ly)) gp tp x5 x6 (Z_to_bv 64 (c_n cx - t_cin st)) (Z_to_bv 64 (l_SP ly)) (Z_to_bv 64 (l_SPA ly)) x10 x11 x12
            (Z_to_bv 64 c) (Z_to_bv 64 from) x15 x16 x17
            (Z_to_bv 64 (l_Zs ly)) x19 x21 (Z_to_bv 64 2147450880) x22 (Z_to_bv 64 (t_hold st))
            (Z_to_bv 64 (Z.shiftr (l_F0 ly) 3 + 2147450880)) x23 x26 (Z_to_bv 64 (l_F0 ly)) (Z_to_bv 64 (t_bits st)) x29 x30 x31)
       FR (Z_to_bv 64 0x92458) fc None m (seg_rom bsegs).

  Lemma m_join_w : forall (cx : ictx) (ly : ilay) (st : ist) (lf cf wf fo : Z -> Z) (v0 v8 v16 v24 v240 v328 j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word)
      (wi c0 : Z) (x5 x6 x10 x11 x12 x15 x16 x17 x19 x21 x22 x23 x26 x29 x30 x31 : word) (m : amem),
    inf_ctx cx ly AI RNG LB -> Forall (fun c => 0 <= c < 256) payload -> Z.of_nat (length payload) = c_n cx ->
    t_mode st = MATCH -> sinv cx st lf cf -> inf_arr_ok cx wf fo ->
    VIS cx ly st lf cf wf fo v0 v8 v16 v24 v240 v328 (Z_to_bv 64 (Z.shiftr (c_p cx + 108) 3)) j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m -> HIDm cx ly m -> KALLB cx ly (meas cx st) ->
    c_w cx <> 0 -> 0 <= wi -> wi + c0 <= 32768 -> 1 <= c0 -> 1 <= c_osz cx - t_cout st ->
    evtF bsegs RNG POST (M_J cx ly st (c_w cx + wi) c0 x5 x6 x10 x11 x12 x15 x16 x17 x19 x21 x22 x23 x26 x29 x30 x31 m).
  Proof.
    intros until m. intros CTX PAYR PLEN MODE SI ARR VIS HID KA WNZ HWI0 HWI1 HC1 HL1.
    destruct (sinv_match_facts _ _ _ _ SI MODE) as (LEN1 & LEN16 & OFF).
    pose proof (proj1 SI) as RN1. unfold IDefs.RNG in RN1. destruct RN1 as (_ & _ & COUT0 & COUTN & _).
    unfold M_J.
    inf_arm_open.
    clear R13.
    Local Ltac to_goV KA CTX0 PAYR PLEN MODE SI ARR VISf HID WNZ wiv cv lyv :=
      lazymatch type of SI with sinv ?cx0 ?st0 ?lf0 ?cf0 =>
        lazymatch type of ARR with inf_arr_ok _ ?wf0 ?fo0 =>
          eapply (m_go_w AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh cx0 lyv st0 lf0 cf0 wf0 fo0) with (wi := wiv) (c := cv);
            [exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| exact VISf| exact HID| exact KA| exact WNZ| | | | ] end end.
    zrung [0x92470].
    zs. zbr0 KCL.
    -
      zrung [0x92488]. zs. zbr0 KLF.
      +
        zrung [0x924a0].
        to_goV KA CTX0 PAYR PLEN MODE SI ARR VISf HID WNZ wi c0 (ILAY SP SPA Zs F0 lo); clear - HWI0 HWI1 HC1 HL1 KCL KLF LEN1 COUT0 COUTN; gcbn; lia.
      +
        zrung [0x924a0].
        to_goV KA CTX0 PAYR PLEN MODE SI ARR VISf HID WNZ wi (osz - cout) (ILAY SP SPA Zs F0 lo); clear - HWI0 HWI1 HC1 HL1 KCL KLF LEN1 COUT0 COUTN; gcbn; lia.
    -
      zrung [0x9247c]. zs. zbr0 KLF.
      + zrung [0x924a0].
        to_goV KA CTX0 PAYR PLEN MODE SI ARR VISf HID WNZ wi len (ILAY SP SPA Zs F0 lo); clear - HWI0 HWI1 HC1 HL1 KCL KLF LEN1 COUT0 COUTN; gcbn; lia.
      + zrung [0x924a0].
        to_goV KA CTX0 PAYR PLEN MODE SI ARR VISf HID WNZ wi (osz - cout) (ILAY SP SPA Zs F0 lo); clear - HWI0 HWI1 HC1 HL1 KCL KLF LEN1 COUT0 COUTN; gcbn; lia.
  Qed.

  Theorem match_garm : forall cx ly, GARM cx ly 0x9222c MATCH.
  Proof.
    intros cx ly. unfold garm_stmtA, GARM_MS. intros until m. intros CTX PAYR PLEN MODE SI ARR VIS HID KA.
    pose proof KA as (KD & KB & KL & KLV).
    destruct (sinv_match_facts _ _ _ _ SI MODE) as (LEN1 & LEN16 & OFF).
    destruct (sinv_match_win _ _ _ _ SI) as (WIN0 & WIN1).
    pose proof (proj1 SI) as RN1. unfold IDefs.RNG in RN1.
    destruct RN1 as (_ & _ & COUT0 & COUTN & _ & _ & _ & _ & _ & _ & OUT1 & OUT2 & OUT3 & _ & _ & _ & _ & OFF0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & WH0 & WN0 & _).
    inf_arm_open.
    clear R13.
    assert (WHB : whave <= 32768 /\ wnext <= 32768) by (clear - WIN0 WIN1 WH0 WN0; destruct (Z.eq_dec Wd 0) as [E|E]; [destruct (WIN0 E); lia| destruct (WIN1 E); lia]).
    assert (OSZ2 : osz <= 262144) by (clear - OSZ; lia).
    zs. zs. zbr0 KLEFT.
    2: {
      assert (EC : cout = osz) by (clear - KLEFT; lia). subst cout. replace (osz - osz) with 0 in * by (clear; lia).
      zrung [0x9366c].
      eapply (KLV (IST mode last flags cin osz hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) ret lf cf wf fo);
        [exact SI| exact ARR| unfold inf_vis, inf_locals; cbn [c_osz t_cout]; replace (osz - osz) with 0 by (clear; lia); inf_vis_close| inf_hid_close]. }
    zrung [0x92250].
    zs. rewrite ?(zx32_small offset) by (clear - OFF OFF0; lia).
    zrung [0x92264].
    zs. zbr0 KOFF.
    -
      zrung [0x92334].
      replace (6341696 + cout - offset) with (6341696 + (cout - offset)) by (clear; lia).
      zs. zbr0 KLL.
      +
        zrung [0x924a0].
        eapply (m_go_o AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh (ICX u S D n 6341696 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo) with (fi := cout - offset) (c := osz - cout);
          [exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| inf_vis_close| inf_hid_close| exact KA| | | ]; clear - KOFF OUT3 OFF0 KLL KLEFT LEN1 COUT0 COUTN; gcbn; lia.
      +
        zrung [0x924a0].
        eapply (m_go_o AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh (ICX u S D n 6341696 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo) with (fi := cout - offset) (c := len);
          [exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| inf_vis_close| inf_hid_close| exact KA| | | ]; clear - KOFF OUT3 OFF0 KLL KLEFT LEN1 COUT0 COUTN; gcbn; lia.
    -
      (* [U14B] A2 2026-11-12: the 1.4 code loads frame slot 80 before the whave branch (0x922b8 ld a0,80(s1); 0x922bc bgeu
         a4,a3,0x92384); 1.3.1 branched first (0x91ddc), so the mover's 0x922b8 is one instruction early *)
      zrung [0x92284].
      zs. zbr0 KWH.
      +
        assert (WNZ : Wd <> 0) by (intros E; destruct (WIN0 E) as (W1 & _); clear - W1 KWH KOFF; lia).
        destruct (WIN1 WNZ) as (WH32 & WN32).
        assert (WSZE : wsz (ICX u S D n 6341696 osz Wd cin0 cout0 W0 K0 zc) = 32768) by (unfold wsz; cbn [c_w]; destruct (Wd =? 0) eqn:EW; [apply Z.eqb_eq in EW; contradiction| reflexivity]).
        zrung [0x92374].
        zs. zbr0 KWN.
        *
          destruct WDC as [W0E|(W16 & WAB & _)]; [exfalso; exact (WNZ W0E)|].
          pose proof (ablk_lin _ _ WAB) as (WB1 & WB2 & WB3 & WB4). unfold AIMG_HI in WB1. change (2 ^ 47) with 140737488355328 in WB4.
          zrung [0x92458].

          rewrite (Z.mod_small (wnext - (offset - (out - (osz - cout)))) 4294967296) by (clear - KWN WN32 KOFF OFF0; lia).
          zrung [0x92458].
          eapply (m_join_w (ICX u S D n 6341696 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo)
            with (wi := wnext - (offset - (out - (osz - cout)))) (c0 := offset - (out - (osz - cout)));
            [exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| inf_vis_close| inf_hid_close| exact KA| exact WNZ| | | | ];
            clear - KWN WN32 KOFF KLEFT COUT0 COUTN; gcbn; lia.
        *
          destruct WDC as [W0E|(W16 & WAB & _)]; [exfalso; exact (WNZ W0E)|].
          pose proof (ablk_lin _ _ WAB) as (WB1 & WB2 & WB3 & WB4). unfold AIMG_HI in WB1. change (2 ^ 47) with 140737488355328 in WB4.
          zrung [0x923a0].
          lazymatch goal with HS : rw_cells bsegs _ S (C8 _ :: _) |- _ => rewrite WSZE in HS end.
          zs.
          lazymatch goal with HS : rw_cells bsegs _ S (C8 _ :: _) |- _ => rewrite <- WSZE in HS end.
          zrung [0x92458].

          rewrite (Z.mod_small (32768 - (offset - (out - (osz - cout)) - wnext)) 4294967296) by (clear - KWN KWH WH32 WN0 KOFF OFF0; lia).
          zrung [0x92458].
          replace (32768 - (offset - (out - (osz - cout)) - wnext) + Wd) with (Wd + (32768 - (offset - (out - (osz - cout)) - wnext))) by (clear; lia).
          eapply (m_join_w (ICX u S D n 6341696 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo)
            with (wi := 32768 - (offset - (out - (osz - cout)) - wnext)) (c0 := offset - (out - (osz - cout)) - wnext);
            [exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| inf_vis_close| inf_hid_close| exact KA| exact WNZ| | | | ];
            clear - KWN KWH WH32 WN0 WN32 KOFF KLEFT COUT0 COUTN; gcbn; lia.
      +
        zrung [0x92408].
        pose proof (sinv_bad_ofP _ _ lf cf SI) as SIB.
        pose proof (meas_bad_ofP (ICX u S D n 6341696 osz Wd cin0 cout0 W0 K0 zc) (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)) as MEB.
        unfold bad_ofP in SIB, MEB. st_norm SIB. st_norm MEB. subst mode. change (rank MATCH) with 14 in MEB.
        eapply (KB (IST MATCH last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo);
          [exact SIB| unfold bad_of; icx_cbn; clear - MEB; lia| exact ARR| change MATCH with 16204; inf_vis_close| inf_hid_close].
    (* [U14B] A2 2026-11-12: v24 is a vestige binder at 1.4 (InfBBase's inf_locals no longer holds it), so eapply leaves
       it as a shelved word; any value does (G's U1A cure for v240) *)
    Unshelve. all: exact (Z_to_bv 64 0).
  Qed.
End S.
End CANSEC1.
