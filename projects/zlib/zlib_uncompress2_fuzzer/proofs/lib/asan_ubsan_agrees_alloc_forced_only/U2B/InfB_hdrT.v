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
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2A Require Import U2AShadow U2AKit U2AArr U2AObj U2ABlob U2AStore InfAGlue InfPure InfPure_entry.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2B Require Import U2BObj U2BClient U2BIface InfBBase InfBKit InfBIface InfB_hdr0.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2B Require Import U2BKit.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= first [ solve_load_sh0 | solve_load_shlit | solve_load_base | solve_load_image ].
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

  Lemma inf_hdr1_T : inf_hdr1_stmt AI L RNG stA LB gp tp FR fc POST (fun mo => mo = TYPE).
  Proof.
    unfold inf_hdr1_stmt. intros until m. intros K PMODE CTX AH AINV EM FRA FK FKSH RF RFS SHZ SHS STK MI.
    pose proof (inf_facts AI L RNG stA LB cx ly m AH CTX) as LIN0.
    destruct LIN0 as (Fu & ZSE & FU256 & HFU & (S1 & S2 & bS & BS0 & BS1 & BS2) & (U1 & U2 & bU & BU0 & BU1 & BU2) & (F1 & F2 & bF & BF0 & BF1 & BF2)
                     & DL1 & DL2 & (bD & BD0 & BD1 & BD2) & (cSU & CSU0 & CSU1 & CSU2) & (cSF & CSF0 & CSF1 & CSF2) & (cUF & CUF0 & CUF1 & CUF2)
                     & (cSD & CSD0 & CSD1 & CSD2) & (cUD & CUD0 & CUD1 & CUD2) & (cFD & CFD0 & CFD1 & CFD2)).
    destruct CTX as (S16 & SB & _ & _ & RZ & RSZ & HF0 & F064 & F0B & RS & RSS & OBE & OSZ & OCI & ROB & ROBS & WDC
                     & D1 & NR & D16 & RD & RSD & LOC & LOS & SPAR & SPA32 & SP16 & SPT & RSTK & RI & RISH & RSFU & TABC1 & TABC2 & LBABLK).
    hide_or WDC.
    pose proof EM as (STRM & SSC & _).
    pose proof AINV as (RN & _ & MO). pose proof (proj1 MO) as REACH.
    destruct cx as [u S D n OB osz Wd cin0 cout0 W0 K0 zc]. destruct ly as [SP SPA Zs F0 lo].
    destruct st as [mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
    icx_cbn. cbn [l_SP l_SPA l_Zs l_F0 l_lo] in *.
    unfold IDefs.RNG in RN. icx_cbn. destruct RN as (RN1 & RN2 & RN3 & RN4 & RN5 & RN6 & RN7 & RN8 & RN9 & _).
    unfold strm_cells, istate_cells, itail_cells, A_ZCALLOC, A_ZCFREE in STRM, SSC. icx_cbn. cbn [l_SP l_SPA l_Zs l_F0 l_lo] in *.
    unfold hdr_W, F0_cells, F0_shadow in K.
    atop_facts. unfold KEND in SPT. subst OB. unfold A_OUTBUF in *.
    assert (Z8 : Zs mod 8 = 0) by (subst Zs; Z.div_mod_to_equations; lia).
    assert (S8 : S mod 8 = 0) by (Z.div_mod_to_equations; lia).
    assert (RFRM : rng RNG SPA 568) by (eapply rng_sub'; [exact RSTK| lia]).
    assert (MODER : 16180 <= mode <= 16211) by (unfold reach in REACH; cbv [HEAD DICTID MEM] in REACH; lia).
    pose proof (pow2_le_40 bits ltac:(lia)) as P40.
    cbn [chop chop1 shape_size repeat] in FRA. chop_names FRA.
    pose (W := [(F0, F0 + 64); (Z.shiftr F0 3 + 2147450880, Z.shiftr F0 3 + 2147450880 + 8); (lo, SPA + 568); (S + 8, S + 12)]).
    assert (BSF : 2147450880 <= Z.shiftr F0 3 + 2147450880 /\ Z.shiftr F0 3 + 2147450880 + 8 <= 17594333495296)
      by (rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia).
    assert (DJZ6 : disjoint_from W (Z.shiftr Zs 3 + 2147450880) (Z.shiftr Zs 3 + 2147450880 + 14 - (Z.shiftr Zs 3 + 2147450880))).
    { subst W. cbn [disjoint_from]. rewrite ?Z.shiftr_div_pow2 by lia. change (2^3) with 8. repeat split; try exact I; Z.div_mod_to_equations; lia. }
    assert (DJS6 : disjoint_from W (Z.shiftr S 3 + 2147450880) (Z.shiftr S 3 + 2147450880 + 897 - (Z.shiftr S 3 + 2147450880))).
    { subst W. cbn [disjoint_from]. rewrite ?Z.shiftr_div_pow2 by lia. change (2^3) with 8. repeat split; try exact I; Z.div_mod_to_equations; lia. }
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl bsegs m) as WM. subst W.
    apply shadow8_c1s in FKSH. unfold c1z in FKSH.
    unfold istate_cells in K. icx_cbn. cbn [l_SP l_SPA l_Zs l_F0 l_lo] in K.
    cbv [TYPE] in PMODE. cbn [t_mode] in PMODE. subst mode.
    zrunb [0x8e500].
    eapply K; [| | eassumption| eassumption| exact MU| exact WM| eassumption| eassumption].
    + unfold inf_locals. eassumption.
    + change (mode_load 16191) with 16192. eassumption.
    (* [U14B] A2 2026-11-12: v24 is a vestige binder at 1.4 (InfBBase's inf_locals no longer holds it), so eapply leaves
       it as a shelved word; any value does (G's U1A cure for v240) *)
    Unshelve. all: exact (Z_to_bv 64 0).
  Qed.
End S.
End CANSEC1.
