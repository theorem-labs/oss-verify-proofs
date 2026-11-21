(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Lib Require Import Arr Bytes ZBridge Tac InitMem.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.BothW Require Import BImg RtCells ABase ABytes AMalloc_iface AUri_kit I_asan_memset.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2A Require Import U2AShadow U2AKit U2AObj U2ABlob.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2B Require Import U2BObj U2BClient U2BCall U2BIface.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2B Require Import U2BKit.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= first [ solve_load_sh0 | solve_load_shlit | solve_load_base | solve_load_image ].
Local Ltac acc_hint ::= acc_hint_sh.

(* [U14B] A2 2026-11-12: zlib 1.4's inflateInit2_ zeroes the whole state block with memset (combined image: 0x8df00 jal
   __asan_memset with a0 = state, a1 = 0, a2 = 7176; 1.3.1 wrote the fields one by one).  The 7176 zero bytes as the 1.4
   inflate_state cells of U2AObj.istate_cells (33 head cells, 168 bytes), the 6992-byte arrays and the 16-byte tail
. *)
Definition isz4 : cell := C4 (Z_to_bv 64 0).
Definition isz8 : cell := C8 (Z_to_bv 64 0).
Definition isall0 : list cell :=
  [isz8; isz4; isz4; isz4; isz4; isz4; isz4; isz4; isz4; isz8; isz8; isz8; isz4; isz4; isz4; isz4; isz4; isz4; isz8; isz8;
   isz4; isz4; isz4; isz4; isz8; isz8; isz4; isz4; isz4; isz4; isz4; isz4; isz8;
   CB (Z.to_nat 6992) (repeat (Z_to_bv 8 0) (Z.to_nat 6992)); isz4; isz4; isz4; isz4].

Section CANSEC1. Context {rc : runConstT}.
Section S.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32).
  Variables (Fu Zs S lo : Z) (RNG : footprint).
  Notation SP := (bv_unsigned sp).
  Hypothesis LOS : lo <= SP - INIT_STACK.
  Hypothesis LOC : ATOP + 4096 <= lo.
  Hypothesis SP16 : SP mod 16 = 0.
  Hypothesis SPT : SP + 16 < KEND.
  Hypothesis ZSE : Zs = Fu + 32.
  Hypothesis FU256 : Fu mod 256 = 0.
  Hypothesis FUB : ablk Fu (Fu + 256).
  Hypothesis SB : ablk S (S + 7176).
  Hypothesis S16 : S mod 16 = 0.
  Hypothesis SEP : S + 7176 <= Fu \/ Fu + 256 <= S.
  Hypothesis RSTK : rng RNG lo (SP - lo).
  Hypothesis RI : rng_aimg RNG.
  Hypothesis RISH : rng_aimg_sh RNG.
  Hypothesis RZ : rng RNG Zs 112.
  Hypothesis RSF : rng RNG (shad Fu) 32.
  Hypothesis RS : rng RNG S 7176.
  Hypothesis RSS : rng RNG (Z.shiftr S 3 + 2147450880) 897.

  Definition init_finW : list (Z * Z) := [(lo, SP); (Zs, Zs + 112); (S, S + 7176)].

  Lemma init_fin : forall (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m
      (next_in avail_in total_in next_out avail_out total_out state data_type adler reserved p1 p2 p3 : word) (junk : list byte)
      (WLO WHI : Z),
    stk bsegs m lo (SP + -80) -> mem_inv bsegs m ->
    rt_got m -> rt_got_ric m -> rt_shbase m -> rt_inited m -> rt_layout m -> rt_real_mem m ->
    (* [U14B] A2 2026-11-12: the 1.4 combined inflateInit_ frame: 80 bytes, ra and s0 .. s8 (InitB_pre) *)
    rw_cells bsegs m (SP + -80) [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells bsegs m Zs (strm_cells next_in avail_in total_in next_out avail_out total_out (Z_to_bv 64 0) state
                                    (Z_to_bv 64 A_ZCALLOC) (Z_to_bv 64 A_ZCFREE) (Z_to_bv 64 0) data_type adler reserved p1 p2 p3) ->
    rw_cells bsegs m S [CB (Z.to_nat 7176) junk] ->
    shadow_bytes m (Z.shiftr Zs 3 + 2147450880) (Z.shiftr Zs 3 + 2147450880 + 14) (fun _ => 0) ->
    shadow_bytes m (Z.shiftr S 3 + 2147450880) (Z.shiftr S 3 + 2147450880 + 897) (fun _ => 0) ->
    wr_at bsegs m (shad Fu) 32 ->
    (* [U14B] A2 2026-11-12: the state block's 64-aligned shadow window, for __asan_memset(S, 0, 7176) (the premises of
       U2BCall.asan_memset_callz; InitB gets them from AI_block, as UwB.win_hull does for the window) *)
    (WLO <= S /\ S + 7176 <= WHI /\ WLO mod 64 = 0 /\ WHI mod 64 = 0 /\ 0 <= WLO /\ WHI <= KEND) ->
    rng RNG (shad WLO) (shad WHI - shad WLO) -> wr_at bsegs m (shad WLO) (shad WHI - shad WLO) ->
    evtF bsegs RNG (fun ms' => exists (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) m'
                                     (check len off ext lb db ncode nlen ndist have was pad : word) (jarr : list byte),
        ms' = MS (mkR ra sp gp tp x5 x6 x7 s0 s1 (Z_to_bv 64 0) x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                 FR (ret_pc ra) fc None m' (seg_rom bsegs)
        /\ munch init_finW m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
        /\ stk bsegs m' lo SP
        (* [U14B] A2 2026-11-12: zlib 1.4's inflateResetKeep stores strm->data_type = 0 (1.3.1 left it); measured: the
           strm cells at the closing step of build c19 hold C4 (Z_to_bv 64 0) there (G's U1A cure C43) *)
        /\ rw_cells bsegs m' Zs (strm_cells next_in avail_in (Z_to_bv 64 0) next_out avail_out (Z_to_bv 64 0) (Z_to_bv 64 0)
                                            (Z_to_bv 64 S) (Z_to_bv 64 A_ZCALLOC) (Z_to_bv 64 A_ZCFREE) (Z_to_bv 64 0) (Z_to_bv 64 0)
                                            (Z_to_bv 64 1) reserved p1 p2 p3)
        /\ rw_cells bsegs m' S (istate_cells (Z_to_bv 64 Zs) (Z_to_bv 64 16180) (Z_to_bv 64 0) (Z_to_bv 64 5) (Z_to_bv 64 0)
                                      (Z_to_bv 64 (-1)) (Z_to_bv 64 32768) check (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 15)
                                      (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)
                                      len off ext (Z_to_bv 64 (S + 1384)) (Z_to_bv 64 (S + 1384)) lb db ncode nlen ndist have
                                      (Z_to_bv 64 (S + 1384)))
        /\ rw_cells bsegs m' (S + 168) [CB (Z.to_nat 6992) jarr]
        /\ rw_cells bsegs m' (S + 7160) (itail_cells (Z_to_bv 64 1) (Z_to_bv 64 (-1)) was pad))
      (* [U14B] A2 2026-11-12: the registers InitB_pre's init_pre leaves at the zalloc call, with a0 = S *)
      (MS (mkR (Z_to_bv 64 581304) (Z_to_bv 64 (SP + -80)) gp tp t0 t1 t2 (Z_to_bv 64 (Zs + 80)) (Z_to_bv 64 (Zs + 72))
               (Z_to_bv 64 S) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 7176) s3 (Z_to_bv 64 Zs) (Z_to_bv 64 2147450880)
               (Z_to_bv 64 (Z.shiftr (Zs + 72) 3 + 2147450880)) (Z_to_bv 64 (Z.shiftr (Zs + 80) 3 + 2147450880)) s8
               s9 s10 s11 t3 t4 t5 t6)
          FR (Z_to_bv 64 581304) fc None m (seg_rom bsegs)).
  Proof using All.
    intros until WHI. intros ST MI GOT RIC SHB INI LAY REAL FR0 STRM SBLK SHZ SHS WSF WIN WRN WWR.
    destruct WIN as (WI1 & WI2 & WI3 & WI4 & WI5 & WI6).
    unfold init_finW, INIT_STACK, A_ZCALLOC, A_ZCFREE, strm_cells, istate_cells, itail_cells in *.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. unfold KEND in SPT.
    atop_facts. pose proof (ablk_lin _ _ FUB) as (FB1 & FB2 & FB3 & FB4). unfold AIMG_HI in FB1.
    pose proof (ablk_lin _ _ SB) as (SB1 & SB2 & SB3 & SB4). unfold AIMG_HI in SB1.
    assert (Z8 : Zs mod 8 = 0) by (subst Zs; Z.div_mod_to_equations; lia).
    assert (S8 : S mod 8 = 0) by (Z.div_mod_to_equations; lia).
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose (W := [(lo, SP); (Zs, Zs + 112); (S, S + 7176)]).
    assert (DJZ : disjoint_from W (Z.shiftr Zs 3 + 2147450880) (Z.shiftr Zs 3 + 2147450880 + 14 - (Z.shiftr Zs 3 + 2147450880))).
    { subst W. cbn [disjoint_from]. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. unfold ablk, AIMG_HI, KLS in FUB, SB. Z.div_mod_to_equations. lia. }
    assert (DJS : disjoint_from W (Z.shiftr S 3 + 2147450880) (Z.shiftr S 3 + 2147450880 + 897 - (Z.shiftr S 3 + 2147450880))).
    { subst W. cbn [disjoint_from]. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. unfold ablk, AIMG_HI, KLS in FUB, SB. Z.div_mod_to_equations. lia. }
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl bsegs m) as WM. subst W.
    (* [U14B] A2 2026-11-12: the 1.4 walk.  (1) memset over the whole state block *)
    zrunb [0x8dec8].
    zs. (* jal __asan_memset (S, 0, 7176) *)
    callq (asan_memset_callz WLO WHI RNG).
    all: lazymatch goal with
         | |- evtF _ _ _ _ => idtac
         | |- rw_cells _ _ _ [CB _ _] => exact SBLK
         | |- stk _ _ _ _ => exact ST
         | |- mem_inv _ _ => exact MI
         | |- rw_cells _ _ _ _ => assumption
         | |- rng_aimg _ => exact RI
         | |- wr_at _ _ _ _ => exact WWR
         | |- rng _ ?l _ => first [ constr_eq l lo; eapply rng_sub'; [exact RSTK| lia]
                                  | exact WRN
                                  | eapply rng_sub'; [exact RS| lia] ]
         | |- app_blk _ _ => eapply ablk_app_blk; [eapply ablk_sub; [exact SB| lia| lia]| lia]
         | |- unpoisoned _ _ _ => eapply (unp_of_sh0 _ S 897); [exact (sh0_mu _ _ _ _ _ SHS MU DJS)| exact S8| lia| lia| lia| lia| lia]
         | |- _ => first [ assumption | unfold KHIGH, KEND in *; lia | unfold KHIGH, KEND in *; Z.div_mod_to_equations; lia ]
         end.
    (* the zeroed state as typed zero cells *)
    lazymatch goal with H : rw_cells bsegs _ S [CB _ (repeat _ _)] |- _ => rename H into SZ end.
    eapply (rw_cells_recast bsegs _ _ _ isall0) in SZ; [| cbn; tauto| reflexivity| vm_compute; reflexivity].
    unfold isall0, isz4, isz8 in SZ.
    rw_split SZ 33%nat SSC SREST. rw_split SREST 1%nat SARR STAIL.
    lazymatch goal with H : munch _ m ?m1 |- _ => pose proof (sh0_mu _ _ _ _ _ SHZ H DJZ) as SHZ1;
                                                    pose proof (sh0_mu _ _ _ _ _ SHS H DJS) as SHS1 end.
    (* (2) strm->state, state->strm, mode; then jal 0x8da8c (inflateReset2's head: frame 80) *)
    zrunb [0x8da54].
    lazymatch goal with H : stk bsegs _ lo (SP + -80) |- _ => rename H into STK end.
    carve_frame 80%nat STK.
    zrunb [0x8dc8c].
    release_frame FR1 STK (SP + -80).
    (* (3) the tail-jump to 0x8d364 (frame 144), its ret at 0x8d860 back to 0x8df64 *)
    zrunb [0x8d32c].
    carve_frame 144%nat STK.
    zrunb [0x8d828].
    release_frame FR1 STK (SP + -80).
    (* (4) inflateInit_'s epilogue *)
    zrunb [0x8dfa8].
    release_frame FR0 STK (bv_unsigned sp).
    zstep. (* ret *)
    replace (Z.land (bv_unsigned (zx32 (Z_to_bv 64 5))) 1) with 1 in STRM by (vm_compute; reflexivity).
    apply evtF_done. do 15 eexists. eexists _, _, _, _, _, _, _, _, _, _, _, _, _. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact STK|].
    split; [exact STRM|]. split; [exact SSC|]. split; [exact SARR| exact STAIL].
  Qed.
End S.
End CANSEC1.
