(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.Lib Require Import Arr Bytes ZBridge Tac InitMem.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.AsanW Require Import AImg RtCells ABase ABytes AMalloc_iface AUri_kit I_asan_memset.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.U2A Require Import U2AShadow U2AKit U2ABlob.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.U1A Require Import U2AObj U2AClient U2ACall U2AIface.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= first [ solve_load_sh0 | solve_load_shlit | solve_load_base | solve_load_image ].
Local Ltac acc_hint ::= acc_hint_sh.

(* the 1.4 inflate_state, as U2A/U2AObj's istate_cells states it: a
   168-byte head of 33 cells (1.3.1: 152 bytes, 29 cells; 1.4 adds four 4-byte fields: after wrap, after dmax, after
   head, after wnext), then the 6992-byte arrays at S + 168 and the 16-byte tail at S + 7160; 7176 bytes in all. *)
Definition istate_shape : list cshape :=
  [SH8; SH4; SH4; SH4; SH4; SH4; SH4; SH4; SH4; SH8; SH8; SH8; SH4; SH4; SH4; SH4; SH4; SH4; SH8; SH8; SH4; SH4;
   SH4; SH4; SH8; SH8; SH4; SH4; SH4; SH4; SH4; SH4; SH8; SHB (Z.to_nat 6992); SH4; SH4; SH4; SH4].
(* the state block before inflateInit2_'s __asan_memset(state + 8, 0, 7168) (1.4) *)
Definition isblk_shape : list cshape := [SH8; SHB (Z.to_nat 7168)].
(* ... and the 7168 zero bytes after it, as the 1.4 istate cells after state->strm (32 head cells, the arrays, the tail) *)
Definition isz4 : cell := C4 (Z_to_bv 64 0).
Definition isz8 : cell := C8 (Z_to_bv 64 0).
Definition isrest0 : list cell :=
  [isz4; isz4; isz4; isz4; isz4; isz4; isz4; isz4; isz8; isz8; isz8; isz4; isz4; isz4; isz4; isz4; isz4; isz8; isz8;
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
      (j8 : list byte) (RLO RHI : Z),
    stk asegs m lo (SP + -112) -> mem_inv asegs m ->
    rt_got m -> rt_got_ric m -> rt_shbase m -> rt_inited m -> rt_layout m -> rt_real_mem m ->
    rw_cells asegs m (SP + -112) [CB 8 j8; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells asegs m Zs (strm_cells next_in avail_in total_in next_out avail_out total_out (Z_to_bv 64 0) state
                                    (Z_to_bv 64 A_ZCALLOC) (Z_to_bv 64 A_ZCFREE) (Z_to_bv 64 0) data_type adler reserved p1 p2 p3) ->
    rw_cells asegs m S [CB (Z.to_nat 7176) junk] ->
    shadow_bytes m (Z.shiftr Zs 3 + 2147450880) (Z.shiftr Zs 3 + 2147450880 + 14) (fun _ => 0) ->
    shadow_bytes m (Z.shiftr S 3 + 2147450880) (Z.shiftr S 3 + 2147450880 + 897) (fun _ => 0) ->
    wr_at asegs m (shad Fu) 32 ->
    (* the state block's 4096-aligned shadow window (AI_block), for __asan_memset(S + 8, 0, 7168) *)
    RLO mod 64 = 0 -> RHI mod 64 = 0 -> 0 <= RLO -> RLO + 64 <= S -> S + 7176 + 64 <= RHI -> RHI <= KEND ->
    rng RNG (shad RLO) (shlen (RHI - RLO)) -> wr_at asegs m (shad RLO) (shlen (RHI - RLO)) ->
    evtF asegs RNG (fun ms' => exists (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) m'
                                     (check len off ext lb db ncode nlen ndist have was pad : word) (jarr : list byte),
        ms' = MS (mkR ra sp gp tp x5 x6 x7 s0 s1 (Z_to_bv 64 0) x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                 FR (ret_pc ra) fc None m' (seg_rom asegs)
        /\ munch init_finW m m' /\ wmono asegs m m' /\ mem_inv asegs m'
        /\ stk asegs m' lo SP
        /\ rw_cells asegs m' Zs (strm_cells next_in avail_in (Z_to_bv 64 0) next_out avail_out (Z_to_bv 64 0) (Z_to_bv 64 0)
                                            (Z_to_bv 64 S) (Z_to_bv 64 A_ZCALLOC) (Z_to_bv 64 A_ZCFREE) (Z_to_bv 64 0) (Z_to_bv 64 0)
                                            (Z_to_bv 64 1) reserved p1 p2 p3)
        /\ rw_cells asegs m' S (istate_cells (Z_to_bv 64 Zs) (Z_to_bv 64 16180) (Z_to_bv 64 0) (Z_to_bv 64 5) (Z_to_bv 64 0)
                                      (Z_to_bv 64 (-1)) (Z_to_bv 64 32768) check (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 15)
                                      (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)
                                      len off ext (Z_to_bv 64 (S + 1384)) (Z_to_bv 64 (S + 1384)) lb db ncode nlen ndist have
                                      (Z_to_bv 64 (S + 1384)))
        /\ rw_cells asegs m' (S + 168) [CB (Z.to_nat 6992) jarr]
        /\ rw_cells asegs m' (S + 7160) (itail_cells (Z_to_bv 64 1) (Z_to_bv 64 (-1)) was pad))
      (* enter at the zalloc return 0x8d800 of inflateInit2_ with a0 = S, and inflateInit2_'s
         registers (s0 = strm+80, s1 = strm+72, s3 = strm, s4 = strm+64, s6 = shadow base, s7 / s8 / s10 their
         shadows, s11 = windowBits 15; s2 / s5 / s9 still the caller's), as InitA_pre's init_pre leaves them *)
      (MS (mkR (Z_to_bv 64 0x8d850) (Z_to_bv 64 (SP + -112)) gp tp t0 t1 t2 (Z_to_bv 64 (Zs + 80)) (Z_to_bv 64 (Zs + 72))
               (Z_to_bv 64 S) a1 a2 a3 a4 a5 a6 a7
               s2 (Z_to_bv 64 Zs) (Z_to_bv 64 (Zs + 64)) s5 (Z_to_bv 64 2147450880)
               (Z_to_bv 64 (Z.shiftr (Zs + 72) 3 + 2147450880)) (Z_to_bv 64 (Z.shiftr (Zs + 80) 3 + 2147450880)) s9
               (Z_to_bv 64 (Z.shiftr (Zs + 64) 3 + 2147450880)) (Z_to_bv 64 15) t3 t4 t5 t6)
          FR (Z_to_bv 64 0x8d850) fc None m (seg_rom asegs)).
  Proof using All.
    intros until RHI. intros ST MI GOT RIC SHB INI LAY REAL FR0 STRM SBLK SHZ SHS WSF HRL HRH HR0 HRS HRE HRK HRN HWR.
    unfold init_finW, INIT_STACK, A_ZCALLOC, A_ZCFREE, strm_cells, istate_cells, itail_cells in *.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. unfold KEND in SPT.
    atop_facts. pose proof (ablk_lin _ _ FUB) as (FB1 & FB2 & FB3 & FB4). unfold AIMG_HI in FB1.
    pose proof (ablk_lin _ _ SB) as (SB1 & SB2 & SB3 & SB4). unfold AIMG_HI in SB1.
    assert (Z8 : Zs mod 8 = 0) by (subst Zs; Z.div_mod_to_equations; lia).
    assert (S8 : S mod 8 = 0) by (Z.div_mod_to_equations; lia).
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    (* the state block as state->strm (8 bytes), then the 7168 bytes __asan_memset zeroes *)
    apply (rw_cells_chop asegs m S (Z.to_nat 7176) junk isblk_shape) in SBLK; [| vm_compute; reflexivity].
    cbn [chop chop1 shape_size isblk_shape] in SBLK. chop_names SBLK.
    rw_split SBLK 1%nat SB0 SBM.
    pose (W := [(lo, SP); (Zs, Zs + 112); (S, S + 7176)]).
    assert (DJZ : disjoint_from W (Z.shiftr Zs 3 + 2147450880) (Z.shiftr Zs 3 + 2147450880 + 14 - (Z.shiftr Zs 3 + 2147450880))).
    { subst W. cbn [disjoint_from]. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. unfold ablk, AIMG_HI, KLS in FUB, SB. Z.div_mod_to_equations. lia. }
    assert (DJS : disjoint_from W (Z.shiftr S 3 + 2147450880) (Z.shiftr S 3 + 2147450880 + 897 - (Z.shiftr S 3 + 2147450880))).
    { subst W. cbn [disjoint_from]. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. unfold ablk, AIMG_HI, KLS in FUB, SB. Z.div_mod_to_equations. lia. }
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl asegs m) as WM. subst W.
    zrunb [0x8d86c].
    zs. (* jal __asan_memset (S + 8, 0, 7168) *)
    callq (asan_memset_callz RLO RHI RNG).
    all: lazymatch goal with
         | |- evtF _ _ _ _ => idtac
         | |- rw_cells _ _ _ [CB _ _] => exact SBM
         | |- stk _ _ _ _ => exact ST
         | |- mem_inv _ _ => exact MI
         | |- rw_cells _ _ _ _ => assumption
         | |- rng_aimg _ => exact RI
         | |- wr_at _ _ _ _ => replace (shad RHI - shad RLO) with (shlen (RHI - RLO)); [exact HWR|];
                                rewrite !shad_div; unfold shlen; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia
         | |- rng _ ?l _ => first [ constr_eq l lo; eapply rng_sub'; [exact RSTK| lia]
                                  | replace (shad RHI - shad RLO) with (shlen (RHI - RLO)); [exact HRN|];
                                    rewrite !shad_div; unfold shlen; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia
                                  | eapply rng_sub'; [exact RS| lia] ]
         | |- app_blk _ _ => eapply ablk_app_blk; [eapply ablk_sub; [exact SB| lia| lia]| lia]
         | |- unpoisoned _ _ _ => eapply (unp_of_sh0 _ S 897); [exact (sh0_mu _ _ _ _ _ SHS MU DJS)| exact S8| lia| lia| lia| lia| lia]
         | |- _ => first [ unfold KHIGH, KEND in *; lia | unfold KHIGH, KEND; Z.div_mod_to_equations; lia ]
         end.
    (* the zeroed state as typed zero cells *)
    lazymatch goal with H : rw_cells asegs _ (S + 8) [CB _ (repeat _ _)] |- _ => rename H into SZ end.
    eapply (rw_cells_recast asegs _ _ _ isrest0) in SZ; [| cbn; tauto| reflexivity| vm_compute; reflexivity].
    unfold isrest0, isz4, isz8 in SZ.
    rw_split SZ 32%nat SHD SREST. rw_split SREST 1%nat SARR STAIL.
    lazymatch goal with H : munch _ m ?m1 |- _ => pose proof (sh0_mu _ _ _ _ _ SHZ H DJZ) as SHZ1;
                                                    pose proof (sh0_mu _ _ _ _ _ SHS H DJS) as SHS1 end.
    zrunb [0x8d990].
    zs. (* 1.4: jal inflateReset2 (0x8cff0, frame 144) *)
    lazymatch goal with H : stk asegs _ lo (SP + -112) |- _ => rename H into STK1 end.
    carve_frame 144%nat STK1.
    zrunb [0x8d330].
    zs. (* inflateResetKeep: jal __asan_memset (strm + 40, 0, 16): total_out, msg *)
    lazymatch goal with H : rw_cells asegs _ Zs _ |- _ => rename H into STRMa end.
    rw_split STRMa 7%nat STRM1 STRM2. rw_split STRM2 2%nat STRMM STRM3.
    apply rw_cells_forget in STRMM. destruct STRMM as [jm STRMM]. cbn [cells_size csize Nat.add] in STRMM.
    callq (asan_memset_callz Fu (Fu + 256) RNG).
    all: try lazymatch goal with
         | |- evtF _ _ _ _ => idtac
         | |- rw_cells _ _ _ [CB _ _] => exact STRMM
         | |- stk _ _ _ _ => first [ assumption
                                   | lazymatch goal with H : stk asegs ?mm lo ?h |- stk asegs ?mm _ ?h' =>
                                       replace h' with h by lia; exact H end ]
         | |- mem_inv _ _ => assumption
         | |- rw_cells _ _ _ _ => assumption
         | |- rng_aimg _ => exact RI
         | |- rng _ ?l _ => first [ constr_eq l lo; eapply rng_sub'; [exact RSTK| lia]
                                  | eapply rng_sub'; [exact RZ| lia]
                                  | replace (shad (Fu + 256) - shad Fu) with 32 by (rewrite !shad_div; Z.div_mod_to_equations; lia); exact RSF ]
         | |- wr_at _ _ _ _ => replace (shad (Fu + 256) - shad Fu) with 32 by (rewrite !shad_div; Z.div_mod_to_equations; lia);
                                first [ exact WSF | eapply wr_at_transport; [exact WSF| eassumption] ]
         | |- app_blk _ _ => eapply ablk_app_blk; [eapply ablk_sub; [exact FUB| lia| lia]| lia]
         | |- unpoisoned _ _ _ =>
             eapply (unp_of_sh0 _ Zs 14); [exact (sh0_mu _ _ _ _ _ SHZ MU DJZ)| exact Z8| lia| lia| lia| lia| lia]
         | |- _ => first [ unfold KHIGH, KEND in *; lia | unfold KHIGH, KEND; Z.div_mod_to_equations; lia ]
         end.
    lazymatch goal with H : rw_cells asegs _ (Zs + 40) [CB _ _] |- _ => rename H into STRMz end.
    eapply (rw_cells_recast asegs _ _ _ [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]) in STRMz; [| cbn; tauto| reflexivity| reflexivity].
    rw_join STRMz STRM3 STRM2'. rw_join STRM1 STRM2' STRMb. cbn [app] in STRMb.
    zrunb [0x8d994].
    (* back in inflateInit2_: release inflateReset2's 144-byte frame *)
    lazymatch goal with H : stk asegs _ lo _ |- _ => rename H into STK2 end.
    release_frame FR1 STK2 (SP + -112).
    zrunb [0x8da08].
    lazymatch goal with H : stk asegs _ lo (SP + -112) |- _ => rename H into STK end.
    release_frame FR0 STK (bv_unsigned sp).
    zstep. (* ret *)
    rw_join SB0 SHD SSC.
    replace (Z.land (bv_unsigned (zx32 (Z_to_bv 64 5))) 1) with 1 in STRMb by (vm_compute; reflexivity).
    apply evtF_done. do 15 eexists. eexists _, _, _, _, _, _, _, _, _, _, _, _, _. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact STK|].
    split; [exact STRMb|]. split; [exact SSC|]. split; [exact SARR| exact STAIL].
  Qed.
End S.
End CANSEC1.
