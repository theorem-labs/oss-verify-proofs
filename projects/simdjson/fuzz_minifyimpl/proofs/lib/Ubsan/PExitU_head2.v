(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import Tac Image ZBridge ITree Nodes Decode SysStep StoreFast MonadX Arr FP.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import F_fmt_fp_lib Stdio_pure STRW_tac Startup_kit Amo_tac DrvAgree.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Ubsan Require Import F_syscalls StdioFiles Stdio_kit UImg PExitU_tac PExitU_defs PIosX_iface PExitU_tail.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Ubsan Require Import RMallocRep RMallocTree RMalloc_iface ROpNew_iface.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Ubsan Require RMalloc_ifaceP.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import Prelim Malloc Monad Stdio Driver HarnessM PState ProgP.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Ubsan Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac steps_to p := xsteps_to p.

Section CANSEC1. Context {rc : runConstT}.
(* [comment removed for export] *)
Lemma RHEAP_ssp : forall s LB m, RHEAP s LB m ->
  rw_cells usegs m 0xdab68 [C8 (Z_to_bv 64 0x10e7c8)] /\ rw_cells usegs m 0x10e7c8 [C8 CAN].
Proof. intros s LB m (st & LB0 & _ & _ & (_ & _ & (_ & _ & _ & G1 & G2 & _) & _) & _). split; [exact G1 | exact G2]. Qed.

(* [comment removed for export] *)
Lemma rclient_range_data : forall LB SP A n,
  0xd4000 <= A -> A + n <= 0x110000 -> (A + n <= 0x10e7e8 \/ 0x10ed08 <= A) -> (A + n <= 0xee4b4 \/ 0xee4b8 <= A) ->
  (A + n <= 0x10e7c8 \/ 0x10e7d0 <= A) -> (A + n <= 0xdab68 \/ 0xdab70 <= A) -> (A + n <= 0x10f54c \/ 0x10f550 <= A) ->
  rclient_range LB SP A n.
Proof.
  intros LB SP A n H1 H2 H3 H4 H5 H6 H7. right; left. unfold RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP. repeat split; lia.
Qed.

Section Head2.
  Hypothesis SE : stdio_exit_spec_stmt2 (St := stdout_st) (fun so => so) (fun so _ => so).
  Hypothesis WCR : wcrtomb0_stmt.
  Hypothesis FW0 : fwrite0_out_stmt.
  Hypothesis FW0E : fwrite0_err_stmt.
  Hypothesis FFL : fflush_out_stmt ps_so set_so_ps.
  Hypothesis FFLS : fflush_out_stmt (St := stdout_st) (fun so => so) (fun so _ => so).
  Hypothesis FFLE : fflush_err_stmt.
  Hypothesis OPD : opdelete_stmt.

  (* [comment removed for export] *)
  Definition head2_mid (sp gp s4 s5 s6 s7 s8 s9 s10 s11 : word) (lo code : Z)
      : unit -> PState -> machine_state -> Prop :=
    fun _ s1 ms1 =>
      exists (ra t0 t1 t2 s1r a0 a1 a2 a3 a4 a5 a6 a7 s3 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m' : mem)
             (dso x1 x2 x3 xs0 xra : word) (j8 : list byte),
      ms1 = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp (Z_to_bv 64 RTP) t0 t1 t2 (Z_to_bv 64 0x10e5a4) s1r a0 a1 a2 a3 a4 a5 a6 a7
                    (Z_to_bv 64 0x10e5a0) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0xbdc58) fc None m' (seg_rom usegs)
      /\ ios_cells m'
      /\ stk usegs m' lo (bv_unsigned sp + -64)
      /\ rw_cells usegs m' (bv_unsigned sp + -64) [CB 8 j8; C8 x3; C8 x2; C8 x1; C8 (Z_to_bv 64 code); C8 (Z_to_bv 64 0xbdee8)]
      /\ rw_cells usegs m' (bv_unsigned sp + -16) [C8 xs0; C8 xra]
      /\ rw_cells usegs m' 0x10e7eb [C1 (Z_to_bv 8 0)]
      /\ rw_cells usegs m' 0x10e5a0 [C1 (Z_to_bv 8 0); CB 3 (repeat (Z_to_bv 8 0) 3); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 2)]
      /\ rw_cells usegs m' 0x10e5b0 [C8 (Z_to_bv 64 0x10e5b8); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0x80124); C8 (Z_to_bv 64 0xbde30)]
      /\ rw_cells usegs m' 0x10e6c0 [C8 (Z_to_bv 64 0xec5f8); C8 (Z_to_bv 64 0x3bd9c)]
      /\ rw_cells usegs m' 0xec2b4 [C1 (Z_to_bv 8 0)]
      /\ rw_cells usegs m' 0xdab70 [C8 (Z_to_bv 64 0xd4c48); C8 (Z_to_bv 64 0xd4c40)]
      /\ rw_cells usegs m' 0xd4c40 [C8 (Z_to_bv 64 0x3b8e4)]
      /\ rw_cells usegs m' 0xdc2a8 [C1 (Z_to_bv 8 0)]
      /\ rw_cells usegs m' 0xda9c8 [C8 (Z_to_bv 64 0xbdca0); C8 z64]
      /\ rw_cells usegs m' 0xdbb98 [C8 dso]
      /\ rw_cells usegs m' 0x10ed28 [C8 z64] /\ rw_cells usegs m' 0xdc140 [C8 (Z_to_bv 64 RSTDIN)] /\ rw_cells usegs m' RSTDIN stdin_cells
      /\ rw_cells usegs m' 0xdc230 [C8 (Z_to_bv 64 RSTDOUT)] /\ rw_cells usegs m' 0xdc050 [C8 (Z_to_bv 64 RSTDERR)]
      /\ stdout_file m' (ps_so s1) /\ stderr_file m'
      /\ rw_cells usegs m' got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ rw_cells usegs m' ssp_guard [C8 CAN]
      /\ mem_inv usegs m'.

  Lemma exit_head2_spec : forall (s : PState) (Q : Empty_set -> PState -> machine_state -> Prop)
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (code t AB : Z) (td0 td1 td2 td3 dso errv : word)
      (LB : list block) (p : bptr) (V : Z),
    ios_cells m ->
    RHEAP s LB m -> In (p, V, 8) LB ->
    rauxv_ok m AB -> bv_unsigned sp <= AB ->
    rw_cells usegs m 0xee4b4 [C4 errv] ->                                                                     (* [comment removed for export] *)
    rw_cells usegs m 0xec2e8 [C8 (Z_to_bv 64 V); C8 (Z_to_bv 64 (V + 8)); C8 (Z_to_bv 64 (V + 8))] ->        (* [comment removed for export] *)
    stk usegs m lo (bv_unsigned sp) ->
    rw_cells usegs m 0xee490 [C8 td0; C8 td1; C8 td2; C8 td3; C4 (Z_to_bv 64 t)] ->
    rw_cells usegs m 0x10e7c0 [C4 z64] ->
    rw_cells usegs m 0x10e5a0 [C1 (Z_to_bv 8 0); CB 3 (repeat (Z_to_bv 8 0) 3); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 3)] ->   (* [comment removed for export] *)
    rw_cells usegs m 0x10e5b0 [C8 (Z_to_bv 64 0x10e5b8); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0x80124); C8 (Z_to_bv 64 0xbde30)] ->  (* [comment removed for export] *)
    rw_cells usegs m 0x10e5d0 [C8 (Z_to_bv 64 0x3c020)] ->                                                                        (* [comment removed for export] *)
    rw_cells usegs m 0x10e6c0 [C8 (Z_to_bv 64 0xec5f8); C8 (Z_to_bv 64 0x3bd9c)] ->                                                 (* [comment removed for export] *)
    rw_cells usegs m 0x10e6d0 [C8 (Z_to_bv 64 0xec2e8)] ->                                                                        (* [comment removed for export] *)
    rw_cells usegs m 0xec2b4 [C1 (Z_to_bv 8 0)] ->                                                                                (* [comment removed for export] *)
    rw_cells usegs m 0xdab70 [C8 (Z_to_bv 64 0xd4c48); C8 (Z_to_bv 64 0xd4c40)] ->
    rw_cells usegs m 0xd4c40 [C8 (Z_to_bv 64 0x3b8e4)] ->
    rw_cells usegs m 0xdc2a8 [C1 (Z_to_bv 8 0)] ->
    rw_cells usegs m 0xda9c8 [C8 (Z_to_bv 64 0xbdca0); C8 z64] ->
    rw_cells usegs m 0xdbb98 [C8 dso] ->
    rw_cells usegs m 0x10ed28 [C8 z64] -> rw_cells usegs m 0xdc140 [C8 (Z_to_bv 64 RSTDIN)] -> rw_cells usegs m RSTDIN stdin_cells ->
    rw_cells usegs m 0xdc230 [C8 (Z_to_bv 64 RSTDOUT)] -> rw_cells usegs m 0xdc050 [C8 (Z_to_bv 64 RSTDERR)] ->
    stdout_file m (ps_so s) -> stderr_file m ->
    mem_inv usegs m ->
    tp = Z_to_bv 64 RTP -> a0 = Z_to_bv 64 code ->
    0 < t < 4194304 -> lo <= bv_unsigned sp - 32768 -> ATOP <= lo ->
    bv_unsigned sp < 2^47 ->
    implM usegs ((HarnessM.opdelete raw_free p ;;; mupd (set_fa_ps None)) ;;; exit_model ProgP.io code) s Q
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0xbde84) fc None m (seg_rom usegs)).
  Proof.
    intros until V. intros IOS RH INB AUX SPAB ERR VEC ST TID EXL AT0 AT1 AT1b AT2 AT2b INCB GF FA FINZ GCX DSO OFL SIN SINF SOU SEU SOF SEF MI -> -> Ht LO ATL SP47.
    pose proof atop_range as ATOPR.
    assert (GLO : GLOBALS_TOP <= lo) by (unfold GLOBALS_TOP; clear - ATL ATOPR; lia).
    pose proof GLO as GLO'. unfold GLOBALS_TOP in GLO'.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    unfold RSTDIN, stdin_cells in SIN, SINF.
    pose proof (RHEAP_need_locks _ _ _ RH) as LIBC. unfold RNEED_LOCKS, b8 in LIBC.
    pose proof (RMalloc_ifaceP.RHEAP_block_range_proof _ _ _ _ RH INB) as (VB1 & VB2 & _ & VB4 & VB5). cbn [blk_addr blk_size fst snd] in VB1, VB2, VB4, VB5.
    destruct SOF as (flags & mode & tail & bufbytes & FC & FL72 & BUF & BUFP & BUFL & INACT). unfold file_cells in FC.
    destruct SEF as (eflags & emode & ee & ewend & etail & EFC). unfold file_cells in EFC.
    pose proof (munch_refl [(bv_unsigned sp - 8192, bv_unsigned sp); (0x10e5a0, 0x10e7c8); (0xec2e8, 0xec300)]%Z m) as MU.
    pose proof (wmono_refl usegs m) as WM.
    eapply (implM_bind usegs _ _ s (head2_mid sp gp s4 s5 s6 s7 s8 s9 s10 s11 lo code)).
    - eapply (implM_bind usegs _ _ s (fun _ s1 ms1 => head2_mid sp gp s4 s5 s6 s7 s8 s9 s10 s11 lo code tt (set_fa_ps None s1) ms1)).
      + apply implM_from_evt.
        carve_frame 16%nat ST.
        do 6 hstep.
        replace (sx32 (Z_to_bv 64 t)) with (Z_to_bv 64 t)
          by (unfold sx32; f_equal; rewrite unsigned_lit by lia; symmetry; apply swrap32_small; lia).
        hstep. hstep.
        sort_lits. amo_step. replace (sx32 z64) with z64 by (vm_compute; reflexivity).
        nstep. sort_lits. amo_step. nstep.
        hstep. change (bv_swrap 32 (0 + 0)) with 0%Z.
        hstep. if_cases K; zify_cond K; [exfalso; lia|]. clear K. nstep.
        hstep. hstep.
        (* [comment removed for export] *)
        carve_frame 48%nat ST.
        steps_to 0xcf85c%Z.
        hstep. hstep. hstep. change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). if_true. hstep.
        nstep. nstep. hstep.
        replace (sx32 (Z_to_bv 64 3)) with (Z_to_bv 64 3 : word) by (vm_compute; reflexivity).
        (* [comment removed for export] *)
        steps_to 0x3c020%Z.
        (* [comment removed for export] *)
        carve_frame 16%nat ST.
        do 5 hstep.                                              (* [comment removed for export] *)
        nstep.                                                   (* [comment removed for export] *)
        nstep.                                                   (* [comment removed for export] *)
        nstep. nstep.                                            (* [comment removed for export] *)
        assert (EV : bv_unsigned (Z_to_bv 64 V) = V) by (apply unsigned_lit; clear - VB1 VB4 ATOPR; lia).
        assert (EV8 : bv_unsigned (Z_to_bv 64 (V + 8)) = V + 8) by (apply unsigned_lit; clear - VB1 VB4 ATOPR; lia).
        hstep.                                                   (* [comment removed for export] *)
        hstep. if_cases K; zify_cond K. { exfalso. clear - K VB1 EV. lia. } clear K.          (* [comment removed for export] *)
        hstep.                                                   (* [comment removed for export] *)
        hstep. if_cases K; zify_cond K; [exfalso; rewrite ?EV, ?EV8 in K; clear - K VB1; lia|]. clear K.   (* [comment removed for export] *)
        hstep.                                                   (* [comment removed for export] *)
        hstep. if_cases K; zify_cond K; [exfalso; rewrite ?EV8, ?unsigned_lit in K by (clear; lia); clear - K VB1; lia|]. clear K.  (* [comment removed for export] *)
        hstep.                                                   (* [comment removed for export] *)
        hstep. if_cases K; zify_cond K; [exfalso; rewrite ?EV, ?EV8 in K; try rewrite unsigned_lit in K by (clear - VB1 VB4 ATOPR; lia); clear - K VB1 VB4 ATOPR; lia|]. clear K.  (* [comment removed for export] *)
        try (replace (V + 8 + -8) with V by (clear; lia)).
        hstep. hstep.                                            (* [comment removed for export] *)
        hstep.                                                   (* [comment removed for export] *)
        hstep.                                                   (* [comment removed for export] *)
        assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -80)) = bv_unsigned sp + -80) by (apply unsigned_lit; clear - RSP LO GLO'; lia).
        match goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
          assert (RH0 : RHEAP s LB mc)
            by (eapply RMalloc_ifaceP.RHEAP_frame_proof; [exact RH | exact MU | exact WM |];
                apply Forall_cons; [left; cbn [fst snd]; clear - LO ATL; lia |
                apply Forall_cons; [right; left; cbn [fst snd]; unfold RLIBC, RCTX, RSSP_GUARD, RGOT_SSP; clear; lia |
                apply Forall_cons; [right; left; cbn [fst snd]; unfold RLIBC, RCTX, RSSP_GUARD, RGOT_SSP; clear; lia | apply Forall_nil]]]);
          assert (AUX0 : rauxv_ok mc AB)
            by (eapply rauxv_ok_frame; [exact AUX | exact MU | exact WM |];
                apply Forall_cons; [cbn [fst snd]; unfold RAUXV_CELL; clear - LO GLO' SPAB; lia |
                apply Forall_cons; [cbn [fst snd]; unfold RAUXV_CELL; clear - LO GLO' SPAB RSP; lia |
                apply Forall_cons; [cbn [fst snd]; unfold RAUXV_CELL; clear - LO GLO' SPAB RSP; lia | apply Forall_nil]]]);
          assert (IOS0 : ios_cells mc)
            by (eapply ios_cells_munch; [exact IOS | exact MU | exact WM | unfold ios_addr; cbn [outside]; intros a Ha; clear - Ha LO GLO'; lia])
        end.
        apply evt_done.
        eapply implM_post_evt'.
        { destruct OPD as (_ & OPDSZ & _). unfold opdelete_stmt_at, POPDEL_SZ in OPDSZ.
          eapply OPDSZ with (LB := LB) (A := V) (n := 8) (lo := lo) (B := AB) (errv := errv);
            try first [ exact RH0 | exact INB | exact AUX0 | exact ATL | reflexivity
                      | (rewrite ESP; first [ eassumption | unfold RFREE_STACK; clear - LO; lia | clear - SPAB; lia ])
                      | (rewrite errno_lit; unfold RERRNO; hyp_by_addr) | eassumption ]. }
        cbv beta. intros [] s' ms' PO. unfold rfree_post in PO.
        destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MI' & ST' & ERR' & AUX' & HPR & FA' & SO' & RH').
        rewrite ESP in ST', HPR.
        rewrite (ret_pc_even 0x3c034) by (cbn; lia).
        (* [comment removed for export] *)
        lazymatch type of HPR with rheap_pres _ _ ?mc _ =>
          repeat match goal with H : rw_cells usegs mc ?A ?cs |- _ =>
            let H' := fresh "X" in
            first [ assert (H' : rw_cells usegs m' A cs)
                      by (eapply rheap_pres_rw_cells; [exact HPR | exact H |];
                          first [ left; cbn [cells_size csize Nat.add]; clear; lia
                                | apply rclient_range_data; cbn [cells_size csize Nat.add]; clear; lia ]);
                    clear H; rename H' into H
                  | clear H ] end;
          assert (IOS1 : ios_cells m')
            by (eapply (ios_cells_magree (rclient_addr (lb_remove p LB) (bv_unsigned sp + -80))); [exact HPR | | exact IOS0];
                intros a Ha; right; left; unfold ios_addr in Ha; unfold ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP; clear - Ha; lia)
        end.
        pose proof (RHEAP_need_locks _ _ _ RH') as LIBC'. unfold RNEED_LOCKS, b8 in LIBC'.
        pose proof (RHEAP_ssp _ _ _ RH') as (GG' & GU').
        (* [comment removed for export] *)
        hstep. hstep. hstep.
        try (replace (bv_unsigned sp + -80 + 16) with (bv_unsigned sp + -64) by (clear; lia)).
        try (rewrite (ret_pc_even 0xbdc58) by (cbn; lia)).
        lazymatch goal with H : rw_cells usegs m' (bv_unsigned sp + -80) _ |- _ => release_frame H ST' (bv_unsigned sp + -64) end.
        apply evt_done. unfold head2_mid.
        do 18 eexists. exists F, fc, m', dso. do 5 eexists. eexists.
        split; [reflexivity|].
        split; [exact IOS1|].
        split; [eassumption|].
        unfold RSTDIN, stdin_cells, got_ssp, ssp_guard.
        repeat (lazymatch goal with |- rw_cells _ _ _ _ /\ _ => split; [hyp_by_addr|] end).
        split. { cbn [ps_so set_fa_ps]. rewrite SO'.
                 exists flags, mode, tail, bufbytes. unfold file_cells.
                 split; [exact FC|]. split; [exact FL72|]. split; [exact BUF|]. split; [exact BUFP|]. split; [exact BUFL| exact INACT]. }
        split. { exists eflags, emode, ee, ewend, etail. unfold file_cells. exact EFC. }
        split; [exact GG'|]. split; [exact GU'|]. exact MI'.
      + (* [comment removed for export] *)
        intros [] sA msA PO. apply implM_upd. apply evt_done. exact PO.
    - (* [comment removed for export] *)
      intros [] sB msB PO. unfold head2_mid in PO.
      destruct PO as (ra' & t0' & t1' & t2' & s1r & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & s3' & t3' & t4' & t5' & t6' & F' & fc' & m' &
                      dso' & x1' & x2' & x3' & xs0' & xra' & j8' & -> & TM).
      destruct TM as (IOS' & ST' & FRF' & FRE' & LIBC' & AT0' & AT1' & AT2' & INCB' & GF' & FA' & FINZ' & GCX' & DSO' &
                      OFL' & SIN' & SINF' & SOU' & SEU' & SOF' & SEF' & GG' & GU' & MI').
      unfold RSTDIN, stdin_cells, got_ssp, ssp_guard in *.
      destruct SOF' as (flags' & mode' & tail' & bufbytes' & FC' & FL72' & BUF' & BUFP' & BUFL' & INACT'). unfold file_cells in FC'.
      destruct SEF' as (eflags' & emode' & ee' & ewend' & etail' & EFC'). unfold file_cells in EFC'.
      pose proof (munch_refl [(bv_unsigned sp - 8192, bv_unsigned sp); (0x10e5a0, 0x10e7c8)]%Z m') as MU'.
      pose proof (wmono_refl usegs m') as WM'.
      change ProgP.io with (io_S ps_so set_so_ps).
      apply implM_from_evt.
      steps_to 0xcf85c%Z.
      hstep. hstep. hstep. change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). if_true. hstep.
      hstep.
      replace (sx32 (Z_to_bv 64 2)) with (Z_to_bv 64 2 : word) by (vm_compute; reflexivity).
      (* [comment removed for export] *)
      steps_to 0x3bd9c%Z.
      hstep. hstep. hstep. change (zxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). if_false. hstep.
      (* [comment removed for export] *)
      steps_to 0xcf85c%Z.
      hstep. hstep. hstep. change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). if_true. hstep.
      hstep.
      replace (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1 : word) by (vm_compute; reflexivity).
      steps_to 0xbdc34%Z.
      apply evt_done.
      eapply (exit_tail_spec ps_so set_so_ps SE WCR FW0 FW0E FFL FFLS FFLE sB Q) with (lo := lo) (so_x := ps_so sB) (guard := CAN);
        try first [ reflexivity | exact GLO | exact SP47
                  | (intros _; reflexivity)
                  | (unfold EXIT_TAIL_DEPTH; clear - LO; lia)
                  | (eapply ios_cells_munch; [exact IOS' | exact MU' | exact WM' | unfold ios_addr; cbn [outside]; intros a Ha; clear - Ha LO GLO'; lia])
                  | (exists flags', mode', tail', bufbytes'; split; [unfold file_cells; exact FC'|]; split; [exact FL72'|]; split; [exact BUF'|]; split; [exact BUFP'|]; split; [exact BUFL'| exact INACT'])
                  | (exists eflags', emode', ee', ewend', etail'; unfold file_cells; exact EFC')
                  | (unfold got_ssp, ssp_guard, RSTDIN, stdin_cells; hyp_by_addr) ].
  Qed.
End Head2.
End CANSEC1.
