(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Lib Require Import Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Spec Require Import Prelim Monad Stdio Driver.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import Startup_kit.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.BothW Require Import F_syscalls StdioFiles Stdio_kit BImg MonadF AExit AIos_tac AIos_iface AIos_dtor AIos_frame AExitU_fini.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.LibA Require Import Shadow ITreeA StepF.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import F_fmt_fp_lib RunDraw.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.
Section Tail.
  Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
  Variables MDPRE ICPT : mem -> Prop.
  Variable ICPTR : footprint -> Prop.
  Variables SLO SHI : Z.
  Hypothesis MDTOR : module_dtor_stmt MDPRE.
  Hypothesis MDPRE_frame : forall W m m', MDPRE m -> munch W m m' -> wmono bsegs m m' -> Forall exit_wr_ok W -> MDPRE m'.
  Hypothesis ICPT_frame : forall W m m', ICPT m -> munch W m m' -> wmono bsegs m m' -> Forall exit_wr_ok W -> ICPT m'.
  Hypothesis SE : stdio_exit_spec_stmt2 (St := stdout_st) (fun so => so) (fun so _ => so).
  Hypothesis WCR : wcrtomb0_stmt ICPT ICPTR SLO SHI.
  Hypothesis FW0 : fwrite0_out_stmt ICPT ICPTR.
  Hypothesis FW0E : fwrite0_err_stmt ICPT ICPTR.
  Hypothesis FFL : fflush_out_stmt ICPT ICPTR get_so set_so.
  Hypothesis FFLS : fflush_out_stmt ICPT ICPTR (St := stdout_st) (fun so => so) (fun so _ => so).
  Hypothesis FFLE : fflush_err_stmt ICPT ICPTR.

  Lemma ICPT_frame3 : forall W m m', ICPT m -> munch W m m' -> wmono bsegs m m' ->
    Forall (fun iv => ATOP <= fst iv \/ (RSTDERR <= fst iv /\ snd iv <= RSTDOUT + 232) \/ (0x6afad8 <= fst iv /\ snd iv <= 0x6afae0)) W -> ICPT m'.
  Proof.
    intros W m1 m2 H1 H2 H3 H4. eapply ICPT_frame; [exact H1 | exact H2 | exact H3 |].
    eapply Forall_impl; [| exact H4]. cbv beta. unfold exit_wr_ok. intros iv [H|[H|H]]; [left | right; left | right; right; left]; exact H.
  Qed.

  (* [comment removed for export] *)
  Definition tail_mid (sp gp s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (lo code : Z) (s : St)
      : unit -> St -> machine_state -> Prop :=
    fun _ st' ms' => exists (so' : stdout_st) (ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 t3 t4 t5 t6 : word) (m' : mem)
                            (cdt thr sec : byte) (tm1 dso guard x1 x2 x3 xs0 xra f1 f2 a1' a2' : word) (j8 : list byte),
      st' = set_so so' s /\ so_buf so' = []
      /\ ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp (Z_to_bv 64 RTP) t0 t1 t2 (Z_to_bv 64 0x6cfb5c) s1 a0 a1 a2 a3 a4 a5 a6 a7
                       (Z_to_bv 64 0x6cfb58) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x152b38) fc None m' (seg_rom bsegs)
      /\ MDPRE m'
      /\ stk bsegs m' lo (bv_unsigned sp + -64)
      /\ rw_cells bsegs m' (bv_unsigned sp + -64) [CB 8 j8; C8 x3; C8 x2; C8 x1; C8 (Z_to_bv 64 code); C8 (Z_to_bv 64 0x152dc8)]
      /\ rw_cells bsegs m' (bv_unsigned sp + -16) [C8 xs0; C8 xra]
      /\ rw_cells bsegs m' 0x6cfd98 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1]
      /\ rw_cells bsegs m' 0x6cfb58 [C1 (Z_to_bv 8 0)]
      /\ rw_cells bsegs m' 0x6cfb5c [C4 z64]
      /\ rw_cells bsegs m' 0x6cfb60 [C4 (Z_to_bv 64 1)]
      /\ rw_cells bsegs m' 0x6cfb68 [C8 (Z_to_bv 64 0x6cfb70)]
      /\ rw_cells bsegs m' 0x6cfb70 [C8 z64]
      /\ rw_cells bsegs m' 0x6cfb78 [C8 (Z_to_bv 64 0x152d10); C8 f1; C8 f2]
      /\ rw_cells bsegs m' 0x6cfc78 [C8 (Z_to_bv 64 0x9f2c4); C8 a1'; C8 a2']
      /\ rw_cells bsegs m' 0x20cf20 [C1 (Z_to_bv 8 0)]
      /\ rw_cells bsegs m' 0x172e08 [C8 (Z_to_bv 64 0x16bf28); C8 (Z_to_bv 64 0x16bf18)]
      /\ rw_cells bsegs m' 0x16bf18 [C8 (Z_to_bv 64 0xb38c8); C8 (Z_to_bv 64 0x59000)]
      /\ rw_cells bsegs m' 0x177a10 [C1 (Z_to_bv 8 0)]
      /\ rw_cells bsegs m' 0x171fc8 [C8 (Z_to_bv 64 0x152b80); C8 z64]
      /\ rw_cells bsegs m' 0x173e60 [C8 dso]
      /\ rw_cells bsegs m' 0x6d0310 [C8 z64] /\ rw_cells bsegs m' 0x176de8 [C8 (Z_to_bv 64 RSTDIN)] /\ rw_cells bsegs m' RSTDIN stdin_cells
      /\ rw_cells bsegs m' 0x176ed8 [C8 (Z_to_bv 64 RSTDOUT)] /\ rw_cells bsegs m' 0x176cf8 [C8 (Z_to_bv 64 RSTDERR)]
      /\ stdout_file m' (so_inact so') /\ stderr_file m'
      /\ rw_cells bsegs m' got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ rw_cells bsegs m' ssp_guard [C8 guard]
      /\ mem_inv bsegs m'.

  (* [comment removed for export] *)
  Definition EXIT_TAIL_DEPTH : Z := 8192.

  Lemma exit_tail3_spec : forall RNG (s : St) (Q : Empty_set -> St -> machine_state -> Prop)
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (code t : Z) (cdt thr sec : byte) (tm1 dso guard x1 x2 x3 xs0 xra : word) (j8 : list byte)
      (so_x : stdout_st),
    MDPRE m -> ICPT m -> ios_cells m ->
    stk bsegs m lo (bv_unsigned sp + -64) ->
    rw_cells bsegs m (bv_unsigned sp + -64) [CB 8 j8; C8 x3; C8 x2; C8 x1; C8 (Z_to_bv 64 code); C8 (Z_to_bv 64 0x152dc8)] ->
    rw_cells bsegs m (bv_unsigned sp + -16) [C8 xs0; C8 xra] ->
    rw_cells bsegs m 0x6cfd98 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->       (* [comment removed for export] *)
    rw_cells bsegs m 0x6cfb58 [C1 (Z_to_bv 8 0)] ->                                   (* [comment removed for export] *)
    rw_cells bsegs m 0x6cfb5c [C4 z64] ->                                             (* [comment removed for export] *)
    rw_cells bsegs m 0x6cfb60 [C4 (Z_to_bv 64 2)] ->                                  (* [comment removed for export] *)
    rw_cells bsegs m 0x6cfb68 [C8 (Z_to_bv 64 0x6cfb70)] ->                           (* [comment removed for export] *)
    rw_cells bsegs m 0x6cfb70 [C8 z64] ->                                             (* [comment removed for export] *)
    rw_cells bsegs m 0x6cfb78 [C8 (Z_to_bv 64 0x152d10); C8 (Z_to_bv 64 0x114748); C8 (Z_to_bv 64 0x757fc)] ->
    rw_cells bsegs m 0x6cfc78 [C8 (Z_to_bv 64 0x9f2c4); C8 (Z_to_bv 64 0x6adba8); C8 z64] ->
    rw_cells bsegs m 0x171ff0 [C8 (Z_to_bv 64 0x178878)] ->                           (* [comment removed for export] *)
    rw_cells bsegs m 0x178894 [C1 (Z_to_bv 8 0)] ->                                   (* [comment removed for export] *)
    rw_cells bsegs m 0x20cf20 [C1 (Z_to_bv 8 0)] ->                                   (* [comment removed for export] *)
    rw_cells bsegs m 0x172e08 [C8 (Z_to_bv 64 0x16bf28); C8 (Z_to_bv 64 0x16bf18)] -> (* [comment removed for export] *)
    rw_cells bsegs m 0x16bf18 [C8 (Z_to_bv 64 0xb38c8); C8 (Z_to_bv 64 0x59000)] ->  (* [comment removed for export] *)
    rw_cells bsegs m 0x177a10 [C1 (Z_to_bv 8 0)] ->                                   (* [comment removed for export] *)
    rw_cells bsegs m 0x171fc8 [C8 (Z_to_bv 64 0x152b80); C8 z64] ->                   (* [comment removed for export] *)
    rw_cells bsegs m 0x173e60 [C8 dso] ->                                             (* [comment removed for export] *)
    rw_cells bsegs m 0x6d0310 [C8 z64] -> rw_cells bsegs m 0x176de8 [C8 (Z_to_bv 64 RSTDIN)] -> rw_cells bsegs m RSTDIN stdin_cells ->
    rw_cells bsegs m 0x176ed8 [C8 (Z_to_bv 64 RSTDOUT)] -> rw_cells bsegs m 0x176cf8 [C8 (Z_to_bv 64 RSTDERR)] ->
    stdout_file m so_x -> so_buf so_x = so_buf (get_so s) -> (so_buf (get_so s) <> [] -> so_x = get_so s) -> so_first so_x = so_first (get_so s) -> so_lbf_nl so_x = so_lbf_nl (get_so s) ->
    stderr_file m ->
    rw_cells bsegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] -> rw_cells bsegs m ssp_guard [C8 guard] ->
    mem_inv bsegs m ->
    tp = Z_to_bv 64 RTP -> s0 = Z_to_bv 64 0x6cfb5c -> s2 = Z_to_bv 64 0x6cfb58 -> a2 = Z_to_bv 64 2 ->
    lo <= bv_unsigned sp - EXIT_TAIL_DEPTH -> GLOBALS_TOP <= lo -> ATOP <= lo -> SLO <= lo -> bv_unsigned sp <= SHI -> KHIGH <= lo -> bv_unsigned sp mod 16 = 0 ->
    rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG -> ICPTR RNG -> Forall (fun iv => rng RNG (fst iv) (snd iv - fst iv)) MDTOR_W -> rng0 RNG ->
    bv_unsigned sp < 2^47 ->
    implAM RNG (Driver.exit_model (io_S get_so set_so) code) s Q
         (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x152b14) fc None m (seg_rom bsegs)).
  Proof.
    intros until so_x. intros HMD IC IOS ST FRF FRE LIBC FIN ALK SLOT HEAD NEXT FF AA GFL FLG COV GF FA FINZ GCX DSO OFL SIN SINF SOU SEU SOF EB EQ SF SL SEF GG GU MI -> -> -> -> LO GLO ATL SLOK SHIK KH AL RSTK RIMG RI RW RG0 SP47.
    pose proof GLO as GLO'. unfold GLOBALS_TOP in GLO'. pose proof KH as KH'. unfold KHIGH in KH'. unfold EXIT_TAIL_DEPTH in LO.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    unfold got_ssp, ssp_guard in GG, GU. unfold RSTDIN, stdin_cells in SIN, SINF.
    unfold Driver.exit_model.
    change (io_exit (io_S get_so set_so)) with (stdout_exit_flush get_so set_so).
    destruct SOF as (flags & mode & tail & bufbytes & FC & FL72 & BUF & BUFP & BUFL & INACT). unfold file_cells in FC.
    destruct SEF as (eflags & emode & ee & ewend & etail & EFC). unfold file_cells in EFC.
    pose proof (munch_refl [(bv_unsigned sp - 8192, bv_unsigned sp); (RSTDERR, RSTDERR + 232); (RSTDOUT, RSTDOUT + 232); (0x6afad8, 0x6afae0); (0x6cfb58, 0x6cfd80); (0x177a10, 0x177a11)]%Z m) as MU.
    pose proof (munch_refl [(bv_unsigned sp - 8192, bv_unsigned sp); (0x6cfb58, 0x6cfd80)]%Z m) as MUa.
    pose proof (wmono_refl bsegs m) as WM.
    eapply (implAM_bind RNG _ _ s (tail_mid sp gp s4 s5 s6 s7 s8 s9 s10 s11 F fc lo code s)).
    - apply implAM_from_evt.
      (* [comment removed for export] *)
      steps_to 0x67740%Z.
      carve_frame 96%nat ST.
      steps_to 0x6777c%Z. change (zxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). nstep.
      steps_to 0x152b38%Z.
      match goal with H : rw_cells _ _ (bv_unsigned sp + -160)%Z _ |- _ => release_frame H ST (bv_unsigned sp + -64)%Z end.
      (* [comment removed for export] *)
      steps_to 0x16504c%Z.
      hstep. hstep. hstep. change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). if_true. hstep.
      steps_to 0x114748%Z.
      assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; clear - RSP LO GLO'; lia).
      assert (WOK : Forall exit_wr_ok [(bv_unsigned sp - 8192, bv_unsigned sp); (RSTDERR, RSTDERR + 232); (RSTDOUT, RSTDOUT + 232); (0x6afad8, 0x6afae0); (0x6cfb58, 0x6cfd80); (0x177a10, 0x177a11)]%Z)
        by (unfold exit_wr_ok; apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_cons; [right; left; cbn [fst snd]; lia | apply Forall_cons; [right; left; cbn [fst snd]; lia | apply Forall_cons; [right; right; left; cbn [fst snd]; lia | apply Forall_cons; [right; right; right; left; cbn [fst snd]; lia | apply Forall_cons; [right; right; right; right; cbn [fst snd]; lia | apply Forall_nil]]]]]]).
      apply evtF_done.
      eapply implAM_post_evt'.
      { eapply (ios_dtor_spec ICPT ICPTR SLO SHI get_so set_so WCR FW0 FW0E FFL FFLS FFLE ICPT_frame3 RNG) with (lo := lo) (guard := guard) (so_x := so_x);
          [ rewrite ESP; exact ST
          | exists flags, mode, tail, bufbytes; split; [unfold file_cells; exact FC|]; split; [exact FL72|]; split; [exact BUF|]; split; [exact BUFP|]; split; [exact BUFL| exact INACT]
          | exists eflags, emode, ee, ewend, etail; unfold file_cells; exact EFC
          | exact EB | exact EQ | exact SF | exact SL
          | unfold ssp_cells, got_ssp, ssp_guard; split; [exact GG| exact GU]
          | eapply ICPT_frame; [exact IC | exact MU | exact WM | exact WOK]
          | eapply ios_cells_frame; [exact IOS | exact MUa | exact WM | unfold ios_wr_ok; apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_nil]]]
          | exact MI | reflexivity
          | rewrite ESP; clear - LO; lia | exact GLO | exact ATL | exact SLOK | rewrite ESP; clear - SHIK; lia | rewrite ESP; clear - AL; Z.div_mod_to_equations; lia
          | rewrite ESP; eapply rng_sub'; [exact RSTK | clear - LO RSP; lia] | exact RIMG | exact RI | exact RG0 | rewrite ESP; clear - SP47; lia ].
 }
      cbv beta. intros [] st2 ms2 (so' & -> & EB' & PO2).
      destruct PO2 as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & -> & MU2 & WM2 & MI2 & ST2 & SSP2 & IC2 & SOF2 & SEF2 & CURL2).
      rewrite ESP in MU2, ST2. clear MUa.
      rewrite (ret_pc_even 1387320) by (cbn; lia).
      match goal with WMx : wmono bsegs m ?mc |- _ => transport_after_call bsegs mc m2 MU2 WM2 end.
      apply evtF_done. unfold tail_mid.
      exists so'. do 18 eexists. exists m2. exists cdt, thr, sec, tm1, dso, guard. do 9 eexists. eexists.
      split; [reflexivity|]. split; [exact EB'|]. split; [reflexivity|].
      split; [eapply MDPRE_frame; [exact HMD | exact MU | exact WM | exact WOK]|].
      split; [exact ST2|].
      unfold RSTDIN, stdin_cells, got_ssp, ssp_guard.
      repeat (lazymatch goal with |- rw_cells _ _ _ _ /\ _ => split; [hyp_by_addr|] end).
      split; [exact SOF2|]. split; [exact SEF2|].
      repeat (lazymatch goal with |- rw_cells _ _ _ _ /\ _ => split; [hyp_by_addr|] end).
      exact MI2.
    - intros [] st' ms' TM. unfold tail_mid in TM.
      destruct TM as (so' & ra' & t0' & t1' & t2' & s1' & a0' & a1'' & a2'' & a3' & a4' & a5' & a6' & a7' & s3' & t3' & t4' & t5' & t6' & m' &
                      cdt' & thr' & sec' & tm1' & dso' & guard' & x1' & x2' & x3' & xs0' & xra' & f1 & f2 & b1 & b2 & j8' &
                      -> & EB' & -> & TM).
      destruct TM as (HMD' & ST' & FRF' & FRE' & LIBC' & FIN' & ALK' & SLOT' & HEAD' & NEXT' & FF' & AA' & COV' & GF' & FA' & FINZ' & GCX' & DSO' &
                      OFL' & SIN' & SINF' & SOU' & SEU' & SOF' & SEF' & GG' & GU' & MI').
      eapply (exit_fini_spec MDPRE MDTOR MDPRE_frame SE RNG) with (so_i := so_inact so') (lo := lo);
        try first [ eassumption | reflexivity | exact LO | exact GLO | exact ATL | exact KH | exact AL | exact RSTK | exact RIMG | exact RW | exact RG0 | exact SP47 ].
  Qed.
End Tail.
End CANSEC1.
