(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import Tac Image ZBridge ITree Nodes Decode SysStep Arr FP.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import Prelim Monad Stdio Driver AsanCtrl AsanEmbed HarnessM ProgA AsanProgDeps.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import Startup_kit.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require DrvAgree.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AsanW Require Import AImg RtCells AProto ABase AMalloc_iface AU_kit AU_iface AHarnessU_iface AU_fuzz_kit.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AsanW Require Import F_syscalls StdioFiles Stdio_kit MonadF AExit AAtexit_iface.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AsanW Require Import AIos_tac AIos_iface AIos_dtor AIos_frame AExitU_fini AExitU_tail AExitU_join4 AExitU_kit.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import Shadow ExecF ITreeA StepF.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import F_fmt_fp_lib RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.
Section Head6.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Variables MDPRE ICPT : mem -> Prop.
  Variable ICPTR : footprint -> Prop.
  Variables SLO SHI : Z.
  Hypothesis MDTOR : module_dtor_stmt MDPRE.
  Hypothesis MDPRE_frame : forall W m m', MDPRE m -> munch W m m' -> wmono asegs m m' -> Forall exit_wr_ok W -> MDPRE m'.
  Hypothesis ICPT_frame : forall W m m', ICPT m -> munch W m m' -> wmono asegs m m' -> Forall exit_wr_ok W -> ICPT m'.
  Hypothesis SE : stdio_exit_spec_stmt2 (St := stdout_st) (fun so => so) (fun so _ => so).
  Hypothesis WCR : wcrtomb0_stmt ICPT ICPTR SLO SHI.
  Hypothesis FW0 : fwrite0_out_stmt ICPT ICPTR.
  Hypothesis FW0E : fwrite0_err_stmt ICPT ICPTR.
  Hypothesis FFL : fflush_out_stmt ICPT ICPTR aps_so aset_so.
  Hypothesis FFLS : fflush_out_stmt ICPT ICPTR (St := stdout_st) (fun so => so) (fun so _ => so).
  Hypothesis FFLE : fflush_err_stmt ICPT ICPTR.
  Hypothesis AVD : avdtor_stmt AI.

  Hypothesis EXIT_CI : forall iv, In iv exit_ci_need -> In iv CI.
  Hypothesis INCB_CI : In (0x6a2a10, 0x6a2c58) CI.      (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis MDPRE_pres : forall L RNG st LB LB' SP m m', vdtor_pres CI LB SP m m' -> AHEAP AI L RNG st LB' m' -> mem_inv asegs m' -> MDPRE m -> MDPRE m'.
  Hypothesis ICPT_pres : forall L RNG st LB LB' RNG0 st0 LB0 SP m m', vdtor_pres CI LB SP m m' -> AHEAP AI L RNG st LB' m' -> mem_inv asegs m' -> ICPT m ->
    AHEAP AI L RNG0 st0 LB0 m (* [comment removed for export] *) -> ICPT m'.
  Hypothesis ICPTR_mono : forall RNG RNG', fp_le RNG RNG' -> ICPTR RNG -> ICPTR RNG'.

  (* [comment removed for export] *)
  Definition head6_mid (RNG : footprint) (sp gp s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (lo code : Z)
      : unit -> APS -> footprint -> machine_state -> Prop :=
    fun _ s1 RNG1 ms1 => fp_le RNG RNG1 /\
      exists (ra t0 t1 t2 s1r a0 a1 a2 a3 a4 a5 a6 a7 s3 t3 t4 t5 t6 : word) (m' : mem)
             (cdt thr sec : byte) (tm1 dso guard x1 x2 x3 xs0 xra : word) (j8 : list byte),
      ms1 = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp (Z_to_bv 64 RTP) t0 t1 t2 (Z_to_bv 64 0x6c4e3c) s1r a0 a1 a2 a3 a4 a5 a6 a7
                    (Z_to_bv 64 0x6c4e38) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x1478b0) fc None m' (seg_rom asegs)
      /\ MDPRE m' /\ ICPT m' /\ ios_cells m'
      /\ stk asegs m' lo (bv_unsigned sp + -64)
      /\ rw_cells asegs m' (bv_unsigned sp + -64) [CB 8 j8; C8 x3; C8 x2; C8 x1; C8 (Z_to_bv 64 code); C8 (Z_to_bv 64 0x147b40)]
      /\ rw_cells asegs m' (bv_unsigned sp + -16) [C8 xs0; C8 xra]
      /\ rw_cells asegs m' 0x6c5078 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1]
      /\ rw_cells asegs m' 0x6c4e38 [C1 (Z_to_bv 8 0)]
      /\ rw_cells asegs m' 0x6c4e3c [C4 z64]
      /\ rw_cells asegs m' 0x6c4e40 [C4 (Z_to_bv 64 4)]
      /\ rw_cells asegs m' 0x6c4e48 [C8 (Z_to_bv 64 0x6c4e50)]
      /\ rw_cells asegs m' 0x6c4e50 [C8 z64]
      /\ rw_cells asegs m' 0x6c4e58 [C8 (Z_to_bv 64 0x147a88); C8 (Z_to_bv 64 0x109580); C8 (Z_to_bv 64 0x76950)]
      /\ rw_cells asegs m' 0x6c4f58 [C8 (Z_to_bv 64 0xa0418); C8 (Z_to_bv 64 0x6a2e88); C8 z64]
      /\ rw_cells asegs m' 0x6c4e70 [C8 (Z_to_bv 64 0x147a88)]
      /\ rw_cells asegs m' 0x6c4f70 [C8 (Z_to_bv 64 0xb0de0)]
      /\ rw_cells asegs m' 0x6a2a14 [C1 (Z_to_bv 8 0)]
      /\ rw_cells asegs m' 0x167010 [C8 (Z_to_bv 64 0x16dbb8)]
      /\ rw_cells asegs m' 0x16dbd4 [C1 (Z_to_bv 8 0)]
      /\ rw_cells asegs m' 0x202260 [C1 (Z_to_bv 8 0)]
      /\ rw_cells asegs m' 0x167e20 [C8 (Z_to_bv 64 0x160ca0); C8 (Z_to_bv 64 0x160c90)]
      /\ rw_cells asegs m' 0x160c90 [C8 (Z_to_bv 64 0xb45a8); C8 (Z_to_bv 64 0x5a2b8)]
      /\ rw_cells asegs m' 0x16cd50 [C1 (Z_to_bv 8 0)]
      /\ rw_cells asegs m' 0x166fe8 [C8 (Z_to_bv 64 0x1478f8); C8 z64]
      /\ rw_cells asegs m' 0x168e60 [C8 dso]
      /\ rw_cells asegs m' 0x6c55f0 [C8 z64] /\ rw_cells asegs m' 0x16ba18 [C8 (Z_to_bv 64 RSTDIN)] /\ rw_cells asegs m' RSTDIN stdin_cells
      /\ rw_cells asegs m' 0x16bb08 [C8 (Z_to_bv 64 RSTDOUT)] /\ rw_cells asegs m' 0x16b928 [C8 (Z_to_bv 64 RSTDERR)]
      /\ stdout_file m' (aps_so s1) /\ stderr_file m'
      /\ rw_cells asegs m' got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ rw_cells asegs m' ssp_guard [C8 guard]
      /\ mem_inv asegs m'.

  Lemma exit_head6_spec : forall RNG (s : APS) (Q : Empty_set -> APS -> footprint -> machine_state -> Prop)
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (code t : Z) (cdt thr sec : byte) (tm1 dso guard : word)
      (L : alayout) (LB : list ablock) (p : AsanCtrl.aptr) (V : Z) (rstk : region),
    MDPRE m -> ICPT m -> ios_cells m ->
    AHEAP AI L RNG (aps_m s) LB m -> In (HB p V 8) LB -> (forall b, In b LB -> exists q A n, b = HB q A n) ->
    harness_invA m ->
    rw_cells asegs m AVEC [C8 (Z_to_bv 64 V); C8 (Z_to_bv 64 (V + 8)); C8 (Z_to_bv 64 (V + 8))] ->
    rw_cells asegs m V [C8 (Z_to_bv 64 AFALLBACK)] ->
    stk asegs m lo (bv_unsigned sp) ->
    rw_cells asegs m 0x6a4d40 [C4 (Z_to_bv 64 t)] ->
    rw_cells asegs m 0x6c5058 [C4 z64] ->
    rw_cells asegs m 0x6c5078 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
    rw_cells asegs m 0x6c4e38 [C1 (Z_to_bv 8 0)] ->
    rw_cells asegs m 0x6c4e3c [C4 z64] ->
    rw_cells asegs m 0x6c4e40 [C4 (Z_to_bv 64 6)] ->                                  (* [comment removed for export] *)
    rw_cells asegs m 0x6c4e48 [C8 (Z_to_bv 64 0x6c4e50)] ->
    rw_cells asegs m 0x6c4e50 [C8 z64] ->
    rw_cells asegs m 0x6c4e58 [C8 (Z_to_bv 64 0x147a88); C8 (Z_to_bv 64 0x109580); C8 (Z_to_bv 64 0x76950)] ->    (* [comment removed for export] *)
    rw_cells asegs m 0x6c4e70 [C8 (Z_to_bv 64 0x147a88)] ->                                                       (* [comment removed for export] *)
    rw_cells asegs m 0x6c4e78 [C8 (Z_to_bv 64 0xb1194); C8 (Z_to_bv 64 0x76950)] ->                                 (* [comment removed for export] *)
    rw_cells asegs m 0x6c4f58 [C8 (Z_to_bv 64 0xa0418); C8 (Z_to_bv 64 0x6a2e88); C8 z64] ->                        (* [comment removed for export] *)
    rw_cells asegs m 0x6c4f70 [C8 (Z_to_bv 64 0xb0de0)] ->                                                        (* [comment removed for export] *)
    rw_cells asegs m 0x6c4f78 [C8 (Z_to_bv 64 0x6a2a40); C8 z64] ->                                               (* [comment removed for export] *)
    rw_cells asegs m 0x6a2a14 [C1 (Z_to_bv 8 0)] ->                                                               (* [comment removed for export] *)
    rw_cells asegs m 0x167010 [C8 (Z_to_bv 64 0x16dbb8)] ->
    rw_cells asegs m 0x16dbd4 [C1 (Z_to_bv 8 0)] ->
    rw_cells asegs m 0x202260 [C1 (Z_to_bv 8 0)] ->
    rw_cells asegs m 0x167e20 [C8 (Z_to_bv 64 0x160ca0); C8 (Z_to_bv 64 0x160c90)] ->
    rw_cells asegs m 0x160c90 [C8 (Z_to_bv 64 0xb45a8); C8 (Z_to_bv 64 0x5a2b8)] ->
    rw_cells asegs m 0x16cd50 [C1 (Z_to_bv 8 0)] ->
    rw_cells asegs m 0x166fe8 [C8 (Z_to_bv 64 0x1478f8); C8 z64] ->
    rw_cells asegs m 0x168e60 [C8 dso] ->
    rw_cells asegs m 0x6c55f0 [C8 z64] -> rw_cells asegs m 0x16ba18 [C8 (Z_to_bv 64 RSTDIN)] -> rw_cells asegs m RSTDIN stdin_cells ->
    rw_cells asegs m 0x16bb08 [C8 (Z_to_bv 64 RSTDOUT)] -> rw_cells asegs m 0x16b928 [C8 (Z_to_bv 64 RSTDERR)] ->
    stdout_file m (aps_so s) -> stderr_file m ->
    rw_cells asegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] -> rw_cells asegs m ssp_guard [C8 guard] ->
    mem_inv asegs m -> frm0 fc ->
    tp = Z_to_bv 64 RTP -> a0 = Z_to_bv 64 code ->
    0 < t < 4194304 -> lo <= bv_unsigned sp - 32768 -> GLOBALS_TOP <= lo -> ATOP + 4096 <= lo -> SLO <= lo -> bv_unsigned sp <= SHI -> KHIGH <= lo -> bv_unsigned sp mod 16 = 0 ->
    In [AFREE_PC] (al_U L) ->
    rclean m rstk -> r_lo rstk <= lo -> bv_unsigned sp - 64 <= r_hi rstk -> ATOP <= r_rlo rstk ->
    HUX L -> rng RNG lo (al_top L - lo) -> rng_aimg RNG -> ICPTR RNG -> rng_aimg_sh RNG -> rrng RNG rstk -> aps_ok L s ->
    rng RNG lo (bv_unsigned sp - lo) -> Forall (fun iv => rng RNG (fst iv) (snd iv - fst iv)) MDTOR_W -> rng0 RNG ->
    bv_unsigned sp < 2^47 ->
    implMA RNG ((HarnessM.opdelete afree_M p ;;; mupd (aset_cl None)) ;;; exit_model (ioA AAllocAsan) code) s Q
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x147adc) fc None m (seg_rom asegs)).
  Proof.
    intros until rstk. intros HMD IC IOS AH INB HBO HINV VEC VCELL ST TID EXL LIBC FIN ALK SLOT HEAD NEXT FF F3 F45 AA A3 A45 INCB GFL FLG COV GF FA FINZ GCX DSO OFL SIN SINF SOU SEU SOF SEF GG GU MI FRM -> -> Ht LO GLO ATL SLOK SHIK KH AL SPTOP RCL RLO RHI RRLO HUXL RTOP RIMG RI RSH RRNG APOK RSTK RW RG0 SP47.
    pose proof GLO as GLO'. unfold GLOBALS_TOP in GLO'. pose proof KH as KH'. unfold KHIGH in KH'.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    unfold AVEC in VEC. unfold got_ssp, ssp_guard in GG, GU. unfold RSTDIN, stdin_cells in SIN, SINF.
    destruct SOF as (flags & mode & tail & bufbytes & FC & FL72 & BUF & BUFP & BUFL & INACT). unfold file_cells in FC.
    destruct SEF as (eflags & emode & ee & ewend & etail & EFC). unfold file_cells in EFC.
    pose proof (AI_block_bounds AI _ _ _ _ _ _ AH INB) as VB. cbn [ab_addr ab_size] in VB. unfold AIMG_HI in VB.
    assert (ATOPK : ATOP <= 2^47) by (pose proof (AI_layout AI _ _ _ _ _ AH) as LY; atop_facts; lia).
    assert (ATL' : ATOP <= lo) by (clear - ATL; lia).
    pose proof (munch_refl [(bv_unsigned sp - 8192, bv_unsigned sp); (0x6c4e40, 0x6c4e44); (0x6c5058, 0x6c505c)]%Z m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    eapply (implMA_bind RNG _ _ s (head6_mid RNG sp gp s4 s5 s6 s7 s8 s9 s10 s11 F fc lo code)).
    - eapply (implMA_bind RNG _ _ s (fun _ s1 RNG1 ms1 => head6_mid RNG sp gp s4 s5 s6 s7 s8 s9 s10 s11 F fc lo code tt (aset_cl None s1) RNG1 ms1)).
      + apply implMA_from_evtF.
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
        steps_to 0x159dc4%Z.
        hstep. hstep. hstep. change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). if_true. hstep.
        nstep. nstep. hstep.
        replace (sx32 (Z_to_bv 64 6)) with (Z_to_bv 64 6 : word) by (vm_compute; reflexivity).
        steps_to 0x68894%Z.
        (* [comment removed for export] *)
        carve_frame 96%nat ST.
        steps_to 0x688d0%Z. change (zxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). nstep.
        steps_to 0x1478b0%Z.
        match goal with H : rw_cells _ _ (bv_unsigned sp + -160)%Z _ |- _ => release_frame H ST (bv_unsigned sp + -64)%Z end.
        (* [comment removed for export] *)
        steps_to 0x159dc4%Z.
        hstep. hstep. hstep. change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). if_true. hstep.
        steps_to 0xb1194%Z.
        assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; clear - RSP LO GLO'; lia).
        assert (WOK : Forall exit_wr_ok [(bv_unsigned sp - 8192, bv_unsigned sp); (0x6c4e40, 0x6c4e44); (0x6c5058, 0x6c505c)]%Z)
          by (unfold exit_wr_ok; apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_cons; [right; right; right; left; cbn [fst snd]; lia |
              apply Forall_cons; [right; right; right; left; cbn [fst snd]; lia | apply Forall_nil]]]).
        assert (WIOS : Forall ios_wr_ok [(bv_unsigned sp - 8192, bv_unsigned sp); (0x6c4e40, 0x6c4e44); (0x6c5058, 0x6c505c)]%Z)
          by (unfold ios_wr_ok; apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_cons; [left; cbn [fst snd]; lia |
              apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_nil]]]).
        match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) =>
          assert (AH0 : AHEAP AI L RNG (aps_m s) LB mc)
            by (eapply (AI_frame AI); [exact AH | exact MU | exact WM |];
                apply Forall_cons; [left; left; cbn [fst snd]; lia |
                apply Forall_cons; [left; right; left; exists (0x6c4e38, 0x6c5058); split; [apply EXIT_CI; unfold exit_ci_need; cbn [app]; pick_in | cbn [fst snd]; lia] |
                apply Forall_cons; [left; right; left; exists (0x6c5058, 0x6c5060); split; [apply EXIT_CI; unfold exit_ci_need; cbn [app]; pick_in | cbn [fst snd]; lia] | apply Forall_nil]]]);
          assert (HINV0 : harness_invA mc)
            by (destruct HINV as [CIM CSH]; split;
                [ eapply client_img_munch_gen; [exact CIM | exact MU | exact WM | cbn [disjoint_from]; lia | cbn [disjoint_from]; lia | unfold AGOT_ERRC, AERRC, AMSG_SH, AJT_SH, AJT; cbn [disjoint_from]; lia | unfold AGOT_ERRC, AERRC, AMSG_SH, AJT_SH, AJT; cbn [disjoint_from]; lia | unfold AGOT_ERRC, AERRC, AMSG_SH, AJT_SH, AJT; cbn [disjoint_from]; lia | unfold AGOT_ERRC, AERRC, AMSG_SH, AJT_SH, AJT; cbn [disjoint_from]; lia | unfold AREAL_STRLEN; cbn [disjoint_from]; lia]   (* [comment removed for export] *)
                | eapply client_sh_munch_gen; [exact CSH | exact MU |];
                  intros X HX; unfold client_sh_addrs in HX; cbn [In] in HX; cbn [outside];
                  repeat (destruct HX as [<-|HX]; [rewrite shad_div; unfold ASHOFF; cbn; lia|]); destruct HX ]);
          assert (RCL0 : rclean mc rstk)
            by (eapply rclean_transport; [exact RCL | exact MU | exact WM |]; unfold appW, KLOW, KHIGH;
                apply Forall_cons; [right; cbn [fst snd]; lia | apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_nil]]])
        end.
        apply evtF_done.
        eapply implMA_post_evtF.
        { eapply (AVD L RNG) with (LB := LB) (p := p) (V := V) (lo := lo) (rstk := rstk) (s := s);
            try first [ exact AH0 | exact INB | exact HBO | exact HINV0 | exact RCL0 | exact FRM | exact HUXL | exact RTOP | exact RIMG | exact RSH | exact RRNG | exact APOK
                      | exact ATL | exact RLO | exact RRLO | exact SPTOP
                      | reflexivity
                      | (rewrite ESP; first [ eassumption | unfold AVDTOR_STACK; clear - LO; lia | clear - SP47; lia | clear - RHI; lia | (clear - AL; Z.div_mod_to_equations; lia) | (eapply rng_sub'; [exact RSTK | clear - LO RSP; lia]) ])
                      | (unfold AVEC; hyp_by_addr) | hyp_by_addr | eassumption
                      | (rewrite unsigned_lit by lia; cbn; lia) ]. }
        cbv beta. intros [] s' RNG' ms' PO. unfold avdtor_post in PO.
        destruct PO as (FPLE & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MI' & ST' & HPR & AH' & RESTEQ & HINV' & VEC').
        rewrite ESP in ST', HPR.
        assert (HPC : forall a, in_ranges CI a \/ (bv_unsigned sp + -64 <= a < 2^47) -> ~ (0x6a2a40 <= a < 0x6a2a58) ->
                        aclient_addr CI (lb_remove p LB) (bv_unsigned sp + -64) a /\ ~ (AVEC <= a < AVEC + 24))
          by (intros a [X|X] NV; (split; [first [right; left; exact X | left; exact X] | unfold AVEC; lia])).
        pose proof HPR as HPR0. unfold vdtor_pres in HPR.
        pose proof (xp_ci AI EXIT_CI _ _ _ _ HPR HPC) as XCI. pose proof (xp_stack AI _ _ _ _ HPR HPC) as XST.
        rewrite (ret_pc_even 1341616) by (cbn; lia).
        pose proof (exit_relro_of_aheap AI _ _ _ _ _ AH') as (GFL' & GF' & GCX' & GG'). unfold got_ssp, ssp_guard in GG'.
        assert (FF' : rw_cells asegs m' 0x6c4e58 [C8 (Z_to_bv 64 0x147a88); C8 (Z_to_bv 64 0x109580); C8 (Z_to_bv 64 0x76950)])
          by (eapply (XCI _ _ 0x6c4e38 0x6c5058); [exact FF | unfold exit_ci_need; cbn [app]; pick_in | lia | cbn [cells_size csize Nat.add app]; lia | cbn [cells_size csize Nat.add app]; lia]).
        assert (F3' : rw_cells asegs m' 0x6c4e70 [C8 (Z_to_bv 64 0x147a88)])
          by (eapply (XCI _ _ 0x6c4e38 0x6c5058); [exact F3 | unfold exit_ci_need; cbn [app]; pick_in | lia | cbn [cells_size csize Nat.add app]; lia | cbn [cells_size csize Nat.add app]; lia]).
        assert (AA' : rw_cells asegs m' 0x6c4f58 [C8 (Z_to_bv 64 0xa0418); C8 (Z_to_bv 64 0x6a2e88); C8 z64])
          by (eapply (XCI _ _ 0x6c4e38 0x6c5058); [exact AA | unfold exit_ci_need; cbn [app]; pick_in | lia | cbn [cells_size csize Nat.add app]; lia | cbn [cells_size csize Nat.add app]; lia]).
        assert (A3' : rw_cells asegs m' 0x6c4f70 [C8 (Z_to_bv 64 0xb0de0)])
          by (eapply (XCI _ _ 0x6c4e38 0x6c5058); [exact A3 | unfold exit_ci_need; cbn [app]; pick_in | lia | cbn [cells_size csize Nat.add app]; lia | cbn [cells_size csize Nat.add app]; lia]).
        (* [comment removed for export] *)
        assert (INCB' : rw_cells asegs m' 0x6a2a14 [C1 (Z_to_bv 8 0)]).
        { eapply DrvAgree.rw_cells_magree; [exact HPR | exact INCB |]. intros a Ha. cbn in Ha.
          apply HPC; [left; exists (0x6a2a10, 0x6a2c58); split; [exact INCB_CI | cbn [fst snd]; lia] | lia]. }
        clear FF F3 F45 AA A3 A45 INCB GFL GF GCX GG.
        apply evtF_done. unfold head6_mid. split; [exact FPLE|].
        do 18 eexists. exists m', cdt, thr, sec, tm1, dso, guard. do 5 eexists. eexists.
        split; [reflexivity|].
        split; [eapply MDPRE_pres; [exact HPR0 | exact AH' | exact MI' | eapply MDPRE_frame; [exact HMD | exact MU | exact WM | exact WOK]]|].
        split; [eapply ICPT_pres; [exact HPR0 | exact AH' | exact MI' | eapply ICPT_frame; [exact IC | exact MU | exact WM | exact WOK] | exact AH0]|].
        split; [eapply (ios_cells_pres AI EXIT_CI _ _ _ _ HPR HPC); [exact AH' | eapply ios_cells_frame; [exact IOS | exact MU | exact WM | exact WIOS]]|].
        split; [exact ST'|].
        unfold RSTDIN, stdin_cells, got_ssp, ssp_guard.
        repeat (lazymatch goal with
                | |- rw_cells _ _ ?A _ /\ _ =>
                    split; [ first [ hyp_by_addr
                                   | match goal with H : rw_cells _ _ A _ |- _ =>
                                       first [ eapply XST; [exact H | lia | cbn [cells_size csize Nat.add]; lia | lia]
                                             | eapply XCI; [exact H | unfold exit_ci_need, exit_img_ranges; cbn [app]; pick_in
                                                           | cbn [cells_size csize Nat.add]; lia | cbn [cells_size csize Nat.add]; lia | cbn [cells_size csize Nat.add]; lia] ] end ] | ]
                end).
        split. { cbn [aps_so aset_cl]. rewrite (aps_so_of_rest _ _ RESTEQ).
                 eapply (stdout_file_pres AI EXIT_CI _ _ _ _ HPR HPC).
                 exists flags, mode, tail, bufbytes. split; [unfold file_cells; exact FC|]. split; [exact FL72|]. split; [exact BUF|]. split; [exact BUFP|]. split; [exact BUFL| exact INACT]. }
        split. { eapply (stderr_file_pres AI EXIT_CI _ _ _ _ HPR HPC). exists eflags, emode, ee, ewend, etail. unfold file_cells. exact EFC. }
        split; [exact GG'|].
        split; [eapply XCI; [exact GU | unfold exit_ci_need, exit_img_ranges; cbn [app]; pick_in | cbn [cells_size csize Nat.add]; lia | cbn [cells_size csize Nat.add]; lia | cbn [cells_size csize Nat.add]; lia]|].
        exact MI'.
      + (* [comment removed for export] *)
        intros [] sA RNGA msA PO. apply implMA_upd. apply evtF_done. exact PO.
    - (* [comment removed for export] *)
      intros [] sB RNG1 msB PO. unfold head6_mid in PO.
      destruct PO as (FPLE & ra' & t0' & t1' & t2' & s1r & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & s3' & t3' & t4' & t5' & t6' & m' &
                      cdt' & thr' & sec' & tm1' & dso' & guard' & x1' & x2' & x3' & xs0' & xra' & j8' & -> & TM).
      destruct TM as (HMD' & IC' & IOS' & ST' & FRF' & FRE' & LIBC' & FIN' & ALK' & SLOT' & HEAD' & NEXT' & FF' & AA' & F3' & A3' & INCB' & GFL' & FLG' & COV' & GF' & FA' & FINZ' & GCX' & DSO' &
                      OFL' & SIN' & SINF' & SOU' & SEU' & SOF' & SEF' & GG' & GU' & MI').
      unfold implMA. change (ioA AAllocAsan) with (io_S (St := APS) aps_so aset_so).
      eapply implF_epost_mono.
      + eapply (exit_join4_spec aps_so aset_so MDPRE ICPT ICPTR SLO SHI MDTOR MDPRE_frame ICPT_frame SE WCR FW0 FW0E FFL FFLS FFLE RNG1 sB (fun (e : Empty_set) _ _ => match e with end))
          with (lo := lo) (so_x := aps_so sB) (guard := guard') (t := t);
          try first [ eassumption | reflexivity | exact GLO | exact ATL' | exact SLOK | exact SHIK | exact KH | exact AL | exact SP47
                    | (intros _; reflexivity)
                    | (unfold EXIT_TAIL_DEPTH; clear - LO; lia)
                    | (eapply rng_fp_le; [exact FPLE | first [exact RSTK | exact RIMG]])
                    | (eapply ICPTR_mono; [exact FPLE | exact RI])
                    | (eapply Forall_impl; [| exact RW]; cbv beta; intros iv Hiv; eapply rng_fp_le; [exact FPLE | exact Hiv])
                    | (intros b Hb; eapply rng_fp_le; [exact FPLE | apply RG0; exact Hb]) ].
      + intros [e ?] RNG' ms'. destruct e.
  Qed.
End Head6.
End CANSEC1.
