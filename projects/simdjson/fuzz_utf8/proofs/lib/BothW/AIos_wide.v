(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Lib Require Import Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Spec Require Import Prelim Monad Stdio.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import Startup_kit.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.BothW Require Import F_syscalls StdioFiles Stdio_kit BImg MonadF AIos_tac AIos_iface.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.LibA Require Import ITreeA StepF.
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
Section Wide.
  Variable ICPT : mem -> Prop.
  Variable ICPTR : footprint -> Prop.
  Variables SLO SHI : Z.
  Hypothesis WCR : wcrtomb0_stmt ICPT ICPTR SLO SHI.
  Hypothesis FW0E : fwrite0_err_stmt ICPT ICPTR.
  Hypothesis FFLE : fflush_err_stmt ICPT ICPTR.
  (* [comment removed for export] *)
  Hypothesis ICPT_frame : forall W m m', ICPT m -> munch W m m' -> wmono bsegs m m' ->
    Forall (fun iv => ATOP <= fst iv \/ (RSTDERR <= fst iv /\ snd iv <= RSTDOUT + 232) \/ (0x6afad8 <= fst iv /\ snd iv <= 0x6afae0)) W -> ICPT m'.

  Lemma unshift_w_spec :
    forall RNG (TN : Z) (tn0 : list byte) (MBS : Z) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (guard : word),
      stk bsegs m lo (bv_unsigned sp) -> rw_cells bsegs m TN [CB 8 tn0] -> bv_unsigned sp <= TN -> TN + 8 <= 2^47 ->
      ssp_cells m guard -> ICPT m -> ios_wide_shared m -> mem_inv bsegs m ->
      a0 = Z_to_bv 64 0x6ae7f0 -> a1 = Z_to_bv 64 MBS -> (MBS = 0x6adbcc \/ MBS = 0x6adbd4) -> a4 = Z_to_bv 64 TN -> tp = Z_to_bv 64 RTP ->
      lo <= bv_unsigned sp - 4160 -> GLOBALS_TOP <= lo -> ATOP <= lo -> SLO <= lo -> bv_unsigned sp <= SHI -> bv_unsigned sp mod 16 = 0 -> bv_unsigned sp < 2^47 ->
      rng RNG lo (bv_unsigned sp - lo) -> rng RNG TN 8 -> rng_aimg RNG -> ICPTR RNG ->
      evtF bsegs RNG (fun ms' => exists (t0 t1 t2 a1 a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
          ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (ret_pc ra) fc None m' (seg_rom bsegs)
          /\ munch [(bv_unsigned sp - 4160, bv_unsigned sp); (TN, TN + 8); (0x6afad8, 0x6afae0)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
          /\ stk bsegs m' lo (bv_unsigned sp) /\ ssp_cells m' guard /\ ICPT m'
          /\ rw_cells bsegs m' TN [C8 a2] /\ rw_cells bsegs m' 0x6afad8 [C8 (Z_to_bv 64 0x6cfdd0)])
           (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x13cdd4) fc None m (seg_rom bsegs)).
  Proof.
    intros until guard. intros ST TNC TNlo TNhi SSP IC IOSW MI -> -> MBSOK -> -> LO GLO ATL SLOK SHIK AL SP47 RSTK RTN RIMG RI.
    pose proof GLO as GLO'. unfold GLOBALS_TOP in GLO'.
    destruct SSP as [GOT GUARD]. unfold got_ssp, ssp_guard in GOT, GUARD.
    destruct IOSW as (VBW & SYNCW & CVW & UNSW & LOC & CURL).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (munch_refl [(bv_unsigned sp - 4160, bv_unsigned sp); (TN, TN + 8); (0x6afad8, 0x6afae0)]%Z m) as MU.
    pose proof (wmono_refl bsegs m) as WM.
    carve_frame 64%nat ST.
    steps_to 0x6b138%Z.
    (* [comment removed for export] *)
    apply (rw_cells_split_CB bsegs _ _ [] 16 _ _ [12;1;3]%nat) in FR; [| reflexivity]. cbn [app mk_CB_cells] in FR.
    match type of FR with rw_cells _ ?mm ?A (?c1 :: ?c2 :: ?rest) =>
      pose proof (proj1 (rw_cells_app bsegs mm A [c1] (c2 :: rest)) FR) as [FRa FRbc];
      pose proof (proj1 (rw_cells_app bsegs mm _ [c2] rest) FRbc) as [FRb FRc]; clear FR FRbc end.
    cbn [cells_size csize Nat.add] in FRb, FRc.
    change (Z.of_nat 12) with 12 in FRb, FRc. change (Z.of_nat 1) with 1 in FRc.
    replace (bv_unsigned sp + -64 + 12) with (bv_unsigned sp + -52) in FRb, FRc by (clear; lia).
    replace (bv_unsigned sp + -52 + 1) with (bv_unsigned sp + -51) in FRc by (clear; lia).
    change (Z.lor (Z.land (Z.b2z (0 <? 0) + -1) 18446744073709551615) 7142864) with 18446744073709551615 in *.
    call_sp (WCR RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (bv_unsigned sp + -52));
      try first [ eassumption | reflexivity | unfold GLOBALS_TOP; lia | lia
                | (eapply rng_sub'; [exact RSTK | lia])
                | (clear - AL; Z.div_mod_to_equations; lia)
                | (eapply ICPT_frame; [exact IC | exact MU | exact WM |
                     apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_cons; [right; right; cbn [fst snd]; lia | apply Forall_nil]]]]) ].
    { unfold ssp_cells, got_ssp, ssp_guard. split; [exact GOT| exact GUARD]. }
    match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
      pose proof (munch_refl [(0x6afad8, 0x6afae0)]%Z mx) as MUx; pose proof (wmono_refl bsegs mx) as WMx end.
    steps_to 0x13ce34%Z.
    nstep. nstep. nstep. nstep. nstep.
    match goal with |- context [bv_ltu ?x z64] =>
      replace (bv_ltu x z64) with false by (symmetry; unfold bv_ltu; apply Z.ltb_ge; pose proof (bv_unsigned_in_range 64 x) as RX; change (bv_unsigned z64) with 0; clear - RX; lia) end.
    cbn [negb]. cbv iota.
    steps_to 0x13ce98%Z.
    (* [comment removed for export] *)
    assert (FR : rw_cells bsegs m0 (bv_unsigned sp + -64)
                   ([CB 12 (firstn 12 (firstn 16 (firstn 24 (firstn 32 (firstn 40 (firstn 48 (firstn 56 junk)))))))] ++ [C1 (Z_to_bv 8 0)] ++
                    [CB 3 (firstn 3 (skipn 1 (skipn 12 (firstn 16 (firstn 24 (firstn 32 (firstn 40 (firstn 48 (firstn 56 junk)))))))));
                     C8 (Z_to_bv 64 18446744073709551615); C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])).
    { apply (proj2 (rw_cells_app bsegs m0 _ _ _)). split; [exact FRa|].
      apply (proj2 (rw_cells_app bsegs m0 _ _ _)). cbn [cells_size csize Nat.add]. change (Z.of_nat 12) with 12. change (Z.of_nat 1) with 1.
      replace (bv_unsigned sp + -64 + 12) with (bv_unsigned sp + -52) by (clear; lia).
      replace (bv_unsigned sp + -52 + 1) with (bv_unsigned sp + -51) by (clear; lia). split; [exact POST| exact FRc]. }
    clear FRa FRc POST. cbn [app] in FR.
    release_frame FR PC (bv_unsigned sp).
    hstep.
    apply evtF_done. do 14 eexists. eexists.
    split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI0|]. split; [exact PC|].
    split; [unfold ssp_cells, got_ssp, ssp_guard; split; [exact GOT| exact GUARD]|].
    split; [eapply ICPT_frame; [exact PC1 | exact MUx | exact WMx | apply Forall_cons; [right; right; cbn [fst snd]; lia | apply Forall_nil]]|].
    split; [exact TNC| exact CURL].
  Qed.

  (* [comment removed for export] *)
  Definition W_WERR (sp : Z) (d : Z) : list (Z * Z) := [(sp - d, sp); (RSTDERR, RSTDERR + 232); (0x6afad8, 0x6afae0)].

  Lemma sync_w_err_spec :
    forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (guard : word),
      stk bsegs m lo (bv_unsigned sp) -> stderr_file m ->
      ssp_cells m guard -> ICPT m -> ios_wide_shared m -> ios_wclog m -> mem_inv bsegs m ->
      a0 = Z_to_bv 64 0x6add08 -> tp = Z_to_bv 64 RTP ->
      lo <= bv_unsigned sp - 4240 -> GLOBALS_TOP <= lo -> ATOP <= lo -> SLO <= lo -> bv_unsigned sp <= SHI -> bv_unsigned sp mod 16 = 0 -> bv_unsigned sp < 2^47 ->
      rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG -> ICPTR RNG ->
      evtF bsegs RNG (icpt_post ICPT [(bv_unsigned sp - 4240, bv_unsigned sp); (RSTDERR, RSTDERR + 232); (0x6afad8, 0x6afae0)]
                                ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo guard m
                                (fun m' => stderr_file m' /\ rw_cells bsegs m' 0x6afad8 [C8 (Z_to_bv 64 0x6cfdd0)]))
           (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x115428) fc None m (seg_rom bsegs)).
  Proof.
    intros until guard. intros ST SEF SSP IC IOSW IOSC MI -> -> LO GLO ATL SLOK SHIK AL SP47 RSTK RIMG RI.
    pose proof GLO as GLO'. unfold GLOBALS_TOP in GLO'.
    destruct SEF as (eflags & emode & ee & ewend & etail & EFC). unfold file_cells in EFC.
    destruct SSP as [GOT GUARD]. unfold got_ssp, ssp_guard in GOT, GUARD.
    destruct IOSW as (VBW & SYNCW & CVW & UNSW & LOC & CURL). destruct IOSC as (O1 & O2 & O3 & O4 & O5 & B1 & B2).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (munch_refl [(bv_unsigned sp - 4240, bv_unsigned sp); (RSTDERR, RSTDERR + 232); (0x6afad8, 0x6afae0)]%Z m) as MU.
    pose proof (wmono_refl bsegs m) as WM.
    carve_frame 80%nat ST.
    steps_to 0x13cdd4%Z.
    (* [comment removed for export] *)
    apply (rw_cells_split_CB bsegs _ _ [] 24 _ _ [8;8;8]%nat) in FR; [| reflexivity]. cbn [app mk_CB_cells] in FR.
    match type of FR with rw_cells _ ?mm ?A (?c1 :: ?c2 :: ?rest) =>
      pose proof (proj1 (rw_cells_app bsegs mm A [c1] (c2 :: rest)) FR) as [FRa FRbc];
      pose proof (proj1 (rw_cells_app bsegs mm _ [c2] rest) FRbc) as [FRb FRc]; clear FR FRbc end.
    cbn [cells_size csize Nat.add] in FRb, FRc. change (Z.of_nat 8) with 8 in FRb, FRc.
    replace (bv_unsigned sp + -80 + 8) with (bv_unsigned sp + -72) in FRb, FRc by (clear; lia).
    replace (bv_unsigned sp + -72 + 8) with (bv_unsigned sp + -64) in FRc by (clear; lia).
    call_sp (unshift_w_spec RNG (bv_unsigned sp + -72));
      try first [ eassumption | reflexivity | unfold GLOBALS_TOP; lia | lia
                | (eapply rng_sub'; [exact RSTK | lia])
                | (clear - AL; Z.div_mod_to_equations; lia)
                | (eapply ICPT_frame; [exact IC | exact MU | exact WM |
                     apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_cons; [right; left; cbn [fst snd]; lia | apply Forall_cons; [right; right; cbn [fst snd]; lia | apply Forall_nil]]]]) ].
    { unfold ssp_cells, got_ssp, ssp_guard. split; [exact GOT| exact GUARD]. }
    { unfold ios_wide_shared. conj_by_addr. }
    (* [comment removed for export] *)
    match goal with
    | TNP : rw_cells bsegs ?mm (bv_unsigned sp + -72) [?c2], FRa' : rw_cells bsegs ?mm (bv_unsigned sp + -80) [?c1],
      FRc' : rw_cells bsegs ?mm (bv_unsigned sp + -64) ?rest |- _ =>
        assert (FR : rw_cells bsegs mm (bv_unsigned sp + -80) ([c1] ++ [c2] ++ rest))
          by (apply (proj2 (rw_cells_app bsegs mm _ _ _)); split; [exact FRa'|];
              apply (proj2 (rw_cells_app bsegs mm _ _ _)); cbn [cells_size csize Nat.add]; change (Z.of_nat 8) with 8;
              replace (bv_unsigned sp + -80 + 8) with (bv_unsigned sp + -72) by (clear; lia);
              replace (bv_unsigned sp + -72 + 8) with (bv_unsigned sp + -64) by (clear; lia); split; [exact TNP| exact FRc']);
        clear TNP FRa' FRc'; cbn [app] in FR
    end.
    steps_to 0x6b0f4%Z.
    replace (bv_unsigned sp + -64 - (bv_unsigned sp + -64)) with 0 by (clear; lia).
    call_sp (FW0E RNG);
      try first [ eassumption | reflexivity | unfold GLOBALS_TOP; lia
                | (eapply rng_sub'; [exact RSTK | lia])
                | (clear - AL; Z.div_mod_to_equations; lia) ].
    { exists eflags, emode, ee, ewend, etail. unfold file_cells. exact EFC. }
    steps_to 0x6b154%Z.
    call_sp (FFLE RNG);
      try first [ eassumption | reflexivity | unfold GLOBALS_TOP; lia
                | (eapply rng_sub'; [exact RSTK | lia])
                | (clear - AL; Z.div_mod_to_equations; lia) ].
    hstep. hstep. do 9 hstep.
    change (Z.b2z (0 <? 1) + -1) with 0.
    match goal with H : rw_cells _ _ (bv_unsigned sp + -80)%Z _, S : stk _ _ lo _ |- _ => release_frame H S (bv_unsigned sp) end.
    apply evtF_done. unfold icpt_post. do 14 eexists. eexists.
    split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [eassumption|].
    split; [eassumption|]. split; [eassumption|]. split; [eassumption| hyp_by_addr].
  Qed.

  (* [comment removed for export] *)
  Definition flush_w_err_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (lo : Z) (guard : word) (m : mem) : machine_state -> Prop :=
    fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0x6ae158) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom bsegs)
      /\ munch [(bv_unsigned sp - 4288, bv_unsigned sp); (RSTDERR, RSTDERR + 232); (0x6afad8, 0x6afae0)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ stk bsegs m' lo (bv_unsigned sp) /\ ssp_cells m' guard /\ ICPT m' /\ stderr_file m' /\ rw_cells bsegs m' 0x6afad8 [C8 (Z_to_bv 64 0x6cfdd0)].

  Lemma flush_w_err_spec :
    forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (guard : word),
      stk bsegs m lo (bv_unsigned sp) -> stderr_file m ->
      ssp_cells m guard -> ICPT m -> ios_wide_shared m -> ios_wclog m -> mem_inv bsegs m ->
      a0 = Z_to_bv 64 0x6ae158 -> tp = Z_to_bv 64 RTP ->
      lo <= bv_unsigned sp - 4288 -> GLOBALS_TOP <= lo -> ATOP <= lo -> SLO <= lo -> bv_unsigned sp <= SHI -> bv_unsigned sp mod 16 = 0 -> bv_unsigned sp < 2^47 ->
      rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG -> ICPTR RNG ->
      evtF bsegs RNG (flush_w_err_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo guard m)
           (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x113d78) fc None m (seg_rom bsegs)).
  Proof.
    intros until guard. intros ST SEF SSP IC IOSW IOSC MI -> -> LO GLO ATL SLOK SHIK AL SP47 RSTK RIMG RI.
    pose proof GLO as GLO'. unfold GLOBALS_TOP in GLO'.
    destruct SEF as (eflags & emode & ee & ewend & etail & EFC). unfold file_cells in EFC.
    destruct SSP as [GOT GUARD]. unfold got_ssp, ssp_guard in GOT, GUARD.
    destruct IOSW as (VBW & SYNCW & CVW & UNSW & LOC & CURL). destruct IOSC as (O1 & O2 & O3 & O4 & O5 & B1 & B2).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (munch_refl [(bv_unsigned sp - 4288, bv_unsigned sp); (RSTDERR, RSTDERR + 232); (0x6afad8, 0x6afae0)]%Z m) as MU.
    pose proof (wmono_refl bsegs m) as WM.
    carve_frame 48%nat ST.
    steps_to 0x115428%Z.
    call_sp (sync_w_err_spec RNG);
      try first [ eassumption | reflexivity | unfold GLOBALS_TOP; lia | lia
                | (eapply rng_sub'; [exact RSTK | lia])
                | (clear - AL; Z.div_mod_to_equations; lia)
                | (eapply ICPT_frame; [exact IC | exact MU | exact WM |
                     apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_cons; [right; left; cbn [fst snd]; lia | apply Forall_cons; [right; right; cbn [fst snd]; lia | apply Forall_nil]]]]) ].
    { exists eflags, emode, ee, ewend, etail. unfold file_cells. exact EFC. }
    { unfold ssp_cells, got_ssp, ssp_guard. split; [exact GOT| exact GUARD]. }
    { unfold ios_wide_shared. conj_by_addr. }
    { unfold ios_wclog. conj_by_addr. }
    rename POST into CURL2. destruct PC2 as (eflags2 & emode2 & ee2 & ewend2 & etail2 & EFC2). unfold file_cells in EFC2.
    steps_to 0x113f4c%Z.
    match goal with S : stk _ _ lo (bv_unsigned sp + -48)%Z |- _ => carve_frame 16%nat S end.
    steps_to 0x113df8%Z.
    match goal with H : rw_cells _ _ (bv_unsigned sp + -64)%Z _, S : stk _ _ lo _ |- _ => release_frame H S (bv_unsigned sp + -48)%Z end.
    do 6 hstep.
    match goal with H : rw_cells _ _ (bv_unsigned sp + -48)%Z _, S : stk _ _ lo _ |- _ => release_frame H S (bv_unsigned sp) end.
    apply evtF_done. unfold flush_w_err_post. do 14 eexists. eexists.
    split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [eassumption|].
    split; [unfold ssp_cells, got_ssp, ssp_guard; split; [exact GOT| exact GUARD]|].
    split; [eapply ICPT_frame; [exact IC | exact MU | exact WM |
              apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_cons; [right; left; cbn [fst snd]; lia | apply Forall_cons; [right; right; cbn [fst snd]; lia | apply Forall_nil]]]]|].
    split; [exists eflags2, emode2, ee2, ewend2, etail2; unfold file_cells; exact EFC2| exact CURL2].
  Qed.

End Wide.
End CANSEC1.
