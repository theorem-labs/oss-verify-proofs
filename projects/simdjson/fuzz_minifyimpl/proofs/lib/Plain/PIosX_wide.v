(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import Tac ITree Nodes Decode SysStep StoreFast MonadX.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import Prelim Monad Stdio.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import F_fmt_fp_lib Stdio_pure Startup_kit Amo_tac.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Plain Require Import F_syscalls StdioFiles Stdio_kit PImg PExitU_tac PIosX_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac steps_to p := xsteps_to p.

Section Wide.
  Hypothesis WCR : wcrtomb0_stmt.
  Hypothesis FW0E : fwrite0_err_stmt.
  Hypothesis FFLE : fflush_err_stmt.

  Lemma unshift_w_spec :
    forall (TN : Z) (tn0 : list byte) (MBS : Z) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (guard : word),
      stk psegs m lo (bv_unsigned sp) -> rw_cells psegs m TN [CB 8 tn0] -> bv_unsigned sp <= TN -> TN + 8 <= 2^47 ->
      ssp_cells m guard -> ios_wide_shared m -> mem_inv psegs m ->
      a0 = Z_to_bv 64 0xe2710 -> a1 = Z_to_bv 64 MBS -> (MBS = 0xe1aec \/ MBS = 0xe1af4) -> a4 = Z_to_bv 64 TN -> tp = Z_to_bv 64 RTP ->
      lo <= bv_unsigned sp - 4160 -> GLOBALS_TOP <= lo -> bv_unsigned sp < 2^47 ->
      evt psegs (fun ms' => exists (t0 t1 t2 a1 a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
          ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (ret_pc ra) fc None m' (seg_rom psegs)
          /\ munch [(bv_unsigned sp - 4160, bv_unsigned sp); (TN, TN + 8); (0xe39f8, 0xe3a00)] m m' /\ wmono psegs m m' /\ mem_inv psegs m'
          /\ stk psegs m' lo (bv_unsigned sp) /\ ssp_cells m' guard
          /\ rw_cells psegs m' TN [C8 a2] /\ rw_cells psegs m' 0xe39f8 [C8 (Z_to_bv 64 0x103cf0)])
           (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x9debc) fc None m (seg_rom psegs)).
  Proof.
    intros until guard. intros ST TNC TNlo TNhi SSP IOSW MI -> -> MBSOK -> -> LO GLO SP47.
    pose proof GLO as GLO'. unfold GLOBALS_TOP in GLO'.
    destruct SSP as [GOT GUARD]. unfold got_ssp, ssp_guard in GOT, GUARD.
    destruct IOSW as (VBW & SYNCW & CVW & UNSW & LOC & CURL).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (munch_refl [(bv_unsigned sp - 4160, bv_unsigned sp); (TN, TN + 8); (0xe39f8, 0xe3a00)]%Z m) as MU.
    pose proof (wmono_refl psegs m) as WM.
    carve_frame 64%nat ST.
    steps_to 0xb8180%Z.
    (* [comment removed for export] *)
    apply (rw_cells_split_CB psegs _ _ [] 16 _ _ [12;1;3]%nat) in FR; [| reflexivity]. cbn [app mk_CB_cells] in FR.
    match type of FR with rw_cells _ ?mm ?A (?c1 :: ?c2 :: ?rest) =>
      pose proof (proj1 (rw_cells_app psegs mm A [c1] (c2 :: rest)) FR) as [FRa FRbc];
      pose proof (proj1 (rw_cells_app psegs mm _ [c2] rest) FRbc) as [FRb FRc]; clear FR FRbc end.
    cbn [cells_size csize Nat.add] in FRb, FRc.
    change (Z.of_nat 12) with 12 in FRb, FRc. change (Z.of_nat 1) with 1 in FRc.
    replace (bv_unsigned sp + -64 + 12) with (bv_unsigned sp + -52) in FRb, FRc by (clear; lia).
    replace (bv_unsigned sp + -52 + 1) with (bv_unsigned sp + -51) in FRc by (clear; lia).
    change (Z.lor (Z.land (Z.b2z (0 <? 0) + -1) 18446744073709551615) 1064176) with 18446744073709551615 in *.
    call_sp (WCR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (bv_unsigned sp + -52));
      try first [ eassumption | reflexivity | unfold GLOBALS_TOP; lia | lia ].
    match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      pose proof (munch_refl [(0xe39f8, 0xe3a00)]%Z mx) as MUx; pose proof (wmono_refl psegs mx) as WMx end.
    steps_to 0x9df1c%Z.
    nstep. nstep. nstep. nstep. nstep.
    match goal with |- context [bv_ltu ?x z64] =>
      replace (bv_ltu x z64) with false by (symmetry; unfold bv_ltu; apply Z.ltb_ge; pose proof (bv_unsigned_in_range 64 x) as RX; change (bv_unsigned z64) with 0; clear - RX; lia) end.
    cbn [negb]. cbv iota.
    steps_to 0x9df80%Z.
    (* [comment removed for export] *)
    assert (FR : rw_cells psegs m0 (bv_unsigned sp + -64)
                   ([CB 12 (firstn 12 (firstn 16 (firstn 24 (firstn 32 (firstn 40 (firstn 48 (firstn 56 junk)))))))] ++ [C1 (Z_to_bv 8 0)] ++
                    [CB 3 (firstn 3 (skipn 1 (skipn 12 (firstn 16 (firstn 24 (firstn 32 (firstn 40 (firstn 48 (firstn 56 junk)))))))));
                     C8 (Z_to_bv 64 18446744073709551615); C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])).
    { apply (proj2 (rw_cells_app psegs m0 _ _ _)). split; [exact FRa|].
      apply (proj2 (rw_cells_app psegs m0 _ _ _)). cbn [cells_size csize Nat.add]. change (Z.of_nat 12) with 12. change (Z.of_nat 1) with 1.
      replace (bv_unsigned sp + -64 + 12) with (bv_unsigned sp + -52) by (clear; lia).
      replace (bv_unsigned sp + -52 + 1) with (bv_unsigned sp + -51) by (clear; lia). split; [exact POST| exact FRc]. }
    clear FRa FRc POST. cbn [app] in FR.
    release_frame FR PC (bv_unsigned sp).
    hstep.
    apply evt_done. do 14 eexists. eexists.
    split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI0|]. split; [exact PC|].
    split; [unfold ssp_cells, got_ssp, ssp_guard; split; [exact GOT| exact GUARD]|].
    split; [exact TNC| exact CURL].
  Qed.

  (* [comment removed for export] *)
  Definition W_WERR (sp : Z) (d : Z) : list (Z * Z) := [(sp - d, sp); (RSTDERR, RSTDERR + 232); (0xe39f8, 0xe3a00)].

  Lemma sync_w_err_spec :
    forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (guard : word),
      stk psegs m lo (bv_unsigned sp) -> stderr_file m ->
      ssp_cells m guard -> ios_wide_shared m -> ios_wclog m -> mem_inv psegs m ->
      a0 = Z_to_bv 64 0xe1c28 -> tp = Z_to_bv 64 RTP ->
      lo <= bv_unsigned sp - 4240 -> GLOBALS_TOP <= lo -> bv_unsigned sp < 2^47 ->
      evt psegs (icpt_post [(bv_unsigned sp - 4240, bv_unsigned sp); (RSTDERR, RSTDERR + 232); (0xe39f8, 0xe3a00)]
                                ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo guard m
                                (fun m' => stderr_file m' /\ rw_cells psegs m' 0xe39f8 [C8 (Z_to_bv 64 0x103cf0)]))
           (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x765d0) fc None m (seg_rom psegs)).
  Proof.
    intros until guard. intros ST SEF SSP IOSW IOSC MI -> -> LO GLO SP47.
    pose proof GLO as GLO'. unfold GLOBALS_TOP in GLO'.
    destruct SEF as (eflags & emode & ee & ewend & etail & EFC). unfold file_cells in EFC.
    destruct SSP as [GOT GUARD]. unfold got_ssp, ssp_guard in GOT, GUARD.
    destruct IOSW as (VBW & SYNCW & CVW & UNSW & LOC & CURL). destruct IOSC as (O1 & O2 & O3 & O4 & O5 & B1 & B2).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (munch_refl [(bv_unsigned sp - 4240, bv_unsigned sp); (RSTDERR, RSTDERR + 232); (0xe39f8, 0xe3a00)]%Z m) as MU.
    pose proof (wmono_refl psegs m) as WM.
    carve_frame 80%nat ST.
    steps_to 0x9debc%Z.
    (* [comment removed for export] *)
    apply (rw_cells_split_CB psegs _ _ [] 24 _ _ [8;8;8]%nat) in FR; [| reflexivity]. cbn [app mk_CB_cells] in FR.
    match type of FR with rw_cells _ ?mm ?A (?c1 :: ?c2 :: ?rest) =>
      pose proof (proj1 (rw_cells_app psegs mm A [c1] (c2 :: rest)) FR) as [FRa FRbc];
      pose proof (proj1 (rw_cells_app psegs mm _ [c2] rest) FRbc) as [FRb FRc]; clear FR FRbc end.
    cbn [cells_size csize Nat.add] in FRb, FRc. change (Z.of_nat 8) with 8 in FRb, FRc.
    replace (bv_unsigned sp + -80 + 8) with (bv_unsigned sp + -72) in FRb, FRc by (clear; lia).
    replace (bv_unsigned sp + -72 + 8) with (bv_unsigned sp + -64) in FRc by (clear; lia).
    call_sp (unshift_w_spec (bv_unsigned sp + -72));
      try first [ eassumption | reflexivity | unfold GLOBALS_TOP; lia | lia
      ].
    { unfold ssp_cells, got_ssp, ssp_guard. split; [exact GOT| exact GUARD]. }
    { unfold ios_wide_shared. conj_by_addr. }
    (* [comment removed for export] *)
    match goal with
    | TNP : rw_cells psegs ?mm (bv_unsigned sp + -72) [?c2], FRa' : rw_cells psegs ?mm (bv_unsigned sp + -80) [?c1],
      FRc' : rw_cells psegs ?mm (bv_unsigned sp + -64) ?rest |- _ =>
        assert (FR : rw_cells psegs mm (bv_unsigned sp + -80) ([c1] ++ [c2] ++ rest))
          by (apply (proj2 (rw_cells_app psegs mm _ _ _)); split; [exact FRa'|];
              apply (proj2 (rw_cells_app psegs mm _ _ _)); cbn [cells_size csize Nat.add]; change (Z.of_nat 8) with 8;
              replace (bv_unsigned sp + -80 + 8) with (bv_unsigned sp + -72) by (clear; lia);
              replace (bv_unsigned sp + -72 + 8) with (bv_unsigned sp + -64) by (clear; lia); split; [exact TNP| exact FRc']);
        clear TNP FRa' FRc'; cbn [app] in FR
    end.
    steps_to 0xb9394%Z.
    replace (bv_unsigned sp + -64 - (bv_unsigned sp + -64)) with 0 by (clear; lia).
    call_sp FW0E;
      try first [ eassumption | reflexivity | unfold GLOBALS_TOP; lia
 ].
    { exists eflags, emode, ee, ewend, etail. unfold file_cells. exact EFC. }
    steps_to 0xb84ec%Z.
    call_sp FFLE;
      try first [ eassumption | reflexivity | unfold GLOBALS_TOP; lia
 ].
    hstep. hstep. do 9 hstep.
    change (Z.b2z (0 <? 1) + -1) with 0.
    match goal with H : rw_cells _ _ (bv_unsigned sp + -80)%Z _, S : stk _ _ lo _ |- _ => release_frame H S (bv_unsigned sp) end.
    apply evt_done. unfold icpt_post. do 14 eexists. eexists.
    split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [eassumption|].
    split; [eassumption|]. split; [eassumption| hyp_by_addr].
  Qed.

  (* [comment removed for export] *)
  Definition flush_w_err_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (lo : Z) (guard : word) (m : mem) : machine_state -> Prop :=
    fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0xe2078) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom psegs)
      /\ munch [(bv_unsigned sp - 4288, bv_unsigned sp); (RSTDERR, RSTDERR + 232); (0xe39f8, 0xe3a00)] m m' /\ wmono psegs m m' /\ mem_inv psegs m'
      /\ stk psegs m' lo (bv_unsigned sp) /\ ssp_cells m' guard /\ stderr_file m' /\ rw_cells psegs m' 0xe39f8 [C8 (Z_to_bv 64 0x103cf0)].

  Lemma flush_w_err_spec :
    forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (guard : word),
      stk psegs m lo (bv_unsigned sp) -> stderr_file m ->
      ssp_cells m guard -> ios_wide_shared m -> ios_wclog m -> mem_inv psegs m ->
      a0 = Z_to_bv 64 0xe2078 -> tp = Z_to_bv 64 RTP ->
      lo <= bv_unsigned sp - 4288 -> GLOBALS_TOP <= lo -> bv_unsigned sp < 2^47 ->
      evt psegs (flush_w_err_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo guard m)
           (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x74f20) fc None m (seg_rom psegs)).
  Proof.
    intros until guard. intros ST SEF SSP IOSW IOSC MI -> -> LO GLO SP47.
    pose proof GLO as GLO'. unfold GLOBALS_TOP in GLO'.
    destruct SEF as (eflags & emode & ee & ewend & etail & EFC). unfold file_cells in EFC.
    destruct SSP as [GOT GUARD]. unfold got_ssp, ssp_guard in GOT, GUARD.
    destruct IOSW as (VBW & SYNCW & CVW & UNSW & LOC & CURL). destruct IOSC as (O1 & O2 & O3 & O4 & O5 & B1 & B2).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (munch_refl [(bv_unsigned sp - 4288, bv_unsigned sp); (RSTDERR, RSTDERR + 232); (0xe39f8, 0xe3a00)]%Z m) as MU.
    pose proof (wmono_refl psegs m) as WM.
    carve_frame 48%nat ST.
    steps_to 0x765d0%Z.
    call_sp sync_w_err_spec;
      try first [ eassumption | reflexivity | unfold GLOBALS_TOP; lia | lia
      ].
    { exists eflags, emode, ee, ewend, etail. unfold file_cells. exact EFC. }
    { unfold ssp_cells, got_ssp, ssp_guard. split; [exact GOT| exact GUARD]. }
    { unfold ios_wide_shared. conj_by_addr. }
    { unfold ios_wclog. conj_by_addr. }
    rename POST into CURL2. destruct PC1 as (eflags2 & emode2 & ee2 & ewend2 & etail2 & EFC2). unfold file_cells in EFC2.
    steps_to 0x750f4%Z.
    match goal with S : stk _ _ lo (bv_unsigned sp + -48)%Z |- _ => carve_frame 16%nat S end.
    steps_to 0x74fa0%Z.
    match goal with H : rw_cells _ _ (bv_unsigned sp + -64)%Z _, S : stk _ _ lo _ |- _ => release_frame H S (bv_unsigned sp + -48)%Z end.
    do 6 hstep.
    match goal with H : rw_cells _ _ (bv_unsigned sp + -48)%Z _, S : stk _ _ lo _ |- _ => release_frame H S (bv_unsigned sp) end.
    apply evt_done. unfold flush_w_err_post. do 14 eexists. eexists.
    split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [eassumption|].
    split; [unfold ssp_cells, got_ssp, ssp_guard; split; [exact GOT| exact GUARD]|].
    split; [exists eflags2, emode2, ee2, ewend2, etail2; unfold file_cells; exact EFC2| exact CURL2].
  Qed.

End Wide.
