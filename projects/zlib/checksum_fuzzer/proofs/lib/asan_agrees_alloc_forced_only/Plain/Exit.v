(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* reloc14 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_agrees_alloc_forced_only.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_agrees_alloc_forced_only.Common Require Import StrFun STRW_tac Startup_kit Amo_tac.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_agrees_alloc_forced_only.Spec Require Import Prelim Monad Stdio Driver.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_agrees_alloc_forced_only.Plain Require Import PImg F_syscalls Startup_A StdioFiles.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_agrees_alloc_forced_only.Plain Require Import F_atexit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Import ITree.Exc.

Notation rsegs := PImg.psegs.

Lemma p_Exit_spec : forall (code : Z) (Q : Empty_set -> machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  mem_inv rsegs m ->
  a0 = Z_to_bv 64 code ->
  impl rsegs (at_node rsegs) (enode (NExit code) dec_exit) (epost Q)
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 0x15984) fc None m (seg_rom rsegs)).
Proof.
  intros until m. intros MI ->.
  pose proof (wmono_refl rsegs m) as WM.
  apply impl_enode. do 2 lstep. step_ecall.
  split; [ at_node_red; split; [right; reflexivity | reflexivity] | intros rsp a H; cbn in H; discriminate H].
Qed.

Lemma p_Exit_specM : forall {St : Type} (s : St) (code : Z) (Q : Empty_set -> St -> machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  mem_inv rsegs m ->
  a0 = Z_to_bv 64 code ->
  implM rsegs (msys (NExit code) dec_exit) s Q
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 0x15984) fc None m (seg_rom rsegs)).
Proof.
  intros until m. intros MI ->.
  pose proof (wmono_refl rsegs m) as WM.
  apply implM_sys. do 2 lstep. step_ecall.
  split; [ at_node_red; split; [right; reflexivity | reflexivity] | intros rsp a H; cbn in H; discriminate H].
Qed.


Definition pexit_prefix_post (sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo code t : Z) (td0 td1 td2 td3 ra : word) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR (Z_to_bv 64 0x15bf0) (Z_to_bv 64 (bv_unsigned sp + -16)) gp (Z_to_bv 64 RTP) t0 t1 t2 (Z_to_bv 64 code) s1
                 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x17efc) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (0x4fd68, 0x4fd70); (0x1f9f8, 0x1f9f9); (PATX, PATX + PATX_N)]%Z m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp + -16)
    /\ rw_cells rsegs m' (bv_unsigned sp + -16) [C8 s0; C8 ra]
    /\ rw_cells rsegs m' RTD [C8 td0; C8 td1; C8 td2; C8 td3; C4 (Z_to_bv 64 t)]
    /\ rw_cells rsegs m' 0x4fd68 [C4 (Z_to_bv 64 t)]
    /\ rw_cells rsegs m' 0x1f9f8 [C1 (Z_to_bv 8 1)].

Lemma pexit_prefix_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (code t : Z) (td0 td1 td2 td3 : word) (cdt thr sec : byte) (tm1 : word),
  stk rsegs m lo (bv_unsigned sp) ->
  rw_cells rsegs m RTD [C8 td0; C8 td1; C8 td2; C8 td3; C4 (Z_to_bv 64 t)] ->
  rw_cells rsegs m 0x4fd68 [C4 z64] ->
  rw_cells rsegs m 0x1e788 [C8 (Z_to_bv 64 0x1e6f0); C8 (Z_to_bv 64 0x1e6e8)] ->
  rw_cells rsegs m 0x1e6e8 [C8 (Z_to_bv 64 0x13cc0)] ->
  rw_cells rsegs m 0x1f9f8 [C1 (Z_to_bv 8 0)] ->
  rw_cells rsegs m 0x1e730 [C8 (Z_to_bv 64 0x15a68); C8 z64] ->
  rw_cells rsegs m 0x1f798 [C8 (Z_to_bv 64 0x1f798)] ->
  rw_cells rsegs m PLIBC [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
  (atx_cells0 m \/ atx_cellsR m) ->
  mem_inv rsegs m ->
  tp = Z_to_bv 64 RTP -> a0 = Z_to_bv 64 code ->
  (0 < t < 4194304)%Z -> (lo <= bv_unsigned sp - 64)%Z -> (0x51000 <= lo)%Z ->
  evt rsegs (pexit_prefix_post sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo code t td0 td1 td2 td3 ra m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x15b84) fc None m (seg_rom rsegs)).
Proof.
  intros until tm1. intros ST TDa EXL GF FA FIN GCX DSO LCH ATX MI -> -> Ht LO LOLO.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (0x4fd68, 0x4fd70); (0x1f9f8, 0x1f9f9); (PATX, PATX + PATX_N)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (EPATX : PATX = ltac:(let v := eval cbv in PATX in exact v)) by reflexivity.
  assert (EPATXN : PATX_N = ltac:(let v := eval cbv in PATX_N in exact v)) by reflexivity.
  unfold PLIBC in LCH.
  destruct ATX as [[AX0 AX1]|[[AX0 AX1] AX2]]; [| unfold PAEF_INCB in AX2];
  ( carve_frame 16%nat ST;
    do 6 lstep;
    replace (sx32 (Z_to_bv 64 t)) with (Z_to_bv 64 t)
      by (unfold sx32; f_equal; rewrite unsigned_lit by lia; symmetry; apply swrap32_small; lia);
    lstep; lstep;
    amo_step; replace (sx32 z64) with z64 by (vm_compute; reflexivity);
    lstep; if_false; amo_step; lstep; if_false;
    lstep; change (bv_swrap 32 (0 + 0)) with 0%Z;
    lstep; if_cases K; zify_cond K; [exfalso; lia|]; clear K; lstep; if_true;
    lstep; lstep;
    call_sp (funcs_on_exit_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ lo cdt thr sec tm1);
      [ first [exact ST | match goal with H : bv_unsigned _ = _ |- _ => rewrite H; exact ST end]
      | first [left; exact (conj AX0 AX1) | right; exact (conj (conj AX0 AX1) AX2)] | exact LCH | exact MI | lia | lia | ];
    match goal with H : stk _ _ lo _ |- _ => rename H into ST end;
    steps_to 0x15b38%Z;
    carve_frame 32%nat ST; steps_to 0x13cc0%Z;
    carve_frame 16%nat ST; steps_to 0x13d18%Z; astep; astep;
    steps_to 0x13d4c%Z; release_frame FR1 ST (bv_unsigned sp + -48)%Z; astep;
    steps_to 0x15b80%Z; release_frame FR0 ST (bv_unsigned sp + -16)%Z; astep; astep;
    astep;
    unfold pexit_prefix_post; sys_finish ).
Qed.

Section ExitProof.
  Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
  Hypothesis stdio_exit_spec : stdio_exit_spec_stmt get_so set_so.

  Lemma exit_spec : forall (s : St) (Q : Empty_set -> St -> machine_state -> Prop)
      ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (code t : Z) (td0 td1 td2 td3 guard : word)
      (cdt thr sec : byte) (tm1 : word),
    stk rsegs m lo (bv_unsigned sp) ->
    rw_cells rsegs m RTD [C8 td0; C8 td1; C8 td2; C8 td3; C4 (Z_to_bv 64 t)] ->
    rw_cells rsegs m 0x4fd68 [C4 z64] ->
    rw_cells rsegs m 0x1e788 [C8 (Z_to_bv 64 0x1e6f0); C8 (Z_to_bv 64 0x1e6e8)] ->
    rw_cells rsegs m 0x1e6e8 [C8 (Z_to_bv 64 0x13cc0)] ->
    rw_cells rsegs m 0x1f9f8 [C1 (Z_to_bv 8 0)] ->
    rw_cells rsegs m 0x1e730 [C8 (Z_to_bv 64 0x15a68); C8 z64] ->
    rw_cells rsegs m 0x1f798 [C8 (Z_to_bv 64 0x1f798)] ->
    rw_cells rsegs m 0x4fd90 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
    (atx_cells0 m \/ atx_cellsR m) ->
    rw_cells rsegs m 0x501c0 [C8 z64] -> rw_cells rsegs m 0x501b0 [C8 z64] ->
    rw_cells rsegs m 0x1f998 [C8 (Z_to_bv 64 RSTDOUT)] -> rw_cells rsegs m 0x1f8a8 [C8 (Z_to_bv 64 RSTDERR)] ->
    stdout_file m (get_so s) -> stderr_file m ->
    rw_cells rsegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] -> rw_cells rsegs m ssp_guard [C8 guard] ->
    mem_inv rsegs m ->
    tp = Z_to_bv 64 RTP -> a0 = Z_to_bv 64 code ->
    (0 < t < 4194304)%Z -> (lo <= bv_unsigned sp - 176)%Z -> (0x51000 <= lo)%Z ->
    (bv_unsigned sp < 2^47)%Z ->
    implM rsegs (Driver.exit_model (io_S get_so set_so) code) s Q
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x15b84) fc None m (seg_rom rsegs)).
  Proof.
    intros until tm1. intros ST TDa EXL GF FA FIN GCX DSO LCH ATX OFL SIN SOU SEU SOF SEF GG GU MI -> -> Ht LO LOLO SP47.
    unfold got_ssp, ssp_guard in GG, GU.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    destruct SOF as (flg & mode & tail & bufb & SOF1 & SOF2 & SOF3 & SOF4 & SOF5 & SOF6).
    destruct SEF as (flg' & mode' & ee & wend' & tail' & SEF1).
    unfold file_cells in SOF1, SEF1.
    unfold Driver.exit_model.
    eapply (implM_bind rsegs _ _ s
              (fun _ _ ms' => exists sp' gp' tp' x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 m',
                 ms' = MS (mkR (Z_to_bv 64 0x15bf0) sp' gp' tp' x5 x6 x7 (Z_to_bv 64 code) x9 x10 x11 x12 x13 x14 x15 x16 x17
                               x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                          F (Z_to_bv 64 0x15bf0) fc None m' (seg_rom rsegs))).
    -
      change (io_exit (io_S get_so set_so)) with (stdout_exit_flush get_so set_so).
      assert (EPATX : PATX = ltac:(let v := eval cbv in PATX in exact v)) by reflexivity.
      assert (EPATXN : PATX_N = ltac:(let v := eval cbv in PATX_N in exact v)) by reflexivity.
      unfold implM. iprefix.
      call pexit_prefix_spec; [exact ST | exact TDa | exact EXL | exact GF | exact FA | exact FIN | exact GCX | exact DSO | exact LCH | exact ATX | exact MI
                              | reflexivity | reflexivity | lia | lia | lia | ].
      name_sp sp (-16)%Z.
      pose proof stdio_exit_spec as SE. unfold stdio_exit_spec_stmt, implM, got_ssp, ssp_guard, GLOBALS_TOP in SE.
      apply evt_done. eapply impl_epost_mono; [eapply SE|].
      all: lazymatch goal with
           | |- forall _, _ =>
               intros [[] s'] ms' PO; cbn [fst snd] in PO; unfold stdio_exit_post in PO;
               destruct_exs PO; destruct PO as (E & PO); subst ms'; cbn [fst snd];
               replace (ret_pc (Z_to_bv 64 0x15bf0)) with (Z_to_bv 64 0x15bf0) by (symmetry; apply ret_pc_even; [lia|reflexivity]);
               repeat eexists; cbv delta [mkR]; reflexivity
           | |- stdout_file _ _ => exists flg, mode, tail, bufb; exact (conj SOF1 (conj SOF2 (conj SOF3 (conj SOF4 (conj SOF5 SOF6)))))
           | |- stderr_file _ => exists flg', mode', ee, wend', tail'; exact SEF1
           | |- _ => unname_sp; first [ hyp_by_addr | reflexivity | lia ]
           end.
    -
      clear SOF1 SOF2 SOF3 SOF4 SOF5 SOF6 SEF1.
      intros [] s' ms' PO. destruct_exs PO. subst ms'.
      apply implM_sys. do 4 lstep. step_ecall.
      split; [ at_node_red; split; [right; reflexivity | reflexivity] | intros rsp a H; cbn in H; discriminate H].
  Qed.
End ExitProof.
