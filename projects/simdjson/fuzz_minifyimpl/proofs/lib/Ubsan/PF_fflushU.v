(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import Tac ITree Nodes Decode SysStep StoreFast MonadX.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import SFModel Stdio_pure.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import Prelim Monad Stdio.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Ubsan Require Import F_syscalls StdioFiles Stdio_kit.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import F_fmt_fp_lib.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Ubsan Require Import F_stdio_write F_stdout_write F_fwritex_stdout.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Ubsan Require Import UImg PExitU_tac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Ltac raise_high :=
  repeat match goal with H : rw_cells usegs _ ?A _ |- _ =>
    lazymatch A with Zpos _ => idtac | _ => fail end;
    lazymatch eval vm_compute in (0xee160 <=? A)%Z with true => idtac | false => fail end;
    move H at bottom;
    lazymatch type of H with ?T => change T with (sf_hide T) in H end
  end; sf_unhide.
Local Ltac hstep := raise_high; step.
Local Ltac bstep := hstep; try first [if_lit | if_refl | if_true | if_false].

Section Fflush.
  Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
  Hypothesis get_set : forall s so, get_so (set_so so s) = so.
  Hypothesis set_set : forall s so so', set_so so' (set_so so s) = set_so so' s.
  Hypothesis set_get : forall s, set_so (get_so s) s = s.

  Definition fflush_so_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (lo : Z) (guard : word) (m : word -> option byte) (st : St) : unit -> St -> machine_state -> Prop :=
    fun _ st' ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (so' : stdout_st) (flags mode : word) (tail : list byte) (m' : word -> option byte),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom usegs)
      /\ munch [(bv_unsigned sp - 176, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
      /\ stk usegs m' lo (bv_unsigned sp)
      /\ st' = set_so so' st /\ so_buf so' = []
      /\ rw_cells usegs m' RSTDOUT (file_cells flags 0 0 0 (wfn_of so') RSTDOUT_BUF 1024 1 mode (lbf_of so') tail)
      /\ Z.land (bv_unsigned flags) 72 = 0%Z              (* [comment removed for export] *)
      /\ ssp_cells m' guard.

  Lemma fflush_stdout_spec :
    forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (s : St) (guard : word),
      stk usegs m lo (bv_unsigned sp) ->
      stdout_file m (get_so s) ->
      rw_cells usegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] -> rw_cells usegs m ssp_guard [C8 guard] ->
      mem_inv usegs m ->
      a0 = Z_to_bv 64 RSTDOUT ->
      (lo <= bv_unsigned sp - 176)%Z -> (GLOBALS_TOP <= lo)%Z ->
      (bv_unsigned sp < 2^47)%Z ->
      implM usegs (stdout_exit_flush get_so set_so) s
            (fflush_so_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo guard m s)
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0xc2d20) fc None m (seg_rom usegs)).
  Proof.
    intros until guard. intros ST SOF GOT GUARD MI -> LO GLO SP47.
    unfold GLOBALS_TOP, got_ssp, ssp_guard in *.
    destruct SOF as (flags & mode & tail & bufbytes & FC & FL72 & BUF & BUFP & BUFL & INACT).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    remember (get_so s) as so eqn:ESO.
    pose proof (munch_refl [(bv_unsigned sp - 176, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232)]%Z m) as MU.
    pose proof (wmono_refl usegs m) as WM.
    assert (FL64 : Z.land (bv_unsigned flags) 64 = 0).
    { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
      destruct (Z.eq_dec i 6) as [->|NE].
      - pose proof (f_equal (fun z => Z.testbit z 6) FL72) as T. cbn beta in T. rewrite Z.land_spec, Z.bits_0 in T.
        change (Z.testbit 64 6) with true in T |- *. change (Z.testbit 72 6) with true in T. exact T.
      - change 64 with (2^6). rewrite Z.pow2_bits_eqb by lia.
        destruct (Z.eqb_spec 6 i); [lia|]. apply Bool.andb_false_r. }
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32)) = bv_unsigned sp + -32) by (apply unsigned_lit; clear - RSP LO GLO; lia).
    assert (LTB : length (to_bytes (so_buf so)) = length (so_buf so)) by (unfold to_bytes; apply length_map).
    unfold file_cells in FC.
    unfold implM, stdout_exit_flush. apply (implM_rdso usegs get_so). rewrite <- ESO.
    eapply (implM_evt usegs). 2:{ intros ms' H; exact H. } cbv beta.
    carve_frame 32%nat ST.
    do 5 hstep.
    (* [comment removed for export] *)
    bstep. bstep. bstep. bstep.
    hstep. hstep. hstep.
    destruct (0 <? zlength (so_buf so)) eqn:CF.
    - (* [comment removed for export] *)
      pose proof (proj1 (Z.ltb_lt _ _) CF) as CF'.
      assert (ACT : so_active so = true).
      { destruct (so_active so) eqn:E; [reflexivity|]. exfalso. rewrite (INACT eq_refl) in CF'. unfold zlength in CF'. cbn in CF'. clear - CF'. lia. }
      rewrite ACT in FC |- *.
      hstep. if_cases Hq; zify_cond Hq. 1:{ exfalso. unfold zlength in *. clear - Hq CF'. lia. }
      do 4 hstep. hstep.
      rewrite (ret_pc_even _) by (destruct (so_first so); cbn; lia).
      replace (Z_to_bv 64 (if so_first so then 803164 else 798980) : word) with (Z_to_bv 64 (wfn_of (get_so s)) : word)
        by (rewrite <- ESO; reflexivity).
      apply evt_done.
      eapply implM_post_evt'.
      { eapply (stdout_writefn_spec get_so set_so get_set set_set) with (lo := lo) (S := 0) (s := []) (flags := flags) (mode := mode) (tail := tail) (canary := guard);
          [ rewrite <- ESO; exact ACT
          | unfold stdout_cells, wfn_of, lbf_of, file_cells; rewrite <- ESO; exact FC
          | exact FL64
          | rewrite <- ESO; eapply CB_prefix_bytes_at; [exact BUF| rewrite LTB; exact BUFP]
          | rewrite <- ESO; exact BUFL
          | apply bytes_at_nil; clear; lia
          | reflexivity | reflexivity | reflexivity
          | rewrite ESP; exact ST | rewrite ESP; unfold STDOUT_WRITE_DEPTH; clear - LO; lia | exact GLO
          | split; [exact GOT | exact GUARD] | exact MI
          | clear; lia | unfold zlength; cbn; clear; lia
          | rewrite ESP; clear - SP47; lia | unfold zlength; cbn; clear; lia
          | left; reflexivity ]. }
      cbv beta. intros [] st2 ms2 PO2.
      destruct PO2 as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & -> & MU2 & WM2 & MI2 & ST2 & FC2 & SSP2 & ->).
      rewrite ESP in MU2, ST2. unfold STDOUT_WRITE_DEPTH in MU2. rewrite <- ESO in FC2 |- *.
      rewrite (ret_pc_even 798100) by (cbn; lia).
      transport_after_call usegs m1 m2 MU2 WM2.
      unfold stdout_cells, file_cells, wfn_of, lbf_of in FC2. cbn [so_active so_buf so_first so_lbf_nl so_after] in FC2.
      unfold zlength in FC2. cbn [length Z.of_nat] in FC2. rewrite Z.add_0_r in FC2.
      (* [comment removed for export] *)
      hstep. bstep.
      hstep. hstep. bstep.
      do 6 hstep. bstep.
      do 7 hstep.
      release_frame FR ST2 (bv_unsigned sp).
      apply evt_done. unfold fflush_so_post.
      do 14 eexists. exists (so_after so), flags, mode, tail. eexists.
      split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [exact MI2|]. split; [exact ST2|].
      split; [reflexivity|]. split; [reflexivity|].
      split; [unfold file_cells, wfn_of, lbf_of; cbn [so_active so_buf so_first so_lbf_nl so_after]; exact FC2|].
      split; [exact FL72|].
      unfold ssp_cells, got_ssp, ssp_guard. split; [exact GOT | exact GUARD].
    - (* [comment removed for export] *)
      pose proof (proj1 (Z.ltb_ge _ _) CF) as CF'.
      assert (E0 : so_buf so = []).
      { destruct (so_buf so); [reflexivity|]. exfalso. unfold zlength in CF'. cbn [length] in CF'. clear - CF'. lia. }
      rewrite E0 in *. unfold zlength. cbn [length Z.of_nat]. rewrite Z.add_0_r.
      unfold zlength in FC. cbn [length Z.of_nat] in FC. rewrite Z.add_0_r in FC.
      hstep. if_refl.
      hstep. hstep. bstep.
      do 6 hstep. bstep.
      do 7 hstep.
      release_frame FR ST (bv_unsigned sp).
      apply evt_done. apply evt_done. unfold fflush_so_post.
      do 14 eexists. exists so, flags, mode, tail. eexists.
      split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
      split; [rewrite ESO, set_get; reflexivity|]. split; [exact E0|].
      split; [unfold file_cells, wfn_of, lbf_of; exact FC|].
      split; [exact FL72|].
      unfold ssp_cells, got_ssp, ssp_guard. split; [exact GOT | exact GUARD].
  Qed.

  (* [comment removed for export] *)
  Definition fflush_se_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom usegs)
      /\ munch [(bv_unsigned sp - 32, bv_unsigned sp); (RSTDERR, RSTDERR + 232)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
      /\ stk usegs m' lo (bv_unsigned sp)
      /\ stderr_file m'.

  Lemma fflush_stderr_spec :
    forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
      stk usegs m lo (bv_unsigned sp) ->
      stderr_file m ->
      mem_inv usegs m ->
      a0 = Z_to_bv 64 RSTDERR ->
      (lo <= bv_unsigned sp - 32)%Z -> (GLOBALS_TOP <= lo)%Z ->
      evt usegs (fflush_se_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0xc2d20) fc None m (seg_rom usegs)).
  Proof.
    intros until lo. intros ST SEF MI -> LO GLO.
    unfold GLOBALS_TOP in *.
    destruct SEF as (eflags & emode & ee & ewend & etail & EFC).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (RSTDERR, RSTDERR + 232)]%Z m) as MU.
    pose proof (wmono_refl usegs m) as WM.
    unfold file_cells in EFC.
    carve_frame 32%nat ST.
    do 5 hstep.
    bstep. bstep. bstep. bstep.
    hstep. hstep. hstep. hstep. if_refl.
    hstep. hstep. bstep.
    do 6 hstep. bstep.
    do 7 hstep.
    release_frame FR ST (bv_unsigned sp).
    apply evt_done. unfold fflush_se_post.
    do 14 eexists. eexists.
    split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
    unfold stderr_file. exists eflags, emode, 0, 0, etail. unfold file_cells. exact EFC.
  Qed.
End Fflush.
