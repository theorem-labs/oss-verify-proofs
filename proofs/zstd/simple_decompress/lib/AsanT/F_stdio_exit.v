(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac ITree Nodes Decode SysStep.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import SFModel.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import Prelim Monad Stdio Prog.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import F_syscalls StdioFiles Stdio_kit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import F_fmt_fp_lib.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import F_stdio_write F_stdout_write F_fwritex_stdout.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg MonadF AExit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ITreeA StepF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.
Lemma bv_eqb_refl : forall {n} (x : bv n), bv_eqb x x = true.
Proof. intros n x. unfold bv_eqb. apply Z.eqb_refl. Qed.

End CANSEC1.
Ltac if_refl :=
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ (if bv_eqb ?x ?x then _ else _) _ _ _ _) => rewrite (bv_eqb_refl x); cbv iota
  end.

Ltac if_lit :=
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => let v := eval vm_compute in c in change c with v; cbv iota
  end.

(* [comment removed for export] *)
Ltac raise_high :=
  repeat match goal with H : rw_cells bsegs _ ?A _ |- _ =>
    lazymatch A with Zpos _ => idtac | _ => fail end;
    lazymatch eval vm_compute in (0x5f4740 <=? A)%Z with true => idtac | false => fail end;
    move H at bottom;
    lazymatch type of H with ?T => change T with (sf_hide T) in H end
  end; sf_unhide.
Ltac hstep := raise_high; step.

Section CANSEC2. Context {rc : runConstT}.
Section StdioExit.
  Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
  Hypothesis get_set : forall s so, get_so (set_so so s) = so.
  Hypothesis set_set : forall s so so', set_so so' (set_so so s) = set_so so' s.
  Hypothesis set_get : forall s, set_so (get_so s) s = s.

  Theorem stdio_exit_proof : stdio_exit_spec_stmt2 get_so set_so.
  Proof.
    unfold stdio_exit_spec_stmt2. intros until tm1. intros ST LIBC OFL SIN SINF SOUT SERR SOF SEF GOT GUARD MI -> LO GLO RSTK RIMG RG0 SP47.
    unfold GLOBALS_TOP, got_ssp, ssp_guard, RSTDIN, stdin_cells in *.
    destruct SOF as (flags & mode & tail & bufbytes & FC & FL72 & BUF & BUFP & BUFL & INACT).
    destruct SEF as (eflags & emode & ee & ewend & etail & EFC).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    remember (get_so s) as so eqn:ESO.
    pose proof (munch_refl [(bv_unsigned sp - 160, bv_unsigned sp); (RSTDOUT, 0xcbae0); (RSTDOUT_BUF, 0x6237c0)]%Z m) as MU.
    pose proof (wmono_refl bsegs m) as WM.
    assert (FL64 : Z.land (bv_unsigned flags) 64 = 0).
    { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
      destruct (Z.eq_dec i 6) as [->|NE].
      - pose proof (f_equal (fun z => Z.testbit z 6) FL72) as T. cbn beta in T. rewrite Z.land_spec, Z.bits_0 in T.
        change (Z.testbit 64 6) with true in T |- *. change (Z.testbit 72 6) with true in T. exact T.
      - change 64 with (2^6). rewrite Z.pow2_bits_eqb by lia.
        destruct (Z.eqb_spec 6 i); [lia|]. apply Bool.andb_false_r. }
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -16)) = bv_unsigned sp + -16) by (apply unsigned_lit; clear - RSP LO GLO; lia).
    assert (LTB : length (to_bytes (so_buf so)) = length (so_buf so)) by (unfold to_bytes; apply length_map).
    unfold file_cells in FC, EFC.
    unfold stdout_exit_flush. apply (implAM_rdso get_so). rewrite <- ESO.
    eapply implAM_evt. 2:{ intros ms' H; exact H. } cbv beta.
    carve_frame 16%nat ST.
    do 4 hstep.
    (* [comment removed for export] *)
    carve_frame 16%nat ST.
    hstep. hstep. fix_lit_store. do 5 hstep.
    do 3 hstep. change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). if_true.
    hstep.
    do 5 hstep.
    release_frame FR0 ST (bv_unsigned sp + -16).
    (* [comment removed for export] *)
    hstep. hstep. if_false.
    (* [comment removed for export] *)
    hstep. hstep. hstep. if_false.
    hstep. hstep. if_lit.
    hstep. hstep. hstep. if_lit.
    hstep. hstep. hstep. if_lit.
    (* [comment removed for export] *)
    hstep. hstep. hstep. if_false.
    hstep. hstep. if_lit.
    hstep. hstep.
    destruct (0 <? zlength (so_buf so)) eqn:CF.
    - (* [comment removed for export] *)
      pose proof (proj1 (Z.ltb_lt _ _) CF) as CF'.
      assert (ACT : so_active so = true).
      { destruct (so_active so) eqn:E; [reflexivity|]. exfalso. rewrite (INACT eq_refl) in CF'. unfold zlength in CF'. cbn in CF'. clear - CF'. lia. }
      rewrite ACT in FC |- *.
      hstep. if_cases Hq; zify_cond Hq. 1:{ exfalso. unfold zlength in *. clear - Hq CF'. lia. }
      do 4 hstep. hstep.
      rewrite (ret_pc_even _) by (destruct (so_first so); cbn; lia).
      replace (Z_to_bv 64 (if so_first so then 773432 else 770868) : word) with (Z_to_bv 64 (wfn_of (get_so s)) : word)
        by (rewrite <- ESO; reflexivity).
      apply evtF_done.
      eapply implAM_post_evt'.
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
          | left; reflexivity
          | rewrite ESP; eapply rng_sub'; [exact RSTK | clear - LO RSP; lia] | apply (rng0_use _ _ RG0); clear; lia | exact RIMG
          | rewrite ESP; clear - SP47; lia | unfold zlength; cbn; clear; lia ]. }   (* [comment removed for export] *)
      cbv beta. intros [] st2 ms2 PO2.
      destruct PO2 as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & -> & MU2 & WM2 & MI2 & ST2 & FC2 & SSP2 & ->).
      rewrite ESP in MU2, ST2. unfold STDOUT_WRITE_DEPTH in MU2. rewrite <- ESO in FC2 |- *.
      rewrite (ret_pc_even 772548) by (cbn; lia).
      transport_after_call bsegs m1 m2 MU2 WM2.
      unfold stdout_cells, file_cells in FC2.
      (* [comment removed for export] *)
      hstep. hstep. hstep. if_lit.
      (* [comment removed for export] *)
      hstep. hstep. hstep. if_lit.
      hstep. hstep. if_lit.
      hstep. hstep. hstep. if_refl.
      hstep. hstep. hstep. if_lit.
      (* [comment removed for export] *)
      hstep. hstep. hstep. hstep.
      release_frame FR ST2 (bv_unsigned sp).
      apply evtF_done. unfold stdio_exit_post.
      do 15 eexists. exists (so_after so). eexists.
      split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [exact MI2|]. split; [exact ST2|].
      split; [reflexivity|].
      split.
      { unfold stdout_file. exists flags, mode, tail, bufbytes.
        unfold stdout_cells, wfn_of, lbf_of in FC2 |- *. cbn [so_active so_buf so_first so_lbf_nl so_after] in FC2 |- *.
        split; [exact FC2|]. split; [exact FL72|]. split; [exact BUF|]. split; [reflexivity|].
        split; [unfold zlength; cbn; clear; lia|]. intros X; discriminate X. }
      split; [reflexivity|].
      split; [exists eflags, emode, ee, ewend, etail; exact EFC|].
      destruct SSP2 as [GOT2 GUARD2]. split; [exact GOT2 | exact GUARD2].
    - (* [comment removed for export] *)
      pose proof (proj1 (Z.ltb_ge _ _) CF) as CF'.
      assert (E0 : so_buf so = []).
      { destruct (so_buf so); [reflexivity|]. exfalso. unfold zlength in CF'. cbn [length] in CF'. clear - CF'. lia. }
      rewrite E0 in *. unfold zlength. cbn [length Z.of_nat]. rewrite Z.add_0_r.
      unfold zlength in FC. cbn [length Z.of_nat] in FC. rewrite Z.add_0_r in FC.
      hstep. if_refl.
      hstep. hstep. hstep. if_lit.
      (* [comment removed for export] *)
      hstep. hstep. hstep. if_lit.
      hstep. hstep. if_lit.
      hstep. hstep. hstep. if_refl.
      hstep. hstep. hstep. if_lit.
      hstep. hstep. hstep. hstep.
      release_frame FR ST (bv_unsigned sp).
      apply evtF_done. apply implAM_ret. apply evtF_done. unfold stdio_exit_post.
      do 15 eexists. exists so. eexists.
      split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
      split; [rewrite ESO, set_get; reflexivity|].
      split.
      { unfold stdout_file. exists flags, mode, tail, bufbytes. rewrite E0. unfold zlength. cbn [length Z.of_nat]. rewrite Z.add_0_r.
        split; [exact FC|]. split; [exact FL72|]. split; [exact BUF|]. split; [reflexivity|].
        split; [clear; lia|]. intros _; reflexivity. }
      split; [exact E0|].
      split; [exists eflags, emode, ee, ewend, etail; exact EFC|].
      split; [exact GOT | exact GUARD].
  Qed.
End StdioExit.

(* [comment removed for export] *)
Theorem stdio_exit_proof_ps : stdio_exit_spec_stmt2 ps_so set_so_ps.
Proof.
  apply stdio_exit_proof.
  - intros s so. reflexivity.
  - intros s so so'. reflexivity.
  - intros [mm b f so]. reflexivity.
Qed.
End CANSEC2.
