(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac ITree Nodes Decode SysStep.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import SFModel.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import MonadX.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import Prelim Monad Stdio Prog.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import F_syscalls StdioFiles Stdio_kit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import F_fmt_fp_lib.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import F_stdio_write F_stdout_write F_fwritex_stdout.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma bv_eqb_refl : forall {n} (x : bv n), bv_eqb x x = true.
Proof. intros n x. unfold bv_eqb. apply Z.eqb_refl. Qed.

Ltac if_refl :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if bv_eqb ?x ?x then _ else _) _ _ _ _) => rewrite (bv_eqb_refl x); cbv iota
  end.

Ltac if_lit :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => let v := eval vm_compute in c in change c with v; cbv iota
  end.

(* [comment removed for export] *)
Lemma impl_post_evt' : forall {R} (t : itree node R) (Q Q' : R -> machine_state -> Prop) ms,
  impl usegs (at_node usegs) t Q ms -> (forall r ms', Q r ms' -> evt usegs (Q' r) ms') ->
  impl usegs (at_node usegs) t Q' ms.
Proof.
  induction t as [r|n k IH]; intros Q Q' ms H HQ; cbn in *.
  - eapply evt_cut; [exact H|]. intros ms' H'. apply HQ. exact H'.
  - eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. eapply IH; eauto.
Qed.
Lemma implM_post_evt' : forall {St A} (c : M St A) s Q Q' ms,
  implM usegs c s Q ms -> (forall a s' ms', Q a s' ms' -> evt usegs (Q' a s') ms') ->
  implM usegs c s Q' ms.
Proof.
  intros St A c s Q Q' ms H HQ. unfold implM in *. eapply impl_post_evt'; [exact H|].
  intros [|[a s']] ms' H'; cbn in *; [apply evt_done; exact I| apply HQ; exact H'].
Qed.

Section StdioExit.
  Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
  Hypothesis get_set : forall s so, get_so (set_so so s) = so.
  Hypothesis set_set : forall s so so', set_so so' (set_so so s) = set_so so' s.
  Hypothesis set_get : forall s, set_so (get_so s) s = s.

  Theorem stdio_exit_proof : stdio_exit_spec_stmt get_so set_so.
  Proof.
    unfold stdio_exit_spec_stmt. intros until tm1. intros ST LIBC OFL SIN SOUT SERR SOF SEF GOT GUARD MI -> LO GLO SP47.
    unfold GLOBALS_TOP, got_ssp, ssp_guard in *.
    destruct SOF as (flags & mode & tail & bufbytes & FC & FL72 & BUF & BUFP & BUFL & INACT).
    destruct SEF as (eflags & emode & ee & ewend & etail & EFC).
    change usegs with usegs in *.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    remember (get_so s) as so eqn:ESO.
    pose proof (munch_refl [(bv_unsigned sp - 160, bv_unsigned sp); (RSTDOUT, 0x38090); (RSTDOUT_BUF, 0x68cd0)]%Z m) as MU.
    pose proof (wmono_refl usegs m) as WM.
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
    unfold implM, stdout_exit_flush. apply (implM_rdso usegs get_so). rewrite <- ESO.
    eapply (implM_evt usegs). 2:{ intros ms' H; exact H. } cbv beta.
    carve_frame 16%nat ST.
    do 4 step.
    (* [comment removed for export] *)
    carve_frame 16%nat ST.
    step. step. fix_lit_store. do 5 step.
    do 3 step. change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). if_true.
    step.
    do 5 step.
    release_frame FR0 ST (bv_unsigned sp + -16).
    (* [comment removed for export] *)
    step. step. if_false.
    step. step. step. if_true.
    (* [comment removed for export] *)
    step. step. step. if_false.
    step. step. if_lit.
    step. step.
    destruct (0 <? zlength (so_buf so)) eqn:CF.
    - (* [comment removed for export] *)
      pose proof (proj1 (Z.ltb_lt _ _) CF) as CF'.
      assert (ACT : so_active so = true).
      { destruct (so_active so) eqn:E; [reflexivity|]. exfalso. rewrite (INACT eq_refl) in CF'. unfold zlength in CF'. cbn in CF'. clear - CF'. lia. }
      rewrite ACT in FC |- *.
      step. if_cases Hq; zify_cond Hq. 1:{ exfalso. unfold zlength in *. clear - Hq CF'. lia. }
      do 4 step. step.
      rewrite (ret_pc_even _) by (destruct (so_first so); cbn; lia).
      replace (Z_to_bv 64 (if so_first so then 198668 else 198260) : word) with (Z_to_bv 64 (wfn_of (get_so s)) : word)
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
      rewrite (ret_pc_even 197908) by (cbn; lia).
      transport_after_call usegs m1 m2 MU2 WM2.
      unfold stdout_cells, file_cells in FC2.
      (* [comment removed for export] *)
      step. step. step. if_lit.
      (* [comment removed for export] *)
      step. step. step. if_lit.
      step. step. if_lit.
      step. step. step. if_refl.
      step. step. step. if_lit.
      (* [comment removed for export] *)
      step. step. step. step.
      release_frame FR ST2 (bv_unsigned sp).
      apply evt_done. unfold stdio_exit_post.
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
      destruct SSP2 as [GOT2 GUARD2]. change usegs with usegs in GOT2, GUARD2. split; [exact GOT2 | exact GUARD2].
    - (* [comment removed for export] *)
      pose proof (proj1 (Z.ltb_ge _ _) CF) as CF'.
      assert (E0 : so_buf so = []).
      { destruct (so_buf so); [reflexivity|]. exfalso. unfold zlength in CF'. cbn [length] in CF'. clear - CF'. lia. }
      rewrite E0 in *. unfold zlength. cbn [length Z.of_nat]. rewrite Z.add_0_r.
      unfold zlength in FC. cbn [length Z.of_nat] in FC. rewrite Z.add_0_r in FC.
      step. if_refl.
      step. step. step. if_lit.
      (* [comment removed for export] *)
      step. step. step. if_lit.
      step. step. if_lit.
      step. step. step. if_refl.
      step. step. step. if_lit.
      step. step. step. step.
      release_frame FR ST (bv_unsigned sp).
      apply evt_done. apply evt_done. unfold stdio_exit_post.
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
Theorem stdio_exit_proof_ps : stdio_exit_spec_stmt ps_so set_so_ps.
Proof.
  apply stdio_exit_proof.
  - intros s so. reflexivity.
  - intros s so so'. reflexivity.
  - intros [mm b f so]. reflexivity.
Qed.
