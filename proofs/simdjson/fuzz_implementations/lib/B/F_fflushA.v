(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac ITree Nodes Decode SysStep MonadX ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import Prelim Monad Stdio.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.P Require Import Str_tac Startup_glue.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import FX_Layout FX_Stdio_iface F_stdio_write F_stdout_write F_stdio_exit.
From OssFuzzTheorems.simdjson.fuzz_implementations.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Notation bsegs := ImageA.bsegs.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition F_FFLUSH : Z := 0x168400.
Definition FFLUSH_DEPTH : Z := 176.

Section Fflush.
  Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
  Hypothesis get_set : forall s so, get_so (set_so so s) = so.
  Hypothesis set_set : forall s so so', set_so so' (set_so so s) = set_so so' s.
  Hypothesis set_get : forall s, set_so (get_so s) s = s.

  Definition stdout_idle_cells (so' : stdout_st) (flags mode : word) (tail : list byte) : list cell :=
    file_cells flags 0 0 0 (wfn_of so') RSTDOUT_BUF 1024 1 mode (lbf_of so') tail.

  Definition fflush_stdout_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (flags mode : word) (tail : list byte) (lo : Z) (canary : word) (m : mem) (st : St) : unit -> St -> machine_state -> Prop :=
    fun _ st' ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem) (so' : stdout_st),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom bsegs)
      /\ munch [(bv_unsigned sp - FFLUSH_DEPTH, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ stk bsegs m' lo (bv_unsigned sp)
      /\ so' = (if 0 <? zlength (so_buf (get_so st)) then so_after (get_so st) else get_so st)
      /\ st' = set_so so' st
      /\ rw_cells bsegs m' RSTDOUT (stdout_idle_cells so' flags mode tail)
      /\ ssp_cells m' canary.

  Definition fflush_stdout_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St)
           (flags mode : word) (tail : list byte) (bufbytes : list byte) (lo : Z) (canary : word),
      let so := get_so st in
      (so_active so = false -> so_buf so = []) ->
      rw_cells bsegs m RSTDOUT (stdout_cells so flags mode tail) ->
      Z.land (bv_unsigned flags) 72 = 0 ->
      rw_cells bsegs m RSTDOUT_BUF [CB 1024 bufbytes] -> firstn (length (so_buf so)) bufbytes = to_bytes (so_buf so) -> (zlength (so_buf so) <= 1024) ->
      a0 = Z_to_bv 64 RSTDOUT ->
      stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - FFLUSH_DEPTH) -> (GLOBALS_TOP <= lo) ->
      ssp_cells m canary -> mem_inv bsegs m ->
      implM bsegs (stdout_exit_flush get_so set_so) st
            (fflush_stdout_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc flags mode tail lo canary m st)
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 F_FFLUSH) fc None m (seg_rom bsegs)).

  Theorem fflush_stdout_proof : fflush_stdout_stmt.
  Proof.
    unfold fflush_stdout_stmt. intros until canary. cbv zeta. intros INACT FC FL72 BUF BUFP BUFL -> ST LO GLO SSP MI.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    remember (get_so st) as so eqn:ESO.
    unfold F_FFLUSH, FFLUSH_DEPTH, STDOUT_WRITE_DEPTH, GLOBALS_TOP in *.
    pose proof (munch_refl [(bv_unsigned sp - 176, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232)]%Z m) as MU.
    pose proof (wmono_refl bsegs m) as WM.
    assert (FL64 : Z.land (bv_unsigned flags) 64 = 0).
    { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
      destruct (Z.eq_dec i 6) as [->|NE].
      - pose proof (f_equal (fun z => Z.testbit z 6) FL72) as T. cbn beta in T. rewrite Z.land_spec, Z.bits_0 in T.
        change (Z.testbit 64 6) with true in T |- *. change (Z.testbit 72 6) with true in T. exact T.
      - change 64 with (2^6). rewrite Z.pow2_bits_eqb by lia.
        destruct (Z.eqb_spec 6 i); [lia|]. apply Bool.andb_false_r. }
    assert (LTB : length (to_bytes (so_buf so)) = length (so_buf so)) by (unfold to_bytes; apply length_map).
    destruct SSP as [GOT GUARD]. unfold got_ssp, ssp_guard in GOT, GUARD.
    unfold stdout_cells, file_cells, wfn_of, lbf_of in FC.
    unfold implM, stdout_exit_flush. apply (implM_rdso get_so). rewrite <- ESO.
    eapply (implM_evt bsegs). 2:{ intros ms' H; exact H. } cbv beta.
    carve_frame 32%nat ST.
    do 5 step.
    step. if_false.
    step. step.
    step. if_true.
    step.
    step. step.
    destruct (0 <? zlength (so_buf so)) eqn:CF.
    -
      pose proof (proj1 (Z.ltb_lt _ _) CF) as CF'.
      assert (ACT : so_active so = true).
      { destruct (so_active so) eqn:E; [reflexivity|]. exfalso. rewrite (INACT eq_refl) in CF'. unfold zlength in CF'. cbn in CF'. clear - CF'. lia. }
      step. if_cases Hq; zify_cond Hq. 1:{ exfalso. unfold zlength in *. clear - Hq CF'. lia. }
      do 4 step. step.
      rewrite (ret_pc_even _) by (destruct (so_first so); cbn; lia).
      lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?p) _ _ _ _) =>
        replace (Z_to_bv 64 p : word) with (Z_to_bv 64 (wfn_of (get_so st)) : word) by (rewrite <- ESO; reflexivity) end.
      apply evt_done.
      eapply implM_post_evt'.
      { assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32)) = bv_unsigned sp + -32) by (apply unsigned_lit; clear - RSP LO GLO; lia).
        eapply (stdout_writefn_proof get_so set_so get_set set_set) with (lo := lo) (S := 0) (s := []) (flags := flags) (mode := mode) (tail := tail) (canary := canary);
          [ rewrite <- ESO; exact ACT
          | unfold stdout_cells, wfn_of, lbf_of, file_cells; rewrite <- ESO; hyp_by_addr
          | exact FL64
          | rewrite <- ESO; eapply CB_prefix_bytes_at; [hyp_by_addr| rewrite LTB; exact BUFP]
          | rewrite <- ESO; exact BUFL
          | apply bytes_at_nil; clear; lia
          | reflexivity | reflexivity | reflexivity
          | rewrite ESP; exact ST | rewrite ESP; unfold STDOUT_WRITE_DEPTH; clear - LO; lia | unfold GLOBALS_TOP; exact GLO
          | split; [exact GOT | exact GUARD] | assumption
          | unfold zlength; cbn; clear; lia | clear; lia | unfold zlength; cbn; clear; lia
          | left; reflexivity
          | left; reflexivity ]. }
      cbv beta. intros [] st2 ms2 PO2.
      destruct PO2 as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & -> & MU2 & WM2 & MI2 & ST2 & FC2 & SSP2 & ->).
      destruct SSP2 as [GOT2 GUARD2]. unfold got_ssp, ssp_guard in GOT2, GUARD2.
      unfold STDOUT_WRITE_DEPTH in MU2. rewrite <- ESO in FC2 |- *.
      replace (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32))) with (bv_unsigned sp + -32) in MU2, ST2 by (symmetry; apply unsigned_lit; clear - RSP LO GLO; lia).
      lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?r)] => rewrite (ret_pc_even r) by (cbn; lia) end.
      transport_after_call bsegs m1 m2 MU2 WM2.
      unfold stdout_cells, file_cells in FC2. cbn [so_after so_buf so_active so_first so_lbf_nl zlength length Z.of_nat] in FC2.
      rewrite Z.add_0_r in FC2.
      step. step. if_lit.
      step. step. step. if_lit.
      step.
      lstep. lstep. lstep. lstep. lstep.
      step. if_true.
      step. step. step. step. step. step.
      release_frame FR ST2 (bv_unsigned sp).
      step.
      apply evt_done. unfold fflush_stdout_post.
      do 15 eexists. exists (so_after so).
      split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [assumption|].
      split; [rewrite <- ESO, CF; reflexivity|]. split; [reflexivity|].
      split; [| unfold ssp_cells, got_ssp, ssp_guard; split; assumption].
      unfold stdout_idle_cells, file_cells, wfn_of, lbf_of. cbn [so_after so_first so_lbf_nl]. hyp_by_addr.
    -
      pose proof (proj1 (Z.ltb_ge _ _) CF) as CF'.
      assert (E0 : so_buf so = []).
      { destruct (so_buf so); [reflexivity|]. exfalso. unfold zlength in CF'. cbn [length] in CF'. clear - CF'. lia. }
      rewrite E0 in *. unfold zlength. cbn [length Z.of_nat]. rewrite Z.add_0_r.
      unfold zlength in FC. cbn [length Z.of_nat] in FC. rewrite Z.add_0_r in FC.
      step. if_refl.
      step. step. step. if_lit.
      step.
      lstep. lstep. lstep. lstep. lstep.
      step. if_true.
      step. step. step. step. step. step.
      release_frame FR ST (bv_unsigned sp).
      step.
      apply evt_done. apply evt_done. unfold fflush_stdout_post.
      do 15 eexists. exists so.
      split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [assumption|].
      split; [rewrite <- ESO, E0; reflexivity|]. split; [rewrite ESO, set_get; reflexivity|].
      split; [| unfold ssp_cells, got_ssp, ssp_guard; split; assumption].
      unfold stdout_idle_cells, file_cells, wfn_of, lbf_of. hyp_by_addr.
  Qed.
End Fflush.

Definition fflush_idle_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Fp : Z) (flags mode : word) (wfn bufp bufsize fd lbf : Z) (tail : list byte) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp); (Fp, Fp + 64)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' Fp (file_cells flags 0 0 0 wfn bufp bufsize fd mode lbf tail).

Lemma fflush_idle_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (Fp : Z) (flags mode : word) (wend wpos wfn bufp bufsize fd lbf : Z) (tail : list byte) (lo : Z),
  rw_cells bsegs m Fp (file_cells flags wend wpos wpos wfn bufp bufsize fd mode lbf tail) ->
  a0 = Z_to_bv 64 Fp -> (0 < Fp) -> (Fp + 232 <= lo) -> (0 <= wpos < 2^64) ->
  stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 32) -> (GLOBALS_TOP <= lo) ->
  mem_inv bsegs m ->
  evt bsegs (fflush_idle_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp flags mode wfn bufp bufsize fd lbf tail lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 F_FFLUSH) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros FC -> Fp0 SEPF WP ST LO GLO MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  unfold F_FFLUSH, GLOBALS_TOP in *.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (Fp, Fp + 64)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  unfold file_cells in FC.
  carve_frame 32%nat ST.
  do 5 lstep.
  step. if_cases Hf; zify_cond Hf. 1:{ exfalso. clear - Hf Fp0 SEPF LO RSP. try rewrite unsigned_lit in Hf by lia. lia. }
  step. step.
  step. if_lit.
  step.
  step. step.
  step. if_refl.
  step. step. step. if_lit.
  step.
  lstep. lstep. lstep. lstep. lstep.
  step. if_true.
  step. step. step. step. step. step.
  release_frame FR ST (bv_unsigned sp).
  step.
  apply evt_done. unfold fflush_idle_post. sys_finish.
Qed.
