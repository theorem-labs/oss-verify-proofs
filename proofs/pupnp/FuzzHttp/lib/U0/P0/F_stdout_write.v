(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ITree Nodes Decode SysStep MonadX.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require Import Prelim Monad Stdio.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Stdio_base F_stdio_write.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition wfn_of (so : stdout_st) : Z := if so_first so then F_STDOUT_WRITE else F_STDIO_WRITE.
Definition lbf_of (so : stdout_st) : Z := if so_lbf_nl so then 10 else 0xffffffff.
Definition stdout_cells (so : stdout_st) (flags mode : word) (tail : list byte) : list cell :=
  file_cells flags (RSTDOUT_BUF + 1024) (RSTDOUT_BUF + zlength (so_buf so)) RSTDOUT_BUF (wfn_of so) RSTDOUT_BUF 1024 1 mode (lbf_of so) tail.

Definition STDOUT_WRITE_DEPTH : Z := 144.

Ltac fix_lit_store :=
  try (lazymatch goal with
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
           change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
           change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?z)) _) =>
           change (Z_to_le_bytes 1 z) with [Z_to_bv 8 z]; mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) =>
           change (le1 (Z_to_bv 64 z)) with [Z_to_bv 8 z]; mem_after_store
       end).
Ltac exact_frm := lazymatch goal with |- frm0 ?f => first [is_evar f; fail 1 "exact_frm: evar" | assumption] end.
Ltac rpc := apply ret_pc_even; [lia| reflexivity].

Lemma rw_cells_recast : forall m A cs cs',
  rw_cells rsegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> cells_size cs' = cells_size cs ->
  rw_cells rsegs m A cs'.
Proof. intros m A cs cs' [[Hwf Hb] Hw] Hwf' Eb Es. split; [split; [exact Hwf'| rewrite Eb; exact Hb] | rewrite Es; exact Hw]. Qed.
Lemma C4_low32 : forall (a b : word) , bv_unsigned a mod 2^32 = bv_unsigned b mod 2^32 -> cbytes (C4 a) = cbytes (C4 b).
Proof.
  intros a b E. cbn [cbytes]. unfold le4.
  rewrite <- (Z_to_le_bytes_mod 4 (bv_unsigned a) 32), <- (Z_to_le_bytes_mod 4 (bv_unsigned b) 32) by (cbn; lia).
  rewrite E. reflexivity.
Qed.
Lemma rw_cells_C4_eq : forall m A pre (a b : word) post,
  bv_unsigned a mod 2^32 = bv_unsigned b mod 2^32 ->
  rw_cells rsegs m A (pre ++ C4 a :: post) -> rw_cells rsegs m A (pre ++ C4 b :: post).
Proof.
  intros m A pre a b post E H. eapply rw_cells_recast; [exact H| | |].
  - destruct H as [[Hwf _] _]. apply cells_wf_app in Hwf. apply cells_wf_app. destruct Hwf as [H1 H2]. split; [exact H1|]. exact H2.
  - rewrite !cells_bytes_app. cbn [cells_bytes]. rewrite (C4_low32 a b E). reflexivity.
  - rewrite !cells_size_app. reflexivity.
Qed.

Ltac fix_lbf FC :=
  lazymatch type of FC with rw_cells ?sg ?m' ?A ?cs =>
    lazymatch cs with ?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?c11 :: ?c12 :: ?c13 :: ?c14 :: ?c15 :: ?c16 :: ?c17 :: ?c18 :: ?c19 :: ?c20 :: C4 (Z_to_bv 64 (-1)) :: ?rest =>
      apply (rw_cells_C4_eq m' A [c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11; c12; c13; c14; c15; c16; c17; c18; c19; c20]
               (Z_to_bv 64 (-1)) (Z_to_bv 64 4294967295) rest ltac:(vm_compute; reflexivity)) in FC
    end
  end.

Lemma rw_cells_C4_CB4 : forall m A (v : word) cs,
  rw_cells rsegs m A (C4 v :: cs) -> rw_cells rsegs m A (CB 4 (le4 v) :: cs).
Proof.
  intros m A v cs [[W B] R]. split; [split|].
  - cbn [cells_wf cell_wf] in *. split; [apply length_le4| exact (proj2 W)].
  - exact B.
  - exact R.
Qed.
Lemma firstn1_le4 : forall v : word, firstn 1 (skipn 0 (le4 v)) = le1 v.
Proof. intros v. reflexivity. Qed.

Lemma flags_byte_and64 : forall flags : word,
  Z.land (bv_unsigned flags) 64 = 0 -> Z.land (bv_unsigned flags mod 256) 64 = 0.
Proof.
  intros flags H. change 256 with (2 ^ 8). rewrite <- Z.land_ones by lia.
  rewrite (Z.land_comm _ (Z.ones 8)), <- Z.land_assoc, (Z.land_comm (Z.ones 8)), Z.land_ones by lia.
  rewrite H. reflexivity.
Qed.

Lemma rw_cells_CB4_C4 : forall m A (v : word) cs,
  rw_cells rsegs m A (CB 4 (le4 v) :: cs) -> rw_cells rsegs m A (C4 v :: cs).
Proof.
  intros m A v cs [[W B] R]. split; [split|].
  - cbn [cells_wf cell_wf] in *. split; [exact I| exact (proj2 W)].
  - exact B.
  - exact R.
Qed.

Section StdoutWrite.
  Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
  Hypothesis get_set : forall s so, get_so (set_so so s) = so.
  Hypothesis set_set : forall s so so', set_so so' (set_so so s) = set_so so' s.

  Definition so_after (so : stdout_st) : stdout_st :=
    mkStdout true [] (if so_first so then false else so_lbf_nl so) false.

  Definition stdout_writefn_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (flags mode : word) (tail : list byte) (l : Z) (lo : Z) (canary : word) (m : mem) (st : St)
      : unit -> St -> machine_state -> Prop :=
    fun _ st' ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 l) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom rsegs)
      /\ munch [(bv_unsigned sp - STDOUT_WRITE_DEPTH, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ stk rsegs m' lo (bv_unsigned sp)
      /\ rw_cells rsegs m' RSTDOUT (stdout_cells (so_after (get_so st)) flags mode tail)
      /\ ssp_cells m' canary
      /\ st' = set_so (so_after (get_so st)) st.

  #[using="get_set set_set"] Lemma stdout_writefn_spec :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St)
           (flags mode : word) (tail : list byte) (s : list Z) (S lo : Z) (canary : word),
      let so := get_so st in
      so_active so = true ->
      rw_cells rsegs m RSTDOUT (stdout_cells so flags mode tail) ->
      Z.land (bv_unsigned flags) 64 = 0 ->
      bytes_at rsegs m RSTDOUT_BUF (to_bytes (so_buf so)) -> (zlength (so_buf so) <= 1024) ->
      bytes_at rsegs m S (to_bytes s) ->
      a0 = Z_to_bv 64 RSTDOUT -> a1 = Z_to_bv 64 S -> a2 = Z_to_bv 64 (zlength s) ->
      stk rsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - STDOUT_WRITE_DEPTH) -> (0x5d000 <= lo) ->
      (bv_unsigned sp <= 2^47) ->
      ssp_cells m canary -> mem_inv rsegs m ->
      (zlength s + 1024 <= 2^24) -> (0 <= S < 2^64) -> (S + zlength s <= 2^47) ->
      (s = [] \/ ((S + zlength s <= lo \/ bv_unsigned sp <= S) /\ (S + zlength s <= RSTDOUT \/ RSTDOUT + 232 <= S))) ->
      implM rsegs (stdout_writefn get_so set_so s) st
            (stdout_writefn_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc flags mode tail (zlength s) lo canary m st)
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 (wfn_of so)) fc None m (seg_rom rsegs)).
  Proof.
    intros until canary. cbv zeta. intros ACT FC FL64 BUFB BUFL SRC -> -> -> ST LO GLO SP47 SSP MI LENS S0 Shi SEPS.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    destruct SSP as [GOT GUARD]. unfold got_ssp, ssp_guard, STDOUT_WRITE_DEPTH in *.
    pose proof (bytes_at_bound _ _ _ _ SRC) as BS. unfold to_bytes in BS. rewrite length_map in BS.
    assert (LSB : length (to_bytes s) = length s) by (unfold to_bytes; apply length_map).
    unfold stdout_writefn. apply implM_rdso.
    unfold stdout_cells, wfn_of, lbf_of in *.
    destruct (so_first (get_so st)) eqn:FIRST.
    -
      apply implM_bind_assoc. apply implM_updso. apply implM_bind_assoc.
      pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232)] m) as MU.
      pose proof (wmono_refl rsegs m) as WM.
      apply implM_sysk.
      change (bytes_at rsegs m S (to_bytes s)) with (boxed (bytes_at rsegs m S (to_bytes s))) in SRC.
      change (bytes_at rsegs m RSTDOUT_BUF (to_bytes (so_buf (get_so st)))) with (boxed (bytes_at rsegs m RSTDOUT_BUF (to_bytes (so_buf (get_so st))))) in BUFB.
      assert (LBB : length (to_bytes (so_buf (get_so st))) = length (so_buf (get_so st))) by (unfold to_bytes; apply length_map).
      unfold file_cells in FC. apply rw_cells_C4_CB4 in FC.
      carve_frame 32%nat ST.
      do 9 step. rewrite firstn1_le4, zext_extract_le1. unfold zx8.
      step. step. step. fix_lit_store. step.
      if_cases Hsvb; zify_cond Hsvb. 1:{ exfalso. exact (Hsvb (flags_byte_and64 flags FL64)). }
      do 10 step. step_ecall.
      replace (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1 : word) by (symmetry; apply sx32_small; lia).
      split. { at_node_red; split_spine; try reflexivity; try lia. }
      intros rsp ans Hdec. unfold dec_ioctl in Hdec. apply dec_plain_Some in Hdec.
      destruct ans as [e|v]. 2:{ exfalso. destruct Hdec as (_ & Hok & _). discriminate Hok. }
      destruct Hdec as [Hs He]. unfold efferr, eff0. cbv iota.
      apply implM_updso.

      unfold implM. apply impl_from_evt. sys_nret.
      do 5 step.
      if_cases He0; zify_cond He0. 1:{ exfalso. rewrite unsigned_errno_ret in He0 by lia. lia. }
      step. step.
      fix_lbf FC.
      step. apply evt_done.
      rewrite !get_set, !set_set. cbn [so_active so_buf so_first].
      unfold stdout_stdio_write. apply (implM_rdso rsegs get_so). rewrite get_set. cbn [so_buf].
      apply rw_cells_CB4_C4 in FC.
      eapply implM_bind.
      { eapply (stdio_write_spec (St:=St)) with (B := RSTDOUT_BUF) (fd := 1) (Fp := RSTDOUT) (buf := so_buf (get_so st)) (s := s) (S := S)
          (lo := lo) (canary := canary) (wend := RSTDOUT_BUF + 1024) (bufsize := 1024) (mode := mode) (lbf := 0xffffffff) (tail := tail)
          (flags := flags) (wfn := F_STDIO_WRITE); try reflexivity; rewrite ?unsigned_lit by lia.
        all: first [ exact FC | exact ST | exact MI | exact BUFL | split; [exact GOT | exact GUARD]
                   | lia | unfold STDIO_WRITE_DEPTH; lia | unfold got_ssp; lia | unfold ssp_guard; lia
                   | unfold boxed in BUFB; apply (bytes_at_transport _ _ _ _ _ _ BUFB MU); cbn [disjoint_from]; rewrite LBB; unfold zlength in BUFL; lia
                   | destruct SEPS as [-> | [S1 S2]]; [left; reflexivity | right; split; lia]
                   | src_now SRC SEPS MU LSB ]. }
      cbv beta. intros [] st' ms' PO.
      destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & -> & MU2 & WM2 & MI2 & ST2 & FC2 & SSP2 & ->).
      rewrite !unsigned_lit in MU2, ST2 by lia.
      apply implM_upd. rewrite !get_set, !set_set. cbn [so_lbf_nl so_first].

      replace (ret_pc (Z_to_bv 64 0x1b2b4)) with (Z_to_bv 64 0x1b2b4 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      destruct SSP2 as [GOT2 GUARD2]. unfold got_ssp, ssp_guard in GOT2, GUARD2.
      assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp + -32) [CB 8 (firstn 8 (firstn 16 (firstn 24 junk))); C8 canary; C8 s0; C8 ra]).
      { eapply (rw_cells_transport rsegs _ _ m2); [exact FR | exact MU2 | exact WM2 | cbn; unfold STDIO_WRITE_DEPTH in *; lia]. }
      step. step. step. if_false. step. step. step. step.
      release_frame FR2 ST2 (bv_unsigned sp).
      unfold stdout_writefn_post, so_after, stdout_cells, wfn_of, lbf_of, file_cells. rewrite FIRST. cbn [so_first so_buf so_lbf_nl].
      sys_finish.
      + apply (munch_trans _ m m0 m2).
        * eapply munch_weaken; [| exact MU]. unfold sub_fp, STDIO_WRITE_DEPTH, STDOUT_WRITE_DEPTH in *; cbn [outside]; intros; lia.
        * eapply munch_weaken; [| exact MU2]. unfold sub_fp, STDIO_WRITE_DEPTH, STDOUT_WRITE_DEPTH in *; cbn [outside]; intros; lia.
      + eapply wmono_trans; [exact WM | exact WM2].
      + split; [exact GOT2 | exact GUARD2].
      + rewrite ?set_set. reflexivity.
    -
      apply (implM_retb rsegs). unfold stdout_stdio_write. apply (implM_rdso rsegs get_so).
      pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232)] m) as MU.
      assert (LBB : length (to_bytes (so_buf (get_so st))) = length (so_buf (get_so st))) by (unfold to_bytes; apply length_map).
      eapply implM_bind.
      { eapply (stdio_write_spec (St:=St)) with (B := RSTDOUT_BUF) (fd := 1) (Fp := RSTDOUT) (buf := so_buf (get_so st)) (s := s) (S := S)
          (lo := lo) (canary := canary) (wend := RSTDOUT_BUF + 1024) (bufsize := 1024) (mode := mode) (lbf := if so_lbf_nl (get_so st) then 10 else 4294967295) (tail := tail)
          (flags := flags) (wfn := F_STDIO_WRITE); try reflexivity; rewrite ?unsigned_lit by lia.
        all: try first [ exact FC | exact ST | exact MI | exact BUFL | exact BUFB | exact SRC | split; [exact GOT | exact GUARD]
                   | lia | unfold STDIO_WRITE_DEPTH in *; lia | unfold got_ssp; lia | unfold ssp_guard; lia ].
        destruct SEPS as [-> | [S1 S2]]; [left; reflexivity | right; split; lia]. }
      cbv beta. intros [] st' ms' PO.
      destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & -> & MU2 & WM2 & MI2 & ST2 & FC2 & SSP2 & ->).
      apply implM_upd. apply evt_done. rewrite ?get_set.
      unfold stdout_writefn_post, so_after, stdout_cells, wfn_of, lbf_of, file_cells. rewrite FIRST. cbn [so_first so_buf so_lbf_nl].
      sys_finish.
      + eapply munch_weaken; [| exact MU2]. unfold sub_fp, STDIO_WRITE_DEPTH, STDOUT_WRITE_DEPTH in *; cbn [outside]; intros; lia.
      + rewrite ?set_set. reflexivity.
  Qed.
End StdoutWrite.
