(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Walk ITree Nodes Decode SysStep MonadX.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require Import Prelim Monad Stdio.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Stdio_base.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition STDIO_WRITE : Z := 0x1acfc.
Definition STDIO_WRITE_DEPTH : Z := 112.

Definition iovs_of (buf s : list Z) : list (list byte) :=
  match buf with [] => [to_bytes s] | _ => [to_bytes buf; to_bytes s] end.

Lemma to_bytes_skipn : forall i l, to_bytes (skipn i l) = skipn i (to_bytes l).
Proof. intros. unfold to_bytes. rewrite skipn_map. reflexivity. Qed.

Lemma bytes_at_skipn : forall segs m A bs i, bytes_at segs m A bs -> (i <= length bs)%nat ->
  bytes_at segs m (A + Z.of_nat i) (skipn i bs).
Proof.
  intros segs m A bs i H Hi. rewrite <- (firstn_skipn i bs) in H. apply bytes_at_app in H as [_ H].
  rewrite length_firstn in H. replace (Nat.min i (length bs)) with i in H by lia. exact H.
Qed.

Lemma frame_iov1 : forall m base j0 x8 x16 a b c6 c7 c8 c9 c10 c11 c12 c13 c14,
  rw_cells rsegs m base [CB 8 j0; C8 x8; C8 x16; C8 a; C8 b; C8 c6; C8 c7; C8 c8; C8 c9; C8 c10; C8 c11; C8 c12; C8 c13; C8 c14] ->
  bytes_at rsegs m (base + 24) (iovec_bytes [(a, b)]).
Proof.
  intros. change (rw_cells rsegs m base ([CB 8 j0; C8 x8; C8 x16] ++ [C8 a; C8 b] ++ [C8 c6; C8 c7; C8 c8; C8 c9; C8 c10; C8 c11; C8 c12; C8 c13; C8 c14])) in H.
  apply (proj1 (rw_cells_app _ _ _ _ _)) in H as [_ H]. apply (proj1 (rw_cells_app _ _ _ _ _)) in H as [H _].
  destruct H as [[WF HB] _]. cbn [cells_wf cell_wf] in WF. cbn [cells_size csize Nat.add] in HB.
  cbn [cells_bytes cbytes iovec_bytes flat_map fst snd app] in HB |- *. rewrite app_nil_r. exact HB.
Qed.

Lemma frame_iov2 : forall m base j0 x8 x16 a b c6 c7 c8 c9 c10 c11 c12 c13 c14,
  rw_cells rsegs m base [CB 8 j0; C8 x8; C8 x16; C8 a; C8 b; C8 c6; C8 c7; C8 c8; C8 c9; C8 c10; C8 c11; C8 c12; C8 c13; C8 c14] ->
  bytes_at rsegs m (base + 8) (iovec_bytes [(x8, x16); (a, b)]).
Proof.
  intros. change (rw_cells rsegs m base ([CB 8 j0] ++ [C8 x8; C8 x16; C8 a; C8 b] ++ [C8 c6; C8 c7; C8 c8; C8 c9; C8 c10; C8 c11; C8 c12; C8 c13; C8 c14])) in H.
  apply (proj1 (rw_cells_app _ _ _ _ _)) in H as [_ H]. apply (proj1 (rw_cells_app _ _ _ _ _)) in H as [H _].
  destruct H as [[WF HB] _]. cbn [cells_wf cell_wf] in WF. cbn [cells_size csize Nat.add] in HB.
  cbn [cells_bytes cbytes iovec_bytes flat_map fst snd] in HB |- *.
  rewrite ?app_nil_r, <- ?app_assoc in HB |- *. exact HB.
Qed.

Lemma sub_fp_stdio : forall a b Fp, sub_fp [(a, b)] [(a, b); (Fp + 32, Fp + 64)].
Proof. intros a b Fp x. cbn. lia. Qed.

Section StdioWrite.
  Context {St : Type}.

  Definition stdio_write_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (Fp : Z) (flags : word) (B bufsize wfn fd : Z) (mode : word) (lbf : Z) (tail : list byte)
      (l : Z) (lo : Z) (canary : word) (m : mem) (st : St) : unit -> St -> machine_state -> Prop :=
    fun _ st' ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 l) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom rsegs)
      /\ munch [(bv_unsigned sp - STDIO_WRITE_DEPTH, bv_unsigned sp); (Fp + 32, Fp + 64)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ stk rsegs m' lo (bv_unsigned sp)
      /\ rw_cells rsegs m' Fp (file_cells flags (B + bufsize) B B wfn B bufsize fd mode lbf tail)
      /\ ssp_cells m' canary
      /\ st' = st.

  #[using="Type"] Lemma stdio_write_finish :
    forall (x1 sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2r s3r s4r s6r s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (ra s0 s1 s2 s3 s4 s5 s6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m0 m : mem) (st : St)
           (Fp : Z) (flags : word) (wend wpos wbase B bufsize wfn fd : Z) (mode : word) (lbf : Z) (tail : list byte)
           (j0 : list byte) (x8 x16 x24 x32 : word) (l lo : Z) (canary : word),
      rw_cells rsegs m (bv_unsigned sp + -112)
        [CB 8 j0; C8 x8; C8 x16; C8 x24; C8 x32; C8 canary; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      rw_cells rsegs m Fp (file_cells flags wend wpos wbase wfn B bufsize fd mode lbf tail) ->
      ssp_cells m canary ->
      stk rsegs m lo (bv_unsigned sp + -112) -> (0 <= lo <= bv_unsigned sp - 112) -> (bv_unsigned sp < 2^64) ->
      munch [(bv_unsigned sp - STDIO_WRITE_DEPTH, bv_unsigned sp); (Fp + 32, Fp + 64)] m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
      (0 <= Fp) -> (Fp + 232 <= lo) ->
      (Fp + 232 <= got_ssp \/ got_ssp + 8 <= Fp) -> (Fp + 232 <= ssp_guard \/ ssp_guard + 8 <= Fp) ->
      (0 <= B) -> (0 <= bufsize) -> (B + bufsize < 2^64) -> (0 <= l < 2^64) ->
      evt rsegs (stdio_write_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp flags B bufsize wfn fd mode lbf tail
                                  l lo canary m0 st tt st)
          (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0 t1 t2 (Z_to_bv 64 l) (Z_to_bv 64 Fp)
                   a0 a1 a2 a3 a4 a5 a6 a7 s2r s3r s4r (Z_to_bv 64 ssp_guard) s6r s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x1ad90) fc None m (seg_rom rsegs)).
  Proof.
    intros until canary. intros FR FC [GOT GUARD] ST LO SPHI MU WM MI Fp0 FPLO FSEP1 FSEP2 B0 BS0 BShi L.
    unfold got_ssp, ssp_guard, STDIO_WRITE_DEPTH, file_cells in *.
    do 6 step. step. step. step. step. if_false.
    do 10 step.
    release_frame FR ST (bv_unsigned sp).
    unfold stdio_write_post, file_cells, ssp_cells, got_ssp, ssp_guard. sys_finish. reflexivity.
  Qed.

  #[using="Type"] Lemma stdio_write_loop1 : forall fuel (b : list Z) (k A : Z)
           (x1 sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4r s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (ra s0 s1 s2 s3 s4 s5 s6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m0 m : mem) (st : St)
           (Fp : Z) (flags : word) (wend wpos wbase B bufsize wfn fd : Z) (mode : word) (lbf : Z) (tail : list byte)
           (j0 : list byte) (x8 x16 : word) (l lo : Z) (canary : word),
      rw_cells rsegs m (bv_unsigned sp + -112)
        [CB 8 j0; C8 x8; C8 x16; C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 (Z.of_nat (length b))); C8 canary;
         C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      rw_cells rsegs m Fp (file_cells flags wend wpos wbase wfn B bufsize fd mode lbf tail) ->
      ssp_cells m canary ->
      bytes_at rsegs m0 A (to_bytes b) -> (A + Z.of_nat (length b) <= lo \/ bv_unsigned sp <= A) ->
      stk rsegs m lo (bv_unsigned sp + -112) -> (0 <= lo <= bv_unsigned sp - 112) -> (0x5d000 <= lo) -> (bv_unsigned sp <= 2^47) ->
      munch [(bv_unsigned sp - 112, bv_unsigned sp)] m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
      (0 <= Fp) -> (Fp + 232 <= lo) ->
      (Fp + 232 <= got_ssp \/ got_ssp + 8 <= Fp) -> (Fp + 232 <= ssp_guard \/ ssp_guard + 8 <= Fp) ->
      (0 <= B) -> (0 <= bufsize) -> (B + bufsize < 2^64) -> (0 <= l < 2^64) ->
      (fd = 1 \/ fd = 2) -> (1 <= k < Z.of_nat (length b)) -> (Z.of_nat (length b) <= 2^24) -> (0 <= A) -> (A + Z.of_nat (length b) <= 2^47) ->
      implM rsegs (stdio_wloop (St:=St) fuel fd (advance [b] k)) st
            (stdio_write_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp flags B bufsize wfn fd mode lbf tail
                              l lo canary m0 st)
            (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0 t1 t2 (Z_to_bv 64 l) (Z_to_bv 64 Fp)
                     (Z_to_bv 64 k) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 1) (Z_to_bv 64 (bv_unsigned sp + -88)) s4r (Z_to_bv 64 ssp_guard)
                     (Z_to_bv 64 (Z.of_nat (length b))) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x1ae1c) fc None m (seg_rom rsegs)).
  Proof.
    induction fuel as [|fuel IH]; intros until canary;
      intros FR FC SSP SRC SEPA ST LO GLO SPHI MU WM MI Fp0 FPLO FSEP1 FSEP2 B0 BS0 BShi L FD K NB A0 AHI.
    { cbn [stdio_wloop]. apply implM_unr. }
    pose proof SSP as [GOT GUARD]. unfold got_ssp, ssp_guard in *.
    assert (LTB : length (to_bytes b) = length b) by apply to_bytes_length.
    set (n := Z.of_nat (length b)) in *.
    replace (advance [b] k) with [skipn (Z.to_nat k) b]
      by (unfold advance, zlength; fold n; destruct (Z.ltb_spec0 n k); [exfalso; lia| reflexivity]).
    cbn [stdio_wloop]. apply implM_sysk.
    replace (zlength (concat [skipn (Z.to_nat k) b])) with (n - k)
      by (unfold zlength; cbn [concat]; rewrite app_nil_r, length_skipn; lia).

    assert (SRC' : bytes_at rsegs m0 (A + k) (to_bytes (skipn (Z.to_nat k) b))).
    { rewrite to_bytes_skipn. replace (A + k) with (A + Z.of_nat (Z.to_nat k)) by lia. apply bytes_at_skipn; [exact SRC| lia]. }
    unfold file_cells in FC.
    step. if_cases Hc; zify_cond Hc. 1:{ exfalso. lia. }
    step. step.
    replace (v_sltu (Z_to_bv 64 n) (Z_to_bv 64 k)) with (Z_to_bv 64 0).
    2:{ unfold v_sltu, c_ltu, bv_ltu. rewrite !unsigned_lit by lia. destruct (Z.ltb_spec0 n k); [exfalso; lia| reflexivity]. }
    step. step.
    step. step. step. step. step.
    rewrite !Z.land_0_l. rewrite !unsigned_lit by lia. rewrite !Z.sub_0_r.
    step. step. if_cases Hge; zify_cond Hge. 2:{ exfalso. lia. }
    do 8 step. rewrite !unsigned_lit by lia.
    step. step. step. step_ecall.
    replace (sx32 (Z_to_bv 64 fd)) with (Z_to_bv 64 fd) by (symmetry; apply sx32_small; lia).
    split.
    { at_node_red; split_spine; try reflexivity; try lia.
      - cbn [map length]. lia.
      - cbn [map concat]. rewrite app_nil_r, to_bytes_length, length_skipn. lia.
      -   cbn [map length]. rewrite unsigned_lit by lia. lia.
      - exists [(Z_to_bv 64 (A + k), Z_to_bv 64 (n - k))]. split; [|split].
        + rewrite unsigned_lit by lia. replace (bv_unsigned sp + -88) with (bv_unsigned sp + -112 + 24) by lia.
          eapply frame_iov1. exact FR.
        +
          constructor; [|constructor]. cbn [fst snd]. rewrite !unsigned_lit by lia. lia.
        + constructor; [|constructor]. split.
          * cbn [snd]. rewrite to_bytes_length, length_skipn. f_equal. lia.
          * cbn [fst]. rewrite unsigned_lit by lia.
            apply (bytes_at_transport _ _ _ _ _ _ SRC' MU). cbn [disjoint_from]. rewrite to_bytes_length, length_skipn. lia. }
    intros rsp k' Hdec. apply dec_writev_Some in Hdec as (Hs & Hk' & Hk0 & Hkhi).
    ienter. sys_nret.

    step. step. step. step. if_cases Hr; zify_cond Hr. 2:{ exfalso. lia. } step.
    replace (ret_pc (Z_to_bv 64 0x1ae14)) with (Z_to_bv 64 0x1ae14 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    step. step. if_cases Heq; zify_cond Heq.
    -
      replace (k' =? n - k) with true by (symmetry; apply Z.eqb_eq; lia).
      ileave. apply implM_ret.
      eapply stdio_write_finish; try eassumption; try LiaTuning.alia.
      + split; assumption.
      + eapply munch_weaken; [apply sub_fp_stdio| exact MU].
    -
      replace (k' =? n - k) with false by (symmetry; apply Z.eqb_neq; lia).
      ileave.
      assert (En : n - k = Z.of_nat (length (skipn (Z.to_nat k) b))) by (rewrite length_skipn; lia).
      rewrite En in FR |- *.
      eapply (IH (skipn (Z.to_nat k) b) k' (A + k)); try eassumption; try LiaTuning.alia.
      all: try (split; assumption).
      all: rewrite length_skipn; lia.
  Qed.

  #[using="Type"] Lemma stdio_write_loop2 : forall fuel (b0 b1 : list Z) (k A0 A1 : Z)
           (x1 sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4r s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (ra s0 s1 s2 s3 s4 s5 s6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m0 m : mem) (st : St)
           (Fp : Z) (flags : word) (wend wpos wbase B bufsize wfn fd : Z) (mode : word) (lbf : Z) (tail : list byte)
           (j0 : list byte) (l lo : Z) (canary : word),
      rw_cells rsegs m (bv_unsigned sp + -112)
        [CB 8 j0; C8 (Z_to_bv 64 A0); C8 (Z_to_bv 64 (Z.of_nat (length b0))); C8 (Z_to_bv 64 A1); C8 (Z_to_bv 64 (Z.of_nat (length b1))); C8 canary;
         C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      rw_cells rsegs m Fp (file_cells flags wend wpos wbase wfn B bufsize fd mode lbf tail) ->
      ssp_cells m canary ->
      bytes_at rsegs m0 A0 (to_bytes b0) -> (A0 + Z.of_nat (length b0) <= lo \/ bv_unsigned sp <= A0) ->
      bytes_at rsegs m0 A1 (to_bytes b1) -> (b1 = [] \/ (A1 + Z.of_nat (length b1) <= lo \/ bv_unsigned sp <= A1)) ->
      stk rsegs m lo (bv_unsigned sp + -112) -> (0 <= lo <= bv_unsigned sp - 112) -> (0x5d000 <= lo) -> (bv_unsigned sp <= 2^47) ->
      munch [(bv_unsigned sp - 112, bv_unsigned sp)] m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
      (0 <= Fp) -> (Fp + 232 <= lo) ->
      (Fp + 232 <= got_ssp \/ got_ssp + 8 <= Fp) -> (Fp + 232 <= ssp_guard \/ ssp_guard + 8 <= Fp) ->
      (0 <= B) -> (0 <= bufsize) -> (B + bufsize < 2^64) -> (0 <= l < 2^64) ->
      (fd = 1 \/ fd = 2) -> (1 <= k < Z.of_nat (length b0) + Z.of_nat (length b1)) ->
      (Z.of_nat (length b0) + Z.of_nat (length b1) <= 2^24) ->
      (0 <= A0) -> (A0 + Z.of_nat (length b0) <= 2^47) -> (0 <= A1 < 2^64) -> (A1 + Z.of_nat (length b1) <= 2^47) ->
      implM rsegs (stdio_wloop (St:=St) fuel fd (advance [b0; b1] k)) st
            (stdio_write_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp flags B bufsize wfn fd mode lbf tail
                              l lo canary m0 st)
            (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0 t1 t2 (Z_to_bv 64 l) (Z_to_bv 64 Fp)
                     (Z_to_bv 64 k) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 2) (Z_to_bv 64 (bv_unsigned sp + -104)) s4r (Z_to_bv 64 ssp_guard)
                     (Z_to_bv 64 (Z.of_nat (length b0) + Z.of_nat (length b1))) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x1ae1c) fc None m (seg_rom rsegs)).
  Proof.
    induction fuel as [|fuel IH]; intros until canary;
      intros FR FC SSP SRC0 SEPA0 SRC1 SEPA1 ST LO GLO SPHI MU WM MI Fp0 FPLO FSEP1 FSEP2 B0 BS0 BShi L FD K NB A00 AHI0 A10 AHI1.
    { cbn [stdio_wloop]. apply implM_unr. }
    pose proof SSP as [GOT GUARD]. unfold got_ssp, ssp_guard in *.
    assert (LTB0 : length (to_bytes b0) = length b0) by apply to_bytes_length.
    assert (LTB1 : length (to_bytes b1) = length b1) by apply to_bytes_length.
    set (n0 := Z.of_nat (length b0)) in *. set (n1 := Z.of_nat (length b1)) in *.
    unfold file_cells in FC.
    destruct (Z.le_gt_cases k n0) as [Kle | Kgt].
    -
      replace (advance [b0; b1] k) with [skipn (Z.to_nat k) b0; b1]
        by (unfold advance, zlength; fold n0; destruct (Z.ltb_spec0 n0 k); [exfalso; lia| reflexivity]).
      cbn [stdio_wloop]. apply implM_sysk.
      replace (zlength (concat [skipn (Z.to_nat k) b0; b1])) with (n0 + n1 - k)
        by (unfold zlength; cbn [concat]; rewrite app_nil_r, length_app, length_skipn; lia).
      assert (SRC' : bytes_at rsegs m0 (A0 + k) (to_bytes (skipn (Z.to_nat k) b0))).
      { rewrite to_bytes_skipn. replace (A0 + k) with (A0 + Z.of_nat (Z.to_nat k)) by lia. apply bytes_at_skipn; [exact SRC0| lia]. }
      step. if_cases Hc; zify_cond Hc. 1:{ exfalso. lia. }
      step. step.
      replace (v_sltu (Z_to_bv 64 n0) (Z_to_bv 64 k)) with (Z_to_bv 64 0).
      2:{ unfold v_sltu, c_ltu, bv_ltu. rewrite !unsigned_lit by lia. destruct (Z.ltb_spec0 n0 k); [exfalso; lia| reflexivity]. }
      step. step.
      step. step. step. step. step.
      rewrite !Z.land_0_l. rewrite !unsigned_lit by lia. rewrite !Z.sub_0_r.
      step. step. if_cases Hge; zify_cond Hge. 2:{ exfalso. lia. }
      do 8 step. rewrite !unsigned_lit by lia.
      step. step. step. step_ecall.
      replace (sx32 (Z_to_bv 64 fd)) with (Z_to_bv 64 fd) by (symmetry; apply sx32_small; lia).
      split.
      { at_node_red; split_spine; try reflexivity; try lia.
        - cbn [map length]. lia.
        - cbn [map concat]. rewrite app_nil_r, length_app, !to_bytes_length, length_skipn. lia.
        -   cbn [map length]. rewrite unsigned_lit by lia. lia.
        - exists [(Z_to_bv 64 (A0 + k), Z_to_bv 64 (n0 - k)); (Z_to_bv 64 A1, Z_to_bv 64 n1)]. split; [|split].
          + rewrite unsigned_lit by lia. replace (bv_unsigned sp + -104) with (bv_unsigned sp + -112 + 8) by lia.
            eapply frame_iov2. exact FR.
          +
            constructor; [|constructor; [|constructor]]; cbn [fst snd]; rewrite !unsigned_lit by lia; lia.
          + constructor; [|constructor; [|constructor]]; split.
            * cbn [snd]. rewrite to_bytes_length, length_skipn. f_equal. lia.
            * cbn [fst]. rewrite unsigned_lit by lia.
              apply (bytes_at_transport _ _ _ _ _ _ SRC' MU). cbn [disjoint_from]. rewrite to_bytes_length, length_skipn. lia.
            * cbn [snd]. rewrite to_bytes_length. reflexivity.
            * cbn [fst]. rewrite unsigned_lit by lia. destruct SEPA1 as [-> | SEPA1]; [apply bytes_at_nil; lia|].
              apply (bytes_at_transport _ _ _ _ _ _ SRC1 MU). cbn [disjoint_from]. rewrite to_bytes_length. lia. }
      intros rsp k' Hdec. apply dec_writev_Some in Hdec as (Hs & Hk' & Hk0 & Hkhi).
      ienter. sys_nret.
      step. step. step. step. if_cases Hr; zify_cond Hr. 2:{ exfalso. lia. } step.
      replace (ret_pc (Z_to_bv 64 0x1ae14)) with (Z_to_bv 64 0x1ae14 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      step. step. if_cases Heq; zify_cond Heq.
      +
        replace (k' =? n0 + n1 - k) with true by (symmetry; apply Z.eqb_eq; lia).
        ileave. apply implM_ret.
        eapply stdio_write_finish; try eassumption; try LiaTuning.alia.
        * split; assumption.
        * eapply munch_weaken; [apply sub_fp_stdio| exact MU].
      +
        replace (k' =? n0 + n1 - k) with false by (symmetry; apply Z.eqb_neq; lia).
        ileave.
        assert (En : n0 - k = Z.of_nat (length (skipn (Z.to_nat k) b0))) by (rewrite length_skipn; lia).
        replace (n0 + n1 - k) with (Z.of_nat (length (skipn (Z.to_nat k) b0)) + n1) by lia.
        rewrite En in FR.
        eapply (IH (skipn (Z.to_nat k) b0) b1 k' (A0 + k) A1); try eassumption; try LiaTuning.alia.
        all: try (split; assumption).
        all: rewrite length_skipn; lia.
    -
      destruct SEPA1 as [-> | SEPA1]. { exfalso. subst n1. cbn [length] in K. lia. }
      replace (advance [b0; b1] k) with [skipn (Z.to_nat (k - n0)) b1]
        by (unfold advance, zlength; fold n0; destruct (Z.ltb_spec0 n0 k); [reflexivity| exfalso; lia]).
      cbn [stdio_wloop]. apply implM_sysk.
      replace (zlength (concat [skipn (Z.to_nat (k - n0)) b1])) with (n0 + n1 - k)
        by (unfold zlength; cbn [concat]; rewrite app_nil_r, length_skipn; lia).
      assert (SRC' : bytes_at rsegs m0 (A1 + (k - n0)) (to_bytes (skipn (Z.to_nat (k - n0)) b1))).
      { rewrite to_bytes_skipn. replace (A1 + (k - n0)) with (A1 + Z.of_nat (Z.to_nat (k - n0))) by lia. apply bytes_at_skipn; [exact SRC1| lia]. }
      step. if_cases Hc; zify_cond Hc. 1:{ exfalso. lia. }
      step. step.
      replace (v_sltu (Z_to_bv 64 n0) (Z_to_bv 64 k)) with (Z_to_bv 64 1).
      2:{ unfold v_sltu, c_ltu, bv_ltu. rewrite !unsigned_lit by lia. destruct (Z.ltb_spec0 n0 k); [reflexivity| exfalso; lia]. }
      step. step.
      step. step. step. rewrite !unsigned_lit by lia.
      replace (Z.land 18446744073709551615 n0) with n0
        by (change 18446744073709551615 with (Z.ones 64); rewrite Z.land_comm, Z.land_ones by lia; symmetry; apply Z.mod_small; lia).
      step. step. rewrite !unsigned_lit by lia.
      step. step. if_cases Hge; zify_cond Hge. 1:{ exfalso. lia. }
      step. step.
      do 7 step. rewrite !unsigned_lit by lia.
      step. step. step. step_ecall.
      replace (sx32 (Z_to_bv 64 fd)) with (Z_to_bv 64 fd) by (symmetry; apply sx32_small; lia).
      split.
      { at_node_red; split_spine; try reflexivity; try lia.
        - cbn [map length]. lia.
        - cbn [map concat]. rewrite app_nil_r, !to_bytes_length, length_skipn. lia.
        -   cbn [map length]. rewrite unsigned_lit by lia. lia.
        - exists [(Z_to_bv 64 (A1 + (k - n0)), Z_to_bv 64 (n1 - (k - n0)))]. split; [|split].
          + rewrite unsigned_lit by lia. replace (bv_unsigned sp + -88) with (bv_unsigned sp + -112 + 24) by lia.
            eapply frame_iov1. exact FR.
          +
            constructor; [|constructor]. cbn [fst snd]. rewrite !unsigned_lit by lia. lia.
          + constructor; [|constructor]; split.
            * cbn [snd]. rewrite to_bytes_length, length_skipn. f_equal. lia.
            * cbn [fst]. rewrite unsigned_lit by lia.
              apply (bytes_at_transport _ _ _ _ _ _ SRC' MU). cbn [disjoint_from]. rewrite to_bytes_length, length_skipn. lia. }
      intros rsp k' Hdec. apply dec_writev_Some in Hdec as (Hs & Hk' & Hk0 & Hkhi).
      ienter. sys_nret.
      step. step. step. step. if_cases Hr; zify_cond Hr. 2:{ exfalso. lia. } step.
      replace (ret_pc (Z_to_bv 64 0x1ae14)) with (Z_to_bv 64 0x1ae14 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      step. step. if_cases Heq; zify_cond Heq.
      +
        replace (k' =? n0 + n1 - k) with true by (symmetry; apply Z.eqb_eq; lia).
        ileave. apply implM_ret.
        eapply stdio_write_finish; try eassumption; try LiaTuning.alia.
        * split; assumption.
        * eapply munch_weaken; [apply sub_fp_stdio| exact MU].
      +
        replace (k' =? n0 + n1 - k) with false by (symmetry; apply Z.eqb_neq; lia).
        ileave.
        assert (En : n1 - (k - n0) = Z.of_nat (length (skipn (Z.to_nat (k - n0)) b1))) by (rewrite length_skipn; lia).
        replace (n0 + n1 - k) with (Z.of_nat (length (skipn (Z.to_nat (k - n0)) b1))) by lia.
        rewrite En in FR.
        eapply (stdio_write_loop1 fuel (skipn (Z.to_nat (k - n0)) b1) k' (A1 + (k - n0))); try eassumption; try LiaTuning.alia.
        all: try (split; assumption).
        all: rewrite length_skipn; lia.
  Qed.

  #[using="Type"] Lemma stdio_write_spec :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St)
           (Fp : Z) (flags : word) (wend B bufsize wfn fd : Z) (mode : word) (lbf : Z) (tail : list byte)
           (buf s : list Z) (S lo : Z) (canary : word),
      rw_cells rsegs m Fp (file_cells flags wend (B + zlength buf) B wfn B bufsize fd mode lbf tail) ->
      bytes_at rsegs m B (to_bytes buf) ->
      bytes_at rsegs m S (to_bytes s) ->
      a0 = Z_to_bv 64 Fp -> a1 = Z_to_bv 64 S -> a2 = Z_to_bv 64 (zlength s) ->
      (fd = 1 \/ fd = 2) ->
      stk rsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - STDIO_WRITE_DEPTH) -> (0x5d000 <= lo) ->
      (bv_unsigned sp <= 2^47) ->
      ssp_cells m canary -> mem_inv rsegs m ->
      (0 <= Fp) -> (Fp + 232 <= lo) ->
      (Fp + 232 <= got_ssp \/ got_ssp + 8 <= Fp) -> (Fp + 232 <= ssp_guard \/ ssp_guard + 8 <= Fp) ->
      (0 <= B) -> (0 <= bufsize) -> (zlength buf <= bufsize) -> (B + bufsize <= 2^47) ->
      (zlength buf + zlength s <= 2^24) -> (0 <= S < 2^64) -> (S + zlength s <= 2^47) ->
      (s = [] \/ ((S + zlength s <= lo \/ bv_unsigned sp <= S) /\ (S + zlength s <= Fp + 32 \/ Fp + 64 <= S))) ->
      (B + zlength buf <= lo \/ bv_unsigned sp <= B) ->
      implM rsegs (stdio_writev (St:=St) fd buf s) st
            (stdio_write_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp flags B bufsize wfn fd mode lbf tail
                              (zlength s) lo canary m st)
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x1acfc) fc None m (seg_rom rsegs)).
  Proof.
    intros until canary. intros FC BUFB SRC -> -> -> FD ST LO GLO SP47 SSP MI Fp0 FPLO FSEP1 FSEP2 B0 BS0 BUFLE BShi LENS S0 Shi SEPS SEPB.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    destruct SSP as [GOT GUARD]. unfold got_ssp, ssp_guard, STDIO_WRITE_DEPTH in *.
    unfold zlength in *.
    assert (LSB : length (to_bytes s) = length s) by (unfold to_bytes; apply length_map).
    change (bytes_at rsegs m S (to_bytes s)) with (boxed (bytes_at rsegs m S (to_bytes s))) in SRC.
    assert (LBB : length (to_bytes buf) = length buf) by (unfold to_bytes; apply length_map).
    pose proof (bytes_at_bound _ _ _ _ BUFB) as BB. pose proof (bytes_at_bound _ _ _ _ SRC) as BSRC.
    change (bytes_at rsegs m B (to_bytes buf)) with (boxed (bytes_at rsegs m B (to_bytes buf))) in BUFB.
    unfold to_bytes in BB, BSRC. rewrite length_map in BB, BSRC.
    pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    unfold stdio_writev. cbn [stdio_wloop]. apply implM_sysk.
    unfold file_cells in FC.
    carve_frame 112%nat ST.
    do 12 step. do 13 step.
    rewrite !unsigned_lit in FR |- * by lia.
    destruct buf as [|b0 buf'].
    -
      change (Z.of_nat (@length Z [])) with 0 in *. rewrite !Z.add_0_r in *. rewrite Z.lxor_nilpotent. rewrite Z.sub_diag in FR.
      change (v_sltu (Z_to_bv 64 0) (Z_to_bv 64 0)) with (Z_to_bv 64 0).
      step. if_true. do 6 step. step_ecall.
      replace (sx32 (Z_to_bv 64 fd)) with (Z_to_bv 64 fd) by (symmetry; apply sx32_small; lia).
      replace (B - B + Z.of_nat (length s)) with (Z.of_nat (length s)) by lia.
      replace (zlength (concat [s])) with (Z.of_nat (length s)) by (unfold zlength; cbn [concat]; rewrite app_nil_r; reflexivity).
      split.
      { at_node_red; split_spine; try reflexivity; try lia.
        - cbn [map length]. lia.
        - cbn [map concat]. rewrite app_nil_r, LSB. lia.
        -   cbn [map length]. rewrite unsigned_lit by lia. lia.
        - exists [(Z_to_bv 64 S, Z_to_bv 64 (Z.of_nat (length s)))]. split; [|split].
          + rewrite unsigned_lit by lia. replace (bv_unsigned sp + -88) with (bv_unsigned sp + -112 + 24) by lia.
            eapply frame_iov1. exact FR.
          +
            constructor; [|constructor]. cbn [fst snd]. rewrite !unsigned_lit by lia. lia.
          + constructor; [|constructor]. split; [cbn [snd]; rewrite LSB; reflexivity|]. cbn [fst]. rewrite unsigned_lit by lia.
            unfold boxed in SRC. destruct SEPS as [-> | [SEP1 SEP2]]; [apply bytes_at_nil; lia|].
            apply (bytes_at_transport _ _ _ _ _ _ SRC MU). cbn [disjoint_from]. rewrite LSB. lia. }
      intros rsp k Hdec. apply dec_writev_Some in Hdec as (Hs & Hk & Hk0 & Hkhi).
      ienter. sys_nret.

      step. step. step. step. if_cases Hr; zify_cond Hr. 2:{ exfalso. lia. } step.
      replace (ret_pc (Z_to_bv 64 0x1ad8c)) with (Z_to_bv 64 0x1ad8c : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      step. if_cases Heq; zify_cond Heq.
      +
        replace (k =? Z.of_nat (length s)) with false by (symmetry; apply Z.eqb_neq; lia).
        ileave. unfold boxed in SRC.
        destruct SEPS as [-> | [SEP1 SEP2]]. { exfalso. cbn [length] in *. lia. }
        eapply (stdio_write_loop1 _ s k S); try eassumption; try LiaTuning.alia.
        split; assumption.
      +
        replace (k =? Z.of_nat (length s)) with true by (symmetry; apply Z.eqb_eq; lia).
        ileave. apply implM_ret.
        eapply stdio_write_finish; try eassumption; try LiaTuning.alia.
        * split; assumption.
        * eapply munch_weaken; [apply sub_fp_stdio| exact MU].
    -
      set (nb := Z.of_nat (length (b0 :: buf'))) in *.
      assert (NB1 : 1 <= nb) by (subst nb; cbn [length]; lia).
      replace (B + nb - B) with nb in FR by lia.
      replace (Z.lxor (B + nb) B) with (Z.lxor (B + nb) (B + 0)) by (rewrite Z.add_0_r; reflexivity).
      assert (XNZ : Z.lxor (B + nb) (B + 0) <> 0).
      { intros E. apply Z.lxor_eq in E. lia. }
      replace (v_sltu (Z_to_bv 64 0) (Z_to_bv 64 (Z.lxor (B + nb) (B + 0)))) with (Z_to_bv 64 1).
      2:{ pose proof (Z_lxor_range (B + nb) (B + 0) ltac:(lia) ltac:(lia)) as XR.
          unfold v_sltu, c_ltu, bv_ltu. rewrite !unsigned_lit by lia.
          destruct (Z.ltb_spec0 0 (Z.lxor (B + nb) (B + 0))); [reflexivity| exfalso; lia]. }
      step. if_cases Hb; zify_cond Hb. 1:{ exfalso. lia. } do 7 step. step_ecall.
      replace (sx32 (Z_to_bv 64 fd)) with (Z_to_bv 64 fd) by (symmetry; apply sx32_small; lia).
      replace (B + nb - B + Z.of_nat (length s)) with (nb + Z.of_nat (length s)) by lia.
      replace (zlength (concat [b0 :: buf'; s])) with (nb + Z.of_nat (length s))
        by (unfold zlength; cbn [concat]; rewrite app_nil_r, length_app; subst nb; lia).
      split.
      { at_node_red; split_spine; try reflexivity; try lia.
        - cbn [map length]. lia.
        - cbn [map concat]. rewrite app_nil_r, length_app, LSB, LBB. subst nb. lia.
        -   cbn [map length]. rewrite unsigned_lit by lia. lia.
        - exists [(Z_to_bv 64 B, Z_to_bv 64 nb); (Z_to_bv 64 S, Z_to_bv 64 (Z.of_nat (length s)))]. split; [|split].
          + rewrite unsigned_lit by lia. replace (bv_unsigned sp + -104) with (bv_unsigned sp + -112 + 8) by lia.
            eapply frame_iov2. exact FR.
          +
            subst nb. constructor; [|constructor; [|constructor]]; cbn [fst snd]; rewrite !unsigned_lit by lia; lia.
          + constructor; [| constructor; [|constructor]]; split.
            * cbn [snd]. rewrite LBB. subst nb. reflexivity.
            * cbn [fst]. rewrite unsigned_lit by lia. unfold boxed in BUFB.
              apply (bytes_at_transport _ _ _ _ _ _ BUFB MU). cbn [disjoint_from]. rewrite LBB. subst nb. lia.
            * cbn [snd]. rewrite LSB. reflexivity.
            * cbn [fst]. rewrite unsigned_lit by lia.
              unfold boxed in SRC. destruct SEPS as [-> | [SEP1 SEP2]]; [apply bytes_at_nil; lia|].
              apply (bytes_at_transport _ _ _ _ _ _ SRC MU). cbn [disjoint_from]. rewrite LSB. lia. }
      intros rsp k Hdec. apply dec_writev_Some in Hdec as (Hs & Hk & Hk0 & Hkhi).
      ienter. sys_nret.
      step. step. step. step. if_cases Hr; zify_cond Hr. 2:{ exfalso. lia. } step.
      replace (ret_pc (Z_to_bv 64 0x1ad8c)) with (Z_to_bv 64 0x1ad8c : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      step. if_cases Heq; zify_cond Heq.
      +
        replace (k =? nb + Z.of_nat (length s)) with false by (symmetry; apply Z.eqb_neq; lia).
        ileave. unfold boxed in SRC. subst nb.
        unfold boxed in BUFB.
        eapply (stdio_write_loop2 _ (b0 :: buf') s k B S); try eassumption; try LiaTuning.alia.
        * split; assumption.
        * destruct SEPS as [-> | [SEP1 SEP2]]; [left; reflexivity| right; lia].
      +
        replace (k =? nb + Z.of_nat (length s)) with true by (symmetry; apply Z.eqb_eq; lia).
        ileave. apply implM_ret.
        eapply stdio_write_finish; try eassumption; try LiaTuning.alia.
        * split; assumption.
        * eapply munch_weaken; [apply sub_fp_stdio| exact MU].
  Qed.
End StdioWrite.
