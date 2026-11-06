(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import Stdio_pure Printf_pieces.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Ubsan Require Import UImg.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Ubsan Require Import RMallocRep RMallocTree RMalloc_iface ROpNew_iface ROpNew ROpNew_nt.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Ubsan Require RMalloc_ifaceP.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prelim Monad Stdio Malloc HarnessP ProgP SjStage1 SjInvPath SjInv SjS1Bytes.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Ubsan Require Import RunDraw.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Ubsan Require Import PC_kit PC_s12iface PU_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Notation mem := (word -> option byte).

Section CANSEC1. Context {rc : runConstT}.
Ltac ret_lit := lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?r)] =>
      replace (ret_pc (Z_to_bv 64 r)) with (Z_to_bv 64 r) by (symmetry; rpc) end.

Lemma wr_at_wmono_p : forall m m' A n, wr_at usegs m A n -> wmono usegs m m' -> wr_at usegs m' A n.
Proof. intros m m' A n (H0 & H1 & H) W. split; [exact H0|]. split; [exact H1|]. intros i Hi. apply W. apply H. exact Hi. Qed.
Lemma rbr_lin' : forall A n, rblock_range A n -> 0 < A /\ A mod 16 = 0 /\ 0 <= n /\ A + n <= ATOP.
Proof. intros A n (H1 & H2 & H3 & H4 & _). tauto. Qed.
Lemma rbr_img' : forall A n, rblock_range A n -> A + n <= 0x10000 \/ 0xb3000 <= A.
Proof. intros A n (_ & _ & _ & _ & H). exact H. Qed.
(* [comment removed for export] *)
Lemma blk_apart : forall s LB m p1 A1 n1 p2 A2 n2, RHEAP s LB m -> In (p1, A1, n1) LB -> In (p2, A2, n2) LB -> p1 <> p2 ->
  A1 + n1 <= A2 \/ A2 + n2 <= A1.
Proof. intros. pose proof (RMalloc_ifaceP.RHEAP_blocks_disjoint_proof _ _ _ (p1, A1, n1) (p2, A2, n2) H H0 H1 ltac:(cbn; exact H2)) as D. exact D. Qed.
Lemma nodup7' : forall (x1 x2 x3 x4 x5 x6 x7 : bptr), List.NoDup [x1; x2; x3; x4; x5; x6; x7] ->
  x1 <> x2 /\ x1 <> x3 /\ x1 <> x4 /\ x1 <> x5 /\ x1 <> x6 /\ x1 <> x7 /\ x2 <> x3 /\ x2 <> x4 /\ x2 <> x5 /\ x2 <> x6 /\ x2 <> x7
  /\ x3 <> x4 /\ x3 <> x5 /\ x3 <> x6 /\ x3 <> x7 /\ x4 <> x5 /\ x4 <> x6 /\ x4 <> x7 /\ x5 <> x6 /\ x5 <> x7 /\ x6 <> x7.
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 N. apply NoDup_cons_iff in N as [N1 N]. apply NoDup_cons_iff in N as [N2 N]. apply NoDup_cons_iff in N as [N3 N].
  apply NoDup_cons_iff in N as [N4 N]. apply NoDup_cons_iff in N as [N5 N]. apply NoDup_cons_iff in N as [N6 _].
  cbn [In] in N1, N2, N3, N4, N5, N6. repeat split; intros E; subst; tauto.
Qed.

Section Proof.
  Hypothesis S1L : s1l_stmt.
  Hypothesis S2 : stage2_stmt.

  Theorem parse_proof : parse_stmt.
  Proof.
    unfold parse_stmt. intros until jia. intros HP ND INM NIM INS NSI INC BUF1 BUF2 INT INB INO NOC INA NIA TP8 TPS SB1 SB2
      BUFB DB DL O8 O16 O24 O40 O56 WO WI DOCC DSP DTOP D8 BLT BLS BLO BLA FMIN GOT AUX SPB ST LOA LOS SPA SP47 ERR MI FZ TPE A0 A1 A2 A3.
    set (d := strip_bom data) in *.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    unfold PARSE_STACK, PS2_STACK, OPNEW_NT_STACK, OPNEW_STACK, RMALLOC_STACK in LOS. atop_facts.
    subst tp. rewrite errno_lit in ERR. unfold RERRNO in ERR.
    (* [comment removed for export] *)
    pose proof (RMalloc_ifaceP.RHEAP_block_range_proof _ _ _ _ HP INM) as BRM. pose proof (RMalloc_ifaceP.RHEAP_block_range_proof _ _ _ _ HP INS) as BRI.
    pose proof (RMalloc_ifaceP.RHEAP_block_range_proof _ _ _ _ HP INC) as BRC. pose proof (RMalloc_ifaceP.RHEAP_block_range_proof _ _ _ _ HP INT) as BRT.
    pose proof (RMalloc_ifaceP.RHEAP_block_range_proof _ _ _ _ HP INB) as BRS. pose proof (RMalloc_ifaceP.RHEAP_block_range_proof _ _ _ _ HP INO) as BRO.
    pose proof (RMalloc_ifaceP.RHEAP_block_range_proof _ _ _ _ HP INA) as BRA. cbn [blk_addr blk_size fst snd] in BRM, BRI, BRC, BRT, BRS, BRO, BRA.
    pose proof (rbr_lin' _ _ BRM) as (BRM1 & BRM2 & BRM3 & BRM4). pose proof (rbr_lin' _ _ BRI) as (BRI1 & BRI2 & BRI3 & BRI4).
    pose proof (rbr_lin' _ _ BRC) as (BRC1 & BRC2 & BRC3 & BRC4). pose proof (rbr_lin' _ _ BRT) as (BRT1 & BRT2 & BRT3 & BRT4).
    pose proof (rbr_lin' _ _ BRS) as (BRS1 & BRS2 & BRS3 & BRS4). pose proof (rbr_lin' _ _ BRO) as (BRO1 & BRO2 & BRO3 & BRO4).
    pose proof (rbr_lin' _ _ BRA) as (BRA1 & BRA2 & BRA3 & BRA4).
    destruct (nodup7' _ _ _ _ _ _ _ ND) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & E18 & E19 & E20 & E21).
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    assert (ZD0 : 0 <= zlength d) by (unfold zlength; lia).
    unfold PFMIN, fmin_cells in FMIN. unfold PGOT_NOTHROW, PNOTHROW in GOT.
    change (rw_cells usegs m AOC [CB 8192 joc]) with (rw_cells usegs m AOC [CB (Z.to_nat 8192) joc]) in BLO.
    change (rw_cells usegs m AIA [CB 1024 jia]) with (rw_cells usegs m AIA [CB (Z.to_nat 1024) jia]) in BLA.
    assert (BUFL : Z.of_nat (length (s1buf d)) = zlength d + 64) by (unfold s1buf, zlength; rewrite length_map, length_app, repeat_length; lia).
    apply implM_from_evt.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    carve_frame 32%nat ST.
    subst a0 a1 a2 a3. unfold PPARSE.
    do 8 zstep.
    assert (DMI : THIS + nim <= ASI \/ ASI + nsi <= THIS) by exact (blk_apart _ _ _ _ _ _ _ _ _ HP INM INS E1).
    assert (DMC : THIS + nim <= ACP \/ ACP + ncp <= THIS) by exact (blk_apart _ _ _ _ _ _ _ _ _ HP INM INC E2).
    assert (DIC : ASI + nsi <= ACP \/ ACP + ncp <= ASI) by exact (blk_apart _ _ _ _ _ _ _ _ _ HP INS INC E7).
    eapply evt_cut.
    { eapply S1L with (THIS := THIS) (BUF := BUF) (ASI := ASI) (d := d) (lo := lo); rewrite ?unsigned_lit by lia;
        [ exact BUFB | exact DB | exact DL
        | eapply hrange_sub; [exact (hrange_of_block _ _ BRC)| lia| lia| lia| lia] | lia
        | eapply hrange_sub; [exact (hrange_of_block _ _ BRM)| lia| lia| lia| lia]
        | eapply hrange_sub; [exact (hrange_of_block _ _ BRI)| lia| lia| lia| lia]
        | exact BRM2 | exact BRI2 | lia | lia | lia | exact WO | exact O16 | exact WI | exact ST | exact LOA
        | unfold PS1_STACK; lia | lia | lia | exact MI | exact FZ | reflexivity | reflexivity | reflexivity | reflexivity ]. }
    intros ms2 PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F' & fc' & m2 & rcv & -> & FZ2 & RCV & MI2 & ST2 & WM2 & MU2
                    & RC & C72 & CS).
    rewrite ?unsigned_lit in ST2 by lia. rewrite ?unsigned_lit in MU2 by lia.
    ret_lit.
    clear DMI DMC DIC.
    (* [comment removed for export] *)
    assert (PW2 : rheap_pres_W LB (bv_unsigned sp) (parse_win (bv_unsigned sp) THIS ASI (zlength d) ATP ntp ASB nsb AOC AIA) m m2).
    { assert (LBB : forall b, In b LB -> blk_addr b + blk_size b <= ATOP)
        by (intros b Hb; destruct (RMalloc_ifaceP.RHEAP_block_range_proof _ _ _ b HP Hb) as (_ & _ & _ & R4 & _); exact R4).
      eapply rheap_pres_W_trans.
      { eapply rheap_pres_W_of_munch; [exact MU| exact WM|]. intros a Ha Hc Hx. cbn. destruct Hc as [Hc|[Hc|(b & Hb & Hr)]]; [| | pose proof (LBB b Hb)]; split; try exact I; lia. }
      eapply rheap_pres_W_of_munch; [exact MU2| exact WM2|]. intros a Ha Hc Hx. unfold parse_win in Hx. unfold s1_win, PS1_STACK. cbn [outside] in Hx |- *.
      destruct Hc as [Hc|[Hc|(b & Hb & Hr)]]; [| | pose proof (LBB b Hb)]; repeat split; try exact I; lia. }
    assert (ERR2 : rw_cells usegs m2 597308 [C4 errv])
      by (pose proof (rbr_img' _ _ BRM) as BRM5; pose proof (rbr_img' _ _ BRI) as BRI5;
          eapply rw_cells_transport; [exact ERR| exact MU2| exact WM2| unfold s1_win, PS1_STACK; cbn; lia]).
    assert (AUX2 : rauxv_ok m2 B).
    { pose proof (rbr_img' _ _ BRM) as BRM5. pose proof (rbr_img' _ _ BRI) as BRI5.
      eapply rauxv_ok_frame; [| exact MU2| exact WM2|].
      - eapply rauxv_ok_stack_frame; [exact AUX| exact MU| exact WM| repeat constructor; cbn; lia].
      - unfold s1_win, PS1_STACK. repeat (apply Forall_cons; [cbn; unfold RAUXV_CELL in *; lia|]); apply Forall_nil. }
    assert (HP2 : RHEAP s LB m2).
    { eapply RMalloc_ifaceP.RHEAP_frame_proof; [eapply RHEAP_stack_frame; [exact HP| exact MU| exact WM| repeat constructor; cbn; lia]| exact MU2| exact WM2|].
      unfold s1_win, PS1_STACK. apply Forall_cons; [left; cbn; lia|].
      apply Forall_cons; [right; right; exists (pim, THIS, nim); split; [exact INM| cbn; lia]|].
      apply Forall_cons; [right; right; exists (pim, THIS, nim); split; [exact INM| cbn; lia]|].
      apply Forall_cons; [right; right; exists (pim, THIS, nim); split; [exact INM| cbn; lia]|].
      apply Forall_cons; [right; right; exists (psi, ASI, nsi); split; [exact INS| cbn; lia]| apply Forall_nil]. }
    clear ERR AUX.
    lazymatch goal with H : rw_cells usegs _ (bv_unsigned sp + -32) ?cs |- _ =>
      assert (FR2 : rw_cells usegs m2 (bv_unsigned sp + -32) cs)
        by (eapply rw_cells_transport; [exact H| exact MU2| exact WM2| unfold s1_win, PS1_STACK; cbn; lia]); clear H end.
    zstep.
    if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      assert (R0 : rcv = 0) by (change 18446744073709551615 with (Z.ones 64) in K; rewrite ?Z.land_ones in K by lia; rewrite ?Z.mod_small in K by lia; lia).
      destruct (CS R0) as (CS8 & CS24 & CSI). clear CS.
      destruct (scan d) as [ok idx] eqn:ES. cbn [fst snd] in RC, CS8, CSI.
      assert (OK : ok = true) by (apply RC; exact R0). subst ok.
      pose proof (scan_S1OUT d idx ES) as S1O. destruct S1O as [NIX _ _ _ _ _].
      (* [comment removed for export] *)
      assert (DCI : THIS + nim <= ASI \/ ASI + nsi <= THIS) by exact (blk_apart _ _ _ _ _ _ _ _ _ HP INM INS E1).
      assert (TRT : forall A cs, rw_cells usegs m0 A cs -> THIS <= A -> A + Z.of_nat (cells_size cs) <= THIS + 96 ->
                (A + Z.of_nat (cells_size cs) <= THIS + 8 \/ THIS + 12 <= A) -> (A + Z.of_nat (cells_size cs) <= THIS + 24 \/ THIS + 28 <= A) ->
                (A + Z.of_nat (cells_size cs) <= THIS + 72 \/ THIS + 88 <= A) -> rw_cells usegs m2 A cs).
      { intros A cs H H1 H2 H3 H4 H5. eapply rw_cells_transport; [exact H| exact MU2| exact WM2|]. unfold s1_win, PS1_STACK. cbn [disjoint_from].
        clear - H1 H2 H3 H4 H5 DCI NIM NSI BRM4 LOA LOS ZD0. repeat split; try exact I; lia. }
      assert (O16' : rw_cells usegs m2 (THIS + 16) [C8 (Z_to_bv 64 ASI)]) by (apply TRT; [exact O16| lia| cbn; lia| cbn; lia| cbn; lia| cbn; lia]).
      lazymatch type of O40 with rw_cells _ _ _ ?cs =>
        assert (O40' : rw_cells usegs m2 (THIS + 40) cs) by (apply TRT; [exact O40| lia| cbn; lia| cbn; lia| cbn; lia| cbn; lia]) end.
      destruct (rw_cells_app_split usegs _ (THIS + 56) [C8 (Z_to_bv 64 AOC); C8 (Z_to_bv 64 AIA)] [C8 x72; C8 x80; C8 x88] O56) as [O56a O56b].
      cbn [cells_size csize] in O56b. change (Z.of_nat (8 + (8 + 0))) with 16 in O56b. replace (THIS + 56 + 16) with (THIS + 72) in O56b by lia.
      destruct (rw_cells_app_split usegs _ (THIS + 72) [C8 x72; C8 x80] [C8 x88] O56b) as [_ O88].
      cbn [cells_size csize] in O88. change (Z.of_nat (8 + (8 + 0))) with 16 in O88. replace (THIS + 72 + 16) with (THIS + 88) in O88 by lia.
      assert (O56' : rw_cells usegs m2 (THIS + 56) [C8 (Z_to_bv 64 AOC); C8 (Z_to_bv 64 AIA)]) by (apply TRT; [exact O56a| lia| cbn; lia| cbn; lia| cbn; lia| cbn; lia]).
      assert (O88' : rw_cells usegs m2 (THIS + 88) [C8 x88]) by (apply TRT; [exact O88| lia| cbn; lia| cbn; lia| cbn; lia| cbn; lia]).
      clear TRT O16 O40 O56 O56a O56b O88 O8 O24.
      assert (OB56 : rw_cells usegs m2 (THIS + 56) [C8 (Z_to_bv 64 AOC); C8 (Z_to_bv 64 AIA); C8 (Z_to_bv 64 BUF); C8 (Z_to_bv 64 (zlength d)); C8 x88]).
      { pose proof (rw_cells_app_join usegs _ (THIS + 56) [C8 (Z_to_bv 64 AOC); C8 (Z_to_bv 64 AIA)] [C8 (Z_to_bv 64 BUF); C8 (Z_to_bv 64 (zlength d))] O56') as J1.
        cbn [cells_size csize app] in J1. change (Z.of_nat (8 + (8 + 0))) with 16 in J1. replace (THIS + 56 + 16) with (THIS + 72) in J1 by lia.
        specialize (J1 C72).
        pose proof (rw_cells_app_join usegs _ (THIS + 56) [C8 (Z_to_bv 64 AOC); C8 (Z_to_bv 64 AIA); C8 (Z_to_bv 64 BUF); C8 (Z_to_bv 64 (zlength d))] [C8 x88] J1) as J2.
        cbn [cells_size csize app] in J2. change (Z.of_nat (8 + (8 + (8 + (8 + 0))))) with 32 in J2. replace (THIS + 56 + 32) with (THIS + 88) in J2 by lia.
        exact (J2 O88'). }
      clear O56' O88' C72.
      (* [comment removed for export] *)
      assert (TRB : forall p0 X0 n0 A cs, In (p0, X0, n0) LB -> p0 <> pim -> p0 <> psi -> rw_cells usegs m0 A cs -> X0 <= A ->
                A + Z.of_nat (cells_size cs) <= X0 + n0 -> rw_cells usegs m2 A cs).
      { intros p0 X0 n0 A cs IN0 N1 N2 H H1 H2.
        pose proof (blk_apart _ _ _ _ _ _ _ _ _ HP IN0 INM N1) as D1. pose proof (blk_apart _ _ _ _ _ _ _ _ _ HP IN0 INS N2) as D2.
        pose proof (RMalloc_ifaceP.RHEAP_block_range_proof _ _ _ _ HP IN0) as B0. cbn [blk_addr blk_size fst snd] in B0. destruct (rbr_lin' _ _ B0) as (_ & _ & _ & B4).
        eapply rw_cells_transport; [exact H| exact MU2| exact WM2|]. unfold s1_win, PS1_STACK. cbn [disjoint_from].
        clear - H1 H2 D1 D2 B4 NIM NSI LOA LOS ZD0. repeat split; try exact I; lia. }
      assert (BLT' : rw_cells usegs m2 ATP [CB (Z.to_nat ntp) jtp]) by (eapply TRB; [exact INT| intros e; exact (E3 (eq_sym e))| intros e; exact (E8 (eq_sym e))| exact BLT| lia| cbn; lia]).
      assert (BLS' : rw_cells usegs m2 ASB [CB (Z.to_nat nsb) jsb]) by (eapply TRB; [exact INB| intros e; exact (E4 (eq_sym e))| intros e; exact (E9 (eq_sym e))| exact BLS| lia| cbn; lia]).
      assert (BLO' : rw_cells usegs m2 AOC [CB (Z.to_nat 8192) joc]) by (eapply TRB; [exact INO| intros e; exact (E5 (eq_sym e))| intros e; exact (E10 (eq_sym e))| exact BLO| lia| cbn; lia]).
      assert (BLA' : rw_cells usegs m2 AIA [CB (Z.to_nat 1024) jia]) by (eapply TRB; [exact INA| intros e; exact (E6 (eq_sym e))| intros e; exact (E11 (eq_sym e))| exact BLA| lia| cbn; lia]).
      assert (BUF' : bytes_at usegs m2 BUF (s1buf d)).
      { pose proof (blk_apart _ _ _ _ _ _ _ _ _ HP INC INM (fun e => E2 (eq_sym e))) as D1.
        pose proof (blk_apart _ _ _ _ _ _ _ _ _ HP INC INS (fun e => E7 (eq_sym e))) as D2.
        eapply bytes_at_transport; [exact BUFB| exact MU2|]. rewrite BUFL. unfold s1_win, PS1_STACK. cbn [disjoint_from].
        clear - D1 D2 BUF1 BUF2 BRC4 NIM NSI LOA LOS ZD0. repeat split; try exact I; lia. }
      assert (IMG' : rw_cells usegs m2 528176 [C4 (Z_to_bv 64 8388608)] /\ rw_cells usegs m2 523040 [C8 (Z_to_bv 64 112848)]).
      { pose proof (rbr_img' _ _ BRM) as BRM5. pose proof (rbr_img' _ _ BRI) as BRI5.
        split; (eapply rw_cells_transport; [first [exact FMIN | exact GOT]| exact MU2| exact WM2|]); unfold s1_win, PS1_STACK; cbn [disjoint_from cells_size csize];
          clear - BRM5 BRI5 NIM NSI LOA LOS ZD0 ATOPR; repeat split; try exact I; lia. }
      destruct IMG' as (FMIN' & GOT').
      assert (DOC' : rw_cells usegs m2 DOC [C8 (Z_to_bv 64 ATP); C8 (Z_to_bv 64 ASB)])
        by (eapply rw_cells_transport; [exact DOCC| exact MU2| exact WM2| unfold s1_win, PS1_STACK; cbn; lia]).
      clear TRB BLT BLS BLO BLA BUFB FMIN GOT DOCC.
      (* [comment removed for export] *)
      do 7 zstep.
      release_frame FR2 ST2 (bv_unsigned sp).
      apply evt_done.
      rewrite (parse_impl_rn data idx ES).
      eapply implM_mono.
      { eapply S2 with (lo := lo) (B := B) (THIS := THIS) (ASI := ASI) (ACP := ACP) (ATP := ATP) (ASB := ASB) (AOC := AOC) (AIA := AIA) (DOC := DOC) (BUF := BUF);
          rewrite ?unsigned_lit by lia;
          [ exact HP2 | exact ND | exact INM | exact NIM | exact INS | lia | exact INC | exact BUF1 | exact BUF2 | exact INT | exact INB | exact INO
          | exact NOC | exact INA | exact NIA | exact TP8 | lia | exact SB1 | exact SB2 | exact BUF' | exact DB | exact DL | exact ES | exact CSI
          | exact CS8 | exact O16' | exact CS24 | exact O40' | exact OB56 | exact DOC' | exact DSP | exact DTOP | exact D8 | exact BLT' | exact BLS'
          | exact BLO' | exact BLA' | exact FMIN' | exact GOT' | exact AUX2 | exact SPB | exact ST2 | exact LOA
          | unfold PS2_STACK, OPNEW_NT_STACK, OPNEW_STACK, RMALLOC_STACK; lia | exact SPA | exact SP47 | rewrite errno_lit; exact ERR2
          | exact MI2 | exact FZ2 | reflexivity | reflexivity | reflexivity ]. }
      cbv beta. intros [] s' ms' PO.
      destruct PO as (h0 & h1 & h2 & k0 & k1 & k2 & k3 & k4 & k5 & k6 & k7 & h3 & h4 & h5 & h6 & F'' & fc'' & m3 & errv3 & -> & FZ3 & RA3 & MI3 & ST3
                      & ERR3 & AUX3 & RPW3 & FAE3 & SOE3 & HP3).
      unfold s2_post. do 15 eexists. exists F'', fc''. eexists. exists errv3. split; [reflexivity|].
      split; [exact FZ3|]. split; [exact RA3|]. split; [exact MI3|]. split; [exact ST3|]. split; [exact ERR3|]. split; [exact AUX3|].
      split; [|split; [exact FAE3| split; [exact SOE3| exact HP3]]].
      eapply rheap_pres_W_trans; [exact PW2|]. eapply rheap_pres_W_of_W; [exact RPW3| lia| intros b Hb; exact Hb|].
      intros a Ha Hc Hx. unfold parse_win in Hx. unfold s2_win. cbn [outside] in Hx |- *. clear - Hx. repeat split; try exact I; lia.
    - (* [comment removed for export] *)
      assert (R0 : rcv <> 0) by (intros E; subst rcv; apply K; reflexivity).
      assert (HF : fst (scan d) = false).
      { destruct (Bool.bool_dec (fst (scan d)) true) as [E|E]; [exfalso; exact (R0 (proj2 RC E))| apply Bool.not_true_is_false; exact E]. }
      do 5 zstep.
      release_frame FR2 ST2 (bv_unsigned sp).
      apply evt_done.
      rewrite (parse_impl_fail data HF). apply implM_ret. apply evt_done.
      unfold s2_post. do 15 eexists. exists F', fc'. eexists. exists errv. split; [reflexivity|].
      split; [exact FZ2|]. split; [rewrite unsigned_lit by lia; lia|]. split; [exact MI2|]. split; [exact ST2|]. split; [rewrite errno_lit; exact ERR2|]. split; [exact AUX2|].
      split; [exact PW2|]. split; [reflexivity|]. split; [reflexivity| exact HP2].
  Qed.
End Proof.
End CANSEC1.
