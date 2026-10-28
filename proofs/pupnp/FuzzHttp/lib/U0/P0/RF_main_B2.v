(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation Strings.String.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Agree Ceiling.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.Malloc Require Import MallocBlocks MallocTree MallocHINV Malloc_iface.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import InitStack.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Malloc Require Import InitMem.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.P0 Require Import Startup_lib.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Stdio_base Printf_lib Startup RefImpl F_printf_iface Stdio_iface Stdio_init F_printf_diag RDriver_lib RDriver_kit RDriver_ctx RF_main_A RF_main_B1.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Segs RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Segs F_memset F_memcpy F_strlen.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require Import Prelim STree Malloc Monad Stdio Driver Prog.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac ua := idtac.
Ltac rpc := apply ret_pc_even; [lia| reflexivity].

Lemma rw_cells_CB0 : forall m A, 0 <= A <= 2^64 -> rw_cells rsegs m A [CB 0%nat []].
Proof.
  intros m A H. split; [split|].
  - cbn. split; [reflexivity| exact I].
  - cbn [cells_bytes cbytes app]. apply bytes_at_nil. exact H.
  - cbn [cells_size csize Nat.add]. split; [lia|]. split; [lia|]. intros i Hi. lia.
Qed.

Lemma rw_cells_CB_join : forall m A n1 n2 (b1 b2 : list byte),
  rw_cells rsegs m A [CB n1 b1] -> rw_cells rsegs m (A + Z.of_nat n1) [CB n2 b2] ->
  rw_cells rsegs m A [CB (n1 + n2)%nat (b1 ++ b2)].
Proof.
  intros m A n1 n2 b1 b2 H1 H2.
  assert (H : rw_cells rsegs m A ([CB n1 b1] ++ [CB n2 b2])).
  { apply (proj2 (rw_cells_app _ _ _ _ _)). split; [exact H1|]. cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r. exact H2. }
  destruct H as [[Hwf HB] HW]. cbn in Hwf. destruct Hwf as (L1 & L2 & _).
  split; [split|].
  - cbn. rewrite length_app. split; [lia| exact I].
  - cbn [cells_bytes cbytes app] in HB |- *. rewrite !app_nil_r in HB |- *. exact HB.
  - replace (Z.of_nat (cells_size [CB (n1 + n2)%nat (b1 ++ b2)])) with (Z.of_nat (cells_size ([CB n1 b1] ++ [CB n2 b2]))) by (cbn; lia). exact HW.
Qed.

Lemma rw_cells_CB_split : forall m A n (n1 : nat) (b : list byte),
  rw_cells rsegs m A [CB n b] -> (n1 <= n)%nat ->
  rw_cells rsegs m A [CB n1 (firstn n1 b)] /\ rw_cells rsegs m (A + Z.of_nat n1) [CB (n - n1)%nat (skipn n1 b)].
Proof.
  intros m A n n1 b H Hn.
  pose proof H as [[Hwf _] _]. cbn in Hwf. destruct Hwf as [L _].
  assert (H' : rw_cells rsegs m A ([CB n1 (firstn n1 b)] ++ [CB (n - n1)%nat (skipn n1 b)])).
  { apply (InitMem.rw_cells_recast rsegs m A [CB n b]); [exact H| | |].
    - cbn. rewrite length_firstn, length_skipn. repeat split; try exact I; lia.
    - cbn [cells_bytes cbytes app]. rewrite !app_nil_r. apply firstn_skipn.
    - cbn. lia. }
  apply (proj1 (rw_cells_app _ _ _ _ _)) in H'. destruct H' as [H1 H2]. cbn [cells_size csize Nat.add] in H2. rewrite Nat.add_0_r in H2.
  split; [exact H1| exact H2].
Qed.

Lemma stk_rejoin : forall m A cs mid hi,
  rw_cells rsegs m A cs -> stk rsegs m mid hi -> A <= mid <= A + Z.of_nat (cells_size cs) -> mid <= hi ->
  stk rsegs m A hi.
Proof.
  intros m A cs mid hi RC ST H1 H2.
  pose proof (stk_of_rw_cells rsegs _ _ _ RC) as S1.
  destruct (stk_split rsegs _ _ mid _ S1 ltac:(lia)) as [S2 _].
  eapply stk_merge; [exact S2| exact ST| lia].
Qed.

Section B2.
  Context {HGW : HasGuard} {HCEIL : HasCeiling}.
  Variables (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (rnd : EntryDraw) (arg0 arg1 : list byte) (TID : Z)
            (MPAD : list byte) (S4 S5 S6 S7 S8 S9 S10 S11 : word).
  Hypothesis VSP : valid_sp sp0.
  Hypothesis CEIL : alloc_ceiling = LO sp0.
  Hypothesis VARGV : valid_argv argv.
  Hypothesis VENVP : valid_envp envp.
  Hypothesis ESF : entry_stack_fits sp0 argv envp.
  Hypothesis EARGV : argv = [arg0; arg1].
  Hypothesis HT : 0 < TID < 4194304.
  Hypothesis MALLOC : rmalloc_stmt.
  Hypothesis FREE : rfree_stmt.
  Hypothesis FPR : @fprintf_diag_stmt PState.
  Hypothesis EXK : exit_k_stmt.
  Hypothesis FWR : @fwrite_diag_stmt PState.
  Hypothesis TOW : towrite_stmt.

  Notation usp0 := (bv_unsigned sp0).
  Notation gpv := (Z_to_bv 64 0x10800).
  Notation tpv := (Z_to_bv 64 RATP).
  Notation IMGB := (build_stack_bytes rph sp0 argv envp uid hw rnd).
  Notation LO' := (LO sp0).
  Notation BASE' := (BASE sp0 argv envp uid hw rnd TID).
  Notation FRAME' mm := (MFRAME sp0 argv mm MPAD S7 S6 S5 S4).
  Notation RDINV' := (RDINV sp0 argv envp uid hw rnd TID MPAD S4 S5 S6 S7 S8 S9 S10 S11).
  Notation RDBRK' := (RDBRK sp0 argv envp uid hw rnd TID MPAD S4 S5 S6 S7 S8 S9 S10 S11).
  Notation POSTBODY' := (POSTBODY sp0 argv envp uid hw rnd TID MPAD S4 S5 S6 S7 S8 S9 S10 S11).
  Ltac hyps := first [exact VSP | exact CEIL | exact VARGV | exact VENVP | exact ESF | exact EARGV | exact HT | exact MALLOC | exact FREE | exact FPR | exact EXK | exact FWR | exact TOW].

  Notation GST pc x1 t0 t1 t2 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 F fc mm :=
    (MS (mkR x1 (Z_to_bv 64 (usp0 + -128)) gpv tpv t0 t1 t2 (Z_to_bv 64 2) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 S8 S9 S10 S11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom rsegs)).
  Notation RST pc x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 P1v len fd cap x23 t3 t4 t5 t6 F fc mm :=
    (GST pc x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 P1v) (Z_to_bv 64 len) (Z_to_bv 64 fd) (Z_to_bv 64 cap) (Z_to_bv 64 RSV) (Z_to_bv 64 x23) t3 t4 t5 t6 F fc mm).

  #[using="Type"] Lemma read_clamp : forall (Q : machine_state -> Prop) x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 (len : Z) x20 (cap : Z) x22 x23 t3 t4 t5 t6
      (F : bvmap 5 word) (fc : bv 32) (mm : mem),
    0 <= len <= cap -> cap <= 2^40 ->
    evt rsegs Q (GST 0x13bf8 x1 t0 t1 t2 x9 (Z_to_bv 64 0x10000) a1 (Z_to_bv 64 (Z.min (cap - len) 65536)) a3 a4 a5 a6 a7 x18 (Z_to_bv 64 len) x20 (Z_to_bv 64 cap) x22 x23 t3 t4 t5 t6 F fc mm) ->
    evt rsegs Q (GST 0x13be8 x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 (Z_to_bv 64 len) x20 (Z_to_bv 64 cap) x22 x23 t3 t4 t5 t6 F fc mm).
  Proof.
    intros until mm. intros HL HC0 H.
    zstep. zstep. zstep. if_cases K0; zify_cond K0.
    - replace (Z.min (cap - len) 65536) with (cap + - len) in H by (rewrite ?unsigned_lit in K0 by lia; lia). exact H.
    - zstep. replace (Z.min (cap - len) 65536) with 65536 in H by (rewrite ?unsigned_lit in K0 by lia; lia). exact H.
  Qed.

  #[using="Type"] Lemma len_test_step : forall (Q : machine_state -> Prop) x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 (len : Z) x20 (cap : Z) x22 x23 t3 t4 t5 t6
      (F : bvmap 5 word) (fc : bv 32) (mm : mem),
    0 <= len <= cap -> cap <= 2^40 ->
    evt rsegs Q (GST (if len =? cap then 0x13bb0 else 0x13ba8) x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 (Z_to_bv 64 len) x20 (Z_to_bv 64 cap) x22 x23 t3 t4 t5 t6 F fc mm) ->
    evt rsegs Q (GST 0x13ba4 x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 (Z_to_bv 64 len) x20 (Z_to_bv 64 cap) x22 x23 t3 t4 t5 t6 F fc mm).
  Proof.
    intros until mm. intros HL HC0 H.
    zstep. if_cases K0; zify_cond K0; rewrite ?unsigned_lit in K0 by lia;
      first [ replace (len =? cap) with true in H by (symmetry; apply Z.eqb_eq; lia); exact H
            | replace (len =? cap) with false in H by (symmetry; apply Z.eqb_neq; lia); exact H ].
  Qed.

  #[using="Type"] Lemma entry_test_step : forall (Q : machine_state -> Prop) x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 (cap : Z) x22 x23 t3 t4 t5 t6
      (F : bvmap 5 word) (fc : bv 32) (mm : mem),
    0 < cap <= 2^40 ->
    evt rsegs Q (GST 0x13ba8 x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 (Z_to_bv 64 cap) x22 x23 t3 t4 t5 t6 F fc mm) ->
    evt rsegs Q (GST 0x13b84 x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 (Z_to_bv 64 cap) x22 x23 t3 t4 t5 t6 F fc mm).
  Proof.
    intros until mm. intros HC0 H.
    zstep. if_cases K0; zify_cond K0; rewrite ?unsigned_lit in K0 by lia; first [exact H | exfalso; lia].
  Qed.

  #[using="arg0 VSP CEIL VARGV VENVP ESF EARGV HT FPR"] Lemma rd_read : forall (fd P1v : Z) (st1 : rd_st) (s : PState) x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (x23 : Z) t3 t4 t5 t6
      (F : bvmap 5 word) (fc : bv 32) (mm : mem) (A : Z) (DATA junk : list byte) (errv : word),
    3 <= fd < 2^32 -> nth_error (argv_ptrs sp0 argv envp) 1 = Some (Z_to_bv 64 P1v) ->
    rd_content st1 = map bv_unsigned DATA -> BUF mm s (rd_buf st1) A (rd_cap st1) DATA junk -> Z.of_nat (length DATA) < rd_cap st1 ->
    FRAME' mm -> BASE' mm -> CJ0 mm -> rw_cells rsegs mm RERRNO [C4 errv] -> frm0 fc ->
    implM rsegs (rd_read_part fd (map bv_unsigned arg1) st1) s (POSTBODY' fd P1v)
      (RST 0x13be8 x1 t0 t1 t2 (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7 P1v (zlength (rd_content st1)) fd (rd_cap st1) x23 t3 t4 t5 t6 F fc mm).
  Proof.
    intros until errv. intros FD HP1 HC BU LT FR BA CJ ERR FRM.
    pose proof (sp_facts sp0 VSP CEIL) as SF. unfold LO in SF. assert (ERSV : RSV = 0x2b6c9) by reflexivity.
    destruct BU as (P0 & FA0 & SO0 & BLK & [CAPR CAPK] & LENR & BR). pose proof BR as (BR1 & BR2 & BR3 & BR4 & BR5).
    pose proof BA as (ST & MI & RS & AUX & IMG & SE & SOF & RSS). unfold LO in ST.
    assert (LENZ : zlength (rd_content st1) = Z.of_nat (length DATA)) by (rewrite HC; unfold zlength; rewrite length_map; reflexivity).
    rewrite LENZ. unfold MAX_INPUT in CAPR.
    unfold rd_read_part. cbv beta zeta. rewrite LENZ. unfold READ_CHUNK.
    unfold MFRAME in FR. unfold RERRNO in ERR.
    unfold implM. iprefix.
    eapply read_clamp; [lia| lia|].
    zstep. zstep. zstep.
    apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM rsegs tm s (POSTBODY' fd P1v) msx) end.
    set (LEN := Z.of_nat (length DATA)) in *. set (CNT := Z.min (rd_cap st1 - LEN) 65536) in *.
    assert (ELEN : LEN = Z.of_nat (length DATA)) by reflexivity. assert (ECNT : CNT = Z.min (rd_cap st1 - LEN) 65536) by reflexivity. clearbody LEN CNT. assert (LEN0 : 0 <= LEN) by lia.
    assert (CNTR : 0 < CNT <= rd_cap st1 - LEN /\ CNT <= 65536) by lia.

    destruct (stk_split rsegs mm RSV (RSV + CNT) (RSV + 65536) RSS ltac:(unfold RSV; lia)) as [RSlo RShi].
    destruct (stk_carve rsegs mm RSV (RSV + CNT) (Z.to_nat CNT) RSlo ltac:(lia)) as [_ [rsj RSC]].
    replace (RSV + CNT - Z.of_nat (Z.to_nat CNT)) with RSV in RSC by lia. clear RSlo.
    eapply implM_bind.
    { set (w1 := Z_to_bv 64 RSV). replace RSV with (bv_unsigned w1) by (subst w1; rewrite unsigned_lit; unfold RSV; lia).
      eapply implM_of_enode.
      eapply read_spec with (lo := usp0 - 8388608) (junk := rsj) (errv := errv); subst w1; unfold RATP;
        rewrite ?(unsigned_lit 243744) by lia; rewrite ?(unsigned_lit (usp0 + -128)) by lia; rewrite ?(unsigned_lit RSV) by (unfold RSV; lia); try reflexivity;
        first [exact ST | exact RSC | exact ERR | exact MI | unfold RSV in *; lia]. }
    cbv beta. intros a s' ms' [PO ->].
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & -> & MUc & WMc & MI2 & ST2 & RES).
    unfold RATP in MUc, RES. rewrite ?(unsigned_lit 243744) in MUc by lia. rewrite ?(unsigned_lit (usp0 + -128)) in MUc by lia. rewrite ?(unsigned_lit RSV) in MUc by (unfold RSV; lia).
    rewrite ?(unsigned_lit (usp0 + -128)) in ST2 by lia. rewrite ?(unsigned_lit 243744) in RES by lia. rewrite ?(unsigned_lit RSV) in RES by (unfold RSV; lia).
    change (243744 + -164) with 243580 in MUc, RES.
    transport_after_call rsegs mm m2 MUc WMc.
    replace (ret_pc (Z_to_bv 64 0x13c04)) with (Z_to_bv 64 0x13c04) by (symmetry; rpc).
    rename ST2 into ST2'.
    assert (WOKW : Forall (WOKR sp0) [(usp0 + -128 - 16, usp0 + -128); (RSV, RSV + Z.of_nat (Z.to_nat CNT)); (243580, 243580 + 4)]).
    { unfold WOKR, WOK, LO, RERRNO, RSV. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia. }
    assert (P2 : RHEAP s [(rd_buf st1, A, rd_cap st1)] m2).
    { eapply (RHEAP_munchWR sp0 VSP CEIL); [exact WOKW| exact MUc| exact WMc| | exact P0].
      intros iv [<-|[<-|[<-|[]]]]; cbn [fst snd]; unfold RSV; intros Hiv Hiv2; exfalso; lia. }
    assert (CJ2 : CJ0 m2) by (eapply (CJ0_munchWR sp0 VSP CEIL); [exact WOKW| exact MUc| exact WMc| exact CJ]).
    destruct a as [e|bs]; cbn [read_ret] in *.
    -
      destruct RES as (RSC2 & ERR2 & He).
      assert (RSS2 : stk rsegs m2 RSV (RSV + 65536)).
      { eapply stk_rejoin; [exact RSC2| exact RShi| cbn [cells_size csize Nat.add]; lia| lia]. }
      assert (BA2 : BASE' m2) by (eapply (BASE_munchR sp0 argv envp uid hw rnd TID VSP CEIL VARGV VENVP); [exact BA| exact WOKW| exact MUc| exact WMc| exact MI2| unfold LO; first [exact ST2' | replace (usp0 - 8388608) with (usp0 + -8388608) by lia; exact ST2']| exact RSS2]).
      clear MUc WMc BA WOKW.
      pose proof BA2 as (ST3 & MI3 & RS3 & AUX3 & IMG3 & SE3 & SOF3 & _). pose proof RS3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G28 & GD0 & _ & _).
      pose proof VARGV as (_ & _ & ARGLEN & NONUL & _).
      destruct (argv_cstring sp0 argv envp uid hw rnd m2 IMG3 1 arg1 ltac:(rewrite EARGV; reflexivity) ltac:(clear -SF; Z.div_mod_to_equations; lia))
        as (p1 & slack1 & HP1' & P1LO & P1HI & STR1 & SLK1). unfold str_base, struct_size, argc, envc in P1LO.
      pose proof (IMGB_len sp0 argv envp uid hw rnd VSP VARGV VENVP) as IL. pose proof (IMGB_len47 sp0 argv envp uid hw rnd ESF) as IL47.
      rewrite HP1 in HP1'. assert (EP : Z_to_bv 64 P1v = Z_to_bv 64 p1) by congruence. rewrite EP. clear HP1' EP.
      assert (A1NN : ~ In (Z_to_bv 8 0) arg1) by (rewrite EARGV in NONUL; inversion NONUL as [|? ? ? X]; inversion X; assumption).
      assert (A1LEN : Z.of_nat (length arg1) <= 131071) by (rewrite EARGV in ARGLEN; inversion ARGLEN as [|? ? ? X]; inversion X; assumption).
      unfold implM. iprefix.
      replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 18446744073709551615) by (apply Z_to_bv_eqm; reflexivity).
      zstep. if_cases K0; zify_cond K0; try (exfalso; revert K0; clear; intros K0; rewrite ?unsigned_lit in K0 by lia; lia). clear K0.
      zstep. zstep. zstep. zstep. zstep. zstep. zstep. apply evt_done.
      lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM rsegs tm s (POSTBODY' fd P1v) msx) end.
      cbn [io_diag io_S].
      eapply (fprintf_exit sp0 argv envp uid hw rnd TID S8 S9 S10 S11 VSP CEIL HT FPR (PDReadError (map bv_unsigned arg1)));
        [| exact BA2| exact P2| exact SO0| exact FRM| intros ms'' AE; apply implM_ret; apply evt_done; exact AE].
      cbn [diag_args]. split; [reflexivity|]. exists slack1. rewrite unsigned_lit by lia.
      unfold zb. rewrite zbytes_map_unsigned'. unfold zlength. rewrite !length_map.
      split; [exact STR1|]. split; [apply map_unsigned_pos; exact A1NN|]. split; [lia|].
      split; [lia|]. split; [right; lia|]. split; [unfold GLOBALS_TOP; lia| lia].
    - destruct RES as (RSC2 & ERR2 & Hbs).
      assert (RSS2 : stk rsegs m2 RSV (RSV + 65536)).
      { eapply stk_rejoin; [exact RSC2| exact RShi| cbn [cells_size csize Nat.add]; lia| lia]. }
      assert (BA2 : BASE' m2) by (eapply (BASE_munchR sp0 argv envp uid hw rnd TID VSP CEIL VARGV VENVP); [exact BA| exact WOKW| exact MUc| exact WMc| exact MI2| unfold LO; first [exact ST2' | replace (usp0 - 8388608) with (usp0 + -8388608) by lia; exact ST2']| exact RSS2]).
      clear MUc WMc BA WOKW.
      pose proof BA2 as (ST3 & MI3 & RS3 & AUX3 & IMG3 & SE3 & SOF3 & _).
      unfold implM. iprefix.
      zstep. if_cases K0; zify_cond K0; try (exfalso; revert K0 Hbs CAPR LEN0 ECNT LENR CNTR; clear; intros; rewrite ?unsigned_lit in K0 by lia; lia). clear K0.
      zstep. zstep. if_cases K1; zify_cond K1.
      +
        assert (NPOS : length bs <> 0%nat) by (intros E; rewrite E in K1; apply K1; reflexivity).

        pose proof RSC2 as SRC. apply (proj1 (rw_cells_app _ _ _ [CB (length bs) bs] _)) in SRC. destruct SRC as [SRC _].
        pose proof (rw_cells_bytes_at _ _ _ _ SRC) as SRCB. cbn [cells_bytes cbytes app] in SRCB. rewrite app_nil_r in SRCB. clear SRC.
        pose proof BLK as BLK2. apply (proj1 (rw_cells_app _ _ _ [CB (length DATA) DATA] _)) in BLK2. destruct BLK2 as [BLK1 BLK2].
        cbn [cells_size csize Nat.add] in BLK2. replace (length DATA + 0)%nat with (length DATA) in BLK2 by lia.
        destruct (rw_cells_CB_split m2 (A + Z.of_nat (length DATA)) (Z.to_nat (rd_cap st1 - LEN)) (length bs) junk BLK2 ltac:(lia)) as [BLK2c BLK2r].
        zstep. zstep. zstep. zstep.
        eapply evt_cut.
        { eapply RDriver_lib.memcpy_callv with (src := bs) (junk := firstn (length bs) junk);
            [exact SRCB| lia| lia| lia| unfold RSV; lia
            | replace (A + LEN) with (A + Z.of_nat (length DATA)) by lia; replace (Z.to_nat (Z.of_nat (length bs))) with (length bs) by lia; exact BLK2c
            | unfold RSV; lia| exact MI2]. }
        cbv beta. intros ms' PO.
        destruct PO as (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m3 & -> & MUc & WMc & MI3' & NB3 & _).
        transport_after_call rsegs m2 m3 MUc WMc.
        replace (ret_pc (Z_to_bv 64 0x13b9c)) with (Z_to_bv 64 0x13b9c) by (symmetry; rpc).
        assert (WOKW : Forall (WOK sp0) [(A + LEN, A + LEN + Z.of_nat (length bs))]).
        { unfold WOK. constructor; [right; right; cbn [fst snd]; lia| constructor]. }
        assert (P3 : RHEAP s [(rd_buf st1, A, rd_cap st1)] m3).
        { eapply (RHEAP_munchW sp0 VSP CEIL); [exact WOKW| exact MUc| exact WMc| | exact P2].
          intros iv [<-|[]]. cbn [fst snd]. intros _ _. exists (rd_buf st1, A, rd_cap st1). split; [left; reflexivity|]. cbn [fst snd blk_addr blk_size]. lia. }
        assert (BA3 : BASE' m3) by (eapply (BASE_munch sp0 argv envp uid hw rnd TID VSP CEIL VARGV VENVP); [exact BA2| exact WOKW| exact MUc| exact WMc| exact MI3'| unfold LO; first [exact ST3| replace (usp0 - 8388608) with (usp0 + -8388608) by lia; exact ST3]]).
        assert (CJ3 : CJ0 m3) by (eapply (CJ0_munchW sp0 VSP CEIL); [exact WOKW| exact MUc| exact WMc| exact CJ2]).
        clear MUc WMc WOKW.

        zstep. zstep.
        assert (LEN' : zlength (rd_content st1 ++ u8s_of_bytes bs) = LEN + Z.of_nat (length bs)).
        { unfold zlength, u8s_of_bytes. rewrite length_app, length_map. unfold zlength in LENZ. lia. }
        replace (Z.of_nat (length bs) + LEN) with (LEN + Z.of_nat (length bs)) by lia.
        eapply len_test_step; [lia| lia|].
        apply evt_done.
        lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM rsegs tm s (POSTBODY' fd P1v) msx) end.
        replace (length bs =? 0)%nat with false by (symmetry; apply Nat.eqb_neq; exact NPOS).
        apply implM_ret. apply evt_done. cbn [POSTBODY]. unfold RDINV, rd_pc. cbn [rd_content rd_cap rd_buf].
        rewrite LEN'.

        pose proof (rw_cells_CB_join _ _ _ _ _ _ BLK1 ltac:(replace (A + Z.of_nat (length DATA)) with (A + LEN) by lia; replace (length bs) with (Z.to_nat (Z.of_nat (length bs))) by lia; exact NB3)) as BLK1'.
        assert (BLK' : rw_cells rsegs m3 A [CB (length (DATA ++ bs)) (DATA ++ bs); CB (Z.to_nat (rd_cap st1 - Z.of_nat (length (DATA ++ bs)))) (skipn (length bs) junk)]).
        { apply (proj2 (rw_cells_app _ _ _ [CB (length (DATA ++ bs)) (DATA ++ bs)] _)). rewrite length_app. split.
          - replace (length DATA + length bs)%nat with (length DATA + Z.to_nat (Z.of_nat (length bs)))%nat by lia. exact BLK1'.
          - cbn [cells_size csize Nat.add].
            replace (A + Z.of_nat (length DATA + length bs + 0)) with (A + Z.of_nat (length DATA) + Z.of_nat (length bs)) by lia.
            replace (Z.to_nat (rd_cap st1 - Z.of_nat (length DATA + length bs))) with (Z.to_nat (rd_cap st1 - LEN) - length bs)%nat by lia. exact BLK2r. }
        do 17 eexists. exists F, fc, m3, A, (DATA ++ bs), (skipn (length bs) junk), errv.
        split; [reflexivity|].
        split; [rewrite HC; unfold u8s_of_bytes; rewrite map_app; reflexivity|].
        split; [| split; [exact FR| split; [exact BA3| split; [exact CJ3| split; [exact ERR2| exact FRM]]]]].
        split; [exact P3|]. split; [exact FA0|]. split; [exact SO0|]. split; [exact BLK'|]. unfold MAX_INPUT. split; [split; [lia| exact CAPK]|]. split; [rewrite length_app; lia| exact BR].
      +
        assert (Ebs : bs = []) by (destruct bs; [reflexivity| cbn [length] in K1; exfalso; rewrite ?unsigned_lit in K1 by lia; lia]). subst bs.
        cbn [length Nat.eqb Z.of_nat]. apply evt_done.
        lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM rsegs tm s (POSTBODY' fd P1v) msx) end.
        apply implM_ret. apply evt_done.
        cbn [POSTBODY]. unfold RDBRK.
        do 16 eexists. exists F, fc, m2, A, (rd_cap st1), DATA, junk, errv.
        split; [rewrite LENZ; reflexivity|].
        split; [exact HC|]. split; [| split; [exact FR| split; [exact BA2| split; [exact CJ2| split; [exact ERR2| exact FRM]]]]].
        split; [exact P2|]. split; [exact FA0|]. split; [exact SO0|]. split; [rewrite ELEN in BLK; exact BLK|]. unfold MAX_INPUT. split; [split; [lia| exact CAPK]|]. split; [lia| exact BR].
  Qed.
End B2.
