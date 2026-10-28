(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation Strings.String.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Agree MonadX Ceiling.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.Malloc Require Import MallocBlocks MallocTree MallocHINV Malloc_iface.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import InitStack.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Malloc Require Import InitMem.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.P0 Require Import Startup_lib.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Stdio_base Printf_lib Startup RefImpl F_printf_iface Stdio_iface Stdio_init F_printf_diag RDriver_lib RDriver_kit RDriver_ctx RF_main_A RF_main_B1 RF_main_B2.
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

Lemma shiftr26_zero_iff : forall a, 0 <= a -> (Z.shiftr a 26 = 0 <-> a < 67108864).
Proof.
  intros a Ha. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 26) with 67108864.
  split; intros H; [| apply Z.div_small; lia].
  destruct (Z.lt_ge_cases a 67108864) as [L|G]; [exact L|]. exfalso.
  pose proof (Z.div_le_mono 67108864 a 67108864 ltac:(lia) G) as M. rewrite Z.div_same in M by lia. lia.
Qed.

Section B3.
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

  #[using="arg0 VSP CEIL VARGV VENVP ESF EARGV HT MALLOC FREE FPR FWR TOW"] Lemma rd_body : forall (fd P1v : Z) (st : rd_st) (s : PState) ms,
    3 <= fd < 2^32 -> nth_error (argv_ptrs sp0 argv envp) 1 = Some (Z_to_bv 64 P1v) ->
    RDINV' fd P1v st s ms ->
    implM rsegs (read_loop_body (io_S ps_so set_so_ps) raw_malloc raw_free RSV fd (map bv_unsigned arg1) st) s (POSTBODY' fd P1v) ms.
  Proof.
    intros fd P1v st s ms FD HP1 RI.
    destruct RI as (x1 & t0 & t1 & t2 & x9 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & F & fc & mm & A & DATA & junk & errv
                    & -> & HC & BU & FR & BA & CJ & ERR & FRM).
    pose proof (sp_facts sp0 VSP CEIL) as SF. unfold LO in SF. assert (ERSV : RSV = 0x2b6c9) by reflexivity.
    assert (LENZ : zlength (rd_content st) = Z.of_nat (length DATA)) by (rewrite HC; unfold zlength; rewrite length_map; reflexivity).
    pose proof BU as (P0 & FA0 & SO0 & BLK & [CAPR [k [K0' CAPK]]] & LENR & BR). unfold MAX_INPUT in CAPR.
    rewrite read_loop_body_eq. unfold rd_grow_part, rd_pc. rewrite LENZ.
    pose proof BA as (ST & MI & RS & AUX & IMG & SE & SOF & RSS). unfold LO in ST. unfold RERRNO in ERR. unfold MFRAME in FR.
    pose proof BR as (BR1 & BR2 & BR3 & BR4 & BR5).
    destruct (Z.eqb_spec (Z.of_nat (length DATA)) (rd_cap st)) as [K00|K00].
    2:{
        unfold implM. iprefix. zstep. zstep. apply evt_done.
        lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM rsegs tm s (POSTBODY' fd P1v) msx) end.
        apply implM_mret_bind. cbv iota beta.
        rewrite <- LENZ. eapply (rd_read sp0 argv envp uid hw rnd arg0 arg1 TID MPAD S4 S5 S6 S7 S8 S9 S10 S11);
          first [hyps | exact FD | exact HP1 | exact HC | exact BU | exact BA | exact CJ | unfold MFRAME; exact FR | unfold RERRNO; exact ERR | exact FRM | lia]. }

    unfold implM. iprefix.
    zstep. zstep. if_cases K0; zify_cond K0.
    {
      assert (GE : 67108864 <= rd_cap st).
      { destruct (Z.lt_ge_cases (rd_cap st) 67108864) as [L|G]; [| exact G]. exfalso. apply K0.
        apply (proj2 (shiftr26_zero_iff (Z.of_nat (length DATA)) ltac:(lia))). lia. }
      replace (MAX_INPUT <=? rd_cap st) with true by (symmetry; apply Z.leb_le; unfold MAX_INPUT; lia).
      pose proof RS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G28 & GD0 & _ & _).
      zstep. zstep. zstep. zstep. zstep. zstep. apply evt_done.
      lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM rsegs tm s (POSTBODY' fd P1v) msx) end.
      apply implM_bind_assoc. cbn [io_diag io_S].
      eapply (fprintf_exit sp0 argv envp uid hw rnd TID S8 S9 S10 S11 VSP CEIL HT FPR PDTooBig);
        [| exact BA| exact P0| exact SO0| exact FRM| intros ms'' AE; apply implM_mret_bind; cbv beta iota; apply implM_ret; apply evt_done; exact AE].
      cbn [diag_args]. split; [reflexivity|]. rewrite unsigned_lit by lia. reflexivity. }

    assert (LTM : rd_cap st < 67108864).
    { rewrite <- K00. apply (proj1 (shiftr26_zero_iff (Z.of_nat (length DATA)) ltac:(lia))). exact K0. }
    replace (MAX_INPUT <=? rd_cap st) with false by (symmetry; apply Z.leb_gt; unfold MAX_INPUT; lia).
    zstep. zstep. zstep. apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM rsegs tm s (POSTBODY' fd P1v) msx) end.
    apply implM_bind_assoc.
    replace (Z.shiftl (Z.of_nat (length DATA)) 1) with (rd_cap st * 2) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    eapply implM_bind.
    { unfold rmalloc_stmt in MALLOC.
      eapply MALLOC with (lo := usp0 - 8388608) (B := usp0); try reflexivity; unfold RATP; rewrite ?(unsigned_lit 243744) by lia; rewrite ?(unsigned_lit (usp0 + -128)) by lia;
        first [ exact P0 | exact AUX | exact ST | exact ERR | exact MI | unfold RMALLOC_STACK; lia | lia ]. }
    cbv beta. intros r s1 ms1 PO.
    destruct PO as (u0 & u1 & u2 & ra0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 & errv1 & -> & MI1 & ST1 & ERR1 & AUX1 & HPR & FAE & SOE & RR).
    unfold RATP in ERR1. rewrite ?(unsigned_lit 243744) in ERR1 by lia. rewrite ?(unsigned_lit (usp0 + -128)) in ST1 by lia. rewrite ?(unsigned_lit (usp0 + -128)) in HPR by lia.
    change (243744 + -164) with 243580 in ERR1.
    replace (ret_pc (Z_to_bv 64 0x13bc4)) with (Z_to_bv 64 0x13bc4) by (symmetry; rpc).
    assert (BA1 : BASE' m1) by (eapply (BASE_heap_pres sp0 argv envp uid hw rnd TID); [exact BA| exact HPR| exact MI1| unfold LO; first [exact ST1| replace (usp0 - 8388608) with (usp0 + -8388608) by lia; exact ST1]| exact AUX1]).
    assert (CJ1 : CJ0 m1) by (eapply CJ0_heap_pres; [exact HPR| exact CJ]).
    assert (FR1 : FRAME' m1) by (unfold MFRAME; eapply rheap_pres_rw_cells; [exact HPR| exact FR| left; cbn; lia]). unfold MFRAME in FR1.
    assert (BLK1 : rw_cells rsegs m1 A [CB (length DATA) DATA; CB (Z.to_nat (rd_cap st - Z.of_nat (length DATA))) junk]).
    { eapply rheap_pres_rw_cells; [exact HPR| exact BLK|]. right; right. exists (rd_buf st, A, rd_cap st). split; [left; reflexivity|]. cbn [blk_addr blk_size fst snd cells_size csize Nat.add]. lia. }
    clear FR BLK ST MI AUX IMG RS SE SOF ERR RSS.
    destruct r as [nb|].
    2:{
        destruct RR as [-> HEAP1].
        pose proof BA1 as (ST & MI & RS & AUX & IMG & SE & SOF & RSS). unfold LO in ST.
        pose proof RS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G28 & GD0 & _ & _).
        unfold implM. iprefix. zstep. if_cases K1; zify_cond K1; try (exfalso; lia). clear K1.
        zstep. zstep. zstep. zstep. zstep. zstep. zstep. apply evt_done.
        lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM rsegs tm s1 (POSTBODY' fd P1v) msx) end.
        apply implM_bind_assoc. cbn [io_diag io_S].
        eapply (fwrite_exit sp0 argv envp uid hw rnd TID S8 S9 S10 S11 VSP CEIL HT FWR TOW);
          [exact BA1| exact HEAP1| rewrite SOE; exact SO0| intros ms'' AE; apply implM_mret_bind; cbv beta iota; apply implM_ret; apply evt_done; exact AE]. }

    destruct RR as (A' & junk' & -> & BR' & HEAP1 & NBLK & HEXP). clear HEXP.
    pose proof BR' as (BQ1 & BQ2 & BQ3 & BQ4 & BQ5).
    pose proof (RMalloc_ifaceP.RHEAP_blocks_nodup_proof _ _ _ HEAP1) as ND.
    assert (DISJ : A' + rd_cap st * 2 <= A \/ A + rd_cap st <= A').
    { pose proof (RMalloc_ifaceP.RHEAP_blocks_disjoint_proof _ _ _ (nb, A', rd_cap st * 2) (rd_buf st, A, rd_cap st) HEAP1 ltac:(left; reflexivity) ltac:(right; left; reflexivity)) as D.
      cbn [blk_id blk_addr blk_size fst snd] in D. apply D. cbn [map blk_id fst] in ND. inversion ND as [|x l NI ND']; subst. intros E. apply NI. rewrite E. left. reflexivity. }
    apply implM_bind_assoc.
    pose proof BA1 as (ST & MI & RS & AUX & IMG & SE & SOF & RSS). unfold LO in ST.
    unfold implM. iprefix. zstep. if_cases K1; zify_cond K1; try (exfalso; rewrite ?unsigned_lit in K1 by lia; lia). clear K1.
    zstep. zstep. if_cases K2; zify_cond K2; try (exfalso; lia). clear K2.
    zstep. zstep. zstep. zstep.

    apply (rw_cells_split_CB _ _ _ [] _ _ [] [length DATA; Z.to_nat (rd_cap st * 2) - length DATA]%nat) in NBLK; [| cbn; lia]. cbn [mk_CB_cells app] in NBLK.
    apply (proj1 (rw_cells_app _ _ _ [CB (length DATA) (firstn (length DATA) junk')] _)) in NBLK. destruct NBLK as [NB1 NB2]. cbn [cells_size csize Nat.add] in NB2.
    pose proof BLK1 as SRC. apply (proj1 (rw_cells_app _ _ _ [CB (length DATA) DATA] _)) in SRC. destruct SRC as [SRC _].
    pose proof (rw_cells_bytes_at _ _ _ _ SRC) as SRCB. cbn [cells_bytes cbytes app] in SRCB. rewrite app_nil_r in SRCB. clear SRC.
    eapply evt_cut.
    { eapply RDriver_lib.memcpy_callv with (src := DATA) (junk := firstn (length DATA) junk');
        [exact SRCB| lia| lia| lia| lia| replace (Z.to_nat (Z.of_nat (length DATA))) with (length DATA) by lia; exact NB1| lia| exact MI]. }
    cbv beta. intros ms' PO.
    destruct PO as (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m2 & -> & MUc & WMc & MI2 & NB1' & _).
    ua. transport_after_call rsegs m1 m2 MUc WMc.
    replace (ret_pc (Z_to_bv 64 0x13be0)) with (Z_to_bv 64 0x13be0) by (symmetry; rpc).
    assert (WOKW : Forall (WOK sp0) [(A', A' + Z.of_nat (length DATA))]).
    { unfold WOK. constructor; [right; right; cbn [fst snd]; lia| constructor]. }
    assert (P2 : RHEAP s1 [(nb, A', rd_cap st * 2); (rd_buf st, A, rd_cap st)] m2).
    { eapply (RHEAP_munchW sp0 VSP CEIL); [exact WOKW| exact MUc| exact WMc| | exact HEAP1].
      intros iv [<-|[]]. cbn [fst snd]. intros _ _. exists (nb, A', rd_cap st * 2). split; [left; reflexivity|]. cbn [fst snd blk_addr blk_size]. lia. }
    assert (BA2 : BASE' m2) by (eapply (BASE_munch sp0 argv envp uid hw rnd TID VSP CEIL VARGV VENVP); [exact BA1| exact WOKW| exact MUc| exact WMc| exact MI2| unfold LO; first [exact ST| replace (usp0 - 8388608) with (usp0 + -8388608) by lia; exact ST]]).
    assert (CJ2 : CJ0 m2) by (eapply (CJ0_munchW sp0 VSP CEIL); [exact WOKW| exact MUc| exact WMc| exact CJ1]).
    clear MUc WMc BA1 CJ1 ST MI RS AUX IMG SE SOF WOKW RSS.
    pose proof BA2 as (ST & MI & RS & AUX & IMG & SE & SOF & RSS). unfold LO in ST.

    zstep. zstep. apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM rsegs tm s1 (POSTBODY' fd P1v) msx) end.
    eapply implM_bind.
    { unfold rfree_stmt in FREE.
      eapply FREE with (lo := usp0 - 8388608) (B := usp0) (p := rd_buf st) (A := A) (n := rd_cap st); try reflexivity; unfold RATP;
        rewrite ?(unsigned_lit 243744) by lia; rewrite ?(unsigned_lit (usp0 + -128)) by lia;
        first [ exact P2 | right; left; reflexivity | exact AUX | exact ST | exact MI | exact ERR1 | unfold RFREE_STACK; lia | lia ]. }
    cbv beta. intros [] s2 ms2 PO.
    destruct PO as (w0 & w1 & w2 & rb0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m3 & -> & MI3 & ST3 & ERR3 & AUX3 & HPR3 & FAE3 & SOE3 & HEAP3).
    unfold RATP in ERR3. rewrite ?(unsigned_lit 243744) in ERR3 by lia. rewrite ?(unsigned_lit (usp0 + -128)) in ST3 by lia. rewrite ?(unsigned_lit (usp0 + -128)) in HPR3 by lia.
    change (243744 + -164) with 243580 in ERR3.
    replace (ret_pc (Z_to_bv 64 0x13be8)) with (Z_to_bv 64 0x13be8) by (symmetry; rpc).
    rewrite (RDriver_lib.lb_remove_second (rd_buf st) (nb, A', rd_cap st * 2) (rd_buf st, A, rd_cap st) [] eq_refl ND) in HPR3, HEAP3.
    assert (BA3 : BASE' m3) by (eapply (BASE_heap_pres sp0 argv envp uid hw rnd TID); [exact BA2| exact HPR3| exact MI3| unfold LO; first [exact ST3| replace (usp0 - 8388608) with (usp0 + -8388608) by lia; exact ST3]| exact AUX3]).
    assert (CJ3 : CJ0 m3) by (eapply CJ0_heap_pres; [exact HPR3| exact CJ2]).
    assert (FR3 : FRAME' m3) by (unfold MFRAME; eapply rheap_pres_rw_cells; [exact HPR3| exact FR1| left; cbn; lia]).
    assert (NB3 : rw_cells rsegs m3 A' [CB (length DATA) DATA; CB (Z.to_nat (rd_cap st * 2 - Z.of_nat (length DATA))) (firstn (Z.to_nat (rd_cap st * 2) - length DATA)%nat (skipn (length DATA) junk'))]).
    { eapply rheap_pres_rw_cells; [exact HPR3| |].
      - apply (proj2 (rw_cells_app _ _ _ [CB (length DATA) DATA] _)). split; [replace (length DATA) with (Z.to_nat (Z.of_nat (length DATA))) at 1 by lia; exact NB1'|].
        cbn [cells_size csize Nat.add]. replace (Z.to_nat (rd_cap st * 2 - Z.of_nat (length DATA))) with (Z.to_nat (rd_cap st * 2) - length DATA)%nat by lia. exact NB2.
      - right; right. exists (nb, A', rd_cap st * 2). split; [left; reflexivity|]. cbn [blk_addr blk_size fst snd cells_size csize Nat.add]. lia. }
    clear HPR3 FR1 NB1' NB2.

    apply implM_mret_bind. cbv beta iota.
    rewrite <- LENZ.
    eapply (rd_read sp0 argv envp uid hw rnd arg0 arg1 TID MPAD S4 S5 S6 S7 S8 S9 S10 S11 VSP CEIL VARGV VENVP ESF EARGV HT FPR fd P1v (mkRd nb (rd_cap st * 2) (rd_content st)) s2);
      cbn [rd_buf rd_cap rd_content]; first [exact FD | exact HP1 | exact HC | exact FR3 | exact BA3 | exact CJ3 | unfold RERRNO; exact ERR3 | exact FRM | lia | idtac].
    split; [exact HEAP3|]. split; [rewrite FAE3; exact (eq_trans FAE FA0)|]. split; [rewrite SOE3; exact (eq_trans SOE SO0)|]. split; [exact NB3|].
    assert (CAP2 : rd_cap st * 2 <= 67108864).
    { rewrite CAPK in LTM |- *. change 67108864 with (2 ^ 26) in LTM |- *. apply Z.pow_lt_mono_r_iff in LTM; [| lia| lia].
      replace (2 ^ k * 2) with (2 ^ (k + 1)) by (rewrite Z.pow_add_r by lia; lia). apply Z.pow_le_mono_r; lia. }
    unfold MAX_INPUT. split; [split; [lia| exists (k + 1); split; [lia| rewrite CAPK, Z.pow_add_r by lia; lia]]|]. split; [lia| exact BR'].
  Qed.

  Definition POSTLOOP (fd P1v : Z) (r : rd_result) (s : PState) (ms : machine_state) : Prop :=
    match r with
    | RdExit => rat_exit 2 s ms
    | RdDone b c => RDBRK' fd P1v b c s ms
    end.

  #[using="arg0 VSP CEIL VARGV VENVP ESF EARGV HT MALLOC FREE FPR FWR TOW"] Lemma rd_loop : forall (fuel : nat) (fd P1v : Z) (st : rd_st) (s : PState) ms,
    3 <= fd < 2^32 -> nth_error (argv_ptrs sp0 argv envp) 1 = Some (Z_to_bv 64 P1v) ->
    RDINV' fd P1v st s ms ->
    implM rsegs (mloop fuel (read_loop_body (io_S ps_so set_so_ps) raw_malloc raw_free RSV fd (map bv_unsigned arg1)) st) s (POSTLOOP fd P1v) ms.
  Proof.
    induction fuel as [|fuel IH]; intros fd P1v st s ms FD HP1 RI.
    - cbn [mloop]. apply implM_unr.
    - apply implM_loop_S. eapply implM_mono; [apply rd_body; [exact FD| exact HP1| exact RI]|].
      intros [st'|[|b c]] s' ms' PO; cbn [POSTBODY POSTLOOP] in PO |- *.
      + apply IH; [exact FD| exact HP1| exact PO].
      + apply evt_done. exact PO.
      + apply evt_done. exact PO.
  Qed.
End B3.
