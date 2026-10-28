(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation Strings.String.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP InitMem MonadX.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import DrvAgree Startup_kit STRW_tac F_fmt_fp_lib Printf_fmts.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_syscalls F_memcpy StdioFiles Startup Exit F_printf_iface Stdio_iface Stdio_kit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Malloc Require Import MallocBlocks MallocTree MallocHINV Malloc_iface.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import RMallocRep RMallocTree RMalloc_iface Harness_iface RDriver_iface RDriver_facts RDriver_kit RDriver_ctx RF_main_A RF_main_B1 RF_main_B2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import Prelim STree Malloc Monad Stdio Driver Prog.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import RunDraw.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac ua := idtac.
Ltac rpc := apply ret_pc_even; [lia| reflexivity].

Section CANSEC1. Context {rc : runConstT}.
Lemma shiftr26_zero_iff : forall a, 0 <= a -> (Z.shiftr a 26 = 0 <-> a < 67108864).
Proof.
  intros a Ha. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 26) with 67108864.
  split; intros H; [| apply Z.div_small; lia].
  destruct (Z.lt_ge_cases a 67108864) as [L|G]; [exact L|]. exfalso.
  pose proof (Z.div_le_mono 67108864 a 67108864 ltac:(lia) G) as M. rewrite Z.div_same in M by lia. lia.
Qed.

Section B3.
  Variables (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (draw : EntryDraw) (arg0 arg1 : list byte) (TID : Z)
            (J8 : list byte) (S4 S5 S6 S7 S8 S9 S10 S11 : word).
  Hypothesis VSP : dvalid_sp sp0 argv envp.
  Hypothesis VARGV : valid_argv argv.
  Hypothesis VENVP : valid_envp envp.
  Hypothesis EARGV : argv = [arg0; arg1].
  Hypothesis HT : 0 < TID < 4194304.
  Hypothesis MALLOC : rmalloc_stmt.
  Hypothesis FREE : rfree_stmt.
  Hypothesis FPR : @fprintf_diag_stmt PState.
  Hypothesis FWX : fwritex_stderr_stmt.
  Hypothesis SWF : stdio_write_flush_stmt.
  Hypothesis FWR : @fwrite_diag_stmt PState.
  Hypothesis TOW : towrite_stmt.

  Notation usp0 := (bv_unsigned sp0).
  Notation gpv := (Z_to_bv 64 0x10800).
  Notation tpv := (Z_to_bv 64 RATP).
  Notation IMGB := (build_stack_bytes pph sp0 argv envp uid hw draw).
  Notation LO' := (LO sp0).
  Notation BASE' := (BASE sp0 argv envp uid hw draw TID).
  Notation FRAME' mm := (MFRAME sp0 argv mm J8 S7 S6 S5 S4).
  Notation RDINV' := (RDINV sp0 argv envp uid hw draw TID J8 S4 S5 S6 S7 S8 S9 S10 S11).
  Notation RDBRK' := (RDBRK sp0 argv envp uid hw draw TID J8 S4 S5 S6 S7 S8 S9 S10 S11).
  Notation POSTBODY' := (POSTBODY sp0 argv envp uid hw draw TID J8 S4 S5 S6 S7 S8 S9 S10 S11).
  Ltac hyps := first [exact VSP | exact VARGV | exact VENVP | exact EARGV | exact HT | exact MALLOC | exact FREE | exact FPR | exact FWX | exact SWF | exact FWR | exact TOW].

  Notation GST pc x1 t0 t1 t2 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 F fc mm :=
    (MS (mkR x1 (Z_to_bv 64 (usp0 + -128)) gpv tpv t0 t1 t2 (Z_to_bv 64 2) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 S8 S9 S10 S11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).

  (* [comment removed for export] *)
  Definition after_test (fd : Z) (st : rd_st) : M PState (rd_st + rd_result) :=
    g <- (if MAX_INPUT <=? rd_cap st then io_diag Prog.io DTooBig ;;; mret None
          else nb <- raw_malloc (rd_cap st * 2) ;;
               match nb with
               | None => io_diag Prog.io DOom ;;; mret None
               | Some nb' => raw_free (rd_buf st) ;;; mret (Some (mkRd nb' (rd_cap st * 2) (rd_content st)))
               end) ;;
    match g with None => mret (inr RdExit) | Some st1 =>
         let want0 := rd_cap st1 - zlength (rd_content st) in
         let cnt := if 65536 <? want0 then 65536 else want0 in
         a <- msys (NRead fd UREAD_STAGE cnt) (dec_read UREAD_STAGE cnt) ;;
         match a with
         | RdErr _ => io_diag Prog.io (DReadError (map bv_unsigned arg1)) ;;; mret (inr RdExit)
         | RdData bs =>
             if (length bs =? 0)%nat then mret (inr (RdDone (rd_buf st1) (rd_content st1)))
             else mret (inl (mkRd (rd_buf st1) (rd_cap st1) (rd_content st1 ++ u8s_of_bytes bs)))
         end end.

  (* [comment removed for export] *)
  Lemma rd_nogrow : forall (fd P1v : Z) (st : rd_st) (s : PState) x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
      (F : bvmap 5 word) (fc : bv 32) (mm : mem) (A : Z) (DATA junk sj : list byte) (errv : word),
    3 <= fd < 2^32 -> nth_error (argv_ptrs sp0 argv envp) 1 = Some (Z_to_bv 64 P1v) ->
    rd_content st = map bv_unsigned DATA -> BUF mm s (rd_buf st) A (rd_cap st) DATA junk -> STAGE mm sj ->
    Z.of_nat (length DATA) < rd_cap st ->
    FRAME' mm -> BASE' mm -> rw_cells usegs mm RERRNO [C4 errv] -> frm0 fc ->
    implM usegs (rd_read_part fd (map bv_unsigned arg1) st) s (POSTBODY' fd P1v)
      (GST 0x14434 x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 P1v) (Z_to_bv 64 (zlength (rd_content st))) (Z_to_bv 64 fd) (Z_to_bv 64 (rd_cap st)) (Z_to_bv 64 UREAD_STAGE) (Z_to_bv 64 A) t3 t4 t5 t6 F fc mm).
  Proof.
    intros until errv. intros FD HP1 HC BU SJ LT FR BA ERR FRM.
    pose proof BA as (_ & MI & _).
    unfold implM. eapply impl_evt; [| intros ms' H; exact H].
    zstep. zstep. apply evt_done.
    eapply (rd_read sp0 argv envp uid hw draw arg0 arg1 TID J8 S4 S5 S6 S7 S8 S9 S10 S11);
      first [hyps | exact FD | exact HP1 | exact HC | exact BU | exact SJ | exact BA | exact FR | exact ERR | exact FRM | lia].
  Qed.

  (* [comment removed for export] *)
  Lemma rd_grow : forall (fd P1v : Z) (st : rd_st) (s : PState) x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
      (F : bvmap 5 word) (fc : bv 32) (mm : mem) (A : Z) (DATA junk sj : list byte) (errv : word),
    3 <= fd < 2^32 -> nth_error (argv_ptrs sp0 argv envp) 1 = Some (Z_to_bv 64 P1v) ->
    rd_content st = map bv_unsigned DATA -> BUF mm s (rd_buf st) A (rd_cap st) DATA junk -> STAGE mm sj ->
    Z.of_nat (length DATA) = rd_cap st ->
    FRAME' mm -> BASE' mm -> rw_cells usegs mm RERRNO [C4 errv] -> frm0 fc ->
    implM usegs (after_test fd st) s (POSTBODY' fd P1v)
      (GST 0x1443c x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 P1v) (Z_to_bv 64 (zlength (rd_content st))) (Z_to_bv 64 fd) (Z_to_bv 64 (rd_cap st)) (Z_to_bv 64 UREAD_STAGE) (Z_to_bv 64 A) t3 t4 t5 t6 F fc mm).
  Proof.
    intros until errv. intros FD HP1 HC BU SJ K00 FR BA ERR FRM.
    pose proof (sp_facts sp0 argv envp VSP) as SF. unfold LO in SF.
    assert (LENZ : zlength (rd_content st) = Z.of_nat (length DATA)) by (rewrite HC; unfold zlength; rewrite length_map; reflexivity).
    pose proof BU as (P0 & FA0 & SO0 & _ & BLK & [CAPR [k [K0' CAPK]]] & LENR & BR). unfold MAX_INPUT in CAPR.
    pose proof BA as (ST & MI & RS & AUX & IMG & SE & SOF & TR). unfold LO in ST. unfold RERRNO in ERR. unfold MFRAME in FR.
    pose proof BR as (BR1 & BR2 & BR3 & BR4 & BR5). atop_facts. pose proof PSTAGE_LEN_Z as PSTAGER.
    unfold STAGE, UREAD_STAGE in SJ.
    rewrite LENZ. unfold after_test.
    unfold implM. iprefix.
    zstep. zstep. if_cases K0; zify_cond K0.
    { (* [comment removed for export] *)
      assert (GE : 67108864 <= rd_cap st).
      { destruct (Z.lt_ge_cases (rd_cap st) 67108864) as [L|G]; [| exact G]. exfalso. apply K0.
        apply (proj2 (shiftr26_zero_iff (Z.of_nat (length DATA)) ltac:(lia))). lia. }
      replace (MAX_INPUT <=? rd_cap st) with true by (symmetry; apply Z.leb_le; unfold MAX_INPUT; lia).
      pose proof RS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G28 & GD0 & _).
      zstep. zstep. zstep. zstep. zstep. zstep. apply evt_done.
      lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm s (POSTBODY' fd P1v) msx) end.
      apply implM_bind_assoc. cbn [io_diag io_S].
      eapply (fprintf_exit sp0 argv envp uid hw draw TID S8 S9 S10 S11 VSP HT FPR FWX SWF DTooBig);
        [| exact BA| exact P0| exact SO0| exact FRM| intros ms'' AE; apply implM_mret_bind; cbv beta iota; apply implM_ret; apply evt_done; exact AE].
      cbn [diag_args]. split; [reflexivity|]. rewrite unsigned_lit by lia. reflexivity. }
    (* [comment removed for export] *)
    assert (LTM : rd_cap st < 67108864).
    { rewrite <- K00. apply (proj1 (shiftr26_zero_iff (Z.of_nat (length DATA)) ltac:(lia))). exact K0. }
    replace (MAX_INPUT <=? rd_cap st) with false by (symmetry; apply Z.leb_gt; unfold MAX_INPUT; lia).
    zstep. zstep. zstep. apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm s (POSTBODY' fd P1v) msx) end.
    apply implM_bind_assoc.
    replace (Z.shiftl (Z.of_nat (length DATA)) 1) with (rd_cap st * 2) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    eapply implM_bind.
    { unfold rmalloc_stmt in MALLOC.
      eapply MALLOC with (lo := usp0 - 8388608) (B := usp0); try reflexivity; unfold RATP; rewrite ?(unsigned_lit 295416) by lia; rewrite ?(unsigned_lit (usp0 + -128)) by lia;
        first [ exact P0 | exact AUX | exact ST | exact ERR | exact MI | unfold RMALLOC_STACK; lia | lia ]. }
    cbv beta. intros r s1 ms1 PO.
    destruct PO as (u0 & u1 & u2 & ra0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 & errv1 & -> & MI1 & ST1 & ERR1 & AUX1 & HPR & FAE & SOE & RR).
    unfold RATP in ERR1. rewrite ?(unsigned_lit 295416) in ERR1 by lia. rewrite ?(unsigned_lit (usp0 + -128)) in ST1 by lia. rewrite ?(unsigned_lit (usp0 + -128)) in HPR by lia.
    change (295416 + -164) with 295252 in ERR1.
    replace (ret_pc (Z_to_bv 64 0x14450)) with (Z_to_bv 64 0x14450) by (symmetry; rpc).
    assert (BA1 : BASE' m1) by (eapply (BASE_heap_pres sp0 argv envp uid hw draw TID); [exact BA| exact HPR| exact MI1| unfold LO; first [exact ST1| replace (usp0 - 8388608) with (usp0 + -8388608) by lia; exact ST1]| exact AUX1]).
    assert (FR1 : FRAME' m1) by (unfold MFRAME; eapply rheap_pres_rw_cells; [exact HPR| exact FR| left; cbn; lia]). unfold MFRAME in FR1.
    assert (BLK1 : rw_cells usegs m1 A [CB (length DATA) DATA; CB (Z.to_nat (rd_cap st - Z.of_nat (length DATA))) junk]).
    { eapply rheap_pres_rw_cells; [exact HPR| exact BLK|]. right; right. exists (rd_buf st, A, rd_cap st). split; [left; reflexivity|]. cbn [blk_addr blk_size fst snd cells_size csize Nat.add]. lia. }
    assert (SJ1 : rw_cells usegs m1 229609 [CB PSTAGE_LEN sj]).
    { eapply rheap_pres_rw_cells; [exact HPR| exact SJ|]. right; left. cbn [cells_size csize Nat.add]. unfold RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP. lia. }
    clear FR BLK SJ ST MI AUX IMG RS SE SOF ERR.
    destruct r as [nb|].
    2:{ (* [comment removed for export] *)
        destruct RR as [-> HEAP1].
        pose proof BA1 as (ST & MI & RS & AUX & IMG & SE & SOF & TR1). unfold LO in ST.
        pose proof RS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G28 & GD0 & _).
        unfold implM. iprefix. zstep. if_cases K1; zify_cond K1; try (exfalso; lia). clear K1.
        zstep. zstep. zstep. zstep. zstep. zstep. zstep. apply evt_done.
        lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm s1 (POSTBODY' fd P1v) msx) end.
        apply implM_bind_assoc. cbn [io_diag io_S].
        eapply (fwrite_exit sp0 argv envp uid hw draw TID S8 S9 S10 S11 VSP HT FWR TOW);
          [exact BA1| exact HEAP1| rewrite SOE; exact SO0| intros ms'' AE; apply implM_mret_bind; cbv beta iota; apply implM_ret; apply evt_done; exact AE]. }
    (* [comment removed for export] *)
    destruct RR as (A' & junk' & -> & BR' & HEAP1 & NBLK & HEXP).
    pose proof BR' as (BQ1 & BQ2 & BQ3 & BQ4 & BQ5).
    pose proof (RMalloc_ifaceP.RHEAP_blocks_nodup_proof _ _ _ HEAP1) as ND.
    assert (DISJ : A' + rd_cap st * 2 <= A \/ A + rd_cap st <= A').
    { pose proof (RMalloc_ifaceP.RHEAP_blocks_disjoint_proof _ _ _ (nb, A', rd_cap st * 2) (rd_buf st, A, rd_cap st) HEAP1 ltac:(left; reflexivity) ltac:(right; left; reflexivity)) as D.
      cbn [blk_id blk_addr blk_size fst snd] in D. apply D. cbn [map blk_id fst] in ND. inversion ND as [|x l NI ND']; subst. intros E. apply NI. rewrite E. left. reflexivity. }
    apply implM_bind_assoc.
    pose proof BA1 as (ST & MI & RS & AUX & IMG & SE & SOF & TR1). unfold LO in ST.
    unfold implM. iprefix. zstep. if_cases K1; zify_cond K1; try (exfalso; rewrite ?unsigned_lit in K1 by lia; lia). clear K1.
    zstep. zstep. if_cases K2; zify_cond K2; try (exfalso; lia). clear K2.
    zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    apply (rw_cells_split_CB _ _ _ [] _ _ [] [length DATA; Z.to_nat (rd_cap st * 2) - length DATA]%nat) in NBLK; [| cbn; lia]. cbn [mk_CB_cells app] in NBLK.
    apply (proj1 (rw_cells_app _ _ _ [CB (length DATA) (firstn (length DATA) junk')] _)) in NBLK. destruct NBLK as [NB1 NB2]. cbn [cells_size csize Nat.add] in NB2.
    pose proof BLK1 as SRC. apply (proj1 (rw_cells_app _ _ _ [CB (length DATA) DATA] _)) in SRC. destruct SRC as [SRC _].
    pose proof (rw_cells_bytes_at _ _ _ _ SRC) as SRCB. cbn [cells_bytes cbytes app] in SRCB. rewrite app_nil_r in SRCB. clear SRC.
    eapply evt_cut.
    { eapply memcpy_callv with (src := DATA) (junk := firstn (length DATA) junk');
        [exact SRCB| lia| replace (Z.to_nat (Z.of_nat (length DATA))) with (length DATA) by lia; exact NB1| lia| lia| lia| lia| exact MI]. }
    cbv beta. intros ms' PO.
    destruct PO as (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m2 & -> & MUc & WMc & MI2 & NB1' & _).
    ua. transport_after_call usegs m1 m2 MUc WMc.
    replace (ret_pc (Z_to_bv 64 0x1446c)) with (Z_to_bv 64 0x1446c) by (symmetry; rpc).
    assert (WOKW : Forall (WOK sp0) [(A', A' + Z.of_nat (length DATA))]).
    { unfold WOK. constructor; [right; right; left; cbn [fst snd]; lia| constructor]. }
    assert (P2 : RHEAP s1 [(nb, A', rd_cap st * 2); (rd_buf st, A, rd_cap st)] m2).
    { eapply (RHEAP_munchW sp0 argv envp VSP); [exact WOKW| exact MUc| exact WMc| | exact HEAP1].
      intros iv [<-|[]]. cbn [fst snd]. intros _ _. exists (nb, A', rd_cap st * 2). split; [left; reflexivity|]. cbn [fst snd blk_addr blk_size]. lia. }
    assert (BA2 : BASE' m2) by (eapply (BASE_munch sp0 argv envp uid hw draw TID VSP VARGV VENVP); [exact BA1| exact WOKW| exact MUc| exact WMc| exact MI2| unfold LO; first [exact ST| replace (usp0 - 8388608) with (usp0 + -8388608) by lia; exact ST]]).
    clear MUc WMc BA1 ST MI RS AUX IMG SE SOF WOKW TR1.
    pose proof BA2 as (ST & MI & RS & AUX & IMG & SE & SOF & TR2). unfold LO in ST.
    (* [comment removed for export] *)
    zstep. zstep. apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm s1 (POSTBODY' fd P1v) msx) end.
    eapply implM_bind.
    { apply implM_leaves. unfold rfree_stmt in FREE.
      eapply FREE with (lo := usp0 - 8388608) (B := usp0) (p := rd_buf st) (A := A) (n := rd_cap st); try reflexivity; unfold RATP;
        rewrite ?(unsigned_lit 295416) by lia; rewrite ?(unsigned_lit (usp0 + -128)) by lia;
        first [ exact P2 | right; left; reflexivity | exact AUX | exact ST | exact MI | exact ERR1 | unfold RFREE_STACK; lia | lia ]. }
    cbv beta. intros [] s2 ms2 [PO LEAF].
    destruct PO as (w0 & w1 & w2 & rb0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m3 & -> & MI3 & ST3 & ERR3 & AUX3 & HPR3 & FAE3 & SOE3 & HEAP3).
    unfold RATP in ERR3. rewrite ?(unsigned_lit 295416) in ERR3 by lia. rewrite ?(unsigned_lit (usp0 + -128)) in ST3 by lia. rewrite ?(unsigned_lit (usp0 + -128)) in HPR3 by lia.
    change (295416 + -164) with 295252 in ERR3.
    replace (ret_pc (Z_to_bv 64 0x14474)) with (Z_to_bv 64 0x14474) by (symmetry; rpc).
    rewrite (lb_remove_second (rd_buf st) (nb, A', rd_cap st * 2) (rd_buf st, A, rd_cap st) [] eq_refl ND) in HPR3, HEAP3.
    assert (BA3 : BASE' m3) by (eapply (BASE_heap_pres sp0 argv envp uid hw draw TID); [exact BA2| exact HPR3| exact MI3| unfold LO; first [exact ST3| replace (usp0 - 8388608) with (usp0 + -8388608) by lia; exact ST3]| exact AUX3]).
    assert (FR3 : FRAME' m3) by (unfold MFRAME; eapply rheap_pres_rw_cells; [exact HPR3| exact FR1| left; cbn; lia]).
    assert (NB3 : rw_cells usegs m3 A' [CB (length DATA) DATA; CB (Z.to_nat (rd_cap st * 2 - Z.of_nat (length DATA))) (firstn (Z.to_nat (rd_cap st * 2) - length DATA)%nat (skipn (length DATA) junk'))]).
    { eapply rheap_pres_rw_cells; [exact HPR3| |].
      - apply (proj2 (rw_cells_app _ _ _ [CB (length DATA) DATA] _)). split; [replace (length DATA) with (Z.to_nat (Z.of_nat (length DATA))) at 1 by lia; exact NB1'|].
        cbn [cells_size csize Nat.add]. replace (Z.to_nat (rd_cap st * 2 - Z.of_nat (length DATA))) with (Z.to_nat (rd_cap st * 2) - length DATA)%nat by lia. exact NB2.
      - right; right. exists (nb, A', rd_cap st * 2). split; [left; reflexivity|]. cbn [blk_addr blk_size fst snd cells_size csize Nat.add]. lia. }
    assert (SJ3 : rw_cells usegs m3 229609 [CB PSTAGE_LEN sj]).
    { eapply rheap_pres_rw_cells; [exact HPR3| exact SJ1|]. right; left. cbn [cells_size csize Nat.add]. unfold RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP. lia. }
    clear HPR3 FR1 NB1' NB2 LEAF.
    apply implM_mret_bind. cbv beta iota.
    rewrite <- LENZ.
    eapply (rd_read sp0 argv envp uid hw draw arg0 arg1 TID J8 S4 S5 S6 S7 S8 S9 S10 S11 VSP VARGV VENVP EARGV HT FPR FWX SWF fd P1v (mkRd nb (rd_cap st * 2) (rd_content st)) s2);
      cbn [rd_buf rd_cap rd_content]; first [exact FD | exact HP1 | exact HC | exact FR3 | exact BA3 | unfold RERRNO; exact ERR3 | exact FRM | lia | idtac].
    - split; [exact HEAP3|]. split; [rewrite FAE3; exact (eq_trans FAE FA0)|]. split; [rewrite SOE3; exact (eq_trans SOE SO0)|]. split; [exact I|]. split; [exact NB3|].
      assert (CAP2 : rd_cap st * 2 <= 67108864).
      { rewrite CAPK in LTM |- *. change 67108864 with (2 ^ 26) in LTM |- *. apply Z.pow_lt_mono_r_iff in LTM; [| lia| lia].
        replace (2 ^ k * 2) with (2 ^ (k + 1)) by (rewrite Z.pow_add_r by lia; lia). apply Z.pow_le_mono_r; lia. }
      unfold MAX_INPUT. split; [split; [lia| exists (k + 1); split; [lia| rewrite CAPK, Z.pow_add_r by lia; lia]]|]. split; [lia| exact BR'].
    - unfold STAGE, UREAD_STAGE. exact SJ3.
  Qed.

  (* [comment removed for export] *)
  Lemma rd_body : forall (fd P1v : Z) (st : rd_st) (s : PState) ms,
    3 <= fd < 2^32 -> nth_error (argv_ptrs sp0 argv envp) 1 = Some (Z_to_bv 64 P1v) ->
    RDINV' fd P1v st s ms ->
    implM usegs (read_loop_body Prog.io raw_malloc raw_free UREAD_STAGE fd (map bv_unsigned arg1) st) s (POSTBODY' fd P1v) ms.
  Proof.
    intros fd P1v st s ms FD HP1 RI.
    destruct RI as (x1 & t0 & t1 & t2 & x9 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & F & fc & mm & A & DATA & junk & errv & sj & pc
                    & -> & PCX & HC & BU & SJ & FR & BA & ERR & FRM).
    pose proof (sp_facts sp0 argv envp VSP) as SF. unfold LO in SF.
    assert (LENZ : zlength (rd_content st) = Z.of_nat (length DATA)) by (rewrite HC; unfold zlength; rewrite length_map; reflexivity).
    pose proof BU as (P0 & FA0 & SO0 & _ & BLK & [CAPR [k [K0' CAPK]]] & LENR & BR). unfold MAX_INPUT in CAPR.
    pose proof BA as (ST & MI & _). unfold LO in ST.
    rewrite read_loop_body_eq. unfold rd_grow_part. rewrite LENZ.
    unfold implM. iprefix.
    destruct PCX as [[-> ->]|[-> HNIL]].
    - (* [comment removed for export] *)
      zstep. if_cases K00; zify_cond K00.
      + (* [comment removed for export] *)
        replace (Z.of_nat (length DATA) =? rd_cap st) with true by (symmetry; apply Z.eqb_eq; lia).
        apply evt_done.
        lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm s (POSTBODY' fd P1v) msx) end.
        rewrite <- LENZ. eapply (rd_grow fd P1v st s); rewrite ?LENZ; first [exact FD | exact HP1 | exact HC | exact BU | exact SJ | exact FR | exact BA | exact ERR | exact FRM | lia].
      + (* [comment removed for export] *)
        replace (Z.of_nat (length DATA) =? rd_cap st) with false by (symmetry; apply Z.eqb_neq; lia).
        apply evt_done.
        lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm s (POSTBODY' fd P1v) msx) end.
        apply implM_mret_bind. cbv iota beta.
        rewrite <- LENZ. eapply (rd_nogrow fd P1v st s); first [exact FD | exact HP1 | exact HC | exact BU | exact SJ | exact FR | exact BA | exact ERR | exact FRM | lia].
    - (* [comment removed for export] *)
      assert (D0 : DATA = []) by (destruct DATA; [reflexivity| rewrite HNIL in HC; discriminate]). subst DATA. cbn [length Z.of_nat] in *.
      zstep. if_cases K00; zify_cond K00; [| exfalso; rewrite ?unsigned_lit in K00 by lia; lia].
      replace (0 =? rd_cap st) with false by (symmetry; apply Z.eqb_neq; lia).
      apply evt_done.
      lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm s (POSTBODY' fd P1v) msx) end.
      apply implM_mret_bind. cbv iota beta.
      rewrite <- LENZ. eapply (rd_nogrow fd P1v st s); first [exact FD | exact HP1 | exact HC | exact BU | exact SJ | exact FR | exact BA | exact ERR | exact FRM | cbn [length Z.of_nat]; lia].
  Qed.

  (* [comment removed for export] *)
  Definition POSTLOOP (fd P1v : Z) (r : rd_result) (s : PState) (ms : machine_state) : Prop :=
    match r with
    | RdExit => pat_exit 2 s ms
    | RdDone b c => RDBRK' fd P1v b c s ms
    end.

  Lemma rd_loop : forall (fuel : nat) (fd P1v : Z) (st : rd_st) (s : PState) ms,
    3 <= fd < 2^32 -> nth_error (argv_ptrs sp0 argv envp) 1 = Some (Z_to_bv 64 P1v) ->
    RDINV' fd P1v st s ms ->
    implM usegs (mloop fuel (read_loop_body Prog.io raw_malloc raw_free UREAD_STAGE fd (map bv_unsigned arg1)) st) s (POSTLOOP fd P1v) ms.
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
End CANSEC1.
