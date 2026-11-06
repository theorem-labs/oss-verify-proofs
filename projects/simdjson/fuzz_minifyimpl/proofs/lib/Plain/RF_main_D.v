(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation Strings.String.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP InitMem MonadX.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import DrvAgree Startup_kit STRW_tac F_fmt_fp_lib Printf_fmts.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Plain Require Import PImg F_syscalls F_memcpy StdioFiles PStartU F_printf_iface Stdio_iface Stdio_kit.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Malloc Require Import MallocBlocks MallocTree MallocHINV Malloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Plain Require Import RMallocRep RMallocTree RMalloc_iface PU_iface PIosX_iface PAtexit_cells RDriver_iface RDriver_facts RDriver_kit RDriver_ctx RF_main_A RF_main_B1 RF_main_B2 RF_main_B3 RF_main_B4 RF_main_C.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Plain Require RMalloc_ifaceP.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import Prelim STree Malloc Monad Stdio Driver PState ProgP.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Plain Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac ua := idtac.
Ltac rpc := apply ret_pc_even; [lia| reflexivity].

Section CANSEC1. Context {rc : runConstT}.
Section D.
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
  Hypothesis TRUN : ptarget_run_stmt.

  Notation usp0 := (bv_unsigned sp0).
  Notation gpv := (Z_to_bv 64 0x10800).
  Notation tpv := (Z_to_bv 64 RATP).
  Notation IMGB := (build_stack_bytes pph sp0 argv envp uid hw draw).
  Notation LO' := (LO sp0).
  Notation BASE' := (BASE sp0 argv envp uid hw draw TID).
  Notation FRAME' mm := (MFRAME sp0 argv mm J8 S7 S6 S5 S4).
  Notation RUN0' := (RUN0 sp0 argv envp uid hw draw TID J8 S4 S5 S6 S7 S8 S9 S10 S11).

  Notation GST pc x1 t0 t1 t2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 F fc mm :=
    (MS (mkR x1 (Z_to_bv 64 (usp0 + -128)) gpv tpv t0 t1 t2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 S8 S9 S10 S11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom psegs)).

  (* [comment removed for export] *)
  Definition BASE2 (mm : mem) : Prop :=
    stk psegs mm LO' (usp0 + -128) /\ mem_inv psegs mm /\ RSTAT TID mm /\ rauxv_ok mm usp0 /\ stderr_file0 mm
    /\ pincb 0 mm.        (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma free_return : forall (code : Z) (s : PState) (cb : list block) (bufp : bptr) (A cap : Z)
      x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 (F : bvmap 5 word) (fc : bv 32) (mm : mem) (errv : word),
    RHEAP s (cb ++ [(bufp, A, cap)]) mm -> client_static s cb mm -> (cb = [] \/ exists pc V, cb = [(pc, V, 8)]) ->
    FRAME' mm -> BASE2 mm -> stdout_file mm (ps_so s) -> rw_cells psegs mm RERRNO [C4 errv] ->
    implM psegs (raw_free bufp ;;; mret code) s RQEXIT
      (GST 0x3ba68 x1 t0 t1 t2 (Z_to_bv 64 code) (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 F fc mm).
  Proof.
    intros until errv. intros P0 CST CBS FR (ST & MI & RS & AUX & SE & TX) SOF ERR.
    pose proof (sp_facts sp0 argv envp VSP) as SF. unfold LO in SF. unfold LO in ST. unfold RERRNO in ERR. unfold MFRAME in FR.
    pose proof (RMalloc_ifaceP.RHEAP_block_range_proof _ _ _ (bufp, A, cap) P0 ltac:(apply in_or_app; right; left; reflexivity)) as BR. cbn [blk_addr blk_size fst snd] in BR.
    pose proof BR as (BR1 & BR2 & BR3 & BR4 & BR5). atop_facts.
    unfold implM. iprefix. zstep. zstep. apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM psegs tm s RQEXIT msx) end.
    eapply implM_bind.
    { unfold rfree_stmt in FREE.
      eapply FREE with (lo := usp0 - 8388608) (B := usp0) (p := bufp) (A := A) (n := cap) (LB := cb ++ [(bufp, A, cap)]); try reflexivity; unfold RATP;
        rewrite ?(unsigned_lit 932392) by lia; rewrite ?(unsigned_lit (usp0 + -128)) by lia;
        first [ exact P0 | apply in_or_app; right; left; reflexivity | exact AUX | exact ST | exact MI | exact ERR | unfold RFREE_STACK; lia | lia ]. }
    cbv beta. intros [] s2 ms2 PO.
    destruct PO as (w0 & w1 & w2 & rb0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m3 & -> & MI3 & ST3 & ERR3 & AUX3 & HPR3 & FAE3 & SOE3 & HEAP3).
    rewrite ?(unsigned_lit (usp0 + -128)) in ST3 by lia. rewrite ?(unsigned_lit (usp0 + -128)) in HPR3 by lia.
    replace (ret_pc (Z_to_bv 64 0x3ba70)) with (Z_to_bv 64 0x3ba70) by (symmetry; rpc).
    pose proof (RMalloc_ifaceP.RHEAP_blocks_nodup_proof _ _ _ P0) as ND.
    assert (ELB : lb_remove bufp (cb ++ [(bufp, A, cap)]) = cb).
    { destruct CBS as [->|(pc & V & ->)]; cbn [app] in ND |- *.
      - exact (lb_remove_head (bufp, A, cap) [] ND).
      - exact (lb_remove_second bufp (pc, V, 8) (bufp, A, cap) [] eq_refl ND). }
    rewrite ELB in HEAP3, HPR3.
    apply implM_ret. change (RQEXIT code s2) with (pat_exitU code s2).
    eapply (main_return sp0 argv envp TID VSP HT code s2 cb).
    - unfold MFRAME. eapply rheap_pres_rw_cells; [exact HPR3| exact FR| left; cbn; lia].
    - unfold LO. first [exact ST3| replace (usp0 - 8388608) with (usp0 + -8388608) by lia; exact ST3].
    - eapply RSTAT_heap_pres; [exact HPR3| exact RS].
    - exact HEAP3.
    - apply exit_table_of_static.      (* [comment removed for export] *)
      eapply (client_static_fa s); [exact FAE3|]. eapply (client_static_agree _ _ _ _ _ HPR3); [| | exact CST].
      + intros a Ha. right; left. unfold cstat_addr, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in *. lia.
      + intros pv Vv a _ HIN Ha. right; right. exists (pv, Vv, 8). split; [exact HIN| cbn; lia].
    - exact AUX3.
    - rewrite SOE3. eapply stdout_file_heap_pres; [exact HPR3| exact SOF].
    - apply stderr_file0_file. eapply stderr_file0_heap_pres; [exact HPR3| exact SE].
    - exact MI3.
    - eapply pincb_heap_pres; [exact HPR3| exact TX].       (* [comment removed for export] *)
  Qed.

  (* [comment removed for export] *)
  Lemma phaseDE : forall bufp A cap DATA cw L cfg sc s ms,
    RUN0' bufp A cap DATA cw L cfg sc s ms ->
    implM psegs (main_tail bufp cw cfg (skipn (Z.to_nat (6 + L)) (map bv_unsigned DATA))) s RQEXIT ms.
  Proof.
    intros bufp A cap DATA cw L cfg sc s ms R0.
    destruct R0 as (x1 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & x23 & F & fc & mm & junk & errv
                    & -> & HD & PST0 & FA0 & SO0 & BLK & FR & BA & ERR & FRM).
    pose proof (sp_facts sp0 argv envp VSP) as SF. unfold LO in SF.
    pose proof BA as (ST & MI & RS & AUX & IMG & SE & SOF & TR). unfold LO in ST. pose proof ERR as ERR0. unfold RERRNO in ERR. pose proof FR as FR0. unfold MFRAME in FR.
    destruct HD as (LEN6 & LENC & CAPM & BR & CW & EL & LR & LCW & ECW & ECFG & CFGR & SCR & TB). unfold MAX_INPUT in CAPM.
    pose proof BR as (BR1 & BR2 & BR3 & BR4 & BR5). atop_facts.
    pose proof BLK as BLKB. apply (proj1 (rw_cells_app _ _ _ [CB (length DATA) DATA] _)) in BLKB. destruct BLKB as [BLKB _].
    apply rw_cells_bytes_at in BLKB. cbn [cells_bytes cbytes app] in BLKB. rewrite app_nil_r in BLKB.
    unfold main_tail. rewrite ECFG.
    unfold implM. iprefix. zstep. zstep. zstep. zstep. zstep. apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM psegs tm s RQEXIT msx) end.
    eapply implM_bind.
    { eapply TRUN with (lo := usp0 - 8388608) (AB := usp0) (p := bufp) (cap := cap);
        rewrite ?(unsigned_lit (usp0 + -128)) by lia.
      - exact PST0.
      - left; reflexivity.
      - rewrite zbytes_map_unsigned. exact BLKB.
      - apply map_unsigned_range.
      - unfold zlength. rewrite length_map. lia.
      - lia.
      - lia.
      - unfold zlength. rewrite length_map. lia.
      - exact (proj1 TR).
      - exact FA0.                  (* [comment removed for export] *)
      - exact (proj2 TR).           (* [comment removed for export] *)
      - exact AUX.
      - lia.
      - lia.
      - exact ST.
      - lia.
      - unfold PTARGET_RUN_STACK, HARNESS_STACK. lia.
      - unfold RATP. rewrite (unsigned_lit 932392) by lia. exact ERR.
      - exact MI.
      - exact FRM.
      - rewrite SO0. exact SOF.
      - reflexivity.
      - clear -SF. destruct SF as (_ & S16 & _). Z.div_mod_to_equations. lia.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - unfold wz, zlength. rewrite length_map. reflexivity. }
    cbv beta. intros r s1 ms1 PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F1 & fc1 & m1 & errv1 & LB1
                    & -> & RR & MI1 & FRM1 & ST1 & ERR1 & AUX1 & DP & P1 & CST1 & ARM & SOF1 & TX1).     (* [comment removed for export] *)
    (* [comment removed for export] *)
    assert (CB1 : exists cb, (cb = [] \/ exists pc V, cb = [(pc, V, 8)]) /\ LB1 = cb ++ [(bufp, A, cap)] /\ client_static s1 cb m1).
    { pose proof (RMalloc_ifaceP.RHEAP_blocks_nodup_proof _ _ _ P1) as ND1.
      destruct ARM as [[-> EFA]|(pc & V & _ & -> & EFA)].
      - exists []. split; [left; reflexivity|]. split; [reflexivity|].
        eapply (client_static_sub s1 ([] ++ [(bufp, A, cap)])); [exact CST1| exact ND1| intros b []|].
        intros p' E'. rewrite EFA, FA0 in E'. discriminate.
      - exists [(pc, V, 8)]. split; [right; exists pc, V; reflexivity|]. split; [reflexivity|].
        eapply (client_static_sub s1 ([(pc, V, 8)] ++ [(bufp, A, cap)])); [exact CST1| exact ND1| intros b Hb; apply in_or_app; left; exact Hb|].
        intros p' E'. rewrite EFA in E'. injection E'; intros <-. exists V. left. reflexivity. }
    destruct CB1 as (cb & CBS & -> & CST1').
    rewrite ?(unsigned_lit (usp0 + -128)) in ST1 by lia. rewrite ?(unsigned_lit (usp0 + -128)) in DP by lia.
    unfold RATP in ERR1. rewrite ?(unsigned_lit 932392) in ERR1 by lia.
    replace (ret_pc (Z_to_bv 64 0x3b9e8)) with (Z_to_bv 64 0x3b9e8) by (symmetry; rpc).
    pose proof (pdrv_pres_agree _ _ _ _ DP) as AG.
    apply (rw_cells_magree psegs _ _ _ _ _ AG) in FR.
    2:{ intros a Ha. cbn in Ha. split; [left; lia|]. unfold pstdout_ivs, client_wr, PINIT_FLAG, PNEWH. cbn. lia. }
    assert (RS1 : RSTAT TID m1) by (eapply RSTAT_drv_pres; [exact DP| exact RS]).
    assert (SE1 : stderr_file0 m1) by (eapply stderr_file0_drv_pres; [exact DP| exact SE]).
    assert (BA2 : BASE2 m1) by (split; [exact ST1| split; [exact MI1| split; [exact RS1| split; [exact AUX1| split; [exact SE1| exact TX1]]]]]).
    clear AG DP.
    rewrite TB.
    destruct (Z.lt_ge_cases sc 0) as [SNEG|SPOS].
    - (* [comment removed for export] *)
      replace (sc <? 0) with true by (symmetry; apply Z.ltb_lt; lia).
      replace (Z_to_bv 64 sc) with (Z_to_bv 64 (sc + 2^64)) by (apply Z_to_bv_eqm; rewrite <- (Z.mod_add sc 1) by lia; f_equal; lia).
      unfold implM. iprefix. zstep. if_cases K; zify_cond K; [| exfalso; lia].
      zstep. apply evt_done.
      lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM psegs tm s1 RQEXIT msx) end.
      apply implM_bind_assoc. eapply implM_bind; [apply ptarget_alloc_count_spec|].
      cbv beta. intros n s2 ms2 (-> & -> & ->). apply implM_retb.
      replace (ret_pc (Z_to_bv 64 0x3b9f8)) with (Z_to_bv 64 0x3b9f8) by (symmetry; rpc).
      unfold COUNT_MAX. change (if 0 <? 251 then 0 else 251) with 0.
      unfold implM. iprefix. zstep. zstep. zstep. if_cases K2; zify_cond K2; [| exfalso; lia].
      apply evt_done. lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM psegs tm s1 RQEXIT msx) end.
      eapply free_return; [exact P1| exact CST1'| exact CBS| exact FR| exact BA2| exact SOF1| unfold RERRNO; exact ERR1].
    - (* [comment removed for export] *)
      replace (sc <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
      apply implM_retb.
      unfold implM. iprefix. zstep. if_cases K; zify_cond K; [exfalso; lia|].
      zstep. zstep.
      apply evt_done. lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM psegs tm s1 RQEXIT msx) end.
      eapply free_return; [exact P1| exact CST1'| exact CBS| exact FR| exact BA2| exact SOF1| unfold RERRNO; exact ERR1].
  Qed.
End D.
End CANSEC1.
