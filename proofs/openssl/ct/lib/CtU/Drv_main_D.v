(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation Strings.String.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Monad Stdio HexModel Target Driver Prog StrFun LibProg ProgG.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Str_tac Startup_glue InitMem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Layout Exit Startup Stdio_iface Printf_lib Printf_stdio_iface Lib_iface Exit_defs Driver_iface Drv_kit Drv_facts Drv_main_defs Drv_main_A Drv_main_B Drv_main_B2 Drv_main_B3 Drv_main_C.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Str_cpy.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Drv_sys F_memcpy.
From OssFuzzTheorems.openssl.ct.images Require Import Ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation ctusegs := ImageCt.ctusegs.
Notation mem := (word -> option byte).
Notation wz := MallocRep.wz.
Notation pph := Ubsan.M.phdrs.
Ltac rpc := apply ret_pc_even; [lia| reflexivity].

From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_lia__].
Local Ltac std_nia__ := nia.
Local Ltac nia := first [std_nia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_nia__].
Local Ltac OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.ZBridge.flia ::= first [ assumption | OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.ZBridge.slim; lia | lia ].
Local Ltac OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.ZBridge.mlia ::= Z.div_mod_to_equations; lia.
Local Ltac OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.slia ::= first [ exact I | lia | split; [lia|exact I] ].
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd} {LM : LibModel} {LSP : LibSpec} {LL : LibLaws}.
Section D.
  Variables (sp0 : word) (argv envp : list (list byte)) (uid : word) (arg0 arg1 : list byte) (TID : Z) (PAD : list byte) (S4 S5 S6 S7 S8 S9 S10 S11 : word).
  Hypothesis VSP : valid_sp sp0.
  Hypothesis CEIL : ceil_ok sp0.
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
  Hypothesis TRUN : rtarget_run_stmt.

  Notation usp0 := (bv_unsigned sp0).
  Notation LO' := (LO sp0).
  Notation BASE' := (BASE sp0 argv envp uid TID).
  Notation FRAME' mm := (MFRAME sp0 argv mm PAD S7 S6 S5 S4).
  Notation IMGB := (build_stack_bytes pph sp0 argv envp uid run_hw run_draw).
  Notation RUN0' := (RUN0 sp0 argv envp uid TID PAD S4 S5 S6 S7 S8 S9 S10 S11).
  Notation RQEXIT := (Drv_main_C.RQEXIT).

  Notation GST pc x1 t0 t1 t2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 F fc mm :=
    (MS (mkR x1 (Z_to_bv 64 (usp0 + -128)) (Z_to_bv 64 0x10800) (Z_to_bv 64 RATP) t0 t1 t2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 S8 S9 S10 S11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom ctusegs)).

  (* [comment removed for export] *)
  Definition BASE2 (mm : mem) : Prop :=
    stk ctusegs mm LO' (usp0 + -128) /\ mem_inv ctusegs mm /\ ESTATr TID true mm /\ rauxv_ok mm usp0 /\ stderr_wfile mm.   (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma not_DRVW_stack : forall a, usp0 + -128 <= a -> ~ rin_ivs DRVW a.
  Proof.
    intros a Ha H. pose proof (sp_facts sp0 VSP CEIL) as SF. unfold DRVW in H. apply rin_ivs_app in H. destruct H as [H|H].
    - unfold RINIT_FLAG in H. cbn in H. lia.
    - pose proof (LIBW_img a H) as (X & _). lia.
  Qed.
  Lemma not_DRVW_estat : forall a, estat0_addr a -> ~ rin_ivs DRVW a.
  Proof.
    intros a Ha H. unfold DRVW in H. apply rin_ivs_app in H. destruct H as [H|H].
    - unfold RINIT_FLAG in H. cbn in H. unfold estat0_addr, exit_statics_addr in Ha. lia.
    - pose proof (LIBW_img a H) as (_ & _ & X). apply X. unfold drv_addr.
      destruct Ha as [Ha|Ha]; [do 4 right; left; exact Ha| do 6 right; left; unfold RGOT_LLVMINIT; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma free_return : forall (code : Z) (s : PState) (LB : list block) (bufp : bptr) (A cap : Z)
      x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 (F : bvmap 5 word) (fc : bv 32) (mm : mem) (errv : word),
    0 <= code < 2^64 ->
    RHEAP s LB mm -> In (bufp, A, cap) LB -> FRAME' mm -> BASE2 mm -> ossl_exit_cells mm -> stdout_file mm (ps_so s) -> rw_cells ctusegs mm RMallocRep.RERRNO [C4 errv] ->
    implM ctusegs (raw_free bufp ;;; mret code) s RQEXIT
      (GST 0xe2200 x1 t0 t1 t2 (Z_to_bv 64 code) (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 F fc mm).
  Proof.
    intros until errv. intros CR P0 HIN FR (ST & MI & ES & AUX & SE) OSC SOF ERR.
    pose proof (sp_facts sp0 VSP CEIL) as SF. unfold LO in SF. try (pose proof alloc_ceiling_range as CEIL_RANGE). unfold LO in ST. unfold RMallocRep.RERRNO in ERR. pose proof FR as FR0. unfold MFRAME in FR.
    pose proof (RHEAP_block_range_proof _ _ _ (bufp, A, cap) P0 HIN) as BR. cbn [blk_addr blk_size fst snd] in BR.
    pose proof BR as (BR1 & BR2 & BR3 & BR4 & BR5). try (pose proof alloc_ceiling_range as CEIL_RANGE).
    unfold implM. iprefix. zstep. zstep. zstep. apply evt_done.   (* [comment removed for export] *)
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM ctusegs tm s RQEXIT msx) end.
    eapply implM_bind.
    { unfold rfree_stmt in FREE.
      eapply FREE with (lo := usp0 - 8388608) (B := usp0) (p := bufp) (A := A) (n := cap); try reflexivity; unfold RATP;
        rewrite ?(unsigned_lit RMallocRep.RATP) by (unfold RMallocRep.RATP; lia); rewrite ?(unsigned_lit (usp0 + -128)) by lia; unfold RMallocRep.RATP; cbn [Z.add];
        first [ exact P0 | exact HIN | exact AUX | exact ST | exact MI | exact ERR | unfold RFREE_STACK; lia | lia ]. }
    cbv beta. intros [] s2 ms2 PO.
    destruct PO as (w0 & w1 & w2 & rb0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m3 & -> & MI3 & ST3 & ERR3 & AUX3 & HPR3 & FAE3 & SOE3 & HEAP3).
    rewrite ?(unsigned_lit (usp0 + -128)) in ST3 by lia. rewrite ?(unsigned_lit (usp0 + -128)) in HPR3 by lia.
    replace (ret_pc (Z_to_bv 64 0xe220c)) with (Z_to_bv 64 0xe220c) by (symmetry; rpc).
    pose proof (agree_of_heap_pres _ _ _ _ HPR3) as AG.
    unfold RATP in ERR3. rewrite ?(unsigned_lit RMallocRep.RATP) in ERR3 by (unfold RMallocRep.RATP; lia). unfold RMallocRep.RATP in ERR3. cbn [Z.add] in ERR3.
    apply implM_ret. unfold Drv_main_C.RQEXIT.
    eapply (main_return sp0 argv TID PAD S4 S5 S6 S7 S8 S9 S10 S11 VSP CEIL HT code s2 (lb_remove bufp LB)); [lia| eapply (MFRAME_heap sp0 argv); [exact HPR3| exact FR0]| unfold LO; exact ST3| | eapply (OSC_heap sp0); [exact HPR3| exact OSC]| exact HEAP3| | | exact MI3| exact ERR3| exact AUX3].
    - eapply (ESTATr_agree TID _ true _ _ AG); [| exact ES]. intros a Ha. right; left.
      unfold estat_addr, exit_statics_addr, ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP in *. lia.
    - rewrite SOE3. eapply stdout_file_agree; [exact AG| | exact SOF]. intros a Ha. right; left.
      unfold stdout_addr, ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP in *. lia.
    - apply stderr_wfile_file. eapply stderr_wfile_agree; [exact AG| | exact SE]. intros a Ha. right; left.
      unfold stderr_addr, ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP in *. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma phaseDE : forall bufp A cap DATA cw L cfg sc s ms,
    RUN0' bufp A cap DATA cw L cfg sc s ms ->
    implM ctusegs (main_tail bufp cw cfg (skipn (Z.to_nat (6 + L)) (map bv_unsigned DATA))) s RQEXIT ms.
  Proof.
    intros bufp A cap DATA cw L cfg sc s ms R0.
    destruct R0 as (x1 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & x23 & t3 & t4 & t5 & t6 & F & fc & mm & junk & errv
                    & -> & HD & P0 & BLK & FR & BA & EX & ERR & FRM).
    pose proof (sp_facts sp0 VSP CEIL) as SF. unfold LO in SF. try (pose proof alloc_ceiling_range as CEIL_RANGE).
    pose proof BA as (ST & MI & ES & AUX & SSP & LXS & IMG). unfold LO in ST. pose proof ERR as ERR0. unfold RMallocRep.RERRNO in ERR. pose proof FR as FR0. unfold MFRAME in FR.
    pose proof EX as (SOF & SE & IB & OSC & PRI).
    pose proof ES as (ES0 & GOT & ATS).
    destruct HD as (LEN6 & LENC & CAPM & BR & CW & EL & LR & LCW & ECW & ECFG & CFGR & SCR & TB). unfold MAX_INPUT in CAPM.
    pose proof BR as (BR1 & BR2 & BR3 & BR4 & BR5). try (pose proof alloc_ceiling_range as CEIL_RANGE).
    pose proof BLK as BLKB. apply (proj1 (rw_cells_app _ _ _ [CB (length DATA) DATA] _)) in BLKB. destruct BLKB as [BLKB _].
    apply rw_cells_bytes_at in BLKB. cbn [cells_bytes cbytes app] in BLKB. rewrite app_nil_r in BLKB.
    unfold main_tail. rewrite ECFG.
    unfold implM. iprefix. zstep. zstep. zstep. zstep. zstep. apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM ctusegs tm s RQEXIT msx) end.
    eapply implM_bind.
    { unfold rtarget_run_stmt, RTARGET_RUN in TRUN.
      eapply TRUN with (lo := usp0 - 8388608) (B := usp0) (p := bufp) (cap := cap) (errv := errv);
        rewrite ?(unsigned_lit (usp0 + -128)) by lia.
      - exact P0.
      - left; reflexivity.
      - unfold to_bytes. rewrite zbytes_map_unsigned'. exact BLKB.
      - apply map_unsigned_range.
      - unfold zlength. rewrite length_map. lia.
      - lia.
      - lia.
      - unfold zlength. rewrite length_map. lia.
      - exact LXS.
      - apply stderr_wfile0_wfile. exact SE.
      - exact SSP.
      - exact SOF.
      - exact IB.
      - exact GOT.
      - exact ATS.
      - exact PRI.
      - exact AUX.
      - lia.
      - lia.
      - exact ST.
      - lia.
      - unfold GLOBALS_TOP. lia.
      - pose proof LIB_STACK_hi as LSH. unfold RTARGET_RUN_STACK, LX_FUZZ_STACK. lia.
      - unfold RATP. cbv delta [MallocRep.wz]. rewrite (unsigned_lit RMallocRep.RATP) by (unfold RMallocRep.RATP; lia). unfold RMallocRep.RATP. cbn [Z.add]. exact ERR.
      - reflexivity.
      - exact MI.
      - exact FRM.
      - lia.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - cbv delta [MallocRep.wz]. f_equal. unfold zlength. rewrite length_map. lia. }
    cbv beta. intros r s1 ms1 PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F1 & fc1 & m1 & errv1 & ib1
                    & -> & RR & MI1 & FRM1 & ST1 & ERR1 & AUX1 & [OW1 P1] & OSC1 & LXS1 & SE1 & SSP1 & SOF1 & IB1 & ATS1 & DP).
    rewrite ?(unsigned_lit (usp0 + -128)) in ST1 by lia. rewrite ?(unsigned_lit (usp0 + -128)) in DP by lia.
    unfold RATP in ERR1. cbv delta [MallocRep.wz] in ERR1. rewrite ?(unsigned_lit RMallocRep.RATP) in ERR1 by (unfold RMallocRep.RATP; lia). unfold RMallocRep.RATP in ERR1. cbn [Z.add] in ERR1.
    cbv delta [MallocRep.wz].
    replace (ret_pc (Z_to_bv 64 0xe2178)) with (Z_to_bv 64 0xe2178) by (symmetry; rpc).
    pose proof (agree_of_drv_pres _ _ _ _ DP) as AG.
    assert (FR1 : FRAME' m1).
    { unfold MFRAME. eapply rw_cells_agree; [exact AG| exact FR|]. intros a Ha. cbn in Ha. apply stack_client; [lia|].
      apply not_DRVW_stack. lia. }
    assert (ES1 : ESTATr TID true m1).
    { destruct (ESTAT0_agree TID _ _ _ AG) as (B1 & B2); [| exact (conj ES0 GOT)| exact (conj B1 (conj B2 ATS1))]. intros a Ha. split.
      - apply not_DRVW_estat. exact Ha.
      - right; right. unfold estat0_addr, exit_statics_addr, ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP in *. lia. }
    assert (BA2 : BASE2 m1) by (split; [unfold LO; exact ST1| split; [exact MI1| split; [exact ES1| split; [exact AUX1| exact SE1]]]]).
    clear AG DP.
    rewrite TB.
    destruct (Z.lt_ge_cases sc 0) as [SNEG|SPOS].
    - (* [comment removed for export] *)
      replace (sc <? 0) with true by (symmetry; apply Z.ltb_lt; lia).
      replace (Z_to_bv 64 sc) with (Z_to_bv 64 (sc + 2^64)) by (apply Z_to_bv_eqm; rewrite <- (Z.mod_add sc 1) by lia; f_equal; lia).
      unfold implM. iprefix. zstep. if_cases K; zify_cond K; [| exfalso; lia].
      (* [comment removed for export] *)
      zstep. zstep. zstep.
      replace (ret_pc (Z_to_bv 64 0xe2188)) with (Z_to_bv 64 0xe2188) by (symmetry; rpc).
      apply evt_done.
      lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM ctusegs tm s1 RQEXIT msx) end.
      apply implM_bind_assoc. unfold alloc_count. apply implM_retb. apply implM_retb. unfold COUNT_MAX. cbn [Z.ltb].
      unfold implM. iprefix. zstep. zstep. zstep. if_cases K2; zify_cond K2; [| exfalso; rewrite ?unsigned_lit in K2 by lia; lia].
      apply evt_done. lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM ctusegs tm s1 RQEXIT msx) end.
      eapply (free_return _ _ (OW1 ++ [(bufp, A, cap)])); [first [lia| change (0 <? 251) with true; cbv iota; lia]| exact P1| apply in_or_app; right; left; reflexivity| exact FR1| exact BA2| exact OSC1| exact SOF1| unfold RMallocRep.RERRNO; exact ERR1].
    - (* [comment removed for export] *)
      replace (sc <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
      apply implM_retb.
      unfold implM. iprefix. zstep. if_cases K; zify_cond K; [exfalso; lia|].
      zstep. zstep.
      apply evt_done. lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM ctusegs tm s1 RQEXIT msx) end.
      eapply (free_return _ _ (OW1 ++ [(bufp, A, cap)])); [first [lia| change (0 <? 251) with true; cbv iota; lia]| exact P1| apply in_or_app; right; left; reflexivity| exact FR1| exact BA2| exact OSC1| exact SOF1| unfold RMallocRep.RERRNO; exact ERR1].
  Qed.
End D.
End WithCeiling0.
