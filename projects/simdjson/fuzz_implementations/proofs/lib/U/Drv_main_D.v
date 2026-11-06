(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation Strings.String.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import Prelim STree Malloc Monad Stdio SjModel Target Driver Prog StrFun.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Str_tac Startup_glue InitMem Imp_keepsx.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.U Require Import Layout Exit Exit_iface Startup Stdio_iface Printf_lib Printf_stdio_iface Sj_iface Driver_iface Drv_kit Drv_facts Drv_aex Drv_main_defs Drv_main_A Drv_main_B Drv_main_B2 Drv_main_B3 Drv_main_C.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Str_cpy.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.U Require Drv_sys F_memcpy.
From OSSVerify.simdjson.fuzz_implementations.images Require Import Ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation usegs := Image.usegs.
Notation mem := (word -> option byte).
Notation wz := MallocRep.wz.
Notation pph := Ubsan.M.phdrs.
Ltac rpc := apply ret_pc_even; [lia| reflexivity].

From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Rnd.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Malloc Require Import CeilWin.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_lia__].
Local Ltac std_nia__ := nia.
Local Ltac nia := first [std_nia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_nia__].
Local Ltac OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib.ZBridge.flia ::= first [ assumption | OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib.ZBridge.slim; lia | lia ].
Local Ltac OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib.ZBridge.mlia ::= Z.div_mod_to_equations; lia.
Local Ltac OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib.Step.slia ::= first [ exact I | lia | split; [lia|exact I] ].
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
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
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).

  Definition BASE2 (mm : mem) : Prop :=
    stk usegs mm LO' (usp0 + -128) /\ mem_inv usegs mm /\ ESTAT TID 1 mm /\ rauxv_ok mm usp0 /\ stderr_wfile0 mm.

  Lemma vec_block_unique : forall st LL mm q A0 Av, RHEAP st LL mm -> In (q, A0, 8) LL -> In (q, Av, 8) LL -> A0 = Av.
  Proof.
    intros st LL mm q A0 Av HP H1 H2. pose proof (RHEAP_blocks_nodup_proof _ _ _ HP) as ND.
    assert (GEN : forall (l : list block) x y, List.NoDup (map blk_id l) -> In x l -> In y l -> blk_id x = blk_id y -> x = y).
    { induction l as [|bb l IH]; intros x y NDl Hx Hy E; [destruct Hx|]. cbn [map] in NDl. inversion NDl as [|b' l' NI ND']; subst.
      destruct Hx as [<-|Hx], Hy as [<-|Hy]; [reflexivity| | | exact (IH x y ND' Hx Hy E)].
      - exfalso. apply NI. rewrite E. apply in_map. exact Hy.
      - exfalso. apply NI. rewrite <- E. apply in_map. exact Hx. }
    pose proof (GEN LL _ _ ND H1 H2 eq_refl) as E. inversion E. reflexivity.
  Qed.

  Lemma main_return1 : forall (code : Z) (s : PState) (pv : bptr) (Av : Z) (x1 t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (mm : mem) (errv : word),
    0 <= code < 2^64 ->
    FRAME' mm -> stk usegs mm LO' (usp0 + -128) ->
    ESTAT TID 1 mm -> RHEAP s [(pv, Av, 8)] mm -> stdout_file mm (ps_so s) -> stderr_wfile0 mm -> (exists i, sj_statics mm i) -> lx_statics mm ->
    rauxv_ok mm usp0 -> rw_cells usegs mm (errno_addr (wz RATP)) [C4 errv] -> rw_cells usegs mm AEX_VEC_OBJ [C8 (wz Av); C8 (wz (Av + 8)); C8 (wz (Av + 8))] -> 0 < Av -> mem_inv usegs mm ->
    evt usegs (at_exit_immp (Some pv) code s)
      (GST 0x3e988 x1 t0 t1 t2 (Z_to_bv 64 code) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 t3 t4 t5 t6 F fc mm).
  Proof.
    intros until errv. intros CR FR ST ES HP SOF SEF SJS LXS AUX ERR VOBJ A0 MI. pose proof (sp_facts sp0 VSP CEIL) as SF. unfold LO in *. try (pose proof alloc_ceiling_range as CEIL_RANGE). unfold MFRAME in FR.
    unfold Drv_main_defs.RMAIN_RET, RMAIN in FR. cbv delta [MallocRep.wz] in FR.
    do 11 zstep. release_frame FR ST (usp0 + -48). zstep.
    replace (ret_pc (Z_to_bv 64 0xc469c)) with (Z_to_bv 64 0xc469c) by (symmetry; rpc).
    zstep.
    replace (ret_pc (Z_to_bv 64 0xc46a0)) with (Z_to_bv 64 0xc46a0) by (symmetry; rpc).
    apply evt_done. eapply (at_exit_intro sp0 TID HT code s [(pv, Av, 8)] (usp0 + -48) 1 (Some pv));
      [exact ST| unfold EXIT_DEPTH; lia| lia| lia| lia| exact ES| exact HP| exact SOF| exact SEF| exact SJS| exact LXS| | exact MI| lia].
    split; [reflexivity|]. split; [exact HP|]. split; [exists usp0; split; [exact AUX| lia]|]. split; [exists errv; exact ERR|].
    exists Av. split; [left; reflexivity|]. split; [exact VOBJ| exact A0].
  Qed.

  Lemma free_return : forall (code : Z) (s : PState) (bufp : bptr) (A cap : Z) (pv : bptr) (Av : Z)
      x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 (F : bvmap 5 word) (fc : bv 32) (mm : mem) (errv : word),
    0 <= code < 2^64 ->
    RHEAP s ((pv, Av, 8) :: [(bufp, A, cap)]) mm -> FRAME' mm -> BASE2 mm -> stdout_file mm (ps_so s) -> rw_cells usegs mm RMallocRep.RERRNO [C4 errv] ->
    (exists i, sj_statics mm i) -> lx_statics mm -> rw_cells usegs mm AEX_VEC_OBJ [C8 (wz Av); C8 (wz (Av + 8)); C8 (wz (Av + 8))] -> ps_x s = Some pv ->
    implM usegs (raw_free bufp ;;; mret code) s (fun cd s' ms' => at_exit_imp cd s' ms')
      (GST 0x3e980 x1 t0 t1 t2 (Z_to_bv 64 code) (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 F fc mm).
  Proof.
    intros until errv. intros CR P0 FR (ST & MI & ES & AUX & SE) SOF ERR SJS LXS VOBJ PSX.
    pose proof (sp_facts sp0 VSP CEIL) as SF. unfold LO in SF. try (pose proof alloc_ceiling_range as CEIL_RANGE). unfold LO in ST. unfold RMallocRep.RERRNO in ERR. pose proof FR as FR0. unfold MFRAME in FR.
    pose proof (RHEAP_block_range_proof _ _ _ (bufp, A, cap) P0 ltac:(right; left; reflexivity)) as BR. cbn [blk_addr blk_size fst snd] in BR.
    pose proof BR as (BR1 & BR2 & BR3 & BR4 & BR5).
    pose proof (RHEAP_block_range_proof _ _ _ (pv, Av, 8) P0 ltac:(left; reflexivity)) as BV. cbn [blk_addr blk_size fst snd] in BV.
    pose proof BV as (BV1 & BV2 & BV3 & BV4 & BV5). try (pose proof alloc_ceiling_range as CEIL_RANGE).
    assert (P0s : RHEAP s ((bufp, A, cap) :: [(pv, Av, 8)]) mm) by (eapply RHEAP_perm; [exact P0| apply Permutation.perm_swap]).

    eapply implM_mono with (Q := fun cd s' ms' => at_exit_immp (Some pv) cd s' ms' /\ ps_x s' = ps_x s).
    2:{ intros cd s' ms' [H E]. eapply at_exit_imp_of_immp; [exact H| rewrite E; exact PSX]. }
    eapply (implM_keeps ps_x usegs); [apply keeps_seq; [apply raw_free_keepsx| apply keeps_ret]|].
    unfold implM. iprefix. zstep. zstep. apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm s (fun cd s' ms' => at_exit_immp (Some pv) cd s' ms') msx) end.
    eapply implM_bind.
    { unfold rfree_stmt in FREE.
      eapply FREE with (lo := usp0 - 8388608) (B := usp0) (p := bufp) (A := A) (n := cap); try reflexivity; unfold RATP;
        rewrite ?(unsigned_lit RMallocRep.RATP) by (unfold RMallocRep.RATP; lia); rewrite ?(unsigned_lit (usp0 + -128)) by lia; unfold RMallocRep.RATP; cbn [Z.add];
        first [ exact P0s | left; reflexivity | exact AUX | exact ST | exact MI | exact ERR | unfold RFREE_STACK; lia | lia ]. }
    cbv beta. intros [] s2 ms2 PO.
    destruct PO as (w0 & w1 & w2 & rb0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m3 & -> & MI3 & ST3 & ERR3 & AUX3 & HPR3 & FAE3 & SOE3 & HEAP3).
    rewrite ?(unsigned_lit (usp0 + -128)) in ST3 by lia. rewrite ?(unsigned_lit (usp0 + -128)) in HPR3 by lia.
    replace (ret_pc (Z_to_bv 64 0x3e988)) with (Z_to_bv 64 0x3e988) by (symmetry; rpc).
    rewrite (lb_remove_head bufp A cap [(pv, Av, 8)] (RHEAP_blocks_nodup_proof _ _ _ P0s)) in HEAP3, HPR3.
    pose proof (agree_of_heap_pres _ _ _ _ HPR3) as AG.
    Ltac cliS := right; left; unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP.
    apply implM_ret.
    eapply (main_return1 code s2 pv Av); [lia| eapply (MFRAME_heap sp0 argv); [exact HPR3| exact FR0]| unfold LO; exact ST3| | exact HEAP3| | | | | exact AUX3| | | lia| exact MI3].
    - eapply (ESTAT_agree TID _ _ _ 1 AG); [| exact ES]. intros a Ha. cliS.
      unfold estat_addr, aex_addr, stdin_addr, RSTDIN, iosx_img_addr, RGOT_LLVMINIT in *. lia.
    - rewrite SOE3. eapply stdout_file_agree; [exact AG| | exact SOF]. intros a Ha. cliS. unfold stdout_addr in *. lia.
    - eapply stderr_wfile0_agree; [exact AG| | exact SE]. intros a Ha. cliS. unfold stderr_addr in *. lia.
    - destruct SJS as [i SJ]. exists i. eapply sj_statics_agree; [exact AG| | exact SJ]. intros a Ha. cliS. unfold sjs_addr, SJ_STATICS_LO, SJ_STATICS_HI in *. lia.
    - eapply lx_statics_agree; [exact AG| | exact LXS]. intros a Ha. cliS. unfold lxs_addr, LX_GOT_STDERR, LX_STDERR_PTR, SJ_GOT_NOTHROW, SJ_IMPL_VT24, SJ_DPI_VPTR in *. lia.
    - unfold RATP in ERR3 |- *. cbv delta [MallocRep.wz] in ERR3 |- *. exact ERR3.
    - eapply rw_cells_agree; [exact AG| exact VOBJ|]. intros a Ha. cliS. unfold AEX_VEC_OBJ in Ha. cbn in Ha. lia.
  Qed.

  Lemma phaseDE : forall bufp A cap DATA cw L cfg sc s ms,
    RUN0' bufp A cap DATA cw L cfg sc s ms -> ps_x s = None ->
    implM usegs (main_tail bufp cw cfg (skipn (Z.to_nat (6 + L)) (map bv_unsigned DATA))) s (fun cd s' ms' => at_exit_imp cd s' ms') ms.
  Proof.
    intros bufp A cap DATA cw L cfg sc s ms R0 PSX.
    destruct R0 as (x1 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & x23 & t3 & t4 & t5 & t6 & F & fc & mm & junk & errv
                    & -> & HD & P0 & BLK & FR & BA & EX & ERR & FRM).
    pose proof (sp_facts sp0 VSP CEIL) as SF. unfold LO in SF. try (pose proof alloc_ceiling_range as CEIL_RANGE).
    pose proof BA as (ST & MI & ES & AUX & SSP & LXS & IMG). unfold LO in ST. pose proof ERR as ERR0. unfold RMallocRep.RERRNO in ERR. pose proof FR as FR0. unfold MFRAME in FR.
    pose proof EX as (SOF & SE & FL & [ib IB] & VEC0).
    pose proof ES as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & GOT & DSO & IOSX & AEXI).
    destruct HD as (LEN6 & LENC & CAPM & BR & CW & EL & LR & LCW & ECW & ECFG & CFGR & SCR & TB). unfold MAX_INPUT in CAPM.
    pose proof BR as (BR1 & BR2 & BR3 & BR4 & BR5). try (pose proof alloc_ceiling_range as CEIL_RANGE).
    pose proof BLK as BLKB. apply (proj1 (rw_cells_app _ _ _ [CB (length DATA) DATA] _)) in BLKB. destruct BLKB as [BLKB _].
    apply rw_cells_bytes_at in BLKB. cbn [cells_bytes cbytes app] in BLKB. rewrite app_nil_r in BLKB.
    unfold main_tail. rewrite ECFG.
    unfold implM. iprefix. zstep. zstep. zstep. zstep. zstep. apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm s (fun cd s' ms' => at_exit_imp cd s' ms') msx) end.
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
      - exact FL.
      - exact VEC0.
      - exact PSX.
      - apply stderr_wfile0_wfile. exact SE.
      - exact SSP.
      - exact SOF.
      - exact AEXI.
      - exact GOT.
      - exact AUX.
      - lia.
      - lia.
      - exact ST.
      - lia.
      - unfold GLOBALS_TOP. lia.
      - unfold RTARGET_RUN_STACK, LX_FUZZ_STACK, SJ_CLIENT_FRAMES, RMALLOC_STACK. lia.
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
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F1 & fc1 & m1 & errv1 & pv & Av
                    & -> & RR & MI1 & FRM1 & ST1 & ERR1 & AUX1 & P1 & PSX1 & VEC1 & LXS1 & FL1 & SE1 & SSP1 & SOF1 & AEX1 & DP).
    rewrite ?(unsigned_lit (usp0 + -128)) in ST1 by lia. rewrite ?(unsigned_lit (usp0 + -128)) in DP by lia.
    unfold RATP in ERR1. cbv delta [MallocRep.wz] in ERR1. rewrite ?(unsigned_lit RMallocRep.RATP) in ERR1 by (unfold RMallocRep.RATP; lia). unfold RMallocRep.RATP in ERR1. cbn [Z.add] in ERR1.
    cbv delta [MallocRep.wz].
    replace (ret_pc (Z_to_bv 64 0x3e900)) with (Z_to_bv 64 0x3e900) by (symmetry; rpc).
    pose proof (agree_of_drv_pres _ _ _ _ DP) as AG.
    assert (FR1 : FRAME' m1).
    { unfold MFRAME. eapply rw_cells_agree; [exact AG| exact FR|]. intros a Ha. cbn in Ha. apply stack_client; [lia|].
      unfold DRVW, LXW_IMP, LXW_SJ, LXW_AEX, LXW_UNW, LXW_TP, IMP_VEC_LO, SJ_STATICS_LO, SJ_STATICS_HI, RINIT_FLAG. cbn. lia. }
    assert (ES1 : ESTAT TID 1 m1).
    {
      destruct ES as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15). unfold ESTAT, RGOT_LLVMINIT.
      Ltac treD AG E := eapply rw_cells_agree; [exact AG| exact E|]; intros a Ha; cbn in Ha; split;
        [ unfold DRVW, LXW_IMP, LXW_SJ, LXW_AEX, LXW_UNW, LXW_TP, IMP_VEC_LO, SJ_STATICS_LO, SJ_STATICS_HI, RINIT_FLAG; cbn; lia
        | right; right; unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP in *; lia ].
      split; [treD AG E1|]. split; [treD AG E2|]. split; [treD AG E3|]. split; [treD AG E4|]. split; [treD AG E5|]. split; [treD AG E6|].
      split; [treD AG E7|]. split; [treD AG E8|].
      split. { eapply stdin_file0_agree; [exact AG| | exact E9]. intros a Ha. unfold stdin_addr, RSTDIN in Ha. split;
               [ unfold DRVW, LXW_IMP, LXW_SJ, LXW_AEX, LXW_UNW, LXW_TP, IMP_VEC_LO, SJ_STATICS_LO, SJ_STATICS_HI, RINIT_FLAG; cbn; lia
               | right; right; unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP in *; lia ]. }
      split; [treD AG E10|]. split; [treD AG E11|]. split; [treD AG E12|]. split; [treD AG E13|].
      split. { eapply iosx_img_facts_agree; [exact AG| | exact E14]. intros a Ha. unfold iosx_img_addr in Ha. split;
               [ unfold DRVW, LXW_IMP, LXW_SJ, LXW_AEX, LXW_UNW, LXW_TP, IMP_VEC_LO, SJ_STATICS_LO, SJ_STATICS_HI, RINIT_FLAG; cbn; lia
               | right; right; unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP in *; lia ]. }
      exact AEX1. }
    assert (BA2 : BASE2 m1).
    { split; [unfold LO; exact ST1| split; [exact MI1| split; [exact ES1| split; [exact AUX1|]]]].
      eapply stderr_wfile0_agree; [exact AG| | exact SE]. intros a Ha. unfold stderr_addr in Ha. split;
        [ unfold DRVW, LXW_IMP, LXW_SJ, LXW_AEX, LXW_UNW, LXW_TP, IMP_VEC_LO, SJ_STATICS_LO, SJ_STATICS_HI, RINIT_FLAG; cbn; lia
        | right; right; unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP in *; lia ]. }

    destruct VEC1 as (A2 & IN2 & VC & HW).
    assert (EA : A2 = Av) by (eapply (vec_block_unique _ _ _ _ _ _ P1 IN2); left; reflexivity). subst A2.
    unfold imp_vec_cells, IMP_VEC_LO in VC.
    apply (proj1 (rw_cells_app _ _ _ [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1); CB 6 (MallocRep.zeros 6)] _)) in VC. destruct VC as [_ VOBJ]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add] in VOBJ.
    replace (0xf32d0 + 8)%Z with AEX_VEC_OBJ in VOBJ by reflexivity.
    clear AG DP.
    rewrite TB.
    destruct (Z.lt_ge_cases sc 0) as [SNEG|SPOS].
    -
      replace (sc <? 0) with true by (symmetry; apply Z.ltb_lt; lia).
      replace (Z_to_bv 64 sc) with (Z_to_bv 64 (sc + 2^64)) by (apply Z_to_bv_eqm; rewrite <- (Z.mod_add sc 1) by lia; f_equal; lia).
      unfold implM. iprefix. zstep. if_cases K; zify_cond K; [| exfalso; lia].

      zstep. zstep. zstep.
      replace (ret_pc (Z_to_bv 64 0x3e910)) with (Z_to_bv 64 0x3e910) by (symmetry; rpc).
      apply evt_done.
      lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm s1 (fun cd s' ms' => at_exit_imp cd s' ms') msx) end.
      apply implM_bind_assoc. unfold alloc_count. apply implM_retb. apply implM_retb. unfold COUNT_MAX. cbn [Z.ltb].
      unfold implM. iprefix. zstep. zstep. zstep. if_cases K2; zify_cond K2; [| exfalso; rewrite ?unsigned_lit in K2 by lia; lia].
      apply evt_done. lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm s1 (fun cd s' ms' => at_exit_imp cd s' ms') msx) end.
      eapply free_return; [lia| exact P1| exact FR1| exact BA2| exact SOF1| unfold RMallocRep.RERRNO; exact ERR1| exists true; exact FL1| exact LXS1| exact VOBJ| exact PSX1].
    -
      replace (sc <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
      apply implM_retb.
      unfold implM. iprefix. zstep. if_cases K; zify_cond K; [exfalso; lia|].
      zstep. zstep.
      apply evt_done. lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm s1 (fun cd s' ms' => at_exit_imp cd s' ms') msx) end.
      eapply free_return; [lia| exact P1| exact FR1| exact BA2| exact SOF1| unfold RMallocRep.RERRNO; exact ERR1| exists true; exact FL1| exact LXS1| exact VOBJ| exact PSX1].
  Qed.
End D.
End WithCeiling0.
