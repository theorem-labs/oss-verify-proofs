(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation Strings.String.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP InitMem MonadX.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Common Require Import DrvAgree Startup_kit STRW_tac F_fmt_fp_lib Printf_fmts.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Ubsan Require Import UImg F_syscalls F_memcpy StdioFiles Startup Exit F_printf_iface Stdio_iface Stdio_kit.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Malloc Require Import MallocBlocks MallocTree MallocHINV Malloc_iface.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Ubsan Require Import RMallocRep RMallocTree RMalloc_iface Harness_iface F_atexit RDriver_iface RDriver_facts RDriver_kit RDriver_ctx RF_main_A RF_main_B1 RF_main_B2 RF_main_B3 RF_main_B4 RF_main_C.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Ubsan Require RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Spec Require Import Prelim STree Malloc Monad Stdio Driver Prog.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Ubsan Require Import RunDraw.
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
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).

  (* [comment removed for export] *)
  Definition BASE2 (mm : mem) : Prop :=
    stk usegs mm LO' (usp0 + -128) /\ mem_inv usegs mm /\ RSTAT TID mm /\ rauxv_ok mm usp0 /\ stderr_file0 mm.

  (* [comment removed for export] *)
  #[using="envp VSP HT FREE"] Lemma free_return : forall (code : Z) (s : PState) (bufp : bptr) (A cap : Z)
      x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 (F : bvmap 5 word) (fc : bv 32) (mm : mem) (errv : word),
    RHEAP s [(bufp, A, cap)] mm -> FRAME' mm -> BASE2 mm -> stdout_file mm (ps_so s) -> rw_cells usegs mm RERRNO [C4 errv] ->
    implM usegs (raw_free bufp ;;; mret code) s RQEXIT
      (GST 0x129e0 x1 t0 t1 t2 (Z_to_bv 64 code) (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 F fc mm).
  Proof.
    intros until errv. intros P0 FR (ST & MI & RS & AUX & SE) SOF ERR.
    pose proof (sp_facts sp0 argv envp VSP) as SF. unfold LO in SF. unfold LO in ST. unfold RERRNO in ERR. unfold MFRAME in FR.
    pose proof (RMalloc_ifaceP.RHEAP_block_range_proof _ _ _ (bufp, A, cap) P0 ltac:(left; reflexivity)) as BR. cbn [blk_addr blk_size fst snd] in BR.
    pose proof BR as (BR1 & BR2 & BR3 & BR4 & BR5). atop_facts.
    unfold implM. iprefix. zstep. zstep. apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm s RQEXIT msx) end.
    eapply implM_bind.
    { unfold rfree_stmt in FREE.
      Local Ltac2 Set LiaHints.tbl := fun () => "0080?11137728426.80 15706896144.80 19954088631.10549364486404.80 61249635161.10566026048179.10566026193812.80 67159604881.80 00000100200300700800<00@00ASSSS2SFSS2SFS2SFS".
eapply FREE with (lo := usp0 - 8388608) (B := usp0) (p := bufp) (A := A) (n := cap); try reflexivity; unfold RATP;
        rewrite ?(unsigned_lit 188464) by lia; rewrite ?(unsigned_lit (usp0 + -128)) by lia;
        first [ exact P0 | left; reflexivity | exact AUX | exact ST | exact MI | exact ERR | unfold RFREE_STACK; lia | lia ]. }
    cbv beta. intros [] s2 ms2 PO.
    destruct PO as (w0 & w1 & w2 & rb0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m3 & -> & MI3 & ST3 & ERR3 & AUX3 & HPR3 & FAE3 & SOE3 & HEAP3).
    rewrite ?(unsigned_lit (usp0 + -128)) in ST3 by lia. rewrite ?(unsigned_lit (usp0 + -128)) in HPR3 by lia.
    replace (ret_pc (Z_to_bv 64 0x129e8)) with (Z_to_bv 64 0x129e8) by (symmetry; rpc).
    cbn [lb_remove filter bptr_eqb fst snd] in HEAP3, HPR3.
    apply implM_ret. change (RQEXIT code s2) with (pat_exit code s2).
    eapply (main_return sp0 argv envp TID VSP HT code s2).
    - unfold MFRAME. eapply rheap_pres_rw_cells; [exact HPR3| exact FR| left; cbn; lia].
    - unfold LO. first [exact ST3| replace (usp0 - 8388608) with (usp0 + -8388608) by lia; exact ST3].
    - eapply RSTAT_heap_pres; [exact HPR3| exact RS].
    - rewrite bptr_eqb_refl in HEAP3 || idtac. exact HEAP3.
    - rewrite SOE3. eapply stdout_file_heap_pres; [exact HPR3| exact SOF].
    - apply stderr_file0_file. eapply stderr_file0_heap_pres; [exact HPR3| exact SE].
    - exact MI3.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  (* [comment removed for export] *)
  #[using="VSP HT FREE TRUN"] Lemma phaseDE : forall bufp A cap DATA cw L cfg sc s ms,
    RUN0' bufp A cap DATA cw L cfg sc s ms ->
    implM usegs (main_tail bufp cw cfg (skipn (Z.to_nat (6 + L)) (map bv_unsigned DATA))) s RQEXIT ms.
  Proof.
    intros bufp A cap DATA cw L cfg sc s ms R0.
    destruct R0 as (x1 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & x23 & F & fc & mm & junk & errv
                    & -> & HD & PST0 & SO0 & BLK & FR & BA & ERR & FRM).
    pose proof (sp_facts sp0 argv envp VSP) as SF. unfold LO in SF.
    pose proof BA as (ST & MI & RS & AUX & IMG & SE & SOF & TR). unfold LO in ST. pose proof ERR as ERR0. unfold RERRNO in ERR. pose proof FR as FR0. unfold MFRAME in FR.
    destruct HD as (LEN6 & LENC & CAPM & BR & CW & EL & LR & LCW & ECW & ECFG & CFGR & SCR & TB). unfold MAX_INPUT in CAPM.
    pose proof BR as (BR1 & BR2 & BR3 & BR4 & BR5). atop_facts.
    pose proof BLK as BLKB. apply (proj1 (rw_cells_app _ _ _ [CB (length DATA) DATA] _)) in BLKB. destruct BLKB as [BLKB _].
    apply rw_cells_bytes_at in BLKB. cbn [cells_bytes cbytes app] in BLKB. rewrite app_nil_r in BLKB.
    unfold main_tail. rewrite ECFG.
    unfold implM. iprefix. zstep. zstep. zstep. zstep. zstep. apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm s RQEXIT msx) end.
    eapply implM_bind.
    { Local Ltac2 Set LiaHints.tbl := fun () => "00H0?10237888770.13410532517288.10111139871162.10111597543158.1341274098377.101 15704848640.10115719478193.13134848519922.3  40223649585.13140887782655.1354792468082.101 49366599444.10150895322524.10153007035616.13454721685382.13456685145487.13559308628433.13659314923118.13566024050052.10166030389045.1317447421819.135 8818979016.101 9608759401.134 9986082271.101 00000600:00;00<00B00C00D00I00J00T00Z00^00b00h01301401801?01C01G01Q01R01V01\S4SPOSS2LRSSS4LENCSSS3S16SS3SCR4SNEGS4LEN6S2SFS2SFS4SNEGS2SF3BR12HaSS2K2S3SCR1KS2SFS2SFS3SCR4SPOSSS2HaS4CAPM".
eapply TRUN with (lo := usp0 - 8388608) (AB := usp0) (p := bufp) (cap := cap);
        rewrite ?(unsigned_lit (usp0 + -128)) by lia.
      - exact PST0.
      - left; reflexivity.
      - rewrite zbytes_map_unsigned. exact BLKB.
      - apply map_unsigned_range.
      - unfold zlength. rewrite length_map. lia.
      - lia.
      - lia.
      - unfold zlength. rewrite length_map. lia.
      - exact TR.
      - exact SE.
      - exact AUX.
      - lia.
      - lia.
      - exact ST.
      - lia.
      - unfold PTARGET_RUN_STACK, HARNESS_STACK. lia.
      - unfold RATP. rewrite (unsigned_lit 188464) by lia. exact ERR.
      - exact MI.
      - exact FRM.
      - rewrite SO0. exact SOF.
      - reflexivity.
      - clear -SF. destruct SF as (_ & S16 & _). OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - unfold wz, zlength. rewrite length_map. reflexivity. }
    cbv beta. intros r s1 ms1 PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F1 & fc1 & m1 & errv1
                    & -> & RR & MI1 & FRM1 & ST1 & ERR1 & AUX1 & DP & P1 & SOF1 & AX1).
    rewrite ?(unsigned_lit (usp0 + -128)) in ST1 by lia. rewrite ?(unsigned_lit (usp0 + -128)) in DP by lia.
    unfold RATP in ERR1. rewrite ?(unsigned_lit 188464) in ERR1 by lia.
    replace (ret_pc (Z_to_bv 64 0x12960)) with (Z_to_bv 64 0x12960) by (symmetry; rpc).
    pose proof (pdrv_pres_agree _ _ _ _ DP) as AG.
    apply (rw_cells_magree usegs _ _ _ _ _ AG) in FR.
    2:{ intros a Ha. cbn in Ha. split; [left; lia|]. unfold pstdout_ivs, PINIT_FLAG, PAEF_INCB, PATX. cbn. lia. }
    assert (RS1 : RSTAT TID m1) by (eapply RSTAT_drv_pres; [exact DP| exact RS| exists true; exact AX1]).
    assert (SE1 : stderr_file0 m1) by (eapply stderr_file0_drv_pres; [exact DP| exact SE]).
    assert (BA2 : BASE2 m1) by (split; [exact ST1| split; [exact MI1| split; [exact RS1| split; [exact AUX1| exact SE1]]]]).
    clear AG DP.
    rewrite TB.
    destruct (Z.lt_ge_cases sc 0) as [SNEG|SPOS].
    - (* [comment removed for export] *)
      replace (sc <? 0) with true by (symmetry; apply Z.ltb_lt; lia).
      replace (Z_to_bv 64 sc) with (Z_to_bv 64 (sc + 2^64)) by (apply Z_to_bv_eqm; rewrite <- (Z.mod_add sc 1) by lia; f_equal; lia).
      unfold implM. iprefix. zstep. if_cases K; zify_cond K; [| exfalso; lia].
      zstep. apply evt_done.
      lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm s1 RQEXIT msx) end.
      apply implM_bind_assoc. eapply implM_bind; [apply ptarget_alloc_count_spec|].
      cbv beta. intros n s2 ms2 (-> & -> & ->). apply implM_retb.
      replace (ret_pc (Z_to_bv 64 0x12970)) with (Z_to_bv 64 0x12970) by (symmetry; rpc).
      unfold COUNT_MAX. change (if 0 <? 251 then 0 else 251) with 0.
      unfold implM. iprefix. zstep. zstep. zstep. if_cases K2; zify_cond K2; [| exfalso; lia].
      apply evt_done. lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm s1 RQEXIT msx) end.
      eapply free_return; [exact P1| exact FR| exact BA2| exact SOF1| unfold RERRNO; exact ERR1].
    - (* [comment removed for export] *)
      replace (sc <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
      apply implM_retb.
      unfold implM. iprefix. zstep. if_cases K; zify_cond K; [exfalso; lia|].
      zstep. zstep.
      apply evt_done. lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm s1 RQEXIT msx) end.
      eapply free_return; [exact P1| exact FR| exact BA2| exact SOF1| unfold RERRNO; exact ERR1].
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End D.
End CANSEC1.
