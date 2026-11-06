(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation Strings.String.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlg ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac Image ZBridge SysStep ITree ITreeCfg Nodes NodesCfg Decode Arr FP InitMem.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Images.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Top Require Import ImplRz ImplRzCfg TrzNodesCfg TrzStdioCfg TrzLeafCfg ImplSplitCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Agent Require Import MallocBlocks.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.MS Require Import Malloc_iface.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim STree Malloc Monad StdioBase Stdio FmtFp Driver RawAlloc MSafe MLive.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RMallocRep RMallocTree RMalloc_iface R_StartupLib R_Startup R_Exit RF_pad RF_stdio_lib Stdio_iface RF_printf_iface Stdio_init RF_syscalls RF_memcpy RF_fwritex_gen Printf_model.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RDrv_iface RDrv_ctx RDrv_kio RDrv_A RDrv_run RAlloc_rz.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RX_atexit.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import MSuccIface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac rpc := apply ret_pc_even; [lia| reflexivity].
(* [comment removed for export] *)
Ltac fix_lit_store2 :=
  try (lazymatch goal with
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
           change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
           change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 2 ?z)) _) =>
           change (Z_to_le_bytes 2 z) with (le2 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?z)) _) =>
           change (Z_to_le_bytes 1 z) with [Z_to_bv 8 z]; mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) =>
           change (le1 (Z_to_bv 64 z)) with [Z_to_bv 8 z]; mem_after_store
       end).
Ltac zst2 := zstep; fix_lit_store2.
(* [comment removed for export] *)
Ltac RET0 :=
  lazymatch goal with
  | |- context [Z_to_bv 64 (Z.land ?x 78)] =>
      replace (Z_to_bv 64 (Z.land x 78)) with (Z_to_bv 64 0) by (vm_compute; reflexivity)
  | _ => idtac
  end.

Lemma In_lb_remove : forall p b LB, In b LB -> blk_id b <> p -> In b (lb_remove p LB).
Proof.
  intros p b LB. unfold lb_remove. induction LB as [|x LB IH]; [intros [] |].
  intros [-> | H] NE; rewrite filter_cons; destruct (decide _) as [Y|N].
  - left. reflexivity.
  - exfalso. apply N. destruct (bptr_eqb (blk_id b) p) eqn:E; [| exact I]. exfalso. apply NE. apply bptr_eqb_true. exact E.
  - right. apply IH; assumption.
  - apply IH; assumption.
Qed.

Section RUN2.
  Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
  Variables (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (rnd : EntryDraw) (arg0 arg1 : list byte) (TID : Z)
            (PAD : list byte) (S4 S5 S6 S7 X7 S8 S9 S10 S11 : word).
  Hypothesis VSP : valid_sp sp0.
  Hypothesis RCSP : rc_sp = bv_unsigned sp0.          (* [comment removed for export] *)
  Hypothesis RCS : rc_secret = bv_unsigned (secret_of (at_random_bytes (ed_random rnd))).   (* [comment removed for export] *)
  Hypothesis EFIT : entry_stack_fits sp0 argv envp.   (* [comment removed for export] *)
  Hypothesis VARGV : valid_argv argv.
  Hypothesis VENVP : valid_envp envp.
  Hypothesis EARGV : argv = [arg0; arg1].
  Hypothesis HT : 0 < TID < 4194304.
  Variable HKG : HKG_T.
  Hypothesis DI : drv_iface HKG.
  Variable FS0 : Fs.Fs.
  Notation HK := (HKG (G_fs FS0)).

  Notation usp0 := (bv_unsigned sp0).
  Notation gpv := (Z_to_bv 64 0x10800).
  Notation tpv := (Z_to_bv 64 RATP).
  Notation IMGB := (build_stack_bytes rph sp0 argv envp uid hw rnd).
  Notation LO' := (LO sp0).
  Notation BASE' := (BASE sp0 argv envp uid hw rnd TID).
  Notation FRAME' mm := (MFRAME sp0 argv mm PAD S7 S6 S5 S4).

  Let DIR := di_run HKG DI.
  Hypothesis YF : yfuzz_rz_stmt HK.
  Notation TRFRAME := (TRFRAME sp0 X7).
  Notation RBASE := (RBASE sp0 argv envp uid hw rnd TID).
  Notation RUNINV := (RUNINV sp0 argv envp uid hw rnd TID PAD S4 S5 S6 S7 X7 HKG FS0).
  Notation RBASE_heap_pres := (RBASE_heap_pres sp0 argv envp uid hw rnd TID VSP RCSP).
  Notation RBASE_munch := (RBASE_munch sp0 argv envp uid hw rnd arg0 arg1 TID VSP RCSP EFIT VARGV VENVP EARGV).
  Notation RWOK := (RWOK sp0).
  Notation RWOK_outside := (RWOK_outside sp0 argv envp arg0 arg1 VSP RCSP EFIT VARGV EARGV).
  Notation rz_run_loop := (rz_run_loop sp0 argv envp uid hw rnd arg0 arg1 TID PAD S4 S5 S6 S7 X7 S8 S9 S10 S11 VSP RCSP EFIT VARGV VENVP EARGV HKG DI FS0 YF).
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section TargetRun.
    (* [comment removed for export] *)
    Variables (bufp : bptr) (A cap L PL SB1 : Z) (FILE : list byte).
    Hypothesis HL : 0 <= L.
    Hypothesis HPL : 0 <= PL.
    Hypothesis HLEN : Z.of_nat (length FILE) = 6 + L + PL.
    Hypothesis HCAP : Z.of_nat (length FILE) < cap.
    Hypothesis HCAPM : cap <= 67108864.
    Let PAY : list byte := skipn (Z.to_nat (6 + L)) FILE.
    Let calls : nat := if L =? 0 then 1%nat else S (Z.to_nat (bv_unsigned (nth 2 FILE (Z_to_bv 8 0)) mod 4)).

    (* [comment removed for export] *)
    Variable KR : Z -> stdout_st -> TSet.
    Hypothesis KR_nil : forall st so, KR st so [].

    Definition RETINV (so : stdout_st) (s : PState) (mo : Model) (mm : mem) (fc : bv 32) : Prop :=
      exists (LB : list block) (errv : word),
        FRAME' mm /\ stk rsegs mm LO' (usp0 + -128) /\ mem_inv rsegs mm /\ RSTAT TID mm /\ rauxv_ok mm usp0 /\ bytes_at rsegs mm usp0 IMGB
        /\ stderr_wfile0 mm /\ YST mm /\ stdout_file mm so /\ zlength (so_buf so) <= STDOUT_BUFSIZ
        /\ HK s LB mm mo /\ In (bufp, A, cap) LB /\ m_fs mo = FS0
        /\ rw_cells rsegs mm RERRNO [C4 errv] /\ frm0 fc.

    Hypothesis HRET : forall (status : Z) so s mo mm fc (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word),
      0 <= status < 2^32 -> RETINV so s mo mm fc ->
      realizes_cfg acfg rsegs (mkCfg (MS (mkR (Z_to_bv 64 0x13648) (Z_to_bv 64 (usp0 + -128)) gpv tpv t0 t1 t2 (Z_to_bv 64 (A + 2)) (Z_to_bv 64 A) (Z_to_bv 64 status) a1 a2 a3 a4 a5 a6 a7
                                        (Z_to_bv 64 L) (Z_to_bv 64 (A + 6 + L)) (Z_to_bv 64 PL) (Z_to_bv 64 SB1) (Z_to_bv 64 RSTAGE) X7 S8 S9 S10 S11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 0x13648) fc None mm (seg_rom rsegs)) mo)
               (KR status so).

    (* [comment removed for export] *)
    Definition TPR (n : nat) (so : stdout_st) : TSet := ShapeAlg.t_emit (Wz 1 (fst (emits n so))) (KR 0 (snd (emits n so))).

    (* [comment removed for export] *)
    Lemma rz_tr_tail : forall (T OWN : Z) (pad : list byte) (REST0 : list block) (pown : bptr),
      REST0 = (match OWN with 0 => [] | _ => [(pown, OWN, PL)] end) ++ [(bufp, A, cap)] ->
      (OWN = 0 \/ 0 < OWN) ->
      forall so s mo mm fc (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3v t3 t4 t5 t6 : word) (F : bvmap 5 word),
      RUNINV T PL A L SB1 PAY pad REST0 so s mo mm fc ->
      realizes_cfg acfg rsegs (mkCfg (MS (mkR x1 (Z_to_bv 64 (usp0 + -208)) gpv tpv t0 t1 t2 (Z_to_bv 64 PL) (Z_to_bv 64 T) a0 a1 a2 a3 a4 a5 a6 a7
                                        (Z_to_bv 64 OWN) s3v (Z_to_bv 64 0x34c40) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (-2)) S8 S9 S10 S11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 0x13894) fc None mm (seg_rom rsegs)) mo)
               (KR 0 so).
    Proof.
      intros T OWN pad REST0 pown ER HO so s mo mm fc x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3v t3 t4 t5 t6 F RI.
      destruct RI as (LK & errv & TRF & FR & RB & SOF & SOB & HKx & NBLK & FS & PAYB & T0 & T62 & PLEN & PL26 & PBLK & ERR & FRM).
      pose proof (sp_facts sp0 VSP RCSP) as SF. unfold LO in SF.
      pose proof RB as (ST & MI & RS & AUX & IMG & SE & YS). unfold LO in ST. unfold RERRNO in ERR. unfold TRFRAME in TRF.
      destruct (DIR _ _ _ _ _ HKx) as (Hmi & Hh & Hl).
      rz_seg Hh Hl. zstep. zstep. 
      destruct HO as [-> | POS].
      - (* [comment removed for export] *)
        eapply evt_cut; [apply rfree_null_spec; reflexivity|]. cbv beta. intros ms' ->.
        replace (ret_pc (Z_to_bv 64 0x1389c)) with (Z_to_bv 64 0x1389c) by (symmetry; rpc).
        zstep. zstep. zstep. RET0. do 10 zstep. release_frame TRF ST (usp0 + -128). zstep.
        replace (ret_pc (Z_to_bv 64 0x13648)) with (Z_to_bv 64 0x13648) by (symmetry; rpc).
        apply evt_done. apply (HRET 0 so s mo); [lia|]. cbn [app] in ER. subst REST0.
        exists (LK ++ [(bufp, A, cap)]), errv. repeat (split; [assumption|]).
        split; [apply in_or_app; right; left; reflexivity|]. repeat (split; [assumption|]). exact FRM.
      - (* [comment removed for export] *)
        destruct OWN as [|q|q] eqn:EO; try lia. subst REST0.
        apply evt_done.
        eapply (di_freeX HKG DI (G_fdfs (m_fds mo) FS0) (frame_ok_G_fdfs _ _)) with (lo := usp0 - 8388608) (B := usp0) (p := pown) (A := Z.pos q) (n := PL);
          try reflexivity.
        all: unfold RATP; rewrite ?(unsigned_lit 0x34d40) by lia; rewrite ?(unsigned_lit (usp0 + -208)) by lia.
        + apply KR_nil.
        + apply (di_pin_fds HKG DI). exact HKx.
        + apply in_or_app. right. left. reflexivity.
        + exact AUX.
        + lia.
        + exact ST.
        + lia.
        + unfold RFREE_STACK. lia.
        + exact ERR.
        + exact MI.
        + intros w0 w1 w2 rb0 e1 e2 e3 e4 e5 e6 e7 w3 w4 w5 w6 m4 mo4 s4 MI4 ST4 ERR4 AUX4 HPR4 HK4.
          rewrite ?(unsigned_lit (usp0 + -208)) in ST4 by lia. rewrite ?(unsigned_lit (usp0 + -208)) in HPR4 by lia.
          replace (ret_pc (Z_to_bv 64 0x1389c)) with (Z_to_bv 64 0x1389c) by (symmetry; rpc).
          destruct (di_fdfs HKG DI _ _ _ _ _ _ HK4) as [FDS4 FS4]. apply (di_unpin_fds HKG DI) in HK4.
          assert (INB : In (bufp, A, cap) (lb_remove pown (LK ++ [(pown, Z.pos q, PL); (bufp, A, cap)]))).
          { destruct (di_blocks HKG DI _ _ _ _ _ HKx) as (_ & _ & ND).
            apply In_lb_remove; [apply in_or_app; right; right; left; reflexivity|]. cbn [blk_id fst snd]. intros E. subst pown.
            rewrite map_app in ND. cbn [map blk_id fst] in ND.
            apply NoDup_app_remove_l in ND. inversion ND as [|x l NI ND']; subst. apply NI. left. reflexivity. }
          assert (RB4 : RBASE m4) by (eapply (RBASE_heap_pres _ mm m4 (usp0 + -208)); [exact RB | exact HPR4 | lia | exact MI4 | exact ST4 | exact AUX4]).
          assert (TRF4 : TRFRAME m4 pad A L PL SB1).
          { unfold TRFRAME. eapply rheap_pres_rw_cells; [exact HPR4| exact TRF| left; cbn; lia]. }
          unfold TRFRAME in TRF4.
          assert (FR4 : FRAME' m4) by (unfold MFRAME; eapply rheap_pres_rw_cells; [exact HPR4| exact FR| left; cbn; lia]).
          assert (SOF4 : stdout_file m4 so) by (eapply stdout_file_heap_pres; [exact HPR4 | exact SOF]).
          clear ST MI RS AUX IMG SE YS. pose proof RB4 as (ST & MI & RS & AUX & IMG & SE & YS). unfold LO in ST.
          destruct (DIR _ _ _ _ _ HK4) as (Hmi4 & Hh4 & Hl4).
          rz_seg Hh4 Hl4. zstep. zstep. zstep. RET0. do 10 zstep. release_frame TRF4 ST (usp0 + -128). zstep.
          replace (ret_pc (Z_to_bv 64 0x13648)) with (Z_to_bv 64 0x13648) by (symmetry; rpc).
          apply evt_done. apply (HRET 0 so s4 mo4); [lia|].
          unfold RERRNO in ERR4.
          exists (lb_remove pown (LK ++ [(pown, Z.pos q, PL); (bufp, A, cap)])), errv. repeat (split; [assumption|]).
          first [exact FRM | split; [exact HK4|]; split; [exact INB|]; repeat (split; [assumption|]); exact FRM].
    Qed.

    (* [comment removed for export] *)
    Lemma rz_tr_alloc : forall (s : PState) mo mm fc (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (pad junk : list byte) (errv : word),
      0 < PL ->
      TRFRAME mm pad A L PL SB1 -> FRAME' mm -> RBASE mm -> stdout_file mm stdout_init ->
      HK s [(bufp, A, cap)] mm mo -> m_fs mo = FS0 ->
      rw_cells rsegs mm A [CB (length FILE) FILE; CB (Z.to_nat (cap - Z.of_nat (length FILE))) junk] -> rblock_range A cap ->
      rw_cells rsegs mm RERRNO [C4 errv] -> frm0 fc ->
      realizes_cfg acfg rsegs (mkCfg (MS (mkR x1 (Z_to_bv 64 (usp0 + -208)) gpv tpv t0 t1 t2 (Z_to_bv 64 PL) (Z_to_bv 64 (A + 6 + L))
                                        a0 a1 a2 a3 a4 a5 a6 a7
                                        (Z_to_bv 64 L) (Z_to_bv 64 (A + 2)) (Z_to_bv 64 0x34c40) (Z_to_bv 64 (Z.of_nat calls)) (Z_to_bv 64 RSTAGE) X7 S8 S9 S10 S11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 0x13800) fc None mm (seg_rom rsegs)) mo)
               (TPR calls stdout_init).
    Proof.
      intros s mo mm fc x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F pad junk errv PLP TRF FR RB SOF HKx FS BLK BR ERR FRM.
      pose proof (sp_facts sp0 VSP RCSP) as SF. unfold LO in SF.
      pose proof RB as (ST & MI & RS & AUX & IMG & SE & YS). unfold LO in ST. unfold RERRNO in ERR. unfold TRFRAME in TRF. unfold MFRAME in FR.
      pose proof BR as (BR1 & BR2 & BR3 & BR4 & BR5). unfold alloc_ceiling in BR4.
      destruct (DIR _ _ _ _ _ HKx) as (Hmi & Hh & Hl).
      assert (CALLS : (1 <= calls <= 4)%nat).
      { unfold calls. destruct (L =? 0); [lia|]. pose proof (Z.mod_pos_bound (bv_unsigned (nth 2 FILE (Z_to_bv 8 0))) 4 ltac:(lia)). lia. }
      assert (TPR_nil : forall n so, TPR n so []) by (intros; unfold TPR; apply ShapeAlg.t_emit_has_nil).
      rz_seg Hh Hl. zstep. zstep. apply evt_done.
      (* [comment removed for export] *)
      eapply (di_mallocX HKG DI (G_fdfs (m_fds mo) FS0) (frame_ok_G_fdfs _ _)) with (lo := usp0 - 8388608) (B := usp0) (s := s) (LB := [(bufp, A, cap)]) (n := PL);
        try reflexivity.
      all: unfold RATP; rewrite ?(unsigned_lit 0x34d40) by lia; rewrite ?(unsigned_lit (usp0 + -208)) by lia.
      - apply TPR_nil.
      - apply (di_pin_fds HKG DI). exact HKx.
      - exact AUX.
      - lia.
      - exact ST.
      - lia.
      - unfold RMALLOC_STACK. lia.
      - exact ERR.
      - exact MI.
      - unfold NUSERc. lia.
      - (* [comment removed for export] *)
        intros v0 v1 v2 c0 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 m2 mo2 s2 errv2 p T MI2 ST2 ERR2 AUX2 HPR EA0 BR' HK2 [junk' NBLK]. subst c0.
        rewrite ?(unsigned_lit (usp0 + -208)) in ST2 by lia. rewrite ?(unsigned_lit (usp0 + -208)) in HPR by lia.
        replace (ret_pc (Z_to_bv 64 0x13808)) with (Z_to_bv 64 0x13808) by (symmetry; rpc).
        destruct (di_fdfs HKG DI _ _ _ _ _ _ HK2) as [FDS2 FS2]. apply (di_unpin_fds HKG DI) in HK2.
        assert (RB2 : RBASE m2) by (eapply (RBASE_heap_pres _ mm m2 (usp0 + -208)); [exact RB | exact HPR | lia | exact MI2 | exact ST2 | exact AUX2]).
        assert (TRF2 : TRFRAME m2 pad A L PL SB1) by (unfold TRFRAME; eapply rheap_pres_rw_cells; [exact HPR| exact TRF| left; cbn; lia]).
        assert (FR2 : FRAME' m2) by (unfold MFRAME; eapply rheap_pres_rw_cells; [exact HPR| exact FR| left; cbn; lia]).
        assert (SOF2 : stdout_file m2 stdout_init) by (eapply stdout_file_heap_pres; [exact HPR | exact SOF]).
        assert (BLK2 : rw_cells rsegs m2 A [CB (length FILE) FILE; CB (Z.to_nat (cap - Z.of_nat (length FILE))) junk]).
        { eapply rheap_pres_rw_cells; [exact HPR| exact BLK|]. right; right. exists (bufp, A, cap). split; [left; reflexivity|]. cbn [blk_addr blk_size fst snd cells_size csize Nat.add]. lia. }
        clear ST MI RS AUX IMG SE YS. pose proof RB2 as (ST & MI & RS & AUX & IMG & SE & YS). unfold LO in ST.
        pose proof BR' as (BQ1 & BQ2 & BQ3 & BQ4 & BQ5). unfold alloc_ceiling in BQ4.
        destruct (di_blocks HKG DI _ _ _ _ _ HK2) as (_ & DISJ0 & ND).
        assert (DISJ : T + PL <= A \/ A + cap <= T).
        { pose proof (DISJ0 (p, T, PL) (bufp, A, cap) ltac:(left; reflexivity) ltac:(right; left; reflexivity)) as D.
          cbn [blk_id blk_addr blk_size fst snd] in D. apply D. cbn [map blk_id fst] in ND. inversion ND as [|x l NI ND']; subst. intros E. apply NI. rewrite E. left. reflexivity. }
        (* [comment removed for export] *)
        pose proof BLK2 as SRC. apply (proj1 (rw_cells_app _ _ _ [CB (length FILE) FILE] _)) in SRC. destruct SRC as [SRC _].
        pose proof (rw_cells_bytes_at _ _ _ _ SRC) as SRCB. cbn [cells_bytes cbytes app] in SRCB. rewrite app_nil_r in SRCB. clear SRC.
        rewrite <- (firstn_skipn (Z.to_nat (6 + L)) FILE) in SRCB. apply bytes_at_app in SRCB. destruct SRCB as [_ PAYB].
        rewrite length_firstn in PAYB. replace (A + Z.of_nat (Nat.min (Z.to_nat (6 + L)) (length FILE))) with (A + 6 + L) in PAYB by lia.
        assert (PLEN : Z.of_nat (length PAY) = PL) by (unfold PAY; rewrite length_skipn; lia).
        destruct (DIR _ _ _ _ _ HK2) as (Hmi2 & Hh2 & Hl2).
        rz_seg Hh2 Hl2. unfold wz. zstep. if_cases K1; zify_cond K1; try (exfalso; rewrite ?unsigned_lit in K1 by lia; lia). clear K1.
        zstep. zstep. zstep. zstep.
        eapply evt_cut.
        { eapply memcpy_callw with (src := PAY) (junk := junk'); [exact PAYB| lia| exact NBLK| lia| lia| lia| lia| exact MI]. }
        cbv beta. intros ms' PO.
        destruct PO as (w0 & w1 & w2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m3 & -> & MUc & WMc & MI3 & NB3 & _).
        transport_after_call rsegs m2 m3 MUc WMc.
        replace (ret_pc (Z_to_bv 64 0x1381c)) with (Z_to_bv 64 0x1381c) by (symmetry; rpc).
        assert (WOKW : Forall RWOK [(T, T + PL)]) by (unfold RWOK, alloc_ceiling; constructor; [cbn [fst snd]; lia| constructor]).
        assert (RB3 : RBASE m3) by (eapply RBASE_munch; [exact RB2 | exact WOKW | exact MUc | exact WMc | exact MI3 | unfold LO; exact ST]).
        pose proof (agree_on_of_munch _ _ _ MUc WMc) as AG3.
        assert (TRF3 : TRFRAME m3 pad A L PL SB1).
        { unfold TRFRAME. eapply rw_cells_agree; [exact AG3 | exact TRF2 | intros ax Ha; cbn in Ha |- *; lia]. }
        assert (FR3 : FRAME' m3).
        { unfold MFRAME. eapply rw_cells_agree; [exact AG3 | exact FR2 | intros ax Ha; cbn in Ha |- *; lia]. }
        assert (SOF3 : stdout_file m3 stdout_init).
        { eapply stdout_file_munch; [exact MUc | exact WMc | | exact SOF2]. intros ax Ha. cbn. unfold stdout_addr in Ha. lia. }
        assert (HK3 : HK s2 [(p, T, PL); (bufp, A, cap)] m3 mo2).
        { eapply (di_frame HKG DI); [exact HK2| exact MUc| exact WMc|].
          constructor; [| constructor]. right; right. exists (p, T, PL). split; [left; reflexivity|]. cbn [fst snd blk_addr blk_size]. lia. }
        clear MUc WMc AG3 ST MI RS AUX IMG SE YS. pose proof RB3 as (ST & MI & RS & AUX & IMG & SE & YS). unfold LO in ST.
        zstep. zstep. zstep. zstep. apply evt_done.
        unfold TPR.
        eapply (rz_run_loop T PL T A L SB1 PAY pad [(p, T, PL); (bufp, A, cap)] (fun so => KR 0 so) (fun so => KR_nil 0 so)) with (s := s2).
        + intros so s' mo' m' fc' x1' u0 u1 u2 e0 e1 e2 e3 e4 e5 e6 e7 s3' u3 u4 u5 u6 F' RI'.
          eapply (rz_tr_tail T T pad _ p); [| right; lia | exact RI']. destruct T; try lia; reflexivity.
        + exact CALLS.
        + exists [], errv2. cbn [app]. repeat (split; [assumption|]).
          split; [unfold zlength, STDOUT_BUFSIZ; cbn; lia|]. split; [exact HK3|]. split; [cbn [length Z.of_nat]; unfold NHELDc; lia|]. split; [exact FS2|].
          split. { pose proof (rw_cells_bytes_at _ _ _ _ NB3) as X. cbn [cells_bytes cbytes app] in X. rewrite app_nil_r in X. exact X. }
          split; [lia|]. split; [lia|]. split; [exact PLEN|]. split; [lia|].
          split; [left; exists (p, T, PL); split; [left; reflexivity| cbn [blk_addr blk_size fst snd]; lia]|].
          split; [| exact FRM]. unfold RATP in ERR2. rewrite ?(unsigned_lit 0x34d40) in ERR2 by lia. unfold RERRNO. exact ERR2.
    Qed.

    (* [comment removed for export] *)
    Lemma rz_tr_empty : forall (s : PState) mo mm fc (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (pad : list byte) (errv : word),
      PL = 0 ->
      TRFRAME mm pad A L PL SB1 -> FRAME' mm -> RBASE mm -> stdout_file mm stdout_init ->
      HK s [(bufp, A, cap)] mm mo -> m_fs mo = FS0 ->
      rw_cells rsegs mm RERRNO [C4 errv] -> frm0 fc ->
      realizes_cfg acfg rsegs (mkCfg (MS (mkR x1 (Z_to_bv 64 (usp0 + -208)) gpv tpv t0 t1 t2 (Z_to_bv 64 PL) (Z_to_bv 64 (A + 6 + L))
                                        a0 a1 a2 a3 a4 a5 a6 a7
                                        (Z_to_bv 64 L) (Z_to_bv 64 (A + 2)) (Z_to_bv 64 0x34c40) (Z_to_bv 64 (Z.of_nat calls)) (Z_to_bv 64 RSTAGE) X7 S8 S9 S10 S11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 0x1384c) fc None mm (seg_rom rsegs)) mo)
               (TPR calls stdout_init).
    Proof.
      intros s mo mm fc x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F pad errv PL0 TRF FR RB SOF HKx FS ERR FRM.
      pose proof (sp_facts sp0 VSP RCSP) as SF. unfold LO in SF.
      pose proof RB as (ST & MI & RS & AUX & IMG & SE & YS). unfold LO in ST. unfold RERRNO in ERR.
      destruct (DIR _ _ _ _ _ HKx) as (Hmi & Hh & Hl).
      assert (CALLS : (1 <= calls <= 4)%nat).
      { unfold calls. destruct (L =? 0); [lia|]. pose proof (Z.mod_pos_bound (bv_unsigned (nth 2 FILE (Z_to_bv 8 0))) 4 ltac:(lia)). lia. }
      assert (PAY0 : PAY = []) by (unfold PAY; apply skipn_all2; lia).
      rz_seg Hh Hl. zstep. zstep. zstep. zstep. apply evt_done.
      unfold TPR. rewrite PL0.
      eapply (rz_run_loop Y_EMPTY 0 0 A L SB1 [] pad [(bufp, A, cap)] (fun so => KR 0 so) (fun so => KR_nil 0 so)) with (s := s).
      - intros so s' mo' m' fc' x1' u0 u1 u2 e0 e1 e2 e3 e4 e5 e6 e7 s3' u3 u4 u5 u6 F' RI'.
        pose proof (rz_tr_tail Y_EMPTY 0 pad _ bufp eq_refl (or_introl eq_refl) so s' mo' m' fc' x1' u0 u1 u2 e0 e1 e2 e3 e4 e5 e6 e7 s3' u3 u4 u5 u6 F') as TT.
        rewrite PL0, PAY0 in TT. exact (TT RI').
      - exact CALLS.
      - exists [], errv. cbn [app]. rewrite PL0 in TRF. repeat (split; [assumption|]).
        split; [unfold zlength, STDOUT_BUFSIZ; cbn; lia|]. split; [exact HKx|]. split; [cbn [length Z.of_nat]; unfold NHELDc; lia|]. split; [exact FS|].
        split; [apply bytes_at_nil; unfold Y_EMPTY; lia|]. split; [unfold Y_EMPTY; lia|]. split; [unfold Y_EMPTY; lia|].
        split; [reflexivity|]. split; [lia|]. split; [right; reflexivity|]. split; [exact ERR| exact FRM].
    Qed.

    (* [comment removed for export] *)
    Lemma rz_target_run : forall (s : PState) mo (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (mm : mem) (junk : list byte) (errv : word),
      FRAME' mm -> BASE' mm -> HK s [(bufp, A, cap)] mm mo -> m_fs mo = FS0 ->
      rw_cells rsegs mm A [CB (length FILE) FILE; CB (Z.to_nat (cap - Z.of_nat (length FILE))) junk] -> rblock_range A cap ->
      rw_cells rsegs mm RERRNO [C4 errv] -> frm0 fc ->
      realizes_cfg acfg rsegs (mkCfg (MS (mkR (Z_to_bv 64 0x13648) (Z_to_bv 64 (usp0 + -128)) gpv tpv t0 t1 t2 (Z_to_bv 64 (A + 2)) (Z_to_bv 64 A)
                                        (Z_to_bv 64 (A + 2)) (Z_to_bv 64 L) (Z_to_bv 64 (A + 6 + L)) (Z_to_bv 64 PL) a4 a5 a6 a7
                                        (Z_to_bv 64 L) (Z_to_bv 64 (A + 6 + L)) (Z_to_bv 64 PL) (Z_to_bv 64 SB1) (Z_to_bv 64 RSTAGE) X7 S8 S9 S10 S11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 0x137a4) fc None mm (seg_rom rsegs)) mo)
               (TPR calls stdout_init).
    Proof.
      intros s mo t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 F fc mm junk errv FR BA HKx FS BLK BR ERR FRM.
      pose proof (sp_facts sp0 VSP RCSP) as SF. unfold LO in SF.
      pose proof BA as (ST & MI & RS & AUX & IMG & SE & SOF & YSx & TRx). unfold LO in ST. pose proof FR as FR0. unfold MFRAME in FR. unfold RERRNO in ERR.
      destruct TRx as [TR1 TR2]. pose proof BR as (BR1 & BR2 & BR3 & BR4 & BR5). unfold alloc_ceiling in BR4.
      destruct (DIR _ _ _ _ _ HKx) as (Hmi & Hh & Hl).
      destruct (di_libc_head HKG DI _ _ _ _ _ HKx) as (cdt & thr & sec & tm1 & LCH). unfold RLIBC in LCH.
      pose proof BLK as BLKF. apply (proj1 (rw_cells_app _ _ _ [CB (length FILE) FILE] _)) in BLKF. destruct BLKF as [BLKF _].
      apply rw_cells_bytes_at in BLKF. cbn [cells_bytes cbytes app] in BLKF. rewrite app_nil_r in BLKF.
      destruct YSx as (YS1 & YS2 & YS3).
      (* [comment removed for export] *)
      pose proof RS as RSc. apply (proj1 (RSTAT_split TID _)) in RSc. destruct RSc as [RS0 AX].
      destruct (ATX_unreg _ AX TR1) as (p3 & p4 & FJ & AJ & ATC & FLG & DSO). unfold atx_cells in ATC. clear AX.
      assert (BLKK : held (rw_cells rsegs mm A [CB (length FILE) FILE; CB (Z.to_nat (cap - Z.of_nat (length FILE))) junk])) by exact BLK.
      assert (BLKFK : held (bytes_at rsegs mm A FILE)) by exact BLKF.
      assert (IMGK : held (bytes_at rsegs mm usp0 IMGB)) by exact IMG.
      clear BLK BLKF IMG.
      rz_seg Hh Hl.
      pose proof (munch_refl [(usp0 - 256, usp0 - 128); (0x34c40, 0x34c40 + 1); (0x54d88, 0x54d88 + 544)] mm) as MU. pose proof (wmono_refl rsegs mm) as WM.
      zstep. carve_frame 80%nat ST.
      zst2. do 8 zstep. do 5 zstep. zstep. zstep. zstep. if_cases K0; zify_cond K0; [| exfalso; apply K0; reflexivity]. clear K0.
      (* [comment removed for export] *)
      zstep. zst2. zstep. zstep. zstep.
      name_sp sp0 (-208)%Z.
      call ratexit_spec; [rewrite Hsp; exact ST | unfold atx_cells; exact ATC | exact LCH | exact MI | reflexivity | lia | lia | ].
      unname_sp. rename POST into ATC1. rename PC into ST.
      replace (ret_pc (Z_to_bv 64 0x13838)) with (Z_to_bv 64 0x13838) by (symmetry; rpc).
      zstep. if_cases K1; zify_cond K1; [| exfalso; apply K1; reflexivity]. clear K1.
      (* [comment removed for export] *)
      zstep. zstep. zstep. if_cases K1; zify_cond K1; [| exfalso; apply K1; reflexivity]. clear K1.
      (* [comment removed for export] *)
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => set (m1 := mx) in * end.
      lazymatch goal with H : stk _ m1 _ _ |- _ => rename H into ST1 end.
      lazymatch goal with H : mem_inv _ m1 |- _ => rename H into MI1 end.
      lazymatch goal with H : munch _ mm m1 |- _ => rename H into MU1 end.
      lazymatch goal with H : wmono _ mm m1 |- _ => rename H into WM1 end.
      lazymatch goal with H : rw_cells _ m1 (usp0 + -208) _ |- _ => rename H into TRF1 end.
      lazymatch goal with H : rw_cells _ m1 0x34c40 _ |- _ => rename H into INI1 end.
      lazymatch goal with H : rw_cells _ m1 0x34c44 _ |- _ => rename H into FLG1 end.
      lazymatch goal with H : rw_cells _ m1 0x24940 _ |- _ => rename H into DSO1 end.
      pose proof (agree_on_of_munch _ _ _ MU1 WM1) as AG1.
      assert (OUT : forall a, (usp0 - 128 <= a \/ (0x10000 <= a < 0x56000 /\ a <> 0x34c40 /\ ~ (0x54d88 <= a < 0x54fa8)) \/ (a < usp0 - 256 /\ (a < 0x10000 \/ 0x56000 <= a))) ->
                       (fun a0 : Z => outside [(usp0 - 256, usp0 - 128); (0x34c40, 0x34c40 + 1); (0x54d88, 0x54d88 + 544)] a0) a) by (intros a Ha; cbn; lia).
      assert (RB1 : RBASE m1).
      { split; [unfold LO; exact ST1|]. split; [exact MI1|].
        split. { apply (proj2 (RSTAT_split TID _)). split.
                 - eapply (RSTAT0_agree TID _ _ _ AG1); [intros a Ha; apply OUT; unfold rstat0_addr in Ha; lia| exact RS0].
                 - eexists true, _, _, _, _.
                   split; [exact ATC1|]. split; [exact INI1|]. split; [exact FLG1| exact DSO1]. }
        split. { eapply rauxv_ok_frame; [exact AUX| exact MU1| exact WM1|]. unfold RAUXV_CELL, RLIBC, alloc_ceiling. constructor; [cbn [fst snd]; lia|]. constructor; [cbn [fst snd]; lia|]. constructor; [cbn [fst snd]; lia| constructor]. }
        split. { eapply bytes_at_agree; [exact AG1| exact IMGK| intros a Ha; apply OUT; pose proof (IMGB_len sp0 argv envp uid hw rnd VSP VARGV VENVP); lia]. }
        split. { eapply (stderr_wfile0_agree _ _ _ AG1); [intros a Ha; apply OUT; unfold stderr_addr in Ha; lia| exact SE]. }
        split; [exact YS1|]. split; [exact YS2| exact YS3]. }
      assert (FR1 : FRAME' m1) by (unfold MFRAME; eapply rw_cells_agree; [exact AG1 | exact FR0 | intros ax Ha; apply OUT; cbn in Ha; lia]).
      assert (SOF1 : stdout_file m1 stdout_init) by (eapply (stdout_file_agree _ _ _ _ AG1); [intros a Ha; apply OUT; unfold stdout_addr in Ha; lia| exact SOF]).
      assert (HK1 : HK s [(bufp, A, cap)] m1 mo).
      { eapply (di_frame HKG DI); [exact HKx| exact MU1| exact WM1|].
        constructor; [left; cbn [fst snd]; unfold alloc_ceiling in *; lia|]. constructor; [| constructor; [| constructor]].
        - right; left. cbn [fst snd]. unfold RLIBC, RCTX, RSSP_GUARD, RGOT_SSP. lia.
        - right; left. cbn [fst snd]. unfold RLIBC, RCTX, RSSP_GUARD, RGOT_SSP. lia. }
      assert (BLK1 : rw_cells rsegs m1 A [CB (length FILE) FILE; CB (Z.to_nat (cap - Z.of_nat (length FILE))) junk]).
      { eapply rw_cells_agree; [exact AG1 | exact BLKK | intros ax Ha; apply OUT; cbn [cells_size csize Nat.add] in Ha; lia]. }
      assert (ERR1 : rw_cells rsegs m1 RERRNO [C4 errv]) by (first [exact ERR | eapply rw_cells_agree; [exact AG1 | exact ERR | intros ax Ha; apply OUT; cbn in Ha; unfold RERRNO; lia]]).
      assert (BLKF1 : bytes_at rsegs m1 A FILE) by (eapply bytes_at_agree; [exact AG1| exact BLKFK| intros a Ha; apply OUT; lia]).
      clearbody m1. clear MU1 WM1 AG1 OUT. try clear ST. try clear MI. try clear TR1. try clear TR2. try clear BLKK. try clear BLKFK. try clear IMGK. try clear FR. try clear FLG1. try clear INI1. try clear DSO1. try clear ATC1. try clear LCH. try clear RS0. try clear SE. try clear YS1. try clear YS2. try clear YS3.
      (* [comment removed for export] *)
      zstep. if_cases K2; zify_cond K2.
      - (* [comment removed for export] *)
        zstep. zstep. if_cases K3; zify_cond K3.
        + (* [comment removed for export] *)
          apply evt_done.
          replace (Z_to_bv 64 1) with (Z_to_bv 64 (Z.of_nat calls)) by (unfold calls; rewrite (proj2 (Z.eqb_eq L 0) K2); reflexivity).
          eapply rz_tr_alloc; try eassumption. all: lia.
        + apply evt_done.
          replace (Z_to_bv 64 1) with (Z_to_bv 64 (Z.of_nat calls)) by (unfold calls; rewrite (proj2 (Z.eqb_eq L 0) K2); reflexivity).
          eapply rz_tr_empty; try eassumption. all: lia.
      - (* [comment removed for export] *)
        assert (E2 : exists d2, nth_error FILE 2 = Some d2).
        { destruct (nth_error FILE 2) as [d2|] eqn:E; [exists d2; reflexivity|]. apply nth_error_None in E. exfalso. lia. }
        destruct E2 as [d2 E2].
        pose proof (byte_range d2) as Rd2.
        pose proof (u8ro_read rsegs m1 _ _ 2 d2 (wa (A + 2)) BLKF1 E2 ltac:(lia) eq_refl) as R2.
        zstep. clear R2. cbv beta. zstep. zstep.
        replace (Z.land (bv_unsigned d2) 3 + 1) with (Z.of_nat calls).
        2:{ unfold calls. replace (L =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
            rewrite (nth_error_nth FILE 2%nat (Z_to_bv 8 0) E2).
            change 3 with (Z.ones 2). rewrite Z.land_ones by lia. change (2 ^ 2) with 4. lia. }
        zstep. if_cases K3; zify_cond K3.
        + apply evt_done. eapply rz_tr_empty; try eassumption. all: lia.
        + apply evt_done. eapply rz_tr_alloc; try eassumption. all: lia.
    Qed.
  End TargetRun.
End RUN2.
