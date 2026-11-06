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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RMallocRep RMallocTree RMalloc_iface R_StartupLib R_Startup R_Exit RF_pad RF_stdio_lib Stdio_iface RF_printf_iface Stdio_init RF_syscalls.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RDrv_iface RDrv_ctx RDrv_kio RDrv_A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac rpc := apply ret_pc_even; [lia| reflexivity].
Ltac fix_lit_store :=
  try (lazymatch goal with
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
           change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
           change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
       end).
Ltac zst := zstep; fix_lit_store.

(* [comment removed for export] *)
Definition S_OOM : Z := 0x10378.    Definition s_oom : list Z := (str "cli: out of memory"%string ++ [10])%list.
Definition S_SHORT : Z := 0x108b1.  Definition s_short : list Z := (str "cli: input shorter than header"%string ++ [10])%list.
Definition S_OVER : Z := 0x10401.   Definition s_over : list Z := (str "cli: config_len overruns input"%string ++ [10])%list.
Lemma s_oom_ro : ro_bytes_b rsegs S_OOM (zb s_oom) = true. Proof. vm_compute. reflexivity. Qed.
Lemma s_short_ro : ro_bytes_b rsegs S_SHORT (zb s_short) = true. Proof. vm_compute. reflexivity. Qed.
Lemma s_over_ro : ro_bytes_b rsegs S_OVER (zb s_over) = true. Proof. vm_compute. reflexivity. Qed.


(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__0.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition TEXIT2 (so : stdout_st) (fs : Fs.Fs) : TSet :=
  ShapeAlg.t_emit (Wz 1 (fst (exit_flush_pure so))) (t_exit (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) fs).
(* [comment removed for export] *)
Definition TDIE (ps : list (list Z)) (so : stdout_st) (fs : Fs.Fs) : TSet :=
  ShapeAlg.t_emit (Wz 2 (concat ps)) (TEXIT2 so fs).
Lemma TEXIT2_nil : forall so fs, TEXIT2 so fs []. Proof. intros. apply ShapeAlg.t_emit_has_nil. Qed.
Lemma TDIE_nil : forall ps so fs, TDIE ps so fs []. Proof. intros. apply ShapeAlg.t_emit_has_nil. Qed.

(* [comment removed for export] *)
Lemma fd_lookup_insert_same : forall fds fd e, fd_lookup (fd_insert fds fd e) fd = Some e.
Proof. intros fds fd e. unfold fd_insert. cbn [fd_lookup]. rewrite bv_eqb_refl. reflexivity. Qed.
Lemma rw_cells_CB0' : forall m A cs, rw_cells rsegs m A cs -> rw_cells rsegs m A (CB 0 [] :: cs).
Proof. intros m A cs [[W B] R]. split; [split|]; [split; [reflexivity | exact W] | exact B | exact R]. Qed.
End RC__0.

Section B.
  Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
  Variables (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (rnd : EntryDraw) (arg0 arg1 : list byte) (TID : Z)
            (PAD : list byte) (S4 S5 S6 S7 S8 S9 S10 S11 : word).
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

  Notation usp0 := (bv_unsigned sp0).
  Notation gpv := (Z_to_bv 64 0x10800).
  Notation tpv := (Z_to_bv 64 RATP).
  Notation IMGB := (build_stack_bytes rph sp0 argv envp uid hw rnd).
  Notation LO' := (LO sp0).
  Notation BASE' := (BASE sp0 argv envp uid hw rnd TID).
  Notation FRAME' mm := (MFRAME sp0 argv mm PAD S7 S6 S5 S4).
  (* [comment removed for export] *)
  Notation HK := (HKG (G_fs FS0)).

  (* [comment removed for export] *)
  Notation GST pc x1 t0 t1 t2 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 F fc mm :=
    (MS (mkR x1 (Z_to_bv 64 (usp0 + -128)) gpv tpv t0 t1 t2 (Z_to_bv 64 2) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 S8 S9 S10 S11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom rsegs)).
  (* [comment removed for export] *)
  Notation RST pc x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 P1v len fd cap x23 t3 t4 t5 t6 F fc mm :=
    (GST pc x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 P1v) (Z_to_bv 64 len) (Z_to_bv 64 fd) (Z_to_bv 64 cap) (Z_to_bv 64 RSTAGE) x23 t3 t4 t5 t6 F fc mm).

  Let DIR := di_run HKG DI.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma rz_fprintf_exit : forall (d : diag_msg) G (s : PState) (LB : list block) mo
      x1 t0 t1 t2 x9 (a1v a2v : word) x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 (F : bvmap 5 word) (fc : bv 32) (mm : mem),
    diag_args d mm a1v a2v (usp0 - 8388608) (usp0 - 128) ->
    Forall (fun p => zlength p + INTERNAL_BUFSIZ <= WRITEV_MAX) (diag_pieces d) ->
    BASE' mm -> HKG G s LB mm mo -> frm0 fc ->
    realizes_cfg acfg rsegs (mkCfg (GST 0x13734 x1 t0 t1 t2 x9 (Z_to_bv 64 0x24a00) a1v a2v x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 F fc mm) mo)
             (TDIE (diag_pieces d) stdout_init (m_fs mo)).
  Proof.
    intros until mm. intros DA SMALL BA HKx FRM.
    pose proof (sp_facts sp0 VSP RCSP) as SF. unfold LO in SF.
    pose proof BA as (ST & MI & RS & AUX & IMG & SE & SOF & YSx & TRx). unfold LO in ST.
    destruct (DIR _ _ _ _ _ HKx) as (Hmi & Hh & Hl).
    destruct (di_ssp HKG DI _ _ _ _ _ HKx) as [SSP1 SSP2]. unfold RGOT_SSP, RSSP_GUARD in SSP1, SSP2.
    rz_seg Hh Hl. zstep. apply evt_done.
    unfold TDIE.
    eapply (rz_fprintf_diag d) with (lo := usp0 - 8388608) (canary := rc_guard) (st := s);
      [ apply TEXIT2_nil | exact Hmi | exact Hh
      | apply stderr_wfile0_wfile; exact SE | reflexivity
      | rewrite unsigned_lit by lia; replace (usp0 + -128) with (usp0 - 128) by lia; exact DA
      | rewrite unsigned_lit by lia; exact ST
      | rewrite unsigned_lit by lia; unfold FPRINTF_DEPTH; lia | unfold GLOBALS_TOP; lia | rewrite unsigned_lit by lia; lia
      | split; [exact SSP1 | exact SSP2] | exact MI | exact FRM | exact SMALL | ].
    intros u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 Ft fc' m2 MUc WMc MI2 FRM2 FEQ ST2 SEW SSP'.
    rewrite !unsigned_lit in MUc by lia. rewrite !unsigned_lit in ST2 by lia.
    replace (ret_pc (Z_to_bv 64 0x13738)) with (Z_to_bv 64 0x13738) by (symmetry; rpc).
    pose proof (agree_on_of_munch _ _ _ MUc WMc) as AG.
    assert (OUT2 : forall a, (0x10000 <= a < 0x56000 /\ ~ (0x24a00 <= a < 0x24a00 + 232)) -> (fun a0 : Z => outside [(usp0 - 8388608, usp0 + -128); (0x24a00, 0x24a00 + 232)] a0) a).
    { intros a Ha. cbn. lia. }
    assert (HK2 : HKG G s LB m2 mo).
    { eapply (di_frame HKG DI); [exact HKx| exact MUc| exact WMc|].
      constructor; [left; cbn [fst snd]; unfold alloc_ceiling in *; lia|]. constructor; [| constructor].
      right; left. cbn [fst snd]. unfold RLIBC, RCTX, RSSP_GUARD, RGOT_SSP. lia. }
    rz_seg Hh Hl. zstep. apply evt_done.
    unfold TEXIT2.
    eapply (rz_exit2 sp0 TID VSP RCSP HT (HKG G) (DIR G) (di_ssp HKG DI G) (di_libc_head HKG DI G) s ps0 LB).
    - unfold LO. exact ST2.
    - eapply (RSTAT_agree TID _ _ _ AG); [intros a Ha; apply OUT2; unfold rstat_addr in Ha; lia| exact RS].
    - exact HK2.
    - eapply (stdout_file_agree _ _ _ _ AG); [intros a Ha; apply OUT2; unfold stdout_addr in Ha; lia| exact SOF].
    - apply stderr_wfile_file. exact SEW.
    - exact MI2.
    - unfold zlength, STDOUT_BUFSIZ. cbn. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition BUFC (mm : mem) (A cap : Z) (DATA junk : list byte) : Prop :=
    rw_cells rsegs mm A [CB (length DATA) DATA; CB (Z.to_nat (cap - Z.of_nat (length DATA))) junk]
    /\ (65536 <= cap <= MAX_INPUT /\ exists k, 0 <= k /\ cap = 2 ^ k) /\ Z.of_nat (length DATA) <= cap /\ rblock_range A cap.

  (* [comment removed for export] *)
  Definition RDCORE (fd : Z) (ent : FdEntry) (cap : Z) (DATA : list byte) (s : PState) (mo : Model)
             (mm : mem) (fc : bv 32) (A : Z) : Prop :=
    exists (junk stg : list byte) (errv : word) (bufp : bptr),
      BUFC mm A cap DATA junk
      /\ HK s [(bufp, A, cap)] mm mo
      /\ fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some ent /\ m_fs mo = FS0
      /\ FRAME' mm /\ BASE' mm /\ rw_cells rsegs mm RERRNO [C4 errv] /\ RSTG mm stg /\ frm0 fc.

  (* [comment removed for export] *)
  Definition RDINV (fd P1v : Z) (ent : FdEntry) (cap : Z) (DATA : list byte) (s : PState) (mo : Model) (ms : machine_state) : Prop :=
    exists (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x23 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (mm : mem) (A : Z),
      ms = RST 0x135a0 x1 t0 t1 t2 (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7 P1v (Z.of_nat (length DATA)) fd cap x23 t3 t4 t5 t6 F fc mm
      /\ RDCORE fd ent cap DATA s mo mm fc A /\ Z.of_nat (length DATA) < cap.

  (* [comment removed for export] *)
  Definition RDBRK (fd P1v : Z) (ent : FdEntry) (cap : Z) (DATA : list byte) (s : PState) (mo : Model) (ms : machine_state) : Prop :=
    exists (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x23 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (mm : mem) (A : Z),
      ms = RST 0x135c8 x1 t0 t1 t2 (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7 P1v (Z.of_nat (length DATA)) fd cap x23 t3 t4 t5 t6 F fc mm
      /\ RDCORE fd ent cap DATA s mo mm fc A.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variable MO : Model.
  Hypothesis MOFS : m_fs MO = FS0.
  Hypothesis MOFD : alloc_fd (m_fds MO) = Z_to_bv 64 3.
  Hypothesis MOFD3 : fd_lookup (m_fds MO) (Z_to_bv 64 3) = None.

  (* [comment removed for export] *)
  Lemma rz_after_open_err : forall mo (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (fc : bv 32) (mm : mem) (P1v : Z) (errv : word),
    FRAME' mm -> BASE' mm -> HK ps0 [] mm mo -> rw_cells rsegs mm RERRNO [C4 errv] -> frm0 fc -> m_fs mo = FS0 ->
    nth_error (argv_ptrs sp0 argv envp) 1 = Some (Z_to_bv 64 P1v) -> 0 <= P1v < 2^64 ->
    realizes_cfg acfg rsegs (mkCfg (GST 0x13514 (Z_to_bv 64 0x13514) t0 t1 t2 (Z_to_bv 64 2) (Z_to_bv 64 (-1)) a1 a2 a3 a4 a5 a6 a7
                                (Z_to_bv 64 P1v) (Z_to_bv 64 (envp_addr sp0 argv)) S4 S5 S6 S7 t3 t4 t5 t6 bvmap_empty fc mm) mo)
             (TDIE (pieces_cannot_open (map bv_unsigned arg1)) stdout_init FS0).
  Proof.
    intros until errv. intros FR BA HKx ERR FRM FS HP1 P1R.
    pose proof (sp_facts sp0 VSP RCSP) as SF. unfold LO in SF. pose proof (IMGB_len sp0 argv envp uid hw rnd VSP VARGV VENVP) as IL. pose proof (IMGB_ts sp0 argv envp uid hw rnd EFIT) as ITS.
    pose proof BA as (ST & MI & RS & AUX & IMG & SE & SOF & YSx & TRx). unfold LO in ST.
    pose proof RS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G78 & GD0).
    pose proof VARGV as (_ & _ & ARGLEN & NONUL & _).
    assert (A1NN : ~ In (Z_to_bv 8 0) arg1) by (rewrite EARGV in NONUL; inversion NONUL as [|? ? ? X]; inversion X; assumption).
    assert (A1LEN : Z.of_nat (length arg1) <= 131071) by (rewrite EARGV in ARGLEN; inversion ARGLEN as [|? ? ? X]; inversion X; assumption).
    destruct (argv_cstring sp0 argv envp uid hw rnd mm IMG 1 arg1 ltac:(rewrite EARGV; reflexivity) ltac:(clear -SF; Z.div_mod_to_equations; lia))
      as (p1 & slack1 & HP1' & P1LO & P1HI & STR1 & SLK1). unfold str_base, struct_size, argc, envc in P1LO.
    pose proof (bytes_at_bound _ _ _ _ IMG) as IMGBD.
    assert (EP : p1 = P1v).
    { rewrite HP1 in HP1'. assert (E : bv_unsigned (Z_to_bv 64 P1v) = bv_unsigned (Z_to_bv 64 p1)) by congruence.
      rewrite !unsigned_lit in E by lia. lia. }
    subst p1.
    destruct (DIR _ _ _ _ _ HKx) as (Hmi & Hh & Hl).
    rz_seg Hh Hl.
    replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 18446744073709551615) by (apply Z_to_bv_eqm; reflexivity).
    zstep. if_cases K0; zify_cond K0; try (exfalso; revert K0; clear; intros K0; rewrite ?unsigned_lit in K0 by lia; lia). clear K0.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. apply evt_done.
    rewrite <- FS.
    eapply (rz_fprintf_exit (DCannotOpen (map bv_unsigned arg1)) _ ps0 []); [| | exact BA | exact HKx | exact FRM].
    - cbn [diag_args]. split; [reflexivity|]. exists slack1. rewrite unsigned_lit by lia.
      unfold zb. rewrite zbytes_map_unsigned'. unfold zlength. rewrite !length_map.
      split; [exact STR1|]. split; [apply map_unsigned_pos; exact A1NN|]. split; [lia|].
      split; [unfold FmtFp.INT_MAX; lia|]. split; [right; lia| unfold GLOBALS_TOP; lia].
    - cbn [diag_pieces pieces_cannot_open]. unfold INTERNAL_BUFSIZ, WRITEV_MAX, zlength.
      repeat constructor; rewrite ?length_map, ?length_app; cbn [length str list_ascii_of_string map app]; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma rz_after_open_ok : forall (KL : TSet) mo1 (ent : FdEntry) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (fc : bv 32) (mm : mem) (P1v : Z) (errv : word),
    FRAME' mm -> BASE' mm -> HK ps0 [] mm mo1 -> rw_cells rsegs mm RERRNO [C4 errv] -> RSTG mm (repeat (Z_to_bv 8 0) (Z.to_nat STAGE)) -> frm0 fc ->
    m_fs mo1 = FS0 -> fd_lookup (m_fds mo1) (Z_to_bv 64 3) = Some ent ->
    KL [] ->
    (forall s mo ms, RDINV 3 P1v ent 65536 [] s mo ms -> realizes_cfg acfg rsegs (mkCfg ms mo) KL) ->
    realizes_cfg acfg rsegs (mkCfg (GST 0x13514 (Z_to_bv 64 0x13514) t0 t1 t2 (Z_to_bv 64 2) (Z_to_bv 64 3) a1 a2 a3 a4 a5 a6 a7
                                (Z_to_bv 64 P1v) (Z_to_bv 64 (envp_addr sp0 argv)) S4 S5 S6 S7 t3 t4 t5 t6 bvmap_empty fc mm) mo1)
             KL.
  Proof.
    intros until errv. intros FR BA HK1 ERR RSG FRM FS FD3 KL0 HL.
    pose proof (sp_facts sp0 VSP RCSP) as SF. unfold LO in SF. pose proof (IMGB_len sp0 argv envp uid hw rnd VSP VARGV VENVP) as IL. pose proof (IMGB_ts sp0 argv envp uid hw rnd EFIT) as ITS.
    pose proof BA as (ST & MI & RS & AUX & IMG & SE & SOF & YSx & TRx). unfold LO in ST. unfold RERRNO in ERR.
    destruct (DIR _ _ _ _ _ HK1) as (Hmi & Hh & Hl).
    rz_seg Hh Hl.
    zstep. if_cases K0; zify_cond K0; try (exfalso; rewrite ?unsigned_lit in K0 by lia; lia). clear K0.
    zstep. zstep. zstep. zstep. apply evt_done.
    (* [comment removed for export] *)
    eapply (di_mallocX HKG DI (G_fdfs (m_fds mo1) FS0) (frame_ok_G_fdfs _ _)) with (lo := usp0 - 8388608) (B := usp0) (s := ps0) (LB := []) (n := 65536);
      try reflexivity.
    all: unfold RATP; rewrite ?(unsigned_lit 0x34d40) by lia; rewrite ?(unsigned_lit (usp0 + -128)) by lia.
    - exact KL0.
    - apply (di_pin_fds HKG DI). exact HK1.
    - exact AUX.
    - lia.
    - exact ST.
    - lia.
    - unfold RMALLOC_STACK. lia.
    - exact ERR.
    - exact MI.
    - unfold NUSERc. lia.
    - (* [comment removed for export] *)
      intros v0 v1 v2 c0 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 m2 mo2 s2 errv2 p A MI2 ST2 ERR2 AUX2 HPR EA0 BR HK2 [junk BLK].
      subst c0.
      rewrite ?(unsigned_lit (usp0 + -128)) in ST2 by lia. rewrite ?(unsigned_lit (usp0 + -128)) in HPR by lia.
      replace (ret_pc (Z_to_bv 64 0x13528)) with (Z_to_bv 64 0x13528) by (symmetry; rpc).
      destruct (di_fdfs HKG DI _ _ _ _ _ _ HK2) as [FDS2 FS2].
      apply (di_unpin_fds HKG DI) in HK2.
      assert (BA2 : BASE' m2) by (eapply (BASE_heap_pres sp0 argv envp uid hw rnd TID); [exact BA| exact HPR| exact MI2| unfold LO; exact ST2| exact AUX2]).
      assert (FR2 : FRAME' m2) by (unfold MFRAME; eapply rheap_pres_rw_cells; [exact HPR| exact FR| left; cbn; lia]).
      assert (RSG2 : RSTG m2 (repeat (Z_to_bv 8 0) (Z.to_nat STAGE))).
      { unfold RSTG in *. eapply rheap_pres_rw_cells; [exact HPR| exact RSG|]. right; left. pose proof STAGE_val.
        cbn [cells_size csize Nat.add]. unfold RSTAGE, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP. lia. }
      clear FR ST MI RS AUX IMG SE SOF YSx TRx RSG.
      pose proof BR as (BR1 & BR2 & BR3 & BR4 & BR5). unfold alloc_ceiling in BR4.
      destruct (DIR _ _ _ _ _ HK2) as (Hmi2 & Hh2 & Hl2).
      rz_seg Hh2 Hl2.
      unfold wz. zstep. if_cases K1; zify_cond K1; try (exfalso; rewrite ?unsigned_lit in K1 by lia; lia). clear K1.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. if_cases K2; zify_cond K2; try (exfalso; rewrite ?unsigned_lit in K2 by lia; lia). clear K2.
      zstep. zstep. apply evt_done.
      apply (HL s2 mo2). unfold RDINV. cbn [length Z.of_nat].
      do 17 eexists. exists bvmap_empty, fc, m2, A. split; [unfold RSTAGE; reflexivity|].
      split; [| lia].
      unfold RDCORE. exists junk, (repeat (Z_to_bv 8 0) (Z.to_nat STAGE)), errv2, p.
      split. { unfold BUFC. cbn [length Z.of_nat Z.sub]. rewrite Z.sub_0_r.
               split; [apply rw_cells_CB0'; exact BLK|].
               unfold MAX_INPUT. split; [split; [lia| exists 16; split; [lia| reflexivity]]|]. split; [lia| exact BR]. }
      split; [exact HK2|].
      split; [rewrite FDS2; exact FD3|]. split; [exact FS2|].
      split; [exact FR2|]. split; [exact BA2|]. split; [unfold RERRNO; exact ERR2|]. split; [exact RSG2| exact FRM].
  Qed.

  (* [comment removed for export] *)
  Lemma after_open_facts : forall mo1 (a : sret) (mm m1 : mem) (fc : bv 32) (P1v : Z) stg,
    FRAME' mm -> BASE' mm -> HK ps0 [] mm MO -> RSTG mm stg ->
    munch [(bv_unsigned (Z_to_bv 64 (usp0 + -128)) - 112, bv_unsigned (Z_to_bv 64 (usp0 + -128))); (errno_addr tpv, errno_addr tpv + 4)]%Z mm m1 ->
    wmono rsegs mm m1 -> mem_inv rsegs m1 -> stk rsegs m1 (usp0 - 8388608) (bv_unsigned (Z_to_bv 64 (usp0 + -128))) ->
    (exists n rsp evs, nstep (NOpen arg1) MO rsp mo1 evs /\ lazy_free_node (NOpen arg1) /\ n = NOpen arg1) -> m_vmmaps mo1 = m_vmmaps MO ->
    m_fs mo1 = m_fs MO ->
    FRAME' m1 /\ BASE' m1 /\ HK ps0 [] m1 mo1 /\ RSTG m1 stg.
  Proof.
    intros mo1 a mm m1 fc P1v stg FR BA HK0 RSG MU WM MI1 ST1 (n & rsp & evs & Hst & LF & _) VM VFS.
    pose proof (sp_facts sp0 VSP RCSP) as SF. unfold LO in SF. pose proof STAGE_val as SV.
    unfold RATP in MU. rewrite ?(unsigned_lit 0x34d40) in MU by lia. rewrite ?(unsigned_lit (usp0 + -128)) in MU by lia.
    rewrite ?(unsigned_lit (usp0 + -128)) in ST1 by lia. change (0x34d40 + -164) with RERRNO in MU.
    assert (WOKW : Forall (WOK sp0) [(usp0 + -128 - 112, usp0 + -128); (RERRNO, RERRNO + 4)]).
    { unfold WOK, LO, RERRNO. constructor; [cbn [fst snd]; lia|]. constructor; [cbn [fst snd]; lia| constructor]. }
    split. { unfold MFRAME in *. eapply rw_cells_agree; [eapply agree_on_of_munch; [exact MU| exact WM] | exact FR | intros a0 Ha; cbn in Ha |- *; unfold RERRNO; lia]. }
    split. { eapply (BASE_munch sp0 argv envp uid hw rnd TID VSP RCSP VARGV VENVP); [exact BA| exact WOKW| exact MU| exact WM| exact MI1| unfold LO; exact ST1]. }
    assert (HK1 : HK ps0 [] m1 MO).
    { eapply (di_frame HKG DI); [exact HK0| exact MU| exact WM|].
      constructor; [left; cbn [fst snd]; unfold alloc_ceiling in *; lia|]. constructor; [| constructor].
      right; left. cbn [fst snd]. unfold RERRNO, RLIBC, RCTX, RSSP_GUARD, RGOT_SSP. lia. }
    split.
    - eapply (di_mo HKG DI); [exact HK1 | exact LF | exact Hst | exact VM | unfold G_fs; rewrite VFS; exact MOFS].
    - unfold RSTG in *. eapply rw_cells_agree; [eapply agree_on_of_munch; [exact MU| exact WM] | exact RSG |].
      intros a0 Ha; cbn [cells_size csize Nat.add] in Ha; cbn; unfold RERRNO, RSTAGE in *; lia.
  Qed.

  Lemma rz_read_all_head : forall (KLOOP : FdEntry -> TSet) (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (fc : bv 32) (mm : mem),
    FRAME' mm -> BASE' mm -> HK ps0 [] mm MO -> rw_cells rsegs mm RERRNO [C4 (Z_to_bv 64 0)] -> RSTG mm (repeat (Z_to_bv 8 0) (Z.to_nat STAGE)) -> frm0 fc ->
    (forall ent, KLOOP ent []) ->
    (forall ent s mo ms P1v, open_classify arg1 MO = OcMay ent ->
        nth_error (argv_ptrs sp0 argv envp) 1 = Some (Z_to_bv 64 P1v) -> 0 <= P1v < 2^64 ->
        RDINV 3 P1v ent 65536 [] s mo ms -> realizes_cfg acfg rsegs (mkCfg ms mo) (KLOOP ent)) ->
    realizes_cfg acfg rsegs
      (mkCfg (MS (mkR (Z_to_bv 64 0x17048) (Z_to_bv 64 (usp0 + -128)) gpv tpv t0 t1 t2
                      (Z_to_bv 64 2) (Z_to_bv 64 2) (Z_to_bv 64 2) (Z_to_bv 64 (usp0 + 8)) (Z_to_bv 64 (envp_addr sp0 argv)) a3 a4 a5 a6 a7
                      (Z_to_bv 64 0x134d4) (Z_to_bv 64 (envp_addr sp0 argv)) S4 S5 S6 S7 S8 S9 S10 S11 t3 t4 t5 t6)
                 bvmap_empty (Z_to_bv 64 0x13504) fc None mm (seg_rom rsegs)) MO)
      (match open_classify arg1 MO with
       | OcErrno _ => TDIE (pieces_cannot_open (map bv_unsigned arg1)) stdout_init FS0
       | OcMay ent => t_alt2 (TDIE (pieces_cannot_open (map bv_unsigned arg1)) stdout_init FS0) (KLOOP ent)
       end).
  Proof.
    intros until mm. intros FR BA HK0 ERR RSG FRM KL0 HL.
    pose proof (sp_facts sp0 VSP RCSP) as SF. unfold LO in SF. pose proof (IMGB_len sp0 argv envp uid hw rnd VSP VARGV VENVP) as IL. pose proof (IMGB_ts sp0 argv envp uid hw rnd EFIT) as ITS.
    pose proof BA as (ST & MI & RS & AUX & IMG & SE & SOF & YSx & TRx). unfold LO in ST. unfold RERRNO in ERR. pose proof FR as FR0. unfold MFRAME in FR.
    pose proof VARGV as (_ & _ & ARGLEN & NONUL & SLASH).
    destruct (DIR _ _ _ _ _ HK0) as (Hmi & Hh & Hl).
    destruct (di_ssp HKG DI _ _ _ _ _ HK0) as [G1 G2]. unfold RGOT_SSP, RSSP_GUARD in G1, G2.
    (* [comment removed for export] *)
    destruct (argv_cstring sp0 argv envp uid hw rnd mm IMG 1 arg1 ltac:(rewrite EARGV; reflexivity) ltac:(clear -SF; Z.div_mod_to_equations; lia))
      as (P1v & slack1 & HP1 & P1LO & P1HI & STR1 & SLK1). unfold str_base, struct_size, argc, envc in P1LO.
    destruct (stack_pieces sp0 argv envp uid hw rnd mm IMG) as (_ & ARGVP & _).
    assert (A1NN : ~ In (Z_to_bv 8 0) arg1) by (rewrite EARGV in NONUL; inversion NONUL as [|? ? ? X]; inversion X; assumption).
    assert (A1LEN : Z.of_nat (length arg1) <= 131071) by (rewrite EARGV in ARGLEN; inversion ARGLEN as [|? ? ? X]; inversion X; assumption).
    assert (A1SL : path_has_slash arg1 = false) by (rewrite EARGV in SLASH; cbn [tl] in SLASH; inversion SLASH as [|? ? [X _] _]; exact X).
    assert (STR1' : bytes_at rsegs mm P1v (arg1 ++ [Z_to_bv 8 0])).
    { change (arg1 ++ Z_to_bv 8 0 :: slack1) with (arg1 ++ ([Z_to_bv 8 0] ++ slack1)) in STR1. rewrite app_assoc in STR1. apply bytes_at_app in STR1. destruct STR1 as [S1 _]. exact S1. }
    rz_seg Hh Hl.
    pose proof (u64ro_read mm (usp0 + 8) (argv_ptrs sp0 argv envp ++ [Z_to_bv 64 0]) 1 (Z_to_bv 64 P1v) (Z_to_bv 64 (usp0 + 16))
                  ARGVP ltac:(rewrite nth_error_app1 by (rewrite argv_ptrs_length, EARGV; cbn; lia); exact HP1) ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
    zstep. clear RD. zstep. zstep. zstep.
    apply evt_done.
    (* [comment removed for export] *)
    pose proof (open_spec (Z_to_bv 64 0x13514) (Z_to_bv 64 (usp0 + -128)) gpv tpv t0 t1 t2 (Z_to_bv 64 2) (Z_to_bv 64 2)
                  (Z_to_bv 64 P1v) (Z_to_bv 64 0) (Z_to_bv 64 (envp_addr sp0 argv)) a3 a4 a5 a6 a7
                  (Z_to_bv 64 P1v) (Z_to_bv 64 (envp_addr sp0 argv)) S4 S5 S6 S7 S8 S9 S10 S11 t3 t4 t5 t6 bvmap_empty fc mm
                  arg1 (Z_to_bv 64 0) rc_guard (usp0 - 8388608)) as IMO.
    specialize (IMO ltac:(rewrite (unsigned_lit (usp0 + -128)) by lia; exact ST)
                    ltac:(rewrite (unsigned_lit P1v) by lia; exact STR1')
                    ltac:(unfold RATP; rewrite (unsigned_lit 0x34d40) by lia; exact ERR)
                    G1 G2 MI eq_refl A1NN A1SL).
    specialize (IMO ltac:(rewrite (unsigned_lit (usp0 + -128)) by lia; lia)).
    do 6 (specialize (IMO ltac:(unfold RATP, RF_syscalls.got_ssp, RF_syscalls.ssp_guard; rewrite ?(unsigned_lit 0x34d40) by lia; rewrite ?(unsigned_lit (usp0 + -128)) by lia; rewrite ?(unsigned_lit P1v) by lia; lia))).
    specialize (IMO ltac:(unfold RATP; rewrite ?(unsigned_lit 0x34d40) by lia; lia)).
    destruct (open_classify arg1 MO) as [e|ent] eqn:OC.
    - (* [comment removed for export] *)
      eapply (rz_open_errno arg1 e _ _ MO); [exact IMO | exact Hmi | exact Hh | apply TDIE_nil | exact OC |].
      intros ms' PO.
      destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 & -> & MUc & WMc & MI1 & ST1 & ERR1 & _ & _ & _ & _).
      cbn [open_ret open_errno] in *.
      replace (ret_pc (Z_to_bv 64 0x13514)) with (Z_to_bv 64 0x13514) by (symmetry; rpc).
      destruct (after_open_facts MO (SErr e) mm m1 fc P1v _ FR0 BA HK0 RSG MUc WMc MI1 ST1) as (FR1 & BA1 & HK1 & RSG1).
      { exists (NOpen arg1), (efferr e), []. split; [| split; [exact I | reflexivity]].
        apply (nstep_cfg_sub acfg). apply nstep_open_iff. rewrite OC. auto. }
      { reflexivity. }
      { reflexivity. }
      unfold RATP in ERR1. rewrite ?(unsigned_lit 0x34d40) in ERR1 by lia. change (0x34d40 + -164) with RERRNO in ERR1.
      eapply (rz_after_open_err MO); [exact FR1 | exact BA1 | exact HK1 | exact ERR1 | exact FRM | exact MOFS | exact HP1 | pose proof (bytes_at_bound _ _ _ _ IMG); lia].
    - (* [comment removed for export] *)
      eapply (rz_open_may arg1 ent _ _ MO); [exact IMO | exact Hmi | exact Hh | apply TDIE_nil | apply KL0 | exact OC | | | |].
      + rewrite MOFD. exact MOFD3.
      + rewrite MOFD, unsigned_lit by lia. lia.
      + intros e ms' He PO.
        destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 & -> & MUc & WMc & MI1 & ST1 & ERR1 & _ & _ & _ & _).
        cbn [open_ret open_errno] in *.
        replace (ret_pc (Z_to_bv 64 0x13514)) with (Z_to_bv 64 0x13514) by (symmetry; rpc).
        destruct (after_open_facts MO (SErr e) mm m1 fc P1v _ FR0 BA HK0 RSG MUc WMc MI1 ST1) as (FR1 & BA1 & HK1 & RSG1).
        { exists (NOpen arg1), (efferr e), []. split; [| split; [exact I | reflexivity]].
          apply (nstep_cfg_sub acfg). apply nstep_open_iff. rewrite OC. split; [reflexivity|]. left. exists e. auto. }
        { reflexivity. }
        { reflexivity. }
        unfold RATP in ERR1. rewrite ?(unsigned_lit 0x34d40) in ERR1 by lia. change (0x34d40 + -164) with RERRNO in ERR1.
        eapply (rz_after_open_err MO); [exact FR1 | exact BA1 | exact HK1 | exact ERR1 | exact FRM | exact MOFS | exact HP1 | pose proof (bytes_at_bound _ _ _ _ IMG); lia].
      + intros ms' rsp evs Hst PO Hmi1. rewrite MOFD in *. rewrite (unsigned_lit 3) in PO by lia.
        destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 & -> & MUc & WMc & MI1 & ST1 & ERR1 & _ & _ & _ & _).
        cbn [open_ret open_errno] in *.
        replace (ret_pc (Z_to_bv 64 0x13514)) with (Z_to_bv 64 0x13514) by (symmetry; rpc).
        set (mo1 := with_fds (fd_insert (m_fds MO) (Z_to_bv 64 3) ent) MO) in *.
        destruct (after_open_facts mo1 (SVal 3) mm m1 fc P1v _ FR0 BA HK0 RSG MUc WMc MI1 ST1) as (FR1 & BA1 & HK1 & RSG1).
        { exists (NOpen arg1), rsp, evs. split; [exact Hst | split; [exact I | reflexivity]]. }
        { subst mo1. apply m_vmmaps_with_fds. }
        { subst mo1. apply m_fs_with_fds. }
        unfold RATP in ERR1. rewrite ?(unsigned_lit 0x34d40) in ERR1 by lia. change (0x34d40 + -164) with RERRNO in ERR1.
        eapply (rz_after_open_ok (KLOOP ent) mo1 ent); [exact FR1 | exact BA1 | exact HK1 | exact ERR1 | exact RSG1 | exact FRM | | | apply KL0 |].
        * subst mo1. rewrite m_fs_with_fds. exact MOFS.
        * subst mo1. rewrite m_fds_with_fds. apply fd_lookup_insert_same.
        * intros s mo ms RI. exact (HL ent s mo ms P1v ltac:(first [exact OC | reflexivity]) HP1 ltac:(clear - P1LO P1HI SF IL; lia) RI).
  Qed.
End B.
