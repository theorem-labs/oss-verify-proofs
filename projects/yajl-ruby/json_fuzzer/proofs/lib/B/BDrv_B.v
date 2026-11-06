(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation Strings.String.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac Image ZBridge ITree Nodes NodesCfg Decode Arr FP InitMem Frame Mem Cells.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA AImages ExecA LazyModel NodesA ImplRzA CompatE2.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim StdioBase Stdio Driver.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Top Require Import TrzNodes TrzStdio.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import Printf_model.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import B_iface BDrv_ctx BDrv_A.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import BX_atexit B_iface5x.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac rpc := apply ret_pc_even; [lia| reflexivity].
Ltac aceil := first [pose proof alloc_ceiling_range as CEILB | idtac].

(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition s_oom : list Z := (str "cli: out of memory"%string ++ [10])%list.
Definition s_short : list Z := (str "cli: input shorter than header"%string ++ [10])%list.
Definition s_over : list Z := (str "cli: config_len overruns input"%string ++ [10])%list.
Lemma s_oom_ro : ro_bytes_b bsegs A_S_oom (zb s_oom) = true. Proof. vm_compute. reflexivity. Qed.
Lemma s_short_ro : ro_bytes_b bsegs A_S_short (zb s_short) = true. Proof. vm_compute. reflexivity. Qed.
Lemma s_over_ro : ro_bytes_b bsegs A_S_overrun (zb s_over) = true. Proof. vm_compute. reflexivity. Qed.
Lemma str_range : forall s, Forall (fun c => 0 <= c < 256) (str s).
Proof.
  intros s. unfold str. induction (list_ascii_of_string s) as [|a l IH]; cbn; constructor; [| exact IH].
  pose proof (Ascii.N_ascii_bounded a). lia.
Qed.

Lemma m_fds_with_fds : forall f mo, m_fds (with_fds f mo) = f.
Proof. intros f mo; destruct mo; reflexivity. Qed.
Lemma m_fs_with_fds : forall f mo, m_fs (with_fds f mo) = m_fs mo.
Proof. intros f mo; destruct mo; reflexivity. Qed.
Lemma fd_lookup_insert_same : forall fds fd e, fd_lookup (fd_insert fds fd e) fd = Some e.
Proof. intros fds fd e. unfold fd_insert. cbn [fd_lookup]. rewrite bv_eqb_refl. reflexivity. Qed.
Lemma rw_cells_CB0' : forall m A cs, rw_cells bsegs m A cs -> rw_cells bsegs m A (CB 0 [] :: cs).
Proof. intros m A cs [[W B] R]. split; [split|]; [split; [reflexivity | exact W] | exact B | exact R]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition TEXIT2 (so : stdout_st) (fs : Fs.Fs) : TSet :=
  ShapeAlg.t_emit (Wz 1 (fst (exit_flush_pure so))) (t_exit (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) fs).
(* [comment removed for export] *)
Definition TDIE (ps : list (list Z)) (so : stdout_st) (fs : Fs.Fs) : TSet :=
  ShapeAlg.t_emit (Wz 2 (concat ps)) (TEXIT2 so fs).
Lemma TEXIT2_nil : forall so fs, TEXIT2 so fs []. Proof. intros. apply ShapeAlg.t_emit_has_nil. Qed.
Lemma TDIE_nil : forall ps so fs, TDIE ps so fs []. Proof. intros. apply ShapeAlg.t_emit_has_nil. Qed.

Section B.
  Variables (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (rnd : EntryDraw) (arg0 arg1 : list byte)
            (PAD : list byte) (S4 S5 S6 S7 S8 S9 S10 S11 : word).
  Hypothesis VSP : valid_sp sp0.
  Hypothesis RCSP : rc_sp = bv_unsigned sp0.
  Hypothesis EFIT : entry_stack_fits sp0 argv envp.
  Hypothesis VARGV : valid_argv argv.
  Hypothesis VENVP : valid_envp envp.
  Hypothesis EARGV : argv = [arg0; arg1].
  Variable D : adrv_params.
  Hypothesis DI : a_drv_iface bsegs ACONSTS AFMTS D.
  Hypothesis DIx : a_drv_iface5x bsegs ACONSTS D.      (* [comment removed for export] *)
  Notation AHK := (p_AHK D).
  Notation SO := (p_SO D).
  Notation AHEAD := (p_AHEAD D).

  Notation usp0 := (bv_unsigned sp0).
  Notation gpv := (Z_to_bv 64 0x10800).
  Notation tpv := (Z_to_bv 64 0x5e1550).
  Notation IMGB := (build_stack_bytes aph sp0 argv envp uid hw rnd).
  Notation LO' := (LO sp0).
  Notation ABASE' := (ABASE sp0 argv envp uid hw rnd).
  Notation FRAME' mm := (MFRAME sp0 argv mm PAD S7 S6 S5 S4).

  (* [comment removed for export] *)
  Notation GST pc x1 t0 t1 t2 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 F fc mm :=
    (MS (mkR x1 (Z_to_bv 64 (usp0 + -128)) gpv tpv t0 t1 t2 (Z_to_bv 64 2) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 S8 S9 S10 S11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  (* [comment removed for export] *)
  Notation RST pc x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 P1v len fd cap x23 t3 t4 t5 t6 F fc mm :=
    (GST pc x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 P1v) (Z_to_bv 64 len) (Z_to_bv 64 fd) (Z_to_bv 64 cap) (Z_to_bv 64 RSTAGE) x23 t3 t4 t5 t6 F fc mm).

  Let PSTK := PSTK sp0 VSP RCSP.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma az_fprintf_exit : forall (d : diag_msg) s (LB : list ablock) mo
      x1 t0 t1 t2 x9 (a1v a2v : word) x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 (F : bvmap 5 word) (fc : bv 32) (mm : mem),
    adiag_args bsegs AFMTS d mm a1v a2v (usp0 - 8388608) (usp0 + -128) ->
    ABASE' mm -> AHK s LB [] mm mo -> SO s = stdout_init -> frm0 fc ->
    realizes_cfg acfg bsegs (mkCfg (GST 0x81b10 x1 t0 t1 t2 x9 (Z_to_bv 64 0xa9c68) a1v a2v x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 F fc mm) mo)
              (TDIE (adiag_pieces d) stdout_init (m_fs mo)).
  Proof.
    intros until mm. intros DA BA HKx SO0 FRM.
    pose proof (sp_facts sp0 VSP RCSP) as SF. unfold LO in SF.
    pose proof BA as (ST & MI & IMG & AS). unfold LO in ST.
    pose proof (PSTK LB) as PS.
    aseg DI HKx. zstepA. aleaf. intros mo1 Hag1 HK1 Efs1 Efds1 Hh1. rewrite <- Efs1.
    unfold TDIE.
    eapply (adi_fprintf _ _ _ _ DI d) with (lo := usp0 - 8388608);
      [ apply TEXIT2_nil | exact HK1 | rewrite unsigned_lit by lia; exact DA
      | rewrite unsigned_lit by lia; exact ST | lia
      | rewrite unsigned_lit by lia; unfold AICP_STACK; lia | rewrite unsigned_lit by lia; lia | reflexivity | exact FRM | reflexivity | ].
    intros u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 Ft fc' m2 mo2 s2 ST2 MUc WMc FRM2 HK2 AS2 SO2 Efs2 Efds2 VS2.
    rewrite !unsigned_lit in MUc by lia. rewrite !unsigned_lit in ST2 by lia.
    replace (ret_pc (Z_to_bv 64 0x81b14)) with (Z_to_bv 64 0x81b14) by (symmetry; rpc).
    rewrite <- Efs2, <- SO0, <- SO2. unfold TEXIT2.
    pose proof (PSTK LB) as PS2.
    assert (AX2 : atx_ok_on bsegs m2).
    { destruct AS as (_ & _ & AX0). eapply (atx_ok_agree _ _ _ (agree_on_of_munch _ _ _ MUc WMc)); [| exact AX0].
      intros a Ha. cbn [c_stderr_F ACONSTS]. cbn. lia. }
    aseg DI HK2. zstepA. aleaf. intros mo3 Hag3 HK3 Efs3 Efds3 Hh3. rewrite <- Efs3.
    eapply (az_exit2 sp0 VSP RCSP D DI DIx s2 LB); [unfold LO; exact ST2| exact HK3| exact AX2| exact FRM2].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition BUFC (mm : mem) (A cap : Z) (DATA junk : list byte) : Prop :=
    rw_cells bsegs mm A [CB (length DATA) DATA; CB (Z.to_nat (cap - Z.of_nat (length DATA))) junk]
    /\ (65536 <= cap <= MAX_INPUT /\ exists k, 0 <= k /\ cap = 2 ^ k) /\ Z.of_nat (length DATA) <= cap /\ ablock_range ACONSTS A cap.

  Variable FS0 : Fs.Fs.

  (* [comment removed for export] *)
  Definition abud (cap : Z) : nat := Z.to_nat (71 - 2 * Z.log2 cap).
  Lemma abud_grow : forall k, 0 <= k <= 30 -> abud (2 ^ k) = S (S (abud (2 ^ k * 2))).
  Proof.
    intros k Hk. unfold abud. replace (2 ^ k * 2) with (2 ^ (k + 1)) by (rewrite Z.pow_add_r by lia; lia).
    rewrite !Z.log2_pow2 by lia. lia.
  Qed.
  Lemma abud_ge : forall k, 0 <= k <= 26 -> (19 <= abud (2 ^ k))%nat.
  Proof. intros k Hk. unfold abud. rewrite Z.log2_pow2 by lia. lia. Qed.

  (* [comment removed for export] *)
  Definition RDCORE (fd : Z) (ent : FdEntry) (cap : Z) (DATA : list byte) (s : p_APS D) (mo : Model)
             (mm : mem) (fc : bv 32) (A : Z) : Prop :=
    exists (junk : list byte) (H : list aevent),
      BUFC mm A cap DATA junk
      /\ AHK s [mkABlock A cap] [] mm mo /\ AHEAD (abud cap) [(A, cap)] H s mo
      /\ Forall ev_big_or_free H /\ SO s = stdout_init
      /\ fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some ent /\ m_fs mo = FS0
      /\ FRAME' mm /\ ABASE' mm /\ frm0 fc.

  (* [comment removed for export] *)
  Definition RDINV (fd P1v : Z) (ent : FdEntry) (cap : Z) (DATA : list byte) (s : p_APS D) (mo : Model) (ms : machine_state) : Prop :=
    exists (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x23 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (mm : mem) (A : Z),
      ms = RST 0x8197c x1 t0 t1 t2 (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7 P1v (Z.of_nat (length DATA)) fd cap x23 t3 t4 t5 t6 F fc mm
      /\ RDCORE fd ent cap DATA s mo mm fc A /\ Z.of_nat (length DATA) < cap.

  (* [comment removed for export] *)
  Definition RDBRK (fd P1v : Z) (ent : FdEntry) (cap : Z) (DATA : list byte) (s : p_APS D) (mo : Model) (ms : machine_state) : Prop :=
    exists (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x23 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (mm : mem) (A : Z),
      ms = RST 0x819a4 x1 t0 t1 t2 (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7 P1v (Z.of_nat (length DATA)) fd cap x23 t3 t4 t5 t6 F fc mm
      /\ RDCORE fd ent cap DATA s mo mm fc A.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma az_after_open_err : forall s mo (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (mm : mem) (P1v : Z),
    FRAME' mm -> ABASE' mm -> AHK s [] [] mm mo -> SO s = stdout_init -> frm0 fc -> m_fs mo = FS0 ->
    nth_error (argv_ptrs sp0 argv envp) 1 = Some (Z_to_bv 64 P1v) -> 0 <= P1v < 2^64 ->
    realizes_cfg acfg bsegs (mkCfg (GST 0x818f0 (Z_to_bv 64 0x818f0) t0 t1 t2 (Z_to_bv 64 (argc argv)) (Z_to_bv 64 (2^64 - 1)) a1 a2 a3 a4 a5 a6 a7
                                  (Z_to_bv 64 P1v) (Z_to_bv 64 (envp_addr sp0 argv)) S4 S5 S6 S7 t3 t4 t5 t6 F fc mm) mo)
              (TDIE (pieces_cannot_open (map bv_unsigned arg1)) stdout_init FS0).
  Proof.
    intros until P1v. intros FR BA HKx SO0 FRM FS HP1 P1R.
    pose proof (sp_facts sp0 VSP RCSP) as SF. unfold LO in SF. pose proof (IMGB_len sp0 argv envp uid hw rnd VSP VARGV VENVP) as IL.
    pose proof BA as (ST & MI & IMG & (G & E & _)). unfold LO in ST.
    pose proof VARGV as (_ & _ & ARGLEN & NONUL & _).
    assert (A1NN : ~ In (Z_to_bv 8 0) arg1) by (rewrite EARGV in NONUL; inversion NONUL as [|? ? ? X]; inversion X; assumption).
    assert (A1LEN : Z.of_nat (length arg1) <= 131071) by (rewrite EARGV in ARGLEN; inversion ARGLEN as [|? ? ? X]; inversion X; assumption).
    destruct (proj2 IMG 1%nat arg1 ltac:(lia) ltac:(rewrite EARGV; reflexivity))
      as (p1 & slack1 & HP1' & P1LO & P1HI & STR1 & SLK1 & TOP1). unfold str_base, struct_size, argc, envc in P1LO.
    assert (EP : p1 = P1v).
    { rewrite HP1 in HP1'. assert (EE : bv_unsigned (Z_to_bv 64 P1v) = bv_unsigned (Z_to_bv 64 p1)) by congruence.
      rewrite !unsigned_lit in EE by lia. lia. }
    subst p1.
    pose proof (PSTK []) as PS. pose proof (pol_img []) as PI.
    aseg DI HKx.
    zstepA. if_cases K0; zify_cond K0; try (exfalso; revert K0; clear; intros K0; rewrite ?unsigned_lit in K0 by lia; lia). clear K0.
    do 8 zstepA. aleaf. intros mo1 Hag1 HK1 Efs1 Efds1 Hh1.
    rewrite <- FS, <- Efs1.
    eapply (az_fprintf_exit (DCannotOpen (map bv_unsigned arg1)) s []); [| exact BA | exact HK1 | exact SO0 | exact FRM].
    cbn [adiag_args f_cannot_open AFMTS]. split; [reflexivity|].
    rewrite !unsigned_lit by lia. rewrite zb_map_unsigned. unfold zlength. rewrite !length_map.
    split; [exists slack1; split; [exact STR1 | exact SLK1]|]. split; [apply map_unsigned_pos; exact A1NN|]. split; [lia|]. split; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma az_after_open_ok : forall (KL : TSet) s mo1 (ent : FdEntry) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (mm : mem) (P1v : Z),
    FRAME' mm -> ABASE' mm -> AHK s [] [] mm mo1 -> SO s = stdout_init -> frm0 fc -> m_fs mo1 = FS0 ->
    AHEAD 40%nat [] [] s mo1 -> fd_lookup (m_fds mo1) (Z_to_bv 64 3) = Some ent ->
    KL [] ->
    (forall s' mo ms, RDINV 3 P1v ent 65536 [] s' mo ms -> realizes_cfg acfg bsegs (mkCfg ms mo) KL) ->
    realizes_cfg acfg bsegs (mkCfg (GST 0x818f0 (Z_to_bv 64 0x818f0) t0 t1 t2 (Z_to_bv 64 (argc argv)) (Z_to_bv 64 3) a1 a2 a3 a4 a5 a6 a7
                                  (Z_to_bv 64 P1v) (Z_to_bv 64 (envp_addr sp0 argv)) S4 S5 S6 S7 t3 t4 t5 t6 F fc mm) mo1)
              KL.
  Proof.
    intros until P1v. intros FR BA HK1 SO0 FRM FS HD3 FD3 KL0 HL.
    pose proof (sp_facts sp0 VSP RCSP) as SF. unfold LO in SF. pose proof (IMGB_len sp0 argv envp uid hw rnd VSP VARGV VENVP) as IL.
    pose proof BA as (ST & MI & IMG & AS). unfold LO in ST.
    pose proof (PSTK []) as PS.
    aseg DI HK1.
    zstepA. if_cases K0; zify_cond K0; try (exfalso; rewrite ?unsigned_lit in K0 by lia; lia). clear K0.
    do 4 zstepA. aleaf. intros moa Haga HKa Efsa Efdsa Hha.
    (* [comment removed for export] *)
    eapply (adi_malloc _ _ _ _ DI) with (lo := usp0 - 8388608) (n := 65536); try reflexivity.
    all: rewrite ?(unsigned_lit (usp0 + -128)) by lia.
    - exact KL0.
    - exact HKa.
    - exact ST.
    - lia.
    - unfold AMALLOC_STACK. lia.
    - clear -SF. Z.div_mod_to_equations. lia.
    - lia.
    - apply (adi_uanchorC _ _ _ _ DI); [in_lits| rewrite unsigned_lit by lia; aceil; lia].
    - exact FRM.
    - lia.
    - eapply (adi_hd_cmalloc _ _ _ _ DI); [eapply (adi_hd_magree _ _ _ _ DI); [exact HD3| exact Haga] | lia].
    - apply nbig_small; cbn [length]; lia.
    - (* [comment removed for export] *)
      intros v0 v1 v2 c0 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 F2 fc2 m2 mo2 s2 A ST2 HPR WM2 FRM2 SOE REL FS2 FDS2 CR2 EA0 BR HK2 [junk [JL BLK]] BSH2.
      subst c0.
      rewrite ?(unsigned_lit (usp0 + -128)) in ST2 by lia. rewrite ?(unsigned_lit (usp0 + -128)) in HPR by lia.
      replace (ret_pc (Z_to_bv 64 0x81904)) with (Z_to_bv 64 0x81904) by (symmetry; rpc).
      assert (BA2 : ABASE' m2) by (eapply (ABASE_heap_pres sp0 argv envp uid hw rnd VSP RCSP); [exact BA| exact HPR| lia| reflexivity| reflexivity| reflexivity| exact (adi_mem_inv _ _ _ _ DI _ _ _ _ _ HK2)| unfold LO; exact ST2]).
      assert (FR2 : FRAME' m2).
      { unfold MFRAME. eapply rw_cells_agree; [eapply aheap_pres_agree; exact HPR| exact FR| intros ax Ha; left; cbn in Ha; lia]. }
      clear ST MI IMG AS.
      pose proof BR as (BR1 & BR2 & BR3 & BR4 & BR5). cbn [c_img_hi ACONSTS] in BR5.
      pose proof BA2 as (ST & MI & IMG & AS). unfold LO in ST.
      pose proof (PSTK [mkABlock A 65536]) as PS2.
      aseg DI HK2.
      zstepA. if_cases K1; zify_cond K1; try (exfalso; rewrite ?unsigned_lit in K1 by lia; lia). clear K1.
      (* [comment removed for export] *)
      zstepA. zstepA. zstepA. zstepA. zstepA. if_cases K2; zify_cond K2; try (exfalso; rewrite ?unsigned_lit in K2 by lia; lia). clear K2.
      zstepA. zstepA. aleaf. intros mo3 Hag3 HK3 Efs3 Efds3 Hh3.
      apply (HL s2 mo3). unfold RDINV. cbn [length Z.of_nat].
      do 17 eexists. exists F2, fc2, m2, A. split; [unfold RSTAGE; reflexivity|].
      split; [| lia].
      unfold RDCORE. exists junk, [EvMalloc 65536 (Some A)].
      split. { unfold BUFC. cbn [length Z.of_nat Z.sub]. rewrite Z.sub_0_r.
               split; [apply rw_cells_CB0'; exact BLK|].
               unfold MAX_INPUT. split; [split; [lia| exists 16; split; [lia| reflexivity]]|]. split; [lia| exact BR]. }
      split; [exact HK3|].
      split. { eapply (adi_hd_magree _ _ _ _ DI); [| exact Hag3].
               pose proof (adi_hd_malloc _ _ _ _ DI _ _ 65536 39%nat [] [] A _ _ (adi_hd_magree _ _ _ _ DI _ _ _ _ _ _ HD3 Haga) ltac:(lia) REL) as HD2.
               change (abud 65536) with 39%nat.
               exact HD2. }
      split; [constructor; [cbn; lia| constructor]|]. split; [rewrite SOE; exact SO0|].
      split; [rewrite Efds3, FDS2, Efdsa; exact FD3|].
      split; [rewrite Efs3, FS2, Efsa; exact FS|].
      split; [exact FR2|]. split; [exact BA2| exact FRM2].
  Qed.
  (* [comment removed for export] *)
  Lemma az_read_all_head : forall (KLOOP : FdEntry -> TSet) s mo (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (mm : mem),
    FRAME' mm -> ABASE' mm -> AHK s [] [] mm mo -> SO s = stdout_init -> frm0 fc -> m_fs mo = FS0 -> AHEAD 40%nat [] [] s mo ->
    m_fds mo = dfds_std ->
    (forall ent, KLOOP ent []) ->
    (forall ent s' mo' ms P1v, open_classify arg1 mo = OcMay ent ->
        nth_error (argv_ptrs sp0 argv envp) 1 = Some (Z_to_bv 64 P1v) -> 0 <= P1v < 2^64 ->
        RDINV 3 P1v ent 65536 [] s' mo' ms -> realizes_cfg acfg bsegs (mkCfg ms mo') (KLOOP ent)) ->
    realizes_cfg acfg bsegs
      (mkCfg (MS (mkR (Z_to_bv 64 0x92200) (Z_to_bv 64 (usp0 + -128)) gpv tpv t0 t1 t2
                      (Z_to_bv 64 2) (Z_to_bv 64 (argc argv)) (Z_to_bv 64 (argc argv)) (Z_to_bv 64 (usp0 + 8)) (Z_to_bv 64 (envp_addr sp0 argv)) a3 a4 a5 a6 a7
                      (Z_to_bv 64 0x818b0) (Z_to_bv 64 (envp_addr sp0 argv)) S4 S5 S6 S7 S8 S9 S10 S11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x818dc) fc None mm (seg_rom bsegs)) mo)
      (match open_classify arg1 mo with
       | OcErrno _ => TDIE (pieces_cannot_open (map bv_unsigned arg1)) stdout_init FS0
       | OcMay ent => t_alt2 (TDIE (pieces_cannot_open (map bv_unsigned arg1)) stdout_init FS0) (KLOOP ent)
       end).
  Proof.
    intros until mm. intros FR BA HK0 SO0 FRM FS HD0 MOFD KL0 HL.
    pose proof (sp_facts sp0 VSP RCSP) as SF. unfold LO in SF. pose proof (IMGB_len sp0 argv envp uid hw rnd VSP VARGV VENVP) as IL.
    pose proof BA as (ST & MI & IMG & AS). unfold LO in ST. pose proof FR as FR0. unfold MFRAME in FR.
    pose proof VARGV as (ARGC2 & _ & ARGLEN & NONUL & SLASH).
    assert (EARGC : argc argv = 2) by (unfold argc; rewrite EARGV; reflexivity).
    (* [comment removed for export] *)
    destruct (proj2 IMG 1%nat arg1 ltac:(lia) ltac:(rewrite EARGV; reflexivity))
      as (P1v & slack1 & HP1 & P1LO & P1HI & STR1 & SLK1 & TOP1). unfold str_base, struct_size, argc, envc in P1LO.
    assert (A1NN : ~ In (Z_to_bv 8 0) arg1) by (rewrite EARGV in NONUL; inversion NONUL as [|? ? ? X]; inversion X; assumption).
    assert (A1LEN : Z.of_nat (length arg1) <= 131071) by (rewrite EARGV in ARGLEN; inversion ARGLEN as [|? ? ? X]; inversion X; assumption).
    assert (A1SL : path_has_slash arg1 = false) by (rewrite EARGV in SLASH; cbn [tl] in SLASH; inversion SLASH as [|? ? [X _] _]; exact X).
    assert (QPA : usp0 + -128 <= P1v) by (clear - P1LO SF; unfold struct_size, argc, envc in P1LO; lia).
    assert (TOP1' : P1v + Z.of_nat (length arg1) + 1 <= 2^47) by (clear - TOP1; lia).
    assert (STR1' : bytes_at bsegs mm P1v (arg1 ++ [Z_to_bv 8 0])).
    { change (arg1 ++ Z_to_bv 8 0 :: slack1) with (arg1 ++ ([Z_to_bv 8 0] ++ slack1)) in STR1. rewrite app_assoc in STR1. apply bytes_at_app in STR1. destruct STR1 as [S1 _]. exact S1. }
    pose proof (PSTK []) as PS. pose proof (pol_img []) as PI.
    aseg DI HK0.
    zstepA. if_cases K0; zify_cond K0; [exfalso; rewrite ?unsigned_lit in K0 by lia; lia|]. clear K0.
    pose proof (AIMG_ptr_read sp0 argv envp uid hw rnd mm 1 (Z_to_bv 64 P1v) (Z_to_bv 64 (usp0 + 16)) IMG HP1 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
    zstepA. clear RD. zstepA. zstepA. zstepA.
    aleaf. intros mo1 Hag1 HK1 Efs1 Efds1 Hh1.
    (* [comment removed for export] *)
    assert (OC1 : open_classify arg1 mo1 = open_classify arg1 mo).
    { unfold open_classify. rewrite Efs1. reflexivity. }
    rewrite <- OC1.
    assert (WOKW : Forall (AWOK sp0) [(usp0 - 8388608, usp0 + -128); (0x5e14ac, 0x5e14ac + 4)]).
    { unfold AWOK, LO. constructor; [cbn [fst snd]; lia|]. constructor; [cbn [fst snd]; lia| constructor]. }
    (* [comment removed for export] *)
    assert (KERR : forall (u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 : word) (m1 : mem) (mo2 : Model) (s1 : p_APS D) (e : Z),
      (open_classify arg1 mo1 = OcErrno e \/ (exists ent, open_classify arg1 mo1 = OcMay ent /\ In e openat_errnos)) ->
      stk bsegs m1 (usp0 - 8388608) (bv_unsigned (Z_to_bv 64 (usp0 + -128))) ->
      munch [(usp0 - 8388608, bv_unsigned (Z_to_bv 64 (usp0 + -128))); (c_errno ACONSTS, c_errno ACONSTS + 4)] mm m1 -> wmono bsegs mm m1 ->
      AHK s1 [] [] m1 mo2 -> p_aalloc_same D s s1 -> SO s1 = SO s ->
      m_fs mo2 = m_fs mo1 -> m_fds mo2 = m_fds mo1 -> magree mo1 mo2 ->
      realizes_cfg acfg bsegs (mkCfg (MS (mkR (Z_to_bv 64 0x818f0) (Z_to_bv 64 (usp0 + -128)) gpv tpv u0 u1 u2 (Z_to_bv 64 2) (Z_to_bv 64 (argc argv))
                                      (Z_to_bv 64 (2^64 - 1)) b1 b2 b3 b4 b5 b6 b7 (Z_to_bv 64 P1v) (Z_to_bv 64 (envp_addr sp0 argv)) S4 S5 S6 S7 S8 S9 S10 S11 u3 u4 u5 u6)
                              F (ret_pc (Z_to_bv 64 0x818f0)) fc None m1 (seg_rom bsegs)) mo2)
                (TDIE (pieces_cannot_open (map bv_unsigned arg1)) stdout_init FS0)).
    { intros u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 m1 mo2 s1 e He ST1 MUc WMc HK2 AS2 SO2 Efs2 Efds2 Hag2.
      rewrite ?(unsigned_lit (usp0 + -128)) in MUc by lia. rewrite ?(unsigned_lit (usp0 + -128)) in ST1 by lia. cbn [c_errno ACONSTS] in MUc.
      replace (ret_pc (Z_to_bv 64 0x818f0)) with (Z_to_bv 64 0x818f0) by (symmetry; rpc).
      pose proof (adi_mem_inv _ _ _ _ DI _ _ _ _ _ HK2) as MI1.
      assert (BA1 : ABASE' m1) by (eapply (ABASE_munch sp0 argv envp uid hw rnd VSP RCSP VARGV VENVP); [exact BA| exact WOKW| exact MUc| exact WMc| exact MI1| unfold LO; exact ST1]).
      assert (FR1 : FRAME' m1).
      { unfold MFRAME. eapply rw_cells_agree; [eapply agree_on_of_munch; [exact MUc| exact WMc] | exact FR | intros ax Ha; cbn in Ha |- *; lia]. }
      rewrite <- Efs1, <- Efs2 in FS.
      eapply (az_after_open_err s1 mo2); [exact FR1 | exact BA1 | exact HK2 | rewrite SO2; exact SO0 | exact FRM | exact FS | exact HP1 | lia]. }
    assert (KOK : forall (ent : FdEntry) (u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 : word) (m1 : mem) (mo2 : Model) (s1 : p_APS D),
      open_classify arg1 mo1 = OcMay ent ->
      let fd := alloc_fd (m_fds mo1) in
      stk bsegs m1 (usp0 - 8388608) (bv_unsigned (Z_to_bv 64 (usp0 + -128))) ->
      munch [(usp0 - 8388608, bv_unsigned (Z_to_bv 64 (usp0 + -128))); (c_errno ACONSTS, c_errno ACONSTS + 4)] mm m1 -> wmono bsegs mm m1 ->
      AHK s1 [] [] m1 mo2 -> p_aalloc_same D s s1 -> SO s1 = SO s ->
      m_fs mo2 = m_fs mo1 -> m_fds mo2 = fd_insert (m_fds mo1) fd ent -> magree (with_fds (fd_insert (m_fds mo1) fd ent) mo1) mo2 ->
      realizes_cfg acfg bsegs (mkCfg (MS (mkR (Z_to_bv 64 0x818f0) (Z_to_bv 64 (usp0 + -128)) gpv tpv u0 u1 u2 (Z_to_bv 64 2) (Z_to_bv 64 (argc argv))
                                      fd b1 b2 b3 b4 b5 b6 b7 (Z_to_bv 64 P1v) (Z_to_bv 64 (envp_addr sp0 argv)) S4 S5 S6 S7 S8 S9 S10 S11 u3 u4 u5 u6)
                              F (ret_pc (Z_to_bv 64 0x818f0)) fc None m1 (seg_rom bsegs)) mo2)
                (KLOOP ent)).
    { intros ent u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 m1 mo2 s1 OC. rewrite Efds1, MOFD. cbv zeta. intros ST1 MUc WMc HK2 AS2 SO2 Efs2 Efds2 Hag2.
      rewrite ?(unsigned_lit (usp0 + -128)) in MUc by lia. rewrite ?(unsigned_lit (usp0 + -128)) in ST1 by lia. cbn [c_errno ACONSTS] in MUc.
      replace (ret_pc (Z_to_bv 64 0x818f0)) with (Z_to_bv 64 0x818f0) by (symmetry; rpc).
      pose proof (adi_mem_inv _ _ _ _ DI _ _ _ _ _ HK2) as MI1.
      assert (BA1 : ABASE' m1) by (eapply (ABASE_munch sp0 argv envp uid hw rnd VSP RCSP VARGV VENVP); [exact BA| exact WOKW| exact MUc| exact WMc| exact MI1| unfold LO; exact ST1]).
      assert (FR1 : FRAME' m1).
      { unfold MFRAME. eapply rw_cells_agree; [eapply agree_on_of_munch; [exact MUc| exact WMc] | exact FR | intros ax Ha; cbn in Ha |- *; lia]. }
      change (alloc_fd dfds_std) with (Z_to_bv 64 3) in Efds2, Hag2.
      eapply (az_after_open_ok (KLOOP ent) s1 mo2 ent); [exact FR1 | exact BA1 | exact HK2 | rewrite SO2; exact SO0 | exact FRM | | | | apply KL0 |].
      + rewrite Efs2, Efs1. exact FS.
      + eapply (adi_hd_aps _ _ _ _ DI); [| exact AS2]. eapply (adi_hd_magree _ _ _ _ DI); [| exact Hag2].
        eapply (adi_hd_vmsame _ _ _ _ DI); [| apply vm_same_with_fds].
        eapply (adi_hd_magree _ _ _ _ DI); [exact HD0| exact Hag1].
      + rewrite Efds2. apply fd_lookup_insert_same.
      + intros s' mo' ms RI. exact (HL ent s' mo' ms P1v ltac:(rewrite <- OC1; exact OC) HP1 ltac:(clear - P1LO P1HI SF IL; lia) RI). }
    destruct (open_classify arg1 mo1) as [e|ent] eqn:OC.
    - replace (TDIE (pieces_cannot_open (map bv_unsigned arg1)) stdout_init FS0)
        with (match open_classify arg1 mo1 with OcErrno _ => TDIE (pieces_cannot_open (map bv_unsigned arg1)) stdout_init FS0
                                               | OcMay _ => t_alt2 (TDIE (pieces_cannot_open (map bv_unsigned arg1)) stdout_init FS0) (KLOOP FdDir) end)
        by (rewrite OC; reflexivity).
      eapply (adi_open _ _ _ _ DI) with (lo := usp0 - 8388608) (path := arg1) (KB := KLOOP FdDir);
        [ apply TDIE_nil | apply KL0 | exact HK1 | exact STR1' | exact A1NN | rewrite unsigned_lit by lia; exact QPA | exact TOP1' | exact A1SL
        | rewrite Efds1, MOFD; exact dfds_free | rewrite Efds1, MOFD; exact dfds_range
        | rewrite unsigned_lit by lia; exact ST | lia
        | rewrite unsigned_lit by lia; lia | reflexivity | reflexivity | reflexivity
        | intros u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 m1 mo2 s1 e1 He1 ST1 MU1 WM1 HK2 AS2 SO2 Efs2 Efds2 Hag2; rewrite ?OC in He1; eapply (KERR u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 m1 mo2 s1 e1 He1 ST1 MU1 WM1 HK2 AS2 SO2 Efs2 Efds2 Hag2)
        | intros u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 m1 mo2 s1 ent OC'; exfalso; clear - OC OC'; congruence ].
    - replace (t_alt2 (TDIE (pieces_cannot_open (map bv_unsigned arg1)) stdout_init FS0) (KLOOP ent))
        with (match open_classify arg1 mo1 with OcErrno _ => TDIE (pieces_cannot_open (map bv_unsigned arg1)) stdout_init FS0
                                               | OcMay _ => t_alt2 (TDIE (pieces_cannot_open (map bv_unsigned arg1)) stdout_init FS0) (KLOOP ent) end)
        by (rewrite OC; reflexivity).
      eapply (adi_open _ _ _ _ DI) with (lo := usp0 - 8388608) (path := arg1);
        [ apply TDIE_nil | apply KL0 | exact HK1 | exact STR1' | exact A1NN | rewrite unsigned_lit by lia; exact QPA | exact TOP1' | exact A1SL
        | rewrite Efds1, MOFD; exact dfds_free | rewrite Efds1, MOFD; exact dfds_range
        | rewrite unsigned_lit by lia; exact ST | lia
        | rewrite unsigned_lit by lia; lia | reflexivity | reflexivity | reflexivity
        | intros u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 m1 mo2 s1 e1 He1 ST1 MU1 WM1 HK2 AS2 SO2 Efs2 Efds2 Hag2; rewrite ?OC in He1; eapply (KERR u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 m1 mo2 s1 e1 He1 ST1 MU1 WM1 HK2 AS2 SO2 Efs2 Efds2 Hag2)
        | ].
      intros u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 m1 mo2 s1 ent' OC'.
      assert (Ee : ent' = ent) by (clear - OC OC'; congruence). subst ent'.
      cbv zeta. intros ST1 MU1 WM1 HK2 AS2 SO2 Efs2 Efds2 Hag2. eapply (KOK ent u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 m1 mo2 s1); first [exact ST1 | exact MU1 | exact WM1 | exact HK2 | exact AS2 | exact SO2 | exact Efs2 | exact Efds2 | exact Hag2 | exact OC | reflexivity].
  Qed.
End B.
End RC__1.
