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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import B_iface BDrv_ctx.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import BX_atexit B_iface5x.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac rpc := apply ret_pc_even; [lia| reflexivity].

(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac aceil := first [pose proof alloc_ceiling_range as CEILB | idtac].
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma u64ro_read : forall m A ws (i : Z) w a,
  bytes_at bsegs m A (u64s ws) -> nth_error ws (Z.to_nat i) = Some w -> (0 <= i)%Z -> a = wa (A + 8 * i) ->
  ov_read_bytes bsegs m a 8 = Some (le8 w).
Proof. aceil.
  intros m A ws i w a Hb Hn Hi ->.
  destruct (u64s_split _ _ _ Hn) as (pre & post & E & Hlen & Eu & Hlu).
  replace (8 * i)%Z with (Z.of_nat (8 * Z.to_nat i))%Z by lia.
  rewrite (bytes_at_ov_read bsegs m A (u64s ws) (8 * Z.to_nat i) 8 Hb).
  2:{ rewrite Eu, !app_length, length_le8, Hlu. lia. }
  rewrite Eu, skipn_app, skipn_all2, Hlu, Nat.sub_diag by lia. rewrite skipn_O, app_nil_l.
  rewrite firstn_app, firstn_all2 by (rewrite length_le8; lia).
  rewrite length_le8, Nat.sub_diag, firstn_O, app_nil_r. reflexivity.
Qed.

(* [comment removed for export] *)
End RC__1.
Ltac aseg DI HKx :=
  lazymatch goal with
  | |- realizes_cfg ?cf ?segs (mkCfg ?ms ?mo) ?T =>
      lazymatch type of HKx with
      | ?AHK ?s ?LB ?LF ?m mo =>
          eapply (adrv_seg _ DI s LB LF m mo ms
                    (fun ms' => forall mo', magree mo mo' -> AHK s LB LF m mo' -> m_fs mo' = m_fs mo -> m_fds mo' = m_fds mo ->
                                            m_halted mo' = None -> realizes_cfg cf segs (mkCfg ms' mo') T) T HKx);
          [ | let X := fresh in intros ? ? X; intros; eapply X; eassumption ]
      end
  end.
Ltac aleaf := apply evtA_done; cbv beta.

Section RC__2.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section A.
  Variables (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (rnd : EntryDraw).
  Hypothesis VSP : valid_sp sp0.
  Hypothesis RCSP : rc_sp = bv_unsigned sp0.          (* [comment removed for export] *)
  Hypothesis EFIT : entry_stack_fits sp0 argv envp.   (* [comment removed for export] *)
  Hypothesis VARGV : valid_argv argv.
  Hypothesis VENVP : valid_envp envp.
  Notation usp0 := (bv_unsigned sp0).
  Notation gpv := (Z_to_bv 64 0x10800).
  Notation tpv := (Z_to_bv 64 0x5e1550).
  Notation IMGB := (build_stack_bytes aph sp0 argv envp uid hw rnd).
  Notation LO' := (LO sp0).
  Notation ABASE' := (ABASE sp0 argv envp uid hw rnd).

  (* [comment removed for export] *)
  Variable D : adrv_params.
  Hypothesis DI : a_drv_iface bsegs ACONSTS AFMTS D.
  Hypothesis DIx : a_drv_iface5x bsegs ACONSTS D.      (* [comment removed for export] *)
  Notation AHK := (p_AHK D).
  Notation SO := (p_SO D).

  (* [comment removed for export] *)
  Lemma PSTK : forall LB a n, usp0 - 8388608 <= a -> a + Z.of_nat n <= usp0 + 2^32 -> adrv_acc ACONSTS LB (Z_to_bv 64 a, n).
  Proof.
    intros LB a n H1 H2. pose proof (sp_facts sp0 VSP RCSP) as SF. unfold LO in SF.
    apply pol_stack; lia.
  Qed.
  Definition PIMG := pol_img.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma az_exit_call : forall (code : Z) s (LB : list ablock) LF mo
      (x1 t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem),
    stk bsegs m LO' (usp0 + -48) -> AHK s LB LF m mo -> atx_ok_on bsegs m -> frm0 fc -> 0 <= code < 2^32 ->
    realizes_cfg acfg bsegs (mkCfg (MS (mkR x1 (Z_to_bv 64 (usp0 + -48)) gpv tpv t0 t1 t2 s0 s1 (Z_to_bv 64 code) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (Z_to_bv 64 0x92200) fc None m (seg_rom bsegs)) mo)
              (ShapeAlg.t_emit (Wz 1 (fst (exit_flush_pure (SO s)))) (t_exit (bv_and (Z_to_bv 64 code) (Z_to_bv 64 255)) (m_fs mo))).
  Proof.
    intros until m. intros ST HKx AX FRM HC. pose proof (sp_facts sp0 VSP RCSP) as SF. unfold LO in *.
    pose proof (PSTK LB) as PS.
    aseg DI HKx. zstepA. aleaf. intros mo' Hag HKx' Efs Efds Hh'. rewrite <- Efs.
    eapply (adx_exit _ _ _ DIx) with (lo := usp0 - 8388608);
      [ exact HKx' | exact AX | exact HC | exact (adi_so _ _ _ _ DI _ _ _ _ _ HKx') | rewrite unsigned_lit by lia; exact ST
      | lia | rewrite unsigned_lit by lia; unfold AEXIT_STACK; lia | rewrite unsigned_lit by lia; lia
      | reflexivity | exact FRM | reflexivity ].
  Qed.

  (* [comment removed for export] *)
  Lemma az_main_return : forall (code : Z) s (LB : list ablock) LF mo
      (x1 t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (pad : list byte) (s7v s6v s5v s4v : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
    MFRAME sp0 argv m pad s7v s6v s5v s4v ->
    stk bsegs m LO' (usp0 + -128) -> AHK s LB LF m mo -> atx_ok_on bsegs m -> mem_inv bsegs m -> frm0 fc -> 0 <= code < 2^32 ->
    realizes_cfg acfg bsegs (mkCfg (MS (mkR x1 (Z_to_bv 64 (usp0 + -128)) gpv tpv t0 t1 t2 (Z_to_bv 64 code) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (Z_to_bv 64 0x81aac) fc None m (seg_rom bsegs)) mo)
              (ShapeAlg.t_emit (Wz 1 (fst (exit_flush_pure (SO s)))) (t_exit (bv_and (Z_to_bv 64 code) (Z_to_bv 64 255)) (m_fs mo))).
  Proof.
    intros until m. intros FR ST HKx AX MI FRM HC. pose proof (sp_facts sp0 VSP RCSP) as SF. unfold LO in *. unfold MFRAME in FR.
    pose proof (PSTK LB) as PS.
    aseg DI HKx.
    do 11 zstepA. release_frame FR ST (usp0 + -48). zstepA.
    replace (ret_pc (Z_to_bv 64 0x92200)) with (Z_to_bv 64 0x92200) by (symmetry; rpc).
    aleaf. intros mo' Hag HKx' Efs Efds Hh'. rewrite <- Efs.
    eapply az_exit_call; [exact ST| exact HKx'| exact AX| exact FRM| exact HC].
  Qed.

  (* [comment removed for export] *)
  Lemma az_exit2 : forall s (LB : list ablock) LF mo
      (x1 t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem),
    stk bsegs m LO' (usp0 + -128) -> AHK s LB LF m mo -> atx_ok_on bsegs m -> frm0 fc ->
    realizes_cfg acfg bsegs (mkCfg (MS (mkR x1 (Z_to_bv 64 (usp0 + -128)) gpv tpv t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (Z_to_bv 64 0x81b38) fc None m (seg_rom bsegs)) mo)
              (ShapeAlg.t_emit (Wz 1 (fst (exit_flush_pure (SO s)))) (t_exit (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) (m_fs mo))).
  Proof.
    intros until m. intros ST HKx AX FRM. pose proof (sp_facts sp0 VSP RCSP) as SF. unfold LO in *.
    pose proof (PSTK LB) as PS.
    aseg DI HKx. zstepA. zstepA. aleaf. intros mo' Hag HKx' Efs Efds Hh'. rewrite <- Efs.
    eapply (adx_exit _ _ _ DIx) with (lo := usp0 - 8388608);
      [ exact HKx' | exact AX | lia | exact (adi_so _ _ _ _ DI _ _ _ _ _ HKx') | rewrite unsigned_lit by lia; exact ST
      | lia | rewrite unsigned_lit by lia; unfold AEXIT_STACK; lia | rewrite unsigned_lit by lia; lia
      | reflexivity | exact FRM | reflexivity ].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma main_prologue : forall LB (Q : machine_state -> Prop) (ra s0 s1 a0 a1 a2 s2 s3 t0 t1 t2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem),
    stk bsegs m LO' (usp0 + -48) -> mem_inv bsegs m ->
    (forall m' (pad : list byte), rw_cells bsegs m' (usp0 + -128) [CB 8 pad; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
        stk bsegs m' LO' (usp0 + -128) ->
        munch [(usp0 - 128, usp0 - 48)] m m' -> wmono bsegs m m' -> mem_inv bsegs m' ->
        evtA bsegs (adrv_acc ACONSTS LB) Q
             (MS (mkR ra (Z_to_bv 64 (usp0 + -128)) gpv tpv t0 t1 t2 (Z_to_bv 64 2) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x818dc) fc None m' (seg_rom bsegs))) ->
    evtA bsegs (adrv_acc ACONSTS LB) Q
         (MS (mkR ra (Z_to_bv 64 (usp0 + -48)) gpv tpv t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x818b0) fc None m (seg_rom bsegs)).
  Proof.
    intros until m. intros ST MI K. pose proof (sp_facts sp0 VSP RCSP) as SF. unfold LO in *.
    pose proof (PSTK LB) as PS.
    pose proof (munch_refl [(usp0 - 128, usp0 - 48)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    zstepA. carve_frame 80%nat ST.
    do 10 zstepA.
    lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) => eapply (K mx) end; [exact FR| exact ST| exact MU| exact WM| assumption].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition AENTRY (mo : Model) (s : p_APS D) (ms : machine_state) : Prop :=
    exists (t0 t1 t2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
      ms = MS (mkR (Z_to_bv 64 0x92200) (Z_to_bv 64 (usp0 + -48)) gpv tpv t0 t1 t2 (Z_to_bv 64 (usp0 + 8)) (Z_to_bv 64 (argc argv))
                   (Z_to_bv 64 (argc argv)) (Z_to_bv 64 (usp0 + 8)) (Z_to_bv 64 (envp_addr sp0 argv)) a3 a4 a5 a6 a7
                   (Z_to_bv 64 0x818b0) (Z_to_bv 64 (envp_addr sp0 argv)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x818b0) fc None m (seg_rom bsegs)
      /\ stk bsegs m LO' (usp0 + -48) /\ mem_inv bsegs m /\ AIMG sp0 argv envp uid hw rnd m /\ ASTAT m /\ frm0 fc
      /\ AHK s [] [] m mo /\ SO s = stdout_init /\ p_AHEAD D 40%nat [] [] s mo.

  (* [comment removed for export] *)
  Lemma main_to_test : forall mo s (ms : machine_state) (T : TSet),
    AENTRY mo s ms ->
    (forall (t0 t1 t2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (mm : mem) (mo' : Model)
            (pad : list byte),
        MFRAME sp0 argv mm pad s7 s6 s5 s4 -> ABASE' mm -> AHK s [] [] mm mo' -> frm0 fc -> SO s = stdout_init ->
        p_AHEAD D 40%nat [] [] s mo' -> m_fs mo' = m_fs mo -> m_fds mo' = m_fds mo ->
        realizes_cfg acfg bsegs (mkCfg
             (MS (mkR (Z_to_bv 64 0x92200) (Z_to_bv 64 (usp0 + -128)) gpv tpv t0 t1 t2
                      (Z_to_bv 64 2) (Z_to_bv 64 (argc argv)) (Z_to_bv 64 (argc argv)) (Z_to_bv 64 (usp0 + 8)) (Z_to_bv 64 (envp_addr sp0 argv)) a3 a4 a5 a6 a7
                      (Z_to_bv 64 0x818b0) (Z_to_bv 64 (envp_addr sp0 argv)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x818dc) fc None mm (seg_rom bsegs)) mo') T) ->
    realizes_cfg acfg bsegs (mkCfg ms mo) T.
  Proof.
    intros mo s ms T AE K.
    destruct AE as (t0 & t1 & t2 & a3 & a4 & a5 & a6 & a7 & s4 & s5 & s6 & s7 & s8 & s9 & s10 & s11 & t3 & t4 & t5 & t6 & F & fc & m
                    & -> & ST & MI & IMG & AS & FRM & HK0 & SO0 & HD0).
    pose proof (sp_facts sp0 VSP RCSP) as SF. pose proof (IMGB_len sp0 argv envp uid hw rnd VSP VARGV VENVP) as IL. unfold LO in *.
    aseg DI HK0.
    eapply (main_prologue []); [unfold LO; exact ST| exact MI|].
    intros m1 pad FR ST1 MU WM MI1. unfold LO in ST1.
    pose proof (agree_on_of_munch _ _ _ MU WM) as AG.
    assert (OUT : forall a, (a < usp0 - 128 \/ usp0 - 48 <= a) -> (fun a0 : Z => outside [(usp0 - 128, usp0 - 48)] a0) a) by (intros a Ha; cbn; lia).
    aleaf. intros mo' Hag HK1 Efs Efds Hh'.
    apply (K t0 t1 t2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 mo' pad).
    - exact FR.
    - split; [unfold LO; exact ST1|]. split; [exact MI1|]. split.
      + eapply AIMG_agree; [exact AG| intros a Ha; apply OUT; lia| exact IMG].
      + eapply ASTAT_agree; [exact AG| | exact AS]. intros a Ha. apply OUT. unfold astat_addr in Ha. lia.
    - eapply (AHK_after D DI); [exact HK1| exact MU| exact WM|]. constructor; [| constructor]. apply wok_stack. lia.
    - exact FRM.
    - exact SO0.
    - eapply (adi_hd_magree _ _ _ _ DI); [exact HD0| exact Hag].
    - exact Efs.
    - exact Efds.
  Qed.

  (* [comment removed for export] *)
  Definition TUSAGE (fs : Fs.Fs) : TSet :=
    ShapeAlg.t_emit (Wz 2 (concat (pieces_usage (map bv_unsigned (hd [] argv)))))
       (ShapeAlg.t_emit (Wz 1 (fst (exit_flush_pure stdout_init))) (t_exit (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) fs)).

  (* [comment removed for export] *)
  Lemma main_usage : forall mo s ms, AENTRY mo s ms -> Z.of_nat (length argv) <> 2 ->
    realizes_cfg acfg bsegs (mkCfg ms mo) (TUSAGE (m_fs mo)).
  Proof.
    intros mo s ms AE HARGC.
    eapply main_to_test; [exact AE|]. intros t0 t1 t2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc mm mo0 pad FR BA HK0 FRM SO0 HD0 Efs0 Efds0.
    rewrite <- Efs0. clear Efs0 Efds0 HD0.
    aseg DI HK0.
    pose proof (sp_facts sp0 VSP RCSP) as SF. pose proof (IMGB_len sp0 argv envp uid hw rnd VSP VARGV VENVP) as IL.
    pose proof (IMGB_ts sp0 argv envp uid hw rnd EFIT) as ITS. unfold LO in *.
    pose proof BA as (ST & MI & IMG & (G & E & AX0)). unfold LO in ST.
    pose proof (PSTK []) as PS. pose proof (pol_img []) as PI.
    destruct VARGV as (ARGC & _ & ARGLEN & NONUL & _).
    destruct argv as [|arg0 argv'] eqn:EARGV; [cbn in ARGC; lia|]. rewrite <- EARGV in *.
    (* [comment removed for export] *)
    destruct (proj2 IMG 0%nat arg0 ltac:(lia) ltac:(rewrite EARGV; reflexivity))
      as (p0 & slack0 & HP0 & P0LO & P0HI & STR0 & SLK0 & TOP0). unfold str_base, struct_size, argc, envc in P0LO.
    assert (A0NN : ~ In (Z_to_bv 8 0) arg0) by (rewrite EARGV in NONUL; inversion NONUL; assumption).
    assert (A0LEN : Z.of_nat (length arg0) <= 131071) by (rewrite EARGV in ARGLEN; inversion ARGLEN; assumption).
    unfold argc. zstepA. if_cases K0; zify_cond K0; try (exfalso; lia). clear K0.
    (* [comment removed for export] *)
    zstepA. zstepA. zstepA.
    pose proof (AIMG_ptr_read sp0 argv envp uid hw rnd mm 0 (Z_to_bv 64 p0) (Z_to_bv 64 (usp0 + 8)) IMG HP0 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
    zstepA. clear RD. zstepA. zstepA. zstepA.
    (* [comment removed for export] *)
    aleaf. intros mo1 Hag1 HK1 Efs1 Efds1 Hh1. unfold TUSAGE. rewrite <- Efs1.
    rewrite EARGV. cbn [hd].
    eapply (adi_fprintf _ _ _ _ DI (DUsage (map bv_unsigned arg0))) with (lo := usp0 - 8388608);
      [ apply ShapeAlg.t_emit_has_nil | exact HK1
      | | rewrite unsigned_lit by lia; exact ST | lia
      | rewrite unsigned_lit by lia; unfold AICP_STACK; lia | rewrite unsigned_lit by lia; lia | reflexivity | exact FRM | reflexivity | ].
    { cbn [adiag_args f_usage AFMTS]. split; [reflexivity|].
      rewrite !unsigned_lit by lia. rewrite zb_map_unsigned. unfold zlength. rewrite !length_map.
      split; [exists slack0; split; [exact STR0 | exact SLK0]|].
      split; [apply map_unsigned_pos; exact A0NN|]. split; [lia|]. split; lia. }
    intros u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 Ft fc' m2 mo2 s2 ST2 MUc WMc FRM2 HK2 AS2 SO2 Efs2 Efds2 VS2.
    rewrite !unsigned_lit in MUc by lia. rewrite !unsigned_lit in ST2 by lia.
    replace (ret_pc (Z_to_bv 64 0x81a64)) with (Z_to_bv 64 0x81a64) by (symmetry; rpc).
    pose proof (agree_on_of_munch _ _ _ MUc WMc) as AG.
    assert (OUT : forall a, (usp0 - 128 <= a /\ ~ (0xa9c68 <= a < 0xa9c68 + 232)) -> (fun a0 : Z => outside [(usp0 - 8388608, usp0 + -128); (0xa9c68, 0xa9c68 + 232)] a0) a).
    { intros a Ha. cbn. lia. }
    unfold MFRAME in FR. cbn [c_stderr_F ACONSTS] in MUc, AG.
    apply (rw_cells_agree _ _ _ _ _ AG) in FR; [| intros a Ha; apply OUT; cbn in Ha; lia].
    pose proof (adi_mem_inv _ _ _ _ DI _ _ _ _ _ HK2) as MI2.
    assert (AX2 : atx_ok_on bsegs m2) by (eapply (atx_ok_agree _ _ _ AG); [intros a Ha; cbn; lia| exact AX0]).
    rewrite <- Efs2, <- SO0, <- SO2.
    aseg DI HK2. zstepA. aleaf. intros mo3 Hag3 HK3 Efs3 Efds3 Hh3. rewrite <- Efs3.
    eapply (az_main_return 2 s2 []); [exact FR| unfold LO; exact ST2| exact HK3| exact AX2| exact MI2| exact FRM2| lia].
  Qed.
End A.
End RC__2.
