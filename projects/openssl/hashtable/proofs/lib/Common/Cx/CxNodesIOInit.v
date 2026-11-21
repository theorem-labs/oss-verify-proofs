(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the start state is the launch's (LaunchX): execfn, kernel, stdin, groups, gid, rseq area and the string block). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk StepTac ShapeAlg SpinAlg AgentLib
  AsanAcct AsanAcctShape.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore CxPlan CxPlanSound AsanInit.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import CxNodesFs AsanNodesIO CxNodesIOSound.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import CxRel CxAcctShape CxNodesLibE.
From OSSVerify.Proofs.openssl.hashtable.lib Require FileSim.
Import ListNotations.
Import AX2. Import AX2S. Import CAP. Import CXS. Import ION.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Fixpoint ion_nb_lt (b : nat) (e : expr) : bool :=
  match e with
  | ELit _ => true
  | EVar n => Nat.ltb n b
  | EAlu _ a c | EAluw _ a c | EMd _ a c | EMdw _ a c => ion_nb_lt b a && ion_nb_lt b c
  | EExt _ _ _ a => ion_nb_lt b a
  | EBlob _ _ _ _ => false
  end.

Lemma ion_edenot_ev_agree : forall b E E' e,
  ion_nb_lt b e = true -> (forall n, (n < b)%nat -> ev E n = ev E' n) -> edenot E e = edenot E' e.
Proof.
  intros b E E' e. induction e; cbn [ion_nb_lt edenot]; intros H Hag; try reflexivity;
    try (apply andb_prop in H as [H1 H2]; rewrite (IHe1 H1 Hag), (IHe2 H2 Hag); reflexivity).
  - apply Hag. apply Nat.ltb_lt. exact H.
  - rewrite (IHe H Hag). reflexivity.
  - discriminate.
Qed.

Section IOInit.
  (* [comment removed for export] *)
  Variable segs : list Segment.
  Variable A : atable.
  Variable ph : PhdrInfo.
  Hypothesis SEGS_wx : wx_segs_nowrap segs.
  Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment segs (bv_unsigned a) 1 = None.
  Hypothesis HULL_ok : hull_ok A.

  (* [comment removed for export] *)
  Variable sp brk0 : word.
  Variable argv envp : list (list byte).
  Variable FS0 : Fs.Fs.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Variable uid : word.
  Variable hw : word.           (* [comment removed for export] *)
  Context {L : LaunchX}.
  Variable rdraw : EntryDraw.   (* [comment removed for export] *)
  Hypothesis Hfit : entry_stack_fits sp argv envp.   (* [comment removed for export] *)

  (* [comment removed for export] *)
  Variable SINV : env -> (word -> option byte) -> Prop.
  Hypothesis SINV_SINV0 : forall E M, SINV E M -> SINVL ph sp rdraw brk0 argv envp uid hw L E M.
  Hypothesis SINV_frame : forall E M M', (forall a, argH0 sp rdraw argv envp (lx_kb L) (lx_execfn L) E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
  Hypothesis SINV_agree : forall E E' M, env_agree NX0 E E' -> SINV E M -> SINV E' M.

  (* [comment removed for export] *)
  Variable T : iotab.
  Let argv1 := nth 1 argv [].
  Hypothesis H_class : match io_open T with
    | ONone => True
    | OTooLong => (4096 <= length argv1)%nat
    | ONoEnt => argv1 = [] \/ (path_has_slash argv1 = false /\ path_is_dirref argv1 = false /\ (length argv1 <= 4095)%nat /\ fs_lookup FS0 argv1 = None)
    | ODir => path_is_dirref argv1 = true /\ (length argv1 <= 4095)%nat
    | OFile lo hi => exists c, argv1 <> [] /\ path_has_slash argv1 = false /\ path_is_dirref argv1 = false /\ (length argv1 <= 4095)%nat /\ fs_lookup FS0 argv1 = Some c
                     /\ lo <= flen c <= hi
                     /\ (forall E M, SINV E M -> forall j, 65536 * Z.of_nat j < 2 ^ 26 -> eb E (io_blob T + j)%nat = chunk j c)
                     /\ hdr_ok T c
    end.

  Let usp := bv_unsigned sp.
  Let argc := Z.of_nat (length argv).
  Let envc := Z.of_nat (length envp).
  Let argv0 := nth 0 argv [].
  (* The launch image and argv[1]'s address in the initial stack layout of LPS 727298f3: the
     strings sit at the top of the stack VMA, argv[0] at sp + block_head_size + block_pad_len
     (CatExec.cat_string_off), so argv[1] follows argv[0] and its NUL. *)
  Let INP := inpL argv envp uid hw L.
  Let entryw := Z_to_bv 64 (Z.of_N (lx_apc L)).
  Let W0 := wrap_mem INP (lx_mbase L) ph entryw sp rdraw.
  Let rseq := kb_rseq (lx_kb L).
  Let top := ed_top rdraw.
  Let STR0 := usp + Z.of_nat (block_head_size rseq argv envp) + Z.of_nat (block_pad_len rseq sp top argv envp (lx_execfn L)).
  Let STR1 := STR0 + Z.of_nat (length argv0) + 1.

  Lemma sp_lo : sp_window_lo <= bv_unsigned sp.
  Proof. destruct Hsp as [H _]. exact H. Qed.
  Lemma sp_hi : bv_unsigned sp <= sp_window_hi.
  Proof. destruct Hsp as (_ & H & _). exact H. Qed.

  Lemma io_total_firstn1 : forall (l : list (list byte)), (0 < length l)%nat ->
    total_arg_bytes_nat (firstn 1 l) = (length (nth 0 l []) + 1)%nat.
  Proof. intros [|a r] H; [cbn in H; lia|]. cbn [firstn nth]. rewrite total_arg_bytes_cons. change (total_arg_bytes_nat (firstn 0 r)) with 0%nat. lia. Qed.

  Lemma STR1_lo : usp <= STR1.
  Proof. unfold STR1, STR0. lia. Qed.

  (* The string area ends eight bytes below the stack VMA's top, which is at most 2^47. *)
  Lemma STR1_hi : valid_launch INP -> entry_launch_ok_va Sv48 (mkEntry sp brk0 (lx_mbase L) rdraw) INP ->
    STR1 + Z.of_nat (length argv1) + 1 <= 2 ^ 47.
  Proof.
    intros Hlaunch Hlau.
    pose proof (str0_hi 0%N sp rdraw brk0 (lx_mbase L) argv envp (lx_fs L) (lx_stdin L) uid (lx_gid L) hw (lx_groups L)
                  (lx_net L) (lx_nofile L) (lx_sigmask L) (lx_kb L) (lx_execfn L) (lx_crd L) (lx_sgd L) (lx_sgt L) Hlau) as HT.
    pose proof (s01_in_strings 0%N sp rdraw argv envp (lx_kb L) (lx_execfn L) Hva) as HS.
    pose proof (usp_fit ph (lx_apc L) sp rdraw brk0 (lx_mbase L) argv envp (lx_fs L) (lx_stdin L) uid (lx_gid L) hw (lx_groups L)
                  (lx_net L) (lx_nofile L) (lx_sigmask L) (lx_kb L) (lx_execfn L) (lx_crd L) (lx_sgd L) (lx_sgt L) Hlau) as UF.
    pose proof (length_bsb_eq ph (lx_apc L) sp rdraw brk0 (lx_mbase L) argv envp (lx_fs L) (lx_stdin L) uid (lx_gid L) hw (lx_groups L)
                  (lx_net L) (lx_nofile L) (lx_sigmask L) (lx_kb L) (lx_execfn L) (lx_crd L) (lx_sgd L) (lx_sgt L) Hlau) as LE.
    unfold stack_image_size in LE.
    unfold STR1, STR0, argv0, argv1, usp, rseq, top. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma IO_vals : valid_launch INP -> entry_launch_ok_va Sv48 (mkEntry sp brk0 (lx_mbase L) rdraw) INP ->
    forall E M, SINV E M -> ev E V_ARGC = Z_to_bv 64 argc /\ (2 <= argc -> uE E e_str1 = STR1).
  Proof.
    intros Hlaunch Hlau E M HS. apply SINV_SINV0 in HS. destruct HS as [Hev _].
    pose proof (uE0 ph (lx_apc L) sp rdraw brk0 (lx_mbase L) argv envp (lx_fs L) (lx_stdin L) uid (lx_gid L) hw (lx_groups L)
                  (lx_net L) (lx_nofile L) (lx_sigmask L) (lx_kb L) (lx_execfn L) (lx_crd L) (lx_sgd L) (lx_sgt L)
                  Hsp Hva Hve Hfit Hlau) as (_ & _ & U1 & _).
    pose proof (u_e_str1 ph (lx_apc L) sp rdraw brk0 (lx_mbase L) argv envp (lx_fs L) (lx_stdin L) uid (lx_gid L) hw (lx_groups L)
                  (lx_net L) (lx_nofile L) (lx_sigmask L) (lx_kb L) (lx_execfn L) (lx_crd L) (lx_sgd L) (lx_sgt L)
                  Hsp Hva Hve Hfit Hlaunch Hlau) as U7.
    split.
    - change (ev E V_ARGC) with (edenot E (EVar V_ARGC)).
      rewrite (ion_edenot_ev_agree NX0 E (E0 sp rdraw brk0 argv envp uid (lx_gid L) hw (lx_kb L) (lx_execfn L)) (EVar V_ARGC) eq_refl Hev).
      apply bv_eq. unfold uE, AsanPlanSound.APS.uE in U1. rewrite U1. unfold argc. destruct Hva as [H _]. rewrite u64_lit by lia. reflexivity.
    - intros _. unfold uE. unfold AsanPlanSound.APS.uE in U7.
      rewrite (ion_edenot_ev_agree NX0 E (E0 sp rdraw brk0 argv envp uid (lx_gid L) hw (lx_kb L) (lx_execfn L)) e_str1 eq_refl Hev).
      rewrite U7. unfold STR1, STR0, argv0, usp, rseq, top. reflexivity.
  Qed.

  Lemma IO_str1 : valid_launch INP -> entry_launch_ok_va Sv48 (mkEntry sp brk0 (lx_mbase L) rdraw) INP ->
    forall E M (a : word), SINV E M -> 2 <= argc ->
    STR1 <= bv_unsigned a <= STR1 + Z.of_nat (length argv1) -> M a = W0 a.
  Proof.
    intros Hlaunch Hlau E M a HS H2 Ha. pose proof (STR1_hi Hlaunch Hlau) as HI.
    apply SINV_SINV0 in HS. destruct HS as (_ & HM & _). apply HM.
    pose proof (str0_hi 0%N sp rdraw brk0 (lx_mbase L) argv envp (lx_fs L) (lx_stdin L) uid (lx_gid L) hw (lx_groups L)
                  (lx_net L) (lx_nofile L) (lx_sigmask L) (lx_kb L) (lx_execfn L) (lx_crd L) (lx_sgd L) (lx_sgt L) Hlau) as HT.
    pose proof (s01_in_strings 0%N sp rdraw argv envp (lx_kb L) (lx_execfn L) Hva) as HS1.
    unfold argH0. cbv beta zeta. apply orb_true_intro. right.
    unfold STR1, STR0, argv0, argv1, usp, rseq, top in *.
    apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
  Qed.

  (* argv[1]'s address is cat_argv_ptr's for index 1 (CatExec.cat_argv_ptr_offset, cat_string_base_offset). *)
  Lemma STR1_eq : entry_launch_ok_va Sv48 (mkEntry sp brk0 (lx_mbase L) rdraw) INP -> 2 <= argc ->
    cat_argv_ptr top argv envp (lx_execfn L) 1 = Z_to_bv 64 STR1.
  Proof.
    intros Hlau H2.
    assert (Hk : (1 < length argv)%nat) by (unfold argc in H2; lia).
    rewrite (cat_argv_ptr_offset top argv envp (lx_execfn L) 1 Hk).
    assert (HB : cat_string_base top argv envp (lx_execfn L)
                 = (sp + nat_to_word (cat_string_off rseq sp top argv envp (lx_execfn L)))%bv)
      by exact (cat_string_base_offset Sv48 INP (lx_mbase L) sp brk0 rdraw Hlau).
    rewrite HB, nat_to_word_add_merge, word_add_nat. apply f_equal.
    unfold cat_string_off. rewrite io_total_firstn1 by lia. unfold STR1, STR0, argv0, usp. lia.
  Qed.

  Lemma IO_rd1 : valid_launch INP -> entry_launch_ok_va Sv48 (mkEntry sp brk0 (lx_mbase L) rdraw) INP ->
    forall M, 2 <= argc ->
    (forall a : word, STR1 <= bv_unsigned a <= STR1 + Z.of_nat (length argv1) -> M a = W0 a) ->
    rdn segs M (Z_to_bv 64 STR1) (length argv1 + 1) = Some (argv1 ++ [Z_to_bv 8 0]).
  Proof.
    intros Hlaunch Hlau M H2 HM. pose proof (STR1_hi Hlaunch Hlau) as HI. pose proof STR1_lo as HL.
    assert (HU : 0 <= STR1 < 2 ^ 64) by (unfold usp in HL; pose proof (u64_range sp); lia).
    rewrite (rdn_ext segs (length argv1 + 1) M W0).
    - unfold W0. rewrite rdn_wrap_stack_above; [| rewrite u64_lit by lia; exact HL | rewrite u64_lit by lia; rewrite Nat2Z.inj_add; cbn [Z.of_nat Pos.of_succ_nat]; lia].
      rewrite <- (STR1_eq Hlau H2).
      exact (FileSim.read_argv_cstr_k Sv48 segs INP (lx_mbase L) ph entryw sp brk0 rdraw 1 Hlau ltac:(unfold argc in H2; cbn; lia)).
    - rewrite u64_lit by lia. rewrite Nat2Z.inj_add. cbn [Z.of_nat Pos.of_succ_nat]. lia.
    - intros a Ha. rewrite u64_lit in Ha by lia. rewrite Nat2Z.inj_add in Ha. cbn [Z.of_nat Pos.of_succ_nat] in Ha.
      apply HM. lia.
  Qed.

  #[local] Notation AH := (argH0 sp rdraw argv envp (lx_kb L) (lx_execfn L)).

  Theorem io_xn_sound_init : forall id args,
    node1_stmt segs A NX0 LIMIT SINV AH usp FS0 always (ION.xn segs A T id args).
  Proof.
    intros id args cs cs' E R FULL model TT HC.
    pose proof Hfit as Hfit'.
    pose proof (co_sinv _ _ _ _ _ _ _ _ _ _ _ _ HC) as HL. apply SINV_SINV0, SINVL_launch in HL. destruct HL as [Hlaunch Hlau].
    assert (X : node1_stmt segs A NX0 LIMIT SINV AH usp FS0 always (ION.xn segs A T id args)).
    { eapply (io_xn_sound segs A NX0 LIMIT SINV AH FS0) with (W0 := W0) (STR1 := STR1) (T := T) (sp := sp) (argv := argv) (envp := envp);
        try solve [ reflexivity | exact SEGS_in_hull | exact HULL_ok | exact (argH0_high sp rdraw argv envp (lx_kb L) (lx_execfn L) Hsp Hva)
                  | exact NX0_spw | exact (argH0_agree sp rdraw argv envp (lx_kb L) (lx_execfn L)) | exact SINV_frame | exact SINV_agree
                  | exact Hva | exact Hve | exact sp_lo | exact sp_hi | exact STR1_lo | exact (STR1_hi Hlaunch Hlau)
                  | exact (IO_vals Hlaunch Hlau) | exact (IO_str1 Hlaunch Hlau) | exact (IO_rd1 Hlaunch Hlau) | exact H_class
                  | exact (le_n NX0) | assumption ]. }
    exact (X cs cs' E R FULL model TT HC).
  Qed.

  Theorem io_xb_sound_init : forall id args cs csa csb E R FULL model TA TB,
    cs_ok segs A LIMIT SINV AH usp FS0 E cs R FULL model -> ION.xb segs NX0 T id args cs = Some (csa, csb) ->
    (forall E' R' FULL' model', env_agree NX0 E E' /\ env_agree (nxt cs) E E' -> cs_ok segs A LIMIT SINV AH usp FS0 E' csa R' FULL' model' ->
        m_fs model' = m_fs model -> crz segs (cfg_of segs R' (pc csa) FULL' model') TA) ->
    (forall E' R' FULL' model', env_agree NX0 E E' /\ env_agree (nxt cs) E E' -> cs_ok segs A LIMIT SINV AH usp FS0 E' csb R' FULL' model' ->
        m_fs model' = m_fs model -> crz segs (cfg_of segs R' (pc csb) FULL' model') TB) ->
    crz segs (cfg_of segs R (pc cs) FULL model) (t_alt2 TA TB).
  Proof.
    intros id args cs csa csb E R FULL model TA TB HC Hn HkA HkB.
    pose proof Hfit as Hfit'.
    pose proof (co_sinv _ _ _ _ _ _ _ _ _ _ _ _ HC) as HL. apply SINV_SINV0, SINVL_launch in HL. destruct HL as [Hlaunch Hlau].
    eapply (io_xb_sound segs A NX0 LIMIT SINV AH FS0) with (W0 := W0) (STR1 := STR1) (T := T) (sp := sp) (argv := argv) (envp := envp);
      try solve [ reflexivity | exact HULL_ok | exact NX0_spw | exact (argH0_agree sp rdraw argv envp (lx_kb L) (lx_execfn L))
                | exact SINV_frame | exact SINV_agree
                | exact Hva | exact Hve | exact sp_lo | exact sp_hi | exact STR1_lo | exact (STR1_hi Hlaunch Hlau)
                | exact (IO_vals Hlaunch Hlau) | exact (IO_str1 Hlaunch Hlau) | exact (IO_rd1 Hlaunch Hlau) | exact H_class
                | exact (le_n NX0) | eassumption ].
  Qed.
  Corollary io_ext_stmt_init : ext_stmt segs A NX0 LIMIT (ION.xn segs A T) SINV AH usp FS0.
  Proof. exact io_xn_sound_init. Qed.
  Corollary io_ext2_stmt_init : ext2_stmt segs A NX0 LIMIT (ION.xb segs NX0 T) SINV AH usp FS0.
  Proof. exact io_xb_sound_init. Qed.
End IOInit.
