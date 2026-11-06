(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg SpinAlg AgentLib AsanAcct AsanAcctShape.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanInit.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import AsanNodesAux. From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require Import AsanIOSpec AsanNodesIO AsanNodesIOSound.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS. Import ION.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section IOInit.
Context {fx : FPState}.
  (* [comment removed for export] *)
  Variable segs : list Segment.
  Variable A : atable.
  Variable ph : PhdrInfo.
  Hypothesis SEGS_wx : wx_segs_nowrap segs.
  Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment segs (bv_unsigned a) 1 = None.
  Hypothesis HULL_ok : hull_ok A.

  (* [comment removed for export] *)
  Variable sp : word.
  Variable rdraw : EntryDraw.   (* [comment removed for export] *)
  Variable brk0 mbase : word.
  Variable argv envp : list (list byte).
  Variable fs : Fs.Fs.
  Variable stdin : InputStream.
  Variable FS0 : Fs.Fs.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Variable uid : word.
  Variable hw : word.   (* [comment removed for export] *)
  Hypothesis Hfit : entry_stack_fits sp argv envp.   (* [comment removed for export] *)
  Variable LIMIT : Z.   (* [comment removed for export] *)

  (* [comment removed for export] *)
  Variable SINV : env -> (word -> option byte) -> Prop.
  Hypothesis SINV_SINV0 : forall E M, SINV E M -> SINV0 ph sp rdraw brk0 argv envp uid hw E M.
  Hypothesis SINV_frame : forall E M M', (forall a, argH0 ph sp rdraw argv envp uid hw E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
  Hypothesis SINV_agree : forall E E' M, env_agree NX0 E E' -> SINV E M -> SINV E' M.

  (* [comment removed for export] *)
  Variable T : iotab.
  Let argv1 := nth 1 argv [].
  Hypothesis H_class : match io_open T with
    | ONone => True
    | OTooLong => (4096 <= length argv1)%nat
    | ONoEnt => argv1 = [] \/ (argv1 <> dot_path /\ (length argv1 <= 4095)%nat /\ fs_lookup FS0 argv1 = None)
    | ODir => argv1 = dot_path
    | OFile lo hi => exists c, argv1 <> [] /\ argv1 <> dot_path /\ (length argv1 <= 4095)%nat /\ fs_lookup FS0 argv1 = Some c
                     /\ lo <= flen c <= hi
                     /\ (forall E M, SINV E M -> forall j, 65536 * Z.of_nat j < 2 ^ 26 -> eb E (io_blob T + j)%nat = chunk j c)
                     /\ hdr_ok T c
    end.

  Let usp := bv_unsigned sp.
  Let argc := Z.of_nat (length argv).
  Let envc := Z.of_nat (length envp).
  Let argv0 := nth 0 argv [].
  Let STR1 := usp + 8 * argc + 8 * envc + 184 + Z.of_nat (length argv0) + 1.   (* [comment removed for export] *)

  Lemma sp_lo : sp_window_lo <= bv_unsigned sp.
  Proof. destruct Hsp as [H _]. exact H. Qed.
  Lemma sp_hi : bv_unsigned sp <= sp_window_hi.
  Proof. destruct Hsp as (_ & H & _). exact H. Qed.

  (* [comment removed for export] *)
  Lemma IO_vals : forall E M, SINV E M ->
    ev E V_ARGC = Z_to_bv 64 argc /\ (2 <= argc -> uE E e_str1 = STR1).
  Proof.
    intros E M HS. apply SINV_SINV0 in HS. destruct HS as [Hev _].
    pose proof (uE0 ph sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit) as (_ & _ & U1 & _).
    pose proof (u_e_str1 ph sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit) as U7.
    split.
    - change (ev E V_ARGC) with (edenot E (EVar V_ARGC)).
      rewrite (edenot_ev_agree NX0 E (E0 ph sp rdraw brk0 argv envp uid hw) (EVar V_ARGC) eq_refl Hev).
      apply bv_eq. unfold uE in U1. rewrite U1. unfold argc. destruct Hva as [H _]. rewrite u64_lit by lia. reflexivity.
    - intros _. unfold uE. rewrite (edenot_ev_agree NX0 E (E0 ph sp rdraw brk0 argv envp uid hw) e_str1 eq_refl Hev). exact U7.
  Qed.

  Lemma IO_str1 : forall E M (a : word), SINV E M -> 2 <= argc ->
    STR1 <= bv_unsigned a <= STR1 + Z.of_nat (length argv1) -> M a = wrap_mem ph sp argv envp uid hw rdraw a.
  Proof.
    intros E M a HS H2 Ha. apply SINV_SINV0 in HS. destruct HS as [_ HM]. apply HM.
    unfold argH0. apply orb_true_intro. right.
    pose proof (W_range ph sp rdraw argv envp uid hw Hva Hve) as (W1 & W2 & W3).
    pose proof (length_bsb_eq ph sp rdraw argv envp uid hw) as L. pose proof (total_arg_bytes_Z argv) as TA. pose proof (total_arg_bytes_Z envp) as TE.
    unfold stack_image_size in L.
    assert (Hpd : 0 <= (8 - (8 + (Z.of_nat (length argv) + 1) * 8 + (Z.of_nat (length envp) + 1) * 8 + 160
                              + total_arg_bytes argv + total_arg_bytes envp) mod 8) mod 8 < 8) by (apply Z.mod_pos_bound; lia).
    (* [comment removed for export] *)
    assert (F : Z.of_nat (length argv0) + 1 + Z.of_nat (length argv1) + 1 <= total_arg_bytes argv).
    { unfold argv0, argv1. rewrite total_arg_bytes_Z. unfold argc in H2.
      destruct argv as [|a0 [|a1 r]]; cbn in H2; try lia. cbn [nth]. rewrite !total_arg_bytes_cons. lia. }
    apply andb_true_intro. unfold STR1, usp, argc, envc in Ha. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma IO_usp : forall E M, SINV E M -> uE E e_sp0 = usp.
  Proof. intros E M HS. apply SINV_SINV0 in HS. exact (SINV0_u_e_sp0 ph sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit E M HS). Qed.

  Theorem io_xn_sound_init : forall id args,
    node1_stmt segs A NX0 LIMIT SINV (argH0 ph sp rdraw argv envp uid hw) FS0 always (ION.xn segs T id args).
  Proof.
    exact (io_xn_sound segs A NX0 NX0_min_ok_NX0 LIMIT SINV (argH0 ph sp rdraw argv envp uid hw) FS0 SEGS_in_hull HULL_ok
             (argH0_high ph sp rdraw argv envp uid hw Hsp Hva) (argH0_agree ph sp rdraw argv envp uid hw) SINV_frame SINV_agree
             T ph sp rdraw argv envp uid hw Hva Hve sp_lo sp_hi IO_vals IO_str1 IO_usp H_class (le_n NX0)).
  Qed.

  Theorem io_xb_sound_init : forall id args cs csa csb E R FULL model TA TB,
    cs_ok segs A LIMIT SINV (argH0 ph sp rdraw argv envp uid hw) FS0 E cs R FULL model -> ION.xb segs NX0 T id args cs = Some (csa, csb) ->
    (forall E' R' FULL' model', env_agree NX0 E E' /\ env_agree (nxt cs) E E' -> cs_ok segs A LIMIT SINV (argH0 ph sp rdraw argv envp uid hw) FS0 E' csa R' FULL' model' ->
        m_fs model' = m_fs model -> srealizes segs (cfg_of segs R' (pc csa) FULL' model') TA) ->
    (forall E' R' FULL' model', env_agree NX0 E E' /\ env_agree (nxt cs) E E' -> cs_ok segs A LIMIT SINV (argH0 ph sp rdraw argv envp uid hw) FS0 E' csb R' FULL' model' ->
        m_fs model' = m_fs model -> srealizes segs (cfg_of segs R' (pc csb) FULL' model') TB) ->
    srealizes segs (cfg_of segs R (pc cs) FULL model) (t_alt2 TA TB).
  Proof.
    exact (io_xb_sound segs A NX0 NX0_min_ok_NX0 LIMIT SINV (argH0 ph sp rdraw argv envp uid hw) FS0
             (argH0_agree ph sp rdraw argv envp uid hw) SINV_frame SINV_agree
             T ph sp rdraw argv envp uid hw Hva Hve sp_lo sp_hi IO_vals IO_str1 IO_usp H_class).
  Qed.
  Corollary io_ext_stmt_init : ext_stmt segs A NX0 LIMIT (ION.xn segs T) SINV (argH0 ph sp rdraw argv envp uid hw) FS0.
  Proof. exact io_xn_sound_init. Qed.
  (* [comment removed for export] *)
  Theorem io_xn_soundF_init : forall id, io_extF id = true -> forall args,
    node1_stmtF segs A NX0 LIMIT SINV (argH0 ph sp rdraw argv envp uid hw) FS0 always (ION.xn segs T id args).
  Proof.
    exact (io_xn_soundF segs A NX0 NX0_min_ok_NX0 LIMIT SINV (argH0 ph sp rdraw argv envp uid hw) FS0
             (argH0_agree ph sp rdraw argv envp uid hw) SINV_frame SINV_agree T sp argv envp H_class (le_n NX0)).
  Qed.
  Corollary io_ext2_stmt_init : ext2_stmt segs A NX0 LIMIT (ION.xb segs NX0 T) SINV (argH0 ph sp rdraw argv envp uid hw) FS0.
  Proof. exact io_xb_sound_init. Qed.
  (* [comment removed for export] *)
  Theorem io_xn_soundW_init : forall id args cs ws, ION.xn_ws id args cs = Some ws ->
    node1_stmtW_at segs A NX0 LIMIT SINV (argH0 ph sp rdraw argv envp uid hw) FS0 always (ION.xn segs T id args) cs ws.
  Proof.
    exact (io_xn_soundW segs A NX0 LIMIT SINV (argH0 ph sp rdraw argv envp uid hw) FS0 SEGS_in_hull HULL_ok
             (argH0_high ph sp rdraw argv envp uid hw Hsp Hva) SINV_frame T sp argv envp).
  Qed.
End IOInit.
