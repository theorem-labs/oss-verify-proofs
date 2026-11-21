(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch's validity hypotheses; the process input's new fields; the new initial stack layout; the start-up taken per CONFIG_RSEQ value; the SIGPIPE disposition). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg SpinAlg AgentLib.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AsanAcct AsanAcctShape.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanInit.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AsanNodesAux AsanIOSpec AsanNodesIO AsanNodesIOSound.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS. Import ION.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPW_1. Context {fx : PropExec.FPState}.


Section IOInit.
  (* [comment removed for export] *)
  Variable segs : list Segment.
  Variable A : atable.
  Variable ph : PhdrInfo.
  Hypothesis SEGS_wx : wx_segs_nowrap segs.
  Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment segs (bv_unsigned a) 1 = None.
  Hypothesis HULL_ok : hull_ok A.
  Hypothesis SHADOW_ok : APS.shadow_ok A.   (* [comment removed for export] *)

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

  (* [comment removed for export] *)
  Variable apc : N.
  Variable gid : word.
  Variable groups : list word.
  Variable net : NetQueue.
  Variable ur : InputStream.
  Variable kern : KernelBuild.
  Variable execfn : list byte.
  Variable nofile : word.
  Variable sigmask : word.
  Variables abt sdf : bool.
  Variable SINV : env -> (word -> option byte) -> Prop.
  Hypothesis SINV_SINV0 : forall E M, SINV E M -> SINV0 ph apc sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net ur kern execfn nofile sigmask abt sdf E M.
  Hypothesis SINV_frame : forall E M M', (forall a, argH0 sp rdraw argv envp kern execfn E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
  Hypothesis SINV_agree : forall E E' M, env_agree NX0 E E' -> SINV E M -> SINV E' M.
  Variable LINV : (word -> option byte) -> Prop.   (* [comment removed for export] *)
  Hypothesis Hkernel : in_kernel (inp argv envp fs stdin uid gid hw groups net ur kern execfn nofile sigmask abt sdf) = recorded_kernel (in_kernel (inp argv envp fs stdin uid gid hw groups net ur kern execfn nofile sigmask abt sdf)).
  Hypothesis Hlaunch : valid_launch (inp argv envp fs stdin uid gid hw groups net ur kern execfn nofile sigmask abt sdf).
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) (inp argv envp fs stdin uid gid hw groups net ur kern execfn nofile sigmask abt sdf).
Hypothesis LINV_frame : forall M M' : word -> option byte, (forall a : word, in_lfp A (bv_unsigned a) = true -> M' a = M a) -> LINV M -> LINV M'.
Hypothesis LFP_hull : forall z, in_lfp A z = true -> img_lo A <= z < img_hi A.

  (* [comment removed for export] *)
  Variable T : iotab.
  Let argv1 := nth 1 argv [].
  Hypothesis H_class : match io_open T with
    | ONone => True
    | OTooLong => (4096 <= length argv1)%nat
    | ONoEnt => argv1 = [] \/ (path_has_slash argv1 = false /\ path_is_dirref argv1 = false /\ (length argv1 <= 4095)%nat /\ fs_lookup FS0 argv1 = None)   (* [comment removed for export] *)
    | ODir => argv1 = dot_path
    | OFile lo hi => exists c, argv1 <> [] /\ path_has_slash argv1 = false /\ path_is_dirref argv1 = false /\ (length argv1 <= 4095)%nat /\ fs_lookup FS0 argv1 = Some c
                     /\ lo <= flen c <= hi
                     /\ (forall E M, SINV E M -> forall j, 65536 * Z.of_nat j < 2 ^ 26 -> eb E (io_blob T + j)%nat = chunk j c)
                     /\ hdr_ok T c
    end.

  Let usp := bv_unsigned sp.
  Let argc := Z.of_nat (length argv).
  Let envc := Z.of_nat (length envp).
  Let argv0 := nth 0 argv [].
  (* #38: STR1 WAS usp + 8*argc + 8*envc + 184 + |argv0| + 1.  The 184 is the pre-#38 auxv block
     size.  AsanInit's u_e_str1 (AsanInit.v:474) states `uE E0 e_str1 = STR0 + L0 + 1` over
     AsanInit's own STR0 = usp + CHEAD + W, so these Lets are its (AsanInit.v:118,121,153,155,157)
     term for term and IO_vals' `exact U7` matches by conversion.
     entryw is AsanInit.v:119's, and it is needed here now that wrap_mem takes the #38 list
     (inp mbase ph entry sp draw) rather than (ph sp argv envp uid hw rdraw). *)
  Let rseq : bool := kb_rseq kern.
  Let top : word := ed_top rdraw.
  Let entryw : word := Z_to_bv 64 (Z.of_N apc).
  Let CHEAD := Z.of_nat (block_head_size rseq argv envp).
  Let LSTR := Z.of_nat (launch_string_bytes argv envp execfn).
  Let W := Z.of_nat (block_pad_len rseq sp top argv envp execfn).
  Let STR0 := usp + CHEAD + W.
  Let STR1 := STR0 + Z.of_nat (length argv0) + 1.

  Lemma sp_lo : sp_window_lo <= bv_unsigned sp.
  Proof. destruct Hsp as [H _]. exact H. Qed.
  Lemma sp_hi : bv_unsigned sp <= sp_window_hi.
  Proof. destruct Hsp as (_ & H & _). exact H. Qed.

  (* [comment removed for export] *)
  Lemma IO_vals : forall E M, SINV E M ->
    uE E e_sp0 = usp /\ ev E V_ARGC = Z_to_bv 64 argc /\ (2 <= argc -> uE E e_str1 = STR1).
  Proof.
    intros E M HS. apply SINV_SINV0 in HS. destruct HS as [Hev _].
    pose proof (uE0 ph apc sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net ur kern execfn Hsp Hva Hve Hfit nofile sigmask abt sdf Hlau) as (_ & _ & U1 & _).
    pose proof (u_e_str1 ph apc sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net ur kern execfn Hsp Hva Hve Hfit nofile sigmask abt sdf Hlaunch Hlau) as U7.
    split.
    { unfold uE. rewrite (edenot_ev_agree NX0 E (E0 sp rdraw brk0 argv envp uid gid hw kern execfn) e_sp0 eq_refl Hev).
      exact (u_e_sp0 ph apc sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net ur kern execfn Hsp Hva Hve Hfit nofile sigmask abt sdf Hlau). }
    split.
    - change (ev E V_ARGC) with (edenot E (EVar V_ARGC)).
      rewrite (edenot_ev_agree NX0 E (E0 sp rdraw brk0 argv envp uid gid hw kern execfn) (EVar V_ARGC) eq_refl Hev).
      apply bv_eq. unfold uE in U1. rewrite U1. unfold argc. destruct Hva as [H _]. rewrite u64_lit by lia. reflexivity.
    - intros _. unfold uE. rewrite (edenot_ev_agree NX0 E (E0 sp rdraw brk0 argv envp uid gid hw kern execfn) e_str1 eq_refl Hev). exact U7.
  Qed.

  (* The two facts AsanNodesIOSound's generic section takes as parameters: argv[0]'s address
     with its range, and argv[1]'s address.  Both are AsanInit's (str0_range, cat_argv1_eq),
     stated there so that chead_range / pad_range need no argument list; here they only need
     the Section prefix each captures.  str0_range does not reach ph, apc, Hsp, Hva, Hve or
     Hfit; cat_argv1_eq reaches ph, apc, Hsp, Hva and Hve through usp_lo / usp_fit / len_av /
     len_ev, and neither reaches Hfit. *)
  Lemma IO_sb : usp <= STR0 /\ STR0 <= usp + 8 * argc + 8 * envc + 4622.
  Proof.
    exact (str0_range apc sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net ur kern execfn
             nofile sigmask abt sdf Hlau).
  Qed.

  Lemma IO_str1_val : 2 <= argc ->
    bv_unsigned (cat_argv_ptr (ed_top rdraw) argv envp execfn 1) = STR1.
  Proof.
    exact (cat_argv1_eq ph apc sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net ur
             kern execfn Hsp Hva Hve Hfit nofile sigmask abt sdf Hlau).
  Qed.

  (* argv[0]'s address is at least sp's window floor; the generic section needs it as a
     hypothesis because its lia tier cannot reach that section's usp_lo. *)
  Lemma IO_sb_pos : 0x7fff80000000 <= STR0.
  Proof. pose proof sp_lo. pose proof (proj1 IO_sb). unfold sp_window_lo, usp in *. lia. Qed.

  (* The 2^47 fit the generic section's own `lia` sites cannot derive: dc's lia tier reads the
     CONTEXT, not that section's lemmas.  AsanInit.str1_fit is usp_fit plus s01_in_strings. *)
  Lemma IO_str1_fit : STR1 + Z.of_nat (length argv1) + 1 <= 2 ^ 47.
  Proof.
    exact (str1_fit ph apc sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net ur
             kern execfn Hva Hfit nofile sigmask abt sdf Hlau).
  Qed.

  (* STR1's plain u64 range, stated with no list-length atom so no caller rewrite detaches it.
     STR1 = STR0 + |argv0| + 1, STR0 >= 0 and str1_fit bounds the whole below 2^47 < 2^64. *)
  Lemma IO_str1_u64 : 0 <= STR1 < 2 ^ 64.
  Proof.
    pose proof IO_sb_pos. pose proof IO_str1_fit.
    pose proof (Nat2Z.is_nonneg (length argv0)). pose proof (Nat2Z.is_nonneg (length argv1)).
    unfold STR1 in *. unfold sp_window_lo in *. lia.
  Qed.

  Lemma IO_str1 : forall E M (a : word), SINV E M -> 2 <= argc ->
    STR1 <= bv_unsigned a <= STR1 + Z.of_nat (length argv1) ->
    M a = wrap_mem (inp argv envp fs stdin uid gid hw groups net ur kern execfn nofile sigmask abt sdf)
            mbase ph entryw sp rdraw a.
  Proof.
    intros E M a HS H2 Ha. apply SINV_SINV0 in HS. destruct HS as [_ HM]. apply HM.
    unfold argH0. apply orb_true_intro. right.
    (* W_range is GONE from AsanInit: it baked in 184 and was FALSE at #38.  The replacements are
       that file's length_bsb_sum (:299) and length_bsb_eq (:293); together they give
       usp + CHEAD + W + LSTR + 8 = bv_unsigned top, which is the upper edge argH0 now uses. *)
    pose proof (length_bsb_sum ph apc sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net ur kern execfn nofile sigmask abt sdf Hlau) as LS.
    pose proof (length_bsb_eq  ph apc sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net ur kern execfn nofile sigmask abt sdf Hlau) as LB.
    unfold stack_image_size in LB.
    (* argv[0] and argv[1] with their NULs are the lowest bytes of the string area
       (75d69e00 StackLayout.v:406-409). *)
    assert (F : Z.of_nat (length argv0) + 1 + Z.of_nat (length argv1) + 1 <= LSTR).
    { unfold LSTR, launch_string_bytes, argv0, argv1, argc in *.
      pose proof (Nat2Z.is_nonneg (length (flatten_strings envp))).
      pose proof (Nat2Z.is_nonneg (length execfn)).
      destruct argv as [|a0 [|a1 r]]; cbn in H2 |- *; try lia.
      cbn [flatten_strings flat_map nth]. rewrite !length_app. cbn [length]. lia. }
    assert (HW : 0 <= W) by (unfold W; lia).
    assert (HC : 0 <= CHEAD) by (unfold CHEAD; lia).
    apply andb_true_intro.
    unfold STR1, STR0, CHEAD, LSTR, W, rseq, top, usp, argc, envc in *.
    split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
  Qed.


  Theorem io_xn_sound_init : forall id args,
    node1_stmt segs A NX0 LIMIT SINV (argH0 sp rdraw argv envp kern execfn) LINV FS0 always (ION.xn segs A T id args).
  Proof.
    (* io_xn_sound's premise order, read off `About io_xn_sound` at this pin:
       SEGS A nx0 LIMIT SINV argH LINV FS0 | in_hull hull_ok argH_high argH_agree nx0_ok
       SINV_frame SINV_agree LINV_frame | T ph sp rdraw argv envp INP mbase brk entry
       Hargv Henvp Hlau Hva Hve sp_lo sp_hi | SB sb_lo sb_pos sb_hi str1_u64 str1_fit
       vals str1_val str1 open | nx0_le_NX0 shadow_ok.  argH_top, SEGS_wx and LFP_hull are
       not among them. *)
    exact (io_xn_sound segs A NX0 LIMIT SINV (argH0 sp rdraw argv envp kern execfn) LINV FS0
             SEGS_in_hull HULL_ok
             (argH0_high apc sp rdraw argv envp kern execfn Hsp Hva) (argH0_agree sp rdraw argv envp kern execfn) (Nat.le_refl NX0) SINV_frame SINV_agree LINV_frame
             T ph sp rdraw argv envp
             (inp argv envp fs stdin uid gid hw groups net ur kern execfn nofile sigmask abt sdf)
             mbase brk0 entryw eq_refl eq_refl Hlau
             Hva Hve sp_lo sp_hi STR0 (proj1 IO_sb) IO_sb_pos (proj2 IO_sb) IO_str1_u64 IO_str1_fit
             IO_vals IO_str1_val IO_str1 H_class (le_n NX0) SHADOW_ok).
  Qed.

  Theorem io_xb_sound_init : forall id args cs csa csb E R FULL model TA TB,
    cs_ok segs A LIMIT SINV (argH0 sp rdraw argv envp kern execfn) LINV FS0 E cs R FULL model -> ION.xb segs NX0 T id args cs = Some (csa, csb) ->
    (forall E' R' FULL' model', env_agree NX0 E E' /\ env_agree (nxt cs) E E' -> cs_ok segs A LIMIT SINV (argH0 sp rdraw argv envp kern execfn) LINV FS0 E' csa R' FULL' model' ->
        m_fs model' = m_fs model -> srealizes segs (cfg_of segs R' (pc csa) FULL' model') TA) ->
    (forall E' R' FULL' model', env_agree NX0 E E' /\ env_agree (nxt cs) E E' -> cs_ok segs A LIMIT SINV (argH0 sp rdraw argv envp kern execfn) LINV FS0 E' csb R' FULL' model' ->
        m_fs model' = m_fs model -> srealizes segs (cfg_of segs R' (pc csb) FULL' model') TB) ->
    srealizes segs (cfg_of segs R (pc cs) FULL model) (t_alt2 TA TB).
  Proof.
    (* io_xb_sound takes neither the hull pair nor argH_high nor H_sb_hi, and ends at H_open. *)
    exact (io_xb_sound segs A NX0 LIMIT SINV (argH0 sp rdraw argv envp kern execfn) LINV FS0
             (argH0_agree sp rdraw argv envp kern execfn) (Nat.le_refl NX0) SINV_frame SINV_agree LINV_frame
             T ph sp rdraw argv envp
             (inp argv envp fs stdin uid gid hw groups net ur kern execfn nofile sigmask abt sdf)
             mbase brk0 entryw eq_refl eq_refl Hlau
             Hva Hve sp_lo sp_hi STR0 (proj1 IO_sb) IO_sb_pos IO_str1_u64 IO_str1_fit
             IO_vals IO_str1_val IO_str1 H_class).
  Qed.
  Corollary io_ext_stmt_init : ext_stmt segs A NX0 LIMIT (ION.xn segs A T) SINV (argH0 sp rdraw argv envp kern execfn) LINV FS0.
  Proof. exact io_xn_sound_init. Qed.
  Corollary io_ext2_stmt_init : ext2_stmt segs A NX0 LIMIT (ION.xb segs NX0 T) SINV (argH0 sp rdraw argv envp kern execfn) LINV FS0.
  Proof. exact io_xb_sound_init. Qed.
End IOInit.

End FPW_1.
