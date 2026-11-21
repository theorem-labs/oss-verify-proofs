(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: the IO soundness is instantiated with AsanInit's full LPS 727298f3 launch at a flag of the flagged relation SpinAlg.srealizesM, and cat_string_off is bridged to the head-plus-pad layout, following theories/Common/AsanNodesStartXInit.v at LPS 727298f3. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg SpinAlg AgentLib AsanAcct AsanAcctShape.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanInit.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AsanNodesAux AsanIOSpec AsanNodesIO AsanNodesIOSound.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS. Import ION.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* argv[0] and argv[1], each with its NUL, are inside the launch's string
   area.  [AsanInit.s0_in_strings] is the argv[0] half; this is the two-string
   version, which is what argv[1]'s path read needs and which AsanInit does
   not export. *)
Lemma s1_in_launch_strings : forall av ev ex, (2 <= length av)%nat ->
  (length (nth 0 av []) + 1 + (length (nth 1 av []) + 1)
   <= launch_string_bytes av ev ex)%nat.
Proof.
  intros [|a0 [|a1 r]] ev ex H; cbn [length] in H; try lia.
  unfold launch_string_bytes. rewrite !length_flatten_strings.
  cbn [nth]. rewrite !total_arg_bytes_cons. lia.
Qed.

Section IOInit.
Context {sfl : bool}.   (* the flag of [SpinAlg.srealizesM] *)
  (* [comment removed for export] *)
  Variable segs : list Segment.
  Variable A : atable.
  Variable ph : PhdrInfo.
  Hypothesis SEGS_wx : wx_segs_nowrap segs.
  Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment segs (bv_unsigned a) 1 = None.
  Hypothesis HULL_ok : hull_ok A.

  (* The launch, in AsanInit's Section order: the model folds it into one [ProcInput]
     ([c0dd863a:theories/LinuxProcessSem/State.v:7340-7609]), and [SINV0]/[argH0] are
     generalised over the fields that build it. *)
  Variable apc : N.
  Variable sp : word.
  Variable rdraw : EntryDraw.   (* [comment removed for export] *)
  Variable brk0 mbase : word.
  Variable argv envp : list (list byte).
  Variable fs : Fs.Fs.
  Variable stdin : InputStream.
  Variable uid gid : word.
  Variable hw : word.   (* [comment removed for export] *)
  Variable groups : list word.
  Variable net : NetQueue.
  Variables nofile sigmask : word.
  Variable urnd : InputStream.
  Variable tmp : Fs.Fs.
  Variable kb : KernelBuild.
  Variable execfn : list byte.
  Context {sigpipe_default : bool}.   (* AsanInit's: the launch's SIGPIPE disposition at entry *)
  Variable FS0 : Fs.Fs.

  Let INP := @AsanInit.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sigpipe_default.
  Let entryw : word := Z_to_bv 64 (Z.of_N apc).

  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk segs brk0.
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.   (* [comment removed for export] *)
  (* [Run.valid_input]'s last conjunct and [Run.valid_entry]'s fifth. *)
  Hypothesis Hvl : valid_launch INP.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) INP.
  (* the table's layout is the launch's CONFIG_RSEQ flag *)
  Hypothesis Hrs : a_rseq A = rseq_z (kb_rseq kb).

  #[local] Notation SINV0L :=
    (@SINV0 ph apc sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sigpipe_default).
  #[local] Notation AH := (argH0 sp rdraw argv envp kb execfn).
  #[local] Notation E0L := (E0 sp rdraw brk0 argv envp uid gid kb execfn).

  (* [comment removed for export] *)
  Variable SINV : env -> (word -> option byte) -> Prop.
  Hypothesis SINV_SINV0 : forall E M, SINV E M -> SINV0L E M.
  Hypothesis SINV_frame : forall E M M', (forall a, AH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
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
  Let argv0 := nth 0 argv [].
  (* argv[0]'s first byte.  The model puts the string area at the TOP of the stack VMA, below
     the eight-byte slot ([string_base_addr], [c0dd863a:theories/LinuxProcessSem/StackLayout.v:414-419]),
     [cat_string_off] past sp, which is AsanInit's [STR0 = usp + CHEAD + W]. *)
  Let STR0 := usp + Z.of_nat (cat_string_off (kb_rseq kb) sp (ed_top rdraw) argv envp execfn).
  Let STR1 := STR0 + Z.of_nat (length argv0) + 1.   (* [comment removed for export] *)

  Lemma sp_lo : sp_window_lo <= bv_unsigned sp.
  Proof. destruct Hsp as [H _]. exact H. Qed.
  Lemma sp_hi : bv_unsigned sp <= sp_window_hi.
  Proof. destruct Hsp as (_ & H & _). exact H. Qed.

  (* AsanInit's [STR0] ([usp + CHEAD + W]) and [cat_string_off] are the same
     number, written with the addition split the other way. *)
  Lemma str0_split : STR0 = usp + Z.of_nat (block_head_size (kb_rseq kb) argv envp)
                              + Z.of_nat (block_pad_len (kb_rseq kb) sp (ed_top rdraw) argv envp execfn).
  Proof. unfold STR0, cat_string_off. rewrite Nat2Z.inj_add. lia. Qed.

  (* [e_auxsz] is [ELit (AUXSZ (a_rseq A))], so [nb_lt] is stuck on the
     table's r and is not [eq_refl]: it reduces only once [Hrs] has
     replaced r by the run's flag. *)
  Lemma nb_lt_e_str1 : nb_lt NX0 (e_str1 A) = true.
  Proof.
    unfold e_str1, e_str0, e_atrandom, e_auxsz, AUXSZ. rewrite Hrs.
    destruct (kb_rseq kb); vm_compute; reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma IO_vals : forall E M, SINV E M ->
    ev E V_ARGC = Z_to_bv 64 argc /\ (2 <= argc -> uE E (e_str1 A) = STR1) /\ uE E e_sp0 = bv_unsigned sp.
  Proof.
    intros E M HS. apply SINV_SINV0 in HS. destruct HS as [Hev _].
    pose proof (uE0 ph apc sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn
                  Hsp Hva Hve Hfit Hlau) as (_ & _ & U1 & _).
    (* AsanInit generalises each of its lemmas over every Section variable its
       PROOF reads, so give the hypotheses first and let Unshelve place the
       rest. *)
    assert (U7 : uE E0L (e_str1 A)
                 = usp + Z.of_nat (block_head_size (kb_rseq kb) argv envp)
                   + Z.of_nat (block_pad_len (kb_rseq kb) sp (ed_top rdraw) argv envp execfn)
                   + Z.of_nat (length (nth 0 argv [])) + 1).
    { unfold usp. eapply u_e_str1; try eassumption.
      Unshelve. all: try first [exact ph | exact A | exact segs | exact apc | exact Sv48 | eassumption]. }
    assert (U0 : uE E0L e_sp0 = bv_unsigned sp).
    { eapply u_e_sp0; try eassumption.
      Unshelve. all: try first [exact ph | exact A | exact segs | exact apc | exact Sv48 | eassumption]. }
    split.
    - change (ev E V_ARGC) with (edenot E (EVar V_ARGC)).
      rewrite (edenot_ev_agree NX0 E E0L (EVar V_ARGC) eq_refl Hev).
      apply bv_eq. unfold uE in U1. rewrite U1. unfold argc. destruct Hva as [H _]. rewrite u64_lit by lia. reflexivity.
    - split.
      + intros _. unfold uE. rewrite (edenot_ev_agree NX0 E E0L (e_str1 A) nb_lt_e_str1 Hev).
        unfold uE in U7. rewrite U7. unfold STR1, argv0. rewrite str0_split. reflexivity.
      + unfold uE. rewrite (edenot_ev_agree NX0 E E0L e_sp0 eq_refl Hev). exact U0.
  Qed.

  Lemma IO_str1 : forall E M (a : word), SINV E M -> 2 <= argc ->
    STR1 <= bv_unsigned a <= STR1 + Z.of_nat (length argv1) ->
    M a = wrap_mem INP mbase ph entryw sp rdraw a.
  Proof.
    intros E M a HS H2 Ha. apply SINV_SINV0 in HS. destruct HS as [_ HM]. apply HM.
    (* the string area ends 8 bytes below the stack VMA's end *)
    assert (HT : usp + Z.of_nat (block_head_size (kb_rseq kb) argv envp)
                 + Z.of_nat (block_pad_len (kb_rseq kb) sp (ed_top rdraw) argv envp execfn)
                 + Z.of_nat (launch_string_bytes argv envp execfn) + 8
                 = bv_unsigned (ed_top rdraw)).
    { unfold usp. eapply AsanInit.str0_hi; try eassumption.
      Unshelve. all: try first [exact ph | exact A | exact segs | exact apc | exact Sv48 | eassumption]. }
    assert (Hk : (2 <= length argv)%nat) by (unfold argc in H2; lia).
    pose proof (s1_in_launch_strings argv envp execfn Hk) as HS1.
    unfold STR1, argv0, argv1 in Ha. rewrite str0_split in Ha. unfold usp in Ha.
    unfold argH0. apply orb_true_intro. right. apply andb_true_intro.
    split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
  Qed.

  Lemma AH_high : forall E (a : word), AH E a = true -> CEIL <= bv_unsigned a.
  Proof.
    intros E a H. eapply argH0_high; try eassumption.
    Unshelve. all: try first [exact ph | exact A | exact segs | exact apc | exact Sv48 | eassumption].
  Qed.

  Lemma AH_agree : forall E E' (a : word), env_agree NX0 E E' -> AH E a = AH E' a.
  Proof. intros E E' a H. eapply argH0_agree; eassumption. Qed.

  Theorem io_xn_sound_init : forall id args,
    node1_stmt segs A NX0 LIMIT SINV AH FS0 sfl always (ION.xn segs A T id args).
  Proof.
    apply (io_xn_sound segs A NX0 LIMIT SINV AH FS0 SEGS_in_hull HULL_ok
             AH_high AH_agree SINV_frame SINV_agree ltac:(unfold APS.nx0_ok, NX0; lia)
             T ph INP mbase entryw sp brk0 rdraw);
      solve [ assumption | exact Hva | exact Hve | exact Hvl | exact Hlau
            | exact sp_lo | exact sp_hi | exact IO_vals | exact IO_str1
            | exact H_class | exact (N.le_refl NX0) ].
  Qed.

  Theorem io_xb_sound_init : forall id args cs csa csb E R FULL model TA TB,
    cs_ok segs A LIMIT SINV AH FS0 E cs R FULL model -> ION.xb segs A NX0 T id args cs = Some (csa, csb) ->
    (forall E' R' FULL' model', env_agree NX0 E E' /\ env_agree (nxt cs) E E' -> cs_ok segs A LIMIT SINV AH FS0 E' csa R' FULL' model' ->
        m_fs model' = m_fs model -> srealizesM segs sfl (cfg_of segs R' (pc csa) FULL' model') TA) ->
    (forall E' R' FULL' model', env_agree NX0 E E' /\ env_agree (nxt cs) E E' -> cs_ok segs A LIMIT SINV AH FS0 E' csb R' FULL' model' ->
        m_fs model' = m_fs model -> srealizesM segs sfl (cfg_of segs R' (pc csb) FULL' model') TB) ->
    srealizesM segs sfl (cfg_of segs R (pc cs) FULL model) (t_alt2 TA TB).
  Proof.
    apply (io_xb_sound segs A NX0 LIMIT SINV AH FS0
             AH_agree SINV_frame SINV_agree ltac:(unfold APS.nx0_ok, NX0; lia)
             T ph INP mbase entryw sp brk0 rdraw);
      solve [ assumption | exact Hva | exact Hve | exact Hvl | exact Hlau
            | exact sp_lo | exact sp_hi | exact IO_vals | exact IO_str1 | exact H_class ].
  Qed.

  Corollary io_ext_stmt_init : ext_stmt segs A NX0 LIMIT (ION.xn segs A T) SINV AH FS0 sfl.
  Proof. exact io_xn_sound_init. Qed.
  Corollary io_ext2_stmt_init : ext2_stmt segs A NX0 LIMIT (ION.xb segs A NX0 T) SINV AH FS0 sfl.
  Proof. exact io_xb_sound_init. Qed.
End IOInit.
