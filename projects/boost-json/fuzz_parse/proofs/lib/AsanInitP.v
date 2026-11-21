(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: new file for LPS 727298f3, made from this unit's AsanInit.v: its init lemmas instantiated at the projections of one ProcInput. *)

(** * The packed [AsanInit] interface.

    At 75d69e00 [AsanInit]'s [Section Init] gained the five [ProcInput] fields after
    [in_tmp] ([kern execfn chrdr sigdfl sigterm]) and the image entry [apc], and [SINV0]
    names [wrap_mem inp mbase ph entryw sp rdraw].  [inp] is built from all twenty
    component variables, so the discharged [SINV0] takes TWENTY-SIX arguments:

      ph sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask
      abterm vasz urnd tmp kern execfn chrdr sigdfl sigterm apc

    (measured: a farm round, `About SINV0`).  Every consumer in the
    AsMain*/AS_InstMain*/AsStartup cone holds the run's input as ONE [ProcInput] section
    variable, so spelling that out at each of the ~40 sites would be forty twenty-six
    argument applications.  This file packs it ONCE.

    Nothing here is a new assumption: every lemma is the [AsanInit] one, instantiated at
    the projections of the caller's own [inp].  [AsanInit.v] itself is NOT reopened.

    [argH0] and [E0] are NOT packed -- they lost [ph]/[uid]/[hw] and gained [kern]/
    [execfn], so they are six and nine arguments and short enough to write raw.  They are
    given packed names anyway so that the cone reads uniformly.

    r is never pinned: [kb_rseq] reaches these definitions only through [in_kernel p],
    which is the run's own kernel build and stays free. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import
  PropExec AxSymExec3 AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanInit.
Import ListNotations. Import AX2. Import AP. Import APS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section PK.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.

  (** [ProcInput] has NO definitional eta -- measured, a farm round,
      where `reflexivity` failed and the probe printed "ETA: NOT definitional".  So the
      rebuilt input and the input are equal only propositionally, and every lemma below
      that has to cross between them does it by [destruct]. *)
  Lemma eta_inp : forall p : ProcInput,
    AsanInit.inp (in_argv p) (in_envp p) (in_image_fs p) (in_stdin p) (in_uid p)
                 (in_gid p) (in_hwcap p) (in_groups p) (in_net p) (in_nofile p)
                 (in_sigmask p) (in_abort_terminal p) (in_va_size p) (in_urandom p)
                 (in_tmp p) (in_kernel p) (in_execfn p) (in_channel_reader p)
                 (in_sigpipe_default p) (in_sigpipe_terminal p) = p.
  Proof. intros p. destruct p. reflexivity. Qed.

  Variable ph : PhdrInfo.
  Variable apc : N.
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variable brk0 mbase : word.
  Variable p : ProcInput.

  Definition SINVp : env -> (word -> option byte) -> Prop :=
    AsanInit.SINV0 ph sp rdraw brk0 mbase
      (in_argv p) (in_envp p) (in_image_fs p) (in_stdin p) (in_uid p) (in_gid p)
      (in_hwcap p) (in_groups p) (in_net p) (in_nofile p) (in_sigmask p)
      (in_abort_terminal p) (in_va_size p) (in_urandom p) (in_tmp p) (in_kernel p)
      (in_execfn p) (in_channel_reader p) (in_sigpipe_default p) (in_sigpipe_terminal p)
      apc.

  Definition argHp : env -> word -> bool :=
    AsanInit.argH0 sp rdraw (in_argv p) (in_envp p) (in_kernel p) (in_execfn p).

  Definition argBp : word -> bool :=
    AsanInit.argB0 sp rdraw (in_argv p) (in_envp p) (in_kernel p) (in_execfn p).

  Definition E0p : env :=
    AsanInit.E0 sp rdraw brk0 (in_argv p) (in_envp p) (in_uid p) (in_gid p) (in_hwcap p)
                (in_kernel p) (in_execfn p).

  Definition FULL0p : word -> option byte :=
    AsanInit.FULL0 ph sp rdraw mbase
      (in_argv p) (in_envp p) (in_image_fs p) (in_stdin p) (in_uid p) (in_gid p)
      (in_hwcap p) (in_groups p) (in_net p) (in_nofile p) (in_sigmask p)
      (in_abort_terminal p) (in_va_size p) (in_urandom p) (in_tmp p) (in_kernel p)
      (in_execfn p) (in_channel_reader p) (in_sigpipe_default p) (in_sigpipe_terminal p)
      apc.

  Definition model0p (segs : list Segment) : Model :=
    AsanInit.model0 segs sp rdraw brk0 mbase
      (in_argv p) (in_envp p) (in_image_fs p) (in_stdin p) (in_uid p) (in_gid p)
      (in_hwcap p) (in_groups p) (in_net p) (in_nofile p) (in_sigmask p)
      (in_abort_terminal p) (in_va_size p) (in_urandom p) (in_tmp p) (in_kernel p)
      (in_execfn p) (in_channel_reader p) (in_sigpipe_default p)
      (in_sigpipe_terminal p).

  (** the run's own CONFIG_RSEQ as the plan's [r]; a VARIABLE of the launch, never a
      literal -- [Run.valid_input] leaves [kb_rseq] free and so does this *)
  Definition Rp : Z := rseq_z (kb_rseq (in_kernel p)).

  (** ** The lemmas the cone uses, at the packed arguments. *)

  Lemma argHp_sp0 : forall E a,
    argHp E a = true -> bv_unsigned (edenot E e_sp0_early) <= bv_unsigned a.
  Proof. unfold argHp. apply AsanInit.argH0_sp0. Qed.

  Lemma argHp_agree : forall E E' a,
    env_agree NX0 E E' -> argHp E a = argHp E' a.
  Proof. unfold argHp. apply AsanInit.argH0_agree. Qed.

  (* [AsanInit.CEIL] is a section [Let], so it is inlined on discharge and there is no
     name for it outside AsanInit (a farm round: "The reference
     AsanInit.CEIL was not found").  These two therefore take their types from the
     [AsanInit] lemma rather than restating it, which also guarantees they say exactly
     what it says.  The premise is at the caller's own [p]; [eq_ind_r] over [eta_inp]
     carries it to [AsanInit]'s rebuilt input, which is the only crossing in the file
     besides [init_cs_okp]. *)
  Definition argHp_high
    (Hsp : valid_sp sp) (Hva : valid_argv (in_argv p)) (Hve : valid_envp (in_envp p))
    (Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) p) :=
    AsanInit.argH0_high sp rdraw brk0 mbase
      (in_argv p) (in_envp p) (in_image_fs p) (in_stdin p) (in_uid p) (in_gid p)
      (in_hwcap p) (in_groups p) (in_net p) (in_nofile p) (in_sigmask p)
      (in_abort_terminal p) (in_va_size p) (in_urandom p) (in_tmp p)
      (in_kernel p) (in_execfn p) (in_channel_reader p) (in_sigpipe_default p)
      (in_sigpipe_terminal p) apc Hsp Hva Hve
      (eq_ind_r (fun q => entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) q)
                Hlau (eta_inp p)).

  Definition argHp_SINVp
    (Hsp : valid_sp sp) (Hva : valid_argv (in_argv p)) (Hve : valid_envp (in_envp p))
    (Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) p) :=
    AsanInit.argH0_SINV0 ph sp rdraw brk0 mbase
      (in_argv p) (in_envp p) (in_image_fs p) (in_stdin p) (in_uid p) (in_gid p)
      (in_hwcap p) (in_groups p) (in_net p) (in_nofile p) (in_sigmask p)
      (in_abort_terminal p) (in_va_size p) (in_urandom p) (in_tmp p)
      (in_kernel p) (in_execfn p) (in_channel_reader p) (in_sigpipe_default p)
      (in_sigpipe_terminal p) apc Hsp Hva Hve
      (eq_ind_r (fun q => entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) q)
                Hlau (eta_inp p)).

  Lemma SINVp_frame : forall E M M',
    (forall a, argHp E a = true -> M' a = M a) -> SINVp E M -> SINVp E M'.
  Proof. unfold SINVp, argHp. apply AsanInit.SINV0_frame. Qed.

  Lemma SINVp_agree : forall E E' M,
    env_agree NX0 E E' -> SINVp E M -> SINVp E' M.
  Proof. unfold SINVp. apply AsanInit.SINV0_agree. Qed.

  (** The glue.  Every premise is stated at the caller's OWN [p]; the crossing to
      [AsanInit]'s rebuilt input happens here and nowhere else in the cone. *)
  Lemma init_cs_okp : forall (segs : list Segment) (A : atable),
    img_facts segs A ph -> valid_sp sp -> valid_brk segs brk0 -> valid_mmap_base mbase ->
    valid_argv (in_argv p) -> valid_envp (in_envp p) ->
    valid_id (in_uid p) -> valid_hwcap (in_hwcap p) ->
    valid_launch p -> entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) p -> in_channel_reader p = true ->
    (* LPS 727298f3: the start state now claims AT_ENTRY ([auxv_rest]), the image's entry *)
    Z.of_N apc = a_entry A ->
    cs_ok segs A AsanInit.LIMIT SINVp argHp (in_fs p) E0p
          (init_acs_of Rp A) (AsanInit.R0 sp) FULL0p (model0p segs).
  Proof.
    intros segs A IMG Hsp Hbrk Hmb Hva Hve Huid Hhw Hlaunch Hlau Hrdr Hapc.
    unfold SINVp, argHp, E0p, FULL0p, model0p, Rp.
    rewrite <- (eta_inp p) in Hlaunch, Hlau |- *.
    exact (AsanInit.init_cs_ok segs A ph sp rdraw brk0 mbase
             (in_argv p) (in_envp p) (in_image_fs p) (in_stdin p) (in_uid p) (in_gid p)
             (in_hwcap p) (in_groups p) (in_net p) (in_nofile p) (in_sigmask p)
             (in_abort_terminal p) (in_va_size p) (in_urandom p) (in_tmp p)
             (in_kernel p) (in_execfn p) (in_channel_reader p) (in_sigpipe_default p)
             (in_sigpipe_terminal p) apc IMG Hsp Hbrk Hmb Hva Hve Huid Hhw Hapc Hlaunch Hlau Hrdr).
  Qed.

End PK.

From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import AxSymExec3Sound CatExec.
Import AX2S.

(** * The invariant past start-up, with the run's mmap base bound inside it.

    LPS 727298f3: [SINV0]'s memory conjunct is [wrap_mem inp mbase ...], and the mmap base
    is an execve choice ([Run.valid_launch_base]) that no function of the input gives.  The
    main phase holds no base, so its invariant binds the base existentially under its two
    launch facts ([valid_mmap_base] and [entry_launch_ok_va], [Run.valid_entry]'s fifth
    conjunct); the start-up, which has the run's own base, introduces the witness once
    (AsStartupTop.holes_ok).  The design of boost-beast/http_request's As/AsanInitL.v
    ([SINV0L]), here over this file's packed [SINVp]. *)
Section PKM.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.

  Variable ph : PhdrInfo.
  Variable apc : N.
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variable brk0 : word.
  Variable p : ProcInput.

  (** the run's mmap base, by its two defining facts *)
  Definition launch_base_ok (mb : word) : Prop :=
    valid_mmap_base mb /\ entry_launch_ok_va Sv48 (mkEntry sp brk0 mb rdraw) p.

  Definition SINVm (E : env) (M : word -> option byte) : Prop :=
    exists mb, launch_base_ok mb /\ SINVp ph apc sp rdraw brk0 mb p E M.

  (** the first conjunct reads no mmap base *)
  Lemma SINVm_ev : forall E M, SINVm E M ->
    forall n, (n < NX0)%nat -> ev E n = ev (E0p sp rdraw brk0 p) n.
  Proof. intros E M (mb & _ & H & _). exact H. Qed.

  (** the memory the invariant pins, at its own base *)
  Lemma SINVm_mem : forall E M, SINVm E M ->
    exists mb, launch_base_ok mb
      /\ forall a, argHp sp rdraw p E a = true -> M a = wrap_mem p mb ph (Z_to_bv 64 (Z.of_N apc)) sp rdraw a.
  Proof.
    intros E M (mb & Hb & _ & H). exists mb. split; [exact Hb|].
    intros a Ha. rewrite (H a Ha). rewrite (eta_inp p). reflexivity.
  Qed.

  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv (in_argv p).
  Hypothesis Hve : valid_envp (in_envp p).

  (** the valuation's early stack pointer is the run's *)
  Lemma SINVm_sp0 : forall E M, SINVm E M -> uE E e_sp0_early = bv_unsigned sp.
  Proof using ph apc sp rdraw brk0 p Hsp Hva Hve.   (* a fixed argument list for positional callers *)
    intros E M (mb & (Hmb & Hlau) & H). rewrite <- (eta_inp p) in Hlau.
    eapply AsanInit.SINV0_sp0_E0; eassumption.
  Qed.

  (* the argument strings' address needs the stack fit ([AsanInit]'s [Hfit]) *)
  Hypothesis Hfit : entry_stack_fits sp (in_argv p) (in_envp p).
  (** the envp array pointer, envc, and argv[0]'s address *)
  Lemma SINVm_vals : forall E M, SINVm E M ->
    uE E e_envp = (bv_unsigned sp + 8 * Z.of_nat (length (in_argv p)) + 16)%Z
    /\ ev E V_ENVC = Z_to_bv 64 (Z.of_nat (length (in_envp p)))
    /\ uE E e_str0 = (bv_unsigned sp
                     + Z.of_nat (cat_string_off (kb_rseq (in_kernel p)) sp (ed_top rdraw) (in_argv p) (in_envp p) (in_execfn p)))%Z.
  Proof using ph apc sp rdraw brk0 p Hsp Hva Hve Hfit.   (* a fixed argument list for positional callers *)
    intros E M (mb & (Hmb & Hlau) & H). rewrite <- (eta_inp p) in Hlau.
    (* [SINV0_vals_E0] is generalised over [AsanInit]'s [segs] and [A], which neither its statement
       nor its proof reads; any values do. *)
    eapply AsanInit.SINV0_vals_E0 with (segs := []) (A := {| img_lo := 0; img_hi := 0; n_res := O; shadow_off := 0; a_entry := 0; rw_lo := 0; rw_len := 0; ph_addr_z := 0; ph_ent_z := 0; ph_num_z := 0; x_imemset := 0; x_imemcpy := 0; x_memset := 0; x_memcpy := 0; x_memiszero := 0; x_istrncpy := 0; x_sealed := 0; x_popfree := 0; x_smear := 0; x_sniff := 0; sniff_tab := 0; sniff_cell := 0; x_envscan := 0; x_envscan_k := 0; x_pnscan := 0; x_pnscan_k := 0; stops_more := [] |}); eassumption.
  Qed.
End PKM.
