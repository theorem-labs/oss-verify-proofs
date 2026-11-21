(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: the start-up nodes take AsanInit's LPS 727298f3 launch (kernel build, exec file name, rseq flag), argv[0]'s address follows the new string layout, and the node statements carry the flag of the flagged relation SpinAlg.srealizesM. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg SpinAlg AgentLib AsanAcct AsanAcctShape.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanInit.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AsanNodesAux.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import AsanStartLoops.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AsanNodesStartX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section GenericInit.
  (* [comment removed for export] *)
  Variable segs : list Segment.
  Variable A : atable.
  Variable ph : PhdrInfo.
  Hypothesis SEGS_wx : wx_segs_nowrap segs.
  Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment segs (bv_unsigned a) 1 = None.
  Hypothesis HULL_ok : hull_ok A.

  (* [comment removed for export] *)
  Variables we1 we2 we3 wp0 wp1 wp2 wp3 wp4 : bv 32.
  Hypothesis Xenv : 0 <= x_envscan A /\ x_envscan A + 12 < 2 ^ 64 /\ x_envscan_k A = x_envscan A + 12.
  Hypothesis Fe1 : fetch_word segs (Z_to_bv 64 (x_envscan A)) = Some we1.
  Hypothesis Fe2 : fetch_word segs (Z_to_bv 64 (x_envscan A + 4)) = Some we2.
  Hypothesis Fe3 : fetch_word segs (Z_to_bv 64 (x_envscan A + 8)) = Some we3.
  Hypothesis Ee : is_ecall we1 = false /\ is_ecall we2 = false /\ is_ecall we3 = false.
  Hypothesis De1 : decode_any we1 = Some (Load SZ8 true 10 9 0, 4%Z).
  Hypothesis De2 : decode_any we2 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
  Hypothesis De3 : decode_any we3 = Some (Branch BC_NE 10 0 8184, 4%Z).
  Hypothesis Xpn : 8 <= x_pnscan A /\ x_pnscan A + 12 < 2 ^ 64 /\ x_pnscan_k A = x_pnscan A + 12.
  Hypothesis Fp0 : fetch_word segs (Z_to_bv 64 (x_pnscan A - 8)) = Some wp0.
  Hypothesis Fp1 : fetch_word segs (Z_to_bv 64 (x_pnscan A - 4)) = Some wp1.
  Hypothesis Fp2 : fetch_word segs (Z_to_bv 64 (x_pnscan A)) = Some wp2.
  Hypothesis Fp3 : fetch_word segs (Z_to_bv 64 (x_pnscan A + 4)) = Some wp3.
  Hypothesis Fp4 : fetch_word segs (Z_to_bv 64 (x_pnscan A + 8)) = Some wp4.
  Hypothesis Ep : is_ecall wp0 = false /\ is_ecall wp1 = false /\ is_ecall wp2 = false /\ is_ecall wp3 = false /\ is_ecall wp4 = false.
  Hypothesis Dp0 : decode_any wp0 = Some (Store SZ8 10 11 0, 4%Z).
  Hypothesis Dp1 : decode_any wp1 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
  Hypothesis Dp2 : decode_any wp2 = Some (Load SZ1 false 13 11 4095, 4%Z).
  Hypothesis Dp3 : decode_any wp3 = Some (Branch BC_EQ 13 12 8180, 4%Z).
  Hypothesis Dp4 : decode_any wp4 = Some (Branch BC_NE 13 0 8180, 4%Z).

  (** AsanInit's launch, in its Section order
      ([ph apc sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn]).
      [apc], [mbase], [gid], [groups], [net], [nofile], [sigmask], [urnd], [tmp], [kb] and [execfn] are here
      because the auxv — hence the stack image [SINV0] speaks about — reads AT_ENTRY, AT_SYSINFO_EHDR and
      AT_GID/AT_EGID, and because the string area's position depends on the run's CONFIG_RSEQ flag and the
      exec file name. *)
Context {sfl : bool}.   (* the flag of [SpinAlg.srealizesM] *)
  Variable apc : N.
  Variable sp : word.
  Variable rdraw : EntryDraw.   (* [comment removed for export] *)
  Variable brk0 mbase : word.
  Variable argv envp : list (list byte).
  Variable fs : Fs.Fs.
  Variable stdin : InputStream.
  Variable FS0 : Fs.Fs.
  Variables uid gid hw : word.   (* [comment removed for export] *)
  Variable groups : list word.
  Variable net : NetQueue.
  Variables nofile sigmask : word.
  Variable urnd : InputStream.
  Variable tmp : Fs.Fs.
  Variable kb : KernelBuild.
  Variable execfn : list byte.
  Context {sigpipe_default : bool}.   (* AsanInit's: the launch's SIGPIPE disposition at entry *)

  (** AsanInit's own process input and entry word, at this Section's names *)
  Let INP := @AsanInit.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sigpipe_default.
  Let entryw : word := Z_to_bv 64 (Z.of_N apc).

  (** AsanInit's Section carries all of these, and Rocq generalises each of its lemmas over every hypothesis
      its proof term reads, so they must all be here for [eassumption] to discharge them. *)
  Hypothesis IMG : img_facts segs A ph.
  Hypothesis Hapc : Z.of_N apc = a_entry A.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk segs brk0.
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.   (* [comment removed for export] *)
  Hypothesis Huid : valid_id uid.
  Hypothesis Hzr : AsanCeil.zero_random_draw (ed_random rdraw).
  Hypothesis Hlaunch : valid_launch INP.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) INP.
  Hypothesis Hrs : a_rseq A = rseq_z (kb_rseq kb).

  (* [comment removed for export] *)
  Variable SINV : env -> (word -> option byte) -> Prop.
  Hypothesis SINV_SINV0 : forall E M, SINV E M ->
    @SINV0 ph apc sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sigpipe_default E M.
  Hypothesis SINV_frame : forall E M M', (forall a, argH0 sp rdraw argv envp kb execfn E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
  Hypothesis SINV_agree : forall E E' M, env_agree NX0 E E' -> SINV E M -> SINV E' M.

  #[local] Notation E0L := (E0 sp rdraw brk0 argv envp uid gid kb execfn).

  Let usp := bv_unsigned sp.
  Let argc := Z.of_nat (length argv).
  Let envc := Z.of_nat (length envp).
  Let s0 := nth 0 argv [].
  (** the run's CONFIG_RSEQ flag and the stack VMA's end, spelled as AsanInit and AsanNodesStartX spell them *)
  Let rseq := kb_rseq kb.
  Let top := ed_top rdraw.
  (** argv[0]'s first byte: the top of the AT_RANDOM bytes plus the [arch_align_stack] pad. *)
  Let STR0 := usp + Z.of_nat (cat_string_off rseq sp top argv envp execfn).

  Lemma sp_lo : sp_window_lo <= bv_unsigned sp.
  Proof. destruct Hsp as [H _]. exact H. Qed.
  Lemma sp_hi : bv_unsigned sp <= sp_window_hi.
  Proof. destruct Hsp as (_ & H & _). exact H. Qed.

  (** AsanInit's [STR0] ([usp + CHEAD + W]) and AsanNodesStartX's ([usp + cat_string_off]) are the same
      number: [CatExec.cat_string_off] IS [block_head_size + block_pad_len]. *)
  Lemma str0_split : STR0 = usp + Z.of_nat (block_head_size rseq argv envp)
                                 + Z.of_nat (block_pad_len rseq sp top argv envp execfn).
  Proof. unfold STR0, cat_string_off. rewrite Nat2Z.inj_add. lia. Qed.

  (* [comment removed for export] *)
  Lemma SINV0_vals : forall E M, SINV E M ->
    uE E e_envp = usp + 8 * argc + 16
    /\ ev E V_ENVC = Z_to_bv 64 envc
    /\ uE E (e_str0 A) = STR0
    /\ uE E e_sp0 = usp.   (* [comment removed for export] *)
  Proof.
    intros E M HS. apply SINV_SINV0 in HS. destruct HS as [Hev _].
    assert (U1 : uE E0L e_envp = usp + 8 * argc + 16)
      by (unfold usp, argc; eapply u_e_envp; eassumption).
    assert (U3 : uE E0L (e_str0 A)
                 = usp + Z.of_nat (block_head_size rseq argv envp)
                   + Z.of_nat (block_pad_len rseq sp top argv envp execfn))
      by (unfold usp, rseq, top; eapply u_e_str0; eassumption).
    assert (U2 : uE E0L (EVar V_ENVC) = envc)
      by (unfold envc; eapply uE0_envc; eassumption).
    assert (U4 : uE E0L e_sp0 = usp)
      by (unfold usp; eapply u_e_sp0; eassumption).
    assert (Hev7 : forall n, (n < NX0)%N -> ev E n = ev E0L n) by (intros n Hn; apply Hev; exact Hn).
    unfold uE in *.
    rewrite (edenot_ev_agree NX0 E E0L e_envp eq_refl Hev7).
    (* [nb_lt NX0 (e_str0 A) = true]: every index in the term is below [NX0] = 11
       (V_S1 0, V_ARGC 1, V_ENVC 2, V_W 4, V_S2 6, V_G 9), so the fact is true — but it does not close
       by conversion while [A] is abstract: [e_auxsz A = ELit (AUXSZ (a_rseq A))] with
       [AUXSZ r = 432 + 32*r], and an abstract [a_rseq A] never reduces, whatever is unfolded.
       [Hrs : a_rseq A = rseq_z (kb_rseq kb)] pins it to a concrete flag and
       the boolean case-split closes both branches — the route the model's [nb_lt_e_str0] takes. *)
    assert (NB : nb_lt NX0 (e_str0 A) = true)
      by (unfold e_str0, e_atrandom, e_auxsz; rewrite Hrs; destruct (kb_rseq kb); reflexivity).
    rewrite (edenot_ev_agree NX0 E E0L (e_str0 A) NB Hev7).
    rewrite (edenot_ev_agree NX0 E E0L e_sp0 eq_refl Hev7).
    split; [exact U1|]. split; [|split; [rewrite U3; symmetry; exact str0_split | exact U4]].
    change (ev E V_ENVC) with (edenot E (EVar V_ENVC)).
    rewrite (edenot_ev_agree NX0 E E0L (EVar V_ENVC) eq_refl Hev7).
    apply bv_eq. rewrite U2. unfold envc. destruct Hve as [H _]. rewrite u64_lit by lia. reflexivity.
  Qed.

  Lemma SINV0_envp : forall E M (a : word), SINV E M ->
    usp + 8 * argc + 16 <= bv_unsigned a < usp + 8 * argc + 16 + 8 * envc + 8 ->
    M a = wrap_mem INP mbase ph entryw sp rdraw a.
  Proof.
    intros E M a HS Ha. apply SINV_SINV0 in HS. destruct HS as [_ HM]. apply HM. unfold argH0. apply orb_true_intro. left.
    apply andb_true_intro. unfold usp, argc, envc in Ha. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
  Qed.

  (** the string area runs from argv[0] to the stack VMA's end, and argv[0] with its NUL is inside it
      ([AsanInit.s0_in_strings]), so the bytes the progname scan reads are hidden by [argH0].
      [AsanInit.str0_hi] is QUALIFIED: [AsanNodesStartX] exports a lemma of the same name and is imported
      later, so the bare reference resolves to the wrong one, and the two differ only in their arguments —
      the mistake would surface as a type error far from its cause. *)
  Lemma SINV0_str0 : forall E M (a : word), SINV E M ->
    STR0 <= bv_unsigned a <= STR0 + Z.of_nat (length s0) ->
    M a = wrap_mem INP mbase ph entryw sp rdraw a.
  Proof.
    intros E M a HS Ha. apply SINV_SINV0 in HS. destruct HS as [_ HM]. apply HM. unfold argH0. apply orb_true_intro. right.
    assert (HS0 : Z.of_nat (length (nth 0 argv [])) + 1 <= Z.of_nat (launch_string_bytes argv envp execfn))
      by (eapply AsanInit.s0_in_strings; eassumption).
    assert (HT : bv_unsigned sp + Z.of_nat (block_head_size rseq argv envp)
                 + Z.of_nat (block_pad_len rseq sp top argv envp execfn)
                 + Z.of_nat (launch_string_bytes argv envp execfn) + 8 = bv_unsigned top)
      by (unfold rseq, top; eapply AsanInit.str0_hi; eassumption).
    rewrite str0_split in Ha. unfold s0, usp, rseq, top in Ha, HT, HS0.
    apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
  Qed.

  (** [AsanInit.argH0_high] at this Section's names.  [argH0] reads [kb] and [execfn], so the lemma
      takes them too. *)
  Lemma argH0_high_sp : forall E (a : word),
    argH0 sp rdraw argv envp kb execfn E a = true -> CEIL <= bv_unsigned a.
  Proof. intros E a H. eapply argH0_high; eassumption. Qed.

  (** [x_sound_envscan]/[x_sound_pnscan] state their launch facts over the PROJECTIONS
      ([valid_argv (in_argv inp)]), while this Section states them over its own names ([valid_argv argv]).
      The two are convertible, but under [eapply] the provider's [inp] is still an evar when the goal is
      offered, and [valid_argv (in_argv ?inp)] does not unify with [valid_argv argv] — nothing tells the
      unifier to pick [INP].  Restating each fact over [in_argv INP] pins the evar by unification. *)
  Lemma Hva_inp : valid_argv (in_argv INP).   Proof. exact Hva. Qed.
  Lemma Hve_inp : valid_envp (in_envp INP).   Proof. exact Hve. Qed.
  Lemma Hvl_inp : valid_launch INP.           Proof. exact Hlaunch. Qed.

  Theorem init_x_sound_envscan :
    x_stmt segs A NX0 LIMIT SINV (argH0 sp rdraw argv envp kb execfn) FS0 sfl XEnvScan.
  Proof.
    (* NO named arguments: [x_sound_envscan]'s discharged parameter names are not this Section's.
       Unification pins what the goal determines; [Hlau] fixes [inp]/[mbase]/[brk]/[rdraw] and
       [Fe1]-[Fe3] the code words.

       The alternatives are the ones [init_x_sound_pnscan] also tries: [sp_lo], [argH0_high_sp],
       [SINV0_vals] and the other lemmas they name are facts of this Section that no hypothesis
       carries, so [eassumption] cannot see them.  Both theorems take the same list. *)
    eapply x_sound_envscan;
      try solve [ exact Hva_inp | exact Hve_inp | exact Hvl_inp | eassumption
                | exact sp_lo | exact sp_hi
                | exact argH0_high_sp | exact (argH0_agree sp rdraw argv envp kb execfn)
                | exact SINV0_vals | exact SINV0_envp | exact SINV0_str0
                | unfold APS.nx0_ok, NX0; lia ].
  Qed.

  Theorem init_x_sound_pnscan :
    x_stmt segs A NX0 LIMIT SINV (argH0 sp rdraw argv envp kb execfn) FS0 sfl XPnScan.
  Proof.
    (* The same projection-form facts as [init_x_sound_envscan]. *)
    eapply x_sound_pnscan;
      solve [ exact Hva_inp | exact Hve_inp | exact Hvl_inp | eassumption
            | exact sp_lo | exact sp_hi
            | exact argH0_high_sp | exact (argH0_agree sp rdraw argv envp kb execfn)
            | exact SINV0_vals | exact SINV0_envp | exact SINV0_str0
            | unfold APS.nx0_ok, NX0; lia ].
  Qed.

  Theorem init_x_sound_layout :
    x_stmt segs A NX0 LIMIT SINV (argH0 sp rdraw argv envp kb execfn) FS0 sfl XLayout.
  Proof. apply x_sound_layout. Qed.
End GenericInit.
