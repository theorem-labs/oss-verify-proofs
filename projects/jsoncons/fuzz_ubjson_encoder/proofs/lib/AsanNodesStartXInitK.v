(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: recorded proofs replaced by tactic proofs; the SIGPIPE disposition as a launch variable; the new launch (process input, auxv, group id, exec file name); the CONFIG_RSEQ flag; new lemmas; unused lemmas removed; launch_auxv / vdso_text_base at the entry's stack pointer (LPS b84e73ef); taken in part from projects/jsoncons/fuzz_bigint/proofs/lib/AsanNodesStartXInitK.v, 125 lines within its lines 66-282. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg SpinAlg AgentLib
  AsanAcct AsanAcctShape.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import AxSymExec3K AxSymExec3SoundK AxSymRun3K AsanPlanCoreK AsanPlanK AsanPlanSoundK AsanInitK.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import AsanNodesAuxK AsanStartLoops AsanNodesStartXK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2K. Import AX2SK. Import APK. Import APSK.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section GenericInit.

  Variable segs : list Segment.
  Variable scfg : SpuriousCfg.
  Variable A : atable.
  Variable ph : PhdrInfo.
  Hypothesis SEGS_wx : wx_segs_nowrap segs.
  Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment segs (bv_unsigned a) 1 = None.
  Hypothesis HULL_ok : hull_ok A.

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

  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variable brk0 mbase : word.
  Variable argv envp : list (list byte).
  Variable fs : Fs.Fs.
  Variable stdin : InputStream.
  (* [AsanInitK]'s [Section Init] is parameterised by the full
     [State.mkProcInput_full] field list, so [SINV0]/[argH0] discharge all
     fifteen of [AsanInitK.inp]'s arguments plus [mbase] and [apc].  Same block
     as the already-migrated [HandoffBridgeK.v:619-629]; [mbase] and [stdin]
     this Section already had. *)
  Variable gid : word.
  Variable groups : list word.
  Variable net : NetQueue.
  Variables nofile sigmask : word.
  Variable abrt : bool.
  Variable ur : InputStream.
  Variable kb : KernelBuild.
  Variable execfn : list byte.
  Variable sdf : bool.
  Variable apc : N.
  Variable FS0 : Fs.Fs.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Variable uid : word.
  Variable hw : word.
  Hypothesis Hfit : entry_stack_fits sp argv envp.

  (* The input [AsanInitK.inp] builds out of the field list above, and the ELF
     entry its auxv carries.  [AsanNodesStartXK]'s [Section NodesD] is
     parameterised by the input itself, so this Section is where the two
     spellings meet: [in_argv INP] is [argv] by conversion. *)
  #[local] Notation INP :=
    (AsanInitK.inp argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf).
  #[local] Notation ENTRY := (Z_to_bv 64 (Z.of_N apc)).
  #[local] Notation E00 :=
    (E0 sp rdraw brk0 argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf).
  (* [Run.valid_input]'s exec-name conjunct and [Run.valid_entry]'s launch
     conjunct.  [AsanInitK]'s [u_e_*] and [length_bsb_eq] discharge [Hlau], and
     [AsanNodesStartXK]'s [Section NodesD] takes both, so they are premises of
     this Section rather than facts it can derive. *)
  Hypothesis Hlaunch : valid_launch INP.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) INP.

  Variable SINV : env -> (word -> option byte) -> Prop.
  Hypothesis SINV_SINV0 : forall E M, SINV E M ->
    SINV0 ph sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf apc E M.
  Hypothesis SINV_frame : forall E M M',
    (forall a, argH0 sp rdraw argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf E a = true -> M' a = M a) ->
    SINV E M -> SINV E M'.
  Hypothesis SINV_agree : forall E E' M, env_agree NX0 E E' -> SINV E M -> SINV E' M.

  Let usp := bv_unsigned sp.
  Let argc := Z.of_nat (length argv).
  Let envc := Z.of_nat (length envp).
  Let s0 := nth 0 argv [].
  (* the run's CONFIG_RSEQ flag and the top of the stack VMA, the two values
     [cat_string_off] measures from; both are [Section NodesD]'s own [Let]s. *)
  Let rseq := kb_rseq (in_kernel INP).
  Let top := ed_top rdraw.

  Lemma sp_lo : sp_window_lo <= bv_unsigned sp.
  Proof. destruct Hsp as [H _]. exact H. Qed.
  Lemma sp_hi : bv_unsigned sp <= sp_window_hi.
  Proof. destruct Hsp as (_ & H & _). exact H. Qed.

  (* [in_argv INP] and friends are [argv] and friends by conversion; this names
     the four rewrites the arithmetic below needs so [lia] sees one atom. *)
  Lemma inp_fields :
    in_argv INP = argv /\ in_envp INP = envp /\ in_execfn INP = execfn.
  Proof. repeat split. Qed.

  Lemma SINV0_vals : forall E M, SINV E M ->
    uE E e_envp = usp + 8 * argc + 16
    /\ ev E V_ENVC = Z_to_bv 64 envc
    /\ uE E (e_str0 (rseq_z rseq)) = usp + Z.of_nat (cat_string_off rseq sp top argv envp execfn).
  Proof.
    intros E M HS. apply SINV_SINV0 in HS. destruct HS as [Hev _].
    pose proof (u_e_envp ph sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf apc Hsp Hva Hve Hfit Hlau) as U1.
    pose proof (u_e_str0 ph sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf apc Hsp Hva Hve Hfit Hlau) as U3.
    pose proof (uE0 ph sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf apc Hsp Hva Hve Hfit Hlau) as (_ & _ & _ & U2 & _).
    assert (Hev7 : forall n, (n < NX0)%nat -> ev E n = ev E00 n) by (intros n Hn; apply Hev; exact Hn).
    unfold uE in *. unfold rseq in *.

    (* [rewrite ?] rather than [rewrite]: which of U1/U2/U3 mentions the flag
       is not something to assert -- one build round said U1 does
       not and another said U3 does not either. *)
    (* The flag's literal is read off the goal: an [_] in the rewrite term is
       elaborated before it can unify, and [eq_refl] then meets [e_str0 ?rz]
       (measured at this line). *)
    destruct (kb_rseq (in_kernel INP)) eqn:Hrs; rewrite ?Hrs in U1, U2, U3; cbn [rseq_z];
      rewrite (edenot_ev_agree NX0 E E00 e_envp eq_refl Hev7);
      lazymatch goal with |- context [edenot E (e_str0 ?k)] =>
        rewrite (edenot_ev_agree NX0 E E00 (e_str0 k) eq_refl Hev7) end;
      (split; [exact U1|]); (split; [|exact U3]);
      change (ev E V_ENVC) with (edenot E (EVar V_ENVC));
      rewrite (edenot_ev_agree NX0 E E00 (EVar V_ENVC) eq_refl Hev7);
      apply bv_eq; rewrite U2; unfold envc; destruct Hve as [Hvec _];
      rewrite u64_lit by lia; reflexivity.
  Qed.

  Lemma SINV0_sp0 : forall E M, SINV E M -> uE E e_sp0 = usp.
  Proof.
    intros E M HS. apply SINV_SINV0 in HS. destruct HS as [Hev _].
    assert (Hev7 : forall n, (n < NX0)%nat -> ev E n = ev E00 n) by (intros n Hn; apply Hev; exact Hn).
    unfold uE. rewrite (edenot_ev_agree NX0 E E00 e_sp0 eq_refl Hev7).
    exact (u_e_sp0 ph sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf apc Hsp Hva Hve Hfit Hlau).
  Qed.

  Lemma SINV0_envp : forall E M (a : word), SINV E M ->
    usp + 8 * argc + 16 <= bv_unsigned a < usp + 8 * argc + 16 + 8 * envc + 8 ->
    M a = wrap_mem INP mbase ph ENTRY sp rdraw a.
  Proof.
    intros E M a HS Ha. pose proof (SINV0_sp0 E M HS) as US. apply SINV_SINV0 in HS. destruct HS as [_ HM]. apply HM. unfold argH0.
    pose proof (proj1 Hva) as AV. fold argc in AV.
    apply andb_true_intro. split; [apply Z.leb_le; rewrite US; lia|].
    (* [argH0] has TWO disjuncts at this revision: the pointer vectors, and the
       strings at [STR0 .. utop].  The envp vector is the first. *)
    apply orb_true_intro. left.
    apply andb_true_intro. unfold usp, argc, envc in Ha. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
  Qed.

  (* argv[0]'s bytes and its NUL are inside the string area, so argv[0] ends
     strictly below the top of the stack VMA.  [length_bsb_eq] pins the image's
     length to [utop - usp]; [bsb_len_sum] splits that length into
     [cat_string_off + launch_string_bytes + 8], exactly as the already-migrated
     [AsanNodesStartXK.v:142-167] does. *)
  Lemma s0_le_strings :
    Z.of_nat (length s0) + 1 <= Z.of_nat (launch_string_bytes argv envp execfn).
  Proof.
    assert (Hnz : (0 < length argv)%nat) by (destruct Hva as [[H _] _]; lia).
    unfold launch_string_bytes, s0.
    pose proof (Nat2Z.is_nonneg (length (flatten_strings envp))).
    pose proof (Nat2Z.is_nonneg (length execfn)).
    destruct argv as [|a t] eqn:Ea; [cbn in Hnz; lia|].
    cbn [flatten_strings flat_map nth]. rewrite !length_app. cbn [length]. lia.
  Qed.

  Lemma bsb_len_sum :
    Z.of_nat (length (entry_stack_image INP mbase ph ENTRY sp rdraw))
    = Z.of_nat (cat_string_off rseq sp top argv envp execfn)
      + Z.of_nat (launch_string_bytes argv envp execfn) + 8.
  Proof.
    rewrite entry_stack_image_block, length_build_stack_bytes.
    unfold cat_string_off, rseq, top.
    change (la_rseq (launch_auxv INP sp mbase)) with (kb_rseq (in_kernel INP)).
    destruct inp_fields as (Q1 & Q2 & Q3). rewrite ?Q1, ?Q2, ?Q3. lia.
  Qed.

  Lemma str0_lt_top :
    usp + Z.of_nat (cat_string_off rseq sp top argv envp execfn) + Z.of_nat (length s0)
    < bv_unsigned top.
  Proof.
    pose proof bsb_len_sum as S. pose proof s0_le_strings as F.
    pose proof (length_bsb_eq ph sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf apc Hlau) as L.
    unfold stack_image_size in L. unfold usp, top in *. lia.
  Qed.

  Lemma SINV0_str0 : forall E M (a : word), SINV E M ->
    usp + Z.of_nat (cat_string_off rseq sp top argv envp execfn) <= bv_unsigned a
      <= usp + Z.of_nat (cat_string_off rseq sp top argv envp execfn) + Z.of_nat (length s0) ->
    M a = wrap_mem INP mbase ph ENTRY sp rdraw a.
  Proof.
    intros E M a HS Ha. pose proof (SINV0_sp0 E M HS) as US. apply SINV_SINV0 in HS. destruct HS as [_ HM]. apply HM. unfold argH0.
    pose proof (Nat2Z.is_nonneg (cat_string_off rseq sp top argv envp execfn)) as CN.
    pose proof str0_lt_top as ST.
    apply andb_true_intro. split; [apply Z.leb_le; rewrite US; unfold usp in *; lia|].
    apply orb_true_intro. right.
    apply andb_true_intro. unfold usp, rseq, top in *. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
  Qed.

  (* [Section NodesD] now takes the input, the mmap base and the ELF entry, and
     the launch premises [Hvl]/[Hlau] with them; the obligations are discharged
     by name rather than by position so the script survives a hypothesis this
     file cannot see being absent from one of the two telescopes. *)
  Theorem init_x_sound_envscan :
    x_stmt segs scfg A NX0 LIMIT (rseq_z rseq) SINV
      (argH0 sp rdraw argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf) FS0 XEnvScan.
  Proof.
    eapply (x_sound_envscan segs scfg A NX0 LIMIT (rseq_z rseq) SINV
              (argH0 sp rdraw argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf) FS0
              SEGS_wx SEGS_in_hull HULL_ok SINV_frame
              we1 we2 we3 Xenv Fe1 Fe2 Fe3 Ee De1 De2 De3
              ph INP mbase ENTRY sp brk0 rdraw);
      try exact Hva; try exact Hve; try exact Hlaunch; try exact Hlau;
      try exact sp_lo; try exact sp_hi;
      try exact SINV0_vals; try exact SINV0_sp0; try exact SINV0_envp; try exact SINV0_str0.
  Qed.

  Theorem init_x_sound_pnscan :
    x_stmt segs scfg A NX0 LIMIT (rseq_z rseq) SINV
      (argH0 sp rdraw argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf) FS0 XPnScan.
  Proof.
    eapply (x_sound_pnscan segs scfg A NX0 LIMIT (rseq_z rseq) SINV
              (argH0 sp rdraw argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf) FS0
              SEGS_wx SEGS_in_hull HULL_ok
              (argH0_high sp rdraw argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf apc Hsp Hva)
              e_sp0_init
              (argH0_agree sp rdraw argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf)
              SINV_frame SINV_agree
              wp0 wp1 wp2 wp3 wp4 Xpn Fp0 Fp1 Fp2 Fp3 Fp4 Ep Dp0 Dp1 Dp2 Dp3 Dp4
              ph INP mbase ENTRY sp brk0 rdraw);
      try exact Hva; try exact Hve; try exact Hlaunch; try exact Hlau;
      try exact sp_lo; try exact sp_hi;
      try exact SINV0_vals; try exact SINV0_sp0; try exact SINV0_envp; try exact SINV0_str0.
  Qed.

  Theorem init_x_sound_layout :
    x_stmt segs scfg A NX0 LIMIT (rseq_z rseq) SINV
      (argH0 sp rdraw argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf) FS0 XLayout.
  Proof. apply x_sound_layout. Qed.
End GenericInit.
