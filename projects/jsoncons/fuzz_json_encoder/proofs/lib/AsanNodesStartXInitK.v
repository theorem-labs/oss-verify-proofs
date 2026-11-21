(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the SIGPIPE disposition left free, the rseq-dependent auxv, the launch input's kernel build; launch_auxv / vdso_text_base at the entry's stack pointer (LPS b84e73ef)): changed SINV0_envp, SINV0_sp0, SINV0_str0 and 8 more; added ARGH, EI, Hapc and 28 more; removed s0_fits; taken in part from projects/jsoncons/fuzz_json_cursor/proofs/lib/AsanNodesStartXInitK.v, 92 lines within its lines 25-219. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg SpinAlg AgentLib
  AsanAcct AsanAcctShape.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import AxSymExec3K AxSymExec3SoundK AxSymRun3K AsanPlanCoreK AsanPlanK AsanPlanSoundK AsanInitK.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import AsanNodesAuxK AsanStartLoops AsanNodesStartXK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2K. Import AX2SK. Import APK. Import APSK.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [edenot_ev_agree] asks that [e_str0 r] read only the initial variables, which is a
   computation once [r] is a literal; at the run's flag it is one per layout.
   Model donor [75d69e00:theories/Common/AsanNodesStartXInit.v:27-28]. *)
Lemma nb_lt_e_str0 : forall b, nb_lt NX0 (e_str0 (rseq_z b)) = true.
Proof. intros [|]; reflexivity. Qed.

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

  (* the run: AsanInitK's Section variables, in its order *)
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variable brk0 mbase : word.
  Variable argv envp : list (list byte).
  Variable fs : Fs.Fs.
  Variable stdin : InputStream.
  Variables uid gid hw : word.
  Variable groups : list word.
  Variable net : NetQueue.
  Variables nofile sigmask : word.
  Variable abrt : bool.
  Variable urnd : InputStream.
  Variable tmp0 : Fs.Fs.
  Variable kb : KernelBuild.
  Variable execfn : list byte.
  Variable sdf : bool.
  Variable apc : N.
  Variable FS0 : Fs.Fs.

  Let INP := AsanInitK.inp argv envp fs stdin uid gid hw groups net nofile sigmask abrt urnd tmp0 kb execfn sdf.
  Let entryw := Z_to_bv 64 (Z.of_N apc).

  (* AsanInitK's Section carries these, and Rocq generalises each of its lemmas over
     every hypothesis its proof term reads, so they are here for [eassumption]. *)
  Hypothesis IMG : img_facts segs A ph.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk segs brk0.
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Hypothesis Huid : valid_id uid.
  Hypothesis Hhw : valid_hwcap hw.
  Hypothesis Hapc : Z.of_N apc = a_entry A.
  Hypothesis Hlaunch : valid_launch INP.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) INP.

  #[local] Notation ARGH := (argH0 sp rdraw argv envp fs stdin uid gid hw groups net nofile sigmask abrt urnd tmp0 kb execfn sdf).
  (* [E0] reads [mbase] since vals0 slot 12 ([V_EHDR]) is the vDSO text base *)
  #[local] Notation EI := (E0 sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask abrt urnd tmp0 kb execfn sdf).

  Variable SINV : env -> (word -> option byte) -> Prop.
  Hypothesis SINV_SINV0 : forall E M, SINV E M ->
    SINV0 ph sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask abrt urnd tmp0 kb execfn sdf apc E M.
  Hypothesis SINV_frame : forall E M M', (forall a, ARGH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
  Hypothesis SINV_agree : forall E E' M, env_agree NX0 E E' -> SINV E M -> SINV E' M.

  Let usp := bv_unsigned sp.
  Let argc := Z.of_nat (length argv).
  Let envc := Z.of_nat (length envp).
  Let s0 := nth 0 argv [].
  (* the run's CONFIG_RSEQ flag, as AsanInitK spells it, and as the plan's 0 or 1 *)
  Let rseq := kb_rseq (in_kernel INP).
  Let RZ := rseq_z rseq.
  Let top := ed_top rdraw.
  (* argv[0]: the top of the AT_RANDOM bytes plus the [arch_align_stack] pad.
     It WAS [usp + 8*argc + 8*envc + 184]. *)
  Let STR0 := usp + Z.of_nat (cat_string_off rseq sp top argv envp execfn).

  Lemma sp_lo : sp_window_lo <= bv_unsigned sp.
  Proof. destruct Hsp as [H _]. exact H. Qed.
  Lemma sp_hi : bv_unsigned sp <= sp_window_hi.
  Proof. destruct Hsp as (_ & H & _). exact H. Qed.

  Lemma Hev0 : forall E M, SINV E M -> forall n, (n < NX0)%nat -> ev E n = ev EI n.
  Proof. intros E M HS. apply SINV_SINV0 in HS. destruct HS as [Hev _]. exact Hev. Qed.

  Lemma SINV0_sp0 : forall E M, SINV E M -> uE E e_sp0 = usp.
  Proof.
    intros E M HS. pose proof (Hev0 E M HS) as Hev7.
    unfold uE. rewrite (edenot_ev_agree NX0 E EI e_sp0 eq_refl Hev7).
    change (bv_unsigned (edenot EI e_sp0) = usp). eapply u_e_sp0; eassumption.
  Qed.

  Lemma SINV0_vals : forall E M, SINV E M ->
    uE E e_envp = usp + 8 * argc + 16
    /\ ev E V_ENVC = Z_to_bv 64 envc
    /\ uE E (e_str0 RZ) = STR0.
  Proof.
    intros E M HS. pose proof (Hev0 E M HS) as Hev7.
    assert (U1 : uE EI e_envp = usp + 8 * argc + 16) by (eapply u_e_envp; eassumption).
    assert (U3 : uE EI (e_str0 RZ) = STR0) by (eapply u_e_str0; eassumption).
    assert (U2 : uE EI (EVar V_ENVC) = envc) by (eapply uE0; eassumption).
    unfold uE in *.
    rewrite (edenot_ev_agree NX0 E EI e_envp eq_refl Hev7).
    rewrite (edenot_ev_agree NX0 E EI (e_str0 RZ) (nb_lt_e_str0 rseq) Hev7).
    split; [exact U1|]. split; [|exact U3].
    change (ev E V_ENVC) with (edenot E (EVar V_ENVC)).
    rewrite (edenot_ev_agree NX0 E EI (EVar V_ENVC) eq_refl Hev7).
    apply bv_eq. rewrite U2. unfold envc. destruct Hve as [H _]. rewrite u64_lit by lia. reflexivity.
  Qed.

  Lemma SINV0_envp : forall E M (a : word), SINV E M ->
    usp + 8 * argc + 16 <= bv_unsigned a < usp + 8 * argc + 16 + 8 * envc + 8 ->
    M a = wrap_mem INP mbase ph entryw sp rdraw a.
  Proof.
    intros E M a HS Ha. pose proof (SINV0_sp0 E M HS) as US. apply SINV_SINV0 in HS. destruct HS as [_ HM]. apply HM.
    pose proof (proj1 Hva) as AV. fold argc in AV.
    (* [argH0] is navigated only through AsanInitK's per-region lemmas.  They are
       Section lemmas, generalised over every Section variable their proofs read,
       some absent from their conclusions ([apc : N] among them), so the region
       facts are proved first and the lemma is applied by [eapply ...; eassumption];
       [exact] closes AsanInitK's [uE]/[EAUX] up to conversion. *)
    assert (G1 : uE E e_sp0 <= bv_unsigned a) by (rewrite US; unfold usp, argc, envc in *; lia).
    assert (G2 : usp + 24 <= bv_unsigned a < usp + 8 * argc + 8 * envc + 24) by (unfold usp, argc, envc in *; lia).
    eapply argH0_argblock; try exact G1; try exact G2; eassumption.
  Qed.

  (* the string area runs from argv[0] to the stack VMA's end, and argv[0] with its
     NUL is inside it ([AsanInitK.s0_in_strings], [AsanInitK.str0_hi]) *)
  Lemma SINV0_str0 : forall E M (a : word), SINV E M ->
    STR0 <= bv_unsigned a <= STR0 + Z.of_nat (length s0) ->
    M a = wrap_mem INP mbase ph entryw sp rdraw a.
  Proof.
    intros E M a HS Ha. pose proof (SINV0_sp0 E M HS) as US. apply SINV_SINV0 in HS. destruct HS as [_ HM]. apply HM.
    assert (HS0 : Z.of_nat (length (nth 0 argv [])) + 1 <= Z.of_nat (launch_string_bytes argv envp execfn))
      by (eapply s0_in_strings; eassumption).
    assert (HT : STR0 + Z.of_nat (launch_string_bytes argv envp execfn) + 8 = bv_unsigned top)
      by (eapply AsanInitK.str0_hi; eassumption).
    pose proof (Nat2Z.is_nonneg (cat_string_off rseq sp top argv envp execfn)).
    (* [argH0_strings]'s range carries AsanInitK's Lets inlined ([kb_rseq (in_kernel
       (inp ..))], [ed_top rdraw]); this Section's [rseq]/[INP] are local
       definitions, which [lia] would read as different atoms, so they are unfolded. *)
    assert (G1 : uE E e_sp0 <= bv_unsigned a) by (rewrite US; unfold STR0, usp in *; lia).
    assert (G2 : STR0 <= bv_unsigned a < bv_unsigned top) by (unfold s0 in Ha; unfold STR0, usp, top, rseq, INP in *; lia).
    eapply argH0_strings; try exact G1; try exact G2; eassumption.
  Qed.

  Lemma argH0_high_sp : forall E (a : word), ARGH E a = true -> CEIL <= bv_unsigned a /\ uE E e_sp0 <= bv_unsigned a.
  Proof. intros E a H. eapply argH0_high; eassumption. Qed.

  Theorem init_x_sound_envscan :
    x_stmt segs scfg A NX0 LIMIT RZ SINV ARGH FS0 XEnvScan.
  Proof.
    apply (x_sound_envscan segs scfg A NX0 LIMIT RZ SINV ARGH FS0
              SEGS_wx SEGS_in_hull HULL_ok SINV_frame
              we1 we2 we3 Xenv Fe1 Fe2 Fe3 Ee De1 De2 De3
              ph INP mbase entryw sp brk0 rdraw);
      solve [ assumption | exact sp_lo | exact sp_hi
            | exact SINV0_vals | exact SINV0_sp0 | exact SINV0_envp | exact SINV0_str0 ].
  Qed.

  Theorem init_x_sound_pnscan :
    x_stmt segs scfg A NX0 LIMIT RZ SINV ARGH FS0 XPnScan.
  Proof.
    apply (x_sound_pnscan segs scfg A NX0 LIMIT RZ SINV ARGH FS0
              SEGS_wx SEGS_in_hull HULL_ok
              argH0_high_sp e_sp0_init (argH0_agree sp rdraw argv envp fs stdin uid gid hw groups net nofile sigmask abrt urnd tmp0 kb execfn sdf)
              SINV_frame SINV_agree
              wp0 wp1 wp2 wp3 wp4 Xpn Fp0 Fp1 Fp2 Fp3 Fp4 Ep Dp0 Dp1 Dp2 Dp3 Dp4
              ph INP mbase entryw sp brk0 rdraw);
      solve [ assumption | exact sp_lo | exact sp_hi
            | exact SINV0_vals | exact SINV0_sp0 | exact SINV0_envp | exact SINV0_str0 ].
  Qed.

  Theorem init_x_sound_layout :
    x_stmt segs scfg A NX0 LIMIT RZ SINV ARGH FS0 XLayout.
  Proof. apply x_sound_layout. Qed.
End GenericInit.
