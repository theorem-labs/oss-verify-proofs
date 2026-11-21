(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch is the run's whole ProcInput, with the mmap base and the image entry; argv[0] sits above the AT_RANDOM bytes and the arch_align_stack pad; the obligations are discharged by naming the hypotheses that pin each witness). *)
(* Ported to LPS 08b1429: the launch is the run's whole [ProcInput]; argv[0] sits at
   [usp + cat_string_off] (the top of the AT_RANDOM bytes plus the [arch_align_stack]
   pad), not at a constant offset above sp. *)

(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg SpinAlg AgentLib
  AsanAcct AsanAcctShape.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanInit.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import AsanNodesAux AsanStartLoops AsanNodesStartX.
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
  Variable LIM : Z.

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

  (** the run: the input carries argv, envp, the credentials, the exec file name
      and the kernel build; [apc] is the auxv's AT_ENTRY *)
  Variable apc : N.
  Variable sp : word.
  Variable rdraw : EntryDraw.   (* the entry draw [Run.en_draw]; ed_random = the AT_RANDOM bytes, ed_top = the stack VMA's end *)
  Variable brk0 mbase : word.
  Variable inp : ProcInput.
  Variable FS0 : Fs.Fs.
  Let entryw := Z_to_bv 64 (Z.of_N apc).

  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv (in_argv inp).
  Hypothesis Hve : valid_envp (in_envp inp).
  (** AsanInit's Section carries these too, and Rocq generalises each of its
      lemmas over every hypothesis its proof term reads, so they must be here
      for [eassumption] to discharge them. *)
  Hypothesis IMG : AsanInit.img_facts segs A ph.
  Hypothesis Hapc : Z.of_N apc = a_entry A.
  Hypothesis Hbrk : valid_brk segs brk0.
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Huid : valid_id (in_uid inp).
  Hypothesis Hzr : AsanCeil.zero_random_draw (ed_random rdraw).
  Hypothesis Hlaunch : valid_launch inp.
  Hypothesis Hrdr : in_channel_reader inp = true.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) inp.

  (* [comment removed for export] *)
  Variable SINV : env -> (word -> option byte) -> Prop.
  Hypothesis SINV_SINV0 : forall E M, SINV E M -> SINV0 ph apc sp rdraw brk0 mbase inp E M.
  Hypothesis SINV_frame : forall E M M', (forall a, argH0 sp rdraw inp E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
  Hypothesis SINV_agree : forall E E' M, env_agree NX0 E E' -> SINV E M -> SINV E' M.

  Let usp := bv_unsigned sp.
  Let argc := Z.of_nat (length (in_argv inp)).
  Let envc := Z.of_nat (length (in_envp inp)).
  Let s0 := nth 0 (in_argv inp) [].
  Let STR0 := usp + Z.of_nat (cat_string_off (kb_rseq (in_kernel inp)) sp (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp)).

  Lemma sp_lo : sp_window_lo <= bv_unsigned sp.
  Proof. destruct Hsp as [H _]. exact H. Qed.
  Lemma sp_hi : bv_unsigned sp <= sp_window_hi.
  Proof. destruct Hsp as (_ & H & _). exact H. Qed.

  (* [comment removed for export] *)
  Lemma SINV0_vals : forall E M, SINV E M ->
    uE E e_envp = usp + 8 * argc + 16
    /\ ev E V_ENVC = Z_to_bv 64 envc
    /\ uE E e_str0 = STR0.
  Proof.
    intros E M HS. apply SINV_SINV0 in HS.
    eapply SINV0_vals_E0; eauto.
  Qed.

  Lemma SINV0_envp : forall E M (a : word), SINV E M ->
    usp + 8 * argc + 16 <= bv_unsigned a < usp + 8 * argc + 16 + 8 * envc + 8 ->
    M a = wrap_mem inp mbase ph entryw sp rdraw a.
  Proof.
    intros E M a HS Ha. apply SINV_SINV0 in HS.
    eapply SINV0_envp_E0; eauto.
  Qed.

  Lemma SINV0_str0 : forall E M (a : word), SINV E M ->
    STR0 <= bv_unsigned a <= STR0 + Z.of_nat (length s0) ->
    M a = wrap_mem inp mbase ph entryw sp rdraw a.
  Proof.
    intros E M a HS Ha. apply SINV_SINV0 in HS.
    eapply SINV0_str0_E0; eauto.
  Qed.

  (* [comment removed for export] *)
  Theorem init_x_sound_envscan :
    x_stmt segs A NX0 LIM SINV (argH0 sp rdraw inp) (bv_unsigned sp) FS0 XEnvScan.
  Proof.
    (* The Section generalises over EIGHT [bv 32] variables - we1 we2 we3 wp0 wp1 wp2 wp3
       wp4, one [Variables] line in AsanNodesStartX.v - and over seven word-ish ones, so a
       single [first] applied to every goal cannot tell them apart.  A diagnostic arm
       named the actual failure, the goal fetch_word segs
       (Z_to_bv 64 (x_envscan A)) = Some wp4 -- [eassumption], the FIRST arm, had closed
       the bare [bv 32] goal with whichever such hypothesis the context offered last
       (wp4), and the fetch obligation then asked for a word nothing proves.
       So: pass one uses only arms that are unambiguous by type or that PIN the variables
       by unification (Fe1/Fe2/Fe3 and De1/De2/De3 each mention we1/we2/we3; SINV0_envp
       mentions ph, entryw and mbase; the conclusion already pins segs, A, SINV, sp,
       rdraw, inp, LIM and FS0).  Pass two closes whatever is genuinely unconstrained, and
       only there may [eassumption] choose.  Pass three closes the rest. *)
    unshelve eapply x_sound_envscan;
      (* Hlau pins brk0 AND mbase, Hbrk pins brk0, Hmb pins mbase - all by unification,
         and all before any bare [word] goal can be reached.  Naming them here instead of
         leaving them to the later [eassumption] is the whole point: two section variables
         of one type must be pinned by a statement, never chosen by a tactic. *)
      try first [exact Hsp | exact Hva | exact Hve | exact Hlaunch | exact Hlau
                | exact Hbrk | exact Hmb | exact IMG | exact Hapc | exact Huid
                | exact Hzr | exact Hrdr | exact SINV_SINV0];
      try first [exact SEGS_wx | exact SEGS_in_hull | exact HULL_ok | exact SINV_frame | exact SINV_agree
                | exact Xenv | exact Fe1 | exact Fe2 | exact Fe3
                | exact Ee | exact De1 | exact De2 | exact De3
                | exact SINV0_vals | exact SINV0_envp | exact SINV0_str0
                | exact NX0_spw | exact (argH0_agree sp rdraw inp)
                | intros E0_ a0_ Ha0_; eapply argH0_high; eassumption
                | exact sp_lo | exact sp_hi | reflexivity];
      try first [eassumption | exact we1 | exact we2 | exact we3
                | exact ph | exact inp | exact mbase | exact entryw | exact sp | exact brk0 | exact rdraw];
      first [eassumption | reflexivity].
  Qed.

  Theorem init_x_sound_pnscan :
    x_stmt segs A NX0 LIM SINV (argH0 sp rdraw inp) (bv_unsigned sp) FS0 XPnScan.
  Proof.
    (* as init_x_sound_envscan: three passes, the ambiguous [bv 32] and word arms held
       back until the hypotheses have pinned what they can. *)
    unshelve eapply x_sound_pnscan;
      (* as init_x_sound_envscan: the pinning hypotheses first. *)
      try first [exact Hsp | exact Hva | exact Hve | exact Hlaunch | exact Hlau
                | exact Hbrk | exact Hmb | exact IMG | exact Hapc | exact Huid
                | exact Hzr | exact Hrdr | exact SINV_SINV0];
      try first [exact SEGS_wx | exact SEGS_in_hull | exact HULL_ok | exact SINV_frame | exact SINV_agree
                | exact Xpn | exact Fp0 | exact Fp1 | exact Fp2 | exact Fp3 | exact Fp4
                | exact Ep | exact Dp0 | exact Dp1 | exact Dp2 | exact Dp3 | exact Dp4
                | exact SINV0_vals | exact SINV0_envp | exact SINV0_str0
                | exact NX0_spw | exact (argH0_agree sp rdraw inp)
                | intros E0_ a0_ Ha0_; eapply argH0_high; eassumption
                | exact sp_lo | exact sp_hi | reflexivity];
      try first [eassumption | exact wp0 | exact wp1 | exact wp2 | exact wp3 | exact wp4
                | exact ph | exact inp | exact mbase | exact entryw | exact sp | exact brk0 | exact rdraw];
      first [eassumption | reflexivity].
  Qed.
  Theorem init_x_sound_layout :
    x_stmt segs A NX0 LIM SINV (argH0 sp rdraw inp) (bv_unsigned sp) FS0 XLayout.
  Proof. apply x_sound_layout. Qed.
End GenericInit.
