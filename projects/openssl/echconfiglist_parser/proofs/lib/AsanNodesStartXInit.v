(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (Section GenericInit takes the run's ProcInput and AsanInit's launch premises, valid_launch and entry_launch_ok_va among them; argv[0] sits at cat_string_off, and the SINV0 lemmas are re-proved from AsanInit's E0 lemmas); Section GenericInit is generic in the Leaf class. *)
(* Ported to LPS 08b1429: AsanInit's Section takes the run's whole input, and argv[0]
   sits at the top of the stack VMA ([CatExec.cat_string_off]). *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg SpinAlg AgentLib AsanAcct AsanAcctShape.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanInit.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import AsanNodesAux AsanStartLoops AsanNodesStartX Scfg.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.Cfg Require Import Leaf.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section GenericInit.
  Variable segs : list Segment.
  Context {SC : StepCfg}.
  Context {LF : Leaf}.
  Variable A : atable.
  Variable ph : PhdrInfo.
  Hypothesis SEGS_wx : wx_segs_nowrap segs.
  Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment segs (bv_unsigned a) 1 = None.
  Hypothesis HULL_ok : hull_ok A.

  (** the code of the two musl loops *)
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

  (** the run, as AsanInit's Section takes it *)
  Variable apc : N.
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variable brk0 mbase : word.
  Variable inp : ProcInput.
  Variable FS0 : Fs.Fs.

  Let argv := in_argv inp.
  Let envp := in_envp inp.
  Let entryw := Z_to_bv 64 (Z.of_N apc).

  (** AsanInit's Section hypotheses: each of its lemmas is generalised over those its
      proof reads, so they are here for [eassumption] *)
  Hypothesis IMG : img_facts segs A ph.
  Hypothesis Hapc : Z.of_N apc = a_entry A.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk segs brk0.
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Hypothesis Huid : valid_id (in_uid inp).
  Hypothesis Hhw : valid_hwcap (in_hwcap inp).
  Hypothesis Hlaunch : valid_launch inp.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) inp.

  (** the class invariant: anything implying SINV0 and stable like it *)
  Variable SINV : env -> (word -> option byte) -> Prop.
  Hypothesis SINV_SINV0 : forall E M, SINV E M -> SINV0 ph apc sp rdraw brk0 mbase inp E M.
  Hypothesis SINV_frame : forall E M M', (forall a, argH0 sp rdraw inp E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
  Hypothesis SINV_agree : forall E E' M, env_agree NX0 E E' -> SINV E M -> SINV E' M.

  Let usp := bv_unsigned sp.
  Let argc := Z.of_nat (length argv).
  Let envc := Z.of_nat (length envp).
  Let s0 := nth 0 argv [].
  Let rseq := kb_rseq (in_kernel inp).
  Let execfn := in_execfn inp.
  Let top := ed_top rdraw.
  (** argv[0]: the top of the AT_RANDOM bytes plus the [arch_align_stack] pad *)
  Let STR0 := usp + Z.of_nat (cat_string_off rseq sp top argv envp execfn).

  Lemma sp_lo : sp_window_lo <= bv_unsigned sp.
  Proof. destruct Hsp as [H _]. exact H. Qed.
  Lemma sp_hi : bv_unsigned sp <= sp_window_hi.
  Proof. destruct Hsp as (_ & H & _). exact H. Qed.

  Lemma SINV0_vals : forall E M, SINV E M ->
    uE E e_envp = usp + 8 * argc + 16
    /\ ev E V_ENVC = Z_to_bv 64 envc
    /\ uE E e_str0 = STR0.
  Proof. intros E M HS. eapply AsanInit.SINV0_vals_E0; [eassumption .. | exact (SINV_SINV0 E M HS)]. Qed.

  Lemma SINV0_sp0 : forall E M, SINV E M -> uE E e_sp0_early = usp.
  Proof. intros E M HS. eapply AsanInit.SINV0_sp0_E0; [eassumption .. | exact (SINV_SINV0 E M HS)]. Qed.

  Lemma SINV0_pg : forall E M, SINV E M -> uE E e_pg_early = pagedown (uE E e_sp0_early).
  Proof. intros E M HS. eapply AsanInit.SINV0_pg_E0; [eassumption .. | exact (SINV_SINV0 E M HS)]. Qed.

  Lemma SINV0_envp : forall E M (a : word), SINV E M ->
    usp + 8 * argc + 16 <= bv_unsigned a < usp + 8 * argc + 16 + 8 * envc + 8 ->
    M a = wrap_mem inp mbase ph entryw sp rdraw a.
  Proof. intros E M a HS Ha. eapply AsanInit.SINV0_envp_E0; [eassumption .. | exact (SINV_SINV0 E M HS) | exact Ha]. Qed.

  Lemma SINV0_str0 : forall E M (a : word), SINV E M ->
    STR0 <= bv_unsigned a <= STR0 + Z.of_nat (length s0) ->
    M a = wrap_mem inp mbase ph entryw sp rdraw a.
  Proof. intros E M a HS Ha. eapply AsanInit.SINV0_str0_E0; [eassumption .. | exact (SINV_SINV0 E M HS) | exact Ha]. Qed.

  Lemma argH0_high' : forall E (a : word), argH0 sp rdraw inp E a = true -> CEIL <= bv_unsigned a.
  Proof. intros E a H. eapply AsanInit.argH0_high; [eassumption .. | exact H]. Qed.

  Lemma argH0_agree' : forall E E' (a : word), env_agree NX0 E E' -> argH0 sp rdraw inp E a = argH0 sp rdraw inp E' a.
  Proof. intros E E' a H. eapply AsanInit.argH0_agree; [eassumption .. | exact H]. Qed.

  Lemma E_SP0' : AP.expr_vars_lt NX0 e_sp0_early = true.
  Proof. reflexivity. Qed.

  Ltac close_init :=
    first [ eassumption | exact sp_lo | exact sp_hi | exact E_SP0'
          | exact SINV0_vals | exact SINV0_envp | exact SINV0_str0 | exact SINV0_sp0
          | exact argH0_high' | exact argH0_agree' | exact SINV_frame | exact SINV_agree
          (* LPS c0dd863a: [APS.cs_ok_agree]'s [EHDR_lt], at [NX0], by computation *)
          | exact (proj1 (Nat.ltb_lt V_EHDR NX0) eq_refl) ].

  Theorem init_x_sound_envscan :
    x_stmt segs A NX0 LIMIT SINV (argH0 sp rdraw inp) FS0 XEnvScan.
  Proof.
    eapply (x_sound_envscan segs A NX0 LIMIT SINV (argH0 sp rdraw inp) FS0).
    all: close_init.
  Qed.

  Theorem init_x_sound_pnscan :
    x_stmt segs A NX0 LIMIT SINV (argH0 sp rdraw inp) FS0 XPnScan.
  Proof.
    eapply (x_sound_pnscan segs A NX0 LIMIT SINV (argH0 sp rdraw inp) FS0).
    all: close_init.
  Qed.

  Theorem init_x_sound_layout :
    x_stmt segs A NX0 LIMIT SINV (argH0 sp rdraw inp) FS0 XLayout.
  Proof. apply x_sound_layout. Qed.
End GenericInit.
