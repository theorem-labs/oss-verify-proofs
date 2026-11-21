(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the 27- or 29-pair auxv; the launch's input, mmap base and entry draw; the CONFIG_RSEQ value; the launch's reader of the standard channels). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.ASN Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg SpinAlg AgentLib
  AsanAcct AsanAcctShape.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.ASN Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanInit.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.ASN Require Import AsanNodesAux AsanStartLoops AsanNodesStartX.

Unset Lia Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section GenericInit.

  Variable segs : list Segment.
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

  (* the run: [AsanInit]'s launch, with every launch fact the chain reads in [launch_ok] *)
  Variable apc : N.
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variable brk0 mbase : word.
  Variable inp : ProcInput.
  Variable FS0 : Fs.Fs.
  Hypothesis HL : launch_ok segs A ph apc sp rdraw brk0 mbase inp.

  Variable SINV : env -> (word -> option byte) -> Prop.
  Hypothesis SINV_SINV0 : forall E M, SINV E M -> SINV0 ph apc sp rdraw brk0 mbase inp E M.
  Hypothesis SINV_frame : forall E M M', (forall a, argH0 sp rdraw inp E a = true -> M' a = M a) -> SINV E M -> SINV E M'.

  Variable nx0 : nat.
  Hypothesis Hnx0 : (NX0 <= nx0)%nat.
  Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.

  Lemma argH0_agree_nx : forall E E' (a : word), env_agree nx0 E E' -> argH0 sp rdraw inp E a = argH0 sp rdraw inp E' a.
  Proof. intros E E' a [Hag Hb]. apply (argH0_agree sp rdraw inp). split; [|exact Hb]. intros n Hn. apply Hag. lia. Qed.

  Let usp := bv_unsigned sp.
  Let argc := Z.of_nat (length (in_argv inp)).
  Let envc := Z.of_nat (length (in_envp inp)).
  Let s0 := nth 0 (in_argv inp) [].
  Let rseq := kb_rseq (in_kernel inp).
  Let RZ := rseq_z rseq.
  Let STR0 := usp + Z.of_nat (cat_string_off rseq sp (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp)).

  Lemma sp_lo : sp_window_lo <= bv_unsigned sp.
  Proof. pose proof HL as [_ _ Hsp _ _ _ _ _ _ _ _ _ _ _]. destruct Hsp as [H _]. exact H. Qed.
  Lemma sp_hi : bv_unsigned sp <= sp_window_hi.
  Proof. pose proof HL as [_ _ Hsp _ _ _ _ _ _ _ _ _ _ _]. destruct Hsp as (_ & H & _). exact H. Qed.

  (* [e_str0]'s variables are launch variables under both auxv layouts *)
  Lemma nb_lt_e_str0 : forall b, nb_lt NX0 (e_str0 (rseq_z b)) = true.
  Proof. intros [|]; reflexivity. Qed.

  (* what [SINV0] provides, in the form AsanNodesStartX wants *)
  Lemma SINV0_vals : forall E M, SINV E M ->
    uE E e_envp = usp + 8 * argc + 16
    /\ ev E V_ENVC = Z_to_bv 64 envc
    /\ uE E (e_str0 RZ) = STR0.
  Proof.
    intros E M HS. apply SINV_SINV0 in HS. destruct HS as [Hev _].
    pose proof (u_e_envp_l segs A ph apc sp rdraw brk0 mbase inp HL) as U1.
    pose proof (u_e_str0_l segs A ph apc sp rdraw brk0 mbase inp HL) as U3.
    pose proof (uE0_envc_l segs A ph apc sp rdraw brk0 mbase inp HL) as U2.
    assert (Hev7 : forall n, (n < NX0)%nat -> ev E n = ev (E0 sp rdraw brk0 inp) n) by (intros n Hn; apply Hev; exact Hn).
    unfold uE in *.
    rewrite (edenot_ev_agree NX0 E (E0 sp rdraw brk0 inp) e_envp eq_refl Hev7).
    rewrite (edenot_ev_agree NX0 E (E0 sp rdraw brk0 inp) (e_str0 RZ) (nb_lt_e_str0 rseq) Hev7).
    split; [exact U1|]. split.
    - change (ev E V_ENVC) with (edenot E (EVar V_ENVC)).
      rewrite (edenot_ev_agree NX0 E (E0 sp rdraw brk0 inp) (EVar V_ENVC) eq_refl Hev7).
      apply bv_eq. rewrite U2. unfold envc. pose proof HL as [_ _ _ _ _ _ Hve _ _ _ _ _ _ _].
      destruct Hve as [H _]. rewrite u64_lit by lia. reflexivity.
    - unfold RZ, rseq. rewrite U3. unfold STR0, usp, cat_string_off, rseq. rewrite Nat2Z.inj_add. lia.
  Qed.

  Lemma SINV0_sp0 : forall E M, SINV E M -> uE E e_sp0 = usp.
  Proof.
    intros E M HS. apply SINV_SINV0 in HS. destruct HS as [Hev _].
    assert (Hev7 : forall n, (n < NX0)%nat -> ev E n = ev (E0 sp rdraw brk0 inp) n) by (intros n Hn; apply Hev; exact Hn).
    unfold uE. rewrite (edenot_ev_agree NX0 E (E0 sp rdraw brk0 inp) e_sp0 eq_refl Hev7).
    exact (u_e_sp0_l segs A ph apc sp rdraw brk0 mbase inp HL).
  Qed.

  Lemma SINV0_envp : forall E M (a : word), SINV E M ->
    usp + 8 * argc + 16 <= bv_unsigned a < usp + 8 * argc + 16 + 8 * envc + 8 ->
    M a = wrap_mem inp mbase ph (Z_to_bv 64 (Z.of_N apc)) sp rdraw a.
  Proof.
    intros E M a HS Ha. apply SINV_SINV0 in HS. destruct HS as [_ HM]. apply HM. unfold argH0. apply orb_true_intro. left.
    apply andb_true_intro. unfold usp, argc, envc in Ha. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
  Qed.

  (* the string area runs from argv[0] to the stack VMA's end, and argv[0] with its NUL is inside
     it, so the bytes the progname scan reads are hidden by [argH0] *)
  Lemma SINV0_str0 : forall E M (a : word), SINV E M ->
    STR0 <= bv_unsigned a <= STR0 + Z.of_nat (length s0) ->
    M a = wrap_mem inp mbase ph (Z_to_bv 64 (Z.of_N apc)) sp rdraw a.
  Proof.
    intros E M a HS Ha. apply SINV_SINV0 in HS. destruct HS as [_ HM]. apply HM. unfold argH0. apply orb_true_intro. right.
    pose proof (s0_in_strings_l segs A ph apc sp rdraw brk0 mbase inp HL) as HS0.
    pose proof (str0_hi_l segs A ph apc sp rdraw brk0 mbase inp HL) as HT.
    unfold STR0, s0, usp, rseq, cat_string_off in Ha. rewrite Nat2Z.inj_add in Ha.
    apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
  Qed.

  Lemma argH0_high_sp : forall E (a : word), argH0 sp rdraw inp E a = true -> CEIL <= bv_unsigned a.
  Proof. exact (argH0_high_l segs A ph apc sp rdraw brk0 mbase inp HL). Qed.

  Theorem init_x_sound_envscan :
    x_stmt segs A nx0 LIMIT RZ SINV (argH0 sp rdraw inp) FS0 XEnvScan.
  Proof using All.
    pose proof HL as HL'. destruct HL' as [_ _ _ _ _ Hva Hve _ _ _ Hvl Hlau _ _ _].
    eapply x_sound_envscan;
      solve [ eassumption | exact sp_lo | exact sp_hi
            | exact SINV0_vals | exact SINV0_sp0 | exact SINV0_envp | exact SINV0_str0 ].
  Qed.

  Theorem init_x_sound_pnscan :
    x_stmt segs A nx0 LIMIT RZ SINV (argH0 sp rdraw inp) FS0 XPnScan.
  Proof using All.
    pose proof HL as HL'. destruct HL' as [_ _ _ _ _ Hva Hve _ _ _ Hvl Hlau _ _ _].
    eapply x_sound_pnscan;
      solve [ eassumption | exact sp_lo | exact sp_hi | exact argH0_high_sp | exact argH0_agree_nx
            | exact SINV0_vals | exact SINV0_sp0 | exact SINV0_envp | exact SINV0_str0 ].
  Qed.

  Theorem init_x_sound_layout :
    x_stmt segs A nx0 LIMIT RZ SINV (argH0 sp rdraw inp) FS0 XLayout.
  Proof using All. apply x_sound_layout. Qed.
End GenericInit.
