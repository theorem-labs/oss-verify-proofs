(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (SINV_SINV0 and SINV_frame restated for SINV0's and argH0's new arguments, over the whole launch input INP (new section variables gid, groups, net, nof, sigm, abt, urnd, tmpf, kb, execfn, chrdr, sigdef and sigterm) with valid_launch and entry_launch_ok_va hypotheses; the first string STR0 counted down from the stack top (str0_split added, s0_fits removed), so argH0_agree_nx, SINV0_vals, SINV0_envp and SINV0_str0 are restated over the launch's entry stack image; init_x_sound_envscan, init_x_sound_pnscan and init_x_sound_layout at the run's CONFIG_RSEQ flag (RZ); SINV0_sp0 re-proved). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg SpinAlg AgentLib
  AsanAcct AsanAcctShape.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanInit.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS Require Import AsanNodesAux AsanStartLoops AsanNodesStartX.
Unset Nia Cache. Unset Nra Cache.

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

  (** THE INPUT GROUP.  [AsanInit]'s [SINV0] now mentions [wrap_mem inp ...],
      and [inp] is all twenty [State.ProcInput] fields, so this Section can no
      longer carry just [fs stdin uid hw]: it must be able to BUILD [inp].
      The declaration order is [AsanInit]'s, so the positional lists this file
      spells for [AsanInit]'s discharged names read in the same order. *)
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variable brk0 mbase : word.
  Variable argv envp : list (list byte).
  Variable fs : Fs.Fs.
  Variable stdin : InputStream.
  Variable uid gid : word.
  Variable hw : word.
  Variable groups : list word.
  Variable net : NetQueue.
  Variables nof sigm : word.
  Variable abt : bool.
  Variable urnd : InputStream.
  Variable tmpf : Fs.Fs.
  Variable kb : KernelBuild.
  Variable execfn : list byte.
  Variables chrdr sigdef sigterm : bool.
  Variable FS0 : Fs.Fs.

  (** THE LONG LISTS, SPELLED ONCE.  A notation may abbreviate an APPLIED
      term, so every site below reads one name.  Discharge order is
      [AsanInit.v]'s Section declaration order, variables and hypotheses
      INTERLEAVED ([Hsp] 71, [Hva] 74, [Hve] 75 sit BETWEEN [net] 68 and
      [nof] 83; [Hlaunch] 100 and [Hlau] 107 are last). *)
  #[local] Notation INP := (inp argv envp fs stdin uid gid hw groups net nof sigm abt urnd tmpf kb execfn chrdr sigdef sigterm).
  (** the run's CONFIG_RSEQ flag as the plan's 0 or 1 *)
  #[local] Notation RZ := (rseq_z (kb_rseq kb)).
  #[local] Notation ENTRYW := (Z_to_bv 64 (a_entry A)).
  (** [argH0] LOST [ph], [uid] and [hw]: its new [V_W] is
      [StackLayout.block_pad_len], which names none of the three.  [ph] was
      argument ONE, so every pre-port call site is shifted by one. *)
  #[local] Notation argH0i := (argH0 sp rdraw argv envp kb execfn).
  #[local] Notation SINV0i := (SINV0 A ph sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nof sigm abt urnd tmpf kb execfn chrdr sigdef sigterm).

  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  (** [Run.valid_entry]'s stack-fit conjunct: [AsanInit]'s bundle below reads it
      (its proof's arithmetic does), so it is in the bundle's list after [Hve]. *)
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  (** [Run.valid_input]'s last conjunct.  NOT a conjunct of [valid_entry], so
      this is a genuinely new premise: a caller holding only [valid_entry] must
      get it from its own [valid_input]. *)
  Hypothesis Hlaunch : valid_launch INP.
  (** [Run.valid_entry]'s FIFTH conjunct, so a caller that destructures
      [valid_entry] already has it. *)
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) INP.
  (** [AsanInit.SINV0_exports], the bundle, with the ONE list this file owes
      it: [segs] first (the bundle's proof reads the image at this revision),
      then the hypotheses it uses in declaration order, {[Hsp], [Hva], [Hve],
      [Hfit], [Hlaunch], [Hlau]}. *)
  #[local] Notation EXP0 :=
    (SINV0_exports segs A ph sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net
                   Hsp Hva Hve Hfit nof sigm abt urnd tmpf kb execfn chrdr sigdef sigterm
                   Hlaunch Hlau).

  Variable SINV : env -> (word -> option byte) -> Prop.
  Hypothesis SINV_SINV0 : forall E M, SINV E M -> SINV0i E M.
  Hypothesis SINV_frame : forall E M M', (forall a, argH0i E a = true -> M' a = M a) -> SINV E M -> SINV E M'.

  Variable nx0 : nat.
  Hypothesis Hnx0 : (NX0 <= nx0)%nat.
  Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.

  Lemma argH0_agree_nx : forall E E' (a : word), env_agree nx0 E E' -> argH0i E a = argH0i E' a.
  Proof.
    intros E E' a [Hag Hb]. apply (argH0_agree sp rdraw argv envp kb execfn).
    split; [|exact Hb]. intros n Hn. apply Hag. lia.
  Qed.

  (** NOTATIONS, not [Let]s: a section [Let] that reaches a statement is
      discharged as a let-binder IN THE TYPE, which would change the shape of
      the three exported statements.  A notation cannot. *)
  #[local] Notation usp := (bv_unsigned sp).
  #[local] Notation argc := (Z.of_nat (length argv)).
  #[local] Notation envc := (Z.of_nat (length envp)).
  #[local] Notation s0 := (nth 0 argv (@nil byte)).
  #[local] Notation top := (ed_top rdraw).
  (** argv[0]'s address, in the form [AsanNodesStartX] states it *)
  #[local] Notation STR0 := (usp + Z.of_nat (cat_string_off (kb_rseq kb) sp top argv envp execfn)).

  Lemma sp_lo : sp_window_lo <= bv_unsigned sp.
  Proof. destruct Hsp as [H _]. exact H. Qed.
  Lemma sp_hi : bv_unsigned sp <= sp_window_hi.
  Proof. destruct Hsp as (_ & H & _). exact H. Qed.

  (** [CatExec.cat_string_off] is the head plus the pad, which is exactly
      [AsanInit]'s [STR0 = usp + CHEAD + W]; only the [Z.of_nat] has to be
      pushed through the sum. *)
  Lemma str0_split : STR0 = usp + Z.of_nat (block_head_size (kb_rseq kb) argv envp)
                            + Z.of_nat (block_pad_len (kb_rseq kb) sp top argv envp execfn).
  Proof. unfold cat_string_off. rewrite Nat2Z.inj_add. lia. Qed.

  (** the four facts [AsanNodesStartX.NodesD] asks of [SINV], from
      [AsanInit.SINV0_exports] — the bundle that file provides for exactly this
      purpose, so the long positional list is spelled ONCE here. *)
  Lemma SINV0_vals : forall E M, SINV E M ->
    uE E e_envp = usp + 8 * argc + 16
    /\ ev E V_ENVC = Z_to_bv 64 envc
    /\ uE E (e_str0 RZ) = STR0.
  Proof.
    intros E M HS. apply SINV_SINV0 in HS.
    destruct EXP0 as (X1 & _ & _ & _).
    destruct (X1 E M HS) as (U1 & U2 & U3).
    split; [exact U1|]. split; [exact U2|]. rewrite U3, str0_split. reflexivity.
  Qed.

  Lemma SINV0_sp0 : forall E M, SINV E M -> uE E e_sp0 = usp.
  Proof.
    intros E M HS. apply SINV_SINV0 in HS.
    destruct EXP0 as (_ & X2 & _ & _).
    exact (X2 E M HS).
  Qed.

  Lemma SINV0_envp : forall E M (a : word), SINV E M ->
    usp + 8 * argc + 16 <= bv_unsigned a < usp + 8 * argc + 16 + 8 * envc + 8 ->
    M a = wrap_mem INP mbase ph ENTRYW sp rdraw a.
  Proof.
    intros E M a HS Ha. apply SINV_SINV0 in HS.
    destruct EXP0 as (_ & _ & X3 & _).
    exact (X3 E M a HS Ha).
  Qed.

  Lemma SINV0_str0 : forall E M (a : word), SINV E M ->
    STR0 <= bv_unsigned a <= STR0 + Z.of_nat (length s0) ->
    M a = wrap_mem INP mbase ph ENTRYW sp rdraw a.
  Proof.
    intros E M a HS Ha. apply SINV_SINV0 in HS.
    destruct EXP0 as (_ & _ & _ & X4).
    apply (X4 E M a HS). rewrite <- str0_split. exact Ha.
  Qed.

  (** THE ONE DISCHARGE LIST.  Without [Proof using] each of the three would
      discharge its OWN used-variable subset and a consumer would have to
      re-derive three different ~45-argument lists from the proof scripts, with
      no build to check them.  Naming the whole Section context pins all three
      to the SAME list, in declaration order:

        segs A ph SEGS_wx SEGS_in_hull HULL_ok
        we1 we2 we3 wp0 wp1 wp2 wp3 wp4
        Xenv Fe1 Fe2 Fe3 Ee De1 De2 De3
        Xpn Fp0 Fp1 Fp2 Fp3 Fp4 Ep Dp0 Dp1 Dp2 Dp3 Dp4
        sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net
        nof sigm abt urnd tmpf kb execfn chrdr sigdef sigterm FS0
        Hsp Hva Hve Hfit Hlaunch Hlau
        SINV SINV_SINV0 SINV_frame nx0 Hnx0 SINV_agree

      ([Proof using] may name a SUPERSET of what the proof uses.) *)
  Theorem init_x_sound_envscan :
    x_stmt segs A nx0 LIMIT RZ SINV argH0i FS0 XEnvScan.
  Proof using segs A ph SEGS_wx SEGS_in_hull HULL_ok
              we1 we2 we3 wp0 wp1 wp2 wp3 wp4
              Xenv Fe1 Fe2 Fe3 Ee De1 De2 De3
              Xpn Fp0 Fp1 Fp2 Fp3 Fp4 Ep Dp0 Dp1 Dp2 Dp3 Dp4
              sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net
              nof sigm abt urnd tmpf kb execfn chrdr sigdef sigterm FS0
              Hsp Hva Hve Hfit Hlaunch Hlau
              SINV SINV_SINV0 SINV_frame nx0 Hnx0 SINV_agree.
    exact (x_sound_envscan segs A nx0 LIMIT RZ SINV argH0i FS0
              SEGS_wx SEGS_in_hull HULL_ok SINV_frame
              we1 we2 we3 Xenv Fe1 Fe2 Fe3 Ee De1 De2 De3
              ph INP mbase ENTRYW sp brk0 rdraw Hva Hve Hlaunch Hlau sp_lo sp_hi
              SINV0_vals SINV0_sp0 SINV0_envp).
  Qed.

  Theorem init_x_sound_pnscan :
    x_stmt segs A nx0 LIMIT RZ SINV argH0i FS0 XPnScan.
  Proof using segs A ph SEGS_wx SEGS_in_hull HULL_ok
              we1 we2 we3 wp0 wp1 wp2 wp3 wp4
              Xenv Fe1 Fe2 Fe3 Ee De1 De2 De3
              Xpn Fp0 Fp1 Fp2 Fp3 Fp4 Ep Dp0 Dp1 Dp2 Dp3 Dp4
              sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net
              nof sigm abt urnd tmpf kb execfn chrdr sigdef sigterm FS0
              Hsp Hva Hve Hfit Hlaunch Hlau
              SINV SINV_SINV0 SINV_frame nx0 Hnx0 SINV_agree.
    exact (x_sound_pnscan segs A nx0 LIMIT RZ SINV argH0i FS0
              SEGS_wx SEGS_in_hull HULL_ok
              (argH0_high sp rdraw argv envp Hsp Hva kb execfn) argH0_agree_nx
              SINV_frame SINV_agree
              wp0 wp1 wp2 wp3 wp4 Xpn Fp0 Fp1 Fp2 Fp3 Fp4 Ep Dp0 Dp1 Dp2 Dp3 Dp4
              ph INP mbase ENTRYW sp brk0 rdraw Hva Hve Hlau sp_lo sp_hi
              SINV0_vals SINV0_sp0 SINV0_envp SINV0_str0).
  Qed.

  Theorem init_x_sound_layout :
    x_stmt segs A nx0 LIMIT RZ SINV argH0i FS0 XLayout.
  Proof using segs A ph SEGS_wx SEGS_in_hull HULL_ok
              we1 we2 we3 wp0 wp1 wp2 wp3 wp4
              Xenv Fe1 Fe2 Fe3 Ee De1 De2 De3
              Xpn Fp0 Fp1 Fp2 Fp3 Fp4 Ep Dp0 Dp1 Dp2 Dp3 Dp4
              sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net
              nof sigm abt urnd tmpf kb execfn chrdr sigdef sigterm FS0
              Hsp Hva Hve Hfit Hlaunch Hlau
              SINV SINV_SINV0 SINV_frame nx0 Hnx0 SINV_agree.
    apply x_sound_layout.
  Qed.
End GenericInit.
