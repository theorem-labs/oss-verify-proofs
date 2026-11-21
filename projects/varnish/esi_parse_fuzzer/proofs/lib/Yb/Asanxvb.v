(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: the stack invariant, its hidden ranges and the initial valuation take the GID, the kernel build and the exec file name, argv[0] lies at the top of the AT_RANDOM bytes plus the arch_align_stack pad, the string area runs to the stack VMA's end, and the stack image is read through the stack's view of the input; and launch_auxv / vdso_text_base at the entry's stack pointer (LPS b84e73ef). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require CatSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require StoreOk ShapeAlg SpinAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanqlm.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require AsanAcct.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanqlm.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim.CatExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.CatSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim.SeqExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.StoreOk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.ShapeAlg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.SpinAlg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanqlm.AgentLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanAcct OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanqlm.Asanbbl.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require AxSyioe.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require AsanPlan.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanqlm.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AxSyioe OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanPlan.AxSyetn OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanqlm.AxSyqqh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Import Asanz3l AsanPlan Asanqlm AsanInit.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanj99.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanj99.Asangat.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanj99.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanj99.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanj99.Asanfjy OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanj99.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [Asanj99.edenot_ev_agree] asks that [e_str0 r] read only the initial variables, which
   is a computation once [r] is a literal: one case per CONFIG_RSEQ value. *)
Lemma nb_lt_e_str0 : forall b, nb_lt NX0 (e_str0 (rseq_z b)) = true.
Proof. intros [|]; reflexivity. Qed.

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
  (* LPS 727298f3: the stack image reads AT_GID, the kernel build (CONFIG_RSEQ sizes the
     auxv) and the exec file name, so AsanInit's [SINV0]/[argH0] take them.  [Hlau] is
     valid_entry's launch conjunct over the stack's view of the input
     ([AsanInit.stk_inp]; the same proposition as over the full input, by conversion): it
     pins the stack VMA's end, so it bounds the string area argv[0] lies in. *)
  Variable gid : word.
  Variable kb : KernelBuild.
  Variable execfn : list byte.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) (AsanInit.stk_inp argv envp uid gid hw kb execfn).

  (* [comment removed for export] *)
  Variable SINV : env -> (word -> option byte) -> Prop.
  Hypothesis SINV_SINV0 : forall E M, SINV E M -> SINV0 A ph sp rdraw brk0 mbase argv envp uid gid hw kb execfn E M.
  Hypothesis SINV_frame : forall E M M', (forall a, argH0 sp rdraw argv envp kb execfn E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
  Hypothesis SINV_agree : forall E E' M, env_agree NX0 E E' -> SINV E M -> SINV E' M.

  Let usp := bv_unsigned sp.
  Let argc := Z.of_nat (length argv).
  Let envc := Z.of_nat (length envp).
  Let s0 := nth 0 argv [].
  #[local] Notation E0x := (E0 sp rdraw brk0 argv envp uid gid hw kb execfn).
  #[local] Notation SINP := (AsanInit.stk_inp argv envp uid gid hw kb execfn).
  #[local] Notation ENTRY := (Z_to_bv 64 (a_entry A)).
  #[local] Notation RSEQ := (kb_rseq kb).
  (* argv[0]: the top of the AT_RANDOM bytes plus the [arch_align_stack] pad, spelled as
     Asanj99's [Section NodesD] spells it ([cat_string_off] is head + pad, so this is
     AsanInit's [usp + CHEAD + W]).  It WAS [usp + 8 * argc + 8 * envc + 184]. *)
  #[local] Notation STR0 := (bv_unsigned sp + Z.of_nat (cat_string_off RSEQ sp (ed_top rdraw) argv envp execfn)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma SINV0_vals : forall E M, SINV E M ->
    uE E e_envp = usp + 8 * argc + 16
    /\ ev E V_ENVC = Z_to_bv 64 envc
    /\ uE E (e_str0 (rseq_z RSEQ)) = STR0.
  Proof using Hsp Hva Hve Hfit SINV_SINV0.
    intros E M HS. apply SINV_SINV0 in HS. destruct HS as [Hev _].
    assert (U1 : uE E0x e_envp = usp + 8 * argc + 16)
      by exact (u_e_envp sp rdraw brk0 argv envp uid gid hw kb execfn Hsp Hva Hve Hfit).
    assert (U3 : uE E0x (e_str0 (rseq_z RSEQ))
                 = usp + Z.of_nat (block_head_size RSEQ argv envp)
                   + Z.of_nat (block_pad_len RSEQ sp (ed_top rdraw) argv envp execfn))
      by exact (u_e_str0 sp rdraw brk0 argv envp uid gid hw kb execfn Hsp Hva Hve Hfit).
    pose proof (uE0 sp rdraw brk0 argv envp uid gid hw kb execfn Hsp Hva Hve Hfit) as (_ & _ & _ & U2 & _).
    assert (Hev7 : forall n, (n < NX0)%nat -> ev E n = ev E0x n) by (intros n Hn; apply Hev; exact Hn).
    unfold uE in *.
    rewrite (edenot_ev_agree NX0 E E0x e_envp eq_refl Hev7).
    rewrite (edenot_ev_agree NX0 E E0x (e_str0 (rseq_z RSEQ)) (nb_lt_e_str0 RSEQ) Hev7).
    split; [exact U1|]. split; [|rewrite U3; unfold cat_string_off; rewrite Nat2Z.inj_add; unfold usp; lia].
    change (ev E V_ENVC) with (edenot E (EVar V_ENVC)).
    rewrite (edenot_ev_agree NX0 E E0x (EVar V_ENVC) eq_refl Hev7).
    apply bv_eq. rewrite U2. unfold envc. destruct Hve as [H _]. rewrite u64_lit by lia. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma SINV0_sp : forall E M, SINV E M -> uE E e_sp0 = usp.
  Proof using Hsp Hva Hve Hfit SINV_SINV0.
    intros E M HS. apply SINV_SINV0 in HS. destruct HS as [Hev _].
    pose proof (u_e_sp0 sp rdraw brk0 argv envp uid gid hw kb execfn Hsp Hva Hve Hfit) as U. unfold usp. rewrite <- U.
    unfold uE, e_sp0, eadd, escale. rewrite !mkAlu_denot, !mkMd_denot. cbn [edenot].
    rewrite (Hev V_S1) by (unfold V_S1, NX0; lia). rewrite (Hev V_S2) by (unfold V_S2, NX0; lia). reflexivity.
  Qed.

  Lemma SINV0_envp : forall E M (a : word), SINV E M ->
    usp + 8 * argc + 16 <= bv_unsigned a < usp + 8 * argc + 16 + 8 * envc + 8 -> M a = wrap_mem SINP mbase ph ENTRY sp rdraw a.
  Proof using SINV_SINV0.
    intros E M a HS Ha. apply SINV_SINV0 in HS. destruct HS as [_ HM]. apply HM. unfold argH0. apply orb_true_intro. left.
    apply andb_true_intro. unfold usp, argc, envc in Ha. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
  Qed.

  (* argv[0] and its NUL are among the launch's string bytes *)
  Lemma s0_in_strs : Z.of_nat (length s0) + 1 <= Z.of_nat (launch_string_bytes argv envp execfn).
  Proof.
    assert (Hnz : (0 < length argv)%nat) by (destruct Hva as [H _]; lia).
    unfold launch_string_bytes, s0.
    pose proof (Nat2Z.is_nonneg (length (flatten_strings envp))).
    pose proof (Nat2Z.is_nonneg (length execfn)).
    (* case analysis on a copy of [argv], not on the section variable (which would make the
       lemma depend on every section hypothesis that mentions [argv]) *)
    revert Hnz. generalize argv as l. intros l Hnz.
    destruct l as [|a t]; [cbn in Hnz; lia|].
    cbn [flatten_strings flat_map nth]. rewrite !length_app. cbn [length]. lia.
  Qed.

  (* the block runs from sp to the stack VMA's end: head, pad, strings, the 8-byte slot
     ([Yb.PropExec.length_entry_stack_image_launch] under the launch conjunct) *)
  Lemma str0_top :
    STR0 + Z.of_nat (launch_string_bytes argv envp execfn) + 8 = bv_unsigned (ed_top rdraw).
  Proof.
    pose proof (length_entry_stack_image_launch Sv48 SINP mbase ph ENTRY sp brk0 rdraw Hlau) as L.
    rewrite entry_stack_image_block, length_build_stack_bytes in L.
    change (la_rseq (launch_auxv SINP sp mbase)) with RSEQ in L.
    change (in_argv SINP) with argv in L. change (in_envp SINP) with envp in L.
    change (in_execfn SINP) with execfn in L.
    unfold cat_string_off. lia.
  Qed.

  (* the string area runs from argv[0] to the stack VMA's end and argv[0] with its NUL is
     inside it, so the bytes the progname scan reads are hidden by [argH0] *)
  Lemma SINV0_str0 : forall E M (a : word), SINV E M ->
    STR0 <= bv_unsigned a <= STR0 + Z.of_nat (length s0) ->
    M a = wrap_mem SINP mbase ph ENTRY sp rdraw a.
  Proof using Hva Hlau SINV_SINV0.
    intros E M a HS Ha. apply SINV_SINV0 in HS. destruct HS as [_ HM]. apply HM.
    pose proof s0_in_strs as F. pose proof str0_top as T.
    unfold s0 in F, Ha. unfold cat_string_off in Ha, T.
    unfold argH0. apply orb_true_intro. right.
    apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
  Qed.

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
End GenericInit.
