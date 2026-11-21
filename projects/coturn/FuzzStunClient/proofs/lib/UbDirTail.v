(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: for LPS 727298f3, the section takes the launch input, mmap base, entry point, uid and hwcap of the 12-argument main_entry and the stderr write's channel reader, and the argument pointer follows the launch's string layout. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.coturn.FuzzStunClient.images Require Import Ubsan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Amb.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg SymExec.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import SymExec2 SymExec2Sound SymDriveX Spec UbStartup UbMainEntry UbMainEntryN UbReadBase UbWorld UbReadErr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFast.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastK.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastS.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastM.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import SumWalkFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.gres ::= gres_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.vnorm ::= vnorm_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StepTac.step_simpl ::= step_simpl_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.RefMemcpyLib.not_kept ::= not_kept_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StartupTac.in_list ::= in_list_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StartupTac.peel ::= peel_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StoreOk.store_ok_peel ::= store_ok_peel_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.SumWalkTac.rdn_peel1 ::= rdn_peel1_fast.
(* [comment removed for export] *)
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Record dir_tail_pre {AMB : Amb} (sp0 p1 : word) (tid : Z) (mem0 : word -> option byte)
       (R : bvmap 5 word) (M : word -> option byte) : Prop := DIR_TAIL_PRE {
  dt_sp : getr R 2 = Z_to_bv 64 (bv_unsigned sp0 - 128);
  dt_gp : getr R 3 = Z_to_bv 64 0x10800;
  dt_tp : getr R 4 = Z_to_bv 64 0x36c60;
  dt_s2 : getr R 18 = p1;                                  (* [comment removed for export] *)
  dt_stack : stack_writable M sp0;
  dt_img : Forall (fun iv => img_clear M (fst iv) (snd iv)) re_ivs;
  dt_tid : cell M 0x36bb8 4 tid;
  dt_tidr : (0 < tid < 2 ^ 22)%Z;
  dt_self : cell M 0x36b98 8 0x36b98;
  dt_canary : exists cn, cell M 0x56ca0 8 cn;   (* [comment removed for export] *)
  dt_pagesz : cell M 0x56f18 8 4096;
  dt_above : forall a : word, (bv_unsigned sp0 <= bv_unsigned a)%Z -> M a = mem0 a
}.

Section DirTail.
  Context {AMB : Amb}.
  Variable sp0 : word.
  Variable a0s : list byte.
  Variable envv : list (list byte).
  Variable rdraw : EntryDraw.   (* [comment removed for export] *)
  Variable tid : word.
  Variable regs0 : bvmap 5 word.
  Variable mem0 : word -> option byte.
  Hypothesis Hva : valid_argv [a0s; dot_path].
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  (* LPS 08b1429: the launch input, mmap base, entry point, uid/hwcap and the 12-argument
     [main_entry] (as in RefMainEntryN). *)
  Variable inp : ProcInput.
  Variables mbase entry : word.
  Variables uid hw : word.
  Hypothesis ME : main_entry inp mbase entry sp0 [a0s; dot_path] envv uid hw rdraw tid regs0 mem0.

  Theorem dir_tail : forall (R : bvmap 5 word) (M : word -> option byte) (model : Model),
    m_halted model = None -> m_vm_lazy model = [] ->
    fd_lookup (m_fds model) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) ->
    m_channel_reader model = true ->   (* LPS 08b1429: the stderr write's channel reader *)
    dir_tail_pre sp0 (p1 a0s dot_path envv rdraw inp) (bv_unsigned tid) mem0 R M ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x13cec) M (seg_rom RSEGS)) model)
               (t_die (msg_read_error dot_path) (m_fs model)).
  Proof.
    intros R M model Hh Hlazy Hfd2 Hrdr P.
    destruct P as [Rsp Rgp Rtp Rs2 Mstack Mimg Mtid Htidr Mself [cn Mcanary] Mpagesz Habove].
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi.
    unfold sp_window_lo, sp_window_hi in SPlo, SPhi.
    edestruct main_strN with (k := 1%nat) (sp0 := sp0) (av := [a0s; dot_path]) (envv := envv) (rdraw := rdraw)
      (tid := tid) (regs := regs0) (mem := mem0) (inp := inp) (mbase := mbase) (entry := entry) (uid := uid) (hw := hw)
      as (Sr & Slo & Shi & Slen & (t8 & Ht8) & Send); try eassumption; try (cbn; lia).
    cbn [nth length Nat.add dot_path app] in Sr, Slo, Shi, Ht8.
    set (pp := p1 a0s dot_path envv rdraw inp) in *.
    change (cat_argv_ptr (ed_top rdraw) [a0s; dot_path] envv (in_execfn inp) 1) with pp in Sr, Slo, Shi, Ht8.
    change (Z.of_nat 1) with 1%Z in Ht8.
    pose proof (u64_range pp) as Hppr.
    assert (Hstr : rdn RSEGS M pp 2 = Some [Z_to_bv 8 46; Z_to_bv 8 0]).
    { rewrite <- Sr. apply rdn_agree. intros j Hj. apply Habove. rewrite u_small by lia. lia. }
    assert (Ht8' : rdn RSEGS M (Z_to_bv 64 (bv_unsigned pp + 1)) 8 = Some t8).
    { rewrite <- Ht8. apply rdn_agree. intros j Hj. apply Habove.
      rewrite (u_small (bv_unsigned pp + 1)) by lia. rewrite u_small by lia. lia. }
    apply (ref_read_error_dot sp0 [] model Hvsp Hh Hlazy Hfd2 Hrdr pp (bv_unsigned tid) cn R M
             Rsp Rgp Rtp Rs2 Mstack Mimg Mtid Htidr Mself Mcanary
             Mpagesz Slo t8 ltac:(lia) Hstr Ht8').
  Qed.
End DirTail.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
