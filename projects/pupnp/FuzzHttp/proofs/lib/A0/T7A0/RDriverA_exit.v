(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Agree Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts Globals IcptA0 AllocA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import InitStack EntrySecret.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import Prelim STree Monad Stdio Driver Prog.
From OSSVerify.pupnp.FuzzHttp.images Require Import Asan.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.T7 Require Import A0Prog.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.T7A0 Require Import ShadowKit GlobalsShadow Stdio_base Stdio_iface F_stdio_exit Exit RDriverA_kit RDriverA_ctx RDriverA_main.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac rpc := apply ret_pc_even; [lia| reflexivity].

Lemma aget_set : forall (s : ASt) so, aget_so (aset_so so s) = so. Proof. reflexivity. Qed.
Lemma aset_set : forall (s : ASt) so so', aset_so so' (aset_so so s) = aset_so so' s. Proof. reflexivity. Qed.
Lemma aset_get : forall (s : ASt), aset_so (aget_so s) s = s. Proof. reflexivity. Qed.

Section EXITS.
  Context {HC : HasCeiling}.
  Variables (sp0 : word) (argv envp : list (list byte)) (TID : Z).
  Notation usp0 := (bv_unsigned sp0).
  Notation gpv := (Z_to_bv 64 0x10800).
  Notation tpv := (Z_to_bv 64 RATPA).
  Hypothesis VSP : valid_sp sp0.
  Hypothesis CEIL : alloc_ceiling = LO sp0.
  Hypothesis HT : 0 < TID < 2^31.

  #[using="VSP CEIL"] Lemma sp_factsE : 0x7fff80000000 <= usp0 <= 0x800000000000 /\ usp0 mod 16 = 0 /\ alloc_ceiling = LO sp0 /\ LO sp0 + 8388608 = usp0.
  Proof. destruct VSP as (A & B & C). rewrite CEIL. unfold LO, sp_window_lo, sp_window_hi, stack_max_size in *. repeat split; lia. Qed.

  Definition rat_exitA (code : Z) (so : stdout_st) (ms : machine_state) : Prop :=
    exists (ra t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (SP lo : Z) (f0 : byte) (p3 p4 : list byte) (dso : word) (cf : byte) (guard : word)
           (cdt thr sec : byte) (tm1 : word),
      ms = MS (mkR ra (Z_to_bv 64 SP) gpv tpv t0 t1 t2 s0 s1 (Z_to_bv 64 code) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x94a84) fc None m (seg_rom asegs)
      /\ 0 <= SP <= 2^47 /\ alloc_ceiling <= lo /\ lo <= SP - 48 - A0_RT_STACK
      /\ stk asegs m lo SP
      /\ rw_cells asegs m 0x5e68c8 [C4 (Z_to_bv 64 TID)]
      /\ rw_cells asegs m 0x606be0 [C4 z64]
      /\ exit_atx f0 p3 p4 m
      /\ rw_cells asegs m 0x1457a0 [C1 (Z_to_bv 8 0)]
      /\ rw_cells asegs m 0x606c00 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1]
      /\ rw_cells asegs m 0xaad98 [C8 (Z_to_bv 64 0xa9ae8); C8 (Z_to_bv 64 0xa9ad8)]
      /\ rw_cells asegs m 0xa9ad8 [C8 (Z_to_bv 64 0x8b360); C8 (Z_to_bv 64 0x324d0)]
      /\ rw_cells asegs m 0xb0290 [C1 cf]
      /\ rw_cells asegs m 0xaa0a0 [C8 (Z_to_bv 64 0x94968); C8 z64]
      /\ rw_cells asegs m 0xabde0 [C8 dso]
      /\ asan_env asegs m /\ globals_shadow m
      /\ rw_cells asegs m 0x607068 [C8 z64]
      /\ rw_cells asegs m 0xaed90 [C8 (Z_to_bv 64 0xaeca8)] /\ stdin_file m
      /\ rw_cells asegs m 0xaeca0 [C8 (Z_to_bv 64 RSTDOUT)] /\ rw_cells asegs m 0xaebb0 [C8 (Z_to_bv 64 RSTDERR)]
      /\ stdout_file m so /\ stderr_file m
      /\ rw_cells asegs m 0xaad68 [C8 (Z_to_bv 64 0x6069b0)] /\ rw_cells asegs m 0x6069b0 [C8 guard]
      /\ mem_inv asegs m.

  Definition exit_k_stmtA : Prop :=
    forall (A : Type) (code : Z) (so : ASt) (Q : A -> ASt -> machine_state -> Prop) (ms : machine_state),
      rat_exitA code so ms -> implM asegs (exit_k ioA (A:=A) code) so Q ms.

  Section WithDtor.
    Hypothesis DT : asan_dtor_stmt.

    #[using="HT DT"] Theorem exit_k_proofA : exit_k_stmtA.
    Proof.
      unfold exit_k_stmtA. intros A code so Q ms RX.
      destruct RX as (ra & t0 & t1 & t2 & s0 & s1 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s2 & s3 & s4 & s5 & s6 & s7 & s8 & s9 & s10 & s11 & t3 & t4 & t5 & t6
                      & F & fc & m & SP & lo & f0 & p3 & p4 & dso & cf & guard & cdt & thr & sec & tm1
                      & -> & HSP & CLO & LO & ST & TIDc & EXL & ATXS & COV & LCH & GF & FA & CF & GCX & DSO & ENV & GSH & OFL & SIU & SIF & SOU & SEU & SOF & SEF & GG & GU & MI).
      unfold exit_k. eapply implM_bind with (Q1 := fun _ _ _ => False).
      - eapply (Exit.exit_spec aget_so aset_so DT (F_stdio_exit.stdio_exit_proof aget_so aset_so aget_set aset_set aset_get));
          rewrite ?unsigned_lit by lia;
          first [exact ST| exact TIDc| exact EXL| exact ATXS| exact COV| exact LCH| exact GF| exact FA| exact CF| exact GCX| exact DSO| exact ENV| exact GSH
                | exact OFL| exact SIU| exact SIF| exact SOU| exact SEU| exact SOF| exact SEF| exact GG| exact GU| exact MI| reflexivity| exact HT| lia].
      - intros e s' ms' X. destruct X.
    Qed.
  End WithDtor.

  #[using="Type"] Lemma rat_exitA_intro : forall (code : Z) (so : stdout_st) (SP : Z) (ra t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (guard : word),
    stk asegs m lo SP -> lo <= SP - 48 - A0_RT_STACK -> alloc_ceiling <= lo -> 0 <= SP <= 2^47 ->
    EXITC TID m -> wr_at asegs m 0xb0290 1 -> asan_env asegs m -> globals_shadow m ->
    rw_cells asegs m 0xaad68 [C8 (Z_to_bv 64 0x6069b0)] -> rw_cells asegs m 0x6069b0 [C8 guard] ->
    stdout_file m so -> stderr_file m -> stdin_file m -> mem_inv asegs m ->
    rat_exitA code so (MS (mkR ra (Z_to_bv 64 SP) gpv tpv t0 t1 t2 s0 s1 (Z_to_bv 64 code) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                           F (Z_to_bv 64 0x94a84) fc None m (seg_rom asegs)).
  Proof.
    intros until guard. intros ST LOS CLO SPR (TD & EXL & (p3 & p4 & ATX) & ATA & COV & (cdt & thr & sec & tm1 & LCH) & GF & FA & GCX & (dso & DSO) & OFL & SIU & SOU & SEU) CRT ENV GSH GG GU SOF SEF SIF MI.
    destruct (crt_cell_any m CRT) as [cf CF].
    unfold rat_exitA. do 27 eexists. exists F, fc, m, SP, lo, (Z_to_bv 8 0), p3, p4, dso, cf, guard, cdt, thr, sec, tm1.
    split; [reflexivity|]. repeat (split; [first [assumption | lia | (left; split; assumption)]|]). exact MI.
  Qed.

  #[using="Type"] Lemma rat_exitA_intro2 : forall (code : Z) (so : stdout_st) (SP : Z) (ra t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (guard : word),
    stk asegs m lo SP -> lo <= SP - 48 - A0_RT_STACK -> alloc_ceiling <= lo -> 0 <= SP <= 2^47 ->
    EXITC2 TID m -> wr_at asegs m 0xb0290 1 -> asan_env asegs m -> globals_shadow m ->
    rw_cells asegs m 0xaad68 [C8 (Z_to_bv 64 0x6069b0)] -> rw_cells asegs m 0x6069b0 [C8 guard] ->
    stdout_file m so -> stderr_file m -> stdin_file m -> mem_inv asegs m ->
    rat_exitA code so (MS (mkR ra (Z_to_bv 64 SP) gpv tpv t0 t1 t2 s0 s1 (Z_to_bv 64 code) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                           F (Z_to_bv 64 0x94a84) fc None m (seg_rom asegs)).
  Proof.
    intros until guard. intros ST LOS CLO SPR (TD & EXL & (p3 & p4 & ATX) & ATA & COV & (cdt & thr & sec & tm1 & LCH) & GF & FA & GCX & (dso & DSO) & OFL & SIU & SOU & SEU & ICB) CRT ENV GSH GG GU SOF SEF SIF MI.
    destruct (crt_cell_any m CRT) as [cf CF].
    unfold rat_exitA. do 27 eexists. exists F, fc, m, SP, lo, (Z_to_bv 8 0), p3, p4, dso, cf, guard, cdt, thr, sec, tm1.
    split; [reflexivity|]. repeat (split; [first [assumption | lia | (right; split; [assumption| split; assumption])]|]). exact MI.
  Qed.

  #[using="VSP CEIL"] Lemma main_return : forall (code : Z) (so : stdout_st) (x1 t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (pad : list byte) (s7v s6v s5v s4v : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (guard : word),
    MFRAME sp0 argv m pad s7v s6v s5v s4v ->
    stk asegs m (LO sp0) (usp0 + -128) ->
    EXITC TID m -> wr_at asegs m 0xb0290 1 -> asan_env asegs m -> globals_shadow m ->
    rw_cells asegs m 0xaad68 [C8 (Z_to_bv 64 0x6069b0)] -> rw_cells asegs m 0x6069b0 [C8 guard] ->
    stdout_file m so -> stderr_file m -> stdin_file m -> mem_inv asegs m ->
    evt asegs (rat_exitA code so)
      (MS (mkR x1 (Z_to_bv 64 (usp0 + -128)) gpv tpv t0 t1 t2 (Z_to_bv 64 code) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x86270) fc None m (seg_rom asegs)).
  Proof.
    intros until guard. intros FR ST EX CRT ENV GSH GG GU SOF SEF SIF MI. pose proof sp_factsE as SF. unfold LO in *. unfold MFRAME in FR.
    do 11 zstep. release_frame FR ST (usp0 + -48). zstep.
    replace (ret_pc (Z_to_bv 64 0x94384)) with (Z_to_bv 64 0x94384) by (symmetry; rpc).
    zstep.
    apply evt_done. eapply rat_exitA_intro; [exact ST| unfold A0_RT_STACK; lia| lia| lia| exact EX| exact CRT| exact ENV| exact GSH| exact GG| exact GU| exact SOF| exact SEF| exact SIF| exact MI].
  Qed.

  #[using="VSP CEIL"] Lemma main_return2 : forall (code : Z) (so : stdout_st) (x1 t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (pad : list byte) (s7v s6v s5v s4v : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (guard : word),
    MFRAME sp0 argv m pad s7v s6v s5v s4v ->
    stk asegs m (LO sp0) (usp0 + -128) ->
    EXITC2 TID m -> wr_at asegs m 0xb0290 1 -> asan_env asegs m -> globals_shadow m ->
    rw_cells asegs m 0xaad68 [C8 (Z_to_bv 64 0x6069b0)] -> rw_cells asegs m 0x6069b0 [C8 guard] ->
    stdout_file m so -> stderr_file m -> stdin_file m -> mem_inv asegs m ->
    evt asegs (rat_exitA code so)
      (MS (mkR x1 (Z_to_bv 64 (usp0 + -128)) gpv tpv t0 t1 t2 (Z_to_bv 64 code) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x86270) fc None m (seg_rom asegs)).
  Proof.
    intros until guard. intros FR ST EX CRT ENV GSH GG GU SOF SEF SIF MI. pose proof sp_factsE as SF. unfold LO in *. unfold MFRAME in FR.
    do 11 zstep. release_frame FR ST (usp0 + -48). zstep.
    replace (ret_pc (Z_to_bv 64 0x94384)) with (Z_to_bv 64 0x94384) by (symmetry; rpc).
    zstep.
    apply evt_done. eapply rat_exitA_intro2; [exact ST| unfold A0_RT_STACK; lia| lia| lia| exact EX| exact CRT| exact ENV| exact GSH| exact GG| exact GU| exact SOF| exact SEF| exact SIF| exact MI].
  Qed.

  #[using="VSP CEIL"] Lemma exit2_tail : forall (so : stdout_st) (x1 t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (guard : word),
    stk asegs m (LO sp0) (usp0 + -128) ->
    EXITC TID m -> wr_at asegs m 0xb0290 1 -> asan_env asegs m -> globals_shadow m ->
    rw_cells asegs m 0xaad68 [C8 (Z_to_bv 64 0x6069b0)] -> rw_cells asegs m 0x6069b0 [C8 guard] ->
    stdout_file m so -> stderr_file m -> stdin_file m -> mem_inv asegs m ->
    evt asegs (rat_exitA 2 so)
      (MS (mkR x1 (Z_to_bv 64 (usp0 + -128)) gpv tpv t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x862fc) fc None m (seg_rom asegs)).
  Proof.
    intros until guard. intros ST EX CRT ENV GSH GG GU SOF SEF SIF MI. pose proof sp_factsE as SF. unfold LO in *.
    zstep. zstep.
    apply evt_done. eapply rat_exitA_intro; [exact ST| unfold A0_RT_STACK; lia| lia| lia| exact EX| exact CRT| exact ENV| exact GSH| exact GG| exact GU| exact SOF| exact SEF| exact SIF| exact MI].
  Qed.
End EXITS.
