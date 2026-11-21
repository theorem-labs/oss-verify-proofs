(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: made from Lib/SysExtra.v (triple1_writev2J, triple1_writev1J, triple1_writev01J) and Fw3/Glue3.v (triple_exit_eval): the same lemmas, each asking for the syscall-frame obligation only at a non-allocation call number (BudgetWit.NoAlloc.ok_pframeJ_na, ok_pframe_na), which each discharges from the number it pins (66; 93 or 94). *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (triple1_writev2J_na and triple1_writev1J_na take writev's channel-reader premise, as Lib/SysExtra.v's triple1_writev2J and triple1_writev1J). *)
From Stdlib Require Import ZArith NArith List Lia Bool PArith.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uaccess.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Refusable.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundW
  SymSoundF SymSoundR SymComplete SymCall SymEntail SymExit SymFrame SymBytes Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SysExtra.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.BudgetWit Require Import NoAlloc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section WithSegs.
Variable segs : list Segment.

Lemma triple1_writev2J_na : forall (ok : world -> Prop) (J J' : jpred) S rho ch bs1 bs2 e,
  ok_frameJ segs ok J -> ok_pframeJ_na segs ok J ->
  instr_at segs (ss_pc S) = Some Ecall ->
  reg_sv S 17 = SLit 66 -> reg_sv S 10 = SLit ch -> reg_sv S 12 = SLit 2 ->
  0 < ch < 2 ^ 32 -> (1 <= Z.of_nat (length (bs1 ++ bs2)) <= MAX_RW_COUNT)%Z ->
  sv_below (ss_next S) e = true ->
  (forall rho' tr md k, agree_below (ss_next S) rho rho' ->
     rw rho' (ss_next S) = Z_to_bv 64 (Z.of_nat k) ->
     J rho tr md -> (1 <= k <= length (bs1 ++ bs2))%nat ->
     fd_lookup (m_fds md) (Z_to_bv 64 ch) = Some (FdChannel (Z_to_bv 64 ch))
     /\ J' rho' (tr ++ map (WriteEv (Z_to_bv 64 ch)) (firstn k (bs1 ++ bs2))) md) ->
  (forall tr ms md, smatch_pending segs rho S (tr, mkCfg ms md) -> J rho tr md ->
     exists b1 l1 b2 l2,
       read_u64 (ms_read_byte ms) (eval rho (reg_sv S 11)) = Some b1
       /\ read_u64 (ms_read_byte ms) (eval rho (reg_sv S 11) + 8)%bv = Some l1
       /\ read_u64 (ms_read_byte ms) (eval rho (reg_sv S 11) + 16)%bv = Some b2
       /\ read_u64 (ms_read_byte ms) ((eval rho (reg_sv S 11) + 16) + 8)%bv = Some l2
       /\ read_bytes_map (ms_read_byte ms) b1 l1 = Some bs1
       /\ read_bytes_map (ms_read_byte ms) b2 l2 = Some bs2
       /\ bv_unsigned (eval rho e) = Z.of_nat (length (bs1 ++ bs2))
       /\ (bv_unsigned (eval rho (reg_sv S 11)) + 32 <= TASK_SIZE)%Z
       /\ (bv_unsigned b1 + bv_unsigned l1 <= TASK_SIZE)%Z
       /\ (bv_unsigned b2 + bv_unsigned l2 <= TASK_SIZE)%Z) ->
  (* LPS 08b1429 (in 727298f3): writev's reader gate, as Lib/SysExtra.v's [triple1_writev2J]. *)
  (forall tr ms md, smatch_pending segs rho S (tr, mkCfg ms md) -> J rho tr md -> m_channel_reader md = true) ->
  triple1 segs ok (SPJ segs J S rho)
    (fun w => exists rho', agree_below (ss_next S) rho rho' /\ SPJ segs J' (S_after_write S e) rho' w).
Proof using .
  intros ok J J' S rho ch bs1 bs2 e Hokf Hokp Hi H17 H10 H12 Hch Hlen He HK Hbs Hrdq.
  apply triple1_ecall_detJ; [exact Hokf | exact Hi |].
  intros tr ms md Hsp Hk.
  pose proof (smatch_pending_pending segs _ _ _ _ _ Hsp) as Hp. rewrite H17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pending_halted segs _ _ _ _ _ Hsp) as Hh.
  pose proof (smatch_pending_swf segs _ _ _ _ _ Hsp) as Hwf.
  pose proof (smatch_pending_gpr segs _ _ _ _ _ 0 Hsp ltac:(lia)) as G0. change (10 + Z.of_nat 0) with 10 in G0. rewrite H10 in G0. cbn [eval] in G0.
  pose proof (smatch_pending_gpr segs _ _ _ _ _ 1 Hsp ltac:(lia)) as G1. change (10 + Z.of_nat 1) with 11 in G1.
  pose proof (smatch_pending_gpr segs _ _ _ _ _ 2 Hsp ltac:(lia)) as G2. change (10 + Z.of_nat 2) with 12 in G2. rewrite H12 in G2. cbn [eval] in G2.
  destruct (Hbs tr ms md Hsp Hk) as (b1 & l1 & b2 & l2 & R1 & R2 & R3 & R4 & B1 & B2 & Hev & T0 & T1 & T2).
  pose proof (Hrdq tr ms md Hsp Hk) as Hrdr.
  rewrite <- G1 in R1, R2, R3, R4, T0.
  assert (Hag1 : agree_below (ss_next S) rho (rho_set_rw rho (ss_next S) (Z_to_bv 64 (Z.of_nat 1)))) by (apply agree_below_set_rw; lia).
  destruct (HK _ tr md 1%nat Hag1 (rho_set_rw_at _ _ _) Hk ltac:(lia)) as [Hlk _].
  assert (H66 : bv_unsigned (Z_to_bv 64 66) = 66%Z) by reflexivity.
  assert (Hfd' : fd_lookup (m_fds md) (fd32 (ms_gpr ms 0)) = Some (FdChannel (Z_to_bv 64 ch))).
  { rewrite G0, fd32_lit by lia. exact Hlk. }
  assert (Hch0 : Z_to_bv 64 ch <> Z_to_bv 64 0) by (apply Z_to_bv64_neq; lia).
  split.
  - eapply Hokp; [exact Hk | exact Hp | exact (na_of _ 66 H66 eq_refl) |].
    eapply writev2_only_ok; [exact Hh | exact H66 | exact Hfd' | exact Hch0 | exact G2 | exact R1 | exact R2 | exact R3 | exact R4 | exact B1 | exact B2 | exact T0 | exact T1 | exact T2 | exact Hlen | exact Hrdr].
  - intros w' Hw.
    destruct (wstep_writev2_inv Hp Hh H66 Hfd' Hch0 G2 R1 R2 R3 R4 B1 B2 T0 T1 T2 Hlen Hrdr Hw) as (k & Hk1 & ->).
    assert (Hag : agree_below (ss_next S) rho (rho_set_rw rho (ss_next S) (Z_to_bv 64 (Z.of_nat k)))) by (apply agree_below_set_rw; lia).
    exists (rho_set_rw rho (ss_next S) (Z_to_bv 64 (Z.of_nat k))). split; [exact Hag|].
    split; [|exact (proj2 (HK _ tr md k Hag (rho_set_rw_at _ _ _) Hk Hk1))].
    eapply smatch_after_write; [exact Hsp | exact He | exact Hev | lia].
Qed.

Lemma triple1_writev1J_na : forall (ok : world -> Prop) (J J' : jpred) S rho ch bs1 e,
  ok_frameJ segs ok J -> ok_pframeJ_na segs ok J ->
  instr_at segs (ss_pc S) = Some Ecall ->
  reg_sv S 17 = SLit 66 -> reg_sv S 10 = SLit ch -> reg_sv S 12 = SLit 1 ->
  0 < ch < 2 ^ 32 -> (1 <= Z.of_nat (length bs1) <= MAX_RW_COUNT)%Z ->
  sv_below (ss_next S) e = true ->
  (forall rho' tr md k, agree_below (ss_next S) rho rho' ->
     rw rho' (ss_next S) = Z_to_bv 64 (Z.of_nat k) ->
     J rho tr md -> (1 <= k <= length bs1)%nat ->
     fd_lookup (m_fds md) (Z_to_bv 64 ch) = Some (FdChannel (Z_to_bv 64 ch))
     /\ J' rho' (tr ++ map (WriteEv (Z_to_bv 64 ch)) (firstn k bs1)) md) ->
  (forall tr ms md, smatch_pending segs rho S (tr, mkCfg ms md) -> J rho tr md ->
     exists b1 l1,
       read_u64 (ms_read_byte ms) (eval rho (reg_sv S 11)) = Some b1
       /\ read_u64 (ms_read_byte ms) (eval rho (reg_sv S 11) + 8)%bv = Some l1
       /\ read_bytes_map (ms_read_byte ms) b1 l1 = Some bs1
       /\ bv_unsigned (eval rho e) = Z.of_nat (length bs1)
       /\ (bv_unsigned (eval rho (reg_sv S 11)) + 16 <= TASK_SIZE)%Z
       /\ (bv_unsigned b1 + bv_unsigned l1 <= TASK_SIZE)%Z) ->
  (* LPS 08b1429 (in 727298f3): writev's reader gate, as Lib/SysExtra.v's [triple1_writev1J]. *)
  (forall tr ms md, smatch_pending segs rho S (tr, mkCfg ms md) -> J rho tr md -> m_channel_reader md = true) ->
  triple1 segs ok (SPJ segs J S rho)
    (fun w => exists rho', agree_below (ss_next S) rho rho' /\ SPJ segs J' (S_after_write S e) rho' w).
Proof using .
  intros ok J J' S rho ch bs1 e Hokf Hokp Hi H17 H10 H12 Hch Hlen He HK Hbs Hrdq.
  apply triple1_ecall_detJ; [exact Hokf | exact Hi |].
  intros tr ms md Hsp Hk.
  pose proof (smatch_pending_pending segs _ _ _ _ _ Hsp) as Hp. rewrite H17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pending_halted segs _ _ _ _ _ Hsp) as Hh.
  pose proof (smatch_pending_swf segs _ _ _ _ _ Hsp) as Hwf.
  pose proof (smatch_pending_gpr segs _ _ _ _ _ 0 Hsp ltac:(lia)) as G0. change (10 + Z.of_nat 0) with 10 in G0. rewrite H10 in G0. cbn [eval] in G0.
  pose proof (smatch_pending_gpr segs _ _ _ _ _ 1 Hsp ltac:(lia)) as G1. change (10 + Z.of_nat 1) with 11 in G1.
  pose proof (smatch_pending_gpr segs _ _ _ _ _ 2 Hsp ltac:(lia)) as G2. change (10 + Z.of_nat 2) with 12 in G2. rewrite H12 in G2. cbn [eval] in G2.
  destruct (Hbs tr ms md Hsp Hk) as (b1 & l1 & R1 & R2 & B1 & Hev & T0 & T1).
  pose proof (Hrdq tr ms md Hsp Hk) as Hrdr.
  rewrite <- G1 in R1, R2, T0.
  assert (Hag1 : agree_below (ss_next S) rho (rho_set_rw rho (ss_next S) (Z_to_bv 64 (Z.of_nat 1)))) by (apply agree_below_set_rw; lia).
  destruct (HK _ tr md 1%nat Hag1 (rho_set_rw_at _ _ _) Hk ltac:(lia)) as [Hlk _].
  assert (H66 : bv_unsigned (Z_to_bv 64 66) = 66%Z) by reflexivity.
  assert (Hfd' : fd_lookup (m_fds md) (fd32 (ms_gpr ms 0)) = Some (FdChannel (Z_to_bv 64 ch))).
  { rewrite G0, fd32_lit by lia. exact Hlk. }
  assert (Hch0 : Z_to_bv 64 ch <> Z_to_bv 64 0) by (apply Z_to_bv64_neq; lia).
  split.
  - eapply Hokp; [exact Hk | exact Hp | exact (na_of _ 66 H66 eq_refl) |].
    eapply writev1_only_ok; [exact Hh | exact H66 | exact Hfd' | exact Hch0 | exact G2 | exact R1 | exact R2 | exact B1 | exact T0 | exact T1 | exact Hlen | exact Hrdr].
  - intros w' Hw.
    destruct (wstep_writev1_inv Hp Hh H66 Hfd' Hch0 G2 R1 R2 B1 T0 T1 Hlen Hrdr Hw) as (k & Hk1 & ->).
    assert (Hag : agree_below (ss_next S) rho (rho_set_rw rho (ss_next S) (Z_to_bv 64 (Z.of_nat k)))) by (apply agree_below_set_rw; lia).
    exists (rho_set_rw rho (ss_next S) (Z_to_bv 64 (Z.of_nat k))). split; [exact Hag|].
    split; [|exact (proj2 (HK _ tr md k Hag (rho_set_rw_at _ _ _) Hk Hk1))].
    eapply smatch_after_write; [exact Hsp | exact He | exact Hev | lia].
Qed.

Lemma triple1_writev01J_na : forall (ok : world -> Prop) (J : jpred) S rho ch,
  ok_frameJ segs ok J -> ok_pframeJ_na segs ok J ->
  instr_at segs (ss_pc S) = Some Ecall ->
  reg_sv S 17 = SLit 66 -> reg_sv S 10 = SLit ch -> reg_sv S 12 = SLit 1 ->
  0 < ch < 2 ^ 32 ->
  (forall rho tr md, J rho tr md -> fd_lookup (m_fds md) (Z_to_bv 64 ch) = Some (FdChannel (Z_to_bv 64 ch))) ->
  (forall tr ms md, smatch_pending segs rho S (tr, mkCfg ms md) -> J rho tr md ->
     exists b, read_u64 (ms_read_byte ms) (eval rho (reg_sv S 11)) = Some b
          /\ read_u64 (ms_read_byte ms) (eval rho (reg_sv S 11) + 8)%bv = Some (Z_to_bv 64 0)
          /\ (bv_unsigned (eval rho (reg_sv S 11)) + 16 <= TASK_SIZE)%Z
          /\ (bv_unsigned b <= TASK_SIZE)%Z) ->
  triple1 segs ok (SPJ segs J S rho) (SPJ segs J (S_after S (SLit 0) (ss_objs S) (ss_next S)) rho).
Proof using .
  intros ok J S rho ch Hokf Hokp Hi H17 H10 H12 Hch HJ Hrd.
  apply triple1_ecall_detJ; [exact Hokf | exact Hi |].
  intros tr ms md Hsp Hk.
  pose proof (smatch_pending_pending segs _ _ _ _ _ Hsp) as Hp. rewrite H17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pending_halted segs _ _ _ _ _ Hsp) as Hh.
  pose proof (smatch_pending_gpr segs _ _ _ _ _ 0 Hsp ltac:(lia)) as G0. change (10 + Z.of_nat 0) with 10 in G0. rewrite H10 in G0. cbn [eval] in G0.
  pose proof (smatch_pending_gpr segs _ _ _ _ _ 1 Hsp ltac:(lia)) as G1. change (10 + Z.of_nat 1) with 11 in G1.
  pose proof (smatch_pending_gpr segs _ _ _ _ _ 2 Hsp ltac:(lia)) as G2. change (10 + Z.of_nat 2) with 12 in G2. rewrite H12 in G2. cbn [eval] in G2.
  destruct (Hrd tr ms md Hsp Hk) as (b & R1 & R2 & T0 & T1). rewrite <- G1 in R1, R2, T0.
  assert (H66 : bv_unsigned (Z_to_bv 64 66) = 66%Z) by reflexivity.
  assert (Hfd' : fd_lookup (m_fds md) (fd32 (ms_gpr ms 0)) = Some (FdChannel (Z_to_bv 64 ch))).
  { rewrite G0, fd32_lit by lia. exact (HJ rho tr md Hk). }
  assert (Hch0 : Z_to_bv 64 ch <> Z_to_bv 64 0) by (apply Z_to_bv64_neq; lia).
  split.
  - eapply Hokp; [exact Hk | exact Hp | exact (na_of _ 66 H66 eq_refl) |]. eapply writev01_only_ok; [exact Hh | exact H66 | exact Hfd' | exact Hch0 | exact G2 | exact R1 | exact R2 | exact T0 | exact T1].
  - intros w' Hw. rewrite (wstep_writev01_inv segs tr ms md _ _ b w' Hp Hh H66 Hfd' Hch0 G2 R1 R2 T0 T1 Hw).
    split; [|exact Hk]. change (SLit 0) with (SLit (bv_unsigned (Z_to_bv 64 0))).
    eapply smatch_after_ret_lit; [exact Hsp | exact Hh].
Qed.

Lemma triple_exit_eval_na : forall (ok : world -> Prop) (Spec : list event -> Prop)
    (K : list event -> Model -> Prop) (S : sstate) (rho : valuation) (c : Z),
  ok_frame segs ok K -> ok_pframe_na segs ok K -> ok_halted ok Spec ->
  instr_at segs (ss_pc S) = Some Ecall ->
  (reg_sv S 17 = SLit 94 \/ reg_sv S 17 = SLit 93) ->
  Z.modulo (bv_unsigned (eval rho (reg_sv S 10))) 256 = c ->
  (forall tr md, K tr md -> Spec (tr ++ [ExitEv (Z_to_bv 64 c) (m_fs md)])) ->
  triple segs ok (SP segs K S rho) (fun _ => False).
Proof using .
  intros ok Spec K S rho c Hokf Hokp Hokh Hi H17 Hc Hspec.
  apply (@triple_seq segs ok _ (exited_world segs K S rho)).
  - apply triple1_triple. eapply triple1_ecall_det; [exact Hokf | exact Hi |].
    intros tr ms md Hsp Hk.
    pose proof (smatch_pending_pending segs _ _ _ _ _ Hsp) as Hp.
    pose proof (smatch_pending_halted segs _ _ _ _ _ Hsp) as Hh.
    assert (Hno : bv_unsigned (eval rho (reg_sv S 17)) = 93 \/ bv_unsigned (eval rho (reg_sv S 17)) = 94).
    { destruct H17 as [-> | ->]; cbn; [right | left]; reflexivity. }
    split.
    + eapply Hokp; [exact Hk | exact Hp | exact (na_exit _ Hno) |]. apply exit_only_ok. exact Hno.
    + intros w' Hw. rewrite (wstep_exit_inv Hp (model_idle_halted Hh) Hno Hw).
      exists tr, ms, md. split; [exact Hk|]. split; [exact Hsp | reflexivity].
  - apply triple_halt. intros w' (tr & ms & md & Hk & Hsp & ->).
    split.
    + eapply Hokh; [|apply exited_halted].
      exists (tr ++ [ExitEv (Z_to_bv 64 c) (m_fs md)]). split; [exact (Hspec tr md Hk)|].
      rewrite (exit_code_eval segs rho S tr ms md c Hsp Hc). apply is_prefix_refl.
    + intros w'' Hw'. exact (wstep_exited_none Hw').
Qed.

End WithSegs.
