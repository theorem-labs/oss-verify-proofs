(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Cfg.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import PropExec MState ITree Nodes Decode.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import Prelim Monad MSafe STree Malloc Prog KInv KStep KStepK JLedger MBound EquivK.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Import TSim MSim.
Import ListNotations.
Import ITree.Exc.
Local Open Scope Z_scope.

Lemma mm_frame_fds_fs mo mo' : mm_frame mo mo' -> m_fds mo' = m_fds mo /\ m_fs mo' = m_fs mo.
Proof. intros (A & B & _). auto. Qed.

Definition mval (a : mmap_ans) : Z := match a with MmErr e => neg_errno e | MmOk x => x end.

Lemma is_err_small x : 0 <= x -> x + 0 <= alloc_ceiling_max -> is_err x = false.
Proof. intros. unfold is_err, TWO64, alloc_ceiling_max in *. apply Z.ltb_ge. lia. Qed.

Lemma brk_grow_facts L pbrk mo req :
  KL L pbrk mo -> event_pre L (EBrk req) -> req <> 0 ->
  let b := bv_unsigned (vm_brk (m_vmmaps mo)) in
  0 < b /\ b mod 4096 = 0 /\ pbrk = b /\ bv_unsigned (vm_start_brk (m_vmmaps mo)) <= b /\ (req = b + PGSZ \/ req = b + 2 * PGSZ)
  /\ req < 2^63.
Proof.
  intros K PRE NZ. cbv zeta. pose proof (kl_start _ _ _ K) as (S1 & S2 & S3 & S4). pose proof (kl_phase _ _ _ K) as PH.
  pose proof (KL_ceil_bracket _ _ _ K) as CL.
  destruct PRE as [[-> _]|[(cur & Hph & ->)|(b0 & l & Hph & Hreg & ->)]]; [congruence| |].
  - rewrite Hph in PH. destruct PH as (Ecur & Eb & Epb & _). rewrite round_up_pg_aligned by (rewrite Ecur; exact S2).
    unfold PGSZ in *. repeat split; try lia; rewrite Eb, Ecur; exact S2.
  - rewrite Hph in PH. destruct PH as (b1 & l1 & Hreg1 & Eb & Epb). rewrite Hreg in Hreg1. injection Hreg1 as <- <-.
    pose proof (kl_brkreg _ _ _ K b0 l Hreg) as (R1 & R2 & R3 & R4 & R5 & _).
    unfold PGSZ in *. repeat split; try lia; rewrite Eb; rewrite Z.add_mod, R2, R4 by lia; reflexivity.
Qed.

Lemma dec_mmap_fixed_cases a rsp (x : fixed_ans) :
  0 <= a <= 2^64 - 4096 ->
  let A := Z_to_bv 64 a in let n := Z_to_bv 64 (page_round_up_Z (bv_unsigned (Z_to_bv 64 PGSZ))) in
  match x with
  | FxKept e => 1 <= e <= 4095 /\ Nodes.strip rsp = efferr e
  | FxDone => Nodes.strip rsp = mkEffectU A [] [] [(A, n)] [] []
  | FxLost e => 1 <= e <= 4095 /\ Nodes.strip rsp = mkEffectU (errno_ret e) [] [] [(A, n)] [] []
  end -> dec_mmap_fixed a PGSZ rsp = Some x.
Proof.
  intros Ha A n H. change (bv_unsigned (Z_to_bv 64 PGSZ)) with PGSZ in n. change (page_round_up_Z PGSZ) with (mmap_len PGSZ) in n.
  destruct rsp as [r ws zs us cs ci]. rewrite strip_mk in H. unfold dec_mmap_fixed.
  destruct x as [e| |e].
  - destruct H as [He H]. unfold efferr, eff0 in H. inversion H; subst. rewrite errno_of_errno_ret by lia. reflexivity.
  - inversion H; subst. subst A n. rewrite !bv_eqb_refl. cbn [andb]. rewrite errno_of_lit by lia. reflexivity.
  - destruct H as [He H]. inversion H; subst. subst A n. rewrite !bv_eqb_refl. cbn [andb]. rewrite errno_of_errno_ret by lia. reflexivity.
Qed.

Lemma munmap_facts L pbrk mo a len : KL L pbrk mo -> event_pre L (EMunmap a len) -> 0 <= a < 2^64 /\ 0 < len < 2^64.
Proof.
  intros K (_ & l & Hin & Hl). pose proof (kl_groups _ _ _ K a l Hin) as (G1 & G2 & G3 & G4 & _).
  pose proof (KL_ceil_lt63 _ _ _ K). pose proof (mmap_len_bound l ltac:(lia)). rewrite KStep.round_up_pg_eq in Hl. fold (mmap_len l) in Hl.
  unfold LEN_MAX in G1. lia.
Qed.

Lemma mprotect_facts L pbrk mo a : KL L pbrk mo -> event_pre L (EMprotect a PGSZ PROT_RW) -> 0 <= a < 2^64.
Proof.
  intros K (_ & _ & _ & b & l & k & Hin & -> & Hk). pose proof (kl_metas _ _ _ K b l k Hin) as (G1 & G2 & G3 & G4 & G5 & G6 & _).
  pose proof (KL_ceil_lt63 _ _ _ K). rewrite KStep.round_up_pg_eq in Hk. fold (mmap_len l) in Hk. unfold PGSZ in *. nia.
Qed.

Lemma dec_mprotect_rw_ok a :
  dec_mprotect_rw a PGSZ (mkEffect (Z_to_bv 64 0) [] [(Z_to_bv 64 a, Z_to_bv 64 (page_round_up_Z (bv_unsigned (Z_to_bv 64 PGSZ))))]) = Some (RgDone true).
Proof.
  unfold dec_mprotect_rw, dec_mprotect. cbn -[bv_unsigned Z_to_bv bv_eqb Z.eqb mmap_len page_round_up_Z PGSZ andb].
  change (bv_unsigned (Z_to_bv 64 0) =? 0) with true. change (bv_unsigned (Z_to_bv 64 PGSZ)) with PGSZ. unfold mmap_len.
  rewrite !bv_eqb_refl. reflexivity.
Qed.

Lemma frame_ok_true : frame_ok (fun _ _ => True).
Proof. intros ? ? ? ? _ _ _ _. exact I. Qed.

Definition frames (s0 s : PState) : Prop := ps_m s = ps_m s0 /\ ps_fa s = ps_fa s0 /\ ps_so s = ps_so s0.
Lemma frames_refl s : frames s s. Proof. repeat split; reflexivity. Qed.
Lemma frames_trans a b c : frames a b -> frames b c -> frames a c.
Proof. intros (A1 & A2 & A3) (B1 & B2 & B3). repeat split; congruence. Qed.
