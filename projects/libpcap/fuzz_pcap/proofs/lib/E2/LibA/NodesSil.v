(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Exec ITree Nodes PlacementSearch.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import AcctCore ExecF ModelX MmXfer.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ITreeA NodesA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AllocSim2__Common.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Prelude Dispatch.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)


Lemma check_syscall_madvise : forall i eff m, bv_unsigned (in_sysno i) = 233 ->
  check_syscall i eff m = Madvise.check_madvise (in_arg i 0) (in_arg i 1) (int32 (in_arg i 2)) eff m.
Proof.
  intros i eff m H. unfold check_syscall. rewrite H.
  change (lookup_ca checked_table 233) with (Some arm_madvise). cbv beta iota. apply ca_check_arm_madvise.
Qed.

(* [comment removed for export] *)
Lemma region_free_sub : forall l (b sz a n : word),
  region_free l b sz = true ->
  bv_unsigned b <= bv_unsigned a -> bv_unsigned a + bv_unsigned n <= bv_unsigned b + bv_unsigned sz ->
  region_free l a n = true.
Proof.
  intros l b sz a n H L1 L2. apply region_free_intro. intros x s Hin.
  pose proof (region_free_In _ _ _ _ _ H Hin) as O. unfold iv_overlap in *.
  apply andb_false_iff in O. apply andb_false_iff.
  destruct O as [O|O]; apply Z.ltb_ge in O; [left|right]; apply Z.ltb_ge; lia.
Qed.

Lemma map_contains_In : forall maps (b sz a n : word),
  In (b, sz) maps -> bv_unsigned b <= bv_unsigned a -> bv_unsigned a + bv_unsigned n <= bv_unsigned b + bv_unsigned sz ->
  map_contains maps a n = true.
Proof.
  intros maps b sz a n Hin L1 L2. unfold map_contains. apply existsb_exists. exists (b, sz). split; [exact Hin|].
  cbn [fst snd]. apply andb_true_intro. split; apply Z.leb_le; lia.
Qed.

(* [comment removed for export] *)
Lemma materialize_nil : forall m, materialize_model_accesses m [] = Some m.
Proof.
  intros m. unfold materialize_model_accesses, materialize_accesses, newly_materialized_pages. cbn.
  f_equal. apply MX_mat.
Qed.

Section Sil.
Variable segs : list Segment.
Variable NMAX : nat.
Variable SHM : list (Z * Z).

#[using="Type"] Lemma madvise_gate : forall mo addr len,
  shinv SHM mo -> 0 <= addr -> 0 < len -> addr + page_round_up_Z len < 2^64 ->
  Exists (fun e => fst e <= addr /\ addr + page_round_up_Z len <= fst e + snd e) SHM ->
  madvise_dontneed_ok (m_vmmaps mo) (Z_to_bv 64 addr) (Z_to_bv 64 (page_round_up_Z len)) = true.
Proof.
  intros mo addr len SH A0 L0 HI EX. apply Exists_exists in EX as (e & Hin & E1 & E2).
  pose proof (proj1 (Forall_forall _ _) SH e Hin) as (B0 & S0 & BS & HM & HN & HR).
  pose proof (page_round_up_Z_ge len) as RU.
  assert (U1 : bv_unsigned (Z_to_bv 64 addr) = addr) by (apply unsigned_lit; lia).
  assert (U2 : bv_unsigned (Z_to_bv 64 (page_round_up_Z len)) = page_round_up_Z len) by (apply unsigned_lit; lia).
  assert (U3 : bv_unsigned (Z_to_bv 64 (fst e)) = fst e) by (apply unsigned_lit; lia).
  assert (U4 : bv_unsigned (Z_to_bv 64 (snd e)) = snd e) by (apply unsigned_lit; lia).
  unfold madvise_dontneed_ok. apply andb_true_intro. split; [apply andb_true_intro; split|].
  - eapply region_free_sub; [exact HR| |]; rewrite ?U1, ?U2, ?U3, ?U4; lia.
  - eapply map_contains_In; [exact HM| |]; rewrite ?U1, ?U2, ?U3, ?U4; lia.
  - eapply region_free_sub; [exact HN| |]; rewrite ?U1, ?U2, ?U3, ?U4; lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma madvise_check : forall A ms mo mo_ addr len eff,
  ms_svc_pending ms = Some (Z_to_bv 64 233) ->
  areg ms 10 = Z_to_bv 64 addr -> areg ms 11 = Z_to_bv 64 len ->
  bv_unsigned (int32 (areg ms 12)) = MADV_DONTNEED ->
  0 <= addr -> addr mod page_size = 0 -> 0 < len < 2^64 -> addr + page_round_up_Z len < 2^64 ->
  Exists (fun e => fst e <= addr /\ addr + page_round_up_Z len <= fst e + snd e) SHM ->
  minvA SHM mo -> mrel A mo mo_ ->
  check_syscall (sys_input segs ms (Z_to_bv 64 233)) eff mo_ =
  match eff with
  | mkEffectU r [] zs [] [] [] =>
      if w_is0 r && listNN_eqb zs [(Z_to_bv 64 addr, Z_to_bv 64 (page_round_up_Z len))]
      then CheckOk (madvise_dontneed_next mo_ (Z_to_bv 64 addr) (Z_to_bv 64 (page_round_up_Z len))) []
      else CheckReject
  | _ => CheckReject
  end.
Proof.
  intros A ms mo mo_ addr len eff Hsvc Ha0 Ha1 Hadv A0 AL [L0 L1] HI EX Hminv MR.
  rewrite check_syscall_madvise by (rewrite in_sysno_si; reflexivity).
  rewrite in_a0_si, in_a1_si, in_a2_si, Ha0, Ha1. unfold Madvise.check_madvise.
  assert (U1 : bv_unsigned (Z_to_bv 64 addr) = addr) by (apply unsigned_lit; pose proof (page_round_up_Z_ge len); lia).
  assert (U2 : bv_unsigned (Z_to_bv 64 len) = len) by (apply unsigned_lit; lia).
  rewrite U1, U2. rewrite (proj2 (Z.eqb_eq _ _) AL). cbn [negb].
  unfold madvise_dontneed_b. rewrite Hadv, Z.eqb_refl. cbn [negb].
  rewrite w_is0_lit by lia. rewrite (proj2 (Z.eqb_neq _ _)) by lia.
  destruct (Z.leb_spec two_pow_64 (addr + page_round_up_Z len)) as [C|_]; [unfold two_pow_64 in C; lia|].
  cbv zeta.
  pose proof (same_but_mat_frame _ _ (proj1 MR)) as (_ & VMM & _). rewrite VMM.
  rewrite (madvise_gate mo addr len (proj2 (proj2 Hminv)) A0 L0 HI EX). reflexivity.
Qed.

#[using="Type"] Lemma madv_next_mrel : forall A mo mo_ a n, mrel A mo mo_ -> mrel A mo (madvise_dontneed_next mo_ a n).
Proof.
  intros A mo mo_ a n (SB & CAN & ND & AL). unfold madvise_dontneed_next.
  pose proof (same_but_mat_frame _ _ SB) as (_ & _ & LZ & _).
  split; [| split; [exact CAN| split]].
  - unfold same_but_mat in *. rewrite SB. destruct mo as [fd [mp lzz mt] io fs pr lm tm]. reflexivity.
  - cbn. apply NoDup_filter. exact ND.
  - intros p Hp. cbn in Hp. apply filter_In in Hp as [Hp _]. apply AL, Hp.
Qed.

#[using="Type"] Theorem silA_sound : sil_soundA segs (silA SHM) (minvA SHM) NMAX.
Proof.
  intros RNG A ms ms' mo mo_ (addr & len & Hsvc & Ha0 & Ha1 & Hadv & A0 & AL & LL & HI & EX & ->) Hh Hminv FOK MR INV.
  set (a := Z_to_bv 64 addr). set (nn := Z_to_bv 64 (page_round_up_Z len)).
  set (nx := madvise_dontneed_next mo_ a nn).
  pose proof (fun eff => madvise_check A ms mo mo_ addr len eff Hsvc Ha0 Ha1 Hadv A0 AL LL HI EX Hminv MR) as CHK.
  fold a nn nx in CHK.
  assert (Hh_ : m_halted mo_ = None) by (rewrite (mrel_halted _ _ _ MR); exact Hh).
  assert (Hnospur : forall M eff, ~ spurious_refusal_cfg CFG (sys_input segs ms (Z_to_bv 64 233)) M eff).
  { intros M eff. apply spurious_refusal_family_on. rewrite injected_family_off_CFG, in_sysno_si. reflexivity. }
  assert (SPEC : syscall_spec (sys_input segs ms (Z_to_bv 64 233)) mo_ (Ok (madv_rsp addr len) nx [])).
  { apply check_syscall_ok_iff. rewrite CHK. unfold madv_rsp. fold a nn.
    change (w_is0 (Z_to_bv 64 0)) with true. rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity. }
  exists nx. split; [| apply madv_next_mrel; exact MR].
  split.
  - intros _. unfold nret.
    eapply (sstep_cfg_syscall segs CFG ms mo_ (Z_to_bv 64 233) (madv_rsp addr len) nx nx []);
      [exact Hh_ | exact Hsvc | exact SPEC | apply Hnospur | exact Hh_ | ].
    unfold madv_rsp. apply materialize_nil.
  - intros e st Hss. exists tt.
    destruct (sstep_svc_inv segs _ _ _ _ _ Hsvc Hss)
      as [(eff & moX & mo'' & Hsp & Hns & Hh' & Hmat & ->)
         | [(eff & moX & evs0 & Hsp & Hns & Hh' & Hmat & -> & ->)
         | [(eff & moX & evs0 & code & Hsp & Hh' & -> & ->)
         | [(eff & moX & evs0 & sig & Hsp & Hk & -> & ->) | (Hsp & -> & ->)]]]].
    all: try (apply check_syscall_ok_iff in Hsp; rewrite CHK in Hsp;
              destruct eff as [r ws zs us cs ci]; destruct ws; [|discriminate Hsp]; destruct us; [|discriminate Hsp];
              destruct cs; [|discriminate Hsp]; destruct ci; [|discriminate Hsp];
              destruct (w_is0 r && listNN_eqb zs [(a, nn)]) eqn:E; [|discriminate Hsp];
              injection Hsp as <- <-; apply andb_prop in E as [E1 E2];
              apply listNN_eqb_eq in E2; subst zs;
              assert (r = Z_to_bv 64 0) by (apply bv_eqb_eq; exact E1); subst r).
    + cbn [syscall_effect_accesses eff_copyins eff_writes write_accesses app] in Hmat.
      rewrite materialize_nil in Hmat. injection Hmat as <-. split; reflexivity.
    + exfalso. cbn [syscall_effect_accesses eff_copyins eff_writes write_accesses app] in Hmat.
      rewrite materialize_nil in Hmat. discriminate.
    + exfalso. unfold nx, madvise_dontneed_next in Hh'. change (m_halted (with_vm_backing _ _ mo_)) with (m_halted mo_) in Hh'. congruence.
    + exfalso. unfold nx, madvise_dontneed_next in Hk. change (m_killed (with_vm_backing _ _ mo_)) with (m_killed mo_) in Hk.
      pose proof (m_killed_of_m_halted_none _ Hh_). congruence.
    + exfalso. apply check_syscall_err_iff with (eff := madv_rsp addr len) in Hsp. rewrite CHK in Hsp.
      unfold madv_rsp in Hsp. fold a nn in Hsp. change (w_is0 (Z_to_bv 64 0)) with true in Hsp.
      rewrite (proj2 (listNN_eqb_eq _ _) eq_refl) in Hsp. discriminate.
Qed.

End Sil.
