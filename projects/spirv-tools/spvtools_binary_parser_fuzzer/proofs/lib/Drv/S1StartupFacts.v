(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import Amb StartupTac ArgvEnv RefLayout.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require Import Overlay RunsLib S1BootDefs S1Boot S1StartInit S1CxxTable S1Start S1CxxLink.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition D_main_cells : list (Z * nat) :=
  D8_cells ++ map (fun r : run => (fst r, length (snd r))) D_CXX.

Definition range_disjoint_b (a : Z) (n : nat) (c : Z * nat) : bool :=
  ((a + Z.of_nat n <=? fst c) || (fst c + Z.of_nat (snd c) <=? a))%Z.

Definition runs_clearZ (rs : list run) (lo hi : Z) : bool :=
  forallb (fun r : run => (hi <=? fst r) || (fst r + Z.of_nat (length (snd r)) <=? lo))%Z rs.

Definition D_main_missb (a : Z) (n : nat) : bool :=
  let hi := (a + Z.of_nat n)%Z in
  (runs_clearZ D_CXX a hi && range_miss D8_cells a hi && (0 <=? a) && (hi <=? 0x100000000))%Z%bool.

Lemma missb_parts : forall a n, D_main_missb a n = true ->
  runs_clear D_CXX a n = true /\ range_miss D8_cells a (a + Z.of_nat n) = true
  /\ (0 <= a)%Z /\ (a + Z.of_nat n <= 0x100000000)%Z.
Proof.
  intros a n H. unfold D_main_missb in H. cbv zeta in H.
  change (runs_clearZ D_CXX a (a + Z.of_nat n)) with (runs_clear D_CXX a n) in H.
  apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Z.leb_le in H3. apply Z.leb_le in H4. repeat split; assumption.
Qed.

Lemma runs_clear_sub : forall rs lo n i k, runs_clear rs lo n = true ->
  (lo <= i)%Z -> (i + Z.of_nat k <= lo + Z.of_nat n)%Z -> runs_clear rs i k = true.
Proof.
  intros rs lo n i k H Hlo Hhi. unfold runs_clear in *. apply forallb_forall. intros r Hr.
  pose proof (proj1 (forallb_forall _ _) H r Hr) as Hb. apply orb_true_iff in Hb. apply orb_true_iff.
  rewrite !Z.leb_le in *. lia.
Qed.

Lemma range_miss_sub : forall cells lo hi lo' hi', range_miss cells lo hi = true ->
  (lo <= lo')%Z -> (hi' <= hi)%Z -> (hi' <= 2 ^ 64)%Z -> range_miss cells lo' hi' = true.
Proof.
  intros cells lo hi lo' hi' H H1 H2 H3. unfold range_miss in *.
  apply andb_prop in H as [H Hc]. apply andb_prop in H as [Ha Hb]. apply Z.leb_le in Ha. apply Z.leb_le in Hb.
  apply andb_true_intro; split; [apply andb_true_intro; split; apply Z.leb_le; lia|].
  apply forallb_forall. intros c Hin. pose proof (proj1 (forallb_forall _ _) Hc c Hin) as Hx.
  apply orb_true_iff in Hx. apply orb_true_iff. rewrite !Z.leb_le in *. lia.
Qed.

Lemma missb_sub : forall lo n i k, D_main_missb lo n = true ->
  (lo <= i)%Z -> (i + Z.of_nat k <= lo + Z.of_nat n)%Z -> D_main_missb i k = true.
Proof.
  intros lo n i k H Hlo Hhi. destruct (missb_parts lo n H) as (H1 & H2 & H3 & H4).
  unfold D_main_missb. cbv zeta. change (runs_clearZ D_CXX i (i + Z.of_nat k)) with (runs_clear D_CXX i k).
  rewrite (runs_clear_sub _ lo n i k H1) by lia.
  rewrite (range_miss_sub _ _ _ i (i + Z.of_nat k) H2) by lia.
  rewrite (proj2 (Z.leb_le 0 i)) by lia. rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity.
Qed.

Section Facts.
  Context {AMB : Amb}.
  Variable sp0 : word.
  Variables av ev : list (list byte).
  Variable tid : word.
  Variable rdraw : EntryDraw.
  Hypothesis Hva : valid_argv av.
  Hypothesis Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z.
  Hypothesis Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z.

  Let D := D_main1 sp0 av ev a_hwcap tid rdraw.

  Lemma len_av : (1 <= Z.of_nat (length av) <= 1024)%Z.
  Proof. destruct Hva as [[H1 H2] _]. lia. Qed.

  Lemma D_main_none : forall (i : Z), D_main_missb i 1 = true -> D (Z_to_bv 64 i) = None.
  Proof.
    intros i Hb. destruct (missb_parts i 1 Hb) as (H1 & H2 & H3 & H4). subst D.
    cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in H2, H4.
    rewrite (D_main1_clear_at sp0 av ev a_hwcap tid rdraw i 1 i H1) by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
    apply (D8_none sp0 rdraw av ev a_hwcap Hva). eapply range_miss_pt; [exact H2 | lia].
  Qed.

  Ltac via_chain :=
    subst D; rewrite D_main1_clear by (first [vm_compute; reflexivity | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia]);
    pose proof (u64_range tid); pose proof len_av;
    unfold D8, D_libc; peel.

  Lemma D_main_tid : forall segs,
    rdn segs D (Z_to_bv 64 0x100610) 4 = Some (word_to_le_bytes 4 tid).
  Proof.
    intros segs. via_chain.
    pose proof (rdn_wbytes_hit segs (word_to_le_bytes 4 tid)) as Hh.
    rewrite length_N_to_le_bytes in Hh. apply Hh. unorm; lia.
  Qed.

  Lemma D_main_guard : forall segs,
    rdn segs D (Z_to_bv 64 0x120928) 8 = Some (word_to_le_bytes 8 (canary rdraw)).
  Proof. intros segs. via_chain. apply rd_guard. Qed.

  Lemma D_main_pagesize : forall segs,
    rdn segs D (Z_to_bv 64 0x120978) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 4096)).
  Proof. intros segs. via_chain. apply rdn_wbytes_hit8. unorm; lia. Qed.

  Lemma D_main_self : forall segs,
    rdn segs D (Z_to_bv 64 0x1005f0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x1005f0)).
  Proof. intros segs. via_chain. apply rdn_wbytes_hit8. unorm; lia. Qed.

  Lemma D_main_canary : forall segs,
    rdn segs D (Z_to_bv 64 0x1006a8) 8 = Some (word_to_le_bytes 8 (canary rdraw)).
  Proof. intros segs. via_chain. apply rdn_wbytes_hit8. unorm; lia. Qed.

  Lemma D_main_auxv : forall segs,
    rdn segs D (Z_to_bv 64 0x120950) 8 = Some (word_to_le_bytes 8 (auxv_w sp0 av ev)).
  Proof. intros segs. via_chain. unfold auxv_w. apply rdn_wbytes_hit8. unorm; lia. Qed.

  Lemma D_main_cdt : forall segs,
    rdn segs D (Z_to_bv 64 0x120948) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 1)).
  Proof.
    intros segs. via_chain.
    pose proof (rdn_wbytes_hit segs [Z_to_bv 8 1]) as Hh. cbn [length] in Hh.
    change (word_to_le_bytes 1 (Z_to_bv 64 1)) with [Z_to_bv 8 1 : byte]. apply Hh. unorm; lia.
  Qed.
  Lemma D_main_tlssize : forall segs,
    rdn segs D (Z_to_bv 64 0x120960) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 224)).
  Proof. intros segs. via_chain. apply rdn_wbytes_hit8. unorm; lia. Qed.
  Lemma D_main_tlsalign : forall segs,
    rdn segs D (Z_to_bv 64 0x120968) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 8)).
  Proof. intros segs. via_chain. apply rdn_wbytes_hit8. unorm; lia. Qed.

  Lemma D_main_cxx : forall segs (x : Z) n zs,
    (0 <= x)%Z -> (x + Z.of_nat n <= 2 ^ 64)%Z -> lookup_runs D_CXX x n = Some zs ->
    rdn segs D (Z_to_bv 64 x) n = Some (map (Z_to_bv 8) zs).
  Proof. intros. subst D. apply D_main1_hit; assumption. Qed.

  Variable regs : bvmap 5 word.
  Variable mem : word -> option byte.
  Hypothesis ME : main_entry sp0 rdraw av ev a_uid a_hwcap tid regs mem.

  Lemma main_entry_tid : forall segs,
    rdn segs mem (Z_to_bv 64 0x100610) 4 = Some (word_to_le_bytes 4 tid).
  Proof.
    intros segs. rewrite (main_entry_rdn_data sp0 rdraw av ev a_uid a_hwcap tid regs mem ME)
      by (rewrite stack_max_size_val; unorm; lia). apply D_main_tid.
  Qed.

  Lemma main_entry_guard : forall segs,
    rdn segs mem (Z_to_bv 64 0x120928) 8 = Some (word_to_le_bytes 8 (canary rdraw)).
  Proof.
    intros segs. rewrite (main_entry_rdn_data sp0 rdraw av ev a_uid a_hwcap tid regs mem ME)
      by (rewrite stack_max_size_val; unorm; lia). apply D_main_guard.
  Qed.

  Lemma main_entry_rdn_D : forall segs (a : Z) (n : nat) r,
    (0 <= a)%Z -> (a + Z.of_nat n <= 0x100000000)%Z ->
    rdn segs D (Z_to_bv 64 a) n = r -> rdn segs mem (Z_to_bv 64 a) n = r.
  Proof.
    intros segs a n r Ha Hn H. rewrite (main_entry_rdn_data sp0 rdraw av ev a_uid a_hwcap tid regs mem ME)
      by (rewrite stack_max_size_val; unorm; lia). exact H.
  Qed.

  Lemma main_entry_cxx : forall segs (x : Z) n zs,
    (0 <= x)%Z -> (x + Z.of_nat n <= 0x100000000)%Z -> lookup_runs D_CXX x n = Some zs ->
    rdn segs mem (Z_to_bv 64 x) n = Some (map (Z_to_bv 8) zs).
  Proof.
    intros segs x n zs Hx Hn HL. rewrite (main_entry_rdn_data sp0 rdraw av ev a_uid a_hwcap tid regs mem ME)
      by (rewrite stack_max_size_val; unorm; lia). apply D_main_cxx; [lia | lia | exact HL].
  Qed.
End Facts.
