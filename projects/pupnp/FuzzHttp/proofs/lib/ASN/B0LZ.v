(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel Require Import Fork.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.ASN Require Import
  PropExec AsanAcct BackingAlgebra AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound MainExport MainFactsBoth B0Img MainEntryBoth.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import PropExec MState Mem Cells Step Frame.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Nodes.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.LZ Require Import ITreeLZ NodesLZ NodesLZSound BridgeLZ.
Import ListNotations.
Open Scope Z_scope.

Definition b0_P0 (V : nat -> Z) : list word := flat_map MainExport.pages_of (allow_of ASHOFF V both_vis).

Lemma page_base_le0 : forall a : word, bv_unsigned (page_base a) <= bv_unsigned a
                                        /\ bv_unsigned a < bv_unsigned (page_base a) + 4096
                                        /\ bv_unsigned (page_base a) mod 4096 = 0.
Proof.
  intros a. unfold page_base, page_base_of, page_size. pose proof (bv_unsigned_in_range 64 a) as Ha. unfold bv_modulus in Ha.
  change (2 ^ Z.of_N 64) with 18446744073709551616 in Ha.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (H : 0 <= bv_unsigned a / 4096 * 4096 <= bv_unsigned a) by lia.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with 18446744073709551616.
  rewrite Z.mod_small by lia. split; [lia|]. split; [lia|]. rewrite Z.mod_mul by lia. reflexivity.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

Lemma wa_mod4096 : forall z, z mod 4096 = 0 -> bv_unsigned (wa z) mod 4096 = 0.
Proof.
  intros z Hz. unfold wa. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with (4096 * 2 ^ 52).
  rewrite Z.rem_mul_r by lia. rewrite Hz. rewrite Z.add_0_l. rewrite Z.mul_comm. apply Z.mod_mul. lia.
Qed.

Lemma pages_of_aligned : forall iv, fst iv mod 4096 = 0 -> Forall (fun p : word => bv_unsigned p mod page_size = 0) (MainExport.pages_of iv).
Proof.
  intros iv Hiv. unfold MainExport.pages_of. apply Forall_forall. intros p Hp. apply in_map_iff in Hp as (k & <- & _).
  unfold page_size. apply wa_mod4096. rewrite Z.add_mod, Hiv by lia. rewrite Z.mul_comm, Z.mod_mul by lia. reflexivity.
Qed.

Section Frame.
  Variables (V : nat -> Z) (sp : word) (fs : Fs.Fs) (mo : Model).
  Hypothesis AM : bmodel V sp fs mo.
  Let A0 := allow_of ASHOFF V both_vis.

  #[using="sp fs mo AM"] Lemma b0_P0_aligned : P_aligned (b0_P0 V).
  Proof.
    unfold P_aligned, b0_P0. apply Forall_forall. intros p Hp. apply in_flat_map in Hp as (iv & Hiv & Hp).
    pose proof (proj1 (Forall_forall _ _) (bm_allow_wf _ _ _ _ AM) iv Hiv) as (_ & W2 & _).
    exact (proj1 (Forall_forall _ _) (pages_of_aligned iv W2) p Hp).
  Qed.

  #[using="sp fs mo AM"] Lemma aallowed_in_P0 : forall p : word, bv_unsigned p mod 4096 = 0 -> aallowed A0 p -> In p (b0_P0 V).
  Proof.
    intros p Hp (iv & Hin & Hlo & Hhi). unfold b0_P0. apply in_flat_map. exists iv. split; [exact Hin|].
    pose proof (proj1 (Forall_forall _ _) (bm_allow_wf _ _ _ _ AM) iv Hin) as (W1 & W2 & W3). cbn in W1, W2, W3.
    unfold MainExport.pages_of. apply in_map_iff. exists (Z.to_nat ((bv_unsigned p - fst iv) / 4096)).
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    split.
    - rewrite Z2Nat.id by (apply Z.div_pos; lia). unfold wa.
      replace (fst iv + 4096 * ((bv_unsigned p - fst iv) / 4096)) with (bv_unsigned p) by lia. apply Z_to_bv_bv_unsigned.
    - apply in_seq. split; [lia|]. cbn. apply Z2Nat.inj_lt; try (apply Z.div_pos; lia). apply Z.div_lt_upper_bound; [lia|]. lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  Qed.

  #[using="Type"] Lemma in_P0_allowedb : forall p : word, In p (b0_P0 V) -> page_allowedb (ivl (b0_P0 V)) p = true.
  Proof.
    intros p Hp. unfold page_allowedb. apply existsb_exists. exists (bv_unsigned p, bv_unsigned p + page_size). split.
    - unfold ivl. apply in_map_iff. exists p. split; [reflexivity| exact Hp].
    - cbn [fst snd]. apply andb_true_intro. split; apply Z.leb_le; lia.
  Qed.

  #[using="sp fs mo AM"] Lemma allowedb_A0_ivl : forall p : word, bv_unsigned p mod 4096 = 0 ->
    page_allowedb A0 p = true -> page_allowedb (ivl (b0_P0 V)) p = true.
  Proof. intros p Hp H. apply in_P0_allowedb. apply aallowed_in_P0; [exact Hp|]. apply page_allowedb_aallowed. exact H. Qed.

  #[using="Type"] Lemma page_base_mod : forall a : word, bv_unsigned (page_base a) mod 4096 = 0.
  Proof. intros a. exact (proj2 (proj2 (page_base_le0 a))). Qed.

  #[using="sp fs AM A0"] Lemma b0_MInv : MInv (ivl (b0_P0 V)) mo.
  Proof.
    constructor.
    - exact (bm_mat_nodup _ _ _ _ AM).
    - intros p Hp. exact (proj1 (bm_mat _ _ _ _ AM p Hp)).
    - intros p Hp. destruct (bm_mat _ _ _ _ AM p Hp) as (P1 & _ & P3). apply in_P0_allowedb. apply aallowed_in_P0; assumption.
    - intros p Hp. exact (proj1 (proj2 (bm_mat _ _ _ _ AM p Hp))).
    - rewrite A_bytes_ivl. unfold b0_P0. pose proof (ivz_bytes_pages A0 (bm_allow_wf _ _ _ _ AM)) as (E1 & E2 & E3).
      fold A0. rewrite E1. rewrite (bm_limit _ _ _ _ AM). pose proof (bm_budget _ _ _ _ AM) as B. fold A0 in B. unfold page_size.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
      lia.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  Qed.

  #[using="sp fs AM A0"] Lemma b0_cover : lazy_cover (b0_H0 V mo) (m_vm_lazy mo) (ivl (b0_P0 V)).
  Proof.
    intros w Hlz Hh. unfold b0_H0 in Hh. rewrite Hlz in Hh. cbn [andb] in Hh. apply negb_false_iff in Hh.
    apply allowedb_A0_ivl; [apply page_base_mod | exact Hh].
  Qed.

  #[using="Type"] Lemma lazy_page_range : forall a : word, page_in_ranges (page_base a) (m_vm_lazy mo) = true ->
    exists r, In r (m_vm_lazy mo) /\ bv_unsigned (fst r) <= bv_unsigned a < bv_unsigned (fst r) + bv_unsigned (snd r).
  Proof.
    intros a H. unfold page_in_ranges in H. apply existsb_exists in H as (r & Hr & Hb).
    apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. unfold page_size in H2.
    pose proof (page_base_le0 a) as (B1 & B2 & _). exists r. split; [exact Hr| lia].
  Qed.

  #[using="sp fs AM"] Lemma b0_Hoff : H_off_segments bsegs (b0_H0 V mo).
  Proof.
    intros a Ha. unfold b0_H0 in Ha. apply andb_prop in Ha as [Hlz _].
    destruct (lazy_page_range a Hlz) as (r & Hr & Hin).
    pose proof (proj1 (Forall_forall _ _) (bm_lazy_bounds _ _ _ _ AM) r Hr) as (Hc & _). unfold BIMG_LO, BIMG_HI in Hc.
    apply ref_find_segment_none; lia.
  Qed.

  #[using="V sp fs AM"] Lemma b0_lazy_in_maps : lazy_in_maps mo.
  Proof.
    intros r x Hr Hx.
    destruct (proj1 (Forall_forall _ _) (bm_lzwf _ _ _ _ AM) r Hr) as (_ & _ & _ & e & He & L4 & L5).
    unfold covered. apply existsb_exists. exists e. split; [exact He|].
    unfold in_iv, in_rng, B, S. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
  Qed.

  #[using="V sp fs AM"] Lemma b0_seps : NodesLZ.seps (vm_maps (m_vmmaps mo)).
  Proof.
    pose proof (bm_seps _ _ _ _ AM) as H. induction H as [|p l Hp Hl IH]; constructor; [| exact IH].
    eapply Forall_impl; [| exact Hp]. intros q Hq. exact Hq.
  Qed.

  #[using="V sp fs AM"] Lemma fd_std_lookup : forall k e, fd_lookup (m_fds mo) k = Some e ->
    (k = Z_to_bv 64 0 \/ k = Z_to_bv 64 1 \/ k = Z_to_bv 64 2) /\ e = FdChannel k.
  Proof.
    intros k e H. rewrite (bm_fds _ _ _ _ AM) in H. cbn [fd_lookup] in H.
    destruct (bv_eqb (Z_to_bv 64 0) k) eqn:E0; [apply bv_eqb_eq in E0; injection H as <-; subst k; tauto|].
    destruct (bv_eqb (Z_to_bv 64 1) k) eqn:E1; [apply bv_eqb_eq in E1; injection H as <-; subst k; tauto|].
    destruct (bv_eqb (Z_to_bv 64 2) k) eqn:E2; [apply bv_eqb_eq in E2; injection H as <-; subst k; tauto|].
    discriminate H.
  Qed.

  #[using="V sp fs AM"] Lemma b0_minv : Nodes.minv (strip_vm mo).
  Proof.
    unfold Nodes.minv. rewrite m_fds_strip_vm, m_fs_strip_vm, m_tid_strip_vm, m_vmmaps_strip_vm.
    split; [rewrite (bm_fds _ _ _ _ AM); reflexivity|].
    split; [rewrite (bm_fds _ _ _ _ AM); reflexivity|].
    split; [rewrite (bm_fds _ _ _ _ AM); reflexivity|].
    split. { intros k c H. destruct (fd_std_lookup k _ H) as ([-> |[-> | ->]] & _); vm_compute; reflexivity. }
    split. { intros k p off H. destruct (fd_std_lookup k _ H) as (_ & X). discriminate X. }
    split. { intros k e H. destruct (fd_std_lookup k _ H) as (_ & ->). exact I. }
    split. { intros t Ht. exact (proj2 (bm_tid _ _ _ _ AM) t Ht). }
    split. { reflexivity. }
    rewrite (bm_top _ _ _ _ AM). pose proof (bm_usp _ _ _ _ AM) as (U1 & U2 & _). unfold sp_window_lo, sp_window_hi. lia.
  Qed.

  #[using="V sp fs AM"] Lemma b0_minvL : minvL mo.
  Proof. split; [exact b0_minv|]. split; [exact b0_lazy_in_maps|]. split; [exact (bm_wf _ _ _ _ AM)| exact b0_seps]. Qed.

  #[using="sp fs AM A0"] Theorem b0_lzframe : lzframe bsegs minvL (b0_H0 V mo) (b0_P0 V) mo.
  Proof.
    constructor.
    - exact (bm_halted _ _ _ _ AM).
    - apply (proj2 (minvL_perase _ _)). exact b0_minvL.
    - exact b0_MInv.
    - exact b0_cover.
    - exact b0_P0_aligned.
    - exact b0_Hoff.
  Qed.

  #[using="A0"] Lemma b0_hzero_mem : forall m, bshadow0 V m -> forall a, b0_H0 V mo a = true -> zb a = true -> m a = Some (Z_to_bv 8 0).
  Proof.
    intros m SH0 a Ha Hz. unfold b0_H0 in Ha. apply andb_prop in Ha as [Hlz Hna]. apply negb_true_iff in Hna.
    pose proof (u64_range a) as Ra.
    rewrite <- (Z_to_bv_bv_unsigned a). change (Z_to_bv 64 (bv_unsigned a)) with (wa (bv_unsigned a)). apply SH0.
    - unfold zb in Hz. unfold bshadow. apply orb_prop in Hz as [Hz|Hz]; apply andb_prop in Hz as [Z1 Z2];
        apply Z.leb_le in Z1; apply Z.ltb_lt in Z2; lia.
    - intros (bn & Hbn & Hin).

      assert (AL : page_allowedb A0 (page_base a) = true).
      { unfold page_allowedb. apply existsb_exists.
        exists (MainExport.pagedown (ASHOFF + zv V (fst bn) / 8), MainExport.pageup (ASHOFF + (zv V (fst bn) + zv V (snd bn)) / 8)). split.
        - unfold A0, allow_of. apply in_flat_map. exists bn. split; [unfold both_vis; apply in_or_app; left; exact Hbn|]. cbn. right. left. reflexivity.
        - cbn [fst snd]. pose proof (page_base_le0 a) as (B1 & B2 & B3). unfold page_size, MainExport.pagedown, MainExport.pageup.
          Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
          apply andb_true_intro. split; apply Z.leb_le; lia.
          Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
      fold A0 in Hna. congruence.
  Qed.
End Frame.

Theorem b0_main_lz : forall en inp ms mo, bmain_at en inp ms mo ->
  exists (w : bool) (V : nat -> Z) (m : word -> option byte),
    let H0 := b0_H0 V mo in
    lzframe bsegs minvL H0 (b0_P0 V) mo /\ hzero H0 ms
    /\ ms_mem ms = m
    /\ Forall (mfact_ok bsegs V (mrestrict H0 m)) (both_mem_facts ++ both_mem_facts_w w)
    /\ Forall (pfact_ok V) (both_pure_facts ++ both_pure_facts_w w)
    /\ bmodel V (en_sp en) (in_fs inp) mo.
Proof.
  intros en inp ms mo (w & V & m & Hms & VR & PINS & HMF & HPF & MI & STK & HARG & SH0 & HMFr & AM).
  exists w, V, m. cbv zeta.
  split; [exact (b0_lzframe V _ _ mo AM)|].
  split. { intros a Ha Hz. rewrite Hms. cbn [ms_mem MS]. exact (b0_hzero_mem V mo m SH0 a Ha Hz). }
  split; [rewrite Hms; reflexivity|].
  split; [exact HMFr|]. split; [exact HPF| exact AM].
Qed.
