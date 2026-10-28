(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import RunEnv
  StartupTac ArgvEnv RefLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10StartupDefs_u Pm10Startup_u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation RPH := Ubsan.M.phdrs.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require PropExec.
Section FPX_1. Context {fx : PropExec.FPState}.

Definition D_main_cells : list (Z * nat) :=
  [(0xd6730%Z, 8%nat); (0xf6a98%Z, 8%nat); (0xf6af8%Z, 8%nat); (0xf6ac0%Z, 8%nat); (0xf6a88%Z, 8%nat); (0xf6a80%Z, 8%nat); (0xf6828%Z, 8%nat); (0xf6838%Z, 8%nat); (0xf6830%Z, 8%nat); (0xf6aa8%Z, 8%nat); (0xf6ab0%Z, 8%nat); (0xd6810%Z, 8%nat); (0xd67f8%Z, 8%nat); (0xd6738%Z, 8%nat); (0xf6a90%Z, 1%nat); (0xd6760%Z, 4%nat); (0xd6758%Z, 4%nat); (0xd67d0%Z, 8%nat); (0xd67b0%Z, 8%nat); (0xd6740%Z, 8%nat); (0xd6748%Z, 8%nat); (0xd6750%Z, 8%nat); (0xf6a70%Z, 4%nat); (0xf6a74%Z, 4%nat); (0xf6a71%Z, 1%nat); (0xd67f0%Z, 8%nat); (0xc4d70%Z, 1%nat)].

Definition range_disjoint_b (a : Z) (n : nat) (c : Z * nat) : bool :=
  ((a + Z.of_nat n <=? fst c) || (fst c + Z.of_nat (snd c) <=? a))%Z.

Definition D_main_missb (a : Z) (n : nat) : bool :=
  forallb (range_disjoint_b a n) D_main_cells && (0 <=? a)%Z && (a + Z.of_nat n <=? 0xf8000)%Z.

Definition djw (P : Prop) : Prop := P.

Lemma range_disjoint_djw : forall a n c,
  range_disjoint_b a n c = true ->
  djw (a + Z.of_nat n <= fst c \/ fst c + Z.of_nat (snd c) <= a)%Z.
Proof.
  intros a n [c l] H. unfold range_disjoint_b in H. cbn [fst snd] in *.
  apply orb_true_iff in H. unfold djw. destruct H as [H|H]; apply Z.leb_le in H; lia.
Qed.

Section Facts.
  Context {RE : RunEnv}.
  Variable sp0 : word.
  Variables av ev : list (list byte).
  Variable uid : word.
  Variable hw : word.
  Variable rdraw : EntryDraw.
  Variable tid : word.
  Hypothesis Hva : valid_argv av.
  Hypothesis Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z.
  Hypothesis Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z.

  Let D := D_main sp0 av ev hw (ed_random rdraw) tid.
  Local Notation RND := (ed_random rdraw) (only parsing).

  Lemma len_av : (1 <= Z.of_nat (length av) <= 1024)%Z.
  Proof. destruct Hva as [[H1 H2] _]. lia. Qed.

  Lemma D_main_miss : forall segs (a : Z) (n : nat),
    D_main_missb a n = true ->
    rdn segs (D_main sp0 av ev hw (ed_random rdraw) tid) (Z_to_bv 64 a) n = rdn segs (fun _ => None) (Z_to_bv 64 a) n.
  Proof.
    intros segs a n Hb. pose proof (u64_range tid). pose proof (u64_range hw).
    unfold D_main_missb, D_main_cells in Hb. cbn [forallb] in Hb.
    repeat match goal with
           | H : (_ && _)%bool = true |- _ => apply andb_true_iff in H; destruct H as [? ?]
           end.
    repeat match goal with
           | H : range_disjoint_b _ _ _ = true |- _ =>
               apply range_disjoint_djw in H; cbn [fst snd Z.of_nat Pos.of_succ_nat Pos.succ] in H
           | H : (_ <=? _)%Z = true |- _ => apply Z.leb_le in H
           | H : true = true |- _ => clear H
           end.
    cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in *.
    unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc.
    repeat (rewrite rdn_wbytes_out by
      (rewrite ?length_N_to_le_bytes; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; imm_norm; unorm;
       lazymatch goal with
       | |- (?A \/ ?B) => match goal with H : djw _ |- _ => exact H end
       | |- _ => lia
       end)).
    reflexivity.
  Qed.

  Ltac hitD :=
    unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc;
    pose proof len_av;
    peel; first [ apply rdn_wbytes_hit8; unorm; lia
                | match goal with |- rdn _ (wbytes _ ?a ?bs) ?a _ = _ =>
                    rewrite <- (length_N_to_le_bytes 4) at 1; apply rdn_wbytes_hit; rewrite length_N_to_le_bytes; unorm; lia end ].

  Lemma D_main_tid : forall segs,
    rdn segs D (Z_to_bv 64 0xd6758) 4 = Some (word_to_le_bytes 4 tid).
  Proof.
    intros segs. pose proof (u64_range tid). pose proof (u64_range hw). subst D.
    unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
    pose proof (rdn_wbytes_hit segs (word_to_le_bytes 4 tid)) as Hh.
    rewrite length_N_to_le_bytes in Hh. apply Hh. unorm; lia.
  Qed.

  Lemma D_main_guard : forall segs,
    rdn segs D (Z_to_bv 64 0xf6a70) 8 = Some (word_to_le_bytes 8 (canary_w RND)).
  Proof.
    intros segs. pose proof (u64_range tid). pose proof (u64_range hw). subst D.
    unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
    rewrite canary_bytes.
    lazymatch goal with
    | |- rdn _ (wbytes (wbytes (wbytes ?DD _ _) _ _) _ _) _ _ = _ =>
        pose proof (rd_guard_at segs DD RND 0xf6a70 ltac:(lia) ltac:(lia)) as HG;
        cbn [Z.add Pos.add Pos.succ] in HG; exact HG
    end.
  Qed.

  Lemma D_main_pagesize : forall segs,
    rdn segs D (Z_to_bv 64 0xf6ac0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 4096)).
  Proof.
    intros segs. pose proof (u64_range tid). pose proof (u64_range hw). pose proof len_av. subst D.
    unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
    apply rdn_wbytes_hit8. unorm; lia.
  Qed.

  Lemma D_main_hwcap : forall segs,
    rdn segs D (Z_to_bv 64 0xf6af8) 8 = Some (word_to_le_bytes 8 hw).
  Proof.
    intros segs. pose proof (u64_range tid). pose proof (u64_range hw). pose proof len_av. subst D.
    unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
    apply rdn_wbytes_hit8. unorm; lia.
  Qed.

  Lemma D_main_environ : forall segs,
    rdn segs D (Z_to_bv 64 0xd6730) 8 = Some (word_to_le_bytes 8 (envp_w sp0 av)).
  Proof.
    intros segs. pose proof (u64_range tid). pose proof (u64_range hw). pose proof len_av. subst D.
    unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
    apply rdn_wbytes_hit8. unorm; lia.
  Qed.

  Lemma D_main_self : forall segs,
    rdn segs D (Z_to_bv 64 0xd6738) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0xd6738)).
  Proof.
    intros segs. pose proof (u64_range tid). pose proof (u64_range hw). subst D.
    unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
    apply rdn_wbytes_hit8. unorm; lia.
  Qed.

  Lemma D_main_locale : forall segs,
    rdn segs D (Z_to_bv 64 0xd67d0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0xf6ac8)).
  Proof.
    intros segs. pose proof (u64_range tid). pose proof (u64_range hw). subst D.
    unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
    apply rdn_wbytes_hit8. unorm; lia.
  Qed.

  Lemma D_main_canary : forall segs,
    rdn segs D (Z_to_bv 64 0xd67f0) 8 = Some (word_to_le_bytes 8 (canary_w RND)).
  Proof.
    intros segs. pose proof (u64_range tid). pose proof (u64_range hw). subst D.
    unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
    apply rdn_wbytes_hit8. unorm; lia.
  Qed.

  Lemma rdn_pointwise_ov : forall segs m n (a : word) bs,
    (forall j, (j < n)%nat -> m (Z_to_bv 64 (bv_unsigned a + Z.of_nat j)) <> None) ->
    (bv_unsigned a + Z.of_nat n <= 2 ^ 64)%Z ->
    rdn segs m a n = Some bs ->
    forall j, (j < n)%nat -> m (Z_to_bv 64 (bv_unsigned a + Z.of_nat j)) = Some (nth j bs (Z_to_bv 8 0)).
  Proof.
    intros segs m n. induction n as [|n IH]; intros a bs Hdef Hnw Hr j Hj; [lia|].
    cbn [rdn] in Hr. pose proof (u64_range a) as Ha.
    pose proof (Hdef 0%nat ltac:(lia)) as H0. rewrite Nat2Z.inj_0, Z.add_0_r, Z_to_bv_bv_unsigned in H0.
    destruct (m a) as [b|] eqn:Hm; [|exfalso; apply H0; reflexivity].
    destruct (rdn segs m (a + 1) n) as [rest|] eqn:Hr'; [|discriminate]. injection Hr as <-.
    destruct j as [|j].
    + rewrite Nat2Z.inj_0, Z.add_0_r, Z_to_bv_bv_unsigned. exact Hm.
    + cbn [nth]. assert (Hu1 : bv_unsigned (a + 1) = (bv_unsigned a + 1)%Z) by (apply u_add1; lia).
      replace (bv_unsigned a + Z.of_nat (S j))%Z with (bv_unsigned (a + 1) + Z.of_nat j)%Z by lia.
      apply (IH (a + 1) rest); [ | lia | exact Hr' | lia].
      intros k Hk. rewrite Hu1. replace (bv_unsigned a + 1 + Z.of_nat k)%Z with (bv_unsigned a + Z.of_nat (S k))%Z by lia.
      apply Hdef. lia.
  Qed.

  Ltac d_cover :=
    repeat first
      [ rewrite wbytes_inside by (rewrite ?length_N_to_le_bytes; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; unorm; lia); discriminate
      | rewrite wbytes_outside by (rewrite ?length_N_to_le_bytes; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; unorm; lia) ].

  Ltac cover8 :=
    let i := fresh "i" in let Hi := fresh "Hi" in
    intros i Hi; pose proof (u64_range tid); pose proof (u64_range hw); pose proof len_av; subst D;
    unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc;
    assert (C : (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7)%Z) by lia;
    destruct C as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]];
    lazymatch goal with |- _ (Z_to_bv 64 ?z) <> None => let c := eval vm_compute in z in change z with c end;
    d_cover.

  Lemma D_cover_guard : forall i, (0 <= i < 8)%Z -> D (Z_to_bv 64 (0xf6a70 + i)) <> None.
  Proof. cover8. Qed.
  Lemma D_cover_canary : forall i, (0 <= i < 8)%Z -> D (Z_to_bv 64 (0xd67f0 + i)) <> None.
  Proof. cover8. Qed.
  Lemma D_cover_hwcap : forall i, (0 <= i < 8)%Z -> D (Z_to_bv 64 (0xf6af8 + i)) <> None.
  Proof. cover8. Qed.

  Ltac pt8 Hcov Hrd :=
    let i := fresh "i" in let Hi := fresh "Hi" in
    intros i Hi;
    lazymatch goal with |- D (Z_to_bv 64 (?a + i)) = Some _ =>
      pose proof (rdn_pointwise_ov SEGS D 8 (Z_to_bv 64 a) _
        ltac:(intros j Hj; rewrite u_Z2bv by lia; apply Hcov; lia)
        ltac:(rewrite u_Z2bv by lia; lia) (Hrd SEGS) (Z.to_nat i) ltac:(lia)) as Hp;
      rewrite u_Z2bv, Z2Nat.id in Hp by lia; exact Hp
    end.

  Lemma D_guard_pt : forall i, (0 <= i < 8)%Z ->
    D (Z_to_bv 64 (0xf6a70 + i)) = Some (nth (Z.to_nat i) (word_to_le_bytes 8 (canary_w RND)) (Z_to_bv 8 0)).
  Proof. pt8 D_cover_guard D_main_guard. Qed.
  Lemma D_canary_pt : forall i, (0 <= i < 8)%Z ->
    D (Z_to_bv 64 (0xd67f0 + i)) = Some (nth (Z.to_nat i) (word_to_le_bytes 8 (canary_w RND)) (Z_to_bv 8 0)).
  Proof. pt8 D_cover_canary D_main_canary. Qed.
  Lemma D_hwcap_pt : forall i, (0 <= i < 8)%Z ->
    D (Z_to_bv 64 (0xf6af8 + i)) = Some (nth (Z.to_nat i) (word_to_le_bytes 8 hw) (Z_to_bv 8 0)).
  Proof. pt8 D_cover_hwcap D_main_hwcap. Qed.

  Variable regs : bvmap 5 word.
  Variable mem : word -> option byte.
  Hypothesis ME : main_entry sp0 av ev uid hw rdraw tid regs mem.

  Lemma main_entry_rdn_image : forall segs (a : Z) (n : nat),
    D_main_missb a n = true ->
    rdn segs mem (Z_to_bv 64 a) n = rdn segs (fun _ => None) (Z_to_bv 64 a) n.
  Proof.
    intros segs a n Hb.
    assert (Hr : (0 <= a /\ a + Z.of_nat n <= 0xf8000)%Z).
    { unfold D_main_missb in Hb. apply andb_true_iff in Hb as [Hb H2]. apply andb_true_iff in Hb as [_ H1].
      apply Z.leb_le in H1. apply Z.leb_le in H2. lia. }
    rewrite (main_entry_rdn_data sp0 av ev uid hw rdraw tid regs mem ME)
      by (rewrite stack_max_size_val; unorm; lia).
    apply D_main_miss. exact Hb.
  Qed.

  Lemma main_entry_tid : forall segs,
    rdn segs mem (Z_to_bv 64 0xd6758) 4 = Some (word_to_le_bytes 4 tid).
  Proof.
    intros segs. rewrite (main_entry_rdn_data sp0 av ev uid hw rdraw tid regs mem ME)
      by (rewrite stack_max_size_val; unorm; lia). apply D_main_tid.
  Qed.

  Lemma main_entry_guard : forall segs,
    rdn segs mem (Z_to_bv 64 0xf6a70) 8 = Some (word_to_le_bytes 8 (canary_w RND)).
  Proof.
    intros segs. rewrite (main_entry_rdn_data sp0 av ev uid hw rdraw tid regs mem ME)
      by (rewrite stack_max_size_val; unorm; lia). apply D_main_guard.
  Qed.
End Facts.
End FPX_1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
