(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From OssFuzzTheorems.openssl.hashtable.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import
  StartupTac ArgvEnv RefLayout ClaBytes HUStartupDefs HUStartup4 HUStartup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import ConeCfg.   (* [comment removed for export] *)
Import ListNotations.
Import ConeCfg.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation RPH := Ubsan.M.phdrs.

(* [comment removed for export] *)
Definition D_main_cells : list (Z * nat) :=
  [(0x331a18%Z, 8%nat); (0x351d80%Z, 8%nat); (0x351de0%Z, 8%nat); (0x351da8%Z, 8%nat); (0x351d70%Z, 8%nat); (0x351d68%Z, 8%nat);
   (0x351b10%Z, 8%nat); (0x351b20%Z, 8%nat); (0x351b18%Z, 8%nat); (0x351d90%Z, 8%nat); (0x351d98%Z, 8%nat); (0x331af8%Z, 8%nat);
   (0x331ae0%Z, 8%nat); (0x331a20%Z, 8%nat); (0x351d78%Z, 1%nat); (0x331a48%Z, 4%nat);
   (0x331a40%Z, 4%nat); (0x331ab8%Z, 8%nat); (0x331a98%Z, 8%nat); (0x331a28%Z, 8%nat); (0x331a30%Z, 8%nat); (0x331a38%Z, 8%nat);
   (0x351b28%Z, 4%nat); (0x351b2c%Z, 4%nat); (0x351b29%Z, 1%nat); (0x331ad8%Z, 8%nat); (0x31eec0%Z, 1%nat)].

Definition range_disjoint_b (a : Z) (n : nat) (c : Z * nat) : bool :=
  ((a + Z.of_nat n <=? fst c) || (fst c + Z.of_nat (snd c) <=? a))%Z.

Definition D_main_missb (a : Z) (n : nat) : bool :=
  forallb (range_disjoint_b a n) D_main_cells && (0 <=? a)%Z && (a + Z.of_nat n <=? 0x354000)%Z.

(* [comment removed for export] *)
Definition djw (P : Prop) : Prop := P.

Lemma range_disjoint_djw : forall a n c,
  range_disjoint_b a n c = true ->
  djw (a + Z.of_nat n <= fst c \/ fst c + Z.of_nat (snd c) <= a)%Z.
Proof.
  intros a n [c l] H. unfold range_disjoint_b in H. cbn [fst snd] in *.
  apply orb_true_iff in H. unfold djw. destruct H as [H|H]; apply Z.leb_le in H; lia.
Qed.

Lemma nth_middle' : forall {A} (l : list A) (x d : A) n, n = length l -> nth n (l ++ [x]) d = x.
Proof. intros A l x d n ->. rewrite app_nth2 by lia. rewrite Nat.sub_diag. reflexivity. Qed.

Section Facts.
  Variable sp0 : word.
  Variables av ev : list (list byte).
  Variables uid hw : word.
  Variable rdraw : EntryDraw.
  Variable tid : word.
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp ev.
  Hypothesis Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z.
  Hypothesis Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z.

  Let D := D_main sp0 av ev hw rdraw tid.

  Lemma len_av : (1 <= Z.of_nat (length av) <= 1024)%Z.
  Proof. destruct Hva as [[H1 H2] _]. lia. Qed.

  Ltac len_sym :=
    rewrite ?len_guard_lo, ?len_guard_hi, ?len_canary8, ?length_N_to_le_bytes;
    cbn [length Z.of_nat Pos.of_succ_nat Pos.succ].

  (* [comment removed for export] *)
  Lemma D_main_miss : forall segs (a : Z) (n : nat),
    D_main_missb a n = true ->
    rdn segs (D_main sp0 av ev hw rdraw tid) (Z_to_bv 64 a) n = rdn segs (fun _ => None) (Z_to_bv 64 a) n.
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
      (len_sym; imm_norm; unorm;
       lazymatch goal with
       | |- (?A \/ ?B) => match goal with H : djw _ |- _ => exact H end
       | |- _ => lia
       end)).
    reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma D_main_guard8 : forall segs,
    rdn segs D (Z_to_bv 64 3480360) 8 = Some (canary8 rdraw).
  Proof.
    intros segs. pose proof (u64_range tid). subst D.
    unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc.
    rewrite rdn_wbytes_out by (len_sym; unorm; lia).
    rewrite rdn_wbytes_out by (len_sym; unorm; lia).
    rewrite <- canary8_eq.
    change (Z_to_bv 64 3480364) with (Z_to_bv 64 (3480360 + 4)).
    change (Z_to_bv 64 3480361) with (Z_to_bv 64 (3480360 + 1)).
    apply (rdn_guard8 segs _ 3480360 (guard_lo rdraw) (guard_hi rdraw) (Z_to_bv 8 0) (len_guard_lo rdraw) (len_guard_hi rdraw)); lia.
  Qed.

  (* [comment removed for export] *)
  Lemma D_main_canary : forall segs,
    rdn segs D (Z_to_bv 64 3349208) 8 = Some (canary8 rdraw).
  Proof.
    intros segs. pose proof (u64_range tid). subst D.
    unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc.
    rewrite rdn_wbytes_out by (len_sym; unorm; lia).
    rewrite <- (len_canary8 rdraw) at 1. apply rdn_wbytes_hit. len_sym. unorm; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma D_main_tid : forall segs,
    rdn segs D (Z_to_bv 64 3349056) 4 = Some (word_to_le_bytes 4 tid).
  Proof.
    intros segs. pose proof (u64_range tid). subst D.
    unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc.
    repeat (rewrite rdn_wbytes_out by (len_sym; unorm; lia)).
    pose proof (rdn_wbytes_hit segs (word_to_le_bytes 4 tid)) as Hh.
    rewrite length_N_to_le_bytes in Hh. apply Hh. unorm; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma D_main_pagesize : forall segs,
    rdn segs D (Z_to_bv 64 0x351da8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 4096)).
  Proof.
    intros segs. pose proof (u64_range tid). pose proof (u64_range hw). pose proof len_av. subst D.
    unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc.
    repeat (rewrite rdn_wbytes_out by (len_sym; unorm; lia)).
    apply rdn_wbytes_hit8. unorm; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma D_main_environ : forall segs,
    rdn segs D (Z_to_bv 64 0x331a18) 8 = Some (word_to_le_bytes 8 (envp_w sp0 av)).
  Proof.
    intros segs. pose proof (u64_range tid). pose proof (u64_range hw). pose proof len_av. subst D.
    unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc.
    repeat (rewrite rdn_wbytes_out by (len_sym; unorm; lia)).
    apply rdn_wbytes_hit8. unorm; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma D_main_auxv : forall segs,
    rdn segs D (Z_to_bv 64 0x351d80) 8 = Some (word_to_le_bytes 8 (auxv_w sp0 av ev)).
  Proof.
    intros segs. pose proof (u64_range tid). pose proof (u64_range hw). pose proof len_av. subst D.
    unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc.
    repeat (rewrite rdn_wbytes_out by (len_sym; unorm; lia)).
    apply rdn_wbytes_hit8. unorm; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma D_main_hwcap : forall segs,
    rdn segs D (Z_to_bv 64 0x351de0) 8 = Some (word_to_le_bytes 8 hw).
  Proof.
    intros segs. pose proof (u64_range tid). pose proof (u64_range hw). pose proof len_av. subst D.
    unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc.
    repeat (rewrite rdn_wbytes_out by (len_sym; unorm; lia)).
    apply rdn_wbytes_hit8. unorm; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma D_main_self : forall segs,
    rdn segs D (Z_to_bv 64 0x331a20) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x331a20)).
  Proof.
    intros segs. pose proof (u64_range tid). pose proof (u64_range hw). subst D.
    unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc.
    repeat (rewrite rdn_wbytes_out by (len_sym; unorm; lia)).
    apply rdn_wbytes_hit8. unorm; lia.
  Qed.

  (* [comment removed for export] *)
  Variable regs : bvmap 5 word.
  Variable mem : word -> option byte.
  Hypothesis ME : main_entry sp0 av ev uid hw rdraw tid regs mem.

  Lemma main_entry_rdn_image : forall segs (a : Z) (n : nat),
    D_main_missb a n = true ->
    rdn segs mem (Z_to_bv 64 a) n = rdn segs (fun _ => None) (Z_to_bv 64 a) n.
  Proof.
    intros segs a n Hb.
    assert (Hr : (0 <= a /\ a + Z.of_nat n <= 0x354000)%Z).
    { unfold D_main_missb in Hb. apply andb_true_iff in Hb as [Hb H2]. apply andb_true_iff in Hb as [_ H1].
      apply Z.leb_le in H1. apply Z.leb_le in H2. lia. }
    rewrite (main_entry_rdn_data sp0 av ev uid hw rdraw tid regs mem ME)
      by (rewrite stack_max_size_val; unorm; lia).
    apply D_main_miss. exact Hb.
  Qed.

  Lemma main_entry_guard8 : forall segs,
    rdn segs mem (Z_to_bv 64 3480360) 8 = Some (canary8 rdraw).
  Proof.
    intros segs. rewrite (main_entry_rdn_data sp0 av ev uid hw rdraw tid regs mem ME)
      by (rewrite stack_max_size_val; unorm; lia). apply D_main_guard8.
  Qed.

  Lemma main_entry_tid : forall segs,
    rdn segs mem (Z_to_bv 64 3349056) 4 = Some (word_to_le_bytes 4 tid).
  Proof.
    intros segs. rewrite (main_entry_rdn_data sp0 av ev uid hw rdraw tid regs mem ME)
      by (rewrite stack_max_size_val; unorm; lia). apply D_main_tid.
  Qed.

  (* [comment removed for export] *)
  Lemma main_entry_guard : forall segs,
    rdn segs mem (Z_to_bv 64 0x351b28) 8 = Some (canary8 rdraw).
  Proof. exact main_entry_guard8. Qed.

  Lemma main_entry_canary : forall segs,
    rdn segs mem (Z_to_bv 64 0x331ad8) 8 = Some (canary8 rdraw).
  Proof.
    intros segs. rewrite (main_entry_rdn_data sp0 av ev uid hw rdraw tid regs mem ME)
      by (rewrite stack_max_size_val; unorm; lia). apply D_main_canary.
  Qed.

  (* [comment removed for export] *)
  Lemma bsb_nw' : (bv_unsigned sp0 + Z.of_nat (length (build_stack_bytes RPH sp0 av ev uid hw rdraw)) < 2^64)%Z.
  Proof. exact (bsb_nw RPH sp0 av ev uid hw rdraw Hva Hve Hhi). Qed.

  Lemma mem0_argv_ptr : forall segs k, (k < length av)%nat ->
    rdn segs (wrap_mem RPH sp0 av ev uid hw rdraw) (Z_to_bv 64 (bv_unsigned sp0 + 8 + 8 * Z.of_nat k)) 8
    = Some (word_to_le_bytes 8 (cat_argv_ptr sp0 av ev k)).
  Proof.
    intros segs k Hk. pose proof len_av.
    replace (Z_to_bv 64 (bv_unsigned sp0 + 8 + 8 * Z.of_nat k)) with (sp0 + nat_to_word (8 + 8 * k))
      by (rewrite word_add_nat; f_equal; lia).
    exact (read_argv_ptr_w segs RPH sp0 av ev uid hw rdraw Hva Hve Hlo Hhi k Hk).
  Qed.

  Lemma argv_ptr_bounds : forall k, (k < length av)%nat ->
    (bv_unsigned sp0 <= bv_unsigned (cat_argv_ptr sp0 av ev k))%Z
    /\ (bv_unsigned (cat_argv_ptr sp0 av ev k) + Z.of_nat (length (nth k av [])) + 1 < 2^64)%Z.
  Proof. intros k Hk. exact (argv_ptr_bounds_at sp0 av ev Hva Hve Hhi k Hk). Qed.

  (* [comment removed for export] *)
  Lemma main_entry_argv_str : forall segs k, (k < length av)%nat ->
    rdn segs mem (cat_argv_ptr sp0 av ev k) (length (nth k av []) + 1)
    = Some (nth k av [] ++ [Z_to_bv 8 0]).
  Proof.
    intros segs k Hk. destruct (argv_ptr_bounds k Hk) as [Hp1 Hp2].
    rewrite (main_entry_rdn_above sp0 av ev uid hw rdraw tid regs mem ME) by lia.
    rewrite rdn_wrap_stack_above by lia.
    apply rdn_app.
    - apply read_argv_str_k; [exact Hk | exact bsb_nw'].
    - rewrite (read_argv_byte_k RPH segs sp0 av ev k (length (nth k av [])) uid hw rdraw Hk ltac:(lia) bsb_nw').
      f_equal. f_equal. rewrite nth_middle' by reflexivity. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma main_entry_argv_prefix : forall segs k n, (k < length av)%nat -> (n <= length (nth k av []))%nat ->
    rdn segs mem (cat_argv_ptr sp0 av ev k) n = Some (firstn n (nth k av [])).
  Proof.
    intros segs k n Hk Hn.
    rewrite (rdn_firstn segs mem (length (nth k av []) + 1) _ _ n (main_entry_argv_str segs k Hk)) by lia.
    f_equal. rewrite firstn_app. replace (n - length (nth k av []))%nat with 0%nat by lia.
    cbn [firstn]. apply app_nil_r.
  Qed.
End Facts.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
