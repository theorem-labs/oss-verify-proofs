(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require NArith ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require PropExec__Common.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require CatSim__Common.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require StepTac.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require ArgvEnv__Common.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AllocSim2__Common.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require StoreOk.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanAcct__Common.
From Stdlib Require FunctionalExtensionality.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require MmapSim.
From Corelib Require PrimString.
From Stdlib Require Uint63.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymExec3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require SpinAlg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module RefLayout.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require PropExec__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require CatSim__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require StepTac. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require ArgvEnv__Common. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.SeqExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.StepTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.ArgvEnv__Common.ArgvEnv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rdn_skipn : forall segs mem n (a : word) bs off k,
  rdn segs mem a n = Some bs -> (off + k <= n)%nat ->
  rdn segs mem (a + nat_to_word off) k = Some (firstn k (skipn off bs)).
Proof.
  intros segs mem n. induction n as [|n IH]; intros a bs off k H Hk.
  - assert (off = 0%nat) by lia. assert (k = 0%nat) by lia. subst.
    rewrite word_add_0. cbn in H |- *. injection H as <-. reflexivity.
  - cbn [rdn] in H.
    destruct (match mem a with Some b => Some b | None => seg_rom segs a end)
      as [b|] eqn:Eb; [|discriminate].
    destruct (rdn segs mem (a+1) n) as [rest|] eqn:Er; [|discriminate].
    injection H as <-.
    destruct off as [|off].
    + rewrite word_add_0. cbn [skipn].
      eapply rdn_firstn; [|exact Hk].
      cbn [rdn]. rewrite Eb, Er. reflexivity.
    + cbn [skipn].
      replace (a + nat_to_word (S off)) with (a + 1 + nat_to_word off)
        by (rewrite word1_nat, nat_to_word_add_merge; reflexivity).
      apply (IH (a+1) rest off k Er). lia.
Qed.

Lemma firstn_app_exact : forall {A} (l1 l2 : list A) n,
  length l1 = n -> firstn n (l1 ++ l2) = l1.
Proof.
  intros A l1 l2 n H. subst n. rewrite firstn_app, firstn_all, Nat.sub_diag.
  cbn. apply app_nil_r.
Qed.

Lemma skipn_app_exact : forall {A} (l1 l2 : list A) n,
  length l1 = n -> skipn n (l1 ++ l2) = l2.
Proof.
  intros A l1 l2 n H. subst n. rewrite skipn_app, skipn_all, Nat.sub_diag. reflexivity.
Qed.

Lemma skipn_repeat' : forall {A} (x : A) off n,
  skipn off (repeat x n) = repeat x (n - off).
Proof.
  intros A x off. induction off as [|off IH]; intros n.
  - cbn. rewrite Nat.sub_0_r. reflexivity.
  - destruct n as [|n]; [reflexivity|]. cbn [repeat skipn]. rewrite IH. f_equal.
Qed.

Lemma firstn_repeat' : forall {A} (x : A) k n, (k <= n)%nat ->
  firstn k (repeat x n) = repeat x k.
Proof.
  intros A x k. induction k as [|k IH]; intros n H; [reflexivity|].
  destruct n as [|n]; [lia|]. cbn [repeat firstn]. rewrite IH by lia. reflexivity.
Qed.

Lemma repeat_firstn_skipn : forall {A} (x : A) n off k,
  (off + k <= n)%nat -> firstn k (skipn off (repeat x n)) = repeat x k.
Proof.
  intros A x n off k H.
  rewrite skipn_repeat', firstn_repeat' by lia. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition cat_envp_ptr (sp : word) (av ev : list (list byte)) (k : nat) : word :=
  nth k (fst (string_addrs (cat_env_base sp av ev) ev)) (Z_to_bv 64 0).

(* [comment removed for export] *)
Definition envp_off (av : list (list byte)) : nat := (8 + 8 * (length av + 1))%nat.
Definition auxv_off (av ev : list (list byte)) : nat :=
  (8 + 8 * (length av + 1) + 8 * (length ev + 1))%nat.

(* [comment removed for export] *)
Definition auxv_words (ph : PhdrInfo) (rnd uid hw : word) : list word :=
  flat_map (fun e => [fst e; snd e]) (auxv_entries ph rnd uid hw).

Lemma build_auxv_words : forall entries,
  build_auxv entries = flat_map word_le8 (flat_map (fun e => [fst e; snd e]) entries).
Proof.
  induction entries as [|[t v] es IH]; [reflexivity|].
  cbn [build_auxv flat_map fst snd app].
  change (build_auxv es) with
    (flat_map (fun e : bv 64 * bv 64 => word_le8 (fst e) ++ word_le8 (snd e)) es) in IH.
  rewrite IH, <- app_assoc. reflexivity.
Qed.

Lemma auxv_bytes_words : forall ph rnd uid hw,
  auxv_bytes ph rnd uid hw = flat_map word_le8 (auxv_words ph rnd uid hw).
Proof. intros. unfold auxv_bytes, auxv_words. apply build_auxv_words. Qed.

Lemma length_auxv_words : forall ph rnd uid hw, length (auxv_words ph rnd uid hw) = 20%nat.
Proof. reflexivity. Qed.

Section Layout.

  Variable segs : list Segment.
  Variable ph : PhdrInfo.
  Variable sp : word.
  Variable rdraw : EntryDraw.   (* [comment removed for export] *)
  Variable av ev : list (list byte).
  Variable uid : word.
  Variable hw : word.       (* [comment removed for export] *)

  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp ev.
  Hypothesis Hsp_lo : (sp_window_lo <= bv_unsigned sp)%Z.
  Hypothesis Hsp_hi : (bv_unsigned sp <= sp_window_hi)%Z.

  Let bsb := build_stack_bytes ph sp av ev uid hw rdraw.
  (* [comment removed for export] *)
  Let stk := stack_to_mem sp (entry_stack_image ph sp av ev uid hw rdraw).

  #[using="Hva Hve Hsp_hi"] Lemma lay_bsb_nw : (bv_unsigned sp + Z.of_nat (length bsb) < 2^64)%Z.
  Proof. exact (bsb_nw ph sp av ev uid hw rdraw Hva Hve Hsp_hi). Qed.

  #[using="ph sp rdraw ev uid hw Hva stk"] Lemma lay_len_av : (1 <= length av <= 1024)%nat.
  Proof. destruct Hva as [[H1 H2] _]. lia. Qed.

  #[using="ph sp rdraw av uid hw Hve stk"] Lemma lay_len_ev : (length ev <= 256)%nat.
  Proof. destruct Hve as [H1 _]. lia. Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma bsb_decomp : exists strs_tail,
    bsb = (word_le8 (len_word av)
           ++ flat_map word_le8 (fst (string_addrs (cat_string_base sp av ev) av)))
          ++ word_le8 (Z_to_bv 64 0)
          ++ flat_map word_le8 (fst (string_addrs (cat_env_base sp av ev) ev))
          ++ word_le8 (Z_to_bv 64 0)
          ++ auxv_bytes ph (at_random_ptr sp av ev) uid hw
          ++ strs_tail.
  Proof.
    unfold bsb, build_stack_bytes, cat_env_base, cat_string_base, cat_struct_size.
    rewrite (string_addrs_pair av). cbv beta iota.
    rewrite (string_addrs_pair ev). cbv beta iota.
    eexists. rewrite <- !app_assoc. reflexivity.
  Qed.

  #[using="ph rdraw uid hw stk"] Lemma len_argc_argv :
    length (word_le8 (len_word av)
            ++ flat_map word_le8 (fst (string_addrs (cat_string_base sp av ev) av)))
    = (8 + 8 * length av)%nat.
  Proof.
    rewrite length_app, length_n_to_le_8, length_flat_map_le8, length_string_addrs_fst. lia.
  Qed.

  #[using="ph rdraw uid hw stk"] Lemma len_envp_ptrs :
    length (flat_map word_le8 (fst (string_addrs (cat_env_base sp av ev) ev))) = (8 * length ev)%nat.
  Proof. rewrite length_flat_map_le8, length_string_addrs_fst. lia. Qed.

  (* [comment removed for export] *)
  #[using="Hva Hve Hsp_hi bsb"] Lemma read_argv_null :
    rdn segs stk (sp + nat_to_word (8 + 8 * length av)) 8%nat = Some (word_le8 (Z_to_bv 64 0)).
  Proof.
    destruct bsb_decomp as [tl E].
    pose proof (read_at_offset_image segs ph sp av ev uid hw rdraw _ (word_le8 (Z_to_bv 64 0)) _ 8%nat E
                  (length_n_to_le_8 _) lay_bsb_nw) as H.
    rewrite len_argc_argv in H. exact H.
  Qed.

  (* [comment removed for export] *)
  #[using="Hva Hve Hsp_hi bsb"] Lemma read_envp_ptr_k : forall k, (k < length ev)%nat ->
    rdn segs stk (sp + nat_to_word (envp_off av + 8 * k)) 8%nat
    = Some (word_le8 (cat_envp_ptr sp av ev k)).
  Proof.
    intros k Hk.
    destruct bsb_decomp as [tl E].
    assert (Hk' : (k < length (fst (string_addrs (cat_env_base sp av ev) ev)))%nat)
      by (rewrite length_string_addrs_fst; exact Hk).
    rewrite (flat_map_le8_decomp _ k Hk') in E.
    rewrite <- !app_assoc in E.
    match type of E with
    | bsb = ?p1 ++ ?p2 ++ ?p3 ++ ?p4 ++ ?mid ++ ?rest =>
        pose proof (read_at_offset_image segs ph sp av ev uid hw rdraw (p1 ++ p2 ++ p3 ++ p4) mid rest 8%nat) as H
    end.
    rewrite <- !app_assoc in H.
    specialize (H E (length_n_to_le_8 _) lay_bsb_nw).
    rewrite !length_app in H.
    rewrite !length_flat_map_le8 in H.
    rewrite length_string_addrs_fst in H.
    rewrite firstn_length_le in H by (rewrite length_string_addrs_fst; lia).
    rewrite !length_n_to_le_8 in H.
    unfold envp_off, cat_envp_ptr.
    replace (8 + 8 * (length av + 1) + 8 * k)%nat with (8 + (8 * length av + (8 + 8 * k)))%nat by lia.
    exact H.
  Qed.

  (* [comment removed for export] *)
  #[using="Hva Hve Hsp_hi bsb"] Lemma read_envp_null :
    rdn segs stk (sp + nat_to_word (envp_off av + 8 * length ev)) 8%nat
    = Some (word_le8 (Z_to_bv 64 0)).
  Proof.
    destruct bsb_decomp as [tl E].
    match type of E with
    | bsb = ?p1 ++ ?p2 ++ ?p3 ++ ?mid ++ ?rest =>
        pose proof (read_at_offset_image segs ph sp av ev uid hw rdraw (p1 ++ p2 ++ p3) mid rest 8%nat) as H
    end.
    rewrite <- !app_assoc in H.
    specialize (H E (length_n_to_le_8 _) lay_bsb_nw).
    rewrite !length_app in H. rewrite len_envp_ptrs in H.
    rewrite !length_n_to_le_8 in H.
    rewrite length_flat_map_le8, length_string_addrs_fst in H.
    unfold envp_off.
    match type of H with
    | rdn _ _ (sp + nat_to_word ?n) 8 = _ =>
        replace (8 + 8 * (length av + 1) + 8 * length ev)%nat with n by lia
    end.
    exact H.
  Qed.

  (* [comment removed for export] *)
  #[using="Hva Hve Hsp_hi bsb"] Lemma read_auxv_all :
    rdn segs stk (sp + nat_to_word (auxv_off av ev)) 160%nat
    = Some (auxv_bytes ph (at_random_ptr sp av ev) uid hw).
  Proof.
    destruct bsb_decomp as [tl E].
    match type of E with
    | bsb = ?p1 ++ ?p2 ++ ?p3 ++ ?p4 ++ ?mid ++ ?rest =>
        pose proof (read_at_offset_image segs ph sp av ev uid hw rdraw (p1 ++ p2 ++ p3 ++ p4) mid rest 160%nat) as H
    end.
    rewrite <- !app_assoc in H.
    specialize (H E (length_auxv_bytes _ _ _ _) lay_bsb_nw).
    rewrite !length_app in H. rewrite len_envp_ptrs in H.
    rewrite !length_n_to_le_8 in H.
    rewrite length_flat_map_le8, length_string_addrs_fst in H.
    unfold auxv_off.
    match type of H with
    | rdn _ _ (sp + nat_to_word ?n) _ = _ =>
        replace (8 + 8 * (length av + 1) + 8 * (length ev + 1))%nat with n by lia
    end.
    exact H.
  Qed.

  (* [comment removed for export] *)
  #[using="Hva Hve Hsp_hi bsb"] Lemma read_auxv_word : forall j, (j < 20)%nat ->
    rdn segs stk (sp + nat_to_word (auxv_off av ev + 8 * j)) 8%nat
    = Some (word_le8 (nth j (auxv_words ph (at_random_ptr sp av ev) uid hw) (Z_to_bv 64 0))).
  Proof.
    intros j Hj.
    rewrite <- nat_to_word_add_merge.
    rewrite (rdn_skipn segs stk 160 _ _ (8 * j) 8 read_auxv_all) by lia.
    f_equal. rewrite auxv_bytes_words.
    rewrite (flat_map_le8_decomp _ j) by (rewrite length_auxv_words; exact Hj).
    rewrite skipn_app_exact
      by (rewrite length_flat_map_le8, firstn_length_le by (rewrite length_auxv_words; lia); lia).
    apply firstn_app_exact. apply length_n_to_le_8.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  #[using="stk"] Lemma bsb_random_split : exists pre,
    bsb = pre ++ at_random_bytes (ed_random rdraw)
    /\ at_random_ptr sp av ev = sp + nat_to_word (length pre)
    /\ (Z.of_nat (length pre) mod 8 = 0)%Z.
  Proof.
    unfold bsb, build_stack_bytes, at_random_ptr.
    rewrite (string_addrs_pair av). cbv beta iota.
    rewrite (string_addrs_pair ev). cbv beta iota zeta.
    match goal with
    | |- exists pre, ?raw ++ repeat ?z ?pd ++ at_random_bytes (ed_random rdraw) = _ /\ _ /\ _ =>
        exists (raw ++ repeat z pd)
    end.
    split; [rewrite <- !app_assoc; reflexivity|].
    rewrite !length_app, !repeat_length, !length_flat_map_le8, !length_string_addrs_fst,
      !length_n_to_le_8, length_auxv_bytes, !length_flatten_strings.
    unfold auxv_size.
    match goal with
    | |- _ /\ (Z.of_nat (?L' + _) mod 8 = 0)%Z => set (L := L')
    end.
    replace (8 + (length av + 1) * 8 + (length ev + 1) * 8 + 160
             + total_arg_bytes_nat av + total_arg_bytes_nat ev)%nat with L by lia.
    assert (Hpd : (0 <= (8 - Z.of_nat L mod 8) mod 8 < 8)%Z) by (apply Z.mod_pos_bound; lia).
    split; [reflexivity|].
    rewrite Nat2Z.inj_add, Z2Nat.id by lia.
    rewrite <- Zplus_mod_idemp_l. rewrite Zplus_mod_idemp_r.
    replace (Z.of_nat L mod 8 + (8 - Z.of_nat L mod 8))%Z with 8%Z by lia.
    reflexivity.
  Qed.

  #[using="Hva Hve Hsp_hi"] Lemma at_random_off : exists off : nat,
    at_random_ptr sp av ev = sp + nat_to_word off
    /\ (off + 16 = length bsb)%nat
    /\ (Z.of_nat off mod 8 = 0)%Z
    /\ forall j n, (j + n <= 16)%nat ->
         rdn segs stk (at_random_ptr sp av ev + nat_to_word j) n
         = Some (firstn n (skipn j (at_random_bytes (ed_random rdraw)))).
  Proof.
    destruct bsb_random_split as [pre [E [Hp Hmod]]].
    pose proof (length_at_random_bytes (ed_random rdraw)) as HL.
    exists (length pre). split; [exact Hp|]. split.
    { unfold bsb in E |- *. rewrite E, length_app, HL. reflexivity. }
    split; [exact Hmod|].
    intros j n Hjn. rewrite Hp, nat_to_word_add_merge.
    rewrite <- (firstn_skipn j (at_random_bytes (ed_random rdraw))) in E.
    rewrite app_assoc in E.
    rewrite <- (firstn_skipn n (skipn j (at_random_bytes (ed_random rdraw)))) in E.
    pose proof (read_at_offset_image segs ph sp av ev uid hw rdraw (pre ++ firstn j (at_random_bytes (ed_random rdraw)))
                  (firstn n (skipn j (at_random_bytes (ed_random rdraw))))
                  (skipn n (skipn j (at_random_bytes (ed_random rdraw)))) n E) as H.
    assert (Hlen : length (pre ++ firstn j (at_random_bytes (ed_random rdraw))) = (length pre + j)%nat).
    { rewrite length_app, firstn_length_le by lia. reflexivity. }
    rewrite Hlen in H.
    apply H; [rewrite firstn_length_le; [reflexivity | rewrite length_skipn; lia] | exact lay_bsb_nw].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  #[using="Hva Hve"] Lemma lay_bsb_len : (Z.of_nat (length bsb) <= 2240000)%Z.
  Proof. exact (bsb_bound ph sp av ev uid hw rdraw Hva Hve). Qed.

  #[using="stk"] Lemma auxv_off_bound : (auxv_off av ev + 160 + 16 <= length bsb)%nat.
  Proof.
    unfold bsb, build_stack_bytes. cbv zeta.
    rewrite (string_addrs_pair av). cbv beta iota.
    rewrite (string_addrs_pair ev). cbv beta iota.
    rewrite !length_app, length_at_random_bytes, !repeat_length, !length_flat_map_le8,
      !length_string_addrs_fst, !length_n_to_le_8, length_auxv_bytes,
      !length_flatten_strings.
    unfold auxv_size, auxv_off. lia.
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  #[using="Type"] Lemma cat_envp_ptr_eq : forall k, (k < length ev)%nat ->
    cat_envp_ptr sp av ev k
    = sp + nat_to_word (cat_struct_size av ev + total_arg_bytes_nat av
                        + total_arg_bytes_nat (firstn k ev)).
  Proof.
    intros k Hk. unfold cat_envp_ptr. rewrite nth_string_addrs by exact Hk.
    unfold cat_env_base, cat_string_base. rewrite !nat_to_word_add_merge.
    rewrite Nat.add_assoc. reflexivity.
  Qed.

  #[using="ph sp rdraw av uid hw Hve stk"] Lemma total_firstn_ev_bound : forall k,
    (Z.of_nat (total_arg_bytes_nat (firstn k ev)) <= 131072)%Z.
  Proof.
    intros k. destruct Hve as [_ [Htot _]]. rewrite total_arg_bytes_Z in Htot.
    pose proof (total_arg_bytes_firstn_le k ev). lia.
  Qed.

  #[using="ph sp rdraw uid hw Hva Hve stk"] Lemma struct_av_bound :
    (Z.of_nat (cat_struct_size av ev + total_arg_bytes_nat av) <= 2107576)%Z.
  Proof.
    destruct Hva as [[Hl0 Hl] [Hta _]]. destruct Hve as [Hle _].
    rewrite total_arg_bytes_Z in Hta. unfold cat_struct_size, auxv_size. lia.
  Qed.

  #[using="ph rdraw uid hw Hva Hve Hsp_lo Hsp_hi stk"] Lemma u_cat_envp_ptr : forall k, (k < length ev)%nat ->
    bv_unsigned (cat_envp_ptr sp av ev k)
    = (bv_unsigned sp + Z.of_nat (cat_struct_size av ev + total_arg_bytes_nat av
                                 + total_arg_bytes_nat (firstn k ev)))%Z.
  Proof.
    intros k Hk. rewrite cat_envp_ptr_eq by exact Hk. rewrite word_add_nat.
    pose proof struct_av_bound. pose proof (total_firstn_ev_bound k).
    unfold sp_window_hi in Hsp_hi. unfold sp_window_lo in Hsp_lo.
    apply u_Z2bv; lia.
  Qed.

  #[using="ph rdraw uid hw Hva Hve Hsp_lo Hsp_hi stk"] Lemma cat_envp_ptr_nz : forall k, (k < length ev)%nat ->
    bv_unsigned (cat_envp_ptr sp av ev k) <> 0%Z.
  Proof.
    intros k Hk. rewrite u_cat_envp_ptr by exact Hk. unfold sp_window_lo in Hsp_lo. lia.
  Qed.

  #[using="ph rdraw uid hw Hva Hve Hsp_lo Hsp_hi stk"] Lemma u_cat_argv_ptr : forall k, (k < length av)%nat ->
    bv_unsigned (cat_argv_ptr sp av ev k)
    = (bv_unsigned sp + Z.of_nat (cat_struct_size av ev + total_arg_bytes_nat (firstn k av)))%Z.
  Proof.
    intros k Hk. rewrite cat_argv_ptr_offset by exact Hk. unfold cat_string_base.
    rewrite nat_to_word_add_merge, word_add_nat.
    pose proof struct_av_bound. pose proof (total_arg_bytes_firstn_le k av).
    unfold sp_window_hi in Hsp_hi. unfold sp_window_lo in Hsp_lo.
    apply u_Z2bv; lia.
  Qed.

  #[using="Hva"] Lemma argv_str_len : forall k, (k < length av)%nat ->
    (Z.of_nat (length (nth k av [])) <= 131071)%Z.
  Proof. intros k Hk. exact (valid_argv_str_len av k Hva Hk). Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma auxv_words_eq : forall rnd,
    auxv_words ph rnd uid hw =
    [AT_PHDR; Z_to_bv 64 (Z.of_N (ph_addr ph)); AT_PHENT; Z_to_bv 64 (Z.of_N (ph_ent ph));
     AT_PHNUM; Z_to_bv 64 (Z.of_N (ph_num ph)); AT_HWCAP; hw; AT_PAGESZ; Z_to_bv 64 4096;
     AT_UID; uid; AT_EUID; uid; AT_SECURE; Z_to_bv 64 0;
     AT_RANDOM; rnd; AT_NULL; Z_to_bv 64 0].
  Proof. reflexivity. Qed.

  (* [comment removed for export] *)
  #[using="Hva Hve Hsp_lo Hsp_hi"] Lemma rnd_facts : forall (Hal : (bv_unsigned sp mod 16 = 0)%Z),
    (bv_unsigned sp <= bv_unsigned (at_random_ptr sp av ev))%Z
    /\ (bv_unsigned (at_random_ptr sp av ev) + 16 <= bv_unsigned sp + Z.of_nat (length bsb))%Z
    /\ (bv_unsigned sp + Z.of_nat (length bsb) < 2^64)%Z
    /\ (bv_unsigned (at_random_ptr sp av ev) mod 8 = 0)%Z
    /\ (forall j n, (j + n <= 16)%nat ->
          rdn segs stk (Z_to_bv 64 (bv_unsigned (at_random_ptr sp av ev) + Z.of_nat j)) n
          = Some (firstn n (skipn j (at_random_bytes (ed_random rdraw))))).
  Proof.
    intros Hal.
    destruct at_random_off as [off [Hp [Hlen [Hmod Hrd]]]].
    pose proof lay_bsb_nw as Hnw. pose proof lay_bsb_len as Hbl.
    unfold sp_window_hi in Hsp_hi. unfold sp_window_lo in Hsp_lo.
    assert (Hu : bv_unsigned (at_random_ptr sp av ev) = (bv_unsigned sp + Z.of_nat off)%Z).
    { rewrite Hp, word_add_nat. apply u_Z2bv; lia. }
    rewrite Hu. split; [lia|]. split; [lia|]. split; [lia|]. split.
    - rewrite Z.add_mod by lia.
      replace (bv_unsigned sp mod 8)%Z with 0%Z.
      2:{ symmetry. rewrite <- (Z.mod_mod_divide _ 16 8) by (exists 2%Z; reflexivity). rewrite Hal. reflexivity. }
      rewrite Hmod. reflexivity.
    - intros j n Hjn. rewrite <- Hu. rewrite <- word_add_nat. apply Hrd. exact Hjn.
  Qed.

End Layout.
End RefLayout.

(* [comment removed for export] *)
Module AgentLib.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require PropExec__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require CatSim__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AllocSim2__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require StoreOk. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.SeqExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.StreamExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim2__Common.ShapeAlg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.StoreOk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma t_emit_app : forall (a b : list event) (T : TSet),
  t_eq (t_emit (a ++ b) T) (t_emit a (t_emit b T)).
Proof.
  intros a b T tr. unfold t_emit. split.
  - intros [Hp | (tr' & -> & HT)].
    + apply is_prefix_app_split in Hp as [Hp | (b' & -> & Hp)].
      * left. exact Hp.
      * right. exists b'. split; [reflexivity | left; exact Hp].
    + right. exists (b ++ tr'). split; [rewrite app_assoc; reflexivity|].
      right. exists tr'. auto.
  - intros [Hp | (tr' & -> & [Hp | (tr'' & -> & HT)])].
    + left. apply is_prefix_app_r. exact Hp.
    + left. apply is_prefix_app_mono. exact Hp.
    + right. exists tr''. rewrite app_assoc. auto.
Qed.

Lemma t_emit_congr : forall (e : list event) (T T' : TSet),
  t_eq T T' -> t_eq (t_emit e T) (t_emit e T').
Proof.
  intros e T T' H tr. unfold t_emit. split.
  - intros [Hp | (tr' & -> & HT)]; [left; exact Hp | right; exists tr'; split; [reflexivity | apply H; exact HT]].
  - intros [Hp | (tr' & -> & HT)]; [left; exact Hp | right; exists tr'; split; [reflexivity | apply H; exact HT]].
Qed.

Lemma t_alt2_congr : forall A A' B B' : TSet,
  t_eq A A' -> t_eq B B' -> t_eq (t_alt2 A B) (t_alt2 A' B').
Proof. intros A A' B B' HA HB tr. unfold t_alt2. rewrite (HA tr), (HB tr). reflexivity. Qed.

Lemma t_emit_nil_l : forall (T : TSet), T [] -> t_eq (t_emit [] T) T.
Proof. exact t_emit_nil_eq. Qed.

(* [comment removed for export] *)
Lemma rz_eq : forall segs c (T T' : TSet),
  t_eq T' T -> realizes segs c T' -> realizes segs c T.
Proof. intros segs c T T' Heq H. eapply rz_conseq; [exact H | exact Heq]. Qed.

(* [comment removed for export] *)
Lemma t_emit_app3 : forall (a b c : list event) (T : TSet),
  t_eq (t_emit a (t_emit b (t_emit c T))) (t_emit (a ++ b ++ c) T).
Proof.
  intros a b c T. apply t_eq_sym.
  eapply t_eq_trans; [apply t_emit_app|].
  apply t_emit_congr. apply t_emit_app.
Qed.

(* [comment removed for export] *)
Lemma map_app3 {A B} (f : A -> B) (a b c : list A) :
  map f (a ++ b ++ c) = map f a ++ map f b ++ map f c.
Proof. rewrite !map_app. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma len_word_of_nat : forall (bs : list byte),
  len_word bs = Z_to_bv 64 (Z.of_nat (length bs)).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma read_bytes_map_of_store_ok : forall segs mem (a : word) (n : nat),
  store_ok segs mem a n = true -> (Z.of_nat n < 2 ^ 64)%Z ->
  exists w, read_bytes_map (wview segs mem) a (Z_to_bv 64 (Z.of_nat n)) = Some w.
Proof.
  intros segs mem a n H Hn. rewrite read_bytes_map_eq. unfold word_to_nat.
  rewrite Z_to_bv_small by (unfold bv_modulus; lia). rewrite Nat2Z.id.
  apply store_ok_read_aux. exact H.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma fd_insert_head_same : forall fds (fd : word) e e',
  fd_insert ((fd, e) :: fds) fd e' = fd_insert fds fd e'.
Proof.
  intros fds fd e e'. unfold fd_insert. cbn [List.filter fst].
  rewrite bv_eqb_refl. cbn [negb]. reflexivity.
Qed.

Lemma filter_fd_id : forall (fds : list (word * FdEntry)) (fd : word),
  fd_lookup fds fd = None ->
  List.filter (fun p => negb (bv_eqb (fst p) fd)) fds = fds.
Proof.
  induction fds as [|[k e] r IH]; intros fd H; [reflexivity|].
  cbn [List.filter fst fd_lookup] in *.
  destruct (bv_eqb k fd) eqn:E; [discriminate|]. cbn [negb].
  rewrite (IH fd H). reflexivity.
Qed.

Lemma fd_insert_fresh_eq : forall fds (fd : word) e,
  fd_lookup fds fd = None -> fd_insert fds fd e = (fd, e) :: fds.
Proof. intros fds fd e H. unfold fd_insert. rewrite (filter_fd_id fds fd H). reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma u64_lit : forall z, (0 <= z < 2 ^ 64)%Z -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. apply Z_to_bv_small. unfold bv_modulus. lia. Qed.

(* [comment removed for export] *)
Lemma v_add_lit : forall a b, (0 <= a)%Z -> (0 <= b)%Z -> (a + b < 2 ^ 64)%Z ->
  v_add (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a + b).
Proof.
  intros a b Ha Hb Hab. unfold v_add. rewrite !u64_lit by lia. reflexivity.
Qed.

Lemma v_sub_lit : forall a b, (0 <= b <= a)%Z -> (a < 2 ^ 64)%Z ->
  v_sub (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a - b).
Proof.
  intros a b Hab Ha. unfold v_sub. rewrite !u64_lit by lia. reflexivity.
Qed.

Lemma v_addi_lit : forall a i, (0 <= a < 2 ^ 64)%Z ->
  v_addi (Z_to_bv 64 a) i = Z_to_bv 64 (a + i).
Proof. intros a i Ha. unfold v_addi. rewrite u64_lit by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma Z_to_bv_64_mod : forall z, Z_to_bv 64 z = Z_to_bv 64 (z mod 2 ^ 64).
Proof.
  intro z. apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
  rewrite Z.mod_mod by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma c_ltu_lit : forall a b, (0 <= a < 2 ^ 64)%Z -> (0 <= b < 2 ^ 64)%Z ->
  c_ltu (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b)%Z.
Proof. intros a b Ha Hb. unfold c_ltu, bv_ltu. rewrite !u64_lit by lia. reflexivity. Qed.

Lemma c_eq_lit : forall a b, (0 <= a < 2 ^ 64)%Z -> (0 <= b < 2 ^ 64)%Z ->
  c_eq (Z_to_bv 64 a) (Z_to_bv 64 b) = (a =? b)%Z.
Proof. intros a b Ha Hb. unfold c_eq, bv_eqb. rewrite !u64_lit by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma bv_signed_small : forall z, (0 <= z < 2 ^ 63)%Z -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. rewrite Z_to_bv_signed. unfold bv_swrap.
  unfold bv_wrap, bv_half_modulus, bv_modulus.
  replace (2 ^ Z.of_N 64)%Z with (2 ^ 64)%Z by reflexivity.
  replace (2 ^ 64 `div` 2)%Z with (2 ^ 63)%Z by reflexivity.
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma bv_signed_neg : forall e, (0 < e <= 2 ^ 63)%Z -> bv_signed (Z_to_bv 64 (- e)) = (- e)%Z.
Proof.
  intros e He. rewrite Z_to_bv_signed. unfold bv_swrap.
  unfold bv_wrap, bv_half_modulus, bv_modulus.
  replace (2 ^ Z.of_N 64)%Z with (2 ^ 64)%Z by reflexivity.
  replace (2 ^ 64 `div` 2)%Z with (2 ^ 63)%Z by reflexivity.
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma c_lts_zero_nonneg : forall z, (0 <= z < 2 ^ 63)%Z ->
  c_lts (Z_to_bv 64 z) (Z_to_bv 64 0) = false.
Proof.
  intros z Hz. unfold c_lts, bv_lts. rewrite !bv_signed_small by lia. apply Z.ltb_ge. lia.
Qed.

Lemma c_lts_zero_errno : forall e, (0 < e <= 2 ^ 63)%Z ->
  c_lts (Z_to_bv 64 (- e)) (Z_to_bv 64 0) = true.
Proof.
  intros e He. unfold c_lts, bv_lts. rewrite bv_signed_neg by lia.
  rewrite bv_signed_small by lia. apply Z.ltb_lt. lia.
Qed.

(* [comment removed for export] *)
Lemma errno_ret_lit : forall e, errno_ret e = Z_to_bv 64 (- e).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Ltac show_goal_marker := match goal with |- ?g => idtac "=====GOAL=====" g end.

(* [comment removed for export] *)
Lemma rdn_addr_eq : forall segs m (a b : word) n r,
  a = b -> rdn segs m b n = r -> rdn segs m a n = r.
Proof. intros segs m a b n r -> H. exact H. Qed.

Ltac rdn_at b :=
  apply (rdn_addr_eq _ _ _ b);
  [ first [ f_equal; lia
          | lazymatch goal with |- ?g => StepTac.check_closed_term g end;
            apply bv_eq; vm_compute; reflexivity ]
  | ].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint zall (n : nat) (f : Z -> bool) (z : Z) : bool :=
  match n with
  | O => true
  | S n' => if f z then zall n' f (z + 1)%Z else false
  end.

Lemma zall_spec : forall n f z,
  zall n f z = true -> forall x, (z <= x < z + Z.of_nat n)%Z -> f x = true.
Proof.
  induction n as [|n IH]; intros f z H x Hx; [lia|].
  cbn [zall] in H. destruct (f z) eqn:E; [|discriminate].
  destruct (Z.eq_dec x z) as [->|Hne]; [exact E|].
  apply (IH f (z + 1)%Z H). lia.
Qed.

(* [comment removed for export] *)
Lemma zallN_spec : forall (n : N) f,
  zall (N.to_nat n) f 0%Z = true -> forall x, (0 <= x < Z.of_N n)%Z -> f x = true.
Proof. intros n f H x Hx. apply (zall_spec (N.to_nat n) f 0%Z H). rewrite N_nat_Z. lia. Qed.

(* [comment removed for export] *)
Ltac rdn_at_hyp Hb :=
  lazymatch type of Hb with
  | rdn _ _ ?b _ = _ => rdn_at b; exact Hb
  end.
End AgentLib.

(* [comment removed for export] *)
Module RefMemcpyLib.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require PropExec__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require CatSim__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require StepTac. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanAcct__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require StoreOk. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.SeqExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.StepTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanAcct__Common.Hoare OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.StoreOk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition sub {A} (bs : list A) (j k : nat) : list A := firstn k (skipn j bs).

Lemma firstn_add : forall {A} (l : list A) a b,
  firstn (a + b) l = firstn a l ++ firstn b (skipn a l).
Proof.
  intros A l a. revert l. induction a as [|a IH]; intros l b.
  - cbn. reflexivity.
  - destruct l as [|x l]; cbn.
    + destruct b; reflexivity.
    + rewrite IH. reflexivity.
Qed.

Lemma firstn_sub_app : forall {A} (bs : list A) j k,
  firstn j bs ++ sub bs j k = firstn (j + k) bs.
Proof. intros. unfold sub. rewrite firstn_add. reflexivity. Qed.

Lemma skipn_add : forall {A} (l : list A) a b, skipn (a + b) l = skipn b (skipn a l).
Proof.
  intros A l a. revert l. induction a as [|a IH]; intros l b; [reflexivity|].
  destruct l as [|x l]; cbn; [destruct b; reflexivity|]. apply IH.
Qed.

Lemma sub_length : forall {A} (bs : list A) j k,
  (j + k <= length bs)%nat -> length (sub bs j k) = k.
Proof.
  intros A bs j k H. unfold sub. rewrite length_firstn, length_skipn. lia.
Qed.

Lemma sub_split : forall {A} (bs : list A) j a b,
  sub bs j (a + b) = sub bs j a ++ sub bs (j + a) b.
Proof.
  intros A bs j a b. unfold sub. rewrite firstn_add. f_equal.
  rewrite <- skipn_add. f_equal; lia.
Qed.

Lemma sub_0_all : forall {A} (bs : list A), sub bs 0 (length bs) = bs.
Proof. intros. unfold sub. cbn. apply firstn_all. Qed.

Lemma length_firstn_id : forall {A} (bs : list A) k, k = length bs -> firstn k bs = bs.
Proof. intros A bs k ->. apply firstn_all. Qed.

Lemma sub_nth : forall (bs : list byte) j,
  (j < length bs)%nat -> sub bs j 1 = [nth j bs (Z_to_bv 8 0)].
Proof.
  intros bs j. revert bs. induction j as [|j IH]; intros bs H.
  - destruct bs; cbn in *; [lia|reflexivity].
  - destruct bs; cbn in *; [lia|]. unfold sub in IH. apply IH. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma at_succ : forall (a : word) d, (at_ a d + 1)%bv = at_ a (d + 1).
Proof.
  intros a d. unfold at_. apply bv_eq.
  rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_unsigned (1 : word)) with 1.
  rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.

Lemma word_succ_at : forall (a : word), (a + 1)%bv = at_ a 1.
Proof. intros a. rewrite <- (at_0 a) at 1. rewrite at_succ. reflexivity. Qed.

Lemma at_u : forall (a : word) d,
  0 <= bv_unsigned a + d -> bv_unsigned a + d < 2^64 ->
  bv_unsigned (at_ a d) = bv_unsigned a + d.
Proof. intros a d H1 H2. unfold at_. apply u_Z2bv; lia. Qed.

Lemma at_nat : forall (a : word) (j : nat), (a + nat_to_word j)%bv = at_ a (Z.of_nat j).
Proof.
  intros a j. unfold at_, nat_to_word. apply bv_eq.
  rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap.
  rewrite Zplus_mod_idemp_r. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma wbytes_app : forall bs1 bs2 m (a : word),
  wbytes m a (bs1 ++ bs2) = wbytes (wbytes m a bs1) (at_ a (Z.of_nat (length bs1))) bs2.
Proof.
  induction bs1 as [|b r IH]; intros bs2 m a.
  - cbn [app wbytes length Z.of_nat]. rewrite at_0. reflexivity.
  - cbn [app wbytes length]. rewrite IH. f_equal.
    rewrite word_succ_at, at_at. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma wbytes_extend : forall m (dst : word) bs j k,
  wbytes (wbytes m dst (firstn j bs)) (at_ dst (Z.of_nat j)) (sub bs j k)
  = wbytes m dst (firstn (j + k) bs) \/ (length bs < j)%nat.
Proof.
  intros m dst bs j k.
  destruct (Nat.le_gt_cases j (length bs)) as [H|H]; [left|right; exact H].
  rewrite <- firstn_sub_app, wbytes_app. rewrite length_firstn. f_equal. f_equal. f_equal. lia.
Qed.

Lemma wbytes_extend' : forall m (dst : word) bs j k,
  (j <= length bs)%nat ->
  wbytes (wbytes m dst (firstn j bs)) (at_ dst (Z.of_nat j)) (sub bs j k)
  = wbytes m dst (firstn (j + k) bs).
Proof.
  intros m dst bs j k H. destruct (wbytes_extend m dst bs j k) as [E|E]; [exact E|lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rdn_skipn : forall segs mem n (a : word) bs j,
  rdn segs mem a n = Some bs -> (j <= n)%nat ->
  rdn segs mem (at_ a (Z.of_nat j)) (n - j) = Some (skipn j bs).
Proof.
  intros segs mem n. induction n as [|n IH]; intros a bs j H Hj.
  - assert (j = 0)%nat by lia. subst j. cbn in H. injection H as <-.
    rewrite at_0. reflexivity.
  - cbn [rdn] in H.
    destruct (match mem a with Some b => Some b | None => seg_rom segs a end) as [b|] eqn:Eb; [|discriminate].
    destruct (rdn segs mem (a+1)%bv n) as [rest|] eqn:Er; [|discriminate].
    injection H as <-.
    destruct j as [|j].
    + rewrite at_0. cbn [Nat.sub skipn rdn]. rewrite Eb, Er. reflexivity.
    + cbn [skipn]. replace (S n - S j)%nat with (n - j)%nat by lia.
      replace (at_ a (Z.of_nat (S j))) with (at_ (a + 1)%bv (Z.of_nat j))
        by (rewrite word_succ_at, at_at; f_equal; lia).
      apply IH; [exact Er|lia].
Qed.

Lemma rdn_sub : forall segs mem n (a : word) bs j k,
  rdn segs mem a n = Some bs -> (j + k <= n)%nat ->
  rdn segs mem (at_ a (Z.of_nat j)) k = Some (sub bs j k).
Proof.
  intros segs mem n a bs j k H Hjk. unfold sub.
  apply (rdn_firstn segs mem (n - j)); [|lia].
  apply rdn_skipn; [exact H|lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Abbreviation lez := bytes_le_to_Z.

(* [comment removed for export] *)
Definition LWv (l : list byte) : word := v_lw (Z_to_bv 64 (lez l)).

Lemma lez_bound_len : forall bs k, length bs = k -> 0 <= lez bs < 2 ^ (8 * Z.of_nat k).
Proof. intros bs k <-. split; [apply bytes_le_to_Z_nonneg | apply bytes_le_to_Z_bound]. Qed.
Lemma lez4_range : forall l, length l = 4%nat -> 0 <= lez l < 2 ^ 32.
Proof. intros l H. pose proof (lez_bound_len l 4%nat H). change (8 * Z.of_nat 4) with 32 in H0. lia. Qed.
Lemma u_lez4 : forall l, length l = 4%nat -> bv_unsigned (Z_to_bv 64 (lez l)) = lez l.
Proof. intros l H. pose proof (lez4_range l H). apply u_Z2bv; lia. Qed.

Lemma testbit_u_LWv : forall l i, length l = 4%nat -> 0 <= i < 32 ->
  Z.testbit (bv_unsigned (LWv l)) i = Z.testbit (lez l) i.
Proof.
  intros l i H Hi. unfold LWv, v_lw. rewrite Z_to_bv_unsigned, u_lez4 by exact H.
  rewrite bv_wrap_spec_low by lia.
  rewrite bv_swrap_spec by lia.
  case_bool_decide; [reflexivity|].
  replace i with 31 by lia. reflexivity.
Qed.

Lemma u_vlw_mod32 : forall l, length l = 4%nat -> bv_unsigned (LWv l) mod 2 ^ 32 = lez l.
Proof.
  intros l H. pose proof (lez4_range l H) as R.
  apply Z.bits_inj'. intros i Hi.
  destruct (Z.lt_ge_cases i 32) as [Hl|Hh].
  - rewrite Z.mod_pow2_bits_low by lia. apply testbit_u_LWv; [exact H|lia].
  - rewrite Z.mod_pow2_bits_high by lia. symmetry. apply (Z_testbit_high 32); lia.
Qed.

Lemma lez_cons : forall b bs, lez (b :: bs) = Z.lor (bv_unsigned b) (Z.shiftl (lez bs) 8).
Proof. reflexivity. Qed.

Lemma testbit_lez_high : forall bs i, 8 * Z.of_nat (length bs) <= i -> Z.testbit (lez bs) i = false.
Proof.
  intros bs i Hi. apply (Z_testbit_high (8 * Z.of_nat (length bs))); try lia.
  apply lez_bound_len. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma testbit_lez_skipn : forall q bs i, 0 <= i ->
  Z.testbit (lez (skipn q bs)) i = Z.testbit (lez bs) (i + 8 * Z.of_nat q).
Proof.
  induction q as [|q IH]; intros bs i Hi.
  - cbn [skipn]. f_equal. lia.
  - destruct bs as [|b bs].
    + cbn [skipn lez]. rewrite !Z.bits_0. reflexivity.
    + cbn [skipn]. rewrite IH by lia. rewrite lez_cons.
      rewrite Z.lor_spec, Z.shiftl_spec by lia.
      pose proof (u8_range b).
      rewrite (Z_testbit_high 8 (bv_unsigned b)) by lia. cbn [orb]. f_equal. lia.
Qed.

Lemma testbit_lez_firstn : forall q bs i, 0 <= i ->
  Z.testbit (lez (firstn q bs)) i = if i <? 8 * Z.of_nat q then Z.testbit (lez bs) i else false.
Proof.
  induction q as [|q IH]; intros bs i Hi.
  - cbn [firstn lez]. rewrite Z.bits_0. destruct (Z.ltb_spec i (8 * Z.of_nat 0)); [lia|reflexivity].
  - destruct bs as [|b bs].
    + cbn [firstn lez]. rewrite !Z.bits_0. destruct (i <? _); reflexivity.
    + cbn [firstn]. rewrite !lez_cons, !Z.lor_spec, !Z.shiftl_spec by lia.
      destruct (Z.lt_ge_cases i 8) as [H8|H8].
      * rewrite !(Z.testbit_neg_r _ (i - 8)) by lia.
        destruct (Z.ltb_spec i (8 * Z.of_nat (S q))); [reflexivity|lia].
      * rewrite IH by lia.
        destruct (Z.ltb_spec (i - 8) (8 * Z.of_nat q)), (Z.ltb_spec i (8 * Z.of_nat (S q))); try lia; try reflexivity.
        pose proof (u8_range b). rewrite (Z_testbit_high 8 (bv_unsigned b)) by lia. reflexivity.
Qed.

Lemma testbit_lez_app : forall xs ys i, 0 <= i ->
  Z.testbit (lez (xs ++ ys)) i =
  if i <? 8 * Z.of_nat (length xs) then Z.testbit (lez xs) i else Z.testbit (lez ys) (i - 8 * Z.of_nat (length xs)).
Proof.
  intros xs ys i Hi. rewrite bytes_le_app, Z.lor_spec, Z.shiftl_spec by lia.
  destruct (Z.ltb_spec i (8 * Z.of_nat (length xs))).
  - rewrite (Z.testbit_neg_r (lez ys)) by lia. apply orb_false_r.
  - rewrite testbit_lez_high by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma Z_to_le_bytes_lez : forall bs, Z_to_le_bytes (length bs) (lez bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|].
  cbn [length Z_to_le_bytes].
  replace (Z.shiftr (lez (b :: bs)) 8) with (lez bs).
  2:{ apply Z.bits_inj'. intros i Hi. rewrite Z.shiftr_spec by lia.
      pose proof (testbit_lez_skipn 1 (b :: bs) i Hi) as E. change (skipn 1 (b :: bs)) with bs in E.
      rewrite E. reflexivity. }
  rewrite IH. f_equal.
  apply bv_eq. rewrite Z_to_bv_unsigned.
  apply Z.bits_inj'. intros i Hi. pose proof (u8_range b).
  destruct (Z.lt_ge_cases i 8).
  - rewrite bv_wrap_spec_low by lia. rewrite lez_cons, Z.lor_spec, Z.shiftl_spec by lia.
    rewrite (Z.testbit_neg_r _ (i - 8)) by lia. apply orb_false_r.
  - rewrite bv_wrap_spec_high by lia. symmetry. apply (Z_testbit_high 8); lia.
Qed.

Lemma word_to_le_bytes_4_eq : forall (v : word) (l : list byte),
  length l = 4%nat ->
  (forall i, 0 <= i < 32 -> Z.testbit (bv_unsigned v) i = Z.testbit (lez l) i) ->
  word_to_le_bytes 4 v = l.
Proof.
  intros v l Hl Hb. unfold word_to_le_bytes.
  rewrite <- (Z_to_le_bytes_wrap 4 32) by (cbn; lia).
  rewrite <- Hl at 1. rewrite <- (Z_to_le_bytes_lez l). rewrite Hl. f_equal.
  apply Z.bits_inj'. intros i Hi.
  destruct (Z.lt_ge_cases i 32).
  - rewrite bv_wrap_spec_low by lia. apply Hb. lia.
  - rewrite bv_wrap_spec_high by lia. symmetry. apply testbit_lez_high. rewrite Hl. cbn. lia.
Qed.

(* [comment removed for export] *)
Lemma sw_bytes_LWv : forall l, length l = 4%nat -> word_to_le_bytes 4 (LWv l) = l.
Proof.
  intros l H. apply word_to_le_bytes_4_eq; [exact H|]. intros i Hi. apply testbit_u_LWv; assumption.
Qed.

(* [comment removed for export] *)
Definition LBv (b : byte) : word := Z_to_bv 64 (bv_unsigned b).

Lemma sb_byte_LBv : forall b : byte, Z_to_bv 8 (bv_unsigned (LBv b)) = b.
Proof.
  intros b. unfold LBv. pose proof (u8_range b). rewrite u_Z2bv by lia.
  apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 8) with 256. lia.
Qed.

(* [comment removed for export] *)
Lemma sb_byte_eq : forall (v : word) (b : byte),
  (forall i, 0 <= i < 8 -> Z.testbit (bv_unsigned v) i = Z.testbit (bv_unsigned b) i) ->
  Z_to_bv 8 (bv_unsigned v) = b.
Proof.
  intros v b Hb. apply bv_eq. rewrite Z_to_bv_unsigned.
  apply Z.bits_inj'. intros i Hi. pose proof (u8_range b).
  destruct (Z.lt_ge_cases i 8).
  - rewrite bv_wrap_spec_low by lia. apply Hb. lia.
  - rewrite bv_wrap_spec_high by lia. symmetry. apply (Z_testbit_high 8); lia.
Qed.

Lemma testbit_nth_lez : forall l q i, 0 <= i < 8 -> (q < length l)%nat ->
  Z.testbit (bv_unsigned (nth q l (Z_to_bv 8 0))) i = Z.testbit (lez l) (i + 8 * Z.of_nat q).
Proof.
  intros l q i Hi Hq. rewrite <- testbit_lez_skipn by lia.
  revert l Hq. induction q as [|q IH]; intros l Hq.
  - destruct l as [|b l]; [cbn in Hq; lia|]. cbn [nth skipn]. rewrite lez_cons.
    rewrite Z.lor_spec, Z.shiftl_spec, (Z.testbit_neg_r _ (i - 8)) by lia. symmetry. apply orb_false_r.
  - destruct l as [|b l]; [cbn in Hq; lia|]. cbn [nth skipn]. apply IH. cbn in Hq. lia.
Qed.

(* [comment removed for export] *)
Lemma sb_byte_srli_LWv : forall l q, length l = 4%nat -> (q <= 3)%nat ->
  Z_to_bv 8 (bv_unsigned (v_srli (LWv l) (8 * Z.of_nat q))) = nth q l (Z_to_bv 8 0).
Proof.
  intros l q H Hq. apply sb_byte_eq. intros i Hi.
  unfold v_srli. rewrite Z_to_bv_unsigned, bv_wrap_spec_low, Z.shiftr_spec by lia.
  rewrite testbit_u_LWv by (try exact H; lia).
  rewrite testbit_nth_lez by (try rewrite H; lia). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma testbit_u_srliw_LWv : forall l s i, length l = 4%nat -> 1 <= s -> 0 <= i ->
  Z.testbit (bv_unsigned (v_srliw (LWv l) s)) i = if i + s <? 32 then Z.testbit (lez l) (i + s) else false.
Proof.
  intros l s i H Hs Hi. unfold v_srliw. rewrite Z_to_bv_unsigned.
  assert (Sh : forall j, 0 <= j -> Z.testbit (Z.shiftr (bv_wrap 32 (bv_unsigned (LWv l))) s) j
                              = if j + s <? 32 then Z.testbit (lez l) (j + s) else false).
  { intros j Hj. rewrite Z.shiftr_spec by lia.
    destruct (Z.ltb_spec (j + s) 32).
    - rewrite bv_wrap_spec_low by lia. apply testbit_u_LWv; [exact H|lia].
    - apply bv_wrap_spec_high. lia. }
  destruct (Z.lt_ge_cases i 64).
  - rewrite bv_wrap_spec_low by lia. rewrite bv_swrap_spec by lia.
    case_bool_decide.
    + apply Sh. lia.
    + rewrite Sh by lia.
      destruct (Z.ltb_spec (Z.of_N 32 - 1 + s) 32), (Z.ltb_spec (i + s) 32); try lia; reflexivity.
  - rewrite bv_wrap_spec_high by lia. destruct (Z.ltb_spec (i + s) 32); [lia|reflexivity].
Qed.

(* [comment removed for export] *)
Lemma testbit_u_slli_LWv : forall l s i, length l = 4%nat -> 0 <= s -> 0 <= i < 32 ->
  Z.testbit (bv_unsigned (v_slli (LWv l) s)) i = if i <? s then false else Z.testbit (lez l) (i - s).
Proof.
  intros l s i H Hs Hi. unfold v_slli. rewrite Z_to_bv_unsigned.
  rewrite bv_wrap_spec_low by lia. rewrite Z.shiftl_spec by lia.
  destruct (Z.ltb_spec i s).
  - apply Z.testbit_neg_r. lia.
  - apply testbit_u_LWv; [exact H|lia].
Qed.

Lemma testbit_u_vor : forall (x y : word) i, 0 <= i ->
  Z.testbit (bv_unsigned (v_or x y)) i = Z.testbit (bv_unsigned x) i || Z.testbit (bv_unsigned y) i.
Proof.
  intros x y i Hi. unfold v_or. rewrite Z_to_bv_unsigned.
  destruct (Z.lt_ge_cases i 64).
  - rewrite bv_wrap_spec_low by lia. apply Z.lor_spec.
  - rewrite bv_wrap_spec_high by lia.
    pose proof (u64_range x). pose proof (u64_range y).
    rewrite (Z_testbit_high 64 (bv_unsigned x)) by lia. rewrite (Z_testbit_high 64 (bv_unsigned y)) by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma sw_bytes_merge : forall l1 l2 (q : nat) (v : word),
  length l1 = 4%nat -> length l2 = 4%nat -> (1 <= q <= 3)%nat ->
  v = v_or (v_slli (LWv l2) (32 - 8 * Z.of_nat q)) (v_srliw (LWv l1) (8 * Z.of_nat q)) ->
  word_to_le_bytes 4 v = skipn q l1 ++ firstn q l2.
Proof.
  intros l1 l2 q v H1 H2 Hq ->.
  apply word_to_le_bytes_4_eq.
  { rewrite length_app, length_skipn, length_firstn, H1, H2. lia. }
  intros i Hi.
  rewrite testbit_u_vor by lia.
  rewrite testbit_u_slli_LWv by (try exact H2; lia).
  rewrite testbit_u_srliw_LWv by (try exact H1; lia).
  rewrite testbit_lez_app by lia. rewrite length_skipn, H1.
  rewrite testbit_lez_skipn by lia.
  destruct (Z.ltb_spec i (32 - 8 * Z.of_nat q)), (Z.ltb_spec i (8 * Z.of_nat (4 - q))),
           (Z.ltb_spec (i + 8 * Z.of_nat q) 32); try lia.
  - reflexivity.
  - rewrite testbit_lez_firstn by lia.
    destruct (Z.ltb_spec (i - 8 * Z.of_nat (4 - q)) (8 * Z.of_nat q)); [|lia].
    rewrite orb_false_r. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma sw_bytes_merge' : forall l1 l2 (q : nat) (v : word),
  length l1 = 4%nat -> length l2 = 4%nat -> (1 <= q <= 3)%nat ->
  v = v_or (v_srliw (LWv l1) (8 * Z.of_nat q)) (v_slli (LWv l2) (32 - 8 * Z.of_nat q)) ->
  word_to_le_bytes 4 v = skipn q l1 ++ firstn q l2.
Proof.
  intros l1 l2 q v H1 H2 Hq ->. apply (sw_bytes_merge l1 l2 q); try assumption.
  unfold v_or. f_equal. apply Z.lor_comm.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma store_ok_at : forall segs m (dst : word) (N : nat) bsw j k,
  bv_unsigned dst + Z.of_nat N <= 2 ^ 64 ->
  store_ok segs m dst N = true ->
  0 <= j -> j + Z.of_nat k <= Z.of_nat N ->
  store_ok segs (wbytes m dst bsw) (at_ dst j) k = true.
Proof.
  intros segs m dst N bsw j k Hnw Hok Hj Hk.
  destruct k as [|k]; [reflexivity|].
  pose proof (u64_range dst).
  apply (store_ok_mono segs (S k) m); [apply wbytes_grows|].
  apply (store_ok_sub segs m dst (at_ dst j) N (S k) Hnw Hok); rewrite at_u; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition callee_kept : list reg :=
  [1; 2; 3; 4; 8; 9; 10; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

Definition keeps (regs regs' : bvmap 5 word) : Prop :=
  forall r : reg, In r callee_kept -> getr regs' r = getr regs r.

Lemma keeps_refl : forall regs, keeps regs regs.
Proof. intros regs r _. reflexivity. Qed.

Lemma keeps_trans : forall r1 r2 r3, keeps r1 r2 -> keeps r2 r3 -> keeps r1 r3.
Proof. intros r1 r2 r3 A B r Hr. rewrite (B r Hr). apply A, Hr. Qed.

(* [comment removed for export] *)
Lemma keeps_upd : forall regs regs' (rd : reg) v,
  keeps regs regs' -> ~ In rd callee_kept -> keeps regs (regupd regs' rd v).
Proof.
  intros regs regs' rd v K Hn r Hr.
  rewrite getr_other; [apply K, Hr|]. intros ->. exact (Hn Hr).
Qed.

(* [comment removed for export] *)
Lemma keeps_getr : forall regs regs' (r : reg), keeps regs regs' -> In r callee_kept -> getr regs' r = getr regs r.
Proof. intros regs regs' r K Hr. apply K, Hr. Qed.

Ltac kept_reg := cbv [callee_kept In]; intuition congruence.

Example keeps_sp_example : forall regs regs', keeps regs regs' -> getr regs' 2 = getr regs 2.
Proof. intros regs regs' K. apply (keeps_getr _ _ 2 K). kept_reg. Qed.

(* [comment removed for export] *)
Ltac not_kept := cbv; intuition discriminate.

(* [comment removed for export] *)
Ltac solve_keeps :=
  repeat (apply keeps_upd; [| not_kept]); first [apply keeps_refl | assumption].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma runs_trans : forall segs (s0 : machine_state)
    (st1 : bvmap 5 word -> machine_state) (P1 : bvmap 5 word -> Prop)
    (st2 : bvmap 5 word -> machine_state) (P2 : bvmap 5 word -> Prop),
  (exists r1, msteps segs s0 (st1 r1) /\ P1 r1) ->
  (forall r1, P1 r1 -> exists r2, msteps segs (st1 r1) (st2 r2) /\ P2 r2) ->
  exists r2, msteps segs s0 (st2 r2) /\ P2 r2.
Proof.
  intros segs s0 st1 P1 st2 P2 (r1 & R1 & H1) K.
  destruct (K r1 H1) as (r2 & R2 & H2).
  exists r2. split; [eapply msteps_trans; eassumption | exact H2].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition callee_saved : list reg :=
  [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

Definition keeps_cs (regs regs' : bvmap 5 word) : Prop :=
  forall r : reg, In r callee_saved -> getr regs' r = getr regs r.

Lemma keeps_cs_refl : forall regs, keeps_cs regs regs.
Proof. intros regs r _. reflexivity. Qed.

Lemma keeps_cs_trans : forall r1 r2 r3, keeps_cs r1 r2 -> keeps_cs r2 r3 -> keeps_cs r1 r3.
Proof. intros r1 r2 r3 A B r Hr. rewrite (B r Hr). apply A, Hr. Qed.

Lemma keeps_cs_upd : forall regs regs' (rd : reg) v,
  keeps_cs regs regs' -> ~ In rd callee_saved -> keeps_cs regs (regupd regs' rd v).
Proof.
  intros regs regs' rd v K Hn r Hr.
  rewrite getr_other; [apply K, Hr|]. intros ->. exact (Hn Hr).
Qed.

(* [comment removed for export] *)
Lemma keeps_cs_upd_same : forall regs regs' (rd : reg) v,
  keeps_cs regs regs' -> getr regs rd = v -> rd <> 0%bv -> keeps_cs regs (regupd regs' rd v).
Proof.
  intros regs regs' rd v K Hv Hnz r Hr.
  destruct (decide (r = rd)) as [->|Hne].
  - rewrite getr_same by exact Hnz. symmetry. exact Hv.
  - rewrite getr_other by exact Hne. apply K, Hr.
Qed.

Lemma keeps_keeps_cs : forall regs regs', keeps regs regs' -> keeps_cs regs regs'.
Proof.
  intros regs regs' K r Hr. apply K. unfold callee_saved, callee_kept in *. cbn [In] in *. intuition.
Qed.

Lemma keeps_cs_getr : forall regs regs' (r : reg), keeps_cs regs regs' -> In r callee_saved -> getr regs' r = getr regs r.
Proof. intros regs regs' r K Hr. apply K, Hr. Qed.

Ltac solve_keeps_cs :=
  repeat (first [ apply keeps_cs_upd; [| not_kept]
                | apply keeps_cs_upd_same; [| solve [eauto | symmetry; eauto] | let X := fresh in intro X; discriminate X ] ]);
  first [apply keeps_cs_refl | assumption | apply keeps_keeps_cs; assumption].
End RefMemcpyLib.

(* [comment removed for export] *)
Module MemsetLib.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require PropExec__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require CatSim__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require StepTac. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanAcct__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require StoreOk. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require ArgvEnv__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require MmapSim. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.SeqExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.StepTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanAcct__Common.Hoare OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.StoreOk OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.ArgvEnv__Common.MemSplit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.MmapSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefLayout__Common.RefMemcpyLib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Instance asanreflect_fx : OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.FPState := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ms_inb (i : Z) (iv : Z * Z) : bool := (fst iv <=? i) && (i <? fst iv + snd iv).
Definition ms_cov (L : list (Z * Z)) (i : Z) : bool := existsb (ms_inb i) L.

Lemma ms_inb_true : forall i o m, ms_inb i (o, m) = true <-> o <= i < o + m.
Proof.
  intros i o m. unfold ms_inb. cbn [fst snd]. rewrite andb_true_iff, Z.leb_le, Z.ltb_lt. tauto.
Qed.

Lemma ms_cov_cons : forall iv L i, ms_cov (iv :: L) i = ms_inb i iv || ms_cov L i.
Proof. reflexivity. Qed.

Lemma ms_cov_app : forall L1 L2 i, ms_cov (L1 ++ L2) i = ms_cov L1 i || ms_cov L2 i.
Proof. intros. unfold ms_cov. apply existsb_app. Qed.

Lemma ms_cov_In : forall L i o m, In (o, m) L -> o <= i < o + m -> ms_cov L i = true.
Proof.
  intros L i o m Hin Hi. unfold ms_cov. apply existsb_exists. exists (o, m). split; [exact Hin|].
  apply ms_inb_true. exact Hi.
Qed.

(* [comment removed for export] *)
Fixpoint ms_chain (from to : Z) (L : list (Z * Z)) : Prop :=
  match L with
  | [] => to <= from
  | (o, m) :: L' => o <= from /\ ms_chain (o + m) to L'
  end.

Lemma ms_chain_cov : forall L from to i,
  ms_chain from to L -> from <= i < to -> exists o m, In (o, m) L /\ o <= i < o + m.
Proof.
  induction L as [|[o m] L IH]; intros from to i Hc Hi; cbn [ms_chain] in Hc.
  - lia.
  - destruct Hc as [Ho Hc].
    destruct (Z.lt_ge_cases i (o + m)) as [Hlt|Hge].
    + exists o, m. split; [left; reflexivity | lia].
    + destruct (IH (o + m) to i Hc ltac:(lia)) as (o' & m' & Hin & Hi').
      exists o', m'. split; [right; exact Hin | exact Hi'].
Qed.

(* [comment removed for export] *)
Lemma ms_cov_by_chain : forall (L L' : list (Z * Z)) n,
  incl L' L -> ms_chain 0 n L' -> forall i, 0 <= i < n -> ms_cov L i = true.
Proof.
  intros L L' n Hincl Hc i Hi.
  destruct (ms_chain_cov L' 0 n i Hc Hi) as (o & m & Hin & Hom).
  apply (ms_cov_In L i o m); [apply Hincl, Hin | exact Hom].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section CFill.
  Variable mem0 : word -> option byte.
  Variable d : word.
  Variable n : Z.
  Variable c : byte.
  Hypothesis Hn : 0 <= n.
  Hypothesis Hnw : bv_unsigned d + n < 2 ^ 64.

  Definition cfill (L : list (Z * Z)) : word -> option byte :=
    fun x => if (bv_unsigned d <=? bv_unsigned x) && (bv_unsigned x <? bv_unsigned d + n)
                && ms_cov L (bv_unsigned x - bv_unsigned d)
             then Some c else mem0 x.

  #[using="Type"] Lemma cfill_nil : cfill [] = mem0.
  Proof.
    apply functional_extensionality. intro x. unfold cfill. cbn [ms_cov existsb].
    rewrite andb_false_r. reflexivity.
  Qed.

  #[using="Type"] Lemma cfill_grows : forall L, mem_grows mem0 (cfill L).
  Proof.
    intros L x Hx. unfold cfill. destruct (_ && _); [discriminate | exact Hx].
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma cfill_ext : forall L1 L2,
    (forall i, 0 <= i < n -> ms_cov L1 i = ms_cov L2 i) -> cfill L1 = cfill L2.
  Proof.
    intros L1 L2 H. apply functional_extensionality. intro x. unfold cfill.
    destruct (Z.leb_spec (bv_unsigned d) (bv_unsigned x)); [|reflexivity].
    destruct (Z.ltb_spec (bv_unsigned x) (bv_unsigned d + n)); [|reflexivity].
    cbn [andb]. rewrite H by lia. reflexivity.
  Qed.

  (* [comment removed for export] *)
  #[using="Hnw"] Lemma cfill_store : forall L o (m : nat),
    0 <= o -> o + Z.of_nat m <= n ->
    wbytes (cfill L) (at_ d o) (repeat c m) = cfill ((o, Z.of_nat m) :: L).
  Proof.
    intros L o m Ho Hm. apply functional_extensionality. intro x.
    pose proof (u64_range d). pose proof (u64_range x).
    assert (Ha : bv_unsigned (at_ d o) = bv_unsigned d + o) by (apply at_u; lia).
    destruct (Z.lt_ge_cases (bv_unsigned x) (bv_unsigned d + o)) as [Hlo|Hge];
      [| destruct (Z.lt_ge_cases (bv_unsigned x) (bv_unsigned d + o + Z.of_nat m)) as [Hin|Hhi]].
    - rewrite wbytes_outside by (rewrite repeat_length, Ha; lia).
      unfold cfill. rewrite ms_cov_cons.
      replace (ms_inb (bv_unsigned x - bv_unsigned d) (o, Z.of_nat m)) with false
        by (symmetry; apply not_true_iff_false; rewrite ms_inb_true; lia).
      reflexivity.
    - rewrite wbytes_inside by (rewrite repeat_length, Ha; lia).
      rewrite nth_repeat_lt by (rewrite Ha; lia). unfold cfill. rewrite ms_cov_cons.
      replace (ms_inb (bv_unsigned x - bv_unsigned d) (o, Z.of_nat m)) with true
        by (symmetry; apply ms_inb_true; lia).
      destruct (Z.leb_spec (bv_unsigned d) (bv_unsigned x)); [|lia].
      destruct (Z.ltb_spec (bv_unsigned x) (bv_unsigned d + n)); [|lia].
      reflexivity.
    - rewrite wbytes_outside by (rewrite repeat_length, Ha; lia).
      unfold cfill. rewrite ms_cov_cons.
      replace (ms_inb (bv_unsigned x - bv_unsigned d) (o, Z.of_nat m)) with false
        by (symmetry; apply not_true_iff_false; rewrite ms_inb_true; lia).
      reflexivity.
  Qed.

  (* [comment removed for export] *)
  #[using="Hn Hnw"] Lemma cfill_full : forall L,
    (forall i, 0 <= i < n -> ms_cov L i = true) ->
    cfill L = wbytes mem0 d (repeat c (Z.to_nat n)).
  Proof.
    intros L Hcov. apply functional_extensionality. intro x.
    pose proof (u64_range d). pose proof (u64_range x).
    unfold cfill.
    destruct (Z.leb_spec (bv_unsigned d) (bv_unsigned x)) as [H1|H1].
    - destruct (Z.ltb_spec (bv_unsigned x) (bv_unsigned d + n)) as [H2|H2]; cbn [andb].
      + rewrite Hcov by lia. rewrite wbytes_inside by (rewrite repeat_length; lia).
        rewrite nth_repeat_lt by lia. reflexivity.
      + rewrite wbytes_outside by (rewrite repeat_length; lia). reflexivity.
    - cbn [andb]. rewrite wbytes_outside by (rewrite repeat_length; lia). reflexivity.
  Qed.

  #[using="Hn Hnw"] Lemma cfill_full_chain : forall L L',
    incl L' L -> ms_chain 0 n L' ->
    cfill L = wbytes mem0 d (repeat c (Z.to_nat n)).
  Proof. intros L L' Hi Hc. apply cfill_full. apply (ms_cov_by_chain L L'); assumption. Qed.

  (* [comment removed for export] *)
  #[using="Hnw"] Lemma cfill_store_ok : forall segs L o (m : nat),
    store_ok segs mem0 d (Z.to_nat n) = true ->
    0 <= o -> o + Z.of_nat m <= n ->
    store_ok segs (cfill L) (at_ d o) m = true.
  Proof.
    intros segs L o m Hok Ho Hm. pose proof (u64_range d).
    apply (store_ok_mono segs m mem0); [apply cfill_grows|].
    apply (store_ok_sub segs mem0 d (at_ d o) (Z.to_nat n) m); try (rewrite ?at_u; lia). exact Hok.
  Qed.
End CFill.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma mod4_mod_pow2_gen : forall t k j, 0 <= j <= k -> (t mod 2 ^ k) mod 2 ^ j = t mod 2 ^ j.
Proof.
  intros t k j Hk. apply Z.mod_mod_divide.
  exists (2 ^ (k - j)). rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.

(* [comment removed for export] *)
Definition cbyte (cv : word) : byte := Z_to_bv 8 (bv_unsigned cv).
(* [comment removed for export] *)
Definition cbz (cv : word) : Z := bv_unsigned cv mod 256.
(* [comment removed for export] *)
Definition c32 (cv : word) : word := Z_to_bv 64 (cbz cv * 16843009).
(* [comment removed for export] *)
Definition c32h (cv : word) : word := Z_to_bv 64 (cbz cv * 16843009 * 2 ^ 32).
(* [comment removed for export] *)
Definition c64 (cv : word) : word := Z_to_bv 64 (cbz cv * 72340172838076673).

Lemma cbz_range : forall cv, 0 <= cbz cv < 256.
Proof. intros cv. unfold cbz. apply Z.mod_pos_bound. lia. Qed.

Lemma cbyte_mod : forall cv, Z_to_bv 8 (bv_unsigned cv mod 256) = cbyte cv.
Proof.
  intros cv. unfold cbyte. apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap8_mod. apply Z.mod_mod. lia.
Qed.

Lemma cbyte_cbz : forall cv, cbyte cv = Z_to_bv 8 (cbz cv).
Proof. intros cv. unfold cbz. symmetry. apply cbyte_mod. Qed.

(* [comment removed for export] *)
Lemma cbyte_Z : forall z, cbyte (Z_to_bv 64 z) = Z_to_bv 8 z.
Proof.
  intros z. unfold cbyte. apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap8_mod, bv_wrap64_mod.
  apply mod4_mod_pow2_gen. lia.
Qed.

(* [comment removed for export] *)
Fixpoint ms_repl (k : nat) : Z := match k with O => 0 | S k' => 1 + 256 * ms_repl k' end.

Lemma ms_repl_nonneg : forall k, 0 <= ms_repl k.
Proof. induction k; cbn [ms_repl]; lia. Qed.

Lemma Z_to_le_bytes_ms_repl : forall k z, 0 <= z < 256 ->
  Z_to_le_bytes k (z * ms_repl k) = repeat (Z_to_bv 8 z) k.
Proof.
  induction k as [|k IH]; intros z Hz; [reflexivity|].
  cbn [Z_to_le_bytes ms_repl repeat]. pose proof (ms_repl_nonneg k). f_equal.
  - apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap8_mod.
    replace (z * (1 + 256 * ms_repl k)) with (z + (z * ms_repl k) * 256) by lia.
    rewrite Z.mod_add by lia. reflexivity.
  - rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
    replace (z * (1 + 256 * ms_repl k)) with (z + (z * ms_repl k) * 256) by lia.
    rewrite Z.div_add by lia. rewrite Z.div_small by lia. rewrite Z.add_0_l. apply IH. exact Hz.
Qed.

Lemma u_c32 : forall cv, bv_unsigned (c32 cv) = cbz cv * 16843009.
Proof. intros cv. pose proof (cbz_range cv). unfold c32. apply u_Z2bv; lia. Qed.

Lemma u_c32h : forall cv, bv_unsigned (c32h cv) = cbz cv * 16843009 * 2 ^ 32.
Proof. intros cv. pose proof (cbz_range cv). unfold c32h. apply u_Z2bv; lia. Qed.

Lemma u_c64 : forall cv, bv_unsigned (c64 cv) = cbz cv * 72340172838076673.
Proof. intros cv. pose proof (cbz_range cv). unfold c64. apply u_Z2bv; lia. Qed.

Lemma wleb4_c32 : forall cv, word_to_le_bytes 4 (c32 cv) = repeat (cbyte cv) 4.
Proof.
  intros cv. unfold word_to_le_bytes. rewrite u_c32, cbyte_cbz.
  change 16843009 with (ms_repl 4). apply Z_to_le_bytes_ms_repl. apply cbz_range.
Qed.

Lemma wleb8_c64 : forall cv, word_to_le_bytes 8 (c64 cv) = repeat (cbyte cv) 8.
Proof.
  intros cv. unfold word_to_le_bytes. rewrite u_c64, cbyte_cbz.
  change 72340172838076673 with (ms_repl 8). apply Z_to_le_bytes_ms_repl. apply cbz_range.
Qed.

(* [comment removed for export] *)
Lemma u_slli56 : forall cv, bv_unsigned (v_slli cv 56) = cbz cv * 2 ^ 56.
Proof.
  intros cv. unfold v_slli, cbz. rewrite Z_to_bv_unsigned, Z.shiftl_mul_pow2 by lia.
  pose proof (u64_range cv).
  unfold bv_wrap. change (bv_modulus 64) with (2 ^ 56 * 256).
  rewrite Z.mul_comm, Z.mul_mod_distr_l by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma mulhu_c32 : forall cv (m : word), bv_unsigned m = 4311810304 ->
  v_mulhu (v_slli cv 56) m = c32 cv.
Proof.
  intros cv m Hm. unfold v_mulhu, c32. f_equal. rewrite u_slli56, Hm.
  rewrite Z.shiftr_div_pow2 by lia.
  replace (cbz cv * 2 ^ 56 * 4311810304) with ((cbz cv * 16843009) * 2 ^ 64) by lia.
  apply Z.div_mul. lia.
Qed.

Lemma slli32_c32 : forall cv, v_slli (c32 cv) 32 = c32h cv.
Proof.
  intros cv. unfold v_slli, c32h. f_equal. rewrite u_c32, Z.shiftl_mul_pow2 by lia. reflexivity.
Qed.

Lemma srli32_c32h : forall cv, v_srli (c32h cv) 32 = c32 cv.
Proof.
  intros cv. unfold v_srli, c32. f_equal. rewrite u_c32h, Z.shiftr_div_pow2 by lia.
  apply Z.div_mul. lia.
Qed.

Lemma lor_disjoint_shift32 : forall a b, 0 <= a -> 0 <= b < 2 ^ 32 ->
  Z.lor (a * 2 ^ 32) b = a * 2 ^ 32 + b.
Proof.
  intros a b Ha Hb.
  assert (Hl : Z.land (a * 2 ^ 32) b = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i 32).
    - rewrite <- Z.shiftl_mul_pow2, Z.shiftl_spec by lia. rewrite (Z.testbit_neg_r a) by lia. reflexivity.
    - rewrite (Z_testbit_high 32 b) by lia. apply andb_false_r. }
  rewrite <- Z.lxor_lor by exact Hl. symmetry. apply Z.add_nocarry_lxor. exact Hl.
Qed.

Lemma or_c64 : forall cv, v_or (c32h cv) (c32 cv) = c64 cv.
Proof.
  intros cv. pose proof (cbz_range cv). unfold v_or, c64. f_equal. rewrite u_c32h, u_c32.
  rewrite lor_disjoint_shift32 by lia. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma mod4_mod_pow2' : forall t k, 2 <= k -> (t mod 2 ^ k) mod 4 = t mod 4.
Proof.
  intros t k Hk. apply Z.mod_mod_divide.
  exists (2 ^ (k - 2)). change 4 with (2 ^ 2). rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma negw_and3 : forall x : word,
  v_andi (v_subw (Z_to_bv 64 0) x) 3 = Z_to_bv 64 ((- bv_unsigned x) mod 4).
Proof.
  intros x. unfold v_andi, v_subw. f_equal.
  change (bv_wrap 64 3) with (Z.ones 2). rewrite Z.land_ones by lia.
  rewrite Z_to_bv_unsigned. change (bv_unsigned (Z_to_bv 64 0)) with 0.
  unfold bv_swrap. rewrite bv_wrap64_mod.
  change (bv_half_modulus 32) with (2 ^ 31).
  unfold bv_wrap. change (bv_modulus 32) with (2 ^ 32). change (2 ^ 2) with 4.
  rewrite mod4_mod_pow2' by lia.
  rewrite <- Zminus_mod_idemp_l.
  rewrite mod4_mod_pow2' by lia.
  replace (0 - bv_unsigned x + 2 ^ 31) with ((- bv_unsigned x) + 536870912 * 4) by lia.
  rewrite Z.mod_add by lia.
  rewrite Zminus_mod_idemp_l.
  replace (- bv_unsigned x - 2 ^ 31) with ((- bv_unsigned x) + (- 536870912) * 4) by lia.
  rewrite Z.mod_add by lia. reflexivity.
Qed.

Lemma neg_mod4_range : forall u, 0 <= (- u) mod 4 <= 3.
Proof. intros u. pose proof (Z.mod_pos_bound (- u) 4). lia. Qed.

Lemma neg_mod4_aligns : forall u, (u + (- u) mod 4) mod 4 = 0.
Proof.
  intros u. rewrite Z.add_mod, Z.mod_mod by lia.
  rewrite <- Z.add_mod by lia. replace (u + - u) with 0 by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma land_trunc4 : forall a, 0 <= a < 2 ^ 64 -> Z.land a (2 ^ 64 - 4) = a - a mod 4.
Proof.
  intros a Ha.
  replace (2 ^ 64 - 4) with (Z.ldiff (Z.ones 64) (Z.ones 2)).
  2:{ rewrite Z.ldiff_land, <- Z.sub_land_same_l, Z.land_ones by lia.
      rewrite Z.ones_mod_pow2 by lia. rewrite !Z.ones_equiv. lia. }
  rewrite Z.ldiff_land, Z.land_assoc, Z.land_ones by lia.
  rewrite Z.mod_small by lia.
  rewrite <- Z.ldiff_land, Z.ldiff_ones_r by lia.
  rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
  pose proof (Z.div_mod a 4 ltac:(lia)). lia.
Qed.

Lemma andi_m4 : forall m, 0 <= m < 2 ^ 64 ->
  v_andi (Z_to_bv 64 m) (-4) = Z_to_bv 64 (m - m mod 4).
Proof.
  intros m Hm. unfold v_andi. f_equal. rewrite u_Z2bv by lia.
  change (bv_wrap 64 (-4)) with (2 ^ 64 - 4). apply land_trunc4. exact Hm.
Qed.

(* [comment removed for export] *)
Lemma land_4_cases : forall a, 0 <= a -> Z.land a 4 = 0 \/ Z.land a 4 = 4.
Proof.
  intros a Ha.
  destruct (Z.testbit a 2) eqn:E; [right|left];
    apply Z.bits_inj'; intros i Hi; rewrite Z.land_spec;
    change 4 with (2 ^ 2); rewrite Z.pow2_bits_eqb by lia;
    destruct (Z.eqb_spec 2 i) as [<-|Hne]; rewrite ?E, ?Z.bits_0; try reflexivity;
    apply andb_false_r.
Qed.

Lemma andi_4_cases : forall x : word, exists s4, v_andi x 4 = Z_to_bv 64 s4 /\ (s4 = 0 \/ s4 = 4).
Proof.
  intros x. exists (Z.land (bv_unsigned x) 4). split.
  - unfold v_andi. f_equal.
  - apply land_4_cases. apply u64_range.
Qed.

(* [comment removed for export] *)
Lemma ms_v_add_Z : forall (x : word) z, 0 <= z < 2 ^ 64 ->
  v_add x (Z_to_bv 64 z) = at_ x z.
Proof. intros x z Hz. unfold v_add, at_. rewrite u_Z2bv by lia. reflexivity. Qed.

Lemma ms_v_add_at_Z : forall (x : word) o z, 0 <= z < 2 ^ 64 ->
  v_add (at_ x o) (Z_to_bv 64 z) = at_ x (o + z).
Proof. intros x o z Hz. rewrite ms_v_add_Z by lia. apply at_at. Qed.

Lemma ms_v_sub_ZZ : forall a b, 0 <= b <= a -> a < 2 ^ 64 ->
  v_sub (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a - b).
Proof. intros a b H1 H2. unfold v_sub. rewrite !u_Z2bv by lia. reflexivity. Qed.

Lemma ms_v_addi_Z : forall a i, 0 <= a < 2 ^ 64 ->
  v_addi (Z_to_bv 64 a) i = Z_to_bv 64 (a + i).
Proof. intros a i Ha. unfold v_addi. rewrite u_Z2bv by lia. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ms_step_subw_at : forall segs regs pc mem rom w rd rs1 rs2 v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Op32 ALU_SUB rd rs1 rs2, 4%Z) ->
  bv_eqb rd 0 = false ->
  v_subw (getr regs rs1) (getr regs rs2) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rd rs1 rs2 v Hf He Hd Hrd Hv.
  rewrite (step_subw segs regs pc mem rom w rd rs1 rs2 Hf He Hd). rewrite Hrd, Hv. reflexivity.
Qed.

Lemma ms_step_mulhu_at : forall segs regs pc mem rom w rd rs1 rs2 v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Mul M_MULHU rd rs1 rs2, 4%Z) ->
  bv_eqb rd 0 = false ->
  v_mulhu (getr regs rs1) (getr regs rs2) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rd rs1 rs2 v Hf He Hd Hrd Hv.
  rewrite (step_mulhu segs regs pc mem rom w rd rs1 rs2 Hf He Hd). rewrite Hrd, Hv. reflexivity.
Qed.

Lemma ms_step_or_at : forall segs regs pc mem rom w rd rs1 rs2 v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Op ALU_OR rd rs1 rs2, 4%Z) ->
  bv_eqb rd 0 = false ->
  v_or (getr regs rs1) (getr regs rs2) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rd rs1 rs2 v Hf He Hd Hrd Hv.
  rewrite (step_or segs regs pc mem rom w rd rs1 rs2 Hf He Hd). rewrite Hrd, Hv. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Stores.
  Variable segs : list Segment.
  Variable mem0 : word -> option byte.
  Variable d : word.
  Variable n : Z.
  Variable cv : word.
  Hypothesis Hn : 0 <= n.
  Hypothesis Hnw : bv_unsigned d + n < 2 ^ 64.
  Hypothesis Hok : store_ok segs mem0 d (Z.to_nat n) = true.

  #[local] Abbreviation CF := (cfill mem0 d n (cbyte cv)).

  #[using="Hnw Hok"] Lemma cf_sb : forall regs pc rom w rs1 rs2 (imm : bv 12) L o0 o,
    fetch_word segs pc = Some w -> is_ecall w = false ->
    decode_any w = Some (Store SZ1 rs1 rs2 imm, 4%Z) ->
    getr regs rs1 = at_ d o0 -> (o0 + bv_signed imm = o)%Z ->
    getr regs rs2 = cv ->
    0 <= o -> o + 1 <= n ->
    RiscvSemantics.step segs (mkst regs pc (CF L) rom) =
    MachineOk (mkst regs (v_addi pc 4) (CF ((o, 1) :: L)) rom).
  Proof.
    intros regs pc rom w rs1 rs2 imm L o0 o Hf He Hdc Hrs1 Ho Hrs2 H0 H1.
    replace ((o, 1) :: L) with ((o, Z.of_nat 1) :: L) by reflexivity.
    rewrite <- (cfill_store mem0 d n (cbyte cv) Hnw L o 1) by lia.
    eapply step_sb_at; [exact Hf | exact He | exact Hdc | | exact Hrs2 | reflexivity |].
    - rewrite Hrs1, at_addi, Ho. reflexivity.
    - apply (cfill_store_ok mem0 d n (cbyte cv) Hnw segs); assumption || lia.
  Qed.

  #[using="Hnw Hok"] Lemma cf_sw : forall regs pc rom w rs1 rs2 (imm : bv 12) L o0 o v,
    fetch_word segs pc = Some w -> is_ecall w = false ->
    decode_any w = Some (Store SZ4 rs1 rs2 imm, 4%Z) ->
    getr regs rs1 = at_ d o0 -> (o0 + bv_signed imm = o)%Z ->
    getr regs rs2 = v -> word_to_le_bytes 4 v = repeat (cbyte cv) 4 ->
    0 <= o -> o + 4 <= n ->
    RiscvSemantics.step segs (mkst regs pc (CF L) rom) =
    MachineOk (mkst regs (v_addi pc 4) (CF ((o, 4) :: L)) rom).
  Proof.
    intros regs pc rom w rs1 rs2 imm L o0 o v Hf He Hdc Hrs1 Ho Hrs2 Hv H0 H1.
    replace ((o, 4) :: L) with ((o, Z.of_nat 4) :: L) by reflexivity.
    rewrite <- (cfill_store mem0 d n (cbyte cv) Hnw L o 4) by lia.
    rewrite <- Hv.
    eapply step_sw_at; [exact Hf | exact He | exact Hdc | | exact Hrs2 |].
    - rewrite Hrs1, at_addi, Ho. reflexivity.
    - apply (cfill_store_ok mem0 d n (cbyte cv) Hnw segs); assumption || lia.
  Qed.

  #[using="Hnw Hok"] Lemma cf_sd : forall regs pc rom w rs1 rs2 (imm : bv 12) L o0 o v,
    fetch_word segs pc = Some w -> is_ecall w = false ->
    decode_any w = Some (Store SZ8 rs1 rs2 imm, 4%Z) ->
    getr regs rs1 = at_ d o0 -> (o0 + bv_signed imm = o)%Z ->
    getr regs rs2 = v -> word_to_le_bytes 8 v = repeat (cbyte cv) 8 ->
    0 <= o -> o + 8 <= n ->
    RiscvSemantics.step segs (mkst regs pc (CF L) rom) =
    MachineOk (mkst regs (v_addi pc 4) (CF ((o, 8) :: L)) rom).
  Proof.
    intros regs pc rom w rs1 rs2 imm L o0 o v Hf He Hdc Hrs1 Ho Hrs2 Hv H0 H1.
    replace ((o, 8) :: L) with ((o, Z.of_nat 8) :: L) by reflexivity.
    rewrite <- (cfill_store mem0 d n (cbyte cv) Hnw L o 8) by lia.
    rewrite <- Hv.
    eapply step_sd_at; [exact Hf | exact He | exact Hdc | | exact Hrs2 |].
    - rewrite Hrs1, at_addi, Ho. reflexivity.
    - apply (cfill_store_ok mem0 d n (cbyte cv) Hnw segs); assumption || lia.
  Qed.
End Stores.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition ms_clob : list reg := [11; 12; 13; 14; 15; 16]%bv.
Definition ms_agree (regs regs' : bvmap 5 word) : Prop :=
  regs_agree (fun r => In r ms_clob) regs regs'.

Lemma ms_agree_refl : forall regs, ms_agree regs regs.
Proof. intros regs. apply regs_agree_refl. Qed.

Lemma ms_agree_trans : forall r1 r2 r3, ms_agree r1 r2 -> ms_agree r2 r3 -> ms_agree r1 r3.
Proof. intros r1 r2 r3. apply regs_agree_trans. Qed.

Lemma ms_agree_upd : forall regs regs' (rd : reg) v,
  ms_agree regs regs' -> In rd ms_clob -> ms_agree regs (regupd regs' rd v).
Proof. intros regs regs' rd v H Hin. apply regs_agree_upd; assumption. Qed.

Lemma ms_agree_getr : forall regs regs' (r : reg),
  ms_agree regs regs' -> ~ In r ms_clob -> getr regs' r = getr regs r.
Proof. intros regs regs' r H Hn. apply H. exact Hn. Qed.

Lemma ms_agree_keeps : forall regs regs', ms_agree regs regs' -> keeps regs regs'.
Proof.
  intros regs regs' H r Hr. apply H. unfold callee_kept in Hr. unfold ms_clob. cbn [In] in *.
  intros Hc. decompose [or] Hr; subst; decompose [or] Hc; try discriminate; auto.
Qed.

Ltac in_clob := cbn [ms_clob In]; repeat first [ left; reflexivity | right ].
Ltac solve_ms_agree :=
  repeat (apply ms_agree_upd; [| in_clob]); first [apply ms_agree_refl | assumption].
End MemsetLib.

(* [comment removed for export] *)
Module AxNfCodec.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From Corelib Require Import PrimString.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require Import AxSymExec3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Export PrimString.PStringNotations.

Module NFC.
Import AX2.

(* [comment removed for export] *)
Definition zd (d : int) : Z :=
  if (d <? 8)%uint63 then
    if (d <? 4)%uint63 then (if (d <? 2)%uint63 then (if (d =? 0)%uint63 then 0 else 1) else (if (d =? 2)%uint63 then 2 else 3))
    else (if (d <? 6)%uint63 then (if (d =? 4)%uint63 then 4 else 5) else (if (d =? 6)%uint63 then 6 else 7))
  else
    if (d <? 12)%uint63 then (if (d <? 10)%uint63 then (if (d =? 8)%uint63 then 8 else 9) else (if (d =? 10)%uint63 then 10 else 11))
    else (if (d <? 14)%uint63 then (if (d =? 12)%uint63 then 12 else 13) else (if (d =? 14)%uint63 then 14 else 15)).

Definition cdig (c : int) : int := if (c <=? 39)%uint63 then (c - 35)%uint63 else if (c <=? 47)%uint63 then (c - 38)%uint63 else 10%uint63.

Fixpoint num_go (f : nat) (s : string) (p : int) (acc : Z) : Z * int :=
  match f with
  | O => (acc, p)
  | S f' =>
      let c := PrimString.get s p in
      if ((48 <=? c)%uint63 && (c <=? 63)%uint63)%bool then ((acc * 16 + zd (c - 48)%uint63)%Z, (p + 1)%uint63)
      else num_go f' s (p + 1)%uint63 (acc * 11 + zd (cdig c))%Z
  end.
Definition dnum (s : string) (p : int) : Z * int := num_go 40 s p 0%Z.
Definition dz (s : string) (p : int) : Z * int :=
  let (n, p') := dnum s p in (if Z.odd n then (- Z.div2 n - 1)%Z else Z.div2 n, p').
Definition dnat (s : string) (p : int) : nat * int := let (n, p') := dnum s p in (Z.to_nat n, p').
Definition dbool (s : string) (p : int) : bool * int := let (n, p') := dnum s p in (Z.eqb n 1, p').

Definition aluop_of (n : Z) : aluop :=
  match n with
  | 0%Z => ALU_ADD | 1%Z => ALU_SUB | 2%Z => ALU_SLL | 3%Z => ALU_SLT | 4%Z => ALU_SLTU
  | 5%Z => ALU_XOR | 6%Z => ALU_SRL | 7%Z => ALU_SRA | 8%Z => ALU_OR | _ => ALU_AND end.
Definition mulop_of (n : Z) : mulop :=
  match n with
  | 0%Z => M_MUL | 1%Z => M_MULH | 2%Z => M_MULHSU | 3%Z => M_MULHU
  | 4%Z => M_DIV | 5%Z => M_DIVU | 6%Z => M_REM | _ => M_REMU end.
Definition bc_of (n : Z) : branch_cond :=
  match n with 0%Z => BC_EQ | 1%Z => BC_NE | 2%Z => BC_LT | 3%Z => BC_GE | 4%Z => BC_LTU | _ => BC_GEU end.

Fixpoint dexpr (f : nat) (s : string) (p : int) : expr * int :=
  match f with
  | O => (ELit 0, p)
  | S f' =>
      let (t, p1) := dnum s p in
      match t with
      | 0%Z => let (z, p2) := dz s p1 in (ELit z, p2)
      | 1%Z => let (n, p2) := dnat s p1 in (EVar n, p2)
      | 2%Z => let (o, p2) := dnum s p1 in let (a, p3) := dexpr f' s p2 in let (b, p4) := dexpr f' s p3 in (EAlu (aluop_of o) a b, p4)
      | 3%Z => let (o, p2) := dnum s p1 in let (a, p3) := dexpr f' s p2 in let (b, p4) := dexpr f' s p3 in (EAluw (aluop_of o) a b, p4)
      | 4%Z => let (o, p2) := dnum s p1 in let (a, p3) := dexpr f' s p2 in let (b, p4) := dexpr f' s p3 in (EMd (mulop_of o) a b, p4)
      | 5%Z => let (o, p2) := dnum s p1 in let (a, p3) := dexpr f' s p2 in let (b, p4) := dexpr f' s p3 in (EMdw (mulop_of o) a b, p4)
      | 6%Z => let (sx, p2) := dbool s p1 in let (lo, p3) := dnat s p2 in let (n, p4) := dnat s p3 in
               let (e, p5) := dexpr f' s p4 in (EExt sx lo n e, p5)
      | _ => let (sx, p2) := dbool s p1 in let (k, p3) := dnat s p2 in let (i, p4) := dz s p3 in
             let (n, p5) := dnat s p4 in (EBlob sx k i n, p5)
      end
  end.
Definition de (s : string) (p : int) : expr * int := dexpr 1000 s p.
Definition dsa (s : string) (p : int) : saddr * int := let (b, p1) := de s p in let (o, p2) := dz s p1 in (SA b o, p2).
Definition dse (s : string) (p : int) : sentry * int :=
  let (a, p1) := dsa s p in let (w, p2) := dnat s p1 in let (v, p3) := de s p2 in (SE a w v, p3).
Definition dke (s : string) (p : int) : kentry * int :=
  let (t, p1) := dnum s p in
  match t with
  | 0%Z => let (a, p2) := dsa s p1 in let (w, p3) := dnat s p2 in let (v, p4) := de s p3 in (KWord a w v, p4)
  | 1%Z => let (a, p2) := dsa s p1 in let (n, p3) := de s p2 in (KZero a n, p3)
  | 2%Z => let (a, p2) := dsa s p1 in let (n, p3) := de s p2 in let (k, p4) := dnat s p3 in (KBlob a n k, p4)
  | 3%Z => let (lo, p2) := dz s p1 in let (hi, p3) := dz s p2 in (KImg lo hi, p3)
  | 4%Z => let (e, p2) := de s p1 in let (m, p3) := dz s p2 in (KAlign e m, p3)
  | 5%Z => let (e, p2) := de s p1 in let (lo, p3) := dz s p2 in let (hi, p4) := dz s p3 in (KRange e lo hi, p4)
  | 6%Z => let (a, p2) := dsa s p1 in let (n, p3) := de s p2 in (KWr a n, p3)
  | 7%Z => let (a1, p2) := dsa s p1 in let (n1, p3) := de s p2 in let (a2, p4) := dsa s p3 in let (n2, p5) := de s p4 in
           (KDisj a1 n1 a2 n2, p5)
  | 8%Z => let (a, p2) := dsa s p1 in let (n, p3) := de s p2 in let (c, p4) := dz s p3 in (KFill a n c, p4)
  | _ => let (a, p2) := dsa s p1 in let (n, p3) := de s p2 in (KUnk a n, p3)
  end.
Definition dsc (s : string) (p : int) : sidecond * int :=
  let (t, p1) := dnum s p in
  match t with
  | 0%Z => let (tk, p2) := dbool s p1 in let (c, p3) := dnum s p2 in let (a, p4) := de s p3 in let (b, p5) := de s p4 in
           (SCBr tk (bc_of c) a b, p5)
  | 1%Z => let (a, p2) := dsa s p1 in let (n, p3) := de s p2 in (SCFlat a n, p3)
  | 2%Z => let (a1, p2) := dsa s p1 in let (n1, p3) := de s p2 in let (a2, p4) := dsa s p3 in let (n2, p5) := de s p4 in
           (SCDisj a1 n1 a2 n2, p5)
  | 3%Z => let (a1, p2) := dsa s p1 in let (n1, p3) := de s p2 in let (a2, p4) := dsa s p3 in let (n2, p5) := de s p4 in
           (SCInside a1 n1 a2 n2, p5)
  | 4%Z => let (a, p2) := dsa s p1 in let (n, p3) := dnat s p2 in (SCStoreOk a n, p3)
  | 5%Z => let (a, p2) := dsa s p1 in let (n, p3) := dnat s p2 in let (sx, p4) := dbool s p3 in let (e, p5) := de s p4 in
           (SCReadBase a n sx e, p5)
  | _ => let (a, p2) := de s p1 in let (b, p3) := de s p2 in (SCEq a b, p3)
  end.

Fixpoint dl_go {A : Type} (d : string -> int -> A * int) (s : string) (n : nat) (p : int) (acc : list A) : list A * int :=
  match n with O => (List.rev' acc, p) | S m => let (a, p') := d s p in dl_go d s m p' (a :: acc) end.
Definition dl {A : Type} (d : string -> int -> A * int) (s : string) (p : int) : list A * int :=
  let (n, p1) := dnat s p in dl_go d s n p1 [].
Definition dopt {A : Type} (d : string -> int -> A * int) (s : string) (p : int) : option A * int :=
  let (t, p1) := dnum s p in if Z.eqb t 0 then (None, p1) else let (a, p2) := d s p1 in (Some a, p2).

Definition dss (s : string) (p : int) : sym_state * int :=
  let (pc, p1) := dz s p in let (rg, p2) := dl de s p1 in let (lg, p3) := dl dse s p2 in let (kn, p4) := dl dke s p3 in
  let (nx, p5) := dnat s p4 in let (rv, p6) := dopt dsa s p5 in (SSR pc rg lg kn nx rv, p6).
Definition dscr (s : string) (p : int) : scripts * int :=
  let (a, p1) := dl dbool s p in let (b, p2) := dl de s p1 in let (c, p3) := dl dbool s p2 in (SCR a b c, p3).

(* [comment removed for export] *)
Definition d_run (s : string) : sym_state * list sidecond * scripts :=
  let (ss, p1) := dss s 0%uint63 in let (scs, p2) := dl dsc s p1 in let (scr, _) := dscr s p2 in (ss, scs, scr).
Definition d_car (s : string) : list kentry * list sidecond * list bool :=
  let (kn, p1) := dl dke s 0%uint63 in let (cs, p2) := dl dsc s p1 in let (hs, _) := dl dbool s p2 in (kn, cs, hs).
Definition d_kl (s : string) : list kentry := fst (dl dke s 0%uint63).
Definition d_ss (s : string) : sym_state := fst (dss s 0%uint63).
Definition d_el (s : string) : list expr := fst (dl de s 0%uint63).

End NFC.
End AxNfCodec.

(* [comment removed for export] *)
Module AsanAcctShape.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Monad Specs Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require CatSim__Common. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatSim.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AllocSim2__Common. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim2__Common.ShapeAlg. (* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanAcct__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require SpinAlg. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanAcct__Common.AsanAcct OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.SpinAlg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Section WithSegs.
Variable segs : list Segment.
Variable H : word -> bool.
Hypothesis HH : H_off_segments segs H.
Hypothesis Hwx : wx_segs_nowrap segs.

#[using="Type"] Lemma node_ok_same : OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanAcct__Common.AsanAcct.node_ok segs = OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim2__Common.ShapeAlg.node_ok segs.
Proof. reflexivity. Qed.

Let P_of (T : TSet) : config -> Prop := fun c => realizes segs c T.

Let P_of_silent1 (T : TSet) : forall c c',
    OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanAcct__Common.AsanAcct.node_ok segs c unit (fun _ => []) (fun _ => c') ->
    P_of T c' -> P_of T c :=
  fun c c' Hn Hr => rz_silent1 segs c c' T (cnode_lift_unit segs c _ _ Hn) Hr.

#[using="HH Hwx P_of P_of_silent1"] Theorem rz_step_restricted_T : forall A ms msr' model T,
  lazy_cover H (m_vm_lazy model) A -> A_wf A -> MInv A model ->
  m_halted model = None ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs (restrict H ms) = MachineOk msr' ->
  (forall model', MInv A model' -> same_but_materialized model model' ->
                  realizes segs (mkCfg (unrestrict H (ms_mem ms) msr') model') T) ->
  realizes segs (mkCfg ms model) T.
Proof.
  intros A ms msr' model T.
  exact (rz_step_restricted segs H HH Hwx (P_of T) (P_of_silent1 T) A ms msr' model).
Qed.

#[using="HH Hwx P_of P_of_silent1"] Theorem rz_msteps_restricted_T : forall A ms msr' model T,
  lazy_cover H (m_vm_lazy model) A -> A_wf A -> MInv A model ->
  m_halted model = None ->
  msteps segs (restrict H ms) msr' ->
  (forall model',
      MInv A model' -> same_but_materialized model model' ->
      hclean H msr' ->
      realizes segs (mkCfg (unrestrict H (ms_mem ms) msr') model') T) ->
  realizes segs (mkCfg ms model) T.
Proof.
  intros A ms msr' model T.
  exact (rz_msteps_restricted' segs H HH Hwx (P_of T) (P_of_silent1 T) A ms msr' model).
Qed.
(* [comment removed for export] *)
Let SP_of (T : TSet) : config -> Prop := fun c => srealizes segs c T.

Let SP_of_silent1 (T : TSet) : forall c c',
    OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanAcct__Common.AsanAcct.node_ok segs c unit (fun _ => []) (fun _ => c') ->
    SP_of T c' -> SP_of T c :=
  fun c c' Hn Hr => srz_silent1 segs c c' T (cnode_lift_unit segs c _ _ Hn) Hr.

#[using="HH Hwx SP_of SP_of_silent1"] Theorem srz_step_restricted_T : forall A ms msr' model T,
  lazy_cover H (m_vm_lazy model) A -> A_wf A -> MInv A model ->
  m_halted model = None ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs (restrict H ms) = MachineOk msr' ->
  (forall model', MInv A model' -> same_but_materialized model model' ->
                  srealizes segs (mkCfg (unrestrict H (ms_mem ms) msr') model') T) ->
  srealizes segs (mkCfg ms model) T.
Proof.
  intros A ms msr' model T.
  exact (rz_step_restricted segs H HH Hwx (SP_of T) (SP_of_silent1 T) A ms msr' model).
Qed.

#[using="HH Hwx SP_of SP_of_silent1"] Theorem srz_msteps_restricted_T : forall A ms msr' model T,
  lazy_cover H (m_vm_lazy model) A -> A_wf A -> MInv A model ->
  m_halted model = None ->
  msteps segs (restrict H ms) msr' ->
  (forall model',
      MInv A model' -> same_but_materialized model model' ->
      hclean H msr' ->
      srealizes segs (mkCfg (unrestrict H (ms_mem ms) msr') model') T) ->
  srealizes segs (mkCfg ms model) T.
Proof.
  intros A ms msr' model T.
  exact (rz_msteps_restricted' segs H HH Hwx (SP_of T) (SP_of_silent1 T) A ms msr' model).
Qed.
End WithSegs.
End AsanAcctShape.
