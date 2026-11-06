(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase MemImageType RiscvSemantics StackLayout State Run.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require StepTac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require PlacementSearch.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim.CatExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.StepTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim.Stre9ts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim.AllocSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.PlacementSearch.Foott1g.

Module ArgvEnv.
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require StepTac.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim.CatExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim.SeqExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.StepTac.

Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.

Section Scaffold.

  (* [comment removed for export] *)
  Variable segs : list Segment.

  (* [comment removed for export] *)
  Variable ph : PhdrInfo.

  Variable sp : word.
  Variable av ev : list (list byte).
  Variable uid : word.
  Variable hw : word.

  (* [comment removed for export] *)
  Variable rnd : EntryDraw.

  (* [comment removed for export] *)
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp ev.
  Hypothesis Hsp_lo : (sp_window_lo <= bv_unsigned sp)%Z.
  Hypothesis Hsp_hi : (bv_unsigned sp <= sp_window_hi)%Z.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)

  Lemma sp_hi_num : (bv_unsigned sp <= 0x800000000000)%Z.
  Proof. exact Hsp_hi. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Definition argcN : word := len_word av.

  Lemma u_argcN : bv_unsigned argcN = Z.of_nat (length av).
  Proof.
    pose proof (valid_argv_len av Hva).
    unfold argcN, len_word. apply u_Z2bv; lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma bsb_nw :
    (bv_unsigned sp + Z.of_nat (length (build_stack_bytes ph sp av ev uid hw rnd)) < 2^64)%Z.
  Proof.
    pose proof (bsb_bound ph sp av ev uid hw rnd Hva Hve). pose proof sp_hi_num. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Definition envp_ptr : word :=
    Z_to_bv 64 (bv_unsigned sp + 8 + 8 * Z.of_nat (length av) + 8).

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Definition wmem : word -> option byte := wrap_mem ph sp av ev uid hw rnd.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)

End Scaffold.
End ArgvEnv.

Module RefL1zx.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require StepTac.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim.CatExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim.SeqExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.StepTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.StoreOk.ArgvEnv.

Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
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

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

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

  Lemma lay_bsb_nw : (bv_unsigned sp + Z.of_nat (length bsb) < 2^64)%Z.
  Proof. exact (bsb_nw ph sp av ev uid hw rdraw Hva Hve Hsp_hi). Qed.

  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma bsb_decomp : exists strs_tail,
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

  Lemma len_argc_argv :
    length (word_le8 (len_word av)
            ++ flat_map word_le8 (fst (string_addrs (cat_string_base sp av ev) av)))
    = (8 + 8 * length av)%nat.
  Proof.
    rewrite length_app, length_n_to_le_8, length_flat_map_le8, length_string_addrs_fst. lia.
  Qed.

  Lemma len_envp_ptrs :
    length (flat_map word_le8 (fst (string_addrs (cat_env_base sp av ev) ev))) = (8 * length ev)%nat.
  Proof. rewrite length_flat_map_le8, length_string_addrs_fst. lia. Qed.

  (* [comment removed for export] *)
  Lemma read_argv_null :
    rdn segs stk (sp + nat_to_word (8 + 8 * length av)) 8%nat = Some (word_le8 (Z_to_bv 64 0)).
  Proof.
    destruct bsb_decomp as [tl E].
    pose proof (read_at_offset_image segs ph sp av ev uid hw rdraw _ (word_le8 (Z_to_bv 64 0)) _ 8%nat E
                  (length_n_to_le_8 _) lay_bsb_nw) as H.
    rewrite len_argc_argv in H. exact H.
  Qed.

  (* [comment removed for export] *)
  Lemma read_envp_ptr_k : forall k, (k < length ev)%nat ->
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
  Lemma read_envp_null :
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
  Lemma read_auxv_all :
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
  Lemma read_auxv_word : forall j, (j < 20)%nat ->
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
  Lemma bsb_random_split : exists pre,
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

  Lemma at_random_off : exists off : nat,
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

  (* [comment removed for export] *)

  (* [comment removed for export] *)


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma cat_envp_ptr_eq : forall k, (k < length ev)%nat ->
    cat_envp_ptr sp av ev k
    = sp + nat_to_word (cat_struct_size av ev + total_arg_bytes_nat av
                        + total_arg_bytes_nat (firstn k ev)).
  Proof.
    intros k Hk. unfold cat_envp_ptr. rewrite nth_string_addrs by exact Hk.
    unfold cat_env_base, cat_string_base. rewrite !nat_to_word_add_merge.
    rewrite Nat.add_assoc. reflexivity.
  Qed.

  Lemma total_firstn_ev_bound : forall k,
    (Z.of_nat (total_arg_bytes_nat (firstn k ev)) <= 131072)%Z.
  Proof.
    intros k. destruct Hve as [_ [Htot _]]. rewrite total_arg_bytes_Z in Htot.
    pose proof (total_arg_bytes_firstn_le k ev). lia.
  Qed.

  Lemma struct_av_bound :
    (Z.of_nat (cat_struct_size av ev + total_arg_bytes_nat av) <= 2107576)%Z.
  Proof.
    destruct Hva as [[Hl0 Hl] [Hta _]]. destruct Hve as [Hle _].
    rewrite total_arg_bytes_Z in Hta. unfold cat_struct_size, auxv_size. lia.
  Qed.

  Lemma u_cat_envp_ptr : forall k, (k < length ev)%nat ->
    bv_unsigned (cat_envp_ptr sp av ev k)
    = (bv_unsigned sp + Z.of_nat (cat_struct_size av ev + total_arg_bytes_nat av
                                 + total_arg_bytes_nat (firstn k ev)))%Z.
  Proof.
    intros k Hk. rewrite cat_envp_ptr_eq by exact Hk. rewrite word_add_nat.
    pose proof struct_av_bound. pose proof (total_firstn_ev_bound k).
    unfold sp_window_hi in Hsp_hi. unfold sp_window_lo in Hsp_lo.
    apply u_Z2bv; lia.
  Qed.

  Lemma cat_envp_ptr_nz : forall k, (k < length ev)%nat ->
    bv_unsigned (cat_envp_ptr sp av ev k) <> 0%Z.
  Proof.
    intros k Hk. rewrite u_cat_envp_ptr by exact Hk. unfold sp_window_lo in Hsp_lo. lia.
  Qed.

  Lemma u_cat_argv_ptr : forall k, (k < length av)%nat ->
    bv_unsigned (cat_argv_ptr sp av ev k)
    = (bv_unsigned sp + Z.of_nat (cat_struct_size av ev + total_arg_bytes_nat (firstn k av)))%Z.
  Proof.
    intros k Hk. rewrite cat_argv_ptr_offset by exact Hk. unfold cat_string_base.
    rewrite nat_to_word_add_merge, word_add_nat.
    pose proof struct_av_bound. pose proof (total_arg_bytes_firstn_le k av).
    unfold sp_window_hi in Hsp_hi. unfold sp_window_lo in Hsp_lo.
    apply u_Z2bv; lia.
  Qed.

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma auxv_words_eq : forall rnd,
    auxv_words ph rnd uid hw =
    [AT_PHDR; Z_to_bv 64 (Z.of_N (ph_addr ph)); AT_PHENT; Z_to_bv 64 (Z.of_N (ph_ent ph));
     AT_PHNUM; Z_to_bv 64 (Z.of_N (ph_num ph)); AT_HWCAP; hw; AT_PAGESZ; Z_to_bv 64 4096;
     AT_UID; uid; AT_EUID; uid; AT_SECURE; Z_to_bv 64 0;
     AT_RANDOM; rnd; AT_NULL; Z_to_bv 64 0].
  Proof. reflexivity. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

End Layout.
End RefL1zx.


Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
(* [comment removed for export] *)
Local Open Scope Z_scope.

(* [comment removed for export] *)
Definition mem_grows (m m' : word -> option byte) : Prop :=
  forall x, m x <> None -> m' x <> None.

Lemma mem_grows_refl : forall m, mem_grows m m.
Proof. intros m x H. exact H. Qed.

Lemma mem_grows_trans : forall m1 m2 m3,
  mem_grows m1 m2 -> mem_grows m2 m3 -> mem_grows m1 m3.
Proof. intros m1 m2 m3 H12 H23 x Hx. apply H23, H12, Hx. Qed.

(* [comment removed for export] *)
Lemma wview_grows : forall segs m m' x,
  mem_grows m m' ->
  wview segs m x <> None -> wview segs m' x <> None.
Proof.
  intros segs m m' x Hg Hx. unfold wview in *.
  destruct (m' x) as [b'|] eqn:Hm'; [discriminate|].
  destruct (m x) as [b|] eqn:Hm.
  - exfalso. apply (Hg x); [rewrite Hm; discriminate|exact Hm'].
  - exact Hx.
Qed.

Lemma store_ok_mono : forall segs n m m' a,
  mem_grows m m' ->
  store_ok segs m a n = true -> store_ok segs m' a n = true.
Proof.
  intros segs n; induction n as [|n IH]; intros m m' a Hg H; [reflexivity|].
  cbn [store_ok] in *.
  destruct (wview segs m a) as [b|] eqn:Hv; [|discriminate].
  destruct (wview segs m' a) as [b'|] eqn:Hv'.
  - apply (IH m m'); assumption.
  - exfalso. apply (wview_grows segs m m' a Hg); [rewrite Hv; discriminate|exact Hv'].
Qed.

(* [comment removed for export] *)

Lemma wbytes_grows : forall bs m a, mem_grows m (wbytes m a bs).
Proof.
  induction bs as [|b rest IH]; intros m a x Hx; [exact Hx|].
  cbn [wbytes]. apply IH.
  destruct (bv_eqb x a); [discriminate|exact Hx].
Qed.

Lemma apply_zeros_grows : forall zs m, mem_grows m (apply_zeros m zs).
Proof.
  intros zs m x Hx. unfold apply_zeros.
  destruct zs as [|z zs']; [exact Hx|].
  destruct (zeros_cover (z :: zs') x); [discriminate|exact Hx].
Qed.

Lemma zmem_grows : forall m b l, mem_grows m (zmem m b l).
Proof.
  intros m b l x Hx. unfold zmem.
  destruct (Z.leb _ _ && Z.ltb _ _)%bool; [discriminate|exact Hx].
Qed.

Lemma write_to_mem_grows : forall bs m a, mem_grows m (write_to_mem m a bs).
Proof.
  induction bs as [|b rest IH]; intros m a x Hx; [exact Hx|].
  cbn [write_to_mem]. apply IH.
  destruct (bv_eqb x a); [discriminate|exact Hx].
Qed.

Lemma apply_writes_grows : forall ws m, mem_grows m (apply_writes m ws).
Proof.
  induction ws as [|w ws' IH]; intros m x Hx.
  - exact Hx.
  - destruct w as [a bs]. cbn [apply_writes].
    apply IH. apply write_to_mem_grows. exact Hx.
Qed.

(* [comment removed for export] *)
Lemma store_ok_of_all : forall segs n m a,
  bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
  (forall x : word,
      bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat n ->
      wview segs m x <> None) ->
  store_ok segs m a n = true.
Proof.
  intros segs n; induction n as [|n IH]; intros m a Hnw Hall; [reflexivity|].
  cbn [store_ok].
  destruct (wview segs m a) as [b|] eqn:Hv.
  2: { exfalso. refine (Hall a _ Hv). rewrite Nat2Z.inj_succ. lia. }
  (* [comment removed for export] *)
  destruct n as [|n']; [reflexivity|].
  rewrite Nat2Z.inj_succ in Hnw.
  assert (Hu1 : bv_unsigned (a + 1) = bv_unsigned a + 1)
    by (apply u_add1; rewrite Nat2Z.inj_succ in Hnw; lia).
  apply IH.
  - rewrite Hu1. lia.
  - intros x Hx. rewrite Hu1 in Hx. apply Hall.
    rewrite Nat2Z.inj_succ. lia.
Qed.

(* [comment removed for export] *)
Lemma wrap_mem_window_defined : forall ph sp argv envp (x : word) uid hw rnd,
  bv_unsigned sp - stack_max_size <= bv_unsigned x ->
  bv_unsigned x < bv_unsigned sp ->
  wrap_mem ph sp argv envp uid hw rnd x <> None.
Proof.
  intros ph sp argv envp x uid hw rnd Hlo Hhi. unfold wrap_mem.
  destruct (stack_to_mem sp (entry_stack_image ph sp argv envp uid hw rnd) x) as [b|];
    [discriminate|].
  rewrite (proj2 (Z.leb_le _ _) Hlo), (proj2 (Z.ltb_lt _ _) Hhi).
  cbn. discriminate.
Qed.

Lemma store_ok_wrap_window : forall segs ph sp argv envp a n uid hw rnd,
  bv_unsigned sp - stack_max_size <= bv_unsigned a ->
  bv_unsigned a + Z.of_nat n <= bv_unsigned sp ->
  store_ok segs (wrap_mem ph sp argv envp uid hw rnd) a n = true.
Proof.
  intros segs ph sp argv envp a n uid hw rnd Hlo Hhi.
  assert (Hsp : bv_unsigned sp < 2 ^ 64) by apply bv_unsigned_in_range.
  apply store_ok_of_all; [lia|].
  intros x Hx. unfold wview.
  destruct (wrap_mem ph sp argv envp uid hw rnd x) as [b|] eqn:Hw; [discriminate|].
  exfalso. revert Hw. apply wrap_mem_window_defined; lia.
Qed.

(* [comment removed for export] *)
Lemma store_ok_zeros_hit : forall segs m zs a n,
  zs <> [] ->
  bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
  (forall x : word,
      bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat n ->
      zeros_cover zs x = true) ->
  store_ok segs (apply_zeros m zs) a n = true.
Proof.
  intros segs m zs a n Hne Hnw Hcov.
  apply store_ok_of_all; [exact Hnw|].
  intros x Hx. unfold wview, apply_zeros.
  destruct zs as [|z zs']; [contradiction|].
  rewrite (Hcov x Hx). discriminate.
Qed.

(* [comment removed for export] *)
Lemma store_ok_zmem : forall segs m (b l a : word) (n : nat),
  bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
  bv_unsigned b <= bv_unsigned a ->
  bv_unsigned a + Z.of_nat n <= bv_unsigned b + bv_unsigned l ->
  store_ok segs (zmem m b l) a n = true.
Proof.
  intros segs m b l a n Hnw Hlo Hhi.
  apply store_ok_of_all; [exact Hnw|].
  intros x Hx. unfold wview, zmem.
  rewrite (proj2 (Z.leb_le _ _)) by lia.
  rewrite (proj2 (Z.ltb_lt _ _)) by lia.
  cbn. discriminate.
Qed.

(* [comment removed for export] *)
Definition store_grant_ok (segs : list Segment) (m : word -> option byte)
                    (b l : word) : Prop :=
  forall (a : word) (n : nat),
    bv_unsigned b <= bv_unsigned a ->
    bv_unsigned a + Z.of_nat n <= bv_unsigned b + bv_unsigned l ->
    store_ok segs m a n = true.

Lemma store_grant_zmem : forall segs m b l,
  bv_unsigned b + bv_unsigned l <= 2 ^ 64 ->
  store_grant_ok segs (zmem m b l) b l.
Proof.
  intros segs m b l Hnw a n Hlo Hhi. apply store_ok_zmem; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma store_grant_mono : forall segs m m' b l,
  mem_grows m m' -> store_grant_ok segs m b l -> store_grant_ok segs m' b l.
Proof.
  intros segs m m' b l Hg H a n Hlo Hhi.
  eapply store_ok_mono; [exact Hg|]. apply H; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma store_ok_wseg : forall segs m a n,
  wseg_ok segs a n = true -> store_ok segs m a n = true.
Proof.
  intros segs m a n; revert a m; induction n as [|n IH]; intros a m H; [reflexivity|].
  cbn [wseg_ok] in H.
  destruct (find_segment segs (bv_unsigned a) 1) as [seg|] eqn:Hseg; [|discriminate].
  apply andb_true_iff in H as [H Hrec].
  apply andb_true_iff in H as [Hwr Hbyte].
  destruct (segment_byte_at (seg_bytes seg)
              (Z.to_N (bv_unsigned a - Z.of_N (seg_base seg)))) as [b|] eqn:Hb;
    [|discriminate].
  cbn [store_ok]. unfold wview at 1.
  destruct (m a) as [b0|]; [apply IH, Hrec|].
  rewrite Hseg, Hwr, Hb. apply IH, Hrec.
Qed.

(* [comment removed for export] *)
Lemma store_ok_all : forall segs m n a,
  bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
  store_ok segs m a n = true ->
  forall x : word,
    bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat n ->
    wview segs m x <> None.
Proof.
  intros segs m n; induction n as [|n IH]; intros a Hnw H x Hx;
    [cbn in Hx; lia|].
  cbn [store_ok] in H.
  destruct (wview segs m a) as [b|] eqn:Hv; [|discriminate].
  rewrite Nat2Z.inj_succ in Hnw, Hx.
  destruct (Z.eq_dec (bv_unsigned x) (bv_unsigned a)) as [Heq|Hne].
  { assert (x = a) by (apply bv_eq; exact Heq). subst x.
    rewrite Hv. discriminate. }
  (* [comment removed for export] *)
  assert (Hn : (1 <= Z.of_nat n)%Z) by lia.
  assert (Hu1 : bv_unsigned (a + 1) = bv_unsigned a + 1) by (apply u_add1; lia).
  (* [comment removed for export] *)
  eapply IH; [ | exact H | ]; lia.
Qed.

Lemma store_ok_sub : forall segs m (lo a : word) (N n : nat),
  bv_unsigned lo + Z.of_nat N <= 2 ^ 64 ->
  store_ok segs m lo N = true ->
  bv_unsigned lo <= bv_unsigned a ->
  bv_unsigned a + Z.of_nat n <= bv_unsigned lo + Z.of_nat N ->
  store_ok segs m a n = true.
Proof.
  intros segs m lo a N n Hnw Hok Hl Hh.
  apply store_ok_of_all; [lia|].
  intros x Hx. apply (store_ok_all segs m N lo Hnw Hok). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma store_ok_read_aux : forall segs m n (a : word),
  store_ok segs m a n = true ->
  exists w, read_bytes_aux (wview segs m) a n = Some w.
Proof.
  intros segs m n; induction n as [|n IH]; intros a H.
  - exists []. reflexivity.
  - cbn [store_ok] in H. cbn [read_bytes_aux].
    destruct (wview segs m a) as [b|] eqn:Hv; [|discriminate].
    destruct (IH (a + 1)%bv H) as [w Hw]. rewrite Hw. exists (b :: w). reflexivity.
Qed.

Lemma store_ok_wbuf : forall segs ms (buf cnt : word),
  store_ok segs (ms_mem ms) buf (word_to_nat cnt) = true ->
  exists w, read_bytes_map (ms_writable_byte segs ms) buf cnt = Some w.
Proof.
  intros segs ms buf cnt H.
  rewrite read_bytes_map_eq. unfold ms_writable_byte.
  apply store_ok_read_aux. exact H.
Qed.

(* [comment removed for export] *)
Lemma of_nat_word_to_nat : forall w : word,
  Z.of_nat (word_to_nat w) = bv_unsigned w.
Proof.
  intro w. unfold word_to_nat. pose proof (u64_range w). lia.
Qed.

(* [comment removed for export] *)
Lemma store_grant_wbuf : forall segs ms (b l buf cnt : word),
  store_grant_ok segs (ms_mem ms) b l ->
  bv_unsigned b <= bv_unsigned buf ->
  bv_unsigned buf + bv_unsigned cnt <= bv_unsigned b + bv_unsigned l ->
  exists w, read_bytes_map (ms_writable_byte segs ms) buf cnt = Some w.
Proof.
  intros segs ms b l buf cnt Hg Hlo Hhi.
  apply store_ok_wbuf, Hg; rewrite ?of_nat_word_to_nat; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma zmem_wbuf : forall segs ms m (b l buf cnt : word),
  mem_grows (zmem m b l) (ms_mem ms) ->
  bv_unsigned b + bv_unsigned l <= 2 ^ 64 ->
  bv_unsigned b <= bv_unsigned buf ->
  bv_unsigned buf + bv_unsigned cnt <= bv_unsigned b + bv_unsigned l ->
  exists w, read_bytes_map (ms_writable_byte segs ms) buf cnt = Some w.
Proof.
  intros segs ms m b l buf cnt Hgr Hnw Hlo Hhi.
  eapply store_grant_wbuf; [ | exact Hlo | exact Hhi ].
  eapply store_grant_mono; [exact Hgr|]. apply store_grant_zmem. exact Hnw.
Qed.

(* [comment removed for export] *)
Example drain_buffer_in_grant : forall segs ms m (b l buf cnt : word) a bs,
  ms_mem ms = wbytes (zmem m b l) a bs ->
  bv_unsigned b + bv_unsigned l <= 2 ^ 64 ->
  bv_unsigned b <= bv_unsigned buf ->
  bv_unsigned buf + bv_unsigned cnt <= bv_unsigned b + bv_unsigned l ->
  exists w, read_bytes_map (ms_writable_byte segs ms) buf cnt = Some w.
Proof.
  intros segs ms m b l buf cnt a bs Hm Hnw Hlo Hhi.
  eapply zmem_wbuf;
    [ rewrite Hm; apply wbytes_grows | exact Hnw | exact Hlo | exact Hhi ].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Inductive sokl_layer : Type :=
| SOKL_wbytes (a : word) (bs : list byte)
| SOKL_wtm (a : word) (bs : list byte)
| SOKL_zeros (zs : list (word * word))
| SOKL_writes (ws : list (word * list byte)).
Definition sokl_app (l : sokl_layer) (m : word -> option byte) : word -> option byte :=
  match l with
  | SOKL_wbytes a bs => wbytes m a bs
  | SOKL_wtm a bs => write_to_mem m a bs
  | SOKL_zeros zs => apply_zeros m zs
  | SOKL_writes ws => apply_writes m ws
  end.
Fixpoint sokl_layers (ls : list sokl_layer) (m : word -> option byte) : word -> option byte :=
  match ls with
  | [] => m
  | l :: ls' => sokl_app l (sokl_layers ls' m)
  end.
Lemma sokl_grows : forall ls m, mem_grows m (sokl_layers ls m).
Proof.
  induction ls as [|l ls IH]; intro m; cbn [sokl_layers]; [apply mem_grows_refl|].
  eapply mem_grows_trans; [apply IH|].
  destruct l; cbn [sokl_app]; [apply wbytes_grows | apply write_to_mem_grows | apply apply_zeros_grows | apply apply_writes_grows].
Qed.
Lemma store_ok_layers : forall segs n ls m a,
  store_ok segs m a n = true -> store_ok segs (sokl_layers ls m) a n = true.
Proof. intros segs n ls m a H. exact (store_ok_mono segs n m (sokl_layers ls m) a (sokl_grows ls m) H). Qed.
Ltac sokl_list M :=
  lazymatch M with
  | wbytes ?m ?a ?bs => let l := sokl_list m in uconstr:(@cons sokl_layer (SOKL_wbytes a bs) l)
  | write_to_mem ?m ?a ?bs => let l := sokl_list m in uconstr:(@cons sokl_layer (SOKL_wtm a bs) l)
  | apply_zeros ?m ?zs => let l := sokl_list m in uconstr:(@cons sokl_layer (SOKL_zeros zs) l)
  | apply_writes ?m ?ws => let l := sokl_list m in uconstr:(@cons sokl_layer (SOKL_writes ws) l)
  | _ => uconstr:(@nil sokl_layer)
  end.
Ltac sokl_base M :=
  lazymatch M with
  | wbytes ?m _ _ => sokl_base m
  | write_to_mem ?m _ _ => sokl_base m
  | apply_zeros ?m _ => sokl_base m
  | apply_writes ?m _ => sokl_base m
  | _ => M
  end.
Ltac store_ok_peel :=
  lazymatch goal with
  | |- store_ok ?segs ?M ?a ?n = true =>
      let b := sokl_base M in
      lazymatch b with
      | M => idtac
      | _ => let l := sokl_list M in
             refine ((store_ok_layers segs n l b a _) : store_ok segs M a n = true)
      end
  | |- _ => idtac
  end.

(* [comment removed for export] *)
Ltac store_ok_base :=
  first
    [ apply store_ok_wrap_window; unfold stack_max_size; u_norm; lia
    | eapply store_ok_zeros_hit;
      [ discriminate | u_norm; lia | intros; u_norm; lia ]
    | apply store_ok_zmem; u_norm; lia ].

(* [comment removed for export] *)
Ltac solve_store_ok :=
  store_ok_peel;
  first [ store_ok_base
        | eapply store_ok_mono; [apply zmem_grows|];
          store_ok_peel; store_ok_base ].

(* [comment removed for export] *)
(* [comment removed for export] *)
Create HintDb store_ok_db.

Ltac store_ok_grows := solve [ eauto with store_ok_db ].

Ltac solve_store_ok_inv :=
  first [ solve_store_ok
        | store_ok_peel;
          eapply store_ok_mono; [ store_ok_grows | ]; solve_store_ok ].

(* [comment removed for export] *)
Ltac solve_mem_grows :=
  repeat first
    [ solve [ eauto with store_ok_db ]
    | apply mem_grows_refl
    | eapply mem_grows_trans; [ | apply wbytes_grows ]
    | eapply mem_grows_trans; [ | apply zmem_grows ]
    | eapply mem_grows_trans; [ | apply write_to_mem_grows ]
    | eapply mem_grows_trans; [ | apply apply_zeros_grows ]
    | eapply mem_grows_trans; [ | apply apply_writes_grows ] ].
