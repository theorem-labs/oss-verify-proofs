(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require SimInv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require CatSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require CatSim PropExec.

Module CatExec.
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require CatSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require PropExec CatSim.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.CatSim.ExitSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.CatSim.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ms_read_bytes_aux_rdn : forall segs ms n addr,
  ms_rom ms = seg_rom segs ->
  ms_read_bytes_aux ms addr n = rdn segs (ms_mem ms) addr n.
Proof.
  intros segs ms n. induction n as [|n IH]; intros addr Hrom; [reflexivity|].
  cbn [ms_read_bytes_aux rdn]. unfold ms_read_byte. rewrite Hrom.
  destruct (ms_mem ms addr) as [b|].
  - rewrite IH by exact Hrom. reflexivity.
  - unfold seg_rom. destruct (memory_read segs addr 1) as [[|b r]|];
      try reflexivity; rewrite IH by exact Hrom; reflexivity.
Qed.

Lemma ms_read_bytes_rdn : forall segs ms addr len,
  ms_rom ms = seg_rom segs ->
  ms_read_bytes ms addr len = rdn segs (ms_mem ms) addr (word_to_nat len).
Proof. intros. unfold ms_read_bytes. apply ms_read_bytes_aux_rdn; assumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint wbytes (m : word -> option byte) (addr : word) (bs : list byte)
    : word -> option byte :=
  match bs with
  | [] => m
  | b :: rest => wbytes (fun a => if bv_eqb a addr then Some b else m a) (addr+1) rest
  end.

(* [comment removed for export] *)
Lemma wbytes_above : forall bs m (addr x : word),
  (bv_unsigned addr + Z.of_nat (length bs) <= bv_unsigned x)%Z ->
  wbytes m addr bs x = m x.
Proof.
  induction bs as [|b rest IH]; intros m addr x Hle; [reflexivity|].
  cbn [wbytes length] in *.
  pose proof (u64_range x) as Hx.
  assert (Hu1 : bv_unsigned (addr + 1) = (bv_unsigned addr + 1)%Z)
    by (apply u_add1; lia).
  rewrite IH by lia.
  cbv beta.
  assert (Hne : bv_eqb x addr = false)
    by (unfold bv_eqb; apply Z.eqb_neq; lia).
  rewrite Hne. reflexivity.
Qed.

Lemma rdn_wbytes_disjoint : forall segs bs m (addr a : word) n,
  (bv_unsigned addr + Z.of_nat (length bs) <= bv_unsigned a)%Z ->
  (bv_unsigned a + Z.of_nat n <= 2^64)%Z ->
  rdn segs (wbytes m addr bs) a n = rdn segs m a n.
Proof.
  intros segs bs m addr a n Hle Hnw. apply rdn_ext; [exact Hnw|].
  intros x Hx. apply wbytes_above. lia.
Qed.

(* [comment removed for export] *)
Lemma wbytes_below : forall bs m (addr x : word),
  (bv_unsigned addr + Z.of_nat (length bs) <= 2^64)%Z ->
  (bv_unsigned x < bv_unsigned addr)%Z ->
  wbytes m addr bs x = m x.
Proof.
  induction bs as [|b rest IH]; intros m addr x Hnw Hlt; [reflexivity|].
  cbn [wbytes length] in *.
  assert (Hne : bv_eqb x addr = false)
    by (unfold bv_eqb; apply Z.eqb_neq; lia).
  destruct rest as [|b' rest'].
  - cbn [wbytes]. rewrite Hne. reflexivity.
  - assert (Hu1 : bv_unsigned (addr + 1) = (bv_unsigned addr + 1)%Z)
      by (apply u_add1; cbn [length] in Hnw; lia).
    rewrite IH by lia.
    cbv beta. rewrite Hne. reflexivity.
Qed.

Lemma rdn_wbytes_below : forall segs bs m (addr a : word) n,
  (bv_unsigned a + Z.of_nat n <= bv_unsigned addr)%Z ->
  (bv_unsigned addr + Z.of_nat (length bs) <= 2^64)%Z ->
  rdn segs (wbytes m addr bs) a n = rdn segs m a n.
Proof.
  intros segs bs m addr a n Hle Hnw.
  pose proof (u64_range addr) as Ha.
  apply rdn_ext; [lia|].
  intros x Hx. apply wbytes_below; [exact Hnw|lia].
Qed.

(* [comment removed for export] *)
Lemma rdn_wbytes_out : forall segs bs m (addr a : word) n,
  (bv_unsigned a + Z.of_nat n <= bv_unsigned addr
   \/ bv_unsigned addr + Z.of_nat (length bs) <= bv_unsigned a)%Z ->
  (bv_unsigned a + Z.of_nat n <= 2^64)%Z ->
  (bv_unsigned addr + Z.of_nat (length bs) <= 2^64)%Z ->
  rdn segs (wbytes m addr bs) a n = rdn segs m a n.
Proof.
  intros segs bs m addr a n [Hb|Hd] Hnw Hnw'.
  - apply rdn_wbytes_below; [exact Hb | exact Hnw'].
  - apply rdn_wbytes_disjoint; [exact Hd | exact Hnw].
Qed.

Lemma length_Z_to_le_bytes : forall n z, length (Z_to_le_bytes n z) = n.
Proof.
  induction n as [|n IH]; intro z; [reflexivity|].
  cbn [Z_to_le_bytes length]. rewrite IH. reflexivity.
Qed.

Lemma length_N_to_le_bytes : forall n (v : word), length (word_to_le_bytes n v) = n.
Proof. intros. unfold word_to_le_bytes. apply length_Z_to_le_bytes. Qed.

(* [comment removed for export] *)
Lemma write_to_mem_wbytes : forall bs (m : word -> option byte) (addr : word),
  write_to_mem m addr bs = wbytes m addr bs.
Proof.
  induction bs as [|b rest IH]; intros m addr; [reflexivity|].
  cbn [write_to_mem wbytes]. apply IH.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma stack_max_size_val : stack_max_size = 8388608%Z.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma flat_map_app' : forall {A B : Type} (f : A -> list B) l1 l2,
  flat_map f (l1 ++ l2) = flat_map f l1 ++ flat_map f l2.
Proof.
  intros A B f l1 l2. induction l1 as [|x xs IH]; cbn; [reflexivity|].
  rewrite IH, app_assoc. reflexivity.
Qed.

Lemma skipn_nth : forall {A : Type} (l : list A) k d, (k < length l)%nat ->
  skipn k l = nth k l d :: skipn (S k) l.
Proof.
  induction l as [|x xs IH]; intros k d Hk; [cbn in Hk; lia|].
  destruct k as [|k']; [reflexivity|].
  cbn [skipn nth]. apply IH. cbn in Hk; lia.
Qed.

Lemma flat_map_split : forall {A B : Type} (f : A -> list B) l k d, (k < length l)%nat ->
  flat_map f l = flat_map f (firstn k l) ++ f (nth k l d) ++ flat_map f (skipn (S k) l).
Proof.
  intros A B f l k d Hk.
  rewrite <- (firstn_skipn k l) at 1.
  rewrite flat_map_app'.
  rewrite (skipn_nth l k d Hk). reflexivity.
Qed.

Lemma flat_map_le8_decomp : forall (l : list word) k, (k < length l)%nat ->
  flat_map word_le8 l =
  flat_map word_le8 (firstn k l) ++ word_le8 (nth k l (Z_to_bv 64 0))
    ++ flat_map word_le8 (skipn (S k) l).
Proof. intros l k Hk. apply (flat_map_split word_le8 l k (Z_to_bv 64 0) Hk). Qed.

Lemma flatten_strings_decomp : forall strs k, (k < length strs)%nat ->
  flatten_strings strs =
  flatten_strings (firstn k strs) ++ (nth k strs [] ++ [Z_to_bv 8 0])
    ++ flatten_strings (skipn (S k) strs).
Proof.
  intros strs k Hk.
  apply (flat_map_split (fun s => s ++ [Z_to_bv 8 0]) strs k [] Hk).
Qed.

Lemma total_arg_bytes_cons : forall s l,
  total_arg_bytes_nat (s :: l) = (length s + 1 + total_arg_bytes_nat l)%nat.
Proof. reflexivity. Qed.

Lemma total_arg_bytes_firstn_le : forall k l,
  (total_arg_bytes_nat (firstn k l) <= total_arg_bytes_nat l)%nat.
Proof.
  induction k as [|k IH]; intros l.
  - change (total_arg_bytes_nat (firstn 0 l)) with 0%nat. lia.
  - destruct l as [|s rest]; [cbn; lia|].
    cbn [firstn]. rewrite !total_arg_bytes_cons. specialize (IH rest). lia.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition cat_struct_size (av ev : list (list byte)) : nat :=
  (8 + (length av + 1) * 8 + (length ev + 1) * 8 + auxv_size)%nat.  (* [comment removed for export] *)

Definition cat_string_base (sp : word) (av ev : list (list byte)) : word :=
  sp + nat_to_word (cat_struct_size av ev).

Definition cat_env_base (sp : word) (av ev : list (list byte)) : word :=
  cat_string_base sp av ev + nat_to_word (total_arg_bytes_nat av).

(* [comment removed for export] *)
Definition cat_argv_ptr (sp : word) (av ev : list (list byte)) (k : nat) : word :=
  nth k (fst (string_addrs (cat_string_base sp av ev) av)) (Z_to_bv 64 0).

Lemma nth_string_addrs : forall strs (base : word) k, (k < length strs)%nat ->
  nth k (fst (string_addrs base strs)) (Z_to_bv 64 0)
  = base + nat_to_word (total_arg_bytes_nat (firstn k strs)).
Proof.
  induction strs as [|s rest IH]; intros base k Hk; [cbn in Hk; lia|].
  rewrite string_addrs_fst_structure.
  destruct k as [|k'].
  - cbn [nth firstn]. change (total_arg_bytes_nat []) with 0%nat.
    rewrite word_add_0. reflexivity.
  - cbn [nth]. rewrite (IH (base + len_word s + 1) k' ltac:(cbn in Hk; lia)).
    cbn [firstn]. rewrite total_arg_bytes_cons.
    rewrite len_word_nat, word1_nat, !nat_to_word_add_merge.
    f_equal. f_equal. lia.
Qed.

Lemma cat_argv_ptr_offset : forall sp av ev k, (k < length av)%nat ->
  cat_argv_ptr sp av ev k
  = cat_string_base sp av ev + nat_to_word (total_arg_bytes_nat (firstn k av)).
Proof. intros. unfold cat_argv_ptr. apply nth_string_addrs. assumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition cat_struct_prefix (ph : PhdrInfo) (sp : word) (av ev : list (list byte))
    (uid : word) (hw : word) : list byte :=
  word_le8 (len_word av)
  ++ flat_map word_le8 (fst (string_addrs (cat_string_base sp av ev) av))
  ++ word_le8 (Z_to_bv 64 0)
  ++ flat_map word_le8 (fst (string_addrs (cat_env_base sp av ev) ev))
  ++ word_le8 (Z_to_bv 64 0) ++ auxv_bytes ph (at_random_ptr sp av ev) uid hw.

Lemma length_cat_struct_prefix : forall ph sp av ev uid hw,
  length (cat_struct_prefix ph sp av ev uid hw) = cat_struct_size av ev.
Proof.
  intros ph sp av ev uid hw. unfold cat_struct_prefix, cat_struct_size.
  rewrite !length_app, !length_flat_map_le8, !length_string_addrs_fst,
    !length_n_to_le_8, length_auxv_bytes.
  lia.
Qed.

(* [comment removed for export] *)
Lemma bsb_argv_prefix : forall ph (sp : word) av ev uid hw rnd, exists tail,
  build_stack_bytes ph sp av ev uid hw rnd =
    word_le8 (len_word av)
    ++ flat_map word_le8 (fst (string_addrs (cat_string_base sp av ev) av))
    ++ tail.
Proof.
  intros ph sp av ev uid hw rnd. unfold build_stack_bytes.
  rewrite (string_addrs_pair av). cbv beta iota.
  rewrite (string_addrs_pair ev). cbv beta iota.
  eexists. rewrite <- !app_assoc. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma bsb_ptr_k : forall ph (sp : word) av ev k uid hw rnd, (k < length av)%nat -> exists post,
  build_stack_bytes ph sp av ev uid hw rnd =
    (word_le8 (len_word av)
      ++ flat_map word_le8 (firstn k (fst (string_addrs (cat_string_base sp av ev) av))))
    ++ word_le8 (nth k (fst (string_addrs (cat_string_base sp av ev) av)) (Z_to_bv 64 0))
    ++ post.
Proof.
  intros ph sp av ev k uid hw rnd Hk.
  destruct (bsb_argv_prefix ph sp av ev uid hw rnd) as [tail E].
  assert (Hk' : (k < length (fst (string_addrs (cat_string_base sp av ev) av)))%nat)
    by (rewrite length_string_addrs_fst; exact Hk).
  rewrite (flat_map_le8_decomp _ k Hk') in E.
  eexists. rewrite E. rewrite <- !app_assoc. reflexivity.
Qed.

Lemma read_argv_ptr_k : forall ph segs (sp : word) av ev k uid hw rnd, (k < length av)%nat ->
  (bv_unsigned sp + Z.of_nat (length (build_stack_bytes ph sp av ev uid hw rnd)) < 2^64)%Z ->
  rdn segs (stack_to_mem sp (entry_stack_image ph sp av ev uid hw rnd))
      (sp + nat_to_word (8 + 8 * k)) 8%nat
  = Some (word_le8 (cat_argv_ptr sp av ev k)).
Proof.
  intros ph segs sp av ev k uid hw rnd Hk Hnw.
  destruct (bsb_ptr_k ph sp av ev k uid hw rnd Hk) as [post E].
  pose proof (read_at_offset_image segs ph sp av ev uid hw rnd
    (word_le8 (len_word av)
      ++ flat_map word_le8 (firstn k (fst (string_addrs (cat_string_base sp av ev) av))))
    (word_le8 (nth k (fst (string_addrs (cat_string_base sp av ev) av)) (Z_to_bv 64 0)))
    post 8%nat E (length_n_to_le_8 _) Hnw) as H'.
  assert (Hlen : length (word_le8 (len_word av)
      ++ flat_map word_le8 (firstn k (fst (string_addrs (cat_string_base sp av ev) av))))
    = (8 + 8 * k)%nat).
  { rewrite length_app, length_n_to_le_8, length_flat_map_le8, firstn_length_le;
      [reflexivity | rewrite length_string_addrs_fst; lia]. }
  rewrite Hlen in H'.
  rewrite H'. unfold cat_argv_ptr. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma bsb_strings_split : forall ph (sp : word) av ev uid hw rnd, exists tail,
  build_stack_bytes ph sp av ev uid hw rnd = cat_struct_prefix ph sp av ev uid hw ++ flatten_strings av ++ tail.
Proof.
  intros ph sp av ev uid hw rnd. unfold build_stack_bytes, cat_struct_prefix, cat_env_base, cat_string_base.
  rewrite (string_addrs_pair av). cbv beta iota.
  rewrite (string_addrs_pair ev). cbv beta iota.
  eexists. rewrite <- !app_assoc. reflexivity.
Qed.

Lemma bsb_byte_k : forall ph (sp : word) av ev k uid hw rnd, (k < length av)%nat -> exists pre post,
  build_stack_bytes ph sp av ev uid hw rnd = pre ++ (nth k av [] ++ [Z_to_bv 8 0]) ++ post
  /\ length pre = (cat_struct_size av ev + total_arg_bytes_nat (firstn k av))%nat.
Proof.
  intros ph sp av ev k uid hw rnd Hk.
  destruct (bsb_strings_split ph sp av ev uid hw rnd) as [tail E].
  rewrite (flatten_strings_decomp av k Hk) in E.
  exists (cat_struct_prefix ph sp av ev uid hw ++ flatten_strings (firstn k av)).
  eexists.
  split.
  - rewrite E. rewrite <- !app_assoc. reflexivity.
  - rewrite length_app, length_cat_struct_prefix, length_flatten_strings. reflexivity.
Qed.

Lemma read_argv_byte_k : forall ph segs (sp : word) av ev k j uid hw rnd,
  (k < length av)%nat -> (j <= length (nth k av []))%nat ->
  (bv_unsigned sp + Z.of_nat (length (build_stack_bytes ph sp av ev uid hw rnd)) < 2^64)%Z ->
  rdn segs (stack_to_mem sp (entry_stack_image ph sp av ev uid hw rnd))
      (cat_argv_ptr sp av ev k + nat_to_word j) 1%nat
  = Some [nth j (nth k av [] ++ [Z_to_bv 8 0]) (Z_to_bv 8 0)].
Proof.
  intros ph segs sp av ev k j uid hw rnd Hk Hj Hnw.
  destruct (bsb_byte_k ph sp av ev k uid hw rnd Hk) as [pre [post [E Hlen]]].
  pose proof (read_byte_at_image segs ph sp av ev uid hw rnd
    pre (nth k av [] ++ [Z_to_bv 8 0]) post j E) as H'.
  rewrite Hlen in H'.
  replace (cat_argv_ptr sp av ev k + nat_to_word j)
    with (sp + nat_to_word (cat_struct_size av ev + total_arg_bytes_nat (firstn k av) + j)).
  2:{ rewrite (cat_argv_ptr_offset sp av ev k Hk). unfold cat_string_base.
      rewrite !nat_to_word_add_merge. f_equal. f_equal. lia. }
  apply H'; [rewrite length_app; cbn [length]; lia | exact Hnw].
Qed.

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

Definition byte_at (s : list byte) (k : nat) : byte :=
  nth k (s ++ [Z_to_bv 8 0]) (Z_to_bv 8 0).

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma valid_argv_len : forall av, valid_argv av ->
  (Z.of_nat (length av) <= 1024)%Z.
Proof. intros av [Hlen _]. lia. Qed.

(* [comment removed for export] *)

Lemma valid_argv_str_len : forall av k, valid_argv av -> (k < length av)%nat ->
  (Z.of_nat (length (nth k av [])) <= 131071)%Z.
Proof.
  intros av k [_ [_ [Hstr _]]] Hk.
  rewrite Forall_forall in Hstr.
  specialize (Hstr _ (nth_In av [] Hk)). exact Hstr.
Qed.

Lemma valid_argv_str_nz : forall av k, valid_argv av -> (k < length av)%nat ->
  ~ In (Z_to_bv 8 0) (nth k av []).
Proof.
  intros av k [_ [_ [_ [Hnz _]]]] Hk.
  rewrite Forall_forall in Hnz. apply Hnz. apply nth_In. exact Hk.
Qed.

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
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition pend (regs : bvmap 5 word) (pc : word) (mem rom : word -> option byte)
    : machine_state :=
  {| ms_regs := regs; ms_fregs := bvmap_empty; ms_pc_val := pc; ms_svc_pending := Some (Z_to_bv 64 64);
     ms_resv := None; ms_fcsr := Z_to_bv 32 0; ms_mem := mem; ms_rom := rom |}.

(* [comment removed for export] *)
Lemma adv_set : forall regs pc sv mem rom v,
  advance_past_svc (set_gpr0
    {| ms_regs := regs; ms_fregs := bvmap_empty; ms_pc_val := pc; ms_svc_pending := sv; ms_resv := None; ms_fcsr := Z_to_bv 32 0;
       ms_mem := mem; ms_rom := rom |} v)
  = mkst (regupd regs 10 v) (v_addi pc 4) mem rom.
Proof.
  intros regs pc sv mem rom v.
  unfold advance_past_svc, set_gpr0, RiscvSemantics.set_reg, ms_pc.
  rewrite bv_eqb_neq by (intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate).
  cbv beta iota.
  cbn [ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom].
  unfold mkst, regupd.
  rewrite b_npc4. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
End CatExec.

Module SeqExec.
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require CatSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require PropExec CatSim.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.CatSim.ExitSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.CatSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.CatExec.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition v_jalr (x : word) (imm : Z) : word := Z_to_bv 64 (jalr_tgtZ x imm).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma step_jal_link : forall segs regs pc mem rom w rd (imm : bv 21),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Jal rd imm, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_addi pc 4))
                  (btgt pc (bv_signed imm)) mem rom).
Proof.
  intros segs regs pc mem rom w rd imm Hfetch Hecall Hdecode.
  step_pipeline Hfetch Hecall Hdecode.
  destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4, ?b_addsext;
    reflexivity.
Qed.

(* [comment removed for export] *)
Lemma step_jalr : forall segs regs pc mem rom w rd rs1 (imm : bv 12),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Jalr rd rs1 imm, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_addi pc 4))
                  (v_jalr (getr regs rs1) (bv_signed imm)) mem rom).
Proof.
  intros segs regs pc mem rom w rd rs1 imm Hf He Hd.
  exact (step_jalr_gen segs regs pc mem rom w rd rs1 imm Hf He Hd).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma step_sd_val : forall segs regs pc mem rom w (rs1 rs2 : reg) (imm : bv 12),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Store SZ8 rs1 rs2 imm, 4%Z) ->
  RiscvSemantics.store_ok segs mem
    (v_addi (getr regs rs1) (bv_signed imm)) 8%nat = true ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs (v_addi pc 4)
    (wbytes mem (v_addi (getr regs rs1) (bv_signed imm))
            (word_to_le_bytes 8 (getr regs rs2))) rom).
Proof.
  intros segs regs pc mem rom w rs1 rs2 imm Hfetch Hecall Hdecode Hok.
  step_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  unfold getr in Hok; rewrite ?bv_eqb0_is_x0 in Hok.
  rewrite b_addsext.
  rewrite Hok; cbv beta iota.
  rewrite write_to_mem_wbytes, b_npc4.
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma step_sd_at : forall segs regs pc mem rom w (rs1 rs2 : reg) (imm : bv 12) (a v : word),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Store SZ8 rs1 rs2 imm, 4%Z) ->
  v_addi (getr regs rs1) (bv_signed imm) = a ->
  getr regs rs2 = v ->
  RiscvSemantics.store_ok segs mem a 8%nat = true ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs (v_addi pc 4) (wbytes mem a (word_to_le_bytes 8 v)) rom).
Proof.
  intros segs regs pc mem rom w rs1 rs2 imm a v Hf He Hd Ha Hv Hok.
  rewrite (step_sd_val segs regs pc mem rom w rs1 rs2 imm Hf He Hd).
  - rewrite Ha, Hv. reflexivity.
  - rewrite Ha. exact Hok.
Qed.

(* [comment removed for export] *)
Lemma step_addi_at : forall segs regs pc mem rom w rd rs (imm : bv 12) v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (OpImm ALU_ADD rd rs imm, 4%Z) ->
  bv_eqb rd 0 = false ->
  v_addi (getr regs rs) (bv_signed imm) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rd rs imm v Hf He Hd Hrd Hv.
  rewrite (step_addi segs regs pc mem rom w rd rs imm Hf He Hd).
  rewrite Hrd, Hv. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma step_add_at : forall segs regs pc mem rom w rd rs1 rs2 v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Op ALU_ADD rd rs1 rs2, 4%Z) ->
  bv_eqb rd 0 = false ->
  v_add (getr regs rs1) (getr regs rs2) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rd rs1 rs2 v Hf He Hd Hrd Hv.
  rewrite (step_add segs regs pc mem rom w rd rs1 rs2 Hf He Hd).
  rewrite Hrd, Hv. reflexivity.
Qed.

Lemma step_sub_at : forall segs regs pc mem rom w rd rs1 rs2 v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Op ALU_SUB rd rs1 rs2, 4%Z) ->
  bv_eqb rd 0 = false ->
  v_sub (getr regs rs1) (getr regs rs2) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rd rs1 rs2 v Hf He Hd Hrd Hv.
  rewrite (step_sub segs regs pc mem rom w rd rs1 rs2 Hf He Hd).
  rewrite Hrd, Hv. reflexivity.
Qed.

Lemma step_lui_at : forall segs regs pc mem rom w rd (imm : bv 20) v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Lui rd imm, 4%Z) ->
  bv_eqb rd 0 = false ->
  v_lui (Z.shiftl (bv_signed imm) 12) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rd imm v Hf He Hd Hrd Hv.
  rewrite (step_lui segs regs pc mem rom w rd imm Hf He Hd).
  rewrite Hrd, Hv. reflexivity.
Qed.

Lemma step_auipc_at : forall segs regs pc mem rom w rd (imm : bv 20) v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Auipc rd imm, 4%Z) ->
  bv_eqb rd 0 = false ->
  v_auipc pc (Z.shiftl (bv_signed imm) 12) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rd imm v Hf He Hd Hrd Hv.
  rewrite (step_auipc segs regs pc mem rom w rd imm Hf He Hd).
  rewrite Hrd, Hv. reflexivity.
Qed.

Lemma step_addiw_at : forall segs regs pc mem rom w rd rs (imm : bv 12) v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (OpImm32 rd rs imm, 4%Z) ->
  bv_eqb rd 0 = false ->
  v_addiw (getr regs rs) (bv_signed imm) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rd rs imm v Hf He Hd Hrd Hv.
  rewrite (step_addiw segs regs pc mem rom w rd rs imm Hf He Hd).
  rewrite Hrd, Hv. reflexivity.
Qed.

Lemma step_sltiu_at : forall segs regs pc mem rom w rd rs (imm : bv 12) v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (OpImm ALU_SLTU rd rs imm, 4%Z) ->
  bv_eqb rd 0 = false ->
  v_sltiu (getr regs rs) (bv_signed imm) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rd rs imm v Hf He Hd Hrd Hv.
  rewrite (step_sltiu segs regs pc mem rom w rd rs imm Hf He Hd).
  rewrite Hrd, Hv. reflexivity.
Qed.

Lemma step_xori_at : forall segs regs pc mem rom w rd rs (imm : bv 12) v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (OpImm ALU_XOR rd rs imm, 4%Z) ->
  bv_eqb rd 0 = false ->
  v_xori (getr regs rs) (bv_signed imm) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rd rs imm v Hf He Hd Hrd Hv.
  rewrite (step_xori segs regs pc mem rom w rd rs imm Hf He Hd).
  rewrite Hrd, Hv. reflexivity.
Qed.

Lemma step_mul_at : forall segs regs pc mem rom w rd rs1 rs2 v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Mul M_MUL rd rs1 rs2, 4%Z) ->
  bv_eqb rd 0 = false ->
  v_mul (getr regs rs1) (getr regs rs2) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rd rs1 rs2 v Hf He Hd Hrd Hv.
  rewrite (step_mul segs regs pc mem rom w rd rs1 rs2 Hf He Hd).
  rewrite Hrd, Hv. reflexivity.
Qed.

Lemma step_andi_at : forall segs regs pc mem rom w rd rs (imm : bv 12) v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (OpImm ALU_AND rd rs imm, 4%Z) ->
  bv_eqb rd 0 = false ->
  v_andi (getr regs rs) (bv_signed imm) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rd rs imm v Hf He Hd Hrd Hv.
  rewrite (step_andi segs regs pc mem rom w rd rs imm Hf He Hd).
  rewrite Hrd, Hv. reflexivity.
Qed.

Lemma step_ori_at : forall segs regs pc mem rom w rd rs (imm : bv 12) v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (OpImm ALU_OR rd rs imm, 4%Z) ->
  bv_eqb rd 0 = false ->
  v_ori (getr regs rs) (bv_signed imm) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rd rs imm v Hf He Hd Hrd Hv.
  rewrite (step_ori segs regs pc mem rom w rd rs imm Hf He Hd).
  rewrite Hrd, Hv. reflexivity.
Qed.

Lemma step_slli_at : forall segs regs pc mem rom w rd rs (sh : bv 6) v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (ShiftImm ALU_SLL rd rs sh, 4%Z) ->
  bv_eqb rd 0 = false ->
  v_slli (getr regs rs) (bv_unsigned sh) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rd rs sh v Hf He Hd Hrd Hv.
  rewrite (step_slli segs regs pc mem rom w rd rs sh Hf He Hd).
  rewrite Hrd, Hv. reflexivity.
Qed.

Lemma step_srli_at : forall segs regs pc mem rom w rd rs (sh : bv 6) v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (ShiftImm ALU_SRL rd rs sh, 4%Z) ->
  bv_eqb rd 0 = false ->
  v_srli (getr regs rs) (bv_unsigned sh) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rd rs sh v Hf He Hd Hrd Hv.
  rewrite (PropExec.step_srli segs regs pc mem rom w rd rs sh Hf He Hd).
  rewrite Hrd, Hv. reflexivity.
Qed.

Lemma step_srai_at : forall segs regs pc mem rom w rd rs (sh : bv 6) v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (ShiftImm ALU_SRA rd rs sh, 4%Z) ->
  bv_eqb rd 0 = false ->
  v_srai (getr regs rs) (bv_unsigned sh) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rd rs sh v Hf He Hd Hrd Hv.
  rewrite (step_srai segs regs pc mem rom w rd rs sh Hf He Hd).
  rewrite Hrd, Hv. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rdn_wbytes_hit : forall segs bs m (a : word),
  (bv_unsigned a + Z.of_nat (length bs) <= 2^64)%Z ->
  rdn segs (wbytes m a bs) a (length bs) = Some bs.
Proof.
  intros segs bs. induction bs as [|b rest IH]; intros m a Hnw; [reflexivity|].
  cbn [length] in Hnw |- *.
  change (wbytes m a (b :: rest))
    with (wbytes (fun x => if bv_eqb x a then Some b else m x) (a+1) rest).
  set (m' := fun x : word => if bv_eqb x a then Some b else m x).
  cbn [rdn].
  destruct rest as [|b' rest'].
  - cbn [wbytes rdn]. unfold m'. rewrite bv_eqb_refl. reflexivity.
  - assert (Hu1 : bv_unsigned (a+1) = (bv_unsigned a + 1)%Z)
      by (apply u_add1; cbn [length] in Hnw; lia).
    assert (Hread : wbytes m' (a+1) (b' :: rest') a = Some b).
    { rewrite (wbytes_below (b' :: rest') m' (a+1) a);
        [ unfold m'; rewrite bv_eqb_refl; reflexivity
        | cbn [length] in *; lia
        | pose proof (u64_range a); lia ]. }
    rewrite Hread.
    rewrite (IH m' (a+1)) by (cbn [length] in *; lia).
    reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rdn_wbytes_hit8 : forall segs m (a v : word),
  (bv_unsigned a + 8 <= 2^64)%Z ->
  rdn segs (wbytes m a (word_to_le_bytes 8 v)) a 8%nat = Some (word_to_le_bytes 8 v).
Proof.
  intros segs m a v Hnw.
  pose proof (rdn_wbytes_hit segs (word_to_le_bytes 8 v) m a) as H.
  rewrite length_N_to_le_bytes in H. apply H. exact Hnw.
Qed.

(* [comment removed for export] *)
Lemma bytes_le_to_Z_8 : forall v : word,
  bytes_le_to_Z (word_to_le_bytes 8 v) = bv_unsigned v.
Proof.
  intro v. rewrite bytes_le_N.
  change (2 ^ (8 * Z.of_nat 8))%Z with (2^64)%Z.
  apply Z.mod_small. apply u64_range.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma c_ltu_ltb : forall x y : word,
  c_ltu x y = (bv_unsigned x <? bv_unsigned y)%Z.
Proof. reflexivity. Qed.

Lemma v_addiw_small : forall (x : word) imm,
  (0 <= bv_unsigned x + imm)%Z -> (bv_unsigned x + imm < 2^31)%Z -> (0 <= imm)%Z ->
  bv_unsigned (v_addiw x imm) = (bv_unsigned x + imm)%Z.
Proof.
  intros x imm Hlo Hhi _. unfold v_addiw.
  rewrite Z_to_bv_unsigned.
  rewrite bv_swrap_small by (change (bv_half_modulus 32) with (2^31)%Z; lia).
  apply bv_wrap_small. change (bv_modulus 64) with (2^64)%Z. lia.
Qed.

(* [comment removed for export] *)
Lemma v_addiw_id : forall x : word, (bv_unsigned x < 2^31)%Z -> v_addiw x 0 = x.
Proof.
  intros x Hx. apply bv_eq.
  rewrite (v_addiw_small x 0); [lia | pose proof (u64_range x); lia .. ].
Qed.

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
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition argv_layout_slack : Z := 4300000%Z.

(* [comment removed for export] *)

Local Lemma argv_struct_arith : forall a e : Z,
  (0 <= a)%Z -> (a <= 1024)%Z -> (0 <= e)%Z -> (e <= 256)%Z ->
  (8 + (a + 1) * 8 + (e + 1) * 8 + 160 <= 10424)%Z.
Proof. intros. lia. Qed.

Local Lemma argv_sum_arith : forall a b : Z,
  (a <= 10424)%Z -> (b <= 2097152)%Z -> (a + b <= 2107576)%Z.
Proof. intros. lia. Qed.

Local Lemma argv_mod_arith : forall s m : Z,
  (0 <= s)%Z -> (0 <= m)%Z -> (m <= 2107576)%Z -> (s + 4300000 < 2^64)%Z ->
  (0 <= s + m < 2^64)%Z.
Proof. intros. lia. Qed.

Local Lemma argv_final_arith : forall s m l : Z,
  (0 <= m)%Z -> (0 <= l)%Z -> (m <= 2107576)%Z -> (l <= 131071)%Z ->
  (s + 4300000 < 2^64)%Z ->
  (s <= s + m)%Z /\ (s + m + l + 1 < 2^64)%Z.
Proof. intros. lia. Qed.

Lemma argv_ptr_bounds : forall (sp : word) av ev k,
  valid_argv av -> valid_envp ev -> (k < length av)%nat ->
  (bv_unsigned sp + argv_layout_slack < 2^64)%Z ->
  (bv_unsigned sp <= bv_unsigned (cat_argv_ptr sp av ev k))%Z /\
  (bv_unsigned (cat_argv_ptr sp av ev k) + Z.of_nat (length (nth k av [])) + 1 < 2^64)%Z.
Proof.
  intros sp av ev k Hva Hve Hk Hsp.
  pose proof (valid_argv_len av Hva) as HavZ.
  pose proof (valid_argv_str_len av k Hva Hk) as HnthZ.
  destruct Hva as [Hlen [Htot [Hstr Hnz]]].
  destruct Hve as [Helen _].
  assert (HevZ : (Z.of_nat (length ev) <= 256)%Z) by exact Helen.
  assert (HtotZ : (Z.of_nat (total_arg_bytes_nat (firstn k av)) <= 2097152)%Z).
  { rewrite total_arg_bytes_Z in Htot.
    pose proof (total_arg_bytes_firstn_le k av). lia. }
  assert (HA : (Z.of_nat (cat_struct_size av ev) <= 10424)%Z).
  { unfold cat_struct_size, auxv_size.
    repeat (rewrite !Nat2Z.inj_add || rewrite !Nat2Z.inj_mul).
    change (Z.of_nat 8) with 8%Z. change (Z.of_nat 1) with 1%Z.
    change (Z.of_nat 160) with 160%Z.
    apply argv_struct_arith;
      solve [ exact HavZ | exact HevZ | apply Nat2Z.is_nonneg ]. }
  assert (Hptr : cat_argv_ptr sp av ev k
    = sp + nat_to_word (cat_struct_size av ev + total_arg_bytes_nat (firstn k av))).
  { rewrite (cat_argv_ptr_offset sp av ev k Hk). unfold cat_string_base.
    rewrite nat_to_word_add_merge. reflexivity. }
  set (n := (cat_struct_size av ev + total_arg_bytes_nat (firstn k av))%nat) in *.
  assert (HnZ : (Z.of_nat n <= 2107576)%Z)
    by (unfold n; rewrite Nat2Z.inj_add; exact (argv_sum_arith _ _ HA HtotZ)).
  assert (Hu : bv_unsigned (sp + nat_to_word n) = (bv_unsigned sp + Z.of_nat n)%Z).
  { unfold nat_to_word. rewrite bv_add_unsigned, Z_to_bv_unsigned.
    rewrite bv_wrap_add_idemp_r, bv_wrap64_mod.
    apply Z.mod_small.
    pose proof (u64_range sp) as Hu64.
    unfold argv_layout_slack in Hsp.
    exact (argv_mod_arith _ _ (proj1 Hu64) (Nat2Z.is_nonneg n) HnZ Hsp). }
  rewrite Hptr, Hu.
  unfold argv_layout_slack in Hsp.
  exact (argv_final_arith _ _ _ (Nat2Z.is_nonneg n)
           (Nat2Z.is_nonneg (length (nth k av []))) HnZ HnthZ Hsp).
Qed.

(* [comment removed for export] *)
Lemma step_jalr_x0 : forall segs regs pc mem rom w rs1 (imm : bv 12) tgt,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Jalr 0 rs1 imm, 4%Z) ->
  getr regs rs1 = tgt ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs (v_jalr tgt (bv_signed imm)) mem rom).
Proof.
  intros segs regs pc mem rom w rs1 imm tgt Hf He Hd Ht.
  rewrite (step_jalr segs regs pc mem rom w 0 rs1 imm Hf He Hd).
  rewrite Ht. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma step_jalr_link : forall segs regs pc mem rom w rd rs1 (imm : bv 12) tgt,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Jalr rd rs1 imm, 4%Z) ->
  bv_eqb rd 0 = false ->
  getr regs rs1 = tgt ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd (v_addi pc 4)) (v_jalr tgt (bv_signed imm)) mem rom).
Proof.
  intros segs regs pc mem rom w rd rs1 imm tgt Hf He Hd Hrd Ht.
  rewrite (step_jalr segs regs pc mem rom w rd rs1 imm Hf He Hd).
  rewrite Ht, Hrd. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma getr_zero : forall regs, getr regs 0 = Z_to_bv 64 0.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Ltac reg_neq_tac :=
  let Hc := fresh "Hc" in intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate Hc.


(* [comment removed for export] *)
Ltac getr_resolve :=
  repeat first [ rewrite getr_same by reg_neq_tac
               | rewrite getr_other by reg_neq_tac ];
  rewrite ?getr_zero;
  rewrite ?getr_nz by reg_neq_tac.


(* [comment removed for export] *)
Ltac regupd_resolve :=
  repeat first [ rewrite regupd_same
               | rewrite regupd_other by reg_neq_tac ].


(* [comment removed for export] *)
Goal forall regs (v : word), getr (regupd (regupd regs 8 v) 9 v) 8 = v.
Proof. intros. getr_resolve. reflexivity. Abort.
Goal forall regs (v : word), getr (regupd regs 8 v) 0 = Z_to_bv 64 0.
Proof. intros. getr_resolve. reflexivity. Abort.
Goal forall regs (v : word), reg_get (regupd (regupd regs 8 v) 9 v) 8 = v.
Proof. intros. regupd_resolve. reflexivity. Abort.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition v_divu (x y : word) : word :=
  Z_to_bv 64 (bv_unsigned x / bv_unsigned y).
Definition v_remu (x y : word) : word :=
  Z_to_bv 64 (bv_unsigned x mod bv_unsigned y).

(* [comment removed for export] *)
Lemma m_divu : forall a b : word, (bv_unsigned b <> 0)%Z ->
  mul_div M_DIVU a b = v_divu a b.
Proof.
  intros a b Hb.
  change (mul_div M_DIVU a b)
    with (if (bv_unsigned b =? 0)%Z then Z_to_bv 64 (-1) else bv_divu a b).
  rewrite (proj2 (Z.eqb_neq _ _) Hb).
  apply bv_eq. unfold v_divu.
  rewrite bv_divu_unsigned, Z_to_bv_unsigned.
  symmetry; apply bv_wrap_small.
  change (bv_modulus 64) with (2^64)%Z.
  pose proof (u64_range a). pose proof (u64_range b).
  split; [apply Z.div_pos; lia|].
  apply Z.le_lt_trans with (bv_unsigned a); [|lia].
  apply Z.div_le_upper_bound; nia.
Qed.

Lemma m_remu : forall a b : word, (bv_unsigned b <> 0)%Z ->
  mul_div M_REMU a b = v_remu a b.
Proof.
  intros a b Hb.
  change (mul_div M_REMU a b)
    with (if (bv_unsigned b =? 0)%Z then a else bv_modu a b).
  rewrite (proj2 (Z.eqb_neq _ _) Hb).
  apply bv_eq. unfold v_remu.
  rewrite bv_modu_unsigned, Z_to_bv_unsigned.
  symmetry; apply bv_wrap_small.
  change (bv_modulus 64) with (2^64)%Z.
  pose proof (u64_range a). pose proof (u64_range b).
  pose proof (Z.mod_pos_bound (bv_unsigned a) (bv_unsigned b) ltac:(lia)).
  lia.
Qed.

Lemma step_divu : forall segs regs pc mem rom w rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Mul M_DIVU rd rs1 rs2, 4%Z) ->
  (bv_unsigned (getr regs rs2) <> 0)%Z ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs
                   else regupd regs rd (v_divu (getr regs rs1) (getr regs rs2)))
                  (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rd rs1 rs2 Hf He Hd Hnz.
  erewrite step_mul_gen by eassumption.
  rewrite m_divu by exact Hnz. reflexivity.
Qed.

Lemma step_remu : forall segs regs pc mem rom w rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Mul M_REMU rd rs1 rs2, 4%Z) ->
  (bv_unsigned (getr regs rs2) <> 0)%Z ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs
                   else regupd regs rd (v_remu (getr regs rs1) (getr regs rs2)))
                  (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rd rs1 rs2 Hf He Hd Hnz.
  erewrite step_mul_gen by eassumption.
  rewrite m_remu by exact Hnz. reflexivity.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma step_sb : forall segs regs pc mem rom w (rs1 rs2 : reg) (imm : bv 12),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Store SZ1 rs1 rs2 imm, 4%Z) ->
  RiscvSemantics.store_ok segs mem
    (v_addi (getr regs rs1) (bv_signed imm)) 1%nat = true ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs (v_addi pc 4)
    (wbytes mem (v_addi (getr regs rs1) (bv_signed imm))
            (word_to_le_bytes 1 (getr regs rs2))) rom).
Proof.
  intros segs regs pc mem rom w rs1 rs2 imm Hfetch Hecall Hdecode Hok.
  assert (Hsb : forall u : word,
    Z_to_le_bytes 1%nat (bv_unsigned (bv_extract 0 8 u)) = word_to_le_bytes 1 u).
  { intro u. unfold word_to_le_bytes. cbn [Z_to_le_bytes].
    f_equal. apply bv_eq.
    rewrite !Z_to_bv_unsigned, bv_extract_unsigned, Z.shiftr_0_r.
    apply bv_wrap_bv_wrap. lia. }
  step_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  unfold getr in Hok; rewrite ?bv_eqb0_is_x0 in Hok.
  rewrite b_addsext.
  rewrite Hok; cbv beta iota.
  rewrite write_to_mem_wbytes, Hsb, b_npc4.
  reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma N_to_le_bytes_1_small : forall v : word,
  word_to_le_bytes 1 v = [Z_to_bv 8 (bv_unsigned v)].
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma Zmod_pow2_div8 : forall z m, (8 <= m)%Z ->
  ((z mod 2^m) / 2^8)%Z = ((z / 2^8) mod 2^(m-8))%Z.
Proof.
  intros z m Hm.
  rewrite <- !Z.shiftr_div_pow2 by lia.
  apply Z.bits_inj'; intros i Hi.
  rewrite !Z.shiftr_spec by lia.
  destruct (Z.lt_ge_cases i (m - 8)) as [Hlt|Hge].
  - rewrite !Z.mod_pow2_bits_low by lia.
    rewrite Z.shiftr_spec by lia. reflexivity.
  - rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma Z_to_le_bytes_wrap : forall n (m : N) z,
  (8 * Z.of_nat n <= Z.of_N m)%Z ->
  Z_to_le_bytes n (bv_wrap m z) = Z_to_le_bytes n z.
Proof.
  induction n as [|n IH]; intros m z Hm; cbn [Z_to_le_bytes]; [reflexivity|].
  f_equal.
  - apply bv_eq. rewrite !Z_to_bv_unsigned.
    apply bv_wrap_bv_wrap. lia.
  - replace (Z.shiftr (bv_wrap m z) 8) with (bv_wrap (m - 8) (Z.shiftr z 8)).
    + apply IH. lia.
    + unfold bv_wrap, bv_modulus.
      rewrite !Z.shiftr_div_pow2 by lia.
      rewrite Zmod_pow2_div8 by lia.
      do 2 f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma store_bytes_low16 : forall u : word,
  Z_to_le_bytes 2 (bv_unsigned (bv_extract 0 16 u)) = word_to_le_bytes 2 u.
Proof.
  intro u. unfold word_to_le_bytes.
  rewrite bv_extract_unsigned, Z.shiftr_0_r.
  apply Z_to_le_bytes_wrap. lia.
Qed.

(* [comment removed for export] *)
Lemma store_bytes_low32 : forall u : word,
  Z_to_le_bytes 4 (bv_unsigned (low32 u)) = word_to_le_bytes 4 u.
Proof.
  intro u. unfold low32, word_to_le_bytes.
  rewrite bv_extract_unsigned, Z.shiftr_0_r.
  apply Z_to_le_bytes_wrap. lia.
Qed.

(* [comment removed for export] *)
Lemma step_sw_val : forall segs regs pc mem rom w (rs1 rs2 : reg) (imm : bv 12),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Store SZ4 rs1 rs2 imm, 4%Z) ->
  RiscvSemantics.store_ok segs mem
    (v_addi (getr regs rs1) (bv_signed imm)) 4%nat = true ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs (v_addi pc 4)
    (wbytes mem (v_addi (getr regs rs1) (bv_signed imm))
            (word_to_le_bytes 4 (getr regs rs2))) rom).
Proof.
  intros segs regs pc mem rom w rs1 rs2 imm Hfetch Hecall Hdecode Hok.
  step_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  unfold getr in Hok; rewrite ?bv_eqb0_is_x0 in Hok.
  rewrite b_addsext.
  rewrite Hok; cbv beta iota.
  rewrite write_to_mem_wbytes, store_bytes_low32, b_npc4.
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma step_sw_at : forall segs regs pc mem rom w (rs1 rs2 : reg) (imm : bv 12) (a v : word),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Store SZ4 rs1 rs2 imm, 4%Z) ->
  v_addi (getr regs rs1) (bv_signed imm) = a ->
  getr regs rs2 = v ->
  RiscvSemantics.store_ok segs mem a 4%nat = true ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs (v_addi pc 4) (wbytes mem a (word_to_le_bytes 4 v)) rom).
Proof.
  intros segs regs pc mem rom w rs1 rs2 imm a v Hf He Hd Ha Hv Hok.
  rewrite (step_sw_val segs regs pc mem rom w rs1 rs2 imm Hf He Hd).
  - rewrite Ha, Hv. reflexivity.
  - rewrite Ha. exact Hok.
Qed.

(* [comment removed for export] *)
Lemma step_sh_val : forall segs regs pc mem rom w (rs1 rs2 : reg) (imm : bv 12),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Store SZ2 rs1 rs2 imm, 4%Z) ->
  RiscvSemantics.store_ok segs mem
    (v_addi (getr regs rs1) (bv_signed imm)) 2%nat = true ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs (v_addi pc 4)
    (wbytes mem (v_addi (getr regs rs1) (bv_signed imm))
            (word_to_le_bytes 2 (getr regs rs2))) rom).
Proof.
  intros segs regs pc mem rom w rs1 rs2 imm Hfetch Hecall Hdecode Hok.
  step_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  unfold getr in Hok; rewrite ?bv_eqb0_is_x0 in Hok.
  rewrite b_addsext.
  rewrite Hok; cbv beta iota.
  rewrite write_to_mem_wbytes, store_bytes_low16, b_npc4.
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma step_sh_at : forall segs regs pc mem rom w (rs1 rs2 : reg) (imm : bv 12) (a v : word),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Store SZ2 rs1 rs2 imm, 4%Z) ->
  v_addi (getr regs rs1) (bv_signed imm) = a ->
  getr regs rs2 = v ->
  RiscvSemantics.store_ok segs mem a 2%nat = true ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs (v_addi pc 4) (wbytes mem a (word_to_le_bytes 2 v)) rom).
Proof.
  intros segs regs pc mem rom w rs1 rs2 imm a v Hf He Hd Ha Hv Hok.
  rewrite (step_sh_val segs regs pc mem rom w rs1 rs2 imm Hf He Hd).
  - rewrite Ha, Hv. reflexivity.
  - rewrite Ha. exact Hok.
Qed.

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

Lemma rdn_app : forall segs mem n1 n2 (a : word) bs1 bs2,
  rdn segs mem a n1 = Some bs1 ->
  rdn segs mem (a + nat_to_word n1) n2 = Some bs2 ->
  rdn segs mem a (n1 + n2)%nat = Some (bs1 ++ bs2).
Proof.
  intros segs mem n1. induction n1 as [|n1 IH]; intros n2 a bs1 bs2 H1 H2.
  - cbn in H1. injection H1 as <-. cbn [app].
    rewrite word_add_0 in H2. exact H2.
  - change (S n1 + n2)%nat with (S (n1 + n2))%nat.
    cbn [rdn] in H1 |- *.
    destruct (match mem a with Some b => Some b | None => seg_rom segs a end)
      as [b|]; [|discriminate].
    destruct (rdn segs mem (a+1) n1) as [rest|] eqn:Er; [|discriminate].
    injection H1 as <-.
    rewrite (IH n2 (a+1) rest bs2 Er); [reflexivity|].
    replace (a + 1 + nat_to_word n1) with (a + nat_to_word (S n1))
      by (rewrite word1_nat, nat_to_word_add_merge; reflexivity).
    exact H2.
Qed.

Lemma rdn_nth : forall segs mem n (a : word) bs j,
  rdn segs mem a n = Some bs -> (j < n)%nat ->
  rdn segs mem (a + nat_to_word j) 1%nat = Some [nth j bs (Z_to_bv 8 0)].
Proof.
  intros segs mem n. induction n as [|n IH]; intros a bs j H Hj; [lia|].
  cbn [rdn] in H.
  destruct (match mem a with Some b => Some b | None => seg_rom segs a end)
    as [b|] eqn:Eb; [|discriminate].
  destruct (rdn segs mem (a+1) n) as [rest|] eqn:Er; [|discriminate].
  injection H as <-.
  destruct j as [|j].
  - rewrite word_add_0. cbn [rdn nth]. rewrite Eb. reflexivity.
  - cbn [nth].
    replace (a + nat_to_word (S j)) with (a + 1 + nat_to_word j)
      by (rewrite word1_nat, nat_to_word_add_merge; reflexivity).
    apply (IH (a+1) rest j Er). lia.
Qed.

(* [comment removed for export] *)
Lemma v_addi_m : forall (x : word) (k : Z),
  (k <= bv_unsigned x)%Z -> (0 < k)%Z ->
  v_addi x (- k) = Z_to_bv 64 (bv_unsigned x - k).
Proof. intros x k _ _. reflexivity. Qed.

(* [comment removed for export] *)

Lemma rdn_firstn : forall segs mem n (a : word) bs k,
  rdn segs mem a n = Some bs -> (k <= n)%nat ->
  rdn segs mem a k = Some (firstn k bs).
Proof.
  intros segs mem n. induction n as [|n IH]; intros a bs k H Hk.
  - assert (k = 0)%nat by lia. subst k. cbn in H |- *.
    injection H as <-. reflexivity.
  - cbn [rdn] in H.
    destruct (match mem a with Some b => Some b | None => seg_rom segs a end)
      as [b|] eqn:Eb; [|discriminate].
    destruct (rdn segs mem (a+1) n) as [rest|] eqn:Er; [|discriminate].
    injection H as <-.
    destruct k as [|k]; [reflexivity|].
    cbn [rdn firstn]. rewrite Eb.
    rewrite (IH (a+1) rest k Er) by lia. reflexivity.
Qed.
End SeqExec.

Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SimInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.CatSim.ExitSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.CatSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.SeqExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.CatExec.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.

Module Stredvh.
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require CatSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require PropExec CatSim.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.CatSim.ExitSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.CatSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.CatExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.SeqExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.


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
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma adv_apply_write : forall regs pc sv mem rom ret buf data,
  advance_past_svc (apply_effect
    {| ms_regs := regs; ms_fregs := bvmap_empty; ms_pc_val := pc; ms_svc_pending := sv; ms_resv := None; ms_fcsr := Z_to_bv 32 0;
       ms_mem := mem; ms_rom := rom |}
    (mkEffect ret [(buf, data)] []))
  = mkst (regupd regs 10 ret) (v_addi pc 4) (write_to_mem mem buf data) rom.
Proof.
  intros regs pc sv mem rom ret buf data.
  unfold advance_past_svc, apply_effect, RiscvSemantics.set_reg, ms_pc.
  rewrite bv_eqb_neq by (intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate).
  cbv beta iota zeta.
  cbn [ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom
       eff_ret eff_writes eff_zeros eff_unmaps eff_copies apply_copies
       apply_zeros apply_unmaps apply_writes].
  unfold mkst, regupd.
  rewrite b_npc4. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
End Stredvh.


Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.

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


(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)


Section WithSegsCh.
Variable segs : list Segment.
Variable fd ch : word.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive to_wall : machine_state -> list byte -> (machine_state -> Prop) -> Prop :=
| twl_write : forall ms x8 rest k,
    ms_svc_pending ms = Some x8 ->
    bv_unsigned x8 = 64%Z ->
    ms_gpr ms 0 = fd ->
    ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some rest ->
    (1 <= length rest)%nat ->
    (forall n, (1 <= n)%nat -> (n <= length rest)%nat ->
       to_wall_tail (advance_past_svc (set_gpr0 ms (len_word (firstn n rest))))
         (skipn n rest) k) ->
    to_wall ms rest k
with to_wall_tail : machine_state -> list byte -> (machine_state -> Prop) -> Prop :=
| twt_done : forall ms k, k ms -> to_wall_tail ms [] k
| twt_more : forall ms rest k,
    (1 <= length rest)%nat ->
    to_wall ms rest k ->
    to_wall_tail ms rest k
| twt_step : forall ms ms' rest k,
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    to_wall_tail ms' rest k ->
    to_wall_tail ms rest k.

Scheme to_wall_min := Minimality for to_wall Sort Prop
  with to_wall_tail_min := Minimality for to_wall_tail Sort Prop.
Combined Scheme to_wall_mutind from to_wall_min, to_wall_tail_min.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Hypothesis Hfd32 : fd32 fd = fd.

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
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint to_wallexit (bufs : list (list byte)) (code : word)
    (ms : machine_state) : Prop :=
  match bufs with
  | [] => to_wexit segs ms [] code
  | buf :: rest =>
      (1 <= length buf)%nat /\
      to_wall_tail ms buf (to_wallexit rest code)
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma twe_step : forall ms ms' bufs code,
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  to_wallexit bufs code ms' -> to_wallexit bufs code ms.
Proof.
  intros ms ms' bufs code Hsvc Hstep Hw.
  destruct bufs as [|buf rest].
  - eapply tw_step; eauto.
  - destruct Hw as [Hnb Hw]. split; [exact Hnb|].
    eapply twt_step; eauto.
Qed.

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
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition wall_won_path (c : config) : Prop :=
  (m_halted (cfg_model c) = None /\ m_vm_lazy (cfg_model c) = [] /\
   fdchan fd ch (cfg_model c) /\
   exists bufs code rest,
     buf_modeled rest /\ bufs_modeled bufs /\
     to_wall_tail (cfg_ms c) rest (to_wallexit bufs code))
  \/ m_halted (cfg_model c) <> None.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)


End WithSegsCh.

(* [comment removed for export] *)
Abbreviation wexit1 segs ms bufs code :=
  (to_wallexit segs (Z_to_bv 64 1) bufs code ms).

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

