(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool LinuxProcessSemantics.EquivalenceDefinition.Equivalence LinuxProcessSemantics.EquivalenceDefinition.MustExit LinuxProcessSemantics.EquivalenceDefinition.OmniEquivalence LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.LinuxProcessSem.OmniRun LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.ReadWrite OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module CatSim.
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence LinuxProcessSemantics.EquivalenceDefinition.MustExit LinuxProcessSemantics.EquivalenceDefinition.OmniEquivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.LinuxProcessSem.OmniRun.
Import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.ReadWrite.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim.SimInv OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim.
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

Lemma read_aux_read_byte : forall ms k a,
  read_bytes_aux (ms_read_byte ms) a k = ms_read_bytes_aux ms a k.
Proof.
  intros ms. induction k as [|k IH]; intro a; [reflexivity|].
  cbn [read_bytes_aux ms_read_bytes_aux].
  destruct (ms_read_byte ms a) as [b|]; [rewrite IH|]; reflexivity.
Qed.

Lemma read_bytes_map_read_byte : forall ms a len,
  read_bytes_map (ms_read_byte ms) a len = ms_read_bytes ms a len.
Proof. intros. rewrite read_bytes_map_eq. unfold ms_read_bytes.
  apply read_aux_read_byte. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma apply_effect_no_write : forall ms r,
  apply_effect ms (mkEffect r [] []) = set_gpr0 ms r.
Proof.
  intros ms r. unfold apply_effect, set_gpr0.
  cbn [eff_ret eff_writes eff_zeros apply_zeros apply_writes].
  reflexivity.
Qed.

Lemma apply_effect_copyins_no_write : forall ms r copyins,
  apply_effect ms (with_copyins copyins (mkEffect r [] [])) = set_gpr0 ms r.
Proof.
  intros ms r copyins. unfold with_copyins, apply_effect, set_gpr0.
  cbn [eff_ret eff_writes eff_zeros eff_unmaps eff_copies
       apply_unmaps apply_zeros apply_copies apply_writes].
  reflexivity.
Qed.






(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition fd1chan (model : Model) : Prop :=
  fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)).

(* [comment removed for export] *)
Definition buf_modeled (b : list byte) : Prop :=
  (Z.of_nat (length b) <= rw_bytes_max)%Z.

Definition bufs_modeled (bufs : list (list byte)) : Prop :=
  Forall buf_modeled bufs.








(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma is_prefix_app_mono {A} : forall (l a b : list A),
  is_prefix a b -> is_prefix (l ++ a) (l ++ b).
Proof.
  induction l as [|x l IH]; intros a b H; cbn; [exact H | split; [reflexivity | apply IH; exact H]].
Qed.


Inductive wpick (ch : word) : list (list byte) -> list event -> Prop :=
| wp_nil : wpick ch [] []
| wp_cons : forall buf bufs n tr,
    (1 <= n)%nat -> (n <= length buf)%nat ->
    wpick ch bufs tr ->
    wpick ch (buf :: bufs) (map (WriteEv ch) (firstn n buf) ++ tr).


Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive to_wexit : machine_state -> list (list byte) -> word -> Prop :=
| tw_exit : forall ms x8,
    ms_svc_pending ms = Some x8 ->
    is_exit_no x8 ->
    to_wexit ms [] (bv_and (ms_gpr ms 0) (Z_to_bv 64 255))
| tw_write : forall ms x8 buf bufs code,
    ms_svc_pending ms = Some x8 ->
    bv_unsigned x8 = 64%Z ->
    ms_gpr ms 0 = Z_to_bv 64 1 ->
    ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
    (1 <= length buf)%nat ->
    (forall n, (1 <= n)%nat -> (n <= length buf)%nat ->
       to_wexit (advance_past_svc (set_gpr0 ms (len_word (firstn n buf)))) bufs code) ->
    to_wexit ms (buf :: bufs) code
| tw_step : forall ms ms' bufs code,
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    to_wexit ms' bufs code ->
    to_wexit ms bufs code.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive msteps : machine_state -> machine_state -> Prop :=
| mst_refl : forall ms, msteps ms ms
| mst_step : forall ms ms' ms'',
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    msteps ms' ms'' ->
    msteps ms ms''.

Lemma msteps_one : forall ms ms',
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  msteps ms ms'.
Proof. intros ms ms' Hsvc Hstep. eapply mst_step; [exact Hsvc | exact Hstep | apply mst_refl]. Qed.

Lemma msteps_trans : forall ms ms' ms'',
  msteps ms ms' -> msteps ms' ms'' -> msteps ms ms''.
Proof.
  intros ms ms' ms'' H; induction H; [auto|].
  intro H2. eapply mst_step; eauto.
Qed.

Lemma msteps_to_wexit : forall ms ms' bufs code,
  msteps ms ms' -> to_wexit ms' bufs code -> to_wexit ms bufs code.
Proof.
  intros ms ms' bufs code H; induction H; [auto|].
  intro Hw. eapply tw_step; eauto.
Qed.










End WithSegs.
















Section WithSegsCh.
Variable segs : list Segment.
Variable fd ch : word.

(* [comment removed for export] *)
Inductive to_wexit_ch : machine_state -> list (list byte) -> word -> Prop :=
| twc_exit : forall ms x8,
    ms_svc_pending ms = Some x8 ->
    is_exit_no x8 ->
    to_wexit_ch ms [] (bv_and (ms_gpr ms 0) (Z_to_bv 64 255))
| twc_write : forall ms x8 buf bufs code,
    ms_svc_pending ms = Some x8 ->
    bv_unsigned x8 = 64%Z ->
    ms_gpr ms 0 = fd ->
    ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
    (1 <= length buf)%nat ->
    (forall n, (1 <= n)%nat -> (n <= length buf)%nat ->
       to_wexit_ch (advance_past_svc (set_gpr0 ms (len_word (firstn n buf)))) bufs code) ->
    to_wexit_ch ms (buf :: bufs) code
| twc_step : forall ms ms' bufs code,
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    to_wexit_ch ms' bufs code ->
    to_wexit_ch ms bufs code.


Hypothesis Hfd32 : fd32 fd = fd.


End WithSegsCh.


End CatSim.
Module MallocDefs.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition UNIT : Z := 16.
Definition IB : Z := 4.

(* [comment removed for export] *)
Definition size_classes : list Z :=
  [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 12; 15; 18; 20; 25; 31; 36; 42; 50; 63; 72; 84; 102; 127;
   146; 170; 204; 255; 292; 340; 409; 511; 584; 682; 818; 1023; 1169; 1364; 1637; 2047;
   2340; 2730; 3276; 4095; 4680; 5460; 6552; 8191].

Definition size_class (sc : Z) : Z := nth (Z.to_nat sc) size_classes 0.

(* [comment removed for export] *)
Definition w_lastidx (W : Z) : Z := W mod 32.
Definition w_freeable (W : Z) : Z := (W / 32) mod 2.
Definition w_sizeclass (W : Z) : Z := (W / 64) mod 64.
Definition w_maplen (W : Z) : Z := W / 4096.

(* [comment removed for export] *)
Definition slot_stride (maplen lastidx sc : Z) : Z :=
  if (negb (maplen =? 0)) && (lastidx =? 0) then maplen * 4096 - UNIT else UNIT * size_class sc.

(* [comment removed for export] *)
Definition slot_start (M stride idx : Z) : Z := M + UNIT + stride * idx.


Lemma size_class_pos : forall sc, 0 <= sc < 48 -> 1 <= size_class sc <= 8191.
Proof.
  intros sc Hsc. unfold size_class.
  assert (E : exists k, (k < 48)%nat /\ Z.to_nat sc = k) by (exists (Z.to_nat sc); split; [lia|reflexivity]).
  destruct E as (k & Hk & ->).
  do 48 (destruct k as [|k]; [cbn; lia|]). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition slack_of (stride n : Z) : Z := (stride - IB - n) / UNIT.

(* [comment removed for export] *)
Definition smear (slack : Z) : Z :=
  let m1 := Z.lor slack (slack / 2) in
  let m2 := Z.lor m1 (m1 / 4) in
  Z.lor m2 (m2 / 16).

(* [comment removed for export] *)
Definition enframe_off (slack off0 : Z) : Z :=
  if off0 <=? slack then off0
  else let om := Z.land off0 (smear slack) in
       if slack <? om then om - slack - 1 else om.

Definition res_code (reserved : Z) : Z := if reserved <? 5 then reserved else 5.

End MallocDefs.
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec CatSim.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Section WithFP.
Context {fx : FPState}.

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
Lemma stack_max_size_val : stack_max_size = 8388608%Z.
Proof. vm_compute. reflexivity. Qed.


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

Definition byte_at (s : list byte) (k : nat) : byte :=
  nth k (s ++ [Z_to_bv 8 0]) (Z_to_bv 8 0).

Lemma nth_lt_byte_at : forall s j, (j < length s)%nat ->
  byte_at s j = nth j s (Z_to_bv 8 0).
Proof. intros s j Hj. unfold byte_at. apply app_nth1. exact Hj. Qed.

Lemma byte_at_len : forall s, byte_at s (length s) = Z_to_bv 8 0.
Proof.
  intros s. unfold byte_at. rewrite app_nth2 by lia.
  rewrite Nat.sub_diag. reflexivity.
Qed.



Lemma valid_argv_len : forall av, valid_argv av ->
  (Z.of_nat (length av) <= 1024)%Z.
Proof. intros av [Hlen _]. lia. Qed.

Lemma valid_argv_nonempty : forall av, valid_argv av -> (1 <= length av)%nat.
Proof. intros av [Hlen _]. lia. Qed.

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
Lemma valid_argv_str_plain : forall av k, valid_argv av ->
  (S k < length av)%nat ->
  path_eqb (nth (S k) av []) dot_path = false ->
  openat_plain_name (nth (S k) av []) = true.
Proof.
  intros av k [_ [_ [_ [_ Hpl]]]] Hk Hdot.
  assert (Hnth : nth (S k) av [] = nth k (tl av) []).
  { destruct av as [|a av']; [cbn in Hk; lia | reflexivity]. }
  assert (Hk' : (k < length (tl av))%nat).
  { destruct av as [|a av']; cbn in *; lia. }
  rewrite Forall_forall in Hpl.
  destruct (Hpl _ (nth_In (tl av) [] Hk')) as [Hsl Hdd].
  rewrite Hnth in Hdot |- *.
  unfold openat_plain_name, path_is_dirref.
  rewrite Hdot, Hsl, Hdd. reflexivity.
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
Definition pend (regs : bvmap 5 word) (pc : word) (mem rom : word -> option byte)
    : machine_state :=
  {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc; ms_svc_pending := Some (Z_to_bv 64 64);
     ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := rom |}.

(* [comment removed for export] *)
Lemma adv_set : forall regs pc sv mem rom v,
  advance_past_svc (set_gpr0
    {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc; ms_svc_pending := sv; ms_resv := None; ms_fcsr := fp_csr;
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




End WithFP.
